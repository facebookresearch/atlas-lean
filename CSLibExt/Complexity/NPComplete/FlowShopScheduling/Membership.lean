/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.NPComplete.FlowShopSchedulingDefs
public import CSLibExt.Computability.Complexity.FramedCNF.Normalize
public import CSLibExt.Computability.Complexity.Host
public import CSLibExt.Computability.Complexity.PolynomialEncoding.Bounds
public import CSLibExt.Computability.Complexity.PolynomialEncoding.Copy
public import CSLibExt.Computability.Complexity.PolynomialEncoding.ListNat
public import CSLibExt.Computability.Complexity.PolynomialEncoding.ListParts
public import CSLibExt.Computability.Complexity.PolynomialEncoding.NormalizeRun
public import CSLibExt.Computability.Complexity.PolynomialEncoding.PairSplit
public import CSLibExt.Computability.CookLevin
public import Mathlib.Data.List.OfFn
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.Ring
public import MathlibExt.Computability.TuringMachine.BitOps
public import MathlibExt.Computability.TuringMachine.Cleanup
public import MathlibExt.Computability.TuringMachine.Program
public import MathlibExt.Computability.TuringMachine.Recursive.OfTM2
public import MathlibExt.Computability.TuringMachine.StackEmbedding

/-!
# FLOW-SHOP SCHEDULING is in NP

A certificate is a schedule: one row of start times `σ_1(j), …, σ_m(j)` per job, encoded like
the job rows of the instance. The functional verifier `Verification.check` reads an instance and
a certificate with finite scans over the raw bit blocks, without decoding them first:

* it splits the instance into `m`, the job rows and `D`, rejecting undecodable input, `m = 0`
  and `D = 0`;
* for each job, a local scan checks every task against the deadline (`σ_i(j) + l(t_i[j]) ≤ D`)
  and against the previous task of the job (`σ_i(j) + l(t_i[j]) ≤ σ_{i+1}(j)`), and that the job
  and its schedule row both have exactly `m` columns;
* for each pair of jobs `j < k`, a column scan checks that their tasks do not overlap on any
  processor;
* it accepts when every job has exactly one schedule row.

The verifier never iterates over the processors on its own, so an instance with a large `m` and
few jobs costs nothing extra. A multi-stack Turing machine computes `check`
(`Verification.isPolyTime_check`, within `40 · (|x| + |w| + 3)⁴` steps), and
`Verification.dec_iff_check` shows that some certificate of length at most `3|x|(2|x| + 1)` is
accepted exactly when the instance is well formed and feasible.

The machine reuses the repository's block splitter, number normalizer and stack copy and cleanup
machines. Its bit-serial comparison kernel `Verification.Compare` is copied from the private
`Compare` of `CSLibExt/Computability/Complexity/Karp/FlowShop/Verifier.lean` (the verifier of
the three-machine problem).

Source: M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), [SS15].
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FlowShopScheduling

namespace Verification

section Spec

/-! ### Raw-bit scans for the general flow-shop verifier

Pure functions over raw bit blocks that mirror the verifier machine phase by phase, and their
equations in terms of the canonical decoder.
-/

open MetaMathlibExt.BitstringEncoding Computability

private theorem undelimit_lt {x p r : List Bool} (h : undelimit x = some (p, r)) :
    r.length < x.length := by
  rw [(Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp h]
  simp only [List.length_append, length_delimit]
  omega

private theorem undelimit_nil : undelimit ([] : List Bool) = none := rfl

/-- Local scan of one job row and its schedule row: number of columns when every column meets
the deadline and the previous task of the job (sum `prev`) ends by the current start. -/
def localScan (D : ℕ) (prev : Option ℕ) (rj rs : List Bool) : Option ℕ :=
  if rj = [] ∧ rs = [] then some 0 else
  match _h : undelimit rj, undelimit rs with
  | some (pl, rj'), some (ps, rs') =>
    if decodeNat ps + decodeNat pl ≤ D ∧ prev.all (· ≤ decodeNat ps) then
      (localScan D (some (decodeNat ps + decodeNat pl)) rj' rs').map (· + 1)
    else none
  | _, _ => none
termination_by rj.length
decreasing_by exact undelimit_lt _h

/-- Column scan of two jobs: every column separates the two tasks. -/
def pairScan (ra sa rb sb : List Bool) : Bool :=
  if ra = [] ∧ sa = [] ∧ rb = [] ∧ sb = [] then true else
  match _h : undelimit ra, undelimit sa, undelimit rb, undelimit sb with
  | some (pla, ra'), some (psa, sa'), some (plb, rb'), some (psb, sb') =>
    (decide (decodeNat psa + decodeNat pla ≤ decodeNat psb) ||
      decide (decodeNat psb + decodeNat plb ≤ decodeNat psa)) && pairScan ra' sa' rb' sb'
  | _, _, _, _ => false
termination_by ra.length
decreasing_by exact undelimit_lt _h

/-- Inner scan: the job `(ra, sa)` against every remaining job. -/
def innerScan (ra sa J S : List Bool) : Bool :=
  if J = [] ∧ S = [] then true else
  match _h : undelimit J, undelimit S with
  | some (rb, J'), some (sb, S') => pairScan ra sa rb sb && innerScan ra sa J' S'
  | _, _ => false
termination_by J.length
decreasing_by exact undelimit_lt _h

/-- Outer scan over all jobs. -/
def outerScan (m D : ℕ) (J S : List Bool) : Bool :=
  if J = [] ∧ S = [] then true else
  match _h : undelimit J, undelimit S with
  | some (ra, J'), some (sa, S') =>
    (localScan D none ra sa == some m) && innerScan ra sa J' S' && outerScan m D J' S'
  | _, _ => false
termination_by J.length
decreasing_by exact undelimit_lt _h

/-- The verifier on raw bitstrings. -/
def check (x w : List Bool) : Bool :=
  match undelimit x with
  | none => false
  | some (M, R) =>
    match undelimit R with
    | none => false
    | some (Jp, E) =>
      decide (0 < decodeNat M) && decide (0 < decodeNat E) &&
        outerScan (decodeNat M) (decodeNat E) Jp w

/-! ## Decoded counterparts -/

def localD (D : ℕ) : Option ℕ → List ℕ → List ℕ → Option ℕ
  | _, [], [] => some 0
  | prev, l :: ls, s :: ss =>
    if s + l ≤ D ∧ prev.all (· ≤ s) then (localD D (some (s + l)) ls ss).map (· + 1)
    else none
  | _, _, _ => none

def pairD : List ℕ → List ℕ → List ℕ → List ℕ → Bool
  | [], [], [], [] => true
  | la :: las, sa :: sas, lb :: lbs, sb :: sbs =>
    (decide (sa + la ≤ sb) || decide (sb + lb ≤ sa)) && pairD las sas lbs sbs
  | _, _, _, _ => false

def innerD (la sa : List ℕ) : List (List ℕ) → List (List ℕ) → Bool
  | [], [] => true
  | lb :: lbs, sb :: sbs => pairD la sa lb sb && innerD la sa lbs sbs
  | _, _ => false

def outerD (m D : ℕ) : List (List ℕ) → List (List ℕ) → Bool
  | [], [] => true
  | la :: las, sa :: sas =>
    (localD D none la sa == some m) && innerD la sa las sas && outerD m D las sas
  | _, _ => false

/-! ## Decoder equations -/

private theorem decode_list_nil {α : Type} [MetaMathlibExt.BitstringEncoding α] :
    bitDecode (α := List α) ([] : List Bool) = some [] := rfl

private theorem decode_nat (p : List Bool) : bitDecode (α := ℕ) p = some (decodeNat p) := rfl

/-- One step of the list decoder on a nonempty input. -/
private theorem decode_list_step {α : Type} [MetaMathlibExt.BitstringEncoding α] {x : List Bool}
    (hx : x ≠ []) :
    bitDecode (α := List α) x = match undelimit x with
      | none => none
      | some (p, r) => (bitDecode (α := α) p).bind fun a =>
          (bitDecode (α := List α) r).map (a :: ·) := by
  cases h : undelimit x with
  | none => exact Cslib.Complexity.PolynomialEncoding.decode_list_none_of_undelimit_none hx h
  | some pr =>
    obtain ⟨p, r⟩ := pr
    rw [(Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp h]
    exact Cslib.Complexity.PolynomialEncoding.decode_list_delimit p r

end Spec

section SpecEq

open MetaMathlibExt.BitstringEncoding Computability

abbrev dec (x : List Bool) : Option (List ℕ) := bitDecode (α := List ℕ) x
abbrev dec2 (x : List Bool) : Option (List (List ℕ)) := bitDecode (α := List (List ℕ)) x

private theorem dec_split {α : Type} [MetaMathlibExt.BitstringEncoding α] {x p r : List Bool}
    (h : undelimit x = some (p, r)) :
    bitDecode (α := List α) x = (bitDecode (α := α) p).bind fun a =>
      (bitDecode (α := List α) r).map (a :: ·) := by
  rw [(Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp h]
  exact Cslib.Complexity.PolynomialEncoding.decode_list_delimit p r

private theorem dec_bad {α : Type} [MetaMathlibExt.BitstringEncoding α] {x : List Bool}
    (hx : x ≠ []) (h : undelimit x = none) : bitDecode (α := List α) x = none :=
  Cslib.Complexity.PolynomialEncoding.decode_list_none_of_undelimit_none hx h

/-- A nonempty input decodes to no list or to a nonempty list. -/
private theorem dec_ne_nil {α : Type} [MetaMathlibExt.BitstringEncoding α] {x : List Bool}
    (hx : x ≠ []) : ∀ l, bitDecode (α := List α) x = some l → l ≠ [] := by
  intro l hl
  cases h : undelimit x with
  | none => rw [dec_bad hx h] at hl; cases hl
  | some pr =>
    obtain ⟨p, r⟩ := pr
    rw [dec_split h] at hl
    cases hp : bitDecode (α := α) p <;> cases hr : bitDecode (α := List α) r <;>
      simp only [hp, hr, Option.bind_some, Option.map_some, Option.bind_none,
        Option.map_none, reduceCtorEq, Option.some.injEq] at hl
    subst hl
    exact List.cons_ne_nil _ _

private theorem localD_nil_left (D : ℕ) (prev : Option ℕ) (ls : List ℕ) (h : ls ≠ []) :
    localD D prev [] ls = none := by
  cases ls with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

private theorem localD_nil_right (D : ℕ) (prev : Option ℕ) (ls : List ℕ) (h : ls ≠ []) :
    localD D prev ls [] = none := by
  cases ls with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

private theorem localScan_eq (D : ℕ) (prev : Option ℕ) (rj rs : List Bool) :
    localScan D prev rj rs = (dec rj).bind fun lj => (dec rs).bind fun ls =>
      localD D prev lj ls := by
  induction h : rj.length using Nat.strong_induction_on generalizing prev rj rs with
  | _ n ih =>
    subst h
    by_cases hj : rj = []
    · subst hj
      by_cases hs : rs = []
      · subst hs
        rw [localScan]
        rfl
      · rw [localScan]
        simp only [hs, and_false, ↓reduceIte]
        simp only [undelimit_nil, decode_list_nil, Option.bind_some]
        cases hd : dec rs with
        | none => rfl
        | some ls => exact (localD_nil_left D prev ls (dec_ne_nil hs ls hd)).symm
    · rw [localScan]
      simp only [hj, false_and, ↓reduceIte]
      cases hu : undelimit rj with
      | none => simp [dec_bad hj hu]
      | some pr =>
        obtain ⟨pl, rj'⟩ := pr
        by_cases hs : rs = []
        · subst hs
          simp only [undelimit_nil, decode_list_nil, Option.bind_some]
          cases hd : dec rj with
          | none => rfl
          | some lj => exact (localD_nil_right D prev lj (dec_ne_nil hj lj hd)).symm
        cases hv : undelimit rs with
        | none => simp [dec_bad hs hv]
        | some qs =>
          obtain ⟨ps, rs'⟩ := qs
          simp only [dec, dec_split hu, dec_split hv, decode_nat, Option.bind_some]
          have hlt := undelimit_lt hu
          rw [ih rj'.length hlt _ rj' rs' rfl]
          simp only [dec]
          cases h₁ : bitDecode (α := List ℕ) rj' <;> cases h₂ : bitDecode (α := List ℕ) rs' <;>
            simp [localD]

private theorem dec_eq_nil {α : Type} [MetaMathlibExt.BitstringEncoding α] {x : List Bool}
    (h : bitDecode (α := List α) x = some []) : x = [] := by
  by_contra hx
  exact dec_ne_nil hx [] h rfl

private theorem dec_eq_cons {α : Type} [MetaMathlibExt.BitstringEncoding α] {x : List Bool} {a : α}
    {l : List α} (h : bitDecode (α := List α) x = some (a :: l)) :
    ∃ p r, undelimit x = some (p, r) ∧ bitDecode (α := α) p = some a ∧
      bitDecode (α := List α) r = some l := by
  have hx : x ≠ [] := by rintro rfl; cases h
  cases hu : undelimit x with
  | none => rw [dec_bad hx hu] at h; cases h
  | some pr =>
    obtain ⟨p, r⟩ := pr
    rw [dec_split hu] at h
    cases hp : bitDecode (α := α) p <;> cases hr : bitDecode (α := List α) r <;>
      simp only [hp, hr, Option.bind_some, Option.map_some, Option.bind_none,
        Option.map_none, reduceCtorEq, Option.some.injEq, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨p, r, rfl, hp, hr⟩

private theorem iteF {c : Prop} [Decidable c] {β : Type} (a b : β) (h : ¬c) :
    (if c then a else b) = b := by simp [h]

private theorem undelimit_ne_nil {x p r : List Bool} (h : undelimit x = some (p, r)) : x ≠ [] := by
  rintro rfl; cases h

private theorem pairScan_sound : ∀ (ra sa rb sb : List Bool), pairScan ra sa rb sb = true →
    ∃ a b c d, dec ra = some a ∧ dec sa = some b ∧ dec rb = some c ∧ dec sb = some d ∧
      pairD a b c d = true := by
  intro ra
  induction h : ra.length using Nat.strong_induction_on generalizing ra with
  | _ n ih =>
    subst h
    intro sa rb sb hp
    rw [pairScan] at hp
    split_ifs at hp with hall
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := hall
      exact ⟨[], [], [], [], rfl, rfl, rfl, rfl, rfl⟩
    · split at hp
      · rename_i pla ra' psa sa' plb rb' psb sb' h₁ h₂ h₃ h₄
        simp only [Bool.and_eq_true] at hp
        obtain ⟨hc, hr⟩ := hp
        obtain ⟨a, b, c, d, ha, hb, hc', hd, hpd⟩ := ih _ (undelimit_lt h₁) ra' rfl sa' rb' sb' hr
        refine ⟨decodeNat pla :: a, decodeNat psa :: b, decodeNat plb :: c, decodeNat psb :: d,
          ?_, ?_, ?_, ?_, ?_⟩
        · simp [dec, dec_split h₁, decode_nat, ha]
        · simp [dec, dec_split h₂, decode_nat, hb]
        · simp [dec, dec_split h₃, decode_nat, hc']
        · simp [dec, dec_split h₄, decode_nat, hd]
        · simp only [pairD, hc, hpd, Bool.and_self]
      · cases hp

private theorem pairScan_complete : ∀ (a b c d : List ℕ) (ra sa rb sb : List Bool),
    dec ra = some a → dec sa = some b → dec rb = some c → dec sb = some d →
    pairD a b c d = true → pairScan ra sa rb sb = true := by
  intro a
  induction a with
  | nil =>
    intro b c d ra sa rb sb ha hb hc hd hp
    match b, c, d, hp with
    | [], [], [], _ =>
      rw [dec_eq_nil ha, dec_eq_nil hb, dec_eq_nil hc, dec_eq_nil hd, pairScan]
      simp
  | cons x a ih =>
    intro b c d ra sa rb sb ha hb hc hd hp
    match b, c, d, hp with
    | y :: b, z :: c, t :: d, hp =>
      obtain ⟨p₁, r₁, h₁, e₁, f₁⟩ := dec_eq_cons ha
      obtain ⟨p₂, r₂, h₂, e₂, f₂⟩ := dec_eq_cons hb
      obtain ⟨p₃, r₃, h₃, e₃, f₃⟩ := dec_eq_cons hc
      obtain ⟨p₄, r₄, h₄, e₄, f₄⟩ := dec_eq_cons hd
      simp only [pairD, Bool.and_eq_true] at hp
      rw [pairScan, iteF _ _ (fun h => undelimit_ne_nil h₁ h.1)]
      split
      · rename_i pla ra' psa sa' plb rb' psb sb' g₁ g₂ g₃ g₄
        rw [h₁] at g₁; rw [h₂] at g₂; rw [h₃] at g₃; rw [h₄] at g₄
        simp only [Option.some.injEq, Prod.mk.injEq] at g₁ g₂ g₃ g₄
        obtain ⟨rfl, rfl⟩ := g₁; obtain ⟨rfl, rfl⟩ := g₂
        obtain ⟨rfl, rfl⟩ := g₃; obtain ⟨rfl, rfl⟩ := g₄
        simp only [decode_nat, Option.some.injEq] at e₁ e₂ e₃ e₄
        subst e₁ e₂ e₃ e₄
        simp only [Bool.and_eq_true]
        exact ⟨hp.1, ih b c d _ _ _ _ f₁ f₂ f₃ f₄ hp.2⟩
      · rename_i hne
        exact absurd (hne _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄) id

private theorem innerScan_sound {ra sa : List Bool} {la sa' : List ℕ} (hra : dec ra = some la)
    (hsa : dec sa = some sa') : ∀ (J S : List Bool), innerScan ra sa J S = true →
    ∃ bs ts, dec2 J = some bs ∧ dec2 S = some ts ∧ innerD la sa' bs ts = true := by
  intro J
  induction h : J.length using Nat.strong_induction_on generalizing J with
  | _ n ih =>
    subst h
    intro S hp
    rw [innerScan] at hp
    split_ifs at hp with hall
    · obtain ⟨rfl, rfl⟩ := hall
      exact ⟨[], [], rfl, rfl, rfl⟩
    · split at hp
      · rename_i rb J' sb S' h₁ h₂
        simp only [Bool.and_eq_true] at hp
        obtain ⟨hpair, hr⟩ := hp
        obtain ⟨a, b, c, d, ha, hb, hc, hd, hpd⟩ := pairScan_sound ra sa rb sb hpair
        rw [hra] at ha; rw [hsa] at hb
        cases ha; cases hb
        obtain ⟨bs, ts, hJ, hS, hi⟩ := ih _ (undelimit_lt h₁) J' rfl S' hr
        refine ⟨c :: bs, d :: ts, ?_, ?_, ?_⟩
        · simp [dec2, dec_split h₁, hc, hJ]
        · simp [dec2, dec_split h₂, hd, hS]
        · simp only [innerD, hpd, hi, Bool.and_self]
      · cases hp

private theorem innerScan_complete {ra sa : List Bool} {la sa' : List ℕ} (hra : dec ra = some la)
    (hsa : dec sa = some sa') : ∀ (bs ts : List (List ℕ)) (J S : List Bool),
    dec2 J = some bs → dec2 S = some ts → innerD la sa' bs ts = true →
    innerScan ra sa J S = true := by
  intro bs
  induction bs with
  | nil =>
    intro ts J S hJ hS hi
    match ts, hi with
    | [], _ =>
      rw [dec_eq_nil hJ, dec_eq_nil hS, innerScan]
      simp
  | cons c bs ih =>
    intro ts J S hJ hS hi
    match ts, hi with
    | d :: ts, hi =>
      obtain ⟨p₁, r₁, h₁, e₁, f₁⟩ := dec_eq_cons hJ
      obtain ⟨p₂, r₂, h₂, e₂, f₂⟩ := dec_eq_cons hS
      simp only [innerD, Bool.and_eq_true] at hi
      rw [innerScan, iteF _ _ (fun h => undelimit_ne_nil h₁ h.1)]
      split
      · rename_i rb J' sb S' g₁ g₂
        rw [h₁] at g₁; rw [h₂] at g₂
        simp only [Option.some.injEq, Prod.mk.injEq] at g₁ g₂
        obtain ⟨rfl, rfl⟩ := g₁; obtain ⟨rfl, rfl⟩ := g₂
        simp only [Bool.and_eq_true]
        exact ⟨pairScan_complete _ _ _ _ _ _ _ _ hra hsa e₁ e₂ hi.1,
          ih ts _ _ f₁ f₂ hi.2⟩
      · rename_i hne
        exact absurd (hne _ _ _ _ h₁ h₂) id

private theorem localScan_some {D : ℕ} {prev : Option ℕ} {rj rs : List Bool} {k : ℕ}
    (h : localScan D prev rj rs = some k) :
    ∃ lj ls, dec rj = some lj ∧ dec rs = some ls ∧ localD D prev lj ls = some k := by
  rw [localScan_eq] at h
  cases hj : dec rj with
  | none => rw [hj] at h; cases h
  | some lj =>
    cases hs : dec rs with
    | none => rw [hj, hs] at h; cases h
    | some ls =>
      rw [hj, hs] at h
      exact ⟨lj, ls, rfl, rfl, h⟩

private theorem outerScan_sound (m D : ℕ) : ∀ (J S : List Bool), outerScan m D J S = true →
    ∃ jobs sched, dec2 J = some jobs ∧ dec2 S = some sched ∧ outerD m D jobs sched = true := by
  intro J
  induction h : J.length using Nat.strong_induction_on generalizing J with
  | _ n ih =>
    subst h
    intro S hp
    rw [outerScan] at hp
    split_ifs at hp with hall
    · obtain ⟨rfl, rfl⟩ := hall
      exact ⟨[], [], rfl, rfl, rfl⟩
    · split at hp
      · rename_i ra J' sa S' h₁ h₂
        simp only [Bool.and_eq_true, beq_iff_eq] at hp
        obtain ⟨⟨hl, hi⟩, hr⟩ := hp
        obtain ⟨la, ls, hla, hls, hloc⟩ := localScan_some hl
        obtain ⟨bs, ts, hJ, hS, hin⟩ := innerScan_sound hla hls J' S' hi
        obtain ⟨jobs, sched, hJ', hS', ho⟩ := ih _ (undelimit_lt h₁) J' rfl S' hr
        rw [hJ] at hJ'; rw [hS] at hS'
        cases hJ'; cases hS'
        refine ⟨la :: bs, ls :: ts, ?_, ?_, ?_⟩
        · simp [dec2, dec_split h₁, hla, hJ]
        · simp [dec2, dec_split h₂, hls, hS]
        · simp only [outerD, hloc, hin, ho, beq_self_eq_true, Bool.and_self]
      · cases hp

private theorem outerScan_complete (m D : ℕ) : ∀ (jobs sched : List (List ℕ)) (J S : List Bool),
    dec2 J = some jobs → dec2 S = some sched → outerD m D jobs sched = true →
    outerScan m D J S = true := by
  intro jobs
  induction jobs with
  | nil =>
    intro sched J S hJ hS ho
    match sched, ho with
    | [], _ =>
      rw [dec_eq_nil hJ, dec_eq_nil hS, outerScan]
      simp
  | cons la jobs ih =>
    intro sched J S hJ hS ho
    match sched, ho with
    | ls :: sched, ho =>
      obtain ⟨p₁, r₁, h₁, e₁, f₁⟩ := dec_eq_cons hJ
      obtain ⟨p₂, r₂, h₂, e₂, f₂⟩ := dec_eq_cons hS
      simp only [outerD, Bool.and_eq_true, beq_iff_eq] at ho
      obtain ⟨⟨hloc, hin⟩, hrest⟩ := ho
      rw [outerScan, iteF _ _ (fun h => undelimit_ne_nil h₁ h.1)]
      split
      · rename_i ra J' sa S' g₁ g₂
        rw [h₁] at g₁; rw [h₂] at g₂
        simp only [Option.some.injEq, Prod.mk.injEq] at g₁ g₂
        obtain ⟨rfl, rfl⟩ := g₁; obtain ⟨rfl, rfl⟩ := g₂
        simp only [Bool.and_eq_true, beq_iff_eq]
        refine ⟨⟨?_, innerScan_complete e₁ e₂ _ _ _ _ f₁ f₂ hin⟩, ih _ _ _ f₁ f₂ hrest⟩
        rw [localScan_eq]
        simp [dec, e₁, e₂, hloc]
      · rename_i hne
        exact absurd (hne _ _ _ _ h₁ h₂) id

private theorem decode_pair {β γ : Type} [MetaMathlibExt.BitstringEncoding β]
    [MetaMathlibExt.BitstringEncoding γ] (x : List Bool) :
    bitDecode (α := β × γ) x =
      match undelimit x with
      | none => none
      | some (block, rest) =>
        match bitDecode (α := β) block, bitDecode (α := γ) rest with
        | some a, some b => some (a, b)
        | _, _ => none := rfl

open MetaMathlibExt.Complexity.NPComplete.FlowShopScheduling in
private theorem decode_instance (x : List Bool) :
    bitDecode (α := FlowShopSchedulingInstance) x = match undelimit x with
      | none => none
      | some (M, R) => match undelimit R with
        | none => none
        | some (Jp, E) => (dec2 Jp).map fun jobs => (decodeNat M, jobs, decodeNat E) := by
  rw [decode_pair]
  cases hx : undelimit x with
  | none => rfl
  | some pr =>
    obtain ⟨M, R⟩ := pr
    dsimp only
    rw [decode_pair, decode_nat]
    cases hR : undelimit R with
    | none => rfl
    | some qr =>
      obtain ⟨Jp, E⟩ := qr
      dsimp only
      rw [decode_nat]
      simp only [dec2]
      cases bitDecode (α := List (List ℕ)) Jp <;> rfl

open MetaMathlibExt.Complexity.NPComplete.FlowShopScheduling in
theorem check_iff (x w : List Bool) :
    check x w = true ↔ ∃ m jobs D sched,
      bitDecode (α := FlowShopSchedulingInstance) x = some (m, jobs, D) ∧
      dec2 w = some sched ∧ 0 < m ∧ 0 < D ∧ outerD m D jobs sched = true := by
  rw [decode_instance]
  unfold check
  cases hx : undelimit x with
  | none => simp
  | some pr =>
    obtain ⟨M, R⟩ := pr
    dsimp only
    cases hR : undelimit R with
    | none => simp
    | some qr =>
      obtain ⟨Jp, E⟩ := qr
      dsimp only
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨⟨hM, hE⟩, ho⟩
        obtain ⟨jobs, sched, hJ, hS, hod⟩ := outerScan_sound _ _ _ _ ho
        exact ⟨_, jobs, _, sched, by simp [hJ], hS, hM, hE, hod⟩
      · rintro ⟨m, jobs, D, sched, hd, hS, hm, hD, hod⟩
        cases hJ : dec2 Jp with
        | none => rw [hJ] at hd; cases hd
        | some jobs' =>
          rw [hJ] at hd
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hd
          obtain ⟨rfl, rfl, rfl⟩ := hd
          exact ⟨⟨hm, hD⟩, outerScan_complete _ _ _ _ _ _ hJ hS hod⟩

end SpecEq

section Lists

/-! ### Index characterizations of the decoded scans -/

theorem localD_iff (D : ℕ) : ∀ (prev : Option ℕ) (lj ls : List ℕ) (k : ℕ),
    localD D prev lj ls = some k ↔ lj.length = k ∧ ls.length = k ∧
      (∀ p < k, ls.getD p 0 + lj.getD p 0 ≤ D) ∧
      (∀ p, p + 1 < k → ls.getD p 0 + lj.getD p 0 ≤ ls.getD (p + 1) 0) ∧
      (∀ v, prev = some v → 0 < k → v ≤ ls.getD 0 0) := by
  intro prev lj
  induction lj generalizing prev with
  | nil =>
    intro ls k
    cases ls with
    | nil =>
      simp only [localD, Option.some.injEq, List.length_nil]
      constructor
      · rintro rfl; refine ⟨rfl, rfl, ?_, ?_, ?_⟩ <;> intros <;> omega
      · rintro ⟨rfl, -⟩; rfl
    | cons s ss =>
      simp only [localD, reduceCtorEq, false_iff, List.length_nil, List.length_cons]
      omega
  | cons l lj ih =>
    intro ls k
    cases ls with
    | nil =>
      simp only [localD, reduceCtorEq, false_iff, List.length_nil, List.length_cons]
      omega
    | cons s ss =>
      simp only [localD]
      split_ifs with hc
      · cases k with
        | zero =>
          simp only [List.length_cons, Option.map_eq_some_iff, Nat.add_eq_zero_iff,
            one_ne_zero, and_false, exists_false, false_and]
        | succ k =>
          simp only [Option.map_eq_some_iff, Nat.add_right_cancel_iff, exists_eq_right,
            List.length_cons]
          rw [ih]
          constructor
          · rintro ⟨h₁, h₂, h₃, h₄, h₅⟩
            refine ⟨h₁, h₂, ?_, ?_, ?_⟩
            · intro p hp
              cases p with
              | zero => simpa using hc.1
              | succ p => simpa using h₃ p (by omega)
            · intro p hp
              cases p with
              | zero =>
                have := h₅ _ rfl (by omega)
                simpa using this
              | succ p => simpa using h₄ p (by omega)
            · intro v hv _
              simp only [List.getD_cons_zero]
              have := hc.2
              rw [hv] at this
              simpa using this
          · rintro ⟨h₁, h₂, h₃, h₄, h₅⟩
            refine ⟨h₁, h₂, ?_, ?_, ?_⟩
            · intro p hp; simpa using h₃ (p + 1) (by omega)
            · intro p hp; simpa using h₄ (p + 1) (by omega)
            · intro v hv hk
              cases hv
              simpa using h₄ 0 (by omega)
      · simp only [false_iff, List.length_cons]
        rintro ⟨h₁, h₂, h₃, h₄, h₅⟩
        apply hc
        refine ⟨by simpa using h₃ 0 (by omega), ?_⟩
        cases prev with
        | none => rfl
        | some v =>
          have := h₅ v rfl (by omega)
          simpa using this

theorem pairD_iff : ∀ (a b c d : List ℕ), pairD a b c d = true ↔
    b.length = a.length ∧ c.length = a.length ∧ d.length = a.length ∧
      ∀ p < a.length, b.getD p 0 + a.getD p 0 ≤ d.getD p 0 ∨
        d.getD p 0 + c.getD p 0 ≤ b.getD p 0 := by
  intro a
  induction a with
  | nil =>
    intro b c d
    cases b <;> cases c <;> cases d <;> simp [pairD]
  | cons x a ih =>
    intro b c d
    cases b with
    | nil => simp [pairD]
    | cons y b =>
      cases c with
      | nil => simp [pairD]
      | cons z c =>
        cases d with
        | nil => simp [pairD]
        | cons t d =>
          simp only [pairD, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, ih,
            List.length_cons, Nat.add_right_cancel_iff]
          constructor
          · rintro ⟨h₀, h₁, h₂, h₃, h₄⟩
            refine ⟨h₁, h₂, h₃, ?_⟩
            intro p hp
            cases p with
            | zero => simpa using h₀
            | succ p => simpa using h₄ p (by omega)
          · rintro ⟨h₁, h₂, h₃, h₄⟩
            refine ⟨by simpa using h₄ 0 (by omega), h₁, h₂, h₃, ?_⟩
            intro p hp
            simpa using h₄ (p + 1) (by omega)

theorem innerD_iff (la sa : List ℕ) : ∀ (bs ts : List (List ℕ)), innerD la sa bs ts = true ↔
    ts.length = bs.length ∧ ∀ i < bs.length, pairD la sa (bs.getD i []) (ts.getD i []) = true := by
  intro bs
  induction bs with
  | nil => intro ts; cases ts <;> simp [innerD]
  | cons b bs ih =>
    intro ts
    cases ts with
    | nil => simp [innerD]
    | cons t ts =>
      simp only [innerD, Bool.and_eq_true, ih, List.length_cons, Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨h₀, h₁, h₂⟩
        refine ⟨h₁, ?_⟩
        intro i hi
        cases i with
        | zero => simpa using h₀
        | succ i => simpa using h₂ i (by omega)
      · rintro ⟨h₁, h₂⟩
        refine ⟨by simpa using h₂ 0 (by omega), h₁, ?_⟩
        intro i hi
        simpa using h₂ (i + 1) (by omega)

theorem outerD_iff (m D : ℕ) : ∀ (jobs sched : List (List ℕ)), outerD m D jobs sched = true ↔
    sched.length = jobs.length ∧
      (∀ j < jobs.length, localD D none (jobs.getD j []) (sched.getD j []) = some m) ∧
      ∀ j k, j < k → k < jobs.length →
        pairD (jobs.getD j []) (sched.getD j []) (jobs.getD k []) (sched.getD k []) = true := by
  intro jobs
  induction jobs with
  | nil => intro sched; cases sched <;> simp [outerD]
  | cons a jobs ih =>
    intro sched
    cases sched with
    | nil => simp [outerD]
    | cons s sched =>
      simp only [outerD, Bool.and_eq_true, beq_iff_eq, ih, innerD_iff, List.length_cons,
        Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨⟨hloc, -, hin⟩, hlen, hl, hp⟩
        refine ⟨hlen, ?_, ?_⟩
        · intro j hj
          cases j with
          | zero => simpa using hloc
          | succ j => simpa using hl j (by omega)
        · intro j k hjk hk
          cases j with
          | zero =>
            cases k with
            | zero => omega
            | succ k => simpa using hin k (by omega)
          | succ j =>
            cases k with
            | zero => omega
            | succ k => simpa using hp j k (by omega) (by omega)
      · rintro ⟨hlen, hl, hp⟩
        refine ⟨⟨by simpa using hl 0 (by omega), hlen, ?_⟩, hlen, ?_, ?_⟩
        · intro i hi
          simpa using hp 0 (i + 1) (by omega) (by omega)
        · intro j hj
          simpa using hl (j + 1) (by omega)
        · intro j k hjk hk
          simpa using hp (j + 1) (k + 1) (by omega) (by omega)

end Lists

section Correct

/-! ### The raw verifier `check` certifies exactly the feasible well-formed instances -/

open MetaMathlibExt.BitstringEncoding MetaMathlibExt.Complexity.NPComplete.FlowShopScheduling

/-! ### Schedule rows and the certificate length bound -/

private def scheduleRows (i : FlowShopSchedulingInstance)
    (σ : Fin i.1 → Fin i.2.1.length → ℕ) : List (List ℕ) :=
  List.ofFn fun j => List.ofFn fun p => σ p j

private theorem scheduleRows_getD (i : FlowShopSchedulingInstance)
    (σ : Fin i.1 → Fin i.2.1.length → ℕ) (p : Fin i.1) (j : Fin i.2.1.length) :
    ((scheduleRows i σ).getD j []).getD p 0 = σ p j := by
  simp [scheduleRows, p.isLt, j.isLt]

private theorem feasible_iff_rows (i : FlowShopSchedulingInstance) :
    FlowShopSchedulingFeasible i ↔
      ∃ s : List (List ℕ), s.length = i.2.1.length ∧
        (∀ row ∈ s, row.length = i.1) ∧
        (∀ (p : Fin i.1) (j : Fin i.2.1.length),
          (s.getD j []).getD p 0 + len i p j ≤ i.2.2) ∧
        (∀ (p : Fin i.1) (j k : Fin i.2.1.length), j ≠ k →
          (s.getD j []).getD p 0 + len i p j ≤ (s.getD k []).getD p 0 ∨
          (s.getD k []).getD p 0 + len i p k ≤ (s.getD j []).getD p 0) ∧
        ∀ (p : Fin i.1) (_hp : p.1 + 1 < i.1) (j : Fin i.2.1.length),
          (s.getD j []).getD p 0 + len i p j ≤
            (s.getD j []).getD (p.1 + 1) 0 := by
  constructor
  · rintro ⟨σ, hd, hs, hp⟩
    refine ⟨scheduleRows i σ, List.length_ofFn, ?_, ?_, ?_, ?_⟩
    · intro row hr
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hr
      exact List.length_ofFn
    · simpa only [scheduleRows_getD] using hd
    · simpa only [scheduleRows_getD] using hs
    · intro p h j
      rw [scheduleRows_getD, scheduleRows_getD i σ ⟨p.1 + 1, h⟩ j]
      exact hp p h j
  · rintro ⟨s, _, _, hd, hs, hp⟩
    exact ⟨fun p j => (s.getD j []).getD p 0, hd, hs, hp⟩

private theorem rows_encode_length_le (rows : List (List ℕ)) (m n : ℕ)
    (hrows : ∀ row ∈ rows, row.length = m)
    (h : ∀ row ∈ rows, ∀ t ∈ row, t.size ≤ n) :
    (bitEncode rows).length ≤ rows.length * (2 * (m * (2 * n + 1)) + 1) := by
  induction rows with
  | nil => change 0 ≤ 0 * _; simp
  | cons row rows ih =>
    have hr := Cslib.Complexity.PolynomialEncoding.list_nat_encode_length_le row n
      (h row (by simp))
    rw [hrows row (by simp)] at hr
    have ht := ih (fun r hr => hrows r (by simp [hr]))
      (fun r hr => h r (by simp [hr]))
    change (delimit (bitEncode row) ++ bitEncode rows).length ≤ _
    simp only [List.length_append, length_delimit, List.length_cons, Nat.add_mul]
    omega

private theorem scheduleRows_encode_length_le (i : FlowShopSchedulingInstance)
    (σ : Fin i.1 → Fin i.2.1.length → ℕ)
    (h : ∀ p j, σ p j + len i p j ≤ i.2.2) :
    (bitEncode (scheduleRows i σ)).length ≤
      i.2.1.length * (2 * (i.1 * (2 * i.2.2.size + 1)) + 1) := by
  have hl : (scheduleRows i σ).length = i.2.1.length := List.length_ofFn
  rw [← hl]
  apply rows_encode_length_le
  · intro row hr
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hr
    exact List.length_ofFn
  · intro row hr t ht
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hr
    obtain ⟨p, rfl⟩ := List.mem_ofFn.mp ht
    apply Nat.size_le_size
    have hd := h p j
    omega

private theorem decoded_rows_mapM_length_le (blocks : List (List Bool))
    (rows : List (List ℕ)) (h : blocks.mapM bitDecode = some rows) :
    (bitEncode rows).length ≤ 3 * ((blocks.map delimit).flatten).length := by
  induction blocks generalizing rows with
  | nil =>
    have he : rows = [] := by simpa using h.symm
    subst rows
    change 0 ≤ 3 * 0
    simp
  | cons p blocks ih =>
    cases hp : bitDecode (α := List ℕ) p with
    | none => simp [List.mapM_cons, hp] at h
    | some row =>
      cases ht : blocks.mapM (bitDecode (α := List ℕ)) with
      | none => simp [List.mapM_cons, hp, ht] at h
      | some tail =>
        have he : row :: tail = rows := by simpa [List.mapM_cons, hp, ht] using h
        subst rows
        have hr := Cslib.Complexity.PolynomialEncoding.decoded_list_nat_encode_length_le hp
        have hl := ih tail ht
        change (delimit (bitEncode row) ++ bitEncode tail).length ≤ _
        simp only [List.map_cons, List.flatten_cons, List.length_append, length_delimit]
        omega

private theorem decoded_rows_encode_length_le {x : List Bool} {rows : List (List ℕ)}
    (h : bitDecode x = some rows) : (bitEncode rows).length ≤ 3 * x.length := by
  change (undelimitBlocks x).bind (List.mapM bitDecode) = _ at h
  obtain ⟨blocks, hb, hr⟩ := Option.bind_eq_some_iff.mp h
  rw [Cslib.Complexity.PolynomialEncoding.blocks_decode_sound hb]
  exact decoded_rows_mapM_length_le blocks rows hr

private theorem decoded_instance_bounds {x : List Bool} {i : FlowShopSchedulingInstance}
    (h : bitDecode x = some i) :
    (bitEncode i.2.1).length ≤ 3 * x.length ∧ i.2.2.size ≤ x.length := by
  obtain ⟨p, r, rfl, _, hr⟩ := Cslib.Complexity.PolynomialEncoding.decoded_pair_parts h
  obtain ⟨q, d, rfl, hq, hd⟩ := Cslib.Complexity.PolynomialEncoding.decoded_pair_parts hr
  have hrows := decoded_rows_encode_length_le hq
  change some (Computability.decodeNat d) = some i.2.2 at hd
  have hn := Option.some.inj hd
  have hs := Cslib.Complexity.FramedCNF.length_normalizeNat_le d
  rw [Cslib.Complexity.FramedCNF.normalizeNat_eq_encode_decode, hn,
    MetaMathlibExt.BinaryNatEncoding.length_encodeNat] at hs
  constructor
  · exact hrows.trans (by simp only [List.length_append, length_delimit]; omega)
  · exact hs.trans (by simp only [List.length_append, length_delimit]; omega)

private theorem rows_encode_length_lower (rows : List (List ℕ)) (m : ℕ)
    (h : ∀ row ∈ rows, row.length = m) :
    rows.length * (2 * m + 1) ≤ (bitEncode rows).length := by
  induction rows with
  | nil => change 0 * _ ≤ 0; simp
  | cons row rows ih =>
    have hr : m ≤ (bitEncode row).length := by
      rw [← h row (by simp)]
      exact Cslib.Complexity.PolynomialEncoding.decoded_list_length_le
        (bitDecode_bitEncode row)
    have ht := ih (fun r hr => h r (by simp [hr]))
    change (rows.length + 1) * (2 * m + 1) ≤
      (delimit (bitEncode row) ++ bitEncode rows).length
    simp only [List.length_append, length_delimit, Nat.add_mul, Nat.one_mul]
    omega

private theorem scheduleRows_polynomial_bound {x : List Bool} {i : FlowShopSchedulingInstance}
    (hx : bitDecode x = some i) (hw : WellFormed i)
    (σ : Fin i.1 → Fin i.2.1.length → ℕ)
    (hσ : ∀ p j, σ p j + len i p j ≤ i.2.2) :
    (bitEncode (scheduleRows i σ)).length ≤ 3 * x.length * (2 * x.length + 1) := by
  have hc : 2 * (i.1 * (2 * i.2.2.size + 1)) + 1 ≤
      (2 * i.1 + 1) * (2 * i.2.2.size + 1) := by
    ring_nf
    omega
  have hr := rows_encode_length_lower i.2.1 i.1 hw.2.1
  obtain ⟨hj, hd⟩ := decoded_instance_bounds hx
  calc
    (bitEncode (scheduleRows i σ)).length ≤
        i.2.1.length * (2 * (i.1 * (2 * i.2.2.size + 1)) + 1) :=
      scheduleRows_encode_length_le i σ hσ
    _ ≤ i.2.1.length * ((2 * i.1 + 1) * (2 * i.2.2.size + 1)) :=
      Nat.mul_le_mul_left _ hc
    _ = (i.2.1.length * (2 * i.1 + 1)) * (2 * i.2.2.size + 1) :=
      (Nat.mul_assoc _ _ _).symm
    _ ≤ (bitEncode i.2.1).length * (2 * i.2.2.size + 1) := Nat.mul_le_mul_right _ hr
    _ ≤ (3 * x.length) * (2 * x.length + 1) := Nat.mul_le_mul hj (by omega)

/-! ### Decoded rows versus feasibility -/

private theorem getD_mem {α : Type} {l : List α} {i : ℕ} {d : α} (h : i < l.length) :
    l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

private theorem accept_of_feasible {m D : ℕ} {jobs : List (List ℕ)}
    (hw : WellFormed (m, jobs, D)) (s : List (List ℕ)) (hs : s.length = jobs.length)
    (hrows : ∀ row ∈ s, row.length = m)
    (hd : ∀ (p : Fin m) (j : Fin jobs.length),
      (s.getD j []).getD p 0 + (jobs.getD j []).getD p 0 ≤ D)
    (hsep : ∀ (p : Fin m) (j k : Fin jobs.length), j ≠ k →
      (s.getD j []).getD p 0 + (jobs.getD j []).getD p 0 ≤ (s.getD k []).getD p 0 ∨
      (s.getD k []).getD p 0 + (jobs.getD k []).getD p 0 ≤ (s.getD j []).getD p 0)
    (hp : ∀ (p : Fin m) (_hp : p.1 + 1 < m) (j : Fin jobs.length),
      (s.getD j []).getD p 0 + (jobs.getD j []).getD p 0 ≤ (s.getD j []).getD (p.1 + 1) 0) :
    outerD m D jobs s = true := by
  have hjl : ∀ i < jobs.length, (jobs.getD i []).length = m :=
    fun i hi => hw.2.1 _ (getD_mem (l := jobs) hi)
  rw [outerD_iff]
  refine ⟨hs, ?_, ?_⟩
  · intro j hj
    rw [localD_iff]
    refine ⟨hjl j hj, hrows _ (getD_mem (by omega)), ?_, ?_, ?_⟩
    · intro p hp'; exact hd ⟨p, hp'⟩ ⟨j, hj⟩
    · intro p hp'; exact hp ⟨p, by omega⟩ hp' ⟨j, hj⟩
    · intro v hv; cases hv
  · intro j k hjk hk
    rw [pairD_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hrows _ (getD_mem (by omega)), hjl j (by omega)]
    · rw [hjl j (by omega), hjl k hk]
    · rw [hrows _ (getD_mem (by omega)), hjl j (by omega)]
    · intro p hp'
      rw [hjl j (by omega)] at hp'
      exact hsep ⟨p, hp'⟩ ⟨j, by omega⟩ ⟨k, hk⟩ (fun h => by
        have := congrArg Fin.val h; simp at this; omega)

/-- **Certificate characterization of the decision problem.** -/
theorem dec_iff_check (x : List Bool) :
    flowShopSchedulingDec x = true ↔
      ∃ w : List Bool, w.length ≤ 3 * x.length * (2 * x.length + 1) ∧ check x w = true := by
  constructor
  · intro hx
    unfold flowShopSchedulingDec at hx
    cases hdec : bitDecode (α := FlowShopSchedulingInstance) x with
    | none => rw [hdec] at hx; cases hx
    | some i =>
      obtain ⟨m, jobs, D⟩ := i
      rw [hdec] at hx
      simp only [decide_eq_true_eq] at hx
      obtain ⟨hw, hf⟩ := hx
      obtain ⟨σ, hd, hs, hp⟩ := hf
      refine ⟨bitEncode (scheduleRows (m, jobs, D) σ),
        scheduleRows_polynomial_bound hdec hw σ hd, ?_⟩
      rw [check_iff]
      refine ⟨m, jobs, D, scheduleRows (m, jobs, D) σ, hdec, bitDecode_bitEncode _, hw.1,
        hw.2.2, ?_⟩
      have hrows := (feasible_iff_rows (m, jobs, D)).mp ⟨σ, hd, hs, hp⟩
      obtain ⟨s, hsl, hsr, hsd, hss, hsp⟩ := hrows
      refine accept_of_feasible hw _ List.length_ofFn ?_ ?_ ?_ ?_
      · intro row hr
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hr
        exact List.length_ofFn
      · intro p j
        rw [scheduleRows_getD (m, jobs, D) σ p j]
        exact hd p j
      · intro p j k hjk
        rw [scheduleRows_getD (m, jobs, D) σ p j, scheduleRows_getD (m, jobs, D) σ p k]
        exact hs p j k hjk
      · intro p hp' j
        rw [scheduleRows_getD (m, jobs, D) σ p j,
          scheduleRows_getD (m, jobs, D) σ ⟨p.1 + 1, hp'⟩ j]
        exact hp p hp' j
  · rintro ⟨w, -, hc⟩
    rw [check_iff] at hc
    obtain ⟨m, jobs, D, sched, hdec, hw, hm, hD, ho⟩ := hc
    rw [outerD_iff] at ho
    obtain ⟨hlen, hloc, hpair⟩ := ho
    have hloc' := fun j hj => (localD_iff D none _ _ m).mp (hloc j hj)
    unfold flowShopSchedulingDec
    rw [hdec]
    simp only [decide_eq_true_eq]
    have hwf : WellFormed (m, jobs, D) := by
      refine ⟨hm, ?_, hD⟩
      intro job hj
      obtain ⟨j, hj', rfl⟩ := List.mem_iff_getElem.mp hj
      have := (hloc' j hj').1
      rwa [List.getD_eq_getElem _ _ hj'] at this
    refine ⟨hwf, (feasible_iff_rows (m, jobs, D)).mpr ⟨sched, hlen, ?_, ?_, ?_, ?_⟩⟩
    · intro row hr
      obtain ⟨j, hj', rfl⟩ := List.mem_iff_getElem.mp hr
      have := (hloc' j (by omega)).2.1
      rwa [List.getD_eq_getElem _ _ hj'] at this
    · intro p j
      exact (hloc' j j.isLt).2.2.1 p p.isLt
    · intro p j k hjk
      have hne : j.1 ≠ k.1 := fun h => hjk (Fin.ext h)
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · have := (pairD_iff _ _ _ _).mp (hpair j k hlt k.isLt)
        have hl : (jobs.getD j []).length = m := hwf.2.1 _ (getD_mem j.isLt)
        exact this.2.2.2 p (by rw [hl]; exact p.isLt)
      · have := (pairD_iff _ _ _ _).mp (hpair k j hgt j.isLt)
        have hl : (jobs.getD k []).length = m := hwf.2.1 _ (getD_mem k.isLt)
        exact (this.2.2.2 p (by rw [hl]; exact p.isLt)).symm
    · intro p hp' j
      exact (hloc' j j.isLt).2.2.2.1 p hp'

end Correct

section Arith

/-! ### Bit-serial comparison and increment

`Compare` is the three-machine verifier's comparison kernel, copied verbatim (it is private
there): it decides `value a + value b ≤ value c` least significant bit first and restores its
operands. `Incr` adds one to a least-significant-bit-first counter.
-/

open MetaMathlibExt

namespace Compare

open Turing Function TM2Program Computability

private def value : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * value bs

private theorem value_step (xs : List Bool) :
    value xs = (xs.headD false).toNat + 2 * value xs.tail := by
  cases xs <;> rfl

private theorem value_encodeNat (n : ℕ) : value (encodeNat n) = n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hn : n = 0
    · subst n
      rfl
    · rw [TM2Recursive.encodeNat_eq_cons hn, value, ih (n / 2) (by omega)]
      by_cases hp : n % 2 = 1 <;> simp [hp] <;> omega

private def borrow (q : Fin 3) (a b c : Bool) : Fin 3 :=
  ⟨(a.toNat + b.toNat + q.val + 1 - c.toNat) / 2, by
    have ha : a.toNat ≤ 1 := by cases a <;> decide
    have hb : b.toNat ≤ 1 := by cases b <;> decide
    have hq := q.isLt
    omega⟩

private theorem borrow_step (q : Fin 3) (a b c : List Bool) :
    value a + value b + q.val ≤ value c ↔
      value a.tail + value b.tail +
        (borrow q (a.headD false) (b.headD false) (c.headD false)).val ≤ value c.tail := by
  nth_rw 1 [value_step a, value_step b, value_step c]
  have hnat : (c.headD false).toNat ≤ 1 := by cases c.headD false <;> decide
  change _ ↔ _ + (_ + _ + q.val + 1 - _) / 2 ≤ _
  omega

private inductive K | a | b | c | ar | br | cr
  deriving DecidableEq

private inductive Lab | compare (q : Fin 3) | restoreA (res : Bool)
  | restoreB (res : Bool) | restoreC (res : Bool) | done (res : Bool)
  deriving DecidableEq, Fintype

private abbrev Stmt := TM2.Stmt (fun _ : K => Bool) Lab Bool

private def readBit (k t : K) (f : Bool → Stmt) : Stmt :=
  .peek k (fun _ o => o.isNone) <| .branch id (f false)
    (.pop k (fun _ o => o.getD false) <| .push t id <| .branch id (f true) (f false))

private def stepBits (q : Fin 3) : Stmt :=
  readBit .a .ar fun a => readBit .b .br fun b => readBit .c .cr fun c =>
    .goto fun _ => .compare (borrow q a b c)

private def prog : Lab → Stmt
  | .compare q =>
    .peek .a (fun _ o => o.isNone) <| .branch id
      (.peek .b (fun _ o => o.isNone) <| .branch id
        (.peek .c (fun _ o => o.isNone) <| .branch id
          (.goto fun _ => .restoreA (decide (q.val = 0))) (stepBits q))
        (stepBits q))
      (stepBits q)
  | .restoreA res => moveB .ar .a some id (.restoreA res) (.restoreB res)
  | .restoreB res => moveB .br .b some id (.restoreB res) (.restoreC res)
  | .restoreC res => moveB .cr .c some id (.restoreC res) (.done res)
  | .done _ => .halt

private def st (a b c ar br cr : List Bool) : K → List Bool
  | .a => a
  | .b => b
  | .c => c
  | .ar => ar
  | .br => br
  | .cr => cr

private def pushHead (xs ys : List Bool) : List Bool :=
  match xs with
  | [] => ys
  | b :: _ => b :: ys

private theorem tail_measure (a b c : List Bool)
    (h : a ≠ [] ∨ b ≠ [] ∨ c ≠ []) :
    a.tail.length + b.tail.length + c.tail.length < a.length + b.length + c.length := by
  cases a <;> cases b <;> cases c <;> simp at h ⊢ <;> omega

private theorem comparison_step (q : Fin 3) (a b c ar br cr : List Bool) (v : Bool)
    (h : a ≠ [] ∨ b ≠ [] ∨ c ≠ []) :
    ∃ v', TM2.step prog ⟨some (.compare q), v, st a b c ar br cr⟩ =
      some ⟨some (.compare (borrow q (a.headD false) (b.headD false) (c.headD false))),
        v', st a.tail b.tail c.tail (pushHead a ar) (pushHead b br) (pushHead c cr)⟩ := by
  refine ⟨c.headD true, ?_⟩
  rcases a with _ | ⟨_ | _, _⟩ <;> rcases b with _ | ⟨_ | _, _⟩ <;>
    rcases c with _ | ⟨_ | _, _⟩
  case nil.nil.nil => simp at h
  all_goals
    apply congrArg some
    apply congrArg (TM2.Cfg.mk _ _)
    funext k
    cases k <;> rfl

private theorem reverse_append_pushHead (xs ys : List Bool) :
    xs.tail.reverse ++ pushHead xs ys = xs.reverse ++ ys := by
  cases xs <;> simp [pushHead, List.reverse_cons, List.append_assoc]

private theorem comparison_run (q : Fin 3) (a b c ar br cr : List Bool) (v : Bool) :
    ∃ v', RunLe prog (a.length + b.length + c.length + 1)
      ⟨some (.compare q), v, st a b c ar br cr⟩
      ⟨some (.restoreA (decide (value a + value b + q.val ≤ value c))), v',
        st [] [] [] (a.reverse ++ ar) (b.reverse ++ br) (c.reverse ++ cr)⟩ := by
  by_cases h : a ≠ [] ∨ b ≠ [] ∨ c ≠ []
  · obtain ⟨v', hs⟩ := comparison_step q a b c ar br cr v h
    have hr := comparison_run
      (borrow q (a.headD false) (b.headD false) (c.headD false))
      a.tail b.tail c.tail (pushHead a ar) (pushHead b br) (pushHead c cr) v'
    simp only [← decide_eq_decide.mpr (borrow_step q a b c), reverse_append_pushHead] at hr
    obtain ⟨v'', hr⟩ := hr
    refine ⟨v'', ((Run.head hs (Run.zero _)).le le_rfl |>.trans hr).mono ?_⟩
    have hm := tail_measure a b c h
    omega
  · push Not at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    change ∃ v', RunLe prog 1 ⟨some (.compare q), v, st [] [] [] ar br cr⟩
        ⟨some (.restoreA (decide (0 + 0 + q.val ≤ 0))), v', st [] [] [] ar br cr⟩
    refine ⟨true, (Run.single ?_).le le_rfl⟩
    simp [prog, TM2.stepAux, st]
termination_by a.length + b.length + c.length
decreasing_by exact tail_measure a b c h

private theorem restore_run (a b c : List Bool) (v : Bool) (res : Bool) :
    ∃ v', Run prog (a.length + b.length + c.length + 3)
      ⟨some (.restoreA res), v, st [] [] [] a.reverse b.reverse c.reverse⟩
      ⟨some (.done res), v', st a b c [] [] []⟩ := by
  obtain ⟨v₁, u₁, h₁, ha₁, ha₂, ha₃⟩ := moveB_run (M := prog)
    (self := .restoreA res) (next := .restoreB res) (a := .ar) (b := .a) (d := some) (g := id)
    rfl (by decide) a.reverse a.reverse [] v (st [] [] [] a.reverse b.reverse c.reverse)
    (by simp [st]) (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  have he₁ : u₁ = st a [] [] [] b.reverse c.reverse := by
    funext k
    cases k
    case a => simpa [st] using ha₂
    case ar => exact ha₁
    all_goals exact ha₃ _ (by decide) (by decide)
  rw [he₁, List.length_reverse] at h₁
  obtain ⟨v₂, u₂, h₂, hb₁, hb₂, hb₃⟩ := moveB_run (M := prog)
    (self := .restoreB res) (next := .restoreC res) (a := .br) (b := .b) (d := some) (g := id)
    rfl (by decide) b.reverse b.reverse [] v₁ (st a [] [] [] b.reverse c.reverse)
    (by simp [st]) (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  have he₂ : u₂ = st a b [] [] [] c.reverse := by
    funext k
    cases k
    case b => simpa [st] using hb₂
    case br => exact hb₁
    all_goals exact hb₃ _ (by decide) (by decide)
  rw [he₂, List.length_reverse] at h₂
  obtain ⟨v₃, u₃, h₃, hc₁, hc₂, hc₃⟩ := moveB_run (M := prog)
    (self := .restoreC res) (next := .done res) (a := .cr) (b := .c) (d := some) (g := id)
    rfl (by decide) c.reverse c.reverse [] v₂ (st a b [] [] [] c.reverse)
    (by simp [st]) (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  have he₃ : u₃ = st a b c [] [] [] := by
    funext k
    cases k
    case c => simpa [st] using hc₂
    case cr => exact hc₁
    all_goals exact hc₃ _ (by decide) (by decide)
  rw [he₃, List.length_reverse] at h₃
  exact ⟨v₃, ((h₁.trans h₂).trans h₃).of_eq (by omega)⟩

private theorem run (a b c : ℕ) (v : Bool) :
    let x := encodeNat a
    let y := encodeNat b
    let z := encodeNat c
    ∃ v', RunLe prog (2 * (x.length + y.length + z.length) + 4)
      ⟨some (.compare 0), v, st x y z [] [] []⟩
      ⟨some (.done (decide (a + b ≤ c))), v', st x y z [] [] []⟩ := by
  intro x y z
  obtain ⟨v₁, h₁⟩ := comparison_run 0 x y z [] [] [] v
  have h₁' : RunLe prog (x.length + y.length + z.length + 1)
      ⟨some (.compare 0), v, st x y z [] [] []⟩
      ⟨some (.restoreA (decide (a + b ≤ c))), v₁, st [] [] [] x.reverse y.reverse z.reverse⟩ := by
    simpa [x, y, z, value_encodeNat] using h₁
  obtain ⟨v₂, h₂⟩ := restore_run x y z v₁ (decide (a + b ≤ c))
  exact ⟨v₂, (h₁'.trans (h₂.le le_rfl)).mono (by omega)⟩

private theorem run_value (x y z : List Bool) (v : Bool) :
    ∃ v', RunLe prog (2 * (x.length + y.length + z.length) + 4)
      ⟨some (.compare 0), v, st x y z [] [] []⟩
      ⟨some (.done (decide (value x + value y ≤ value z))), v', st x y z [] [] []⟩ := by
  obtain ⟨v₁, h₁⟩ := comparison_run 0 x y z [] [] [] v
  have h₁' : RunLe prog (x.length + y.length + z.length + 1)
      ⟨some (.compare 0), v, st x y z [] [] []⟩
      ⟨some (.restoreA (decide (value x + value y ≤ value z))), v₁,
        st [] [] [] x.reverse y.reverse z.reverse⟩ := by
    simpa using h₁
  obtain ⟨v₂, h₂⟩ := restore_run x y z v₁ (decide (value x + value y ≤ value z))
  exact ⟨v₂, (h₁'.trans (h₂.le le_rfl)).mono (by omega)⟩

end Compare

/-! ## Increment -/

namespace Incr

open Turing Function TM2Program Computability

/-- Least-significant-bit-first increment. -/
private def incrBits : List Bool → List Bool
  | [] => [true]
  | true :: r => false :: incrBits r
  | false :: r => true :: r

private theorem value_incrBits : ∀ c, Compare.value (incrBits c) = Compare.value c + 1
  | [] => rfl
  | true :: r => by
    simp only [incrBits, Compare.value, value_incrBits r, Bool.toNat_true, Bool.toNat_false]
    omega
  | false :: r => by
    simp only [incrBits, Compare.value, Bool.toNat_true, Bool.toNat_false]
    omega

private theorem length_incrBits : ∀ c, (incrBits c).length ≤ c.length + 1
  | [] => le_rfl
  | true :: r => by simp only [incrBits, List.length_cons]; have := length_incrBits r; omega
  | false :: r => by simp [incrBits]

private inductive K | c | t
  deriving DecidableEq

private inductive Lab | carry | back | done
  deriving DecidableEq

private instance : Fintype Lab :=
  Fintype.ofList [.carry, .back, .done] (fun l => by cases l <;> decide)

private abbrev Stmt := TM2.Stmt (fun _ : K => Bool) Lab Bool

private def prog : Lab → Stmt
  | .carry =>
    .peek .c (fun _ o => o.isNone) <| .branch id
      (.push .t (fun _ => true) <| .goto fun _ => .back)
      (.pop .c (fun _ o => o.getD false) <| .branch id
        (.push .t (fun _ => false) <| .goto fun _ => .carry)
        (.push .t (fun _ => true) <| .goto fun _ => .back))
  | .back => moveB .t .c some id .back .done
  | .done => .halt

private def st (c t : List Bool) : K → List Bool
  | .c => c
  | .t => t

private theorem carry_run : ∀ (c t : List Bool) (v : Bool), ∃ v' c' t',
    RunLe prog (c.length + 1) ⟨some .carry, v, st c t⟩ ⟨some .back, v', st c' t'⟩ ∧
      t'.reverse ++ c' = t.reverse ++ incrBits c ∧ t'.length ≤ t.length + c.length + 1
  | [], t, v => by
    refine ⟨true, [], true :: t, (Run.single ?_).le le_rfl, by simp [incrBits], by simp⟩
    simp only [prog, TM2.stepAux, st, List.head?_nil, Option.isNone_none, id_eq,
      Option.getD_none, List.tail_nil, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne,
      cond_eq_ite, Bool.false_eq_true, ↓reduceIte, TM2.Cfg.mk.injEq, true_and]
    funext k; cases k <;> rfl
  | false :: r, t, v => by
    refine ⟨false, r, true :: t, (Run.single ?_).le (by simp), by simp [incrBits], by simp⟩
    simp only [prog, TM2.stepAux, st, List.head?_cons, Option.isNone_some, id_eq,
      Option.getD_some, List.tail_cons, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne,
      cond_eq_ite, Bool.false_eq_true, ↓reduceIte, TM2.Cfg.mk.injEq, true_and]
    funext k; cases k <;> rfl
  | true :: r, t, v => by
    obtain ⟨v', c', t', h, he, hl⟩ := carry_run r (false :: t) true
    have hs : TM2.step prog ⟨some .carry, v, st (true :: r) t⟩ =
        some ⟨some .carry, true, st r (false :: t)⟩ := by
      simp only [TM2.step.eq_2, prog, TM2.stepAux, st, List.head?_cons, Option.isNone_some,
        id_eq, Option.getD_some, List.tail_cons, ne_eq, reduceCtorEq, not_false_eq_true,
        update_of_ne, cond_eq_ite, ↓reduceIte, Bool.false_eq_true, Option.some.injEq,
        TM2.Cfg.mk.injEq, true_and]
      funext k; cases k <;> rfl
    refine ⟨v', c', t', ((Run.head hs (Run.zero _)).le le_rfl |>.trans h).mono (by simp; omega),
      ?_, ?_⟩
    · rw [he]; simp [incrBits]
    · simp only [List.length_cons] at hl ⊢; omega

private theorem run (c : List Bool) (v : Bool) :
    ∃ v', RunLe prog (2 * c.length + 4) ⟨some .carry, v, st c []⟩
      ⟨some .done, v', st (incrBits c) []⟩ := by
  obtain ⟨v₁, c', t', h₁, he, hl⟩ := carry_run c [] v
  obtain ⟨v₂, u, h₂, ht, hc, -⟩ := moveB_run (M := prog)
    (self := .back) (next := .done) (a := .t) (b := .c) (d := some) (g := id)
    rfl (by decide) t' t' [] v₁ (st c' t') (by simp [st]) (by simp [IsBitBlock])
    (by simp [EndsBitBlock])
  have hu : u = st (incrBits c) [] := by
    funext k
    cases k
    · simp only [st] at hc ⊢
      rw [hc]
      simpa using he
    · exact ht
  rw [hu] at h₂
  exact ⟨v₂, (h₁.trans (h₂.le le_rfl)).mono (by simp at hl; omega)⟩

end Incr

end Arith

section Machine

/-! ### The general flow-shop verifier machine

A finite multi-stack machine over bits. It splits the instance into its three fields,
normalizes `m` and `D`, then runs the outer loop over job rows: a local column scan of the job
row against its schedule row (deadline, processor order, column count against `m`), and an
inner loop comparing the job against every later job column by column.
-/

open MetaMathlibExt
open Turing Function TM2Program TM2Embedding Cslib.Complexity.PolynomialEncoding

private inductive K
  | raw | mraw | mn | dd | jobsO | schedO | jobsI | schedI | rowJ | rowS | rowJb | rowSb
  | wJ | wS | lA | sA | lB | sB | prevL | prevS | cnt | zero
  | payload | splitTemp | normTemp | copyTemp | cmpA | cmpB | cmpC | incrTemp
  deriving DecidableEq

private def keys : List K :=
  [.raw, .mraw, .mn, .dd, .jobsO, .schedO, .jobsI, .schedI, .rowJ, .rowS, .rowJb, .rowSb,
    .wJ, .wS, .lA, .sA, .lB, .sB, .prevL, .prevS, .cnt, .zero,
    .payload, .splitTemp, .normTemp, .copyTemp, .cmpA, .cmpB, .cmpC, .incrTemp]

private theorem mem_keys (k : K) : k ∈ keys := by cases k <;> decide

private instance : Fintype K := Fintype.ofList keys mem_keys

/-- Number reading sites: which row stack feeds which number stack. -/
private inductive NumSite | locJ | locS | parJ | parS | parJb | parSb
  deriving DecidableEq

private instance : Fintype NumSite :=
  Fintype.ofList [.locJ, .locS, .parJ, .parS, .parJb, .parSb] (fun s => by cases s <;> decide)

private inductive SplitSite | top1 | top2 | outJ | outS | inJ | inS | num (r : NumSite)
  deriving DecidableEq

private instance : Fintype SplitSite :=
  Fintype.ofList ([.top1, .top2, .outJ, .outS, .inJ, .inS] ++
      [NumSite.locJ, .locS, .parJ, .parS, .parJb, .parSb].map .num)
    (fun s => by cases s with
      | num r => cases r <;> decide
      | _ => decide)

private inductive NormSite | dd | mn | num (r : NumSite)
  deriving DecidableEq

private instance : Fintype NormSite :=
  Fintype.ofList ([.dd, .mn] ++ [NumSite.locJ, .locS, .parJ, .parS, .parJb, .parSb].map .num)
    (fun s => by cases s with
      | num r => cases r <;> decide
      | _ => decide)

private inductive CmpSite | deadline | prec | ab | ba | cntLe | cntGe
  deriving DecidableEq

private instance : Fintype CmpSite :=
  Fintype.ofList [.deadline, .prec, .ab, .ba, .cntLe, .cntGe] (fun s => by cases s <;> decide)

private inductive CopySite | locJ | locS | inJ | inS | parJ | parS
  deriving DecidableEq

private instance : Fintype CopySite :=
  Fintype.ofList [.locJ, .locS, .inJ, .inS, .parJ, .parS] (fun s => by cases s <;> decide)

private inductive MoveSite | len | start
  deriving DecidableEq

private instance : Fintype MoveSite :=
  Fintype.ofList [.len, .start] (fun s => by cases s <;> decide)

private inductive CleanSite | prev | locEnd | col | innerEnd
  deriving DecidableEq

private instance : Fintype CleanSite :=
  Fintype.ofList [.prev, .locEnd, .col, .innerEnd] (fun s => by cases s <;> decide)

private inductive Lab
  | split (s : SplitSite) (l : PairSplit.Lab)
  | norm (s : NormSite) (l : Cslib.Complexity.FramedCNF.NormalizeMachine.Lab)
  | cmp (s : CmpSite) (l : Compare.Lab)
  | incr (l : Incr.Lab)
  | copy (s : CopySite) (second : Bool)
  | move (s : MoveSite) (second : Bool)
  | clean (s : CleanSite)
  | checkD | checkM | outer | loc | inner | col | yes | no
  deriving DecidableEq, Fintype

open Cslib.Complexity.FramedCNF

/-! ## Stack assignments of the sites -/

private def numSrc : NumSite → K
  | .locJ => .wJ | .locS => .wS | .parJ => .wJ | .parS => .wS | .parJb => .rowJb | .parSb => .rowSb

private def numDst : NumSite → K
  | .locJ => .lA | .locS => .sA | .parJ => .lA | .parS => .sA | .parJb => .lB | .parSb => .sB

private def splitIn : SplitSite → K
  | .top1 => .raw | .top2 => .raw | .outJ => .jobsO | .outS => .schedO | .inJ => .jobsI
  | .inS => .schedI | .num r => numSrc r

private def splitOut : SplitSite → K
  | .top1 => .mraw | .top2 => .jobsO | .outJ => .rowJ | .outS => .rowS | .inJ => .rowJb
  | .inS => .rowSb | .num _ => .payload

private def normIn : NormSite → K
  | .dd => .raw | .mn => .mraw | .num _ => .payload

private def normOut : NormSite → K
  | .dd => .dd | .mn => .mn | .num r => numDst r

private def cmpArgs : CmpSite → K × K × K
  | .deadline => (.sA, .lA, .dd)
  | .prec => (.prevS, .prevL, .sA)
  | .ab => (.sA, .lA, .sB)
  | .ba => (.sB, .lB, .sA)
  | .cntLe => (.cnt, .zero, .mn)
  | .cntGe => (.mn, .zero, .cnt)

private def copySrc : CopySite → K
  | .locJ => .rowJ | .locS => .rowS | .inJ => .jobsO | .inS => .schedO | .parJ => .rowJ
  | .parS => .rowS

private def copyDst : CopySite → K
  | .locJ => .wJ | .locS => .wS | .inJ => .jobsI | .inS => .schedI | .parJ => .wJ | .parS => .wS

private def moveSrc : MoveSite → K
  | .len => .lA | .start => .sA

private def moveDst : MoveSite → K
  | .len => .prevL | .start => .prevS

private def cleanKs : CleanSite → List K
  | .prev => [.prevL, .prevS]
  | .locEnd => [.cnt, .prevL, .prevS]
  | .col => [.lA, .sA, .lB, .sB]
  | .innerEnd => [.rowJ, .rowS]

/-! ## Continuations -/

private def afterSplit : SplitSite → Lab
  | .top1 => .split .top2 .read
  | .top2 => .norm .dd (.read none)
  | .outJ => .split .outS .read
  | .outS => .copy .locJ false
  | .inJ => .split .inS .read
  | .inS => .copy .parJ false
  | .num r => .norm (.num r) (.read none)

private def afterNorm : NormSite → Lab
  | .dd => .checkD
  | .mn => .checkM
  | .num .locJ => .split (.num .locS) .read
  | .num .locS => .cmp .deadline (.compare 0)
  | .num .parJ => .split (.num .parS) .read
  | .num .parS => .split (.num .parJb) .read
  | .num .parJb => .split (.num .parSb) .read
  | .num .parSb => .cmp .ab (.compare 0)

private def afterCmp : CmpSite → Bool → Lab
  | .deadline, true => .cmp .prec (.compare 0)
  | .prec, true => .clean .prev
  | .ab, true => .clean .col
  | .ab, false => .cmp .ba (.compare 0)
  | .ba, true => .clean .col
  | .cntLe, true => .cmp .cntGe (.compare 0)
  | .cntGe, true => .clean .locEnd
  | _, false => .no

private def afterCopy : CopySite → Lab
  | .locJ => .copy .locS false
  | .locS => .loc
  | .inJ => .copy .inS false
  | .inS => .inner
  | .parJ => .copy .parS false
  | .parS => .col

private def afterMove : MoveSite → Lab
  | .len => .move .start false
  | .start => .incr .carry

private def afterClean : CleanSite → Lab
  | .prev => .move .len false
  | .locEnd => .copy .inJ false
  | .col => .col
  | .innerEnd => .outer

private def splitLabel (s : SplitSite) : PairSplit.Lab → Lab
  | .good => afterSplit s
  | .bad => .no
  | l => .split s l

private def normLabel (s : NormSite) : NormalizeMachine.Lab → Lab
  | .done => afterNorm s
  | l => .norm s l

private def cmpLabel (s : CmpSite) : Compare.Lab → Lab
  | .done b => afterCmp s b
  | l => .cmp s l

private def incrLabel : Incr.Lab → Lab
  | .done => .loc
  | l => .incr l

/-! ## Embeddings -/

private def boolEmb {A : Type} (f : A → K) (hf : Injective f) :
    SEmb (fun _ : A => Bool) (fun _ : K => Bool) :=
  ⟨f, hf, fun _ => Equiv.refl _⟩

private def splitKey (s : SplitSite) : PairSplit.K → K
  | .input => splitIn s
  | .left => splitOut s
  | .scratch => .splitTemp

private def splitEmb (s : SplitSite) : SEmb (fun _ : PairSplit.K => Bool) (fun _ : K => Bool) :=
  boolEmb (splitKey s) (by
    intro a b h
    cases s with
    | num r => cases r <;> cases a <;> cases b <;> simp_all [splitKey, splitIn, splitOut, numSrc]
    | _ => cases a <;> cases b <;> simp_all [splitKey, splitIn, splitOut])

private def normKey (s : NormSite) : NormalizeMachine.K → K
  | .input => normIn s
  | .output => normOut s
  | .buffer => .normTemp

private def normEmb (s : NormSite) :
    SEmb (fun _ : NormalizeMachine.K => Bool) (fun _ : K => Bool) :=
  boolEmb (normKey s) (by
    intro a b h
    cases s with
    | num r => cases r <;> cases a <;> cases b <;> simp_all [normKey, normIn, normOut, numDst]
    | _ => cases a <;> cases b <;> simp_all [normKey, normIn, normOut])

private def cmpKey (s : CmpSite) : Compare.K → K
  | .a => (cmpArgs s).1
  | .b => (cmpArgs s).2.1
  | .c => (cmpArgs s).2.2
  | .ar => .cmpA
  | .br => .cmpB
  | .cr => .cmpC

private def cmpEmb (s : CmpSite) : SEmb (fun _ : Compare.K => Bool) (fun _ : K => Bool) :=
  boolEmb (cmpKey s) (by
    intro k₁ k₂ h
    cases s <;> cases k₁ <;> cases k₂ <;> simp_all [cmpKey, cmpArgs])

private def incrKey : Incr.K → K
  | .c => .cnt
  | .t => .incrTemp

private def incrEmb : SEmb (fun _ : Incr.K => Bool) (fun _ : K => Bool) :=
  boolEmb incrKey (by intro a b h; cases a <;> cases b <;> simp_all [incrKey])

/-! ## The program -/

private def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .split s l => mapS (splitEmb s) (splitLabel s) (PairSplit.prog l)
  | .norm s l => mapS (normEmb s) (normLabel s) (NormalizeMachine.prog l)
  | .cmp s l => mapS (cmpEmb s) (cmpLabel s) (Compare.prog l)
  | .incr l => mapS incrEmb incrLabel (Incr.prog l)
  | .copy s false => moveB (copySrc s) .copyTemp some id (.copy s false) (.copy s true)
  | .copy s true => splitB .copyTemp (copySrc s) (copyDst s) some id id (.copy s true)
      (afterCopy s)
  | .move s false => moveB (moveSrc s) .copyTemp some id (.move s false) (.move s true)
  | .move s true => moveB .copyTemp (moveDst s) some id (.move s true) (afterMove s)
  | .clean s => cleanS (cleanKs s) (.clean s) (afterClean s)
  | .checkD =>
    .peek .dd (fun _ o => o.isNone) <| .branch id (.goto fun _ => .no)
      (.goto fun _ => .norm .mn (.read none))
  | .checkM =>
    .peek .mn (fun _ o => o.isNone) <| .branch id (.goto fun _ => .no) (.goto fun _ => .outer)
  | .outer =>
    .peek .jobsO (fun _ o => o.isNone) <| .branch id
      (.peek .schedO (fun _ o => o.isNone) <| .branch id
        (.goto fun _ => .yes) (.goto fun _ => .split .outJ .read))
      (.goto fun _ => .split .outJ .read)
  | .loc =>
    .peek .wJ (fun _ o => o.isNone) <| .branch id
      (.peek .wS (fun _ o => o.isNone) <| .branch id
        (.goto fun _ => .cmp .cntLe (.compare 0)) (.goto fun _ => .split (.num .locJ) .read))
      (.goto fun _ => .split (.num .locJ) .read)
  | .inner =>
    .peek .jobsI (fun _ o => o.isNone) <| .branch id
      (.peek .schedI (fun _ o => o.isNone) <| .branch id
        (.goto fun _ => .clean .innerEnd) (.goto fun _ => .split .inJ .read))
      (.goto fun _ => .split .inJ .read)
  | .col =>
    .peek .wJ (fun _ o => o.isNone) <| .branch id
      (.peek .wS (fun _ o => o.isNone) <| .branch id
        (.peek .rowJb (fun _ o => o.isNone) <| .branch id
          (.peek .rowSb (fun _ o => o.isNone) <| .branch id
            (.goto fun _ => .inner) (.goto fun _ => .split (.num .parJ) .read))
          (.goto fun _ => .split (.num .parJ) .read))
        (.goto fun _ => .split (.num .parJ) .read))
      (.goto fun _ => .split (.num .parJ) .read)
  | .yes | .no => .halt

private theorem split_embeds (s : SplitSite) :
    Embeds (splitEmb s) (splitLabel s) PairSplit.prog prog := by
  intro l
  cases l <;> simp [splitLabel, prog, PairSplit.prog]

private theorem norm_embeds (s : NormSite) :
    Embeds (normEmb s) (normLabel s) NormalizeMachine.prog prog := by
  intro l
  cases l <;> simp [normLabel, prog, NormalizeMachine.prog]

private theorem cmp_embeds (s : CmpSite) : Embeds (cmpEmb s) (cmpLabel s) Compare.prog prog := by
  intro l
  cases l <;> simp [cmpLabel, prog, Compare.prog]

private theorem incr_embeds : Embeds incrEmb incrLabel Incr.prog prog := by
  intro l
  cases l <;> simp [incrLabel, prog, Incr.prog]

end Machine

section Comp

/-! ### Run lemmas of the embedded components at every site -/

open MetaMathlibExt
open Turing Function TM2Program TM2Embedding Cslib.Complexity.PolynomialEncoding
open Cslib.Complexity.FramedCNF MetaMathlibExt.BitstringEncoding

private theorem eq_of_agrees {A : Type} {E : SEmb (fun _ : A => Bool) (fun _ : K => Bool)}
    {S T U : K → List Bool} {Q : A → List Bool}
    (hT : Agree E Q T) (hU : Agree E Q U) (hFT : Frame E S T) (hFU : Frame E S U) :
    T = U := by
  classical
  funext k
  by_cases hk : ∃ a, E.e a = k
  · obtain ⟨a, rfl⟩ := hk
    exact (hT a).trans (hU a).symm
  · have hne : ∀ a, E.e a ≠ k := fun a ha => hk ⟨a, ha⟩
    exact (hFT k hne).trans (hFU k hne).symm

private theorem splitIn_ne_out (s : SplitSite) : splitIn s ≠ splitOut s := by
  cases s with
  | num r => cases r <;> decide
  | _ => decide

private theorem splitTemp_ne_in (s : SplitSite) : K.splitTemp ≠ splitIn s := by
  cases s with
  | num r => cases r <;> decide
  | _ => decide

private theorem splitTemp_ne_out (s : SplitSite) : K.splitTemp ≠ splitOut s := by
  cases s with
  | num r => cases r <;> decide
  | _ => decide

private theorem split_run (s : SplitSite) (S : K → List Bool) (v : Bool)
    (hout : S (splitOut s) = []) (hbuf : S .splitTemp = []) :
    ∃ v' T, RunLe prog ((S (splitIn s)).length + 1)
      ⟨some (.split s .read), v, S⟩
      ⟨some (if (undelimit (S (splitIn s))).isSome then afterSplit s else .no), v', T⟩ ∧
      ∀ p r, undelimit (S (splitIn s)) = some (p, r) →
        T = update (update S (splitIn s) r) (splitOut s) p := by
  obtain ⟨v', T, hr, hf, ha⟩ := PairSplit.run_embedded (splitEmb s) (splitLabel s)
    (split_embeds s) (S (splitIn s)) v S (by
      intro k
      cases k <;> simp [splitEmb, boolEmb, splitKey, PairSplit.st, hout, hbuf])
  refine ⟨v', T, ?_, fun p r hp => ?_⟩
  · cases h : (undelimit (S (splitIn s))).isSome <;> simpa [h, splitLabel] using hr
  · refine eq_of_agrees (ha p r hp) ?_ hf ?_
    · intro k
      cases k <;> simp [splitEmb, boolEmb, splitKey, PairSplit.st, hbuf, splitIn_ne_out s,
        splitTemp_ne_in s, splitTemp_ne_out s]
    · intro k hk
      have h₁ := hk PairSplit.K.input
      have h₂ := hk PairSplit.K.left
      simp only [splitEmb, boolEmb, splitKey] at h₁ h₂
      simp [update_of_ne h₁.symm, update_of_ne h₂.symm]

private theorem normIn_ne_out (s : NormSite) : normIn s ≠ normOut s := by
  cases s with
  | num r => cases r <;> decide
  | _ => decide

private theorem normTemp_ne_in (s : NormSite) : K.normTemp ≠ normIn s := by
  cases s with
  | num r => cases r <;> decide
  | _ => decide

private theorem normTemp_ne_out (s : NormSite) : K.normTemp ≠ normOut s := by
  cases s with
  | num r => cases r <;> decide
  | _ => decide

private theorem norm_run (s : NormSite) (S : K → List Bool) (v : Bool)
    (hout : S (normOut s) = []) (hbuf : S .normTemp = []) :
    ∃ v', RunLe prog (2 * (S (normIn s)).length + 3)
      ⟨some (.norm s (.read none)), v, S⟩ ⟨some (afterNorm s), v',
        update (update S (normIn s) []) (normOut s) (normalizeNat (S (normIn s)))⟩ := by
  obtain ⟨v', hr⟩ := normalizeNat_run_frame (S (normIn s)) [] v
  obtain ⟨T, ht, ha, hf⟩ := runLe_embed (normLabel s) (norm_embeds s) hr (S' := S) (by
    intro k
    cases k <;> simp [normEmb, boolEmb, normKey, NormalizeMachine.st, hout, hbuf])
  have hs : T = update (update S (normIn s) []) (normOut s) (normalizeNat (S (normIn s))) := by
    refine eq_of_agrees ha ?_ hf ?_
    · intro k
      cases k <;> simp [normEmb, boolEmb, normKey, NormalizeMachine.st, hbuf, normIn_ne_out s,
        normTemp_ne_in s, normTemp_ne_out s]
    · intro k hk
      have h₁ := hk NormalizeMachine.K.input
      have h₂ := hk NormalizeMachine.K.output
      simp only [normEmb, boolEmb, normKey] at h₁ h₂
      simp [update_of_ne h₁.symm, update_of_ne h₂.symm]
  exact ⟨v', hs ▸ ht⟩

private theorem cmp_run (s : CmpSite) (S : K → List Bool) (v : Bool) (x y z : List Bool)
    (hx : S (cmpArgs s).1 = x) (hy : S (cmpArgs s).2.1 = y) (hz : S (cmpArgs s).2.2 = z)
    (hbuf : S .cmpA = [] ∧ S .cmpB = [] ∧ S .cmpC = []) :
    ∃ v', RunLe prog (2 * (x.length + y.length + z.length) + 4)
      ⟨some (.cmp s (.compare 0)), v, S⟩
      ⟨some (afterCmp s (decide (Compare.value x + Compare.value y ≤ Compare.value z))),
        v', S⟩ := by
  subst hx hy hz
  obtain ⟨v', hr⟩ := Compare.run_value (S (cmpArgs s).1) (S (cmpArgs s).2.1)
    (S (cmpArgs s).2.2) v
  have hA : Agree (cmpEmb s) (Compare.st (S (cmpArgs s).1) (S (cmpArgs s).2.1)
      (S (cmpArgs s).2.2) [] [] []) S := by
    intro k
    cases k <;> simp [cmpEmb, boolEmb, cmpKey, Compare.st, hbuf]
  obtain ⟨T, ht, hag, hf⟩ := runLe_embed (cmpLabel s) (cmp_embeds s) hr hA
  have he := eq_of_agrees hag hA hf (Frame.refl _)
  exact ⟨v', by simpa [he, cmpLabel] using ht⟩

private theorem incr_run (S : K → List Bool) (v : Bool) (c : List Bool) (hc : S .cnt = c)
    (htemp : S .incrTemp = []) :
    ∃ v', RunLe prog (2 * c.length + 4) ⟨some (.incr .carry), v, S⟩
      ⟨some .loc, v', update S .cnt (Incr.incrBits c)⟩ := by
  subst hc
  obtain ⟨v', hr⟩ := Incr.run (S .cnt) v
  obtain ⟨T, ht, ha, hf⟩ := runLe_embed incrLabel incr_embeds hr (S' := S) (by
    intro k
    cases k <;> simp [incrEmb, boolEmb, incrKey, Incr.st, htemp])
  have hs : T = update S .cnt (Incr.incrBits (S .cnt)) := by
    refine eq_of_agrees ha ?_ hf ?_
    · intro k
      cases k <;> simp [incrEmb, boolEmb, incrKey, Incr.st, htemp]
    · intro k hk
      have h₁ := hk Incr.K.c
      simp only [incrEmb, boolEmb, incrKey] at h₁
      simp [update_of_ne h₁.symm]
  exact ⟨v', hs ▸ ht⟩

private theorem copySrc_ne_dst (s : CopySite) : copySrc s ≠ copyDst s := by cases s <;> decide
private theorem copySrc_ne_temp (s : CopySite) : copySrc s ≠ .copyTemp := by cases s <;> decide
private theorem copyDst_ne_temp (s : CopySite) : copyDst s ≠ .copyTemp := by cases s <;> decide

private theorem copy_run (s : CopySite) (S : K → List Bool) (v : Bool) (x y : List Bool)
    (hx : S (copySrc s) = x) (hy : S (copyDst s) = y) (htemp : S .copyTemp = []) :
    ∃ v', RunLe prog (2 * x.length + 2) ⟨some (.copy s false), v, S⟩
      ⟨some (afterCopy s), v', update S (copyDst s) (x ++ y)⟩ := by
  subst hx hy
  obtain ⟨S', hr, ha, ht, hb, hk⟩ := copyB_run (M := prog) (a := copySrc s) (b := copyDst s)
    (t := .copyTemp) (da := some) (dt := some) (ga := id) (gb := id) (gt := id)
    (first := .copy s false) (second := .copy s true) (next := afterCopy s) rfl rfl
    (copySrc_ne_dst s) (copySrc_ne_temp s) (copyDst_ne_temp s) (fun _ => rfl) (fun _ => rfl)
    (S (copySrc s)) [] v S (by simp) (by simp [EndsBitBlock]) (by simp [EndsBitBlock, htemp])
  have he : S' = update S (copyDst s) (S (copySrc s) ++ S (copyDst s)) := by
    funext k
    by_cases h₁ : k = copyDst s
    · subst h₁; simpa using hb
    · rw [update_of_ne h₁]
      by_cases h₂ : k = copySrc s
      · subst h₂; exact ha
      · by_cases h₃ : k = .copyTemp
        · subst h₃; exact ht
        · exact hk k h₂ h₁ h₃
  exact ⟨false, he ▸ hr.le le_rfl⟩

private theorem moveSrc_ne_dst (s : MoveSite) : moveSrc s ≠ moveDst s := by cases s <;> decide
private theorem moveSrc_ne_temp (s : MoveSite) : moveSrc s ≠ .copyTemp := by cases s <;> decide
private theorem moveDst_ne_temp (s : MoveSite) : moveDst s ≠ .copyTemp := by cases s <;> decide

private theorem move_run (s : MoveSite) (S : K → List Bool) (v : Bool) (x y : List Bool)
    (hx : S (moveSrc s) = x) (hy : S (moveDst s) = y) (htemp : S .copyTemp = []) :
    ∃ v', RunLe prog (2 * x.length + 2) ⟨some (.move s false), v, S⟩
      ⟨some (afterMove s), v', update (update S (moveSrc s) []) (moveDst s) (x ++ y)⟩ := by
  subst hx hy
  obtain ⟨v₁, U, h₁, ha₁, hb₁, hk₁⟩ := moveB_run (M := prog) (self := .move s false)
    (next := .move s true) (a := moveSrc s) (b := .copyTemp) (d := some) (g := id) rfl
    (moveSrc_ne_temp s) (S (moveSrc s)) (S (moveSrc s)) [] v S (by simp)
    (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  obtain ⟨v₂, T, h₂, ha₂, hb₂, hk₂⟩ := moveB_run (M := prog) (self := .move s true)
    (next := afterMove s) (a := .copyTemp) (b := moveDst s) (d := some) (g := id) rfl
    (moveDst_ne_temp s).symm (S (moveSrc s)).reverse (S (moveSrc s)).reverse [] v₁ U
    (by simp [hb₁, htemp]) (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  have he : T = update (update S (moveSrc s) []) (moveDst s)
      (S (moveSrc s) ++ S (moveDst s)) := by
    funext k
    by_cases h₁ : k = moveDst s
    · subst h₁
      rw [hb₂, hk₁ _ (moveSrc_ne_dst s).symm (moveDst_ne_temp s)]
      simp
    · rw [update_of_ne h₁]
      by_cases h₂ : k = .copyTemp
      · subst h₂; rw [ha₂, update_of_ne (moveSrc_ne_temp s).symm, htemp]
      · rw [hk₂ k h₂ h₁]
        by_cases h₃ : k = moveSrc s
        · subst h₃; simp [ha₁]
        · rw [update_of_ne h₃, hk₁ k h₃ h₂]
  refine ⟨v₂, ?_⟩
  rw [← he]
  exact ((h₁.trans h₂).le (by simp; omega))

private theorem clean_run' (s : CleanSite) (S : K → List Bool) (v : Bool) (m : ℕ)
    (hm : ∀ k ∈ cleanKs s, (S k).length ≤ m) :
    ∃ v', RunLe prog (m + 1) ⟨some (.clean s), v, S⟩
      ⟨some (afterClean s), v', fun k => if k ∈ cleanKs s then [] else S k⟩ :=
  ⟨_, clean_run (M := prog) (ks := cleanKs s) (self := .clean s) (next := afterClean s) rfl
    (by cases s <;> decide) m v S hm⟩

end Comp

section State

/-! ### Canonical stack states and the number reader -/

open MetaMathlibExt
open Turing Function TM2Program TM2Embedding Cslib.Complexity.PolynomialEncoding
open Cslib.Complexity.FramedCNF MetaMathlibExt.BitstringEncoding Computability

/-- The live stacks; every other stack is empty. -/
private structure Tp where
  raw : List Bool := []
  mraw : List Bool := []
  mn : List Bool := []
  dd : List Bool := []
  jobsO : List Bool := []
  schedO : List Bool := []
  jobsI : List Bool := []
  schedI : List Bool := []
  rowJ : List Bool := []
  rowS : List Bool := []
  rowJb : List Bool := []
  rowSb : List Bool := []
  wJ : List Bool := []
  wS : List Bool := []
  lA : List Bool := []
  sA : List Bool := []
  lB : List Bool := []
  sB : List Bool := []
  prevL : List Bool := []
  prevS : List Bool := []
  cnt : List Bool := []

private def Tp.get (t : Tp) : K → List Bool
  | .raw => t.raw | .mraw => t.mraw | .mn => t.mn | .dd => t.dd
  | .jobsO => t.jobsO | .schedO => t.schedO | .jobsI => t.jobsI | .schedI => t.schedI
  | .rowJ => t.rowJ | .rowS => t.rowS | .rowJb => t.rowJb | .rowSb => t.rowSb
  | .wJ => t.wJ | .wS => t.wS | .lA => t.lA | .sA => t.sA | .lB => t.lB | .sB => t.sB
  | .prevL => t.prevL | .prevS => t.prevS | .cnt => t.cnt
  | _ => []

/-- Normalized number. -/
private abbrev enc (p : List Bool) : List Bool := encodeNat (decodeNat p)

private theorem enc_length_le (p : List Bool) : (enc p).length ≤ p.length + 1 := by
  change (encodeNat (decodeNat p)).length ≤ _
  rw [← normalizeNat_eq_encode_decode]
  exact length_normalizeNat_le p

private theorem value_enc (p : List Bool) : Compare.value (enc p) = decodeNat p :=
  Compare.value_encodeNat _

/-- Reading one number: split a block off the source row stack, normalize it onto the
destination number stack. -/
private theorem num_run (r : NumSite) (S : K → List Bool) (v : Bool) (x : List Bool)
    (hx : S (numSrc r) = x)
    (hp : S .payload = []) (hd : S (numDst r) = []) (hs : S .splitTemp = [])
    (hn : S .normTemp = []) :
    ∃ v' T, RunLe prog (3 * x.length + 4)
      ⟨some (.split (.num r) .read), v, S⟩
      ⟨some (if (undelimit x).isSome then afterNorm (.num r) else .no), v', T⟩ ∧
      ∀ p rest, undelimit x = some (p, rest) →
        T = update (update S (numSrc r) rest) (numDst r) (enc p) := by
  subst hx
  obtain ⟨v₁, U, h₁, hu⟩ := split_run (.num r) S v hp hs
  simp only [splitIn, splitOut] at h₁ hu
  cases hx : undelimit (S (numSrc r)) with
  | none =>
    refine ⟨v₁, U, ?_, by simp⟩
    simpa [hx] using h₁.mono (by omega)
  | some pr =>
    obtain ⟨p, rest⟩ := pr
    have hU := hu p rest hx
    have hlen := undelimit_lt hx
    have hpl : p.length < (S (numSrc r)).length := by
      rw [(Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp hx]
      simp only [List.length_append, length_delimit]
      omega
    have hsrc : numSrc r ≠ K.payload := by cases r <;> decide
    have hdst : numDst r ≠ K.payload := by cases r <;> decide
    have hsd : numSrc r ≠ numDst r := by cases r <;> decide
    obtain ⟨v₂, h₂⟩ := norm_run (.num r) U v₁ (by
      simp only [normOut, hU]
      rw [update_of_ne hdst, update_of_ne hsd.symm, hd]) (by
      rw [hU, update_of_ne (by decide), update_of_ne (by cases r <;> decide), hn])
    simp only [normIn, normOut] at h₂
    have hpay : U .payload = p := by rw [hU]; simp
    rw [hpay] at h₂
    refine ⟨v₂, update (update U .payload []) (numDst r) (normalizeNat p), ?_,
      fun p' rest' h' => ?_⟩
    · have h₁' : RunLe prog ((S (numSrc r)).length + 1) ⟨some (.split (.num r) .read), v, S⟩
          ⟨some (.norm (.num r) (.read none)), v₁, U⟩ := by
        simpa [hx, afterSplit] using h₁
      simpa [hx] using (h₁'.trans h₂).mono (by omega)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
      rw [hU, normalizeNat_eq_encode_decode]
      funext k
      by_cases h₁ : k = numDst r
      · subst h₁; simp
      · by_cases h₂ : k = .payload
        · subst h₂; simp [update_of_ne hsrc.symm, update_of_ne hdst.symm, hp]
        · simp [update_of_ne h₁, update_of_ne h₂]

end State

section StateUpd

open MetaMathlibExt Function

private def live : K → Bool
  | .zero | .payload | .splitTemp | .normTemp | .copyTemp | .cmpA | .cmpB | .cmpC | .incrTemp =>
    false
  | _ => true

private def Tp.set (t : Tp) : K → List Bool → Tp
  | .raw, v => { t with raw := v } | .mraw, v => { t with mraw := v }
  | .mn, v => { t with mn := v } | .dd, v => { t with dd := v }
  | .jobsO, v => { t with jobsO := v } | .schedO, v => { t with schedO := v }
  | .jobsI, v => { t with jobsI := v } | .schedI, v => { t with schedI := v }
  | .rowJ, v => { t with rowJ := v } | .rowS, v => { t with rowS := v }
  | .rowJb, v => { t with rowJb := v } | .rowSb, v => { t with rowSb := v }
  | .wJ, v => { t with wJ := v } | .wS, v => { t with wS := v }
  | .lA, v => { t with lA := v } | .sA, v => { t with sA := v }
  | .lB, v => { t with lB := v } | .sB, v => { t with sB := v }
  | .prevL, v => { t with prevL := v } | .prevS, v => { t with prevS := v }
  | .cnt, v => { t with cnt := v }
  | _, _ => t

private theorem update_get (t : Tp) (k : K) (hk : live k = true) (v : List Bool) :
    update t.get k v = (t.set k v).get := by
  cases k <;> simp only [live, Bool.false_eq_true] at hk <;> funext j <;> cases j <;> rfl

end StateUpd

section Local

/-! ### The local column scan of one job -/

open MetaMathlibExt
open Turing Function TM2Program TM2Embedding Cslib.Complexity.PolynomialEncoding
open Cslib.Complexity.FramedCNF MetaMathlibExt.BitstringEncoding Computability

/-! ### Equations of `localScan` -/

private theorem localScan_nil (D : ℕ) (prev : Option ℕ) : localScan D prev [] [] = some 0 := by
  rw [localScan]; simp

private theorem localScan_none₁ {D : ℕ} {prev : Option ℕ} {rj rs : List Bool}
    (hne : ¬(rj = [] ∧ rs = [])) (h : undelimit rj = none) : localScan D prev rj rs = none := by
  rw [localScan, iteF _ _ hne]
  split
  · rename_i heq _; rw [h] at heq; cases heq
  · rfl

private theorem localScan_none₂ {D : ℕ} {prev : Option ℕ} {rj rs pl rj' : List Bool}
    (h₁ : undelimit rj = some (pl, rj')) (h : undelimit rs = none) :
    localScan D prev rj rs = none := by
  rw [localScan, iteF _ _ (fun h' => undelimit_ne_nil h₁ h'.1)]
  split
  · rename_i heq₁ heq₂; rw [h] at heq₂; cases heq₂
  · rfl

private theorem localScan_cons {D : ℕ} {prev : Option ℕ} {rj rs pl rj' ps rs' : List Bool}
    (h₁ : undelimit rj = some (pl, rj')) (h₂ : undelimit rs = some (ps, rs')) :
    localScan D prev rj rs =
      if decodeNat ps + decodeNat pl ≤ D ∧ prev.all (· ≤ decodeNat ps) then
        (localScan D (some (decodeNat ps + decodeNat pl)) rj' rs').map (· + 1)
      else none := by
  rw [localScan, iteF _ _ (fun h' => undelimit_ne_nil h₁ h'.1)]
  split
  · rename_i a b c d heq₁ heq₂
    rw [h₁] at heq₁; rw [h₂] at heq₂
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq₁)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq₂)
    rfl
  · rename_i hne
    exact absurd (hne _ _ _ _ h₁ h₂) id

/-! ### The local state -/

private def pvS (pv : Option (ℕ × ℕ)) : List Bool := pv.elim [] fun q => encodeNat q.1
private def pvL (pv : Option (ℕ × ℕ)) : List Bool := pv.elim [] fun q => encodeNat q.2

private def locT (mn dd J S rj rs wj ws : List Bool) (pv : Option (ℕ × ℕ)) (c : List Bool) : Tp :=
  { mn := mn, dd := dd, jobsO := J, schedO := S, rowJ := rj, rowS := rs, wJ := wj, wS := ws,
    prevS := pvS pv, prevL := pvL pv, cnt := c }

private def PvBound (N : ℕ) (pv : Option (ℕ × ℕ)) : Prop :=
  (pvS pv).length ≤ N ∧ (pvL pv).length ≤ N

private theorem prev_all (pv : Option (ℕ × ℕ)) (s : ℕ) :
    (pv.map fun q => q.1 + q.2).all (· ≤ s) =
      decide (Compare.value (pvS pv) + Compare.value (pvL pv) ≤ s) := by
  cases pv with
  | none => simp [pvS, pvL, Compare.value]
  | some q => simp [pvS, pvL, Compare.value_encodeNat]

private theorem block_length {x p r : List Bool} (h : undelimit x = some (p, r)) :
    p.length + 1 ≤ x.length ∧ r.length + 1 ≤ x.length := by
  rw [(Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp h]
  simp only [List.length_append, length_delimit]
  omega

private theorem loc_peek (t : Tp) (v : Bool) : ∃ v', TM2.step prog ⟨some .loc, v, t.get⟩ =
    some ⟨some (if t.wJ = [] ∧ t.wS = [] then .cmp .cntLe (.compare 0)
      else .split (.num .locJ) .read), v', t.get⟩ := by
  rcases hj : t.wJ with _ | ⟨a, as⟩ <;> rcases hs : t.wS with _ | ⟨b, bs⟩
  · exact ⟨true, by simp [prog, TM2.stepAux, Tp.get, hj, hs]⟩
  · exact ⟨false, by simp [prog, TM2.stepAux, Tp.get, hj, hs]⟩
  · exact ⟨false, by simp [prog, TM2.stepAux, Tp.get, hj, hs]⟩
  · exact ⟨false, by simp [prog, TM2.stepAux, Tp.get, hj, hs]⟩

private theorem loc_loop (N D : ℕ) (mn dd J S rj rs : List Bool) (hdd : dd = encodeNat D)
    (hdN : dd.length ≤ N) :
    ∀ (wj ws : List Bool) (pv : Option (ℕ × ℕ)) (c : List Bool) (v : Bool),
      wj.length ≤ N → ws.length ≤ N → PvBound N pv → c.length + wj.length ≤ N →
      ∃ v' T, RunLe prog ((30 * N + 30) * (wj.length + 1))
        ⟨some .loc, v, (locT mn dd J S rj rs wj ws pv c).get⟩
        ⟨some (if (localScan D (pv.map fun q => q.1 + q.2) wj ws).isSome then
          .cmp .cntLe (.compare 0) else .no), v', T⟩ ∧
        ∀ k, localScan D (pv.map fun q => q.1 + q.2) wj ws = some k →
          ∃ pv' c', T = (locT mn dd J S rj rs [] [] pv' c').get ∧
            Compare.value c' = Compare.value c + k ∧ c'.length ≤ N ∧ PvBound N pv' := by
  intro wj
  induction h : wj.length using Nat.strong_induction_on generalizing wj with
  | _ n ih =>
    subst h
    intro ws pv c v hwj hws hpv hc
    obtain ⟨v₀, h₀⟩ := loc_peek (locT mn dd J S rj rs wj ws pv c) v
    by_cases hemp : wj = [] ∧ ws = []
    · obtain ⟨rfl, rfl⟩ := hemp
      have hr := (Run.head h₀ (Run.zero _)).le (le_refl 1)
      refine ⟨v₀, (locT mn dd J S rj rs [] [] pv c).get, ?_, ?_⟩
      · simpa [locT, localScan_nil] using hr.mono (by simp)
      · intro k hk
        rw [localScan_nil] at hk
        cases hk
        exact ⟨pv, c, rfl, by simp, by simp at hc; omega, hpv⟩
    -- the first number
    have h₀' : RunLe prog 1 ⟨some .loc, v, (locT mn dd J S rj rs wj ws pv c).get⟩
        ⟨some (.split (.num .locJ) .read), v₀, (locT mn dd J S rj rs wj ws pv c).get⟩ := by
      have := (Run.head h₀ (Run.zero _)).le (le_refl 1)
      simpa [locT, hemp] using this
    obtain ⟨v₁, T₁, h₁, hT₁⟩ := num_run .locJ (locT mn dd J S rj rs wj ws pv c).get v₀ wj
      rfl rfl rfl rfl rfl
    simp only [numSrc, numDst] at hT₁
    cases hu₁ : undelimit wj with
    | none =>
      refine ⟨v₁, T₁, ?_, ?_⟩
      · rw [localScan_none₁ hemp hu₁]
        simpa [hu₁] using (h₀'.trans h₁).mono (by nlinarith)
      · intro k hk; rw [localScan_none₁ hemp hu₁] at hk; cases hk
    | some pr =>
      obtain ⟨pl, wj'⟩ := pr
      have hb₁ := block_length hu₁
      have hT₁' := hT₁ pl wj' hu₁
      rw [update_get _ _ rfl, update_get _ _ rfl] at hT₁'
      subst hT₁'
      have h₁' : RunLe prog (3 * wj.length + 4)
          ⟨some (.split (.num .locJ) .read), v₀, (locT mn dd J S rj rs wj ws pv c).get⟩
          ⟨some (.split (.num .locS) .read), v₁,
            (((locT mn dd J S rj rs wj ws pv c).set .wJ wj').set .lA (enc pl)).get⟩ := by
        simpa [hu₁, afterNorm] using h₁
      obtain ⟨v₂, T₂, h₂, hT₂⟩ := num_run .locS
        (((locT mn dd J S rj rs wj ws pv c).set .wJ wj').set .lA (enc pl)).get v₁ ws
        rfl rfl rfl rfl rfl
      simp only [numSrc, numDst] at hT₂
      cases hu₂ : undelimit ws with
      | none =>
        refine ⟨v₂, T₂, ?_, ?_⟩
        · rw [localScan_none₂ hu₁ hu₂]
          simpa [hu₂] using ((h₀'.trans h₁').trans h₂).mono (by nlinarith)
        · intro k hk; rw [localScan_none₂ hu₁ hu₂] at hk; cases hk
      | some qs =>
        obtain ⟨ps, ws'⟩ := qs
        have hb₂ := block_length hu₂
        have hT₂' := hT₂ ps ws' hu₂
        rw [update_get _ _ rfl, update_get _ _ rfl] at hT₂'
        subst hT₂'
        have h₂' : RunLe prog (3 * ws.length + 4)
            ⟨some (.split (.num .locS) .read), v₁,
              (((locT mn dd J S rj rs wj ws pv c).set .wJ wj').set .lA (enc pl)).get⟩
            ⟨some (.cmp .deadline (.compare 0)), v₂, (((((locT mn dd J S rj rs wj ws pv c).set
              .wJ wj').set .lA (enc pl)).set .wS ws').set .sA (enc ps)).get⟩ := by
          simpa [hu₂, afterNorm] using h₂
        set R₂ := ((((locT mn dd J S rj rs wj ws pv c).set .wJ wj').set .lA (enc pl)).set
          .wS ws').set .sA (enc ps) with hR₂
        have hpl := enc_length_le pl
        have hps := enc_length_le ps
        obtain ⟨v₃, h₃⟩ := cmp_run .deadline R₂.get v₂ (enc ps) (enc pl) dd rfl rfl rfl
          ⟨rfl, rfl, rfl⟩
        rw [value_enc, value_enc, hdd, Compare.value_encodeNat, ← hdd] at h₃
        have hA := (h₀'.trans h₁').trans h₂'
        by_cases hD : decodeNat ps + decodeNat pl ≤ D
        swap
        · have hnone : localScan D (pv.map fun q => q.1 + q.2) wj ws = none := by
            rw [localScan_cons hu₁ hu₂]; simp [hD]
          refine ⟨v₃, R₂.get, ?_, by intro k hk; rw [hnone] at hk; cases hk⟩
          rw [hnone]
          simpa [hD, afterCmp] using (hA.trans h₃).mono (by nlinarith)
        obtain ⟨v₄, h₄⟩ := cmp_run .prec R₂.get v₃ (pvS pv) (pvL pv) (enc ps) rfl rfl rfl
          ⟨rfl, rfl, rfl⟩
        rw [value_enc] at h₄
        have h₃' : RunLe prog (2 * ((enc ps).length + (enc pl).length + dd.length) + 4)
            ⟨some (.cmp .deadline (.compare 0)), v₂, R₂.get⟩
            ⟨some (.cmp .prec (.compare 0)), v₃, R₂.get⟩ := by
          simpa [hD, afterCmp] using h₃
        have hB := hA.trans h₃'
        by_cases hP : Compare.value (pvS pv) + Compare.value (pvL pv) ≤ decodeNat ps
        swap
        · have hnone : localScan D (pv.map fun q => q.1 + q.2) wj ws = none := by
            rw [localScan_cons hu₁ hu₂, prev_all]; simp [hP]
          refine ⟨v₄, R₂.get, ?_, by intro k hk; rw [hnone] at hk; cases hk⟩
          rw [hnone]
          simpa [hP, afterCmp] using (hB.trans h₄).mono (by
            obtain ⟨hp₁, hp₂⟩ := hpv; nlinarith)
        have h₄' : RunLe prog (2 * ((pvS pv).length + (pvL pv).length + (enc ps).length) + 4)
            ⟨some (.cmp .prec (.compare 0)), v₃, R₂.get⟩
            ⟨some (.clean .prev), v₄, R₂.get⟩ := by
          simpa [hP, afterCmp] using h₄
        obtain ⟨v₅, h₅⟩ := clean_run' .prev R₂.get v₄ N (by
          intro k hk
          simp only [cleanKs, List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl
          · exact hpv.2
          · exact hpv.1)
        set R₃ := (R₂.set .prevL []).set .prevS [] with hR₃
        have hc₃ : (fun k => if k ∈ cleanKs .prev then [] else R₂.get k) = R₃.get := by
          funext k; cases k <;> simp [cleanKs, Tp.get, Tp.set, hR₃]
        rw [hc₃] at h₅
        obtain ⟨v₆, h₆⟩ := move_run .len R₃.get v₅ (enc pl) [] rfl rfl rfl
        rw [update_get _ _ rfl, update_get _ _ rfl] at h₆
        set R₄ := (R₃.set .lA []).set .prevL (enc pl ++ []) with hR₄
        obtain ⟨v₇, h₇⟩ := move_run .start R₄.get v₆ (enc ps) [] rfl rfl rfl
        rw [update_get _ _ rfl, update_get _ _ rfl] at h₇
        set R₅ := (R₄.set .sA []).set .prevS (enc ps ++ []) with hR₅
        obtain ⟨v₈, h₈⟩ := incr_run R₅.get v₇ c rfl rfl
        rw [update_get _ _ rfl] at h₈
        have hR₆ : R₅.set .cnt (Incr.incrBits c) = locT mn dd J S rj rs wj' ws'
            (some (decodeNat ps, decodeNat pl)) (Incr.incrBits c) := by
          simp [hR₅, hR₄, hR₃, hR₂, locT, Tp.set, pvS, pvL, enc]
        rw [hR₆] at h₈
        have hC := (((hB.trans h₄').trans h₅).trans h₆).trans h₇ |>.trans h₈
        have hwj' : wj'.length < wj.length := by omega
        have hinc := Incr.length_incrBits c
        obtain ⟨v₉, T, h₉, hT⟩ := ih wj'.length hwj' wj' rfl ws'
          (some (decodeNat ps, decodeNat pl)) (Incr.incrBits c) v₈ (by omega) (by omega)
          ⟨by
            change (encodeNat (decodeNat ps)).length ≤ N
            have : (encodeNat (decodeNat ps)).length ≤ ps.length + 1 := enc_length_le ps
            omega,
            by
            change (encodeNat (decodeNat pl)).length ≤ N
            have : (encodeNat (decodeNat pl)).length ≤ pl.length + 1 := enc_length_le pl
            omega⟩
          (by omega)
        have hscan : localScan D (pv.map fun q => q.1 + q.2) wj ws =
            (localScan D (some (decodeNat ps + decodeNat pl)) wj' ws').map (· + 1) := by
          rw [localScan_cons hu₁ hu₂, prev_all]; simp [hD, hP]
        refine ⟨v₉, T, ?_, ?_⟩
        · rw [hscan, Option.isSome_map]
          refine (hC.trans h₉).mono ?_
          obtain ⟨hp₁, hp₂⟩ := hpv
          nlinarith
        · intro k hk
          rw [hscan] at hk
          obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hk
          obtain ⟨pv', c', hT', hv', hl', hb'⟩ := hT k' hk'
          refine ⟨pv', c', hT', ?_, hl', hb'⟩
          rw [hv', Incr.value_incrBits]
          omega

end Local

section Pair

/-! ### The column scan of a pair of jobs -/

open MetaMathlibExt
open Turing Function TM2Program TM2Embedding Cslib.Complexity.PolynomialEncoding
open Cslib.Complexity.FramedCNF MetaMathlibExt.BitstringEncoding Computability

private theorem pairScan_nil : pairScan [] [] [] [] = true := by rw [pairScan]; simp

private theorem pairScan_false {ra sa rb sb : List Bool}
    (hne : ¬(ra = [] ∧ sa = [] ∧ rb = [] ∧ sb = []))
    (h : ∀ a b c d e f g i, undelimit ra = some (a, b) → undelimit sa = some (c, d) →
      undelimit rb = some (e, f) → undelimit sb = some (g, i) → False) :
    pairScan ra sa rb sb = false := by
  rw [pairScan, iteF _ _ hne]
  split
  · rename_i h₁ h₂ h₃ h₄; exact (h _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄).elim
  · rfl

private theorem pairScan_cons {ra sa rb sb pla ra' psa sa' plb rb' psb sb' : List Bool}
    (h₁ : undelimit ra = some (pla, ra')) (h₂ : undelimit sa = some (psa, sa'))
    (h₃ : undelimit rb = some (plb, rb')) (h₄ : undelimit sb = some (psb, sb')) :
    pairScan ra sa rb sb =
      ((decide (decodeNat psa + decodeNat pla ≤ decodeNat psb) ||
        decide (decodeNat psb + decodeNat plb ≤ decodeNat psa)) && pairScan ra' sa' rb' sb') := by
  rw [pairScan, iteF _ _ (fun h => undelimit_ne_nil h₁ h.1)]
  split
  · rename_i a b c d e f g i g₁ g₂ g₃ g₄
    rw [h₁] at g₁; rw [h₂] at g₂; rw [h₃] at g₃; rw [h₄] at g₄
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj g₁)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj g₂)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj g₃)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj g₄)
    rfl
  · rename_i hne
    exact absurd (hne _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄) id

private def colT (mn dd J S rj rs JI SI wj ws rjb rsb : List Bool) : Tp :=
  { mn := mn, dd := dd, jobsO := J, schedO := S, rowJ := rj, rowS := rs, jobsI := JI,
    schedI := SI, wJ := wj, wS := ws, rowJb := rjb, rowSb := rsb }

private theorem col_peek (t : Tp) (v : Bool) : TM2.step prog ⟨some .col, v, t.get⟩ =
    some ⟨some (if t.wJ = [] ∧ t.wS = [] ∧ t.rowJb = [] ∧ t.rowSb = [] then .inner
      else .split (.num .parJ) .read),
      t.wJ.isEmpty && t.wS.isEmpty && t.rowJb.isEmpty && t.rowSb.isEmpty, t.get⟩ := by
  rcases h₁ : t.wJ with _ | ⟨a, as⟩ <;> rcases h₂ : t.wS with _ | ⟨b, bs⟩ <;>
    rcases h₃ : t.rowJb with _ | ⟨c, cs⟩ <;> rcases h₄ : t.rowSb with _ | ⟨d, ds⟩ <;>
    simp [prog, TM2.stepAux, Tp.get, h₁, h₂, h₃, h₄]

private theorem pair_loop (N : ℕ) (mn dd J S rj rs JI SI : List Bool) :
    ∀ (wj ws rjb rsb : List Bool) (v : Bool),
      wj.length ≤ N → ws.length ≤ N → rjb.length ≤ N → rsb.length ≤ N →
      ∃ v' T, RunLe prog ((30 * N + 30) * (wj.length + 1))
        ⟨some .col, v, (colT mn dd J S rj rs JI SI wj ws rjb rsb).get⟩
        ⟨some (if pairScan wj ws rjb rsb then .inner else .no), v', T⟩ ∧
        (pairScan wj ws rjb rsb = true → T = (colT mn dd J S rj rs JI SI [] [] [] []).get) := by
  intro wj
  induction h : wj.length using Nat.strong_induction_on generalizing wj with
  | _ n ih =>
    subst h
    intro ws rjb rsb v hwj hws hjb hsb
    have h₀ := col_peek (colT mn dd J S rj rs JI SI wj ws rjb rsb) v
    by_cases hemp : wj = [] ∧ ws = [] ∧ rjb = [] ∧ rsb = []
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := hemp
      have hr := (Run.head h₀ (Run.zero _)).le (le_refl 1)
      refine ⟨true, (colT mn dd J S rj rs JI SI [] [] [] []).get, ?_, fun _ => rfl⟩
      simpa [colT, pairScan_nil] using hr.mono (by simp)
    set R₀ := colT mn dd J S rj rs JI SI wj ws rjb rsb with hR₀
    set v₀ := wj.isEmpty && ws.isEmpty && rjb.isEmpty && rsb.isEmpty with hv₀
    have h₀' : RunLe prog 1 ⟨some .col, v, R₀.get⟩
        ⟨some (.split (.num .parJ) .read), v₀, R₀.get⟩ := by
      have := (Run.head h₀ (Run.zero _)).le (le_refl 1)
      simpa [hR₀, colT, hemp] using this
    -- four numbers
    obtain ⟨v₁, T₁, h₁, hT₁⟩ := num_run .parJ R₀.get v₀ wj rfl rfl rfl rfl rfl
    simp only [numSrc, numDst] at hT₁
    cases hu₁ : undelimit wj with
    | none =>
      have hf : pairScan wj ws rjb rsb = false := pairScan_false hemp (by
        intro _ _ _ _ _ _ _ _ g; rw [hu₁] at g; cases g)
      refine ⟨v₁, T₁, ?_, by simp [hf]⟩
      simpa [hu₁, hf] using (h₀'.trans h₁).mono (by nlinarith)
    | some pr₁ =>
    obtain ⟨pla, wj'⟩ := pr₁
    have hb₁ := block_length hu₁
    have e₁ := hT₁ _ _ hu₁
    rw [update_get _ _ rfl, update_get _ _ rfl] at e₁
    subst e₁
    have h₁' := h₁
    simp only [hu₁, Option.isSome_some, ↓reduceIte, afterNorm] at h₁'
    set R₁ := (R₀.set .wJ wj').set .lA (enc pla) with hR₁
    obtain ⟨v₂, T₂, h₂, hT₂⟩ := num_run .parS R₁.get v₁ ws rfl rfl rfl rfl rfl
    simp only [numSrc, numDst] at hT₂
    cases hu₂ : undelimit ws with
    | none =>
      have hf : pairScan wj ws rjb rsb = false := pairScan_false hemp (by
        intro _ _ _ _ _ _ _ _ _ g; rw [hu₂] at g; cases g)
      refine ⟨v₂, T₂, ?_, by simp [hf]⟩
      simpa [hu₂, hf] using ((h₀'.trans h₁').trans h₂).mono (by nlinarith)
    | some pr₂ =>
    obtain ⟨psa, ws'⟩ := pr₂
    have hb₂ := block_length hu₂
    have e₂ := hT₂ _ _ hu₂
    rw [update_get _ _ rfl, update_get _ _ rfl] at e₂
    subst e₂
    have h₂' := h₂
    simp only [hu₂, Option.isSome_some, ↓reduceIte, afterNorm] at h₂'
    set R₂ := (R₁.set .wS ws').set .sA (enc psa) with hR₂
    obtain ⟨v₃, T₃, h₃, hT₃⟩ := num_run .parJb R₂.get v₂ rjb rfl rfl rfl rfl rfl
    simp only [numSrc, numDst] at hT₃
    cases hu₃ : undelimit rjb with
    | none =>
      have hf : pairScan wj ws rjb rsb = false := pairScan_false hemp (by
        intro _ _ _ _ _ _ _ _ _ _ g; rw [hu₃] at g; cases g)
      refine ⟨v₃, T₃, ?_, by simp [hf]⟩
      simpa [hu₃, hf] using (((h₀'.trans h₁').trans h₂').trans h₃).mono (by nlinarith)
    | some pr₃ =>
    obtain ⟨plb, rjb'⟩ := pr₃
    have hb₃ := block_length hu₃
    have e₃ := hT₃ _ _ hu₃
    rw [update_get _ _ rfl, update_get _ _ rfl] at e₃
    subst e₃
    have h₃' := h₃
    simp only [hu₃, Option.isSome_some, ↓reduceIte, afterNorm] at h₃'
    set R₃ := (R₂.set .rowJb rjb').set .lB (enc plb) with hR₃
    obtain ⟨v₄, T₄, h₄, hT₄⟩ := num_run .parSb R₃.get v₃ rsb rfl rfl rfl rfl rfl
    simp only [numSrc, numDst] at hT₄
    cases hu₄ : undelimit rsb with
    | none =>
      have hf : pairScan wj ws rjb rsb = false := pairScan_false hemp (by
        intro _ _ _ _ _ _ _ _ _ _ _ g; rw [hu₄] at g; cases g)
      refine ⟨v₄, T₄, ?_, by simp [hf]⟩
      simpa [hu₄, hf] using ((((h₀'.trans h₁').trans h₂').trans h₃').trans h₄).mono
        (by nlinarith)
    | some pr₄ =>
    obtain ⟨psb, rsb'⟩ := pr₄
    have hb₄ := block_length hu₄
    have e₄ := hT₄ _ _ hu₄
    rw [update_get _ _ rfl, update_get _ _ rfl] at e₄
    subst e₄
    have h₄' := h₄
    simp only [hu₄, Option.isSome_some, ↓reduceIte, afterNorm] at h₄'
    set R₄ := (R₃.set .rowSb rsb').set .sB (enc psb) with hR₄
    have hA := (((h₀'.trans h₁').trans h₂').trans h₃').trans h₄'
    have l₁ := enc_length_le pla
    have l₂ := enc_length_le psa
    have l₃ := enc_length_le plb
    have l₄ := enc_length_le psb
    have hscan := pairScan_cons (sb := rsb) hu₁ hu₂ hu₃ hu₄
    -- comparisons
    obtain ⟨v₅, h₅⟩ := cmp_run .ab R₄.get v₄ (enc psa) (enc pla) (enc psb) rfl rfl rfl
      ⟨rfl, rfl, rfl⟩
    rw [value_enc, value_enc, value_enc] at h₅
    have hcol : ∃ v₆, RunLe prog (12 * N + 8) ⟨some (.cmp .ab (.compare 0)), v₄, R₄.get⟩
        ⟨some (if (decide (decodeNat psa + decodeNat pla ≤ decodeNat psb) ||
          decide (decodeNat psb + decodeNat plb ≤ decodeNat psa)) then .clean .col else .no),
          v₆, R₄.get⟩ := by
      by_cases hab : decodeNat psa + decodeNat pla ≤ decodeNat psb
      · exact ⟨v₅, by simpa [hab, afterCmp] using h₅.mono (by omega)⟩
      · have h₅' : RunLe prog (2 * ((enc psa).length + (enc pla).length + (enc psb).length) + 4)
            ⟨some (.cmp .ab (.compare 0)), v₄, R₄.get⟩
            ⟨some (.cmp .ba (.compare 0)), v₅, R₄.get⟩ := by
          simpa [hab, afterCmp] using h₅
        obtain ⟨v₆, h₆⟩ := cmp_run .ba R₄.get v₅ (enc psb) (enc plb) (enc psa) rfl rfl rfl
          ⟨rfl, rfl, rfl⟩
        rw [value_enc, value_enc, value_enc] at h₆
        refine ⟨v₆, ?_⟩
        by_cases hba : decodeNat psb + decodeNat plb ≤ decodeNat psa
        · simpa [hab, hba, afterCmp] using (h₅'.trans h₆).mono (by omega)
        · simpa [hab, hba, afterCmp] using (h₅'.trans h₆).mono (by omega)
    obtain ⟨v₆, h₆⟩ := hcol
    by_cases hsep : (decide (decodeNat psa + decodeNat pla ≤ decodeNat psb) ||
        decide (decodeNat psb + decodeNat plb ≤ decodeNat psa)) = true
    swap
    · have hf : pairScan wj ws rjb rsb = false := by
        rw [hscan]; simp only [Bool.not_eq_true] at hsep; simp [hsep]
      refine ⟨v₆, R₄.get, ?_, by simp [hf]⟩
      simpa [hsep, hf] using (hA.trans h₆).mono (by nlinarith)
    have h₆' : RunLe prog (12 * N + 8) ⟨some (.cmp .ab (.compare 0)), v₄, R₄.get⟩
        ⟨some (.clean .col), v₆, R₄.get⟩ := by simpa [hsep] using h₆
    obtain ⟨v₇, h₇⟩ := clean_run' .col R₄.get v₆ N (by
      intro k hk
      simp only [cleanKs, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · change (enc pla).length ≤ N; omega
      · change (enc psa).length ≤ N; omega
      · change (enc plb).length ≤ N; omega
      · change (enc psb).length ≤ N; omega)
    have hc₇ : (fun k => if k ∈ cleanKs .col then [] else R₄.get k) =
        (colT mn dd J S rj rs JI SI wj' ws' rjb' rsb').get := by
      funext k; cases k <;> simp [cleanKs, Tp.get, Tp.set, hR₄, hR₃, hR₂, hR₁, hR₀, colT]
    rw [hc₇] at h₇
    have hB := (hA.trans h₆').trans h₇
    obtain ⟨v₈, T, h₈, hT⟩ := ih wj'.length (by omega) wj' rfl ws' rjb' rsb' v₇
      (by omega) (by omega) (by omega) (by omega)
    have hscan' : pairScan wj ws rjb rsb = pairScan wj' ws' rjb' rsb' := by
      rw [hscan, hsep, Bool.true_and]
    refine ⟨v₈, T, ?_, fun hp => hT (hscan' ▸ hp)⟩
    rw [hscan']
    exact (hB.trans h₈).mono (by nlinarith)

end Pair

section Inner

/-! ### The inner loop: one job against all later jobs -/

open MetaMathlibExt
open Turing Function TM2Program TM2Embedding Cslib.Complexity.PolynomialEncoding
open Cslib.Complexity.FramedCNF MetaMathlibExt.BitstringEncoding Computability

private theorem innerScan_nil (ra sa : List Bool) : innerScan ra sa [] [] = true := by
  rw [innerScan]; simp

private theorem innerScan_false {ra sa J S : List Bool} (hne : ¬(J = [] ∧ S = []))
    (h : ∀ a b c d, undelimit J = some (a, b) → undelimit S = some (c, d) → False) :
    innerScan ra sa J S = false := by
  rw [innerScan, iteF _ _ hne]
  split
  · rename_i h₁ h₂; exact (h _ _ _ _ h₁ h₂).elim
  · rfl

private theorem innerScan_cons {ra sa J S rb J' sb S' : List Bool}
    (h₁ : undelimit J = some (rb, J')) (h₂ : undelimit S = some (sb, S')) :
    innerScan ra sa J S = (pairScan ra sa rb sb && innerScan ra sa J' S') := by
  rw [innerScan, iteF _ _ (fun h => undelimit_ne_nil h₁ h.1)]
  split
  · rename_i a b c d g₁ g₂
    rw [h₁] at g₁; rw [h₂] at g₂
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj g₁)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj g₂)
    rfl
  · rename_i hne
    exact absurd (hne _ _ _ _ h₁ h₂) id

private theorem C3_ge (N L : ℕ) : 30 * N + 30 ≤ (30 * N + 30) * (N + 3) * (L + 1) := by
  have h1 : 30 * N + 30 ≤ (30 * N + 30) * (N + 3) := Nat.le_mul_of_pos_right _ (by omega)
  exact h1.trans (Nat.le_mul_of_pos_right _ (by omega))

private def outT (mn dd J S : List Bool) : Tp := { mn := mn, dd := dd, jobsO := J, schedO := S }

private theorem inner_peek (t : Tp) (v : Bool) : TM2.step prog ⟨some .inner, v, t.get⟩ =
    some ⟨some (if t.jobsI = [] ∧ t.schedI = [] then .clean .innerEnd else .split .inJ .read),
      t.jobsI.isEmpty && t.schedI.isEmpty, t.get⟩ := by
  rcases h₁ : t.jobsI with _ | ⟨a, as⟩ <;> rcases h₂ : t.schedI with _ | ⟨b, bs⟩ <;>
    simp [prog, TM2.stepAux, Tp.get, h₁, h₂]

private theorem inner_loop (N : ℕ) (mn dd J S rj rs : List Bool) (hrj : rj.length ≤ N)
    (hrs : rs.length ≤ N) :
    ∀ (JI SI : List Bool) (v : Bool), JI.length ≤ N → SI.length ≤ N →
      ∃ v' T, RunLe prog ((30 * N + 30) * (N + 3) * (JI.length + 1))
        ⟨some .inner, v, (colT mn dd J S rj rs JI SI [] [] [] []).get⟩
        ⟨some (if innerScan rj rs JI SI then .outer else .no), v', T⟩ ∧
        (innerScan rj rs JI SI = true → T = (outT mn dd J S).get) := by
  intro JI
  induction h : JI.length using Nat.strong_induction_on generalizing JI with
  | _ n ih =>
    subst h
    intro SI v hJI hSI
    set R₀ := colT mn dd J S rj rs JI SI [] [] [] [] with hR₀
    have h₀ := inner_peek R₀ v
    by_cases hemp : JI = [] ∧ SI = []
    · obtain ⟨rfl, rfl⟩ := hemp
      have hr : RunLe prog 1 ⟨some .inner, v, R₀.get⟩ ⟨some (.clean .innerEnd), true, R₀.get⟩ := by
        have := (Run.head h₀ (Run.zero _)).le (le_refl 1)
        simpa [hR₀, colT] using this
      obtain ⟨v₁, h₁⟩ := clean_run' .innerEnd R₀.get true N (by
        intro k hk
        simp only [cleanKs, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl
        · exact hrj
        · exact hrs)
      have hc : (fun k => if k ∈ cleanKs .innerEnd then [] else R₀.get k) =
          (outT mn dd J S).get := by
        funext k; cases k <;> simp [cleanKs, Tp.get, hR₀, colT, outT]
      rw [hc] at h₁
      refine ⟨v₁, (outT mn dd J S).get, ?_, fun _ => rfl⟩
      have hc3 : 30 * N + 30 ≤ (30 * N + 30) * (N + 3) := Nat.le_mul_of_pos_right _ (by omega)
      simpa [innerScan_nil, afterClean] using (hr.trans h₁).mono (by omega)
    set v₀ := JI.isEmpty && SI.isEmpty
    have h₀' : RunLe prog 1 ⟨some .inner, v, R₀.get⟩ ⟨some (.split .inJ .read), v₀, R₀.get⟩ := by
      have := (Run.head h₀ (Run.zero _)).le (le_refl 1)
      simpa [hR₀, colT, hemp] using this
    obtain ⟨v₁, T₁, h₁, hT₁⟩ := split_run .inJ R₀.get v₀ rfl rfl
    simp only [splitIn, splitOut] at h₁ hT₁
    change ∃ v' T, RunLe prog _ _ _ ∧ _
    have hJ : R₀.get .jobsI = JI := rfl
    rw [hJ] at hT₁
    simp only [hJ] at h₁
    cases hu₁ : undelimit JI with
    | none =>
      have hf : innerScan rj rs JI SI = false := innerScan_false hemp (by
        intro _ _ _ _ g; rw [hu₁] at g; cases g)
      refine ⟨v₁, T₁, ?_, by simp [hf]⟩
      simpa [hu₁, hf] using (h₀'.trans h₁).mono (by have := C3_ge N JI.length; omega)
    | some pr₁ =>
    obtain ⟨rjb, JI'⟩ := pr₁
    have hb₁ := block_length hu₁
    have e₁ := hT₁ _ _ hu₁
    rw [update_get _ _ rfl, update_get _ _ rfl] at e₁
    subst e₁
    have h₁' := h₁
    simp only [hu₁, Option.isSome_some, ↓reduceIte, afterSplit] at h₁'
    set R₁ := (R₀.set .jobsI JI').set .rowJb rjb with hR₁
    obtain ⟨v₂, T₂, h₂, hT₂⟩ := split_run .inS R₁.get v₁ rfl rfl
    simp only [splitIn, splitOut] at h₂ hT₂
    have hS : R₁.get .schedI = SI := rfl
    rw [hS] at hT₂
    simp only [hS] at h₂
    cases hu₂ : undelimit SI with
    | none =>
      have hf : innerScan rj rs JI SI = false := innerScan_false hemp (by
        intro _ _ _ _ _ g; rw [hu₂] at g; cases g)
      refine ⟨v₂, T₂, ?_, by simp [hf]⟩
      simpa [hu₂, hf] using ((h₀'.trans h₁').trans h₂).mono (by
        have := C3_ge N JI.length; omega)
    | some pr₂ =>
    obtain ⟨rsb, SI'⟩ := pr₂
    have hb₂ := block_length hu₂
    have e₂ := hT₂ _ _ hu₂
    rw [update_get _ _ rfl, update_get _ _ rfl] at e₂
    subst e₂
    have h₂' := h₂
    simp only [hu₂, Option.isSome_some, ↓reduceIte, afterSplit] at h₂'
    set R₂ := (R₁.set .schedI SI').set .rowSb rsb with hR₂
    obtain ⟨v₃, h₃⟩ := copy_run .parJ R₂.get v₂ rj [] rfl rfl rfl
    rw [update_get _ _ rfl] at h₃
    obtain ⟨v₄, h₄⟩ := copy_run .parS (R₂.set .wJ (rj ++ [])).get v₃ rs [] rfl rfl rfl
    rw [update_get _ _ rfl] at h₄
    simp only [copyDst] at h₄
    have hR₄ : (R₂.set .wJ (rj ++ [])).set .wS (rs ++ []) =
        colT mn dd J S rj rs JI' SI' rj rs rjb rsb := by
      simp [hR₂, hR₁, hR₀, colT, Tp.set]
    rw [hR₄] at h₄
    simp only [afterCopy] at h₃ h₄
    obtain ⟨v₅, T₅, h₅, hT₅⟩ := pair_loop N mn dd J S rj rs JI' SI' rj rs rjb rsb v₄ hrj hrs
      (by omega) (by omega)
    have hscan := innerScan_cons (ra := rj) (sa := rs) hu₁ hu₂
    have hA := (((h₀'.trans h₁').trans h₂').trans h₃).trans h₄
    by_cases hp : pairScan rj rs rjb rsb = true
    swap
    · have hf : innerScan rj rs JI SI = false := by rw [hscan]; simp [hp]
      refine ⟨v₅, T₅, ?_, by simp [hf]⟩
      have hX : (30 * N + 30) * (rj.length + 1) ≤ (30 * N + 30) * (N + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have hY : (30 * N + 30) * (N + 3) ≤ (30 * N + 30) * (N + 3) * (JI.length + 1) :=
        Nat.le_mul_of_pos_right _ (by omega)
      have hZ : (30 * N + 30) * (N + 3) = (30 * N + 30) * (N + 1) + (60 * N + 60) := by ring
      simpa [hp, hf] using (hA.trans h₅).mono (by linarith)
    have h₅' : RunLe prog ((30 * N + 30) * (rj.length + 1))
        ⟨some .col, v₄, (colT mn dd J S rj rs JI' SI' rj rs rjb rsb).get⟩
        ⟨some .inner, v₅, (colT mn dd J S rj rs JI' SI' [] [] [] []).get⟩ := by
      have := h₅; rw [hT₅ hp] at this; simpa [hp] using this
    obtain ⟨v₆, T, h₆, hT⟩ := ih JI'.length (by omega) JI' rfl SI' v₅ (by omega) (by omega)
    have hscan' : innerScan rj rs JI SI = innerScan rj rs JI' SI' := by
      rw [hscan, hp, Bool.true_and]
    refine ⟨v₆, T, ?_, fun h' => hT (hscan' ▸ h')⟩
    rw [hscan']
    refine ((hA.trans h₅').trans h₆).mono ?_
    have hX : (30 * N + 30) * (rj.length + 1) ≤ (30 * N + 30) * (N + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hW : (30 * N + 30) * (N + 3) * (JI'.length + 1 + 1) ≤
        (30 * N + 30) * (N + 3) * (JI.length + 1) := Nat.mul_le_mul_left _ (by omega)
    have hZ : (30 * N + 30) * (N + 3) = (30 * N + 30) * (N + 1) + (60 * N + 60) := by ring
    have hV : (30 * N + 30) * (N + 3) * (JI'.length + 1 + 1) =
        (30 * N + 30) * (N + 3) * (JI'.length + 1) + (30 * N + 30) * (N + 3) := by ring
    linarith

end Inner

section Outer

/-! ### The outer loop over job rows -/

open MetaMathlibExt
open Turing Function TM2Program TM2Embedding Cslib.Complexity.PolynomialEncoding
open Cslib.Complexity.FramedCNF MetaMathlibExt.BitstringEncoding Computability

private theorem outerScan_nil (m D : ℕ) : outerScan m D [] [] = true := by
  rw [outerScan]; simp

private theorem outerScan_false {m D : ℕ} {J S : List Bool} (hne : ¬(J = [] ∧ S = []))
    (h : ∀ a b c d, undelimit J = some (a, b) → undelimit S = some (c, d) → False) :
    outerScan m D J S = false := by
  rw [outerScan, iteF _ _ hne]
  split
  · rename_i h₁ h₂; exact (h _ _ _ _ h₁ h₂).elim
  · rfl

private theorem outerScan_cons {m D : ℕ} {J S rj J' rs S' : List Bool}
    (h₁ : undelimit J = some (rj, J')) (h₂ : undelimit S = some (rs, S')) :
    outerScan m D J S = ((localScan D none rj rs == some m) && innerScan rj rs J' S' &&
      outerScan m D J' S') := by
  rw [outerScan, iteF _ _ (fun h => undelimit_ne_nil h₁ h.1)]
  split
  · rename_i a b c d g₁ g₂
    rw [h₁] at g₁; rw [h₂] at g₂
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj g₁)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj g₂)
    rfl
  · rename_i hne
    exact absurd (hne _ _ _ _ h₁ h₂) id

private theorem outer_peek (t : Tp) (v : Bool) : TM2.step prog ⟨some .outer, v, t.get⟩ =
    some ⟨some (if t.jobsO = [] ∧ t.schedO = [] then .yes else .split .outJ .read),
      t.jobsO.isEmpty && t.schedO.isEmpty, t.get⟩ := by
  rcases h₁ : t.jobsO with _ | ⟨a, as⟩ <;> rcases h₂ : t.schedO with _ | ⟨b, bs⟩ <;>
    simp [prog, TM2.stepAux, Tp.get, h₁, h₂]

private theorem C4_ge (N L : ℕ) : (30 * N + 30) * (N + 3) * (N + 3) ≤
    (30 * N + 30) * (N + 3) * (N + 3) * (L + 1) := Nat.le_mul_of_pos_right _ (by omega)

private theorem outer_loop (N m D : ℕ) (mn dd : List Bool) (hmn : mn = encodeNat m)
    (hdd : dd = encodeNat D) (hmN : mn.length ≤ N) (hdN : dd.length ≤ N) :
    ∀ (J S : List Bool) (v : Bool), J.length ≤ N → S.length ≤ N →
      ∃ v' T, RunLe prog ((30 * N + 30) * (N + 3) * (N + 3) * (J.length + 1))
        ⟨some .outer, v, (outT mn dd J S).get⟩
        ⟨some (if outerScan m D J S then .yes else .no), v', T⟩ := by
  have hC : 30 * N + 30 ≤ (30 * N + 30) * (N + 3) := Nat.le_mul_of_pos_right _ (by omega)
  have hC' : (30 * N + 30) * (N + 3) ≤ (30 * N + 30) * (N + 3) * (N + 3) :=
    Nat.le_mul_of_pos_right _ (by omega)
  intro J
  induction h : J.length using Nat.strong_induction_on generalizing J with
  | _ n ih =>
    subst h
    intro S v hJ hS
    have hC4 := C4_ge N J.length
    set R₀ := outT mn dd J S with hR₀
    have h₀ := outer_peek R₀ v
    by_cases hemp : J = [] ∧ S = []
    · obtain ⟨rfl, rfl⟩ := hemp
      have hr := (Run.head h₀ (Run.zero _)).le (le_refl 1)
      refine ⟨true, R₀.get, ?_⟩
      simpa [hR₀, outT, outerScan_nil] using hr.mono (by omega)
    set v₀ := J.isEmpty && S.isEmpty
    have h₀' : RunLe prog 1 ⟨some .outer, v, R₀.get⟩ ⟨some (.split .outJ .read), v₀, R₀.get⟩ := by
      have := (Run.head h₀ (Run.zero _)).le (le_refl 1)
      simpa [hR₀, outT, hemp] using this
    obtain ⟨v₁, T₁, h₁, hT₁⟩ := split_run .outJ R₀.get v₀ rfl rfl
    simp only [splitIn, splitOut] at h₁ hT₁
    have hJ' : R₀.get .jobsO = J := rfl
    rw [hJ'] at hT₁
    simp only [hJ'] at h₁
    cases hu₁ : undelimit J with
    | none =>
      have hf : outerScan m D J S = false := outerScan_false hemp (by
        intro _ _ _ _ g; rw [hu₁] at g; cases g)
      refine ⟨v₁, T₁, ?_⟩
      simpa [hu₁, hf] using (h₀'.trans h₁).mono (by omega)
    | some pr₁ =>
    obtain ⟨rj, J'⟩ := pr₁
    have hb₁ := block_length hu₁
    have e₁ := hT₁ _ _ hu₁
    rw [update_get _ _ rfl, update_get _ _ rfl] at e₁
    subst e₁
    have h₁' := h₁
    simp only [hu₁, Option.isSome_some, ↓reduceIte, afterSplit] at h₁'
    set R₁ := (R₀.set .jobsO J').set .rowJ rj with hR₁
    obtain ⟨v₂, T₂, h₂, hT₂⟩ := split_run .outS R₁.get v₁ rfl rfl
    simp only [splitIn, splitOut] at h₂ hT₂
    have hS' : R₁.get .schedO = S := rfl
    rw [hS'] at hT₂
    simp only [hS'] at h₂
    cases hu₂ : undelimit S with
    | none =>
      have hf : outerScan m D J S = false := outerScan_false hemp (by
        intro _ _ _ _ _ g; rw [hu₂] at g; cases g)
      refine ⟨v₂, T₂, ?_⟩
      simpa [hu₂, hf] using ((h₀'.trans h₁').trans h₂).mono (by omega)
    | some pr₂ =>
    obtain ⟨rs, S'⟩ := pr₂
    have hb₂ := block_length hu₂
    have e₂ := hT₂ _ _ hu₂
    rw [update_get _ _ rfl, update_get _ _ rfl] at e₂
    subst e₂
    have h₂' := h₂
    simp only [hu₂, Option.isSome_some, ↓reduceIte, afterSplit] at h₂'
    set R₂ := (R₁.set .schedO S').set .rowS rs with hR₂
    obtain ⟨v₃, h₃⟩ := copy_run .locJ R₂.get v₂ rj [] rfl rfl rfl
    rw [update_get _ _ rfl] at h₃
    obtain ⟨v₄, h₄⟩ := copy_run .locS (R₂.set .wJ (rj ++ [])).get v₃ rs [] rfl rfl rfl
    rw [update_get _ _ rfl] at h₄
    simp only [copyDst, afterCopy] at h₃ h₄
    have hR₄ : (R₂.set .wJ (rj ++ [])).set .wS (rs ++ []) =
        locT mn dd J' S' rj rs rj rs none [] := by
      simp [hR₂, hR₁, hR₀, outT, locT, Tp.set, pvS, pvL]
    rw [hR₄] at h₄
    have hscan := outerScan_cons (m := m) (D := D) hu₁ hu₂
    have hA := (((h₀'.trans h₁').trans h₂').trans h₃).trans h₄
    obtain ⟨v₅, T₅, h₅, hT₅⟩ := loc_loop N D mn dd J' S' rj rs hdd hdN rj rs none [] v₄
      (by omega) (by omega) ⟨by simp [pvS], by simp [pvL]⟩ (by simp; omega)
    simp only [Option.map_none] at h₅ hT₅
    have hX : (30 * N + 30) * (rj.length + 1) ≤ (30 * N + 30) * (N + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    cases hl : localScan D none rj rs with
    | none =>
      have hf : outerScan m D J S = false := by rw [hscan, hl]; rfl
      refine ⟨v₅, T₅, ?_⟩
      simpa [hl, hf] using (hA.trans h₅).mono (by nlinarith)
    | some k =>
    obtain ⟨pv', c', hT', hv', hl', hb'⟩ := hT₅ k hl
    subst hT'
    have h₅' : RunLe prog ((30 * N + 30) * (rj.length + 1))
        ⟨some .loc, v₄, (locT mn dd J' S' rj rs rj rs none []).get⟩
        ⟨some (.cmp .cntLe (.compare 0)), v₅, (locT mn dd J' S' rj rs [] [] pv' c').get⟩ := by
      simpa [hl] using h₅
    set R₅ := locT mn dd J' S' rj rs [] [] pv' c' with hR₅
    have hB := hA.trans h₅'
    simp only [Compare.value, zero_add] at hv'
    obtain ⟨v₆, h₆⟩ := cmp_run .cntLe R₅.get v₅ c' [] mn rfl rfl rfl ⟨rfl, rfl, rfl⟩
    rw [hmn, Compare.value_encodeNat, ← hmn, hv'] at h₆
    simp only [Compare.value, add_zero, List.length_nil] at h₆
    by_cases hle : k ≤ m
    swap
    · have hne : k ≠ m := by omega
      have hf : outerScan m D J S = false := by rw [hscan, hl]; simp [hne]
      refine ⟨v₆, R₅.get, ?_⟩
      simpa [hle, hf, afterCmp] using (hB.trans h₆).mono (by nlinarith)
    have h₆' : RunLe prog (2 * (c'.length + mn.length) + 4)
        ⟨some (.cmp .cntLe (.compare 0)), v₅, R₅.get⟩
        ⟨some (.cmp .cntGe (.compare 0)), v₆, R₅.get⟩ := by
      simpa [hle, afterCmp] using h₆
    obtain ⟨v₇, h₇⟩ := cmp_run .cntGe R₅.get v₆ mn [] c' rfl rfl rfl ⟨rfl, rfl, rfl⟩
    rw [hmn, Compare.value_encodeNat, ← hmn, hv'] at h₇
    simp only [Compare.value, add_zero, List.length_nil] at h₇
    by_cases hge : m ≤ k
    swap
    · have hne : k ≠ m := by omega
      have hf : outerScan m D J S = false := by rw [hscan, hl]; simp [hne]
      refine ⟨v₇, R₅.get, ?_⟩
      simpa [hge, hf, afterCmp] using ((hB.trans h₆').trans h₇).mono (by nlinarith)
    have h₇' : RunLe prog (2 * (mn.length + c'.length) + 4)
        ⟨some (.cmp .cntGe (.compare 0)), v₆, R₅.get⟩
        ⟨some (.clean .locEnd), v₇, R₅.get⟩ := by
      simpa [hge, afterCmp] using h₇
    have hkm : k = m := le_antisymm hle hge
    rw [hkm] at hl
    obtain ⟨v₈, h₈⟩ := clean_run' .locEnd R₅.get v₇ N (by
      intro j hj
      simp only [cleanKs, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl
      · exact hl'
      · exact hb'.2
      · exact hb'.1)
    have hc₈ : (fun j => if j ∈ cleanKs .locEnd then [] else R₅.get j) =
        (outT mn dd J' S' |>.set .rowJ rj |>.set .rowS rs).get := by
      funext j; cases j <;> simp [cleanKs, Tp.get, Tp.set, hR₅, locT, outT]
    rw [hc₈] at h₈
    simp only [afterClean] at h₈
    obtain ⟨v₉, h₉⟩ := copy_run .inJ (outT mn dd J' S' |>.set .rowJ rj |>.set .rowS rs).get v₈
      J' [] rfl rfl rfl
    rw [update_get _ _ rfl] at h₉
    obtain ⟨v₁₀, h₁₀⟩ := copy_run .inS
      ((outT mn dd J' S' |>.set .rowJ rj |>.set .rowS rs).set .jobsI (J' ++ [])).get v₉
      S' [] rfl rfl rfl
    rw [update_get _ _ rfl] at h₁₀
    simp only [copyDst, afterCopy] at h₉ h₁₀
    have hR₁₀ : ((outT mn dd J' S' |>.set .rowJ rj |>.set .rowS rs).set .jobsI (J' ++ [])).set
        .schedI (S' ++ []) = colT mn dd J' S' rj rs J' S' [] [] [] [] := by
      simp [outT, colT, Tp.set]
    rw [hR₁₀] at h₁₀
    have hC := ((((hB.trans h₆').trans h₇').trans h₈).trans h₉).trans h₁₀
    obtain ⟨v₁₁, T₁₁, h₁₁, hT₁₁⟩ := inner_loop N mn dd J' S' rj rs (by omega) (by omega) J' S'
      v₁₀ (by omega) (by omega)
    have hY : (30 * N + 30) * (N + 3) * (J'.length + 1) ≤ (30 * N + 30) * (N + 3) * (N + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    by_cases hi : innerScan rj rs J' S' = true
    swap
    · have hf : outerScan m D J S = false := by rw [hscan, hl]; simp [hi]
      refine ⟨v₁₁, T₁₁, ?_⟩
      simpa [hi, hf] using (hC.trans h₁₁).mono (by nlinarith)
    have h₁₁' : RunLe prog ((30 * N + 30) * (N + 3) * (J'.length + 1))
        ⟨some .inner, v₁₀, (colT mn dd J' S' rj rs J' S' [] [] [] []).get⟩
        ⟨some .outer, v₁₁, (outT mn dd J' S').get⟩ := by
      have := h₁₁; rw [hT₁₁ hi] at this; simpa [hi] using this
    obtain ⟨v₁₂, T, h₁₂⟩ := ih J'.length (by omega) J' rfl S' v₁₁ (by omega) (by omega)
    have hscan' : outerScan m D J S = outerScan m D J' S' := by
      rw [hscan, hl, hi]; simp
    refine ⟨v₁₂, T, ?_⟩
    rw [hscan']
    refine ((hC.trans h₁₁').trans h₁₂).mono ?_
    have hW : (30 * N + 30) * (N + 3) * (N + 3) * (J'.length + 1 + 1) ≤
        (30 * N + 30) * (N + 3) * (N + 3) * (J.length + 1) := Nat.mul_le_mul_left _ (by omega)
    have hV : (30 * N + 30) * (N + 3) * (N + 3) * (J'.length + 1 + 1) =
        (30 * N + 30) * (N + 3) * (N + 3) * (J'.length + 1) +
          (30 * N + 30) * (N + 3) * (N + 3) := by ring
    have hU : (30 * N + 30) * (N + 3) * (N + 3) =
        (30 * N + 30) * (N + 3) * (N + 1) + 2 * ((30 * N + 30) * (N + 3)) := by ring
    linarith

end Outer

section Top

/-! ### The whole verifier run, its polynomial-time bound, and NP membership -/

open MetaMathlibExt
open Turing Function TM2Program TM2Embedding Cslib.Complexity.PolynomialEncoding
open Cslib.Complexity.FramedCNF MetaMathlibExt.BitstringEncoding Computability

private theorem encodeNat_eq_nil_iff (n : ℕ) : encodeNat n = [] ↔ n = 0 := by
  constructor
  · intro h
    by_contra hn
    rw [TM2Recursive.encodeNat_eq_cons hn] at h
    cases h
  · rintro rfl; rfl

private theorem checkD_step (t : Tp) (v : Bool) : TM2.step prog ⟨some .checkD, v, t.get⟩ =
    some ⟨some (if t.dd = [] then .no else .norm .mn (.read none)), t.dd.isEmpty, t.get⟩ := by
  rcases h : t.dd with _ | ⟨a, as⟩ <;> simp [prog, TM2.stepAux, Tp.get, h]

private theorem checkM_step (t : Tp) (v : Bool) : TM2.step prog ⟨some .checkM, v, t.get⟩ =
    some ⟨some (if t.mn = [] then .no else .outer), t.mn.isEmpty, t.get⟩ := by
  rcases h : t.mn with _ | ⟨a, as⟩ <;> simp [prog, TM2.stepAux, Tp.get, h]

private theorem check_eq {x w M R Jp E : List Bool} (hx : undelimit x = some (M, R))
    (hR : undelimit R = some (Jp, E)) :
    check x w = (decide (0 < decodeNat M) && decide (0 < decodeNat E) &&
      outerScan (decodeNat M) (decodeNat E) Jp w) := by
  unfold check
  rw [hx]
  dsimp only
  rw [hR]

private theorem run (x w : List Bool) :
    ∃ v T, RunLe prog (40 * (x.length + w.length + 3) ^ 4)
      ⟨some (.split .top1 .read), false, ({ raw := x, schedO := w } : Tp).get⟩
      ⟨some (if check x w then .yes else .no), v, T⟩ := by
  set N := x.length + w.length with hN
  have hP4 : N + 3 ≤ (N + 3) ^ 4 := Nat.le_self_pow (by norm_num) _
  have hP : 6 * N + 10 ≤ 10 * (N + 3) ^ 4 := by omega
  set T₀ : Tp := { raw := x, schedO := w } with hT₀
  obtain ⟨v₁, T₁, h₁, hT₁⟩ := split_run .top1 T₀.get false rfl rfl
  simp only [splitIn, splitOut] at h₁ hT₁
  have hx₀ : T₀.get .raw = x := rfl
  rw [hx₀] at hT₁
  simp only [hx₀] at h₁
  cases hu₁ : undelimit x with
  | none =>
    have hc : check x w = false := by unfold check; rw [hu₁]
    refine ⟨v₁, T₁, ?_⟩
    simpa [hu₁, hc] using h₁.mono (by nlinarith)
  | some pr₁ =>
  obtain ⟨M, R⟩ := pr₁
  have hb₁ := block_length hu₁
  have e₁ := hT₁ _ _ hu₁
  rw [update_get _ _ rfl, update_get _ _ rfl] at e₁
  subst e₁
  have h₁' := h₁
  simp only [hu₁, Option.isSome_some, ↓reduceIte, afterSplit] at h₁'
  set T₁ := (T₀.set .raw R).set .mraw M with hT₁d
  obtain ⟨v₂, T₂, h₂, hT₂⟩ := split_run .top2 T₁.get v₁ rfl rfl
  simp only [splitIn, splitOut] at h₂ hT₂
  have hr₁ : T₁.get .raw = R := rfl
  rw [hr₁] at hT₂
  simp only [hr₁] at h₂
  cases hu₂ : undelimit R with
  | none =>
    have hc : check x w = false := by unfold check; rw [hu₁]; dsimp only; rw [hu₂]
    refine ⟨v₂, T₂, ?_⟩
    simpa [hu₂, hc] using (h₁'.trans h₂).mono (by nlinarith)
  | some pr₂ =>
  obtain ⟨Jp, E⟩ := pr₂
  have hb₂ := block_length hu₂
  have e₂ := hT₂ _ _ hu₂
  rw [update_get _ _ rfl, update_get _ _ rfl] at e₂
  subst e₂
  have h₂' := h₂
  simp only [hu₂, Option.isSome_some, ↓reduceIte, afterSplit] at h₂'
  set T₂ := (T₁.set .raw E).set .jobsO Jp with hT₂d
  obtain ⟨v₃, h₃⟩ := norm_run .dd T₂.get v₂ rfl rfl
  simp only [normIn, normOut, afterNorm] at h₃
  have hE : T₂.get .raw = E := rfl
  rw [hE, update_get _ _ rfl, update_get _ _ rfl, normalizeNat_eq_encode_decode] at h₃
  set T₃ := (T₂.set .raw []).set .dd (encodeNat (decodeNat E)) with hT₃d
  have hc := check_eq (w := w) hu₁ hu₂
  have hlE : (encodeNat (decodeNat E)).length ≤ E.length + 1 := enc_length_le E
  have hlM : (encodeNat (decodeNat M)).length ≤ M.length + 1 := enc_length_le M
  have hA := h₁'.trans h₂'
  -- the deadline check
  have h₄ := checkD_step T₃ v₃
  by_cases hD : decodeNat E = 0
  · have hz : encodeNat (decodeNat E) = [] := (encodeNat_eq_nil_iff _).mpr hD
    have hf : check x w = false := by rw [hc, hD]; simp
    refine ⟨T₃.dd.isEmpty, T₃.get, ?_⟩
    have h₄' : RunLe prog 1 ⟨some .checkD, v₃, T₃.get⟩ ⟨some .no, T₃.dd.isEmpty, T₃.get⟩ := by
      have := (Run.head h₄ (Run.zero _)).le (le_refl 1)
      simpa [hT₃d, Tp.set, hz] using this
    simpa [hf] using ((hA.trans h₃).trans h₄').mono (by nlinarith)
  have hnz : encodeNat (decodeNat E) ≠ [] := fun h => hD ((encodeNat_eq_nil_iff _).mp h)
  have h₄' : RunLe prog 1 ⟨some .checkD, v₃, T₃.get⟩
      ⟨some (.norm .mn (.read none)), T₃.dd.isEmpty, T₃.get⟩ := by
    have := (Run.head h₄ (Run.zero _)).le (le_refl 1)
    simpa [hT₃d, Tp.set, hnz] using this
  obtain ⟨v₅, h₅⟩ := norm_run .mn T₃.get T₃.dd.isEmpty rfl rfl
  simp only [normIn, normOut, afterNorm] at h₅
  have hMr : T₃.get .mraw = M := rfl
  rw [hMr, update_get _ _ rfl, update_get _ _ rfl, normalizeNat_eq_encode_decode] at h₅
  set T₄ := (T₃.set .mraw []).set .mn (encodeNat (decodeNat M)) with hT₄d
  have h₆ := checkM_step T₄ v₅
  have hB := ((hA.trans h₃).trans h₄').trans h₅
  by_cases hM : decodeNat M = 0
  · have hz : encodeNat (decodeNat M) = [] := (encodeNat_eq_nil_iff _).mpr hM
    have hf : check x w = false := by rw [hc, hM]; simp
    refine ⟨T₄.mn.isEmpty, T₄.get, ?_⟩
    have h₆' : RunLe prog 1 ⟨some .checkM, v₅, T₄.get⟩ ⟨some .no, T₄.mn.isEmpty, T₄.get⟩ := by
      have := (Run.head h₆ (Run.zero _)).le (le_refl 1)
      simpa [hT₄d, Tp.set, hz] using this
    simpa [hf] using (hB.trans h₆').mono (by nlinarith)
  have hnzM : encodeNat (decodeNat M) ≠ [] := fun h => hM ((encodeNat_eq_nil_iff _).mp h)
  have h₆' : RunLe prog 1 ⟨some .checkM, v₅, T₄.get⟩ ⟨some .outer, T₄.mn.isEmpty, T₄.get⟩ := by
    have := (Run.head h₆ (Run.zero _)).le (le_refl 1)
    simpa [hT₄d, Tp.set, hnzM] using this
  have hT₄ : T₄ = outT (encodeNat (decodeNat M)) (encodeNat (decodeNat E)) Jp w := by
    simp [hT₄d, hT₃d, hT₂d, hT₁d, hT₀, Tp.set, outT]
  rw [hT₄] at h₆'
  have hJp : Jp.length ≤ N := by omega
  obtain ⟨v₇, T, h₇⟩ := outer_loop N (decodeNat M) (decodeNat E) _ _ rfl rfl (by omega)
    (by omega) Jp w T₄.mn.isEmpty hJp (by omega)
  have hpos : 0 < decodeNat M ∧ 0 < decodeNat E := ⟨Nat.pos_of_ne_zero hM, Nat.pos_of_ne_zero hD⟩
  have hc' : check x w = outerScan (decodeNat M) (decodeNat E) Jp w := by
    rw [hc]; simp [hpos.1, hpos.2]
  refine ⟨v₇, T, ?_⟩
  rw [hc']
  refine ((hB.trans h₆').trans h₇).mono ?_
  have hY : (30 * N + 30) * (N + 3) * (N + 3) * (Jp.length + 1) ≤
      (30 * N + 30) * (N + 3) * (N + 3) * (N + 3) := Nat.mul_le_mul_left _ (by omega)
  have hZ : (30 * N + 30) * (N + 3) * (N + 3) * (N + 3) ≤ 30 * (N + 3) ^ 4 := by
    have : 30 * N + 30 ≤ 30 * (N + 3) := by omega
    calc (30 * N + 30) * (N + 3) * (N + 3) * (N + 3)
        ≤ 30 * (N + 3) * (N + 3) * (N + 3) * (N + 3) := by gcongr
      _ = 30 * (N + 3) ^ 4 := by ring
  nlinarith

/-! ## Polynomial time -/

private abbrev comp : Cslib.Complexity.Host.Comp where
  K := K
  Γ := fun _ => Bool
  L := Lab
  prog := prog
  ks := keys
  ks_nodup := by decide
  mem_ks := mem_keys

theorem isPolyTime_check :
    ComplexityTheory.IsPolyTime (fun q : List Bool × List Bool => check q.1 q.2) :=
  Cslib.Complexity.Host.isPolyTime_verifier
    (c := comp) (cX := .raw) (cW := .schedO) (gX := id) (gW := id)
    (start := .split .top1 .read) (yes := .yes) (no := .no) check
    (Polynomial.C 40 * (Polynomial.X + Polynomial.C 3) ^ 4) (by decide) (by decide) rfl rfl
    fun x w => by
      obtain ⟨v, T, h⟩ := run x w
      have hS : update (update (fun _ => ([] : List Bool)) K.raw (x.map id)) K.schedO
          (w.map id) = ({ raw := x, schedO := w } : Tp).get := by
        funext k; cases k <;> simp [Tp.get]
      refine ⟨v, T, ?_⟩
      rw [hS]
      simpa using h

end Top

section Membership

open MetaMathlibExt MetaMathlibExt.Complexity.NPComplete.FlowShopScheduling

/-- The verifier on pairs of bitstrings. -/
private def schedVerifyGeneral (q : List Bool × List Bool) : Bool := check q.1 q.2

private theorem isPolyTime_schedVerifyGeneral : ComplexityTheory.IsPolyTime schedVerifyGeneral :=
  isPolyTime_check

/-- **FLOW-SHOP SCHEDULING with `m` part of the instance belongs to NP.** -/
private theorem flowShopScheduling_mem_NP :
    flowShopSchedulingDec ∈ ComplexityTheory.NP := by
  refine ⟨Polynomial.C 3 * Polynomial.X * (Polynomial.C 2 * Polynomial.X + 1),
    schedVerifyGeneral, isPolyTime_schedVerifyGeneral, ?_⟩
  intro x
  have h := dec_iff_check x
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_add,
    Polynomial.eval_one]
  exact h

end Membership

end Verification

/-- **FLOW-SHOP SCHEDULING is in NP.** A polynomial-time multi-stack Turing machine checks a
schedule of polynomial length. -/
public theorem flowShopScheduling_mem_NP :
    flowShopSchedulingDec ∈ MetaMathlibExt.ComplexityTheory.NP :=
  Verification.flowShopScheduling_mem_NP

end MetaMathlibExt.Complexity.NPComplete.FlowShopScheduling
