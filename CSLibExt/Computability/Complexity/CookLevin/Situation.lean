/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.CookLevin.Shift

/-!
# Cook-Levin: situation tables of a `FinTM2` and the correctness of the formula

For an arbitrary `M : FinTM2` (work alphabets may be infinite and need no `DecidableEq`), an
encoding record `Enc M` fixes finite effective alphabets and numberings of stacks and of
(label, state) pairs; `Enc.ofFinTM2` builds one classically for every `M`. From it this file
defines the finite tables `la, wa, na, sa, pl, cn, pu` that the clause generators take as
parameters: a *situation* is a (label, state) pair together with the window of top cells it reads.

The step on a situation is defined on `Option Λ`; the halted label `none` steps to itself with no
pushes and no consumption, so halted rows need no separate family.

Main results:
* `eff_agree`, `step_agree`, `Enc.table_agree`, `Enc.table_agree_run`: the tables agree with
  `TM2.step`;
* `Enc.decRow` and its round trips: decoding a row of the tableau;
* `sh_force`, `Enc.sh_step_run`: the shift clauses force the next row's cells;
* `Enc.accept_sound`, `Enc.accept_complete`, and `Enc.five_iff`: the conjunction of the five
  families is satisfiable iff some certificate makes `M` accept within `T` steps;
* `runI_haltList`: the link to `TM2OutputsInTime`.

Concrete checks of the tables against real runs of two small machines are in
`CSLibExtTest/Computability/Complexity/CookLevinSituationTests.lean`.
-/

@[expose] public section


namespace Cslib.Complexity.CookLevin.Situation

open MetaMathlibExt

open Turing Function

/-! ## [B3] The symbolic effect of one statement tree, computed from windows only -/

section Eff

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- Top of stack `k` as seen from the windows: the last symbol pushed in this step if any,
otherwise window entry `c k` (below the `c k` original symbols already consumed; `none` = ⊥). -/
def readTop (W : ∀ k, List (Option (Γ k))) (P : ∀ k, List (Γ k)) (c : K → ℕ) (k : K) :
    Option (Γ k) :=
  match P k with
  | x :: _ => some x
  | [] => (W k).getD (c k) none

/-- Effect of a statement tree: new label, new state, `P k` = symbols pushed this step and still on
top, `c k` = net original symbols consumed (a push followed by a pop cancels). -/
def eff (W : ∀ k, List (Option (Γ k))) :
    TM2.Stmt Γ Λ σ → σ → (∀ k, List (Γ k)) → (K → ℕ) →
      Option Λ × σ × (∀ k, List (Γ k)) × (K → ℕ)
  | .push k f q, v, P, c => eff W q v (update P k (f v :: P k)) c
  | .peek k f q, v, P, c => eff W q (f v (readTop W P c k)) P c
  | .pop k f q, v, P, c =>
      eff W q (f v (readTop W P c k)) (update P k (P k).tail)
        (if (P k).isEmpty then update c k (c k + 1) else c)
  | .load a q, v, P, c => eff W q (a v) P c
  | .branch p q₁ q₂, v, P, c => cond (p v) (eff W q₁ v P c) (eff W q₂ v P c)
  | .goto f, v, P, c => (some (f v), v, P, c)
  | .halt, v, P, c => (none, v, P, c)

/-- Maximum number of `push`/`peek`/`pop` nodes on a root-to-leaf path. -/
def ops : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => ops q + 1
  | .peek _ _ q => ops q + 1
  | .pop _ _ q => ops q + 1
  | .load _ q => ops q
  | .branch _ q₁ q₂ => max (ops q₁) (ops q₂)
  | .goto _ => 0
  | .halt => 0

/-- `x` can be pushed onto stack `k` by some `push` node of `q` (for some state). -/
def PushSym (k : K) : TM2.Stmt Γ Λ σ → Γ k → Prop
  | .push k' f q, x => (∃ (h : k' = k) (v : σ), x = cast (congrArg Γ h) (f v)) ∨ PushSym k q x
  | .peek _ _ q, x => PushSym k q x
  | .pop _ _ q, x => PushSym k q x
  | .load _ q, x => PushSym k q x
  | .branch _ q₁ q₂, x => PushSym k q₁ x ∨ PushSym k q₂ x
  | .goto _, _ => False
  | .halt, _ => False

theorem length_update_le (P : ∀ k, List (Γ k)) (k₀ k : K) (l : List (Γ k₀))
    (h : l.length ≤ (P k₀).length + 1) : (update P k₀ l k).length ≤ (P k).length + 1 := by
  by_cases hk : k = k₀
  · subst hk; simpa using h
  · rw [update_of_ne hk]; omega

/-- Pushes still on top and net consumption each grow by at most `ops q`. -/
theorem eff_bound (W : ∀ k, List (Option (Γ k))) (q : TM2.Stmt Γ Λ σ) :
    ∀ (v : σ) (P : ∀ k, List (Γ k)) (c : K → ℕ) (k : K),
      ((eff W q v P c).2.2.1 k).length ≤ (P k).length + ops q ∧
        (eff W q v P c).2.2.2 k ≤ c k + ops q := by
  induction q with
  | push k₀ f q ih =>
      intro v P c k
      obtain ⟨h1, h2⟩ := ih v (update P k₀ (f v :: P k₀)) c k
      have := length_update_le P k₀ k (f v :: P k₀) (by simp)
      simp only [eff, ops]; omega
  | peek k₀ f q ih =>
      intro v P c k
      obtain ⟨h1, h2⟩ := ih (f v (readTop W P c k₀)) P c k
      simp only [eff, ops]; omega
  | pop k₀ f q ih =>
      intro v P c k
      obtain ⟨h1, h2⟩ := ih (f v (readTop W P c k₀)) (update P k₀ (P k₀).tail)
        (if (P k₀).isEmpty then update c k₀ (c k₀ + 1) else c) k
      have e1 := length_update_le P k₀ k (P k₀).tail (by simp; omega)
      have e2 : (if (P k₀).isEmpty then update c k₀ (c k₀ + 1) else c) k ≤ c k + 1 := by
        split
        · by_cases hk : k = k₀
          · subst hk; simp
          · rw [update_of_ne hk]; omega
        · omega
      simp only [eff, ops]; omega
  | load a q ih =>
      intro v P c k
      exact ih (a v) P c k
  | branch p q₁ q₂ ih₁ ih₂ =>
      intro v P c k
      simp only [eff, ops]
      cases p v
      · obtain ⟨h1, h2⟩ := ih₂ v P c k; simp only [Bool.cond_false]; omega
      · obtain ⟨h1, h2⟩ := ih₁ v P c k; simp only [Bool.cond_true]; omega
  | goto f => intro v P c k; simp [eff]
  | halt => intro v P c k; simp [eff]

/-- Every symbol left in `P` is one that was there already or one `q` can push. -/
theorem eff_pushed (W : ∀ k, List (Option (Γ k))) (Q : ∀ k, Γ k → Prop) (q : TM2.Stmt Γ Λ σ)
    (hq : ∀ k x, PushSym k q x → Q k x) :
    ∀ (v : σ) (P : ∀ k, List (Γ k)) (c : K → ℕ), (∀ k, ∀ x ∈ P k, Q k x) →
      ∀ k, ∀ x ∈ (eff W q v P c).2.2.1 k, Q k x := by
  induction q with
  | push k₀ f q ih =>
      intro v P c hP
      refine ih (fun k x h => hq k x (Or.inr h)) v _ c ?_
      intro k x hx
      by_cases hk : k = k₀
      · subst hk
        rw [update_self, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hq k (f v) (Or.inl ⟨rfl, v, rfl⟩)
        · exact hP k x hx
      · rw [update_of_ne hk] at hx; exact hP k x hx
  | peek k₀ f q ih =>
      intro v P c hP; exact ih hq _ P c hP
  | pop k₀ f q ih =>
      intro v P c hP
      refine ih hq _ _ _ ?_
      intro k x hx
      by_cases hk : k = k₀
      · subst hk
        rw [update_self] at hx
        exact hP k x (List.mem_of_mem_tail hx)
      · rw [update_of_ne hk] at hx; exact hP k x hx
  | load a q ih =>
      intro v P c hP; exact ih hq _ P c hP
  | branch p q₁ q₂ ih₁ ih₂ =>
      intro v P c hP
      simp only [eff]
      cases p v
      · exact ih₂ (fun k x h => hq k x (Or.inr h)) v P c hP
      · exact ih₁ (fun k x h => hq k x (Or.inl h)) v P c hP
  | goto f => intro v P c hP; exact hP
  | halt => intro v P c hP; exact hP

end Eff

/-! ## [B3] Encoding data for a real machine -/

/-- Stack numbering, combined (label, state) code, and finite effective alphabets (B2's `Γfin`)
of `M`. Symbol code `0` is ⊥; symbol `dec k i` has code `i + 1`. -/
structure Enc (M : FinTM2) where
  /-- Number of stacks. -/
  KK : ℕ
  /-- Stack numbering. -/
  kc : M.K → ℕ
  /-- Inverse of the stack numbering. -/
  kd : ℕ → M.K
  kc_lt : ∀ k, kc k < KK
  kd_kc : ∀ k, kd (kc k) = k
  kc_kd : ∀ n < KK, kc (kd n) = n
  /-- Number of (label, state) codes. -/
  A0 : ℕ
  /-- (Label, state) numbering. -/
  lc : Option M.Λ × M.σ → ℕ
  /-- Inverse of the (label, state) numbering. -/
  ld : ℕ → Option M.Λ × M.σ
  lc_lt : ∀ x, lc x < A0
  ld_lc : ∀ x, ld (lc x) = x
  lc_ld : ∀ c < A0, lc (ld c) = c
  /-- Size of the effective alphabet of each stack. -/
  sz : M.K → ℕ
  /-- The effective symbols of each stack. -/
  dec : ∀ k, Fin (sz k) → M.Γ k
  /-- Symbol codes (`1 + index`; `0` is the empty cell). -/
  enc : ∀ k, M.Γ k → ℕ
  enc_dec : ∀ k i, enc k (dec k i) = i + 1
  push_mem : ∀ l k x, PushSym k (M.m l) x → ∃ i, dec k i = x
  input_mem : ∀ x : M.Γ M.k₀, ∃ i, dec M.k₀ i = x

/-- Window depth: the most `push`/`peek`/`pop` nodes on any path of any statement tree. -/
def depth (M : FinTM2) : ℕ :=
  letI := M.ΛFin
  Finset.univ.sup fun l => ops (M.m l)

theorem ops_le_depth (M : FinTM2) (l : M.Λ) : ops (M.m l) ≤ depth M := by
  letI := M.ΛFin
  exact Finset.le_sup (f := fun l => ops (M.m l)) (Finset.mem_univ l)

/-- **The step on `Option Λ`.** The halted label steps to itself: no pushes, no consumption. -/
def sitStep (M : FinTM2) (l : Option M.Λ) (v : M.σ) (W : ∀ k, List (Option (M.Γ k))) :
    Option M.Λ × M.σ × (∀ k, List (M.Γ k)) × (M.K → ℕ) :=
  match l with
  | none => (none, v, fun _ => [], fun _ => 0)
  | some l => eff W (M.m l) v (fun _ => []) (fun _ => 0)

namespace Enc

variable {M : FinTM2} (E : Enc M)

/-- Symbol codes are `< g` (code 0 = ⊥). -/
def g : ℕ :=
  letI := M.kFin
  1 + Finset.univ.sup E.sz

/-- Number of window combinations `g^(KK·d)`. -/
def G : ℕ := E.g ^ (E.KK * depth M)

/-- Number of situations: (label, state) codes × window combinations. -/
def N : ℕ := E.A0 * E.G

/-- The layout of the D3 families: `A = A0 + N` (one-hot block `[0, A0)`, situation block). -/
def layout : Family.Layout := ⟨E.A0 + E.N, E.KK, E.g, depth M⟩

/-! ### The tables (situation `i` in mixed radix: digits `k·d + j` = windows, top = code) -/

/-- Label/state code of situation `i` (its top digit). -/
def la (i : ℕ) : ℕ := i / E.G % E.A0

/-- Window symbol code of situation `i` on stack `k` at depth `j`. -/
def wa (i k j : ℕ) : ℕ := i / E.g ^ (k * depth M + j) % E.g

/-- Position of situation `i`'s variable in the label/state block. -/
def sa (i : ℕ) : ℕ := E.A0 + i

/-- Decode a symbol code on stack `k`; invalid codes (and 0) read as ⊥. -/
def decO (k : M.K) (c : ℕ) : Option (M.Γ k) :=
  if h : 1 ≤ c ∧ c - 1 < E.sz k then some (E.dec k ⟨c - 1, h.2⟩) else none

/-- Windows of situation `i`, decoded. -/
def win (i : ℕ) : ∀ k, List (Option (M.Γ k)) := fun k =>
  (List.range (depth M)).map fun j => E.decO k (E.wa i (E.kc k) j)

/-- The effect of situation `i`. -/
def res (i : ℕ) : Option M.Λ × M.σ × (∀ k, List (M.Γ k)) × (M.K → ℕ) :=
  sitStep M (E.ld (E.la i)).1 (E.ld (E.la i)).2 (E.win i)

/-- Next label/state code after situation `i`. -/
def na (i : ℕ) : ℕ := E.lc ((E.res i).1, (E.res i).2.1)

/-- Number of symbols situation `i` leaves pushed on stack `k`. -/
def pl (i k : ℕ) : ℕ := ((E.res i).2.2.1 (E.kd k)).length

/-- Number of original symbols situation `i` consumes from stack `k`. -/
def cn (i k : ℕ) : ℕ := (E.res i).2.2.2 (E.kd k)

/-- Code of the symbol situation `i` leaves at depth `j` of stack `k` (`0` if none). -/
def pu (i k j : ℕ) : ℕ := (((E.res i).2.2.1 (E.kd k))[j]?).elim 0 (E.enc (E.kd k))

/-! ### Well-formedness -/

theorem g_pos : 0 < E.g := by unfold g; omega

theorem sz_lt_g (k : M.K) : E.sz k < E.g := by
  letI := M.kFin
  have := Finset.le_sup (f := E.sz) (Finset.mem_univ k)
  unfold g; omega

theorem A0_pos : 0 < E.A0 := Nat.lt_of_le_of_lt (Nat.zero_le _) (E.lc_lt (none, M.initialState))

theorem la_lt (i : ℕ) : E.la i < E.A0 := Nat.mod_lt _ E.A0_pos

theorem na_lt (i : ℕ) : E.na i < E.A0 := E.lc_lt _

theorem wa_lt (i k j : ℕ) : E.wa i k j < E.g := Nat.mod_lt _ E.g_pos

theorem res_bound (i : ℕ) (k : M.K) :
    ((E.res i).2.2.1 k).length ≤ depth M ∧ (E.res i).2.2.2 k ≤ depth M := by
  unfold res sitStep
  split
  · simp
  · next l _ =>
    have := eff_bound (E.win i) (M.m l) (E.ld (E.la i)).2 (fun _ => []) (fun _ => 0) k
    have := ops_le_depth M l
    simp only [List.length_nil] at *; omega

theorem pl_le (i k : ℕ) : E.pl i k ≤ depth M := (E.res_bound i (E.kd k)).1

theorem cn_le (i k : ℕ) : E.cn i k ≤ depth M := (E.res_bound i (E.kd k)).2

/-- Every symbol a situation leaves pushed lies in the effective alphabet. -/
theorem res_pushed (i : ℕ) (k : M.K) (x : M.Γ k) (hx : x ∈ (E.res i).2.2.1 k) :
    ∃ n, E.dec k n = x := by
  unfold res sitStep at hx
  split at hx
  · simp at hx
  · next l _ =>
    exact eff_pushed (E.win i) (fun k x => ∃ n, E.dec k n = x) (M.m l)
      (fun k x h => E.push_mem l k x h) _ _ _ (fun _ _ h => by simp at h) k x hx

theorem decO_succ (k : M.K) (n : Fin (E.sz k)) : E.decO k (n + 1) = some (E.dec k n) := by
  unfold decO
  rw [dite_eq_left ⟨by omega, by simp⟩]
  simp

/-- **`pu` validity** (what pushed fill needs beyond `pu < g`): for `j < pl i k` the code is a
valid code of stack `k`'s own alphabet (`1 ≤ pu ≤ sz`), and it decodes to the real pushed symbol. -/
theorem pu_valid (i k j : ℕ) (hj : j < E.pl i k) :
    ∃ x, ((E.res i).2.2.1 (E.kd k))[j]? = some x ∧ E.pu i k j = E.enc (E.kd k) x ∧
      1 ≤ E.pu i k j ∧ E.pu i k j ≤ E.sz (E.kd k) ∧ E.decO (E.kd k) (E.pu i k j) = some x := by
  unfold pl at hj
  obtain ⟨x, hx⟩ : ∃ x, ((E.res i).2.2.1 (E.kd k))[j]? = some x :=
    ⟨_, List.getElem?_eq_getElem hj⟩
  have hmem : x ∈ (E.res i).2.2.1 (E.kd k) := List.mem_of_getElem? hx
  obtain ⟨n, rfl⟩ := E.res_pushed i _ x hmem
  have hpu : E.pu i k j = n + 1 := by unfold pu; rw [hx]; simp [E.enc_dec]
  refine ⟨_, hx, by rw [hpu, E.enc_dec], by omega, by have := n.2; omega, ?_⟩
  rw [hpu]; exact E.decO_succ _ n

theorem pu_lt (i k j : ℕ) (hj : j < E.pl i k) : E.pu i k j < E.g := by
  obtain ⟨_, _, _, _, h, _⟩ := E.pu_valid i k j hj
  have := E.sz_lt_g (E.kd k); omega

/-- Update family (`D3Fam` with `na`) is well-formed for every situation. -/
theorem wf_upd {H : ℕ} (hH : depth M ≤ H) (i : ℕ) : Family.WF E.layout E.la E.na E.wa H i :=
  ⟨by have := E.la_lt i; simp only [layout]; omega,
   by have := E.na_lt i; simp only [layout]; omega,
   fun k _ j _ => E.wa_lt i k j, hH⟩

/-- S-definition family (`D3Fam` with `na := sa`) is well-formed for every `i < N`. -/
theorem wf_sdef {H : ℕ} (hH : depth M ≤ H) (i : ℕ) (hi : i < E.N) :
    Family.WF E.layout E.la E.sa E.wa H i :=
  ⟨by have := E.la_lt i; simp only [layout]; omega,
   by simp only [layout, sa]; omega,
   fun k _ j _ => E.wa_lt i k j, hH⟩

/-- Shift / overflow / pushed-fill family is well-formed. -/
theorem wf_sh {H : ℕ} (hH : depth M ≤ H) : Shift.WF E.layout E.sa E.pl E.cn E.pu E.N H :=
  ⟨E.g_pos, hH, fun i hi => by simp only [layout, sa]; omega,
   fun i _ k _ => E.pl_le i k, fun i _ k _ => E.cn_le i k,
   fun i _ k _ j hj => E.pu_lt i k j hj⟩

/-! ### Halted situations -/

/-- **Halted labels are covered by the tables themselves**: a situation whose label is `none`
keeps its code and has no pushes and no consumption on any stack. -/
theorem halted (i : ℕ) (h : (E.ld (E.la i)).1 = none) (k : ℕ) :
    E.na i = E.la i ∧ E.pl i k = 0 ∧ E.cn i k = 0 := by
  have hr : E.res i = (none, (E.ld (E.la i)).2, fun _ => [], fun _ => 0) := by
    unfold res sitStep; rw [h]
  refine ⟨?_, by simp [pl, hr], by simp [cn, hr]⟩
  unfold na; rw [hr]
  have : ((none : Option M.Λ), (E.ld (E.la i)).2) = E.ld (E.la i) := by
    rw [← h]
  rw [this, E.lc_ld _ (E.la_lt i)]

/-! ### Every (code, windows) pair is a situation `i < N` (mixed radix; C6 needs it) -/

/-- Mixed radix, least significant digit first: `D 0 + b·(D 1 + b·(… + b·c))`. -/
def mix (b c : ℕ) : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => c
  | m + 1, D => D 0 + b * mix b c m (fun n => D (n + 1))

theorem mix_spec (b c : ℕ) : ∀ (m : ℕ) (D : ℕ → ℕ), (∀ n < m, D n < b) →
    (∀ n < m, mix b c m D / b ^ n % b = D n) ∧ mix b c m D / b ^ m = c ∧
      mix b c m D < (c + 1) * b ^ m := by
  intro m
  induction m with
  | zero => intro D _; simp [mix]
  | succ m ih =>
      intro D hD
      obtain ⟨h1, h2, h3⟩ := ih (fun n => D (n + 1)) (fun n hn => hD (n + 1) (by omega))
      have hb : 0 < b := Nat.lt_of_le_of_lt (Nat.zero_le _) (hD 0 (by omega))
      have h0 := hD 0 (by omega)
      have hdiv : (D 0 + b * mix b c m (fun n => D (n + 1))) / b =
          mix b c m (fun n => D (n + 1)) := by
        rw [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt h0, Nat.zero_add]
      simp only [mix]
      refine ⟨?_, ?_, ?_⟩
      · intro n hn
        cases n with
        | zero => simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
        | succ n =>
            rw [pow_succ', ← Nat.div_div_eq_div_mul, hdiv]; exact h1 n (by omega)
      · rw [pow_succ', ← Nat.div_div_eq_div_mul, hdiv, h2]
      · have : b * (mix b c m (fun n => D (n + 1)) + 1) ≤ b * ((c + 1) * b ^ m) :=
          Nat.mul_le_mul_left _ h3
        rw [pow_succ']
        have e : b * ((c + 1) * b ^ m) = (c + 1) * (b * b ^ m) := by ring
        rw [Nat.mul_add, e] at this; omega

/-- The explicit situation index of code `c` and window contents `w` (mixed radix). -/
theorem mix_sit (c : ℕ) (hc : c < E.A0) (w : ℕ → ℕ → ℕ)
    (hw : ∀ k < E.KK, ∀ j < depth M, w k j < E.g) :
    mix E.g c (E.KK * depth M) (fun n => w (n / depth M) (n % depth M)) < E.N ∧
    E.la (mix E.g c (E.KK * depth M) (fun n => w (n / depth M) (n % depth M))) = c ∧
    ∀ k < E.KK, ∀ j < depth M,
      E.wa (mix E.g c (E.KK * depth M) (fun n => w (n / depth M) (n % depth M))) k j = w k j := by
  set d := depth M
  have hD : ∀ n < E.KK * d, (fun n => w (n / d) (n % d)) n < E.g := by
    intro n hn
    have hd : 0 < d := Nat.pos_of_ne_zero fun h => by simp [h] at hn
    exact hw _ (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hn)) _ (Nat.mod_lt _ hd)
  obtain ⟨h1, h2, h3⟩ := mix_spec E.g c (E.KK * d) _ hD
  refine ⟨?_, ?_, ?_⟩
  · have h3' : _ < (c + 1) * E.G := h3
    exact Nat.lt_of_lt_of_le h3' (Nat.mul_le_mul_right _ hc)
  · unfold la G; rw [h2, Nat.mod_eq_of_lt hc]
  · intro k hk j hj
    have hkj : k * d + j < E.KK * d := by
      have : (k + 1) * d ≤ E.KK * d := Nat.mul_le_mul_right _ hk
      rw [Nat.succ_mul] at this; omega
    unfold wa; rw [h1 _ hkj]
    have hd : 0 < d := by omega
    have e1 : (k * d + j) / d = k := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hj, Nat.zero_add]
    have e2 : (k * d + j) % d = j := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    simp only [e1, e2]

/-- **Situation surjectivity**: every combined code `c < A0` with every window content (codes
`< g`) is the situation of some `i < N`. -/
theorem sit_surj (c : ℕ) (hc : c < E.A0) (w : ℕ → ℕ → ℕ)
    (hw : ∀ k < E.KK, ∀ j < depth M, w k j < E.g) :
    ∃ i < E.N, E.la i = c ∧ ∀ k < E.KK, ∀ j < depth M, E.wa i k j = w k j :=
  ⟨_, E.mix_sit c hc w hw⟩

end Enc

/-! ## [B2] A classical `Enc` for every `FinTM2` -/

section Classical

open Classical

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} [Fintype σ]

/-- The pushable symbols of stack `k` in `q` (over all states), as a finset. -/
noncomputable def pushFS (k : K) : TM2.Stmt Γ Λ σ → Finset (Γ k)
  | .push k' f q =>
      (if h : k' = k then Finset.univ.image fun v => cast (congrArg Γ h) (f v) else ∅) ∪
        pushFS k q
  | .peek _ _ q => pushFS k q
  | .pop _ _ q => pushFS k q
  | .load _ q => pushFS k q
  | .branch _ q₁ q₂ => pushFS k q₁ ∪ pushFS k q₂
  | .goto _ => ∅
  | .halt => ∅

theorem mem_pushFS (k : K) (q : TM2.Stmt Γ Λ σ) (x : Γ k) (h : PushSym k q x) :
    x ∈ pushFS k q := by
  induction q with
  | push k' f q ih =>
      simp only [PushSym] at h
      simp only [pushFS, Finset.mem_union]
      rcases h with ⟨rfl, v, rfl⟩ | h
      · left; rw [dite_eq_left rfl]; exact Finset.mem_image_of_mem _ (Finset.mem_univ v)
      · right; exact ih h
  | peek _ _ q ih => exact ih h
  | pop _ _ q ih => exact ih h
  | load _ q ih => exact ih h
  | branch _ q₁ q₂ ih₁ ih₂ =>
      simp only [PushSym] at h
      simp only [pushFS, Finset.mem_union]
      exact h.imp ih₁ ih₂
  | goto _ => exact h.elim
  | halt => exact h.elim

/-- **B2's `Γfin k`**: every symbol any statement tree can push on stack `k`, plus all of `Γ k₀`
for the input stack. -/
noncomputable def symSet (M : FinTM2) (k : M.K) : Finset (M.Γ k) :=
  letI := M.ΛFin; letI := M.σFin; letI := M.Γk₀Fin
  (Finset.univ.biUnion fun l => pushFS k (M.m l)) ∪
    (if h : M.k₀ = k then Finset.univ.image fun x : M.Γ M.k₀ => cast (congrArg M.Γ h) x else ∅)

theorem push_mem_symSet (M : FinTM2) (l : M.Λ) (k : M.K) (x : M.Γ k)
    (h : PushSym k (M.m l) x) : x ∈ symSet M k := by
  letI := M.ΛFin; letI := M.σFin
  unfold symSet
  exact Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨l, Finset.mem_univ _, mem_pushFS k _ x h⟩)

theorem input_mem_symSet (M : FinTM2) (x : M.Γ M.k₀) : x ∈ symSet M M.k₀ := by
  letI := M.Γk₀Fin
  unfold symSet
  refine Finset.mem_union_right _ ?_
  rw [dite_eq_left rfl]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ x)

/-- **A real `Enc` for an arbitrary `FinTM2`** (classical; only existence matters downstream). -/
noncomputable def Enc.ofFinTM2 (M : FinTM2) : Enc M :=
  letI := M.kFin; letI := M.ΛFin; letI := M.σFin
  { KK := Fintype.card M.K
    kc := fun k => Fintype.equivFin M.K k
    kd := fun n => if h : n < Fintype.card M.K then (Fintype.equivFin M.K).symm ⟨n, h⟩ else M.k₀
    kc_lt := fun k => (Fintype.equivFin M.K k).2
    kd_kc := fun k => by simp
    kc_kd := fun n hn => by simp [hn]
    A0 := Fintype.card (Option M.Λ × M.σ)
    lc := fun x => Fintype.equivFin _ x
    ld := fun c => if h : c < Fintype.card (Option M.Λ × M.σ) then
      (Fintype.equivFin _).symm ⟨c, h⟩ else (none, M.initialState)
    lc_lt := fun x => (Fintype.equivFin _ x).2
    ld_lc := fun x => by rw [dite_eq_left (Fintype.equivFin _ x).2]; simp
    lc_ld := fun c hc => by rw [dite_eq_left hc]; simp
    sz := fun k => (symSet M k).card
    dec := fun k i => ((symSet M k).equivFin.symm i).1
    enc := fun k x => if h : x ∈ symSet M k then (symSet M k).equivFin ⟨x, h⟩ + 1 else 0
    enc_dec := fun k i => by simp
    push_mem := fun l k x h => ⟨(symSet M k).equivFin ⟨x, push_mem_symSet M l k x h⟩, by simp⟩
    input_mem := fun x => ⟨(symSet M M.k₀).equivFin ⟨x, input_mem_symSet M x⟩, by simp⟩ }

end Classical

/-! ## [B3] The real tables feed the proved generators -/

section Gen

variable {M : FinTM2} (E : Enc M) {H : ℕ} (hH : depth M ≤ H)
include hH

open Cslib.Complexity.CookLevin.Family Cslib.Complexity.CookLevin.CounterView in
/-- Update family of the real machine: the `D3Fam` generator runs on the real tables. -/
theorem upd_time (T : ℕ) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (GΓ k)),
      TM2Program.RunLe (prog E.layout E.la E.na E.wa E.N) (genC E.layout E.N * (T + H + 1) ^ 5)
        ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = DenseSAT.encodeCNF (family E.layout E.la E.na E.wa T H E.N) ++ o :=
  gen_time T H (fun i _ => E.wf_upd hH i) o

open Cslib.Complexity.CookLevin.Family Cslib.Complexity.CookLevin.CounterView in
/-- S-definition family of the real machine (`D3Fam` with `na := sa`). -/
theorem sdef_time (T : ℕ) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (GΓ k)),
      TM2Program.RunLe (prog E.layout E.la E.sa E.wa E.N) (genC E.layout E.N * (T + H + 1) ^ 5)
        ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = DenseSAT.encodeCNF (family E.layout E.la E.sa E.wa T H E.N) ++ o :=
  gen_time T H (fun i hi => E.wf_sdef hH i hi) o

open Cslib.Complexity.CookLevin.Shift Cslib.Complexity.CookLevin.CounterView in
/-- Shift / overflow / pushed-fill family of the real machine. -/
theorem shift_time (T : ℕ) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (SΓ Shift.CK k)),
      TM2Program.RunLe (Shift.prog E.layout E.sa E.pl E.cn E.pu E.N) (shC E.layout E.N * (T + H + 1) ^ 6)
        ⟨some (.pre .eg), false, CounterView.st (Shift.initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = DenseSAT.encodeCNF (shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) ++ o :=
  sh_time T H (E.wf_sh hH) o

end Gen

/-! ## [B1] Agreement of the symbolic effect with Mathlib's `TM2.stepAux` -/

section Agree

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- Top-`d` window of a stack, `none` (⊥) below the bottom. -/
def window {α : Type} (d : ℕ) (L : List α) : List (Option α) :=
  (List.range d).map fun j => L[j]?

/-- The configuration an effect produces from original stacks `S0`: pushed prefix on top of what
remains after the net consumption. -/
def applyEff (S0 : ∀ k, List (Γ k)) (r : Option Λ × σ × (∀ k, List (Γ k)) × (K → ℕ)) :
    TM2.Cfg Γ Λ σ :=
  ⟨r.1, r.2.1, fun k => r.2.2.1 k ++ (S0 k).drop (r.2.2.2 k)⟩

omit [DecidableEq K] in
/-- Reading the window below the consumed prefix is reading the real top. -/
theorem readTop_eq (d : ℕ) (S0 P : ∀ k, List (Γ k)) (c : K → ℕ) (k : K) (hc : c k < d) :
    readTop (fun k => window d (S0 k)) P c k = (P k ++ (S0 k).drop (c k)).head? := by
  unfold readTop
  cases P k with
  | cons x _ => rfl
  | nil =>
      simp [window, List.getD_eq_getElem?_getD, List.getElem?_range hc, List.head?_drop]

/-- **B1-core.** On stacks of the form `P ++ drop c S0`, Mathlib's `stepAux` is the symbolic
effect computed from the windows of `S0`, as long as every read stays inside the window. -/
theorem eff_agree (d : ℕ) (S0 : ∀ k, List (Γ k)) (q : TM2.Stmt Γ Λ σ) :
    ∀ (v : σ) (P : ∀ k, List (Γ k)) (c : K → ℕ), (∀ k, c k + ops q ≤ d) →
      TM2.stepAux q v (fun k => P k ++ (S0 k).drop (c k)) =
        applyEff S0 (eff (fun k => window d (S0 k)) q v P c) := by
  induction q with
  | push k₀ f q ih =>
      intro v P c hc
      have e : update (fun k => P k ++ (S0 k).drop (c k)) k₀
          (f v :: (P k₀ ++ (S0 k₀).drop (c k₀))) =
          fun k => update P k₀ (f v :: P k₀) k ++ (S0 k).drop (c k) := by
        funext k
        by_cases hk : k = k₀
        · subst hk; simp
        · simp [update_of_ne hk]
      simp only [TM2.stepAux, eff]
      rw [e]
      exact ih v _ c fun k => by have := hc k; simp only [ops] at this; omega
  | peek k₀ f q ih =>
      intro v P c hc
      have hk : c k₀ < d := by have := hc k₀; simp only [ops] at this; omega
      simp only [TM2.stepAux, eff]
      rw [← readTop_eq d S0 P c k₀ hk]
      exact ih _ P c fun k => by have := hc k; simp only [ops] at this; omega
  | pop k₀ f q ih =>
      intro v P c hc
      have hk : c k₀ < d := by have := hc k₀; simp only [ops] at this; omega
      set c' := if (P k₀).isEmpty then update c k₀ (c k₀ + 1) else c with hc'
      have e : update (fun k => P k ++ (S0 k).drop (c k)) k₀
          (P k₀ ++ (S0 k₀).drop (c k₀)).tail =
          fun k => update P k₀ (P k₀).tail k ++ (S0 k).drop (c' k) := by
        funext k
        by_cases hk : k = k₀
        · subst hk
          rcases h : P k with _ | ⟨x, xs⟩
          · simp [hc', h, List.tail_drop]
          · simp [hc', h]
        · rw [update_of_ne hk, update_of_ne hk, hc']
          split
          · rw [update_of_ne hk]
          · rfl
      have hb : ∀ k, c' k + ops q ≤ d := by
        intro k
        have := hc k
        simp only [ops] at this
        rw [hc']
        split
        · by_cases hk : k = k₀
          · subst hk; simp; omega
          · rw [update_of_ne hk]; omega
        · omega
      simp only [TM2.stepAux, eff]
      rw [← readTop_eq d S0 P c k₀ hk, e]
      exact ih _ _ c' hb
  | load a q ih =>
      intro v P c hc
      simp only [TM2.stepAux, eff]
      exact ih _ P c fun k => by have := hc k; simp only [ops] at this; omega
  | branch p q₁ q₂ ih₁ ih₂ =>
      intro v P c hc
      simp only [TM2.stepAux, eff]
      cases p v
      · simp only [Bool.cond_false]
        exact ih₂ v P c fun k => by have := hc k; simp only [ops] at this; omega
      · simp only [Bool.cond_true]
        exact ih₁ v P c fun k => by have := hc k; simp only [ops] at this; omega
  | goto f => intro v P c _; rfl
  | halt => intro v P c _; rfl

end Agree

/-- The idle-extended step: a halted configuration stays put. -/
def stepI (M : FinTM2) (c : M.Cfg) : M.Cfg := (TM2.step M.m c).getD c

/-- The idle-extended run. -/
def runI (M : FinTM2) (c : M.Cfg) : ℕ → M.Cfg
  | 0 => c
  | t + 1 => stepI M (runI M c t)

/-- Windows of a configuration (depth `depth M`). -/
def winC (M : FinTM2) (c : M.Cfg) : ∀ k, List (Option (M.Γ k)) :=
  fun k => window (depth M) (c.stk k)

/-- **B1 (full configuration equality, no height hypothesis).** The idle-extended real step is
the situation step computed from the label, the state and the top-`depth M` windows, applied as
"pushed prefix ++ drop (net consumption)". -/
theorem step_agree (M : FinTM2) (c : M.Cfg) :
    stepI M c = applyEff c.stk (sitStep M c.l c.var (winC M c)) := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [stepI, TM2.step, sitStep, applyEff]; try rfl
  | some l =>
      simp only [stepI, TM2.step, Option.getD_some, sitStep]
      have := eff_agree (depth M) S (M.m l) v (fun _ => []) (fun _ => 0)
        (fun _ => by simpa using ops_le_depth M l)
      simp only [List.nil_append, List.drop_zero] at this
      exact this

namespace Enc

variable {M : FinTM2} (E : Enc M)

/-! ## [B1] The table-driven step on encoded rows -/

/-- Combined (label, state) code of a configuration. -/
def code (c : M.Cfg) : ℕ := E.lc (c.l, c.var)

/-- Top-indexed cell code of stack number `k`, depth `j` (`0` = ⊥). -/
def cell (c : M.Cfg) (k j : ℕ) : ℕ := ((c.stk (E.kd k))[j]?).elim 0 (E.enc (E.kd k))

/-- The situation index of a configuration: mixed radix of its code and its window cells. -/
def sitIdx (c : M.Cfg) : ℕ :=
  mix E.g (E.code c) (E.KK * depth M) fun n => E.cell c (n / depth M) (n % depth M)

/-- **The table-driven row update** (what the D3Shift clauses force): pushed fill, in-range
shift, overflow ⊥. -/
def tabRow (H i : ℕ) (old : ℕ → ℕ → ℕ) (k j : ℕ) : ℕ :=
  if j < E.pl i k then E.pu i k j
  else if j < H - max (E.pl i k) (E.cn i k) + E.pl i k then old k (j - E.pl i k + E.cn i k)
  else 0

/-- Every stack symbol has a code (lies in the effective alphabet). -/
def Good (c : M.Cfg) : Prop := ∀ k, ∀ x ∈ c.stk k, ∃ n, E.dec k n = x

theorem cell_kc (c : M.Cfg) (k : M.K) (j : ℕ) :
    E.cell c (E.kc k) j = ((c.stk k)[j]?).elim 0 (E.enc k) := by
  unfold cell; rw [E.kd_kc]

theorem decO_zero (k : M.K) : E.decO k 0 = none := by
  unfold decO; rw [dite_eq_right (by omega)]

theorem decO_cell (c : M.Cfg) (hc : E.Good c) (k : M.K) (j : ℕ) :
    E.decO k (((c.stk k)[j]?).elim 0 (E.enc k)) = (c.stk k)[j]? := by
  rcases h : (c.stk k)[j]? with _ | x
  · exact E.decO_zero k
  · obtain ⟨n, rfl⟩ := hc k x (List.mem_of_getElem? h)
    simp only [Option.elim_some, E.enc_dec]
    exact E.decO_succ k n

theorem cell_lt (c : M.Cfg) (hc : E.Good c) (k j : ℕ) : E.cell c k j < E.g := by
  unfold cell
  rcases h : (c.stk (E.kd k))[j]? with _ | x
  · exact E.g_pos
  · obtain ⟨n, rfl⟩ := hc _ x (List.mem_of_getElem? h)
    simp only [Option.elim_some, E.enc_dec]
    have := n.2; have := E.sz_lt_g (E.kd k); omega

/-- The situation of a good configuration is found: index in range, code and windows match. -/
theorem sitIdx_spec (c : M.Cfg) (hc : E.Good c) :
    E.sitIdx c < E.N ∧ E.la (E.sitIdx c) = E.code c ∧
      ∀ k < E.KK, ∀ j < depth M, E.wa (E.sitIdx c) k j = E.cell c k j :=
  E.mix_sit _ (E.lc_lt _) _ fun k _ j _ => E.cell_lt c hc k j

theorem win_sitIdx (c : M.Cfg) (hc : E.Good c) : E.win (E.sitIdx c) = winC M c := by
  funext k
  unfold win winC window
  refine List.map_congr_left fun j hj => ?_
  rw [List.mem_range] at hj
  rw [(E.sitIdx_spec c hc).2.2 _ (E.kc_lt k) j hj, E.cell_kc, E.decO_cell c hc]

theorem res_sitIdx (c : M.Cfg) (hc : E.Good c) :
    E.res (E.sitIdx c) = sitStep M c.l c.var (winC M c) := by
  unfold res
  rw [(E.sitIdx_spec c hc).2.1, code, E.ld_lc, E.win_sitIdx c hc]

/-- One cell of `P ++ drop n S`, in the three cases of `tabRow`. -/
theorem row_cell {α : Type} (e : α → ℕ) (P S : List α) (n H d j : ℕ) (hP : P.length ≤ d)
    (hn : n ≤ d) (hS : S.length ≤ H - d) :
    ((P ++ S.drop n)[j]?).elim 0 e =
      if j < P.length then (P[j]?).elim 0 e
      else if j < H - max P.length n + P.length then (S[j - P.length + n]?).elim 0 e
      else 0 := by
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · rw [List.getElem?_append_right (by omega), List.getElem?_drop, Nat.add_comm]
  · have hm : max P.length n ≤ d := max_le hP hn
    rw [List.getElem?_eq_none]
    · rfl
    · simp only [List.length_append, List.length_drop]; omega

/-- **B1-T (the table-driven step).** For a configuration whose symbols are all encodable and
whose stacks all have height `≤ H − d` (`d ≤ H`): the situation is found (`sitIdx_spec`), the next
row's (label, state) code is `na`, and every one of its `KK·H` cells is `tabRow` of the old
row. (`d ≤ H` is not needed: if `H < d` the heights are all `0`.) -/
theorem table_agree (H : ℕ) (c : M.Cfg) (hc : E.Good c)
    (hh : ∀ k, (c.stk k).length ≤ H - depth M) :
    E.code (stepI M c) = E.na (E.sitIdx c) ∧
      ∀ k < E.KK, ∀ j < H, E.cell (stepI M c) k j = E.tabRow H (E.sitIdx c) (E.cell c) k j := by
  have hr := E.res_sitIdx c hc
  have hs := step_agree M c
  refine ⟨?_, fun k _ j _ => ?_⟩
  · rw [hs]; simp only [code, na, hr]; try rfl
  · have hpl := E.pl_le (E.sitIdx c) k
    have hcn := E.cn_le (E.sitIdx c) k
    unfold pl at hpl; unfold cn at hcn
    rw [hr] at hpl hcn
    unfold tabRow pl cn pu cell
    rw [hr, hs]
    exact row_cell _ _ _ _ H (depth M) j hpl hcn (hh _)

/-- Every old cell `tabRow` reads lies in the row (`index < H`). -/
theorem tabRow_reads_lt (H i k j : ℕ) (hpl : E.pl i k ≤ j)
    (hj : j < H - max (E.pl i k) (E.cn i k) + E.pl i k) :
    j - E.pl i k + E.cn i k < H := by omega

/-! ## [B2] Every configuration of a real run is good (`run_mem_Γfin`) -/

theorem good_step (c : M.Cfg) (hc : E.Good c) : E.Good (stepI M c) := by
  rw [step_agree]
  intro k x hx
  simp only [applyEff, List.mem_append] at hx
  rcases hx with hx | hx
  · unfold sitStep at hx
    split at hx
    · simp at hx
    · next l _ =>
      exact eff_pushed (winC M c) (fun k x => ∃ n, E.dec k n = x) (M.m l)
        (fun k x h => E.push_mem l k x h) _ _ _ (fun _ _ h => by simp at h) k x hx
  · exact hc k x (List.mem_of_mem_drop hx)

theorem good_init (s : List (M.Γ M.k₀)) : E.Good (initList M s) := by
  intro k x hx
  by_cases hk : k = M.k₀
  · subst hk
    simp only [initList, dite_eq_left] at hx
    exact E.input_mem x
  · simp [initList, hk] at hx

theorem run_good (s : List (M.Γ M.k₀)) : ∀ t, E.Good (runI M (initList M s) t)
  | 0 => E.good_init s
  | t + 1 => E.good_step _ (run_good s t)

/-- **B1-T on a real run**: only the height hypothesis remains. -/
theorem table_agree_run (H : ℕ) (s : List (M.Γ M.k₀)) (t : ℕ)
    (hh : ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M) :
    let c := runI M (initList M s) t
    E.sitIdx c < E.N ∧ E.la (E.sitIdx c) = E.code c ∧
      (∀ k < E.KK, ∀ j < depth M, E.wa (E.sitIdx c) k j = E.cell c k j) ∧
      E.code (runI M (initList M s) (t + 1)) = E.na (E.sitIdx c) ∧
      ∀ k < E.KK, ∀ j < H,
        E.cell (runI M (initList M s) (t + 1)) k j = E.tabRow H (E.sitIdx c) (E.cell c) k j :=
  ⟨(E.sitIdx_spec _ (E.run_good s t)).1, (E.sitIdx_spec _ (E.run_good s t)).2.1,
    (E.sitIdx_spec _ (E.run_good s t)).2.2, E.table_agree H _ (E.run_good s t) hh⟩

end Enc

/-! ## [C1] Decoding a row of cells (generic part) -/

section DecS

variable {α : Type}

/-- Read `f j, f (j+1), …` for at most `m` positions, stopping at the first ⊥ (`none`). -/
def decS (f : ℕ → Option α) : ℕ → ℕ → List α
  | _, 0 => []
  | j, m + 1 => match f j with
    | none => []
    | some x => x :: decS f (j + 1) m

theorem decS_length (f : ℕ → Option α) : ∀ j m, (decS f j m).length ≤ m
  | _, 0 => by simp [decS]
  | j, m + 1 => by
    unfold decS
    split
    · simp
    · have := decS_length f (j + 1) m; simp; omega

theorem mem_decS (f : ℕ → Option α) (x : α) : ∀ j m, x ∈ decS f j m → ∃ i, f i = some x
  | _, 0, h => by simp [decS] at h
  | j, m + 1, h => by
    unfold decS at h
    split at h
    · simp at h
    · next y hy =>
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨j, hy⟩
      · exact mem_decS f x (j + 1) m h

theorem decS_congr (f f' : ℕ → Option α) : ∀ j m, (∀ i < m, f (j + i) = f' (j + i)) →
    decS f j m = decS f' j m
  | _, 0, _ => rfl
  | j, m + 1, h => by
    have h0 : f j = f' j := by simpa using h 0 (by omega)
    have ih := decS_congr f f' (j + 1) m fun i hi => by
      have := h (i + 1) (by omega); rwa [show j + (i + 1) = j + 1 + i by omega] at this
    simp only [decS, h0, ih]

/-- Decoding the cells of a stack of height `≤ m` gives the stack back. -/
theorem decS_of_list (f : ℕ → Option α) : ∀ (S : List α) (j m : ℕ),
    (∀ i, f (j + i) = S[i]?) → S.length ≤ m → decS f j m = S
  | [], j, 0, _, _ => rfl
  | [], j, m + 1, h, _ => by have := h 0; simp at this; simp [decS, this]
  | x :: S, j, 0, _, hl => by simp at hl
  | x :: S, j, m + 1, h, hl => by
    have h0 : f j = some x := by simpa using h 0
    have ih := decS_of_list f S (j + 1) m (fun i => by
      have := h (i + 1); rwa [show j + (i + 1) = j + 1 + i by omega] at this)
      (by simp at hl; omega)
    simp only [decS, h0, ih]

/-- On prefix-form input (no symbol below a ⊥), cell `i` of the decoded stack is `f (j+i)`. -/
theorem getElem?_decS (f : ℕ → Option α) : ∀ (j m : ℕ),
    (∀ a b, j ≤ a → a ≤ b → b < j + m → f a = none → f b = none) →
    ∀ i < m, (decS f j m)[i]? = f (j + i)
  | _, 0, _, i, hi => by omega
  | j, m + 1, hp, i, hi => by
    unfold decS
    split
    · next hn =>
      exact (hp j (j + i) le_rfl (by omega) (by omega) hn).symm ▸ (by simp)
    · next x hx =>
      rcases i with _ | i
      · simpa using hx.symm
      · have := getElem?_decS f (j + 1) m
          (fun a b ha hab hb => hp a b (by omega) hab (by omega)) i (by omega)
        simp only [List.getElem?_cons_succ, this]
        congr 1; omega

end DecS

/-- Heights grow by at most `depth M` per step. -/
theorem stepI_height {M : FinTM2} (c : M.Cfg) (k : M.K) :
    ((stepI M c).stk k).length ≤ (c.stk k).length + depth M := by
  rw [step_agree]
  simp only [applyEff, List.length_append, List.length_drop]
  have : ((sitStep M c.l c.var (winC M c)).2.2.1 k).length ≤ depth M := by
    unfold sitStep
    split
    · simp
    · next l _ =>
      have := eff_bound (winC M c) (M.m l) c.var (fun _ => []) (fun _ => 0) k
      have := ops_le_depth M l
      simp only [List.length_nil] at *; omega
  omega

namespace Enc

variable {M : FinTM2} (E : Enc M)

/-- **C1 decoder.** Label/state from the code; stack `k` = the valid codes on top of the first ⊥,
at most `H` of them. -/
def decRow (H n : ℕ) (w : ℕ → ℕ → ℕ) : M.Cfg :=
  ⟨(E.ld n).1, (E.ld n).2, fun k => decS (fun j => E.decO k (w (E.kc k) j)) 0 H⟩

/-- A row of cells that C6 must produce: valid codes, prefix form. -/
def RowOK (H : ℕ) (w : ℕ → ℕ → ℕ) : Prop :=
  ∀ k < E.KK, ∀ j < H, w k j ≤ E.sz (E.kd k) ∧ (w k j = 0 → ∀ b, j ≤ b → b < H → w k b = 0)

theorem decO_eq_none (k : M.K) (n : ℕ) (hn : n ≤ E.sz k) (h : E.decO k n = none) : n = 0 := by
  unfold decO at h
  split at h
  · simp at h
  · next h' => omega

theorem enc_decO (k : M.K) (n : ℕ) (hn : n ≤ E.sz k) : (E.decO k n).elim 0 (E.enc k) = n := by
  unfold decO
  split
  · next h => simp only [Option.elim_some, E.enc_dec]; omega
  · next h => simp only [Option.elim_none]; omega

/-- **C1a.** A good configuration with heights `≤ H` is recovered from its code and cells. -/
theorem decRow_enc (H : ℕ) (c : M.Cfg) (hc : E.Good c) (hh : ∀ k, (c.stk k).length ≤ H) :
    E.decRow H (E.code c) (E.cell c) = c := by
  obtain ⟨l, v, S⟩ := c
  simp only [decRow, code, E.ld_lc]
  congr 1
  funext k
  refine decS_of_list _ _ 0 H (fun i => ?_) (hh k)
  rw [Nat.zero_add]
  first | exact (congrArg (E.decO k) (E.cell_kc ⟨l, v,
      S⟩ k i)).trans (E.decO_cell _ hc k i) | (erw [E.cell_kc]; exact E.decO_cell _ hc k i)

/-- **C1b.** A valid prefix-form row is recovered from its decoding. -/
theorem enc_decRow (H n : ℕ) (hn : n < E.A0) (w : ℕ → ℕ → ℕ) (hw : E.RowOK H w) :
    E.code (E.decRow H n w) = n ∧ ∀ k < E.KK, ∀ j < H, E.cell (E.decRow H n w) k j = w k j := by
  refine ⟨by simp only [code, decRow, E.lc_ld n hn], fun k hk j hj => ?_⟩
  simp only [cell, decRow]
  rw [getElem?_decS _ 0 H ?_ j hj, Nat.zero_add, E.kc_kd k hk]
  · exact E.enc_decO _ _ (hw k hk j hj).1
  · intro a b _ hab hb ha
    rw [E.kc_kd k hk] at ha ⊢
    have := E.decO_eq_none _ _ (hw k hk a (by omega)).1 ha
    rw [(hw k hk a (by omega)).2 this b hab (by omega)]
    exact E.decO_zero _

/-- **C1c.** Rows of good configurations are valid and prefix-form. -/
theorem cell_rowOK (H : ℕ) (c : M.Cfg) (hc : E.Good c) : E.RowOK H (E.cell c) := by
  intro k _ j _
  have key : ∀ j, (E.cell c k j = 0 ∧ (c.stk (E.kd k)).length ≤ j) ∨
      (j < (c.stk (E.kd k)).length ∧ 1 ≤ E.cell c k j ∧ E.cell c k j ≤ E.sz (E.kd k)) := by
    intro j
    unfold cell
    rcases h : (c.stk (E.kd k))[j]? with _ | x
    · exact Or.inl ⟨rfl, List.getElem?_eq_none_iff.1 h⟩
    · obtain ⟨m, rfl⟩ := hc _ x (List.mem_of_getElem? h)
      refine Or.inr ⟨(List.getElem?_eq_some_iff.1 h).1, ?_⟩
      simp only [Option.elim_some, E.enc_dec]; have := m.2; omega
  refine ⟨by rcases key j with h | h <;> omega, fun h0 b hjb _ => ?_⟩
  have hlen : (c.stk (E.kd k)).length ≤ j := by rcases key j with h | h <;> omega
  unfold cell
  rw [List.getElem?_eq_none (by omega)]; rfl

/-- **C1d.** A decoded row is good and has heights `≤ H`. -/
theorem decRow_good (H n : ℕ) (w : ℕ → ℕ → ℕ) : E.Good (E.decRow H n w) := by
  intro k x hx
  obtain ⟨i, hi⟩ := mem_decS _ x 0 H hx
  unfold decO at hi
  split at hi
  · exact ⟨_, Option.some_inj.1 hi⟩
  · simp at hi

theorem decRow_height (H n : ℕ) (w : ℕ → ℕ → ℕ) (k : M.K) : ((E.decRow H n w).stk k).length ≤ H :=
  decS_length _ 0 H

/-- **C1e.** `decRow` only reads the window `k < KK`, `j < H`. -/
theorem decRow_congr (H n : ℕ) (w w' : ℕ → ℕ → ℕ) (h : ∀ k < E.KK, ∀ j < H, w k j = w' k j) :
    E.decRow H n w = E.decRow H n w' := by
  simp only [decRow]
  congr 1
  funext k
  exact decS_congr _ _ 0 H fun i hi => by rw [h _ (E.kc_lt k) _ (by omega)]

/-- **C1f.** Good configurations of height `≤ H` are determined by their row. -/
theorem row_inj (H : ℕ) (c c' : M.Cfg) (hc : E.Good c) (hc' : E.Good c')
    (hh : ∀ k, (c.stk k).length ≤ H) (hh' : ∀ k, (c'.stk k).length ≤ H)
    (hcode : E.code c = E.code c') (hcell : ∀ k < E.KK, ∀ j < H, E.cell c k j = E.cell c' k j) :
    c = c' := by
  rw [← E.decRow_enc H c hc hh, ← E.decRow_enc H c' hc' hh', hcode, E.decRow_congr H _ _ _ hcell]

/-- **C2' (the C2 link, decoded).** Decoding the table-driven next row gives the real next
configuration. -/
theorem decRow_tabRow (H : ℕ) (hH : depth M ≤ H) (c : M.Cfg) (hc : E.Good c)
    (hh : ∀ k, (c.stk k).length ≤ H - depth M) :
    E.decRow H (E.na (E.sitIdx c)) (E.tabRow H (E.sitIdx c) (E.cell c)) = stepI M c := by
  obtain ⟨h1, h2⟩ := E.table_agree H c hc hh
  rw [← h1, E.decRow_congr H _ _ (E.cell (stepI M c)) fun k hk j hj => (h2 k hk j hj).symm]
  exact E.decRow_enc H _ (E.good_step c hc) fun k => by
    have := stepI_height c k; have := hh k; omega

end Enc

/-! ## [C6] Clause forcing: the in-range shift family (no row decoding) -/

section C6

open Cslib.Complexity.DenseSAT

/-- Variable `v` is true under the assignment `a` (indices `≥ a.length` are not true). -/
def Tr (a : List Bool) (v : ℕ) : Prop := a[v]? = some true

theorem mem_of_lookup {p : ℕ} {b : Bool} :
    ∀ {ls : List (ℕ × Bool)}, ls.lookup p = some b → (p, b) ∈ ls
  | [], h => by simp at h
  | (q, c) :: r, h => by
    by_cases hq : p = q
    · subst hq
      simp at h
      simp [h]
    · rw [Family.lookup_cons_ne hq] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup h)

/-- **L0.** A satisfied dense clause has a satisfied literal from its list. -/
theorem clauseSat_dense {V : ℕ} {ls : List (ℕ × Bool)} {a : List Bool}
    (h : clauseSat (Family.denseClause V ls) a) : ∃ p b, (p, b) ∈ ls ∧ a[p]? = some b := by
  obtain ⟨j, b, hc, ha⟩ := h
  unfold Family.denseClause at hc
  have hj : j < V := by
    by_contra hj
    rw [List.getElem?_eq_none (by simp only [List.length_map, List.length_range]; omega)] at hc
    simp at hc
  rw [List.getElem?_map, List.getElem?_range hj] at hc
  simp only [Option.map_some, Option.some.injEq] at hc
  exact ⟨j, b, mem_of_lookup hc, ha⟩

/-- **L1 (in-range shift forcing).** Under a satisfying assignment of the D3Shift family, `S[t,i]`
and `C[t,k,u+c,x]` force `C[t+1,k,u+p,x]`. -/
theorem sh_force {L : Family.Layout} {sa : ℕ → ℕ} {pl cn : ℕ → ℕ → ℕ} {pu : ℕ → ℕ → ℕ → ℕ}
    {N T H : ℕ} {a : List Bool} (ha : cnfSat (Shift.shFamily L sa pl cn pu N T H) a)
    {t i k u x : ℕ} (ht : t < T) (hi : i < N) (hk : k < L.KK)
    (hu : u < H - max (pl i k) (cn i k)) (hx : x < L.g)
    (hS : Tr a (L.xIdx H (t + 1) (sa i))) (hC : Tr a (L.cIdx H t k (u + cn i k) x)) :
    Tr a (L.cIdx H (t + 1) k (u + pl i k) x) := by
  have hm : Family.denseClause (L.numVars T H) (Shift.shLits L sa pl cn H t i k u x) ∈
      Shift.shFamily L sa pl cn pu N T H := by
    refine List.mem_flatMap.2 ⟨t, List.mem_range.2 ht, List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
      List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, ?_⟩⟩⟩
    unfold Shift.shBlk
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨u,
        List.mem_range.2 hu,
      List.mem_map.2 ⟨x, List.mem_range.2 hx, rfl⟩⟩))
  obtain ⟨p, b, hp, hab⟩ := clauseSat_dense (ha _ hm)
  simp only [Shift.shLits, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hp
  unfold Tr at hS hC ⊢
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [hC] at hab; simp at hab
  · rw [hS] at hab; simp at hab
  · exact hab

namespace Enc

variable {M : FinTM2} (E : Enc M)

/-- Row `t`'s cell block is exactly the one-hot image of the array `w` (no decoding). -/
def CellsAre (a : List Bool) (H t : ℕ) (w : ℕ → ℕ → ℕ) : Prop :=
  ∀ k < E.KK, ∀ j < H, ∀ x < E.g, Tr a (E.layout.cIdx H t k j x) ↔ x = w k j

/-- Positive form: the literal of every cell value of `w` in row `t` is true (no exactness). -/
def CellsHold (a : List Bool) (H t : ℕ) (w : ℕ → ℕ → ℕ) : Prop :=
  ∀ k < E.KK, ∀ j < H, Tr a (E.layout.cIdx H t k j (w k j))

/-- **L2⁺ (positive core).** If the literals of a good `c`'s cells hold in row `t` and
`S[t, sitIdx c]` is true, the literal of `tabRow` holds at every in-range cell of row `t+1`. -/
theorem sh_hold {T H t : ℕ} {a : List Bool}
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a) (ht : t < T)
    (c : M.Cfg) (hc : E.Good c) (hrow : E.CellsHold a H t (E.cell c))
    (hS : Tr a (E.layout.xIdx H (t + 1) (E.sa (E.sitIdx c))))
    {k j : ℕ} (hk : k < E.KK) (hj1 : E.pl (E.sitIdx c) k ≤ j)
    (hj2 : j < H - max (E.pl (E.sitIdx c) k) (E.cn (E.sitIdx c) k) + E.pl (E.sitIdx c) k) :
    Tr a (E.layout.cIdx H (t + 1) k j (E.tabRow H (E.sitIdx c) (E.cell c) k j)) := by
  have htab : E.tabRow H (E.sitIdx c) (E.cell c) k j =
      E.cell c k (j - E.pl (E.sitIdx c) k + E.cn (E.sitIdx c) k) := by
    unfold tabRow; rw [ite_eq_right (by omega), ite_eq_left hj2]
  have hu : j - E.pl (E.sitIdx c) k < H - max (E.pl (E.sitIdx c) k) (E.cn (E.sitIdx c) k) := by
    omega
  have := sh_force ha ht (E.sitIdx_spec c hc).1 hk hu (E.cell_lt c hc k _) hS
    (hrow k hk _ (by omega))
  rwa [Nat.sub_add_cancel hj1, ← htab] at this

/-- **L2 (invariant form, exact).** If row `t` holds exactly the cells of a good `c` and
`S[t, sitIdx c]` is true, then every in-range cell of row `t+1` (given at-most-one there) holds
exactly `tabRow` of row `t`. -/
theorem sh_step_cell {T H t : ℕ} {a : List Bool}
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a) (ht : t < T)
    (c : M.Cfg) (hc : E.Good c) (hrow : E.CellsAre a H t (E.cell c))
    (hS : Tr a (E.layout.xIdx H (t + 1) (E.sa (E.sitIdx c))))
    {k j : ℕ} (hk : k < E.KK) (hj1 : E.pl (E.sitIdx c) k ≤ j)
    (hj2 : j < H - max (E.pl (E.sitIdx c) k) (E.cn (E.sitIdx c) k) + E.pl (E.sitIdx c) k)
    (hamo : ∀ x < E.g, ∀ y < E.g, Tr a (E.layout.cIdx H (t + 1) k j x) →
      Tr a (E.layout.cIdx H (t + 1) k j y) → x = y) :
    ∀ x < E.g, Tr a (E.layout.cIdx H (t + 1) k j x) ↔
      x = E.tabRow H (E.sitIdx c) (E.cell c) k j := by
  have hon := E.sh_hold ha ht c hc
    (fun k hk j hj => (hrow k hk j hj _ (E.cell_lt c hc k j)).2 rfl) hS hk hj1 hj2
  have hw : E.tabRow H (E.sitIdx c) (E.cell c) k j < E.g := by
    unfold tabRow; rw [ite_eq_right (by omega), ite_eq_left hj2]; exact E.cell_lt c hc _ _
  intro x hx
  exact ⟨fun h => hamo x hx _ hw h hon, fun h => h ▸ hon⟩

/-- **L3 (the invariant propagates on in-range depths, real run).** Row `t` = cells of
`runI t` ⇒ in-range cells of row `t+1` = cells of `runI (t+1)`. No row is decoded. -/
theorem sh_step_run {T H t : ℕ} {a : List Bool} (s : List (M.Γ M.k₀))
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a) (ht : t < T)
    (hh : ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M)
    (hrow : E.CellsAre a H t (E.cell (runI M (initList M s) t)))
    (hS : Tr a (E.layout.xIdx H (t + 1) (E.sa (E.sitIdx (runI M (initList M s) t)))))
    {k j : ℕ} (hk : k < E.KK) (hj1 : E.pl (E.sitIdx (runI M (initList M s) t)) k ≤ j)
    (hj2 : j < H - max (E.pl (E.sitIdx (runI M (initList M s) t)) k)
      (E.cn (E.sitIdx (runI M (initList M s) t)) k) + E.pl (E.sitIdx (runI M (initList M s) t)) k)
    (hamo : ∀ x < E.g, ∀ y < E.g, Tr a (E.layout.cIdx H (t + 1) k j x) →
      Tr a (E.layout.cIdx H (t + 1) k j y) → x = y) :
    ∀ x < E.g, Tr a (E.layout.cIdx H (t + 1) k j x) ↔
      x = E.cell (runI M (initList M s) (t + 1)) k j := by
  rw [(E.table_agree_run H s t hh).2.2.2.2 k hk j (by omega)]
  exact E.sh_step_cell ha ht _ (E.run_good s t) hrow hS hk hj1 hj2 hamo

/-- **L3⁺ (positive invariant, real run).** Same as L3 without exactness and without
at-most-one: the literal of the real cell holds at every in-range depth of row `t+1`. -/
theorem sh_step_run_pos {T H t : ℕ} {a : List Bool} (s : List (M.Γ M.k₀))
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a) (ht : t < T)
    (hh : ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M)
    (hrow : E.CellsHold a H t (E.cell (runI M (initList M s) t)))
    (hS : Tr a (E.layout.xIdx H (t + 1) (E.sa (E.sitIdx (runI M (initList M s) t)))))
    {k j : ℕ} (hk : k < E.KK) (hj1 : E.pl (E.sitIdx (runI M (initList M s) t)) k ≤ j)
    (hj2 : j < H - max (E.pl (E.sitIdx (runI M (initList M s) t)) k)
      (E.cn (E.sitIdx (runI M (initList M s) t)) k) + E.pl (E.sitIdx (runI M (initList M s) t)) k) :
    Tr a (E.layout.cIdx H (t + 1) k j (E.cell (runI M (initList M s) (t + 1)) k j)) := by
  rw [(E.table_agree_run H s t hh).2.2.2.2 k hk j (by omega)]
  exact E.sh_hold ha ht _ (E.run_good s t) hrow hS hk hj1 hj2

end Enc

/-! ### S-definition forcing (D3Fam family shape: `¬X[t, la i] ∨ ⋁ ¬C[t,k,j,wa i k j] ∨ X[t+1, na i]`) -/

/-- **L1 (D3Fam clause forcing).** The window literals are indexed exactly as in `litPos`, by
`n < KK·d` with `(n / d, n % d)`. No one-hot fact appears. -/
theorem fam_force {L : Family.Layout} {la na : ℕ → ℕ} {wa : ℕ → ℕ → ℕ → ℕ} {N T H : ℕ}
    {a : List Bool} (ha : cnfSat (Family.family L la na wa T H N) a) {t i : ℕ} (ht : t < T)
    (hi : i < N) (hX : Tr a (L.xIdx H t (la i)))
    (hW : ∀ n < L.KK * L.d, Tr a (L.cIdx H t (n / L.d) (n % L.d) (wa i (n / L.d) (n % L.d)))) :
    Tr a (L.xIdx H (t + 1) (na i)) := by
  have hm : Family.denseClause (L.numVars T H) (Family.lits L la na wa H t i) ∈
      Family.family L la na wa T H N :=
    List.mem_flatMap.2 ⟨t, List.mem_range.2 ht, List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩⟩
  obtain ⟨p, b, hp, hab⟩ := clauseSat_dense (ha _ hm)
  unfold Family.lits at hp
  obtain ⟨j, hj, hjp⟩ := List.mem_map.1 hp
  rw [List.mem_range] at hj
  simp only [Prod.mk.injEq] at hjp
  obtain ⟨rfl, rfl⟩ := hjp
  have hn : L.nLits - 1 = L.KK * L.d + 1 := by unfold Family.Layout.nLits; omega
  have hj2 : j < L.KK * L.d + 2 := hj
  unfold Tr at hX hW ⊢
  by_cases h0 : j = 0
  · subst h0
    simp only [Family.litPos, ite_true] at hab
    rw [hX] at hab
    simp [hn] at hab
  · by_cases h1 : j ≤ L.KK * L.d
    · simp only [Family.litPos, ite_eq_right h0, ite_eq_left h1] at hab
      rw [hW (j - 1) (by omega)] at hab
      have : j ≠ L.nLits - 1 := by omega
      simp [this] at hab
    · have hj' : j = L.KK * L.d + 1 := by omega
      simp only [Family.litPos, ite_eq_right h0, ite_eq_right h1] at hab
      rw [hj', hn] at hab
      simpa using hab

/-- **L1, `(k, j)` form** (the form `Enc`'s tables are stated in). -/
theorem fam_force_kj {L : Family.Layout} {la na : ℕ → ℕ} {wa : ℕ → ℕ → ℕ → ℕ} {N T H : ℕ}
    {a : List Bool} (ha : cnfSat (Family.family L la na wa T H N) a) {t i : ℕ} (ht : t < T)
    (hi : i < N) (hX : Tr a (L.xIdx H t (la i)))
    (hW : ∀ k < L.KK, ∀ j < L.d, Tr a (L.cIdx H t k j (wa i k j))) :
    Tr a (L.xIdx H (t + 1) (na i)) :=
  fam_force ha ht hi hX fun n hn =>
    hW _ (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm] at hn; exact hn)) _
      (Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => by simp [h] at hn))

namespace Enc

variable {M : FinTM2} (E : Enc M)

/-- Positive form of the code block of row `t`: the literal of `c`'s (label, state) code is true. -/
def CodeHolds (a : List Bool) (H t : ℕ) (c : M.Cfg) : Prop :=
  Tr a (E.layout.xIdx H t (E.code c))

/-- **L2 (S-definition, positive).** The code literal and the window-cell literals of a good `c`
in row `t` force `S[t, sitIdx c]`. -/
theorem sd_hold {T H t : ℕ} {a : List Bool}
    (ha : cnfSat (Family.family E.layout E.la E.sa E.wa T H E.N) a) (ht : t < T)
    (c : M.Cfg) (hc : E.Good c) (hdH : depth M ≤ H)
    (hcode : E.CodeHolds a H t c) (hrow : E.CellsHold a H t (E.cell c)) :
    Tr a (E.layout.xIdx H (t + 1) (E.sa (E.sitIdx c))) := by
  obtain ⟨hi, hla, hwa⟩ := E.sitIdx_spec c hc
  refine fam_force_kj ha ht hi ?_ fun k hk j hj => ?_
  · rw [hla]; exact hcode
  · rw [hwa k hk j hj]; exact hrow k hk j (lt_of_lt_of_le hj hdH)

/-- **L3 (S-definition, real run).** -/
theorem sd_step_run {T H t : ℕ} {a : List Bool} (s : List (M.Γ M.k₀))
    (ha : cnfSat (Family.family E.layout E.la E.sa E.wa T H E.N) a) (ht : t < T)
    (hdH : depth M ≤ H) (hcode : E.CodeHolds a H t (runI M (initList M s) t))
    (hrow : E.CellsHold a H t (E.cell (runI M (initList M s) t))) :
    Tr a (E.layout.xIdx H (t + 1) (E.sa (E.sitIdx (runI M (initList M s) t)))) :=
  E.sd_hold ha ht _ (E.run_good s t) hdH hcode hrow

/-- **Composition with the shift family.** The S-definition clauses discharge `sh_step_run_pos`'s
`hS`: from the positive row-`t` invariant alone, in-range cells of row `t+1` hold. -/
theorem sdsh_step_run_pos {T H t : ℕ} {a : List Bool} (s : List (M.Γ M.k₀))
    (hs : cnfSat (Family.family E.layout E.la E.sa E.wa T H E.N) a)
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a) (ht : t < T)
    (hh : ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M) (hdH : depth M ≤ H)
    (hcode : E.CodeHolds a H t (runI M (initList M s) t))
    (hrow : E.CellsHold a H t (E.cell (runI M (initList M s) t)))
    {k j : ℕ} (hk : k < E.KK) (hj1 : E.pl (E.sitIdx (runI M (initList M s) t)) k ≤ j)
    (hj2 : j < H - max (E.pl (E.sitIdx (runI M (initList M s) t)) k)
      (E.cn (E.sitIdx (runI M (initList M s) t)) k) + E.pl (E.sitIdx (runI M (initList M s) t)) k) :
    Tr a (E.layout.cIdx H (t + 1) k j (E.cell (runI M (initList M s) (t + 1)) k j)) :=
  E.sh_step_run_pos s ha ht hh hrow (E.sd_step_run s hs ht hdH hcode hrow) hk hj1 hj2

end Enc

/-! ### Update, pushed-fill and overflow forcing (C6, second session): positive literals only -/

namespace Enc

variable {M : FinTM2} (E : Enc M)

/-- **Update forcing (positive).** Same proof as `sd_hold`, with `na` in place of `sa`. -/
theorem upd_hold {T H t : ℕ} {a : List Bool}
    (ha : cnfSat (Family.family E.layout E.la E.na E.wa T H E.N) a) (ht : t < T)
    (c : M.Cfg) (hc : E.Good c) (hdH : depth M ≤ H)
    (hcode : E.CodeHolds a H t c) (hrow : E.CellsHold a H t (E.cell c)) :
    Tr a (E.layout.xIdx H (t + 1) (E.na (E.sitIdx c))) := by
  obtain ⟨hi, hla, hwa⟩ := E.sitIdx_spec c hc
  refine fam_force_kj ha ht hi ?_ fun k hk j hj => ?_
  · rw [hla]; exact hcode
  · rw [hwa k hk j hj]; exact hrow k hk j (lt_of_lt_of_le hj hdH)

/-- **Update forcing, real run.** The code literal of row `t+1` is that of the real next
configuration. -/
theorem upd_step_run {T H t : ℕ} {a : List Bool} (s : List (M.Γ M.k₀))
    (ha : cnfSat (Family.family E.layout E.la E.na E.wa T H E.N) a) (ht : t < T)
    (hh : ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M) (hdH : depth M ≤ H)
    (hcode : E.CodeHolds a H t (runI M (initList M s) t))
    (hrow : E.CellsHold a H t (E.cell (runI M (initList M s) t))) :
    E.CodeHolds a H (t + 1) (runI M (initList M s) (t + 1)) := by
  have h := E.upd_hold ha ht _ (E.run_good s t) hdH hcode hrow
  unfold CodeHolds
  rw [(E.table_agree_run H s t hh).2.2.2.1]
  exact h

end Enc

/-- **Pushed-fill forcing.** Only the situation literal is read. -/
theorem pf_force {L : Family.Layout} {sa : ℕ → ℕ} {pl cn : ℕ → ℕ → ℕ} {pu : ℕ → ℕ → ℕ → ℕ}
    {N T H : ℕ} {a : List Bool} (ha : cnfSat (Shift.shFamily L sa pl cn pu N T H) a)
    {t i k j : ℕ} (ht : t < T) (hi : i < N) (hk : k < L.KK) (hj : j < pl i k)
    (hS : Tr a (L.xIdx H (t + 1) (sa i))) : Tr a (L.cIdx H (t + 1) k j (pu i k j)) := by
  have hm : Family.denseClause (L.numVars T H) (Shift.pfLits L sa pu H t i k j) ∈
      Shift.shFamily L sa pl cn pu N T H := by
    refine List.mem_flatMap.2 ⟨t, List.mem_range.2 ht, List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
      List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, ?_⟩⟩⟩
    unfold Shift.shBlk
    exact List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
  obtain ⟨p, b, hp, hab⟩ := clauseSat_dense (ha _ hm)
  simp only [Shift.pfLits, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hp
  unfold Tr at hS ⊢
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [hS] at hab; simp at hab
  · exact hab

/-- **Overflow forcing.** Only the situation literal is read; the target is the ⊥ literal. -/
theorem ov_force {L : Family.Layout} {sa : ℕ → ℕ} {pl cn : ℕ → ℕ → ℕ} {pu : ℕ → ℕ → ℕ → ℕ}
    {N T H : ℕ} {a : List Bool} (ha : cnfSat (Shift.shFamily L sa pl cn pu N T H) a)
    {t i k r : ℕ} (ht : t < T) (hi : i < N) (hk : k < L.KK) (hr : r < cn i k - pl i k)
    (hS : Tr a (L.xIdx H (t + 1) (sa i))) :
    Tr a (L.cIdx H (t + 1) k (H - cn i k + pl i k + r) 0) := by
  have hm : Family.denseClause (L.numVars T H) (Shift.ovLits L sa pl cn H t i k r) ∈
      Shift.shFamily L sa pl cn pu N T H := by
    refine List.mem_flatMap.2 ⟨t, List.mem_range.2 ht, List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
      List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, ?_⟩⟩⟩
    unfold Shift.shBlk
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2
      ⟨r, List.mem_range.2 hr, rfl⟩))
  obtain ⟨p, b, hp, hab⟩ := clauseSat_dense (ha _ hm)
  simp only [Shift.ovLits, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hp
  unfold Tr at hS ⊢
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [hS] at hab; simp at hab
  · exact hab

namespace Enc

variable {M : FinTM2} (E : Enc M)

/-- Pushed fill, positive: the literal of `tabRow` holds at depths `j < pl`. -/
theorem pf_hold {T H t : ℕ} {a : List Bool}
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a) (ht : t < T)
    (c : M.Cfg) (hc : E.Good c) (hS : Tr a (E.layout.xIdx H (t + 1) (E.sa (E.sitIdx c))))
    {k j : ℕ} (hk : k < E.KK) (hj : j < E.pl (E.sitIdx c) k) :
    Tr a (E.layout.cIdx H (t + 1) k j (E.tabRow H (E.sitIdx c) (E.cell c) k j)) := by
  have htab : E.tabRow H (E.sitIdx c) (E.cell c) k j = E.pu (E.sitIdx c) k j := by
    unfold tabRow; rw [ite_eq_left hj]
  rw [htab]
  exact pf_force ha ht (E.sitIdx_spec c hc).1 hk hj hS

/-- Overflow, positive: the literal of `tabRow` (= ⊥) holds at depths `H - max pl cn + pl ≤ j < H`. -/
theorem ov_hold {T H t : ℕ} {a : List Bool}
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a) (ht : t < T)
    (c : M.Cfg) (hc : E.Good c) (hdH : depth M ≤ H)
    (hS : Tr a (E.layout.xIdx H (t + 1) (E.sa (E.sitIdx c))))
    {k j : ℕ} (hk : k < E.KK)
    (hj1 : H - max (E.pl (E.sitIdx c) k) (E.cn (E.sitIdx c) k) + E.pl (E.sitIdx c) k ≤ j)
    (hj2 : j < H) :
    Tr a (E.layout.cIdx H (t + 1) k j (E.tabRow H (E.sitIdx c) (E.cell c) k j)) := by
  have hp := E.pl_le (E.sitIdx c) k
  have hq := E.cn_le (E.sitIdx c) k
  have htab : E.tabRow H (E.sitIdx c) (E.cell c) k j = 0 := by
    unfold tabRow; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  rw [htab]
  have := ov_force ha ht (E.sitIdx_spec c hc).1 hk
    (r := j - (H - E.cn (E.sitIdx c) k + E.pl (E.sitIdx c) k)) (by omega) hS
  rwa [show H - E.cn (E.sitIdx c) k + E.pl (E.sitIdx c) k +
    (j - (H - E.cn (E.sitIdx c) k + E.pl (E.sitIdx c) k)) = j by omega] at this

/-- Pushed fill, real run. -/
theorem pf_step_run {T H t : ℕ} {a : List Bool} (s : List (M.Γ M.k₀))
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a) (ht : t < T)
    (hh : ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M) (hdH : depth M ≤ H)
    (hS : Tr a (E.layout.xIdx H (t + 1) (E.sa (E.sitIdx (runI M (initList M s) t)))))
    {k j : ℕ} (hk : k < E.KK) (hj : j < E.pl (E.sitIdx (runI M (initList M s) t)) k) :
    Tr a (E.layout.cIdx H (t + 1) k j (E.cell (runI M (initList M s) (t + 1)) k j)) := by
  have := E.pl_le (E.sitIdx (runI M (initList M s) t)) k
  rw [(E.table_agree_run H s t hh).2.2.2.2 k hk j (by omega)]
  exact E.pf_hold ha ht _ (E.run_good s t) hS hk hj

/-- Overflow, real run. -/
theorem ov_step_run {T H t : ℕ} {a : List Bool} (s : List (M.Γ M.k₀))
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a) (ht : t < T)
    (hh : ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M) (hdH : depth M ≤ H)
    (hS : Tr a (E.layout.xIdx H (t + 1) (E.sa (E.sitIdx (runI M (initList M s) t)))))
    {k j : ℕ} (hk : k < E.KK)
    (hj1 : H - max (E.pl (E.sitIdx (runI M (initList M s) t)) k)
      (E.cn (E.sitIdx (runI M (initList M s) t)) k) +
      E.pl (E.sitIdx (runI M (initList M s) t)) k ≤ j) (hj2 : j < H) :
    Tr a (E.layout.cIdx H (t + 1) k j (E.cell (runI M (initList M s) (t + 1)) k j)) := by
  rw [(E.table_agree_run H s t hh).2.2.2.2 k hk j hj2]
  exact E.ov_hold ha ht _ (E.run_good s t) hdH hS hk hj1 hj2

end Enc

/-! ### Stack cap `H` (P2, corrected 2026-09-30) and the `depth_cover` assembly -/

/-- P2's stack cap (corrected): input bound `m`, run length `T`, per-step growth `d = depth M`. -/
def capH (m T d : ℕ) : ℕ := m + (T + 1) * d + 1

/-- Iterated `stepI_height`: `t` steps add at most `t · depth M` to each stack. -/
theorem runI_height {M : FinTM2} (c : M.Cfg) (k : M.K) :
    ∀ t, ((runI M c t).stk k).length ≤ (c.stk k).length + t * depth M
  | 0 => by simp [runI]
  | t + 1 => by
    have h1 := stepI_height (runI M c t) k
    have h2 := runI_height c k t
    have h3 : (t + 1) * depth M = t * depth M + depth M := Nat.succ_mul _ _
    change ((stepI M (runI M c t)).stk k).length ≤ _
    omega

theorem initList_height {M : FinTM2} (s : List (M.Γ M.k₀)) (k : M.K) :
    ((initList M s).stk k).length ≤ s.length := by
  by_cases hk : k = M.k₀
  · subst hk; simp [initList]
  · simp [initList, hk]

/-- **Constraint 1, as the C6 run lemmas consume it**: with the corrected cap, every row
`t ≤ T` of the real run has heights `≤ H − depth M` (the `hh` hypothesis). -/
theorem capH_height {M : FinTM2} {m T t : ℕ} (s : List (M.Γ M.k₀)) (hs : s.length ≤ m)
    (ht : t ≤ T) (k : M.K) :
    ((runI M (initList M s) t).stk k).length ≤ capH m T (depth M) - depth M := by
  have h1 := runI_height (initList M s) k t
  have h2 := initList_height s k
  have h3 : t * depth M ≤ T * depth M := Nat.mul_le_mul_right _ ht
  have h4 : (T + 1) * depth M = T * depth M + depth M := Nat.succ_mul _ _
  unfold capH; omega

theorem depth_le_capH (M : FinTM2) (m T : ℕ) : depth M ≤ capH m T (depth M) := by
  have h4 : (T + 1) * depth M = T * depth M + depth M := Nat.succ_mul _ _
  unfold capH; omega

/-- Constraint 1 in P2's prose form `ℓ + (T+1)·d ≤ H` (`ℓ ≤ m`). -/
theorem capH_c1 {l m T d : ℕ} (hl : l ≤ m) : l + (T + 1) * d ≤ capH m T d := by
  unfold capH; omega

/-- Constraint 2 (`2d ≤ H`) holds when `T ≥ 1` (it is not used; see `cells_step_run`). -/
theorem capH_c2 {m T d : ℕ} (hT : 1 ≤ T) : 2 * d ≤ capH m T d := by
  have h3 : 1 * d ≤ T * d := Nat.mul_le_mul_right _ hT
  have h4 : (T + 1) * d = T * d + d := Nat.succ_mul _ _
  unfold capH; omega

/-- **Depth regions of row `t+1`, stack `k`** (the depth hypotheses of `pf_step_run`,
`sh_step_run_pos`, `ov_step_run`): every `j < H` is in exactly one of pushed fill, in-range
shift, overflow. No hypothesis on `p, q, H`. -/
theorem region_cover (p q H j : ℕ) (hj : j < H) :
    (j < p ∨ (p ≤ j ∧ j < H - max p q + p) ∨ (H - max p q + p ≤ j ∧ j < H)) ∧
    ¬ (j < p ∧ p ≤ j) ∧ ¬ (j < p ∧ H - max p q + p ≤ j) ∧
    ¬ (j < H - max p q + p ∧ H - max p q + p ≤ j) := by
  omega

namespace Enc

variable {M : FinTM2} (E : Enc M)

/-- **`depth_cover` assembly.** S-def + shift families (pushed fill, in-range, overflow): the
positive row-`t` invariant gives every cell literal of row `t+1`, at every depth `j < H`.
Only `hh` and `depth M ≤ H` are assumed about `H`. -/
theorem cells_step_run {T H t : ℕ} {a : List Bool} (s : List (M.Γ M.k₀))
    (hs : cnfSat (Family.family E.layout E.la E.sa E.wa T H E.N) a)
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a) (ht : t < T)
    (hh : ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M) (hdH : depth M ≤ H)
    (hcode : E.CodeHolds a H t (runI M (initList M s) t))
    (hrow : E.CellsHold a H t (E.cell (runI M (initList M s) t))) :
    E.CellsHold a H (t + 1) (E.cell (runI M (initList M s) (t + 1))) := by
  have hS := E.sd_step_run s hs ht hdH hcode hrow
  intro k hk j hj
  rcases (region_cover (E.pl (E.sitIdx (runI M (initList M s) t)) k)
      (E.cn (E.sitIdx (runI M (initList M s) t)) k) H j hj).1 with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact E.pf_step_run s ha ht hh hdH hS hk h
  · exact E.sh_step_run_pos s ha ht hh hrow hS hk h1 h2
  · exact E.ov_step_run s ha ht hh hdH hS hk h1 h2

/-- **One-step invariant** (all four forcing families): code and cells of row `t+1`. -/
theorem row_step_run {T H t : ℕ} {a : List Bool} (s : List (M.Γ M.k₀))
    (hu : cnfSat (Family.family E.layout E.la E.na E.wa T H E.N) a)
    (hs : cnfSat (Family.family E.layout E.la E.sa E.wa T H E.N) a)
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a) (ht : t < T)
    (hh : ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M) (hdH : depth M ≤ H)
    (hcode : E.CodeHolds a H t (runI M (initList M s) t))
    (hrow : E.CellsHold a H t (E.cell (runI M (initList M s) t))) :
    E.CodeHolds a H (t + 1) (runI M (initList M s) (t + 1)) ∧
      E.CellsHold a H (t + 1) (E.cell (runI M (initList M s) (t + 1))) :=
  ⟨E.upd_step_run s hu ht hh hdH hcode hrow, E.cells_step_run s hs ha ht hh hdH hcode hrow⟩

/-- The one-step invariant at the corrected cap: the only assumption left is `|s| ≤ m`. -/
theorem row_step_capH {m T t : ℕ} {a : List Bool} (s : List (M.Γ M.k₀)) (hsm : s.length ≤ m)
    (hu : cnfSat (Family.family E.layout E.la E.na E.wa T (capH m T (depth M)) E.N) a)
    (hs : cnfSat (Family.family E.layout E.la E.sa E.wa T (capH m T (depth M)) E.N) a)
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T (capH m T (depth M))) a)
    (ht : t < T)
    (hcode : E.CodeHolds a (capH m T (depth M)) t (runI M (initList M s) t))
    (hrow : E.CellsHold a (capH m T (depth M)) t (E.cell (runI M (initList M s) t))) :
    E.CodeHolds a (capH m T (depth M)) (t + 1) (runI M (initList M s) (t + 1)) ∧
      E.CellsHold a (capH m T (depth M)) (t + 1) (E.cell (runI M (initList M s) (t + 1))) :=
  E.row_step_run s hu hs ha ht (fun k => capH_height s hsm ht.le k) (depth_le_capH M m T)
    hcode hrow

end Enc

/-! ### Row-`t` induction (C6): chains `row_step_run`; row 0 is `Row0`, derived from the init family
(`init_obl`, below) -/

namespace Enc

variable {M : FinTM2} (E : Enc M)

/-- **Row-0 obligation** (positive form) for the start configuration `initList M s`: its code
literal and all of its cell literals are true at row 0. Discharged for `s = x ++ y` by `init_row0`. -/
def Row0 (a : List Bool) (H : ℕ) (s : List (M.Γ M.k₀)) : Prop :=
  E.CodeHolds a H 0 (initList M s) ∧ E.CellsHold a H 0 (E.cell (initList M s))

/-- **Init obligation, input pinned** (2026-10-01, replaces the placeholder `∃ s` form): the start
stack is the fixed input `x` (instance and `#`) followed by a certificate `y` over the allowed
symbols `Ys`, with `|x ++ y| ≤ m`. Proved from the init clauses by `init_obl`. -/
def InitObl (a : List Bool) (x Ys : List (M.Γ M.k₀)) (m T : ℕ) : Prop :=
  ∃ y : List (M.Γ M.k₀), (∀ z ∈ y, z ∈ Ys) ∧ (x ++ y).length ≤ m ∧
    E.Row0 a (capH m T (depth M)) (x ++ y)

/-- **Row-`t` induction.** With all transition families satisfied, heights bounded on rows `t < T`
and the row-0 obligation `Row0` (a hypothesis here), every row `t ≤ T` carries the positive
invariant of the real run `runI M (initList M s) t`. -/
theorem rows_run {T H : ℕ} {a : List Bool} (s : List (M.Γ M.k₀))
    (hu : cnfSat (Family.family E.layout E.la E.na E.wa T H E.N) a)
    (hs : cnfSat (Family.family E.layout E.la E.sa E.wa T H E.N) a)
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a)
    (hh : ∀ t < T, ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M)
    (hdH : depth M ≤ H) (h0 : E.Row0 a H s) :
    ∀ t ≤ T, E.CodeHolds a H t (runI M (initList M s) t) ∧
      E.CellsHold a H t (E.cell (runI M (initList M s) t)) := by
  intro t
  induction t with
  | zero => intro _; exact h0
  | succ t ih =>
    intro ht
    have hlt : t < T := Nat.lt_of_succ_le ht
    obtain ⟨hc, hr⟩ := ih hlt.le
    exact E.row_step_run s hu hs ha hlt (hh t hlt) hdH hc hr

/-- Row-`t` induction at the corrected cap: only `|s| ≤ m` and `Row0` remain. -/
theorem rows_capH {m T : ℕ} {a : List Bool} (s : List (M.Γ M.k₀)) (hsm : s.length ≤ m)
    (hu : cnfSat (Family.family E.layout E.la E.na E.wa T (capH m T (depth M)) E.N) a)
    (hs : cnfSat (Family.family E.layout E.la E.sa E.wa T (capH m T (depth M)) E.N) a)
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T (capH m T (depth M))) a)
    (h0 : E.Row0 a (capH m T (depth M)) s) :
    ∀ t ≤ T, E.CodeHolds a (capH m T (depth M)) t (runI M (initList M s) t) ∧
      E.CellsHold a (capH m T (depth M)) t (E.cell (runI M (initList M s) t)) :=
  E.rows_run s hu hs ha (fun _ ht k => capH_height s hsm ht.le k) (depth_le_capH M m T) h0

/-- The interface the init family plugs into: `InitObl` (input pinned) plus the transition
families give a certificate `y` over `Ys` such that the assignment tracks the real run on `x ++ y`. -/
theorem rows_of_init {x Ys : List (M.Γ M.k₀)} {m T : ℕ} {a : List Bool}
    (hu : cnfSat (Family.family E.layout E.la E.na E.wa T (capH m T (depth M)) E.N) a)
    (hs : cnfSat (Family.family E.layout E.la E.sa E.wa T (capH m T (depth M)) E.N) a)
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T (capH m T (depth M))) a)
    (hI : E.InitObl a x Ys m T) :
    ∃ y : List (M.Γ M.k₀), (∀ z ∈ y, z ∈ Ys) ∧ (x ++ y).length ≤ m ∧
      ∀ t ≤ T, E.CodeHolds a (capH m T (depth M)) t (runI M (initList M (x ++ y)) t) ∧
        E.CellsHold a (capH m T (depth M)) t (E.cell (runI M (initList M (x ++ y)) t)) := by
  obtain ⟨y, hy, hsm, h0⟩ := hI
  exact ⟨y, hy, hsm, E.rows_capH (x ++ y) hsm hu hs ha h0⟩

end Enc

/-! ### The init family (row 0) and its semantics: discharges `InitObl` with the input pinned -/

theorem cnfSat_append {φ ψ : CNF} {a : List Bool} : cnfSat (φ ++ ψ) a ↔ cnfSat φ a ∧ cnfSat ψ a := by
  simp only [cnfSat, List.mem_append]
  exact ⟨fun h => ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩,
    fun h c hc => hc.elim (h.1 c) (h.2 c)⟩

/-- A satisfied dense unit clause forces its literal. -/
theorem unit_force {V v : ℕ} {φ : CNF} {a : List Bool} (h : cnfSat φ a)
    (hm : Family.denseClause V [(v, true)] ∈ φ) : Tr a v := by
  obtain ⟨p, b, hp, hab⟩ := clauseSat_dense (h _ hm)
  simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hp
  obtain ⟨rfl, rfl⟩ := hp
  exact hab

namespace Enc

variable {M : FinTM2} (E : Enc M)

/-- `⊥` at depth `j` of the input stack, row 0. -/
def zIdx (H j : ℕ) : ℕ := E.layout.cIdx H 0 (E.kc M.k₀) j 0

/-- (I1) The start (label, state) code. -/
def initCode (T H : ℕ) : CNF :=
  [Family.denseClause (E.layout.numVars T H) [(E.layout.xIdx H 0 (E.lc (some M.main,
      M.initialState)), true)]]

/-- (I2) Every stack other than the input stack is empty at row 0. -/
def initOther (T H : ℕ) : CNF :=
  ((List.range E.KK).filter (· ≠ E.kc M.k₀)).flatMap fun k =>
    (List.range H).map fun j => Family.denseClause (E.layout.numVars T H) [(E.layout.cIdx H 0 k j 0, true)]

/-- (I3) The fixed input prefix `x` (the instance and `#`), pinned cell by cell. -/
def initIn (x : List (M.Γ M.k₀)) (T H : ℕ) : CNF :=
  (List.range x.length).map fun j => Family.denseClause (E.layout.numVars T H)
    [(E.layout.cIdx H 0 (E.kc M.k₀) j ((x[j]?).elim 0 (E.enc M.k₀)), true)]

/-- (I4) Certificate depths `|x| ≤ j < m`: `⊥` or some allowed symbol of `Ys`. -/
def initCert (x Ys : List (M.Γ M.k₀)) (m T H : ℕ) : CNF :=
  (List.range (m - x.length)).map fun i => Family.denseClause (E.layout.numVars T H)
    ((E.zIdx H (x.length + i), true) ::
      Ys.map fun z => (E.layout.cIdx H 0 (E.kc M.k₀) (x.length + i) (E.enc M.k₀ z), true))

/-- (I5) Prefix form on the certificate depths: `⊥` at `j` forces `⊥` at `j + 1`. -/
def initPre (x : List (M.Γ M.k₀)) (m T H : ℕ) : CNF :=
  (List.range (m - x.length)).map fun i => Family.denseClause (E.layout.numVars T H)
    [(E.zIdx H (x.length + i), false), (E.zIdx H (x.length + i + 1), true)]

/-- (I6) Length bound: `⊥` at every depth `m ≤ j < H` of the input stack. -/
def initTail (m T H : ℕ) : CNF :=
  (List.range (H - m)).map fun i => Family.denseClause (E.layout.numVars T H) [(E.zIdx H (m + i),
      true)]

/-- **The init family** (row 0): start code, empty work stacks, the input `x` pinned, certificate
cells over `Ys ∪ {⊥}` in prefix form, `⊥` from depth `m` on. -/
def initFamily (x Ys : List (M.Γ M.k₀)) (m T H : ℕ) : CNF :=
  E.initCode T H ++ E.initOther T H ++ E.initIn x T H ++ E.initCert x Ys m T H ++
    E.initPre x m T H ++ E.initTail m T H

theorem initList_k₀ (s : List (M.Γ M.k₀)) : (initList M s).stk M.k₀ = s := by
  simp [initList]

theorem initList_ne (s : List (M.Γ M.k₀)) (k : M.K) (hk : k ≠ M.k₀) : (initList M s).stk k = [] := by
  simp [initList, hk]

/-- **Init semantics.** A satisfying assignment of the init family yields a certificate `y` over
`Ys` such that the start configuration on `x ++ y` satisfies the row-0 invariant. -/
theorem init_row0 {x Ys : List (M.Γ M.k₀)} {m T H : ℕ} {a : List Bool}
    (hx : x.length ≤ m) (hmH : m < H) (hI : cnfSat (E.initFamily x Ys m T H) a) :
    ∃ y : List (M.Γ M.k₀), (∀ z ∈ y, z ∈ Ys) ∧ (x ++ y).length ≤ m ∧ E.Row0 a H (x ++ y) := by
  simp only [initFamily, cnfSat_append] at hI
  obtain ⟨⟨⟨⟨⟨hC, hO⟩, hIn⟩, hCe⟩, hP⟩, hTl⟩ := hI
  -- the forced literals
  have tail : ∀ j, m ≤ j → j < H → Tr a (E.zIdx H j) := fun j h1 h2 => by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h1
    exact unit_force hTl (List.mem_map.2 ⟨i, List.mem_range.2 (by omega), rfl⟩)
  have pre : ∀ j, x.length ≤ j → j < m → Tr a (E.zIdx H j) → Tr a (E.zIdx H (j + 1)) := by
    intro j h1 h2 hz
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h1
    have hm : Family.denseClause (E.layout.numVars T H)
        [(E.zIdx H (x.length + i), false), (E.zIdx H (x.length + i + 1),
            true)] ∈ E.initPre x m T H :=
      List.mem_map.2 ⟨i, List.mem_range.2 (by omega), rfl⟩
    obtain ⟨p, b, hp, hab⟩ := clauseSat_dense (hP _ hm)
    simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hp
    unfold Tr at hz ⊢
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hz] at hab; simp at hab
    · exact hab
  have cert : ∀ j, x.length ≤ j → j < m → ¬ Tr a (E.zIdx H j) →
      ∃ z, z ∈ Ys ∧ Tr a (E.layout.cIdx H 0 (E.kc M.k₀) j (E.enc M.k₀ z)) := by
    intro j h1 h2 hz
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h1
    have hm : Family.denseClause (E.layout.numVars T H) ((E.zIdx H (x.length + i), true) ::
        Ys.map fun z => (E.layout.cIdx H 0 (E.kc M.k₀) (x.length + i) (E.enc M.k₀ z), true)) ∈
        E.initCert x Ys m T H :=
      List.mem_map.2 ⟨i, List.mem_range.2 (by omega), rfl⟩
    obtain ⟨p, b, hp, hab⟩ := clauseSat_dense (hCe _ hm)
    rcases List.mem_cons.1 hp with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact absurd hab hz
    · obtain ⟨z, hz, he⟩ := List.mem_map.1 h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact ⟨z, hz, hab⟩
  -- the first `⊥` at or below `|x|`
  have hex : ∃ j, x.length ≤ j ∧ Tr a (E.zIdx H j) := ⟨m, hx, tail m le_rfl hmH⟩
  classical
  let ℓ := Nat.find hex
  have hxℓ : x.length ≤ ℓ := (Nat.find_spec hex).1
  have hℓm : ℓ ≤ m := Nat.find_min' hex ⟨hx, tail m le_rfl hmH⟩
  have zall : ∀ j, ℓ ≤ j → j < H → Tr a (E.zIdx H j) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact fun _ => (Nat.find_spec hex).2
    | succ j hj ih =>
      intro hjH
      by_cases hjm : j < m
      · exact pre j (by omega) hjm (ih (by omega))
      · exact tail _ (by omega) hjH
  have free : ∀ i, i < ℓ - x.length →
      ∃ z, z ∈ Ys ∧ Tr a (E.layout.cIdx H 0 (E.kc M.k₀) (x.length + i) (E.enc M.k₀ z)) :=
    fun i hi => cert _ (by omega) (by omega) fun hz =>
      Nat.find_min hex (show x.length + i < ℓ by omega) ⟨by omega, hz⟩
  let y : List (M.Γ M.k₀) := List.ofFn fun i : Fin (ℓ - x.length) => Classical.choose (free i i.2)
  have hyl : y.length = ℓ - x.length := List.length_ofFn
  refine ⟨y, fun z hz => ?_, by rw [List.length_append, hyl]; omega, ?_, ?_⟩
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hz
    exact (Classical.choose_spec (free i i.2)).1
  · exact unit_force hC (List.mem_singleton.2 rfl)
  · intro k hk j hj
    by_cases hk0 : k = E.kc M.k₀
    · subst hk0
      rw [E.cell_kc, initList_k₀]
      by_cases hjx : j < x.length
      · rw [List.getElem?_append_left hjx]
        exact unit_force hIn (List.mem_map.2 ⟨j, List.mem_range.2 hjx, rfl⟩)
      · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hjx)
        rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
        by_cases hi : i < ℓ - x.length
        · rw [List.getElem?_ofFn, dite_eq_left hi]
          exact (Classical.choose_spec (free i hi)).2
        · rw [List.getElem?_eq_none (by omega)]
          exact zall _ (by omega) hj
    · have hne : E.kd k ≠ M.k₀ := fun h => hk0 (by rw [← h, E.kc_kd k hk])
      unfold cell
      rw [initList_ne _ _ hne]
      exact unit_force hO (List.mem_flatMap.2 ⟨k, List.mem_filter.2 ⟨List.mem_range.2 hk,
        by simpa using hk0⟩, List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩⟩)

/-- **`init_obl`**: the init family at the corrected cap proves the strengthened obligation. -/
theorem init_obl {x Ys : List (M.Γ M.k₀)} {m T : ℕ} {a : List Bool} (hx : x.length ≤ m)
    (hI : cnfSat (E.initFamily x Ys m T (capH m T (depth M))) a) : E.InitObl a x Ys m T :=
  E.init_row0 hx (by unfold capH; omega) hI

/-- **End to end (soundness direction, up to accept):** the transition families and the init family
at the corrected cap give a certificate `y` over `Ys` whose real run on `x ++ y` the assignment
tracks on every row `t ≤ T`. -/
theorem rows_of_initFamily {x Ys : List (M.Γ M.k₀)} {m T : ℕ} {a : List Bool} (hx : x.length ≤ m)
    (hu : cnfSat (Family.family E.layout E.la E.na E.wa T (capH m T (depth M)) E.N) a)
    (hs : cnfSat (Family.family E.layout E.la E.sa E.wa T (capH m T (depth M)) E.N) a)
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T (capH m T (depth M))) a)
    (hI : cnfSat (E.initFamily x Ys m T (capH m T (depth M))) a) :
    ∃ y : List (M.Γ M.k₀), (∀ z ∈ y, z ∈ Ys) ∧ (x ++ y).length ≤ m ∧
      ∀ t ≤ T, E.CodeHolds a (capH m T (depth M)) t (runI M (initList M (x ++ y)) t) ∧
        E.CellsHold a (capH m T (depth M)) t (E.cell (runI M (initList M (x ++ y)) t)) :=
  E.rows_of_init hu hs ha (E.init_obl hx hI)

end Enc

/-! ### [C6] Accept (row `T`) and literal faithfulness (2026-10-01, second): every literal of every
family survives into its dense clause; the accept family; soundness `accept_sound` -/

/-! ### Literal faithfulness: no literal of a dense clause is dropped (out of range or shadowed) -/

/-- Every literal of `ls` survives into `denseClause V ls`: in range, and not shadowed by an
earlier literal at the same position with the other polarity. -/
def Faithful (V : ℕ) (ls : List (ℕ × Bool)) : Prop :=
  ∀ p b, (p, b) ∈ ls → p < V ∧ ls.lookup p = some b

/-- Every clause of `φ` is a dense clause over `V` variables with faithful literals. -/
def FamOK (V : ℕ) (φ : CNF) : Prop :=
  ∀ c ∈ φ, ∃ ls, c = Family.denseClause V ls ∧ Faithful V ls

/-- `FamOK`, and every clause has a positive literal. -/
def FamPos (V : ℕ) (φ : CNF) : Prop :=
  ∀ c ∈ φ, ∃ ls, c = Family.denseClause V ls ∧ Faithful V ls ∧ ∃ p, (p, true) ∈ ls

theorem FamPos.ok {V : ℕ} {φ : CNF} (h : FamPos V φ) : FamOK V φ := fun c hc =>
  let ⟨ls, h1, h2, _⟩ := h c hc
  ⟨ls, h1, h2⟩

/-- **Exact clause semantics** for faithful literal lists. -/
theorem clauseSat_iff {V : ℕ} {ls : List (ℕ × Bool)} {a : List Bool} (h : Faithful V ls) :
    clauseSat (Family.denseClause V ls) a ↔ ∃ p b, (p, b) ∈ ls ∧ a[p]? = some b := by
  refine ⟨clauseSat_dense, fun ⟨p, b, hp, ha⟩ => ⟨p, b, ?_, ha⟩⟩
  obtain ⟨hV, hl⟩ := h p b hp
  unfold Family.denseClause
  rw [List.getElem?_map, List.getElem?_range hV]
  simp [hl]

theorem lookup_of_mem {p : ℕ} {b : Bool} :
    ∀ {ls : List (ℕ × Bool)}, (p, b) ∈ ls → ∃ b', ls.lookup p = some b'
  | [], h => by simp at h
  | (q, c) :: r, h => by
    by_cases hq : p = q
    · subst hq; exact ⟨c, by simp⟩
    · rw [Family.lookup_cons_ne hq]
      rcases List.mem_cons.1 h with h | h
      · exact absurd (Prod.mk.inj h).1 hq
      · exact lookup_of_mem h

theorem faithful_of_pol {V : ℕ} {ls : List (ℕ × Bool)} (hV : ∀ p b, (p, b) ∈ ls → p < V)
    (hb : ∀ p b b', (p, b) ∈ ls → (p, b') ∈ ls → b = b') : Faithful V ls := by
  intro p b hp
  obtain ⟨b', hl⟩ := lookup_of_mem hp
  exact ⟨hV p b hp, by rw [hl, hb p b' b (mem_of_lookup hl) hp]⟩

theorem faithful_pos {V : ℕ} {ls : List (ℕ × Bool)} (h : ∀ p b, (p, b) ∈ ls → p < V ∧ b = true) :
    Faithful V ls :=
  faithful_of_pol (fun p b hp => (h p b hp).1) fun p b b' hp hp' => by
    rw [(h p b hp).2, (h p b' hp').2]

theorem faithful_single {V p : ℕ} {b : Bool} (h : p < V) : Faithful V [(p, b)] := by
  intro q c hq
  simp only [List.mem_singleton, Prod.mk.injEq] at hq
  obtain ⟨rfl, rfl⟩ := hq
  exact ⟨h, by simp⟩

theorem Inc.ge : ∀ {lo : ℕ} {ls : List (ℕ × Bool)} {V : ℕ}, Family.Inc lo ls V →
    ∀ p b, (p, b) ∈ ls → lo ≤ p
  | _, [], _, _, _, _, h => by simp at h
  | _, (q, _) :: _, _, ⟨h1, h2⟩, p, b, h => by
    rcases List.mem_cons.1 h with h | h
    · rw [(Prod.mk.inj h).1]; exact h1
    · have := Inc.ge h2 p b h; omega

theorem faithful_of_inc : ∀ {lo : ℕ} {ls : List (ℕ × Bool)} {V : ℕ}, Family.Inc lo ls V →
    Faithful V ls
  | _, [], _, _, _, _, h => by simp at h
  | _, (q, c) :: r, _, ⟨h1, h2⟩, p, b, h => by
    have hV := Family.Inc.le h2
    rcases List.mem_cons.1 h with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨by omega, by simp⟩
    · have hq := Inc.ge h2 p b h
      obtain ⟨hp, hl⟩ := faithful_of_inc h2 p b h
      exact ⟨hp, by rw [Family.lookup_cons_ne (by omega)]; exact hl⟩

/-- The all-true assignment satisfies a faithful clause with a positive literal. -/
theorem sat_allTrue {V : ℕ} {ls : List (ℕ × Bool)} (hf : Faithful V ls) (hp : ∃ p, (p, true) ∈ ls) :
    clauseSat (Family.denseClause V ls) (List.replicate V true) := by
  obtain ⟨p, hp⟩ := hp
  refine (clauseSat_iff hf).2 ⟨p, true, hp, ?_⟩
  rw [List.getElem?_replicate, ite_eq_left (hf p true hp).1]

theorem FamPos.allTrue {V : ℕ} {φ : CNF} (h : FamPos V φ) : cnfSat φ (List.replicate V true) := by
  intro c hc
  obtain ⟨ls, rfl, hf, hp⟩ := h c hc
  exact sat_allTrue hf hp

/-! ### The D3 families (update, S-def, shift/overflow/pushed fill) are faithful -/

theorem lt_numVars {L : Family.Layout} {T H t p : ℕ} (ht : t ≤ T) (hp : p < (t + 1) * L.rowW H) :
    p < L.numVars T H :=
  lt_of_lt_of_le hp (Nat.mul_le_mul_right _ (by omega))

theorem fam_pos {L : Family.Layout} {la na : ℕ → ℕ} {wa : ℕ → ℕ → ℕ → ℕ} {N T H : ℕ}
    (hwf : ∀ i < N, Family.WF L la na wa H i) :
    FamPos (L.numVars T H) (Family.family L la na wa T H N) := by
  intro c hc
  obtain ⟨t, ht, hc⟩ := List.mem_flatMap.1 hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
  refine ⟨_, rfl, faithful_of_inc (Family.lits_inc (List.mem_range.1 ht)
    (hwf i (List.mem_range.1 hi))), ⟨Family.litPos L la na wa H t i (L.nLits - 1), List.mem_map.2 ⟨L.nLits - 1, List.mem_range.2 ?_, ?_⟩⟩⟩
  · unfold Family.Layout.nLits; omega
  · simp

theorem sh_pos {L : Family.Layout} {sa : ℕ → ℕ} {pl cn : ℕ → ℕ → ℕ} {pu : ℕ → ℕ → ℕ → ℕ}
    {N T H : ℕ} (hwf : Shift.WF L sa pl cn pu N H) :
    FamPos (L.numVars T H) (Shift.shFamily L sa pl cn pu N T H) := by
  intro c hc
  simp only [Shift.shFamily, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨t, ht, i, hi, k, hk, hc⟩ := hc
  simp only [Shift.shBlk, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  rcases hc with (⟨u, hu, x, hx, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨j, hj, rfl⟩
  · have := Shift.inc_drop (cl := (.sh ⟨x, hx⟩ : Shift.CL L.g L.d))
      (Shift.shPos_mono (i := ⟨i, hi⟩) (k := ⟨k,
          hk⟩) ht hwf (Nat.add_lt_of_lt_sub hu) hx) 0 (Nat.zero_le _)
    rw [List.drop_zero, Shift.clits_sh] at this
    exact ⟨_, rfl, faithful_of_inc this, L.cIdx H (t + 1) k (u + pl i k) x, by simp [Shift.shLits]⟩
  · have := Shift.inc_drop (cl := (.ov : Shift.CL L.g L.d))
      (Shift.ovPos_mono (i := ⟨i, hi⟩) (k := ⟨k, hk⟩) ht hwf hr) 0 (Nat.zero_le _)
    rw [List.drop_zero, Shift.clits_ov] at this
    exact ⟨_, rfl, faithful_of_inc this, L.cIdx H (t + 1) k (H - cn i k + pl i k + r) 0,
        by simp [Shift.ovLits]⟩
  · have hjd : j < L.d := lt_of_lt_of_le hj (hwf.pl_le i hi k hk)
    have := Shift.inc_drop (cl := (.pf ⟨j, hjd⟩ : Shift.CL L.g L.d))
      (Shift.pfPos_mono (i := ⟨i, hi⟩) (k := ⟨k, hk⟩) ht hwf hj) 0 (Nat.zero_le _)
    rw [List.drop_zero, Shift.clits_pf] at this
    exact ⟨_, rfl, faithful_of_inc this, L.cIdx H (t + 1) k j (pu i k j), by simp [Shift.pfLits]⟩

namespace Enc

variable {M : FinTM2} (E : Enc M)

theorem enc_lt (k : M.K) (z : M.Γ k) (h : ∃ i, E.dec k i = z) : E.enc k z < E.g := by
  obtain ⟨i, rfl⟩ := h
  rw [E.enc_dec]; have := E.sz_lt_g k; omega

theorem xIdx_lt {T H t u : ℕ} (ht : t ≤ T) (hu : u < E.A0) :
    E.layout.xIdx H t u < E.layout.numVars T H := by
  refine lt_numVars ht ?_
  unfold Family.Layout.xIdx Family.Layout.rowW
  rw [Nat.succ_mul]
  have : E.layout.A = E.A0 + E.N := rfl
  omega

theorem cIdx_lt {T H t k j x : ℕ} (ht : t ≤ T) (hk : k < E.KK) (hj : j < H) (hx : x < E.g) :
    E.layout.cIdx H t k j x < E.layout.numVars T H :=
  lt_numVars ht (Family.cIdx_lt_next_row (L := E.layout) hk hj hx)

theorem upd_pos {T H : ℕ} (hH : depth M ≤ H) :
    FamPos (E.layout.numVars T H) (Family.family E.layout E.la E.na E.wa T H E.N) :=
  fam_pos fun i _ => E.wf_upd hH i

theorem sdef_pos {T H : ℕ} (hH : depth M ≤ H) :
    FamPos (E.layout.numVars T H) (Family.family E.layout E.la E.sa E.wa T H E.N) :=
  fam_pos fun i hi => E.wf_sdef hH i hi

theorem shift_pos {T H : ℕ} (hH : depth M ≤ H) :
    FamPos (E.layout.numVars T H) (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) :=
  sh_pos (E.wf_sh hH)

/-- **The init family is faithful** (and every clause has a positive literal). -/
theorem init_pos {x Ys : List (M.Γ M.k₀)} {m T H : ℕ} (hx : x.length ≤ m) (hmH : m < H) :
    FamPos (E.layout.numVars T H) (E.initFamily x Ys m T H) := by
  have cl : ∀ k j v, k < E.KK → j < H → v < E.g → E.layout.cIdx H 0 k j v < E.layout.numVars T H :=
    fun k j v hk hj hv => E.cIdx_lt (Nat.zero_le T) hk hj hv
  have e0 : ∀ z : M.Γ M.k₀, E.enc M.k₀ z < E.g := fun z => E.enc_lt _ z (E.input_mem z)
  intro c hc
  simp only [initFamily, List.mem_append] at hc
  rcases hc with ((((hc | hc) | hc) | hc) | hc) | hc
  · obtain rfl := List.mem_singleton.1 hc
    exact ⟨_, rfl, faithful_single (E.xIdx_lt (Nat.zero_le T) (E.lc_lt _)), _,
        List.mem_singleton.2 rfl⟩
  · obtain ⟨k, hk, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hc
    exact ⟨_, rfl, faithful_single (cl _ _ _ (List.mem_range.1 (List.mem_filter.1 hk).1)
      (List.mem_range.1 hj) E.g_pos), _, List.mem_singleton.2 rfl⟩
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hc
    have hj := List.mem_range.1 hj
    refine ⟨_, rfl, faithful_single (cl _ _ _ (E.kc_lt _) (by omega) ?_), _,
        List.mem_singleton.2 rfl⟩
    rw [List.getElem?_eq_getElem hj]
    exact e0 _
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
    have hi := List.mem_range.1 hi
    refine ⟨_, rfl, faithful_pos fun p b hp => ?_, _, List.mem_cons_self⟩
    rcases List.mem_cons.1 hp with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨cl _ _ _ (E.kc_lt _) (by omega) E.g_pos, rfl⟩
    · obtain ⟨z, _, he⟩ := List.mem_map.1 h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact ⟨cl _ _ _ (E.kc_lt _) (by omega) (e0 z), rfl⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
    have hi := List.mem_range.1 hi
    have h2 := cl (E.kc M.k₀) (x.length + i + 1) 0 (E.kc_lt _) (by omega) E.g_pos
    have hg := E.g_pos
    have h1 : E.zIdx H (x.length + i) + 1 ≤ E.zIdx H (x.length + i + 1) := by
      unfold zIdx Family.Layout.cIdx
      have : (E.kc M.k₀ * H + (x.length + i + 1)) * E.layout.g =
          (E.kc M.k₀ * H + (x.length + i)) * E.layout.g + E.layout.g := by ring
      have : E.layout.g = E.g := rfl
      omega
    exact ⟨_, rfl, faithful_of_inc (lo := 0) ⟨Nat.zero_le _, h1, h2⟩, _,
      List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
    have hi := List.mem_range.1 hi
    exact ⟨_, rfl, faithful_single (cl _ _ _ (E.kc_lt _) (by omega) E.g_pos), _,
      List.mem_singleton.2 rfl⟩

/-! ### The accept family (row `T`): exactly the halted start-state code, exactly `acc` on top of `k₁` -/

/-- The code of the halted configuration `haltList` reads: label `none`, state `initialState`. -/
def acode : ℕ := E.lc (none, M.initialState)

/-- (A1) Row `T`'s code block is exactly `acode`: one unit per code `u < A0`, positive iff `u = acode`. -/
def accCode (T H : ℕ) : CNF :=
  (List.range E.A0).map fun u => Family.denseClause (E.layout.numVars T H)
    [(E.layout.xIdx H T u, decide (u = E.acode))]

/-- (A2) Row `T`'s top cell of the output stack `k₁` is exactly `acc`: one unit per code `x < g`. -/
def accCell (acc : M.Γ M.k₁) (T H : ℕ) : CNF :=
  (List.range E.g).map fun x => Family.denseClause (E.layout.numVars T H)
    [(E.layout.cIdx H T (E.kc M.k₁) 0 x, decide (x = E.enc M.k₁ acc))]

/-- **The accept family**: at-least-one and at-most-one (as negated units) on the two places where
acceptance is read, row `T` only. -/
def accFamily (acc : M.Γ M.k₁) (T H : ℕ) : CNF := E.accCode T H ++ E.accCell acc T H

theorem acc_ok {acc : M.Γ M.k₁} {T H : ℕ} (hH : 0 < H) :
    FamOK (E.layout.numVars T H) (E.accFamily acc T H) := by
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hc
    exact ⟨_, rfl, faithful_single (E.xIdx_lt le_rfl (List.mem_range.1 hu))⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
    exact ⟨_, rfl, faithful_single (E.cIdx_lt le_rfl (E.kc_lt _) hH (List.mem_range.1 hx))⟩

theorem unit_pol {V p : ℕ} {b : Bool} {φ : CNF} {a : List Bool} (h : cnfSat φ a)
    (hm : Family.denseClause V [(p, b)] ∈ φ) (ht : Tr a p) : b = true := by
  obtain ⟨q, c, hq, hab⟩ := clauseSat_dense (h _ hm)
  simp only [List.mem_singleton, Prod.mk.injEq] at hq
  obtain ⟨rfl, rfl⟩ := hq
  unfold Tr at ht
  rw [ht] at hab
  exact (Option.some.inj hab).symm

/-- (A1) forces: the only true code literal of row `T` is `acode`. -/
theorem acc_code {acc : M.Γ M.k₁} {T H u : ℕ} {a : List Bool} (h : cnfSat (E.accFamily acc T H) a)
    (hu : u < E.A0) (ht : Tr a (E.layout.xIdx H T u)) : u = E.acode :=
  of_decide_eq_true (unit_pol h (List.mem_append_left _ (List.mem_map.2 ⟨u, List.mem_range.2 hu,
      rfl⟩)) ht)

/-- (A2) forces: the only true top-of-`k₁` literal of row `T` is `enc acc`. -/
theorem acc_cell {acc : M.Γ M.k₁} {T H x : ℕ} {a : List Bool} (h : cnfSat (E.accFamily acc T H) a)
    (hx : x < E.g) (ht : Tr a (E.layout.cIdx H T (E.kc M.k₁) 0 x)) : x = E.enc M.k₁ acc :=
  of_decide_eq_true (unit_pol h (List.mem_append_right _ (List.mem_map.2 ⟨x, List.mem_range.2 hx,
      rfl⟩)) ht)

end Enc

/-- **Accepting configuration** (the shape of `haltList M [acc]` that acceptance reads): halted,
state reset, `acc` on top of the output stack. -/
def Accepts (M : FinTM2) (c : M.Cfg) (acc : M.Γ M.k₁) : Prop :=
  c.l = none ∧ c.var = M.initialState ∧ (c.stk M.k₁).head? = some acc

namespace Enc

variable {M : FinTM2} (E : Enc M)

/-- **Soundness up to plumbing.** A satisfying assignment of the update, S-def, shift, init and
accept families (at the corrected cap) yields a certificate `y` over `Ys` whose real run on
`x ++ y` is accepting at row `T`. No one-hot / at-most-one hypothesis other than the accept family. -/
theorem accept_sound {x Ys : List (M.Γ M.k₀)} {m T : ℕ} {acc : M.Γ M.k₁} {a : List Bool}
    (hx : x.length ≤ m) (hacc : ∃ i, E.dec M.k₁ i = acc)
    (hu : cnfSat (Family.family E.layout E.la E.na E.wa T (capH m T (depth M)) E.N) a)
    (hs : cnfSat (Family.family E.layout E.la E.sa E.wa T (capH m T (depth M)) E.N) a)
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T (capH m T (depth M))) a)
    (hI : cnfSat (E.initFamily x Ys m T (capH m T (depth M))) a)
    (hA : cnfSat (E.accFamily acc T (capH m T (depth M))) a) :
    ∃ y : List (M.Γ M.k₀), (∀ z ∈ y, z ∈ Ys) ∧ (x ++ y).length ≤ m ∧
      Accepts M (runI M (initList M (x ++ y)) T) acc := by
  obtain ⟨y, hy, hl, hrow⟩ := E.rows_of_initFamily hx hu hs ha hI
  obtain ⟨hc, hr⟩ := hrow T le_rfl
  refine ⟨y, hy, hl, ?_⟩
  have hgood := E.run_good (x ++ y) T
  generalize runI M (initList M (x ++ y)) T = c at hc hr hgood
  have h1 : E.code c = E.acode := E.acc_code hA (E.lc_lt _) hc
  have h2 : (c.l, c.var) = ((none : Option M.Λ), M.initialState) := by
    have := congrArg E.ld h1
    simpa only [code, acode, E.ld_lc] using this
  obtain ⟨h2l, h2v⟩ := Prod.mk.inj h2
  have hH : 0 < capH m T (depth M) := by unfold capH; omega
  have h3 := E.acc_cell hA (E.cell_lt c hgood _ _) (hr _ (E.kc_lt M.k₁) 0 hH)
  rw [E.cell_kc] at h3
  obtain ⟨i, rfl⟩ := hacc
  refine ⟨h2l, h2v, ?_⟩
  rw [List.head?_eq_getElem?]
  cases hz : (c.stk M.k₁)[0]? with
  | none => rw [hz, E.enc_dec] at h3; simp at h3
  | some z =>
    rw [hz] at h3
    obtain ⟨n, rfl⟩ := hgood M.k₁ z (List.mem_of_getElem? hz)
    simp only [Option.elim, E.enc_dec, Nat.add_right_cancel_iff] at h3
    rw [Fin.ext h3]

/-- **Contrapositive:** if no certificate `y ∈ Ys*` with `|x ++ y| ≤ m` makes the run accept at
row `T`, then **no** assignment satisfies the five families together (in particular not the
all-true one). -/
theorem unsat_of_noAccept {x Ys : List (M.Γ M.k₀)} {m T : ℕ} {acc : M.Γ M.k₁}
    (hx : x.length ≤ m) (hacc : ∃ i, E.dec M.k₁ i = acc)
    (hno : ¬ ∃ y : List (M.Γ M.k₀), (∀ z ∈ y, z ∈ Ys) ∧ (x ++ y).length ≤ m ∧
      Accepts M (runI M (initList M (x ++ y)) T) acc) (a : List Bool) :
    ¬ (cnfSat (Family.family E.layout E.la E.na E.wa T (capH m T (depth M)) E.N) a ∧
      cnfSat (Family.family E.layout E.la E.sa E.wa T (capH m T (depth M)) E.N) a ∧
      cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T (capH m T (depth M))) a ∧
      cnfSat (E.initFamily x Ys m T (capH m T (depth M))) a ∧
      cnfSat (E.accFamily acc T (capH m T (depth M))) a) :=
  fun ⟨hu, hs, ha, hI, hA⟩ => hno (E.accept_sound hx hacc hu hs ha hI hA)

/-- **The gap accept closes, as a Lean fact:** the all-true assignment satisfies the update,
S-def, shift and init families (every clause has a positive in-range literal). -/
theorem trans_allTrue {x Ys : List (M.Γ M.k₀)} {m T H : ℕ} (hx : x.length ≤ m) (hmH : m < H)
    (hH : depth M ≤ H) :
    cnfSat (Family.family E.layout E.la E.na E.wa T H E.N) (List.replicate (E.layout.numVars T H) true) ∧
    cnfSat (Family.family E.layout E.la E.sa E.wa T H E.N) (List.replicate (E.layout.numVars T H) true) ∧
    cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) (List.replicate (E.layout.numVars T H) true) ∧
    cnfSat (E.initFamily x Ys m T H) (List.replicate (E.layout.numVars T H) true) :=
  ⟨(E.upd_pos hH).allTrue, (E.sdef_pos hH).allTrue, (E.shift_pos hH).allTrue,
    (E.init_pos hx hmH).allTrue⟩

theorem A0_two : 2 ≤ E.A0 := by
  have h1 := E.lc_lt (none, M.initialState)
  have h2 := E.lc_lt (some M.main, M.initialState)
  have hne : E.lc (none, M.initialState) ≠ E.lc (some M.main, M.initialState) := fun h => by
    have := congrArg E.ld h
    simp [E.ld_lc] at this
  omega

/-- ...and the all-true assignment does **not** satisfy the accept family. -/
theorem accFamily_allTrue (acc : M.Γ M.k₁) (T H : ℕ) :
    ¬ cnfSat (E.accFamily acc T H) (List.replicate (E.layout.numVars T H) true) := by
  intro h
  have hne : E.lc (some M.main, M.initialState) ≠ E.acode := fun h => by
    have := congrArg E.ld h
    simp [acode, E.ld_lc] at this
  have hlt := E.xIdx_lt (H := H) (le_refl T) (E.lc_lt (some M.main, M.initialState))
  refine hne (E.acc_code h (E.lc_lt _) ?_)
  unfold Tr
  rw [List.getElem?_replicate, ite_eq_left hlt]

end Enc


/-! ### Link to the repo's output notion (`EvalsTo`, `haltList`) -/

theorem runI_succ' (M : FinTM2) (c : M.Cfg) : ∀ n, runI M c (n + 1) = runI M (stepI M c) n
  | 0 => rfl
  | n + 1 => by rw [runI, runI_succ' M c n]; rfl

theorem iterate_bind_none {σ : Type} (f : σ → Option σ) : ∀ n, (flip bind f)^[n] none = none
  | 0 => rfl
  | n + 1 => by rw [Function.iterate_succ_apply]; exact iterate_bind_none f n

/-- If the real machine reaches `c'` in exactly `n` steps, the idle-extended run agrees at `n`. -/
theorem runI_of_iterate (M : FinTM2) : ∀ (n : ℕ) (c c' : M.Cfg),
    (flip bind (TM2.step M.m))^[n] (some c) = some c' → runI M c n = c'
  | 0, c, c', h => Option.some.inj h
  | n + 1, c, c', h => by
    rw [Function.iterate_succ_apply] at h
    change (flip bind (TM2.step M.m))^[n] (TM2.step M.m c) = some c' at h
    cases hs : TM2.step M.m c with
    | none => rw [hs, iterate_bind_none] at h; exact absurd h (by simp)
    | some c1 =>
      rw [hs] at h
      rw [runI_succ', show stepI M c = c1 by simp [stepI, hs]; try rfl]
      exact runI_of_iterate M n c1 c' h

theorem runI_add (M : FinTM2) (c : M.Cfg) (a : ℕ) : ∀ b, runI M c (a + b) = runI M (runI M c a) b
  | 0 => rfl
  | b + 1 => by
    change stepI M (runI M c (a + b)) = stepI M (runI M (runI M c a) b)
    rw [runI_add M c a b]

/-- A halted configuration idles. -/
theorem runI_halted (M : FinTM2) (c : M.Cfg) (hc : c.l = none) : ∀ t, runI M c t = c
  | 0 => rfl
  | t + 1 => by
    rw [runI, runI_halted M c hc t]
    obtain ⟨l, v, S⟩ := c
    subst hc
    simp [stepI, TM2.step]; try rfl

/-- **Plumbing link.** If the machine outputs `l'` from `initList M s` within `p` steps (the repo's
`TM2OutputsInTime`), then from row `p` on the idle-extended run *is* `haltList M l'`. -/
theorem runI_haltList (M : FinTM2) (s : List (M.Γ M.k₀)) (l' : List (M.Γ M.k₁)) {p : ℕ}
    (h : TM2OutputsInTime M s (some l') p) {T : ℕ} (hT : p ≤ T) :
    runI M (initList M s) T = haltList M l' := by
  have h1 := runI_of_iterate M h.steps _ _ h.evals_in_steps
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (h.steps_le_m.trans hT)
  rw [runI_add, h1, runI_halted _ _ rfl]

/-- What `Accepts` means on a `haltList`: the output's head is `acc`. -/
theorem accepts_haltList (M : FinTM2) (l' : List (M.Γ M.k₁)) (acc : M.Γ M.k₁) :
    Accepts M (haltList M l') acc ↔ l'.head? = some acc := by
  simp [Accepts, haltList]

/-! ### [C5] Completeness: the one-hot image of an accepting real run satisfies all five families
(2026-10-01, third). New ingredients vs. C6: index inversion (`row_pos_inj`, `Layout` injectivity)
and situation injectivity (`Enc.sit_inj`); clause semantics via `clauseSat_iff`. -/

/-- Positions `t·W + r` with `r < W` determine `(t, r)`. -/
theorem row_pos_inj {W t t' r r' : ℕ} (hr : r < W) (hr' : r' < W)
    (h : t * W + r = t' * W + r') : t = t' ∧ r = r' := by
  have hW : 0 < W := by omega
  have e : ∀ t r, r < W → (t * W + r) / W = t := fun t r hr => by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt hr, Nat.zero_add]
  have ht : t = t' := by rw [← e t r hr, h, e t' r' hr']
  subst ht
  exact ⟨rfl, by omega⟩

section Inv

variable {L : Family.Layout}

theorem cIdx_split (H t k j x : ℕ) :
    L.cIdx H t k j x = t * L.rowW H + (L.A + ((k * H + j) * L.g + x)) := by
  unfold Family.Layout.cIdx; ring

theorem cell_off_lt {H k j x : ℕ} (hk : k < L.KK) (hj : j < H) (hx : x < L.g) :
    L.A + ((k * H + j) * L.g + x) < L.rowW H := by
  have h1 : (k * H + j) * L.g + x < (k * H + j + 1) * L.g := by
    rw [Nat.add_one_mul]; omega
  have h2 : k * H + j + 1 ≤ L.KK * H := by
    have := Nat.mul_le_mul_right H (show k + 1 ≤ L.KK by omega)
    rw [Nat.add_one_mul] at this; omega
  have h3 := Nat.mul_le_mul_right L.g h2
  have e : L.KK * H * L.g = L.KK * (H * L.g) := by ring
  unfold Family.Layout.rowW; omega

theorem A_le_rowW (H : ℕ) : L.A ≤ L.rowW H := by unfold Family.Layout.rowW; omega

theorem xIdx_inj {H t t' u u' : ℕ} (hu : u < L.A) (hu' : u' < L.A)
    (h : L.xIdx H t u = L.xIdx H t' u') : t = t' ∧ u = u' :=
  row_pos_inj (lt_of_lt_of_le hu (A_le_rowW H)) (lt_of_lt_of_le hu' (A_le_rowW H)) h

theorem xIdx_ne_cIdx {H t t' u k j x : ℕ} (hu : u < L.A) (hk : k < L.KK) (hj : j < H) (hx : x < L.g) :
    L.xIdx H t u ≠ L.cIdx H t' k j x := by
  intro h
  rw [cIdx_split] at h
  have := (row_pos_inj (lt_of_lt_of_le hu (A_le_rowW H)) (cell_off_lt hk hj hx) h).2
  omega

theorem cIdx_inj {H t t' k k' j j' x x' : ℕ} (hk : k < L.KK) (hj : j < H) (hx : x < L.g)
    (hk' : k' < L.KK) (hj' : j' < H) (hx' : x' < L.g)
    (h : L.cIdx H t k j x = L.cIdx H t' k' j' x') : t = t' ∧ k = k' ∧ j = j' ∧ x = x' := by
  rw [cIdx_split, cIdx_split] at h
  obtain ⟨rfl, h⟩ := row_pos_inj (cell_off_lt hk hj hx) (cell_off_lt hk' hj' hx') h
  obtain ⟨h1, rfl⟩ := row_pos_inj (t := k * H + j) (t' := k' * H + j') hx hx' (by omega)
  obtain ⟨rfl, rfl⟩ := row_pos_inj hj hj' h1
  exact ⟨rfl, rfl, rfl, rfl⟩

end Inv

/-- A natural number below `b^n` is determined by its first `n` base-`b` digits. -/
theorem mod_pow_eq_of_digits {b i i' : ℕ} : ∀ n, (∀ e < n, i / b ^ e % b = i' / b ^ e % b) →
    i % b ^ n = i' % b ^ n
  | 0, _ => by simp [Nat.mod_one]
  | n + 1, h => by
    rw [Nat.mod_pow_succ, Nat.mod_pow_succ, mod_pow_eq_of_digits n fun e he => h e (by omega),
      h n (by omega)]

namespace Enc

variable {M : FinTM2} (E : Enc M)

/-- **Situation injectivity** (C5; the converse of `sitIdx_spec`): a situation `i < N` with the
code and the windows of a good `c` is `sitIdx c`. -/
theorem sit_inj (c : M.Cfg) (hc : E.Good c) {i : ℕ} (hi : i < E.N) (hl : E.la i = E.code c)
    (hw : ∀ k < E.KK, ∀ j < depth M, E.wa i k j = E.cell c k j) : i = E.sitIdx c := by
  obtain ⟨hN, hl', hw'⟩ := E.sitIdx_spec c hc
  set i' := E.sitIdx c
  have hG : 0 < E.G := pow_pos E.g_pos _
  have top : ∀ n, n < E.N → E.la n = n / E.G := fun n hn => by
    unfold la
    exact Nat.mod_eq_of_lt ((Nat.div_lt_iff_lt_mul hG).2 hn)
  have hdig : ∀ e < E.KK * depth M, i / E.g ^ e % E.g = i' / E.g ^ e % E.g := by
    intro e he
    have hd : 0 < depth M := Nat.pos_of_ne_zero fun h => by simp [h] at he
    have hk : e / depth M < E.KK := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
    have hj : e % depth M < depth M := Nat.mod_lt _ hd
    have h1 := hw _ hk _ hj
    have h2 := hw' _ hk _ hj
    unfold wa at h1 h2
    rw [Nat.div_add_mod'] at h1 h2
    rw [h1, h2]
  have hmod := mod_pow_eq_of_digits (b := E.g) (i := i) (i' := i') _ hdig
  have hdiv : i / E.G = i' / E.G := by rw [← top i hi, ← top i' hN, hl, hl']
  rw [← Nat.mod_add_div i E.G, ← Nat.mod_add_div i' E.G]
  unfold G at hdiv ⊢
  rw [hmod, hdiv]

/-! #### The assignment: the exact one-hot image of the real run -/

/-- **The real run's literals**: row `t`'s (label, state) code, its `KK·H` cells (⊥ = code 0
included), and `S[t, sitIdx (row t)]` (stored in row `t+1`). Row 0's situation block is empty. -/
def RunLit (s : List (M.Γ M.k₀)) (H p : ℕ) : Prop :=
  ∃ t, p = E.layout.xIdx H t (E.code (runI M (initList M s) t)) ∨
    (∃ k < E.KK, ∃ j < H, p = E.layout.cIdx H t k j (E.cell (runI M (initList M s) t) k j)) ∨
    p = E.layout.xIdx H (t + 1) (E.sa (E.sitIdx (runI M (initList M s) t)))

open Classical in
/-- **The C5 assignment** on `numVars T H` variables: true exactly on `RunLit`. -/
noncomputable def runAsg (s : List (M.Γ M.k₀)) (T H : ℕ) : List Bool :=
  (List.range (E.layout.numVars T H)).map fun p => decide (E.RunLit s H p)

theorem runAsg_length (s : List (M.Γ M.k₀)) (T H : ℕ) :
    (E.runAsg s T H).length = E.layout.numVars T H := by
  simp [runAsg]

theorem runAsg_get {s : List (M.Γ M.k₀)} {T H p : ℕ} (hp : p < E.layout.numVars T H) (b : Bool)
    (hb : b = true ↔ E.RunLit s H p) : (E.runAsg s T H)[p]? = some b := by
  unfold runAsg
  rw [List.getElem?_map, List.getElem?_range hp]
  cases b <;> simp_all

/-- **C5 clause semantics**: a faithful clause is satisfied by `runAsg` as soon as one of its
literals agrees with `RunLit`. -/
theorem sat_run {s : List (M.Γ M.k₀)} {T H : ℕ} {ls : List (ℕ × Bool)}
    (hf : Faithful (E.layout.numVars T H) ls) {p : ℕ} {b : Bool} (hp : (p, b) ∈ ls)
    (hb : b = true ↔ E.RunLit s H p) :
    clauseSat (Family.denseClause (E.layout.numVars T H) ls) (E.runAsg s T H) :=
  (clauseSat_iff hf).2 ⟨p, b, hp, E.runAsg_get (hf p b hp).1 b hb⟩

/-! #### `RunLit` read back (index inversion) -/

theorem sa_lt {i : ℕ} (hi : i < E.N) : E.sa i < E.layout.A := by
  change E.A0 + i < E.A0 + E.N; omega

theorem code_lt (c : M.Cfg) : E.code c < E.layout.A := by
  have := E.lc_lt (c.l, c.var); show _ < E.A0 + E.N; unfold code; omega

theorem lit_x (s : List (M.Γ M.k₀)) {H t u : ℕ} (hu : u < E.A0) :
    E.RunLit s H (E.layout.xIdx H t u) ↔ u = E.code (runI M (initList M s) t) := by
  have hu' : u < E.layout.A := by show u < E.A0 + E.N; omega
  refine ⟨fun ⟨t', h⟩ => ?_, fun h => ⟨t, Or.inl (by rw [h])⟩⟩
  have hg := E.run_good s t'
  rcases h with h | ⟨k, hk, j, hj, h⟩ | h
  · obtain ⟨rfl, rfl⟩ := xIdx_inj hu' (E.code_lt _) h; rfl
  · exact absurd h (xIdx_ne_cIdx hu' hk hj (E.cell_lt _ hg k j))
  · have := (xIdx_inj hu' (E.sa_lt (E.sitIdx_spec _ hg).1) h).2
    unfold sa at this; omega

theorem lit_c (s : List (M.Γ M.k₀)) {H t k j x : ℕ} (hk : k < E.KK) (hj : j < H) (hx : x < E.g) :
    E.RunLit s H (E.layout.cIdx H t k j x) ↔ x = E.cell (runI M (initList M s) t) k j := by
  refine ⟨fun ⟨t', h⟩ => ?_, fun h => ⟨t, Or.inr (Or.inl ⟨k, hk, j, hj, by rw [h]⟩)⟩⟩
  have hg := E.run_good s t'
  rcases h with h | ⟨k', hk', j', hj', h⟩ | h
  · exact absurd h.symm (xIdx_ne_cIdx (E.code_lt _) hk hj hx)
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := cIdx_inj hk hj hx hk' hj' (E.cell_lt _ hg k' j') h; rfl
  · exact absurd h.symm (xIdx_ne_cIdx (E.sa_lt (E.sitIdx_spec _ hg).1) hk hj hx)

theorem lit_s (s : List (M.Γ M.k₀)) {H t i : ℕ} (hi : i < E.N) :
    E.RunLit s H (E.layout.xIdx H (t + 1) (E.sa i)) ↔ i = E.sitIdx (runI M (initList M s) t) := by
  refine ⟨fun ⟨t', h⟩ => ?_, fun h => ⟨t, Or.inr (Or.inr (by rw [h]))⟩⟩
  have hg := E.run_good s t'
  rcases h with h | ⟨k, hk, j, hj, h⟩ | h
  · have := (xIdx_inj (E.sa_lt hi) (E.code_lt _) h).2
    have := E.lc_lt ((runI M (initList M s) t').l, (runI M (initList M s) t').var)
    unfold sa code at *; omega
  · exact absurd h (xIdx_ne_cIdx (E.sa_lt hi) hk hj (E.cell_lt _ hg k j))
  · obtain ⟨h1, h2⟩ := xIdx_inj (E.sa_lt hi) (E.sa_lt (E.sitIdx_spec _ hg).1) h
    obtain rfl : t = t' := by omega
    unfold sa at h2; omega

/-! #### Family by family -/

/-- **D3Fam families (update, S-def), completeness.** If the head literal of the real situation
is a run literal, every clause `(t, i)` is satisfied: by the head when `i` is the real situation,
otherwise by a false body literal (situation injectivity). -/
theorem fam_complete {T H : ℕ} (s : List (M.Γ M.k₀)) (nx : ℕ → ℕ)
    (hwf : ∀ i < E.N, Family.WF E.layout E.la nx E.wa H i) (hdH : depth M ≤ H)
    (hnx : ∀ t < T,
        E.RunLit s H (E.layout.xIdx H (t + 1) (nx (E.sitIdx (runI M (initList M s) t))))) :
    cnfSat (Family.family E.layout E.la nx E.wa T H E.N) (E.runAsg s T H) := by
  intro c hc
  obtain ⟨t, ht, hc⟩ := List.mem_flatMap.1 hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
  rw [List.mem_range] at ht hi
  have hf := faithful_of_inc (Family.lits_inc ht (hwf i hi))
  have hn : E.layout.nLits = E.KK * depth M + 2 := rfl
  have mem : ∀ j < E.layout.nLits, (Family.litPos E.layout E.la nx E.wa H t i j,
      decide (j = E.layout.nLits - 1)) ∈ Family.lits E.layout E.la nx E.wa H t i :=
    fun j hj => List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩
  set c := runI M (initList M s) t with hc
  by_cases hsit : i = E.sitIdx c
  · refine E.sat_run hf (mem (E.layout.nLits - 1) (by omega)) ?_
    have : Family.litPos E.layout E.la nx E.wa H t i (E.layout.nLits - 1) =
        E.layout.xIdx H (t + 1) (nx i) := by
      unfold Family.litPos; rw [ite_eq_right (by omega),
          ite_eq_right (show ¬ _ ≤ E.layout.KK * E.layout.d by
        change ¬ _ ≤ E.KK * depth M; omega)]
    rw [this, hsit]; simpa using hnx t ht
  by_cases hla : E.la i = E.code c
  · have : ∃ k < E.KK, ∃ j < depth M, E.wa i k j ≠ E.cell c k j := by
      by_contra hno
      push Not at hno
      exact hsit (E.sit_inj c (E.run_good s t) hi hla hno)
    obtain ⟨k, hk, j, hj, hne⟩ := this
    have hkj : k * depth M + j < E.KK * depth M := by
      have := Nat.mul_le_mul_right (depth M) (show k + 1 ≤ E.KK by omega)
      rw [Nat.add_one_mul] at this; omega
    refine E.sat_run hf (mem (k * depth M + j + 1) (by omega)) ?_
    have hd : 0 < depth M := by omega
    have e1 : (k * depth M + j) / depth M = k := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hj, Nat.zero_add]
    have e2 : (k * depth M + j) % depth M = j := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    have : Family.litPos E.layout E.la nx E.wa H t i (k * depth M + j + 1) =
        E.layout.cIdx H t k j (E.wa i k j) := by
      unfold Family.litPos
      rw [ite_eq_right (by omega), ite_eq_left (show _ ≤ E.layout.KK * E.layout.d from
        show _ ≤ E.KK * depth M by omega)]
      change E.layout.cIdx H t ((k * depth M + j + 1 - 1) / depth M) ((k * depth M + j + 1 - 1) % depth M)
        (E.wa i ((k * depth M + j + 1 - 1) / depth M) ((k * depth M + j + 1 - 1) % depth M)) = _
      rw [Nat.add_sub_cancel, e1, e2]
    rw [this, E.lit_c s hk (by omega) (E.wa_lt i k j)]
    simp only [show k * depth M + j + 1 ≠ E.layout.nLits - 1 by omega, decide_false]
    simpa using hne
  · refine E.sat_run hf (mem 0 (by omega)) ?_
    have : Family.litPos E.layout E.la nx E.wa H t i 0 = E.layout.xIdx H t (E.la i) := by
      unfold Family.litPos; rw [ite_eq_left rfl]
    rw [this, E.lit_x s (E.la_lt i)]
    simp only [show (0 : ℕ) ≠ E.layout.nLits - 1 by omega, decide_false]
    simpa using hla

/-- Update family: the head is the real next code (`table_agree`). -/
theorem upd_complete {T H : ℕ} (s : List (M.Γ M.k₀)) (hdH : depth M ≤ H)
    (hh : ∀ t < T, ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M) :
    cnfSat (Family.family E.layout E.la E.na E.wa T H E.N) (E.runAsg s T H) :=
  E.fam_complete s E.na (fun i _ => E.wf_upd hdH i) hdH fun t ht =>
    ⟨t + 1, Or.inl (by rw [(E.table_agree_run H s t (hh t ht)).2.2.2.1])⟩

/-- S-def family: the head is the real situation literal, by definition of `RunLit`. -/
theorem sdef_complete {T H : ℕ} (s : List (M.Γ M.k₀)) (hdH : depth M ≤ H) :
    cnfSat (Family.family E.layout E.la E.sa E.wa T H E.N) (E.runAsg s T H) :=
  E.fam_complete s E.sa (fun i hi => E.wf_sdef hdH i hi) hdH fun t _ =>
    ⟨t, Or.inr (Or.inr rfl)⟩

/-- **Shift / overflow / pushed fill, completeness**: `¬S` is false off the real situation; on it,
the target cell of row `t+1` is `tabRow` (`table_agree`). -/
theorem shift_complete {T H : ℕ} (s : List (M.Γ M.k₀)) (hdH : depth M ≤ H)
    (hh : ∀ t < T, ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M) :
    cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) (E.runAsg s T H) := by
  have hwf := E.wf_sh hdH
  intro c hc
  simp only [Shift.shFamily, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨t, ht, i, hi, k, hk, hc⟩ := hc
  obtain ⟨-, -, -, -, hrow⟩ := E.table_agree_run H s t (hh t ht)
  have hS := E.lit_s s (H := H) (t := t) hi
  set c := runI M (initList M s) t with hcdef
  have hpl := E.pl_le i k
  have hcn := E.cn_le i k
  simp only [Shift.shBlk, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  rcases hc with (⟨u, hu, x, hx, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨j, hj, rfl⟩
  · have := Shift.inc_drop (cl := (.sh ⟨x, hx⟩ : Shift.CL E.layout.g E.layout.d))
      (Shift.shPos_mono (i := ⟨i, hi⟩) (k := ⟨k,
          hk⟩) ht hwf (Nat.add_lt_of_lt_sub hu) hx) 0 (Nat.zero_le _)
    rw [List.drop_zero, Shift.clits_sh] at this
    have hf := faithful_of_inc this
    by_cases hsit : i = E.sitIdx c
    · subst hsit
      by_cases hxc : x = E.cell c k (u + E.cn (E.sitIdx c) k)
      · refine E.sat_run hf (p := E.layout.cIdx H (t + 1) k (u + E.pl (E.sitIdx c) k) x) (b := true)
          (by simp [Shift.shLits]) ?_
        rw [E.lit_c s hk (by omega) hx, hrow k hk _ (by omega)]
        unfold tabRow
        rw [ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel, ← hxc]
        simp
      · refine E.sat_run hf (p := E.layout.cIdx H t k (u + E.cn (E.sitIdx c) k) x) (b := false)
          (by simp [Shift.shLits]) ?_
        rw [E.lit_c s hk (by omega) hx]
        simpa using hxc
    · exact E.sat_run hf (p := E.layout.xIdx H (t + 1) (E.sa i)) (b := false)
        (by simp [Shift.shLits]) (by rw [hS]; simpa using hsit)
  · have := Shift.inc_drop (cl := (.ov : Shift.CL E.layout.g E.layout.d))
      (Shift.ovPos_mono (i := ⟨i, hi⟩) (k := ⟨k, hk⟩) ht hwf hr) 0 (Nat.zero_le _)
    rw [List.drop_zero, Shift.clits_ov] at this
    have hf := faithful_of_inc this
    by_cases hsit : i = E.sitIdx c
    · subst hsit
      refine E.sat_run hf (p := E.layout.cIdx H (t + 1) k (H - E.cn (E.sitIdx c) k + E.pl (E.sitIdx c) k + r) 0)
        (b := true) (by simp [Shift.ovLits]) ?_
      rw [E.lit_c s hk (by omega) E.g_pos, hrow k hk _ (by omega)]
      unfold tabRow
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      simp
    · exact E.sat_run hf (p := E.layout.xIdx H (t + 1) (E.sa i)) (b := false)
        (by simp [Shift.ovLits]) (by rw [hS]; simpa using hsit)
  · have hjd : j < E.layout.d := lt_of_lt_of_le hj (hwf.pl_le i hi k hk)
    have := Shift.inc_drop (cl := (.pf ⟨j, hjd⟩ : Shift.CL E.layout.g E.layout.d))
      (Shift.pfPos_mono (i := ⟨i, hi⟩) (k := ⟨k, hk⟩) ht hwf hj) 0 (Nat.zero_le _)
    rw [List.drop_zero, Shift.clits_pf] at this
    have hf := faithful_of_inc this
    by_cases hsit : i = E.sitIdx c
    · subst hsit
      refine E.sat_run hf (p := E.layout.cIdx H (t + 1) k j (E.pu (E.sitIdx c) k j)) (b := true)
        (by simp [Shift.pfLits]) ?_
      rw [E.lit_c s hk (by omega) (E.pu_lt _ k j hj), hrow k hk _ (by omega)]
      unfold tabRow
      rw [ite_eq_left hj]
      simp
    · exact E.sat_run hf (p := E.layout.xIdx H (t + 1) (E.sa i)) (b := false)
        (by simp [Shift.pfLits]) (by rw [hS]; simpa using hsit)


/-- A unit clause on a run literal is satisfied. -/
theorem sat_unit {s : List (M.Γ M.k₀)} {T H p : ℕ} (hp : p < E.layout.numVars T H)
    (h : E.RunLit s H p) :
    clauseSat (Family.denseClause (E.layout.numVars T H) [(p, true)]) (E.runAsg s T H) :=
  E.sat_run (faithful_single hp) (List.mem_singleton.2 rfl) (iff_of_true rfl h)

/-- Row-0 cell literals of the real start configuration are run literals. -/
theorem lit_cell0 (s : List (M.Γ M.k₀)) {H k j : ℕ} (hk : k < E.KK) (hj : j < H) :
    E.RunLit s H (E.layout.cIdx H 0 k j (E.cell (initList M s) k j)) :=
  ⟨0, Or.inr (Or.inl ⟨k, hk, j, hj, rfl⟩)⟩

theorem cell0_k₀ (s : List (M.Γ M.k₀)) (j : ℕ) :
    E.cell (initList M s) (E.kc M.k₀) j = (s[j]?).elim 0 (E.enc M.k₀) := by
  rw [E.cell_kc, initList_k₀]

/-- **Init family, completeness**: the start configuration on `x ++ y` (`y` over `Ys`,
`|x ++ y| ≤ m < H`) satisfies I1–I6. -/
theorem init_complete {x y Ys : List (M.Γ M.k₀)} {m T H : ℕ} (hy : ∀ z ∈ y, z ∈ Ys)
    (hl : (x ++ y).length ≤ m) (hmH : m < H) :
    cnfSat (E.initFamily x Ys m T H) (E.runAsg (x ++ y) T H) := by
  have cl : ∀ k j v, k < E.KK → j < H → v < E.g → E.layout.cIdx H 0 k j v < E.layout.numVars T H :=
    fun k j v hk hj hv => E.cIdx_lt (Nat.zero_le T) hk hj hv
  have e0 : ∀ z : M.Γ M.k₀, E.enc M.k₀ z < E.g := fun z => E.enc_lt _ z (E.input_mem z)
  have hk0 := E.kc_lt M.k₀
  have hxl : x.length ≤ (x ++ y).length := by simp
  -- the input-stack cell at depth `j` is `⊥` iff `j ≥ |x ++ y|`
  have z0 : ∀ j, (x ++ y).length ≤ j → E.cell (initList M (x ++ y)) (E.kc M.k₀) j = 0 := by
    intro j hj; rw [E.cell0_k₀, List.getElem?_eq_none hj]; rfl
  have z1 : ∀ j, j < (x ++ y).length → E.cell (initList M (x ++ y)) (E.kc M.k₀) j ≠ 0 := by
    intro j hj
    rw [E.cell0_k₀, List.getElem?_eq_getElem hj, Option.elim_some]
    obtain ⟨n, hn⟩ := E.input_mem (x ++ y)[j]
    rw [← hn, E.enc_dec]; omega
  simp only [initFamily, cnfSat_append]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · -- I1
    intro c hc
    obtain rfl := List.mem_singleton.1 hc
    exact E.sat_unit (E.xIdx_lt (Nat.zero_le T) (E.lc_lt _)) ⟨0, Or.inl rfl⟩
  · -- I2
    intro c hc
    obtain ⟨k, hk, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hc
    obtain ⟨hk, hne⟩ := List.mem_filter.1 hk
    rw [List.mem_range] at hk hj
    have hne : E.kd k ≠ M.k₀ := fun h => by
      have := E.kc_kd k hk; rw [h] at this; simp [this] at hne
    have h0 : E.cell (initList M (x ++ y)) k j = 0 := by
      unfold cell; rw [initList_ne _ _ hne]; rfl
    refine E.sat_unit (cl _ _ _ hk hj E.g_pos) ?_
    have := E.lit_cell0 (x ++ y) hk hj
    rwa [h0] at this
  · -- I3
    intro c hc
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_range] at hj
    have hjH : j < H := by omega
    refine E.sat_unit (cl _ _ _ hk0 hjH (by rw [List.getElem?_eq_getElem hj]; exact e0 _)) ?_
    have := E.lit_cell0 (x ++ y) hk0 hjH
    rwa [E.cell0_k₀, List.getElem?_append_left hj] at this
  · -- I4
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_range] at hi
    have hjH : x.length + i < H := by omega
    have hf : Faithful (E.layout.numVars T H) ((E.zIdx H (x.length + i), true) ::
        Ys.map fun z => (E.layout.cIdx H 0 (E.kc M.k₀) (x.length + i) (E.enc M.k₀ z), true)) := by
      refine faithful_pos fun p b hp => ?_
      rcases List.mem_cons.1 hp with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact ⟨cl _ _ _ hk0 hjH E.g_pos, rfl⟩
      · obtain ⟨z, _, he⟩ := List.mem_map.1 h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        exact ⟨cl _ _ _ hk0 hjH (e0 z), rfl⟩
    have hlit := E.lit_cell0 (x ++ y) hk0 hjH
    by_cases hin : x.length + i < (x ++ y).length
    · have hiy : i < y.length := by simp at hin; omega
      refine E.sat_run hf (p := E.layout.cIdx H 0 (E.kc M.k₀) (x.length + i) (E.enc M.k₀ y[i]))
        (b := true) (List.mem_cons_of_mem _ (List.mem_map.2 ⟨_, hy _ (List.getElem_mem hiy), rfl⟩))
        (iff_of_true rfl ?_)
      rwa [E.cell0_k₀, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
        List.getElem?_eq_getElem hiy, Option.elim_some] at hlit
    · refine E.sat_run hf (p := E.zIdx H (x.length + i)) (b := true) List.mem_cons_self
        (iff_of_true rfl ?_)
      unfold zIdx
      rwa [z0 _ (by omega)] at hlit
  · -- I5
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_range] at hi
    have h2 := cl (E.kc M.k₀) (x.length + i + 1) 0 hk0 (by omega) E.g_pos
    have hg := E.g_pos
    have h1 : E.zIdx H (x.length + i) + 1 ≤ E.zIdx H (x.length + i + 1) := by
      unfold zIdx Family.Layout.cIdx
      have : (E.kc M.k₀ * H + (x.length + i + 1)) * E.layout.g =
          (E.kc M.k₀ * H + (x.length + i)) * E.layout.g + E.layout.g := by ring
      have : E.layout.g = E.g := rfl
      omega
    have hf := faithful_of_inc (lo := 0) (V := E.layout.numVars T H)
      (ls := [(E.zIdx H (x.length + i), false), (E.zIdx H (x.length + i + 1), true)])
      ⟨Nat.zero_le _, h1, h2⟩
    by_cases hin : x.length + i < (x ++ y).length
    · refine E.sat_run hf (p := E.zIdx H (x.length + i)) (b := false) List.mem_cons_self ?_
      unfold zIdx
      rw [E.lit_c _ hk0 (by omega) E.g_pos]
      simpa [runI] using (z1 _ hin).symm
    · refine E.sat_run hf (p := E.zIdx H (x.length + i + 1)) (b := true)
        (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)) (iff_of_true rfl ?_)
      have := E.lit_cell0 (x ++ y) hk0 (show x.length + i + 1 < H by omega)
      unfold zIdx
      rwa [z0 _ (by omega)] at this
  · -- I6
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_range] at hi
    refine E.sat_unit (cl _ _ _ hk0 (by omega) E.g_pos) ?_
    have := E.lit_cell0 (x ++ y) hk0 (show m + i < H by omega)
    unfold zIdx
    rwa [z0 _ (by omega)] at this

/-- **Accept family, completeness**: if the real run accepts at row `T`, the exact one-hot image
satisfies both the positive and the negated units. -/
theorem acc_complete (s : List (M.Γ M.k₀)) {T H : ℕ} {acc : M.Γ M.k₁} (hH : 0 < H)
    (hA : Accepts M (runI M (initList M s) T) acc) :
    cnfSat (E.accFamily acc T H) (E.runAsg s T H) := by
  obtain ⟨hl, hv, hk⟩ := hA
  have hcode : E.code (runI M (initList M s) T) = E.acode := by
    unfold code acode; rw [hl, hv]
  have hcell : E.cell (runI M (initList M s) T) (E.kc M.k₁) 0 = E.enc M.k₁ acc := by
    rw [E.cell_kc, ← List.head?_eq_getElem?, hk]; rfl
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_range] at hu
    refine E.sat_run (faithful_single (E.xIdx_lt le_rfl hu)) (List.mem_singleton.2 rfl) ?_
    rw [E.lit_x s hu, hcode]; simp
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_range] at hx
    refine E.sat_run (faithful_single (E.cIdx_lt le_rfl (E.kc_lt _) hH hx))
      (List.mem_singleton.2 rfl) ?_
    rw [E.lit_c s (E.kc_lt _) hH hx, hcell]; simp

/-- **C5 (completeness), Sit level.** If some certificate `y` over `Ys` with `|x ++ y| ≤ m` makes
the real run accept at row `T`, the exact one-hot image of that run (`runAsg`, on `numVars`
variables) satisfies all five families at the corrected cap. No `|x| ≤ m` or `hacc` needed. -/
theorem accept_complete {x y Ys : List (M.Γ M.k₀)} {m T : ℕ} {acc : M.Γ M.k₁}
    (hy : ∀ z ∈ y, z ∈ Ys) (hl : (x ++ y).length ≤ m)
    (hA : Accepts M (runI M (initList M (x ++ y)) T) acc) :
    let a := E.runAsg (x ++ y) T (capH m T (depth M))
    a.length = E.layout.numVars T (capH m T (depth M)) ∧
    cnfSat (Family.family E.layout E.la E.na E.wa T (capH m T (depth M)) E.N) a ∧
    cnfSat (Family.family E.layout E.la E.sa E.wa T (capH m T (depth M)) E.N) a ∧
    cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T (capH m T (depth M))) a ∧
    cnfSat (E.initFamily x Ys m T (capH m T (depth M))) a ∧
    cnfSat (E.accFamily acc T (capH m T (depth M))) a := by
  have hh : ∀ t < T, ∀ k, ((runI M (initList M (x ++ y)) t).stk k).length ≤
      capH m T (depth M) - depth M := fun t ht k => capH_height (x ++ y) hl ht.le k
  have hdH := depth_le_capH M m T
  exact ⟨E.runAsg_length _ _ _, E.upd_complete _ hdH hh, E.sdef_complete _ hdH,
    E.shift_complete _ hdH hh, E.init_complete hy hl (by unfold capH; omega),
    E.acc_complete _ (by unfold capH; omega) hA⟩

/-- **Soundness + completeness of the five families (Sit level).** With `|x| ≤ m` and `acc`
encodable (soundness's hypotheses), the five families at the corrected cap are jointly satisfiable
iff some certificate `y` over `Ys` with `|x ++ y| ≤ m` makes the real run accept at row `T`. -/
theorem five_iff {x Ys : List (M.Γ M.k₀)} {m T : ℕ} {acc : M.Γ M.k₁}
    (hx : x.length ≤ m) (hacc : ∃ i, E.dec M.k₁ i = acc) :
    (∃ a : List Bool,
      cnfSat (Family.family E.layout E.la E.na E.wa T (capH m T (depth M)) E.N) a ∧
      cnfSat (Family.family E.layout E.la E.sa E.wa T (capH m T (depth M)) E.N) a ∧
      cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T (capH m T (depth M))) a ∧
      cnfSat (E.initFamily x Ys m T (capH m T (depth M))) a ∧
      cnfSat (E.accFamily acc T (capH m T (depth M))) a) ↔
    ∃ y : List (M.Γ M.k₀), (∀ z ∈ y, z ∈ Ys) ∧ (x ++ y).length ≤ m ∧
      Accepts M (runI M (initList M (x ++ y)) T) acc := by
  constructor
  · rintro ⟨a, hu, hs, ha, hI, hA⟩
    exact E.accept_sound hx hacc hu hs ha hI hA
  · rintro ⟨y, hy, hl, hA⟩
    obtain ⟨_, h⟩ := E.accept_complete hy hl hA
    exact ⟨_, h⟩

end Enc

end C6

end Cslib.Complexity.CookLevin.Situation
