/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.FlowShop.Basic
import CSLibExt.Computability.Complexity.PolynomialEncoding.Bounds
import CSLibExt.Computability.Complexity.PolynomialEncoding.ListParts
import CSLibExt.Computability.Complexity.PolynomialEncoding.PairSplit
import CSLibExt.Computability.Complexity.PolynomialEncoding.Copy
import CSLibExt.Computability.Complexity.PolynomialEncoding.NormalizeRun
import CSLibExt.Computability.Complexity.FramedCNF.Normalize
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import CSLibExt.Computability.CookLevin
import MathlibExt.Computability.TuringMachine.Recursive.OfTM2

/-!
# A polynomial-time verifier for three-machine flow-shop scheduling

An encoded list of start times is a certificate of polynomial size. A finite multi-stack
Turing machine checks the certificate in polynomial time, proving membership in NP.
-/

public section

namespace MetaMathlibExt.Complexity.NPComplete.FlowShop

open BitstringEncoding
open Cslib.Complexity.PolynomialEncoding

private theorem witness_bounded {i : FlowShopInstance} {s : List (List ℕ)}
    (hlen : s.length = i.1.length) (hrows : ∀ row ∈ s, row.length = 3)
    (hjob : ∀ j < i.1.length, (s.getD j []).getD 0 0 + (i.1.getD j []).getD 0 0 ≤
        (s.getD j []).getD 1 0 ∧
      (s.getD j []).getD 1 0 + (i.1.getD j []).getD 1 0 ≤
        (s.getD j []).getD 2 0 ∧
      (s.getD j []).getD 2 0 + (i.1.getD j []).getD 2 0 ≤ i.2) :
    ∀ row ∈ s, ∀ t ∈ row, t ≤ i.2 := by
  intro row hr t ht
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hr
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ht
  have hk3 := hrows _ hr
  rw [List.getElem_eq_getD 0, List.getElem_eq_getD []]
  have hk' : k < 3 := hk3 ▸ hk
  obtain ⟨h₀, h₁, h₂⟩ := hjob j (by omega)
  interval_cases k <;> omega

private theorem deadline_size {x : List Bool} {jobs : List (List ℕ)} {d : ℕ}
    (h : bitDecode x = some (jobs, d)) : d.size ≤ x.length := by
  open Cslib.Complexity.FramedCNF in
  obtain ⟨p, r, rfl, _, hr⟩ := decoded_pair_parts h
  have hn : Computability.decodeNat r = d := Option.some.inj hr
  have hl := length_normalizeNat_le r
  rw [normalizeNat_eq_encode_decode, hn, BinaryNatEncoding.length_encodeNat] at hl
  simp only [List.length_append, length_delimit]
  omega

private theorem nested_encode_length_le (ss : List (List ℕ)) (m : ℕ)
    (h₃ : ∀ s ∈ ss, s.length = 3) (hs : ∀ s ∈ ss, ∀ t ∈ s, t.size ≤ m) :
    (bitEncode ss).length ≤ ss.length * (12 * m + 7) := by
  induction ss with
  | nil => change 0 ≤ 0 * _; simp
  | cons s ss ih =>
    have hs₁ := list_nat_encode_length_le s m (hs s (by simp))
    rw [h₃ s (by simp)] at hs₁
    have hs₂ := ih (fun r hr => h₃ r (by simp [hr])) (fun r hr => hs r (by simp [hr]))
    change (delimit (bitEncode s) ++ bitEncode ss).length ≤ _
    simp only [List.length_append, List.length_cons, length_delimit, Nat.add_mul]
    omega

private theorem certificate_bound {x : List Bool} {i : FlowShopInstance}
    (hd : bitDecode x = some i) (hf : FlowShopFeasible i) :
    ∃ start : List (List ℕ),
      (bitEncode start).length ≤ x.length * (12 * x.length + 7) ∧
      start.length = i.1.length ∧
      (∀ row ∈ start, row.length = 3) ∧
      (∀ j < i.1.length, (start.getD j []).getD 0 0 + (i.1.getD j []).getD 0 0 ≤
          (start.getD j []).getD 1 0 ∧
        (start.getD j []).getD 1 0 + (i.1.getD j []).getD 1 0 ≤
          (start.getD j []).getD 2 0 ∧
        (start.getD j []).getD 2 0 + (i.1.getD j []).getD 2 0 ≤ i.2) ∧
      ∀ k < 3, ∀ a < i.1.length, ∀ b < i.1.length, a < b →
        (start.getD a []).getD k 0 + (i.1.getD a []).getD k 0 ≤
            (start.getD b []).getD k 0 ∨
          (start.getD b []).getD k 0 + (i.1.getD b []).getD k 0 ≤
            (start.getD a []).getD k 0 := by
  obtain ⟨start, hlen, hrows, hjob, hmach⟩ := hf
  refine ⟨start, ?_, hlen, hrows, hjob, hmach⟩
  have hdl := deadline_size hd
  have hjl := decoded_fst_list_length_le hd
  refine (nested_encode_length_le start x.length hrows (fun row hr t ht => ?_)).trans ?_
  · exact (Nat.size_le_size (witness_bounded hlen hrows hjob row hr t ht)).trans hdl
  · exact Nat.mul_le_mul_right _ (hlen ▸ hjl)

private def fits (d : ℕ) (job : List ℕ × List ℕ) : Bool :=
  match job with
  | ([a₀, a₁, a₂], [s₀, s₁, s₂]) =>
    decide (s₀ + a₀ ≤ s₁ ∧ s₁ + a₁ ≤ s₂ ∧ s₂ + a₂ ≤ d)
  | _ => false

private def separate (a b : List ℕ × List ℕ) : Bool :=
  [0, 1, 2].all fun k =>
    decide ((a.2.getD k 0 + a.1.getD k 0 ≤ b.2.getD k 0) ∨
      (b.2.getD k 0 + b.1.getD k 0 ≤ a.2.getD k 0))

private def separated : List (List ℕ × List ℕ) → Bool
  | [] => true
  | j :: js => js.all (separate j) && separated js

private theorem separated_iff (js : List (List ℕ × List ℕ)) :
    separated js = true ↔ js.Pairwise (fun a b => separate a b = true) := by
  induction js with
  | nil => simp [separated]
  | cons j js ih => simp [separated, ih, List.all_eq_true]

private theorem fits_iff (d : ℕ) (a s : List ℕ) :
    fits d (a, s) = true ↔ a.length = 3 ∧ s.length = 3 ∧
      s.getD 0 0 + a.getD 0 0 ≤ s.getD 1 0 ∧
      s.getD 1 0 + a.getD 1 0 ≤ s.getD 2 0 ∧
      s.getD 2 0 + a.getD 2 0 ≤ d := by
  cases a with
  | nil => simp [fits]
  | cons a₀ a =>
    cases a with
    | nil => simp [fits]
    | cons a₁ a =>
      cases a with
      | nil => simp [fits]
      | cons a₂ a =>
        cases a with
        | cons _ _ => simp [fits]
        | nil =>
          cases s with
          | nil => simp [fits]
          | cons s₀ s =>
            cases s with
            | nil => simp [fits]
            | cons s₁ s =>
              cases s with
              | nil => simp [fits]
              | cons s₂ s => cases s <;> simp [fits]

private theorem separate_iff (a b : List ℕ × List ℕ) :
    separate a b = true ↔ ∀ k < 3,
      a.2.getD k 0 + a.1.getD k 0 ≤ b.2.getD k 0 ∨
        b.2.getD k 0 + b.1.getD k 0 ≤ a.2.getD k 0 := by
  simp only [separate, List.all_eq_true, decide_eq_true_eq]
  have hmem (k : ℕ) : k ∈ [0, 1, 2] ↔ k < 3 := by simp; omega
  simp only [hmem]

/-- **Three-machine flow-shop schedule verifier.** Given an encoded instance and start times,
the verifier checks each job's precedence and deadline and tests each pair for nonoverlap
on all three machines. Malformed inputs or certificates are rejected.

Source: The row lengths and start-time inequalities in `WellFormed` and `FlowShopFeasible`. -/
def flowShopCheck (x w : List Bool) : Bool :=
  match bitDecode (α := FlowShopInstance) x, bitDecode (α := List (List ℕ)) w with
  | some (jobs, d), some starts =>
    decide (jobs.length = starts.length) &&
      (jobs.zip starts).all (fits d) &&
      separated (jobs.zip starts)
  | _, _ => false

private theorem check_decoded (jobs starts : List (List ℕ)) (d : ℕ) :
    (decide (jobs.length = starts.length) &&
      (jobs.zip starts).all (fits d) && separated (jobs.zip starts)) = true ↔
      starts.length = jobs.length ∧
      WellFormed (jobs, d) ∧
      (∀ row ∈ starts, row.length = 3) ∧
      (∀ j < jobs.length, (starts.getD j []).getD 0 0 + (jobs.getD j []).getD 0 0 ≤
          (starts.getD j []).getD 1 0 ∧
        (starts.getD j []).getD 1 0 + (jobs.getD j []).getD 1 0 ≤
          (starts.getD j []).getD 2 0 ∧
        (starts.getD j []).getD 2 0 + (jobs.getD j []).getD 2 0 ≤ d) ∧
      ∀ k < 3, ∀ a < jobs.length, ∀ b < jobs.length, a < b →
        (starts.getD a []).getD k 0 + (jobs.getD a []).getD k 0 ≤
            (starts.getD b []).getD k 0 ∨
          (starts.getD b []).getD k 0 + (jobs.getD b []).getD k 0 ≤
            (starts.getD a []).getD k 0 := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, separated_iff, and_assoc]
  by_cases hlen : starts.length = jobs.length
  · have hzip : (jobs.zip starts).length = jobs.length := by simp [hlen]
    have hget (j : ℕ) (hj : j < (jobs.zip starts).length) :
        (jobs.zip starts)[j] = (jobs.getD j [], starts.getD j []) := by
      rw [List.getElem_zip, List.getElem_eq_getD [], List.getElem_eq_getD []]
    simp only [hlen, true_and]
    have hfits : (jobs.zip starts).all (fits d) = true ↔
        WellFormed (jobs, d) ∧
        (∀ row ∈ starts, row.length = 3) ∧
        (∀ j < jobs.length, (starts.getD j []).getD 0 0 + (jobs.getD j []).getD 0 0 ≤
            (starts.getD j []).getD 1 0 ∧
          (starts.getD j []).getD 1 0 + (jobs.getD j []).getD 1 0 ≤
            (starts.getD j []).getD 2 0 ∧
          (starts.getD j []).getD 2 0 + (jobs.getD j []).getD 2 0 ≤ d) := by
      simp only [List.all_eq_true, List.mem_iff_getElem, forall_exists_index,
        forall_apply_eq_imp_iff₂, hget, fits_iff, WellFormed]
      constructor
      · intro h
        refine ⟨?_, ?_, ?_⟩
        · rintro _ j hj rfl
          simpa only [← List.getElem_eq_getD [] (h := hj)] using (h j (hzip ▸ hj)).1
        · rintro _ j hj rfl
          simpa only [← List.getElem_eq_getD [] (h := hj)] using
            (h j (by omega)).2.1
        · intro j hj
          exact (h j (by omega)).2.2
      · rintro ⟨ha, hs, hj⟩ j hj'
        have haj : j < jobs.length := by omega
        have hsj : j < starts.length := by omega
        have hja := ha jobs[j] j haj rfl
        have hjs := hs starts[j] j hsj rfl
        exact ⟨by simpa only [List.getElem_eq_getD []] using hja,
          by simpa only [List.getElem_eq_getD []] using hjs, hj j haj⟩
    rw [hfits, and_assoc, and_assoc]
    congr! 3
    simp only [List.pairwise_iff_getElem, hget, separate_iff]
    constructor
    · intro h k hk a ha b hb hab
      exact h a b (by omega) (by omega) hab k hk
    · intro h a b ha hb hab k hk
      exact h k hk a (by omega) b (by omega) hab
  · have hn := Ne.symm hlen
    simp [hlen, hn]

private theorem check_certificate (x : List Bool) :
    flowShopDec x = true ↔ ∃ w : List Bool,
      w.length ≤ x.length * (12 * x.length + 7) ∧ flowShopCheck x w = true := by
  cases hd : bitDecode (α := FlowShopInstance) x with
  | none => simp [flowShopDec, flowShopCheck, hd]
  | some i =>
    rcases i with ⟨jobs, d⟩
    simp only [flowShopDec, hd, decide_eq_true_eq]
    constructor
    · rintro ⟨hw, hf⟩
      obtain ⟨start, hbound, hlen, hrows, hjob, hpair⟩ := certificate_bound hd hf
      refine ⟨bitEncode start, hbound, ?_⟩
      simp only [flowShopCheck, hd, bitDecode_bitEncode, check_decoded]
      exact ⟨hlen, hw, hrows, hjob, hpair⟩
    · rintro ⟨w, _, hw⟩
      cases hs : bitDecode (α := List (List ℕ)) w with
      | none => simp [flowShopCheck, hd, hs] at hw
      | some start =>
        simp only [flowShopCheck, hd, hs, check_decoded] at hw
        exact ⟨hw.2.1, start, hw.1, hw.2.2⟩

/-! ## Comparing binary sums

The comparator reads the three operands least significant bit first and retains the borrow
in its finite control. At the end it restores all three operand stacks.
-/

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

end Compare

namespace Verifier

open Turing Function TM2Program TM2Embedding
open Cslib.Complexity.FramedCNF Computability

private def boolEmb {A K : Type} (f : A → K) (hf : Injective f) :
    SEmb (fun _ : A => Bool) (fun _ : K => Bool) :=
  ⟨f, hf, fun _ => Equiv.refl _⟩

private theorem eq_of_agrees {A K : Type} {E : SEmb (fun _ : A => Bool) (fun _ : K => Bool)}
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

private structure ThreeStacks (K : Type) where
  input : K
  output : K
  buffer : K
  io : input ≠ output
  ib : input ≠ buffer
  ob : output ≠ buffer

private def ThreeStacks.splitKey {K : Type} (f : ThreeStacks K) : PairSplit.K → K
  | .input => f.input
  | .left => f.output
  | .scratch => f.buffer

private def ThreeStacks.normKey {K : Type} (f : ThreeStacks K) : NormalizeMachine.K → K
  | .input => f.input
  | .output => f.output
  | .buffer => f.buffer

private def ThreeStacks.splitEmb {K : Type} (f : ThreeStacks K) :
    SEmb (fun _ : PairSplit.K => Bool) (fun _ : K => Bool) :=
  boolEmb f.splitKey (by
    intro a b h
    cases a <;> cases b <;>
      simp_all [ThreeStacks.splitKey, f.io, f.ib, f.ob, Ne.symm f.io, Ne.symm f.ib, Ne.symm f.ob])

private def ThreeStacks.normEmb {K : Type} (f : ThreeStacks K) :
    SEmb (fun _ : NormalizeMachine.K => Bool) (fun _ : K => Bool) :=
  boolEmb f.normKey (by
    intro a b h
    cases a <;> cases b <;>
      simp_all [ThreeStacks.normKey, f.io, f.ib, f.ob, Ne.symm f.io, Ne.symm f.ib, Ne.symm f.ob])

private theorem split_run {K L : Type} [DecidableEq K] {M : L → TM2.Stmt (fun _ : K => Bool) L Bool}
    (f : ThreeStacks K) (φ : PairSplit.Lab → L) (he : Embeds f.splitEmb φ PairSplit.prog M)
    (S : K → List Bool) (v : Bool) (hout : S f.output = []) (hbuf : S f.buffer = []) :
    ∃ v' T, RunLe M ((S f.input).length + 1)
      ⟨some (φ .read), v, S⟩
      ⟨some (φ (if (undelimit (S f.input)).isSome then .good else .bad)), v', T⟩ ∧
      ∀ p r, undelimit (S f.input) = some (p, r) →
        T = update (update S f.input r) f.output p := by
  obtain ⟨v', T, hr, hf, ha⟩ := PairSplit.run_embedded f.splitEmb φ he (S f.input) v S (by
    intro k
    cases k <;> simp [ThreeStacks.splitEmb, boolEmb, ThreeStacks.splitKey, PairSplit.st,
      hout, hbuf])
  refine ⟨v', T, hr, fun p r hp => ?_⟩
  refine eq_of_agrees (ha p r hp) ?_ hf ?_
  · intro k
    cases k <;> simp [ThreeStacks.splitEmb, boolEmb, ThreeStacks.splitKey, PairSplit.st,
      hbuf, f.io, Ne.symm f.ib, Ne.symm f.ob]
  · intro k hk
    have h₁ := hk PairSplit.K.input
    have h₂ := hk PairSplit.K.left
    simp only [ThreeStacks.splitEmb, boolEmb, ThreeStacks.splitKey] at h₁ h₂
    simp [update_of_ne h₁.symm, update_of_ne h₂.symm]

private theorem norm_run {K L : Type} [DecidableEq K] {M : L → TM2.Stmt (fun _ : K => Bool) L Bool}
    (f : ThreeStacks K) (φ : NormalizeMachine.Lab → L)
    (he : Embeds f.normEmb φ NormalizeMachine.prog M)
    (S : K → List Bool) (v : Bool) (hout : S f.output = []) (hbuf : S f.buffer = []) :
    ∃ v', RunLe M (2 * (S f.input).length + 3)
      ⟨some (φ (.read none)), v, S⟩ ⟨some (φ .done), v',
        update (update S f.input []) f.output (normalizeNat (S f.input))⟩ := by
  obtain ⟨v', hr⟩ := normalizeNat_run_frame (S f.input) [] v
  obtain ⟨T, ht, ha, hf⟩ := runLe_embed φ he hr (S' := S) (by
    intro k
    cases k <;> simp [ThreeStacks.normEmb, boolEmb, ThreeStacks.normKey,
      NormalizeMachine.st, hout, hbuf])
  have hs : T = update (update S f.input []) f.output (normalizeNat (S f.input)) := by
    refine eq_of_agrees ha ?_ hf ?_
    · intro k
      cases k <;> simp [ThreeStacks.normEmb, boolEmb, ThreeStacks.normKey,
        NormalizeMachine.st, hbuf, f.io, Ne.symm f.ib, Ne.symm f.ob]
    · intro k hk
      have h₁ := hk NormalizeMachine.K.input
      have h₂ := hk NormalizeMachine.K.output
      simp only [ThreeStacks.normEmb, boolEmb, ThreeStacks.normKey] at h₁ h₂
      simp [update_of_ne h₁.symm, update_of_ne h₂.symm]
  exact ⟨v', hs ▸ ht⟩

/-! ## Decoding job and schedule rows -/

private abbrev Row := ℕ × ℕ × ℕ

private def rowList (a : Row) : List ℕ := [a.1, a.2.1, a.2.2]

private def rawRow (r : List Bool) : Option Row := do
  let (a, r) ← undelimit r
  let (b, r) ← undelimit r
  let (c, r) ← undelimit r
  if r.isEmpty then some (decodeNat a, decodeNat b, decodeNat c) else none

private def readRow (x : List Bool) : Option (Row × List Bool) := do
  let (r, x) ← undelimit x
  let a ← rawRow r
  pure (a, x)

private theorem frame_sizes {x p r : List Bool} (h : undelimit x = some (p, r)) :
    p.length < x.length ∧ r.length < x.length := by
  have hh := congrArg List.length
    ((Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp h)
  simp only [List.length_append, length_delimit] at hh
  omega

private theorem rawRow_some {x : List Bool} {a : Row} :
    rawRow x = some a ↔ bitDecode (α := List ℕ) x = some (rowList a) := by
  have aux₀ (y : List Bool) {l : List ℕ} (hl : l ≠ []) (hy : undelimit y = none) :
      bitDecode (α := List ℕ) y ≠ some l := by
    cases y with
    | nil =>
      intro h
      exact hl (Option.some.inj h).symm
    | cons b y =>
      rw [decode_list_none_of_undelimit_none (by simp) hy]
      simp
  have aux₁ (y p r : List Bool) (hy : undelimit y = some (p, r)) (a : ℕ) (as : List ℕ) :
      bitDecode (α := List ℕ) y = some (a :: as) ↔
        decodeNat p = a ∧ bitDecode (α := List ℕ) r = some as := by
    rw [(Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp hy, decode_list_delimit]
    change (bitDecode (α := List ℕ) r).map (decodeNat p :: ·) = _ ↔ _
    cases bitDecode (α := List ℕ) r <;> simp [and_comm]
  have aux₂ (r : List Bool) : bitDecode (α := List ℕ) r = some [] ↔ r.isEmpty = true := by
    cases r with
    | nil => simp [show bitDecode (α := List ℕ) [] = some [] from rfl]
    | cons b r =>
      cases hh : undelimit (b :: r) with
      | none => simp [decode_list_none_of_undelimit_none (by simp) hh]
      | some p =>
        obtain ⟨p, r'⟩ := p
        have he := (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp hh
        have hi : bitDecode (α := List ℕ) (b :: r) ≠ some [] := by
          rw [he, decode_list_delimit]
          change (bitDecode (α := List ℕ) r').map (decodeNat p :: ·) ≠ _
          cases bitDecode (α := List ℕ) r' <;> simp
        simp [hi]
  obtain ⟨a₀, a₁, a₂⟩ := a
  cases h₀ : undelimit x with
  | none => simp [rawRow, h₀, aux₀ x (l := rowList (a₀, a₁, a₂)) (by simp [rowList]) h₀]
  | some p₀ =>
    obtain ⟨p₀, r₀⟩ := p₀
    rw [rowList, aux₁ _ _ _ h₀]
    cases h₁ : undelimit r₀ with
    | none => simp [rawRow, h₀, h₁, aux₀ r₀ (l := [a₁, a₂]) (by simp) h₁]
    | some p₁ =>
      obtain ⟨p₁, r₁⟩ := p₁
      rw [aux₁ _ _ _ h₁]
      cases h₂ : undelimit r₁ with
      | none => simp [rawRow, h₀, h₁, h₂, aux₀ r₁ (l := [a₂]) (by simp) h₂]
      | some p₂ =>
        obtain ⟨p₂, r₂⟩ := p₂
        rw [aux₁ _ _ _ h₂, aux₂]
        cases r₂ <;> simp [rawRow, h₀, h₁, h₂]

private theorem readRow_sizes {x : List Bool} {a : Row} {r : List Bool}
    (h : readRow x = some (a, r)) :
    r.length < x.length ∧
      (encodeNat a.1).length ≤ x.length ∧
      (encodeNat a.2.1).length ≤ x.length ∧
      (encodeNat a.2.2).length ≤ x.length := by
  unfold readRow at h
  cases hx : undelimit x with
  | none => simp [hx] at h
  | some pr =>
    obtain ⟨p, r'⟩ := pr
    have hp : rawRow p = some a ∧ r' = r := by
      cases hz : rawRow p <;> simp_all
    obtain ⟨hp, rfl⟩ := hp
    refine ⟨(frame_sizes hx).2, ?_⟩
    unfold rawRow at hp
    cases h₀ : undelimit p with
    | none => simp [h₀] at hp
    | some p₀ =>
      obtain ⟨p₀, r₀⟩ := p₀
      cases h₁ : undelimit r₀ with
      | none => simp [h₀, h₁] at hp
      | some p₁ =>
        obtain ⟨p₁, r₁⟩ := p₁
        cases h₂ : undelimit r₁ with
        | none => simp [h₀, h₁, h₂] at hp
        | some p₂ =>
          obtain ⟨p₂, r₂⟩ := p₂
          cases r₂ with
          | cons b r₂ => simp [h₀, h₁, h₂] at hp
          | nil =>
            have hrow : (decodeNat p₀, decodeNat p₁, decodeNat p₂) = a := by
              simpa [h₀, h₁, h₂] using hp
            subst a
            simp only [← normalizeNat_eq_encode_decode]
            have hA := frame_sizes hx
            have hB := frame_sizes h₀
            have hC := frame_sizes h₁
            have hD := frame_sizes h₂
            have h₀' := length_normalizeNat_le p₀
            have h₁' := length_normalizeNat_le p₁
            have h₂' := length_normalizeNat_le p₂
            exact ⟨by omega, by omega, by omega⟩

private inductive Column | first | second | third
  deriving DecidableEq

private instance columnsFinite : Fintype Column := Fintype.ofList [.first, .second, .third]
  (fun k => by cases k <;> decide)

private def rowValue (r : Row) : Column → ℕ
  | .first => r.1
  | .second => r.2.1
  | .third => r.2.2

namespace ReadRow

private inductive K | input | row | payload | splitBuffer | normBuffer | number (c : Column)
  deriving DecidableEq

private inductive Lab
  | split (field : Option Column) (l : PairSplit.Lab)
  | norm (field : Column) (l : NormalizeMachine.Lab)
  | atEnd | good | bad
  deriving DecidableEq, Fintype

private def splitStacks (field : Option Column) : ThreeStacks K :=
  match field with
  | none => ⟨.input, .row, .splitBuffer, by decide, by decide, by decide⟩
  | some _ => ⟨.row, .payload, .splitBuffer, by decide, by decide, by decide⟩

private def normStacks (field : Column) : ThreeStacks K :=
  ⟨.payload, .number field, .normBuffer, by simp, by decide, by simp⟩

private def afterField : Column → Lab
  | .first => .split (some .second) .read
  | .second => .split (some .third) .read
  | .third => .atEnd

private def splitLabel (field : Option Column) : PairSplit.Lab → Lab
  | .good =>
    match field with
    | none => .split (some .first) .read
    | some c => .norm c (.read none)
  | .bad => .bad
  | l => .split field l

private def normLabel (field : Column) : NormalizeMachine.Lab → Lab
  | .done => afterField field
  | l => .norm field l

private def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .split field l => mapS (splitStacks field).splitEmb (splitLabel field) (PairSplit.prog l)
  | .norm field l => mapS (normStacks field).normEmb (normLabel field) (NormalizeMachine.prog l)
  | .atEnd => .peek .row (fun _ o => o.isNone) <| .goto fun empty => if empty then .good else .bad
  | .good | .bad => .halt

private theorem split_embeds (field : Option Column) :
    Embeds (splitStacks field).splitEmb (splitLabel field) PairSplit.prog prog := by
  intro l
  cases l <;> simp [splitLabel, prog, PairSplit.prog]

private theorem norm_embeds (field : Column) :
    Embeds (normStacks field).normEmb (normLabel field) NormalizeMachine.prog prog := by
  intro l
  cases l <;> simp [normLabel, prog, NormalizeMachine.prog]

private def st (x r p : List Bool) (ns : Column → List Bool) : K → List Bool
  | .input => x
  | .row => r
  | .payload => p
  | .splitBuffer | .normBuffer => []
  | .number c => ns c

@[simp] private theorem update_input (x r p y : List Bool) (ns : Column → List Bool) :
    update (st x r p ns) .input y = st y r p ns := by
  funext k
  cases k <;> rfl

@[simp] private theorem update_row (x r p y : List Bool) (ns : Column → List Bool) :
    update (st x r p ns) .row y = st x y p ns := by
  funext k
  cases k <;> rfl

@[simp] private theorem update_payload (x r p y : List Bool) (ns : Column → List Bool) :
    update (st x r p ns) .payload y = st x r y ns := by
  funext k
  cases k <;> rfl

@[simp] private theorem update_number (x r p y : List Bool) (ns : Column → List Bool) (c : Column) :
    update (st x r p ns) (.number c) y = st x r p (update ns c y) := by
  funext k
  cases k <;> first
    | rfl
    | simp [st, Function.update_apply]

private theorem value_run (c : Column) (x r : List Bool) (ns : Column → List Bool)
    (hn : ns c = []) (v : Bool) :
    ∃ v' S, RunLe prog (3 * r.length + 4)
      ⟨some (.split (some c) .read), v, st x r [] ns⟩
      ⟨some (if (undelimit r).isSome then afterField c else .bad), v', S⟩ ∧
      ∀ p r', undelimit r = some (p, r') →
        S = st x r' [] (update ns c (encodeNat (decodeNat p))) := by
  obtain ⟨v₁, S, h₁, ha⟩ := split_run (splitStacks (some c)) (splitLabel (some c))
    (split_embeds (some c)) (st x r [] ns) v rfl rfl
  cases hr : undelimit r with
  | none =>
    refine ⟨v₁, S, ?_, by simp⟩
    have hh : RunLe prog (r.length + 1)
        ⟨some (.split (some c) .read), v, st x r [] ns⟩ ⟨some .bad, v₁, S⟩ := by
      simpa [splitStacks, st, splitLabel, hr] using h₁
    simpa [hr] using hh.mono (B' := 3 * r.length + 4) (by omega)
  | some pr =>
    obtain ⟨p, r'⟩ := pr
    have hS : S = st x r' p ns := by simpa [splitStacks, st] using ha p r' hr
    have hh : RunLe prog (r.length + 1)
        ⟨some (.split (some c) .read), v, st x r [] ns⟩
        ⟨some (.norm c (.read none)), v₁, st x r' p ns⟩ := by
      simpa [splitStacks, st, splitLabel, hr, hS] using h₁
    obtain ⟨v₂, h₂⟩ := norm_run (normStacks c) (normLabel c) (norm_embeds c)
      (st x r' p ns) v₁ (by exact hn) rfl
    have hnorm : RunLe prog (2 * p.length + 3)
        ⟨some (.norm c (.read none)), v₁, st x r' p ns⟩
        ⟨some (afterField c), v₂, st x r' [] (update ns c (encodeNat (decodeNat p)))⟩ := by
      simpa [normStacks, st, normalizeNat_eq_encode_decode, normLabel] using h₂
    have hp := (frame_sizes hr).1
    refine ⟨v₂, st x r' [] (update ns c (encodeNat (decodeNat p))), ?_, ?_⟩
    · simpa using (hh.trans hnorm).mono (B' := 3 * r.length + 4) (by omega)
    · intro p' r'' h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      rfl

private theorem run (x : List Bool) (v : Bool) :
    ∃ v' S, RunLe prog (10 * x.length + 14)
      ⟨some (.split none .read), v, st x [] [] (fun _ => [])⟩
      ⟨some (if (readRow x).isSome then .good else .bad), v', S⟩ ∧
      ∀ a r, readRow x = some (a, r) →
        S = st r [] [] (fun c => encodeNat (rowValue a c)) := by
  let zero : Column → List Bool := fun _ => []
  obtain ⟨v₀, S₀, h₀, ha₀⟩ := split_run (splitStacks none) (splitLabel none)
    (split_embeds none) (st x [] [] zero) v rfl rfl
  cases hx : undelimit x with
  | none =>
    refine ⟨v₀, S₀, ?_, by simp [readRow, hx]⟩
    have hr : RunLe prog (x.length + 1)
        ⟨some (.split none .read), v, st x [] [] zero⟩ ⟨some .bad, v₀, S₀⟩ := by
      simpa [splitStacks, st, splitLabel, hx] using h₀
    simpa [readRow, hx, zero] using hr.mono (B' := 10 * x.length + 14) (by omega)
  | some pr =>
    obtain ⟨p, r⟩ := pr
    let start := (Lab.split none .read)
    have hA : RunLe prog (x.length + 1)
        ⟨some start, v, st x [] [] zero⟩
        ⟨some (.split (some .first) .read), v₀, st r p [] zero⟩ := by
      have he := ha₀ p r hx
      simpa [start, splitStacks, st, splitLabel, hx, he] using h₀
    have hxlen := (frame_sizes hx).1
    obtain ⟨v₁, S₁, h₁, ha₁⟩ := value_run .first r p zero rfl v₀
    cases hp : undelimit p with
    | none =>
      have hr := hA.trans (by simpa [hp] using h₁)
      refine ⟨v₁, S₁, ?_, by simp [readRow, rawRow, hx, hp]⟩
      simpa [start, zero, readRow, rawRow, hx, hp] using
        hr.mono (B' := 10 * x.length + 14) (by omega)
    | some pp₁ =>
      obtain ⟨p₁, r₁⟩ := pp₁
      let n₁ := update zero Column.first (encodeNat (decodeNat p₁))
      have hS₁ := ha₁ p₁ r₁ hp
      have hB : RunLe prog (3 * p.length + 4)
          ⟨some (.split (some .first) .read), v₀, st r p [] zero⟩
          ⟨some (.split (some .second) .read), v₁, st r r₁ [] n₁⟩ := by
        simpa [hp, hS₁, afterField, n₁] using h₁
      have hlen₁ := (frame_sizes hp).2
      obtain ⟨v₂, S₂, h₂, ha₂⟩ := value_run .second r r₁ n₁ (by simp [n₁, zero]) v₁
      cases hp₁ : undelimit r₁ with
      | none =>
        have hr := (hA.trans hB).trans (by simpa [hp₁] using h₂)
        refine ⟨v₂, S₂, ?_, by simp [readRow, rawRow, hx, hp, hp₁]⟩
        simpa [start, zero, readRow, rawRow, hx, hp, hp₁] using
          hr.mono (B' := 10 * x.length + 14) (by omega)
      | some pp₂ =>
        obtain ⟨p₂, r₂⟩ := pp₂
        let n₂ := update n₁ Column.second (encodeNat (decodeNat p₂))
        have hS₂ := ha₂ p₂ r₂ hp₁
        have hC : RunLe prog (3 * r₁.length + 4)
            ⟨some (.split (some .second) .read), v₁, st r r₁ [] n₁⟩
            ⟨some (.split (some .third) .read), v₂, st r r₂ [] n₂⟩ := by
          simpa [hp₁, hS₂, afterField, n₂] using h₂
        have hlen₂ := (frame_sizes hp₁).2
        obtain ⟨v₃, S₃, h₃, ha₃⟩ := value_run .third r r₂ n₂ (by simp [n₂, n₁, zero]) v₂
        cases hp₂ : undelimit r₂ with
        | none =>
          have hr := ((hA.trans hB).trans hC).trans (by simpa [hp₂] using h₃)
          refine ⟨v₃, S₃, ?_, by simp [readRow, rawRow, hx, hp, hp₁, hp₂]⟩
          simpa [start, zero, readRow, rawRow, hx, hp, hp₁, hp₂] using
            hr.mono (B' := 10 * x.length + 14) (by omega)
        | some pp₃ =>
          obtain ⟨p₃, r₃⟩ := pp₃
          let n₃ := update n₂ Column.third (encodeNat (decodeNat p₃))
          have hS₃ := ha₃ p₃ r₃ hp₂
          have hD : RunLe prog (3 * r₂.length + 4)
              ⟨some (.split (some .third) .read), v₂, st r r₂ [] n₂⟩
              ⟨some .atEnd, v₃, st r r₃ [] n₃⟩ := by
            simpa [hp₂, hS₃, afterField, n₃] using h₃
          have hE : Run prog 1 ⟨some .atEnd, v₃, st r r₃ [] n₃⟩
              ⟨some (if r₃.isEmpty then .good else .bad), r₃.isEmpty, st r r₃ [] n₃⟩ :=
            Run.single (by cases r₃ <;> rfl)
          have hr := (((hA.trans hB).trans hC).trans hD).trans (hE.le le_rfl)
          refine ⟨r₃.isEmpty, st r r₃ [] n₃, ?_, ?_⟩
          · have hm := hr.mono (B' := 10 * x.length + 14) (by omega)
            cases r₃ <;> simpa [start, zero, readRow, rawRow, hx, hp, hp₁, hp₂] using hm
          · intro a re h
            cases r₃ with
            | cons b r₃ => simp [readRow, rawRow, hx, hp, hp₁, hp₂] at h
            | nil =>
              obtain ⟨rfl, rfl⟩ : (decodeNat p₁, decodeNat p₂, decodeNat p₃) = a ∧ r = re := by
                simpa [readRow, rawRow, hx, hp, hp₁, hp₂] using h
              congr 1
              funext k
              cases k <;> rfl

end ReadRow
private def toRow : List ℕ → Option Row
  | [a, b, c] => some (a, b, c)
  | _ => none

private theorem toRow_eq_some (as : List ℕ) (r : Row) :
    toRow as = some r ↔ rowList r = as := by
  obtain ⟨a, b, c⟩ := r
  rcases as with _ | ⟨a', _ | ⟨b', _ | ⟨c', _ | ⟨d', tail⟩⟩⟩⟩ <;>
    simp [toRow, rowList]; tauto

private theorem rows_eq_some (as : List (List ℕ)) (rs : List Row) :
    as.mapM toRow = some rs ↔ rs.map rowList = as := by
  induction as generalizing rs with
  | nil => cases rs <;> simp
  | cons a as ih =>
    cases rs with
    | nil =>
      rw [List.mapM_cons]
      cases toRow a <;> cases as.mapM toRow <;> simp
    | cons r rs =>
      rw [List.mapM_cons]
      change (toRow a).bind (fun a' => (as.mapM toRow).bind (fun as' => some (a' :: as'))) = _ ↔ _
      simp only [Option.bind_eq_some_iff, Option.some.injEq,
        List.cons.injEq, List.map_cons, toRow_eq_some, ih]
      constructor
      · rintro ⟨_, h, _, h', rfl, rfl⟩
        exact ⟨h, h'⟩
      · rintro ⟨ha, hs⟩
        exact ⟨r, ha, rs, hs, rfl, rfl⟩

private theorem rows_of_shape (as : List (List ℕ)) (h : ∀ a ∈ as, a.length = 3) :
    ∃ rs : List Row, rs.map rowList = as := by
  induction as with
  | nil => exact ⟨[], rfl⟩
  | cons a as ih =>
    have ha := h a (by simp)
    obtain ⟨rs, hr⟩ := ih (fun b hb => h b (by simp [hb]))
    rcases a with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, t⟩⟩⟩⟩
    all_goals simp at ha
    exact ⟨(a, b, c) :: rs, by simp [rowList, hr]⟩

private def decodeRows (x : List Bool) : Option (List Row) :=
  (bitDecode (α := List (List ℕ)) x).bind (·.mapM toRow)

private theorem decodeRows_some (x : List Bool) (rs : List Row) :
    decodeRows x = some rs ↔ bitDecode (α := List (List ℕ)) x = some (rs.map rowList) := by
  unfold decodeRows
  simp only [Option.bind_eq_some_iff, rows_eq_some]
  constructor
  · rintro ⟨_, h, rfl⟩
    exact h
  · intro h
    exact ⟨_, h, rfl⟩

private theorem decodeRows_parts {x p r : List Bool} (h : undelimit x = some (p, r)) :
    decodeRows x = (rawRow p).bind (fun a => (decodeRows r).map (a :: ·)) := by
  apply Option.ext
  intro rs
  rw [decodeRows_some, (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp h, decode_list_delimit]
  cases rs with
  | nil =>
    cases bitDecode (α := List ℕ) p <;> cases bitDecode (α := List (List ℕ)) r <;>
      cases rawRow p <;> cases decodeRows r <;> simp
  | cons a rs =>
    simp only [List.map_cons, Option.bind_eq_some_iff, Option.map_eq_some_iff, List.cons.injEq]
    constructor
    · rintro ⟨u, hu, us, hus, rfl, rfl⟩
      exact ⟨a, rawRow_some.mpr hu, rs, (decodeRows_some _ _).mpr hus, rfl, rfl⟩
    · rintro ⟨u, hu, us, hus, rfl, rfl⟩
      exact ⟨rowList u, rawRow_some.mp hu, us.map rowList, (decodeRows_some _ _).mp hus, rfl, rfl⟩

private theorem decodeRows_failed {x : List Bool} (hx : x ≠ []) (h : readRow x = none) :
    decodeRows x = none := by
  cases hp : undelimit x with
  | none => simp [decodeRows, decode_list_none_of_undelimit_none hx hp]
  | some pr =>
    obtain ⟨p, r⟩ := pr
    rw [decodeRows_parts hp]
    cases ha : rawRow p with
    | none => rfl
    | some a => simp [readRow, hp, ha] at h

private theorem decodeRows_read {x r : List Bool} {a : Row} (h : readRow x = some (a, r)) :
    decodeRows x = (decodeRows r).map (a :: ·) := by
  cases hp : undelimit x with
  | none => simp [readRow, hp] at h
  | some pr =>
    obtain ⟨p, r'⟩ := pr
    cases ha : rawRow p with
    | none => simp [readRow, hp, ha] at h
    | some a' =>
      obtain ⟨rfl, rfl⟩ : a' = a ∧ r' = r := by simpa [readRow, hp, ha] using h
      rw [decodeRows_parts hp, ha]
      rfl

private theorem decodeRows_empty (x : List Bool) :
    decodeRows x = some [] ↔ x = [] := by
  cases x with
  | nil => simp [show decodeRows [] = some [] from rfl]
  | cons b x =>
    cases hp : undelimit (b :: x) with
    | none =>
      rw [decodeRows_failed (by simp) (by simp [readRow, hp])]
      simp
    | some pr =>
      obtain ⟨p, r⟩ := pr
      rw [decodeRows_parts hp]
      cases rawRow p <;> cases decodeRows r <;> simp

private abbrev Job := Row × Row
private abbrev Bits := List Bool × List Bool

private def listJob (j : Job) : List ℕ × List ℕ := (rowList j.1, rowList j.2)
private def localCheck (d : ℕ) (j : Job) : Bool := fits d (listJob j)
private def pairCheck (a b : Job) : Bool := separate (listJob a) (listJob b)

private theorem localCheck_eq (d : ℕ) (j : Job) :
    localCheck d j =
      (decide (j.2.1 + j.1.1 ≤ j.2.2.1) &&
      decide (j.2.2.1 + j.1.2.1 ≤ j.2.2.2) &&
      decide (j.2.2.2 + j.1.2.2 ≤ d)) := by
  obtain ⟨⟨_, _, _⟩, ⟨_, _, _⟩⟩ := j
  simp [localCheck, fits, listJob, rowList, Bool.and_assoc]

private def columnCheck (c : Column) (a b : Job) : Bool :=
  decide (rowValue a.2 c + rowValue a.1 c ≤ rowValue b.2 c) ||
    decide (rowValue b.2 c + rowValue b.1 c ≤ rowValue a.2 c)

private theorem pairCheck_eq (a b : Job) :
    pairCheck a b = (columnCheck .first a b && columnCheck .second a b &&
      columnCheck .third a b) := by
  simp [pairCheck, separate, listJob, rowList, columnCheck, rowValue, Bool.and_assoc]
  rfl

private def innerCheck (a : Job) (inp : Bits) : Bool :=
  match decodeRows inp.1, decodeRows inp.2 with
  | some js, some ss => decide (js.length = ss.length) && (js.zip ss).all (pairCheck a)
  | _, _ => false

private def outerCheck (d : ℕ) (inp : Bits) : Bool :=
  match decodeRows inp.1, decodeRows inp.2 with
  | some js, some ss => decide (js.length = ss.length) &&
      ((js.zip ss).all (localCheck d) && separated ((js.zip ss).map listJob))
  | _, _ => false

private theorem innerCheck_step {a b : Job} {x w x' w' : List Bool}
    (hx : readRow x = some (b.1, x')) (hw : readRow w = some (b.2, w')) :
    innerCheck a (x, w) = (pairCheck a b && innerCheck a (x', w')) := by
  unfold innerCheck
  rw [decodeRows_read hx, decodeRows_read hw]
  cases decodeRows x' <;> cases decodeRows w' <;>
    simp [List.zip_cons_cons, Bool.and_left_comm]

private theorem outerCheck_step {a : Job} {x w x' w' : List Bool} {d : ℕ}
    (hx : readRow x = some (a.1, x')) (hw : readRow w = some (a.2, w')) :
    outerCheck d (x, w) = (localCheck d a && innerCheck a (x', w') && outerCheck d (x', w')) := by
  unfold outerCheck innerCheck
  rw [decodeRows_read hx, decodeRows_read hw]
  cases decodeRows x' <;> cases decodeRows w' <;>
    simp [List.zip_cons_cons, separated, Bool.and_assoc, Bool.and_left_comm,
      List.all_map, Function.comp_def]; rfl

private theorem check_no_rows {x w : List Bool} {d : ℕ} {a : Job}
    (h : decodeRows x = none ∨ decodeRows w = none) :
    outerCheck d (x, w) = false ∧ innerCheck a (x, w) = false := by
  rcases h with h | h
  · simp [outerCheck, innerCheck, h]
  · cases decodeRows x <;> simp [outerCheck, innerCheck, h]

private theorem check_uneven_rows {x w : List Bool} {d : ℕ} {a : Job}
    (h : (x = [] ∧ w ≠ []) ∨ (x ≠ [] ∧ w = [])) :
    outerCheck d (x, w) = false ∧ innerCheck a (x, w) = false := by
  rcases h with ⟨rfl, hw⟩ | ⟨hx, rfl⟩
  · have he := fun h => hw ((decodeRows_empty w).mp h)
    cases hs : decodeRows w with
    | none => exact check_no_rows (Or.inr hs)
    | some rs =>
      cases rs with
      | nil => exact (he hs).elim
      | cons r rs => simp [outerCheck, innerCheck, hs, show decodeRows [] = some [] from rfl]
  · have he := fun h => hx ((decodeRows_empty x).mp h)
    cases hs : decodeRows x with
    | none => exact check_no_rows (Or.inl hs)
    | some rs =>
      cases rs with
      | nil => exact (he hs).elim
      | cons r rs => simp [outerCheck, innerCheck, hs, show decodeRows [] = some [] from rfl]

private theorem zip_map_rowList (js ss : List Row) :
    (js.map rowList).zip (ss.map rowList) = (js.zip ss).map listJob := by
  induction js generalizing ss with
  | nil => simp
  | cons j js ih => cases ss <;> simp [listJob, List.zip_cons_cons, ih]

private theorem outerCheck_correct (x w : List Bool) (d : ℕ) :
    outerCheck d (x, w) =
      match bitDecode (α := List (List ℕ)) x, bitDecode (α := List (List ℕ)) w with
      | some js, some ss =>
        decide (js.length = ss.length) && (js.zip ss).all (fits d) && separated (js.zip ss)
      | _, _ => false := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    cases hx : decodeRows x with
    | none => simp [outerCheck, hx] at h
    | some js =>
      cases hw : decodeRows w with
      | none => simp [outerCheck, hx, hw] at h
      | some ss =>
        simpa [outerCheck, hx, hw, (decodeRows_some _ _).mp hx, (decodeRows_some _ _).mp hw,
          zip_map_rowList, List.all_map, Function.comp_def, localCheck, Bool.and_assoc] using h
  · intro h
    cases hx : bitDecode (α := List (List ℕ)) x with
    | none => simp [hx] at h
    | some js =>
      cases hw : bitDecode (α := List (List ℕ)) w with
      | none => simp [hx, hw] at h
      | some ss =>
        have hc := (check_decoded js ss d).mp (by simpa [hx, hw] using h)
        obtain ⟨jrows, hj⟩ := rows_of_shape js hc.2.1
        obtain ⟨srows, hs⟩ := rows_of_shape ss hc.2.2.1
        subst js
        subst ss
        have ha := (decodeRows_some _ _).mpr hx
        have hb := (decodeRows_some _ _).mpr hw
        simpa [outerCheck, hx, hw, ha, hb, zip_map_rowList, List.all_map, Function.comp_def,
          localCheck, Bool.and_assoc] using h
/-! ## Verifier machine

The outer pass reads a job and its proposed start times, then checks the three precedence
and deadline inequalities. The inner pass reads copies of the remaining rows to compare them
with the current job. Both passes parse and normalize only the rows they are using.
-/

private inductive Pass | outer | inner
  deriving DecidableEq

private instance fintypePass : Fintype Pass :=
  Fintype.ofList [.outer, .inner] (fun k => by cases k <;> decide)

private inductive Side | jobs | starts
  deriving DecidableEq

private instance fintypeSide : Fintype Side :=
  Fintype.ofList [.jobs, .starts] (fun k => by cases k <;> decide)

private def Side.pick (s : Side) {α : Type} (p : α × α) : α :=
  match s with
  | .jobs => p.1
  | .starts => p.2

private inductive Test | precedence₁ | precedence₂ | deadline | pair (c : Column) (rev : Bool)
  deriving DecidableEq, Fintype

private inductive K
  | tape (p : Pass) (s : Side) | field (p : Pass) (s : Side) (c : Column)
  | row | payload | splitTemp | normTemp | raw | deadline | copyTemp
  | compareA | compareB | compareC
  deriving DecidableEq

private inductive Lab
  | split (l : PairSplit.Lab) | norm (l : NormalizeMachine.Lab)
  | head (p : Pass) | read (p : Pass) (s : Side) (l : ReadRow.Lab)
  | cmp (q : Test) (l : Compare.Lab) | copy (s : Side) (reverse : Bool)
  | clear (p : Pass) | yes | no
  deriving DecidableEq, Fintype

private abbrev firstRead : ReadRow.Lab := .split none .read
private abbrev firstCompare : Compare.Lab := .compare 0
private abbrev checkEach (p : Pass) : Lab :=
  match p with
  | .outer => .cmp .precedence₁ firstCompare
  | .inner => .cmp (.pair .first false) firstCompare

private def topSplit : ThreeStacks K :=
  ⟨.raw, .tape .outer .jobs, .splitTemp, by decide, by decide, by decide⟩

private def topNorm : ThreeStacks K :=
  ⟨.raw, .deadline, .normTemp, by decide, by decide, by decide⟩

private def splitLabel : PairSplit.Lab → Lab
  | .good => .norm (.read none)
  | .bad => .no
  | l => .split l

private def normLabel : NormalizeMachine.Lab → Lab
  | .done => .head .outer
  | l => .norm l

private def readKey (p : Pass) (s : Side) : ReadRow.K → K
  | .input => .tape p s
  | .number c => .field p s c
  | .row => .row
  | .payload => .payload
  | .splitBuffer => .splitTemp
  | .normBuffer => .normTemp

private def readEmb (p : Pass) (s : Side) :
    SEmb (fun _ : ReadRow.K => Bool) (fun _ : K => Bool) :=
  boolEmb (readKey p s) (by
    intro a b h
    cases a <;> cases b <;> simp_all [readKey])

private def readLabel (p : Pass) (s : Side) : ReadRow.Lab → Lab
  | .good =>
    match s with
    | .jobs => .read p .starts firstRead
    | .starts => checkEach p
  | .bad => .no
  | l => .read p s l

private def args : Test → K × K × K
  | .precedence₁ => (.field .outer .starts .first, .field .outer .jobs .first,
      .field .outer .starts .second)
  | .precedence₂ => (.field .outer .starts .second, .field .outer .jobs .second,
      .field .outer .starts .third)
  | .deadline => (.field .outer .starts .third, .field .outer .jobs .third, .deadline)
  | .pair c false => (.field .outer .starts c, .field .outer .jobs c, .field .inner .starts c)
  | .pair c true => (.field .inner .starts c, .field .inner .jobs c, .field .outer .starts c)

private def cmpKey (q : Test) : Compare.K → K
  | .a => (args q).1
  | .b => (args q).2.1
  | .c => (args q).2.2
  | .ar => .compareA
  | .br => .compareB
  | .cr => .compareC

private def cmpEmb (q : Test) : SEmb (fun _ : Compare.K => Bool) (fun _ : K => Bool) :=
  boolEmb (cmpKey q) (by
    intro k l h
    cases q with
    | pair c rev => cases c <;> cases rev <;> cases k <;> cases l <;> simp_all [cmpKey, args]
    | _ => cases k <;> cases l <;> simp_all [cmpKey, args])

private def nextColumn : Column → Lab
  | .first => .cmp (.pair .second false) firstCompare
  | .second => .cmp (.pair .third false) firstCompare
  | .third => .clear .inner

private def cmpEnd : Test → Bool → Lab
  | .precedence₁, true => .cmp .precedence₂ firstCompare
  | .precedence₂, true => .cmp .deadline firstCompare
  | .deadline, true => .copy .jobs false
  | .pair c _, true => nextColumn c
  | .pair c false, false => .cmp (.pair c true) firstCompare
  | _, false => .no

private def cmpLabel (q : Test) : Compare.Lab → Lab
  | .done ans => cmpEnd q ans
  | l => .cmp q l

private def copyEnd : Side → Lab
  | .jobs => .copy .starts false
  | .starts => .head .inner

private def jobFields (p : Pass) : List K :=
  [.field p .jobs .first, .field p .jobs .second, .field p .jobs .third,
    .field p .starts .first, .field p .starts .second, .field p .starts .third]

private def emptyEnd : Pass → Lab
  | .outer => .yes
  | .inner => .clear .outer

private def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .split l => mapS topSplit.splitEmb splitLabel (PairSplit.prog l)
  | .norm l => mapS topNorm.normEmb normLabel (NormalizeMachine.prog l)
  | .read p s l => mapS (readEmb p s) (readLabel p s) (ReadRow.prog l)
  | .cmp q l => mapS (cmpEmb q) (cmpLabel q) (Compare.prog l)
  | .head p =>
    .peek (.tape p .jobs) (fun _ o => o.isNone) <| .branch id
      (.peek (.tape p .starts) (fun _ o => o.isNone) <| .branch id
        (.goto fun _ => emptyEnd p) (.goto fun _ => .no))
      (.peek (.tape p .starts) (fun _ o => o.isNone) <| .branch id
        (.goto fun _ => .no) (.goto fun _ => .read p .jobs firstRead))
  | .copy s false => moveB (.tape .outer s) .copyTemp some id (.copy s false) (.copy s true)
  | .copy s true => splitB .copyTemp (.tape .outer s) (.tape .inner s)
      some id id (.copy s true) (copyEnd s)
  | .clear p => cleanS (jobFields p) (.clear p) (.head p)
  | .yes | .no => .halt

private theorem split_embeds : Embeds topSplit.splitEmb splitLabel PairSplit.prog prog := by
  intro l
  cases l <;> simp [splitLabel, prog, PairSplit.prog]

private theorem norm_embeds : Embeds topNorm.normEmb normLabel NormalizeMachine.prog prog := by
  intro l
  cases l <;> simp [normLabel, prog, NormalizeMachine.prog]

private theorem read_embeds (p : Pass) (s : Side) :
    Embeds (readEmb p s) (readLabel p s) ReadRow.prog prog := by
  intro l
  cases l <;> simp [readLabel, prog, ReadRow.prog]

private theorem cmp_embeds (q : Test) :
    Embeds (cmpEmb q) (cmpLabel q) Compare.prog prog := by
  intro l
  cases l <;> simp [cmpLabel, prog, Compare.prog]

private def st (tapes : Pass → Bits) (jobs : Pass → Option Job)
    (d : List Bool) (raw : List Bool := []) : K → List Bool
  | .tape p s => s.pick (tapes p)
  | .field p s c => (jobs p).elim [] (fun j => encodeNat (rowValue (s.pick j) c))
  | .deadline => d
  | .raw => raw
  | _ => []

private def setRead (S : K → List Bool) (p : Pass) (s : Side)
    (rest : List Bool) (row : Row) : K → List Bool
  | .tape q t => if q = p ∧ t = s then rest else S (.tape q t)
  | .field q t c => if q = p ∧ t = s then encodeNat (rowValue row c) else S (.field q t c)
  | k => S k

private theorem read_run (S : K → List Bool) (p : Pass) (s : Side) (v : Bool)
    (hS : ∀ k ≠ ReadRow.K.input, S (readKey p s k) = []) :
    let x := S (.tape p s)
    ∃ v' T, RunLe prog (10 * x.length + 14)
      ⟨some (.read p s firstRead), v, S⟩
      ⟨some (if (readRow x).isSome then readLabel p s .good else .no), v', T⟩ ∧
      ∀ a rest, readRow x = some (a, rest) → T = setRead S p s rest a := by
  intro x
  obtain ⟨v', U, hr, ha⟩ := ReadRow.run x v
  obtain ⟨T, ht, hag, hf⟩ := runLe_embed (readLabel p s) (read_embeds p s) hr (S' := S) (by
    intro k
    cases k with
    | input => simp [readEmb, boolEmb, readKey, ReadRow.st, x]
    | row => exact hS .row (by simp)
    | payload => exact hS .payload (by simp)
    | splitBuffer => exact hS .splitBuffer (by simp)
    | normBuffer => exact hS .normBuffer (by simp)
    | number c => exact hS (.number c) (by simp))
  refine ⟨v', T, ?_, ?_⟩
  · cases hx : readRow x <;> simpa [readLabel, hx] using ht
  · intro a rest h
    rw [ha a rest h] at hag
    refine eq_of_agrees hag ?_ hf ?_
    · intro k
      cases k with
      | input => simp [readEmb, boolEmb, readKey, setRead, ReadRow.st]
      | number c => simp [readEmb, boolEmb, readKey, setRead, ReadRow.st]
      | row => exact hS .row (by simp)
      | payload => exact hS .payload (by simp)
      | splitBuffer => exact hS .splitBuffer (by simp)
      | normBuffer => exact hS .normBuffer (by simp)
    · intro k hk
      cases k with
      | tape q t =>
        have h := hk ReadRow.K.input
        change K.tape p s ≠ K.tape q t at h
        have he : ¬ (q = p ∧ t = s) := by
          rintro ⟨rfl, rfl⟩
          exact h rfl
        simp [setRead, he]
      | field q t c =>
        have h := hk (ReadRow.K.number c)
        change K.field p s c ≠ K.field q t c at h
        have he : ¬ (q = p ∧ t = s) := by
          rintro ⟨rfl, rfl⟩
          exact h rfl
        simp [setRead, he]
      | _ => rfl

private def readPair (x : Bits) : Option (Job × Bits) := do
  let (j, x') ← readRow x.1
  let (s, w') ← readRow x.2
  pure ((j, s), x', w')

private theorem readPair_run (tapes : Pass → Bits) (jobs : Pass → Option Job)
    (d : List Bool) (p : Pass) (v : Bool) (hjob : jobs p = none) :
    let x := tapes p
    ∃ v' T, RunLe prog (10 * (x.1.length + x.2.length) + 28)
      ⟨some (.read p .jobs firstRead), v, st tapes jobs d⟩
      ⟨some (if (readPair x).isSome then checkEach p else .no), v', T⟩ ∧
      ∀ a rest, readPair x = some (a, rest) →
        T = st (update tapes p rest) (update jobs p (some a)) d := by
  intro x
  obtain ⟨v₁, U, h₁, hu⟩ := read_run (st tapes jobs d) p .jobs v (by
    intro k hk
    cases k <;> simp_all [readKey, st])
  change RunLe prog (10 * x.1.length + 14) _ _ at h₁
  change ∀ a r, readRow x.1 = some (a, r) → _ at hu
  cases hx : readRow x.1 with
  | none =>
    refine ⟨v₁, U, ?_, by simp [readPair, hx]⟩
    have h := h₁.mono (B' := 10 * (x.1.length + x.2.length) + 28) (by omega)
    simpa [readPair, st, Side.pick, ← show x = tapes p from rfl, hx] using h
  | some j₁ =>
    obtain ⟨a, r⟩ := j₁
    have he := hu a r hx
    rw [he] at h₁
    let S := setRead (st tapes jobs d) p .jobs r a
    have hA : RunLe prog (10 * x.1.length + 14)
        ⟨some (.read p .jobs firstRead), v, st tapes jobs d⟩
        ⟨some (.read p .starts firstRead), v₁, S⟩ := by
      simpa [st, Side.pick, ← show x = tapes p from rfl, hx, readLabel, S] using h₁
    obtain ⟨v₂, T, h₂, ht⟩ := read_run S p .starts v₁ (by
      intro k hk
      cases k <;> simp_all [readKey, st, S, setRead])
    have hstarts : S (.tape p .starts) = x.2 := by simp [S, setRead, st, Side.pick, x]
    rw [hstarts] at h₂ ht
    have hcomp := hA.trans h₂
    have hcomp' := hcomp.mono (B' := 10 * (x.1.length + x.2.length) + 28) (by omega)
    cases hw : readRow x.2 with
    | none =>
      refine ⟨v₂, T, ?_, by simp [readPair, hx, hw]⟩
      simpa [readPair, S, setRead, st, Side.pick, ← show x = tapes p from rfl, hx, hw] using hcomp'
    | some j₂ =>
      obtain ⟨b, s⟩ := j₂
      refine ⟨v₂, T, ?_, ?_⟩
      · simpa [readPair, readLabel, S, setRead, st, Side.pick,
          ← show x = tapes p from rfl, hx, hw] using hcomp'
      · intro j rest h
        have hpair : (a, b) = j ∧ (r, s) = rest := by simpa [readPair, hx, hw] using h
        obtain ⟨rfl, rfl⟩ := hpair
        rw [ht b s hw]
        funext k
        cases k with
        | tape q t => cases t <;> by_cases he : q = p <;> simp [S, setRead, st, Side.pick, he]
        | field q t c => cases t <;> by_cases he : q = p <;> simp [S, setRead, st, Side.pick, he]
        | _ => rfl
private def jobBound (j : Job) (n : ℕ) : Prop :=
  ∀ (s : Side) (c : Column), (encodeNat (rowValue (s.pick j) c)).length ≤ n

private theorem readPair_fields {inp rest : Bits} {a : Job} (h : readPair inp = some (a, rest)) :
    readRow inp.1 = some (a.1, rest.1) ∧ readRow inp.2 = some (a.2, rest.2) := by
  cases hx : readRow inp.1 with
  | none => simp [readPair, hx] at h
  | some j =>
    obtain ⟨j, x⟩ := j
    cases hw : readRow inp.2 with
    | none => simp [readPair, hx, hw] at h
    | some s =>
      obtain ⟨s, w⟩ := s
      obtain ⟨rfl, rfl⟩ : (j, s) = a ∧ (x, w) = rest := by simpa [readPair, hx, hw] using h
      simp

private theorem readPair_bounds {inp rest : Bits} {a : Job} {n : ℕ}
    (h : readPair inp = some (a, rest)) (hx : inp.1.length ≤ n) (hw : inp.2.length ≤ n) :
    rest.1.length < inp.1.length ∧ rest.2.length < inp.2.length ∧ jobBound a n := by
  obtain ⟨ha, hb⟩ := readPair_fields h
  obtain ⟨hx', h₁, h₂, h₃⟩ := readRow_sizes ha
  obtain ⟨hw', h₄, h₅, h₆⟩ := readRow_sizes hb
  refine ⟨hx', hw', ?_⟩
  intro s c
  cases s <;> cases c <;> simp only [Side.pick, rowValue] <;> omega

private theorem readPair_bad {inp : Bits} (h : readPair inp = none) :
    readRow inp.1 = none ∨ readRow inp.2 = none := by
  cases hx : readRow inp.1 with
  | none => exact Or.inl rfl
  | some j =>
    obtain ⟨j, x⟩ := j
    cases hw : readRow inp.2 with
    | none => exact Or.inr rfl
    | some s =>
      obtain ⟨s, w⟩ := s
      simp [readPair, hx, hw] at h

private theorem cmp_run (q : Test) (S : K → List Bool) (v : Bool) (a b c n : ℕ)
    (ha : S (args q).1 = encodeNat a) (hb : S (args q).2.1 = encodeNat b)
    (hc : S (args q).2.2 = encodeNat c)
    (hbuf : S .compareA = [] ∧ S .compareB = [] ∧ S .compareC = [])
    (h₁ : (encodeNat a).length ≤ n) (h₂ : (encodeNat b).length ≤ n)
    (h₃ : (encodeNat c).length ≤ n) :
    ∃ v', RunLe prog (6 * n + 4)
      ⟨some (.cmp q firstCompare), v, S⟩ ⟨some (cmpEnd q (decide (a + b ≤ c))), v', S⟩ := by
  obtain ⟨v', hr⟩ := Compare.run a b c v
  have hA : Agree (cmpEmb q) (Compare.st (encodeNat a) (encodeNat b) (encodeNat c) [] [] []) S := by
    intro k
    cases k <;> simp [cmpEmb, boolEmb, cmpKey, Compare.st, ha, hb, hc, hbuf]
  obtain ⟨T, ht, hag, hf⟩ := runLe_embed (cmpLabel q) (cmp_embeds q) hr hA
  have ht' := ht.mono (B' := 6 * n + 4) (by omega)
  have he := eq_of_agrees hag hA hf (Frame.refl _)
  simpa [he, cmpLabel] using (show ∃ v'', RunLe prog (6 * n + 4)
    ⟨some (cmpLabel q firstCompare), v, S⟩
    ⟨some (cmpLabel q (.done (decide (a + b ≤ c)))), v'', T⟩ from ⟨v', ht'⟩)

private theorem local_run (tapes : Pass → Bits) (jobs : Pass → Option Job)
    (d n : ℕ) (j : Job) (hj : jobs .outer = some j) (hbound : jobBound j n)
    (hd : (encodeNat d).length ≤ n) (v : Bool) :
    let S := st tapes jobs (encodeNat d)
    ∃ v', RunLe prog (18 * n + 12) ⟨some (checkEach .outer), v, S⟩
      ⟨some (if localCheck d j then .copy .jobs false else .no), v', S⟩ := by
  intro S
  let bound_ := 6 * n + 4
  obtain ⟨v₁, hr₁⟩ := cmp_run .precedence₁ S v j.2.1 j.1.1 j.2.2.1 n
    (by simp [S, st, hj, args, Side.pick, rowValue])
    (by simp [S, st, hj, args, Side.pick, rowValue])
    (by simp [S, st, hj, args, Side.pick, rowValue])
    ⟨rfl, rfl, rfl⟩ (hbound .starts .first) (hbound .jobs .first) (hbound .starts .second)
  by_cases h₁ : j.2.1 + j.1.1 ≤ j.2.2.1
  · have hA : RunLe prog bound_ ⟨some (checkEach .outer), v, S⟩
        ⟨some (.cmp .precedence₂ firstCompare), v₁, S⟩ := by
      simpa [h₁, cmpEnd, bound_] using hr₁
    obtain ⟨v₂, hr₂⟩ := cmp_run .precedence₂ S v₁ j.2.2.1 j.1.2.1 j.2.2.2 n
      (by simp [S, st, hj, args, Side.pick, rowValue])
      (by simp [S, st, hj, args, Side.pick, rowValue])
      (by simp [S, st, hj, args, Side.pick, rowValue])
      ⟨rfl, rfl, rfl⟩ (hbound .starts .second) (hbound .jobs .second) (hbound .starts .third)
    by_cases h₂ : j.2.2.1 + j.1.2.1 ≤ j.2.2.2
    · have hB : RunLe prog bound_ ⟨some (.cmp .precedence₂ firstCompare), v₁, S⟩
          ⟨some (.cmp .deadline firstCompare), v₂, S⟩ := by
        simpa [h₂, cmpEnd, bound_] using hr₂
      obtain ⟨v₃, hr₃⟩ := cmp_run .deadline S v₂ j.2.2.2 j.1.2.2 d n
        (by simp [S, st, hj, args, Side.pick, rowValue])
        (by simp [S, st, hj, args, Side.pick, rowValue]) rfl
        ⟨rfl, rfl, rfl⟩ (hbound .starts .third) (hbound .jobs .third) hd
      have hC : RunLe prog bound_ ⟨some (.cmp .deadline firstCompare), v₂, S⟩
          ⟨some (if localCheck d j then .copy .jobs false else .no), v₃, S⟩ := by
        by_cases h₃ : j.2.2.2 + j.1.2.2 ≤ d <;>
          simpa [h₁, h₂, h₃, cmpEnd, bound_, localCheck_eq] using hr₃
      exact ⟨v₃, ((hA.trans hB).trans hC).mono (by dsimp [bound_]; omega)⟩
    · have hB : RunLe prog bound_ ⟨some (.cmp .precedence₂ firstCompare), v₁, S⟩
          ⟨some (if localCheck d j then .copy .jobs false else .no), v₂, S⟩ := by
        simpa [h₂, cmpEnd, bound_, localCheck_eq] using hr₂
      exact ⟨v₂, (hA.trans hB).mono (by dsimp [bound_]; omega)⟩
  · refine ⟨v₁, ?_⟩
    have h := hr₁.mono (B' := 18 * n + 12) (by omega)
    simpa [h₁, cmpEnd, localCheck_eq] using h

private theorem column_run (tapes : Pass → Bits) (jobs : Pass → Option Job)
    (d : List Bool) (n : ℕ) (a b : Job) (ha : jobs .outer = some a) (hb : jobs .inner = some b)
    (hA : jobBound a n) (hB : jobBound b n) (c : Column) (v : Bool) :
    let S := st tapes jobs d
    ∃ v', RunLe prog (12 * n + 8) ⟨some (.cmp (.pair c false) firstCompare), v, S⟩
      ⟨some (if columnCheck c a b then nextColumn c else .no), v', S⟩ := by
  intro S
  obtain ⟨v₁, h₁⟩ := cmp_run (.pair c false) S v
    (rowValue a.2 c) (rowValue a.1 c) (rowValue b.2 c) n
    (by simp [S, st, ha, args, Side.pick])
    (by simp [S, st, ha, args, Side.pick])
    (by simp [S, st, hb, args, Side.pick])
    ⟨rfl, rfl, rfl⟩ (hA .starts c) (hA .jobs c) (hB .starts c)
  by_cases hc : rowValue a.2 c + rowValue a.1 c ≤ rowValue b.2 c
  · refine ⟨v₁, ?_⟩
    simpa [hc, cmpEnd, columnCheck] using h₁.mono (B' := 12 * n + 8) (by omega)
  · have hr : RunLe prog (6 * n + 4) ⟨some (.cmp (.pair c false) firstCompare), v, S⟩
        ⟨some (.cmp (.pair c true) firstCompare), v₁, S⟩ := by simpa [hc, cmpEnd] using h₁
    obtain ⟨v₂, h₂⟩ := cmp_run (.pair c true) S v₁
      (rowValue b.2 c) (rowValue b.1 c) (rowValue a.2 c) n
      (by simp [S, st, hb, args, Side.pick])
      (by simp [S, st, hb, args, Side.pick])
      (by simp [S, st, ha, args, Side.pick])
      ⟨rfl, rfl, rfl⟩ (hB .starts c) (hB .jobs c) (hA .starts c)
    have hcomp := (hr.trans h₂).mono (B' := 12 * n + 8) (by omega)
    refine ⟨v₂, ?_⟩
    by_cases hc' : rowValue b.2 c + rowValue b.1 c ≤ rowValue a.2 c <;>
      simpa [hc, hc', cmpEnd, columnCheck] using hcomp

private theorem pair_run (tapes : Pass → Bits) (jobs : Pass → Option Job)
    (d : List Bool) (n : ℕ) (a b : Job) (ha : jobs .outer = some a) (hb : jobs .inner = some b)
    (hA : jobBound a n) (hB : jobBound b n) (v : Bool) :
    let S := st tapes jobs d
    ∃ v', RunLe prog (36 * n + 24) ⟨some (checkEach .inner), v, S⟩
      ⟨some (if pairCheck a b then .clear .inner else .no), v', S⟩ := by
  intro S
  obtain ⟨v₁, hr₁⟩ := column_run tapes jobs d n a b ha hb hA hB .first v
  cases h₁ : columnCheck .first a b with
  | false =>
    refine ⟨v₁, ?_⟩
    simpa [h₁, pairCheck_eq] using hr₁.mono (B' := 36 * n + 24) (by omega)
  | true =>
    have h₁' : RunLe prog (12 * n + 8) ⟨some (checkEach .inner), v, S⟩
        ⟨some (.cmp (.pair .second false) firstCompare), v₁, S⟩ := by
      simpa [h₁, nextColumn] using hr₁
    obtain ⟨v₂, hr₂⟩ := column_run tapes jobs d n a b ha hb hA hB .second v₁
    cases h₂ : columnCheck .second a b with
    | false =>
      refine ⟨v₂, ?_⟩
      simpa [h₂, pairCheck_eq] using (h₁'.trans hr₂).mono (B' := 36 * n + 24) (by omega)
    | true =>
      have h₂' : RunLe prog (12 * n + 8)
          ⟨some (.cmp (.pair .second false) firstCompare), v₁, S⟩
          ⟨some (.cmp (.pair .third false) firstCompare), v₂, S⟩ := by
        simpa [h₂, nextColumn] using hr₂
      obtain ⟨v₃, hr₃⟩ := column_run tapes jobs d n a b ha hb hA hB .third v₂
      refine ⟨v₃, ?_⟩
      simpa [h₁, h₂, nextColumn, pairCheck_eq] using
        ((h₁'.trans h₂').trans hr₃).mono (B' := 36 * n + 24) (by omega)
private def passes {α : Type} (outer inner : α) : Pass → α
  | .outer => outer
  | .inner => inner

@[simp] private theorem passes_outer {α : Type} (a b : α) : passes a b .outer = a := rfl
@[simp] private theorem passes_inner {α : Type} (a b : α) : passes a b .inner = b := rfl

@[simp] private theorem passes_update_outer {α : Type} (a b c : α) :
    Function.update (passes a b) .outer c = passes c b := by
  funext p
  cases p <;> simp

@[simp] private theorem passes_update_inner {α : Type} (a b c : α) :
    Function.update (passes a b) .inner c = passes a c := by
  funext p
  cases p <;> simp

private theorem head_run (p : Pass) (tapes : Pass → Bits) (jobs : Pass → Option Job)
    (d : List Bool) (v : Bool) :
    let inp := tapes p
    let next := if inp.1.isEmpty then (if inp.2.isEmpty then emptyEnd p else .no)
      else if inp.2.isEmpty then .no else .read p .jobs firstRead
    Run prog 1 ⟨some (.head p), v, st tapes jobs d⟩
      ⟨some next, inp.2.isEmpty, st tapes jobs d⟩ := by
  rcases ht : tapes p with ⟨x, w⟩
  cases x <;> cases w <;> apply Run.single <;>
    simp [prog, TM2.stepAux, st, Side.pick, ht]

private theorem copy_one (s : Side) (S : K → List Bool) (v : Bool)
    (ht : S .copyTemp = []) (hb : S (.tape .inner s) = []) :
    Run prog (2 * (S (.tape .outer s)).length + 2) ⟨some (.copy s false), v, S⟩
      ⟨some (copyEnd s), false, Function.update S (.tape .inner s) (S (.tape .outer s))⟩ := by
  obtain ⟨T, hr, ha, ht', hc, hf⟩ := copyB_run (M := prog) (first := .copy s false)
    (second := .copy s true) (next := copyEnd s) (da := some) (dt := some)
    (ga := id) (gb := id) (gt := id) rfl rfl (by simp) (by simp) (by simp)
    (fun _ => rfl) (fun _ => rfl) (S (.tape .outer s)) [] v S (by simp)
    (by simp [EndsBitBlock]) (by simp [ht, EndsBitBlock])
  convert hr using 2
  funext k
  by_cases hk : k = .tape .inner s
  · subst k
    simpa [hb] using hc.symm
  by_cases ha' : k = .tape .outer s
  · subst k
    simpa [hk] using ha.symm
  by_cases ht'' : k = .copyTemp
  · subst k
    simpa [hk] using ht'.symm
  simpa [hk] using (hf k ha' hk ht'').symm

private theorem copy_pair (input : Bits) (jobs : Pass → Option Job) (d : List Bool) (v : Bool) :
    Run prog (2 * (input.1.length + input.2.length) + 4)
      ⟨some (.copy .jobs false), v, st (passes input ([], [])) jobs d⟩
      ⟨some (.head .inner), false, st (passes input input) jobs d⟩ := by
  let S := st (passes input ([], [])) jobs d
  let T := Function.update S (.tape .inner .jobs) input.1
  have h₁ : Run prog (2 * input.1.length + 2)
      ⟨some (.copy .jobs false), v, S⟩ ⟨some (.copy .starts false), false, T⟩ :=
    copy_one .jobs S v rfl rfl
  have h₂ : Run prog (2 * input.2.length + 2)
      ⟨some (.copy .starts false), false, T⟩
      ⟨some (.head .inner), false, Function.update T (.tape .inner .starts) input.2⟩ :=
    copy_one .starts T false rfl rfl
  have he : Function.update T (.tape .inner .starts) input.2 = st (passes input input) jobs d := by
    funext k
    cases k with
    | tape p s => cases p <;> cases s <;> rfl
    | _ => rfl
  rw [he] at h₂
  exact (h₁.trans h₂).of_eq (by omega)

private theorem clear_run (p : Pass) (tapes : Pass → Bits) (jobs : Pass → Option Job)
    (d : List Bool) (v : Bool) (j : Job) (n : ℕ) (hj : jobs p = some j) (hb : jobBound j n) :
    RunLe prog (n + 1) ⟨some (.clear p), v, st tapes jobs d⟩
      ⟨some (.head p), false, st tapes (Function.update jobs p none) d⟩ := by
  have hn : (jobFields p).Nodup := by cases p <;> decide
  have h := clean_run (M := prog) (ks := jobFields p) (self := .clear p) (next := .head p)
    rfl hn n v (st tapes jobs d) (by
      intro k hk
      cases p <;> simp only [jobFields, List.mem_cons, List.not_mem_nil, or_false] at hk <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [st, jobBound])
  have hst : (fun k => if k ∈ jobFields p then [] else st tapes jobs d [] k) =
      st tapes (Function.update jobs p none) d := by
    funext k
    cases k with
    | field q s c => cases p <;> cases q <;> cases s <;> cases c <;> rfl
    | tape q s => cases p <;> rfl
    | _ => cases p <;> rfl
  rwa [hst] at h

private theorem bad_rows {x w : List Bool}
    (hx : x ≠ []) (hw : w ≠ []) (h : readPair (x, w) = none) :
    decodeRows x = none ∨ decodeRows w = none := by
  rcases readPair_bad h with h | h
  · exact Or.inl (decodeRows_failed hx h)
  · exact Or.inr (decodeRows_failed hw h)

private theorem loop_cost {k x r cost : ℕ} (hr : r < x) (hc : cost ≤ k) :
    cost + k * (r + 1) ≤ k * (x + 1) := by
  calc
    _ ≤ k + k * (r + 1) := Nat.add_le_add_right hc _
    _ = k * ((r + 1) + 1) := by
      simp only [Nat.mul_add, Nat.mul_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    _ ≤ _ := Nat.mul_le_mul_left k (by omega)

-- Each iteration consumes a row and performs a bounded number of linear-time operations.
private theorem inner_run (outer : Bits) (input : Bits) (a : Job) (d : List Bool)
    (n : ℕ) (hx : input.1.length ≤ n) (hw : input.2.length ≤ n) (ha : jobBound a n) (v : Bool) :
    let jobs := passes (some a) none
    ∃ v' T, RunLe prog (100 * (n + 1) * (input.1.length + 1))
      ⟨some (.head .inner), v, st (passes outer input) jobs d⟩
      ⟨some (if innerCheck a input then .clear .outer else .no), v', T⟩ ∧
      (innerCheck a input = true → T = st (passes outer ([], [])) jobs d) := by
  intro jobs
  induction hlen : input.1.length using Nat.strong_induction_on generalizing input v
    with | ind m ih => ?_
  rcases input with ⟨x, w⟩
  change x.length ≤ n at hx
  change w.length ≤ n at hw
  subst m
  let tapes := passes outer (x, w)
  let S := st tapes jobs d
  have hhead := (head_run .inner tapes jobs d v).le le_rfl
  have hcost : 1 ≤ 100 * (n + 1) * (x.length + 1) :=
    Nat.succ_le_of_lt (Nat.mul_pos (by positivity) (Nat.succ_pos _))
  by_cases hX : x = []
  · by_cases hW : w = []
    · subst x
      subst w
      refine ⟨true, S, ?_, fun _ => rfl⟩
      simpa [S, tapes, emptyEnd, innerCheck, show decodeRows [] = some [] from rfl]
        using hhead.mono hcost
    · have he := (check_uneven_rows (x := x) (w := w) (d := 0) (a := a) (Or.inl ⟨hX, hW⟩)).2
      refine ⟨false, S, ?_, by simp [he]⟩
      rw [he]
      simpa [S, tapes, hX, hW, List.isEmpty_eq_false_iff.mpr hW] using hhead.mono hcost
  · by_cases hW : w = []
    · have he := (check_uneven_rows (x := x) (w := w) (d := 0) (a := a) (Or.inr ⟨hX, hW⟩)).2
      refine ⟨true, S, ?_, by simp [he]⟩
      rw [he]
      simpa [S, tapes, hX, hW] using hhead.mono hcost
    have hh : RunLe prog 1 ⟨some (.head .inner), v, S⟩
        ⟨some (.read .inner .jobs firstRead), false, S⟩ := by
      simpa [S, tapes, hX, hW, List.isEmpty_eq_false_iff.mpr hW] using hhead
    obtain ⟨v₁, U, hread, hU⟩ := readPair_run tapes jobs d .inner false rfl
    change RunLe prog (10 * (x.length + w.length) + 28) _ _ at hread
    change ∀ b rest, readPair (x, w) = some (b, rest) → _ at hU
    have hconst : 100 * (n + 1) ≤ 100 * (n + 1) * (x.length + 1) := by
      simp
    cases h : readPair (x, w) with
    | none =>
      have he := (check_no_rows (d := 0) (a := a) (bad_rows hX hW h)).2
      have hr : RunLe prog (10 * (x.length + w.length) + 28)
          ⟨some (.read .inner .jobs firstRead), false, S⟩ ⟨some .no, v₁, U⟩ := by
        simpa [S, tapes, h] using hread
      exact ⟨v₁, U, by simpa [he] using (hh.trans hr).mono (by omega), by simp [he]⟩
    | some result =>
      obtain ⟨b, rest⟩ := result
      obtain ⟨hrx, hrw, hb⟩ := readPair_bounds h hx hw
      obtain ⟨hbx, hbw⟩ := readPair_fields h
      obtain ⟨r, s⟩ := rest
      change r.length < x.length at hrx
      change s.length < w.length at hrw
      have he := innerCheck_step (a := a) hbx hbw
      have hUb : U = st (passes outer (r, s)) (passes (some a) (some b)) d := by
        simpa [tapes, jobs] using hU b (r, s) h
      have hr : RunLe prog (10 * (x.length + w.length) + 28)
          ⟨some (.read .inner .jobs firstRead), false, S⟩
          ⟨some (checkEach .inner), v₁, st (passes outer (r, s)) (passes (some a) (some b)) d⟩ := by
        simpa [S, tapes, h, hUb] using hread
      obtain ⟨v₂, hcheck⟩ := pair_run (passes outer (r, s)) (passes (some a) (some b))
        d n a b rfl rfl ha hb v₁
      cases hp : pairCheck a b with
      | false =>
        exact ⟨v₂, _, by simpa [he, hp] using ((hh.trans hr).trans hcheck).mono (by omega),
          by simp [he, hp]⟩
      | true =>
        have hclear := clear_run .inner (passes outer (r, s)) (passes (some a) (some b))
          d v₂ b n rfl hb
        simp only [hp, ite_true] at hcheck
        have htail := (((hh.trans hr).trans hcheck).trans hclear)
        simp only [passes_update_inner] at htail
        obtain ⟨v₃, T, hloop, hT⟩ := ih r.length hrx (r, s)
          (hrx.le.trans hx) (hrw.le.trans hw) false rfl
        have htotal := (htail.trans hloop).mono (loop_cost (show r.length < x.length from hrx)
          (show 1 + (10 * (x.length + w.length) + 28) + (36 * n + 24) + (n + 1) ≤
            100 * (n + 1) by omega))
        exact ⟨v₃, T, by simpa [he, hp] using htotal, fun h => hT (by simpa [he, hp] using h)⟩

-- An outer iteration may run a full inner scan before proceeding with the next job.
private theorem outer_run (input : Bits) (d n : ℕ)
    (hx : input.1.length ≤ n) (hw : input.2.length ≤ n) (hd : (encodeNat d).length ≤ n) (v : Bool) :
    ∃ v' T, RunLe prog (200 * (n + 1)^2 * (input.1.length + 1))
      ⟨some (.head .outer), v, st (passes input ([], [])) (passes none none) (encodeNat d)⟩
      ⟨some (if outerCheck d input then .yes else .no), v', T⟩ := by
  induction hlen : input.1.length using Nat.strong_induction_on generalizing input v
    with | ind m ih => ?_
  rcases input with ⟨x, w⟩
  change x.length ≤ n at hx
  change w.length ≤ n at hw
  subst m
  let tapes := passes (x, w) ([], [])
  let jobs : Pass → Option Job := passes none none
  let d' := encodeNat d
  let S := st tapes jobs d'
  have hhead := (head_run .outer tapes jobs d' v).le le_rfl
  have hsquare : n + 1 ≤ (n + 1)^2 := by
    rw [pow_two]
    simp
  have hconst : 200 * (n + 1)^2 ≤ 200 * (n + 1)^2 * (x.length + 1) := by
    simp
  have hcost : 1 ≤ 200 * (n + 1)^2 * (x.length + 1) :=
    Nat.succ_le_of_lt (Nat.mul_pos (by positivity) (Nat.succ_pos _))
  by_cases hX : x = []
  · by_cases hW : w = []
    · subst x
      subst w
      refine ⟨true, S, ?_⟩
      simpa [S, tapes, emptyEnd, outerCheck, separated, show decodeRows [] = some [] from rfl]
        using hhead.mono hcost
    · have he := (check_uneven_rows (x := x) (w := w) (d := d)
        (a := ((0, 0, 0), (0, 0, 0))) (Or.inl ⟨hX, hW⟩)).1
      refine ⟨false, S, ?_⟩
      rw [he]
      simpa [S, tapes, hX, hW, List.isEmpty_eq_false_iff.mpr hW] using hhead.mono hcost
  · by_cases hW : w = []
    · have he := (check_uneven_rows (x := x) (w := w) (d := d)
        (a := ((0, 0, 0), (0, 0, 0))) (Or.inr ⟨hX, hW⟩)).1
      refine ⟨true, S, ?_⟩
      rw [he]
      simpa [S, tapes, hX, hW] using hhead.mono hcost
    have hh : RunLe prog 1 ⟨some (.head .outer), v, S⟩
        ⟨some (.read .outer .jobs firstRead), false, S⟩ := by
      simpa [S, tapes, hX, hW, List.isEmpty_eq_false_iff.mpr hW] using hhead
    obtain ⟨v₁, U, hread, hU⟩ := readPair_run tapes jobs d' .outer false rfl
    change RunLe prog (10 * (x.length + w.length) + 28) _ _ at hread
    change ∀ a rest, readPair (x, w) = some (a, rest) → _ at hU
    cases h : readPair (x, w) with
    | none =>
      have he := (check_no_rows (d := d) (a := ((0, 0, 0), (0, 0, 0))) (bad_rows hX hW h)).1
      have hr : RunLe prog (10 * (x.length + w.length) + 28)
          ⟨some (.read .outer .jobs firstRead), false, S⟩ ⟨some .no, v₁, U⟩ := by
        simpa [S, tapes, h] using hread
      exact ⟨v₁, U, by simpa [he] using (hh.trans hr).mono (by omega)⟩
    | some result =>
      obtain ⟨a, rest⟩ := result
      obtain ⟨hrx, hrw, ha⟩ := readPair_bounds h hx hw
      obtain ⟨hax, haw⟩ := readPair_fields h
      obtain ⟨r, s⟩ := rest
      change r.length < x.length at hrx
      change s.length < w.length at hrw
      have he := outerCheck_step (d := d) hax haw
      let updated := st (passes (r, s) ([], [])) (passes (some a) none) d'
      have hUa : U = updated := by simpa [updated, tapes, jobs] using hU a (r, s) h
      have hr : RunLe prog (10 * (x.length + w.length) + 28)
          ⟨some (.read .outer .jobs firstRead), false, S⟩
          ⟨some (checkEach .outer), v₁, updated⟩ := by
        simpa [S, tapes, h, hUa] using hread
      obtain ⟨v₂, hl⟩ := local_run (passes (r, s) ([], [])) (passes (some a) none)
        d n a rfl ha hd v₁
      cases hp : localCheck d a with
      | false =>
        exact ⟨v₂, _, by simpa [he, hp] using ((hh.trans hr).trans hl).mono (by omega)⟩
      | true =>
        have hl' : RunLe prog (18 * n + 12) ⟨some (checkEach .outer), v₁, updated⟩
            ⟨some (.copy .jobs false), v₂, updated⟩ := by simpa [hp, updated, d'] using hl
        have hcopy : RunLe prog (2 * (r.length + s.length) + 4) _ _ :=
          (copy_pair (r, s) (passes (some a) none) d' v₂).le le_rfl
        have hin₀ := (((hh.trans hr).trans hl').trans hcopy)
        have hx' : r.length ≤ n := by omega
        have hw' : s.length ≤ n := by omega
        obtain ⟨v₃, T, hin, hT⟩ := inner_run (r, s) (r, s) a d' n hx' hw' ha false
        have hinnerBound : 100 * (n + 1) * (r.length + 1) ≤ 100 * (n + 1)^2 := by
          rw [pow_two, ← Nat.mul_assoc]
          exact Nat.mul_le_mul_left _ (by omega)
        have hin' := hin.mono hinnerBound
        cases hi : innerCheck a (r, s) with
        | false =>
          simp only [hi, Bool.false_eq_true, ite_false] at hin'
          exact ⟨v₃, T, by simpa [he, hp, hi] using (hin₀.trans hin').mono (by omega)⟩
        | true =>
          have ht := hT hi
          simp only [hi, ite_true, ht] at hin'
          have hc := clear_run .outer (passes (r, s) ([], [])) (passes (some a) none)
            d' v₃ a n rfl ha
          have hpart := ((hin₀.trans hin').trans hc)
          simp only [passes_update_outer] at hpart
          obtain ⟨v₄, V, hloop⟩ := ih r.length hrx (r, s) hx' hw' false rfl
          have htotal := (hpart.trans hloop).mono (loop_cost (show r.length < x.length from hrx)
            (show 1 + (10 * (x.length + w.length) + 28) + (18 * n + 12) +
              (2 * (r.length + s.length) + 4) + 100 * (n + 1)^2 + (n + 1) ≤
              200 * (n + 1)^2 by omega))
          exact ⟨v₄, V, by simpa [he, hp, hi] using htotal⟩

private theorem decode_product {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (x : List Bool) : bitDecode (α := α × β) x =
      match undelimit x with
      | none => none
      | some (p, r) => match bitDecode (α := α) p, bitDecode (α := β) r with
        | some a, some b => some (a, b)
        | _, _ => none := rfl

private theorem check_frame (x w : List Bool) :
    flowShopCheck x w = match undelimit x with
      | none => false
      | some (p, r) => outerCheck (decodeNat r) (p, w) := by
  have hdecode : bitDecode (α := FlowShopInstance) x =
      (match undelimit x with
      | none => none
      | some (p, r) => (bitDecode (α := List (List ℕ)) p).map (·, decodeNat r)) := by
    rw [decode_product]
    cases undelimit x with
    | none => rfl
    | some pr =>
      obtain ⟨p, r⟩ := pr
      have hn : bitDecode (α := ℕ) r = some (decodeNat r) := rfl
      simp only [hn]
      cases bitDecode (α := List (List ℕ)) p <;> rfl
  rw [flowShopCheck, hdecode]
  cases hx : undelimit x with
  | none => rfl
  | some pr =>
    obtain ⟨p, r⟩ := pr
    simp only [outerCheck_correct]
    cases bitDecode (α := List (List ℕ)) p <;> cases bitDecode (α := List (List ℕ)) w <;> rfl

private theorem run (x w : List Bool) :
    let n := x.length + w.length
    ∃ v T, RunLe prog (206 * (n + 1)^3)
      ⟨some (.split .read), false, update (update (fun _ => []) K.raw x) (.tape .outer .starts) w⟩
      ⟨some (if flowShopCheck x w then .yes else .no), v, T⟩ := by
  intro n
  let jobs : Pass → Option Job := passes none none
  let S := st (passes ([], w) ([], [])) jobs [] x
  have hS : S = update (update (fun _ => []) K.raw x) (.tape .outer .starts) w := by
    funext k
    cases k with
    | tape p s => cases p <;> cases s <;> rfl
    | field p s c => cases p <;> rfl
    | _ => rfl
  rw [← hS, check_frame]
  obtain ⟨v₁, U, hsplit, hU⟩ := split_run topSplit splitLabel split_embeds S false rfl rfl
  change RunLe prog (x.length + 1) _ _ at hsplit
  change ∀ p r, undelimit x = some (p, r) → _ at hU
  have hn : x.length ≤ n := Nat.le_add_right _ _
  have hw : w.length ≤ n := Nat.le_add_left _ _
  have hsq : n + 1 ≤ (n + 1)^2 := by
    rw [pow_two]
    simp
  have hcube : n + 1 ≤ (n + 1)^3 := by
    rw [pow_succ]
    exact le_trans hsq (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  cases h : undelimit x with
  | none =>
    refine ⟨v₁, U, ?_⟩
    have hh : RunLe prog (x.length + 1) ⟨some (.split .read), false, S⟩ ⟨some .no, v₁, U⟩ := by
      have hh := hsplit
      change RunLe prog (x.length + 1) _ ⟨some (splitLabel (if (undelimit x).isSome then
        .good else .bad)), v₁, U⟩ at hh
      simpa [h, splitLabel] using hh
    exact hh.mono (by omega)
  | some pr =>
    obtain ⟨p, r⟩ := pr
    let S₁ := st (passes (p, w) ([], [])) jobs [] r
    have hU' : U = S₁ := by
      rw [hU p r h]
      funext k
      cases k with
      | tape p s => cases p <;> cases s <;> rfl
      | field p s c => cases p <;> rfl
      | _ => rfl
    have hh : RunLe prog (x.length + 1) ⟨some (.split .read), false, S⟩
        ⟨some (.norm (.read none)), v₁, S₁⟩ := by
      have hh := hsplit
      change RunLe prog (x.length + 1) _ ⟨some (splitLabel (if (undelimit x).isSome then
        .good else .bad)), v₁, U⟩ at hh
      simpa [h, splitLabel, hU'] using hh
    obtain ⟨v₂, hnorm⟩ := norm_run topNorm normLabel norm_embeds S₁ v₁ rfl rfl
    let S₂ := st (passes (p, w) ([], [])) jobs (encodeNat (decodeNat r))
    have hS₂ : update (update S₁ topNorm.input []) topNorm.output (normalizeNat r) = S₂ := by
      rw [normalizeNat_eq_encode_decode]
      funext k
      cases k with
      | tape p s => cases p <;> cases s <;> rfl
      | field p s c => cases p <;> rfl
      | _ => rfl
    have hnorm' : RunLe prog (2 * r.length + 3) ⟨some (.norm (.read none)), v₁, S₁⟩
        ⟨some (.head .outer), v₂, S₂⟩ := by
      rw [← hS₂]
      exact hnorm
    obtain ⟨hp, hr⟩ := frame_sizes h
    have hdr : (encodeNat (decodeNat r)).length ≤ n := by
      rw [← normalizeNat_eq_encode_decode]
      exact (length_normalizeNat_le r).trans (by omega)
    have hp' : p.length ≤ n := by omega
    obtain ⟨v₃, T, hout⟩ := outer_run (p, w) (decodeNat r) n hp' hw hdr v₂
    have hproduct : 200 * (n + 1)^2 * (p.length + 1) ≤ 200 * (n + 1)^3 := by
      rw [show (n + 1)^3 = (n + 1)^2 * (n + 1) from pow_succ _ _, ← Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ (by omega)
    exact ⟨v₃, T, ((hh.trans hnorm').trans hout).mono (by change
      x.length + 1 + (2 * r.length + 3) + 200 * (n + 1)^2 * (p.length + 1) ≤ _; omega)⟩

private def keys : List K :=
  [.tape .outer .jobs, .tape .outer .starts, .tape .inner .jobs, .tape .inner .starts] ++
    jobFields .outer ++ jobFields .inner ++
    [.row, .payload, .splitTemp, .normTemp, .raw, .deadline, .copyTemp,
      .compareA, .compareB, .compareC]

private theorem mem_keys (k : K) : k ∈ keys := by
  cases k with
  | tape p s => cases p <;> cases s <;> decide
  | field p s c => cases p <;> cases s <;> cases c <;> decide
  | _ => decide

private instance fintypeK : Fintype K := Fintype.ofList keys mem_keys

private abbrev comp : Cslib.Complexity.Host.Comp where
  K := K
  Γ := fun _ => Bool
  L := Lab
  prog := prog
  ks := keys
  ks_nodup := by decide
  mem_ks := mem_keys

private theorem isPolyTime_check :
    ComplexityTheory.IsPolyTime (fun p : List Bool × List Bool => flowShopCheck p.1 p.2) :=
  Cslib.Complexity.Host.isPolyTime_verifier
    (c := comp) (cX := .raw) (cW := .tape .outer .starts) (gX := id) (gW := id)
    (start := .split .read) (yes := .yes) (no := .no) flowShopCheck
    (Polynomial.C 206 * (Polynomial.X + 1)^3) (by decide) (by decide) rfl rfl
    fun x w => by simpa using run x w

end Verifier

/-- **Three-machine flow-shop scheduling belongs to NP.** Each start time is bounded by the
deadline, so the binary schedule certificate has length polynomial in the instance length.

Source: Direct verification of the start-time certificate with `flowShopCheck`. -/
theorem flowShop_mem_NP : flowShopDec ∈ MetaMathlibExt.ComplexityTheory.NP := by
  refine ⟨Polynomial.X * (Polynomial.C 12 * Polynomial.X + Polynomial.C 7),
    fun p => flowShopCheck p.1 p.2, Verifier.isPolyTime_check, ?_⟩
  intro x
  simpa using check_certificate x

end MetaMathlibExt.Complexity.NPComplete.FlowShop
