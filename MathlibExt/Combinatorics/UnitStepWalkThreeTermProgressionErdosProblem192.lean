/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Three-term progressions in unit-step walks (Erdős Problem 192)

Erdős Problem 192: let `a₁, a₂, …` be an infinite sequence in `ℝ^d` such that each `aᵢ₊₁ - aᵢ` is a
standard unit vector. For which `d` must the sequence contain a three-term arithmetic progression?
-/


module

public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace MathlibExt.Combinatorics.UnitStepWalkThreeTermProgressionErdosProblem192Wanted

@[expose] public section

/-!
Source: T. F. Bloom, Erdős Problems, Problem #192, https://www.erdosproblems.com/192 (status SOLVED
(LEAN)). UnsolvedMath record UM-30006758 (`EP-192`), dataset ulamai/UnsolvedMath v1.8.0.

Points of `ℝ^d` are functions `Fin d → ℝ`, a step is `Pi.single j 1`, and a three-term progression
is `x, y, z` among the points with `x ≠ y` and `x + z = 2 y` (points of the walk are distinct since
the coordinate sum grows by `1` at each step). The answer is stated as an equivalence for every `d`;
for `d = 0` no such walk exists and `0 ≤ 3`. Compared with the formal-conjectures statement
`ErdosProblems/192.lean` (answer `Set.Iic 3`, equivalent; no code imported).
-/

/-- **Unit-step walks.** Let $d$ be a natural number. A sequence
$a_0, a_1, a_2, \dots$ of points of $\mathbb{R}^d$ is a unit-step walk when for every $i$ the
step $a_{i+1} - a_i$ is a standard unit vector $e_j$ of $\mathbb{R}^d$ for some $j$. -/
def IsUnitStepWalk (d : ℕ) (a : ℕ → Fin d → ℝ) : Prop :=
  ∀ i, ∃ j : Fin d, a (i + 1) = a i + Pi.single j 1

/-- **Three-term arithmetic progressions in a sequence of points.** Let $d$ be a natural number
and let $a_0, a_1, a_2, \dots$ be a sequence of points of $\mathbb{R}^d$. The sequence contains a
three-term arithmetic progression when there are indices $i$, $j$, $k$ with $a_i \ne a_j$ and
$a_i + a_k = 2 a_j$. -/
def HasThreeAP {d : ℕ} (a : ℕ → Fin d → ℝ) : Prop :=
  ∃ i j k : ℕ, a i ≠ a j ∧ a i + a k = 2 • a j

/-- **Erdős Problem 192 on three-term progressions in unit-step walks.** The statement that for
every natural number $d$, every sequence $a_0, a_1, a_2, \dots$ of points of $\mathbb{R}^d$ whose
steps $a_{i+1} - a_i$ are all standard unit vectors contains a three-term arithmetic progression
(indices $i$, $j$, $k$ with $a_i \ne a_j$ and $a_i + a_k = 2 a_j$) if and only if $d \le 3$. -/
def unitStepWalkThreeAPIff : Prop :=
  ∀ d : ℕ, (∀ a : ℕ → Fin d → ℝ, IsUnitStepWalk d a → HasThreeAP a) ↔ d ≤ 3

end

private def prefixCount {α : Type*} [DecidableEq α] (w : ℕ → α) (n : ℕ) (c : α) : ℤ :=
  ∑ t ∈ Finset.range n, if w t = c then 1 else 0

private theorem prefixCount_succ {α : Type*} [DecidableEq α]
    (w : ℕ → α) (n : ℕ) (c : α) :
    prefixCount w (n + 1) c = prefixCount w n c + if w n = c then 1 else 0 := by
  simp only [prefixCount, Finset.sum_range_succ]

private theorem prefixCount_split {α : Type*} [DecidableEq α]
    (w : ℕ → α) (i m : ℕ) (c : α) :
    prefixCount w (i + m) c = prefixCount w i c + prefixCount (fun n ↦ w (i + n)) m c := by
  exact Finset.sum_range_add _ _ _

/-- The balance equation for the three prefix counts means the two intervening blocks
have the same number of occurrences of each letter. -/
private def HasAbelianSquare {α : Type*} [DecidableEq α] (w : ℕ → α) : Prop :=
  ∃ i j k : ℕ, i < j ∧ j < k ∧
    ∀ c, prefixCount w i c + prefixCount w k c = 2 * prefixCount w j c

private theorem sum_prefixCount {d : ℕ} (w : ℕ → Fin d) (n : ℕ) :
    ∑ c, prefixCount w n c = (n : ℤ) := by
  unfold prefixCount
  rw [Finset.sum_comm]
  calc
    (∑ t ∈ Finset.range n, ∑ c : Fin d, if w t = c then (1 : ℤ) else 0) =
        ∑ _t ∈ Finset.range n, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro t _
      exact Finset.sum_ite_eq_of_mem _ _ _ (Finset.mem_univ _)
    _ = _ := by simp

private theorem walk_eq {d : ℕ} {a : ℕ → Fin d → ℝ} {w : ℕ → Fin d}
    (hw : ∀ n, a (n + 1) = a n + Pi.single (w n) 1) (n : ℕ) (c : Fin d) :
    a n c = a 0 c + (prefixCount w n c : ℝ) := by
  induction n with
  | zero => simp [prefixCount]
  | succ n ih =>
    rw [hw, Pi.add_apply, ih, prefixCount_succ, Int.cast_add, add_assoc]
    congr 1
    by_cases h : w n = c
    · subst c
      simp
    · simp [h]

private theorem threeAP_iff {d : ℕ} {a : ℕ → Fin d → ℝ} {w : ℕ → Fin d}
    (hw : ∀ n, a (n + 1) = a n + Pi.single (w n) 1) :
    HasThreeAP a ↔ HasAbelianSquare w := by
  have hbalance (i j k : ℕ) : a i + a k = 2 • a j ↔
      ∀ c, prefixCount w i c + prefixCount w k c = 2 * prefixCount w j c := by
    rw [funext_iff]
    apply forall_congr'
    intro c
    rw [two_nsmul, Pi.add_apply, Pi.add_apply, walk_eq hw i c, walk_eq hw j c,
      walk_eq hw k c]
    constructor <;> intro h
    · have he : (prefixCount w i c : ℝ) + (prefixCount w k c : ℝ) =
          2 * (prefixCount w j c : ℝ) := by linarith
      exact_mod_cast he
    · have he : (prefixCount w i c : ℝ) + (prefixCount w k c : ℝ) =
          2 * (prefixCount w j c : ℝ) := by exact_mod_cast h
      linarith
  have hne (i j : ℕ) (h : i ≠ j) : a i ≠ a j := by
    intro e
    apply h
    have hc (c : Fin d) : prefixCount w i c = prefixCount w j c := by
      have he := congrFun e c
      rw [walk_eq hw i c, walk_eq hw j c, add_right_inj] at he
      exact_mod_cast he
    have hs := Finset.sum_congr (s₁ := Finset.univ) rfl fun c _ ↦ hc c
    rw [sum_prefixCount, sum_prefixCount] at hs
    exact_mod_cast hs
  constructor
  · rintro ⟨i, j, k, hne', h⟩
    have hb := (hbalance i j k).mp h
    have hs := Finset.sum_congr (s₁ := Finset.univ) rfl fun c _ ↦ hb c
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_prefixCount, sum_prefixCount,
      sum_prefixCount] at hs
    have hij : i ≠ j := fun e ↦ hne' (congrArg a e)
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact ⟨i, j, k, hlt, by omega, hb⟩
    · exact ⟨k, j, i, by omega, hgt, fun c ↦ by rw [add_comm]; exact hb c⟩
  · rintro ⟨i, j, k, hij, _, hb⟩
    exact ⟨i, j, k, hne i j hij.ne, (hbalance i j k).mpr hb⟩

private def fromWord {d : ℕ} (w : ℕ → Fin d) (n : ℕ) (c : Fin d) : ℝ :=
  prefixCount w n c

private theorem fromWord_step {d : ℕ} (w : ℕ → Fin d) (n : ℕ) :
    fromWord w (n + 1) = fromWord w n + Pi.single (w n) 1 := by
  funext c
  simp only [fromWord, Pi.add_apply, prefixCount_succ, Int.cast_add]
  congr 1
  by_cases h : w n = c
  · subst c
    simp
  · simp [h]

private theorem prefixCount_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (w : ℕ → α) (n : ℕ) (c : α) :
    prefixCount (f ∘ w) n (f c) = prefixCount w n c := by
  simp [prefixCount, hf.eq_iff]

private theorem abelianSquare_of_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    {f : α → β} (hf : Function.Injective f) {w : ℕ → α}
    (h : HasAbelianSquare (f ∘ w)) : HasAbelianSquare w := by
  obtain ⟨i, j, k, hij, hjk, h⟩ := h
  exact ⟨i, j, k, hij, hjk, fun c ↦ by simpa only [prefixCount_map f hf] using h (f c)⟩

private def segment {α : Type*} (w : ℕ → α) (i : ℕ) : ℕ → List α
  | 0 => []
  | n + 1 => w i :: segment w (i + 1) n

private theorem segment_count {α : Type*} [DecidableEq α]
    (w : ℕ → α) (i n m : ℕ) (hm : m ≤ n) (c : α) :
    (((segment w i n).take m).count c : ℤ) = prefixCount (fun t ↦ w (i + t)) m c := by
  induction m generalizing i n with
  | zero => simp [prefixCount]
  | succ m ih =>
    cases n with
    | zero => omega
    | succ n =>
      rw [segment, List.take_succ_cons, List.count_cons, Int.natCast_add,
        ih (i + 1) n (by omega)]
      conv_rhs =>
        rw [Nat.add_comm m 1, prefixCount_split (fun t ↦ w (i + t)) 1 m c]
      have hfirst : prefixCount (fun t ↦ w (i + t)) 1 c = if w i = c then 1 else 0 := by
        rw [show (1 : ℕ) = 0 + 1 by rfl, prefixCount_succ]
        simp [prefixCount]
      rw [hfirst]
      have hf : (fun t ↦ w (i + (1 + t))) = (fun t ↦ w (i + 1 + t)) := by
        funext t
        rw [Nat.add_assoc]
      rw [hf, add_comm (if w i = c then (1 : ℤ) else 0)]
      by_cases h : w i = c <;> simp [h, Ne.symm]

private def headSquare (u : List (Fin 3)) : Bool :=
  (List.range (u.length / 2)).any fun m ↦
    ([0, 1, 2] : List (Fin 3)).all fun c ↦ (u.take (m + 1)).count c ==
      ((u.drop (m + 1)).take (m + 1)).count c

private def ternaryCandidates : ℕ → List (List (Fin 3))
  | 0 => [[]]
  | n + 1 => (ternaryCandidates n).flatMap fun u ↦
    (([0, 1, 2] : List (Fin 3)).map (· :: u)).filter (!headSquare ·)

set_option maxRecDepth 2048 in
private theorem ternaryCandidates_eight : ternaryCandidates 8 = [] := by decide

private theorem segment_length {α : Type*} (w : ℕ → α) (i n : ℕ) :
    (segment w i n).length = n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [segment, ih]

private theorem segment_drop {α : Type*} (w : ℕ → α) (i n m : ℕ) :
    (segment w i n).drop m = segment w (i + m) (n - m) := by
  induction m generalizing i n with
  | zero => rfl
  | succ m ih =>
    cases n with
    | zero => simp [segment]
    | succ n =>
      simpa [segment, Nat.add_right_comm, Nat.add_assoc, Nat.add_comm 1] using ih (i + 1) n

private theorem candidates_of_avoids {w : ℕ → Fin 3} (h : ¬ HasAbelianSquare w) (i n : ℕ) :
    segment w i n ∈ ternaryCandidates n := by
  induction n generalizing i with
  | zero => simp [segment, ternaryCandidates]
  | succ n ih =>
    rw [ternaryCandidates, List.mem_flatMap]
    refine ⟨segment w (i + 1) n, ih _, List.mem_filter.mpr ⟨?_, ?_⟩⟩
    · apply List.mem_map.mpr
      refine ⟨w i, ?_, rfl⟩
      have h' : w i = 0 ∨ w i = 1 ∨ w i = 2 := by omega
      simpa using h'
    · cases he : headSquare (segment w i (n + 1)) with
      | false => rfl
      | true =>
        exfalso
        apply h
        unfold headSquare at he
        obtain ⟨m, hm, hall⟩ := List.any_eq_true.mp he
        have hm' := List.mem_range.mp hm
        rw [segment_length] at hm'
        refine ⟨i, i + (m + 1), i + (m + 1) + (m + 1), by omega, by omega, fun c ↦ ?_⟩
        have hc : c ∈ ([0, 1, 2] : List (Fin 3)) := by
          have h' : c = 0 ∨ c = 1 ∨ c = 2 := by omega
          simpa using h'
        have hc' := beq_iff_eq.mp (List.all_eq_true.mp hall c hc)
        rw [segment_drop] at hc'
        have heq := congrArg (fun x : ℕ ↦ (x : ℤ)) hc'
        rw [segment_count w i _ _ (by omega), segment_count w _ _ _ (by omega)] at heq
        rw [prefixCount_split w (i + (m + 1)), prefixCount_split w i]
        omega

private theorem ternary_hasAbelianSquare (w : ℕ → Fin 3) : HasAbelianSquare w := by
  by_contra h
  have hm := candidates_of_avoids h 0 8
  rw [ternaryCandidates_eight] at hm
  exact List.not_mem_nil hm

private theorem smallDimension {d : ℕ} (hd : d ≤ 3) (a : ℕ → Fin d → ℝ)
    (ha : IsUnitStepWalk d a) : HasThreeAP a := by
  choose w hw using ha
  apply (threeAP_iff hw).mpr
  exact abelianSquare_of_map (f := Fin.castLE hd)
    (fun _ _ h ↦ Fin.ext (congrArg (fun x ↦ x.val) h)) (ternary_hasAbelianSquare _)

private theorem largeDimension_of_word {d : ℕ} (hd : 4 ≤ d) {w : ℕ → Fin 4}
    (hw : ¬ HasAbelianSquare w) : ∃ a : ℕ → Fin d → ℝ, IsUnitStepWalk d a ∧ ¬ HasThreeAP a := by
  let u := Fin.castLE hd ∘ w
  refine ⟨fromWord u, fun n ↦ ⟨u n, fromWord_step u n⟩, fun h ↦ hw ?_⟩
  exact abelianSquare_of_map (f := Fin.castLE hd) (fun _ _ h ↦ Fin.ext (congrArg (fun x ↦ x.val) h))
    ((threeAP_iff (fromWord_step u)).mp h)

/-!
## Keränen's four-letter word

The substitution is from V. Keränen, *Abelian squares are avoidable on 4 letters*, ICALP 1992,
<https://doi.org/10.1007/3-540-55719-9_62>. The four images are also printed in G. Fici and
S. Puzynina, *Abelian combinatorics on words: a survey*, §5, <https://arxiv.org/abs/2207.09937>.

We use the parent-template method of J. D. Currie and N. Rampersad, *Fixed points avoiding Abelian
k-powers*, <https://arxiv.org/abs/1106.1842>, specialized to three marked positions. Instead of a
norm bound on the inverse matrix, we check a finite set closed under taking parents. The only
additional local cases are when two of the three marked positions fall in the same image block.
-/

private def kerDigits : Array (Fin 4) :=
  #[0, 1, 2, 0, 2, 3, 2, 1, 2, 3, 2, 0, 3, 2, 3, 1, 3, 0, 1, 0, 2, 0, 1, 0, 3, 1, 0, 1, 2, 1,
    3, 1, 2, 1, 0, 2, 1, 2, 3, 2, 0, 2, 1, 0, 1, 3, 0, 1, 0, 2, 0, 3, 2, 1, 2, 3, 2, 0, 2, 3,
    1, 2, 1, 0, 2, 1, 2, 3, 2, 0, 2, 3, 2, 1, 3, 2, 3, 0, 3, 1, 3, 2, 1, 2, 0]

private def kerLetter (a : Fin 4) (r : ℕ) : Fin 4 := kerDigits[r]! + a

private def substitute (w : ℕ → Fin 4) (n : ℕ) : Fin 4 := kerLetter (w (n / 85)) (n % 85)

private theorem substitute_at (w : ℕ → Fin 4) (q r : ℕ) (hr : r < 85) :
    substitute w (85 * q + r) = kerLetter (w q) r := by
  unfold substitute
  rw [show (85 * q + r) / 85 = q by omega, show (85 * q + r) % 85 = r by omega]

private def kerWord (n : ℕ) : Fin 4 :=
  if h : n = 0 then 0 else kerLetter (kerWord (n / 85)) (n % 85)
termination_by n
decreasing_by omega

private theorem kerWord_fixed : substitute kerWord = kerWord := by
  funext n
  by_cases h : n = 0
  · subst n
    have h0 : kerWord 0 = 0 := by rw [kerWord, dite_eq_left rfl]
    change kerLetter (kerWord 0) 0 = kerWord 0
    rw [h0]
    rfl
  · conv_rhs => rw [kerWord, dite_eq_right h]
    rfl

private theorem kerLetter_first (a : Fin 4) : kerLetter a 0 = a := by
  change 0 + a = a
  exact Fin.zero_add a

private theorem kerLetter_last (a : Fin 4) : kerLetter a 84 = a := by
  change 0 + a = a
  exact Fin.zero_add a

private theorem kerLetter_adjacent (a : Fin 4) (r : Fin 84) :
    kerLetter a r.val ≠ kerLetter a (r.val + 1) := by
  have h : ∀ (a : Fin 4) (r : Fin 84),
      kerLetter a r.val ≠ kerLetter a (r.val + 1) := by decide +kernel
  exact h a r

private theorem kerWord_adjacent (n : ℕ) : kerWord n ≠ kerWord (n + 1) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    let q := n / 85
    let r := n % 85
    have hn : n = 85 * q + r := by dsimp [q, r]; omega
    have hr : r < 85 := Nat.mod_lt _ (by decide)
    rw [← kerWord_fixed, hn, substitute_at _ q r hr]
    by_cases h : r < 84
    · rw [Nat.add_assoc, substitute_at _ q (r + 1) (by omega)]
      exact kerLetter_adjacent _ ⟨r, h⟩
    · have hh : r = 84 := by omega
      rw [hh, show 85 * q + 84 + 1 = 85 * (q + 1) + 0 by omega,
        substitute_at _ (q + 1) 0 (by decide), kerLetter_last, kerLetter_first]
      apply ih q
      dsimp [q] at *
      omega

private structure Counts where
  x0 : ℤ
  x1 : ℤ
  x2 : ℤ
  x3 : ℤ
  deriving DecidableEq

private instance : Inhabited Counts := ⟨⟨0, 0, 0, 0⟩⟩

private def Counts.get (v : Counts) (c : Fin 4) : ℤ :=
  match c.val with
  | 0 => v.x0
  | 1 => v.x1
  | 2 => v.x2
  | _ => v.x3

private def Counts.ofFn (f : Fin 4 → ℤ) : Counts := ⟨f 0, f 1, f 2, f 3⟩

@[simp] private theorem Counts.get_ofFn (f : Fin 4 → ℤ) (c : Fin 4) :
    (Counts.ofFn f).get c = f c := by fin_cases c <;> rfl

private theorem Counts.eq_of_get {v u : Counts} (h : ∀ c, v.get c = u.get c) : v = u := by
  cases v
  cases u
  congr
  · exact h 0
  · exact h 1
  · exact h 2
  · exact h 3

private def Counts.zero : Counts := ⟨0, 0, 0, 0⟩

@[simp] private theorem Counts.get_zero (c : Fin 4) : Counts.zero.get c = 0 := by
  fin_cases c <;> rfl

private def Counts.total (v : Counts) : ℤ := v.x0 + v.x1 + v.x2 + v.x3

private theorem Counts.total_eq (v : Counts) : v.total = ∑ c, v.get c := by
  rw [Fin.sum_univ_four]
  rfl

private def Counts.letter (a : Fin 4) (sign : ℤ) : Counts :=
  Counts.ofFn fun c ↦ if a = c then sign else 0

private def Counts.rem (v : Counts) (m : ℤ) : Counts :=
  Counts.ofFn fun c ↦ v.get c % m

private def Counts.quot (v : Counts) (m : ℤ) : Counts :=
  Counts.ofFn fun c ↦ v.get c / m

private def coefficient (c a : Fin 4) : ℤ :=
  (#[-701, -531, 4059, -2316] : Array ℤ)[(a - c).val]!

private def transformed (v : Counts) : Counts :=
  Counts.ofFn fun c ↦ coefficient c 0 * v.x0 + coefficient c 1 * v.x1 +
    coefficient c 2 * v.x2 + coefficient c 3 * v.x3

private theorem transformed_get (v : Counts) (c : Fin 4) :
    (transformed v).get c = ∑ a, coefficient c a * v.get a := by
  rw [Fin.sum_univ_four, transformed, Counts.get_ofFn]
  rfl

private def weighted (w : ℕ → Fin 4) (n : ℕ) (c : Fin 4) : ℤ :=
  ∑ t ∈ Finset.range n, coefficient c (w t)

private theorem weighted_eq (w : ℕ → Fin 4) (n : ℕ) (c : Fin 4) :
    weighted w n c = ∑ a, coefficient c a * prefixCount w n a := by
  symm
  simp only [prefixCount, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  simp only [mul_ite, mul_one, mul_zero]
  exact Finset.sum_ite_eq_of_mem _ _ _ (Finset.mem_univ _)

private theorem weighted_split (w : ℕ → Fin 4) (i m : ℕ) (c : Fin 4) :
    weighted w (i + m) c = weighted w i c + weighted (fun n ↦ w (i + n)) m c := by
  exact Finset.sum_range_add _ _ _

private theorem weighted_substitute_block (w : ℕ → Fin 4) (q r : ℕ) (c : Fin 4) (hr : r ≤ 85) :
    weighted (fun t ↦ substitute w (85 * q + t)) r c = weighted (kerLetter (w q)) r c := by
  unfold weighted
  exact Finset.sum_congr rfl fun t ht ↦ congrArg _ (substitute_at w q t (by
    have := Finset.mem_range.mp ht
    omega))

-- Each inverse row gives 43435 on the corresponding image and 0 on the other images.
private theorem weighted_full (a c : Fin 4) :
    weighted (kerLetter a) 85 c = if a = c then 43435 else 0 := by
  have h : ∀ a c : Fin 4, weighted (kerLetter a) 85 c = if a = c then 43435 else 0 := by
    decide +kernel
  exact h a c

private theorem weighted_substitute (w : ℕ → Fin 4) (q r : ℕ) (c : Fin 4) (hr : r ≤ 85) :
    weighted (substitute w) (85 * q + r) c =
      43435 * prefixCount w q c + weighted (kerLetter (w q)) r c := by
  rw [weighted_split, weighted_substitute_block w q r c hr]
  congr 1
  induction q with
  | zero => simp [weighted, prefixCount]
  | succ q ih =>
    rw [show 85 * (q + 1) = 85 * q + 85 by omega, weighted_split,
      weighted_substitute_block w q 85 c le_rfl, weighted_full, ih, prefixCount_succ, mul_add]
    split <;> simp_all

private def imbalance (w : ℕ → Fin 4) (i j k : ℕ) : Counts :=
  Counts.ofFn fun c ↦ prefixCount w i c + prefixCount w k c - 2 * prefixCount w j c

private theorem imbalance_total (w : ℕ → Fin 4) (i j k : ℕ) :
    (imbalance w i j k).total = (i : ℤ) + k - 2 * j := by
  simp only [Counts.total_eq, imbalance, Counts.get_ofFn, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, sum_prefixCount]

private theorem transformed_imbalance (w : ℕ → Fin 4) (i j k : ℕ) (c : Fin 4) :
    (transformed (imbalance w i j k)).get c =
      weighted w i c + weighted w k c - 2 * weighted w j c := by
  simp only [transformed_get, imbalance, Counts.get_ofFn, weighted_eq, mul_sub, mul_add,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, mul_left_comm]

private theorem imbalance_left_repeat (w : ℕ → Fin 4) (i : ℕ) :
    imbalance w i i (i + 1) = Counts.letter (w i) 1 := by
  apply Counts.eq_of_get
  intro c
  simp only [imbalance, Counts.letter, Counts.get_ofFn, prefixCount_succ]
  split <;> omega

private theorem imbalance_right_repeat (w : ℕ → Fin 4) (i : ℕ) :
    imbalance w i (i + 1) (i + 1) = Counts.letter (w i) (-1) := by
  apply Counts.eq_of_get
  intro c
  simp only [imbalance, Counts.letter, Counts.get_ofFn, prefixCount_succ]
  split <;> omega

private structure Template where
  a : Fin 4
  b : Fin 4
  c : Fin 4
  delta : Counts
  deriving DecidableEq

private def templateAt (w : ℕ → Fin 4) (i j k : ℕ) : Template :=
  ⟨w i, w j, w k, imbalance w i j k⟩

private def Counts.rotate (v : Counts) (a : Fin 4) : Counts :=
  Counts.ofFn fun c ↦ v.get (c - a)

private def Template.normalized (t : Template) : Template :=
  ⟨0, t.b - t.a, t.c - t.a, t.delta.rotate (-t.a)⟩

private def Template.rotate (t : Template) (a : Fin 4) : Template :=
  ⟨t.a + a, t.b + a, t.c + a, t.delta.rotate a⟩

private def finiteRoots : List Template :=
  (List.finRange 4).flatMap fun b ↦ (List.finRange 4).map fun c ↦ ⟨0, b, c, Counts.zero⟩

-- The nonzero normalized parents of the square templates. Correctness does not depend on
-- how this table was found: the checker below independently verifies closure of the whole set.
private def finiteParents : List Template :=
  [
    ⟨0, 0, 0, ⟨-1, 0, 0, 0⟩⟩,
    ⟨0, 0, 0, ⟨1, 0, 0, 0⟩⟩,
    ⟨0, 0, 1, ⟨1, -1, 0, 0⟩⟩,
    ⟨0, 0, 2, ⟨-1, 0, 0, 0⟩⟩,
    ⟨0, 0, 2, ⟨1, 0, -1, 0⟩⟩,
    ⟨0, 0, 3, ⟨1, 0, 0, -1⟩⟩,
    ⟨0, 0, 3, ⟨2, 0, 0, -1⟩⟩,
    ⟨0, 1, 0, ⟨-2, 2, 0, 0⟩⟩,
    ⟨0, 1, 0, ⟨-1, 0, 0, 0⟩⟩,
    ⟨0, 1, 0, ⟨-1, 2, 0, 0⟩⟩,
    ⟨0, 1, 1, ⟨-1, 1, 0, 0⟩⟩,
    ⟨0, 1, 1, ⟨-1, 2, 0, 0⟩⟩,
    ⟨0, 1, 2, ⟨-1, 2, -1, 0⟩⟩,
    ⟨0, 1, 2, ⟨-1, 2, 0, 0⟩⟩,
    ⟨0, 1, 2, ⟨0, 0, -1, 0⟩⟩,
    ⟨0, 1, 2, ⟨0, 2, -1, 0⟩⟩,
    ⟨0, 1, 3, ⟨-1, 0, 0, 0⟩⟩,
    ⟨0, 1, 3, ⟨-1, 2, 0, -1⟩⟩,
    ⟨0, 1, 3, ⟨0, 2, 0, -1⟩⟩,
    ⟨0, 2, 0, ⟨-2, 0, 2, 0⟩⟩,
    ⟨0, 2, 0, ⟨-1, 0, 0, 0⟩⟩,
    ⟨0, 2, 0, ⟨-1, 0, 2, 0⟩⟩,
    ⟨0, 2, 1, ⟨-1, -1, 2, 0⟩⟩,
    ⟨0, 2, 1, ⟨-1, 0, 2, 0⟩⟩,
    ⟨0, 2, 1, ⟨0, -1, 0, 0⟩⟩,
    ⟨0, 2, 2, ⟨-1, 0, 1, 0⟩⟩,
    ⟨0, 2, 2, ⟨0, 0, -1, 0⟩⟩,
    ⟨0, 2, 3, ⟨-1, 0, 2, -1⟩⟩,
    ⟨0, 2, 3, ⟨-1, 0, 2, 0⟩⟩,
    ⟨0, 2, 3, ⟨0, 0, 0, -1⟩⟩,
    ⟨0, 2, 3, ⟨0, 0, 2, -1⟩⟩,
    ⟨0, 3, 0, ⟨-2, 0, 0, 2⟩⟩,
    ⟨0, 3, 0, ⟨-1, 0, 0, 0⟩⟩,
    ⟨0, 3, 0, ⟨-1, 0, 0, 2⟩⟩,
    ⟨0, 3, 1, ⟨-1, -1, 0, 2⟩⟩,
    ⟨0, 3, 1, ⟨-1, 0, 0, 0⟩⟩,
    ⟨0, 3, 1, ⟨-1, 0, 0, 2⟩⟩,
    ⟨0, 3, 1, ⟨0, -1, 0, 2⟩⟩,
    ⟨0, 3, 2, ⟨-1, 0, -1, 2⟩⟩,
    ⟨0, 3, 2, ⟨-1, 0, 0, 0⟩⟩,
    ⟨0, 3, 2, ⟨-1, 0, 0, 2⟩⟩,
    ⟨0, 3, 2, ⟨0, 0, -1, 2⟩⟩,
    ⟨0, 3, 3, ⟨-1, 0, 0, 1⟩⟩
  ]

private def finiteTemplates : List Template := finiteRoots ++ finiteParents

private def accepted (t : Template) : Prop := t.normalized ∈ finiteTemplates

private instance (t : Template) : Decidable (accepted t) :=
  inferInstanceAs (Decidable (t.normalized ∈ finiteTemplates))

private theorem root_accepted (a b c : Fin 4) : accepted ⟨a, b, c, Counts.zero⟩ := by
  have hz : Counts.zero.rotate (-a) = Counts.zero := by
    apply Counts.eq_of_get
    simp [Counts.rotate]
  unfold accepted Template.normalized finiteTemplates
  rw [hz]
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨b - a, List.mem_finRange _, List.mem_map.mpr
    ⟨c - a, List.mem_finRange _, rfl⟩⟩

-- Weighted prefix counts of the base image. This table only speeds up the checker;
-- `baseWeight_correct` verifies it against `kerDigits`.
private def baseWeights : Array (Array Counts) :=
  #[
    #[⟨0, 0, 0, 0⟩, ⟨-701, -2316, 4059, -531⟩,
      ⟨-1232, -3017, 1743, 3528⟩, ⟨2827, -3548, 1042, 1212⟩,
      ⟨2126, -5864, 5101, 681⟩, ⟨6185, -6395, 4400, -1635⟩,
      ⟨3869, -2336, 3869, -2336⟩, ⟨7928, -2867, 3168, -4652⟩,
      ⟨7397, -3568, 852, -593⟩, ⟨11456, -4099, 151, -2909⟩],
    #[⟨9140, -40, -380, -3610⟩, ⟨13199, -571, -1081, -5926⟩,
      ⟨12498, -2887, 2978, -6457⟩, ⟨10182, 1172, 2447, -7158⟩,
      ⟨14241, 641, 1746, -9474⟩, ⟨11925, 4700, 1215, -10175⟩,
      ⟨11394, 3999, -1101, -6116⟩, ⟨9078, 8058, -1632, -6817⟩,
      ⟨8377, 5742, 2427, -7348⟩, ⟨7846, 5041, 111, -3289⟩],
    #[⟨7145, 2725, 4170, -3820⟩, ⟨11204, 2194, 3469, -6136⟩,
      ⟨10503, -122, 7528, -6667⟩, ⟨9972, -823, 5212, -2608⟩,
      ⟨9271, -3139, 9271, -3139⟩, ⟨6955, 920, 8740, -3840⟩,
      ⟨6424, 219, 6424, 219⟩, ⟨5723, -2097, 10483, -312⟩,
      ⟨5192, -2798, 8167, 3747⟩, ⟨9251, -3329, 7466, 1431⟩],
    #[⟨8720, -4030, 5150, 5490⟩, ⟨6404, 29, 4619, 4789⟩,
      ⟨5873, -672, 2303, 8848⟩, ⟨9932, -1203, 1602, 6532⟩,
      ⟨9401, -1904, -714, 10591⟩, ⟨8700, -4220, 3345, 10060⟩,
      ⟨12759, -4751, 2644, 7744⟩, ⟨12228, -5452, 328, 11803⟩,
      ⟨16287, -5983, -373, 9487⟩, ⟨13971, -1924, -904, 8786⟩],
    #[⟨18030, -2455, -1605, 6470⟩, ⟨17329, -4771, 2454, 5939⟩,
      ⟨21388, -5302, 1753, 3623⟩, ⟨20857, -6003, -563, 7682⟩,
      ⟨20156, -8319, 3496, 7151⟩, ⟨19625, -9020, 1180, 11210⟩,
      ⟨17309, -4961, 649, 10509⟩, ⟨16608, -7277, 4708, 9978⟩,
      ⟨16077, -7978, 2392, 14037⟩, ⟨15376, -10294, 6451, 13506⟩],
    #[⟨19435, -10825, 5750, 11190⟩, ⟨18734, -13141, 9809, 10659⟩,
      ⟨16418, -9082, 9278, 9958⟩, ⟨20477, -9613, 8577, 7642⟩,
      ⟨19946, -10314, 6261, 11701⟩, ⟨24005, -10845, 5560, 9385⟩,
      ⟨21689, -6786, 5029, 8684⟩, ⟨25748, -7317, 4328, 6368⟩,
      ⟨25047, -9633, 8387, 5837⟩, ⟨29106, -10164, 7686, 3521⟩],
    #[⟨26790, -6105, 7155, 2820⟩, ⟨26259, -6806, 4839, 6879⟩,
      ⟨30318, -7337, 4138, 4563⟩, ⟨29787, -8038, 1822, 8622⟩,
      ⟨29086, -10354, 5881, 8091⟩, ⟨33145, -10885, 5180, 5775⟩,
      ⟨32614, -11586, 2864, 9834⟩, ⟨36673, -12117, 2163, 7518⟩,
      ⟨34357, -8058, 1632, 6817⟩, ⟨38416, -8589, 931, 4501⟩],
    #[⟨37715, -10905, 4990, 3970⟩, ⟨41774, -11436, 4289, 1654⟩,
      ⟨39458, -7377, 3758, 953⟩, ⟨43517, -7908, 3057, -1363⟩,
      ⟨42986, -8609, 741, 2696⟩, ⟨40670, -4550, 210, 1995⟩,
      ⟨44729, -5081, -491, -321⟩, ⟨42413, -1022, -1022, -1022⟩,
      ⟨41712, -3338, 3037, -1553⟩, ⟨39396, 721, 2506, -2254⟩],
    #[⟨38865, 20, 190, 1805⟩, ⟨36549, 4079, -341, 1104⟩,
      ⟨40608, 3548, -1042, -1212⟩, ⟨40077, 2847, -3358, 2847⟩,
      ⟨44136, 2316, -4059, 531⟩]
  ]

private def baseWeight (r : Fin 85) : Counts := (baseWeights[r.val / 10]!)[r.val % 10]!

private theorem baseWeight_correct (r : Fin 85) (c : Fin 4) :
    (baseWeight r).get c = weighted (kerLetter 0) r.val c := by
  have h : ∀ (r : Fin 85) (c : Fin 4),
      (baseWeight r).get c = weighted (kerLetter 0) r.val c := by decide +kernel
  exact h r c

private theorem weighted_rotate (a : Fin 4) (n : ℕ) (c : Fin 4) :
    weighted (kerLetter a) n c = weighted (kerLetter 0) n (c - a) := by
  have he : ∀ i a c : Fin 4, coefficient c (i + a) = coefficient (c - a) (i + 0) := by decide
  exact Finset.sum_congr rfl fun t _ ↦ he kerDigits[t]! a c

private structure Cut where
  a : Fin 4
  r : Fin 85
  weightedPrefix : Counts

private def Cut.at (a : Fin 4) (r : Fin 85) : Cut := ⟨a, r, (baseWeight r).rotate a⟩

private theorem cutWeighted (a : Fin 4) (r : Fin 85) (c : Fin 4) :
    (Cut.at a r).weightedPrefix.get c = weighted (kerLetter a) r.val c := by
  simp only [Cut.at, Counts.rotate, Counts.get_ofFn, baseWeight_correct, weighted_rotate a]

private def Cut.ofLetter (b : Fin 4) (r : Fin 85) : Cut := Cut.at (b - kerDigits[r.val]!) r

private theorem cut_ofLetter (a : Fin 4) (r : Fin 85) :
    Cut.ofLetter (kerLetter a r.val) r = Cut.at a r := by
  have h : ∀ i a : Fin 4, i + a - i = a := by decide
  simp only [Cut.ofLetter, kerLetter, h]

private def correction (delta : Counts) (p q : Cut) : Counts :=
  let d := transformed delta
  Counts.ofFn fun c ↦ d.get c - p.weightedPrefix.get c + 2 * q.weightedPrefix.get c

private def removeLast (v : Counts) (r : Cut) : Counts :=
  Counts.ofFn fun c ↦ v.get c - r.weightedPrefix.get c

-- The sum of the four coordinates of the imbalance is the difference of the two lengths.
-- Once the first two offsets are fixed, that sum determines the last offset modulo 85.
private def lastOffset (d : Counts) (x y : Fin 85) : Fin 85 :=
  ⟨((d.total + 2 * (y.val : ℤ) - x.val) % 85).toNat, by omega⟩

-- If the coarser cuts coincide, their summed imbalance determines the only possible
-- spacing: all equal, or one equal pair and the remaining cut just one position away.
private def Degenerate (p q r : Cut) (d : Counts) : Prop :=
  (p.a = q.a ∧ q.a = r.a ∧ p.r < q.r ∧ q.r < r.r ∧ d = Counts.zero) ∨
  (p.a = q.a ∧ q.a ≠ r.a ∧ p.r < q.r ∧ d = Counts.letter q.a 1) ∨
  (p.a ≠ q.a ∧ q.a = r.a ∧ q.r < r.r ∧ d = Counts.letter p.a (-1))
  deriving Decidable

private def ValidParent (p q r : Cut) (d : Counts) : Prop :=
  accepted ⟨p.a, q.a, r.a, d⟩ ∧ -1 ≤ d.total ∧ d.total ≤ 1 ∧ ¬ Degenerate p q r d
  deriving Decidable

private def checkParent (v : Counts) (p q r : Cut) : Bool :=
  let d := removeLast v r
  if d.x0 % 43435 = 0 then
    if d.rem 43435 = Counts.zero then decide (ValidParent p q r (d.quot 43435)) else true
  else true

private def checkAt (t : Template) (x y : Fin 85) : Bool :=
  let p := Cut.ofLetter t.a x
  let q := Cut.ofLetter t.b y
  let r := Cut.ofLetter t.c (lastOffset t.delta x y)
  checkParent (correction t.delta p q) p q r


-- The first inverse-coordinate residue is a fast necessary test. Pack sixteen 16-bit
-- residues per chunk so the kernel can test most pairs without constructing their vectors.
private def phaseKeys : Array (Array ℕ) :=
  #[
    #[0x125c84a9098f9072338fa82f9e4e03549e780f1da34813ed0b0b06cfa09f0000,
      0x001d15729caa1fe7a17a191803989d6826f4a9312bc4104a1ea6166e237691c7,
      0x8d3e439d2bca892c517994f50996466ea623250f0148971c0d1124b9a4f808ff,
      0x745b8d0212e791d20dc120c3649413a524a91875841e243e29a34beb19333ecd,
      0x02d1a39aa5ada86a00d20a888ac70eae0676137e961006601d5e0b307f2616f9,
      0x02bd9c8d0ddca856070d],
    #[0x2e9506d204940ba29285a98300979bbb1ef8a08b113092c304bc9de2a6ee0000,
      0x1904141e24239ebd165b00db1b2b24379f7b290791b30aa59cd220b98f0aa55e,
      0x40e0290d049c4ebc1e02538c97081946a227a836945f31d7992f295f26cca70b,
      0x21ae766e8f1568a61e06840a18e08f2915b881614ffd863126512bb6817536d5,
      0x99e40bdda5ada7c097e502e500528cda10c17f1211958a3108737c6981798139,
      0x02130b1f9ea00fef00be],
    #[0x81ec028127c69e64a57223b499a81ce5977f0f1d90b0084e0412a4dba7980000,
      0x12b599ed05971448a87319189aab9d68145c8fa00d8d1be9006f8cf7a34b0f9f,
      0x26fa0289866f1befa7780e2743b1a3663693924c2fc41e4021fca6e1198416f1,
      0x071e11d366930b0481f761d710e854b97f4e4dea1dda4022765616763c100958,
      0xa0dd9ca1a5ad95d29ede880aa4589a227cff935303a386357a567f66168f719e,
      0x99d09c8da4ef8ec50014],
    #[0x04bf37a18db530d2a7709b912cc0a75a0c60a08b182902a99bcf0dc80fdb0000,
      0x120b22101d2a0ea328f300db22242437a6741d6808929abf13b1097b1f7a2c82,
      0x1264964a4ca90da8923806d91733a01422523f9f2e1b0a54274ca23b06422290,
      0x8a45102a1adf1bf371b216cd8d1621ec5dc52db5218126e6492e7f6234c28a81,
      0x09caa2f0a5ad050e07cba7ea0bf103b9a32e0f82881e1aa18f41266a143c1f9b,
      0x090c0b1fa599045097d1]
  ]

private def phaseKey (letter : Fin 4) (r : ℕ) : ℕ :=
  (((phaseKeys[letter.val]!)[r / 16]! >>> (16 * (r % 16))) % 65536)

private theorem phaseKey_correct (letter : Fin 4) (r : Fin 85) :
    (phaseKey letter r.val : ℤ) = (Cut.ofLetter letter r).weightedPrefix.x0 % 43435 := by
  have h : ∀ (letter : Fin 4) (r : Fin 85),
      (phaseKey letter r.val : ℤ) = (Cut.ofLetter letter r).weightedPrefix.x0 % 43435 := by
    decide +kernel
  exact h letter r

private def offsetKey (total x y : ℕ) : ℕ := (total + 2 * y + 85 - x) % 85

private def keyPass (t : Template) (x y : Fin 85) : Bool :=
  let z := offsetKey (t.delta.total % 85).toNat x.val y.val
  let delta := ((transformed t.delta).x0 % 43435).toNat
  (86870 + delta + 2 * phaseKey t.b y.val - phaseKey t.a x.val - phaseKey t.c z) % 43435 == 0

private def check (t : Template) : Bool :=
  (List.finRange 85).all fun x ↦ (List.finRange 85).all fun y ↦
    if keyPass t x y then checkAt t x y else true
private theorem validParent_of_check {p q r : Cut} {d v : Counts}
    (hc : checkParent v p q r = true)
    (hd : ∀ c, (removeLast v r).get c = 43435 * d.get c) : ValidParent p q r d := by
  have h0 := hd 0
  change (removeLast v r).x0 = 43435 * d.x0 at h0
  have hmask : (removeLast v r).x0 % 43435 = 0 := by rw [h0]; simp
  have hm : (removeLast v r).rem 43435 = Counts.zero := by
    apply Counts.eq_of_get
    intro c
    simp only [Counts.rem, Counts.get_ofFn, Counts.get_zero, hd]
    omega
  have hquot : (removeLast v r).quot 43435 = d := by
    apply Counts.eq_of_get
    intro c
    simp only [Counts.quot, Counts.get_ofFn, hd]
    omega
  simpa [checkParent, hmask, hm, hquot] using hc


private theorem offsetKey_correct (d : Counts) (x y : Fin 85) :
    offsetKey (d.total % 85).toNat x.val y.val = (lastOffset d x y).val := by
  have hx := x.isLt
  let t := d.total
  change (Int.toNat (t % 85) + 2 * y.val + 85 - x.val) % 85 =
    ((t + 2 * (y.val : ℤ) - x.val) % 85).toNat
  omega

private theorem phaseKeys_test (d p q r : ℤ) (h : (d - p + 2 * q - r) % 43435 = 0) :
    (86870 + (d % 43435).toNat + 2 * (q % 43435).toNat - (p % 43435).toNat -
      (r % 43435).toNat) % 43435 = 0 := by
  let lhs := 86870 + (d % 43435).toNat + 2 * (q % 43435).toNat
  have hcast (a : ℤ) : ((a % 43435).toNat : ℤ) = a % 43435 :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  have hlt (a : ℤ) : (a % 43435).toNat < 43435 := by
    have hh : a % 43435 < 43435 := Int.emod_lt_of_pos _ (by decide)
    rw [← hcast a] at hh
    exact_mod_cast hh
  have hp := hlt p
  have hr := hlt r
  have h₁ : (p % 43435).toNat ≤ lhs := by dsimp only [lhs]; omega
  have h₂ : (r % 43435).toNat ≤ lhs - (p % 43435).toNat := by dsimp only [lhs]; omega
  change (lhs - (p % 43435).toNat - (r % 43435).toNat) % 43435 = 0
  apply Int.ofNat_inj.mp
  rw [Int.natCast_mod, Int.natCast_sub h₂, Int.natCast_sub h₁]
  simp only [lhs, Int.natCast_add, Int.natCast_mul, hcast, Int.natCast_zero]
  change ((86870 : ℤ) + d % 43435 + 2 * (q % 43435) - p % 43435 - r % 43435) % 43435 = 0
  have he := Int.emod_add_mul_ediv (d - p + 2 * q - r) 43435
  rw [h, zero_add] at he
  have hz : (86870 : ℤ) + d % 43435 + 2 * (q % 43435) - p % 43435 - r % 43435 =
      0 + 43435 * (2 + (d - p + 2 * q - r) / 43435 - d / 43435 + p / 43435 -
        2 * (q / 43435) + r / 43435) := by
    linarith only [he, Int.emod_add_mul_ediv d 43435, Int.emod_add_mul_ediv p 43435,
      Int.emod_add_mul_ediv q 43435, Int.emod_add_mul_ediv r 43435]
  rw [hz, Int.add_mul_emod_self_left]
  rfl

private theorem keyPass_of_divisible (t : Template) (x y : Fin 85)
    (h : ((transformed t.delta).x0 - (Cut.ofLetter t.a x).weightedPrefix.x0 +
      2 * (Cut.ofLetter t.b y).weightedPrefix.x0 -
      (Cut.ofLetter t.c (lastOffset t.delta x y)).weightedPrefix.x0) % 43435 = 0) :
    keyPass t x y = true := by
  unfold keyPass
  rw [offsetKey_correct]
  apply beq_iff_eq.mpr
  have he (a : Fin 4) (r : Fin 85) : phaseKey a r.val =
      ((Cut.ofLetter a r).weightedPrefix.x0 % 43435).toNat := by
    rw [← phaseKey_correct]
    simp
  simpa only [he] using phaseKeys_test _ _ _ _ h

private theorem pullback_of_check
    (w : ℕ → Fin 4) (hw : ∀ n, w n ≠ w (n + 1)) (i j k : ℕ) (x y z : Fin 85)
    (hij : 85 * i + x.val < 85 * j + y.val) (hjk : 85 * j + y.val < 85 * k + z.val)
    (ht : check (templateAt (substitute w) (85 * i + x.val) (85 * j + y.val)
      (85 * k + z.val)) = true) :
    i < j ∧ j < k ∧ accepted (templateAt w i j k) := by
  let t := templateAt (substitute w) (85 * i + x.val) (85 * j + y.val) (85 * k + z.val)
  let p := Cut.at (w i) x
  let q := Cut.at (w j) y
  let r := Cut.at (w k) z
  have ha : t.a = kerLetter (w i) x.val := substitute_at w i _ x.isLt
  have hb : t.b = kerLetter (w j) y.val := substitute_at w j _ y.isLt
  have hc : t.c = kerLetter (w k) z.val := substitute_at w k _ z.isLt
  have hlast : lastOffset t.delta x y = z := by
    apply Fin.ext
    have hsum : t.delta.total = (↑(85 * i + x.val) : ℤ) + ↑(85 * k + z.val) -
        2 * ↑(85 * j + y.val) := imbalance_total _ _ _ _
    change ((t.delta.total + 2 * (y.val : ℤ) - x.val) % 85).toNat = z.val
    have he : t.delta.total + 2 * (y.val : ℤ) - x.val =
        (z.val : ℤ) + 85 * ((i : ℤ) + k - 2 * j) := by
      rw [hsum]
      omega
    rw [he, Int.add_mul_emod_self_left]
    have hz := z.isLt
    omega
  have hd (c : Fin 4) : (removeLast (correction t.delta p q) r).get c =
      43435 * (imbalance w i j k).get c := by
    simp only [removeLast, correction, Counts.get_ofFn]
    change (transformed (imbalance (substitute w) (85 * i + x.val) (85 * j + y.val)
      (85 * k + z.val))).get c - (Cut.at (w i) x).weightedPrefix.get c +
      2 * (Cut.at (w j) y).weightedPrefix.get c - (Cut.at (w k) z).weightedPrefix.get c = _
    simp only [cutWeighted, transformed_imbalance,
      weighted_substitute w i x.val c x.isLt.le, weighted_substitute w j y.val c y.isLt.le,
      weighted_substitute w k z.val c z.isLt.le]
    simp only [imbalance, Counts.get_ofFn]
    omega
  have hpass : keyPass t x y = true := by
    apply keyPass_of_divisible
    rw [hlast, ha, hb, hc, cut_ofLetter, cut_ofLetter, cut_ofLetter]
    have h0 := hd 0
    change (transformed t.delta).x0 - p.weightedPrefix.x0 + 2 * q.weightedPrefix.x0 -
      r.weightedPrefix.x0 = 43435 * (imbalance w i j k).get 0 at h0
    rw [h0]
    simp
  have hvalid : ValidParent p q r (imbalance w i j k) := by
    apply validParent_of_check (v := correction t.delta p q) _ hd
    change check t = true at ht
    unfold check at ht
    have hcheck := List.all_eq_true.mp (List.all_eq_true.mp ht x (List.mem_finRange _)) y
      (List.mem_finRange _)
    simpa only [hpass, ite_true, checkAt, hlast, ha, hb, hc, cut_ofLetter] using hcheck
  obtain ⟨hparent, hlo, hhi, hnd⟩ := hvalid
  rw [imbalance_total] at hlo hhi
  have hi : i ≤ j := by have := x.isLt; have := y.isLt; omega
  have hk : j ≤ k := by have := y.isLt; have := z.isLt; omega
  refine ⟨?_, ?_, hparent⟩
  · by_contra h
    have h' : j = i := by omega
    subst j
    apply hnd
    have hxy : x < y := by change x.val < y.val; omega
    rcases show k = i ∨ k = i + 1 by omega with e | e
    · subst k
      have hyz : y < z := by change y.val < z.val; omega
      refine Or.inl ⟨rfl, rfl, hxy, hyz, ?_⟩
      apply Counts.eq_of_get
      intro c
      simp only [imbalance, Counts.get_ofFn, Counts.get_zero]
      omega
    · subst k
      exact Or.inr (Or.inl ⟨rfl, hw i, hxy, imbalance_left_repeat w i⟩)
  · by_contra h
    have h' : k = j := by omega
    subst k
    apply hnd
    have hyz : y < z := by change y.val < z.val; omega
    rcases show j = i ∨ j = i + 1 by omega with e | e
    · subst j
      have hxy : x < y := by change x.val < y.val; omega
      refine Or.inl ⟨rfl, rfl, hxy, hyz, ?_⟩
      apply Counts.eq_of_get
      intro c
      simp only [imbalance, Counts.get_ofFn, Counts.get_zero]
      omega
    · subst j
      exact Or.inr (Or.inr ⟨hw i, rfl, hyz, imbalance_right_repeat w i⟩)

private def rotateWord (w : ℕ → Fin 4) (a : Fin 4) (n : ℕ) : Fin 4 := w n + a

private theorem substitute_rotate (w : ℕ → Fin 4) (a : Fin 4) :
    substitute (rotateWord w a) = rotateWord (substitute w) a := by
  funext n
  have ha : ∀ a b c : Fin 4, a + (b + c) = (a + b) + c := by decide
  simp only [substitute, rotateWord, kerLetter, ha]

private theorem templateAt_rotate (w : ℕ → Fin 4) (a : Fin 4) (i j k : ℕ) :
    templateAt (rotateWord w a) i j k = (templateAt w i j k).rotate a := by
  have he : ∀ b a c : Fin 4, b + a = c ↔ b = c - a := by decide
  have hcount (n : ℕ) (c : Fin 4) :
      prefixCount (rotateWord w a) n c = prefixCount w n (c - a) := by
    simp only [prefixCount, rotateWord, he]
  have hdelta : imbalance (rotateWord w a) i j k = (imbalance w i j k).rotate a := by
    apply Counts.eq_of_get
    intro c
    simp only [imbalance, Counts.rotate, Counts.get_ofFn, hcount]
  rw [templateAt, Template.rotate]
  change Template.mk ((rotateWord w a) i) ((rotateWord w a) j) ((rotateWord w a) k)
    (imbalance (rotateWord w a) i j k) = _
  rw [hdelta]
  rfl

private theorem rotate_neg_normalized (t : Template) : t.rotate (-t.a) = t.normalized := by
  have hzero : ∀ a : Fin 4, a + -a = 0 := by decide
  have hsub : ∀ a b : Fin 4, b + -a = b - a := by decide
  simp only [Template.rotate, Template.normalized, hzero, hsub]

private theorem template_normalized_rotate (t : Template) (a : Fin 4) :
    (t.rotate a).normalized = t.normalized := by
  have hab : ∀ b c a : Fin 4, b + a - (c + a) = b - c := by decide
  have hi : ∀ i c a : Fin 4, i - -(c + a) - a = i - -c := by decide
  have hd : (t.delta.rotate a).rotate (-(t.a + a)) = t.delta.rotate (-t.a) := by
    apply Counts.eq_of_get
    intro c
    simp only [Counts.rotate, Counts.get_ofFn, hi]
  simp only [Template.normalized, Template.rotate, hab, hd]

private theorem pullback (cert : ∀ t ∈ finiteTemplates, check t = true)
    (w : ℕ → Fin 4) (hw : ∀ n, w n ≠ w (n + 1)) (i j k : ℕ) (x y z : Fin 85)
    (hij : 85 * i + x.val < 85 * j + y.val) (hjk : 85 * j + y.val < 85 * k + z.val)
    (ht : accepted (templateAt (substitute w) (85 * i + x.val) (85 * j + y.val) (85 * k + z.val))) :
    i < j ∧ j < k ∧ accepted (templateAt w i j k) := by
  let t := templateAt (substitute w) (85 * i + x.val) (85 * j + y.val) (85 * k + z.val)
  let u := rotateWord w (-t.a)
  have ht' : templateAt (substitute u) (85 * i + x.val) (85 * j + y.val) (85 * k + z.val) =
      t.normalized := by
    rw [substitute_rotate, templateAt_rotate, rotate_neg_normalized]
  have hcheck := cert t.normalized ht
  rw [← ht'] at hcheck
  have hu (n : ℕ) : u n ≠ u (n + 1) := by
    intro h
    have he : ∀ a b c : Fin 4, a + c = b + c → a = b := by decide
    exact hw n (he _ _ _ h)
  obtain ⟨hi, hj, h⟩ := pullback_of_check u hu i j k x y z hij hjk hcheck
  have hn : (templateAt u i j k).normalized = (templateAt w i j k).normalized := by
    rw [templateAt_rotate, template_normalized_rotate]
  unfold accepted at h ⊢
  rw [hn] at h
  exact ⟨hi, hj, h⟩

private theorem kerWord_avoids_templates (cert : ∀ t ∈ finiteTemplates, check t = true)
    (k i j : ℕ) (hij : i < j) (hjk : j < k) : ¬ accepted (templateAt kerWord i j k) := by
  induction k using Nat.strong_induction_on generalizing i j with
  | ind k ih =>
    intro ht
    let x : Fin 85 := ⟨i % 85, Nat.mod_lt _ (by decide)⟩
    let y : Fin 85 := ⟨j % 85, Nat.mod_lt _ (by decide)⟩
    let z : Fin 85 := ⟨k % 85, Nat.mod_lt _ (by decide)⟩
    have hx : 85 * (i / 85) + x.val = i := by dsimp [x]; omega
    have hy : 85 * (j / 85) + y.val = j := by dsimp [y]; omega
    have hz : 85 * (k / 85) + z.val = k := by dsimp [z]; omega
    rw [← kerWord_fixed] at ht
    obtain ⟨hij', hjk', hp⟩ := pullback cert kerWord kerWord_adjacent
      (i / 85) (j / 85) (k / 85) x y z (by simpa only [hx, hy] using hij)
      (by simpa only [hy, hz] using hjk) (by simpa only [hx, hy, hz] using ht)
    exact ih (k / 85) (by omega) (i / 85) (j / 85) hij' hjk' hp

private theorem kerWord_avoids_of_certificate
    (cert : ∀ t ∈ finiteTemplates, check t = true) : ¬ HasAbelianSquare kerWord := by
  rintro ⟨i, j, k, hij, hjk, h⟩
  apply kerWord_avoids_templates cert k i j hij hjk
  change accepted ⟨kerWord i, kerWord j, kerWord k, imbalance kerWord i j k⟩
  have hz : imbalance kerWord i j k = Counts.zero := by
    apply Counts.eq_of_get
    intro c
    simp only [imbalance, Counts.get_ofFn, Counts.get_zero, h, sub_self]
  rw [hz]
  exact root_accepted _ _ _

private theorem threshold_of_certificate
    (cert : ∀ t ∈ finiteTemplates, check t = true) : unitStepWalkThreeAPIff := by
  intro d
  constructor
  · intro h
    by_contra hd
    obtain ⟨a, hw, hno⟩ := largeDimension_of_word (d := d) (by omega)
      (kerWord_avoids_of_certificate cert)
    exact hno (h a hw)
  · exact smallDimension


-- Check the finite invariant by kernel reduction in small independent batches.

set_option maxRecDepth 12000 in
set_option maxHeartbeats 30000000 in
-- This batch checks up to eight templates, each with 85² pairs of offsets.
private theorem checkBatch0 : ((finiteTemplates.drop 0).take 8).all check = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 30000000 in
-- This batch checks up to eight templates, each with 85² pairs of offsets.
private theorem checkBatch1 : ((finiteTemplates.drop 8).take 8).all check = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 30000000 in
-- This batch checks up to eight templates, each with 85² pairs of offsets.
private theorem checkBatch2 : ((finiteTemplates.drop 16).take 8).all check = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 30000000 in
-- This batch checks up to eight templates, each with 85² pairs of offsets.
private theorem checkBatch3 : ((finiteTemplates.drop 24).take 8).all check = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 30000000 in
-- This batch checks up to eight templates, each with 85² pairs of offsets.
private theorem checkBatch4 : ((finiteTemplates.drop 32).take 8).all check = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 30000000 in
-- This batch checks up to eight templates, each with 85² pairs of offsets.
private theorem checkBatch5 : ((finiteTemplates.drop 40).take 8).all check = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 30000000 in
-- This batch checks up to eight templates, each with 85² pairs of offsets.
private theorem checkBatch6 : ((finiteTemplates.drop 48).take 8).all check = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 30000000 in
-- This batch checks up to eight templates, each with 85² pairs of offsets.
private theorem checkBatch7 : ((finiteTemplates.drop 56).take 8).all check = true := by
  decide +kernel

private theorem certificate_passes : finiteTemplates.all check = true := by
  have h : finiteTemplates =
      ((finiteTemplates.drop 0).take 8) ++
      ((finiteTemplates.drop 8).take 8) ++
      ((finiteTemplates.drop 16).take 8) ++
      ((finiteTemplates.drop 24).take 8) ++
      ((finiteTemplates.drop 32).take 8) ++
      ((finiteTemplates.drop 40).take 8) ++
      ((finiteTemplates.drop 48).take 8) ++
      ((finiteTemplates.drop 56).take 8) := by decide +kernel
  rw [h]
  simp only [List.all_append, checkBatch0, checkBatch1, checkBatch2, checkBatch3,
    checkBatch4, checkBatch5, checkBatch6, checkBatch7, Bool.and_self]


/--
**Solution of Erdős Problem 192 on three-term progressions in unit-step walks.** For every
natural number $d$, every sequence $a_0, a_1, a_2, \dots$ of points of $\mathbb{R}^d$ whose steps
$a_{i+1} - a_i$ are all standard unit vectors contains a three-term arithmetic progression
(indices $i$, $j$, $k$ with $a_i \ne a_j$ and $a_i + a_k = 2 a_j$) if and only if $d \le 3$.

Points $a_i, a_j, a_k$ form a progression exactly when the step words from $i$ to $j$ and from
$j$ to $k$ are permutations of each other (an abelian square). Over at most three letters every
long enough word contains an abelian square, and Keränen's infinite abelian-square-free word over
four letters gives, for every $d \ge 4$, a walk with no three-term progression.
erdosproblems.com/192 lists the problem as solved.

Source: T.
F. Bloom, Erdős Problems, Problem #192, https://www.erdosproblems.com/192 (status SOLVED (LEAN));
resolution: V. Keränen, Abelian squares are avoidable on 4 letters, Automata, Languages and
Programming (ICALP 1992), Lecture Notes in Comput. Sci. 623, Springer (1992), 41-52,
erdosproblems.com/192: true for d ≤ 3 and false for d ≥ 4, via an infinite abelian-square-free word
over 4 letters (Keränen), https://doi.org/10.1007/3-540-55719-9_62.
-/
public theorem unitStepWalkThreeAPIff_holds : unitStepWalkThreeAPIff :=
  threshold_of_certificate fun t ht ↦ List.all_eq_true.mp certificate_passes t ht

end MathlibExt.Combinatorics.UnitStepWalkThreeTermProgressionErdosProblem192Wanted
