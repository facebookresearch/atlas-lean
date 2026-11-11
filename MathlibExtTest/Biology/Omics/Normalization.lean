/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Omics.Normalization
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Tests for the centered log-ratio transform.

* ground truth: `clr (1, 1, 1) = 0` and `clr (1, e²) = (-1, 1)`, computed from the definition;
* scale invariance on `x = (1, 2, 3)` and `5 • x = (5, 10, 15)`;
* information loss: `(1, 2, 3) ≠ (2, 4, 6)` have the same CLR transform but totals `6 ≠ 12`;
* zeros: the counts `(0, 3, 1)` are outside the CLR domain and enter only via the pseudocount
  rule (`c = 1/2` gives `(1/2, 7/2, 3/2)`), where the zero gets the smallest CLR coordinate;
* boundary: no parts (`Fin 0`). -/

namespace MathlibExtTest.Biology.Omics.Normalization

open MathlibExt.Biology.Omics.Normalization

/-! ### Ground truth from the definition -/

example : clr (⟨fun _ : Fin 3 => 1, fun _ => one_pos⟩ : PosComposition (Fin 3)) = 0 := by
  funext i; simp [clr]

/-- `(1, e²)`: logs `(0, 2)`, mean `1`, so `clr = (-1, 1)`. -/
noncomputable def xe : PosComposition (Fin 2) :=
  ⟨![1, Real.exp 2], fun i => by fin_cases i <;> simp [Real.exp_pos]⟩

example : clr xe = ![-1, 1] := by
  funext i
  fin_cases i <;> norm_num [clr, xe, Fin.sum_univ_two]

/-! ### Scale invariance on a concrete composition -/

/-- The composition `(1, 2, 3)`. -/
def x123 : PosComposition (Fin 3) := ⟨![1, 2, 3], fun i => by fin_cases i <;> norm_num⟩

/-- The composition `(5, 10, 15)`. -/
def x51015 : PosComposition (Fin 3) := ⟨![5, 10, 15], fun i => by fin_cases i <;> norm_num⟩

/-- Multiplying `(1, 2, 3)` by `5` gives `(5, 10, 15)` (checked entrywise). -/
example : x123.smul 5 (by norm_num) = x51015 := by
  apply Subtype.ext; funext i
  fin_cases i <;> simp [x123, x51015, PosComposition.smul] <;> norm_num

/-- Scale invariance: `clr (5, 10, 15) = clr (1, 2, 3)`. -/
example : clr x51015 = clr x123 := by
  have h : x51015 = x123.smul 5 (by norm_num) := by
    apply Subtype.ext; funext i
    fin_cases i <;> simp [x123, x51015, PosComposition.smul] <;> norm_num
  rw [h, clr_smul]

example : ∑ i, clr x123 i = 0 := sum_clr x123

/-- Permutation equivariance on the swap of the first two parts. -/
example : clr (x123.perm (Equiv.swap 0 1)) = clr x123 ∘ Equiv.swap 0 1 := clr_perm _ x123

/-! ### Information loss -/

/-- The composition `(2, 4, 6)`. -/
def x246 : PosComposition (Fin 3) := ⟨![2, 4, 6], fun i => by fin_cases i <;> norm_num⟩

example : x123 ≠ x246 := by
  intro h
  have := congrArg (fun x : PosComposition (Fin 3) => x.1 0) h
  simp [x123, x246] at this

/-- Distinct compositions with the same CLR transform. -/
example : clr x123 = clr x246 :=
  clr_eq_clr_iff.2 ⟨2, two_pos, by
    apply Subtype.ext; funext i
    fin_cases i <;> simp [x123, x246, PosComposition.smul] <;> norm_num⟩

/-- ... whose totals differ, so the total cannot be read off the CLR transform. -/
example : ∑ i, x123.1 i = 6 ∧ ∑ i, x246.1 i = 12 := by
  simp [x123, x246, Fin.sum_univ_three]; norm_num

example : ¬ ∃ f : (Fin 3 → ℝ) → ℝ, ∀ x : PosComposition (Fin 3), f (clr x) = ∑ i, x.1 i :=
  not_exists_total_of_clr

/-! ### Zeros: the pseudocount policy -/

/-- Counts with a zero: `(0, 3, 1)`. -/
def n031 : Fin 3 → ℝ := ![0, 3, 1]

theorem n031_nonneg : ∀ i, 0 ≤ n031 i := fun i => by fin_cases i <;> simp [n031]

/-- The counts `(0, 3, 1)` are not in the domain of `clr`. -/
example : ¬ ∀ i, 0 < n031 i := fun h => by simpa [n031] using h 0

/-- With pseudocount `1/2` they become the positive composition `(1/2, 7/2, 3/2)`. -/
example : (withPseudocount (1 / 2) (by norm_num) n031 n031_nonneg).1 = ![1 / 2, 7 / 2, 3 / 2] := by
  funext i; fin_cases i <;> simp [withPseudocount, n031] <;> norm_num

/-- The zero count gets the smallest CLR coordinate. -/
example (j : Fin 3) :
    clr (withPseudocount (1 / 2) (by norm_num) n031 n031_nonneg) 0 ≤
      clr (withPseudocount (1 / 2) (by norm_num) n031 n031_nonneg) j :=
  clr_withPseudocount_le_of_eq_zero _ _ _ _ (by simp [n031]) j

/-- With a fixed pseudocount, scale invariance fails. -/
example : ∃ (n : Fin 2 → ℝ) (hn : ∀ i, 0 ≤ n i) (h2n : ∀ i, 0 ≤ ((2 : ℝ) • n) i),
    clr (withPseudocount 1 one_pos ((2 : ℝ) • n) h2n) ≠ clr (withPseudocount 1 one_pos n hn) :=
  exists_clr_withPseudocount_smul_ne

/-! ### Boundary: no parts -/

example (x : PosComposition (Fin 0)) : ∑ i, clr x i = 0 := sum_clr x

/-! ### Axioms -/

#print axioms clr_smul
#print axioms clr_perm
#print axioms sum_clr
#print axioms clr_eq_clr_iff
#print axioms exists_clr_eq_sum_eq
#print axioms not_exists_total_of_clr
#print axioms clr_withPseudocount_smul
#print axioms exists_clr_withPseudocount_smul_ne
#print axioms clr_withPseudocount_le_of_eq_zero

end MathlibExtTest.Biology.Omics.Normalization
