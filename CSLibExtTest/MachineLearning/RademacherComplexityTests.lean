/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.RademacherComplexity
public import Mathlib.Tactic.NormNum

/-!
# Empirical Rademacher complexity tests

The two-point set `{1, -1} ⊆ ℝ¹` has complexity exactly `1`: whatever the sign, one of the two
points matches it. A single vector has complexity `0`. Closed checks instantiate scaling,
convex-hull invariance, the contraction lemma with `|·|`, Massart's lemma, the VC bound on
the full cube of sign patterns, and the explicit VC rate.
-/

namespace Cslib.MachineLearning.Rademacher

open Real Finset Pointwise

open MathlibExt.Analysis.InnerProductSpace.RademacherTypeCotype (rademacherSign)

private noncomputable def twoPoints : Set (Fin 1 → ℝ) := {![1], ![-1]}

/-- Every sign vector attains correlation `1` on `{1, -1}`. -/
example (ε : Fin 1 → Bool) : supCorr twoPoints ε = 1 := by
  simp only [supCorr, twoPoints, Set.image_pair, csSup_pair, signCorr, Fin.sum_univ_one,
    rademacherSign]
  cases ε 0 <;> norm_num

example : rademacherComplexity twoPoints = 1 := by
  have h : ∀ ε : Fin 1 → Bool, supCorr twoPoints ε = 1 := by
    intro ε
    simp only [supCorr, twoPoints, Set.image_pair, csSup_pair, signCorr, Fin.sum_univ_one,
      rademacherSign]
    cases ε 0 <;> norm_num
  simp only [rademacherComplexity, h, Finset.sum_const, Finset.card_univ, Fintype.card_pi,
    Fintype.card_bool, Finset.prod_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

example (v : Fin 3 → ℝ) : rademacherComplexity ({v} : Set (Fin 3 → ℝ)) = 0 :=
  rademacherComplexity_singleton v

/-! Closed checks -/

example (A : Set (Fin 4 → ℝ)) :
    rademacherComplexity ((-3 : ℝ) • A) = 3 * rademacherComplexity A := by
  rw [rademacherComplexity_smul]; norm_num

example (A : Set (Fin 4 → ℝ)) (hne : A.Nonempty) (hA : Bornology.IsBounded A) :
    rademacherComplexity (convexHull ℝ A) = rademacherComplexity A :=
  rademacherComplexity_convexHull hne hA

/-- Taking absolute values coordinatewise does not increase the complexity. -/
example (A : Set (Fin 4 → ℝ)) (hA : Bornology.IsBounded A) :
    rademacherComplexity (coordMap (fun _ x => ‖x‖) '' A) ≤ rademacherComplexity A := by
  have := rademacherComplexity_coordMap_le hA (fun _ x => ‖x‖) (L := 1)
    (fun _ => lipschitzWith_one_norm)
  simpa using this

example (A : Set (Fin 4 → ℝ)) (hA : A.Finite) (hne : A.Nonempty)
    (h : ∀ a ∈ A, ∑ i, a i ^ 2 ≤ 2 ^ 2) :
    rademacherComplexity A ≤ 2 * √(2 * log A.ncard) / 4 := by
  simpa using rademacherComplexity_le_of_finite hA hne (by norm_num) h

/-- All four sign patterns on two points: VC dimension `2`, bound `√(log 4)`. -/
example : rademacherComplexity (signPatterns (Finset.univ : Finset (Finset (Fin 2)))) ≤
    √(2 * log (∑ k ∈ Iic (Finset.univ : Finset (Finset (Fin 2))).vcDim, (2 : ℕ).choose k : ℕ)
      / 2) := by
  simpa using rademacherComplexity_signPatterns_le (n := 2) Finset.univ_nonempty (by norm_num)

example (𝒜 : Finset (Finset (Fin 10))) (h𝒜 : 𝒜.Nonempty) (hd : 1 ≤ 𝒜.vcDim) :
    rademacherComplexity (signPatterns 𝒜) ≤
      √(2 * 𝒜.vcDim * log (exp 1 * 10 / 𝒜.vcDim) / 10) := by
  simpa using rademacherComplexity_signPatterns_le_vcDim h𝒜 hd

end Cslib.MachineLearning.Rademacher
