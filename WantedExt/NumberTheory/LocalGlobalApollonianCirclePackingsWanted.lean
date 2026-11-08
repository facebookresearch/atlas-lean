/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The local-global conjecture for Apollonian circle packings is false

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.LocalGlobalApollonianCirclePackings` — annals_local_global_apollonian_circle_packings (manifest `manifests/problems/annals_local_global_apollonian_circle_packings.toml`, rev 1, submitter Thomas Browning, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.LocalGlobalApollonianCirclePackingsWanted` namespace. Mathematical
statements are unchanged. Source: S. Haag, C. Kertzer, J. Rickards, and K. E. Stange, `The local-global conjecture for Apollonian circle packings is false`, Annals of Math, 200 (2) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-200-2-LocalGlobalApollonianCirclePackings.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.LinearAlgebra.Matrix.Permutation

@[expose] public section

namespace MathlibExt.NumberTheory.LocalGlobalApollonianCirclePackingsWanted
/-!
# Main Statements from The local-global conjecture for Apollonian circle packings is false

We formalise the statements of the main results from S. Haag, C. Kertzer, J. Rickards, and
K. E. Stange, `The local-global conjecture for Apollonian circle packings is false`,
Annals of Math, 200 (2) 2024.
-/

set_option autoImplicit false

namespace LocalGlobalApollonianCirclePackings

open Matrix

/-- The action of the general linear group on quadruples of integers. -/
instance : MulAction (GL (Fin 4) ℤ) (Fin 4 → ℤ) where
  smul X v := X.1 *ᵥ v
  one_smul v := one_mulVec v
  mul_smul X Y v := (mulVec_mulVec v X.1 Y.1).symm

@[simp]
lemma GeneralLinearGroup.smul_def (X : GL (Fin 4) ℤ) (v : Fin 4 → ℤ) :
    X • v = X.1 *ᵥ v :=
  rfl

/-- The action of the general linear group on primitive quadruples of integers. -/
def GeneralLinearGroupAction : SubMulAction (GL (Fin 4) ℤ) (Fin 4 → ℤ) where
  carrier := { v | Finset.univ.gcd v = 1}
  smul_mem' X v hv := by
    rw [Set.mem_ofPred_eq] at hv ⊢
    apply Int.eq_one_of_dvd_one
    · rw [← Finset.normalize_gcd, ← Int.abs_eq_normalize]
      apply abs_nonneg
    · rw [← hv, Finset.dvd_gcd_iff]
      intro i _
      have key : v i = ((X⁻¹).1 *ᵥ (X.1 *ᵥ v)) i := by simp
      rw [key, mulVec_eq_sum (X.1 *ᵥ v) (X⁻¹).1]
      simp only [op_smul_eq_smul, Finset.sum_apply]
      apply Finset.dvd_sum
      intro i hi
      apply dvd_mul_of_dvd_left
      apply Finset.gcd_dvd hi

/-- The matrix of the Descartes form `2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) - (a + b + c + d) ^ 2`. -/
def DescartesMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, -1, -1, -1;
     -1, 1, -1, -1;
     -1, -1, 1, -1;
     -1, -1, -1, 1]

/-- The group of matrices preserving the Descartes form. -/
def DescartesOrthogonalGroup : Subgroup (GL (Fin 4) ℤ) where
  carrier := {X | star X * DescartesMatrix * X = DescartesMatrix}
  one_mem' := by simp
  inv_mem' hX := by grind [star_inv, Units.inv_mul_cancel_left, Units.mul_inv]
  mul_mem' hX hY := by grind [Units.val_mul, StarMul.star_mul]

theorem mem_descartesOrthogonalGroup_iff {X : GL (Fin 4) ℤ} :
    X ∈ DescartesOrthogonalGroup ↔ star X * DescartesMatrix * X = DescartesMatrix :=
  Iff.rfl

instance (X : GL (Fin 4) ℤ) : Decidable (X ∈ DescartesOrthogonalGroup) :=
  decidable_of_iff (star X * DescartesMatrix * X = DescartesMatrix) mem_descartesOrthogonalGroup_iff

theorem descartes_iff {v : Fin 4 → ℤ} :
    (∑ i, v i) ^ 2 = 2 * ∑ i, v i ^ 2 ↔ v ᵥ* DescartesMatrix ⬝ᵥ v = 0 := by
  simp [DescartesMatrix, vecMul_eq_sum, dotProduct, Fin.sum_univ_four]
  grind

/-- The action of the Descartes orthogonal group on primitive Descartes quadruples. -/
def DescartesOrthogonalGroupAction : SubMulAction DescartesOrthogonalGroup (Fin 4 → ℤ) where
  carrier := { v | (∑ i, v i) ^ 2 = 2 * ∑ i, v i ^ 2 ∧ Finset.univ.gcd v = 1}
  smul_mem' := by
    rintro ⟨X, hX⟩ v ⟨hv1, hv2⟩
    rw [mem_descartesOrthogonalGroup_iff, Units.coe_star,
      star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at hX
    refine ⟨?_, GeneralLinearGroupAction.smul_mem X hv2⟩
    rw [descartes_iff] at hv1 ⊢
    rwa [Subgroup.mk_smul, GeneralLinearGroup.smul_def,
      vecMul_mulVec, dotProduct_mulVec, vecMul_vecMul, hX]

/-- An integral primitive Descartes quadruple, as defined in Section 1.1 of the paper. -/
def integralPrimitiveDescartesQuadruple : Set (Fin 4 → ℤ) :=
  { v | ∑ i, v i > 0 ∧ (∑ i, v i) ^ 2 = 2 * ∑ i, v i ^ 2 ∧ Finset.univ.gcd v = 1}

theorem mem_integralPrimitiveDescartesQuadruple_iff {v : Fin 4 → ℤ} :
    v ∈ integralPrimitiveDescartesQuadruple ↔
      ∑ i, v i > 0 ∧ (∑ i, v i) ^ 2 = 2 * ∑ i, v i ^ 2 ∧ Finset.univ.gcd v = 1 :=
  Iff.rfl

instance (v : Fin 4 → ℤ) : Decidable (v ∈ integralPrimitiveDescartesQuadruple) :=
  decidable_of_iff
    (∑ i, v i > 0 ∧ (∑ i, v i) ^ 2 = 2 * ∑ i, v i ^ 2 ∧ Finset.univ.gcd v = 1)
    mem_integralPrimitiveDescartesQuadruple_iff

/-- One of the generators of the Apollonian group; see the start of Section 3 of the paper. -/
abbrev S₁ : GL (Fin 4) ℤ :=
  ⟨!![-1, 2, 2, 2; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
    !![-1, 2, 2, 2; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
    by decide, by decide⟩

/-- One of the generators of the Apollonian group; see the start of Section 3 of the paper. -/
abbrev S₂ : GL (Fin 4) ℤ :=
  ⟨!![1, 0, 0, 0; 2, -1, 2, 2; 0, 0, 1, 0; 0, 0, 0, 1],
    !![1, 0, 0, 0; 2, -1, 2, 2; 0, 0, 1, 0; 0, 0, 0, 1],
    by decide, by decide⟩

/-- One of the generators of the Apollonian group; see the start of Section 3 of the paper. -/
abbrev S₃ : GL (Fin 4) ℤ :=
  ⟨!![1, 0, 0, 0; 0, 1, 0, 0; 2, 2, -1, 2; 0, 0, 0, 1],
    !![1, 0, 0, 0; 0, 1, 0, 0; 2, 2, -1, 2; 0, 0, 0, 1],
    by decide, by decide⟩

/-- One of the generators of the Apollonian group; see the start of Section 3 of the paper. -/
abbrev S₄ : GL (Fin 4) ℤ :=
  ⟨!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 2, 2, 2, -1],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 2, 2, 2, -1],
    by decide, by decide⟩

/-- The Apollonian group, as defined at the start of Section 3 of the paper. -/
def ApollonianGroup : Subgroup (GL (Fin 4) ℤ) := Subgroup.closure {S₁, S₂, S₃, S₄}

theorem apollonianGroup_le_descartesOrthogonalGroup :
    ApollonianGroup ≤ DescartesOrthogonalGroup := by
  simp +decide [ApollonianGroup, Set.insert_subset_iff]

/-- The group of allowable transformations of integral primitive Descartes quadruples. -/
def TransformationGroup : Subgroup (GL (Fin 4) ℤ) :=
  ApollonianGroup ⊔ permMatrixHom.toHomUnits.range

open scoped Pointwise

/-- `TransformationGroup` stabilizes `integralPrimitiveDescartesQuadruple`. -/
theorem transformationGroup_smul_integralPrimitiveDescartesQuadruple
    (g : GL (Fin 4) ℤ) (hg : g ∈ TransformationGroup) :
    g • integralPrimitiveDescartesQuadruple ⊆ integralPrimitiveDescartesQuadruple := by
  revert g
  rw [← MulAction.le_stabilizer_iff_smul_le]
  apply sup_le
  · suffices h1 : ∀ X ∈ ({S₁, S₂, S₃, S₄} : Set (GL (Fin 4) ℤ)),
        X • integralPrimitiveDescartesQuadruple ⊆ integralPrimitiveDescartesQuadruple by
      rw [ApollonianGroup, Subgroup.closure_le]
      simp_rw [Set.subset_def, SetLike.mem_coe, MulAction.mem_stabilizer_iff,
        Set.Subset.antisymm_iff, forall_and, Set.subset_smul_set_iff, and_iff_right h1]
      rw [show ({S₁, S₂, S₃, S₄} : Set (GL (Fin 4) ℤ)) = {S₁, S₂, S₃, S₄}⁻¹ by simp]
      simpa only [Set.mem_inv, Set.forall_inv_mem]
    simp only [Set.smul_set_subset_iff]
    rintro X hX v ⟨hv1, hv2⟩
    refine ⟨?_, DescartesOrthogonalGroupAction.smul_mem
      ⟨X, apollonianGroup_le_descartesOrthogonalGroup (Subgroup.subset_closure hX)⟩ hv2⟩
    simp only [Fin.sum_univ_four] at hv1 hv2
    rcases hX with rfl | rfl | rfl | rfl <;> simp [Fin.sum_univ_four, mulVec_eq_sum] <;> nlinarith
  · rw [MulAction.le_stabilizer_iff_smul_le]
    simp only [Set.smul_set_subset_iff]
    rintro X ⟨σ, rfl⟩ v ⟨hv1, hv2, hv3⟩
    simp only [GeneralLinearGroup.smul_def, MonoidHom.coe_toHomUnits, permMatrixHom_apply,
      permMatrix_mulVec, Equiv.Perm.coe_inv, mem_integralPrimitiveDescartesQuadruple_iff,
      Function.comp_apply, Equiv.sum_comp, gt_iff_lt]
    refine ⟨hv1, ?_, ?_⟩
    · refine hv2.trans ?_
      congr 1
      exact (Equiv.sum_comp _ _).symm
    · rw [← Finset.normalize_gcd, ← Int.abs_eq_normalize]
      apply Int.eq_one_of_dvd_one (abs_nonneg _)
      rw [Int.abs_eq_normalize, Finset.normalize_gcd, ← hv3, Finset.dvd_gcd_iff]
      exact fun i hi ↦ (Finset.gcd_dvd (Finset.mem_univ (σ i))).trans (by simp)

/-- The action of `TransformationGroup` on integral primitive Descartes quadruples. -/
def TransformationGroupAction : SubMulAction TransformationGroup (Fin 4 → ℤ) where
  carrier := integralPrimitiveDescartesQuadruple
  smul_mem' X v hv :=
    transformationGroup_smul_integralPrimitiveDescartesQuadruple X X.2 ⟨v, hv, rfl⟩

instance : MulAction TransformationGroup integralPrimitiveDescartesQuadruple :=
  TransformationGroupAction.mulAction

/-- A `PrimitiveApollonianCirclePacking` is an orbit of integral primitive Descartes quadruples
under the action of the transformation group. -/
def PrimitiveApollonianCirclePacking :=
  MulAction.orbitRel.Quotient TransformationGroup integralPrimitiveDescartesQuadruple

/-- The curvature set of a primitive Apollonian circle packing. -/
def curvatureSet (A : PrimitiveApollonianCirclePacking) : Set ℤ :=
  ⋃ v ∈ A.orbit, Set.range v.1

/--
Statement of Theorem 1.6:

The Apollonian circle packing `A` generated by `(−3, 5, 8, 8)` has no square curvatures.
Source: S. Haag, C. Kertzer, J. Rickards, and K. E. Stange, `The local-global conjecture for Apollonian circle packings is false`, Annals of Math, 200 (2) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-200-2-LocalGlobalApollonianCirclePackings.lean Via leanprover/lean-eval@38361be, problem `annals_local_global_apollonian_circle_packings`.
-/
public theorem_wanted theorem_1_6 : ∀ n, n ^ 2 ∉ curvatureSet ⟦⟨![-3, 5, 8, 8], by decide⟩⟧

/-- The positive curvatures missing in a primitive Apollonian circle packing,
as defined in the start of Section 1.2 of the paper. -/
def missingCurvatureSet (A : PrimitiveApollonianCirclePacking) : Set ℤ :=
  {n | n > 0 ∧ n ∉ curvatureSet A ∧ ∃ k ∈ curvatureSet A, k ≡ n [ZMOD 24]}

/-- The number of missing curvatures up to `N` in a primitive Apollonian circle packing. -/
noncomputable def missingCurvatures (A : PrimitiveApollonianCirclePacking) (N : ℝ) : ℝ :=
  (missingCurvatureSet A ∩ {x | x ≤ N}).ncard

/--
Statement of Theorem 1.3:

There exist infinitely many `A` for which the number of missing curvatures up to `N` is `Ω(√N)`.
Source: S. Haag, C. Kertzer, J. Rickards, and K. E. Stange, `The local-global conjecture for Apollonian circle packings is false`, Annals of Math, 200 (2) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-200-2-LocalGlobalApollonianCirclePackings.lean Via leanprover/lean-eval@38361be, problem `annals_local_global_apollonian_circle_packings`.
-/
public theorem_wanted theorem_1_3 : {A : PrimitiveApollonianCirclePacking |
    Real.sqrt =O[Filter.atTop] missingCurvatures A}.Infinite

end LocalGlobalApollonianCirclePackings

end MathlibExt.NumberTheory.LocalGlobalApollonianCirclePackingsWanted
