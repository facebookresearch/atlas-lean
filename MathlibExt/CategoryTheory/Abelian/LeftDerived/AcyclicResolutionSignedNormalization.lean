/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Abelian.LeftDerived.AcyclicResolutionZeroNormalization
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.AcyclicResolutionOneNormalization

/-!
# All-degree normalization of the retained projective acyclic comparison
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
namespace CategoryTheory.ProjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C] [HasProjectiveResolutions C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- The sign forced by the original kernel-tail boundary at each retained dimension-shift step. -/
def acyclicResolutionNormalizationSign : ℕ → ℤ
  | 0 => 1
  | n + 1 => normalizationCrossSign n * acyclicResolutionNormalizationSign n

/-- The original normalization sign is one in degree zero. -/
theorem acyclicResolutionNormalizationSign_zero : acyclicResolutionNormalizationSign 0 = 1 := rfl

/-- The original normalization sign is minus one in degree one. -/
theorem acyclicResolutionNormalizationSign_one : acyclicResolutionNormalizationSign 1 = -1 := by
  simp only [acyclicResolutionNormalizationSign, normalizationCrossSign, zero_add, pow_one, mul_one]

/-- Every projective resolution term has the required original positive-derived vanishing. -/
theorem normalizationProjectiveTerms_acyclic {X : C} (P : ProjectiveResolution X)
    (F : C ⥤ D) [F.Additive] :
    ∀ q n : ℕ, IsZero ((F.leftDerived (n + 1)).obj (P.complex.X q)) :=
  fun q n => F.isZero_leftDerived_obj_projective_succ n (P.complex.X q)

set_option backward.isDefEq.respectTransparency false in
/-- The retained higher comparison uses the boundary and kernel-tail homology iso. -/
theorem normalizationAcyclicProjective_succ_succ {X : C} (P : ProjectiveResolution X)
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    (hP : ∀ q i : ℕ, IsZero ((F.leftDerived (i + 1)).obj (P.complex.X q))) (n : ℕ) :
    (F.leftDerivedObjIsoHomologyOfAcyclicResolution P.complex P.π hP (n + 2)).hom =
      LeftDerivedDelta.LDdelta F (n + 1) (ShortComplex.kernelSequence (P.π.f 0))
        (normalizationKernelSequence_shortExact P) ≫
      (F.leftDerivedObjIsoHomologyOfAcyclicResolution
        (normalizationKernelTail P).complex (normalizationKernelTail P).π
        (normalizationProjectiveTerms_acyclic (normalizationKernelTail P) F) (n + 1)).hom ≫
      (normalizationKernelTailHomologyIso P F n).hom := by
  rw [Functor.leftDerivedObjIsoHomologyOfAcyclicResolution]
  dsimp only [Nat.casesAuxOn, Iso.trans_hom]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
In every degree the retained acyclic comparison is the SAME projective comparison multiplied by
the recursively forced original kernel-tail sign.
-/
theorem normalizationAcyclicProjective_hom {X : C} (P : ProjectiveResolution X)
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    (hP : ∀ q i : ℕ, IsZero ((F.leftDerived (i + 1)).obj (P.complex.X q))) (n : ℕ) :
    (F.leftDerivedObjIsoHomologyOfAcyclicResolution P.complex P.π hP n).hom =
      acyclicResolutionNormalizationSign n • (P.isoLeftDerivedObj F n).hom := by
  induction n using Nat.twoStepInduction generalizing X with
  | zero =>
      simpa only [acyclicResolutionNormalizationSign_zero, one_zsmul] using
        normalizationAcyclicProjective_zero P F hP
  | one =>
      simpa only [acyclicResolutionNormalizationSign_one, neg_one_zsmul] using
        normalizationAcyclicProjective_one P F hP
  | more n _ ih =>
      have hi := ih (P := normalizationKernelTail P)
        (hP := normalizationProjectiveTerms_acyclic (normalizationKernelTail P) F)
      apply (cancel_epi (P.isoLeftDerivedObj F (n + 2)).inv).1
      rw [normalizationAcyclicProjective_succ_succ, hi]
      simp only [comp_zsmul, zsmul_comp, Iso.inv_hom_id]
      rw [normalizationKernelTail_nativeBoundary_sign]
      simp only [smul_smul]
      change (acyclicResolutionNormalizationSign (n + 1) * normalizationCrossSign (n + 1)) •
          𝟙 (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homology (n + 2)) =
        (normalizationCrossSign (n + 1) * acyclicResolutionNormalizationSign (n + 1)) •
          𝟙 (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homology (n + 2))
      rw [Int.mul_comm]

set_option backward.isDefEq.respectTransparency false in
/-- The all-degree original normalization can be read directly after the SAME comparison inverse. -/
theorem normalizationAcyclicProjective_inv_comp_hom {X : C} (P : ProjectiveResolution X)
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    (hP : ∀ q i : ℕ, IsZero ((F.leftDerived (i + 1)).obj (P.complex.X q))) (n : ℕ) :
    (P.isoLeftDerivedObj F n).inv ≫
      (F.leftDerivedObjIsoHomologyOfAcyclicResolution P.complex P.π hP n).hom =
    acyclicResolutionNormalizationSign n • 𝟙
      (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homology n) := by
  rw [normalizationAcyclicProjective_hom, comp_zsmul, Iso.inv_hom_id]
  rfl

end CategoryTheory.ProjectiveResolution
