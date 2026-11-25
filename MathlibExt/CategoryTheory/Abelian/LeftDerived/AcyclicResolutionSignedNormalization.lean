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
# Triangular normalization of a projective acyclic comparison

The kernel-tail cross coefficients `ε_n=(-1)^(n+1)` define
`σ₀=1`, `σ_(n+1)=ε_n σ_n`, hence `σ_n=(-1)^(n(n+1)/2)`.
For an additive right-exact functor between abelian categories, the
acyclic comparison on a projective resolution is `σ_n` times its
canonical projective-resolution comparison.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
namespace CategoryTheory.ProjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C] [HasProjectiveResolutions C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- The integer normalization signs satisfy `σ₀=1` and
`σ_(n+1)=(-1)^(n+1) σ_n`, the recurrence imposed by the kernel-tail
boundary coefficients. -/
def acyclicResolutionNormalizationSign : ℕ → ℤ
  | 0 => 1
  | n + 1 => normalizationCrossSign n * acyclicResolutionNormalizationSign n

/-- The triangular normalization scalar in degree zero is `σ₀=1`. -/
theorem acyclicResolutionNormalizationSign_zero : acyclicResolutionNormalizationSign 0 = 1 := rfl

/-- The triangular normalization scalar in degree one is `σ₁=-1`. -/
theorem acyclicResolutionNormalizationSign_one : acyclicResolutionNormalizationSign 1 = -1 := by
  simp only [acyclicResolutionNormalizationSign, normalizationCrossSign, zero_add, pow_one, mul_one]

/-- Let `C,D` be abelian, with projective resolutions in `C`, and
`F : C → D` additive. Every term of a projective resolution `P`
is `F`-acyclic: `L_(n+1)F(P_q)=0` for all `q,n`. -/
theorem normalizationProjectiveTerms_acyclic {X : C} (P : ProjectiveResolution X)
    (F : C ⥤ D) [F.Additive] :
    ∀ q n : ℕ, IsZero ((F.leftDerived (n + 1)).obj (P.complex.X q)) :=
  fun q n => F.isZero_leftDerived_obj_projective_succ n (P.complex.X q)

set_option backward.isDefEq.respectTransparency false in
/-- Let `C,D` be abelian, with projective resolutions in `C`,
`F : C → D` additive and preserving finite colimits, and `P` a
projective resolution of `X` with `L_(i+1)F(P_q)=0` for every `q,i`. In degree `n+2`, the acyclic comparison is the boundary for
`ker(P₀ → X) → P₀ → X`, followed by the degree-`n+1` acyclic
comparison for the kernel-tail resolution and its homology
identification with `H_(n+2)(F(P))`. -/
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
/-- Let `C,D` be abelian, with projective resolutions in `C`,
`F : C → D` additive and preserving finite colimits, and `P` a
projective resolution of `X` with `L_(i+1)F(P_q)=0` for every `q,i`. In degree `n`, the forward acyclic comparison on `P` equals
`σ_n=(-1)^(n(n+1)/2)` times its forward canonical
projective-resolution comparison. -/
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
/-- Let `C,D` be abelian, with projective resolutions in `C`,
`F : C → D` additive and preserving finite colimits, and `P` a
projective resolution of `X` with `L_(i+1)F(P_q)=0` for every `q,i`. The inverse canonical projective comparison followed by the
forward acyclic comparison is `σ_n • 𝟙` on `H_n(F(P))`, where
`σ_n=(-1)^(n(n+1)/2)`. -/
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
