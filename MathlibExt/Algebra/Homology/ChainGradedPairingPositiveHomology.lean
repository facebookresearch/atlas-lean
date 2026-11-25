/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.HomologicalComplexCokernelHomology
public import MathlibExt.Algebra.Homology.ChainGradedPairingPositiveCokernel

/-!
# Low homology of the actual both-positive pairing quotient

The actual strict-positive map is zero in degrees zero and one. Its native
cokernel projection therefore preserves homology in these degrees. The
module pointwise quotient obtains the same comparison through its earned
native cokernel isomorphism. No full Harrison or AQ comparison is asserted.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v

namespace HomologicalComplex.ChainGradedPairing

section GeneralNativeCokernel

variable {C : Type u} [Category.{v} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  {K₁ K₂ K₃ : ChainComplex C ℕ} (P : ChainGradedPairing K₁ K₂ K₃)
  (h₁ : K₁.d 1 0 = 0) (h₂ : K₂.d 1 0 = 0)

/-- The actual strict-positive map has zero components below degree two. -/
theorem strictPositivePairing_f_eq_zero (n : ℕ) (hn : n < 2) :
    (strictPositivePairing P h₁ h₂).f n = 0 := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = n at hpq
  subst n
  simp only [comp_zero]
  change (strictPositivePairing P h₁ h₂).pair p q = 0
  have hcompat : tensorHom (K₁.positiveStupidTruncInclusion h₁)
      (K₂.positiveStupidTruncInclusion h₂) ≫ P =
        strictPositivePairing P h₁ h₂ ≫ 𝟙 K₃ := by
    simp only [strictPositivePairing, Category.comp_id]
  have h := pair_naturality (strictPositivePairing P h₁ h₂) P
    (K₁.positiveStupidTruncInclusion h₁)
    (K₂.positiveStupidTruncInclusion h₂) (𝟙 K₃) hcompat p q
  have hzero : p = 0 ∨ q = 0 := by omega
  rcases hzero with hp | hq
  · subst p
    rw [positiveStupidTruncInclusion_f_zero] at h
    simpa only [MonoidalPreadditive.zero_tensor, zero_comp, id_f,
      Category.comp_id] using h.symm
  · subst q
    rw [positiveStupidTruncInclusion_f_zero] at h
    simpa only [MonoidalPreadditive.tensor_zero, zero_comp, id_f,
      Category.comp_id] using h.symm

/-- The native projection is a quasi-isomorphism at every degree below two. -/
theorem strictPositiveProjection_quasiIsoAt (n : ℕ) (hn : n < 2) :
    QuasiIsoAt (strictPositiveProjection P h₁ h₂) n := by
  change QuasiIsoAt (cokernel.π (strictPositivePairing P h₁ h₂)) n
  apply HomologicalComplex.quasiIsoAt_cokernelProjection_of_zero_components
  · exact strictPositivePairing_f_eq_zero P h₁ h₂ n hn
  · apply strictPositivePairing_f_eq_zero P h₁ h₂
    have hnext : (ComplexShape.down ℕ).next n ≤ n := by
      cases n <;> simp
    omega

/-- The canonical low-degree isomorphism is the homology of the actual native projection. -/
def strictPositiveCokernelHomologyIso (n : ℕ) (hn : n < 2) :
    K₃.homology n ≅ (strictPositiveCokernel P h₁ h₂).homology n := by
  letI := strictPositiveProjection_quasiIsoAt P h₁ h₂ n hn
  exact _root_.isoOfQuasiIsoAt (strictPositiveProjection P h₁ h₂) n

/-- The comparison's forward map is the original projection on homology. -/
theorem strictPositiveCokernelHomologyIso_hom (n : ℕ) (hn : n < 2) :
    (strictPositiveCokernelHomologyIso P h₁ h₂ n hn).hom =
      HomologicalComplex.homologyMap (strictPositiveProjection P h₁ h₂) n := rfl

end GeneralNativeCokernel

section ModulePointwiseQuotient

variable {R : Type u} [Ring R]
  [MonoidalCategory (ModuleCat.{v} R)] [MonoidalPreadditive (ModuleCat.{v} R)]
  {K₁ K₂ K₃ : ChainComplex (ModuleCat.{v} R) ℕ}
  (P : ChainGradedPairing K₁ K₂ K₃)
  (h₁ : K₁.d 1 0 = 0) (h₂ : K₂.d 1 0 = 0)

/-- The actual pointwise quotient has the same low-degree quasi-isomorphism. -/
theorem positiveImageProjection_quasiIsoAt (n : ℕ) (hn : n < 2) :
    QuasiIsoAt (positiveImageProjection P h₁ h₂) n := by
  let := strictPositiveProjection_quasiIsoAt P h₁ h₂ n hn
  let e := strictPositiveCokernelIsoPositiveImageQuotient P h₁ h₂
  have h : QuasiIsoAt (strictPositiveProjection P h₁ h₂ ≫ e.hom) n := by
    infer_instance
  simpa only [e, strictPositiveProjection_comp_iso_hom] using h

/-- The pointwise quotient comparison is induced by the original quotient projection. -/
def positiveImageQuotientHomologyIso (n : ℕ) (hn : n < 2) :
    K₃.homology n ≅ (positiveImageQuotient P h₁ h₂).homology n := by
  letI := positiveImageProjection_quasiIsoAt P h₁ h₂ n hn
  exact _root_.isoOfQuasiIsoAt (positiveImageProjection P h₁ h₂) n

/-- The low-degree comparison retains the actual pointwise projection map. -/
theorem positiveImageQuotientHomologyIso_hom (n : ℕ) (hn : n < 2) :
    (positiveImageQuotientHomologyIso P h₁ h₂ n hn).hom =
      HomologicalComplex.homologyMap (positiveImageProjection P h₁ h₂) n := rfl

end ModulePointwiseQuotient

end HomologicalComplex.ChainGradedPairing
