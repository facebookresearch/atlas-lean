/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.Exactness
public import MathlibExt.Algebra.Lie.UniversalEnveloping.AugmentationIdeal
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoefficientHomologyZero
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Exactness at the enveloping Chevalley–Eilenberg augmentation

Degree-zero coefficient coordinates identify the incoming differential's
image with the augmentation relation span. This span is the augmentation
kernel, and the augmentation is surjective. These endpoint results hold
over any commutative ring. Under `Module.Free R L`, the filtered boundary
construction also gives positive exactness of the enveloping complex.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open scoped TensorProduct

namespace ChevalleyEilenberg

attribute [local instance] rightRegularLieRingModule rightRegularLieModule

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L
local notation:max "C" n:max => ((⋀[R]^n L) ⊗[R] regularCoefficients R L)

/-- The original incoming boundary in the existing ground-ring zero coordinates. -/
def envelopingZeroBoundary : C 1 →ₗ[R] U :=
  (coefficientZeroEquiv R L (regularCoefficients R L)).toLinearMap.comp
    (coefficientDifferential R L (regularCoefficients R L) 0)

theorem envelopingZeroBoundary_ι_tmul (x : L) (u : regularCoefficients R L) :
    envelopingZeroBoundary R L (exteriorPower.ιMulti R 1 (fun _ => x) ⊗ₜ[R] u) =
      u * UniversalEnvelopingAlgebra.ι R x := by
  rw [envelopingZeroBoundary, LinearMap.comp_apply, coefficientDifferential_ι_tmul,
    regularCoefficients_lie]
  let a₀ : ⋀[R]^0 L := exteriorPower.ιMulti R 0 Fin.elim0
  let z : regularCoefficients R L := u * UniversalEnvelopingAlgebra.ι R x
  have hTensor : -(a₀ ⊗ₜ[R] (-z)) = a₀ ⊗ₜ[R] z :=
    (congrArg (fun t : (⋀[R]^0 L) ⊗[R] regularCoefficients R L => -t)
      (TensorProduct.tmul_neg a₀ z)).trans (neg_neg (a₀ ⊗ₜ[R] z))
  change coefficientZeroEquiv R L (regularCoefficients R L) (-(a₀ ⊗ₜ[R] (-z))) = z
  rw [hTensor]
  exact coefficientZeroEquiv_ι_tmul R L (regularCoefficients R L) z

/-- The original incoming differential has exactly the native right-generator image. -/
theorem envelopingZeroBoundary_range :
    LinearMap.range (envelopingZeroBoundary R L) =
      UniversalEnvelopingAlgebra.augmentationSubmodule R L := by
  apply le_antisymm
  · rintro u ⟨p, rfl⟩
    induction p using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact (UniversalEnvelopingAlgebra.augmentationSubmodule R L).zero_mem
    | add p q hp hq =>
        rw [map_add]
        exact (UniversalEnvelopingAlgebra.augmentationSubmodule R L).add_mem hp hq
    | tmul w u =>
        have hw : w = exteriorPower.ιMulti R 1 (fun _ => exteriorPower.oneEquiv R L w) := by
          apply (exteriorPower.oneEquiv R L).injective
          rw [exteriorPower.oneEquiv_ιMulti]
        rw [hw, envelopingZeroBoundary_ι_tmul]
        exact UniversalEnvelopingAlgebra.mul_ι_mem_augmentationSubmodule R L u _
  · apply Submodule.span_le.mpr
    rintro u ⟨⟨v, x⟩, rfl⟩
    exact ⟨exteriorPower.ιMulti R 1 (fun _ => x) ⊗ₜ[R] v,
      envelopingZeroBoundary_ι_tmul R L x v⟩

/-- Ground-ring zero coordinates agree with the already constructed native
left-enveloping zero coordinates on their original carrier. -/
theorem coefficientZeroEquiv_eq_envelopingZeroEquiv (p : C 0) :
    coefficientZeroEquiv R L (regularCoefficients R L) p = envelopingZeroEquiv R L p := by
  induction p using TensorProduct.induction_on with
  | zero =>
      exact ((coefficientZeroEquiv R L (regularCoefficients R L)).map_zero).trans
        ((envelopingZeroEquiv R L).map_zero).symm
  | add p q hp hq =>
      let p₀ : (envelopingComplex R L).X 0 := p
      let q₀ : (envelopingComplex R L).X 0 := q
      exact ((coefficientZeroEquiv R L (regularCoefficients R L)).map_add p q).trans
        ((congrArg₂ (fun x y => x + y) hp hq).trans
          ((envelopingZeroEquiv R L).map_add p₀ q₀).symm)
  | tmul w u =>
      rw [coefficientZeroEquiv, LinearEquiv.trans_apply, LinearEquiv.rTensor_tmul,
        TensorProduct.lid_tmul, envelopingZeroEquiv_tmul]

/-- The augmented native enveloping CE short complex. -/
def envelopingAugmentationShortComplex : ShortComplex (ModuleCat.{max u v} U) :=
  ShortComplex.mk ((envelopingComplex R L).d 1 0)
    (ModuleCat.ofHom (X := (envelopingComplex R L).X 0) (Y := envelopingTrivialObject R L)
      (envelopingAugmentationComponent R L))
    (envelopingAugmentationComponent_boundary R L)

/-- The original augmentation end is exact, with no PBW or freeness premise. -/
theorem envelopingAugmentationShortComplex_exact :
    (envelopingAugmentationShortComplex R L).Exact := by
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  unfold envelopingAugmentationShortComplex
  intro z hz
  change envelopingAugmentationComponent R L z = 0 at hz
  rw [envelopingAugmentationComponent_apply] at hz
  have hzero : UniversalEnvelopingAlgebra.augmentation R L (envelopingZeroEquiv R L z) = 0 :=
    congrArg ULift.down hz
  have hmem : envelopingZeroEquiv R L z ∈
      UniversalEnvelopingAlgebra.augmentationSubmodule R L :=
    (UniversalEnvelopingAlgebra.augmentation_ker_eq_submodule R L).le hzero
  rw [← envelopingZeroBoundary_range R L] at hmem
  obtain ⟨w, hw⟩ := hmem
  refine ⟨w, ?_⟩
  apply (envelopingZeroEquiv R L).injective
  change envelopingZeroEquiv R L
      (coefficientDifferential R L (regularCoefficients R L) 0 w) = envelopingZeroEquiv R L z
  exact (coefficientZeroEquiv_eq_envelopingZeroEquiv R L
    (coefficientDifferential R L (regularCoefficients R L) 0 w)).symm.trans hw

/-- The original augmentation is surjective onto its original lifted scalar carrier. -/
theorem envelopingAugmentationComponent_surjective :
    Function.Surjective (envelopingAugmentationComponent R L) := by
  intro r
  refine ⟨(envelopingZeroEquiv R L).symm (algebraMap R U r.down), ?_⟩
  rw [envelopingAugmentationComponent_apply, LinearEquiv.apply_symm_apply]
  apply ULift.ext
  change UniversalEnvelopingAlgebra.augmentation R L (algebraMap R U r.down) = r.down
  simpa using (UniversalEnvelopingAlgebra.augmentation R L).commutes r.down

instance envelopingAugmentationShortComplex_epi_g :
    Epi (envelopingAugmentationShortComplex R L).g := by
  change Epi (ModuleCat.ofHom (X := (envelopingComplex R L).X 0) (Y := envelopingTrivialObject R L)
    (envelopingAugmentationComponent R L))
  exact (ModuleCat.epi_iff_surjective _).mpr (envelopingAugmentationComponent_surjective R L)

/-- The native successor differential has the existing coefficient value. -/
theorem envelopingComplex_d_succ_apply (n : ℕ) (p : C (n + 1)) :
    ((envelopingComplex R L).d (n + 1) n).hom p =
      coefficientDifferential R L (regularCoefficients R L) n p := by
  unfold envelopingComplex coefficientScalarComplex
  simp only [ChainComplex.of_d]
  change ((coefficientComplex R L (regularCoefficients R L)).d (n + 1) n).hom p = _
  rw [coefficientComplex_d_succ]
  rfl

/-- Positive exactness is exactness of the original native enveloping complex,
retaining the original free-underlying-module hypothesis. -/
theorem envelopingComplex_exactAt_succ [Module.Free R L] (k : ℕ) :
    (envelopingComplex R L).ExactAt (k + 1) := by
  rw [HomologicalComplex.exactAt_iff'
    (K := envelopingComplex R L) (j := k + 1) (i := k + 2) (k := k)
    ((ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel (k + 2) (k + 1) by rfl))
    ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel (k + 1) k by rfl)),
    ShortComplex.moduleCat_exact_iff]
  intro z hz
  let z₀ : (envelopingComplex R L).X (k + 1) := z
  have hz₀ : coefficientDifferential R L (regularCoefficients R L) k z₀ = 0 :=
    (envelopingComplex_d_succ_apply R L k z₀).symm.trans hz
  obtain ⟨w, hw⟩ := enveloping_exact_cycles_of_free R L k z₀ hz₀
  refine ⟨w, ?_⟩
  change ((envelopingComplex R L).d (k + 2) (k + 1)).hom w = z
  exact (envelopingComplex_d_succ_apply R L (k + 1) w).trans hw

end ChevalleyEilenberg
