/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.Algebra.Homology.KoszulComplexFamilyResidue
public import MathlibExt.Algebra.Homology.KoszulComplexFamilyBaseChange
public import MathlibExt.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# A chosen cotangent-basis family

For a Noetherian local ring, choose lifts to the maximal ideal of a basis of
the cotangent space. The resulting finite family spans the maximal ideal and
vanishes in the residue field.

The generic finite-family quotient/residue isomorphism is specialized to the
literal residue-field object by removing its universe lift. The degree-zero
Koszul augmentation followed by this isomorphism becomes bijective after
residue-field base change.

## Main declarations

* `IsLocalRing.cotangentFamily`
* `IsLocalRing.cotangentFamilyEquiv`
* `IsLocalRing.cotangentFamily_span`
* `IsLocalRing.cotangentFamilyResidueIso`
* `IsLocalRing.cotangentFamilyAugmentation_baseChange_bijective`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Function
open CategoryTheory CategoryTheory.Limits

universe u

namespace IsLocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R]
  [IsNoetherianRing R]

/-- A chosen lift to the maximal ideal of a vector in the canonical finite
basis of the cotangent space. -/
noncomputable def cotangentGenerator
    (i : Fin (Module.finrank (ResidueField R) (CotangentSpace R))) :
    maximalIdeal R :=
  Classical.choose ((maximalIdeal R).toCotangent_surjective
    (Module.finBasis (ResidueField R) (CotangentSpace R) i))

/-- The chosen generator maps to the corresponding vector of the canonical
finite cotangent basis. -/
@[simp]
theorem cotangentGenerator_spec
    (i : Fin (Module.finrank (ResidueField R) (CotangentSpace R))) :
    (maximalIdeal R).toCotangent (cotangentGenerator R i) =
      Module.finBasis (ResidueField R) (CotangentSpace R) i :=
  Classical.choose_spec ((maximalIdeal R).toCotangent_surjective
    (Module.finBasis (ResidueField R) (CotangentSpace R) i))

/-- The finite family in the ring obtained from the chosen cotangent-basis
lifts. -/
noncomputable def cotangentFamily :
    Fin (Module.finrank (ResidueField R) (CotangentSpace R)) → R :=
  fun i => cotangentGenerator R i

/-- The standard coordinate space on the cotangent-basis index is linearly
equivalent to the cotangent space. -/
noncomputable def cotangentFamilyEquiv :
    (Fin (Module.finrank (ResidueField R) (CotangentSpace R)) →
        ResidueField R) ≃ₗ[ResidueField R]
      CotangentSpace R :=
  (Pi.basisFun (ResidueField R)
      (Fin (Module.finrank (ResidueField R) (CotangentSpace R)))).equiv
    (Module.finBasis (ResidueField R) (CotangentSpace R)) (Equiv.refl _)

/-- A standard coordinate vector maps to the cotangent class of its chosen
lift. -/
@[simp]
theorem cotangentFamilyEquiv_single
    (i : Fin (Module.finrank (ResidueField R) (CotangentSpace R))) :
    cotangentFamilyEquiv R (Pi.single i 1) =
      (maximalIdeal R).toCotangent (cotangentGenerator R i) := by
  rw [cotangentFamilyEquiv, ← Pi.basisFun_apply,
    Module.Basis.equiv_apply, Equiv.refl_apply,
    ← cotangentGenerator_spec]

/-- The chosen cotangent-basis lifts span the maximal ideal as a module. -/
theorem cotangentGenerator_span :
    Submodule.span R (Set.range (cotangentGenerator R)) = ⊤ := by
  rw [← CotangentSpace.span_image_eq_top_iff]
  have himage :
      (maximalIdeal R).toCotangent '' Set.range (cotangentGenerator R) =
        Set.range
          (Module.finBasis (ResidueField R) (CotangentSpace R)) := by
    ext z
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (cotangentGenerator_spec R i).symm⟩
    · rintro ⟨i, rfl⟩
      exact
        ⟨cotangentGenerator R i, ⟨i, rfl⟩,
          cotangentGenerator_spec R i⟩
  rw [himage]
  exact
    (Module.finBasis (ResidueField R) (CotangentSpace R)).span_eq

/-- The underlying ring-valued cotangent family generates the maximal ideal. -/
theorem cotangentFamily_span :
    Ideal.span (Set.range (cotangentFamily R)) = maximalIdeal R := by
  change Submodule.span R
      (Set.range ((maximalIdeal R).subtype ∘ cotangentGenerator R)) = _
  rw [Set.range_comp, ← Submodule.map_span, cotangentGenerator_span,
    Submodule.map_top, Submodule.range_subtype]

/-- Every member of the chosen family maps to zero in the residue field. -/
@[simp]
theorem cotangentFamily_mapped_residue :
    KoszulComplex.mappedFamily R (ResidueField R) (cotangentFamily R) =
      0 := by
  funext i
  change algebraMap R (ResidueField R) (cotangentGenerator R i) = 0
  rw [ResidueField.algebraMap_eq, residue_eq_zero_iff]
  exact (cotangentGenerator R i).property

omit [IsNoetherianRing R] in
/-- The coefficient functional of a zero finite family is zero. -/
@[simp]
theorem cotangentFamilyFunctional_residue :
    KoszulComplex.familyFunctional (ResidueField R)
      (0 : Fin (Module.finrank (ResidueField R) (CotangentSpace R)) →
        ResidueField R) = 0 := by
  ext f
  simp [KoszulComplex.familyFunctional]

/-- The generic universe-lifted quotient/residue isomorphism specialized to
the chosen family and the literal residue-field object. -/
@[no_expose]
noncomputable def cotangentFamilyResidueIso :
    KoszulComplex.familyAugmentationTarget R (cotangentFamily R) ≅
      ModuleCat.of R (ResidueField R) :=
  (KoszulComplex.familyQuotientResidueIso R (cotangentFamily R)
    (cotangentFamily_span R)).trans ULift.moduleEquiv.toModuleIso

/-- On quotient representatives, the specialized residue isomorphism is the
residue map. -/
@[simp]
theorem cotangentFamilyResidueIso_hom_up_mk (r : R) :
    (cotangentFamilyResidueIso R).hom.hom
        (ULift.up (Ideal.Quotient.mk
          (KoszulComplex.ideal R
            (Fin (Module.finrank (ResidueField R) (CotangentSpace R)) → R)
            (KoszulComplex.familyFunctional R (cotangentFamily R))) r)) =
      residue R r := by
  change ULift.down
      ((KoszulComplex.familyQuotientResidueIso R
        (cotangentFamily R) (cotangentFamily_span R)).hom.hom
          (ULift.up (Ideal.Quotient.mk _ r))) = _
  rw [KoszulComplex.familyQuotientResidueIso_hom_up_mk]

/-- The degree-zero Koszul augmentation followed by the specialized residue
isomorphism becomes bijective after residue-field base change. -/
theorem cotangentFamilyAugmentation_baseChange_bijective :
    Function.Bijective
      (((KoszulComplex.augmentation R
          (Fin (Module.finrank (ResidueField R) (CotangentSpace R)) → R)
          (KoszulComplex.familyFunctional R (cotangentFamily R))).f 0 ≫
        (cotangentFamilyResidueIso R).hom).hom.baseChange
          (ResidueField R)) := by
  rw [KoszulComplex.augmentation_f_zero]
  let M :=
    Fin (Module.finrank (ResidueField R) (CotangentSpace R)) → R
  let x := KoszulComplex.familyFunctional R (cotangentFamily R)
  let aug := KoszulComplex.augmentationLinearLifted R M x
  let q := (cotangentFamilyResidueIso R).hom.hom
  let g : (⋀[R]^0 M) →ₗ[R] ResidueField R := q.comp aug
  change Function.Bijective (g.baseChange (ResidueField R))
  have hq_surj : Function.Surjective q := by
    intro y
    refine ⟨(cotangentFamilyResidueIso R).inv.hom y, ?_⟩
    exact (cotangentFamilyResidueIso R).inv_hom_id_apply y
  have hq_inj : Function.Injective q := by
    exact
      (ModuleCat.mono_iff_injective
        (cotangentFamilyResidueIso R).hom).mp inferInstance
  have haug_surj : Function.Surjective aug :=
    KoszulComplex.augmentationLinearLifted_surjective R M x
  have hg_surj : Function.Surjective g :=
    hq_surj.comp haug_surj
  have hxrange : LinearMap.range x = maximalIdeal R :=
    KoszulComplex.familyIdeal_eq_maximalIdeal R (cotangentFamily R)
      (cotangentFamily_span R)
  have hd_range :
      LinearMap.range (KoszulComplex.differential R M x 0) ≤
        maximalIdeal R • (⊤ : Submodule R (⋀[R]^0 M)) := by
    rintro _ ⟨z, rfl⟩
    let r : R := x ((exteriorPower.oneEquiv R M) z)
    have hr : r ∈ maximalIdeal R := by
      rw [← hxrange]
      exact LinearMap.mem_range_self x ((exteriorPower.oneEquiv R M) z)
    have hdeg :=
      LinearMap.congr_fun
        (KoszulComplex.differential_zero_equiv R M x) z
    change (exteriorPower.zeroEquiv R M)
        (KoszulComplex.differential R M x 0 z) =
      x ((exteriorPower.oneEquiv R M) z) at hdeg
    have hd_eq :
        KoszulComplex.differential R M x 0 z =
          r • (exteriorPower.zeroEquiv R M).symm 1 := by
      apply (exteriorPower.zeroEquiv R M).injective
      rw [map_smul, LinearEquiv.apply_symm_apply]
      simpa only [smul_eq_mul, mul_one, r] using hdeg
    rw [hd_eq]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  have hg_ker :
      LinearMap.ker g ≤
        maximalIdeal R • (⊤ : Submodule R (⋀[R]^0 M)) := by
    intro z hz
    have haug_zero : aug z = 0 := by
      apply hq_inj
      have hz0 := LinearMap.mem_ker.mp hz
      change q (aug z) = 0 at hz0
      simpa using hz0
    have hker_range :
        LinearMap.ker aug ≤
          LinearMap.range (KoszulComplex.differential R M x 0) :=
      (ShortComplex.moduleCat_exact_iff_ker_sub_range
        (KoszulComplex.augmentationShortComplex R M x)).mp
          (KoszulComplex.augmentation_exact_zero R M x)
    exact hd_range (hker_range (LinearMap.mem_ker.mpr haug_zero))
  constructor
  · exact
      (LinearMap.ker_le_ideal_smul_top_iff_baseChange_quotient_injective
        (maximalIdeal R) g hg_surj).mp hg_ker
  · exact LinearMap.baseChange_surjective (ResidueField R) hg_surj

end IsLocalRing
