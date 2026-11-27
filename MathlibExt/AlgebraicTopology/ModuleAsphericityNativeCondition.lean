/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModuleAsphericityHornCorrection
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure

/-!
# Simplicial and additive asphericity of module augmentations

For an augmented simplicial module over a ring `R`, additive asphericity means that
the normalized augmentation is a quasi-isomorphism. This condition is equivalent to
the underlying simplicial-set augmentation being a trivial fibration in the Kan–Quillen
model structure.

Positive-dimensional boundary lifts follow from horn correction and normalized
obstruction fillers; the zero-dimensional lift is degree-zero augmentation surjectivity.
Thus the same condition is recognized by the right lifting property against all boundary
inclusions. The ring and module-carrier universes are independent.

See Loday, §3.5.3, and the Stacks Project, Tag 0194.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

universe u v

namespace AlgebraicTopology.ModuleResolutionAsphericity

variable {R : Type u} [Ring R]
  (P : SimplicialObject.Augmented (ModuleCat.{v} R))

section Aspherical

variable [QuasiIso (augmentation P)]

/--
If the normalized module augmentation is a quasi-isomorphism, its underlying
simplicial-set augmentation has the right lifting property against the boundary
inclusion in every dimension `n`, including zero.
-/
theorem hasLiftingProperty_boundary_of_quasiIso (n : ℕ) :
    HasLiftingProperty (SSet.boundary.{v} n).ι (underlying P).hom := by
  constructor
  intro top bottom sq
  cases n with
  | zero =>
    obtain ⟨x, hx⟩ := original_augmentation_zero_surjective_of_quasiIso P
      (SSet.yonedaEquiv bottom)
    let ψ : (SSet.stdSimplex.obj ⦋0⦌) ⟶ (underlying P).left := SSet.yonedaEquiv.symm x
    have hp : ψ ≫ (underlying P).hom = bottom := by
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp]
      change (P.hom.app (op ⦋0⦌)).hom (SSet.yonedaEquiv ψ) = SSet.yonedaEquiv bottom
      have hψ : SSet.yonedaEquiv ψ = x :=
        (SSet.yonedaEquiv (X := (underlying P).left) (n := ⦋0⦌)).apply_symm_apply _
      exact (congrArg (P.hom.app (op ⦋0⦌)).hom hψ).trans hx
    exact CommSq.HasLift.mk' ⟨ψ, SSet.boundary.hom_ext₀, hp⟩
  | succ n =>
    obtain ⟨ψ, hleft, hright⟩ := exists_original_boundary_lift_of_quasiIso P n top bottom sq
    exact CommSq.HasLift.mk' ⟨ψ, hleft, hright⟩

/--
The underlying augmentation of an additively aspherical simplicial module has the
right lifting property against the Kan–Quillen generating boundary inclusions.
-/
theorem underlying_mem_I_rlp_of_quasiIso :
    SSet.modelCategoryQuillen.I.{v}.rlp (underlying P).hom := by
  rintro _ _ _ ⟨n⟩
  exact hasLiftingProperty_boundary_of_quasiIso P n

/--
If the normalized module augmentation is a quasi-isomorphism, its underlying
simplicial-set augmentation is a trivial fibration.
-/
theorem underlying_trivialFibration_of_quasiIso :
    trivialFibrations SSet.{v} (underlying P).hom := by
  letI : Fibration (underlying P).hom := underlying_module_fibration P
  letI : WeakEquivalence (underlying P).hom :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr
      (SSet.modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences _
        (underlying_mem_I_rlp_of_quasiIso P))
  exact (mem_trivialFibrations_iff _).mpr ⟨inferInstance, inferInstance⟩

end Aspherical

/--
For any augmented simplicial module, the underlying simplicial-set augmentation is
a trivial fibration exactly when its normalized module augmentation is a quasi-isomorphism.
-/
theorem underlying_trivialFibration_iff_additive_asphericity :
    trivialFibrations SSet.{v} (underlying P).hom ↔ QuasiIso (augmentation P) :=
  ⟨augmentation_quasiIso P, fun h => by
    letI : QuasiIso (augmentation P) := h
    exact underlying_trivialFibration_of_quasiIso P⟩

end AlgebraicTopology.ModuleResolutionAsphericity

end
