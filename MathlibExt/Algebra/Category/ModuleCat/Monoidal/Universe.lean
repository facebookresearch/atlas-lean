/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Flat.Basic

/-!
# Tensor products in module categories with larger universes

The tensor product on modules over a commutative ring uses the native tensor
maps, associator and braiding. Its unit is the ring lifted to the module
universe; the unitors combine the lift equivalence with the tensor unitors.
The instances are scoped, and the equal-universe structure is identified
explicitly with the existing module-category structure.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u v
namespace ModuleCat.UniverseTensor

variable {R : Type u} [CommRing R]

/-- The original native tensor structure on the larger module carriers. -/
scoped instance tensorStructure : MonoidalCategoryStruct (ModuleCat.{max u v} R) where
  tensorObj M N := ModuleCat.of R (TensorProduct R M N)
  whiskerLeft M _ _ f := ModuleCat.ofHom (f.hom.lTensor M)
  whiskerRight f M := ModuleCat.ofHom (f.hom.rTensor M)
  tensorHom f g := ModuleCat.ofHom (TensorProduct.map f.hom g.hom)
  tensorUnit := ModuleCat.of R (ULift.{v} R)
  associator M N K := (TensorProduct.assoc R M N K).toModuleIso
  leftUnitor M := ((TensorProduct.congr
    (ULift.moduleEquiv : ULift.{v} R ≃ₗ[R] R) (LinearEquiv.refl R M)) ≪≫ₗ
      TensorProduct.lid R M).toModuleIso
  rightUnitor M := ((TensorProduct.congr (LinearEquiv.refl R M)
    (ULift.moduleEquiv : ULift.{v} R ≃ₗ[R] R)) ≪≫ₗ TensorProduct.rid R M).toModuleIso

open scoped ModuleCat.UniverseTensor

/-- The canonical native tensor maps satisfy the monoidal axioms in the
original ring and the larger coefficient category. -/
scoped instance monoidalCategory : MonoidalCategory (ModuleCat.{max u v} R) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun M N => by
      apply ModuleCat.hom_ext
      exact TensorProduct.ext rfl)
    (tensorHom_comp_tensorHom := fun f g h k => by
      apply ModuleCat.hom_ext
      exact TensorProduct.ext rfl)
    (associator_naturality := fun f g h => by
      apply ModuleCat.hom_ext
      apply TensorProduct.ext_threefold
      intro x y z
      rfl)
    (leftUnitor_naturality := fun f => by
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      apply LinearMap.ext
      intro r
      apply LinearMap.ext
      intro x
      exact (f.hom.map_smul r.down x).symm)
    (rightUnitor_naturality := fun f => by
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro r
      exact (f.hom.map_smul r.down x).symm)
    (pentagon := fun W X Y Z => by
      apply ModuleCat.hom_ext
      apply TensorProduct.ext_fourfold
      intro w x y z
      rfl)
    (triangle := fun M N => by
      apply ModuleCat.hom_ext
      apply TensorProduct.ext_threefold
      intro m r n
      exact TensorProduct.tmul_smul r.down m n)

/-- The actual tensor morphism is the original native tensor linear map. -/
theorem hom_tensorHom {K L M N : ModuleCat.{max u v} R}
    (f : K ⟶ L) (g : M ⟶ N) :
    (f ⊗ₘ g).hom = TensorProduct.map f.hom g.hom := rfl

/-- The actual left whiskering is the original tensor linear map. -/
theorem hom_whiskerLeft (L : ModuleCat.{max u v} R)
    {M N : ModuleCat.{max u v} R} (f : M ⟶ N) :
    (L ◁ f).hom = f.hom.lTensor L := rfl

/-- The actual right whiskering is the original tensor linear map. -/
theorem hom_whiskerRight {L M : ModuleCat.{max u v} R}
    (f : L ⟶ M) (N : ModuleCat.{max u v} R) :
    (f ▷ N).hom = f.hom.rTensor N := rfl

/-- The canonical tensor remains additive on the original modules. -/
scoped instance monoidalPreadditive : MonoidalPreadditive (ModuleCat.{max u v} R) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intros
    apply ModuleCat.hom_ext
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp [hom_whiskerLeft]
  · intros
    apply ModuleCat.hom_ext
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp [hom_whiskerRight]
  · intros
    apply ModuleCat.hom_ext
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp [hom_whiskerLeft]
  · intros
    apply ModuleCat.hom_ext
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp [hom_whiskerRight]

/-- The canonical tensor is linear over the original ring. -/
scoped instance monoidalLinear : MonoidalLinear R (ModuleCat.{max u v} R) := by
  refine ⟨?_, ?_⟩
  · intros
    apply ModuleCat.hom_ext
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp [hom_whiskerLeft]
  · intros
    apply ModuleCat.hom_ext
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp [hom_whiskerRight]

/-- The original native tensor commutation is the braiding in the larger
coefficient universe. -/
scoped instance symmetricCategory : SymmetricCategory (ModuleCat.{max u v} R) where
  braiding M N := (TensorProduct.comm R M N).toModuleIso
  braiding_naturality_left := by
    intros
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    rfl
  braiding_naturality_right := by
    intros
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    rfl
  hexagon_forward := by
    intros
    apply ModuleCat.hom_ext
    apply TensorProduct.ext_threefold
    intros
    rfl
  hexagon_reverse := by
    intro X Y Z
    apply (cancel_epi (α_ X Y Z).hom).mp
    apply ModuleCat.hom_ext
    apply TensorProduct.ext_threefold
    intros
    rfl
  symmetry := by
    intros
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    rfl

/-- The larger coefficient category keeps the original ring tensor
linear map on every pair of original modules. -/
theorem tensorHom_tmul {K L M N : ModuleCat.{max u v} R}
    (f : K ⟶ L) (g : M ⟶ N) (x : K) (y : M) :
    (f ⊗ₘ g) (x ⊗ₜ[R] y) = f x ⊗ₜ[R] g y := rfl

/-- The actual left unitor uses only the canonical down scalar. -/
theorem leftUnitor_tmul (M : ModuleCat.{max u v} R)
    (r : ULift.{v} R) (m : M) : (λ_ M).hom (r ⊗ₜ[R] m) = r.down • m := rfl

/-- The actual right unitor uses only the canonical down scalar. -/
theorem rightUnitor_tmul (M : ModuleCat.{max u v} R)
    (m : M) (r : ULift.{v} R) : (ρ_ M).hom (m ⊗ₜ[R] r) = r.down • m := rfl

end ModuleCat.UniverseTensor
