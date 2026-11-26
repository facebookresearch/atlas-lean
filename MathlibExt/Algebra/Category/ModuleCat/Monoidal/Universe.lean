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
# Tensor products in a module category containing the ring unit

For `R : Type u` a commutative ring and any universe `v`, the category `ModuleCat.{max u v} R`
has the scoped symmetric monoidal structure with tensor product `M ⊗[R] N` and tensor unit
`ULift.{v} R`.

The associator sends `(x⊗y)⊗z` to `x⊗(y⊗z)`. The left and right unitors use the down scalar:
`r⊗m ↦ r.down • m` and `m⊗r ↦ r.down • m`. The symmetry flips the two factors.

Whiskering is additive and `R`-linear.

References: Bourbaki, *Algebra*, Chapter III; Mac Lane, *Categories for the Working
Mathematician*, Chapter VII.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u v
namespace ModuleCat.UniverseTensor

variable {R : Type u} [CommRing R]

/-- Let `R : Type u` be a commutative ring, `v` a universe, and `h=max(u,v)`. Equip `ModuleCat.{h}
R` with the scoped tensor structure having tensor product over `R` and unit `ULift.{v} R`.
Tensor morphisms are `TensorProduct.map`, the associator is the tensor associator, and the
unitors identify `ULift R ⊗ M` and `M ⊗ ULift R` with `M` by the down scalar. -/
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

/-- Let `R : Type u` be a commutative ring, `v` a universe, and `h=max(u,v)`. Equip `ModuleCat.{h}
R` with the scoped tensor structure having tensor product over `R` and unit `ULift.{v} R`. The
tensor morphisms, associator and unitors satisfy naturality, pentagon and triangle axioms,
giving `MonoidalCategory (ModuleCat.{h} R)`. -/
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

/-- Let `R : Type u` be a commutative ring, `v` a universe, and `h=max(u,v)`. Equip `ModuleCat.{h}
R` with the scoped tensor structure having tensor product over `R` and unit `ULift.{v} R`. For
`f : K → L` and `g : M → N` in this category, `(f ⊗ₘ g).hom = TensorProduct.map f.hom g.hom`. -/
theorem hom_tensorHom {K L M N : ModuleCat.{max u v} R}
    (f : K ⟶ L) (g : M ⟶ N) :
    (f ⊗ₘ g).hom = TensorProduct.map f.hom g.hom := rfl

/-- Let `R : Type u` be a commutative ring, `v` a universe, and `h=max(u,v)`. Equip `ModuleCat.{h}
R` with the scoped tensor structure having tensor product over `R` and unit `ULift.{v} R`. For
an object `L` and morphism `f : M → N`, `(L ◁ f).hom=f.hom.lTensor L`, namely `id_L ⊗ f`. -/
theorem hom_whiskerLeft (L : ModuleCat.{max u v} R)
    {M N : ModuleCat.{max u v} R} (f : M ⟶ N) :
    (L ◁ f).hom = f.hom.lTensor L := rfl

/-- Let `R : Type u` be a commutative ring, `v` a universe, and `h=max(u,v)`. Equip `ModuleCat.{h}
R` with the scoped tensor structure having tensor product over `R` and unit `ULift.{v} R`. For
a morphism `f : L → M` and object `N`, `(f ▷ N).hom=f.hom.rTensor N`, namely `f ⊗ id_N`. -/
theorem hom_whiskerRight {L M : ModuleCat.{max u v} R}
    (f : L ⟶ M) (N : ModuleCat.{max u v} R) :
    (f ▷ N).hom = f.hom.rTensor N := rfl

/-- Let `R : Type u` be a commutative ring, `v` a universe, and `h=max(u,v)`. Equip `ModuleCat.{h}
R` with the scoped tensor structure having tensor product over `R` and unit `ULift.{v} R`. The
tensor structure is monoidal preadditive: left and right whiskering preserve addition and zero
morphisms. -/
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

/-- Let `R : Type u` be a commutative ring, `v` a universe, and `h=max(u,v)`. Equip `ModuleCat.{h}
R` with the scoped tensor structure having tensor product over `R` and unit `ULift.{v} R`. The
structure is `MonoidalLinear R`: `L ◁ (r • f)=r • (L ◁ f)` and `(r • f) ▷ N=r • (f ▷ N)`. -/
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

/-- Let `R : Type u` be a commutative ring, `v` a universe, and `h=max(u,v)`. Equip `ModuleCat.{h}
R` with the scoped tensor structure having tensor product over `R` and unit `ULift.{v} R`. The
braiding `M⊗N ≃ N⊗M` is `TensorProduct.comm R M N`, with `x⊗y ↦ y⊗x`. It satisfies the hexagon
and symmetry laws. -/
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

/-- Let `R : Type u` be a commutative ring, `v` a universe, and `h=max(u,v)`. Equip `ModuleCat.{h}
R` with the scoped tensor structure having tensor product over `R` and unit `ULift.{v} R`. For
`f : K → L`, `g : M → N`, `x : K`, and `y : M`, `(f ⊗ₘ g)(x⊗y)=f(x)⊗g(y)`. -/
theorem tensorHom_tmul {K L M N : ModuleCat.{max u v} R}
    (f : K ⟶ L) (g : M ⟶ N) (x : K) (y : M) :
    (f ⊗ₘ g) (x ⊗ₜ[R] y) = f x ⊗ₜ[R] g y := rfl

/-- Let `R : Type u` be a commutative ring, `v` a universe, and `h=max(u,v)`. Equip `ModuleCat.{h}
R` with the scoped tensor structure having tensor product over `R` and unit `ULift.{v} R`. For
`M : ModuleCat.{h} R`, `r : ULift.{v} R`, and `m : M`, the left unitor sends `r⊗m` to `r.down
• m`. -/
theorem leftUnitor_tmul (M : ModuleCat.{max u v} R)
    (r : ULift.{v} R) (m : M) : (λ_ M).hom (r ⊗ₜ[R] m) = r.down • m := rfl

/-- Let `R : Type u` be a commutative ring, `v` a universe, and `h=max(u,v)`. Equip `ModuleCat.{h}
R` with the scoped tensor structure having tensor product over `R` and unit `ULift.{v} R`. For
`M : ModuleCat.{h} R`, `m : M`, and `r : ULift.{v} R`, the right unitor sends `m⊗r` to `r.down
• m`. -/
theorem rightUnitor_tmul (M : ModuleCat.{max u v} R)
    (m : M) (r : ULift.{v} R) : (ρ_ M).hom (m ⊗ₜ[R] r) = r.down • m := rfl

end ModuleCat.UniverseTensor
