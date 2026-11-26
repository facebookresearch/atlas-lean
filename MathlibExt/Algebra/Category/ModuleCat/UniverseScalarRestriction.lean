/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.ModuleCat.RingEquivTensorUniverse
public import MathlibExt.Algebra.Category.ModuleCat.Monoidal.Universe
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Monoidal restriction from a lifted scalar ring

Let `R : Type u` be a commutative ring and set `R' = ULift.{v} R : Type (max u v)`. The ring
equivalence `r ↦ up(r)` induces restriction from `R'`-modules to `R`-modules, both with
coefficient carrier universe `max u v`.

Equip the `R`-module category with the universe tensor structure whose unit is `ULift.{v} R`.
The unit comparison retains the lifted scalar value, and the tensor comparison sends `m ⊗[R]
n` to `m ⊗[R'] n`. Together they make scalar restriction strong monoidal. The tensor
comparison also commutes with the symmetric interchange of the two factors. Scalar restriction
is an additive equivalence and preserves homology.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

namespace ModuleCat.UniverseScalarRestriction

variable (R : Type u) [CommRing R]

/-- The scalar ring lifted to the coefficient universe.

For `R : Type u`, this ring is `ULift.{v} R`, with carrier universe `max u v` and ring
operations induced from `R`. -/
abbrev LiftedRing : Type (max u v) := ULift.{v} R

/-- The scalar-module category with a lifted tensor unit.

This is `ModuleCat.{max u v} R`, equipped here with the universe tensor structure whose unit
carrier is `ULift.{v} R`. -/
def Modules := ModuleCat.{max u v} R


/-- The category structure on the universe scalar modules.

Objects are `R`-modules of carrier universe `max u v`, and morphisms are their `R`-linear
maps. -/
instance category : Category (Modules.{u,v} R) := inferInstanceAs (Category (ModuleCat.{max u v} R))
/-- The carrier coercion for universe scalar modules.

An object is regarded as its coefficient type in universe `max u v`. -/
instance coeSort : CoeSort (Modules.{u,v} R) (Type (max u v)) :=
  ⟨fun M => (show ModuleCat.{max u v} R from M).carrier⟩
/-- The additive group of a universe scalar module.

Each coefficient carrier has the additive commutative group structure of its underlying
`R`-module. -/
instance addCommGroup (M : Modules.{u,v} R) : AddCommGroup M :=
  (show ModuleCat.{max u v} R from M).isAddCommGroup
/-- The ground action on a universe scalar module.

Each coefficient carrier has its given module structure over `R`. -/
instance module (M : Modules.{u,v} R) : Module R M :=
  (show ModuleCat.{max u v} R from M).isModule
/-- The concrete structure of the universe scalar-module category.

Categorical morphisms are the underlying `R`-linear maps between coefficient carriers. -/
instance concreteCategory : ConcreteCategory (Modules.{u,v} R) (fun M N => M →ₗ[R] N) :=
  inferInstanceAs (ConcreteCategory (ModuleCat.{max u v} R) (fun M N => M →ₗ[R] N))
/-- The preadditive structure of universe scalar modules.

Morphism spaces have pointwise addition, and composition is additive in both variables. -/
instance preadditive : Preadditive (Modules.{u,v} R) := inferInstanceAs (Preadditive (ModuleCat.{max u v} R))
/-- The abelian category of universe scalar modules.

The category inherits kernels, cokernels, and the abelian category structure of
`ModuleCat.{max u v} R`. -/
instance abelian : Abelian (Modules.{u,v} R) := inferInstanceAs (Abelian (ModuleCat.{max u v} R))
/-- The ground-linear structure of universe scalar modules.

Each morphism space is an `R`-module, and composition is `R`-linear in both variables. -/
instance linear : Linear R (Modules.{u,v} R) :=
  inferInstanceAs (Linear R (ModuleCat.{max u v} R))
/-- The tensor structure with a lifted regular unit.

The tensor of two coefficient modules is their balanced tensor over `R`, and the unit is the
lifted regular module `ULift.{v} R`. -/
instance tensorStructure : MonoidalCategoryStruct (Modules.{u,v} R) :=
  ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
/-- The monoidal structure on universe scalar modules.

Balanced tensor products over `R`, the lifted regular unit, and their associator and unitors
form the universe tensor monoidal category. -/
instance monoidalCategory : MonoidalCategory (Modules.{u,v} R) :=
  ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
/-- Additivity of the universe tensor product.

Tensoring morphisms is additive in each variable for the universe scalar-module category. -/
instance monoidalPreadditive : MonoidalPreadditive (Modules.{u,v} R) :=
  ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
/-- Scalar linearity of the universe tensor product.

Tensoring morphisms is `R`-linear in each variable for the universe scalar-module category. -/
instance monoidalLinear : MonoidalLinear R (Modules.{u,v} R) :=
  ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
/-- The symmetric structure on universe scalar tensors.

The braiding interchanges the factors of a pure tensor: `m ⊗ n ↦ n ⊗ m`. -/
instance symmetricCategory : SymmetricCategory (Modules.{u,v} R) :=
  ModuleCat.UniverseTensor.symmetricCategory.{u,v} (R := R)

/-- The ring equivalence from scalars to lifted scalars.

The equivalence `R ≃+* ULift.{v} R` sends `r` to `ULift.up r` and has inverse `x ↦ x.down`. -/
def scalarEquiv : R ≃+* (LiftedRing.{u,v} R) := (ULift.ringEquiv : (LiftedRing.{u,v} R) ≃+* R).symm

/-- Restriction from lifted scalars to the ground ring.

An `ULift.{v} R`-module becomes an `R`-module by `r • m = (ULift.up r) • m`, retaining its
coefficient carrier and module-map values. -/
def toOriginal : ModuleCat.{max u v} (LiftedRing.{u,v} R) ⥤ (Modules.{u,v} R) := ModuleCat.restrictScalars
  (scalarEquiv.{u,v} R).toRingHom

/-- Additivity of lifted-scalar restriction.

Restriction from `ULift.{v} R` to `R` preserves addition of module morphisms. -/
instance toOriginal_additive : (toOriginal.{u,v} R).Additive where
  map_add := by intros; rfl

/-- The equivalence property of lifted-scalar restriction.

Restriction along `R ≃+* ULift.{v} R` is an equivalence between their module categories in the
common coefficient universe. -/
instance toOriginal_isEquivalence : (toOriginal.{u,v} R).IsEquivalence := by
  unfold toOriginal
  exact ModuleCat.restrictScalars_isEquivalence_of_ringEquiv (scalarEquiv.{u,v} R)

/-- Homology preservation by lifted-scalar restriction.

The additive equivalence from lifted-scalar modules to ground-scalar modules preserves
homology of short complexes. -/
instance toOriginal_preservesHomology : (toOriginal.{u,v} R).PreservesHomology := by
  infer_instance


/-- The unit comparison for lifted-scalar restriction.

The lifted regular unit of the ground-scalar tensor category is isomorphic to the restriction
of the regular unit over `ULift.{v} R`. Both maps retain the lifted scalar value. -/
def unitIso : 𝟙_ (Modules.{u,v} R) ≅
    (toOriginal.{u,v} R).obj (𝟙_ (ModuleCat.{max u v} (LiftedRing.{u,v} R))) := by
  let X : Modules.{u,v} R := 𝟙_ (Modules.{u,v} R)
  let Y : Modules.{u,v} R :=
    (toOriginal.{u,v} R).obj (𝟙_ (ModuleCat.{max u v} (LiftedRing.{u,v} R)))
  let e : X ≃ₗ[R] Y :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by cases x; rfl }
  exact e.toModuleIso

/-- The forward value of the lifted-scalar unit comparison.

For `x ∈ ULift.{v} R`, the forward unit comparison sends `x` to itself. -/
@[simp]
theorem unitIso_hom_value (x : ULift.{v} R) : (unitIso.{u,v} R).hom x = x := rfl

/-- The inverse value of the lifted-scalar unit comparison.

For `x ∈ ULift.{v} R`, the inverse unit comparison sends `x` to itself. -/
@[simp]
theorem unitIso_inv_value (x : ULift.{v} R) : (unitIso.{u,v} R).inv x = x := rfl

/-- The tensor comparison for lifted-scalar restriction.

For modules `M, N` over `R' = ULift.{v} R`, this identifies `Res(M) ⊗[R] Res(N)` with `Res(M
⊗[R'] N)` by retaining both pure-tensor values. -/
def tensorIso (M N : ModuleCat.{max u v} (LiftedRing.{u,v} R)) : (toOriginal.{u,v} R).obj M ⊗
  (toOriginal.{u,v} R).obj N ≅ (toOriginal.{u,v} R).obj (M ⊗ N) :=
  ModuleCat.RingEquivUniverse.tensorIso.{u,max u v,0} (scalarEquiv.{u,v} R) M N

/-- The forward tensor value under lifted-scalar restriction.

The tensor comparison sends `m ⊗ₜ[R] n` to `m ⊗ₜ[ULift.{v} R] n`. -/
@[simp]
theorem tensorIso_hom_tmul (M N : ModuleCat.{max u v} (LiftedRing.{u,v} R))
    (m : (toOriginal.{u,v} R).obj M) (n : (toOriginal.{u,v} R).obj N) :
    (tensorIso.{u,v} R M N).hom (m ⊗ₜ[R] n) = m ⊗ₜ[(LiftedRing.{u,v} R)] n :=
  ModuleCat.RingEquivUniverse.tensorIso_hom_tmul (scalarEquiv.{u,v} R) M N m n

/-- The inverse tensor value under lifted-scalar restriction.

The inverse tensor comparison sends `m ⊗ₜ[ULift.{v} R] n` to the pure `R`-tensor of the same
coefficient elements. -/
@[simp]
theorem tensorIso_inv_tmul (M N : ModuleCat.{max u v} (LiftedRing.{u,v} R)) (m : M) (n : N) :
    (tensorIso.{u,v} R M N).inv (m ⊗ₜ[(LiftedRing.{u,v} R)] n) =
      (show (toOriginal.{u,v} R).obj M from m) ⊗ₜ[R]
        (show (toOriginal.{u,v} R).obj N from n) :=
  ModuleCat.RingEquivUniverse.tensorIso_inv_tmul (scalarEquiv.{u,v} R) M N m n

/-- Naturality of the lifted-scalar tensor comparison.

For module maps `f` and `g` over the lifted ring, tensoring their restrictions over `R` and
then comparing equals comparing first and restricting their tensor map over the lifted ring. -/
@[reassoc]
theorem tensorIso_naturality {M N M' N' : ModuleCat.{max u v} (LiftedRing.{u,v} R)} (f : M ⟶ M') (g : N ⟶ N') :
    ((toOriginal.{u,v} R).map f ⊗ₘ (toOriginal.{u,v} R).map g) ≫ (tensorIso.{u,v} R M' N').hom =
      (tensorIso.{u,v} R M N).hom ≫ (toOriginal.{u,v} R).map (f ⊗ₘ g) :=
  ModuleCat.RingEquivUniverse.tensorIso_naturality (scalarEquiv.{u,v} R) f g

/-- The strong monoidal structure on lifted-scalar restriction.

The unit and balanced-tensor comparisons make restriction from `ULift.{v} R` to `R` a monoidal
functor between the specified module tensor categories. -/
def monoidal : (toOriginal.{u,v} R).Monoidal :=
  (show (toOriginal.{u,v} R).CoreMonoidal from
    { εIso := unitIso.{u,v} R
      μIso := tensorIso.{u,v} R
      μIso_hom_natural_left := fun f M => by
        have ht := congrArg (fun z => (toOriginal.{u,v} R).map f ⊗ₘ z)
          ((toOriginal.{u,v} R).map_id M)
        have hw := ht.trans (tensorHom_id ((toOriginal.{u,v} R).map f)
          ((toOriginal.{u,v} R).obj M))
        exact (congrArg (fun z => z ≫ (tensorIso.{u,v} R _ M).hom) hw).symm.trans
          (tensorIso_naturality.{u,v} R f (𝟙 M))
      μIso_hom_natural_right := fun M f => by
        have ht := congrArg (fun z => z ⊗ₘ (toOriginal.{u,v} R).map f)
          ((toOriginal.{u,v} R).map_id M)
        have hw := ht.trans (id_tensorHom ((toOriginal.{u,v} R).obj M)
          ((toOriginal.{u,v} R).map f))
        exact (congrArg (fun z => z ≫ (tensorIso.{u,v} R M _).hom) hw).symm.trans
          (tensorIso_naturality.{u,v} R (𝟙 M) f)
      associativity := fun M N P => by
        apply ModuleCat.hom_ext
        apply TensorProduct.ext_threefold
        intro m n p
        rfl
      left_unitality := fun M => by
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro r m
        cases r
        rfl
      right_unitality := fun M => by
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro m r
        cases r
        rfl }).toMonoidal

/-- Compatibility of lifted-scalar restriction with tensor interchange.

The tensor comparison commutes with the braidings of the lifted-ring and ground-ring module
tensor categories. -/
@[reassoc]
theorem tensorIso_braiding (M N : ModuleCat.{max u v} (LiftedRing.{u,v} R)) :
    (tensorIso.{u,v} R M N).hom ≫ (toOriginal.{u,v} R).map (β_ M N).hom =
      (β_ ((toOriginal.{u,v} R).obj M) ((toOriginal.{u,v} R).obj N)).hom ≫ (tensorIso.{u,v} R N M).hom := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m n
  rfl

end ModuleCat.UniverseScalarRestriction
