/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Operad.FinBijDegreeInclusion
public import MathlibExt.CategoryTheory.Operad.FinBijTensorPower
public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.SymmetricTensorAlgebra

/-!
# The sphere Day monoid for an arbitrary stabilizing object

The sphere sequence of `T` has its actual ordered tensor powers as values.
Every finite bijection acts by the corresponding permutation of tensor factors.
The block tensorator and the tensor unit give a commutative Day monoid.

Only small colimits and their preservation by the two tensor functors enter
the Day construction. No cofibrancy or model structure is used here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.TensorPower
open CategoryTheory.MonoidalCategory.SymmetricTensorPower
open scoped ExternalProduct CategoryTheory.MonObj

namespace CategoryTheory

local notation "I" => Operad.SmallFinBijGroupoid

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]

attribute [local instance] Operad.SmallFinBijGroupoid.tensorPowerFunctorBraided

/-- The symmetric sequence of all ordered tensor powers of `T`. -/
def genericSphereSequence (T : V) : DayFunctor I V :=
  DayFunctor.mk (Operad.SmallFinBijGroupoid.tensorPowerFunctor T)

/-- Every level is the original tensor power, including level zero. -/
@[simp]
theorem genericSphereSequence_obj (T : V) (A : I) :
    (genericSphereSequence T).functor.obj A = tensorPowObj T A.of.len := rfl

/-- The actual degree-zero value is the selected tensor unit. -/
theorem genericSphereSequence_zero (T : V) :
    (genericSphereSequence T).functor.obj (𝟙_ I) = 𝟙_ V := rfl

/-- Every finite bijection acts by the full original tensor permutation. -/
theorem genericSphereSequence_map (T : V) {A B : I} (f : A ⟶ B) :
    (genericSphereSequence T).functor.map f =
      (permutationIso T (Operad.SmallFinBijGroupoid.smallEquivOfHom f)).hom := rfl

/-- Every finite identity acts by the identity of its whole tensor power. -/
theorem genericSphereSequence_map_id (T : V) (A : I) :
    (genericSphereSequence T).functor.map (𝟙 A) =
      𝟙 ((genericSphereSequence T).functor.obj A) :=
  (genericSphereSequence T).functor.map_id A

/-- All finite bijections compose in the source-first order. -/
theorem genericSphereSequence_map_comp (T : V) {A B C : I}
    (f : A ⟶ B) (g : B ⟶ C) :
    (genericSphereSequence T).functor.map (f ≫ g) =
      (genericSphereSequence T).functor.map f ≫
        (genericSphereSequence T).functor.map g :=
  (genericSphereSequence T).functor.map_comp f g

/-- The tensorator joins the two original ordered blocks. -/
theorem genericSphereSequence_tensorator (T : V) (A B : I) :
    Functor.LaxMonoidal.μ (Operad.SmallFinBijGroupoid.tensorPowerFunctor T) A B =
      (tensorPowObj_add T A.of.len B.of.len).inv := rfl

/-- Block multiplication is natural in both complete finite bijections. -/
theorem genericSphereSequence_block_natural (T : V) {A A' B B' : I}
    (f : A ⟶ A') (g : B ⟶ B') :
    ((genericSphereSequence T).functor.map f ⊗ₘ
        (genericSphereSequence T).functor.map g) ≫
      (tensorPowObj_add T A'.of.len B'.of.len).inv =
    (tensorPowObj_add T A.of.len B.of.len).inv ≫
      (genericSphereSequence T).functor.map (f ⊗ₘ g) :=
  Functor.LaxMonoidal.μ_natural
    (Operad.SmallFinBijGroupoid.tensorPowerFunctor T) f g

/-- All three blocks associate through the original value and index associators. -/
theorem genericSphereSequence_block_assoc (T : V) (A B C : I) :
    (tensorPowObj_add T A.of.len B.of.len).inv ▷ tensorPowObj T C.of.len ≫
      (tensorPowObj_add T (A ⊗ B).of.len C.of.len).inv ≫
      (genericSphereSequence T).functor.map (α_ A B C).hom =
    (α_ (tensorPowObj T A.of.len) (tensorPowObj T B.of.len)
      (tensorPowObj T C.of.len)).hom ≫
      tensorPowObj T A.of.len ◁ (tensorPowObj_add T B.of.len C.of.len).inv ≫
      (tensorPowObj_add T A.of.len (B ⊗ C).of.len).inv :=
  Functor.LaxMonoidal.associativity
    (Operad.SmallFinBijGroupoid.tensorPowerFunctor T) A B C

/-- The empty left block acts through the actual left unitor. -/
theorem genericSphereSequence_block_unit_left (T : V) (A : I) :
    (tensorPowObj_add T 0 A.of.len).inv ≫
      (genericSphereSequence T).functor.map (λ_ A).hom =
      (λ_ (tensorPowObj T A.of.len)).hom := by
  have h := Functor.LaxMonoidal.left_unitality
    (Operad.SmallFinBijGroupoid.tensorPowerFunctor T) A
  change (λ_ (tensorPowObj T A.of.len)).hom =
    𝟙 (𝟙_ V) ▷ tensorPowObj T A.of.len ≫
      (tensorPowObj_add T 0 A.of.len).inv ≫
      (genericSphereSequence T).functor.map (λ_ A).hom at h
  simpa only [tensorPowObj_zero, genericSphereSequence_obj,
    id_whiskerRight, Category.id_comp] using h.symm

/-- The empty right block acts through the actual right unitor. -/
theorem genericSphereSequence_block_unit_right (T : V) (A : I) :
    (tensorPowObj_add T A.of.len 0).inv ≫
      (genericSphereSequence T).functor.map (ρ_ A).hom =
      (ρ_ (tensorPowObj T A.of.len)).hom := by
  have h := Functor.LaxMonoidal.right_unitality
    (Operad.SmallFinBijGroupoid.tensorPowerFunctor T) A
  change (ρ_ (tensorPowObj T A.of.len)).hom =
    tensorPowObj T A.of.len ◁ 𝟙 (𝟙_ V) ≫
      (tensorPowObj_add T A.of.len 0).inv ≫
      (genericSphereSequence T).functor.map (ρ_ A).hom at h
  simpa only [tensorPowObj_zero, genericSphereSequence_obj,
    whiskerLeft_id, Category.id_comp] using h.symm

/-- The complete block swap is the value braiding followed by the same block join. -/
theorem genericSphereSequence_block_braiding (T : V) (A B : I) :
    (tensorPowObj_add T A.of.len B.of.len).inv ≫
      (genericSphereSequence T).functor.map (β_ A B).hom =
    (β_ (tensorPowObj T A.of.len) (tensorPowObj T B.of.len)).hom ≫
      (tensorPowObj_add T B.of.len A.of.len).inv :=
  Functor.LaxBraided.braided
    (F := Operad.SmallFinBijGroupoid.tensorPowerFunctor T) A B

variable [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The actual commutative sphere Day monoid `S(T)` on the full tensor-power sequence. -/
def genericSphereDayMonoid (T : V) : CommMon (DayFunctor I V) :=
  Operad.SmallFinBijGroupoid.SymmetricTensorAlgebra.freeMonoid T

/-- The monoid carrier is precisely the same full tensor-power sequence. -/
@[simp]
theorem genericSphereDayMonoid_carrier (T : V) :
    (genericSphereDayMonoid T).X = genericSphereSequence T := rfl

/-- The selected Day unit descends from the identity on the actual tensor unit. -/
theorem genericSphereDayMonoid_unit (T : V) :
    DayFunctor.ν I V ≫ (genericSphereDayMonoid T).mon.one.natTrans.app (𝟙_ I) =
      𝟙 (𝟙_ V) :=
  DayFunctor.monObjOfLaxMonoidal_one_app
    (Operad.SmallFinBijGroupoid.tensorPowerFunctor T)

/-- Every Day generator product is the original whole ordered block tensorator. -/
theorem genericSphereDayMonoid_multiplication (T : V) (A B : I) :
    (DayFunctor.η (genericSphereDayMonoid T).X (genericSphereDayMonoid T).X).app (A, B) ≫
      (genericSphereDayMonoid T).mon.mul.natTrans.app (A ⊗ B) =
    (tensorPowObj_add T A.of.len B.of.len).inv :=
  DayFunctor.monObjOfLaxMonoidal_mul_app
    (Operad.SmallFinBijGroupoid.tensorPowerFunctor T) A B

/-- Every labelled Day product retains the whole finite output bijection. -/
theorem genericSphereDayMonoid_labelled_multiplication (T : V) (A B : I)
    {C : I} (f : A ⊗ B ⟶ C) :
    (DayFunctor.η (genericSphereDayMonoid T).X (genericSphereDayMonoid T).X).app (A, B) ≫
      ((genericSphereDayMonoid T).X ⊗ (genericSphereDayMonoid T).X).functor.map f ≫
      (genericSphereDayMonoid T).mon.mul.natTrans.app C =
    (tensorPowObj_add T A.of.len B.of.len).inv ≫
      (permutationIso T (Operad.SmallFinBijGroupoid.smallEquivOfHom f)).hom := by
  rw [(genericSphereDayMonoid T).mon.mul.natTrans.naturality f]
  rw [← Category.assoc, genericSphereDayMonoid_multiplication]
  rfl

/-- The full selected Day multiplication has the original left unit law. -/
theorem genericSphereDayMonoid_one_mul (T : V) :
    (genericSphereDayMonoid T).mon.one ▷ (genericSphereDayMonoid T).X ≫
      (genericSphereDayMonoid T).mon.mul =
      (λ_ (genericSphereDayMonoid T).X).hom :=
  (genericSphereDayMonoid T).mon.one_mul

/-- The full selected Day multiplication has the original right unit law. -/
theorem genericSphereDayMonoid_mul_one (T : V) :
    (genericSphereDayMonoid T).X ◁ (genericSphereDayMonoid T).mon.one ≫
      (genericSphereDayMonoid T).mon.mul =
      (ρ_ (genericSphereDayMonoid T).X).hom :=
  (genericSphereDayMonoid T).mon.mul_one

/-- The full selected Day multiplication has the original associativity law. -/
theorem genericSphereDayMonoid_mul_assoc (T : V) :
    (genericSphereDayMonoid T).mon.mul ▷ (genericSphereDayMonoid T).X ≫
      (genericSphereDayMonoid T).mon.mul =
    (α_ (genericSphereDayMonoid T).X (genericSphereDayMonoid T).X
      (genericSphereDayMonoid T).X).hom ≫
      (genericSphereDayMonoid T).X ◁ (genericSphereDayMonoid T).mon.mul ≫
      (genericSphereDayMonoid T).mon.mul :=
  (genericSphereDayMonoid T).mon.mul_assoc

/-- The selected Day braiding leaves the same full multiplication unchanged. -/
theorem genericSphereDayMonoid_mul_comm (T : V) :
    (β_ (genericSphereDayMonoid T).X (genericSphereDayMonoid T).X).hom ≫
      (genericSphereDayMonoid T).mon.mul =
      (genericSphereDayMonoid T).mon.mul :=
  DayFunctor.mul_comm (Operad.SmallFinBijGroupoid.tensorPowerFunctor T)

end CategoryTheory
