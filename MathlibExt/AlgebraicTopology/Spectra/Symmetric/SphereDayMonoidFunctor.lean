/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.SphereDayMonoid

/-!
# Functoriality of the generic sphere Day monoid

Every map of stabilizing objects gives its tensor-power map at every level.
These maps respect all finite bijections and the same Day unit and multiplication.
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

/-- A finite coordinate equivalence acts by its actual tensor permutation. -/
theorem genericSphereSequence_finite_permutation (T : V) {m n : ℕ}
    (e : Fin m ≃ Fin n) :
    (genericSphereSequence T).functor.map
      (Operad.SmallFinBijGroupoid.mkCoreIso
        (X := Operad.SmallFinBijGroupoid.card m)
        (Y := Operad.SmallFinBijGroupoid.card n)
        (Equiv.ulift.trans (e.trans Equiv.ulift.symm))).hom =
      (permutationIso T e).hom := by
  rw [genericSphereSequence_map]
  have h : Operad.SmallFinBijGroupoid.smallEquivOfHom
      (Operad.SmallFinBijGroupoid.mkCoreIso
        (X := Operad.SmallFinBijGroupoid.card m)
        (Y := Operad.SmallFinBijGroupoid.card n)
        (Equiv.ulift.trans (e.trans Equiv.ulift.symm))).hom = e := by
    ext z
    rfl
  rw [h]
  rfl

/-- The actual levelwise tensor-power map induced by every stabilizing-object map. -/
def genericSphereSequenceMap {T U : V} (f : T ⟶ U) :
    genericSphereSequence T ⟶ genericSphereSequence U where
  natTrans :=
    { app A := tensorPowMap f A.of.len
      naturality := by
        intro A B g
        exact (permutationIso_hom_naturality f
          (Operad.SmallFinBijGroupoid.smallEquivOfHom g)).symm }

/-- Every component is the full original tensor-power map. -/
theorem genericSphereSequenceMap_app {T U : V} (f : T ⟶ U) (A : I) :
    (genericSphereSequenceMap f).natTrans.app A = tensorPowMap f A.of.len := rfl

/-- All finite bijections commute with every map of stabilizing objects. -/
theorem genericSphereSequenceMap_natural {T U : V} (f : T ⟶ U)
    {A B : I} (g : A ⟶ B) :
    (genericSphereSequence T).functor.map g ≫ tensorPowMap f B.of.len =
      tensorPowMap f A.of.len ≫ (genericSphereSequence U).functor.map g :=
  (genericSphereSequenceMap f).natTrans.naturality g

omit [SymmetricCategory V] in
/-- Both original block comparisons commute with every stabilizing-object map. -/
theorem genericSphereSequenceMap_block {T U : V} (f : T ⟶ U) (p q : ℕ) :
    (tensorPowObj_add T p q).inv ≫ tensorPowMap f (p + q) =
      (tensorPowMap f p ⊗ₘ tensorPowMap f q) ≫ (tensorPowObj_add U p q).inv := by
  apply (cancel_mono (tensorPowObj_add U p q).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [tensorPowObj_add_naturality]
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The whole sphere-sequence map preserves every identity. -/
theorem genericSphereSequenceMap_id (T : V) :
    genericSphereSequenceMap (𝟙 T) = 𝟙 (genericSphereSequence T) := by
  apply DayFunctor.hom_ext
  apply NatTrans.ext
  funext A
  exact tensorPowMap_id T A.of.len

/-- The whole sphere-sequence map preserves every composite. -/
theorem genericSphereSequenceMap_comp {T U W : V} (f : T ⟶ U) (g : U ⟶ W) :
    genericSphereSequenceMap (f ≫ g) = genericSphereSequenceMap f ≫ genericSphereSequenceMap g := by
  apply DayFunctor.hom_ext
  apply NatTrans.ext
  funext A
  exact tensorPowMap_comp f g A.of.len

variable [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- Every stabilizing-object map gives a genuine map of the actual sphere Day monoids. -/
def genericSphereDayMonoidMap {T U : V} (f : T ⟶ U) :
    genericSphereDayMonoid T ⟶ genericSphereDayMonoid U :=
  Operad.SmallFinBijGroupoid.SymmetricTensorAlgebra.freeMap f

/-- The actual monoid map has the original full tensor-power component in every arity. -/
theorem genericSphereDayMonoidMap_app {T U : V} (f : T ⟶ U) (A : I) :
    (genericSphereDayMonoidMap f).hom.hom.natTrans.app A = tensorPowMap f A.of.len :=
  Operad.SmallFinBijGroupoid.SymmetricTensorAlgebra.freeMap_app f A

/-- The map on the actual sphere Day monoids preserves every identity. -/
theorem genericSphereDayMonoidMap_id (T : V) :
    genericSphereDayMonoidMap (𝟙 T) = 𝟙 (genericSphereDayMonoid T) :=
  Operad.SmallFinBijGroupoid.SymmetricTensorAlgebra.freeMap_id T

/-- The map on the actual sphere Day monoids preserves every composite. -/
theorem genericSphereDayMonoidMap_comp {T U W : V} (f : T ⟶ U) (g : U ⟶ W) :
    genericSphereDayMonoidMap (f ≫ g) =
      genericSphereDayMonoidMap f ≫ genericSphereDayMonoidMap g :=
  Operad.SmallFinBijGroupoid.SymmetricTensorAlgebra.freeMap_comp f g

/-- The complete sphere Day monoid construction is functorial in the stabilizing object. -/
def genericSphereDayMonoidFunctor : V ⥤ CommMon (DayFunctor I V) :=
  Operad.SmallFinBijGroupoid.SymmetricTensorAlgebra.freeFunctor

end CategoryTheory
