/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.CategoryTheory.Operad.FinBijSmallCoreMonoidal

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped MonoidalCategory

open CategoryTheory.Operad
open CategoryTheory.Operad.SmallFinBijGroupoid

namespace MathlibExtTest.CategoryTheory.Operad.FinBijSmallCoreMonoidal

private def small (n : ℕ) : SmallFinBijGroupoid :=
  ⟨FintypeCat.Skeleton.mk n⟩

section Surface

#check SmallFinBijGroupoid
#check blockSumObj
#check blockSumObj_len
#check blockSumHom
#check blockSumHom_equivOfHom
#check braiding_equivOfHom
#check smallFinBijEquivalence
#check smallFinBijEquivalence_functor_obj
#check smallFinBijEquivalence_functor_map
#check SymmetricCollection.restrictSmall
#check SymmetricCollection.restrictSmall_obj
#check SymmetricCollection.restrictSmall_map
#check SmallFinBijGroupoid.instMonoidalCategory
#check SmallFinBijGroupoid.instSymmetricCategory
#check MonoidalCategory.triangle

end Surface

section Objects

example : (blockSumObj (small 0) (small 0)).of.len = 0 := rfl
example : (blockSumObj (small 0) (small 1)).of.len = 1 := rfl
example : (blockSumObj (small 1) (small 0)).of.len = 1 := rfl

example (m n : ℕ) :
    (blockSumObj (small m) (small n)).of.len = m + n :=
  blockSumObj_len _ _

example : (𝟙_ SmallFinBijGroupoid) = small 0 := rfl

example (X Y : SmallFinBijGroupoid) :
    X ⊗ Y = blockSumObj X Y :=
  rfl

end Objects

section Morphisms

example {X X' Y Y' : SmallFinBijGroupoid}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    f ⊗ₘ g = blockSumHom f g :=
  rfl

example (X Y : SmallFinBijGroupoid) :
    blockSumHom (𝟙 X) (𝟙 Y) = 𝟙 (blockSumObj X Y) := by
  change (𝟙 X ⊗ₘ 𝟙 Y) = 𝟙 (X ⊗ Y)
  exact MonoidalCategory.id_tensorHom_id X Y

example {X X' X'' Y Y' Y'' : SmallFinBijGroupoid}
    (f : X ⟶ X') (f' : X' ⟶ X'')
    (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    blockSumHom f g ≫ blockSumHom f' g' =
      blockSumHom (f ≫ f') (g ≫ g') :=
  MonoidalCategory.tensorHom_comp_tensorHom f g f' g'

example {X X' Y Y' : SmallFinBijGroupoid}
    (f : X ⟶ X') (g : Y ⟶ Y') : True := by
  have _ := blockSumHom_equivOfHom f g
  trivial

end Morphisms

section SymmetryComputations

private abbrev one : SmallFinBijGroupoid := small 1

example :
    FinBijGroupoid.equivOfHom
        (smallFinBijEquivalence.functor.map
          (𝟙 (blockSumObj one one)))
        (ULift.up (0 : Fin 2)) =
      ULift.up (0 : Fin 2) := by
  rw [smallFinBijEquivalence.functor.map_id,
    FinBijGroupoid.equivOfHom_id]
  rfl

example :
    FinBijGroupoid.equivOfHom
        (smallFinBijEquivalence.functor.map
          (𝟙 (blockSumObj one one)))
        (ULift.up (1 : Fin 2)) =
      ULift.up (1 : Fin 2) := by
  rw [smallFinBijEquivalence.functor.map_id,
    FinBijGroupoid.equivOfHom_id]
  rfl

example :
    FinBijGroupoid.equivOfHom
        (smallFinBijEquivalence.functor.map (β_ one one).hom)
        (ULift.up (0 : Fin 2)) =
      ULift.up (1 : Fin 2) := by
  rw [braiding_equivOfHom]
  rfl

example :
    FinBijGroupoid.equivOfHom
        (smallFinBijEquivalence.functor.map (β_ one one).hom)
        (ULift.up (1 : Fin 2)) =
      ULift.up (0 : Fin 2) := by
  rw [braiding_equivOfHom]
  rfl

example (m n : ℕ) (i : Fin m) :
    FinBijGroupoid.equivOfHom
        (smallFinBijEquivalence.functor.map
          (β_ (small m) (small n)).hom)
        (ULift.up (Fin.castAdd n i)) =
      ULift.up (Fin.natAdd n i) := by
  rw [braiding_equivOfHom]
  exact congrArg ULift.up (finAddFlip_apply_castAdd i n)

example (m n : ℕ) (j : Fin n) :
    FinBijGroupoid.equivOfHom
        (smallFinBijEquivalence.functor.map
          (β_ (small m) (small n)).hom)
        (ULift.up (Fin.natAdd m j)) =
      ULift.up (Fin.castAdd m j) := by
  rw [braiding_equivOfHom]
  exact congrArg ULift.up (finAddFlip_apply_natAdd j m)

example (X Y : SmallFinBijGroupoid) :
    (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y) :=
  SymmetricCategory.symmetry X Y

example (X Y : SmallFinBijGroupoid) :
    (α_ X (𝟙_ SmallFinBijGroupoid) Y).hom ≫
        (X ◁ (λ_ Y).hom) =
      ((ρ_ X).hom ▷ Y) :=
  MonoidalCategory.triangle X Y

end SymmetryComputations

section Equivalence

example (X : SmallFinBijGroupoid) :
    (smallFinBijEquivalence.functor.obj X).of =
      FintypeCat.Skeleton.incl.obj X.of :=
  smallFinBijEquivalence_functor_obj X

example {X Y : SmallFinBijGroupoid} (f : X ⟶ Y) :
    (smallFinBijEquivalence.functor.map f).iso =
      FintypeCat.Skeleton.incl.mapIso f.iso :=
  smallFinBijEquivalence_functor_map f

end Equivalence

section Restriction

universe v u

variable {C : Type u} [Category.{v} C]

example (P : SymmetricCollection C) (A : SmallFinBijGroupoid) :
    P.restrictSmall.obj A =
      P.obj (smallFinBijEquivalence.functor.obj A) :=
  SymmetricCollection.restrictSmall_obj P A

example (P : SymmetricCollection C) {A B : SmallFinBijGroupoid}
    (f : A ⟶ B) :
    P.restrictSmall.map f =
      P.map (smallFinBijEquivalence.functor.map f) :=
  SymmetricCollection.restrictSmall_map P f

example (P : SymmetricCollection (Type 1)) :
    P.restrictSmall.obj (small 0) =
      P.obj (smallFinBijEquivalence.functor.obj (small 0)) :=
  SymmetricCollection.restrictSmall_obj P (small 0)

example (P : SymmetricCollection (Type 1)) :
    P.restrictSmall.map (𝟙 (small 0)) =
      P.map (smallFinBijEquivalence.functor.map (𝟙 (small 0))) :=
  SymmetricCollection.restrictSmall_map P (𝟙 (small 0))

example (P : SymmetricCollection Type) :
    P.restrictSmall.obj (small 1) =
      P.obj (smallFinBijEquivalence.functor.obj (small 1)) :=
  SymmetricCollection.restrictSmall_obj P (small 1)

example (P : SymmetricCollection Type) :
    P.restrictSmall.map (𝟙 (small 1)) =
      P.map (smallFinBijEquivalence.functor.map (𝟙 (small 1))) :=
  SymmetricCollection.restrictSmall_map P (𝟙 (small 1))

end Restriction

section SharedImplementation

-- The shared finite-block implementation is part of the public module API.
#check SmallFinBijGroupoid.blockSumEquiv

#check SmallFinBijGroupoid.blockSumEquiv_refl

#check SmallFinBijGroupoid.blockSumEquiv_comp

#check SmallFinBijGroupoid.associatorEquiv

#check SmallFinBijGroupoid.leftUnitorEquiv

#check SmallFinBijGroupoid.braidingEquiv

end SharedImplementation

section RemovedDuplicates

#guard_msgs (error, substring := true) in
#check CategoryTheory.Operad.FinBij

#guard_msgs (error, substring := true) in
#check CategoryTheory.Operad.FinBij.Hom

#guard_msgs (error, substring := true) in
#check CategoryTheory.Operad.FinBij.instCategory

#guard_msgs (error, substring := true) in
#check CategoryTheory.Operad.FinBij.instGroupoid

#guard_msgs (error, substring := true) in
#check CategoryTheory.Operad.FinBij.of

#guard_msgs (error, substring := true) in
#check CategoryTheory.Operad.FinBij.card

#guard_msgs (error, substring := true) in
#check CategoryTheory.Operad.FinBij.skeletonEquivalence

#guard_msgs (error, substring := true) in
#check CategoryTheory.Operad.SymmetricSequence

#guard_msgs (error, substring := true) in
#check SmallFinBijGroupoid.instBraidedCategory

#guard_msgs (error, substring := true) in
#check CategoryTheory.Operad.SmallFinBijGroupoid.dayConvolution

#guard_msgs (error, substring := true) in
#check CategoryTheory.Operad.sphereSequence

#guard_msgs (error, substring := true) in
#check CategoryTheory.Operad.Spectrum

#guard_msgs (error, substring := true) in
#check CategoryTheory.Operad.SmallFinBijGroupoid.modelCategory

#guard_msgs (error, substring := true) in
#check CategoryTheory.Operad.SmallFinBijGroupoid.localization

end RemovedDuplicates

#print axioms SmallFinBijGroupoid.instMonoidalCategory
#print axioms SmallFinBijGroupoid.instSymmetricCategory
#print axioms blockSumHom_equivOfHom
#print axioms braiding_equivOfHom
#print axioms SymmetricCollection.restrictSmall_obj
#print axioms SymmetricCollection.restrictSmall_map

end MathlibExtTest.CategoryTheory.Operad.FinBijSmallCoreMonoidal
