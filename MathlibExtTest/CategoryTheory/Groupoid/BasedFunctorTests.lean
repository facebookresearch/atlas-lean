/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.CategoryTheory.Groupoid.BasedFunctor
import Mathlib.CategoryTheory.Sums.Basic
import Mathlib.GroupTheory.Perm.Basic

/-!
# A nontrivial based functor with an unreachable component

Use the stock categorical sum of two permutation groupoids. The left
inclusion identifies the original based End group with the noncommutative
permutation group, while arrows in the separate right component have value one.
-/

set_option autoImplicit false

open CategoryTheory

noncomputable section

namespace MathlibExtTest.BasedFunctorTests

private abbrev Perm := Equiv.Perm (Fin 3)
private abbrev C := SingleObj Perm ⊕ SingleObj Perm
private abbrev base : C := Sum.inl (SingleObj.star Perm)

-- The category and all its arrows are the stock sum. Promote it using the
-- stock constructor and isomorphism preservation by the two stock inclusions.
private noncomputable instance : Groupoid C :=
  Groupoid.ofIsIso (fun {_ _} f => by
    exact Sum.homInduction
      (P := fun {_ _} g => IsIso g)
      (inl := fun _ _ g =>
        Functor.map_isIso (Sum.inl_ (SingleObj Perm) (SingleObj Perm)) g)
      (inr := fun _ _ g =>
        Functor.map_isIso (Sum.inr_ (SingleObj Perm) (SingleObj Perm)) g) f)

private def leftFullyFaithful : (Sum.inl_ (SingleObj Perm) (SingleObj Perm)).FullyFaithful where
  preimage f := f.down
  map_preimage f := by cases f; rfl
  preimage_map _ := rfl

private def leftEnd : Perm ≃* End base :=
  (SingleObj.toEnd Perm).trans
    (leftFullyFaithful.mulEquivEnd (SingleObj.star Perm))

private def originalHom : End base →* Perm := leftEnd.symm.toMonoidHom

private def client : C ⥤ SingleObj Perm :=
  Groupoid.basedFunctor base originalHom

-- Fix the declared value carrier before permutation application and typeclass synthesis.
private def mapValue {a b : C} (f : a ⟶ b) : Perm := client.map f

private theorem mapValue_comp {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    mapValue (f ≫ g) = mapValue g * mapValue f := by
  exact (client.map_comp f g).trans
    (SingleObj.comp_as_mul (M := Perm) (client.map f) (client.map g))

private theorem client_leftEnd (p : Perm) : mapValue (leftEnd p).asHom = p :=
  (Groupoid.basedFunctor_map_end base originalHom (leftEnd p)).trans
    (leftEnd.symm_apply_apply p)

-- Exact recovery of the original, concretely constructed based homomorphism.
example :
    (SingleObj.toEnd Perm).symm.toMonoidHom.comp (client.mapEnd base) = originalHom :=
  Groupoid.basedFunctor_mapEnd base originalHom

-- The chosen original homomorphism really is nontrivial.
example : originalHom (leftEnd (Equiv.swap (0 : Fin 3) 1)) ≠ 1 := by
  have hp : originalHom (leftEnd (Equiv.swap (0 : Fin 3) 1)) =
      Equiv.swap (0 : Fin 3) 1 := leftEnd.symm_apply_apply _
  rw [hp]
  intro h
  have h0 := congrArg (fun p : Perm => p (0 : Fin 3)) h
  exact (by decide : (Equiv.swap (0 : Fin 3) 1) 0 ≠ (1 : Perm) 0) h0

-- At the original basepoint the nonidentity transposition retains its value.
example : (mapValue (leftEnd (Equiv.swap (0 : Fin 3) 1)).asHom) (0 : Fin 3) = 1 := by
  rw [client_leftEnd]
  decide

-- SingleObj and End both reverse categorical composition: the first edge
-- followed by the second has value swap12 * swap01, and moves zero to two.
example :
    (mapValue ((leftEnd (Equiv.swap (0 : Fin 3) 1)).asHom ≫
      (leftEnd (Equiv.swap (1 : Fin 3) 2)).asHom)) (0 : Fin 3) = 2 := by
  rw [mapValue_comp, client_leftEnd, client_leftEnd]
  decide

-- Reversing those two arrows moves zero to one, so these are not commuting tests.
example :
    (mapValue ((leftEnd (Equiv.swap (1 : Fin 3) 2)).asHom ≫
      (leftEnd (Equiv.swap (0 : Fin 3) 1)).asHom)) (0 : Fin 3) = 1 := by
  rw [mapValue_comp, client_leftEnd, client_leftEnd]
  decide

-- Every actual arrow in the second component, including nonidentity ones,
-- is unreachable from the original base object and has value one.
example (p : Perm) :
    mapValue ((Sum.inr_ (SingleObj Perm) (SingleObj Perm)).map
      (SingleObj.toEnd Perm p).asHom) = 1 := by
  exact Groupoid.basedFunctor_map_of_not_nonempty base originalHom _ (by
    rintro ⟨f⟩
    exact hom_inl_inr_false (SingleObj Perm) (SingleObj Perm) f)

end MathlibExtTest.BasedFunctorTests

end
