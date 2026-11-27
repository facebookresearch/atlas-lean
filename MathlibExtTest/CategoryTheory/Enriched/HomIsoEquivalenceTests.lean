/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.HomIsoEquivalence

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uA uB

open CategoryTheory MonoidalCategory

namespace HomIsoEquivalenceTests

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {A : Type uA} [EnrichedCategory V A] {B : Type uB} [EnrichedCategory V B]
  (e : A ≃ B) (h : ∀ a b : A, (a ⟶[V] b) ≅ (e a ⟶[V] e b))
  (hid : ∀ a : A, eId V a ≫ (h a a).hom = eId V (e a))
  (hcomp : ∀ a b c : A, eComp V a b c ≫ (h a c).hom =
    ((h a b).hom ⊗ₘ (h b c).hom) ≫ eComp V (e a) (e b) (e c))

open CategoryTheory.EnrichedHomIsoEquivalence

example : EnrichedFunctor V A B := forward e h hid hcomp

example : EnrichedFunctor V B A := inverse e h hid hcomp

example (a : A) : (forward e h hid hcomp).obj a = e a :=
  forward_obj e h hid hcomp a

example (a b : A) : HEq ((forward e h hid hcomp).map a b) (h a b).hom :=
  forward_map e h hid hcomp a b

example (b : B) : (inverse e h hid hcomp).obj b = e.symm b :=
  inverse_obj e h hid hcomp b

example (b c : B) : HEq ((inverse e h hid hcomp).map b c) (inverseMap e h b c) :=
  inverse_map e h hid hcomp b c

example (b : B) : eId V b ≫ inverseMap e h b b = eId V (e.symm b) :=
  inverse_id e h hid b

example (b c d : B) :
    eComp V b c d ≫ inverseMap e h b d =
      (inverseMap e h b c ⊗ₘ inverseMap e h c d) ≫
        eComp V (e.symm b) (e.symm c) (e.symm d) :=
  inverse_comp e h hcomp b c d

example (a b : A) :
    inverseMap e h (e a) (e b) ≫
      eqToHom (congrArg₂ (fun x y : A => x ⟶[V] y)
        (e.symm_apply_apply a) (e.symm_apply_apply b)) = (h a b).inv :=
  inverseMap_image e h a b

example :
    (forward e h hid hcomp).comp V (inverse e h hid hcomp) = EnrichedFunctor.id V A :=
  forward_inverse e h hid hcomp

example :
    (inverse e h hid hcomp).comp V (forward e h hid hcomp) = EnrichedFunctor.id V B :=
  inverse_forward e h hid hcomp

example (b c : B) : inverseMap e h b c =
    eqToHom (congrArg₂ (fun x y : B => x ⟶[V] y)
      (e.apply_symm_apply b).symm (e.apply_symm_apply c).symm) ≫
        (h (e.symm b) (e.symm c)).inv :=
  inverseMap_eq e h b c

end HomIsoEquivalenceTests
