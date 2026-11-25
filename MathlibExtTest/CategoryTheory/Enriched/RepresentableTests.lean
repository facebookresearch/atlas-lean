/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

import MathlibExt.CategoryTheory.Enriched.Representable

/-!
# Tests for enriched representable functors
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Opposite
open scoped MonoidalClosed

universe uV vV uA

variable (V : Type uV) [Category.{vV} V] [MonoidalCategory V]
  [MonoidalClosed V]
variable (A : Type uA) [EnrichedCategory V A]

example (c a : A) :
    (EnrichedFunctor.covariantRepresentable V A c).obj a = (c ⟶[V] a) :=
  rfl

example (c a b : A) :
    (EnrichedFunctor.covariantRepresentable V A c).map a b =
      MonoidalClosed.curry (eComp V c a b) :=
  rfl

example (c a : A) :
    eId V a ≫ (EnrichedFunctor.covariantRepresentable V A c).map a a =
      eId V ((EnrichedFunctor.covariantRepresentable V A c).obj a) :=
  (EnrichedFunctor.covariantRepresentable V A c).map_id a

example (c a b d : A) :
    eComp V a b d ≫ (EnrichedFunctor.covariantRepresentable V A c).map a d =
      ((EnrichedFunctor.covariantRepresentable V A c).map a b ⊗ₘ
          (EnrichedFunctor.covariantRepresentable V A c).map b d) ≫
        eComp V ((EnrichedFunctor.covariantRepresentable V A c).obj a)
          ((EnrichedFunctor.covariantRepresentable V A c).obj b)
          ((EnrichedFunctor.covariantRepresentable V A c).obj d) :=
  (EnrichedFunctor.covariantRepresentable V A c).map_comp a b d

example (c : A) : EnrichedFunctor V A V :=
  EnrichedFunctor.covariantRepresentable V A c

example : True := by
  fail_if_success
    exact inferInstanceAs (Category A)
  fail_if_success
    exact inferInstanceAs (BraidedCategory V)
  trivial

example : True := by
  fail_if_success
    exact (fun c : A =>
      (EnrichedFunctor.contravariantRepresentable V A c :
        EnrichedFunctor V Aᵒᵖ V))
  trivial

#check @EnrichedFunctor.covariantRepresentable.{0, 0, 1}
#check @EnrichedFunctor.covariantRepresentable.{1, 1, 0}

#print axioms CategoryTheory.EnrichedFunctor.covariantRepresentable

section Contravariant

variable [BraidedCategory V]

example (c a : A) :
    (EnrichedFunctor.contravariantRepresentable V A c).obj (op a) = (a ⟶[V] c) :=
  rfl

example (c a b : A) :
    (EnrichedFunctor.contravariantRepresentable V A c).map (op a) (op b) =
      MonoidalClosed.curry
        ((β_ (a ⟶[V] c) (b ⟶[V] a)).hom ≫ eComp V b a c) :=
  rfl

example (c a : A) :
    eId V (op a) ≫ (EnrichedFunctor.contravariantRepresentable V A c).map (op a) (op a) =
      eId V ((EnrichedFunctor.contravariantRepresentable V A c).obj (op a)) :=
  (EnrichedFunctor.contravariantRepresentable V A c).map_id (op a)

example (c a b d : A) :
    eComp V (op a) (op b) (op d) ≫
          (EnrichedFunctor.contravariantRepresentable V A c).map (op a) (op d) =
      ((EnrichedFunctor.contravariantRepresentable V A c).map (op a) (op b) ⊗ₘ
          (EnrichedFunctor.contravariantRepresentable V A c).map (op b) (op d)) ≫
        eComp V ((EnrichedFunctor.contravariantRepresentable V A c).obj (op a))
          ((EnrichedFunctor.contravariantRepresentable V A c).obj (op b))
          ((EnrichedFunctor.contravariantRepresentable V A c).obj (op d)) :=
  (EnrichedFunctor.contravariantRepresentable V A c).map_comp (op a) (op b) (op d)

#check @EnrichedFunctor.contravariantRepresentable.{0, 0, 1}
#check @EnrichedFunctor.contravariantRepresentable.{1, 1, 0}

#print axioms CategoryTheory.EnrichedFunctor.contravariantRepresentable

end Contravariant

section OrdinaryClients

universe uB vB

variable (B : Type uB) [Category.{vB} B]
  [EnrichedOrdinaryCategory V B]

example (c : B) : EnrichedFunctor V B V :=
  EnrichedFunctor.covariantRepresentable V B c

section

variable [BraidedCategory V]

example (c : B) : EnrichedFunctor V Bᵒᵖ V :=
  EnrichedFunctor.contravariantRepresentable V B c

end

end OrdinaryClients
