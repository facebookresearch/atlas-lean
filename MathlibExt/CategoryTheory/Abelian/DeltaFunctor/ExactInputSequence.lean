/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.MappedConnecting

-- Authors: @toskua, Avocado

@[expose] public section

noncomputable section
set_option autoImplicit false
open CategoryTheory
universe uA vA uB vB uD vD uC vC uE vE

namespace CategoryTheory.CohomologicalDeltaFunctor

/--
Recover the source type, including its captured parameters, from an existing natural
transformation. This is a reducible type alias.
-/
abbrev inputSourceType {C : Type uC} [Category.{vC} C]
    {E : Type uE} [Category.{vE} E] {F G : C ⥤ E} (_η : F ⟶ G) : Type uC := C

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]

/--
The input category is taken from the connector of T. In particular, its ShortComplex category and
zero-morphism dictionaries are the ones already captured by T, rather than a new field-level
typeclass choice.
-/
abbrev exactInputSequenceType (T : CohomologicalDeltaFunctor B D) :=
  inputSourceType (T.connecting 0)

/--
Construct the mapped original short exact sequence in the same input category used by T. The only
exactness proof is the hR S hS.
-/
def exactInputSequence (R : A ⥤ B) [R.Additive]
    (hR : ∀ S : ShortComplex A, S.ShortExact → (S.map R).ShortExact)
    (T : CohomologicalDeltaFunctor B D) (S : ShortComplex A) (hS : S.ShortExact) :
    exactInputSequenceType T := by
  let hzeroR : R.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive R
  exact ⟨@ShortComplex.map _ _ _ _ _ _ S R hzeroR, hR S hS⟩

/-- The stored object is the original S mapped by R. -/
theorem exactInputSequence_obj (R : A ⥤ B) [R.Additive]
    (hR : ∀ S : ShortComplex A, S.ShortExact → (S.map R).ShortExact)
    (T : CohomologicalDeltaFunctor B D) (S : ShortComplex A) (hS : S.ShortExact) :
    (exactInputSequence R hR T S hS).obj = S.map R := rfl

/-- Evaluating the original connector on this typed input is literally the
same mappedConnecting arrow, in every degree and for every original sequence. -/
theorem exactInputSequence_connecting (R : A ⥤ B) [R.Additive]
    (hR : ∀ S : ShortComplex A, S.ShortExact → (S.map R).ShortExact)
    (T : CohomologicalDeltaFunctor B D) (S : ShortComplex A) (hS : S.ShortExact)
    (q : ℕ) :
    (T.connecting q).app (exactInputSequence R hR T S hS) =
      mappedConnecting R hR T q S hS := rfl

end CategoryTheory.CohomologicalDeltaFunctor

end
