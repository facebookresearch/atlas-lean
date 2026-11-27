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

/- Proof implementation note.
Recover the source type, including its captured parameters, from an existing natural
transformation. This is a reducible type alias.
-/

/-- For a natural transformation `η : F → G` between functors
`F,G : C → E`, the source-category type of the transformation is
`C`. This comparison retains the specified source objects and
category structure. -/
abbrev inputSourceType {C : Type uC} [Category.{vC} C]
    {E : Type uE} [Category.{vE} E] {F G : C ⥤ E} (_η : F ⟶ G) : Type uC := C

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]

/- Proof implementation note.
The input category is taken from the connector of T. In particular, its ShortComplex category and
zero-morphism dictionaries are the ones already captured by T, rather than a new field-level
typeclass choice.
-/

/-- For a cohomological δ-functor `T : B → D` between preadditive
categories, its connecting transformations are indexed by short
exact short complexes in `B`. This input type consists of such
complexes together with their short-exactness property. -/
abbrev exactInputSequenceType (T : CohomologicalDeltaFunctor B D) :=
  inputSourceType (T.connecting 0)

/-- For an additive functor `R : A → B` preserving short exact
sequences between preadditive categories, a short exact `S` in `A`
gives the exact input `R(S)` to the connecting maps of any
cohomological δ-functor `T : B → D`. -/
def exactInputSequence (R : A ⥤ B) [R.Additive]
    (hR : ∀ S : ShortComplex A, S.ShortExact → (S.map R).ShortExact)
    (T : CohomologicalDeltaFunctor B D) (S : ShortComplex A) (hS : S.ShortExact) :
    exactInputSequenceType T := by
  let hzeroR : R.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive R
  exact ⟨@ShortComplex.map _ _ _ _ _ _ S R hzeroR, hR S hS⟩

/-- For an additive functor `R : A → B` preserving short exact
sequences and a short exact short complex `S` in the preadditive
category `A`, the underlying input short complex for `T : B → D`
is the mapped complex `S.map R`. -/
theorem exactInputSequence_obj (R : A ⥤ B) [R.Additive]
    (hR : ∀ S : ShortComplex A, S.ShortExact → (S.map R).ShortExact)
    (T : CohomologicalDeltaFunctor B D) (S : ShortComplex A) (hS : S.ShortExact) :
    (exactInputSequence R hR T S hS).obj = S.map R := rfl

/- Proof implementation note.
Evaluating the original connector on this typed input is literally the
same mappedConnecting arrow, in every degree and for every original sequence.
-/

/-- For additive short-exact-sequence-preserving `R : A → B` and a
cohomological δ-functor `T : B → D` between preadditive categories,
the degree-`q` connecting map evaluated on the input `R(S)` of a
short exact `S` in `A` is `mappedConnecting R hR T q S hS`. -/
theorem exactInputSequence_connecting (R : A ⥤ B) [R.Additive]
    (hR : ∀ S : ShortComplex A, S.ShortExact → (S.map R).ShortExact)
    (T : CohomologicalDeltaFunctor B D) (S : ShortComplex A) (hS : S.ShortExact)
    (q : ℕ) :
    (T.connecting q).app (exactInputSequence R hR T S hS) =
      mappedConnecting R hR T q S hS := rfl

end CategoryTheory.CohomologicalDeltaFunctor

end
