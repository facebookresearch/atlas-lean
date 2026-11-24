/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.ExactInputSequence
public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.MappedConnecting

-- Authors: @toskua, Avocado

@[expose] public section

noncomputable section
set_option autoImplicit false
open CategoryTheory
universe uW vW uA vA uB vB uC vC uD vD

namespace CategoryTheory.CohomologicalDeltaFunctor

variable {W : Type uW} [Category.{vW} W] [Preadditive W]
variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B]
variable {C : Type uC} [Category.{vC} C] [Preadditive C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]

/--
Reindex the ORIGINAL sequence by L, then map by R into T's input category. Both exactness proofs
are the supplied functor providers.
-/
def reindexedExactInputSequence (L : W ⥤ A) [L.Additive]
    (hL : ∀ S : ShortComplex W, S.ShortExact → (S.map L).ShortExact)
    (R : A ⥤ B) [R.Additive]
    (hR : ∀ S : ShortComplex A, S.ShortExact → (S.map R).ShortExact)
    (T : CohomologicalDeltaFunctor B D) (S : ShortComplex W) (hS : S.ShortExact) :
    exactInputSequenceType T :=
  let SL := exactInputSequence L hL (precompose R hR T) S hS
  exactInputSequence R hR T SL.obj SL.property

/-- No complex or coefficient is changed: the object is literally two maps. -/
theorem reindexedExactInputSequence_obj (L : W ⥤ A) [L.Additive]
    (hL : ∀ S : ShortComplex W, S.ShortExact → (S.map L).ShortExact)
    (R : A ⥤ B) [R.Additive]
    (hR : ∀ S : ShortComplex A, S.ShortExact → (S.map R).ShortExact)
    (T : CohomologicalDeltaFunctor B D) (S : ShortComplex W) (hS : S.ShortExact) :
    (reindexedExactInputSequence L hL R hR T S hS).obj = (S.map L).map R := rfl

/--
The comparison is evaluated at the L-object, avoiding functor associator reductions in a later
field specialization.
-/
def reindexedCohomologyComponent (L : W ⥤ A) (R : A ⥤ B) (F : A ⥤ C)
    (T : CohomologicalDeltaFunctor B D) (U : CohomologicalDeltaFunctor C D)
    (c : ∀ q, R ⋙ T.T q ≅ F ⋙ U.T q) (q : ℕ) (X : W) :
    (T.T q).obj (R.obj (L.obj X)) ≅ (U.T q).obj (F.obj (L.obj X)) :=
  (c q).app (L.obj X)

omit [Preadditive W] [Preadditive A] in
/-- Every ORIGINAL arrow f acts by the literal L.map f in the same components. -/
theorem reindexedCohomologyComponent_naturality (L : W ⥤ A) (R : A ⥤ B) (F : A ⥤ C)
    (T : CohomologicalDeltaFunctor B D) (U : CohomologicalDeltaFunctor C D)
    (c : ∀ q, R ⋙ T.T q ≅ F ⋙ U.T q) (q : ℕ) {X Y : W} (f : X ⟶ Y) :
    (T.T q).map (R.map (L.map f)) ≫
        (reindexedCohomologyComponent L R F T U c q Y).hom =
      (reindexedCohomologyComponent L R F T U c q X).hom ≫
        (U.T q).map (F.map (L.map f)) :=
  (c q).hom.naturality (L.map f)

/--
The delta comparison applies to every original sequence reindexed by L. Ordinary endpoints and the
exact mapped sequence are retained in all q.
-/
theorem reindexedCohomology_connecting (L : W ⥤ A) [L.Additive]
    (hL : ∀ S : ShortComplex W, S.ShortExact → (S.map L).ShortExact)
    (R : A ⥤ B) [R.Additive] (F : A ⥤ C) [F.Additive]
    (hR : ∀ S : ShortComplex A, S.ShortExact → (S.map R).ShortExact)
    (hF : ∀ S : ShortComplex A, S.ShortExact → (S.map F).ShortExact)
    (T : CohomologicalDeltaFunctor B D) (U : CohomologicalDeltaFunctor C D)
    (e : precompose R hR T ≅ precompose F hF U)
    (c : ∀ q, R ⋙ T.T q ≅ F ⋙ U.T q)
    (hc : ∀ q, Hom.app e.hom q = (c q).hom)
    (q : ℕ) (S : ShortComplex W) (hS : S.ShortExact) :
    (T.connecting q).app (reindexedExactInputSequence L hL R hR T S hS) ≫
        (reindexedCohomologyComponent L R F T U c (q + 1) S.X₁).hom =
      (reindexedCohomologyComponent L R F T U c q S.X₃).hom ≫
        (U.connecting q).app (reindexedExactInputSequence L hL F hF U S hS) :=
  mappedConnecting_iso_components R F hR hF T U e c hc q (S.map L) (hL S hS)

end CategoryTheory.CohomologicalDeltaFunctor

end
