/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverBaseChangeDeck

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

#check SSet.KanComplex.nativeCoverBaseChangeDeckMap
#print axioms SSet.KanComplex.nativeCoverBaseChangeDeckMap
#check SSet.KanComplex.nativeCoverBaseChangeDeckMap_fst
#print axioms SSet.KanComplex.nativeCoverBaseChangeDeckMap_fst
#check SSet.KanComplex.nativeCoverBaseChangeDeckMap_snd
#print axioms SSet.KanComplex.nativeCoverBaseChangeDeckMap_snd
#check SSet.KanComplex.nativeCoverBaseChangeDeckMap_mul
#print axioms SSet.KanComplex.nativeCoverBaseChangeDeckMap_mul
#check SSet.KanComplex.nativeCoverBaseChangeDeckMap_one
#print axioms SSet.KanComplex.nativeCoverBaseChangeDeckMap_one
#check SSet.KanComplex.nativeCoverBaseChangeMap
#print axioms SSet.KanComplex.nativeCoverBaseChangeMap
#check SSet.KanComplex.nativeCoverBaseChangeMap_fst
#print axioms SSet.KanComplex.nativeCoverBaseChangeMap_fst
#check SSet.KanComplex.nativeCoverBaseChangeMap_snd
#print axioms SSet.KanComplex.nativeCoverBaseChangeMap_snd
#check SSet.KanComplex.nativeCoverBaseChangeMap_isPullback
#print axioms SSet.KanComplex.nativeCoverBaseChangeMap_isPullback
#check SSet.KanComplex.nativeCoverBaseChangeMap_mem_realizationWeakEquivalences
#print axioms SSet.KanComplex.nativeCoverBaseChangeMap_mem_realizationWeakEquivalences
#check SSet.KanComplex.nativeCoverBaseChangeMap_deck
#print axioms SSet.KanComplex.nativeCoverBaseChangeMap_deck

namespace NativeCoverBaseChangeDeckTests

open SSet.KanComplex

variable {E E' B : SSet.{u}} {p : E ⟶ B} {q : E' ⟶ B}
  (u : E ⟶ E') (hu : u ≫ q = p) (b : B _⦋0⦌)

example : nativeCoverBaseChangeMap u hu b ≫ pullback.fst q (nativeCoverProjection B b) =
    pullback.fst p (nativeCoverProjection B b) ≫ u :=
  nativeCoverBaseChangeMap_fst u hu b

example (h : SSet.realizationWeakEquivalences u) :
    SSet.realizationWeakEquivalences (nativeCoverBaseChangeMap u hu b) :=
  nativeCoverBaseChangeMap_mem_realizationWeakEquivalences u hu b h

example (g : End (SSet.FundamentalGroupoid.mk b)) :
    nativeCoverBaseChangeDeckMap p b g ≫ nativeCoverBaseChangeMap u hu b =
      nativeCoverBaseChangeMap u hu b ≫ nativeCoverBaseChangeDeckMap q b g :=
  nativeCoverBaseChangeMap_deck u hu b g

example (g h : End (SSet.FundamentalGroupoid.mk b)) :
    nativeCoverBaseChangeDeckMap p b (g * h) =
      nativeCoverBaseChangeDeckMap p b h ≫ nativeCoverBaseChangeDeckMap p b g :=
  nativeCoverBaseChangeDeckMap_mul p b g h

end NativeCoverBaseChangeDeckTests
