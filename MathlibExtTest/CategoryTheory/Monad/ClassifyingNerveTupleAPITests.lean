/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module


import MathlibExt.CategoryTheory.Monad.ClassifyingNerveData

/-!
# Public clients for classifying-bar tuple formulas
-/

namespace CategoryTheory.Monad.ClassifyingNerveTupleAPITests

noncomputable section

universe u

variable (G : Type u) [Monoid G]

attribute [local instance] typeMonObj pointModObj

example (n : ℕ) (t : Fin (n + 1) → G) (m : Fin n) : Fin n → G :=
  tupleMulAt G n t m

example (n : ℕ) (t : Fin n → G) (m : Fin (n + 1)) :
    Fin (n + 1) → G :=
  tupleInsAt G n t m

example (Y : Type u) (w : PUnit × Y) :
    (rightModuleOfRightAction PUnit G (ractPt G) (ractPt_one G)
      (ractPt_assoc G)).functor.obj Y :=
  rCastIn G Y w

example (Y : Type u) (w :
    (rightModuleOfRightAction PUnit G (ractPt G) (ractPt_one G)
      (ractPt_assoc G)).functor.obj Y) : PUnit × Y :=
  rCastOut G Y w

example (n : ℕ) (X : Type u)
    (y : PUnit × ((monadPow (tensorMonad G) (n + 1)).obj X)) :
    (let aR := ConcreteCategory.hom
        (rightActionPow (tensorMonad G)
          (rightModuleOfRightAction PUnit G (ractPt G) (ractPt_one G)
            (ractPt_assoc G)) n X)
        (rCastIn G ((monadPow (tensorMonad G) (n + 1)).obj X) y)
      let aP := rCastOut G ((monadPow (tensorMonad G) n).obj X) aR
      ((powTupleGen G X n) aP.2).1) =
      Fin.tail (((powTupleGen G X (n + 1)) y.2).1) :=
  genZeroFst G n X y

example (n : ℕ) (X : Type u) (j : Fin n)
    (y : (monadPow (tensorMonad G) (n + 1)).obj X) :
    ((powTupleGen G X n) ((tensorMonad G).muAtPos n j X y)).1 =
      tupleMulAt G n ((powTupleGen G X (n + 1) y).1)
        ⟨n - 1 - j.val, by have := j.isLt; omega⟩ :=
  genMuFst G n X j y

example (n : ℕ) (X : Type u) (j : Fin (n + 1))
    (y : (monadPow (tensorMonad G) n).obj X) :
    ((powTupleGen G X (n + 1)) ((tensorMonad G).etaAtPos n j X y)).1 =
      tupleInsAt G n ((powTupleGen G X n y).1)
        ⟨n - j.val, by have := j.isLt; omega⟩ :=
  genEtaFst G n X j y

variable (a : Discrete PUnit.{1})

example (n : ℕ) (x : (barEvalData G a).obj (n + 1)) :
    barTupleEquiv G a n ((barEvalData G a).δ (0 : Fin (n + 2)) x) =
      Fin.tail (barTupleEquiv G a (n + 1) x) :=
  barTuple_zero_face G a n x

example (n : ℕ) (x : (barEvalData G a).obj (n + 1))
    (i : Fin (n + 2)) (hL : i.val = n + 1) :
    barTupleEquiv G a n ((barEvalData G a).δ i x) =
      Fin.init (barTupleEquiv G a (n + 1) x) :=
  barTuple_last_face G a n x i hL

example (n : ℕ) (x : (barEvalData G a).obj (n + 1))
    (k : Fin n) (i : Fin (n + 2)) (hk : i.val = k.val + 1) :
    barTupleEquiv G a n ((barEvalData G a).δ i x) =
      tupleMulAt G n (barTupleEquiv G a (n + 1) x) k :=
  barTuple_middle_face G a n x k i hk

example (n : ℕ) (x : (barEvalData G a).obj n) (i : Fin (n + 1)) :
    barTupleEquiv G a (n + 1) ((barEvalData G a).σ i x) =
      tupleInsAt G n (barTupleEquiv G a n x) i :=
  barTuple_degen G a n x i

end

end CategoryTheory.Monad.ClassifyingNerveTupleAPITests
