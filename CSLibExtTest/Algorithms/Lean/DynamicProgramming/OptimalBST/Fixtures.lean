/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import CSLibExt.Algorithms.Lean.DynamicProgramming.OptimalBST.Cost
public meta import CSLibExt.Algorithms.Lean.DynamicProgramming.OptimalBST.Basic
public meta import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.Order.Field.Rat
public meta import Mathlib.Algebra.Order.Field.Rat

set_option autoImplicit false
open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.BinarySearchTree
open Cslib.Algorithms.Lean.OptimalBST

namespace Cslib.Algorithms.Lean.OptimalBST.Fixtures

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def figureE : Vector (Vector Rat 6) 6 := #v[
  #v[5/100, 45/100, 90/100, 125/100, 175/100, 275/100],
  #v[0, 10/100, 40/100, 70/100, 120/100, 200/100],
  #v[0, 0, 5/100, 25/100, 60/100, 130/100],
  #v[0, 0, 0, 5/100, 30/100, 90/100],
  #v[0, 0, 0, 0, 5/100, 50/100],
  #v[0, 0, 0, 0, 0, 10/100]
]

private def figureRoot : Vector (Vector (Option (Fin 5)) 5) 5 := #v[
  #v[some ⟨0, by decide⟩, some ⟨0, by decide⟩, some ⟨1, by decide⟩,
    some ⟨1, by decide⟩, some ⟨1, by decide⟩],
  #v[none, some ⟨1, by decide⟩, some ⟨1, by decide⟩,
    some ⟨1, by decide⟩, some ⟨3, by decide⟩],
  #v[none, none, some ⟨2, by decide⟩, some ⟨3, by decide⟩,
    some ⟨4, by decide⟩],
  #v[none, none, none, some ⟨3, by decide⟩, some ⟨4, by decide⟩],
  #v[none, none, none, none, some ⟨4, by decide⟩]
]

private def exerciseE : Vector (Vector Rat 8) 8 := #v[
  #v[6/100,28/100,62/100,102/100,134/100,183/100,244/100,312/100],
  #v[0,6/100,30/100,68/100,93/100,141/100,196/100,261/100],
  #v[0,0,6/100,32/100,57/100,104/100,148/100,213/100],
  #v[0,0,0,6/100,24/100,57/100,101/100,155/100],
  #v[0,0,0,0,5/100,30/100,72/100,120/100],
  #v[0,0,0,0,0,5/100,32/100,78/100],
  #v[0,0,0,0,0,0,5/100,34/100],
  #v[0,0,0,0,0,0,0,5/100]
]

private def exerciseRoot : Vector (Vector (Option (Fin 7)) 7) 7 := #v[
  #v[some ⟨0,by decide⟩,some ⟨1,by decide⟩,some ⟨1,by decide⟩,
    some ⟨1,by decide⟩,some ⟨2,by decide⟩,some ⟨2,by decide⟩,
    some ⟨4,by decide⟩],
  #v[none,some ⟨1,by decide⟩,some ⟨2,by decide⟩,some ⟨2,by decide⟩,
    some ⟨2,by decide⟩,some ⟨4,by decide⟩,some ⟨4,by decide⟩],
  #v[none,none,some ⟨2,by decide⟩,some ⟨2,by decide⟩,some ⟨3,by decide⟩,
    some ⟨4,by decide⟩,some ⟨4,by decide⟩],
  #v[none,none,none,some ⟨3,by decide⟩,some ⟨4,by decide⟩,
    some ⟨4,by decide⟩,some ⟨5,by decide⟩],
  #v[none,none,none,none,some ⟨4,by decide⟩,some ⟨5,by decide⟩,
    some ⟨5,by decide⟩],
  #v[none,none,none,none,none,some ⟨5,by decide⟩,some ⟨6,by decide⟩],
  #v[none,none,none,none,none,none,some ⟨6,by decide⟩]
]

private def verifyFigure : IO Unit := do
  let p : Vector Rat 5 := #v[15/100,10/100,5/100,10/100,20/100]
  let q : Vector Rat 6 := #v[5/100,10/100,5/100,5/100,5/100,10/100]
  let actual := optimalBST p q
  require (actual.ret.1 == figureE) "Figure 14.10 e table"
  require (actual.ret.2 == figureRoot) "Figure 14.10 root table"
  require (actual.time == 35) "Figure 14.10 candidate count"

private def verifyEmptyAndSingleton : IO Unit := do
  let emptyP : Vector Rat 0 := #v[]
  let emptyQ : Vector Rat 1 := #v[1]
  let empty := optimalBST emptyP emptyQ
  require (empty.ret.1 == #v[#v[1]]) "empty dummy cost"
  require (empty.ret.2 == (#v[] : Vector (Vector (Option (Fin 0)) 0) 0)) "empty roots"
  require (empty.time == 0) "empty candidate count"
  let p : Vector Rat 1 := #v[7/10]
  let q : Vector Rat 2 := #v[2/10,1/10]
  let singleton := optimalBST p q
  let expectedE : Vector (Vector Rat 2) 2 := #v[#v[2/10,13/10],#v[0,1/10]]
  let expectedRoot : Vector (Vector (Option (Fin 1)) 1) 1 :=
    #v[#v[some ⟨0,by decide⟩]]
  require (singleton.ret.1 == expectedE) "singleton e table"
  require (singleton.ret.2 == expectedRoot) "singleton root table"
  require (singleton.time == 1) "singleton candidate count"
  let tree : BinaryTree (Fin 1) := .node ⟨0,by decide⟩ .nil .nil
  have complete : inorder tree = List.finRange 1 := by decide
  require (expectedSearchCost 1 p q tree complete == 13/10) "singleton objective"

private def verifyTiesAndEndpoints : IO Unit := do
  let tieP : Vector Rat 3 := #v[0,0,0]
  let tieQ : Vector Rat 4 := #v[0,0,0,0]
  let ties := optimalBST tieP tieQ
  require (ties.ret.2[0][2] == some ⟨0,by decide⟩) "strict earliest tie"
  require (ties.time == 10) "tie candidate count"
  let zeroP : Vector Rat 2 := #v[0,0]
  let left := optimalBST zeroP (#v[1,0,0] : Vector Rat 3)
  let right := optimalBST zeroP (#v[0,0,1] : Vector Rat 3)
  require (left.ret.1[0][2] == 2 && left.ret.2[0][1] == some ⟨0,by decide⟩)
    "left dummy endpoint"
  require (right.ret.1[0][2] == 2 && right.ret.2[0][1] == some ⟨1,by decide⟩)
    "right dummy endpoint"
  let successful := optimalBST (#v[1,0,0] : Vector Rat 3) (#v[0,0,0,0] : Vector Rat 4)
  require (successful.ret.1[0][3] == 1 && successful.ret.2[0][2] == some ⟨0,by decide⟩)
    "successful-only fixture"

private def verifyFractionsExerciseAndScaling : IO Unit := do
  let fractional := optimalBST (#v[1/30,2/30,7/30] : Vector Rat 3)
    (#v[3/30,4/30,5/30,8/30] : Vector Rat 4)
  require (fractional.ret.1[0][3] == 73/30) "fractional cost"
  require (fractional.ret.2[0][2] == some ⟨2,by decide⟩) "fractional root"
  require (fractional.time == 10) "fractional count"
  let exercise := optimalBST (#v[4/100,6/100,8/100,2/100,10/100,12/100,14/100] : Vector Rat 7)
    (#v[6/100,6/100,6/100,6/100,5/100,5/100,5/100,5/100] : Vector Rat 8)
  require (exercise.ret.1 == exerciseE) "Exercise 14.5-2 e table"
  require (exercise.ret.2 == exerciseRoot) "Exercise 14.5-2 root table"
  require (exercise.time == 84) "Exercise 14.5-2 candidate count"
  let scaled := optimalBST (#v[105/100,70/100,35/100,70/100,140/100] : Vector Rat 5)
    (#v[35/100,70/100,35/100,35/100,35/100,70/100] : Vector Rat 6)
  require (scaled.ret.1[0][5] == 1925/100) "scaling cost"
  require (scaled.ret.2 == figureRoot) "scaling roots"
  require (scaled.time == 35) "scaling count"

private def verify : IO Unit := do
  verifyFigure
  verifyEmptyAndSingleton
  verifyTiesAndEndpoints
  verifyFractionsExerciseAndScaling
  IO.println "U065_FIXTURES_OK"

#eval verify

end Cslib.Algorithms.Lean.OptimalBST.Fixtures

namespace U065SignedCompetitors

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def verify : IO Unit := do
  let p : Vector Rat 2 := #v[-1, 2]
  let q : Vector Rat 3 := #v[0, 0, 0]
  let actual := optimalBST p q
  let attaining : BinaryTree (Fin 2) :=
    .node ⟨1, by decide⟩ (.node ⟨0, by decide⟩ .nil .nil) .nil
  let competitor : BinaryTree (Fin 2) :=
    .node ⟨0, by decide⟩ .nil (.node ⟨1, by decide⟩ .nil .nil)
  have attainingComplete : inorder attaining = List.finRange 2 := by decide
  have competitorComplete : inorder competitor = List.finRange 2 := by decide
  require (actual.ret.1[0][2] == 0) "signed actual optimum"
  require (actual.ret.2[0][1] == some ⟨1, by decide⟩) "signed selected root"
  require (actual.time == 4) "signed actual candidate count"
  require (expectedSearchCost 2 p q attaining attainingComplete == 0)
    "signed attaining tree objective"
  require (expectedSearchCost 2 p q competitor competitorComplete == 3)
    "signed competing tree objective"
  let tied := optimalBST (#v[-1, -1] : Vector Rat 2) q
  require (tied.ret.1[0][2] == -3) "signed negative tie optimum"
  require (tied.ret.2[0][1] == some ⟨0, by decide⟩) "signed earliest tie root"
  require (tied.time == 4) "signed tie actual count"
  IO.println "U065_SIGNED_COMPETITORS_OK managers=2 objectives=2 assertions=8"

#eval verify
end U065SignedCompetitors
