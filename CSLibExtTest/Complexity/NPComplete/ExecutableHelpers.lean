/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.RubiksCubeDefs
import CSLibExt.Complexity.NPComplete.RubiksSquareDefs
import CSLibExt.Complexity.NPComplete.SortingByTranspositionsDefs
import CSLibExt.Complexity.NPComplete.StarFreeRegularExpressionInequivalenceDefs
import CSLibExt.Complexity.NPComplete.TriangularSlitherLinkDefs
import CSLibExt.Complexity.NPComplete.ZhedDefs

/-! # Small checks on moves, parsing, and grid coordinates -/

namespace MetaMathlibExt.Complexity.NPComplete

/-- Only the two adjacent blocks are exchanged. -/
example : SortingByTranspositions.transposition [0, 1, 2, 3, 4, 5] 1 3 5 = [0, 3, 4, 1, 2, 5] := rfl

/-- Concatenation takes its left and right operands from the stack in that order. -/
example : StarFreeRegularExpressionInequivalence.parse [(2, 3), (2, 4), (4, 0)] =
    some (RegularExpression.char 3 * RegularExpression.char 4) := rfl

example : StarFreeRegularExpressionInequivalence.readToken [] (4, 0) = none := rfl

/-- Flipping one row exposes its underside without changing the neighboring row. -/
example (C : RubiksSquare.Config 3) : (RubiksSquare.flipRow 1 C).top 0 1 = C.bottom 2 1 ∧
    (RubiksSquare.flipRow 1 C).top 0 0 = C.top 0 0 := ⟨rfl, rfl⟩

/-- Flipping one column reverses its other coordinate. -/
example (C : RubiksSquare.Config 3) : (RubiksSquare.flipColumn 0 C).top 0 0 = C.bottom 0 2 ∧
    (RubiksSquare.flipColumn 0 C).top 1 0 = C.top 1 0 := ⟨rfl, rfl⟩

/-- A quarter turn around the first axis moves a positive second-axis sticker to the third. -/
example : RubiksCube.turnSticker (n := 3) 0 (1, true, 0, 2) = (2, true, 2, 2) := by decide

/-- Adjacent triangles point in opposite directions and share two vertices. -/
example : TriangularSlitherLink.corners 0 0 = ((0, 0), (1, 0), (0, 1)) ∧
    TriangularSlitherLink.corners 0 1 = ((0, 1), (1, 1), (1, 0)) := ⟨rfl, rfl⟩

/-- A ray stops at the board edge. A move skips an occupied square before spending its budget. -/
example : Zhed.ray 3 (0, 0) (1, 0) = [(1, 0), (2, 0)] ∧
    Zhed.move 3 [(1, 0)] (0, 0) 1 (1, 0) = [(1, 0), (2, 0)] := ⟨rfl, rfl⟩

end MetaMathlibExt.Complexity.NPComplete
