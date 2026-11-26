/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.MarkoffGraph
import Mathlib.Data.Fin.VecNotation

open MathlibExt.Combinatorics.MarkoffGraphWanted.Combinatorics

private def zeroFirst : MarkoffTriple 5 := ⟨![0, 1, 2], by decide⟩
private def firstMove : MarkoffTriple 5 := ⟨![1, 1, 2], by decide⟩

-- A zero coordinate can become nonzero along an edge.
example : (markoffGraph 5).Adj zeroFirst firstMove :=
  ⟨by decide, Or.inl ⟨by decide, rfl, rfl⟩⟩

example : 5 ∣ Nat.card ((markoffGraph 5).connectedComponentMk zeroFirst) :=
  dvd_card_connectedComponent_markoffGraph (hp := by decide) (hgt := by decide) _

-- A fixed point of the first Vieta involution gives no loop.
private def fixedFirst : MarkoffTriple 7 := ⟨![1, 2, 5], by decide⟩

example : 3 * fixedFirst.1 1 * fixedFirst.1 2 - fixedFirst.1 0 = fixedFirst.1 0 ∧
    ¬ (markoffGraph 7).Adj fixedFirst fixedFirst :=
  ⟨by decide, (markoffGraph 7).loopless.irrefl _⟩
