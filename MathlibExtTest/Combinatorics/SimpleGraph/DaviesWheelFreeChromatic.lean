/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.DaviesWheelFreeChromatic

namespace MathlibExtTest.Combinatorics.SimpleGraph.DaviesWheelFreeChromatic

open MathlibExt.Combinatorics.SimpleGraph.DaviesWheelFreeChromaticWanted

-- A bare hexagon has an induced rim, but every possible hub has degree two.
example : wheelFree (SimpleGraph.cycleGraph 6) := by
  rintro ⟨l, rim, hub, _, _, _, i, j, k, hij, hjk, hki, hi, hj, hk⟩
  have h : ∀ (v x y z : Fin 6), (SimpleGraph.cycleGraph 6).Adj v x →
      (SimpleGraph.cycleGraph 6).Adj v y → (SimpleGraph.cycleGraph 6).Adj v z →
      x = y ∨ y = z ∨ z = x := by decide
  rcases h hub _ _ _ hi hj hk with e | e | e
  · exact hij (rim.injective e)
  · exact hjk (rim.injective e)
  · exact hki (rim.injective e)

-- In a clique every candidate rim of length at least four has a chord.
example : wheelFree (⊤ : SimpleGraph (Fin 5)) := by
  rintro ⟨l, rim, _, hl, _, hcycle, _⟩
  have h : SimpleGraph.cycleGraph l = ⊤ := by
    ext i j
    rw [← hcycle]
    simp
  have := SimpleGraph.cycleGraph_eq_top_iff.mp h
  omega

private def hexagonWithHub : SimpleGraph (Option (Fin 6)) where
  Adj
    | some i, some j => (SimpleGraph.cycleGraph 6).Adj i j
    | none, some i | some i, none => i ∈ ({0, 2, 4} : Finset (Fin 6))
    | none, none => False
  symm := ⟨by rintro (_ | i) (_ | j) h <;> first | exact h | exact h.symm⟩
  loopless := ⟨by rintro (_ | i) <;> simp⟩

-- Three alternating spokes suffice, although the hub misses half the rim.
example : hasInducedWheel hexagonWithHub := by
  refine ⟨6, ⟨some, Option.some_injective _⟩, none, by decide, fun _ => by simp,
    fun _ _ => Iff.rfl, 0, 2, 4, by decide, by decide, by decide, ?_, ?_, ?_⟩
  all_goals change _ ∈ ({0, 2, 4} : Finset (Fin 6)); decide

end MathlibExtTest.Combinatorics.SimpleGraph.DaviesWheelFreeChromatic
