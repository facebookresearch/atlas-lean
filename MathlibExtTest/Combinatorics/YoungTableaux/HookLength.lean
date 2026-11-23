/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.YoungTableaux.HookLength

@[expose] public section

open MetaMathlibExt MathlibExt.Combinatorics.YoungTableaux.HookLength

namespace MathlibExtTest.Combinatorics.YoungTableaux.HookLength

/-- The empty shape has exactly one standard Young tableau, the empty one: `f^∅ = 1`. -/
example : sytCount ⊥ = 1 := by
  unfold sytCount
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨⟨fun _ _ => 0, fun h => absurd h (YoungDiagram.notMem_bot _),
    fun _ h => absurd h (YoungDiagram.notMem_bot _),
    fun _ h => absurd h (YoungDiagram.notMem_bot _), fun _ => rfl⟩, ?_⟩,
    fun T => SkewStandardYoungTableau.ext' ?_⟩
  · simp [straightShape]
  · funext i j
    exact T.zeros (by simp [straightShape])

/-- Tableaux of any straight shape form a finite type. -/
example (μ : YoungDiagram) : Finite (SkewStandardYoungTableau (straightShape μ)) := inferInstance

/-- The corner cell `(0, 0)` of a nonempty diagram has positive hook length. -/
example (μ : YoungDiagram) (h : (0, 0) ∈ μ) : 0 < hookLength μ (0, 0) := hookLength_pos h

/-- The partition `λ = (4, 2, 2)`, the example of the `hookLength` docstring. -/
def lam422 : YoungDiagram := YoungDiagram.ofRowLens [4, 2, 2] (by decide)

/-- The hook lengths of `λ = (4, 2, 2)` are `6 5 2 1 / 3 2 / 2 1` (Stanley, *Topics in Algebraic
Combinatorics*, author's draft of 1 February 2013, Chapter 8, figure before Theorem 8.1). -/
example : [hookLength lam422 (0, 0), hookLength lam422 (0, 1), hookLength lam422 (0, 2),
      hookLength lam422 (0, 3)] = [6, 5, 2, 1] ∧
    [hookLength lam422 (1, 0), hookLength lam422 (1, 1)] = [3, 2] ∧
    [hookLength lam422 (2, 0), hookLength lam422 (2, 1)] = [2, 1] := by
  simp only [hookLength, YoungDiagram.rowLen_eq_card, YoungDiagram.colLen_eq_card]
  decide

end MathlibExtTest.Combinatorics.YoungTableaux.HookLength
