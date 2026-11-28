/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.SlowANimReducedMin

open MetaMathlibExt

private theorem reduced_two_equal : SlowANimReduced ({2} : Finset ℕ) (fun _ : Fin 2 => 2) := by
  have move (k : ℕ) : (fun _ : Fin 2 => k) ∈ slowANimMoves {2} (fun _ : Fin 2 => k + 1) := by
    simp only [slowANimMoves, Finset.mem_image, Finset.mem_filter]
    refine ⟨Finset.univ, ⟨Finset.mem_univ _, ⟨0, Finset.mem_univ _⟩, by decide, ?_⟩, ?_⟩
    · intro i hi
      omega
    · funext i
      simp [slowANimAfter]
  intro i
  exact ⟨fun _ => 0, (Relation.ReflTransGen.single (move 1)).tail (move 0),
    slowANimMoves_zero _, rfl⟩

-- A cap strictly below the old maximum preserves reduction even with no token surplus.
example : SlowANimReduced ({2} : Finset ℕ) (fun _ : Fin 2 => 1) :=
  slowANimReduced_min 2 {2} (by decide) (fun _ => 2) reduced_two_equal 1

-- The zero cap empties every stack.
example : SlowANimReduced ({2} : Finset ℕ) (fun _ : Fin 2 => 0) :=
  slowANimReduced_min 2 {2} (by decide) (fun _ => 2) reduced_two_equal 0

example (m : ℕ) : SlowANimReduced (∅ : Finset ℕ) (fun _ : Fin 0 => 0) := by
  simpa using slowANimReduced_min 0 ∅ (by simp) (fun _ => 0) (slowANimReduced_zero ∅) m
