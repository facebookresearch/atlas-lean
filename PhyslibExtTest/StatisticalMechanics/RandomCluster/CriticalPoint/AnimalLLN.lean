/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.AnimalLLN

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.AnimalLLN`

On `Fin 2` with unit weights `w ≡ 1` rooted at `0`:
* `greedyAnimalValue w 0 1 = 1`, from `greedyAnimalValue_ge_root` and
  `greedyAnimalValue_le_card_mul`;
* `greedyAnimalValue_lln` (Fekete convergence) and `greedyAnimalValue_lln_le_bound` with `M = 1`;
* `mem_animalsLE` for the animal `{0, 1}` of size `2`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.AnimalLLN

open _root_.StatMech _root_.StatMech.BeffaraDC

/-- The greedy animal of size at most `1` has weight `1` under unit weights. -/
theorem greedy_one : greedyAnimalValue (fun _ : Fin 2 => (1 : ℝ)) 0 1 = 1 := by
  refine le_antisymm ?_
    (greedyAnimalValue_ge_root (w := fun _ : Fin 2 => (1 : ℝ)) (0 : Fin 2) le_rfl)
  simpa using greedyAnimalValue_le_card_mul (w := fun _ : Fin 2 => (1 : ℝ)) (fun _ => le_rfl)
    zero_le_one 0 1

-- The normalized greedy animal value converges.
example := greedyAnimalValue_lln (w := fun _ : Fin 2 => (1 : ℝ)) (fun _ => zero_le_one) 0

-- The limit is at most the uniform bound `1`.
example := greedyAnimalValue_lln_le_bound (w := fun _ : Fin 2 => (1 : ℝ)) (M := 1)
  (fun _ => zero_le_one) (fun _ => le_rfl) zero_le_one 0

-- `{0, 1}` is an animal of size at most `2` rooted at `0`.
example : ({0, 1} : Finset (Fin 2)) ∈ animalsLE 0 2 :=
  mem_animalsLE.mpr ⟨by simp, by decide⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.AnimalLLN
