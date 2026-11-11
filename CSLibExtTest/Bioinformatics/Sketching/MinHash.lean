/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Sketching.MinHash
public meta import CSLibExt.Bioinformatics.Sketching.MinHash
import Mathlib.Tactic.NormNum

/-!
# MinHash tests

Executed fixtures: on the universe `Fin 4` (all `24` permutations), the number of colliding
permutations is `24 · |A ∩ B| / |A ∪ B|` for overlapping, equal, disjoint, nested and
one-empty pairs of sets. Instances: the probability form with the discrete measurable
structure `⊤` on `Equiv.Perm (Fin 4)`, including the boundary cases `A = B` (probability `1`)
and disjoint sets (probability `0`).
-/

namespace Cslib.Bioinformatics.Sketching.MinHash

open Finset

/-- The number of permutations of `Fin 4` under which `A` and `B` have the same min-hash. -/
def collisions (A B : Finset (Fin 4)) : ℕ :=
  (univ.filter fun π : Equiv.Perm (Fin 4) => minHash π A = minHash π B).card

#guard collisions {0, 1} {1, 2} = 8           -- `J = 1/3`
#guard collisions {0, 1, 2} {0, 1, 2} = 24    -- `J = 1`
#guard collisions {0, 1} {2, 3} = 0           -- `J = 0`
#guard collisions {0} {0, 1, 2, 3} = 6        -- `J = 1/4`
#guard collisions {0, 1, 3} {1, 3} = 16       -- `J = 2/3`
#guard collisions ∅ {2} = 0                   -- an empty set never collides with a nonempty one
#guard (univ : Finset (Equiv.Perm (Fin 4))).card = 24

section Probability

/-- The discrete measurable structure on the permutations of `Fin 4`. -/
local instance : MeasurableSpace (Equiv.Perm (Fin 4)) := ⊤

local instance : MeasurableSingletonClass (Equiv.Perm (Fin 4)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

-- `A = {0, 1}`, `B = {1, 2}`: probability `1/3`.
example : ProbabilityTheory.uniformOn Set.univ
      {π : Equiv.Perm (Fin 4) | minHash π {0, 1} = minHash π {1, 2}} = 1 / 3 := by
  rw [uniformOn_minHash_collision {0, 1} {1, 2} ⟨0, by decide⟩,
    show ({0, 1} ∩ {1, 2} : Finset (Fin 4)).card = 1 by decide,
    show ({0, 1} ∪ {1, 2} : Finset (Fin 4)).card = 3 by decide]
  norm_num

-- `A = B`: the collision probability is `1`.
example (A : Finset (Fin 4)) (hA : A.Nonempty) :
    ProbabilityTheory.uniformOn Set.univ {π : Equiv.Perm (Fin 4) | minHash π A = minHash π A} =
      1 := by
  rw [uniformOn_minHash_collision A A (by simpa using hA), inter_self, union_self]
  exact ENNReal.div_self (by simpa using hA.ne_empty) (ENNReal.natCast_ne_top _)

-- Disjoint sets: the collision probability is `0`.
example (A B : Finset (Fin 4)) (h : Disjoint A B) (hC : (A ∪ B).Nonempty) :
    ProbabilityTheory.uniformOn Set.univ {π : Equiv.Perm (Fin 4) | minHash π A = minHash π B} =
      0 := by
  rw [uniformOn_minHash_collision A B hC, disjoint_iff_inter_eq_empty.mp h]
  simp

end Probability

end Cslib.Bioinformatics.Sketching.MinHash
