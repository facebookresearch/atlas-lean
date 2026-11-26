/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Hash.BoundedUniversalHashing
import Mathlib.Tactic.NormNum

namespace Cslib.Crypto.BoundedUniversalHashing.Tests

private def halfColliding (key x : Bool) : Bool := key && x

private theorem halfColliding_probability {x y : Bool} (hxy : x ≠ y) :
    collisionProbability halfColliding x y = (1 / 2 : ℝ) := by
  unfold collisionProbability
  let p := fun key : Bool => halfColliding key x = halfColliding key y
  change ((@Finset.filter Bool p (fun k => Classical.propDecidable (p k)) Finset.univ).card : ℝ) /
    Fintype.card Bool = 1 / 2
  have hkeys :
      @Finset.filter Bool p (fun k => Classical.propDecidable (p k)) Finset.univ =
        ({false} : Finset Bool) := by
    ext key
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    cases key
    · simp [p, halfColliding]
    · simpa [p, halfColliding] using hxy
  rw [hkeys]
  norm_num

/-- At the endpoint `1 / 2`, Boolean conjunction is bounded universal. -/
public theorem and_isBoundedUniversal :
    IsBoundedUniversal (fun (key x : Bool) => key && x) (1 / 2 : ℝ) := by
  change IsBoundedUniversal halfColliding (1 / 2 : ℝ)
  refine ⟨⟨false⟩, by norm_num, ?_⟩
  intro x y hxy
  rw [halfColliding_probability hxy]

example : ¬ IsBoundedUniversal halfColliding (1 / 3 : ℝ) := by
  intro h
  have hbound := h.2.2 false true (by decide)
  rw [halfColliding_probability (by decide : false ≠ true)] at hbound
  norm_num at hbound

-- With a singleton input type the pairwise condition would be vacuous.
example : ¬ IsBoundedUniversal (fun (_ : Empty) (_ : Unit) => false) 1 := by
  intro h
  exact h.1.elim Empty.elim

example : ¬ IsBoundedUniversal (fun (_ : Bool) (_ : Unit) => false) (-1) := by
  intro h
  have hε := h.2.1
  norm_num at hε

end Cslib.Crypto.BoundedUniversalHashing.Tests
