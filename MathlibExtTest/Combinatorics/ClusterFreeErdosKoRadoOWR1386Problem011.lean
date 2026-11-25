/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ClusterFreeErdosKoRadoOWR1386Problem011
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.NormNum

open Finset
open MathlibExt.Combinatorics.ClusterFreeErdosKoRadoOWR1386Problem011Wanted

private def star {n : ℕ} (k : ℕ) (x : Fin n) : Finset (Finset (Fin n)) :=
  ((univ : Finset (Fin n)).powersetCard k).filter fun A ↦ x ∈ A

private theorem star_isKdFamily {n k d : ℕ} (x : Fin n) : IsKdFamily n k d (star k x) := by
  constructor
  · intro A hA
    exact (mem_powersetCard.mp (mem_filter.mp hA).1).2
  · intro A _ hA _
    exact ⟨x, fun i ↦ (mem_filter.mp (hA i)).2⟩

-- At the exact threshold n = d*k/(d-1), the dense case attains equality.
example : ∃ x : Fin 6, ∀ A ∈ star 4 (0 : Fin 6), x ∈ A := by
  have h := kdFamilyErdosKoRado_holds 6 4 3 (by decide) (by decide) (by norm_num)
    (star 4 0) (star_isKdFamily 0)
  exact h.2 (by decide)

-- The transition n = 2*k belongs to the weighted induction range.
example : ∃ x : Fin 6, ∀ A ∈ star 3 (0 : Fin 6), x ∈ A := by
  have h := kdFamilyErdosKoRado_holds 6 3 3 (by decide) (by decide) (by norm_num)
    (star 3 0) (star_isKdFamily 0)
  exact h.2 (by decide)
