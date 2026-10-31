/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.RevealmentTranslation

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.RevealmentTranslation`

* `siteRadius` and `centeredRadius` evaluated on explicit sites of `ℤ²`;
* `mem_box_iff_siteRadius_le` on an explicit site;
* `nat_discrete_ivt` for the identity map;
* `revealment_sum_bound_lattice` for the uniform mass on one edge of `ℤ¹`, at the origin with
  `Λ = {0}`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.RevealmentTranslation

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.RevealmentTranslation
open _root_.StatMech.Lattice _root_.StatMech.OSSS.RevealmentConstruction

-- The sup-norm radius of `(3, -5)` is `5`, and its distance to `(1, -1)` is `4`.
example : siteRadius (![3, -5] : Site 2) = 5 ∧ centeredRadius (![1, -1] : Site 2) ![3, -5] = 4 := by
  decide

-- `(3, -5)` lies in the box of radius `5` but not in the box of radius `4`.
example : (![3, -5] : Site 2) ∈ box 2 5 ∧ (![3, -5] : Site 2) ∉ box 2 4 := by
  rw [mem_box_iff_siteRadius_le, mem_box_iff_siteRadius_le]
  decide

-- The discrete intermediate-value theorem for the identity.
example : ∃ i ≤ 5, id i = 3 :=
  nat_discrete_ivt id 5 rfl (fun _ _ => le_rfl) 3 (by decide)

open Classical in
-- The revealment-sum bound at the origin of `ℤ¹`, for the uniform mass on one edge.
example (edge : Fin 1 → Sym2 (Site 1)) (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n,
        Lindeberg.mean (fun _ => (1 / 2 : ℝ)) (fun ω => if ConnectedToSet 1 (liftCfg edge ω) 0
          (vertexBoundary 1 k) then (1 : ℝ) else 0))
      ≤ 2 * ({0} : Finset (Site 1)).sup' (Finset.singleton_nonempty _)
        (fun x => ∑ j ∈ Finset.range n,
          Lindeberg.mean (fun _ => (1 / 2 : ℝ)) (fun ω => if ConnectedToSet 1 (liftCfg edge ω) x
            (centeredBoundary x j) then (1 : ℝ) else 0)) :=
  revealment_sum_bound_lattice _ (fun _ => by norm_num) edge {0} _ 0 (Finset.mem_singleton_self 0)
    (mem_box_iff_siteRadius_le.2 (by simp [siteRadius]))

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.RevealmentTranslation
