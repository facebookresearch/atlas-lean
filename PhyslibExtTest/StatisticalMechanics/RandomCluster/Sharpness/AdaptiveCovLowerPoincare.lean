/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCovLowerPoincare

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCovLowerPoincare`

The concrete geometry: the single (loop) edge of `Sym2 (Fin 1)` embedded as the unit edge
`s(0, 1)` of `ℤ¹`, origin `o = 0`, and `disc₀ k` the vertex boundary of the box of radius
`k` as a finset.

* the origin never lies on a vertex boundary, and the unit-edge embedding is injective (witnesses
  for the geometric hypotheses; the first is discharged by `simp` inline);
* `acl_fk_q2_poincare_adaptive` on this geometry, for the random-cluster mass of the complete
  graph on `Fin 1` at `p = 1/2`, `n = 1`;
* `acl_fk_q2_hcov_of_translationComparison` in its conditional form on the same geometry.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCovLowerPoincare

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.AdaptiveCovLowerClose
open _root_.StatMech.OSSS.MonotonicFK _root_.StatMech.Lattice
open _root_.StatMech.OSSS.RevealmentConstruction

/-- The origin never lies on the vertex boundary of a box. -/
theorem origin_notMem_vertexBoundary (d k : ℕ) : (0 : Site d) ∉ vertexBoundary d k := by
  simp

/-- The constant unit-edge embedding of `Sym2 (Fin 1)` into `ℤ¹` is injective. -/
theorem unitEdge_injective :
    Function.Injective (fun _ : Sym2 (Fin 1) => s((0 : Site 1), fun _ => 1)) := by
  intro a b _
  revert a b
  decide

-- The adaptive Poincaré inequality for the crossing indicator, on a one-edge geometry.
example :
    Lindeberg.var (fkMass (⊤ : SimpleGraph (Fin 1)) (1 / 2) 2)
        (crossInd (fun _ : Sym2 (Fin 1) => s((0 : Site 1), fun _ => 1)) 0 1)
      ≤ ∑ e, Lindeberg.cov (fkMass (⊤ : SimpleGraph (Fin 1)) (1 / 2) 2)
          (crossInd (fun _ : Sym2 (Fin 1) => s((0 : Site 1), fun _ => 1)) 0 1)
          (Lindeberg.coord e) :=
  acl_fk_q2_poincare_adaptive ⊤ (by norm_num) (by norm_num) unitEdge_injective
    (endU := fun _ => 0) (endV := fun _ => fun _ => 1) (fun _ => rfl) (fun _ => by simp) 0
    [s(0, 0)] (by decide) (fun k => (vertexBoundary_finite 1 k).toFinset)
    (fun _ _ hb => (Set.Finite.mem_toFinset _).2 hb)
    (fun _ => by simp) (fun _ _ => by simp) 1 le_rfl

open Classical in
-- The covariance lower bound, conditional on the translation comparison, on the same geometry.
example (conn : Site 1 → ℕ → ℝ) (hconnnn : ∀ x j, 0 ≤ conn x j)
    (rdist : Sym2 (Fin 1) → ℕ × ℕ)
    (hru : ∀ e, (rdist e).1 ≤ 1) (hrv : ∀ e, (rdist e).2 ≤ 1)
    (hcomp : ∀ (e : Sym2 (Fin 1)),
      (∀ k, Lindeberg.mean (fkMass (⊤ : SimpleGraph (Fin 1)) (1 / 2) 2)
          (fun ω => if ConnectedToSet 1
              (liftCfg (fun _ : Sym2 (Fin 1) => s((0 : Site 1), fun _ => 1)) ω) 0
              (vertexBoundary 1 k) then (1 : ℝ) else 0)
          ≤ conn 0 ((k : ℤ) - ((rdist e).1 : ℤ)).natAbs)
      ∧ (∀ k, Lindeberg.mean (fkMass (⊤ : SimpleGraph (Fin 1)) (1 / 2) 2)
          (fun ω => if ConnectedToSet 1
              (liftCfg (fun _ : Sym2 (Fin 1) => s((0 : Site 1), fun _ => 1)) ω) (fun _ => 1)
              (vertexBoundary 1 k) then (1 : ℝ) else 0)
          ≤ conn (fun _ => 1) ((k : ℤ) - ((rdist e).2 : ℤ)).natAbs))
    (hmaxpos : 0 < ({0, fun _ => 1} : Finset (Site 1)).sup' (by simp)
      (fun x => ∑ j ∈ Finset.range 2, conn x j)) :=
  acl_fk_q2_hcov_of_translationComparison ⊤ (by norm_num) (by norm_num) unitEdge_injective
    (endU := fun _ => 0) (endV := fun _ => fun _ => 1) (fun _ => rfl) (fun _ => by simp) 0
    [s(0, 0)] (by decide) (fun k => (vertexBoundary_finite 1 k).toFinset)
    (fun _ _ hb => (Set.Finite.mem_toFinset _).1 hb)
    (fun _ _ hb => (Set.Finite.mem_toFinset _).2 hb)
    (fun _ => by simp) (fun _ _ => by simp) 1 le_rfl
    {0, fun _ => 1} (by simp) conn hconnnn (fun _ => by simp) (fun _ => by simp) rdist hru hrv
    hcomp hmaxpos

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCovLowerPoincare
