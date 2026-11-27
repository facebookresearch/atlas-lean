/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCovLowerGeom

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCovLowerGeom`

The concrete geometry: the single (loop) edge of `Sym2 (Fin 1)` embedded as the unit edge
`s(0, 1)` of `ℤ¹`, origin `o = 0`, `disc₀ k` the vertex boundary of the box of radius `k` as a
finset, `n = 1` and `Λ = {0, 1}`.

* the unit-edge embedding is injective (witness for the geometric hypothesis);
* `fk_q2_hcov_lattice` on this geometry, for the random-cluster mass of the complete graph on
  `Fin 1` at `p = 1/2`;
* `hcov_lattice_mass` on the same geometry for a general FKG probability mass;
* `hcov_crossTree_mass` in its conditional form (revealment budget as a binder).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCovLowerGeom

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.AdaptiveCovLowerGeom
open _root_.StatMech.OSSS.MonotonicFK _root_.StatMech.Lattice
open _root_.StatMech.OSSS.RevealmentConstruction _root_.StatMech.OSSS.Monotonic

/-- The constant unit-edge embedding of `Sym2 (Fin 1)` into `ℤ¹` is injective. -/
theorem unitEdge_injective :
    Function.Injective (fun _ : Sym2 (Fin 1) => s((0 : Site 1), fun _ => 1)) := by
  intro a b _
  revert a b
  decide

-- The `q = 2` covariance lower bound on the one-edge geometry.
example :=
  fk_q2_hcov_lattice (⊤ : SimpleGraph (Fin 1)) (p := 1 / 2) (by norm_num) (by norm_num)
    unitEdge_injective (endU := fun _ => 0) (endV := fun _ => fun _ => 1) (fun _ => rfl)
    (fun _ => by simp) 0 [s(0, 0)] (by decide) (fun k => (vertexBoundary_finite 1 k).toFinset)
    (fun _ _ hb => (Set.Finite.mem_toFinset _).1 hb)
    (fun _ _ hb => (Set.Finite.mem_toFinset _).2 hb) (fun _ => by simp) (fun _ _ => by simp)
    1 le_rfl {0, fun _ => 1} (by simp) (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
    (fun _ => by simp)

-- The covariance lower bound for any FKG probability mass on the one-edge geometry.
example (μ : ConfigSpace (Sym2 (Fin 1)) → ℝ) (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (hFKG : FKGLatticeCondition μ) :=
  hcov_lattice_mass μ hpos hμ1 hFKG unitEdge_injective (endU := fun _ => 0)
    (endV := fun _ => fun _ => 1) (fun _ => rfl) (fun _ => by simp) 0 [s(0, 0)] (by decide)
    (fun k => (vertexBoundary_finite 1 k).toFinset)
    (fun _ _ hb => (Set.Finite.mem_toFinset _).1 hb)
    (fun _ _ hb => (Set.Finite.mem_toFinset _).2 hb) (fun _ => by simp) (fun _ _ => by simp)
    1 le_rfl {0, fun _ => 1} (by simp) (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
    (fun _ => by simp)

-- The cross-tree bound, conditional on a revealment budget `D`.
example {E : Type*} [Fintype E] [DecidableEq E] {d : ℕ} (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) (hFKG : FKGLatticeCondition μ)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (l : List E) (hl : ∀ e, e ∈ l) (disc₀ : ℕ → Finset (Site d))
    (hdisc₀sub : ∀ k, ∀ x ∈ disc₀ k, x ∈ vertexBoundary d k)
    (hdisc₀sup : ∀ k, ∀ b ∈ vertexBoundary d k, b ∈ disc₀ k)
    (hoB : ∀ k, o ∉ disc₀ k) (ho : ∀ k : ℕ, 1 ≤ k → o ∈ box d (k - 1))
    (n : ℕ) (hn : 1 ≤ n) (D : ℝ) (hD : 0 < D)
    (hsum : ∀ e : E, (∑ k : ↥(Finset.Icc 1 n), boxRevealG μ edge endU endV (k : ℕ) e)
        ≤ (Fintype.card (↥(Finset.Icc 1 n)) : ℝ) * D) :
    Lindeberg.mean μ (crossIndG edge o n) * (1 - Lindeberg.mean μ (crossIndG edge o n)) / D ≤
      ∑ e, Lindeberg.cov μ (crossIndG edge o n) (Lindeberg.coord e) :=
  hcov_crossTree_mass μ hpos hμ1 hFKG hinj hcoh hadj o l hl disc₀ hdisc₀sub hdisc₀sup hoB ho n
    hn D hD hsum

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCovLowerGeom
