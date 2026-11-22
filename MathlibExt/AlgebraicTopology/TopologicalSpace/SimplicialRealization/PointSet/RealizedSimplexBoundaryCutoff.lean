/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.Boundary
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizationBoundaryZeroCoordinate
public import MathlibExt.Topology.Convenient.StdSimplexRadialBoundary
public import Mathlib.Topology.Order

/-!
# Boundary cutoffs on realized simplices

Transporting the minimum barycentric weight `StdSimplexRadialBoundary.radMin`
through `SimplexCategory.toTopHomeo` defines the continuous function `cutoff N`
on the realization of `Δ[N]`. Its zero locus is exactly the realized boundary
range. The sublevel sets `thickening N ε` are open, contain that range for
positive `ε`, and are preserved by the stated radial homotopy. The boundary
identification uses `SSet.mem_realizedBoundary_of_zeroCoord` and the converse
zero-coordinate lift.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial
open scoped unitInterval

namespace RealizedSimplexBoundaryCutoff

/-- Minimum-weight cutoff on the realized simplex, via `toTopHomeo`. -/
noncomputable def cutoff (N : ℕ) (q : SSet.toTop.obj (Δ[N] : SSet.{u})) : ℝ :=
  StdSimplexRadialBoundary.radMin N ((⦋N⦌.toTopHomeo) q)

/-- The cutoff is continuous. -/
theorem continuous_cutoff (N : ℕ) :
    Continuous (cutoff N) := by
  unfold cutoff
  exact (StdSimplexRadialBoundary.continuous_radMin N).comp
    (⦋N⦌.toTopHomeo).continuous

/-- Zero cutoff iff some barycentric weight vanishes. -/
theorem cutoff_eq_zero_iff_exists_zeroCoord (N : ℕ)
    (q : SSet.toTop.obj (Δ[N] : SSet.{u})) :
    cutoff N q = 0 ↔
      ∃ j : Fin (N + 1), (((⦋N⦌.toTopHomeo) q).weights j = 0) := by
  constructor
  · intro h0
    have hcut : StdSimplexRadialBoundary.radMin N ((⦋N⦌.toTopHomeo) q) = 0 :=
      h0
    obtain ⟨j, hj⟩ := StdSimplexRadialBoundary.exists_radMin_eq N
      ((⦋N⦌.toTopHomeo) q)
    exact ⟨j, hj.symm.trans hcut⟩
  · rintro ⟨j, hj⟩
    unfold cutoff
    have hle : StdSimplexRadialBoundary.radMin N ((⦋N⦌.toTopHomeo) q) ≤ 0 := by
      have h := StdSimplexRadialBoundary.radMin_le N ((⦋N⦌.toTopHomeo) q) j
      rw [hj] at h
      exact h
    have hnn : 0 ≤ StdSimplexRadialBoundary.radMin N ((⦋N⦌.toTopHomeo) q) :=
      StdSimplexRadialBoundary.radMin_nonneg N ((⦋N⦌.toTopHomeo) q)
    exact le_antisymm hle hnn

/-- Zero cutoff lands in the realized boundary range (reverse lift). -/
theorem mem_range_of_cutoff_eq_zero (N : ℕ)
    (q : SSet.toTop.obj (Δ[N] : SSet.{u})) (h0 : cutoff N q = 0) :
    q ∈ Set.range ⇑(SSet.toTop.map (SSet.boundary.{u} N).ι) := by
  obtain ⟨j, hj⟩ := (cutoff_eq_zero_iff_exists_zeroCoord N q).mp h0
  have hmem := SSet.mem_realizedBoundary_of_zeroCoord N
    ((⦋N⦌.toTopHomeo) q) j hj
  rwa [Homeomorph.symm_apply_apply] at hmem

/-- Every realized boundary point has zero cutoff (forward lift). -/
theorem cutoff_eq_zero_of_mem_range (N : ℕ)
    (q : SSet.toTop.obj (Δ[N] : SSet.{u}))
    (hq : q ∈ Set.range ⇑(SSet.toTop.map (SSet.boundary.{u} N).ι)) :
    cutoff N q = 0 := by
  obtain ⟨j, hj⟩ :=
    SSet.boundary.mem_zeroCoord_of_mem_realizedBoundaryRange N q hq
  exact (cutoff_eq_zero_iff_exists_zeroCoord N q).mpr ⟨j, hj⟩

/-- The zero locus is exactly the realized boundary range. -/
theorem zeroLocus_eq_range (N : ℕ) :
    {q | cutoff N q = 0} =
      Set.range ⇑(SSet.toTop.map (SSet.boundary.{u} N).ι) := by
  ext q
  constructor
  · intro hq
    exact mem_range_of_cutoff_eq_zero N q hq
  · intro hq
    exact cutoff_eq_zero_of_mem_range N q hq

/-- Open boundary thickening at level `ε`. -/
def thickening (N : ℕ) (ε : ℝ) : Set (SSet.toTop.obj (Δ[N] : SSet.{u})) :=
  {q | cutoff N q < ε}

/-- Every thickening is open. -/
theorem isOpen_thickening (N : ℕ) (ε : ℝ) : IsOpen (thickening N ε) := by
  have h : thickening N ε = cutoff N ⁻¹' Set.Iio ε := rfl
  rw [h]
  exact isOpen_Iio.preimage (continuous_cutoff N)

/-- The zero locus lies in every positive thickening. -/
theorem zeroLocus_subset_thickening (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    {q | cutoff N q = 0} ⊆
      thickening N ε := by
  intro q hq
  change cutoff N q < ε
  rw [hq]
  exact hε

/-- The realized boundary range lies in every positive thickening. -/
theorem range_subset_thickening (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Set.range ⇑(SSet.toTop.map (SSet.boundary.{u} N).ι) ⊆ thickening N ε := by
  rw [← zeroLocus_eq_range N]
  exact zeroLocus_subset_thickening N hε

/-- Realized cutoff is nonincreasing along the transported homotopy
on the barycenter complement. -/
theorem cutoff_homotopyPoint_le (N : ℕ) (t : I)
    (q : SSet.toTop.obj (Δ[N] : SSet.{u}))
    (hx : (⦋N⦌.toTopHomeo) q ≠ Convexity.StdSimplex.barycenter) :
    cutoff N ((⦋N⦌.toTopHomeo).symm
      (StdSimplexRadialBoundary.homotopyPoint N t ((⦋N⦌.toTopHomeo) q) hx)) ≤
      cutoff N q := by
  unfold cutoff
  rw [Homeomorph.apply_symm_apply]
  exact StdSimplexRadialBoundary.radMin_homotopyPoint_le N t _ hx

/-- Transported homotopy preserves thickening membership
on the barycenter complement. -/
theorem homotopyPoint_mem_thickening_of_mem (N : ℕ) (ε : ℝ) (t : I)
    (q : SSet.toTop.obj (Δ[N] : SSet.{u}))
    (hx : (⦋N⦌.toTopHomeo) q ≠ Convexity.StdSimplex.barycenter)
    (hmem : q ∈ thickening N ε) :
    (⦋N⦌.toTopHomeo).symm
      (StdSimplexRadialBoundary.homotopyPoint N t ((⦋N⦌.toTopHomeo) q) hx) ∈
      thickening N ε := by
  change cutoff N ((⦋N⦌.toTopHomeo).symm
    (StdSimplexRadialBoundary.homotopyPoint N t ((⦋N⦌.toTopHomeo) q) hx)) < ε
  exact lt_of_le_of_lt (cutoff_homotopyPoint_le N t q hx) hmem

end RealizedSimplexBoundaryCutoff
