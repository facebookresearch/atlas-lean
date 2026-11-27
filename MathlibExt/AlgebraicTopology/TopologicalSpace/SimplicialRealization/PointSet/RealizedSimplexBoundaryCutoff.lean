/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.Boundary
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizationBoundaryZeroCoordinate
public import MathlibExt.Topology.Convenient.StdSimplexRadialBoundary
public import Mathlib.Topology.Order

/-!
# Minimum-coordinate cutoff and boundary neighborhoods

For a point of the realized standard `N`-simplex, the cutoff is the minimum
of its barycentric coordinates under the standard realization homeomorphism.
The cutoff is continuous and has zero locus exactly the realized boundary image.

Every strict sublevel set `{q | cutoff(q) < ε}` is open; positive sublevels
contain the boundary. On the barycenter complement, the transported radial
homotopy does not increase the cutoff and therefore preserves each sublevel.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial
open scoped unitInterval

namespace RealizedSimplexBoundaryCutoff

/--
The minimum barycentric coordinate of a realized simplex point, read through
the standard realization homeomorphism.
-/
noncomputable def cutoff (N : ℕ) (q : SSet.toTop.obj (Δ[N] : SSet.{u})) : ℝ :=
  StdSimplexRadialBoundary.radMin N ((⦋N⦌.toTopHomeo) q)

/--
The minimum-coordinate cutoff on each realized standard simplex is continuous.
-/
theorem continuous_cutoff (N : ℕ) :
    Continuous (cutoff N) := by
  unfold cutoff
  exact (StdSimplexRadialBoundary.continuous_radMin N).comp
    (⦋N⦌.toTopHomeo).continuous

/--
The cutoff is zero exactly when some barycentric coordinate of the corresponding
standard-simplex point is zero.
-/
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

/--
A realized simplex point with zero cutoff lies in the image of the realized
boundary inclusion.
-/
theorem mem_range_of_cutoff_eq_zero (N : ℕ)
    (q : SSet.toTop.obj (Δ[N] : SSet.{u})) (h0 : cutoff N q = 0) :
    q ∈ Set.range ⇑(SSet.toTop.map (SSet.boundary.{u} N).ι) := by
  obtain ⟨j, hj⟩ := (cutoff_eq_zero_iff_exists_zeroCoord N q).mp h0
  have hmem := SSet.mem_realizedBoundary_of_zeroCoord N
    ((⦋N⦌.toTopHomeo) q) j hj
  rwa [Homeomorph.symm_apply_apply] at hmem

/--
Every point in the image of the realized boundary inclusion has cutoff zero.
-/
theorem cutoff_eq_zero_of_mem_range (N : ℕ)
    (q : SSet.toTop.obj (Δ[N] : SSet.{u}))
    (hq : q ∈ Set.range ⇑(SSet.toTop.map (SSet.boundary.{u} N).ι)) :
    cutoff N q = 0 := by
  obtain ⟨j, hj⟩ :=
    SSet.boundary.mem_zeroCoord_of_mem_realizedBoundaryRange N q hq
  exact (cutoff_eq_zero_iff_exists_zeroCoord N q).mpr ⟨j, hj⟩

/--
The zero locus of the minimum-coordinate cutoff equals the image of the
realized boundary inclusion.
-/
theorem zeroLocus_eq_range (N : ℕ) :
    {q | cutoff N q = 0} =
      Set.range ⇑(SSet.toTop.map (SSet.boundary.{u} N).ι) := by
  ext q
  constructor
  · intro hq
    exact mem_range_of_cutoff_eq_zero N q hq
  · intro hq
    exact cutoff_eq_zero_of_mem_range N q hq

/--
The subset of the realized standard simplex where the cutoff is strictly
less than the real parameter `ε`.
-/
def thickening (N : ℕ) (ε : ℝ) : Set (SSet.toTop.obj (Δ[N] : SSet.{u})) :=
  {q | cutoff N q < ε}

/--
Each strict cutoff sublevel is open, for every real parameter `ε`.
-/
theorem isOpen_thickening (N : ℕ) (ε : ℝ) : IsOpen (thickening N ε) := by
  have h : thickening N ε = cutoff N ⁻¹' Set.Iio ε := rfl
  rw [h]
  exact isOpen_Iio.preimage (continuous_cutoff N)

/--
For `ε > 0`, the cutoff zero locus is contained in the strict sublevel at `ε`.
-/
theorem zeroLocus_subset_thickening (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    {q | cutoff N q = 0} ⊆
      thickening N ε := by
  intro q hq
  change cutoff N q < ε
  rw [hq]
  exact hε

/--
For `ε > 0`, the realized boundary image is contained in the strict cutoff
sublevel at `ε`.
-/
theorem range_subset_thickening (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Set.range ⇑(SSet.toTop.map (SSet.boundary.{u} N).ι) ⊆ thickening N ε := by
  rw [← zeroLocus_eq_range N]
  exact zeroLocus_subset_thickening N hε

/--
On the barycenter complement, the cutoff at every point of the transported radial
homotopy is at most the cutoff at its initial point.
-/
theorem cutoff_homotopyPoint_le (N : ℕ) (t : I)
    (q : SSet.toTop.obj (Δ[N] : SSet.{u}))
    (hx : (⦋N⦌.toTopHomeo) q ≠ Convexity.StdSimplex.barycenter) :
    cutoff N ((⦋N⦌.toTopHomeo).symm
      (StdSimplexRadialBoundary.homotopyPoint N t ((⦋N⦌.toTopHomeo) q) hx)) ≤
      cutoff N q := by
  unfold cutoff
  rw [Homeomorph.apply_symm_apply]
  exact StdSimplexRadialBoundary.radMin_homotopyPoint_le N t _ hx

/--
A point of a cutoff sublevel that is not the barycenter stays in that sublevel
throughout the transported radial homotopy.
-/
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
