/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BdEdgeMatchStarHull
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.EulerGeometricFaces
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanLeftRegionInterior

/-!
# A finite set with the boundary edges of a closed walk is its inside

Let `Vc` be a closed walk in the square lattice `ℤ²` and let `jec_leftRegion Vc` be its inside by
the even–odd rule: the sites `z` for which the leftward horizontal ray from the face centre
`z - (1/2, 1/2)` crosses `Vc` an odd number of times. Two subsets of `ℤ²` with the same boundary
edges are equal or complementary. When the support of `Vc` lies in a
box, its inside is finite and the complement of the inside is infinite, so a *finite* set `K` with
the same boundary edges as the inside must equal the inside.

## Main results

* `StatMech.Lattice.bemc_bdEdge_iff_support_flip`: a lattice edge is a boundary edge of the inside
  exactly when its endpoints lie on opposite sides; such edges touch the support of `Vc`.
* `StatMech.Lattice.bemc_compl_leftRegion_infinite`: the outside of a closed walk in a box is
  infinite.
* `StatMech.Lattice.bemc_bdEdgeMatch_iff_leftRegion_eq`: a finite set has the same boundary edges
  as the inside of `Vc` if and only if it equals the inside.
* `StatMech.Lattice.bemc_dcd_windingRegion_orientation`: the inside is finite, its complement is
  infinite, and its boundary edges are exactly the boundary edges touching the support of `Vc`.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- For a lattice edge `{u, v}`, being a boundary edge of the inside of `Vc` is equivalent to `u`
and `v` lying on opposite sides together with one of them lying on `Vc`; the second condition is
automatic (`StatMech.Lattice.jec_leftRegion_bdEdge_support`). -/
theorem bemc_bdEdge_iff_support_flip {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v) :
    bdEdge (jec_leftRegion Vc) s(u, v) ↔
      ((u ∈ jec_leftRegion Vc ↔ v ∉ jec_leftRegion Vc) ∧
        (u ∈ Vc.support ∨ v ∈ Vc.support)) := by
  constructor
  · intro hbd
    refine ⟨(bdEdge_mk _ u v).mp hbd,
      jec_leftRegion_bdEdge_support Vc hadj hbd⟩
  · rintro ⟨hflip, _⟩
    exact (bdEdge_mk _ u v).mpr hflip

/-- The outside of a closed walk whose support lies in the box `box 2 R` is infinite: it contains
the exterior of the box. -/
theorem bemc_compl_leftRegion_infinite {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
    (jec_leftRegion Vc)ᶜ.Infinite := by
  have hsub : exterior 2 R ⊆ (jec_leftRegion Vc)ᶜ :=
    fun z hz => egf_exterior_outside Vc R hsupp hz
  exact (exterior_infinite R (by norm_num)).mono hsub

/-- Of the inside of `Vc` and its complement, only the inside can be finite: a finite set equal to
one of them equals the inside. -/
theorem bemc_orientation_selected {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) {K : Set (Site 2)} (hKfin : K.Finite)
    (hid : K = jec_leftRegion Vc ∨ K = (jec_leftRegion Vc)ᶜ) :
    K = jec_leftRegion Vc := by
  rcases hid with h | h
  · exact h
  · exact absurd (h ▸ hKfin) (bemc_compl_leftRegion_infinite Vc R hsupp)

/-- A finite set with the same boundary edges as the inside of a closed walk in a box equals that
inside. -/
theorem bemc_leftRegion_eq_of_bdEdgeMatch {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) {K : Set (Site 2)} (hKfin : K.Finite)
    (hmatch : pww_BdEdgeMatch K Vc) :
    K = jec_leftRegion Vc :=
  bemc_orientation_selected Vc R hsupp hKfin
    ((pbs_bdEdgeMatch_iff_setIdentity Vc).mp hmatch)

/-- **Boundary edges determine a finite region.** For a closed walk `Vc` with support in a box and
a finite set `K ⊆ ℤ²`, `K` has the same boundary edges as the inside of `Vc` if and only if `K`
equals the inside. See also `StatMech.Lattice.pbs_bdEdgeMatch_iff_setIdentity`, which without the
finiteness hypothesis gives "equal or complementary". -/
theorem bemc_bdEdgeMatch_iff_leftRegion_eq {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) {K : Set (Site 2)} (hKfin : K.Finite) :
    pww_BdEdgeMatch K Vc ↔ K = jec_leftRegion Vc := by
  constructor
  · intro hmatch
    exact bemc_leftRegion_eq_of_bdEdgeMatch Vc R hsupp hKfin hmatch
  · intro heq
    exact pbs_bdEdgeMatch_of_leftRegion_eq Vc heq

/-- Summary of the inside of a closed walk `Vc` in a box: it is finite, its complement is infinite,
every boundary edge touches the support of `Vc`, and no lattice edge with both endpoints off the
support is a boundary edge. -/
theorem bemc_dcd_windingRegion_orientation {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
    (jec_leftRegion Vc).Finite ∧ (jec_leftRegion Vc)ᶜ.Infinite ∧
      (∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
        (bdEdge (jec_leftRegion Vc) s(u, v) →
          (u ∈ Vc.support ∨ v ∈ Vc.support)) ∧
        (u ∉ Vc.support → v ∉ Vc.support →
          ¬ bdEdge (jec_leftRegion Vc) s(u, v))) := by
  refine ⟨egf_leftRegion_finite Vc R hsupp, bemc_compl_leftRegion_infinite Vc R hsupp, ?_⟩
  intro u v hadj
  exact ⟨jec_leftRegion_bdEdge_support Vc hadj,
    jlri_no_bdEdge_off_support Vc hadj⟩

end Lattice

end StatMech
