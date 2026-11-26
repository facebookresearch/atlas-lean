/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.WindingWitness

/-!
# Ray parity versus crossing parity

Let `Vc` be a closed walk in the square lattice and `γ` a walk from a site `z₀` to a site `q`
lying weakly left of every vertex of `Vc` (so `q` has ray count zero). Then `z₀` has odd ray count
with respect to `Vc` iff `γ` crosses the boundary of the even–odd inside `jec_leftRegion Vc` an odd
number of times. If a set `K` has the same boundary edges as that inside, crossings of `K` and of
the inside have the same parity; so a site of `K` joined to a site outside `K` left of the loop
has odd ray count. Applied to the face loop of a boundary orbit, this produces the odd dart tail
required by `wwit_TailOdd`.

## Main results

* `StatMech.Lattice.ral_oddRay_iff_oddCross_leftRegion`: odd ray count iff odd number of boundary
  crossings of the inside along a walk to a far-left site.
* `StatMech.Lattice.ral_inRegion_rayCount_odd`: if `K` and the inside of `Vc` have the same
  boundary edges, every site of `K` joined to a far-left site outside `K` has odd ray count.
* `StatMech.Lattice.ral_tailOdd_of_bdEdgeMatch`: the same for the face loop of a boundary orbit,
  giving `wwit_TailOdd`.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- For a closed walk `Vc` and a walk `γ` from `z₀` to a site `q` weakly left of every vertex of
`Vc`, the ray count of `z₀` is odd iff `γ` crosses the boundary of `jec_leftRegion Vc` an odd
number of times. Generalizes `pww_oddRay_iff_oddCross_leftRegion` from the origin to an arbitrary
start `z₀`. -/
theorem ral_oddRay_iff_oddCross_leftRegion {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z₀ q : Site 2} (hq : ∀ p ∈ Vc.support, q 0 ≤ p 0)
    (γ : (hypercubicLattice 2).Walk z₀ q) :
    (¬ Even (jec_rayCount z₀ Vc)) ↔ (¬ Even (crossCount (jec_leftRegion Vc) γ)) := by
  have hqout : ¬ ¬ Even (jec_rayCount q Vc) :=
    not_not.mpr (by rw [jec_rayCount_eq_zero_of_right q Vc hq]; exact Nat.even_iff.mpr rfl)
  have hpar := crossCount_parity (jec_leftRegion Vc) γ
  simp only [jec_mem_leftRegion] at hpar
  constructor
  · intro hodd heven
    exact hqout ((hpar.mp heven).mp hodd)
  · intro hcrossOdd hray
    apply hcrossOdd
    rw [hpar]
    exact ⟨fun h => absurd h (not_not.mpr hray), fun h => absurd h hqout⟩

/-- If `K` and the even–odd inside of `Vc` have the same boundary edges, a site `z₀ ∈ K` joined by
a walk to a site `q ∉ K` weakly left of `Vc` has odd ray count. Generalizes
`pww_oddRay_of_bdEdge_match` from the origin cluster to an arbitrary set. -/
theorem ral_inRegion_rayCount_odd {K : Set (Site 2)} {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (hmatch : pww_BdEdgeMatch K Vc)
    {z₀ q : Site 2} (hz₀K : z₀ ∈ K) (hqK : q ∉ K)
    (hqfar : ∀ p ∈ Vc.support, q 0 ≤ p 0)
    (γ : (hypercubicLattice 2).Walk z₀ q) :
    ¬ Even (jec_rayCount z₀ Vc) := by
  have hoddK : ¬ Even (crossCount K γ) :=
    crossCount_odd_of_separated K hz₀K hqK γ
  have heq : crossCount (jec_leftRegion Vc) γ = crossCount K γ :=
    pww_crossCount_eq_of_bdEdge_match (jec_leftRegion Vc) K (fun e => (hmatch e).symm) γ
  have hoddL : ¬ Even (crossCount (jec_leftRegion Vc) γ) := by rw [heq]; exact hoddK
  exact (ral_oddRay_iff_oddCross_leftRegion Vc hqfar γ).mpr hoddL

/-- If `K` and the inside of the face loop of the orbit of `a` have the same boundary edges, and
the tail of `a` is joined to a site outside `K` weakly left of the loop, then `wwit_TailOdd` holds.
-/
theorem ral_tailOdd_of_bdEdgeMatch (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e})
    (hmatch : pww_BdEdgeMatch K (olb_orbitLoop K hK a.1 a.2))
    {q : Site 2} (hqK : q ∉ K)
    (hqfar : ∀ p ∈ (olb_orbitLoop K hK a.1 a.2).support, q 0 ≤ p 0)
    (γ : (hypercubicLattice 2).Walk a.1.tail q) :
    wwit_TailOdd K hK a := by
  refine ⟨0, ?_⟩
  simp only [Function.iterate_zero, id_eq]
  exact ral_inRegion_rayCount_odd (olb_orbitLoop K hK a.1 a.2) hmatch a.2.tail_mem hqK hqfar γ

end Lattice

end StatMech
