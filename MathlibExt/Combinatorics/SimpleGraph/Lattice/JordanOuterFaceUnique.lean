/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.PlanarDual
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.UniqueInfiniteComponent
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.PlanarFaceGeometric
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.CycleRank

/-!
# The region graph has a unique infinite component

For a `PlanarZ2Subgraph` `P`, the region graph agrees with the lattice outside a box containing the
image of `P`, so it has exactly one infinite component, the outer region. A component is bounded iff
it is not the outer region; hence, when there are finitely many components, the number of finite
regions plus one is the number of components.

## Main definitions

* `StatMech.Lattice.outerBoxRadius P`: a radius `R` with the image of `P` inside `box 2 R`.
* `StatMech.Lattice.outerRegion P`: the component of the region graph containing the far site
  `beacon 2 R`.

## Main results

* `StatMech.Lattice.regionGraph_unique_infinite_component`: the region graph has a unique infinite
  component.
* `StatMech.Lattice.boundedRegion_iff_ne_outer`: a component is finite iff it is not the outer
  region.
* `StatMech.Lattice.geometricRegionCount_add_one_eq_card`: finite regions plus one equals the number
  of components.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- A radius `R` such that the image of `P` lies in `box 2 R`. -/
noncomputable def outerBoxRadius (P : PlanarZ2Subgraph) : ℕ := (image_subset_box P).choose

theorem outerBoxRadius_spec (P : PlanarZ2Subgraph) :
    ∀ v : P.V, P.emb v ∈ box 2 (outerBoxRadius P) :=
  (image_subset_box P).choose_spec

/-- The outer region: the component of the region graph containing the far site `beacon 2 R`. -/
noncomputable def outerRegion (P : PlanarZ2Subgraph) :
    (regionGraph (imageGraph P)).ConnectedComponent :=
  (regionGraph (imageGraph P)).connectedComponentMk (beacon 2 (outerBoxRadius P))

theorem exterior_in_outerRegion (P : PlanarZ2Subgraph) {x : Site 2}
    (hx : x ∈ exterior 2 (outerBoxRadius P)) :
    (regionGraph (imageGraph P)).connectedComponentMk x = outerRegion P := by
  set R := outerBoxRadius P with hR
  have hRbox := outerBoxRadius_spec P
  have hb_ext : beacon 2 R ∈ exterior 2 R := beacon_mem_exterior R (by omega)
  exact ConnectedComponent.sound
    (regionGraph_reachable_of_exterior P R hRbox hx hb_ext
      (box_exterior_connected R (by omega) x (beacon 2 R) hx hb_ext))

theorem outerRegion_infinite (P : PlanarZ2Subgraph) :
    (outerRegion P).supp.Infinite := by
  set R := outerBoxRadius P with hR
  have : Infinite ↥(exterior 2 R) := (exterior_infinite R (by omega)).to_subtype
  refine Set.infinite_of_injective_forall_mem
    (f := fun w : ↥(exterior 2 R) => (w : Site 2)) ?_ ?_
  · intro a b hab; exact Subtype.ext hab
  · intro w
    rw [ConnectedComponent.mem_supp_iff]
    exact exterior_in_outerRegion P w.2

theorem infiniteComponent_meets_exterior (P : PlanarZ2Subgraph)
    {C : (regionGraph (imageGraph P)).ConnectedComponent} (hC : C.supp.Infinite) :
    ∃ x ∈ C.supp, x ∈ exterior 2 (outerBoxRadius P) := by
  set R := outerBoxRadius P with hR
  by_contra hcon
  push Not at hcon
  have hsubbox : C.supp ⊆ box 2 R := by
    intro v hv
    have hvnotext : v ∉ exterior 2 R := hcon v hv
    rw [exterior_eq_compl_box, Set.mem_compl_iff, not_not] at hvnotext
    exact hvnotext
  exact hC ((box_finite 2 R).subset hsubbox)

theorem regionGraph_unique_infinite_component (P : PlanarZ2Subgraph) :
    ∃! C : (regionGraph (imageGraph P)).ConnectedComponent, C.supp.Infinite := by
  refine ⟨outerRegion P, outerRegion_infinite P, ?_⟩
  intro C hCinf
  obtain ⟨x, hx_supp, hx_ext⟩ := infiniteComponent_meets_exterior P hCinf
  have h1 : (regionGraph (imageGraph P)).connectedComponentMk x = C :=
    (C.mem_supp_iff x).mp hx_supp
  have h2 : (regionGraph (imageGraph P)).connectedComponentMk x = outerRegion P :=
    exterior_in_outerRegion P hx_ext
  rw [← h1, h2]

theorem outerRegion_eq_of_infinite (P : PlanarZ2Subgraph)
    {C : (regionGraph (imageGraph P)).ConnectedComponent} (hC : C.supp.Infinite) :
    C = outerRegion P :=
  ((regionGraph_unique_infinite_component P).unique hC (outerRegion_infinite P))

theorem boundedRegion_iff_ne_outer (P : PlanarZ2Subgraph)
    (C : (regionGraph (imageGraph P)).ConnectedComponent) :
    C.supp.Finite ↔ C ≠ outerRegion P := by
  constructor
  · intro hfin hcon
    rw [hcon] at hfin
    exact (outerRegion_infinite P) hfin
  · intro hne
    by_contra hinf
    rw [Set.not_finite] at hinf
    exact hne (outerRegion_eq_of_infinite P hinf)

/-- The finite components of the region graph are exactly the components other than the outer
region. -/
def boundedRegionEquivNeOuter (P : PlanarZ2Subgraph) :
    {C : (regionGraph (imageGraph P)).ConnectedComponent // C.supp.Finite} ≃
      {C : (regionGraph (imageGraph P)).ConnectedComponent // C ≠ outerRegion P} :=
  Equiv.subtypeEquivRight (boundedRegion_iff_ne_outer P)

theorem geometricRegionCount_add_one_eq_card
    (P : PlanarZ2Subgraph)
    [Finite (regionGraph (imageGraph P)).ConnectedComponent] :
    geometricRegionCount P + 1 =
      Nat.card (regionGraph (imageGraph P)).ConnectedComponent := by
  unfold geometricRegionCount
  rw [Nat.card_congr (boundedRegionEquivNeOuter P), card_subtype_ne_add_one]

end Lattice

end StatMech
