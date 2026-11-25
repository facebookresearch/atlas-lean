/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CartesianMonoidal
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Constants
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MarkedMinimumMaximumPointIso
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.PushoutMarking
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SelectedEdges
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.TopMarkedCylinder

/-!
# Focused clients of the marked simplicial-set API

Concrete checks on the interval `Δ[1]`, whose identity edge is its only nondegenerate edge.

* Marked structures and their maps: marking the identity edge gives a monomorphism out of the
  minimal marking which is not an isomorphism, although its underlying map is the identity; a
  constant map is a marked map that is not a monomorphism; pulling the minimal marking back along a
  constant map marks the identity edge, while pulling it back along the identity does not.
* Products: the coordinate swap carries the marking of one product to the other, and the chosen
  tensor product of the Cartesian monoidal structure marks exactly what the product marks.
* The point is the boundary case: there the minimal and the maximal marking agree.
* Colimits and cylinders: the top-marked cylinder is an explicit pushout. In it the top identity
  edge is marked, although the product it is built from does not mark it, while the bottom identity
  edge stays unmarked; so the inclusion of the product is not an isomorphism.
-/

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.MarkedFocusedClients

open SSet SSet.stdSimplex SSet.Marked

/-! ### The interval -/

/-- The identity edge of the interval. -/
abbrev idEdge : (Δ[1] : SSet.{u}) _⦋1⦌ :=
  objMk₁ (1 : Fin 3)

/-- The first vertex of the interval. -/
abbrev v₀ : (Δ[1] : SSet.{u}) _⦋0⦌ :=
  objMk₁ (0 : Fin 2)

/-- The second vertex of the interval. -/
abbrev v₁ : (Δ[1] : SSet.{u}) _⦋0⦌ :=
  objMk₁ (1 : Fin 2)

/-- The interval with its minimal marking. -/
abbrev minInterval : Marked.{u} :=
  Marked.min (Δ[1] : SSet.{u})

theorem v₀_ne_v₁ : v₀.{u} ≠ v₁.{u} :=
  fun h => absurd (objMk₁_injective h) (by decide)

/-- Every degenerate edge of the interval is one of the two constant edges. -/
theorem degenerate_edge (x : (Δ[1] : SSet.{u}) _⦋0⦌) :
    (Δ[1] : SSet.{u}).σ (0 : Fin 1) x = objMk₁ (0 : Fin 3) ∨
      (Δ[1] : SSet.{u}).σ (0 : Fin 1) x = objMk₁ (2 : Fin 3) := by
  obtain ⟨i, rfl⟩ := objMk₁_surjective x
  fin_cases i
  · exact Or.inl (σ_objMk₁_of_le (0 : Fin 2) (0 : Fin 1) (by decide))
  · exact Or.inr (σ_objMk₁_of_lt (1 : Fin 2) (0 : Fin 1) (by decide))

/-- The identity edge is not marked in the minimal marking. -/
theorem idEdge_not_mem_min : idEdge.{u} ∉ minInterval.{u}.marking := by
  rintro ⟨x, hx⟩
  rcases degenerate_edge x with h | h
  · exact absurd (objMk₁_injective (h.symm.trans hx)) (by decide)
  · exact absurd (objMk₁_injective (h.symm.trans hx)) (by decide)

/-! ### Selected edges: a monomorphism that is not an isomorphism -/

/-- The interval with its identity edge marked as well. -/
abbrev markedInterval : Marked.{u} :=
  withEdges (Δ[1] : SSet.{u}) {idEdge}

theorem idEdge_mem_markedInterval : idEdge.{u} ∈ markedInterval.{u}.marking :=
  (mem_withEdges_iff _ _ _).mpr (Or.inr rfl)

/-- Selecting no edges gives the minimal marking. -/
theorem withEdges_empty_marking :
    (withEdges (Δ[1] : SSet.{u}) ∅).marking = minInterval.{u}.marking :=
  Set.union_empty _

/-- Enlarging the marking by the identity edge. -/
abbrev markIdEdge : withEdges (Δ[1] : SSet.{u}) ∅ ⟶ markedInterval.{u} :=
  withEdgesInclusion (Set.empty_subset _)

example : Mono markIdEdge.{u} :=
  withEdgesInclusion_mono _

/-- Its underlying map is the identity, an isomorphism. -/
example : IsIso markIdEdge.{u}.hom := by
  rw [withEdgesInclusion_hom]
  exact IsIso.id _

/-- But it is not an isomorphism of marked simplicial sets: an isomorphism reflects markings. -/
theorem markIdEdge_not_isIso : ¬ IsIso markIdEdge.{u} := by
  intro _
  have h : idEdge.{u} ∈ (withEdges (Δ[1] : SSet.{u}) ∅).marking :=
    (mem_marking_iff_of_iso (asIso markIdEdge.{u}) idEdge).mpr idEdge_mem_markedInterval
  rw [withEdges_empty_marking] at h
  exact idEdge_not_mem_min h

/-- A map out of the marked interval is a simplicial map that sends the identity edge to a marked
edge: into the minimal marking, the identity is not one. -/
example : ¬ ∃ f : markedInterval.{u} ⟶ minInterval.{u}, f.hom = 𝟙 _ := by
  rintro ⟨f, hf⟩
  have h := ((withEdgesHomEquiv _ _ _ f).property idEdge rfl)
  rw [show (withEdgesHomEquiv _ _ _ f).val = 𝟙 _ from hf] at h
  exact idEdge_not_mem_min h

/-! ### Constant maps: marked maps that are not monomorphisms -/

/-- A constant map is a marked map, here out of the marked interval into the minimal marking: the
identity edge goes to the degenerate edge at the chosen vertex. -/
theorem const_idEdge (y : (Δ[1] : SSet.{u}) _⦋0⦌) :
    (Marked.const (X := markedInterval.{u}) (Y := minInterval) y).hom.app (op ⦋1⦌) idEdge =
      (Δ[1] : SSet.{u}).σ (0 : Fin 1) y :=
  const_app_one (X := markedInterval.{u}) (Y := minInterval) y idEdge

/-- A constant map identifies the two vertices, so it is not a monomorphism. -/
theorem const_not_mono (y : (Δ[1] : SSet.{u}) _⦋0⦌) :
    ¬ Mono (Marked.const (X := markedInterval.{u}) (Y := minInterval) y) := by
  intro _
  have hinj := Hom.injective_app (Marked.const (X := markedInterval.{u}) (Y := minInterval) y) ⦋0⦌
  have h : (Marked.const (X := markedInterval.{u}) (Y := minInterval) y).hom.app (op ⦋0⦌) v₀ =
      (Marked.const (X := markedInterval.{u}) (Y := minInterval) y).hom.app (op ⦋0⦌) v₁ :=
    rfl
  exact v₀_ne_v₁ (hinj h)

/-! ### Pulling markings back -/

/-- Along a constant map every edge is marked, the identity edge included. -/
theorem idEdge_mem_comap_const (y : (Δ[1] : SSet.{u}) _⦋0⦌) :
    idEdge.{u} ∈ (comap minInterval.{u} (SSet.const y)).marking :=
  (Marked.const (X := Marked.max (Δ[1] : SSet.{u})) (Y := minInterval) y).preserve (Set.mem_univ _)

/-- Along the identity the marking stays minimal, so the identity edge stays unmarked. -/
theorem idEdge_not_mem_comap_id : idEdge.{u} ∉ (comap minInterval.{u} (𝟙 _)).marking :=
  fun h => idEdge_not_mem_min h

example : comap minInterval.{u} (𝟙 _) = minInterval :=
  comap_id _

/-! ### Products and the Cartesian monoidal structure -/

/-- The product of the maximally and the minimally marked interval. -/
abbrev maxMin : Marked.{u} :=
  prod (Marked.max (Δ[1] : SSet.{u})) minInterval

/-- The product with the factors in the other order. -/
abbrev minMax : Marked.{u} :=
  prod minInterval (Marked.max (Δ[1] : SSet.{u}))

/-- The swap exchanges the coordinates. -/
theorem swap_apply (a b : (Δ[1] : SSet.{u}) _⦋1⦌) :
    (prodSwapIso (Marked.max (Δ[1] : SSet.{u})) minInterval).hom.hom.app (op ⦋1⦌)
      ((a, b) : maxMin.{u}.toSSet _⦋1⦌) = (b, a) :=
  rfl

/-- It carries the marked edge `(id, σ v)` of `max × min` to an edge of `min × max`, namely
`(σ v, id)`, which is marked there. -/
theorem swap_marked (v : (Δ[1] : SSet.{u}) _⦋0⦌) :
    (prodSwapIso (Marked.max (Δ[1] : SSet.{u})) minInterval).hom.hom.app (op ⦋1⦌)
      ((idEdge.{u}, (Δ[1] : SSet.{u}).σ (0 : Fin 1) v) : maxMin.{u}.toSSet _⦋1⦌) ∈
        minMax.{u}.marking :=
  (prodSwapIso _ _).hom.preserve ⟨Set.mem_univ _, ⟨v, rfl⟩⟩

/-- An isomorphism reflects markings: the swap of the unmarked edge `(id, id)` is unmarked. -/
theorem swap_unmarked :
    (prodSwapIso (Marked.max (Δ[1] : SSet.{u})) minInterval).hom.hom.app (op ⦋1⦌)
      ((idEdge.{u}, idEdge.{u}) : maxMin.{u}.toSSet _⦋1⦌) ∉ minMax.{u}.marking :=
  fun h => idEdge_not_mem_min ((mem_marking_iff_of_iso (prodSwapIso _ _) _).mpr h).2

section CartesianMonoidal

attribute [local instance] cartesianMonoidalCategory

/-- The chosen tensor product is the product: it marks `(id, σ v)` ... -/
example (v : (Δ[1] : SSet.{u}) _⦋0⦌) :
    ((idEdge.{u}, (Δ[1] : SSet.{u}).σ (0 : Fin 1) v) :
        (Marked.max (Δ[1] : SSet.{u}) ⊗ minInterval).toSSet _⦋1⦌) ∈
      (Marked.max (Δ[1] : SSet.{u}) ⊗ minInterval).marking :=
  ⟨Set.mem_univ _, ⟨v, rfl⟩⟩

/-- ... but not `(id, id)`. -/
example :
    ((idEdge.{u}, idEdge.{u}) : (Marked.max (Δ[1] : SSet.{u}) ⊗ minInterval).toSSet _⦋1⦌) ∉
      (Marked.max (Δ[1] : SSet.{u}) ⊗ minInterval).marking :=
  fun h => idEdge_not_mem_min h.2

/-- The unit is the maximally marked point. -/
example : 𝟙_ Marked.{u} = Marked.max (Δ[0] : SSet.{u}) :=
  cartesianMonoidal_unit

end CartesianMonoidal

/-- Boundary case: on the point the minimal and the maximal marking agree, through the identity. -/
example : (minimumMaximumPointIso.{u}).hom.hom = 𝟙 (Δ[0] : SSet.{u}) := by
  rw [minimumMaximumPointIso_hom]
  rfl

/-! ### Colimits: the top-marked cylinder is an explicit pushout -/

/-- The top-marked cylinder on the minimally marked interval. -/
noncomputable abbrev cyl : Marked.{u} :=
  topMarkedCylinder minInterval.{u}

/-- The square that presents it as a pushout. -/
theorem cyl_isPushout :
    IsPushout (markedCylinderTop minInterval.{u})
      (toMax (𝟙 minInterval.{u}.toSSet) : minInterval.{u} ⟶ Marked.max minInterval.{u}.toSSet)
      (topMarkedCylinderInl minInterval.{u}) (topMarkedCylinderInr minInterval.{u}) :=
  IsPushout.of_isColimit (topMarkedCylinderIsColimit minInterval.{u})

/-- The top identity edge is marked in the cylinder: it comes from the maximally marked side. -/
theorem top_edge_mem : (SSet.ι₁ (X := (Δ[1] : SSet.{u}))).app (op ⦋1⦌) idEdge ∈ cyl.{u}.marking :=
  (mem_marking_of_isPushout_iff cyl_isPushout _).mpr (Or.inr ⟨idEdge, Set.mem_univ _, rfl⟩)

/-- But the product the cylinder is built from does not mark it. -/
theorem top_edge_not_mem_prod :
    (SSet.ι₁ (X := (Δ[1] : SSet.{u}))).app (op ⦋1⦌) idEdge ∉
      (prod minInterval.{u} minInterval).marking :=
  fun h => idEdge_not_mem_min h.1

/-- The bottom identity edge stays unmarked: it comes from neither side of the pushout. -/
theorem bottom_edge_not_mem :
    (SSet.ι₀ (X := (Δ[1] : SSet.{u}))).app (op ⦋1⦌) idEdge ∉ cyl.{u}.marking := by
  intro he
  rcases (mem_marking_of_isPushout_iff cyl_isPushout _).mp he with ⟨x, hx, hxe⟩ | ⟨y, -, hye⟩
  · have : x = (SSet.ι₀ (X := (Δ[1] : SSet.{u}))).app (op ⦋1⦌) idEdge := hxe
    subst this
    exact idEdge_not_mem_min hx.1
  · have h := congrArg (fun p : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) _⦋1⦌ => p.2 0) hye
    change (1 : Fin 2) = 0 at h
    exact absurd h (by decide)

/-- So the inclusion of the product into the cylinder, the identity underneath, is not an
isomorphism. -/
theorem cylInl_not_isIso : ¬ IsIso (topMarkedCylinderInl minInterval.{u}) := by
  intro _
  exact top_edge_not_mem_prod
    ((mem_marking_iff_of_iso (asIso (topMarkedCylinderInl minInterval.{u}))
      ((SSet.ι₁ (X := (Δ[1] : SSet.{u}))).app (op ⦋1⦌) idEdge)).mpr top_edge_mem)

/-- The bottom and the top inclusion of the cylinder differ. -/
theorem bottom_ne_top : markedCylinderBottom minInterval.{u} ≠ markedCylinderTop minInterval := by
  intro h
  have := congrArg (fun f : minInterval.{u} ⟶ prod minInterval minInterval =>
    (fun p : (Δ[1] : SSet.{u}) _⦋0⦌ => p 0) (f.hom.app (op ⦋0⦌) v₀).2) h
  change (0 : Fin 2) = 1 at this
  exact absurd this (by decide)

end MathlibExtTest.AlgebraicTopology.SimplicialSet.MarkedFocusedClients
