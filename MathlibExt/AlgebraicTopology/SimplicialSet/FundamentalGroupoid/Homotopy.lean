/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
See NOTICE in the repository root for the original Mathlib attribution.
-/

module

-- BACKPORT: Homotopy/functor comparisons from Mathlib PR #42576,
-- head `28fbf220a205c47649528c7daacf165f7618caf8`,
-- `Mathlib/AlgebraicTopology/SimplicialSet/FundamentalGroupoid/Homotopy.lean`,
-- blob `863ff98a547c483d74dac8629e8f11d9d8b3ca3b`.
-- The canonical core and seven-helper adapter are reused; see `BACKPORTS.md`.

public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
# Homotopies and fundamental-groupoid functor comparison

A combinatorial simplicial homotopy gives original endpoint and diagonal edges with their
composition triangles. These construct a natural isomorphism between the fundamental-groupoid
functors of the two original simplicial maps. The same comparison is obtained for a homotopy
expressed as a map from the Cartesian product with the interval.

The compatibility scope against Mathlib 4.35.0 (`56a005855ea17e0b0958f73ec801ae140b0a1679`) and
its removal conditions are recorded in `BACKPORTS.md`.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial

namespace SSet

variable {X Y : SSet.{u}} {f g : X ⟶ Y}

namespace Edge

open ConcreteCategory

variable (h : SimplicialObject.Homotopy f g)

/-- The edge connecting `f.app _ x` and `g.app _ x`
when `h : SimplicialObject.Homotopy f g` and `x` is a `0`-simplex. -/
def ofSimplicialObjectHomotopy (x : X _⦋0⦌) :
    Edge (f.app _ x) (g.app _ x) :=
  Edge.mk (h.h 0 x) (by rw [← (h.h_last_comp_δ_last 0)]; dsimp)
    (by rw [← SimplicialObject.Homotopy.h_zero_comp_δ_zero]; dsimp)

@[simp]
lemma ofSimplicialObjectHomotopy_edge (x : X _⦋0⦌) :
  (Edge.ofSimplicialObjectHomotopy h x).edge = h.h 0 x := rfl

variable {x y : X _⦋0⦌} (e : Edge x y)

/-- Given `h : SimplicialObject.Homotopy f g` and an edge `e : Edge x y`,
this is the edge that is the diagonal of the "commutative square" involving
`f.app _ x`, `g.app _ x`, `g.app _ y` and `f.app _ y`. -/
@[no_expose]
def diagOfSimplicialObjectHomotopy :
    Edge (f.app _ x) (g.app _ y) :=
  Edge.mk (Y.δ 1 (h.h 1 e.edge)) (by
    rw [dsimp% congr_hom (h.h_succ_comp_δ_castSucc_succ (n := 0) 0) e.edge,
      ← dsimp% Y.δ_comp_δ_apply (i := 1) (j := 1) (by simp),
      dsimp% congr_hom (h.h_castSucc_comp_δ_succ_of_lt (n := 0) 1 0 (by simp)) e.edge,
      e.src_eq, ← h.h_last_comp_δ_last 0]
    dsimp) (by
    rw [dsimp% Y.δ_comp_δ_apply (i := 0) (j := 0) (by simp),
      dsimp% congr_hom (h.h_succ_comp_δ_castSucc_of_lt 0 0 (by simp)) e.edge,
      tgt_eq, dsimp% congr_hom (h.h_zero_comp_δ_zero 0) y])

lemma diagOfSimplicialObjectHomotopy_edge :
    (diagOfSimplicialObjectHomotopy h e).edge = Y.δ 1 (h.h 1 e.edge) := by rfl

lemma diagOfSimplicialObjectHomotopy_edge' :
    (diagOfSimplicialObjectHomotopy h e).edge = Y.δ 1 (h.h 0 e.edge) :=
  congr_hom (h.h_succ_comp_δ_castSucc_succ (n := 0) 0) e.edge

/-- One of the two "triangles" of the "commutative square" that
`diagOfSimplicialObjectHomotopy h e` is part of,
when `h : SimplicialObject.Homotopy f g` and `e` is an edge. -/
def CompStruct.ofSimplicialObjectHomotopy :
    Edge.CompStruct (e.map f) (.ofSimplicialObjectHomotopy h y)
      (diagOfSimplicialObjectHomotopy h e) :=
  CompStruct.mk (h.h 1 e.edge) (by simp [← h.h_last_comp_δ_last 1])
    (by simpa using congr_hom (h.h_succ_comp_δ_castSucc_of_lt 0 0
      (by simp)) e.edge) (by simp [diagOfSimplicialObjectHomotopy_edge])

/-- One of the two "triangles" of the "commutative square" that
`diagOfSimplicialObjectHomotopy h e` is part of,
when `h : SimplicialObject.Homotopy f g` and `e` is an edge. -/
def CompStruct.ofSimplicialObjectHomotopy' :
    Edge.CompStruct (.ofSimplicialObjectHomotopy h x) (e.map g)
      (diagOfSimplicialObjectHomotopy h e) :=
  CompStruct.mk (h.h 0 e.edge)
    (by simpa using congr_hom (h.h_castSucc_comp_δ_succ_of_lt 1 0 (by simp)) e.edge)
    (congr_hom (h.h_zero_comp_δ_zero 1) e.edge)
    (by simp [diagOfSimplicialObjectHomotopy_edge'])

end Edge

open FundamentalGroupoid Edge.CompStruct in
/-- Two homotopic maps of simplicial sets (where the homotopy is given
by a term in `SimplicialObject.Homotopy`) induce isomorphic functors
between the fundamental groupoids. -/
noncomputable def congrMapFundamentalGroupoid' (h : SimplicialObject.Homotopy f g) :
    mapFundamentalGroupoid f ≅ mapFundamentalGroupoid g := by
  with_unfolding_all
    exact natIsoMk (fun x ↦ asIso (homMk (Edge.ofSimplicialObjectHomotopy h x)))
      (fun {x y} e ↦ by
        with_unfolding_all
          simp only [mapFundamentalGroupoid_map_homMk, asIso_hom]
          change homMk (e.map f) ≫ homMk (Edge.ofSimplicialObjectHomotopy h y) =
            homMk (Edge.ofSimplicialObjectHomotopy h x) ≫ homMk (e.map g)
          exact (ofSimplicialObjectHomotopy h e).homMk_comp.trans
            (ofSimplicialObjectHomotopy' h e).homMk_comp.symm)

/-- Two homotopic maps of simplicial sets (where the homotopy is given
by a term in `SSet.Homotopy`) induce isomorphic functors
between the fundamental groupoids. -/
noncomputable def congrMapFundamentalGroupoid (h : Homotopy f g) :
    mapFundamentalGroupoid f ≅ mapFundamentalGroupoid g :=
  congrMapFundamentalGroupoid' h.toSimplicialObjectHomotopy

end SSet
