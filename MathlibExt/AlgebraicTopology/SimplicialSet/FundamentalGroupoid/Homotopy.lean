/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

-- BACKPORT: Full-file copy of
-- `Mathlib/AlgebraicTopology/SimplicialSet/FundamentalGroupoid/Homotopy.lean`
-- from PR `leanprover-community/mathlib4#42576` at commit
-- `28fbf220a205c47649528c7daacf165f7618caf8`,
-- blob `863ff98a547c483d74dac8629e8f11d9d8b3ca3b`.
-- Import adaptation: `Mathlib.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic`
-- → `MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic`;
-- `Mathlib.AlgebraicTopology.SimplicialSet.Homotopy` is kept (pinned on 4.33).
-- Deletion rule: delete this module and replace the `MathlibExt` import with
-- `Mathlib.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Homotopy`
-- once the pinned Mathlib provides the file; see `BACKPORTS.md`.
-- See `BACKPORTS.md` for provenance and upgrade-removal steps.

public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
# Provenance and upgrade note

This file is a temporary local copy of
`Mathlib/AlgebraicTopology/SimplicialSet/FundamentalGroupoid/Homotopy.lean`
from PR `leanprover-community/mathlib4#42576` at head commit
`28fbf220a205c47649528c7daacf165f7618caf8` (file blob
`863ff98a547c483d74dac8629e8f11d9d8b3ca3b`). The copy was prepared for the
pinned Mathlib `v4.33.0` (`db584cd`) on Lean `4.33`.

## Source

* PR: `leanprover-community/mathlib4#42576`
* PR head: `28fbf220a205c47649528c7daacf165f7618caf8`
* File: `Mathlib/AlgebraicTopology/SimplicialSet/FundamentalGroupoid/Homotopy.lean`
* Blob: `863ff98a547c483d74dac8629e8f11d9d8b3ca3b`
* Upstream author: Joël Riou (copyright header in upstream source)
* Durable provenance: `BACKPORTS.md`

## Copied surface

Full 121-line upstream file preserving implementation, namespaces, universes,
attributes, theorem statements, and proof bodies. Upstream declarations include:

* `SSet.Edge.ofSimplicialObjectHomotopy`
* `SSet.Edge.ofSimplicialObjectHomotopy_edge`
* `SSet.Edge.diagOfSimplicialObjectHomotopy`
* `SSet.Edge.diagOfSimplicialObjectHomotopy_edge`
* `SSet.Edge.diagOfSimplicialObjectHomotopy_edge'`
* `SSet.Edge.CompStruct.ofSimplicialObjectHomotopy`
* `SSet.Edge.CompStruct.ofSimplicialObjectHomotopy'`
* `SSet.congrMapFundamentalGroupoid'`
* `SSet.congrMapFundamentalGroupoid`

## Adaptations for Lean 4.33 pin

* `Mathlib.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic` →
  `MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic`
  (provides the accepted local compatibility layer for the upstream `Basic`
  file from PR #42587, blob `ee7aba11`, required for `Edge`, `CompStruct`,
  `mapFundamentalGroupoid`, `homMk`, etc.)
* `Mathlib.AlgebraicTopology.SimplicialSet.Homotopy` kept as pinned (present
  in `v4.33.0` / `v4.34.0-rc2`).

No proof bodies, signatures, attributes, or universe parameters were otherwise
changed. Lean 4.33 required only the single import-path adaptation above.

## Removal rule

Delete this module
`MathlibExt/AlgebraicTopology/SimplicialSet/FundamentalGroupoid/Homotopy.lean`
and replace its `MathlibExt` import with the canonical
`Mathlib.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Homotopy`
once the pinned Mathlib contains the file (i.e. PR #42576 is merged).
After deletion, regenerate roots with `scripts/mk_all.sh --no-build` in a
separate Avocado task and rebuild `MathlibExt`.

-/

/-!
# Homotopic maps induce isomorphisms functors on the fundamental groupoid

The main definition in this file is `SSet.congrMapFundamentalGroupoid`.
Given two morphisms of simplicial sets `f : X ⟶ Y` and `g : X ⟶ Y`
and a homotopy `h : Homotopy f g`, this is an isomorphism between
the functors `mapFundamentalGroupoid f` and `mapFundamentalGroupoid g`.

## Implementation notes

We first define the variant `SSet.congrMapFundamentalGroupoid'`
which takes as an input a combinatorial simplicial homotopy
(as `h : SimplicialObject.Homotopy f g`), and then we deduce the result
for terms in `SSet.Homotopy f g` which involve a morphism `X ⊗ Δ[1] ⟶ Y`.

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
