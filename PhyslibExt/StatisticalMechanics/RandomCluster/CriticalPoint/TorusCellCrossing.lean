/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Onsager.Torus

/-!
# Edges of the discrete torus and the cell crossing

Coordinates for the edges of the `L × L` torus and the cell-crossing bijection that sends each edge
to the dual edge crossing it.

## i. Overview

Each torus edge is coded by its base site and orientation (`torusEdgeCodeEquiv`). The cell crossing
`torusCellCrossing` rotates a horizontal edge at `(x, y)` to the vertical edge at `(x, y - 1)` and a
vertical edge to a horizontal one; it is a bijection of the torus edges. All results are
unconditional.

## ii. Key results

- `torusEdgeCodeEquiv`: edges are coded by site and orientation.
- `torusCellCrossing_horizontal`, `torusCellCrossing_vertical`: explicit form of the crossing.

## iii. Table of contents

- A. Edge codes
- B. The cell crossing

## iv. References

* V. Beffara, H. Duminil-Copin, *The self-dual point of the two-dimensional random-cluster model is
  critical for q ≥ 1*, Probab. Theory Related Fields 153 (2012).
-/

@[expose] public section

open SimpleGraph

namespace StatMech.BeffaraDC

open StatMech.Onsager

/-! ## A. Edge codes -/

/-- The orientation of a torus edge: horizontal or vertical. -/
inductive TorusEdgeOrientation
  | horizontal
  | vertical
  deriving DecidableEq

/-- A torus edge code: a base site and an orientation. -/
abbrev TorusEdgeCode (L : ℕ) :=
  (ZMod L × ZMod L) × TorusEdgeOrientation

/-- The edges of the `L × L` torus graph. -/
abbrev TorusAmbientEdge (L : ℕ) [Fact (2 < L)] :=
  {e : Sym2 (ZMod L × ZMod L) // e ∈ (onsTorusGraph L).edgeFinset}

/-- The horizontal torus edge from `(x, y)` to `(x + 1, y)`. -/
def torusHorizontalEdge (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    TorusAmbientEdge L :=
  ⟨s((x, y), (x + 1, y)), by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; change onsTorusAdj L _ _
    exact Or.inr ⟨rfl, Or.inr (by ring)⟩⟩

/-- The vertical torus edge from `(x, y)` to `(x, y + 1)`. -/
def torusVerticalEdge (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    TorusAmbientEdge L :=
  ⟨s((x, y), (x, y + 1)), by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; change onsTorusAdj L _ _
    exact Or.inl ⟨rfl, Or.inr (by ring)⟩⟩

@[simp] lemma torusHorizontalEdge_val (L : ℕ) [Fact (2 < L)]
    (x y : ZMod L) :
    (torusHorizontalEdge L x y : Sym2 (ZMod L × ZMod L)) =
      s((x, y), (x + 1, y)) := rfl

@[simp] lemma torusVerticalEdge_val (L : ℕ) [Fact (2 < L)]
    (x y : ZMod L) :
    (torusVerticalEdge L x y : Sym2 (ZMod L × ZMod L)) =
      s((x, y), (x, y + 1)) := rfl

lemma torusHorizontalEdge_orientation_independent
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    (torusHorizontalEdge L x y : Sym2 (ZMod L × ZMod L)) =
      s((x + 1, y), (x, y)) := by
  rw [torusHorizontalEdge_val, Sym2.eq_swap]

lemma torusVerticalEdge_orientation_independent
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    (torusVerticalEdge L x y : Sym2 (ZMod L × ZMod L)) =
      s((x, y + 1), (x, y)) := by
  rw [torusVerticalEdge_val, Sym2.eq_swap]

/-- The torus edge with the given code. -/
def torusEdgeOfCode (L : ℕ) [Fact (2 < L)] :
    TorusEdgeCode L → TorusAmbientEdge L
  | ((x, y), .horizontal) => torusHorizontalEdge L x y
  | ((x, y), .vertical) => torusVerticalEdge L x y

lemma torusEdgeOfCode_injective (L : ℕ) [Fact (2 < L)] :
    Function.Injective (torusEdgeOfCode L) := by
  have htwo : (2 : ZMod L) ≠ 0 := by
    have h : ((2 : ℕ) : ZMod L) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have hle := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd
      have := (Fact.out : 2 < L)
      omega
    simpa using h
  have hone : (1 : ZMod L) ≠ 0 := by
    intro h
    apply htwo
    linear_combination 2 * h
  rintro ⟨⟨x, y⟩, o⟩ ⟨⟨x', y'⟩, o'⟩ h
  cases o <;> cases o'
  · simp only [torusEdgeOfCode, Subtype.ext_iff, torusHorizontalEdge_val,
      Sym2.eq_iff, Prod.mk.injEq] at h
    rcases h with ⟨hxy, _⟩ | ⟨hxx, hyy⟩
    · rcases hxy with ⟨rfl, rfl⟩
      rfl
    · exfalso
      apply htwo
      linear_combination hyy.1 - hxx.1
  · simp only [torusEdgeOfCode, Subtype.ext_iff, torusHorizontalEdge_val,
      torusVerticalEdge_val, Sym2.eq_iff, Prod.mk.injEq] at h
    rcases h with h | h
    · exfalso
      apply hone
      linear_combination h.2.1 - h.1.1
    · exfalso
      apply hone
      linear_combination h.2.1 - h.1.1
  · simp only [torusEdgeOfCode, Subtype.ext_iff, torusHorizontalEdge_val,
      torusVerticalEdge_val, Sym2.eq_iff, Prod.mk.injEq] at h
    rcases h with h | h
    · exfalso
      apply hone
      linear_combination h.2.2 - h.1.2
    · exfalso
      apply hone
      linear_combination h.2.2 - h.1.2
  · simp only [torusEdgeOfCode, Subtype.ext_iff, torusVerticalEdge_val,
      Sym2.eq_iff, Prod.mk.injEq] at h
    rcases h with ⟨hxy, _⟩ | ⟨hxx, hyy⟩
    · rcases hxy with ⟨rfl, rfl⟩
      rfl
    · exfalso
      apply htwo
      linear_combination hyy.2 - hxx.2

lemma torusEdgeOfCode_surjective (L : ℕ) [Fact (2 < L)] :
    Function.Surjective (torusEdgeOfCode L) := by
  rintro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he; change onsTorusAdj L u v at he
      rcases he with (⟨h0, h1 | h1⟩ | ⟨h1, h0 | h0⟩)
      · refine ⟨⟨v, .vertical⟩, ?_⟩
        apply Subtype.ext
        change s((v.1, v.2), (v.1, v.2 + 1)) = s(u, v)
        rw [Sym2.eq_iff]
        right
        exact ⟨rfl, Prod.ext h0.symm h1.symm⟩
      · refine ⟨⟨u, .vertical⟩, ?_⟩
        apply Subtype.ext
        change s((u.1, u.2), (u.1, u.2 + 1)) = s(u, v)
        rw [Sym2.eq_iff]
        left
        exact ⟨rfl, Prod.ext h0 (by linear_combination h1)⟩
      · refine ⟨⟨v, .horizontal⟩, ?_⟩
        apply Subtype.ext
        change s((v.1, v.2), (v.1 + 1, v.2)) = s(u, v)
        rw [Sym2.eq_iff]
        right
        exact ⟨rfl, Prod.ext h0.symm h1.symm⟩
      · refine ⟨⟨u, .horizontal⟩, ?_⟩
        apply Subtype.ext
        change s((u.1, u.2), (u.1 + 1, u.2)) = s(u, v)
        rw [Sym2.eq_iff]
        left
        exact ⟨rfl, Prod.ext (by linear_combination h0) h1⟩

/-- The bijection between edge codes and torus edges. -/
noncomputable def torusEdgeCodeEquiv (L : ℕ) [Fact (2 < L)] :
    TorusEdgeCode L ≃ TorusAmbientEdge L :=
  Equiv.ofBijective (torusEdgeOfCode L)
    ⟨torusEdgeOfCode_injective L, torusEdgeOfCode_surjective L⟩

@[simp] lemma torusEdgeCodeEquiv_apply (L : ℕ) [Fact (2 < L)]
    (c : TorusEdgeCode L) :
    torusEdgeCodeEquiv L c = torusEdgeOfCode L c := rfl

/-! ## B. The cell crossing -/

/-- The cell crossing on edge codes: horizontal at `(x, y)` to vertical at `(x, y - 1)`, vertical at
  `(x, y)` to horizontal at `(x - 1, y)`. -/
def torusCellCrossingCode (L : ℕ) : TorusEdgeCode L ≃ TorusEdgeCode L where
  toFun
    | ((x, y), .horizontal) => ((x, y - 1), .vertical)
    | ((x, y), .vertical) => ((x - 1, y), .horizontal)
  invFun
    | ((x, y), .horizontal) => ((x + 1, y), .vertical)
    | ((x, y), .vertical) => ((x, y + 1), .horizontal)
  left_inv c := by rcases c with ⟨⟨x, y⟩, o⟩; cases o <;> simp
  right_inv c := by rcases c with ⟨⟨x, y⟩, o⟩; cases o <;> simp

/-- The cell crossing on torus edges: each edge goes to the edge crossing it in the shifted dual
  torus. -/
noncomputable def torusCellCrossing (L : ℕ) [Fact (2 < L)] :
    TorusAmbientEdge L ≃ TorusAmbientEdge L :=
  (torusEdgeCodeEquiv L).symm.trans
    ((torusCellCrossingCode L).trans (torusEdgeCodeEquiv L))

@[simp] lemma torusCellCrossing_horizontal
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    torusCellCrossing L (torusHorizontalEdge L x y) =
      torusVerticalEdge L x (y - 1) := by
  have hcode : (torusEdgeCodeEquiv L).symm
      (torusHorizontalEdge L x y) = ((x, y), .horizontal) := by
    apply (torusEdgeCodeEquiv L).injective
    simp [torusEdgeCodeEquiv_apply, torusEdgeOfCode]
  change torusEdgeCodeEquiv L
      (torusCellCrossingCode L
        ((torusEdgeCodeEquiv L).symm (torusHorizontalEdge L x y))) = _
  rw [hcode]
  rfl

@[simp] lemma torusCellCrossing_vertical
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    torusCellCrossing L (torusVerticalEdge L x y) =
      torusHorizontalEdge L (x - 1) y := by
  have hcode : (torusEdgeCodeEquiv L).symm
      (torusVerticalEdge L x y) = ((x, y), .vertical) := by
    apply (torusEdgeCodeEquiv L).injective
    simp [torusEdgeCodeEquiv_apply, torusEdgeOfCode]
  change torusEdgeCodeEquiv L
      (torusCellCrossingCode L
        ((torusEdgeCodeEquiv L).symm (torusVerticalEdge L x y))) = _
  rw [hcode]
  rfl

@[simp] lemma torusCellCrossing_horizontal_val
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    (torusCellCrossing L (torusHorizontalEdge L x y) :
        Sym2 (ZMod L × ZMod L)) =
      s((x, y - 1), (x, y)) := by
  rw [torusCellCrossing_horizontal, torusVerticalEdge_val]
  simp

@[simp] lemma torusCellCrossing_vertical_val
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    (torusCellCrossing L (torusVerticalEdge L x y) :
        Sym2 (ZMod L × ZMod L)) =
      s((x - 1, y), (x, y)) := by
  rw [torusCellCrossing_vertical, torusHorizontalEdge_val]
  simp

lemma torusCellCrossing_of_reversed_horizontal
    (L : ℕ) [Fact (2 < L)] (e : TorusAmbientEdge L) (x y : ZMod L)
    (he : (e : Sym2 (ZMod L × ZMod L)) =
      s((x + 1, y), (x, y))) :
    torusCellCrossing L e = torusVerticalEdge L x (y - 1) := by
  have heq : e = torusHorizontalEdge L x y := by
    apply Subtype.ext
    rw [he, torusHorizontalEdge_orientation_independent]
  rw [heq, torusCellCrossing_horizontal]

lemma torusCellCrossing_of_reversed_vertical
    (L : ℕ) [Fact (2 < L)] (e : TorusAmbientEdge L) (x y : ZMod L)
    (he : (e : Sym2 (ZMod L × ZMod L)) =
      s((x, y + 1), (x, y))) :
    torusCellCrossing L e = torusHorizontalEdge L (x - 1) y := by
  have heq : e = torusVerticalEdge L x y := by
    apply Subtype.ext
    rw [he, torusVerticalEdge_orientation_independent]
  rw [heq, torusCellCrossing_vertical]

@[simp] lemma torusCellCrossing_symm_horizontal
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    (torusCellCrossing L).symm (torusHorizontalEdge L x y) =
      torusVerticalEdge L (x + 1) y := by
  apply (torusCellCrossing L).injective
  simp

@[simp] lemma torusCellCrossing_symm_vertical
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    (torusCellCrossing L).symm (torusVerticalEdge L x y) =
      torusHorizontalEdge L x (y + 1) := by
  apply (torusCellCrossing L).injective
  simp

lemma torusCellCrossing_mem_edgeFinset
    (L : ℕ) [Fact (2 < L)] (e : TorusAmbientEdge L) :
    (torusCellCrossing L e : Sym2 (ZMod L × ZMod L)) ∈
      (onsTorusGraph L).edgeFinset :=
  (torusCellCrossing L e).2

lemma torusCellCrossing_injective
    (L : ℕ) [Fact (2 < L)] :
    Function.Injective (torusCellCrossing L) :=
  (torusCellCrossing L).injective

lemma torusCellCrossing_surjective
    (L : ℕ) [Fact (2 < L)] :
    Function.Surjective (torusCellCrossing L) :=
  (torusCellCrossing L).surjective

@[simp] lemma torusCellCrossing_symm_apply_apply
    (L : ℕ) [Fact (2 < L)] (e : TorusAmbientEdge L) :
    (torusCellCrossing L).symm (torusCellCrossing L e) = e :=
  (torusCellCrossing L).symm_apply_apply e

@[simp] lemma torusCellCrossing_apply_symm_apply
    (L : ℕ) [Fact (2 < L)] (e : TorusAmbientEdge L) :
    torusCellCrossing L ((torusCellCrossing L).symm e) = e :=
  (torusCellCrossing L).apply_symm_apply e

end StatMech.BeffaraDC
