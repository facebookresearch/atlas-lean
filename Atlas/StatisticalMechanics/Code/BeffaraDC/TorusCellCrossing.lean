/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















import Code.Onsager.Torus

open SimpleGraph

namespace StatMech.BeffaraDC

open StatMech.Onsager


inductive TorusEdgeOrientation
  | horizontal
  | vertical
  deriving DecidableEq



abbrev TorusEdgeCode (L : ℕ) :=
  (ZMod L × ZMod L) × TorusEdgeOrientation


abbrev TorusAmbientEdge (L : ℕ) [Fact (2 < L)] :=
  {e : Sym2 (ZMod L × ZMod L) // e ∈ (onsTorusGraph L).edgeFinset}


def torusHorizontalEdge (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    TorusAmbientEdge L :=
  ⟨s((x, y), (x + 1, y)), by
    simp only [SimpleGraph.mem_edgeFinset, onsTorusGraph]
    exact Or.inr ⟨rfl, Or.inr (by ring)⟩⟩


def torusVerticalEdge (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    TorusAmbientEdge L :=
  ⟨s((x, y), (x, y + 1)), by
    simp only [SimpleGraph.mem_edgeFinset, onsTorusGraph]
    exact Or.inl ⟨rfl, Or.inr (by ring)⟩⟩

@[simp] theorem torusHorizontalEdge_val (L : ℕ) [Fact (2 < L)]
    (x y : ZMod L) :
    (torusHorizontalEdge L x y : Sym2 (ZMod L × ZMod L)) =
      s((x, y), (x + 1, y)) := rfl

@[simp] theorem torusVerticalEdge_val (L : ℕ) [Fact (2 < L)]
    (x y : ZMod L) :
    (torusVerticalEdge L x y : Sym2 (ZMod L × ZMod L)) =
      s((x, y), (x, y + 1)) := rfl


theorem torusHorizontalEdge_orientation_independent
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    (torusHorizontalEdge L x y : Sym2 (ZMod L × ZMod L)) =
      s((x + 1, y), (x, y)) := by
  rw [torusHorizontalEdge_val, Sym2.eq_swap]


theorem torusVerticalEdge_orientation_independent
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    (torusVerticalEdge L x y : Sym2 (ZMod L × ZMod L)) =
      s((x, y + 1), (x, y)) := by
  rw [torusVerticalEdge_val, Sym2.eq_swap]


def torusEdgeOfCode (L : ℕ) [Fact (2 < L)] :
    TorusEdgeCode L → TorusAmbientEdge L
  | ((x, y), .horizontal) => torusHorizontalEdge L x y
  | ((x, y), .vertical) => torusVerticalEdge L x y

theorem torusEdgeOfCode_injective (L : ℕ) [Fact (2 < L)] :
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

theorem torusEdgeOfCode_surjective (L : ℕ) [Fact (2 < L)] :
    Function.Surjective (torusEdgeOfCode L) := by
  rintro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [SimpleGraph.mem_edgeFinset, onsTorusGraph] at he
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


noncomputable def torusEdgeCodeEquiv (L : ℕ) [Fact (2 < L)] :
    TorusEdgeCode L ≃ TorusAmbientEdge L :=
  Equiv.ofBijective (torusEdgeOfCode L)
    ⟨torusEdgeOfCode_injective L, torusEdgeOfCode_surjective L⟩

@[simp] theorem torusEdgeCodeEquiv_apply (L : ℕ) [Fact (2 < L)]
    (c : TorusEdgeCode L) :
    torusEdgeCodeEquiv L c = torusEdgeOfCode L c := rfl


def torusCellCrossingCode (L : ℕ) : TorusEdgeCode L ≃ TorusEdgeCode L where
  toFun
    | ((x, y), .horizontal) => ((x, y - 1), .vertical)
    | ((x, y), .vertical) => ((x - 1, y), .horizontal)
  invFun
    | ((x, y), .horizontal) => ((x + 1, y), .vertical)
    | ((x, y), .vertical) => ((x, y + 1), .horizontal)
  left_inv c := by rcases c with ⟨⟨x, y⟩, o⟩; cases o <;> simp
  right_inv c := by rcases c with ⟨⟨x, y⟩, o⟩; cases o <;> simp




noncomputable def torusCellCrossing (L : ℕ) [Fact (2 < L)] :
    TorusAmbientEdge L ≃ TorusAmbientEdge L :=
  (torusEdgeCodeEquiv L).symm.trans
    ((torusCellCrossingCode L).trans (torusEdgeCodeEquiv L))

@[simp] theorem torusCellCrossing_horizontal
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

@[simp] theorem torusCellCrossing_vertical
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

@[simp] theorem torusCellCrossing_horizontal_val
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    (torusCellCrossing L (torusHorizontalEdge L x y) :
        Sym2 (ZMod L × ZMod L)) =
      s((x, y - 1), (x, y)) := by
  rw [torusCellCrossing_horizontal, torusVerticalEdge_val]
  simp

@[simp] theorem torusCellCrossing_vertical_val
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    (torusCellCrossing L (torusVerticalEdge L x y) :
        Sym2 (ZMod L × ZMod L)) =
      s((x - 1, y), (x, y)) := by
  rw [torusCellCrossing_vertical, torusHorizontalEdge_val]
  simp



theorem torusCellCrossing_of_reversed_horizontal
    (L : ℕ) [Fact (2 < L)] (e : TorusAmbientEdge L) (x y : ZMod L)
    (he : (e : Sym2 (ZMod L × ZMod L)) =
      s((x + 1, y), (x, y))) :
    torusCellCrossing L e = torusVerticalEdge L x (y - 1) := by
  have heq : e = torusHorizontalEdge L x y := by
    apply Subtype.ext
    rw [he, torusHorizontalEdge_orientation_independent]
  rw [heq, torusCellCrossing_horizontal]



theorem torusCellCrossing_of_reversed_vertical
    (L : ℕ) [Fact (2 < L)] (e : TorusAmbientEdge L) (x y : ZMod L)
    (he : (e : Sym2 (ZMod L × ZMod L)) =
      s((x, y + 1), (x, y))) :
    torusCellCrossing L e = torusHorizontalEdge L (x - 1) y := by
  have heq : e = torusVerticalEdge L x y := by
    apply Subtype.ext
    rw [he, torusVerticalEdge_orientation_independent]
  rw [heq, torusCellCrossing_vertical]

@[simp] theorem torusCellCrossing_symm_horizontal
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    (torusCellCrossing L).symm (torusHorizontalEdge L x y) =
      torusVerticalEdge L (x + 1) y := by
  apply (torusCellCrossing L).injective
  simp

@[simp] theorem torusCellCrossing_symm_vertical
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    (torusCellCrossing L).symm (torusVerticalEdge L x y) =
      torusHorizontalEdge L x (y + 1) := by
  apply (torusCellCrossing L).injective
  simp


theorem torusCellCrossing_mem_edgeFinset
    (L : ℕ) [Fact (2 < L)] (e : TorusAmbientEdge L) :
    (torusCellCrossing L e : Sym2 (ZMod L × ZMod L)) ∈
      (onsTorusGraph L).edgeFinset :=
  (torusCellCrossing L e).2

theorem torusCellCrossing_injective
    (L : ℕ) [Fact (2 < L)] :
    Function.Injective (torusCellCrossing L) :=
  (torusCellCrossing L).injective

theorem torusCellCrossing_surjective
    (L : ℕ) [Fact (2 < L)] :
    Function.Surjective (torusCellCrossing L) :=
  (torusCellCrossing L).surjective

@[simp] theorem torusCellCrossing_symm_apply_apply
    (L : ℕ) [Fact (2 < L)] (e : TorusAmbientEdge L) :
    (torusCellCrossing L).symm (torusCellCrossing L e) = e :=
  (torusCellCrossing L).symm_apply_apply e

@[simp] theorem torusCellCrossing_apply_symm_apply
    (L : ℕ) [Fact (2 < L)] (e : TorusAmbientEdge L) :
    torusCellCrossing L ((torusCellCrossing L).symm e) = e :=
  (torusCellCrossing L).apply_symm_apply e

end StatMech.BeffaraDC
