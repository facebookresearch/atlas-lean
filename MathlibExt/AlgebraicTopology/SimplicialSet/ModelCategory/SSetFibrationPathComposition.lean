/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexCompat
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations

/-!
# Connecting edges above a simplicial fibration

Let `p : X ⟶ Y` be a simplicial fibration in universe `u`. Two edges of `X` that agree at
their shared vertex and project to two faces of a specified `2`-simplex of `Y` extend to its
remaining edge. The three cases fill edges `02`, `12`, and `01`; the equations use `δ 1` for
the initial vertex and `δ 0` for the terminal vertex of an edge.

If edge `01` is constant over the base, the chosen connecting edge `02` projects to the image of
edge `12`. If edges `01` and `02`, or edges `02` and `12`, have equal base images, the missing
edge can be chosen constant over the base.
-/

@[expose] public section

universe u

open CategoryTheory HomotopicalAlgebra Simplicial
open scoped SSet.modelCategoryQuillen

namespace SSet

variable {X Y : SSet.{u}}

/-- In `SSet.{u}`, let `H` be the pushout of `a : V ⟶ L` and `b : V ⟶ R`, with legs `inl : L ⟶ H`
and `inr : R ⟶ H`. Let `j : H ⟶ D` have the left lifting property against `p : X ⟶ Y`. Suppose
`left : L ⟶ X` and `right : R ⟶ X` agree on `V`, and for `base : D ⟶ Y` satisfy `left ≫ p =
inl ≫ j ≫ base` and `right ≫ p = inr ≫ j ≫ base`. There is `filler : D ⟶ X` with `inl ≫ j ≫
filler = left`, `inr ≫ j ≫ filler = right`, and `filler ≫ p = base`. -/
private lemma exists_pushout_filler
    {V L R H D X Y : SSet.{u}}
    {a : V ⟶ L} {b : V ⟶ R} {inl : L ⟶ H} {inr : R ⟶ H}
    (hPush : IsPushout a b inl inr) (j : H ⟶ D) (p : X ⟶ Y)
    [HasLiftingProperty j p]
    (left : L ⟶ X) (right : R ⟶ X) (hShared : a ≫ left = b ≫ right)
    (base : D ⟶ Y)
    (hLeft : left ≫ p = inl ≫ j ≫ base)
    (hRight : right ≫ p = inr ≫ j ≫ base) :
    ∃ (filler : D ⟶ X),
      inl ≫ j ≫ filler = left ∧
      inr ≫ j ≫ filler = right ∧
      filler ≫ p = base := by
  let hornMap := hPush.desc left right hShared
  have hHornLeft : inl ≫ hornMap = left := hPush.inl_desc left right hShared
  have hHornRight : inr ≫ hornMap = right := hPush.inr_desc left right hShared
  let sq : CommSq hornMap j p base := ⟨by
    apply hPush.hom_ext
    · calc
        inl ≫ hornMap ≫ p = (inl ≫ hornMap) ≫ p := (Category.assoc _ _ _).symm
        _ = left ≫ p := by rw [hHornLeft]
        _ = inl ≫ j ≫ base := hLeft
    · calc
        inr ≫ hornMap ≫ p = (inr ≫ hornMap) ≫ p := (Category.assoc _ _ _).symm
        _ = right ≫ p := by rw [hHornRight]
        _ = inr ≫ j ≫ base := hRight⟩
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · rw [sq.fac_left, hHornLeft]
  · rw [sq.fac_left, hHornRight]

/-- For `X : SSet.{u}` and a vertex map `f : Δ[0] ⟶ X`, the degeneracy `stdSimplex.σ 0 : Δ[1] ⟶
Δ[0]` satisfies `stdSimplex.σ 0 ≫ f = const (yonedaEquiv f)`. -/
private lemma sigmaZero_comp (f : Δ[0] ⟶ X) :
    stdSimplex.σ 0 ≫ f = const (yonedaEquiv f) := by
  apply yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_σ_comp, σ_zero_eq_yonedaEquiv_const]

/-- Let `p : X ⟶ Y` be a simplicial fibration in universe `u`. Suppose edges `x₀₁, x₁₂ : Δ[1] ⟶ X`
satisfy `δ 0 ≫ x₀₁ = δ 1 ≫ x₁₂`, and `s : Δ[2] ⟶ Y` satisfies `δ 2 ≫ s = x₀₁ ≫ p` and `δ 0 ≫ s
= x₁₂ ≫ p`, where `δ` denotes `stdSimplex.δ`. There is `x₀₂ : Δ[1] ⟶ X` with `δ 1 ≫ x₀₂ = δ 1
≫ x₀₁`, `δ 0 ≫ x₀₂ = δ 0 ≫ x₁₂`, and `x₀₂ ≫ p = δ 1 ≫ s`. -/
lemma exists_path_composition_above_of_fibration
    (p : X ⟶ Y) [Fibration p] (x₀₁ x₁₂ : Δ[1] ⟶ X)
    (h : stdSimplex.δ 0 ≫ x₀₁ = stdSimplex.δ 1 ≫ x₁₂)
    (s : Δ[2] ⟶ Y)
    (hs₀₁ : stdSimplex.δ 2 ≫ s = x₀₁ ≫ p)
    (hs₁₂ : stdSimplex.δ 0 ≫ s = x₁₂ ≫ p) :
    ∃ (x₀₂ : Δ[1] ⟶ X),
      stdSimplex.δ 1 ≫ x₀₂ = stdSimplex.δ 1 ≫ x₀₁ ∧
      stdSimplex.δ 0 ≫ x₀₂ = stdSimplex.δ 0 ≫ x₁₂ ∧
      x₀₂ ≫ p = stdSimplex.δ 1 ≫ s := by
  obtain ⟨filler, hFace₀₁, hFace₁₂, hOver⟩ :=
    exists_pushout_filler horn₂₁.isPushout (horn 2 1).ι p x₀₁ x₁₂ h s
      (by simpa only [horn.ι_ι_assoc] using hs₀₁.symm)
      (by simpa only [horn.ι_ι_assoc] using hs₁₂.symm)
  have hFace₀₁' : stdSimplex.δ 2 ≫ filler = x₀₁ := by
    simpa only [horn.ι_ι_assoc] using hFace₀₁
  have hFace₁₂' : stdSimplex.δ 0 ≫ filler = x₁₂ := by
    simpa only [horn.ι_ι_assoc] using hFace₁₂
  refine ⟨stdSimplex.δ 1 ≫ filler, ?_, ?_, by simp only [Category.assoc, hOver]⟩
  · rw [← hFace₀₁']
    symm
    apply stdSimplex.δ_comp_δ_assoc (n := 0) (i := 1) (j := 1) (by rfl)
  · rw [← hFace₁₂']
    symm
    apply stdSimplex.δ_comp_δ_self_assoc (n := 0) (i := 0)

/-- For a simplicial fibration `p : X ⟶ Y` in universe `u`, suppose `x₀₁, x₁₂ : Δ[1] ⟶ X` satisfy
`δ 0 ≫ x₀₁ = δ 1 ≫ x₁₂`, and `x₀₁ ≫ p = const b` for `b : Y _⦋0⦌`. Then there is `x₀₂ : Δ[1] ⟶
X` with `δ 1 ≫ x₀₂ = δ 1 ≫ x₀₁`, `δ 0 ≫ x₀₂ = δ 0 ≫ x₁₂`, and `x₀₂ ≫ p = x₁₂ ≫ p`. Here `δ`
denotes `stdSimplex.δ`. -/
lemma exists_path_composition_above_of_fibration'
    (p : X ⟶ Y) [Fibration p] (x₀₁ x₁₂ : Δ[1] ⟶ X) (b : Y _⦋0⦌)
    (h : stdSimplex.δ 0 ≫ x₀₁ = stdSimplex.δ 1 ≫ x₁₂)
    (hx : x₀₁ ≫ p = const b) :
    ∃ (x₀₂ : Δ[1] ⟶ X),
      stdSimplex.δ 1 ≫ x₀₂ = stdSimplex.δ 1 ≫ x₀₁ ∧
      stdSimplex.δ 0 ≫ x₀₂ = stdSimplex.δ 0 ≫ x₁₂ ∧
      x₀₂ ≫ p = x₁₂ ≫ p := by
  let base : Δ[2] ⟶ Y := stdSimplex.σ 0 ≫ x₁₂ ≫ p
  have hBase₁₂ : stdSimplex.δ 0 ≫ base = x₁₂ ≫ p := by
    dsimp [base]
    exact stdSimplex.δ_comp_σ_self_assoc (n := 1) (i := 0) _
  have hBase₀₁ : stdSimplex.δ 2 ≫ base = x₀₁ ≫ p := by
    have hVertex := h =≫ p
    simp only [Category.assoc] at hVertex
    have hDegeneracy :=
      stdSimplex.{u}.δ_comp_σ_of_gt (n := 0) (i := 1) (j := 0) (by simp)
    dsimp [base] at hBase₁₂ ⊢
    dsimp at hDegeneracy
    rw [reassoc_of% hDegeneracy, ← hVertex, hx, comp_const, comp_const]
  obtain ⟨x₀₂, hSource, hTarget, hOver⟩ :=
    exists_path_composition_above_of_fibration p x₀₁ x₁₂ h base hBase₀₁ hBase₁₂
  refine ⟨x₀₂, hSource, hTarget, ?_⟩
  calc
    x₀₂ ≫ p = stdSimplex.δ 1 ≫ base := hOver
    _ = x₁₂ ≫ p := by
      dsimp [base]
      exact stdSimplex.δ_comp_σ_succ_assoc (n := 1) (i := 0) _

/-- Let `p : X ⟶ Y` be a simplicial fibration in universe `u`. Suppose `x₀₁, x₀₂ : Δ[1] ⟶ X` have
the same initial vertex, `δ 1 ≫ x₀₁ = δ 1 ≫ x₀₂`, and lie above the faces `δ 2 ≫ s` and `δ 1 ≫
s` of `s : Δ[2] ⟶ Y`. There is `x₁₂ : Δ[1] ⟶ X` with `δ 1 ≫ x₁₂ = δ 0 ≫ x₀₁`, `δ 0 ≫ x₁₂ = δ 0
≫ x₀₂`, and `x₁₂ ≫ p = δ 0 ≫ s`. Here `δ` denotes `stdSimplex.δ`. -/
lemma exists_path_composition₀_above_of_fibration
    (p : X ⟶ Y) [Fibration p] (x₀₁ x₀₂ : Δ[1] ⟶ X)
    (h : stdSimplex.δ 1 ≫ x₀₁ = stdSimplex.δ 1 ≫ x₀₂)
    (s : Δ[2] ⟶ Y)
    (hs₀₁ : stdSimplex.δ 2 ≫ s = x₀₁ ≫ p)
    (hs₀₂ : stdSimplex.δ 1 ≫ s = x₀₂ ≫ p) :
    ∃ (x₁₂ : Δ[1] ⟶ X),
      stdSimplex.δ 1 ≫ x₁₂ = stdSimplex.δ 0 ≫ x₀₁ ∧
      stdSimplex.δ 0 ≫ x₁₂ = stdSimplex.δ 0 ≫ x₀₂ ∧
      x₁₂ ≫ p = stdSimplex.δ 0 ≫ s := by
  obtain ⟨filler, hFace₀₁, hFace₀₂, hOver⟩ :=
    exists_pushout_filler horn₂₀.isPushout (horn 2 0).ι p x₀₁ x₀₂ h s
      (by simpa only [horn.ι_ι_assoc] using hs₀₁.symm)
      (by simpa only [horn.ι_ι_assoc] using hs₀₂.symm)
  have hFace₀₁' : stdSimplex.δ 2 ≫ filler = x₀₁ := by
    simpa only [horn.ι_ι_assoc] using hFace₀₁
  have hFace₀₂' : stdSimplex.δ 1 ≫ filler = x₀₂ := by
    simpa only [horn.ι_ι_assoc] using hFace₀₂
  refine ⟨stdSimplex.δ 0 ≫ filler, ?_, ?_, by simp only [Category.assoc, hOver]⟩
  · rw [← hFace₀₁']
    symm
    apply stdSimplex.δ_comp_δ_assoc (n := 0) (i := 0) (j := 1) (by simp)
  · rw [← hFace₀₂']
    symm
    apply stdSimplex.δ_comp_δ_self_assoc (n := 0) (i := 0)

/-- For a simplicial fibration `p : X ⟶ Y` in universe `u`, let `x₀₁, x₀₂ : Δ[1] ⟶ X` satisfy `δ 1
≫ x₀₁ = δ 1 ≫ x₀₂` and `x₀₁ ≫ p = x₀₂ ≫ p`. There are an edge `x₁₂ : Δ[1] ⟶ X` and `b : Y
_⦋0⦌` such that `δ 1 ≫ x₁₂ = δ 0 ≫ x₀₁`, `δ 0 ≫ x₁₂ = δ 0 ≫ x₀₂`, and `x₁₂ ≫ p = const b`.
Here `δ` denotes `stdSimplex.δ`. -/
lemma exists_path_composition₀_above_of_fibration'
    (p : X ⟶ Y) [Fibration p] (x₀₁ x₀₂ : Δ[1] ⟶ X)
    (h : stdSimplex.δ 1 ≫ x₀₁ = stdSimplex.δ 1 ≫ x₀₂)
    (hx : x₀₁ ≫ p = x₀₂ ≫ p) :
    ∃ (x₁₂ : Δ[1] ⟶ X) (b : Y _⦋0⦌),
      stdSimplex.δ 1 ≫ x₁₂ = stdSimplex.δ 0 ≫ x₀₁ ∧
      stdSimplex.δ 0 ≫ x₁₂ = stdSimplex.δ 0 ≫ x₀₂ ∧
      x₁₂ ≫ p = const b := by
  let base : Δ[2] ⟶ Y := stdSimplex.σ 1 ≫ x₀₁ ≫ p
  have hBase₀₁ : stdSimplex.δ 2 ≫ base = x₀₁ ≫ p := by
    dsimp [base]
    exact stdSimplex.δ_comp_σ_succ_assoc (n := 1) (i := 1) _
  have hBase₀₂ : stdSimplex.δ 1 ≫ base = x₀₂ ≫ p := by
    dsimp [base]
    rw [hx]
    exact stdSimplex.δ_comp_σ_self_assoc (n := 1) (i := 1) _
  obtain ⟨x₁₂, hSource, hTarget, hOver⟩ :=
    exists_path_composition₀_above_of_fibration p x₀₁ x₀₂ h base hBase₀₁ hBase₀₂
  let vertex : Y _⦋0⦌ := yonedaEquiv (stdSimplex.δ 0 ≫ x₀₁ ≫ p)
  refine ⟨x₁₂, vertex, hSource, hTarget, ?_⟩
  calc
    x₁₂ ≫ p = stdSimplex.δ 0 ≫ base := hOver
    _ = stdSimplex.σ 0 ≫ (stdSimplex.δ 0 ≫ x₀₁ ≫ p) := by
      dsimp [base]
      have hDegeneracy :=
        stdSimplex.{u}.δ_comp_σ_of_le (n := 0) (i := 0) (j := 0) (by simp)
      dsimp at hDegeneracy
      rw [reassoc_of% hDegeneracy]
    _ = const vertex := sigmaZero_comp _

/-- Let `p : X ⟶ Y` be a simplicial fibration in universe `u`. Suppose `x₀₂, x₁₂ : Δ[1] ⟶ X` have
the same terminal vertex, `δ 0 ≫ x₀₂ = δ 0 ≫ x₁₂`, and lie above the faces `δ 1 ≫ s` and `δ 0
≫ s` of `s : Δ[2] ⟶ Y`. There is `x₀₁ : Δ[1] ⟶ X` with `δ 1 ≫ x₀₁ = δ 1 ≫ x₀₂`, `δ 0 ≫ x₀₁ = δ
1 ≫ x₁₂`, and `x₀₁ ≫ p = δ 2 ≫ s`. Here `δ` denotes `stdSimplex.δ`. -/
lemma exists_path_composition₂_above_of_fibration
    (p : X ⟶ Y) [Fibration p] (x₀₂ x₁₂ : Δ[1] ⟶ X)
    (h : stdSimplex.δ 0 ≫ x₀₂ = stdSimplex.δ 0 ≫ x₁₂)
    (s : Δ[2] ⟶ Y)
    (hs₀₂ : stdSimplex.δ 1 ≫ s = x₀₂ ≫ p)
    (hs₁₂ : stdSimplex.δ 0 ≫ s = x₁₂ ≫ p) :
    ∃ (x₀₁ : Δ[1] ⟶ X),
      stdSimplex.δ 1 ≫ x₀₁ = stdSimplex.δ 1 ≫ x₀₂ ∧
      stdSimplex.δ 0 ≫ x₀₁ = stdSimplex.δ 1 ≫ x₁₂ ∧
      x₀₁ ≫ p = stdSimplex.δ 2 ≫ s := by
  obtain ⟨filler, hFace₀₂, hFace₁₂, hOver⟩ :=
    exists_pushout_filler horn₂₂.isPushout (horn 2 2).ι p x₀₂ x₁₂ h s
      (by simpa only [horn.ι_ι_assoc] using hs₀₂.symm)
      (by simpa only [horn.ι_ι_assoc] using hs₁₂.symm)
  have hFace₀₂' : stdSimplex.δ 1 ≫ filler = x₀₂ := by
    simpa only [horn.ι_ι_assoc] using hFace₀₂
  have hFace₁₂' : stdSimplex.δ 0 ≫ filler = x₁₂ := by
    simpa only [horn.ι_ι_assoc] using hFace₁₂
  refine ⟨stdSimplex.δ 2 ≫ filler, ?_, ?_, by simp only [Category.assoc, hOver]⟩
  · rw [← hFace₀₂']
    symm
    apply stdSimplex.δ_comp_δ_self_assoc (n := 0) (i := 1)
  · rw [← hFace₁₂']
    apply stdSimplex.δ_comp_δ_assoc (n := 0) (i := 0) (j := 1) (by simp)

/-- For a simplicial fibration `p : X ⟶ Y` in universe `u`, let `x₀₂, x₁₂ : Δ[1] ⟶ X` satisfy `δ 0
≫ x₀₂ = δ 0 ≫ x₁₂` and `x₀₂ ≫ p = x₁₂ ≫ p`. There are an edge `x₀₁ : Δ[1] ⟶ X` and `b : Y
_⦋0⦌` such that `δ 1 ≫ x₀₁ = δ 1 ≫ x₀₂`, `δ 0 ≫ x₀₁ = δ 1 ≫ x₁₂`, and `x₀₁ ≫ p = const b`.
Here `δ` denotes `stdSimplex.δ`. -/
lemma exists_path_composition₂_above_of_fibration'
    (p : X ⟶ Y) [Fibration p] (x₀₂ x₁₂ : Δ[1] ⟶ X)
    (h : stdSimplex.δ 0 ≫ x₀₂ = stdSimplex.δ 0 ≫ x₁₂)
    (hx : x₀₂ ≫ p = x₁₂ ≫ p) :
    ∃ (x₀₁ : Δ[1] ⟶ X) (b : Y _⦋0⦌),
      stdSimplex.δ 1 ≫ x₀₁ = stdSimplex.δ 1 ≫ x₀₂ ∧
      stdSimplex.δ 0 ≫ x₀₁ = stdSimplex.δ 1 ≫ x₁₂ ∧
      x₀₁ ≫ p = const b := by
  let base : Δ[2] ⟶ Y := stdSimplex.σ 0 ≫ x₀₂ ≫ p
  have hBase₀₂ : stdSimplex.δ 1 ≫ base = x₀₂ ≫ p := by
    dsimp [base]
    exact stdSimplex.δ_comp_σ_succ_assoc (n := 1) (i := 0) _
  have hBase₁₂ : stdSimplex.δ 0 ≫ base = x₁₂ ≫ p := by
    dsimp [base]
    rw [← hx]
    exact stdSimplex.δ_comp_σ_self_assoc (n := 1) (i := 0) _
  obtain ⟨x₀₁, hSource, hTarget, hOver⟩ :=
    exists_path_composition₂_above_of_fibration p x₀₂ x₁₂ h base hBase₀₂ hBase₁₂
  let vertex : Y _⦋0⦌ := yonedaEquiv (stdSimplex.δ 1 ≫ x₀₂ ≫ p)
  refine ⟨x₀₁, vertex, hSource, hTarget, ?_⟩
  calc
    x₀₁ ≫ p = stdSimplex.δ 2 ≫ base := hOver
    _ = stdSimplex.σ 0 ≫ (stdSimplex.δ 1 ≫ x₀₂ ≫ p) := by
      dsimp [base]
      have hDegeneracy :=
        stdSimplex.{u}.δ_comp_σ_of_gt (n := 0) (i := 1) (j := 0) (by simp)
      dsimp at hDegeneracy
      rw [reassoc_of% hDegeneracy]
    _ = const vertex := sigmaZero_comp _

end SSet
