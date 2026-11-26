/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Abelian.Refinements
public import MathlibExt.Algebra.Homology.ExactSequence

/-!
# The exact braid lemma

An exact braid in an abelian category consists of overlapping chains
`A → P → B₁ → A₁ → P₁ → B₂`,
`X → Q → B₁ → X₁ → Q₁ → B₂`, and
`A → X → R → A₁ → X₁`, with their specified exact interior terms
and commuting comparison maps `P → Q`, `Q → R`, `P₁ → Q₁`.
Its diagonal `P → Q → R → P₁ → Q₁` is exact, with the third map
factoring through `R → A₁ → P₁`.
-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Limits
open CategoryTheory.Preadditive

universe v u

/-- In an abelian category `C`, exact-braid data consists of chains
`A → P → B₁ → A₁ → P₁ → B₂`, `X → Q → B₁ → X₁ → Q₁ → B₂`,
and `A → X → R → A₁ → X₁`. They are exact respectively at
`B₁,A₁,P₁`, at `Q,B₁,X₁`, and at `X,R,A₁`.
The comparison maps `p : P → Q`, `q : Q → R`, `p₁ : P₁ → Q₁`
have zero composite `p ≫ q`, agree with the two routes from `A`
to `Q` and from `A₁` to `Q₁`, and factor the maps `P → B₁`,
`X → R`, `Q → A₁`, `B₁ → X₁`, and `P₁ → B₂` through the
corresponding commuting braid squares. -/
structure ExactBraid (C : Type u) [Category.{v} C] [Abelian C] where
  A : C
  X : C
  P : C
  Q : C
  R : C
  B₁ : C
  A₁ : C
  X₁ : C
  P₁ : C
  Q₁ : C
  B₂ : C
  ax : A ⟶ X
  aP : A ⟶ P
  pB : P ⟶ B₁
  bA : B₁ ⟶ A₁
  aP₁ : A₁ ⟶ P₁
  pB₂ : P₁ ⟶ B₂
  xQ : X ⟶ Q
  qB : Q ⟶ B₁
  bX : B₁ ⟶ X₁
  xQ₁ : X₁ ⟶ Q₁
  qB₂ : Q₁ ⟶ B₂
  xR : X ⟶ R
  rA : R ⟶ A₁
  aX : A₁ ⟶ X₁
  pQ : P ⟶ Q
  qR : Q ⟶ R
  pQ₁ : P₁ ⟶ Q₁
  z_pB_bA : pB ≫ bA = 0
  z_xQ_qB : xQ ≫ qB = 0
  z_ax_xR : ax ≫ xR = 0
  z_bA_aP₁ : bA ≫ aP₁ = 0
  z_qB_bX : qB ≫ bX = 0
  z_xR_rA : xR ≫ rA = 0
  z_rA_aX : rA ≫ aX = 0
  z_aP₁_pB₂ : aP₁ ≫ pB₂ = 0
  z_bX_xQ₁ : bX ≫ xQ₁ = 0
  hABB : (ShortComplex.mk pB bA z_pB_bA).Exact
  hXBQ : (ShortComplex.mk xQ qB z_xQ_qB).Exact
  hXA₀ : (ShortComplex.mk ax xR z_ax_xR).Exact
  hABA : (ShortComplex.mk bA aP₁ z_bA_aP₁).Exact
  hXBB : (ShortComplex.mk qB bX z_qB_bX).Exact
  hXAR : (ShortComplex.mk xR rA z_xR_rA).Exact
  hXAA : (ShortComplex.mk rA aX z_rA_aX).Exact
  hABP₁ : (ShortComplex.mk aP₁ pB₂ z_aP₁_pB₂).Exact
  hXBX : (ShortComplex.mk bX xQ₁ z_bX_xQ₁).Exact
  comm_aP : aP ≫ pQ = ax ≫ xQ
  comm_pB : pQ ≫ qB = pB
  comm_xR : xQ ≫ qR = xR
  comm_rA : qR ≫ rA = qB ≫ bA
  comm_bX : bA ≫ aX = bX
  comm_aP₁ : aP₁ ≫ pQ₁ = aX ≫ xQ₁
  comm_pB₂ : pQ₁ ≫ qB₂ = pB₂
  zero_pq : pQ ≫ qR = 0

namespace ExactBraid

variable {C : Type u} [Category.{v} C] [Abelian C] (S : ExactBraid C)

private lemma exact_Q :
    (ShortComplex.mk S.pQ S.qR S.zero_pq).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro Z y hy
  have h_yqB_bA : (y ≫ S.qB) ≫ S.bA = 0 := by
    calc
      (y ≫ S.qB) ≫ S.bA = y ≫ (S.qB ≫ S.bA) := by rw [Category.assoc]
      _ = y ≫ (S.qR ≫ S.rA) := by rw [← S.comm_rA]
      _ = (y ≫ S.qR) ≫ S.rA := by rw [← Category.assoc]
      _ = (0 : Z ⟶ S.R) ≫ S.rA := by rw [hy]
      _ = 0 := by simp
  obtain ⟨Z₁, π₁, hπ₁, p, hp⟩ := S.hABB.exact_up_to_refinements (y ≫ S.qB) h_yqB_bA
  have hπ₁_epi : Epi π₁ := hπ₁
  have h_corr_qB : (π₁ ≫ y - p ≫ S.pQ) ≫ S.qB = 0 := by
    calc
      (π₁ ≫ y - p ≫ S.pQ) ≫ S.qB = (π₁ ≫ y) ≫ S.qB - (p ≫ S.pQ) ≫ S.qB := by
        rw [Preadditive.sub_comp]
      _ = π₁ ≫ (y ≫ S.qB) - (p ≫ S.pQ) ≫ S.qB := by
        simp only [Category.assoc]
      _ = (p ≫ S.pB) - (p ≫ S.pQ) ≫ S.qB := by
        rw [hp]
      _ = (p ≫ S.pB) - p ≫ (S.pQ ≫ S.qB) := by
        simp only [Category.assoc]
      _ = p ≫ S.pB - p ≫ S.pB := by
        rw [S.comm_pB]
      _ = 0 := by simp
  obtain ⟨Z₂, π₂, hπ₂, x, hx⟩ := S.hXBQ.exact_up_to_refinements (π₁ ≫ y - p ≫ S.pQ) h_corr_qB
  have hπ₂_epi : Epi π₂ := hπ₂
  have h_xR : x ≫ S.xR = 0 := by
    calc
      x ≫ S.xR = x ≫ (S.xQ ≫ S.qR) := by rw [← S.comm_xR]
      _ = (x ≫ S.xQ) ≫ S.qR := by simp only [Category.assoc]
      _ = (π₂ ≫ (π₁ ≫ y - p ≫ S.pQ)) ≫ S.qR := by rw [← hx]
      _ = π₂ ≫ ((π₁ ≫ y - p ≫ S.pQ) ≫ S.qR) := by simp only [Category.assoc]
      _ = π₂ ≫ ((π₁ ≫ y) ≫ S.qR - (p ≫ S.pQ) ≫ S.qR) := by
        rw [Preadditive.sub_comp]
      _ = π₂ ≫ (π₁ ≫ (y ≫ S.qR) - p ≫ (S.pQ ≫ S.qR)) := by
        simp
      _ = π₂ ≫ (π₁ ≫ (0 : Z ⟶ S.R) - p ≫ (0 : S.P ⟶ S.R)) := by rw [hy, S.zero_pq]
      _ = 0 := by simp
  obtain ⟨Z₃, π₃, hπ₃, a, ha⟩ := S.hXA₀.exact_up_to_refinements x h_xR
  have hπ₃_epi : Epi π₃ := hπ₃
  have h_fully_refined : π₃ ≫ π₂ ≫ (π₁ ≫ y - p ≫ S.pQ) = a ≫ S.aP ≫ S.pQ := by
    calc
      π₃ ≫ π₂ ≫ (π₁ ≫ y - p ≫ S.pQ) = π₃ ≫ (π₂ ≫ (π₁ ≫ y - p ≫ S.pQ)) := by
        rfl
      _ = π₃ ≫ (x ≫ S.xQ) := by rw [hx]
      _ = (π₃ ≫ x) ≫ S.xQ := by simp only [Category.assoc]
      _ = (a ≫ S.ax) ≫ S.xQ := by rw [ha]
      _ = a ≫ (S.ax ≫ S.xQ) := by simp only [Category.assoc]
      _ = a ≫ (S.aP ≫ S.pQ) := by rw [← S.comm_aP]
      _ = a ≫ S.aP ≫ S.pQ := by simp
  have h_sub_eq : π₃ ≫ π₂ ≫ π₁ ≫ y - π₃ ≫ π₂ ≫ p ≫ S.pQ = a ≫ S.aP ≫ S.pQ := by
    have h1 : π₃ ≫ π₂ ≫ (π₁ ≫ y - p ≫ S.pQ) = π₃ ≫ π₂ ≫ π₁ ≫ y - π₃ ≫ π₂ ≫ p ≫ S.pQ := by
      simp only [Preadditive.comp_sub]
    rw [← h1, h_fully_refined]
  have h_main : (π₃ ≫ π₂ ≫ π₁) ≫ y = (π₃ ≫ π₂ ≫ p + a ≫ S.aP) ≫ S.pQ := by
    have h_eq_add : π₃ ≫ π₂ ≫ π₁ ≫ y = a ≫ S.aP ≫ S.pQ + π₃ ≫ π₂ ≫ p ≫ S.pQ := by
      rwa [sub_eq_iff_eq_add] at h_sub_eq
    have h_eq_add' : π₃ ≫ π₂ ≫ π₁ ≫ y = π₃ ≫ π₂ ≫ p ≫ S.pQ + a ≫ S.aP ≫ S.pQ := by
      rw [h_eq_add, add_comm]
    calc
      (π₃ ≫ π₂ ≫ π₁) ≫ y = π₃ ≫ π₂ ≫ π₁ ≫ y := by simp only [Category.assoc]
      _ = π₃ ≫ π₂ ≫ p ≫ S.pQ + a ≫ S.aP ≫ S.pQ := h_eq_add'
      _ = (π₃ ≫ π₂ ≫ p) ≫ S.pQ + (a ≫ S.aP) ≫ S.pQ := by simp only [Category.assoc]
      _ = (π₃ ≫ π₂ ≫ p + a ≫ S.aP) ≫ S.pQ := by rw [Preadditive.add_comp]
  have hπ₂₁ : Epi (π₂ ≫ π₁) := epi_comp π₂ π₁
  have hπ₃₂₁ : Epi (π₃ ≫ π₂ ≫ π₁) := epi_comp π₃ (π₂ ≫ π₁)
  exact ⟨Z₃, π₃ ≫ π₂ ≫ π₁, hπ₃₂₁, π₃ ≫ π₂ ≫ p + a ≫ S.aP, h_main⟩

private lemma exact_R :
    (ShortComplex.mk S.qR (S.rA ≫ S.aP₁) (by
      rw [← Category.assoc, S.comm_rA, Category.assoc,
        S.z_bA_aP₁, comp_zero])).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro Z y hy
  have hy' : (y ≫ S.rA) ≫ S.aP₁ = 0 := by
    rw [Category.assoc, hy]
  obtain ⟨Z₁, π₁, _, b, hb⟩ := S.hABA.exact_up_to_refinements (y ≫ S.rA) hy'
  have hbX : b ≫ S.bX = 0 := by
    calc
      b ≫ S.bX = b ≫ (S.bA ≫ S.aX) := by rw [← S.comm_bX]
      _ = (b ≫ S.bA) ≫ S.aX := by rw [Category.assoc]
      _ = (π₁ ≫ (y ≫ S.rA)) ≫ S.aX := by rw [← hb]
      _ = π₁ ≫ (y ≫ (S.rA ≫ S.aX)) := by simp only [Category.assoc]
      _ = 0 := by rw [S.z_rA_aX, comp_zero, comp_zero]
  obtain ⟨Z₂, π₂, _, q, hq⟩ := S.hXBB.exact_up_to_refinements b hbX
  have h_diff : (π₂ ≫ π₁ ≫ y - q ≫ S.qR) ≫ S.rA = 0 := by
    calc
      (π₂ ≫ π₁ ≫ y - q ≫ S.qR) ≫ S.rA
          = (π₂ ≫ π₁ ≫ y) ≫ S.rA - (q ≫ S.qR) ≫ S.rA := by rw [Preadditive.sub_comp]
      _ = π₂ ≫ (π₁ ≫ (y ≫ S.rA)) - q ≫ (S.qR ≫ S.rA) := by simp only [Category.assoc]
      _ = π₂ ≫ (b ≫ S.bA) - q ≫ (S.qB ≫ S.bA) := by rw [hb, S.comm_rA]
      _ = (π₂ ≫ b) ≫ S.bA - (q ≫ S.qB) ≫ S.bA := by simp only [Category.assoc]
      _ = (q ≫ S.qB) ≫ S.bA - (q ≫ S.qB) ≫ S.bA := by rw [hq]
      _ = 0 := by simp
  obtain ⟨Z₃, π₃, _, x, hx⟩ := S.hXAR.exact_up_to_refinements (π₂ ≫ π₁ ≫ y - q ≫ S.qR) h_diff
  have h_sub : π₃ ≫ π₂ ≫ π₁ ≫ y - π₃ ≫ q ≫ S.qR = x ≫ S.xR := by
    have h1 : π₃ ≫ (π₂ ≫ π₁ ≫ y - q ≫ S.qR) = π₃ ≫ π₂ ≫ π₁ ≫ y - π₃ ≫ q ≫ S.qR := by
      rw [Preadditive.comp_sub]
    rw [← h1, hx]
  have h_xR : x ≫ S.xR = (x ≫ S.xQ) ≫ S.qR := by
    calc
      x ≫ S.xR = x ≫ (S.xQ ≫ S.qR) := congrArg (x ≫ ·) S.comm_xR.symm
      _ = (x ≫ S.xQ) ≫ S.qR := (Category.assoc _ _ _).symm
  have h_eq : π₃ ≫ π₂ ≫ π₁ ≫ y - π₃ ≫ q ≫ S.qR = (x ≫ S.xQ) ≫ S.qR := by
    calc
      π₃ ≫ π₂ ≫ π₁ ≫ y - π₃ ≫ q ≫ S.qR = x ≫ S.xR := h_sub
      _ = (x ≫ S.xQ) ≫ S.qR := h_xR
  have h_main : π₃ ≫ π₂ ≫ π₁ ≫ y = (π₃ ≫ q + x ≫ S.xQ) ≫ S.qR := by
    have h1 : π₃ ≫ π₂ ≫ π₁ ≫ y = (x ≫ S.xQ) ≫ S.qR + π₃ ≫ q ≫ S.qR := by
      rwa [sub_eq_iff_eq_add] at h_eq
    have h2 : π₃ ≫ π₂ ≫ π₁ ≫ y = π₃ ≫ q ≫ S.qR + (x ≫ S.xQ) ≫ S.qR := by
      rw [h1, add_comm]
    calc
      π₃ ≫ π₂ ≫ π₁ ≫ y = π₃ ≫ q ≫ S.qR + (x ≫ S.xQ) ≫ S.qR := h2
      _ = (π₃ ≫ q) ≫ S.qR + (x ≫ S.xQ) ≫ S.qR := by rw [← Category.assoc]
      _ = (π₃ ≫ q + x ≫ S.xQ) ≫ S.qR := by rw [← Preadditive.add_comp]
  have h_epi : Epi (π₃ ≫ π₂ ≫ π₁) := by
    have : Epi π₁ := inferInstance
    have : Epi π₂ := inferInstance
    have : Epi π₃ := inferInstance
    exact epi_comp π₃ (π₂ ≫ π₁)
  exact ⟨Z₃, π₃ ≫ π₂ ≫ π₁, h_epi, π₃ ≫ q + x ≫ S.xQ, by
    simp only [Category.assoc] at h_main ⊢
    exact h_main⟩

private lemma exact_P₁ :
    (ShortComplex.mk (S.rA ≫ S.aP₁) S.pQ₁ (by
      rw [Category.assoc, S.comm_aP₁, ← Category.assoc,
        S.z_rA_aX, zero_comp])).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro Z y hy
  have h_y_pB₂ : y ≫ S.pB₂ = 0 := by
    calc
      y ≫ S.pB₂ = y ≫ (S.pQ₁ ≫ S.qB₂) := by rw [← S.comm_pB₂]
      _ = (y ≫ S.pQ₁) ≫ S.qB₂ := by rw [← Category.assoc]
      _ = (0 : Z ⟶ S.Q₁) ≫ S.qB₂ := by rw [hy]
      _ = 0 := by simp
  obtain ⟨Z₁, π₁, _, a, ha⟩ := S.hABP₁.exact_up_to_refinements y h_y_pB₂
  have h_aX : (a ≫ S.aX) ≫ S.xQ₁ = 0 := by
    calc
      (a ≫ S.aX) ≫ S.xQ₁ = a ≫ (S.aX ≫ S.xQ₁) := by rw [Category.assoc]
      _ = a ≫ (S.aP₁ ≫ S.pQ₁) := by rw [← S.comm_aP₁]
      _ = (a ≫ S.aP₁) ≫ S.pQ₁ := by rw [← Category.assoc]
      _ = (π₁ ≫ y) ≫ S.pQ₁ := by rw [← ha]
      _ = π₁ ≫ (y ≫ S.pQ₁) := by rw [Category.assoc]
      _ = 0 := by rw [hy, comp_zero]
  obtain ⟨Z₂, π₂, _, b, hb⟩ := S.hXBX.exact_up_to_refinements (a ≫ S.aX) h_aX
  have h_corr : (π₂ ≫ a - b ≫ S.bA) ≫ S.aX = 0 := by
    calc
      (π₂ ≫ a - b ≫ S.bA) ≫ S.aX = (π₂ ≫ a) ≫ S.aX - (b ≫ S.bA) ≫ S.aX := by
        rw [Preadditive.sub_comp]
      _ = π₂ ≫ (a ≫ S.aX) - b ≫ (S.bA ≫ S.aX) := by simp only [Category.assoc]
      _ = (b ≫ S.bX) - b ≫ (S.bA ≫ S.aX) := by rw [hb]
      _ = b ≫ S.bX - b ≫ S.bX := by rw [S.comm_bX]
      _ = 0 := by simp
  obtain ⟨Z₃, π₃, _, r, hr⟩ := S.hXAA.exact_up_to_refinements (π₂ ≫ a - b ≫ S.bA) h_corr
  have h_comp_sub : π₃ ≫ (π₂ ≫ a - b ≫ S.bA) = π₃ ≫ (π₂ ≫ a) - π₃ ≫ (b ≫ S.bA) := by
    rw [Preadditive.comp_sub]
  have h_eq : π₃ ≫ (π₂ ≫ a) - π₃ ≫ (b ≫ S.bA) = r ≫ S.rA := by
    rw [← h_comp_sub, hr]
  have h_fully : (π₃ ≫ π₂ ≫ π₁) ≫ y = (π₃ ≫ (π₂ ≫ a)) ≫ S.aP₁ := by
    simp only [Category.assoc, ha]
  have h_vanish : (π₃ ≫ (b ≫ S.bA)) ≫ S.aP₁ = 0 := by
    calc
      (π₃ ≫ (b ≫ S.bA)) ≫ S.aP₁ = π₃ ≫ (b ≫ (S.bA ≫ S.aP₁)) := by simp only [Category.assoc]
      _ = π₃ ≫ (b ≫ (0 : S.B₁ ⟶ S.P₁)) := by rw [S.z_bA_aP₁]
      _ = 0 := by simp
  have h_main : (π₃ ≫ π₂ ≫ π₁) ≫ y = r ≫ (S.rA ≫ S.aP₁) := by
    calc
      (π₃ ≫ π₂ ≫ π₁) ≫ y = (π₃ ≫ (π₂ ≫ a)) ≫ S.aP₁ := h_fully
      _ = ((π₃ ≫ (π₂ ≫ a) - π₃ ≫ (b ≫ S.bA) + π₃ ≫ (b ≫ S.bA))) ≫ S.aP₁ := by
        rw [sub_add_cancel]
      _ = ((r ≫ S.rA + π₃ ≫ (b ≫ S.bA))) ≫ S.aP₁ := by rw [h_eq]
      _ = (r ≫ S.rA) ≫ S.aP₁ + (π₃ ≫ (b ≫ S.bA)) ≫ S.aP₁ := by rw [Preadditive.add_comp]
      _ = (r ≫ S.rA) ≫ S.aP₁ := by rw [h_vanish, add_zero]
      _ = r ≫ (S.rA ≫ S.aP₁) := by rw [Category.assoc]
  have h_epi : Epi (π₃ ≫ π₂ ≫ π₁) := by
    have : Epi π₁ := inferInstance
    have : Epi π₂ := inferInstance
    have : Epi π₃ := inferInstance
    exact epi_comp π₃ (π₂ ≫ π₁)
  exact ⟨Z₃, π₃ ≫ π₂ ≫ π₁, h_epi, r, by
    simp only [Category.assoc] at h_main ⊢
    exact h_main⟩

/-- For an exact braid `S` in an abelian category `C`, the diagonal
sequence `P → Q → R → P₁ → Q₁`, with maps `pQ`, `qR`,
`rA ≫ aP₁`, and `pQ₁`, is exact at its three interior objects. -/
theorem exact :
    (ComposableArrows.mk₄ S.pQ S.qR (S.rA ≫ S.aP₁) S.pQ₁).Exact :=
  ComposableArrows.exact_of_δ₀ S.exact_Q.exact_toComposableArrows
    (ComposableArrows.exact_of_δ₀ S.exact_R.exact_toComposableArrows
      S.exact_P₁.exact_toComposableArrows)

end ExactBraid

end CategoryTheory
