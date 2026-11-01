/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
state capacity and magnitude bounds for the finite-alphabet grid row network.
-/
module

public import MathlibExt.Combinatorics.TensorNetwork.GridRows

/-! # Bounds for finite grid row networks

This module bounds the state, label, capacity, and integer magnitudes of the canonical row
contraction of a rectangular grid. Edge and diagonal alphabets remain explicit finite sets, while
the bounds on weights, factors, and interactions quantify over their unrestricted raw carriers.

Adapted from `Groundwork.Grid.Size` in
[`eth`](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5).

Attribution notice: eth: a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace TensorNetwork

open Finset

variable {ρ γ A T : Type*}

private theorem sum_le_card_mul {ι : Type*} (s : Finset ι) (f : ι → ℕ) (c : ℕ)
    (h : ∀ i ∈ s, f i ≤ c) :
    ∑ i ∈ s, f i ≤ s.card * c :=
  (Finset.sum_le_sum h).trans (Finset.sum_const_nat fun _ _ => rfl).le

private theorem two_mul_card_orderedPairs (X : Type*) [Fintype X] [LinearOrder X] :
    2 * (orderedPairs X).card = Fintype.card X * (Fintype.card X - 1) := by
  have hcard : (orderedPairs X).card = (Fintype.card X).choose 2 := by
    simpa [orderedPairs] using (Fintype.card_product_filter_lt (α := X))
  rw [hcard, Nat.choose_two_right,
    Nat.mul_div_cancel' (even_iff_two_dvd.1 (Nat.even_mul_pred_self _))]

private theorem gridRowCapacity_bound {g L m : ℕ} (hm : 1 ≤ m)
    (X : Type*) [Fintype X] [LinearOrder X] (hX : Fintype.card X = g)
    (F : X × X → ℕ) (hF : ∀ k, F k ≤ 2 * m * L) :
    g * L + ∑ k : X × X with k ∈ orderedPairs X, F k ≤ g ^ 2 * (m * L) := by
  have hpairs : 2 * (orderedPairs X).card = g * (g - 1) := by
    rw [two_mul_card_orderedPairs, hX]
  have hsum : ∑ k ∈ orderedPairs X, F k ≤ (orderedPairs X).card * (2 * m * L) :=
    sum_le_card_mul _ _ _ fun k _ => hF k
  have hsum' : ∑ k : X × X with k ∈ orderedPairs X, F k ≤
      (orderedPairs X).card * (2 * m * L) := by
    rw [show (univ.filter fun k : X × X => k ∈ orderedPairs X) = orderedPairs X by
      ext k
      simp]
    exact hsum
  have hrewrite : (orderedPairs X).card * (2 * m * L) =
      g * (g - 1) * (m * L) := by
    rw [← hpairs]
    ring
  rw [hrewrite] at hsum'
  have hfirst : g * L ≤ g * (m * L) :=
    Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hm)
  refine (Nat.add_le_add hfirst hsum').trans (le_of_eq ?_)
  rcases g with _ | n
  · simp
  · simp only [Nat.add_sub_cancel]
    ring

private theorem sum_erase_le {g c : ℕ} (X : Type*) [Fintype X] [DecidableEq X]
    (hX : Fintype.card X = g) (F : X → ℕ) (hF : ∀ b, F b ≤ g ^ 2 * c) (a : X) :
    ∑ b ∈ univ.erase a, F b ≤ g ^ 3 * c := by
  refine (sum_le_card_mul _ _ _ fun b _ => hF b).trans ?_
  rw [Finset.card_erase_of_mem (mem_univ a), Finset.card_univ, hX, ← Nat.mul_assoc]
  refine Nat.mul_le_mul_right _ ?_
  calc
    (g - 1) * g ^ 2 ≤ g * g ^ 2 := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    _ = g ^ 3 := by ring

private theorem sum_pairIndex_eq_two_mul [Fintype ρ] [LinearOrder ρ]
    (h : ρ × ρ → ℕ) :
    ∑ a, ∑ b ∈ univ.erase a, h (min a b, max a b) =
      2 * ∑ p ∈ orderedPairs ρ, h p := by
  have hsplit : ∀ a b : ρ, (if b ≠ a then h (min a b, max a b) else 0) =
      (if a < b then h (a, b) else 0) + (if b < a then h (b, a) else 0) := by
    intro a b
    rcases lt_trichotomy a b with hab | hab | hab
    · simp [hab, hab.ne', hab.le, not_lt.2 hab.le]
    · simp [hab]
    · simp [hab, hab.ne, hab.le, not_lt.2 hab.le]
  have hincreasing : ∑ p ∈ orderedPairs ρ, h p =
      ∑ a, ∑ b, if a < b then h (a, b) else 0 := by
    rw [orderedPairs, Finset.sum_filter, Fintype.sum_prod_type]
  have hdecreasing : (∑ a : ρ, ∑ b : ρ, if b < a then h (b, a) else 0) =
      ∑ a, ∑ b, if a < b then h (a, b) else 0 :=
    Finset.sum_comm
  calc
    ∑ a, ∑ b ∈ univ.erase a, h (min a b, max a b) =
        ∑ a, ∑ b, if b ≠ a then h (min a b, max a b) else 0 := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.filter_ne' univ a, Finset.sum_filter]
    _ = 2 * ∑ p ∈ orderedPairs ρ, h p := by
      simp only [hsplit, Finset.sum_add_distrib]
      rw [hdecreasing, hincreasing, two_mul]

private theorem sum_gridRectangles_eq [Fintype ρ] [LinearOrder ρ]
    [Fintype γ] [LinearOrder γ] (F : ((ρ × ρ) × (γ × γ)) → ℕ) :
    (∑ p ∈ orderedPairs ρ, ∑ k : γ × γ with k ∈ orderedPairs γ, F (p, k)) =
      ∑ ω ∈ gridRectangles ρ γ, F ω := by
  rw [gridRectangles, Finset.sum_product]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [show (univ.filter fun k : γ × γ => k ∈ orderedPairs γ) = orderedPairs γ by
    ext k
    simp]

private theorem card_gridRowStates_le [Fintype ρ] [LinearOrder ρ]
    [Fintype γ] [LinearOrder γ] [DecidableEq A]
    {g L : ℕ} (hρ : Fintype.card ρ = g) (hγ : Fintype.card γ = g)
    (labels diagonalLabels : Finset A) (hlabels : labels.card ≤ 2 ^ L)
    (hdiagonal : diagonalLabels.card ≤ 2 ^ L) (a : ρ) :
    (Fintype.piFinset fun i : γ =>
      Fintype.piFinset fun w : ρ × γ => if w = (a, i) then diagonalLabels else labels).card ≤
        2 ^ (g ^ 3 * L) := by
  rw [Fintype.card_piFinset]
  calc
    ∏ i : γ, (Fintype.piFinset fun w : ρ × γ =>
        if w = (a, i) then diagonalLabels else labels).card ≤
        ∏ _i : γ, (2 ^ L) ^ Fintype.card (ρ × γ) := by
      refine Finset.prod_le_prod fun i _ => ?_
      rw [Fintype.card_piFinset]
      calc
        ∏ w : ρ × γ, (if w = (a, i) then diagonalLabels else labels).card ≤
            ∏ _w : ρ × γ, 2 ^ L := by
          refine Finset.prod_le_prod fun w _ => ?_
          split_ifs
          · exact hdiagonal
          · exact hlabels
        _ = (2 ^ L) ^ Fintype.card (ρ × γ) := by simp
    _ = 2 ^ (g ^ 3 * L) := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_prod, hρ, hγ]
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring

private theorem card_gridRowLabels_le [Fintype γ] [LinearOrder γ] [DecidableEq A]
    {g L : ℕ} (hγ : Fintype.card γ = g)
    (labels : Finset A) (hlabels : labels.card ≤ 2 ^ L)
    (cutLabels : ((ρ × ρ) × (γ × γ)) → Finset T)
    (cap : ((ρ × ρ) × (γ × γ)) → ℕ)
    (hcut : ∀ ω, (cutLabels ω).card ≤ 2 ^ cap ω) (p : ρ × ρ) :
    ((Fintype.piFinset fun _ : γ => labels) ×ˢ
      Fintype.piFinset fun k : {k : γ × γ // k ∈ orderedPairs γ} =>
        cutLabels (p, k)).card ≤
      2 ^ (g * L + ∑ k : γ × γ with k ∈ orderedPairs γ, cap (p, k)) := by
  rw [Finset.card_product, Fintype.card_piFinset, Fintype.card_piFinset]
  have hedge : (∏ _i : γ, labels.card) ≤ 2 ^ (g * L) := by
    calc
      ∏ _i : γ, labels.card ≤ ∏ _i : γ, 2 ^ L :=
        Finset.prod_le_prod fun _ _ => hlabels
      _ = 2 ^ (g * L) := by
        simp only [Finset.prod_const, Finset.card_univ, hγ]
        rw [← pow_mul]
        congr 1
        ring
  have hcuts :
      (∏ k : {k : γ × γ // k ∈ orderedPairs γ}, (cutLabels (p, k)).card) ≤
        2 ^ ∑ k : {k : γ × γ // k ∈ orderedPairs γ}, cap (p, k) := by
    calc
      _ ≤ ∏ k : {k : γ × γ // k ∈ orderedPairs γ}, 2 ^ cap (p, k) :=
        Finset.prod_le_prod fun k _ => hcut (p, k)
      _ = _ := Finset.prod_pow_eq_pow_sum _ _ _
  have hsum : (∑ k : {k : γ × γ // k ∈ orderedPairs γ}, cap (p, k)) =
      ∑ k : γ × γ with k ∈ orderedPairs γ, cap (p, k) := by
    calc
      _ = ∑ k ∈ orderedPairs γ, cap (p, k) :=
        (Finset.sum_subtype (orderedPairs γ) (fun _ => Iff.rfl) fun k => cap (p, k)).symm
      _ = _ := by
        rw [show (univ.filter fun k : γ × γ => k ∈ orderedPairs γ) =
            orderedPairs γ by
          ext k
          simp]
  calc
    _ ≤ 2 ^ (g * L) *
        2 ^ ∑ k : {k : γ × γ // k ∈ orderedPairs γ}, cap (p, k) :=
      Nat.mul_le_mul hedge hcuts
    _ = 2 ^ (g * L + ∑ k : γ × γ with k ∈ orderedPairs γ, cap (p, k)) := by
      rw [← pow_add, hsum]

private theorem abs_indicator_mul_prod_le {ι κ : Type*}
    (s : Finset ι) (e : ι → ℤ) (t : Finset κ) (f : κ → ℤ) {b m : ℕ}
    (he : ∀ i ∈ s, |e i| ≤ 1) (hf : ∀ k ∈ t, |f k| ≤ 2 ^ b)
    (hm : t.card * b ≤ m) :
    |(∏ i ∈ s, e i) * ∏ k ∈ t, f k| ≤ 2 ^ m := by
  rw [abs_mul, Finset.abs_prod, Finset.abs_prod]
  have heprod : (∏ i ∈ s, |e i|) ≤ 1 := by
    calc
      _ ≤ ∏ _i ∈ s, (1 : ℤ) := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) he
      _ = 1 := by simp
  have hfprod : (∏ k ∈ t, |f k|) ≤ 2 ^ (t.card * b) := by
    calc
      _ ≤ ∏ _k ∈ t, (2 : ℤ) ^ b :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) hf
      _ = 2 ^ (t.card * b) := by rw [Finset.prod_const, ← pow_mul, Nat.mul_comm]
  calc
    (∏ i ∈ s, |e i|) * ∏ k ∈ t, |f k| ≤ 1 * 2 ^ (t.card * b) :=
      mul_le_mul heprod hfprod (Finset.prod_nonneg fun _ _ => abs_nonneg _) zero_le_one
    _ = 2 ^ (t.card * b) := one_mul _
    _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm

private theorem card_orderedPairs_le_sq [Fintype γ] [LinearOrder γ]
    {g : ℕ} (hγ : Fintype.card γ = g) :
    (orderedPairs γ).card ≤ g ^ 2 :=
  (Finset.card_le_univ _).trans_eq (by rw [Fintype.card_prod, hγ, sq])

private theorem abs_gridRowNetwork_interaction_le [Fintype ρ] [LinearOrder ρ]
    [Fintype γ] [LinearOrder γ] [DecidableEq A]
    {g L b : ℕ} (hγ : Fintype.card γ = g)
    (labels diagonalLabels : Finset A) (R : Instance (ρ × γ) A)
    (cutLabels : ((ρ × ρ) × (γ × γ)) → Finset T)
    (top bottom : ((ρ × ρ) × (γ × γ)) → A → A → T → ℤ)
    (cap : ((ρ × ρ) × (γ × γ)) → ℕ)
    (G : ((ρ × ρ) × (γ × γ)) → A → A → A → A → ℤ)
    (hfactor : ∀ ω x y u v,
      G ω x y u v = ∑ θ ∈ cutLabels ω, top ω x y θ * bottom ω u v θ)
    (hG : ∀ ω x y u v, |G ω x y u v| ≤ 2 ^ b)
    {a c : ρ} (hac : a < c) (z z' : γ → ρ × γ → A) :
    |(gridRowNetwork labels diagonalLabels R cutLabels top bottom cap L).interaction
      a c z z'| ≤ 2 ^ (g ^ 2 * b) := by
  rw [gridRowNetwork_interaction labels diagonalLabels R cutLabels top bottom cap L G
    hfactor hac]
  refine abs_indicator_mul_prod_le univ _ univ _ (b := b) (m := g ^ 2 * b) ?_ ?_ ?_
  · intro i _
    split_ifs <;> simp
  · intro k _
    exact hG _ _ _ _ _
  · simp only [Finset.card_univ, Fintype.card_coe]
    exact Nat.mul_le_mul_right b (card_orderedPairs_le_sq hγ)

/-- The capacity between two grid rows is at most `g²mL` when every active rectangle is
charged at most `2mL` and there are `g` columns. -/
theorem gridRowNetwork_capacity_le [Fintype ρ] [LinearOrder ρ]
    [Fintype γ] [LinearOrder γ] [DecidableEq A]
    {g L m : ℕ} (hm : 1 ≤ m) (hγ : Fintype.card γ = g)
    (labels diagonalLabels : Finset A) (R : Instance (ρ × γ) A)
    (cutLabels : ((ρ × ρ) × (γ × γ)) → Finset T)
    (top bottom : ((ρ × ρ) × (γ × γ)) → A → A → T → ℤ)
    (cap : ((ρ × ρ) × (γ × γ)) → ℕ)
    (hcap : ∀ ω, cap ω ≤ 2 * m * L) (a b : ρ) :
    (gridRowNetwork labels diagonalLabels R cutLabels top bottom cap L).c a b ≤
      g ^ 2 * (m * L) := by
  simp only [gridRowNetwork, hγ]
  exact gridRowCapacity_bound hm γ hγ
    (fun k => cap ((min a b, max a b), k)) fun k => hcap _

/-- The grid row network has shape `m g³ L` when both raw-state alphabets have at most
`2^L` elements and every rectangle label set and capacity obeys its declared bound. -/
theorem gridRowNetwork_shaped [Fintype ρ] [LinearOrder ρ]
    [Fintype γ] [LinearOrder γ] [DecidableEq A]
    {g L m : ℕ} (hm : 1 ≤ m) (hρ : Fintype.card ρ = g)
    (hγ : Fintype.card γ = g)
    (labels diagonalLabels : Finset A) (hlabels : labels.card ≤ 2 ^ L)
    (hdiagonal : diagonalLabels.card ≤ 2 ^ L) (R : Instance (ρ × γ) A)
    (cutLabels : ((ρ × ρ) × (γ × γ)) → Finset T)
    (top bottom : ((ρ × ρ) × (γ × γ)) → A → A → T → ℤ)
    (cap : ((ρ × ρ) × (γ × γ)) → ℕ)
    (hcut : ∀ ω, (cutLabels ω).card ≤ 2 ^ cap ω)
    (hcap : ∀ ω, cap ω ≤ 2 * m * L) :
    (gridRowNetwork labels diagonalLabels R cutLabels top bottom cap L).Shaped
      (m * (g ^ 3 * L)) where
  card_S a := by
    simp only [gridRowNetwork]
    exact (card_gridRowStates_le hρ hγ labels diagonalLabels hlabels hdiagonal a).trans
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left _ hm))
  c_symm a b := by
    simp only [gridRowNetwork, min_comm, max_comm]
  sum_c a := by
    calc
      ∑ b ∈ univ.erase a,
          (gridRowNetwork labels diagonalLabels R cutLabels top bottom cap L).c a b ≤
          g ^ 3 * (m * L) :=
        sum_erase_le ρ hρ _
          (fun b => gridRowNetwork_capacity_le hm hγ labels diagonalLabels R cutLabels
            top bottom cap hcap a b) a
      _ = m * (g ^ 3 * L) := by ring
  card_labelSet a b hab := by
    have hlt : min a b < max a b := min_lt_max.mpr hab
    simp only [Factored.labelSet, gridRowNetwork, hγ, hlt, ↓reduceIte]
    exact card_gridRowLabels_le hγ labels hlabels cutLabels cap hcut (min a b, max a b)

/-- Under uniform raw tensor and factor bounds, the grid row network has exact source exponents
`m g³ L` for shape and `g B + g² b` for integer magnitudes. -/
theorem gridRowNetwork_sized [Fintype ρ] [LinearOrder ρ]
    [Fintype γ] [LinearOrder γ] [DecidableEq A]
    {g L m B b : ℕ} (hm : 1 ≤ m) (hρ : Fintype.card ρ = g)
    (hγ : Fintype.card γ = g)
    (labels diagonalLabels : Finset A) (hlabels : labels.card ≤ 2 ^ L)
    (hdiagonal : diagonalLabels.card ≤ 2 ^ L) (R : Instance (ρ × γ) A)
    (hR : ∀ w h, |R w h| ≤ 2 ^ B)
    (G : ((ρ × ρ) × (γ × γ)) → A → A → A → A → ℤ)
    (cutLabels : ((ρ × ρ) × (γ × γ)) → Finset T)
    (top bottom : ((ρ × ρ) × (γ × γ)) → A → A → T → ℤ)
    (cap : ((ρ × ρ) × (γ × γ)) → ℕ)
    (hfactor : ∀ ω x y u v,
      G ω x y u v = ∑ θ ∈ cutLabels ω, top ω x y θ * bottom ω u v θ)
    (hcut : ∀ ω, (cutLabels ω).card ≤ 2 ^ cap ω)
    (hcap : ∀ ω, cap ω ≤ 2 * m * L)
    (htop : ∀ ω x y θ, |top ω x y θ| ≤ 2 ^ b)
    (hbottom : ∀ ω u v θ, |bottom ω u v θ| ≤ 2 ^ b)
    (hG : ∀ ω x y u v, |G ω x y u v| ≤ 2 ^ b) :
    (gridRowNetwork labels diagonalLabels R cutLabels top bottom cap L).Sized
      (m * (g ^ 3 * L)) (g * B + g ^ 2 * b) where
  toShaped := gridRowNetwork_shaped hm hρ hγ labels diagonalLabels hlabels hdiagonal
    R cutLabels top bottom cap hcut hcap
  abs_W a z := by
    simp only [gridRowNetwork]
    rw [mul_comm]
    refine abs_indicator_mul_prod_le (orderedPairs γ) _ univ _
      (b := B) (m := g * B + g ^ 2 * b) ?_ ?_ ?_
    · intro q _
      split_ifs <;> simp
    · intro i _
      exact hR _ _
    · simp only [Finset.card_univ, hγ]
      exact Nat.le_add_right _ _
  abs_f a c z θ := by
    have hcount : (orderedPairs γ).card * b ≤ g * B + g ^ 2 * b := by
      exact (Nat.mul_le_mul_right b (card_orderedPairs_le_sq hγ)).trans
        (Nat.le_add_left _ _)
    simp only [gridRowNetwork]
    split_ifs
    · refine abs_indicator_mul_prod_le univ _ univ _
        (b := b) (m := g * B + g ^ 2 * b) ?_ ?_ ?_
      · intro i _
        split_ifs <;> simp
      · intro k _
        exact htop _ _ _ _
      · simpa using hcount
    · refine abs_indicator_mul_prod_le univ _ univ _
        (b := b) (m := g * B + g ^ 2 * b) ?_ ?_ ?_
      · intro i _
        split_ifs <;> simp
      · intro k _
        exact hbottom _ _ _ _
      · simpa using hcount
  abs_interaction a c z z' hac := by
    rcases lt_or_gt_of_ne hac with h | h
    · exact (abs_gridRowNetwork_interaction_le hγ labels diagonalLabels R cutLabels
        top bottom cap G hfactor hG h z z').trans
          (pow_le_pow_right₀ (by norm_num) (Nat.le_add_left _ _))
    · rw [Factored.interaction_comm]
      exact (abs_gridRowNetwork_interaction_le hγ labels diagonalLabels R cutLabels
        top bottom cap G hfactor hG h z' z).trans
          (pow_le_pow_right₀ (by norm_num) (Nat.le_add_left _ _))

/-- The directed total capacity consists of all vertical row edges plus twice the active
rectangle capacity; diagonal row capacities are excluded. -/
theorem gridRowNetwork_totalCapacity [Fintype ρ] [LinearOrder ρ]
    [Fintype γ] [LinearOrder γ] [DecidableEq A]
    {g L : ℕ} (hρ : Fintype.card ρ = g) (hγ : Fintype.card γ = g)
    (labels diagonalLabels : Finset A) (R : Instance (ρ × γ) A)
    (cutLabels : ((ρ × ρ) × (γ × γ)) → Finset T)
    (top bottom : ((ρ × ρ) × (γ × γ)) → A → A → T → ℤ)
    (cap : ((ρ × ρ) × (γ × γ)) → ℕ) :
    (gridRowNetwork labels diagonalLabels R cutLabels top bottom cap L).totalCapacity =
      g ^ 2 * (g - 1) * L +
        2 * ∑ ω ∈ gridRectangles ρ γ, cap ω := by
  have hpair := sum_pairIndex_eq_two_mul (ρ := ρ) fun p =>
    g * L + ∑ k : γ × γ with k ∈ orderedPairs γ, cap (p, k)
  unfold Factored.totalCapacity
  simp only [gridRowNetwork, hγ]
  rw [hpair, Finset.sum_add_distrib, sum_gridRectangles_eq]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hpairs := two_mul_card_orderedPairs ρ
  rw [hρ] at hpairs
  calc
    2 * ((orderedPairs ρ).card * (g * L) +
        ∑ ω ∈ gridRectangles ρ γ, cap ω) =
        (2 * (orderedPairs ρ).card) * (g * L) +
          2 * ∑ ω ∈ gridRectangles ρ γ, cap ω := by ring
    _ = g ^ 2 * (g - 1) * L +
        2 * ∑ ω ∈ gridRectangles ρ γ, cap ω := by
      rw [hpairs]
      ring

end TensorNetwork
