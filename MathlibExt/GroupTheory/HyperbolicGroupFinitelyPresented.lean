/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.FinitelyPresentedGroup
public import MathlibExt.GroupTheory.HyperbolicGroup
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Set.Finite.List
import Mathlib.Tactic.Rify

/-!
# Finite presentations of hyperbolic groups

A word-hyperbolic group is finitely presented. The four-point inequality gives a shortcut
across each sufficiently long closed word, so the bounded-length relations normally generate
the kernel of the presentation map.
-/

namespace MathlibExt.GroupTheory.HyperbolicGroupWanted

open FreeGroup (mk invRev invRev_length mul_mk inv_mk)

section

variable {G ι : Type*} [Group G] (P : Group.Generators G ι)

-- The corners of the loop are 1, a, a*b, and a*b*c. If both diagonals had length at
-- least 2*k, their sum would violate the four-point bound for the opposite sides.
private theorem short_diagonal {δ : ℝ}
    (hδ : @Metric.IsDeltaHyperbolic G P.normedGroup.toPseudoMetricSpace δ)
    {k : ℕ} (hk : δ + 3 < k) (a b c d : G) (h : a * b * c * d = 1)
    (ha : P.wordLength a ≤ k + 3) (hb : P.wordLength b ≤ k + 3)
    (hc : P.wordLength c ≤ k + 3) (hd : P.wordLength d ≤ k + 3) :
    P.wordLength (a * b) < 2 * k ∨ P.wordLength (b * c) < 2 * k := by
  let _ := P.normedGroup
  have step (x y : G) : dist x (x * y) = (P.wordLength y : ℝ) := by
    rw [dist_eq_norm_inv_mul, inv_mul_cancel_left]
    rfl
  have origin (x : G) : dist 1 x = (P.wordLength x : ℝ) := by simpa using step 1 x
  have diag : dist a (a * b * c) = (P.wordLength (b * c) : ℝ) := by
    rw [mul_assoc, step]
  have four := hδ.four_point 1 a (a * b) (a * b * c)
  simp only [Metric.gromovProduct_eq, origin, diag, step] at four
  rw [eq_inv_of_mul_eq_one_left h, P.wordLength_inv] at four
  by_contra! hlong
  obtain ⟨h₁, h₂⟩ := hlong
  rify at ha hb hc hd h₁ h₂
  rw [min_def] at four
  split at four <;> linarith

-- Cutting the word u ++ v along a geodesic representative of u gives two shorter
-- relations. Their images multiply to the image of the original relation.
private theorem cut_loop {H : Type*} [Group H] (q : FreeGroup ι →* H)
    (u v : List (ι × Bool)) (h : P.wordProd u * P.wordProd v = 1)
    (hu : P.wordLength (P.wordProd u) < u.length)
    (hv : P.wordLength (P.wordProd u) < v.length)
    (ih : ∀ w : List (ι × Bool), w.length < u.length + v.length →
      P.wordProd w = 1 → q (mk w) = 1) :
    q (mk u) * q (mk v) = 1 := by
  obtain ⟨s, hs, he⟩ := P.exists_isGeodesic (P.wordProd u)
  have hlen : s.length = P.wordLength (P.wordProd u) := he ▸ hs.eq.symm
  have left := ih (u ++ invRev s) (by simp only [List.length_append, invRev_length]; omega)
    (by rw [P.wordProd_append, P.wordProd_invRev, he, mul_inv_cancel])
  have right := ih (s ++ v) (by simp only [List.length_append]; omega)
    (by rwa [P.wordProd_append, he])
  simp only [← mul_mk, ← inv_mk, map_mul, map_inv] at left right
  rwa [eq_of_mul_inv_eq_one left]

-- Peel off three arcs of length k. The fourth contains the remainder modulo four.
private theorem split_quarters {α : Type*} (w : List α) (k : ℕ) (hk : k = w.length / 4) :
    ∃ a b c d : List α, w = a ++ b ++ c ++ d ∧
      a.length = k ∧ b.length = k ∧ c.length = k ∧ k ≤ d.length ∧ d.length ≤ k + 3 := by
  have peel (l : List α) (hl : k ≤ l.length) :
      ∃ x y : List α, l = x ++ y ∧ x.length = k :=
    ⟨_, _, (l.take_append_drop k).symm, by simp [Nat.min_eq_left hl]⟩
  obtain ⟨a, s, rfl, ha⟩ := peel w (by omega)
  simp only [List.length_append] at hk
  obtain ⟨b, t, rfl, hb⟩ := peel s (by omega)
  simp only [List.length_append] at hk
  obtain ⟨c, d, rfl, hc⟩ := peel t (by omega)
  simp only [List.length_append] at hk
  exact ⟨a, b, c, d, by simp [List.append_assoc], ha, hb, hc, by omega, by omega⟩

private theorem kill_loops {δ : ℝ}
    (hδ : @Metric.IsDeltaHyperbolic G P.normedGroup.toPseudoMetricSpace δ)
    {K : ℕ} (hK : δ + 3 < K) {H : Type*} [Group H] (q : FreeGroup ι →* H)
    (short : ∀ w : List (ι × Bool), w.length < 4 * K → P.wordProd w = 1 → q (mk w) = 1)
    (w : List (ι × Bool)) (hw : P.wordProd w = 1) : q (mk w) = 1 := by
  induction hlen : w.length using Nat.strong_induction_on generalizing w with
  | ind n ih =>
    by_cases hn : n < 4 * K
    · exact short w (by omega) hw
    let k := n / 4
    have hk : K ≤ k := by dsimp [k]; omega
    obtain ⟨a, b, c, d, rfl, ha, hb, hc, hd, hd'⟩ := split_quarters w k (by rw [hlen])
    simp only [List.length_append] at hlen
    simp only [P.wordProd_append] at hw
    have arc (s : List (ι × Bool)) (hs : s.length ≤ k + 3) :
        P.wordLength (P.wordProd s) ≤ k + 3 := (P.wordLength_wordProd_le s).trans hs
    have diagonals := short_diagonal P hδ (hK.trans_le (by exact_mod_cast hk))
      _ _ _ _ hw (arc a (by omega)) (arc b (by omega)) (arc c (by omega)) (arc d hd')
    have cut (u v : List (ι × Bool)) (hsum : u.length + v.length = n)
        (hu : 2 * k ≤ u.length) (hv : 2 * k ≤ v.length)
        (hdiag : P.wordLength (P.wordProd u) < 2 * k)
        (he : P.wordProd u * P.wordProd v = 1) : q (mk u) * q (mk v) = 1 :=
      cut_loop P q u v he (hdiag.trans_le hu) (hdiag.trans_le hv)
        fun s hs he' => ih s.length (hsum ▸ hs) s he' rfl
    rcases diagonals with h | h
    · have glued := cut (a ++ b) (c ++ d) (by simp; omega) (by simp; omega) (by simp; omega)
        (by rwa [P.wordProd_append]) (by simpa [P.wordProd_append, mul_assoc] using hw)
      simpa only [← mul_mk, map_mul, mul_assoc] using glued
    · have rot : P.wordProd b * P.wordProd c * P.wordProd d * P.wordProd a = 1 := by
        apply mul_eq_one_comm.mpr
        simpa only [mul_assoc] using hw
      have glued := cut (b ++ c) (d ++ a) (by simp; omega) (by simp; omega) (by simp; omega)
        (by rwa [P.wordProd_append]) (by simpa [P.wordProd_append, mul_assoc] using rot)
      simp only [← mul_mk, map_mul, mul_assoc] at glued ⊢
      apply mul_eq_one_comm.mpr
      simpa only [mul_assoc] using glued

end

/-- **Hyperbolic groups are finitely presented** (Gromov, *Hyperbolic groups*, 1987,
Corollary 2.2.A of Rips's theorem 2.2). -/
public theorem isFinitelyPresented_of_isHyperbolic {G : Type*} [Group G]
    (h : Group.IsHyperbolic G) : Group.IsFinitelyPresented G := by
  obtain ⟨ι, _, P, δ, hδ⟩ := h
  obtain ⟨K, hK⟩ := exists_nat_gt (δ + 3)
  let words := {w : List (ι × Bool) | w.length < 4 * K ∧ P.wordProd w = 1}
  let rels := mk '' words
  have hfin : words.Finite := (List.finite_length_lt _ _).subset fun _ hw => hw.1
  apply Group.IsFinitelyPresented.of_surjective P.lift P.lift_surjective
  refine ⟨rels, hfin.image _, le_antisymm (Subgroup.normalClosure_le_normal ?_) ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact hw.2
  · intro x hx
    obtain ⟨w, rfl⟩ := (Quot.mk_surjective x : ∃ w, mk w = x)
    apply PresentedGroup.mk_eq_one_iff.mp
    exact kill_loops P hδ hK (PresentedGroup.mk rels)
      (fun s hs he => PresentedGroup.one_of_mem ⟨s, ⟨hs, he⟩, rfl⟩) w hx

end MathlibExt.GroupTheory.HyperbolicGroupWanted
