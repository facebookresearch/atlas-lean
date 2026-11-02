/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Radon
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

section

open scoped InnerProductSpace

namespace MathlibExt.Geometry.Convex.RadoCenterpointWanted

/-- A strict upper halfspace is convex. -/
private theorem aux_convex_upper {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    Convex ℝ {y | t < ⟪v, y⟫_ℝ} := by
  intro a ha b hb s w hs hw hsw
  simp only [Set.mem_ofPred_eq] at ha hb ⊢
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  rcases eq_or_ne s 0 with rfl | hs0
  · have hw1 : w = 1 := by linarith
    rw [hw1, one_mul]
    simpa using hb
  · have hspos : 0 < s := by
      rcases lt_or_gt_of_ne hs0 with h | h
      · linarith
      · exact h
    have e1 : s * t < s * ⟪v, a⟫_ℝ := mul_lt_mul_of_pos_left ha hspos
    have e2 : w * t ≤ w * ⟪v, b⟫_ℝ := mul_le_mul_of_nonneg_left hb.le hw
    have e3 : s * t + w * t = t := by rw [← add_mul, hsw, one_mul]
    linarith

/--
**Rado's centerpoint theorem.** Let $n \ge 1$ and let $p_1, \dots, p_n$ be points of
$\mathbb{R}^d$, not necessarily distinct. Then some point $x$ in the convex hull of
$\{p_1, \dots, p_n\}$ has at least $n/(d+1)$ of the points in every closed halfspace containing
it: for all $v \in \mathbb{R}^d$ and $t \in \mathbb{R}$ with $\langle v, x \rangle \le t$, the
number of indices $i$ with $\langle v, p_i \rangle \le t$ is at least $n/(d+1)$.

Proves `Wanted` entry `rado_centerpoint`.

Source: R. Rado, J. London Math. Soc. s1-21 (1946), 291-300, DOI 10.1112/jlms/s1-21.4.291.
-/
theorem rado_centerpoint
    {d n : ℕ} (hn : 0 < n)
    (p : Fin n → EuclideanSpace ℝ (Fin d)) :
    ∃ x ∈ convexHull ℝ (Set.range p),
      ∀ (v : EuclideanSpace ℝ (Fin d)) (t : ℝ),
        ⟪v, x⟫_ℝ ≤ t →
          n ≤ (d + 1) * Fintype.card {i : Fin n // ⟪v, p i⟫_ℝ ≤ t} := by
  classical
  have hd1 : 0 < d + 1 := Nat.succ_pos d
  set q : ℕ := (d * n) / (d + 1) with hq
  have hdiv1 : (d + 1) * q ≤ d * n := by
    have h := Nat.div_mul_le_self (d * n) (d + 1)
    rw [hq, mul_comm (d + 1) ((d * n) / (d + 1))]
    exact h
  have hmod : (d * n) % (d + 1) < d + 1 := Nat.mod_lt _ hd1
  have hdiv2 : d * n < (d + 1) * (q + 1) := by
    have hdm := Nat.div_add_mod (d * n) (d + 1)
    rw [← hq] at hdm
    have e3 : (d + 1) * (q + 1) = (d + 1) * q + (d + 1) := by ring
    omega
  have hlt : d * n < (d + 1) * n := mul_lt_mul_of_pos_right (Nat.lt_succ_self d) hn
  have hqq : q < n := by
    by_contra hcon
    push Not at hcon
    have hle : (d + 1) * n ≤ (d + 1) * q := Nat.mul_le_mul_left _ hcon
    omega
  have hqn : q + 1 ≤ n := by omega
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  have hmem : ∀ (J : Finset {S : Finset (Fin n) // S.card = q + 1}), J ⊆ Finset.univ →
      J.card ≤ d + 1 → (⋂ a ∈ J, convexHull ℝ (p '' (↑a.1 : Set (Fin n)))).Nonempty := by
    intro J _ hJcard
    have hcomp : ∀ a : {S : Finset (Fin n) // S.card = q + 1},
        (Finset.univ \ a.1).card = n - (q + 1) := by
      intro a
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, a.2]
    have hub : (J.biUnion (fun a => Finset.univ \ a.1)).card ≤ J.card * (n - (q + 1)) := by
      calc (J.biUnion (fun a => Finset.univ \ a.1)).card
          ≤ ∑ a ∈ J, (Finset.univ \ a.1).card := Finset.card_biUnion_le
        _ = ∑ _a ∈ J, (n - (q + 1)) := Finset.sum_congr rfl (fun a _ => hcomp a)
        _ = J.card * (n - (q + 1)) := by simp [Finset.sum_const]
    have hsmall : (J.biUnion (fun a => Finset.univ \ a.1)).card ≤ n - 1 := by
      have h1 : J.card * (n - (q + 1)) ≤ (d + 1) * (n - (q + 1)) :=
        Nat.mul_le_mul_right _ hJcard
      have h2 : (d + 1) * (n - (q + 1)) ≤ n - 1 := by
        have e1 : (d + 1) * (n - (q + 1)) + (d + 1) * (q + 1) = (d + 1) * n := by
          rw [← Nat.mul_add, Nat.sub_add_cancel hqn]
        have e2 : (d + 1) * n = d * n + n := by ring
        have e3 : (d + 1) * (q + 1) = (d + 1) * q + (d + 1) := by ring
        omega
      omega
    obtain ⟨i, hiU⟩ : ∃ i, i ∉ J.biUnion (fun a => Finset.univ \ a.1) := by
      by_contra hcon
      push Not at hcon
      have hsub : (Finset.univ : Finset (Fin n)) ⊆ J.biUnion (fun a => Finset.univ \ a.1) :=
        fun i _ => hcon i
      have hle := Finset.card_le_card hsub
      rw [Finset.card_univ, Fintype.card_fin] at hle
      omega
    refine ⟨p i, ?_⟩
    refine Set.mem_biInter (fun a ha => ?_)
    have haJ : a ∈ J := Finset.mem_coe.mp ha
    have hia : i ∈ a.1 := by
      by_contra hcon
      exact hiU (Finset.mem_biUnion.mpr
        ⟨a, haJ, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hcon⟩⟩)
    exact subset_convexHull ℝ _ (Set.mem_image_of_mem _ (Finset.mem_coe.mpr hia))
  have hHelly := Convex.helly_theorem' (𝕜 := ℝ)
    (F := fun a : {S : Finset (Fin n) // S.card = q + 1} =>
      convexHull ℝ (p '' (↑a.1 : Set (Fin n)))) (s := Finset.univ)
    (fun a _ => convex_convexHull ℝ _)
    (fun I hIsub hIcard => by
      rw [hfr] at hIcard
      exact hmem I hIsub hIcard)
  obtain ⟨x, hx⟩ := hHelly
  simp only [Set.mem_iInter] at hx
  obtain ⟨S₀, hS₀sub, hS₀card⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n))) (n := q + 1)
    (by rw [Finset.card_univ, Fintype.card_fin]; exact hqn)
  have hx0 : x ∈ convexHull ℝ (p '' (↑S₀ : Set (Fin n))) := hx ⟨S₀, hS₀card⟩ (Finset.mem_univ _)
  have hsubRange : p '' (↑S₀ : Set (Fin n)) ⊆ Set.range p := by
    rintro y ⟨i, _, rfl⟩
    exact Set.mem_range_self i
  have hxRange : x ∈ convexHull ℝ (Set.range p) := convexHull_mono hsubRange hx0
  refine ⟨x, hxRange, ?_⟩
  intro v t hxt
  set Bad : Finset (Fin n) := Finset.univ.filter (fun i => ⟪v, p i⟫_ℝ ≤ t) with hBad
  have hBk : Fintype.card {i : Fin n // ⟪v, p i⟫_ℝ ≤ t} = Bad.card := by
    have h := Fintype.card_ofFinset (p := {x : Fin n | ⟪v, p x⟫_ℝ ≤ t}) Bad
      (fun x => by simp [hBad])
    exact h
  by_contra hcon
  push Not at hcon
  rw [hBk] at hcon
  have hk_le : Bad.card ≤ n := by
    rw [hBad]
    calc (Finset.univ.filter _).card ≤ Finset.univ.card := Finset.card_filter_le _ _
      _ = n := by rw [Finset.card_univ, Fintype.card_fin]
  have hTc : (Finset.univ \ Bad).card = n - Bad.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  have hTcard : q + 1 ≤ (Finset.univ \ Bad).card := by
    rw [hTc]
    by_contra hlt
    push Not at hlt
    have hle : (d + 1) * (n - Bad.card) ≤ (d + 1) * q := Nat.mul_le_mul_left _ (by omega)
    have f1 : (d + 1) * (n - Bad.card) + (d + 1) * Bad.card = (d + 1) * n := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hk_le]
    have e2 : (d + 1) * n = d * n + n := by ring
    omega
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq
    (s := Finset.univ \ Bad) (n := q + 1) hTcard
  have hxS : x ∈ convexHull ℝ (p '' (↑S : Set (Fin n))) := hx ⟨S, hScard⟩ (Finset.mem_univ _)
  have hsub : p '' (↑S : Set (Fin n)) ⊆ {y | t < ⟪v, y⟫_ℝ} := by
    rintro y ⟨i, hi, rfl⟩
    simp only [Set.mem_ofPred_eq]
    have hiS : i ∈ S := Finset.mem_coe.mp hi
    have hiT := hSsub hiS
    rw [Finset.mem_sdiff] at hiT
    by_contra hle
    push Not at hle
    exact hiT.2 (by rw [hBad]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hle⟩)
  have hxmem : x ∈ {y | t < ⟪v, y⟫_ℝ} := convexHull_min hsub (aux_convex_upper v t) hxS
  simp only [Set.mem_ofPred_eq] at hxmem
  linarith

end MathlibExt.Geometry.Convex.RadoCenterpointWanted
