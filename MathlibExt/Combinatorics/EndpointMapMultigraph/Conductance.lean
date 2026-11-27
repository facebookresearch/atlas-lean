/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.EndpointMapMultigraph.WeightedLaplacian
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Weighted degrees, volumes and the easy conductance bound

For a finite multigraph with endpoint maps `end₁ end₂ : E → V` and edge weights `w`, the weighted
degree `d(a)` of a vertex, the volume `d(S) = ∑_{a ∈ S} d(a)` of a vertex set, and the easy
direction of Cheeger's inequality for conductance: if `λ · yᵀDy ≤ yᵀLy` for every `y` with
`yᵀd = 0` (the second eigenvalue `ν₂` of the normalized Laplacian is the best such `λ`), then
`λ d(S) d(V \ S) ≤ d(V) w(∂S)` for every `S` (D. A. Spielman, *Spectral and Algebraic Graph
Theory*, draft of 2 April 2025, Lemma 20.3.1 and inequality (20.2)); and the hard direction
(`exists_threshold_cut_le_sqrt`): a threshold cut of any degree-centered vector `z` has
conductance at most `√(2 zᵀLz / zᵀDz)` (Spielman, Theorem 21.1.3).
-/

@[expose] public section

namespace EndpointMapMultigraph

open Matrix Finset

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]

/-- **Weighted degree.** The weighted degree `d(a) = ∑_e w_e [a is an endpoint of e]` of a vertex
in the multigraph with endpoint maps `end₁ end₂` and weights `w` (a loop counts twice; loops
contribute nothing to the Laplacian, and the conductance results below allow them). -/
noncomputable def weightedDegree (end₁ end₂ : E → V) (w : E → ℝ) (a : V) : ℝ :=
  ∑ e, w e * ((if end₁ e = a then 1 else 0) + (if end₂ e = a then 1 else 0))

/-- **Volume of a vertex set.** `d(S) = ∑_{a ∈ S} d(a)`, the sum of the weighted degrees. -/
noncomputable def volume (end₁ end₂ : E → V) (w : E → ℝ) (S : Finset V) : ℝ :=
  ∑ a ∈ S, weightedDegree end₁ end₂ w a

omit [DecidableEq E] [Fintype V] in
/-- **Weighted degrees are nonnegative.** For nonnegative weights `w`, every weighted degree
`d(a) = ∑_e w_e [a is an endpoint of e]` is nonnegative. For positive conductances on a loopless
multigraph, `d(a)` is the weight `π(a)` of R. Lyons and Y. Peres, *Probability on Trees and
Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026,
Section 2.1: the sum of the weights of the edges incident to `a`. -/
theorem weightedDegree_nonneg (end₁ end₂ : E → V) {w : E → ℝ} (hw : 0 ≤ w) (a : V) :
    0 ≤ weightedDegree end₁ end₂ w a :=
  Finset.sum_nonneg fun e _ => mul_nonneg (hw e) (by split_ifs <;> norm_num)

/-- **Easy direction of Cheeger's inequality for conductance.** Let `d` be the weighted degrees
and `λ` a lower bound for the generalized Rayleigh quotient `yᵀLy / yᵀDy` over all `y` with
`∑_a d(a) y(a) = 0` (the second-smallest eigenvalue `ν₂` of the normalized Laplacian is the best
such bound). Then for every vertex set `S`, `λ · d(S) · d(V \ S) ≤ d(V) · w(∂S)`, i.e.
`ν₂ ≤ d(V) w(∂S) / (d(S) d(V \ S))`, which gives `ν₂ / 2 ≤ φ(S)` (D. A. Spielman, *Spectral and
Algebraic Graph Theory*, draft of 2 April 2025, Lemma 20.3.1 and inequality (20.2)). -/
theorem mul_volume_mul_volume_compl_le_of_forall (end₁ end₂ : E → V) {w : E → ℝ} (hw : 0 ≤ w)
    {lam : ℝ}
    (hlam : ∀ y : V → ℝ, ∑ a, weightedDegree end₁ end₂ w a * y a = 0 →
      lam * ∑ a, weightedDegree end₁ end₂ w a * y a ^ 2 ≤ y ⬝ᵥ (laplacian end₁ end₂ w *ᵥ y))
    (S : Finset V) :
    lam * volume end₁ end₂ w S * volume end₁ end₂ w (Finset.univ \ S) ≤
      volume end₁ end₂ w Finset.univ * ∑ e ∈ cut end₁ end₂ S, w e := by
  classical
  set d := weightedDegree end₁ end₂ w
  set D := volume end₁ end₂ w Finset.univ
  set dS := volume end₁ end₂ w S
  set dSc := volume end₁ end₂ w (Finset.univ \ S)
  have hsplit : D = dS + dSc := by
    simp only [D, dS, dSc, volume]
    rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset
      (Finset.subset_univ S)]
  set y : V → ℝ := D • indicator S - dS • (1 : V → ℝ) with hy
  have hyS : ∀ a ∈ S, y a = D - dS := fun a ha => by simp [hy, indicator, ha]
  have hyN : ∀ a ∉ S, y a = -dS := fun a ha => by simp [hy, indicator, ha]
  have hsum : ∀ f : V → ℝ, ∑ a, f a = ∑ a ∈ S, f a + ∑ a ∈ Finset.univ \ S, f a := fun f => by
    rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset
      (Finset.subset_univ S)]
  have hyd : ∑ a, d a * y a = 0 := by
    have h1 : ∑ a ∈ S, d a * y a = ∑ a ∈ S, d a * (D - dS) :=
      Finset.sum_congr rfl fun a ha => by rw [hyS a ha]
    have h2 : ∑ a ∈ Finset.univ \ S, d a * y a = ∑ a ∈ Finset.univ \ S, d a * (-dS) :=
      Finset.sum_congr rfl fun a ha => by rw [hyN a (Finset.mem_sdiff.1 ha).2]
    rw [hsum, h1, h2, ← Finset.sum_mul, ← Finset.sum_mul]
    change dS * (D - dS) + dSc * (-dS) = 0
    rw [hsplit]
    ring
  have hyDy : ∑ a, d a * y a ^ 2 = dS * dSc * D := by
    have h1 : ∑ a ∈ S, d a * y a ^ 2 = ∑ a ∈ S, d a * (D - dS) ^ 2 :=
      Finset.sum_congr rfl fun a ha => by rw [hyS a ha]
    have h2 : ∑ a ∈ Finset.univ \ S, d a * y a ^ 2 = ∑ a ∈ Finset.univ \ S, d a * (-dS) ^ 2 :=
      Finset.sum_congr rfl fun a ha => by rw [hyN a (Finset.mem_sdiff.1 ha).2]
    rw [hsum, h1, h2, ← Finset.sum_mul, ← Finset.sum_mul]
    change dS * (D - dS) ^ 2 + dSc * (-dS) ^ 2 = dS * dSc * D
    rw [hsplit]
    ring
  have hLy : y ⬝ᵥ (laplacian end₁ end₂ w *ᵥ y) = D ^ 2 * ∑ e ∈ cut end₁ end₂ S, w e := by
    have hL1 := laplacian_mulVec_one end₁ end₂ w
    have hsym : (1 : V → ℝ) ⬝ᵥ (laplacian end₁ end₂ w *ᵥ indicator S) = 0 := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, laplacian_transpose, hL1,
        zero_dotProduct]
    rw [hy, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hL1, smul_zero, sub_zero,
      dotProduct_smul, sub_dotProduct, smul_dotProduct, smul_dotProduct, hsym,
      indicator_dotProduct_mulVec_laplacian, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring
  have key := hlam y hyd
  rw [hyDy, hLy] at key
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun a _ => weightedDegree_nonneg end₁ end₂ hw a
  have hdS0 : 0 ≤ dS := Finset.sum_nonneg fun a _ => weightedDegree_nonneg end₁ end₂ hw a
  have hdSc0 : 0 ≤ dSc := Finset.sum_nonneg fun a _ => weightedDegree_nonneg end₁ end₂ hw a
  rcases hD0.eq_or_lt with h0 | hpos
  · have hdS : dS = 0 := by linarith
    rw [hdS, ← h0]
    simp
  · have : D * (lam * dS * dSc) ≤ D * (D * ∑ e ∈ cut end₁ end₂ S, w e) := by nlinarith [key]
    exact le_of_mul_le_mul_left this hpos

/-- The antiderivative `τ |τ|` of the threshold density `2 |τ|`. -/
private noncomputable def cheegerG (τ : ℝ) : ℝ := τ * |τ|

private theorem cheegerG_mono {x y : ℝ} (h : x ≤ y) : cheegerG x ≤ cheegerG y := by
  unfold cheegerG
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hx, abs_of_nonneg hy]; nlinarith
  · rw [abs_of_nonneg hx, abs_of_nonpos hy]; nlinarith
  · rw [abs_of_nonpos hx, abs_of_nonneg hy]; nlinarith
  · rw [abs_of_nonpos hx, abs_of_nonpos hy]; nlinarith

/-- Mass of the threshold interval ending at `τ`: `g τ - g p`, `p` the predecessor of `τ` in `T`. -/
private noncomputable def cheegerMu (T : Finset ℝ) (τ : ℝ) : ℝ :=
  if h : (T.filter (· < τ)).Nonempty then cheegerG τ - cheegerG ((T.filter (· < τ)).max' h)
  else 0

private theorem cheegerMu_nonneg (T : Finset ℝ) (τ : ℝ) : 0 ≤ cheegerMu T τ := by
  unfold cheegerMu
  split_ifs with h
  · have := (Finset.mem_filter.1 (Finset.max'_mem _ h)).2
    linarith [cheegerG_mono this.le]
  · exact le_rfl

private theorem cheegerMu_telescope (T : Finset ℝ) {x : ℝ} (hx : x ∈ T) :
    ∀ n : ℕ, ∀ y ∈ T, x ≤ y → (T.filter fun τ => x < τ ∧ τ ≤ y).card = n →
      ∑ τ ∈ T.filter (fun τ => x < τ ∧ τ ≤ y), cheegerMu T τ = cheegerG y - cheegerG x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro y hy hxy hn
  rcases hxy.eq_or_lt with rfl | hlt
  · rw [Finset.filter_false_of_mem (fun τ _ h => by linarith [h.1, h.2]), Finset.sum_empty,
      sub_self]
  set F := T.filter (· < y)
  have hF : F.Nonempty := ⟨x, Finset.mem_filter.2 ⟨hx, hlt⟩⟩
  set p := F.max' hF
  have hpF := Finset.mem_filter.1 (Finset.max'_mem F hF)
  have hxp : x ≤ p := Finset.le_max' F x (Finset.mem_filter.2 ⟨hx, hlt⟩)
  have hset : T.filter (fun τ => x < τ ∧ τ ≤ y) =
      insert y (T.filter fun τ => x < τ ∧ τ ≤ p) := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hτ, h1, h2⟩
      rcases h2.eq_or_lt with h | h
      · exact Or.inl h
      · exact Or.inr ⟨hτ, h1, Finset.le_max' F τ (Finset.mem_filter.2 ⟨hτ, h⟩)⟩
    · rintro (rfl | ⟨hτ, h1, h2⟩)
      · exact ⟨hy, hlt, le_rfl⟩
      · exact ⟨hτ, h1, h2.trans hpF.2.le⟩
  have hnot : y ∉ T.filter fun τ => x < τ ∧ τ ≤ p := fun h => by
    have := (Finset.mem_filter.1 h).2.2; linarith [hpF.2]
  have hcard : (T.filter fun τ => x < τ ∧ τ ≤ p).card < n := by
    rw [← hn, hset, Finset.card_insert_of_notMem hnot]; omega
  rw [hset, Finset.sum_insert hnot, ih _ hcard p hpF.1 hxp rfl]
  have hmu : cheegerMu T y = cheegerG y - cheegerG p := by
    unfold cheegerMu
    split_ifs with h
    · rfl
    · exact absurd hF h
  rw [hmu]; ring

private theorem cheegerMu_sum (T : Finset ℝ) {x y : ℝ} (hx : x ∈ T) (hy : y ∈ T) (hxy : x ≤ y) :
    ∑ τ ∈ T.filter (fun τ => x < τ ∧ τ ≤ y), cheegerMu T τ = cheegerG y - cheegerG x :=
  cheegerMu_telescope T hx _ y hy hxy rfl

private theorem cheegerG_sub_le {x y : ℝ} (h : x ≤ y) :
    cheegerG y - cheegerG x ≤ (y - x) * (|x| + |y|) := by
  unfold cheegerG
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hx, abs_of_nonneg hy]; nlinarith
  · rw [abs_of_nonneg hx, abs_of_nonpos hy]; nlinarith
  · rw [abs_of_nonpos hx, abs_of_nonneg hy]; nlinarith
  · rw [abs_of_nonpos hx, abs_of_nonpos hy]; nlinarith

omit [DecidableEq E] in
private theorem sum_mul_weightedDegree (end₁ end₂ : E → V) (w : E → ℝ) (f : V → ℝ) :
    ∑ a, weightedDegree end₁ end₂ w a * f a = ∑ e, w e * (f (end₁ e) + f (end₂ e)) := by
  simp only [weightedDegree, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [mul_assoc, ← Finset.mul_sum, add_mul, Finset.sum_add_distrib, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The thresholds of the sweep: the values of `z` and `0`. -/
private noncomputable def cheegerThresholds (z : V → ℝ) : Finset ℝ :=
  insert 0 (Finset.univ.image z)

omit [DecidableEq E] in
/-- With a centered `z`, the smaller side of a threshold cut is the side away from `0`. -/
private theorem cheeger_min_volume_eq (end₁ end₂ : E → V) {w : E → ℝ} (hw : 0 ≤ w) (z : V → ℝ)
    (hpos : volume end₁ end₂ w (Finset.univ.filter fun a => 0 < z a) ≤
      volume end₁ end₂ w Finset.univ / 2)
    (hneg : volume end₁ end₂ w (Finset.univ.filter fun a => z a < 0) ≤
      volume end₁ end₂ w Finset.univ / 2) (τ : ℝ) :
    min (volume end₁ end₂ w (Finset.univ.filter fun a => z a < τ))
        (volume end₁ end₂ w (Finset.univ \ Finset.univ.filter fun a => z a < τ)) =
      ∑ a, weightedDegree end₁ end₂ w a *
        (if (τ ≤ 0 ∧ z a < τ) ∨ (0 < τ ∧ τ ≤ z a) then 1 else 0) := by
  classical
  set d := weightedDegree end₁ end₂ w
  set S : Finset V := Finset.univ.filter fun a => z a < τ
  have hd0 : ∀ a, 0 ≤ d a := fun a => weightedDegree_nonneg end₁ end₂ hw a
  have hvsplit : volume end₁ end₂ w S + volume end₁ end₂ w (Finset.univ \ S) =
      volume end₁ end₂ w Finset.univ := by
    simp only [volume]
    rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset
      (Finset.subset_univ S)]
  have hvmono : ∀ A B : Finset V, A ⊆ B → volume end₁ end₂ w A ≤ volume end₁ end₂ w B :=
    fun A B h => Finset.sum_le_sum_of_subset_of_nonneg h fun a _ _ => hd0 a
  by_cases hτ : τ ≤ 0
  · have hsub : S ⊆ Finset.univ.filter fun a => z a < 0 := fun a ha => by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢; linarith
    have h1 := hvmono _ _ hsub
    rw [min_eq_left (by linarith)]
    simp only [volume, S, Finset.sum_filter, mul_ite, mul_one, mul_zero]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : z a < τ
    · simp [ha, hτ, d]
    · simp [ha, hτ, d]
  · push Not at hτ
    have hsub : Finset.univ \ S ⊆ Finset.univ.filter fun a => 0 < z a := fun a ha => by
      simp only [S, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      linarith
    have h1 := hvmono _ _ hsub
    rw [min_eq_right (by linarith)]
    simp only [volume, S]
    rw [show Finset.univ \ Finset.univ.filter (fun a => z a < τ) =
        Finset.univ.filter (fun a => ¬ z a < τ) by ext; simp]
    simp only [Finset.sum_filter, mul_ite, mul_one, mul_zero]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : z a < τ
    · simp [ha, not_le.2 hτ, d]
    · simp [ha, not_le.2 hτ, hτ, not_lt.1 ha, d]

omit [DecidableEq E] in
/-- The expected smaller-side volume of the sweep is `zᵀDz`. -/
private theorem cheeger_expected_volume (end₁ end₂ : E → V) (w : E → ℝ) (z : V → ℝ) :
    ∑ τ ∈ cheegerThresholds z, cheegerMu (cheegerThresholds z) τ *
        ∑ a, weightedDegree end₁ end₂ w a *
          (if (τ ≤ 0 ∧ z a < τ) ∨ (0 < τ ∧ τ ≤ z a) then 1 else 0) =
      ∑ a, weightedDegree end₁ end₂ w a * z a ^ 2 := by
  classical
  set T := cheegerThresholds z
  set d := weightedDegree end₁ end₂ w
  have hzT : ∀ a, z a ∈ T := fun a => Finset.mem_insert_of_mem (Finset.mem_image_of_mem z
    (Finset.mem_univ a))
  have h0T : (0 : ℝ) ∈ T := Finset.mem_insert_self _ _
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [mul_ite, mul_one, mul_zero, mul_comm (cheegerMu T _) (d a)]
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  congr 1
  rcases lt_or_ge (z a) 0 with ha | ha
  · rw [show T.filter (fun τ => (τ ≤ 0 ∧ z a < τ) ∨ (0 < τ ∧ τ ≤ z a)) =
        T.filter (fun τ => z a < τ ∧ τ ≤ 0) by
      ext τ; simp only [Finset.mem_filter]
      constructor
      · rintro ⟨h, h' | h'⟩
        · exact ⟨h, h'.2, h'.1⟩
        · exact absurd (h'.1.trans_le h'.2) (by linarith)
      · rintro ⟨h, h'⟩; exact ⟨h, Or.inl ⟨h'.2, h'.1⟩⟩]
    rw [cheegerMu_sum T (hzT a) h0T ha.le]
    simp [cheegerG, abs_of_neg ha]; ring
  · rw [show T.filter (fun τ => (τ ≤ 0 ∧ z a < τ) ∨ (0 < τ ∧ τ ≤ z a)) =
        T.filter (fun τ => 0 < τ ∧ τ ≤ z a) by
      ext τ; simp only [Finset.mem_filter]
      constructor
      · rintro ⟨h, h' | h'⟩
        · exact absurd (h'.2.trans_le h'.1) (by linarith)
        · exact ⟨h, h'⟩
      · rintro ⟨h, h'⟩; exact ⟨h, Or.inr h'⟩]
    rw [cheegerMu_sum T h0T (hzT a) ha]
    simp [cheegerG, abs_of_nonneg ha]; ring

omit [DecidableEq V] [DecidableEq E] in
/-- The expected cut weight of the sweep is at most
`∑_e w_e |z(a) - z(b)| (|z(a)| + |z(b)|)`. -/
private theorem cheeger_expected_cut (end₁ end₂ : E → V) {w : E → ℝ} (hw : 0 ≤ w) (z : V → ℝ) :
    ∑ τ ∈ cheegerThresholds z, cheegerMu (cheegerThresholds z) τ *
        ∑ e ∈ cut end₁ end₂ (Finset.univ.filter fun a => z a < τ), w e ≤
      ∑ e, w e * (|z (end₁ e) - z (end₂ e)| * (|z (end₁ e)| + |z (end₂ e)|)) := by
  classical
  set T := cheegerThresholds z
  set S : ℝ → Finset V := fun τ => Finset.univ.filter fun a => z a < τ
  have hzT : ∀ a, z a ∈ T := fun a => Finset.mem_insert_of_mem (Finset.mem_image_of_mem z
    (Finset.mem_univ a))
  have hcutiff : ∀ τ e, e ∈ cut end₁ end₂ (S τ) ↔ (z (end₁ e) < τ ↔ ¬ z (end₂ e) < τ) := by
    intro τ e
    simp only [cut, S, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h1 : z (end₁ e) < τ <;> by_cases h2 : z (end₂ e) < τ <;> simp [h1, h2]
  have key : ∀ e x y, x ≤ y → (∀ τ, e ∈ cut end₁ end₂ (S τ) ↔ x < τ ∧ τ ≤ y) → x ∈ T →
      y ∈ T → ∑ τ ∈ T, cheegerMu T τ * (if e ∈ cut end₁ end₂ (S τ) then w e else 0) =
        w e * (cheegerG y - cheegerG x) := by
    intro e x y hxy hiff hx hy
    simp only [mul_ite, mul_zero]
    rw [← Finset.sum_filter, Finset.filter_congr (fun τ _ => hiff τ), ← Finset.sum_mul,
      cheegerMu_sum T hx hy hxy]
    ring
  have hEXe : ∀ e, ∑ τ ∈ T, cheegerMu T τ * (if e ∈ cut end₁ end₂ (S τ) then w e else 0) ≤
      w e * (|z (end₁ e) - z (end₂ e)| * (|z (end₁ e)| + |z (end₂ e)|)) := by
    intro e
    rcases le_total (z (end₁ e)) (z (end₂ e)) with h | h
    · rw [key e _ _ h (fun τ => by
        rw [hcutiff]
        constructor
        · intro hh
          by_cases h1 : z (end₁ e) < τ
          · exact ⟨h1, not_lt.1 (hh.1 h1)⟩
          · exfalso
            by_cases h2 : z (end₂ e) < τ
            · exact h1 (lt_of_le_of_lt h h2)
            · exact h1 (hh.2 h2)
        · rintro ⟨h1, h2⟩
          exact ⟨fun _ => not_lt.2 h2, fun _ => h1⟩) (hzT _) (hzT _)]
      refine mul_le_mul_of_nonneg_left ?_ (hw e)
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)]
      exact cheegerG_sub_le h
    · rw [key e _ _ h (fun τ => by
        rw [hcutiff]
        constructor
        · intro hh
          by_cases h2 : z (end₂ e) < τ
          · refine ⟨h2, ?_⟩
            by_contra h1
            push Not at h1
            exact (hh.1 h1) h2
          · exfalso
            by_cases h1 : z (end₁ e) < τ
            · exact h2 (lt_of_le_of_lt h h1)
            · exact h1 (hh.2 h2)
        · rintro ⟨h2, h1⟩
          exact ⟨fun h1' => absurd h1' (not_lt.2 h1), fun _ => absurd h2 ‹_›⟩) (hzT _) (hzT _)]
      refine mul_le_mul_of_nonneg_left ?_ (hw e)
      rw [abs_of_nonneg (sub_nonneg.2 h), add_comm]
      exact cheegerG_sub_le h
  have hX : ∀ τ, ∑ e ∈ cut end₁ end₂ (S τ), w e =
      ∑ e, if e ∈ cut end₁ end₂ (S τ) then w e else 0 := fun τ => by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  simp only [S] at hX hEXe
  simp only [hX, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun e _ => hEXe e

/-- Cauchy–Schwarz for the sweep: `∑_e w_e |z(a) - z(b)| (|z(a)| + |z(b)|) ≤ √(2 zᵀLz / zᵀDz) zᵀDz`
when `zᵀDz > 0` (Spielman, inequality (21.2)). -/
private theorem cheeger_cauchy_schwarz (end₁ end₂ : E → V) {w : E → ℝ} (hw : 0 ≤ w) (z : V → ℝ)
    (hz : 0 < ∑ a, weightedDegree end₁ end₂ w a * z a ^ 2) :
    ∑ e, w e * (|z (end₁ e) - z (end₂ e)| * (|z (end₁ e)| + |z (end₂ e)|)) ≤
      Real.sqrt (2 * (z ⬝ᵥ (laplacian end₁ end₂ w *ᵥ z)) /
          ∑ a, weightedDegree end₁ end₂ w a * z a ^ 2) *
        ∑ a, weightedDegree end₁ end₂ w a * z a ^ 2 := by
  set Q := ∑ a, weightedDegree end₁ end₂ w a * z a ^ 2
  set Lz := z ⬝ᵥ (laplacian end₁ end₂ w *ᵥ z)
  set P := ∑ e, w e * (|z (end₁ e) - z (end₂ e)| * (|z (end₁ e)| + |z (end₂ e)|))
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun e => Real.sqrt (w e) * |z (end₁ e) - z (end₂ e)|)
    (fun e => Real.sqrt (w e) * (|z (end₁ e)| + |z (end₂ e)|))
  have hsq : ∀ e, Real.sqrt (w e) ^ 2 = w e := fun e => Real.sq_sqrt (hw e)
  have hl : ∑ e, (Real.sqrt (w e) * |z (end₁ e) - z (end₂ e)|) ^ 2 = Lz := by
    simp only [Lz, dotProduct_mulVec_laplacian, mul_pow, hsq, sq_abs]
  have hr : ∑ e, (Real.sqrt (w e) * (|z (end₁ e)| + |z (end₂ e)|)) ^ 2 ≤ 2 * Q := by
    have hQ : Q = ∑ e, w e * (z (end₁ e) ^ 2 + z (end₂ e) ^ 2) :=
      sum_mul_weightedDegree end₁ end₂ w (fun a => z a ^ 2)
    rw [hQ, Finset.mul_sum]
    refine Finset.sum_le_sum fun e _ => ?_
    rw [mul_pow, hsq]
    have : (|z (end₁ e)| + |z (end₂ e)|) ^ 2 ≤ 2 * (z (end₁ e) ^ 2 + z (end₂ e) ^ 2) := by
      nlinarith [sq_nonneg (|z (end₁ e)| - |z (end₂ e)|), sq_abs (z (end₁ e)),
        sq_abs (z (end₂ e))]
    have := mul_le_mul_of_nonneg_left this (hw e)
    linarith
  have hP : ∑ e, Real.sqrt (w e) * |z (end₁ e) - z (end₂ e)| *
      (Real.sqrt (w e) * (|z (end₁ e)| + |z (end₂ e)|)) = P := by
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [show Real.sqrt (w e) * |z (end₁ e) - z (end₂ e)| *
        (Real.sqrt (w e) * (|z (end₁ e)| + |z (end₂ e)|)) =
        Real.sqrt (w e) ^ 2 * (|z (end₁ e) - z (end₂ e)| * (|z (end₁ e)| + |z (end₂ e)|)) by
      ring, hsq]
  rw [hP, hl] at h
  have hLz0 : 0 ≤ Lz := by
    rw [← hl]; exact Finset.sum_nonneg fun e _ => sq_nonneg _
  have hCS : P ^ 2 ≤ Lz * (2 * Q) := by nlinarith
  have hcq : Real.sqrt (2 * Lz / Q) * Q = Real.sqrt (Lz * (2 * Q)) := by
    rw [show Lz * (2 * Q) = (2 * Lz / Q) * Q ^ 2 by field_simp, Real.sqrt_mul' _ (sq_nonneg Q),
      Real.sqrt_sq hz.le]
  rw [hcq]
  exact Real.le_sqrt_of_sq_le hCS

/-- Averaging: if `∑ μ X ≤ c ∑ μ Y` with `μ, X, Y ≥ 0` and `∑ μ Y > 0`, some `τ` has `Y τ > 0`
and `X τ ≤ c Y τ`. -/
private theorem exists_le_mul_of_sum_le (T : Finset ℝ) (μ X Y : ℝ → ℝ) {c : ℝ}
    (hμ : ∀ τ, 0 ≤ μ τ) (hX : ∀ τ, 0 ≤ X τ) (hY : ∀ τ, 0 ≤ Y τ)
    (hsum : ∑ τ ∈ T, μ τ * X τ ≤ c * ∑ τ ∈ T, μ τ * Y τ) (hpos : 0 < ∑ τ ∈ T, μ τ * Y τ) :
    ∃ τ, 0 < Y τ ∧ X τ ≤ c * Y τ := by
  by_contra hcon
  push Not at hcon
  have hstrict : ∀ τ ∈ T, c * (μ τ * Y τ) ≤ μ τ * X τ := by
    intro τ _
    rcases (mul_nonneg (hμ τ) (hY τ)).eq_or_lt with h | h
    · rw [← h, mul_zero]; exact mul_nonneg (hμ τ) (hX τ)
    · have hYpos : 0 < Y τ := pos_of_mul_pos_right h (hμ τ)
      have := hcon τ hYpos
      have hμpos : 0 < μ τ := pos_of_mul_pos_left h (hY τ)
      nlinarith
  have hex : ∃ τ ∈ T, 0 < μ τ * Y τ := by
    by_contra hne
    push Not at hne
    have : ∑ τ ∈ T, μ τ * Y τ ≤ 0 := Finset.sum_nonpos hne
    linarith
  obtain ⟨τ₀, hτ₀, hpos₀⟩ := hex
  have hlt : ∑ τ ∈ T, c * (μ τ * Y τ) < ∑ τ ∈ T, μ τ * X τ := by
    refine Finset.sum_lt_sum hstrict ⟨τ₀, hτ₀, ?_⟩
    have hYpos : 0 < Y τ₀ := pos_of_mul_pos_right hpos₀ (hμ τ₀)
    have hμpos : 0 < μ τ₀ := pos_of_mul_pos_left hpos₀ hYpos.le
    have := hcon τ₀ hYpos
    nlinarith
  rw [← Finset.mul_sum] at hlt
  linarith

/-- **Cheeger's inequality, hard direction.** Let `w ≥ 0` be edge weights, `L` the Laplacian and
`d` the weighted degrees. Let `z` be centered with respect to `d` (the vertices where `z > 0`, and
those where `z < 0`, each have volume at most `d(V)/2`) with `zᵀDz = ∑_a d(a) z(a)² > 0`. Then
some threshold set `S_τ = {a : z(a) < τ}` has conductance
`φ(S_τ) = w(∂S_τ) / min(d(S_τ), d(V \ S_τ)) ≤ √(2 zᵀLz / zᵀDz)`; the conductance is stated here
multiplied out, with its denominator positive (D. A. Spielman, *Spectral and Algebraic Graph
Theory*, draft of 2 April 2025, Theorem 21.1.3 with Definition 21.1.1, stated there for positive
weights). The proof is the one of that chapter, after Trevisan: a threshold drawn with density
`2|τ|` gives `E[w(∂S_τ)] ≤ ∑_e w_e |z(a) - z(b)| (|z(a)| + |z(b)|) ≤ √(zᵀLz) √(2 zᵀDz)` by
Cauchy–Schwarz (inequality (21.2)) and `E[min(d(S_τ), d(V \ S_τ))] = zᵀDz` by centering; here the
expectation is a finite sum over the thresholds at the values of `z` and at `0`. -/
theorem exists_threshold_cut_le_sqrt (end₁ end₂ : E → V) {w : E → ℝ} (hw : 0 ≤ w) (z : V → ℝ)
    (hpos : volume end₁ end₂ w (Finset.univ.filter fun a => 0 < z a) ≤
      volume end₁ end₂ w Finset.univ / 2)
    (hneg : volume end₁ end₂ w (Finset.univ.filter fun a => z a < 0) ≤
      volume end₁ end₂ w Finset.univ / 2)
    (hz : 0 < ∑ a, weightedDegree end₁ end₂ w a * z a ^ 2) :
    ∃ τ : ℝ,
      0 < min (volume end₁ end₂ w (Finset.univ.filter fun a => z a < τ))
        (volume end₁ end₂ w (Finset.univ \ Finset.univ.filter fun a => z a < τ)) ∧
      ∑ e ∈ cut end₁ end₂ (Finset.univ.filter fun a => z a < τ), w e ≤
        Real.sqrt (2 * (z ⬝ᵥ (laplacian end₁ end₂ w *ᵥ z)) /
            ∑ a, weightedDegree end₁ end₂ w a * z a ^ 2) *
          min (volume end₁ end₂ w (Finset.univ.filter fun a => z a < τ))
            (volume end₁ end₂ w (Finset.univ \ Finset.univ.filter fun a => z a < τ)) := by
  have hmin := cheeger_min_volume_eq end₁ end₂ hw z hpos hneg
  have hvol0 : ∀ A : Finset V, 0 ≤ volume end₁ end₂ w A := fun A =>
    Finset.sum_nonneg fun a _ => weightedDegree_nonneg end₁ end₂ hw a
  simp only [hmin]
  refine exists_le_mul_of_sum_le (cheegerThresholds z) (cheegerMu (cheegerThresholds z)) _ _
    (cheegerMu_nonneg _) (fun τ => Finset.sum_nonneg fun e _ => hw e)
    (fun τ => by rw [← hmin]; exact le_min (hvol0 _) (hvol0 _)) ?_ ?_
  · rw [cheeger_expected_volume]
    exact (cheeger_expected_cut end₁ end₂ hw z).trans (cheeger_cauchy_schwarz end₁ end₂ hw z hz)
  · rw [cheeger_expected_volume]; exact hz

end EndpointMapMultigraph
