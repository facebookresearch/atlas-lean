/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Comparison of products of `1 - 1 / x` under prefix-product domination

We prove `MetaMathlibExt.prod_one_sub_inv_le_of_prefix_prod_le`: for monotone
`z y : Fin k → ℝ` above `1`, with the prefix products of `z` dominated by those
of `y`, the product of `1 - 1 / z i` is at most the product of `1 - 1 / y i`,
with equality if and only if `z = y`.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*,
INTEGERS 24 (2024), Article A114, Lemma 2.
-/

namespace MetaMathlibExt

namespace prod_one_sub_inv_le_of_prefix_prod_le

-- Abel summation: antitone nonnegative weights and nonnegative partial sums
-- give a nonnegative weighted sum.
private lemma abel_sum_nonneg (n : ℕ) : ∀ (d c : ℕ → ℝ),
    (∀ i j, i ≤ j → j ≤ n → c j ≤ c i) →
    (∀ i ≤ n, 0 ≤ c i) →
    (∀ l ≤ n, 0 ≤ ∑ i ∈ Finset.range l, d i) →
    0 ≤ ∑ i ∈ Finset.range n, c i * d i := by
  induction n with
  | zero =>
    intro d c _ _ _
    simp
  | succ n IH =>
    intro d c hc_anti hc_nonneg hD
    have hIH := IH d (fun i => c i - c n)
      (fun i j hij hjn => sub_le_sub_right (hc_anti i j hij (le_trans hjn (Nat.le_succ n))) _)
      (fun i hin => sub_nonneg.mpr (hc_anti i n hin (Nat.le_succ n)))
      (fun l hl => hD l (le_trans hl (Nat.le_succ n)))
    have hsplit : ∑ i ∈ Finset.range (n + 1), c i * d i
        = ∑ i ∈ Finset.range n, (c i - c n) * d i
          + c n * ∑ i ∈ Finset.range (n + 1), d i := by
      have e1 : ∑ i ∈ Finset.range n, (c i - c n) * d i
          = ∑ i ∈ Finset.range n, c i * d i - c n * ∑ i ∈ Finset.range n, d i := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun i _ => by ring)
      rw [Finset.sum_range_succ (fun i => c i * d i) n, Finset.sum_range_succ d n,
        mul_add, e1]
      ring
    rw [hsplit]
    exact add_nonneg hIH (mul_nonneg (hc_nonneg n (Nat.le_succ n)) (hD (n + 1) le_rfl))

-- Tangent bound for `t ↦ log (1 - e^{-t})` at `log v`, in `u, v` coordinates:
-- the gap is nonnegative and vanishes only at `u = v`.
private lemma tangent_gap (v u : ℝ) (hv : 1 < v) (hu : 1 < u) :
    0 ≤ Real.log (1 - 1 / v) - Real.log (1 - 1 / u) - (Real.log v - Real.log u) / (v - 1)
      ∧ (Real.log (1 - 1 / v) - Real.log (1 - 1 / u) - (Real.log v - Real.log u) / (v - 1) = 0 →
        u = v) := by
  have hv0 : (0:ℝ) < v := zero_lt_one.trans hv
  have hu0 : (0:ℝ) < u := zero_lt_one.trans hu
  have hv1 : (0:ℝ) < v - 1 := sub_pos.mpr hv
  have hderiv : ∀ w > (1:ℝ), HasDerivAt (fun w => v / (v - 1) * Real.log w - Real.log (w - 1))
      (v / (v - 1) * w⁻¹ - 1 / (w - 1)) w := by
    intro w hw
    have hw0 : w ≠ 0 := ne_of_gt (zero_lt_one.trans hw)
    have hw1 : w - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hw)
    have h1 : HasDerivAt (fun w => v / (v - 1) * Real.log w) (v / (v - 1) * w⁻¹) w :=
      (Real.hasDerivAt_log hw0).const_mul _
    have h2 : HasDerivAt (fun w => Real.log (w - 1)) (1 / (w - 1)) w :=
      ((hasDerivAt_id w).sub_const 1).log hw1
    exact h1.sub h2
  have hder : ∀ w > (1:ℝ), deriv (fun w => v / (v - 1) * Real.log w - Real.log (w - 1)) w
      = (w - v) / ((v - 1) * w * (w - 1)) := by
    intro w hw
    rw [(hderiv w hw).deriv]
    have hv1ne : (v:ℝ) - 1 ≠ 0 := ne_of_gt hv1
    have hw0 : (w:ℝ) ≠ 0 := ne_of_gt (zero_lt_one.trans hw)
    have hw1 : (w:ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hw)
    field_simp
    ring
  have hcont : ∀ D : Set ℝ, D ⊆ Set.Ioi 1 →
      ContinuousOn (fun w => v / (v - 1) * Real.log w - Real.log (w - 1)) D := by
    intro D hD
    have hdiff : DifferentiableOn ℝ (fun w => v / (v - 1) * Real.log w - Real.log (w - 1)) D :=
      fun w hw => ((hderiv w (hD hw)).differentiableAt).differentiableWithinAt
    exact hdiff.continuousOn
  have hAnti : StrictAntiOn (fun w => v / (v - 1) * Real.log w - Real.log (w - 1))
      (Set.Ioc 1 v) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioc 1 v) (hcont _ Set.Ioc_subset_Ioi_self)
      (fun x hx => ?_)
    rw [interior_Ioc] at hx
    rw [hder x (Set.mem_Ioo.mp hx).1]
    have hxv : x - v < 0 := sub_neg.mpr (Set.mem_Ioo.mp hx).2
    have hpos : (0:ℝ) < (v - 1) * x * (x - 1) :=
      mul_pos (mul_pos hv1 (zero_lt_one.trans (Set.mem_Ioo.mp hx).1))
        (sub_pos.mpr (Set.mem_Ioo.mp hx).1)
    exact div_neg_of_neg_of_pos hxv hpos
  have hMono : StrictMonoOn (fun w => v / (v - 1) * Real.log w - Real.log (w - 1)) (Set.Ici v) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici v) (hcont _ ?_) (fun x hx => ?_)
    · intro x hx
      exact lt_of_lt_of_le hv (Set.mem_Ici.mp hx)
    · rw [interior_Ici] at hx
      rw [hder x (lt_trans hv (Set.mem_Ioi.mp hx))]
      have hxv : (0:ℝ) < x - v := sub_pos.mpr (Set.mem_Ioi.mp hx)
      have h1x : (1:ℝ) < x := lt_trans hv (Set.mem_Ioi.mp hx)
      have hpos : (0:ℝ) < (v - 1) * x * (x - 1) :=
        mul_pos (mul_pos hv1 (zero_lt_one.trans h1x)) (sub_pos.mpr h1x)
      exact div_pos hxv hpos
  have hmin : (v / (v - 1) * Real.log v - Real.log (v - 1))
      ≤ (v / (v - 1) * Real.log u - Real.log (u - 1))
      ∧ ((v / (v - 1) * Real.log u - Real.log (u - 1))
        = (v / (v - 1) * Real.log v - Real.log (v - 1)) → u = v) := by
    rcases lt_trichotomy u v with h | h | h
    · have hlt := hAnti (Set.mem_Ioc.mpr ⟨hu, le_of_lt h⟩) (Set.mem_Ioc.mpr ⟨hv, le_rfl⟩) h
      exact ⟨le_of_lt hlt, fun heq => absurd heq (ne_of_gt hlt)⟩
    · subst h
      exact ⟨le_rfl, fun _ => rfl⟩
    · have hlt := hMono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (le_of_lt h)) h
      exact ⟨le_of_lt hlt, fun heq => absurd heq (ne_of_gt hlt)⟩
  have hgap : Real.log (1 - 1 / v) - Real.log (1 - 1 / u) - (Real.log v - Real.log u) / (v - 1)
      = (v / (v - 1) * Real.log u - Real.log (u - 1))
        - (v / (v - 1) * Real.log v - Real.log (v - 1)) := by
    have hv0ne : (v:ℝ) ≠ 0 := ne_of_gt hv0
    have hu0ne : (u:ℝ) ≠ 0 := ne_of_gt hu0
    have hv1ne : (v:ℝ) - 1 ≠ 0 := ne_of_gt hv1
    have hu1ne : (u:ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hu)
    have e1 : (1:ℝ) - 1 / v = (v - 1) / v := by
      rw [sub_div, div_self hv0ne]
    have e2 : (1:ℝ) - 1 / u = (u - 1) / u := by
      rw [sub_div, div_self hu0ne]
    rw [e1, e2, Real.log_div hv1ne hv0ne, Real.log_div hu1ne hu0ne]
    field_simp
    ring
  rw [hgap]
  exact ⟨sub_nonneg.mpr hmin.1, fun h => hmin.2 (sub_eq_zero.mp h)⟩

-- Products over an initial segment of `Fin k` agree with products over `range l`.
private lemma prod_filter_eq_prod_range {k : ℕ} (g : Fin k → ℝ) (G : ℕ → ℝ)
    (hG : ∀ i (h : i < k), G i = g ⟨i, h⟩) (l : ℕ) (hl : l ≤ k) :
    ∏ i ∈ Finset.univ.filter (fun i : Fin k => (i : ℕ) < l), g i
      = ∏ i ∈ Finset.range l, G i := by
  refine Finset.prod_bij (fun i _ => (i : ℕ)) ?_ ?_ ?_ ?_
  · intro a ha
    show (a : ℕ) ∈ Finset.range l
    exact Finset.mem_range.mpr (Finset.mem_filter.mp ha).2
  · intro a₁ _ a₂ _ h
    have h' : (a₁ : ℕ) = a₂ := h
    exact Fin.ext h'
  · intro b hb
    have hb' : b < l := Finset.mem_range.mp hb
    have hbk : b < k := lt_of_lt_of_le hb' hl
    refine ⟨⟨b, hbk⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb'⟩, rfl⟩
  · intro a ha
    show g a = G (a : ℕ)
    have hak : (a : ℕ) < k :=
      lt_of_lt_of_le (Finset.mem_filter.mp ha).2 hl
    rw [hG _ hak, Fin.eta a hak]

-- Range version of the main inequality. Only the monotonicity of `yy` is used
-- (for the weights); `zz`'s is kept for a symmetric interface.
private theorem prod_range_h_le (k : ℕ) (zz yy : ℕ → ℝ)
    (_hzz : ∀ i j, i ≤ j → j < k → zz i ≤ zz j)
    (hyy : ∀ i j, i ≤ j → j < k → yy i ≤ yy j)
    (hzz1 : ∀ i < k, 1 < zz i) (hyy1 : ∀ i < k, 1 < yy i)
    (hprefix : ∀ l ≤ k, ∏ i ∈ Finset.range l, zz i ≤ ∏ i ∈ Finset.range l, yy i) :
    ∏ i ∈ Finset.range k, (1 - 1 / zz i) ≤ ∏ i ∈ Finset.range k, (1 - 1 / yy i) ∧
      (∏ i ∈ Finset.range k, (1 - 1 / zz i) = ∏ i ∈ Finset.range k, (1 - 1 / yy i)
        ↔ ∀ i < k, zz i = yy i) := by
  have hzz_pos : ∀ i < k, (0:ℝ) < zz i := fun i hi => zero_lt_one.trans (hzz1 i hi)
  have hyy_pos : ∀ i < k, (0:ℝ) < yy i := fun i hi => zero_lt_one.trans (hyy1 i hi)
  have hzz_hpos : ∀ i < k, (0:ℝ) < 1 - 1 / zz i := by
    intro i hi
    have h : (1:ℝ) / zz i < 1 := by
      rw [div_lt_one (hzz_pos i hi)]
      exact hzz1 i hi
    exact sub_pos.mpr h
  have hyy_hpos : ∀ i < k, (0:ℝ) < 1 - 1 / yy i := by
    intro i hi
    have h : (1:ℝ) / yy i < 1 := by
      rw [div_lt_one (hyy_pos i hi)]
      exact hyy1 i hi
    exact sub_pos.mpr h
  set d : ℕ → ℝ := fun i => Real.log (yy i) - Real.log (zz i) with hd
  set c : ℕ → ℝ := fun i => if i < k then (yy i - 1)⁻¹ else 0 with hc
  have hD : ∀ l ≤ k, 0 ≤ ∑ i ∈ Finset.range l, d i := by
    intro l hl
    have hZ : (0:ℝ) < ∏ i ∈ Finset.range l, zz i := by
      apply Finset.prod_pos
      intro i hi
      exact hzz_pos i (lt_of_lt_of_le (Finset.mem_range.mp hi) hl)
    have hY : (0:ℝ) < ∏ i ∈ Finset.range l, yy i := by
      apply Finset.prod_pos
      intro i hi
      exact hyy_pos i (lt_of_lt_of_le (Finset.mem_range.mp hi) hl)
    have hneZ : ∀ i ∈ Finset.range l, zz i ≠ 0 :=
      fun i hi => ne_of_gt (hzz_pos i (lt_of_lt_of_le (Finset.mem_range.mp hi) hl))
    have hneY : ∀ i ∈ Finset.range l, yy i ≠ 0 :=
      fun i hi => ne_of_gt (hyy_pos i (lt_of_lt_of_le (Finset.mem_range.mp hi) hl))
    have hsum : ∑ i ∈ Finset.range l, d i
        = Real.log (∏ i ∈ Finset.range l, yy i) - Real.log (∏ i ∈ Finset.range l, zz i) := by
      simp only [hd, Finset.sum_sub_distrib]
      rw [← Real.log_prod hneY, ← Real.log_prod hneZ]
    rw [hsum, ← Real.log_div (ne_of_gt hY) (ne_of_gt hZ)]
    apply Real.log_nonneg
    rw [one_le_div hZ]
    exact hprefix l hl
  have hc_anti : ∀ i j, i ≤ j → j ≤ k → c j ≤ c i := by
    intro i j hij hjk
    by_cases hj : j < k
    · have hi : i < k := lt_of_le_of_lt hij hj
      simp only [hc]
      rw [ite_eq_left hj, ite_eq_left hi,
        inv_le_inv₀ (sub_pos.mpr (hyy1 j hj)) (sub_pos.mpr (hyy1 i hi))]
      exact sub_le_sub_right (hyy i j hij hj) _
    · have hj0 : c j = 0 := by
        simp only [hc]
        rw [ite_eq_right hj]
      by_cases hi : i < k
      · have hi0 : c i = (yy i - 1)⁻¹ := by
          simp only [hc]
          rw [ite_eq_left hi]
        rw [hj0, hi0]
        exact inv_nonneg.mpr (le_of_lt (sub_pos.mpr (hyy1 i hi)))
      · have hi0 : c i = 0 := by
          simp only [hc]
          rw [ite_eq_right hi]
        exact le_of_eq (hj0.trans hi0.symm)
  have hc_nonneg : ∀ i ≤ k, 0 ≤ c i := by
    intro i hik
    by_cases hi : i < k
    · have hi0 : c i = (yy i - 1)⁻¹ := by
        simp only [hc]
        rw [ite_eq_left hi]
      rw [hi0]
      exact inv_nonneg.mpr (le_of_lt (sub_pos.mpr (hyy1 i hi)))
    · have hi0 : c i = 0 := by
        simp only [hc]
        rw [ite_eq_right hi]
      exact le_of_eq hi0.symm
  have hA : 0 ≤ ∑ i ∈ Finset.range k, c i * d i := abel_sum_nonneg k d c hc_anti hc_nonneg hD
  have hcd : ∀ i < k, c i * d i = (Real.log (yy i) - Real.log (zz i)) / (yy i - 1) := by
    intro i hi
    simp only [hc, hd]
    rw [ite_eq_left hi, div_eq_inv_mul]
  have hgap : ∀ i ∈ Finset.range k,
      0 ≤ (Real.log (1 - 1 / yy i) - Real.log (1 - 1 / zz i)) - c i * d i := by
    intro i hi
    have hi' : i < k := Finset.mem_range.mp hi
    rw [hcd i hi']
    exact (tangent_gap (yy i) (zz i) (hyy1 i hi') (hzz1 i hi')).1
  have hG : 0 ≤ ∑ i ∈ Finset.range k,
      ((Real.log (1 - 1 / yy i) - Real.log (1 - 1 / zz i)) - c i * d i) :=
    Finset.sum_nonneg hgap
  have hTAG : ∑ i ∈ Finset.range k, (Real.log (1 - 1 / yy i) - Real.log (1 - 1 / zz i))
      = ∑ i ∈ Finset.range k, c i * d i
        + ∑ i ∈ Finset.range k,
          ((Real.log (1 - 1 / yy i) - Real.log (1 - 1 / zz i)) - c i * d i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => by ring)
  have hlogsum : ∑ i ∈ Finset.range k, (Real.log (1 - 1 / yy i) - Real.log (1 - 1 / zz i))
      = Real.log (∏ i ∈ Finset.range k, (1 - 1 / yy i))
        - Real.log (∏ i ∈ Finset.range k, (1 - 1 / zz i)) := by
    have hneY : ∀ i ∈ Finset.range k, (1:ℝ) - 1 / yy i ≠ 0 :=
      fun i hi => ne_of_gt (hyy_hpos i (Finset.mem_range.mp hi))
    have hneZ : ∀ i ∈ Finset.range k, (1:ℝ) - 1 / zz i ≠ 0 :=
      fun i hi => ne_of_gt (hzz_hpos i (Finset.mem_range.mp hi))
    simp only [Finset.sum_sub_distrib]
    rw [← Real.log_prod hneY, ← Real.log_prod hneZ]
  have hPZ : (0:ℝ) < ∏ i ∈ Finset.range k, (1 - 1 / zz i) := by
    apply Finset.prod_pos
    intro i hi
    exact hzz_hpos i (Finset.mem_range.mp hi)
  have hPY : (0:ℝ) < ∏ i ∈ Finset.range k, (1 - 1 / yy i) := by
    apply Finset.prod_pos
    intro i hi
    exact hyy_hpos i (Finset.mem_range.mp hi)
  have hT : (0:ℝ) ≤ ∑ i ∈ Finset.range k, (Real.log (1 - 1 / yy i) - Real.log (1 - 1 / zz i)) := by
    rw [hTAG]
    exact add_nonneg hA hG
  have hle : ∏ i ∈ Finset.range k, (1 - 1 / zz i) ≤ ∏ i ∈ Finset.range k, (1 - 1 / yy i) := by
    rw [← Real.log_le_log_iff hPZ hPY, ← sub_nonneg, ← hlogsum]
    exact hT
  refine ⟨hle, ?_, ?_⟩
  · intro heq i hi
    have hlog : Real.log (∏ i ∈ Finset.range k, (1 - 1 / zz i))
        = Real.log (∏ i ∈ Finset.range k, (1 - 1 / yy i)) := congrArg _ heq
    have hT0 : ∑ i ∈ Finset.range k, (Real.log (1 - 1 / yy i) - Real.log (1 - 1 / zz i)) = 0 := by
      rw [hlogsum, hlog, sub_self]
    have hAG0 : ∑ i ∈ Finset.range k, c i * d i
        + ∑ i ∈ Finset.range k,
          ((Real.log (1 - 1 / yy i) - Real.log (1 - 1 / zz i)) - c i * d i) = 0 :=
      hTAG.symm.trans hT0
    obtain ⟨-, hG0⟩ := (add_eq_zero_iff_of_nonneg hA hG).mp hAG0
    have each := (Finset.sum_eq_zero_iff_of_nonneg hgap).mp hG0 i (Finset.mem_range.mpr hi)
    rw [hcd i hi] at each
    exact (tangent_gap (yy i) (zz i) (hyy1 i hi) (hzz1 i hi)).2 each
  · intro h
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have hi' := Finset.mem_range.mp hi
    rw [h i hi']

end prod_one_sub_inv_le_of_prefix_prod_le

open prod_one_sub_inv_le_of_prefix_prod_le in
/-- **Comparison of products of $1 - 1/x$ under prefix-product domination.** Let $k \ge 0$ and let
$z_1 \le \dots \le z_k$ and $y_1 \le \dots \le y_k$ be real numbers, all greater than $1$, such
that $z_1 \cdots z_l \le y_1 \cdots y_l$ for every $l$ with $0 \le l \le k$ (for $l = 0$ both sides
are the empty product). Then $\prod_{i=1}^k (1 - 1/z_i) \le \prod_{i=1}^k (1 - 1/y_i)$, with
equality if and only if $z_i = y_i$ for all $i$.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 2 (`integers-2024-A114-lem-2`), citing its reference [4]. -/
public theorem prod_one_sub_inv_le_of_prefix_prod_le (k : ℕ) (z y : Fin k → ℝ)
    (hz : Monotone z) (hy : Monotone y) (hz1 : ∀ i, 1 < z i) (hy1 : ∀ i, 1 < y i)
    (hprefix : ∀ l ≤ k, ∏ i ∈ Finset.univ.filter (fun i : Fin k => (i : ℕ) < l), z i ≤
      ∏ i ∈ Finset.univ.filter (fun i : Fin k => (i : ℕ) < l), y i) :
    ∏ i, (1 - 1 / z i) ≤ ∏ i, (1 - 1 / y i) ∧
      (∏ i, (1 - 1 / z i) = ∏ i, (1 - 1 / y i) ↔ z = y) := by
  set Z : ℕ → ℝ := fun i => if h : i < k then z ⟨i, h⟩ else 1 with hZdef
  set Y : ℕ → ℝ := fun i => if h : i < k then y ⟨i, h⟩ else 1 with hYdef
  have hZ : ∀ i (h : i < k), Z i = z ⟨i, h⟩ := by
    intro i h
    simp only [hZdef]
    rw [dite_eq_left h]
  have hY : ∀ i (h : i < k), Y i = y ⟨i, h⟩ := by
    intro i h
    simp only [hYdef]
    rw [dite_eq_left h]
  have hmonoZ : ∀ i j, i ≤ j → j < k → Z i ≤ Z j := by
    intro i j hij hjk
    have hi : i < k := lt_of_le_of_lt hij hjk
    rw [hZ i hi, hZ j hjk]
    exact hz (Fin.mk_le_mk.mpr hij)
  have hmonoY : ∀ i j, i ≤ j → j < k → Y i ≤ Y j := by
    intro i j hij hjk
    have hi : i < k := lt_of_le_of_lt hij hjk
    rw [hY i hi, hY j hjk]
    exact hy (Fin.mk_le_mk.mpr hij)
  have h1Z : ∀ i < k, 1 < Z i := by
    intro i hi
    rw [hZ i hi]
    exact hz1 _
  have h1Y : ∀ i < k, 1 < Y i := by
    intro i hi
    rw [hY i hi]
    exact hy1 _
  have hpre : ∀ l ≤ k, ∏ i ∈ Finset.range l, Z i ≤ ∏ i ∈ Finset.range l, Y i := by
    intro l hl
    rw [← prod_filter_eq_prod_range z Z hZ l hl, ← prod_filter_eq_prod_range y Y hY l hl]
    exact hprefix l hl
  have hmainZ : ∏ i, (1 - 1 / z i) = ∏ i ∈ Finset.range k, (1 - 1 / Z i) := by
    have hfil : Finset.univ.filter (fun i : Fin k => (i : ℕ) < k) = Finset.univ :=
      Finset.filter_true_of_mem (fun i _ => Fin.isLt i)
    rw [← hfil]
    exact prod_filter_eq_prod_range (fun i => 1 - 1 / z i) (fun i => 1 - 1 / Z i)
      (fun i h => by show 1 - 1 / Z i = 1 - 1 / z ⟨i, h⟩; rw [hZ i h]) k le_rfl
  have hmainY : ∏ i, (1 - 1 / y i) = ∏ i ∈ Finset.range k, (1 - 1 / Y i) := by
    have hfil : Finset.univ.filter (fun i : Fin k => (i : ℕ) < k) = Finset.univ :=
      Finset.filter_true_of_mem (fun i _ => Fin.isLt i)
    rw [← hfil]
    exact prod_filter_eq_prod_range (fun i => 1 - 1 / y i) (fun i => 1 - 1 / Y i)
      (fun i h => by show 1 - 1 / Y i = 1 - 1 / y ⟨i, h⟩; rw [hY i h]) k le_rfl
  obtain ⟨hle, heq⟩ := prod_range_h_le k Z Y hmonoZ hmonoY h1Z h1Y hpre
  refine ⟨?_, ?_⟩
  · rw [hmainZ, hmainY]
    exact hle
  · rw [hmainZ, hmainY, heq]
    constructor
    · intro h
      funext j
      have hi : (j : ℕ) < k := Fin.isLt j
      have h2 := h _ hi
      rw [hZ _ hi, hY _ hi, Fin.eta j hi] at h2
      exact h2
    · intro h i hi
      rw [hZ i hi, hY i hi, h]

end MetaMathlibExt
