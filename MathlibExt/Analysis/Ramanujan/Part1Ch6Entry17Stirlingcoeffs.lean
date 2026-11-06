/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

@[expose] public section

open scoped BigOperators
open Filter Finset Topology

-- Supergeometric factor: (i+1) * A^i * X^(i*(i+1)) is summable when
-- 0 ≤ A, 0 ≤ X ≤ 1, and A < 1 in the boundary case X = 1.
private theorem supergeom_summable (A X : ℝ) (hA0 : 0 ≤ A) (hX0 : 0 ≤ X)
    (hX1 : X ≤ 1) (hlt : X = 1 → A < 1) :
    Summable fun i : ℕ => ((i : ℝ) + 1) * A ^ i * X ^ (i * (i + 1)) := by
  by_cases hXeq : X = 1
  · subst hXeq
    have hA : ‖A‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hA0]; exact hlt rfl
    have g1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hA
    have g0 := summable_geometric_of_norm_lt_one hA
    have hcongr : (fun i : ℕ => ((i : ℝ) + 1) * A ^ i * (1 : ℝ) ^ (i * (i + 1)))
        = (fun i : ℕ => (i : ℝ) ^ 1 * A ^ i + A ^ i) := by
      funext i; simp [one_pow, pow_one]; ring
    rw [hcongr]
    exact g1.add g0
  · have hXlt : X < 1 := lt_of_le_of_ne hX1 hXeq
    have hX2 : ‖X ^ 2‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hX0 2)]
      exact pow_lt_one₀ hX0 hXlt two_ne_zero
    have gpow := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hX2
    -- ratio factor c i → 0
    set c : ℕ → ℝ := fun i => ((i : ℝ) + 2) / ((i : ℝ) + 1) * A * X ^ (2 * (i + 1)) with hcdef
    have hc0 : ∀ i : ℕ, 0 ≤ c i := by
      intro i
      apply mul_nonneg
      · apply mul_nonneg
        · apply div_nonneg
          · have := Nat.cast_nonneg (α := ℝ) i; linarith
          · have := Nat.cast_nonneg (α := ℝ) i; linarith
        · exact hA0
      · exact pow_nonneg hX0 _
    have hc_le : ∀ i : ℕ, c i ≤ 2 * A * (X ^ 2) ^ (i + 1) := by
      intro i
      have hfrac : ((i : ℝ) + 2) / ((i : ℝ) + 1) ≤ 2 := by
        have hpos : (0 : ℝ) < (i : ℝ) + 1 := by
          have := Nat.cast_nonneg (α := ℝ) i; linarith
        rw [div_le_iff₀ hpos]
        have := Nat.cast_nonneg (α := ℝ) i; linarith
      have hXeq2 : X ^ (2 * (i + 1)) = (X ^ 2) ^ (i + 1) := by rw [pow_mul]
      have hnn : 0 ≤ A * (X ^ 2) ^ (i + 1) :=
        mul_nonneg hA0 (pow_nonneg (pow_nonneg hX0 2) _)
      calc c i = ((i : ℝ) + 2) / ((i : ℝ) + 1) * (A * (X ^ 2) ^ (i + 1)) := by
            simp only [hcdef]; rw [hXeq2]; ring
        _ ≤ 2 * (A * (X ^ 2) ^ (i + 1)) :=
            mul_le_mul_of_nonneg_right hfrac hnn
        _ = 2 * A * (X ^ 2) ^ (i + 1) := by ring
    have hlim : Tendsto (fun i : ℕ => 2 * A * (X ^ 2) ^ (i + 1)) atTop (𝓝 0) := by
      have hbase : Tendsto (fun i : ℕ => (2 * A * X ^ 2) * (X ^ 2) ^ i) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds.mul gpow)
      refine hbase.congr (fun i => ?_)
      rw [pow_succ']; ring
    have hc_tend : Tendsto c atTop (𝓝 0) :=
      squeeze_zero hc0 (fun i => hc_le i) hlim
    -- step equation u (i+1) = c i * u i
    have hstep : ∀ i : ℕ,
        (((i + 1 : ℕ) : ℝ) + 1) * A ^ (i + 1) * X ^ ((i + 1) * (i + 1 + 1))
          = c i * (((i : ℝ) + 1) * A ^ i * X ^ (i * (i + 1))) := by
      intro i
      have eA : A ^ (i + 1) = A ^ i * A := pow_succ A i
      have eX : X ^ ((i + 1) * (i + 1 + 1)) = X ^ (i * (i + 1)) * X ^ (2 * (i + 1)) := by
        rw [← pow_add]; congr 1; ring
      have ecast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
      have hpos : (0 : ℝ) < (i : ℝ) + 1 := by
        have := Nat.cast_nonneg (α := ℝ) i; linarith
      rw [ecast, eA, eX]
      simp only [hcdef]
      field_simp
      ring
    have hnn : ∀ i : ℕ, 0 ≤ ((i : ℝ) + 1) * A ^ i * X ^ (i * (i + 1)) := by
      intro i
      apply mul_nonneg
      · apply mul_nonneg
        · have := Nat.cast_nonneg (α := ℝ) i; linarith
        · exact pow_nonneg hA0 _
      · exact pow_nonneg hX0 _
    apply summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num)
    have hev : ∀ᶠ i in atTop, c i < 1 / 2 :=
      hc_tend.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    refine hev.mono (fun i hi => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hnn (i + 1)),
      abs_of_nonneg (hnn i), hstep i]
    exact mul_le_mul_of_nonneg_right (le_of_lt hi) (hnn i)

-- Plain supergeometric factor, derived from the linear-weighted version.
private theorem supergeom_summable_plain (A X : ℝ) (hA0 : 0 ≤ A) (hX0 : 0 ≤ X)
    (hX1 : X ≤ 1) (hlt : X = 1 → A < 1) :
    Summable fun i : ℕ => A ^ i * X ^ (i * (i + 1)) := by
  have hsup := supergeom_summable A X hA0 hX0 hX1 hlt
  apply Summable.of_norm_bounded hsup
  intro i
  have hnn : 0 ≤ A ^ i * X ^ (i * (i + 1)) :=
    mul_nonneg (pow_nonneg hA0 _) (pow_nonneg hX0 _)
  have h1i : (1 : ℝ) ≤ (i : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) i; linarith
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  calc A ^ i * X ^ (i * (i + 1)) = 1 * (A ^ i * X ^ (i * (i + 1))) := (one_mul _).symm
    _ ≤ ((i : ℝ) + 1) * (A ^ i * X ^ (i * (i + 1))) :=
        mul_le_mul_of_nonneg_right h1i hnn
    _ = ((i : ℝ) + 1) * A ^ i * X ^ (i * (i + 1)) := by ring

-- Tail of a geometric series.
private theorem geom_tail_summable (r : ℝ) (hr : ‖r‖ < 1) :
    Summable fun j : ℕ => r ^ (j + 1) := by
  have g := summable_geometric_of_norm_lt_one hr (R := ℝ)
  exact (g.mul_right r).congr (fun j => (pow_succ r j).symm)

-- Linear-weighted tail of a geometric series.
private theorem geom_weighted_summable (r : ℝ) (hr : ‖r‖ < 1) :
    Summable fun j : ℕ => ((j : ℝ) + 1) * r ^ (j + 1) := by
  have g1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr
  have g0 := summable_geometric_of_norm_lt_one hr (R := ℝ)
  have hcongr : (fun j : ℕ => ((j : ℝ) + 1) * r ^ (j + 1))
      = (fun j : ℕ => r * ((j : ℝ) ^ 1 * r ^ j) + r * r ^ j) := by
    funext j; simp only [pow_succ]; ring
  rw [hcongr]
  exact (g1.mul_left r).add (g0.mul_left r)

-- Value of a geometric row sum.
private theorem row_geom_value (C r : ℝ) (hr : ‖r‖ < 1) :
    ∑' j : ℕ, C * r ^ j = C / (1 - r) := by
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hr, div_eq_mul_inv]

-- Value of a linear-weighted geometric row sum.
private theorem row_weighted_value (C r : ℝ) (hr : ‖r‖ < 1) :
    ∑' j : ℕ, ((j : ℝ) + 1) * (C * r ^ j) = C / (1 - r) ^ 2 := by
  have hs := (hasSum_coe_mul_geometric_of_norm_lt_one hr).summable
  have g0 := summable_geometric_of_norm_lt_one hr (R := ℝ)
  have hr1 : r ≠ 1 := by
    intro h; rw [h, norm_one] at hr; exact lt_irrefl 1 hr
  have h1r : (1 : ℝ) - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr1)
  have hcongr : (fun j : ℕ => ((j : ℝ) + 1) * (C * r ^ j))
      = (fun j : ℕ => C * ((j : ℝ) * r ^ j) + C * (r ^ j)) := by
    funext j; ring
  rw [hcongr, Summable.tsum_add (hs.mul_left C) (g0.mul_left C),
    tsum_mul_left, tsum_mul_left,
    (hasSum_coe_mul_geometric_of_norm_lt_one hr).tsum_eq,
    tsum_geometric_of_norm_lt_one hr]
  field_simp
  ring

-- Factorization of the double-series summand along rows.
private theorem G_row_factor (m nu x : ℝ) (k j : ℕ) :
    m ^ k * nu ^ (k + j + 1) * x ^ (k * (k + j + 1))
      = (m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) * (nu * x ^ k) ^ j := by
  have e1 : k + j + 1 = (k + 1) + j := by omega
  have e2 : k * (k + j + 1) = k * (k + 1) + k * j := by ring
  rw [e2, e1, mul_pow, ← pow_mul, pow_add, pow_add]
  ring

-- The second-series numerator is m times the row numerator.
private theorem second_num_factor (m nu x : ℝ) (k : ℕ) :
    (m * nu * x ^ k) ^ (k + 1) = m * (m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) := by
  have e : (m * nu * x ^ k) ^ (k + 1)
      = m ^ (k + 1) * nu ^ (k + 1) * (x ^ k) ^ (k + 1) := by
    rw [mul_pow, mul_pow]
  rw [e, ← pow_mul, pow_succ m k]
  ring

-- Pieces for the first-term algebra.
private theorem first_alg_ts (m nu x : ℝ) (k : ℕ) :
    m * nu * x ^ (2 * k) = (m * x ^ k) * (nu * x ^ k) := by
  have ex : x ^ (2 * k) = x ^ k * x ^ k := by
    rw [← pow_add]; congr 1; omega
  rw [ex]; ring

private theorem first_alg_tkq (m nu x : ℝ) (k : ℕ) :
    (m * nu * x ^ k) ^ k = (m * x ^ k) ^ k * nu ^ k := by
  rw [show m * nu * x ^ k = (m * x ^ k) * nu from by ring, mul_pow]

-- Expanded norm bound for the double-series summand.
private theorem G_norm_bound (m nu x : ℝ) (_hx : |x| ≤ 1) (i j : ℕ) :
    ‖m ^ i * nu ^ (i + j + 1) * x ^ (i * (i + j + 1))‖
      ≤ (|m * nu| ^ i * |x| ^ (i * (i + 1))) * (|nu| ^ (j + 1) * |x| ^ (i * j)) := by
  have e2 : i * (i + j + 1) = i * (i + 1) + i * j := by ring
  have e1 : i + j + 1 = i + (j + 1) := by omega
  have eA : |m * nu| ^ i = |m| ^ i * |nu| ^ i := by rw [abs_mul, mul_pow]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_pow, abs_pow, e2, e1,
    pow_add, pow_add, eA]
  exact le_of_eq (by ring)

-- The double series G is absolutely summable.
private theorem G_summable (m nu x : ℝ) (hx : |x| ≤ 1) (hnu : |nu| < 1)
    (hboundary : |x| = 1 → |m * nu| < 1) :
    Summable fun p : ℕ × ℕ =>
      m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)) := by
  have hU := supergeom_summable_plain |m * nu| |x| (abs_nonneg _) (abs_nonneg _) hx
    (fun h => hboundary h)
  have hV : Summable fun j : ℕ => |nu| ^ (j + 1) :=
    geom_tail_summable |nu| (by rw [Real.norm_eq_abs, abs_abs]; exact hnu)
  have hUV := hU.mul_of_nonneg hV
    (fun i => mul_nonneg (pow_nonneg (abs_nonneg _) _) (pow_nonneg (abs_nonneg _) _))
    (fun j => pow_nonneg (abs_nonneg _) _)
  apply Summable.of_norm_bounded hUV
  intro ⟨i, j⟩
  have hXij : |x| ^ (i * j) ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
  have hnn : 0 ≤ |m * nu| ^ i * |x| ^ (i * (i + 1)) := by positivity
  have hnn2 : 0 ≤ |nu| ^ (j + 1) := pow_nonneg (abs_nonneg _) _
  calc ‖m ^ i * nu ^ (i + j + 1) * x ^ (i * (i + j + 1))‖
        ≤ (|m * nu| ^ i * |x| ^ (i * (i + 1))) * (|nu| ^ (j + 1) * |x| ^ (i * j)) :=
          G_norm_bound m nu x hx i j
      _ ≤ (|m * nu| ^ i * |x| ^ (i * (i + 1))) * (|nu| ^ (j + 1) * 1) := by
          apply mul_le_mul_of_nonneg_left _ hnn
          exact mul_le_mul_of_nonneg_left hXij hnn2
      _ = |m * nu| ^ i * |x| ^ (i * (i + 1)) * |nu| ^ (j + 1) := by ring

-- The (i+1)-weighted double series is summable.
private theorem Gi_summable (m nu x : ℝ) (hx : |x| ≤ 1) (hnu : |nu| < 1)
    (hboundary : |x| = 1 → |m * nu| < 1) :
    Summable fun p : ℕ × ℕ => ((p.1 : ℝ) + 1) *
      (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))) := by
  have hU := supergeom_summable |m * nu| |x| (abs_nonneg _) (abs_nonneg _) hx
    (fun h => hboundary h)
  have hV : Summable fun j : ℕ => |nu| ^ (j + 1) :=
    geom_tail_summable |nu| (by rw [Real.norm_eq_abs, abs_abs]; exact hnu)
  have hnnU : ∀ i : ℕ, 0 ≤ ((i : ℝ) + 1) * |m * nu| ^ i * |x| ^ (i * (i + 1)) := by
    intro i
    apply mul_nonneg
    · apply mul_nonneg
      · have := Nat.cast_nonneg (α := ℝ) i; linarith
      · exact pow_nonneg (abs_nonneg _) _
    · exact pow_nonneg (abs_nonneg _) _
  have hUV := hU.mul_of_nonneg hV hnnU (fun j => pow_nonneg (abs_nonneg _) _)
  have hbound : ∀ i j : ℕ, ‖((i : ℝ) + 1) *
      (m ^ i * nu ^ (i + j + 1) * x ^ (i * (i + j + 1)))‖
      ≤ (((i : ℝ) + 1) * |m * nu| ^ i * |x| ^ (i * (i + 1))) * |nu| ^ (j + 1) := by
    intro i j
    have hfi : (0 : ℝ) ≤ (i : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) i; linarith
    have hXij : |x| ^ (i * j) ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
    have hnnUij : 0 ≤ ((i : ℝ) + 1) * (|m * nu| ^ i * |x| ^ (i * (i + 1))) := by
      positivity
    have hnn2 : 0 ≤ |nu| ^ (j + 1) := pow_nonneg (abs_nonneg _) _
    have efac : ‖((i : ℝ) + 1) * (m ^ i * nu ^ (i + j + 1) * x ^ (i * (i + j + 1)))‖
        = ((i : ℝ) + 1) * ‖m ^ i * nu ^ (i + j + 1) * x ^ (i * (i + j + 1))‖ := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hfi,
        ← Real.norm_eq_abs]
    rw [efac]
    refine le_trans
      (mul_le_mul_of_nonneg_left (G_norm_bound m nu x hx i j) hfi) ?_
    have hle : |nu| ^ (j + 1) * |x| ^ (i * j) ≤ |nu| ^ (j + 1) * 1 :=
      mul_le_mul_of_nonneg_left hXij hnn2
    calc ((i : ℝ) + 1) * ((|m * nu| ^ i * |x| ^ (i * (i + 1))) *
            (|nu| ^ (j + 1) * |x| ^ (i * j)))
          = (((i : ℝ) + 1) * (|m * nu| ^ i * |x| ^ (i * (i + 1)))) *
            (|nu| ^ (j + 1) * |x| ^ (i * j)) := by rw [← mul_assoc]
        _ ≤ (((i : ℝ) + 1) * (|m * nu| ^ i * |x| ^ (i * (i + 1)))) *
            (|nu| ^ (j + 1) * 1) :=
          mul_le_mul_of_nonneg_left hle hnnUij
        _ = (((i : ℝ) + 1) * |m * nu| ^ i * |x| ^ (i * (i + 1))) * |nu| ^ (j + 1) := by
          rw [mul_one, ← mul_assoc]
  apply Summable.of_norm_bounded hUV
  intro ⟨i, j⟩
  exact hbound i j

-- The (j+1)-weighted double series is summable.
private theorem Gj_summable (m nu x : ℝ) (hx : |x| ≤ 1) (hnu : |nu| < 1)
    (hboundary : |x| = 1 → |m * nu| < 1) :
    Summable fun p : ℕ × ℕ => ((p.2 : ℝ) + 1) *
      (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))) := by
  have hU := supergeom_summable_plain |m * nu| |x| (abs_nonneg _) (abs_nonneg _) hx
    (fun h => hboundary h)
  have hV := geom_weighted_summable |nu|
    (by rw [Real.norm_eq_abs, abs_abs]; exact hnu)
  have hUV := hU.mul_of_nonneg hV
    (fun i => mul_nonneg (pow_nonneg (abs_nonneg _) _) (pow_nonneg (abs_nonneg _) _))
    (fun j => mul_nonneg (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
      (pow_nonneg (abs_nonneg _) _))
  have hbound : ∀ i j : ℕ, ‖((j : ℝ) + 1) *
      (m ^ i * nu ^ (i + j + 1) * x ^ (i * (i + j + 1)))‖
      ≤ (|m * nu| ^ i * |x| ^ (i * (i + 1))) * (((j : ℝ) + 1) * |nu| ^ (j + 1)) := by
    intro i j
    have hfj : (0 : ℝ) ≤ (j : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) j; linarith
    have hXij : |x| ^ (i * j) ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
    have hnn : 0 ≤ |m * nu| ^ i * |x| ^ (i * (i + 1)) := by positivity
    have hnn2 : 0 ≤ ((j : ℝ) + 1) * |nu| ^ (j + 1) := mul_nonneg hfj
      (pow_nonneg (abs_nonneg _) _)
    have efac : ‖((j : ℝ) + 1) * (m ^ i * nu ^ (i + j + 1) * x ^ (i * (i + j + 1)))‖
        = ((j : ℝ) + 1) * ‖m ^ i * nu ^ (i + j + 1) * x ^ (i * (i + j + 1))‖ := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hfj,
        ← Real.norm_eq_abs]
    rw [efac]
    refine le_trans
      (mul_le_mul_of_nonneg_left (G_norm_bound m nu x hx i j) hfj) ?_
    have hle : ((j : ℝ) + 1) * |nu| ^ (j + 1) * |x| ^ (i * j)
        ≤ ((j : ℝ) + 1) * |nu| ^ (j + 1) * 1 :=
      mul_le_mul_of_nonneg_left hXij hnn2
    calc ((j : ℝ) + 1) * ((|m * nu| ^ i * |x| ^ (i * (i + 1))) *
            (|nu| ^ (j + 1) * |x| ^ (i * j)))
          = (|m * nu| ^ i * |x| ^ (i * (i + 1))) *
            (((j : ℝ) + 1) * |nu| ^ (j + 1) * |x| ^ (i * j)) := by ring
        _ ≤ (|m * nu| ^ i * |x| ^ (i * (i + 1))) *
            (((j : ℝ) + 1) * |nu| ^ (j + 1) * 1) :=
          mul_le_mul_of_nonneg_left hle hnn
        _ = (|m * nu| ^ i * |x| ^ (i * (i + 1))) *
            (((j : ℝ) + 1) * |nu| ^ (j + 1)) := by rw [mul_one]
  apply Summable.of_norm_bounded hUV
  intro ⟨i, j⟩
  exact hbound i j

-- Row sums of G are geometric.
private theorem Grow_tsum (m nu x : ℝ) (k : ℕ) (hr : ‖nu * x ^ k‖ < 1) :
    ∑' j : ℕ, m ^ k * nu ^ (k + j + 1) * x ^ (k * (k + j + 1))
      = (m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) / (1 - nu * x ^ k) := by
  have hcongr : (fun j : ℕ => m ^ k * nu ^ (k + j + 1) * x ^ (k * (k + j + 1)))
      = (fun j : ℕ => (m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) * (nu * x ^ k) ^ j) :=
    funext (fun j => G_row_factor m nu x k j)
  rw [hcongr]
  exact row_geom_value _ _ hr

-- Weighted row sums of G.
private theorem Grow_weighted_tsum (m nu x : ℝ) (k : ℕ) (hr : ‖nu * x ^ k‖ < 1) :
    ∑' j : ℕ, ((j : ℝ) + 1) *
        (m ^ k * nu ^ (k + j + 1) * x ^ (k * (k + j + 1)))
      = (m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) / (1 - nu * x ^ k) ^ 2 := by
  have hcongr : (fun j : ℕ => ((j : ℝ) + 1) *
        (m ^ k * nu ^ (k + j + 1) * x ^ (k * (k + j + 1))))
      = (fun j : ℕ => ((j : ℝ) + 1) *
        ((m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) * (nu * x ^ k) ^ j)) := by
    funext j
    congr 1
    exact G_row_factor m nu x k j
  rw [hcongr]
  exact row_weighted_value _ _ hr

-- Diagonal reindexing: pairs (i,j) correspond to (k = i+j+1, i < k).
private def diagEquiv : ℕ × ℕ ≃ (k : ℕ) × Fin k where
  toFun p := ⟨p.1 + p.2 + 1, ⟨p.1, by omega⟩⟩
  invFun q := (q.2.val, q.1 - 1 - q.2.val)
  left_inv := by
    rintro ⟨i, j⟩
    change (i, i + j + 1 - 1 - i) = (i, j)
    rw [Prod.mk.injEq]
    exact ⟨rfl, by omega⟩
  right_inv := by
    rintro ⟨k, ⟨i, h⟩⟩
    have e : i + (k - 1 - i) + 1 = k := by omega
    have key : ∀ (A : ℕ) (e' : A = k) (a : Fin A) (_ha : a.val = i),
        (⟨A, a⟩ : (k' : ℕ) × Fin k') = ⟨k, (⟨i, h⟩ : Fin k)⟩ := by
      intro A e' a ha
      subst e'
      have hav : a = ⟨i, h⟩ := by ext; exact ha
      rw [hav]
    exact key _ e _ rfl

-- Norm bound for the geometric factor nu * x^k.
private theorem row_norm_aux (nu x : ℝ) (hx : |x| ≤ 1) (hnu : |nu| < 1) (k : ℕ) :
    ‖nu * x ^ k‖ < 1 := by
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  calc |nu| * |x| ^ k ≤ |nu| * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg _) hx) (abs_nonneg _)
    _ = |nu| := mul_one _
    _ < 1 := hnu

-- Nonvanishing of 1 - nu * x^k.
private theorem nu_ne_aux (nu x : ℝ) (hx : |x| ≤ 1) (hnu : |nu| < 1) (k : ℕ) :
    1 - nu * x ^ k ≠ 0 := by
  have h1 := row_norm_aux nu x hx hnu k
  intro hcon
  have heq : nu * x ^ k = 1 := (sub_eq_zero.mp hcon).symm
  rw [heq, norm_one] at h1
  exact lt_irrefl 1 h1

-- Pointwise bound for the linear-times-geometric numerator.
private theorem base_norm_bound (a b nu : ℝ) (k : ℕ) :
    ‖(a + (k : ℝ) * b) * nu ^ k‖ ≤ (|a| + |b| * ((k : ℝ) + 1)) * |nu| ^ k := by
  have hk := Nat.cast_nonneg (α := ℝ) k
  have h1 : |(a + (k : ℝ) * b)| ≤ |a| + |b| * ((k : ℝ) + 1) := by
    have h2 : (k : ℝ) * |b| ≤ |b| * ((k : ℝ) + 1) := by
      rw [mul_comm (k : ℝ) |b|]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      linarith
    calc |(a + (k : ℝ) * b)| ≤ |a| + |(k : ℝ) * b| := abs_add_le _ _
      _ = |a| + (k : ℝ) * |b| := by rw [abs_mul, abs_of_nonneg hk]
      _ ≤ |a| + |b| * ((k : ℝ) + 1) := by linarith
  calc ‖(a + (k : ℝ) * b) * nu ^ k‖ = |(a + (k : ℝ) * b)| * |nu| ^ k := by
        rw [Real.norm_eq_abs, abs_mul, abs_pow]
    _ ≤ (|a| + |b| * ((k : ℝ) + 1)) * |nu| ^ k :=
        mul_le_mul_of_nonneg_right h1 (pow_nonneg (abs_nonneg _) _)

-- Summable majorant for the numerators.
private theorem maj_summable (a b nu : ℝ) (hnu : |nu| < 1) :
    Summable fun k : ℕ => (|a| + |b| * ((k : ℝ) + 1)) * |nu| ^ k := by
  have hnuA : ‖|nu|‖ < 1 := by rw [Real.norm_eq_abs, abs_abs]; exact hnu
  have g1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnuA
  have g0 := summable_geometric_of_norm_lt_one hnuA (R := ℝ)
  have hcongr : (fun k : ℕ => (|a| + |b| * ((k : ℝ) + 1)) * |nu| ^ k)
      = (fun k : ℕ => |a| * |nu| ^ k
        + (|b| * ((k : ℝ) ^ 1 * |nu| ^ k) + |b| * |nu| ^ k)) := by
    funext k; simp only [pow_one]; ring
  rw [hcongr]
  exact (g0.mul_left |a|).add ((g1.mul_left |b|).add (g0.mul_left |b|))

-- The numerators (a + k b) nu^k are absolutely summable.
private theorem base_summable (a b nu : ℝ) (hnu : |nu| < 1) :
    Summable fun k : ℕ => (a + (k : ℝ) * b) * nu ^ k := by
  apply Summable.of_norm_bounded (maj_summable a b nu hnu)
  intro k
  exact base_norm_bound a b nu k

-- Left series, interior case: the cofactor tends to 1.
private theorem left_summable_lt (a b m nu x : ℝ) (hxlt : |x| < 1) (hnu : |nu| < 1) :
    Summable fun k : ℕ => (a + (k : ℝ) * b) * nu ^ k / (1 - m * x ^ k) := by
  have hfnorm : Summable fun k : ℕ => ‖(a + (k : ℝ) * b) * nu ^ k‖ := by
    apply Summable.of_norm_bounded (maj_summable a b nu hnu)
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact base_norm_bound a b nu k
  have hxk : Tendsto (fun k : ℕ => m * x ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hxlt))
  have h1 : Tendsto (fun k : ℕ => 1 - m * x ^ k) atTop (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds.sub hxk)
  have h2 : Tendsto (fun k : ℕ => (1 - m * x ^ k)⁻¹) cofinite (𝓝 (1 : ℝ)) := by
    rw [Nat.cofinite_eq_atTop]
    simpa using (h1.inv₀ one_ne_zero)
  have hmul := Summable.mul_tendsto_const hfnorm h2
  refine hmul.congr (fun k => ?_)
  change (a + (k : ℝ) * b) * nu ^ k * (1 - m * x ^ k)⁻¹
    = (a + (k : ℝ) * b) * nu ^ k / (1 - m * x ^ k)
  exact (div_eq_mul_inv _ _).symm

-- Left series, boundary case x = 1.
private theorem left_summable_one (a b m nu : ℝ) (hnu : |nu| < 1) :
    Summable fun k : ℕ => (a + (k : ℝ) * b) * nu ^ k / (1 - m * (1 : ℝ) ^ k) := by
  have hbase := base_summable a b nu hnu
  have hcongr : (fun k : ℕ => (a + (k : ℝ) * b) * nu ^ k / (1 - m * (1 : ℝ) ^ k))
      = (fun k : ℕ => ((a + (k : ℝ) * b) * nu ^ k) * (1 - m)⁻¹) := by
    funext k; rw [one_pow, mul_one, div_eq_mul_inv]
  rw [hcongr]
  exact hbase.mul_right _

-- Left series, boundary case x = -1.
private theorem left_summable_negone (a b m nu : ℝ) (hnu : |nu| < 1) :
    Summable fun k : ℕ => (a + (k : ℝ) * b) * nu ^ k / (1 - m * (-1 : ℝ) ^ k) := by
  have hmaj := maj_summable a b nu hnu
  have hB : ∀ k : ℕ, ‖((1 : ℝ) - m * (-1) ^ k)⁻¹‖ ≤ ‖(1 - m)⁻¹‖ ⊔ ‖(1 + m)⁻¹‖ := by
    intro k
    rcases Nat.even_or_odd k with hev | hodd
    · rw [hev.neg_one_pow, mul_one]
      exact le_max_left _ _
    · have e : (-1 : ℝ) ^ k = -1 := hodd.neg_one_pow
      have e2 : (1 : ℝ) - m * -1 = 1 + m := by ring
      rw [e, e2]
      exact le_max_right _ _
  have hmul := hmaj.mul_left (‖(1 - m)⁻¹‖ ⊔ ‖(1 + m)⁻¹‖)
  apply Summable.of_norm_bounded hmul
  intro k
  calc ‖(a + (k : ℝ) * b) * nu ^ k / (1 - m * (-1) ^ k)‖
      = ‖(a + (k : ℝ) * b) * nu ^ k‖ * ‖((1 : ℝ) - m * (-1) ^ k)⁻¹‖ := by
        rw [div_eq_mul_inv, norm_mul]
    _ ≤ ((|a| + |b| * ((k : ℝ) + 1)) * |nu| ^ k) * (‖(1 - m)⁻¹‖ ⊔ ‖(1 + m)⁻¹‖) :=
        mul_le_mul (base_norm_bound a b nu k) (hB k) (norm_nonneg _)
          (mul_nonneg (add_nonneg (abs_nonneg _)
            (mul_nonneg (abs_nonneg _) (by
              have hk := Nat.cast_nonneg (α := ℝ) k; linarith)))
            (pow_nonneg (abs_nonneg _) _))
    _ = (‖(1 - m)⁻¹‖ ⊔ ‖(1 + m)⁻¹‖) * ((|a| + |b| * ((k : ℝ) + 1)) * |nu| ^ k) := by
        ring

-- Left series in all cases.
private theorem left_summable (a b m nu x : ℝ) (hx : |x| ≤ 1) (hnu : |nu| < 1)
    (hmx : ∀ k : ℕ, 1 - m * x ^ k ≠ 0) :
    Summable fun k : ℕ => (a + (k : ℝ) * b) * nu ^ k / (1 - m * x ^ k) := by
  rcases lt_or_eq_of_le hx with hlt | heq
  · exact left_summable_lt a b m nu x hlt hnu
  · have hxval : x = 1 ∨ x = -1 := eq_or_eq_neg_of_abs_eq heq
    rcases hxval with rfl | rfl
    · exact left_summable_one a b m nu hnu
    · exact left_summable_negone a b m nu hnu

-- The i-weighted double series is summable.
private theorem IG_summable (m nu x : ℝ) (hx : |x| ≤ 1) (hnu : |nu| < 1)
    (hboundary : |x| = 1 → |m * nu| < 1) :
    Summable fun p : ℕ × ℕ => (p.1 : ℝ) *
      (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))) := by
  have hsub := (Gi_summable m nu x hx hnu hboundary).sub
    (G_summable m nu x hx hnu hboundary)
  exact hsub.congr (fun p => by ring)

-- The j-weighted double series is summable.
private theorem JG_summable (m nu x : ℝ) (hx : |x| ≤ 1) (hnu : |nu| < 1)
    (hboundary : |x| = 1 → |m * nu| < 1) :
    Summable fun p : ℕ × ℕ => (p.2 : ℝ) *
      (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))) := by
  have hsub := (Gj_summable m nu x hx hnu hboundary).sub
    (G_summable m nu x hx hnu hboundary)
  exact hsub.congr (fun p => by ring)

-- The (a + i b)-weighted double series is summable (Q side).
private theorem W1_summable (a b m nu x : ℝ) (hx : |x| ≤ 1) (hnu : |nu| < 1)
    (hboundary : |x| = 1 → |m * nu| < 1) :
    Summable fun p : ℕ × ℕ => (a + (p.1 : ℝ) * b) *
      (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))) := by
  have hG := G_summable m nu x hx hnu hboundary
  have hIG := IG_summable m nu x hx hnu hboundary
  have hcongr : (fun p : ℕ × ℕ => (a + (p.1 : ℝ) * b) *
        (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))))
      = (fun p : ℕ × ℕ => a * (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)))
        + b * ((p.1 : ℝ) * (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))))) := by
    funext p; ring
  rw [hcongr]
  exact (hG.mul_left a).add (hIG.mul_left b)

-- The (a + (i+j+1) b)-weighted double series is summable (D side).
private theorem W2_summable (a b m nu x : ℝ) (hx : |x| ≤ 1) (hnu : |nu| < 1)
    (hboundary : |x| = 1 → |m * nu| < 1) :
    Summable fun p : ℕ × ℕ => (a + (((p.1 + p.2 + 1 : ℕ)) : ℝ) * b) *
      (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))) := by
  have hG := G_summable m nu x hx hnu hboundary
  have hIG := IG_summable m nu x hx hnu hboundary
  have hJG := JG_summable m nu x hx hnu hboundary
  have hcongr : (fun p : ℕ × ℕ => (a + (((p.1 + p.2 + 1 : ℕ)) : ℝ) * b) *
        (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))))
      = (fun p : ℕ × ℕ => (a + b) * (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)))
        + (b * ((p.1 : ℝ) * (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))))
          + b * ((p.2 : ℝ) * (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)))))) := by
    funext p; push_cast; ring
  rw [hcongr]
  exact (hG.mul_left (a + b)).add ((hIG.mul_left b).add (hJG.mul_left b))

-- Row sums on the Q side.
private theorem Qrow_value (a b m nu x : ℝ) (k : ℕ) (hr : ‖nu * x ^ k‖ < 1) :
    (∑' j : ℕ, (a + (k : ℝ) * b) *
      (m ^ k * nu ^ (k + j + 1) * x ^ (k * (k + j + 1))))
      = (a + (k : ℝ) * b) *
        ((m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) / (1 - nu * x ^ k)) := by
  rw [tsum_mul_left]
  congr 1
  exact Grow_tsum m nu x k hr

-- Diagonal terms equal nu^k * (m * x^k)^i.
private theorem Dterm_value (a b m nu x : ℝ) (k i : ℕ) (h : i < k) :
    (fun p : ℕ × ℕ => (a + (((p.1 + p.2 + 1 : ℕ)) : ℝ) * b) *
      (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)))) (i, k - 1 - i)
      = (a + (k : ℝ) * b) * (nu ^ k * (m * x ^ k) ^ i) := by
  have e : i + (k - 1 - i) + 1 = k := by omega
  have e3 : i * k = k * i := by ring
  change (a + (((i + (k - 1 - i) + 1 : ℕ)) : ℝ) * b) *
      (m ^ i * nu ^ (i + (k - 1 - i) + 1) * x ^ (i * (i + (k - 1 - i) + 1)))
      = (a + (k : ℝ) * b) * (nu ^ k * (m * x ^ k) ^ i)
  rw [e, e3, mul_pow, ← pow_mul]
  ring

-- Diagonal (range) sums on the D side.
private theorem Drow_value (a b m nu x : ℝ) (k : ℕ)
    (hf : ∀ i : Fin k, ((fun p : ℕ × ℕ => (a + (((p.1 + p.2 + 1 : ℕ)) : ℝ) * b) *
      (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)))) ∘ diagEquiv.symm) ⟨k, i⟩
        = (a + (k : ℝ) * b) * (nu ^ k * (m * x ^ k) ^ (i.val))) :
    (∑' i : Fin k, ((fun p : ℕ × ℕ => (a + (((p.1 + p.2 + 1 : ℕ)) : ℝ) * b) *
      (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)))) ∘ diagEquiv.symm) ⟨k, i⟩)
      = (a + (k : ℝ) * b) * (nu ^ k * ∑ i ∈ range k, (m * x ^ k) ^ i) := by
  have h1 : (∑' i : Fin k, ((fun p : ℕ × ℕ => (a + (((p.1 + p.2 + 1 : ℕ)) : ℝ) * b) *
      (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)))) ∘ diagEquiv.symm) ⟨k, i⟩)
      = ∑ i ∈ range k, (a + (k : ℝ) * b) * (nu ^ k * (m * x ^ k) ^ i) := by
    rw [tsum_fintype]
    apply Finset.sum_bij (fun a _ => a.val)
    · intro a _
      exact Finset.mem_range.mpr a.isLt
    · intro a₁ _ a₂ _ h12
      exact Fin.ext h12
    · intro b hb
      exact ⟨⟨b, Finset.mem_range.mp hb⟩, Finset.mem_univ _, rfl⟩
    · intro a _
      exact hf a
  rw [h1, ← Finset.mul_sum]
  congr 1
  rw [← Finset.mul_sum]

-- Second-series terms are m times the weighted row sums.
private theorem hsec_val (m nu x : ℝ) (k : ℕ) (hr : ‖nu * x ^ k‖ < 1) :
    (m * nu * x ^ k) ^ (k + 1) / (1 - nu * x ^ k) ^ 2
      = m * (∑' j : ℕ, ((j : ℝ) + 1) *
        (m ^ k * nu ^ (k + j + 1) * x ^ (k * (k + j + 1)))) := by
  rw [Grow_weighted_tsum m nu x k hr, second_num_factor]
  ring

-- Pointwise identity: leftTerm = firstTerm + (w * D - w * Q).
private theorem point_ident (a b m nu x : ℝ) (k : ℕ)
    (h1mt : (1 : ℝ) - m * x ^ k ≠ 0) (h1ms : (1 : ℝ) - nu * x ^ k ≠ 0)
    (ht1 : m * x ^ k ≠ 1) :
    (a + (k : ℝ) * b) * nu ^ k / (1 - m * x ^ k)
      = ((a + (k : ℝ) * b) * (1 - m * nu * x ^ (2 * k)) * (m * nu * x ^ k) ^ k) /
          ((1 - m * x ^ k) * (1 - nu * x ^ k))
        + ((a + (k : ℝ) * b) * (nu ^ k * ∑ i ∈ range k, (m * x ^ k) ^ i)
          - (a + (k : ℝ) * b) *
            ((m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) / (1 - nu * x ^ k))) := by
  have hgeom : ∑ i ∈ range k, (m * x ^ k) ^ i = ((m * x ^ k) ^ k - 1) / ((m * x ^ k) - 1) :=
    geom_sum_eq ht1 k
  have hQnum : m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))
      = nu ^ k * (m * x ^ k) ^ k * (nu * x ^ k) := by
    rw [mul_pow, ← pow_mul]; ring
  rw [hgeom, hQnum, first_alg_tkq m nu x k, first_alg_ts m nu x k]
  have hmt : (m : ℝ) * x ^ k - 1 ≠ 0 := sub_ne_zero.mpr ht1
  have h1ms' : (1 : ℝ) - x ^ k * nu ≠ 0 := by
    have h := h1ms
    rwa [mul_comm nu (x ^ k)] at h
  field_simp [h1mt, h1ms, h1ms', hmt]
  ring

-- Full statement with explicit series (no local lets).
private theorem entry17_aux (a b m nu x : ℝ)
    (hx : |x| ≤ 1) (hnu : |nu| < 1)
    (hboundary : |x| = 1 → |m * nu| < 1)
    (hm : m ≠ 0)
    (hmx : ∀ k : ℕ, 1 - m * x ^ k ≠ 0) :
    (∀ k : ℕ, 1 - nu * x ^ k ≠ 0) ∧
      Summable (fun k : ℕ => (a + (k : ℝ) * b) * nu ^ k / (1 - m * x ^ k)) ∧
      Summable (fun k : ℕ => ((a + (k : ℝ) * b) * (1 - m * nu * x ^ (2 * k)) *
        (m * nu * x ^ k) ^ k) / ((1 - m * x ^ k) * (1 - nu * x ^ k))) ∧
      Summable (fun k : ℕ => (m * nu * x ^ k) ^ (k + 1) / (1 - nu * x ^ k) ^ 2) ∧
      (∑' k : ℕ, ((a + (k : ℝ) * b) * nu ^ k / (1 - m * x ^ k)))
        = (∑' k : ℕ, (((a + (k : ℝ) * b) * (1 - m * nu * x ^ (2 * k)) *
          (m * nu * x ^ k) ^ k) / ((1 - m * x ^ k) * (1 - nu * x ^ k))))
          + b / m * ∑' k : ℕ, ((m * nu * x ^ k) ^ (k + 1) / (1 - nu * x ^ k) ^ 2) := by
  have hnu_ne : ∀ k : ℕ, 1 - nu * x ^ k ≠ 0 := fun k => nu_ne_aux nu x hx hnu k
  have hr : ∀ k : ℕ, ‖nu * x ^ k‖ < 1 := fun k => row_norm_aux nu x hx hnu k
  have hLeft := left_summable a b m nu x hx hnu hmx
  have hW1 := W1_summable a b m nu x hx hnu hboundary
  have hW2 := W2_summable a b m nu x hx hnu hboundary
  have hGj := Gj_summable m nu x hx hnu hboundary
  have hWQ : Summable fun k : ℕ => (a + (k : ℝ) * b) *
      ((m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) / (1 - nu * x ^ k)) := by
    have hS : Summable ((fun p : ℕ × ℕ => (a + (p.1 : ℝ) * b) *
        (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)))) ∘
        ⇑(Equiv.sigmaEquivProd ℕ ℕ)) :=
      ((Equiv.sigmaEquivProd ℕ ℕ).summable_iff (f := fun p : ℕ × ℕ => (a + (p.1 : ℝ) * b) *
        (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))))).mpr hW1
    have hsig := hS.sigma
    apply hsig.congr
    intro k
    simp only [Function.comp_apply, Equiv.sigmaEquivProd_apply]
    exact Qrow_value a b m nu x k (hr k)
  have hW2d : Summable ((fun p : ℕ × ℕ => (a + (((p.1 + p.2 + 1 : ℕ)) : ℝ) * b) *
      (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)))) ∘ diagEquiv.symm) :=
    (diagEquiv.symm.summable_iff (f := fun p : ℕ × ℕ => (a + (((p.1 + p.2 + 1 : ℕ)) : ℝ) * b) *
      (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))))).mpr hW2
  have hWD : Summable fun k : ℕ => (a + (k : ℝ) * b) *
      (nu ^ k * ∑ i ∈ range k, (m * x ^ k) ^ i) := by
    have hsig : Summable fun k : ℕ => ∑' i : Fin k,
        ((fun p : ℕ × ℕ => (a + (((p.1 + p.2 + 1 : ℕ)) : ℝ) * b) *
          (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)))) ∘
          diagEquiv.symm) ⟨k, i⟩ := hW2d.sigma
    apply hsig.congr
    intro k
    apply Drow_value a b m nu x k
    intro i
    obtain ⟨i', h⟩ := i
    exact Dterm_value a b m nu x k i' h
  have hSec : Summable fun k : ℕ => (m * nu * x ^ k) ^ (k + 1) / (1 - nu * x ^ k) ^ 2 := by
    have hS : Summable ((fun p : ℕ × ℕ => ((p.2 : ℝ) + 1) *
        (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)))) ∘
        ⇑(Equiv.sigmaEquivProd ℕ ℕ)) :=
      ((Equiv.sigmaEquivProd ℕ ℕ).summable_iff (f := fun p : ℕ × ℕ => ((p.2 : ℝ) + 1) *
        (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))))).mpr hGj
    have hsig := hS.sigma
    have hval : (fun k : ℕ => (m * nu * x ^ k) ^ (k + 1) / (1 - nu * x ^ k) ^ 2)
        = (fun k : ℕ => m * (∑' j : ℕ, ((j : ℝ) + 1) *
          (m ^ k * nu ^ (k + j + 1) * x ^ (k * (k + j + 1))))) := by
      funext k
      exact hsec_val m nu x k (hr k)
    rw [hval]
    exact hsig.mul_left m
  have hpoint : ∀ k : ℕ, (a + (k : ℝ) * b) * nu ^ k / (1 - m * x ^ k)
      = ((a + (k : ℝ) * b) * (1 - m * nu * x ^ (2 * k)) * (m * nu * x ^ k) ^ k) /
          ((1 - m * x ^ k) * (1 - nu * x ^ k))
        + ((a + (k : ℝ) * b) * (nu ^ k * ∑ i ∈ range k, (m * x ^ k) ^ i)
          - (a + (k : ℝ) * b) *
            ((m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) / (1 - nu * x ^ k))) := by
    intro k
    exact point_ident a b m nu x k (hmx k) (hnu_ne k)
      (fun h => hmx k (by rw [h, sub_self]))
  have hFirst : Summable fun k : ℕ => ((a + (k : ℝ) * b) *
      (1 - m * nu * x ^ (2 * k)) * (m * nu * x ^ k) ^ k) /
        ((1 - m * x ^ k) * (1 - nu * x ^ k)) := by
    have hsub := hWD.sub hWQ
    have hmain := hLeft.sub hsub
    have hcongr : ∀ k : ℕ, ((a + (k : ℝ) * b) * nu ^ k / (1 - m * x ^ k)
        - ((a + (k : ℝ) * b) * (nu ^ k * ∑ i ∈ range k, (m * x ^ k) ^ i)
          - (a + (k : ℝ) * b) *
            ((m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) / (1 - nu * x ^ k))))
        = ((a + (k : ℝ) * b) * (1 - m * nu * x ^ (2 * k)) * (m * nu * x ^ k) ^ k) /
          ((1 - m * x ^ k) * (1 - nu * x ^ k)) := fun k => by
      rw [hpoint k]; ring
    exact hmain.congr hcongr
  have hT1 : (∑' k : ℕ, (a + (k : ℝ) * b) *
      ((m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) / (1 - nu * x ^ k)))
      = ∑' p : ℕ × ℕ, (a + (p.1 : ℝ) * b) *
        (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))) :=
    (tsum_congr (fun k => (Qrow_value a b m nu x k (hr k)).symm)).trans
      hW1.tsum_prod.symm
  have hT2 : (∑' k : ℕ, (a + (k : ℝ) * b) *
      (nu ^ k * ∑ i ∈ range k, (m * x ^ k) ^ i))
      = ∑' p : ℕ × ℕ, (a + (((p.1 + p.2 + 1 : ℕ)) : ℝ) * b) *
        (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))) := by
    have hstep : (∑' k : ℕ, (a + (k : ℝ) * b) *
        (nu ^ k * ∑ i ∈ range k, (m * x ^ k) ^ i))
        = ∑' k : ℕ, ∑' i : Fin k, ((fun p : ℕ × ℕ => (a + (((p.1 + p.2 + 1 : ℕ)) : ℝ) * b) *
          (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)))) ∘
          diagEquiv.symm) ⟨k, i⟩ :=
      tsum_congr (fun k => (Drow_value a b m nu x k (fun i => by
        obtain ⟨i', h⟩ := i
        exact Dterm_value a b m nu x k i' h)).symm)
    have hsig := hW2d.tsum_sigma
    have hteq := diagEquiv.symm.tsum_eq (fun p : ℕ × ℕ => (a + (((p.1 + p.2 + 1 : ℕ)) : ℝ) * b) *
      (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))))
    exact hstep.trans hsig.symm |>.trans hteq
  have hS2 : (∑' k : ℕ, (m * nu * x ^ k) ^ (k + 1) / (1 - nu * x ^ k) ^ 2)
      = m * ∑' p : ℕ × ℕ, ((p.2 : ℝ) + 1) *
        (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))) := by
    have hstep : (∑' k : ℕ, (m * nu * x ^ k) ^ (k + 1) / (1 - nu * x ^ k) ^ 2)
        = ∑' k : ℕ, m * (∑' j : ℕ, ((j : ℝ) + 1) *
          (m ^ k * nu ^ (k + j + 1) * x ^ (k * (k + j + 1)))) :=
      tsum_congr (fun k => hsec_val m nu x k (hr k))
    have hmul : (∑' k : ℕ, m * (∑' j : ℕ, ((j : ℝ) + 1) *
        (m ^ k * nu ^ (k + j + 1) * x ^ (k * (k + j + 1)))))
        = m * ∑' k : ℕ, (∑' j : ℕ, ((j : ℝ) + 1) *
          (m ^ k * nu ^ (k + j + 1) * x ^ (k * (k + j + 1)))) :=
      tsum_mul_left
    exact hstep.trans hmul |>.trans (congrArg (m * ·) hGj.tsum_prod.symm)
  have hDiff : (∑' p : ℕ × ℕ, (a + (((p.1 + p.2 + 1 : ℕ)) : ℝ) * b) *
      (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))))
      - (∑' p : ℕ × ℕ, (a + (p.1 : ℝ) * b) *
        (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))))
      = b * ∑' p : ℕ × ℕ, ((p.2 : ℝ) + 1) *
        (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))) := by
    have hsub := hW2.tsum_sub hW1
    have hfun : (fun p : ℕ × ℕ => (a + (((p.1 + p.2 + 1 : ℕ)) : ℝ) * b) *
        (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)))
        - (a + (p.1 : ℝ) * b) *
          (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))))
        = (fun p : ℕ × ℕ => b * (((p.2 : ℝ) + 1) *
          (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))))) := by
      funext p; push_cast; ring
    have hval : (∑' p : ℕ × ℕ, ((a + (((p.1 + p.2 + 1 : ℕ)) : ℝ) * b) *
        (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)))
        - (a + (p.1 : ℝ) * b) *
          (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)))))
        = b * ∑' p : ℕ × ℕ, ((p.2 : ℝ) + 1) *
          (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))) := by
      rw [hfun, tsum_mul_left]
    exact hsub.symm.trans hval
  have hval : (∑' k : ℕ, ((a + (k : ℝ) * b) * nu ^ k / (1 - m * x ^ k)))
      = (∑' k : ℕ, (((a + (k : ℝ) * b) * (1 - m * nu * x ^ (2 * k)) *
        (m * nu * x ^ k) ^ k) / ((1 - m * x ^ k) * (1 - nu * x ^ k))))
        + ((∑' k : ℕ, (a + (k : ℝ) * b) *
          (nu ^ k * ∑ i ∈ range k, (m * x ^ k) ^ i))
          - (∑' k : ℕ, (a + (k : ℝ) * b) *
            ((m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) / (1 - nu * x ^ k)))) := by
    have htsum : (∑' k : ℕ, ((a + (k : ℝ) * b) * nu ^ k / (1 - m * x ^ k)
        - ((a + (k : ℝ) * b) * (nu ^ k * ∑ i ∈ range k, (m * x ^ k) ^ i)
          - (a + (k : ℝ) * b) *
            ((m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) / (1 - nu * x ^ k)))))
        = (∑' k : ℕ, ((a + (k : ℝ) * b) * nu ^ k / (1 - m * x ^ k)))
          - (∑' k : ℕ, ((a + (k : ℝ) * b) * (nu ^ k * ∑ i ∈ range k, (m * x ^ k) ^ i)
            - (a + (k : ℝ) * b) *
              ((m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) / (1 - nu * x ^ k)))) :=
      hLeft.tsum_sub (hWD.sub hWQ)
    have htsum2 : (∑' k : ℕ, ((a + (k : ℝ) * b) * (nu ^ k * ∑ i ∈ range k, (m * x ^ k) ^ i)
        - (a + (k : ℝ) * b) *
          ((m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) / (1 - nu * x ^ k))))
        = (∑' k : ℕ, (a + (k : ℝ) * b) * (nu ^ k * ∑ i ∈ range k, (m * x ^ k) ^ i))
          - (∑' k : ℕ, (a + (k : ℝ) * b) *
            ((m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) / (1 - nu * x ^ k))) :=
      hWD.tsum_sub hWQ
    have hcongr : (∑' k : ℕ, ((a + (k : ℝ) * b) * nu ^ k / (1 - m * x ^ k)
        - ((a + (k : ℝ) * b) * (nu ^ k * ∑ i ∈ range k, (m * x ^ k) ^ i)
          - (a + (k : ℝ) * b) *
            ((m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) / (1 - nu * x ^ k)))))
        = (∑' k : ℕ, (((a + (k : ℝ) * b) * (1 - m * nu * x ^ (2 * k)) *
          (m * nu * x ^ k) ^ k) / ((1 - m * x ^ k) * (1 - nu * x ^ k)))) :=
      tsum_congr (fun k => by rw [hpoint k]; ring)
    have hL : (∑' k : ℕ, ((a + (k : ℝ) * b) * nu ^ k / (1 - m * x ^ k)))
        - (∑' k : ℕ, ((a + (k : ℝ) * b) * (nu ^ k * ∑ i ∈ range k, (m * x ^ k) ^ i)
          - (a + (k : ℝ) * b) *
            ((m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) / (1 - nu * x ^ k))))
        = (∑' k : ℕ, (((a + (k : ℝ) * b) * (1 - m * nu * x ^ (2 * k)) *
          (m * nu * x ^ k) ^ k) / ((1 - m * x ^ k) * (1 - nu * x ^ k)))) :=
      htsum.symm.trans hcongr
    rw [htsum2] at hL
    exact sub_eq_iff_eq_add.mp hL
  have hfin : b / m * (∑' k : ℕ, (m * nu * x ^ k) ^ (k + 1) / (1 - nu * x ^ k) ^ 2)
      = b * ∑' p : ℕ × ℕ, ((p.2 : ℝ) + 1) *
        (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))) := by
    rw [hS2, ← mul_assoc, div_mul_cancel₀ _ hm]
  refine ⟨hnu_ne, hLeft, hFirst, hSec, ?_⟩
  rw [hval, hT2, hT1, hDiff, hfin]



section
/-!
# Ramanujan's Notebooks, Part I, Chapter 6

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch6

namespace Entry17Stirlingcoeffs

open scoped BigOperators
open Filter Finset Topology

noncomputable section

/-- **Ramanujan's identity for $\sum_k (a + kb) \nu^k / (1 - m x^k)$.** Let $a, b, m, \nu, x$ be
real numbers with $|x| \le 1$, $|\nu| < 1$ and $m \ne 0$, such that $|m \nu| < 1$ if $|x| = 1$,
and such that $1 - m x^k \ne 0$ for every integer $k \ge 0$ (here $x^0 = 1$). Then
$1 - \nu x^k \ne 0$ for every $k \ge 0$, the series
$L = \sum_{k=0}^{\infty} \frac{(a + kb) \, \nu^k}{1 - m x^k}$,
$F = \sum_{k=0}^{\infty} \frac{(a + kb) (1 - m \nu x^{2k}) (m \nu x^k)^k}{(1 - m x^k)(1 - \nu x^k)}$
and $G = \sum_{k=0}^{\infty} \frac{(m \nu x^k)^{k+1}}{(1 - \nu x^k)^2}$ are summable, and
$L = F + \frac{b}{m} G$.

Proves `Wanted` entry `ramanujan_part1_ch6_entry17_stirlingcoeffs`.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 6.
-/
theorem ramanujan_part1_ch6_entry17_stirlingcoeffs
    (a b m nu x : ℝ)
    (hx : |x| ≤ 1) (hnu : |nu| < 1)
    (hboundary : |x| = 1 → |m * nu| < 1)
    (hm : m ≠ 0)
    (hmx : ∀ k : ℕ, 1 - m * x ^ k ≠ 0) :
    let leftTerm := fun k : ℕ =>
      (a + (k : ℝ) * b) * nu ^ k / (1 - m * x ^ k)
    let firstTerm := fun k : ℕ =>
      ((a + (k : ℝ) * b) * (1 - m * nu * x ^ (2 * k)) *
          (m * nu * x ^ k) ^ k) /
        ((1 - m * x ^ k) * (1 - nu * x ^ k))
    let secondTerm := fun k : ℕ =>
      (m * nu * x ^ k) ^ (k + 1) / (1 - nu * x ^ k) ^ 2
    (∀ k : ℕ, 1 - nu * x ^ k ≠ 0) ∧
      Summable leftTerm ∧ Summable firstTerm ∧ Summable secondTerm ∧
      ∑' k, leftTerm k =
        ∑' k, firstTerm k + b / m * ∑' k, secondTerm k := by
  exact entry17_aux a b m nu x hx hnu hboundary hm hmx

end
end Entry17Stirlingcoeffs
end MathlibExt.Analysis.Ramanujan.Part1Ch6
end
