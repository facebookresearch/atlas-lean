/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import MathlibExt.Combinatorics.Coding.CycleCode
import MathlibExt.Combinatorics.SimpleGraph.LovaszThetaStrongPower
import MathlibExt.Combinatorics.SimpleGraph.ShannonCapacityPentagon
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Data.ZMod.Basic

/-!
# Lovász's upper bound for the capacity of the 7-cycle

This module proves that the Shannon capacity of the 7-cycle is at most
`7 * cos (π / 7) / (1 + cos (π / 7))`. It defines `lovaszThetaCycleSeven` and proves
`lovasz1979UpperBound` via an orthogonal labeling of the 7-cycle in `ℝ⁵`.

Source: L. Lovász, "On the Shannon capacity of a graph",
IEEE Trans. Inform. Theory 25 (1979), 1-7;
Buys--Polak--Zuiddam arXiv:2607.29681.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Coding.CycleShannonBoundsWanted

open MathlibExt.Combinatorics.Coding.CycleGraphCode
open MathlibExt.Combinatorics.SimpleGraph.LovaszTheta
open scoped RealInnerProductSpace
open MathlibExt.Combinatorics.ShannonCapacityPentagonWanted.Combinatorics.ShannonCapacityPentagon
  (strongPower)

private noncomputable def c7w1 : ℝ :=
  Real.cos (2 * Real.pi / 7) - Real.cos (6 * Real.pi / 7)

private noncomputable def c7w2 : ℝ :=
  Real.cos (4 * Real.pi / 7) - Real.cos (6 * Real.pi / 7)

private noncomputable def c7h : ℝ :=
  Real.sqrt ((1 - Real.cos (6 * Real.pi / 7)) / 2)

private noncomputable def c7theta : ℝ :=
  7 * Real.cos (Real.pi / 7) / (1 + Real.cos (Real.pi / 7))

private theorem c7w1_nonneg : 0 ≤ c7w1 := by
  unfold c7w1
  have h : Real.cos (6 * Real.pi / 7) ≤ Real.cos (2 * Real.pi / 7) := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · positivity
    · have hpi : 0 < Real.pi := Real.pi_pos
      have hle : Real.pi ≤ 4 := Real.pi_le_four
      linarith
    · have hpi : 0 < Real.pi := Real.pi_pos
      linarith
  linarith

private theorem c7w2_nonneg : 0 ≤ c7w2 := by
  unfold c7w2
  have h : Real.cos (6 * Real.pi / 7) ≤ Real.cos (4 * Real.pi / 7) := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · positivity
    · have hpi : 0 < Real.pi := Real.pi_pos
      have hle : Real.pi ≤ 4 := Real.pi_le_four
      linarith
    · have hpi : 0 < Real.pi := Real.pi_pos
      linarith
  linarith

private theorem c7h_sq : c7h * c7h = (1 - Real.cos (6 * Real.pi / 7)) / 2 := by
  unfold c7h
  apply Real.mul_self_sqrt
  have h : Real.cos (6 * Real.pi / 7) ≤ 1 := Real.cos_le_one _
  linarith

private theorem c7cos6 : Real.cos (6 * Real.pi / 7) = -Real.cos (Real.pi / 7) := by
  have e : 6 * Real.pi / 7 = Real.pi - Real.pi / 7 := by ring
  rw [e, Real.cos_pi_sub]

private theorem c7cos_pos : 0 < Real.cos (Real.pi / 7) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have hpi : 0 < Real.pi := Real.pi_pos
    linarith
  · have hpi : 0 < Real.pi := Real.pi_pos
    linarith

private theorem c7theta_nonneg : 0 ≤ c7theta := by
  unfold c7theta
  have hc : 0 < Real.cos (Real.pi / 7) := c7cos_pos
  positivity

private theorem c7prod : 2 * (Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7))
    = Real.cos (2 * Real.pi / 7) + Real.cos (6 * Real.pi / 7) := by
  have h1 : Real.cos (2 * Real.pi / 7 + 4 * Real.pi / 7)
      = Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7)
        - Real.sin (2 * Real.pi / 7) * Real.sin (4 * Real.pi / 7) :=
    Real.cos_add _ _
  have h2 : Real.cos (2 * Real.pi / 7 - 4 * Real.pi / 7)
      = Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7)
        + Real.sin (2 * Real.pi / 7) * Real.sin (4 * Real.pi / 7) :=
    Real.cos_sub _ _
  have e1 : 2 * Real.pi / 7 + 4 * Real.pi / 7 = 6 * Real.pi / 7 := by ring
  have e2 : 2 * Real.pi / 7 - 4 * Real.pi / 7 = -(2 * Real.pi / 7) := by ring
  rw [e1] at h1
  rw [e2, Real.cos_neg] at h2
  linarith

private theorem c7double : 2 * Real.cos (6 * Real.pi / 7) ^ 2 - 1
    = Real.cos (2 * Real.pi / 7) := by
  have h : Real.cos (2 * (6 * Real.pi / 7))
      = 2 * Real.cos (6 * Real.pi / 7) ^ 2 - 1 :=
    Real.cos_two_mul _
  rw [← h]
  have e : 2 * (6 * Real.pi / 7) = -(2 * Real.pi / 7) + 2 * Real.pi := by ring
  rw [e, Real.cos_add_two_pi, Real.cos_neg]

private theorem c7sum : Real.cos (2 * Real.pi / 7) + Real.cos (4 * Real.pi / 7)
    + Real.cos (6 * Real.pi / 7) = -1 / 2 := by
  have hs : 0 < Real.sin (Real.pi / 7) := by
    apply Real.sin_pos_of_mem_Ioo
    constructor
    · have hpi : 0 < Real.pi := Real.pi_pos
      linarith
    · have hpi : 0 < Real.pi := Real.pi_pos
      have hle : Real.pi ≤ 4 := Real.pi_le_four
      linarith
  have h1 : 2 * Real.sin (Real.pi / 7) * Real.cos (2 * Real.pi / 7)
      = Real.sin (3 * Real.pi / 7) - Real.sin (Real.pi / 7) := by
    calc 2 * Real.sin (Real.pi / 7) * Real.cos (2 * Real.pi / 7)
        = Real.sin (Real.pi / 7 + 2 * Real.pi / 7)
          - Real.sin (2 * Real.pi / 7 - Real.pi / 7) := by
            rw [Real.sin_add, Real.sin_sub]
            ring
      _ = Real.sin (3 * Real.pi / 7) - Real.sin (Real.pi / 7) := by
            rw [show Real.pi / 7 + 2 * Real.pi / 7 = 3 * Real.pi / 7 by ring,
              show 2 * Real.pi / 7 - Real.pi / 7 = Real.pi / 7 by ring]
  have h2 : 2 * Real.sin (Real.pi / 7) * Real.cos (4 * Real.pi / 7)
      = Real.sin (5 * Real.pi / 7) - Real.sin (3 * Real.pi / 7) := by
    calc 2 * Real.sin (Real.pi / 7) * Real.cos (4 * Real.pi / 7)
        = Real.sin (Real.pi / 7 + 4 * Real.pi / 7)
          - Real.sin (4 * Real.pi / 7 - Real.pi / 7) := by
            rw [Real.sin_add, Real.sin_sub]
            ring
      _ = Real.sin (5 * Real.pi / 7) - Real.sin (3 * Real.pi / 7) := by
            rw [show Real.pi / 7 + 4 * Real.pi / 7 = 5 * Real.pi / 7 by ring,
              show 4 * Real.pi / 7 - Real.pi / 7 = 3 * Real.pi / 7 by ring]
  have h3 : 2 * Real.sin (Real.pi / 7) * Real.cos (6 * Real.pi / 7)
      = Real.sin (7 * Real.pi / 7) - Real.sin (5 * Real.pi / 7) := by
    calc 2 * Real.sin (Real.pi / 7) * Real.cos (6 * Real.pi / 7)
        = Real.sin (Real.pi / 7 + 6 * Real.pi / 7)
          - Real.sin (6 * Real.pi / 7 - Real.pi / 7) := by
            rw [Real.sin_add, Real.sin_sub]
            ring
      _ = Real.sin (7 * Real.pi / 7) - Real.sin (5 * Real.pi / 7) := by
            rw [show Real.pi / 7 + 6 * Real.pi / 7 = 7 * Real.pi / 7 by ring,
              show 6 * Real.pi / 7 - Real.pi / 7 = 5 * Real.pi / 7 by ring]
  have hpi7 : 7 * Real.pi / 7 = Real.pi := by ring
  rw [hpi7, Real.sin_pi] at h3
  have hsum : 2 * Real.sin (Real.pi / 7)
      * (Real.cos (2 * Real.pi / 7) + Real.cos (4 * Real.pi / 7)
        + Real.cos (6 * Real.pi / 7))
      = -Real.sin (Real.pi / 7) := by
    linear_combination h1 + h2 + h3
  have hs_ne : Real.sin (Real.pi / 7) ≠ 0 := ne_of_gt hs
  field_simp at hsum ⊢
  linarith

private theorem c7orthA : c7h * c7h + c7w1 * Real.cos (4 * Real.pi / 7)
    + c7w2 * Real.cos (6 * Real.pi / 7) = 0 := by
  have hh := c7h_sq
  unfold c7w1 c7w2 at *
  have h1 := c7prod
  have h2 := c7double
  linear_combination h1 / 2 - h2 / 2 + hh

private theorem c7orthB : c7h * c7h + c7w1 * Real.cos (6 * Real.pi / 7)
    + c7w2 * Real.cos (2 * Real.pi / 7) = 0 := by
  have hh := c7h_sq
  unfold c7w1 c7w2 at *
  have h1 := c7prod
  have h2 := c7double
  linear_combination h1 / 2 - h2 / 2 + hh

private noncomputable def umbrellaC7 (k : Fin 7) : EuclideanSpace ℝ (Fin 5) :=
  !₂[c7h, Real.sqrt c7w1 * Real.cos (2 * Real.pi * k / 7),
    Real.sqrt c7w1 * Real.sin (2 * Real.pi * k / 7),
    Real.sqrt c7w2 * Real.cos (4 * Real.pi * k / 7),
    Real.sqrt c7w2 * Real.sin (4 * Real.pi * k / 7)]

private theorem inner_umbrellaC7 (j k : Fin 7) :
    ⟪umbrellaC7 j, umbrellaC7 k⟫ =
      c7h * c7h + c7w1 * Real.cos (2 * Real.pi * (((j : ℤ) - (k : ℤ) : ℤ) : ℝ) / 7)
        + c7w2 * Real.cos (4 * Real.pi * (((j : ℤ) - (k : ℤ) : ℤ) : ℝ) / 7) := by
  have s1 : (Real.sqrt c7w1) ^ 2 = c7w1 := Real.sq_sqrt c7w1_nonneg
  have s2 : (Real.sqrt c7w2) ^ 2 = c7w2 := Real.sq_sqrt c7w2_nonneg
  simp only [umbrellaC7, PiLp.inner_apply, Fin.sum_univ_five, RCLike.inner_apply,
    conj_trivial, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Int.cast_sub, Int.cast_natCast]
  rw [show 2 * Real.pi * ((j : ℝ) - k) / 7
      = 2 * Real.pi * j / 7 - 2 * Real.pi * k / 7 by ring, Real.cos_sub]
  rw [show 4 * Real.pi * ((j : ℝ) - k) / 7
      = 4 * Real.pi * j / 7 - 4 * Real.pi * k / 7 by ring, Real.cos_sub]
  linear_combination
    (Real.cos (2 * Real.pi * j / 7) * Real.cos (2 * Real.pi * k / 7)
      + Real.sin (2 * Real.pi * j / 7) * Real.sin (2 * Real.pi * k / 7)) * s1
    + (Real.cos (4 * Real.pi * j / 7) * Real.cos (4 * Real.pi * k / 7)
      + Real.sin (4 * Real.pi * j / 7) * Real.sin (4 * Real.pi * k / 7)) * s2

private theorem c7nonadj_diff {u v : Fin 7} (huv : u ≠ v)
    (hadj : ¬ (SimpleGraph.cycleGraph 7).Adj u v) :
    ((u : ℤ) - v) = 2 ∨ ((u : ℤ) - v) = 3 ∨ ((u : ℤ) - v) = 4 ∨ ((u : ℤ) - v) = 5 ∨
    ((u : ℤ) - v) = -2 ∨ ((u : ℤ) - v) = -3 ∨ ((u : ℤ) - v) = -4 ∨
    ((u : ℤ) - v) = -5 := by
  rw [SimpleGraph.cycleGraph_adj] at hadj
  revert u v
  decide

private theorem c7cosA {m : ℤ} (hm : m = 2 ∨ m = 5 ∨ m = -2 ∨ m = -5) :
    Real.cos (2 * Real.pi * m / 7) = Real.cos (4 * Real.pi / 7)
    ∧ Real.cos (4 * Real.pi * m / 7) = Real.cos (6 * Real.pi / 7) := by
  rcases hm with rfl | rfl | rfl | rfl
  · constructor
    · congr 1
      push_cast
      ring
    · have e : 4 * Real.pi * ((2 : ℤ) : ℝ) / 7
          = -(6 * Real.pi / 7) + 2 * Real.pi := by push_cast; ring
      rw [e, Real.cos_add_two_pi, Real.cos_neg]
  · constructor
    · have e : 2 * Real.pi * ((5 : ℤ) : ℝ) / 7
          = -(4 * Real.pi / 7) + 2 * Real.pi := by push_cast; ring
      rw [e, Real.cos_add_two_pi, Real.cos_neg]
    · have e : 4 * Real.pi * ((5 : ℤ) : ℝ) / 7
          = 6 * Real.pi / 7 + 2 * Real.pi := by push_cast; ring
      rw [e, Real.cos_add_two_pi]
  · constructor
    · have e : 2 * Real.pi * ((-2 : ℤ) : ℝ) / 7
          = -(4 * Real.pi / 7) := by push_cast; ring
      rw [e, Real.cos_neg]
    · have e : 4 * Real.pi * ((-2 : ℤ) : ℝ) / 7
          = 6 * Real.pi / 7 - 2 * Real.pi := by push_cast; ring
      rw [e, Real.cos_sub_two_pi]
  · constructor
    · have e : 2 * Real.pi * ((-5 : ℤ) : ℝ) / 7
          = 4 * Real.pi / 7 - 2 * Real.pi := by push_cast; ring
      rw [e, Real.cos_sub_two_pi]
    · have e : 4 * Real.pi * ((-5 : ℤ) : ℝ) / 7
          = -(6 * Real.pi / 7) - 2 * Real.pi := by push_cast; ring
      rw [e, Real.cos_sub_two_pi, Real.cos_neg]

private theorem c7cosB {m : ℤ} (hm : m = 3 ∨ m = 4 ∨ m = -3 ∨ m = -4) :
    Real.cos (2 * Real.pi * m / 7) = Real.cos (6 * Real.pi / 7)
    ∧ Real.cos (4 * Real.pi * m / 7) = Real.cos (2 * Real.pi / 7) := by
  rcases hm with rfl | rfl | rfl | rfl
  · constructor
    · congr 1
      push_cast
      ring
    · have e : 4 * Real.pi * ((3 : ℤ) : ℝ) / 7
          = -(2 * Real.pi / 7) + 2 * Real.pi := by push_cast; ring
      rw [e, Real.cos_add_two_pi, Real.cos_neg]
  · constructor
    · have e : 2 * Real.pi * ((4 : ℤ) : ℝ) / 7
          = -(6 * Real.pi / 7) + 2 * Real.pi := by push_cast; ring
      rw [e, Real.cos_add_two_pi, Real.cos_neg]
    · have e : 4 * Real.pi * ((4 : ℤ) : ℝ) / 7
          = 2 * Real.pi / 7 + 2 * Real.pi := by push_cast; ring
      rw [e, Real.cos_add_two_pi]
  · constructor
    · have e : 2 * Real.pi * ((-3 : ℤ) : ℝ) / 7
          = -(6 * Real.pi / 7) := by push_cast; ring
      rw [e, Real.cos_neg]
    · have e : 4 * Real.pi * ((-3 : ℤ) : ℝ) / 7
          = 2 * Real.pi / 7 - 2 * Real.pi := by push_cast; ring
      rw [e, Real.cos_sub_two_pi]
  · constructor
    · have e : 2 * Real.pi * ((-4 : ℤ) : ℝ) / 7
          = 6 * Real.pi / 7 - 2 * Real.pi := by push_cast; ring
      rw [e, Real.cos_sub_two_pi]
    · have e : 4 * Real.pi * ((-4 : ℤ) : ℝ) / 7
          = -(2 * Real.pi / 7) - 2 * Real.pi := by push_cast; ring
      rw [e, Real.cos_sub_two_pi, Real.cos_neg]

private theorem umbrellaC7_orth :
    IsOrthogonalLabeling (SimpleGraph.cycleGraph 7) umbrellaC7 := by
  intro u v huv hadj
  rw [inner_umbrellaC7]
  have hdiff := c7nonadj_diff huv hadj
  rcases hdiff with h | h | h | h | h | h | h | h
  · rw [h]
    have hc := c7cosA (Or.inl rfl)
    rw [hc.1, hc.2]
    exact c7orthA
  · rw [h]
    have hc := c7cosB (Or.inl rfl)
    rw [hc.1, hc.2]
    exact c7orthB
  · rw [h]
    have hc := c7cosB (Or.inr (Or.inl rfl))
    rw [hc.1, hc.2]
    exact c7orthB
  · rw [h]
    have hc := c7cosA (Or.inr (Or.inl rfl))
    rw [hc.1, hc.2]
    exact c7orthA
  · rw [h]
    have hc := c7cosA (Or.inr (Or.inr (Or.inl rfl)))
    rw [hc.1, hc.2]
    exact c7orthA
  · rw [h]
    have hc := c7cosB (Or.inr (Or.inr (Or.inl rfl)))
    rw [hc.1, hc.2]
    exact c7orthB
  · rw [h]
    have hc := c7cosB (Or.inr (Or.inr (Or.inr rfl)))
    rw [hc.1, hc.2]
    exact c7orthB
  · rw [h]
    have hc := c7cosA (Or.inr (Or.inr (Or.inr rfl)))
    rw [hc.1, hc.2]
    exact c7orthA

private theorem umbrellaC7_norm (v : Fin 7) :
    ‖umbrellaC7 v‖ ^ 2 = 7 * Real.cos (Real.pi / 7) / 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_umbrellaC7]
  have h0 : ((((v : ℤ) - (v : ℤ) : ℤ) : ℝ)) = 0 := by push_cast; ring
  rw [h0]
  simp only [mul_zero, zero_div, Real.cos_zero, mul_one]
  have hh := c7h_sq
  have hs := c7sum
  have hc := c7cos6
  unfold c7w1 c7w2 at *
  linear_combination hh + hs - 7 / 2 * hc

private theorem c7mem_feasible :
    c7theta ∈ thetaFeasible (SimpleGraph.cycleGraph 7) := by
  refine ⟨c7theta_nonneg, 5, umbrellaC7, EuclideanSpace.single 0 1, ?_, umbrellaC7_orth, ?_⟩
  · intro h
    have := congrArg (fun x : EuclideanSpace ℝ (Fin 5) => x 0) h
    simp at this
  · intro v
    have hin : ⟪EuclideanSpace.single 0 (1 : ℝ), umbrellaC7 v⟫ = c7h := by
      rw [EuclideanSpace.inner_single_left]
      simp [umbrellaC7]
    have hnorm := umbrellaC7_norm v
    have hsq : c7h ^ 2 = (1 - Real.cos (6 * Real.pi / 7)) / 2 := by
      rw [sq]
      exact c7h_sq
    have hcpos := c7cos_pos
    have hc6 := c7cos6
    simp only [cost, hin, hnorm, hsq, PiLp.norm_single, norm_one, one_pow, one_mul]
    unfold c7theta
    rw [hc6]
    have h1c : (0 : ℝ) < 1 + Real.cos (Real.pi / 7) := by linarith
    have hc_ne : Real.cos (Real.pi / 7) ≠ 0 := ne_of_gt hcpos
    have h1c_ne : (1 : ℝ) + Real.cos (Real.pi / 7) ≠ 0 := ne_of_gt h1c
    field_simp
    apply le_of_eq
    ring

private theorem c7theta_le :
    lovaszTheta (SimpleGraph.cycleGraph 7) ≤ c7theta :=
  csInf_le ⟨0, fun _ ht => ht.1⟩ c7mem_feasible

private theorem c7StrongPower_hyp (n : ℕ) :
    ∀ x y, x ≠ y → ¬ (strongPower (SimpleGraph.cycleGraph 7) n).Adj x y →
      ∃ i, x i ≠ y i ∧ ¬ (SimpleGraph.cycleGraph 7).Adj (x i) (y i) := by
  intro x y hxy hna
  by_contra! h
  exact hna ⟨hxy, fun i => or_iff_not_imp_left.mpr (h i)⟩

private theorem c7adj_diff (u v : Fin 7)
    (h : (SimpleGraph.cycleGraph 7).Adj u v) :
    (u : ZMod 7) - (v : ZMod 7) = 1 ∨ (u : ZMod 7) - (v : ZMod 7) = -1 := by
  revert u v
  decide

private theorem c7code_indep (n : ℕ) (A : Finset (Fin n → ZMod 7))
    (hA : IsCycleCode 7 A) :
    (strongPower (SimpleGraph.cycleGraph 7) n).IsIndepSet
      ((A : Set (Fin n → ZMod 7)) : Set (Fin n → Fin 7)) := by
  intro x hx y hy hxy hadj
  obtain ⟨hxy', hcoord⟩ := hadj
  have hx' : (x : Fin n → ZMod 7) ∈ A := hx
  have hy' : (y : Fin n → ZMod 7) ∈ A := hy
  let d : Fin n → ZMod 7 := x - y
  have hd : ∀ i, d i = -1 ∨ d i = 0 ∨ d i = 1 := by
    intro i
    rcases hcoord i with heq | hadj'
    · have heqZ : (x : Fin n → ZMod 7) i = (y : Fin n → ZMod 7) i := by
        exact_mod_cast heq
      have h0 : d i = 0 := by
        change ((x : Fin n → ZMod 7) - (y : Fin n → ZMod 7)) i = 0
        rw [Pi.sub_apply, heqZ, sub_self]
      rw [h0]
      exact Or.inr (Or.inl rfl)
    · have hdiff := c7adj_diff _ _ hadj'
      have e : d i = (x i : ZMod 7) - (y i : ZMod 7) := rfl
      rw [e]
      rcases hdiff with h1 | h1
      · exact Or.inr (Or.inr h1)
      · exact Or.inl h1
  have hex : ∃ a₁ ∈ A, ∃ a₂ ∈ A, a₁ - a₂ = d := ⟨x, hx', y, hy', rfl⟩
  have hz : d = 0 := hA d hex hd
  have hxyZ : (x : Fin n → ZMod 7) = (y : Fin n → ZMod 7) := sub_eq_zero.mp hz
  have : x = y := by exact_mod_cast hxyZ
  exact hxy this

private theorem c7rate_le (n : PositiveNat) (A : CycleCode 7 n.1) :
    cycleCodeRate 7 n A ≤ ENNReal.ofReal c7theta := by
  have hn_ne : n.1 ≠ 0 := by
    have := n.2
    omega
  have h_indep := c7code_indep n.1 A.1 A.2
  have hcard : A.1.card ≤ (strongPower (SimpleGraph.cycleGraph 7) n.1).indepNum :=
    h_indep.card_le_indepNum
  have hcast : (A.1.card : ℝ) ≤ ((strongPower (SimpleGraph.cycleGraph 7) n.1).indepNum : ℝ) :=
    Nat.cast_le.mpr hcard
  have h_theta_pow := indepNum_le_lovaszTheta_pow
    (SimpleGraph.cycleGraph 7) (c7StrongPower_hyp n.1)
  have h_pow_le : lovaszTheta (SimpleGraph.cycleGraph 7) ^ n.1 ≤ c7theta ^ n.1 :=
    pow_le_pow_left₀ (lovaszTheta_nonneg _) c7theta_le _
  have h_le : (A.1.card : ℝ) ≤ c7theta ^ n.1 :=
    calc (A.1.card : ℝ) ≤ ((strongPower (SimpleGraph.cycleGraph 7) n.1).indepNum : ℝ) := hcast
      _ ≤ lovaszTheta (SimpleGraph.cycleGraph 7) ^ n.1 := h_theta_pow
      _ ≤ c7theta ^ n.1 := h_pow_le
  have hM_nonneg : (0 : ℝ) ≤ (A.1.card : ℝ) := Nat.cast_nonneg _
  have hexp_nonneg : (0 : ℝ) ≤ ((n.1 : ℝ)⁻¹) := by positivity
  have h_rpow : Real.rpow (A.1.card : ℝ) ((n.1 : ℝ)⁻¹) ≤ c7theta := by
    calc Real.rpow (A.1.card : ℝ) ((n.1 : ℝ)⁻¹)
        ≤ Real.rpow (c7theta ^ n.1) ((n.1 : ℝ)⁻¹) :=
          Real.rpow_le_rpow hM_nonneg h_le hexp_nonneg
      _ = c7theta := Real.pow_rpow_inv_natCast c7theta_nonneg hn_ne
  have e1 : (A.1.card : ENNReal) = ENNReal.ofReal (A.1.card : ℝ) :=
    (ENNReal.ofReal_natCast _).symm
  unfold cycleCodeRate
  rw [e1]
  change (ENNReal.ofReal (A.1.card : ℝ)) ^ ((n.1 : ℝ)⁻¹) ≤ _
  rw [ENNReal.ofReal_rpow_of_nonneg hM_nonneg hexp_nonneg]
  exact ENNReal.ofReal_le_ofReal h_rpow

/-- **Lovász's theta value for the 7-cycle.** This is the real number
$\frac{7 \cos(\pi/7)}{1 + \cos(\pi/7)}$, Lovász's closed form for the theta number of the
$7$-cycle, viewed as an element of $[0, \infty]$.

Approximate decimal displays of this number in the source are not asserted as equalities.

Source: Lovász (1979), as printed in BPZ, arXiv:2607.29681. -/
noncomputable def lovaszThetaCycleSeven : ENNReal :=
  ENNReal.ofReal (7 * Real.cos (Real.pi / 7) / (1 + Real.cos (Real.pi / 7)))

/-- **Lovász's upper bound for the capacity of the 7-cycle.** The Shannon capacity of the
$7$-cycle is at most $\frac{7 \cos(\pi/7)}{1 + \cos(\pi/7)}$, as an inequality in $[0, \infty]$.

Source: Lovász (1979); the closed form is also printed in the retained BPZ primary. -/
theorem lovasz1979UpperBound :
  shannonCapacityCycle 7 ≤ lovaszThetaCycleSeven
    := by
  change shannonCapacityCycle 7 ≤ ENNReal.ofReal c7theta
  unfold shannonCapacityCycle
  apply iSup_le
  intro n
  apply iSup_le
  intro A
  exact c7rate_le n A

end MathlibExt.Combinatorics.Coding.CycleShannonBoundsWanted
