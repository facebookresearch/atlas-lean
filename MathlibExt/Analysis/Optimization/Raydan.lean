/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Optimization.BarzilaiBorwein
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Raydan's convergence theorem

The gradients of the Barzilai–Borwein iteration on a positive definite quadratic converge
to zero. In an orthonormal eigenbasis, we bound their squared components by geometric
sequences, working from the smallest eigenvalue up.
-/

public section

namespace WantedExt.Analysis.Optimization.BarzilaiBorweinWanted

open scoped RealInnerProductSpace
open Filter Topology MathlibExt.Analysis.Optimization.BarzilaiBorwein

-- A step that would amplify a component with eigenvalue μ i can occur only when
-- the previous gradient had substantial mass at smaller eigenvalues.
private lemma mass_of_large_step {n : ℕ} {μ e : Fin n → ℝ} {a : ℝ}
    (hμ : Antitone μ) (hpos : ∀ j, 0 ≤ μ j) (he : ∀ j, 0 ≤ e j) (ha : 0 ≤ a)
    (hbalance : a * (∑ j, μ j * e j) = ∑ j, e j)
    (i : Fin n) (hlarge : 3 / 2 < a * μ i) :
    e i ≤ 2 * ∑ j with i < j, e j := by
  have hterm (j : Fin n) : (1 - a * μ j) * e j ≤
      (if i < j then e j else 0) - (if j = i then e j / 2 else 0) := by
    rcases lt_trichotomy j i with hj | rfl | hj
    · simp only [not_lt.mpr hj.le, ite_false, hj.ne, sub_zero]
      have := mul_le_mul_of_nonneg_left (hμ hj.le) ha
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (he j)
    · simp only [lt_irrefl, ite_false, ite_true, zero_sub]
      nlinarith [mul_nonneg (show 0 ≤ a * μ j - 3 / 2 by linarith) (he j)]
    · simp only [hj, ite_true, hj.ne', ite_false, sub_zero]
      nlinarith [mul_nonneg (mul_nonneg ha (hpos j)) (he j)]
  have h := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hterm j
  simp_rw [sub_mul, one_mul, mul_assoc] at h
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hbalance, sub_self,
    Finset.sum_sub_distrib, ← Finset.sum_filter] at h
  simp at h
  linarith

-- A component either contracts in the current step or is bounded by a geometric
-- estimate from two steps earlier. Both estimates give the same geometric rate.
private lemma geometric_of_two_steps {u : ℕ → ℝ} {r D : ℝ} (hr : 0 < r)
    (h : ∀ k, u (k + 2) ≤ r * u (k + 1) ∨ u (k + 2) ≤ D * r ^ k) :
    ∃ C, ∀ k, u k ≤ C * r ^ k := by
  let C := max (u 0) (max (u 1 / r) (D / r ^ 2))
  have h₁ : u 1 ≤ C * r := (div_le_iff₀ hr).mp <|
    (le_max_left ..).trans (le_max_right ..)
  have hD : D ≤ C * r ^ 2 := (div_le_iff₀ (sq_pos_of_pos hr)).mp <|
    (le_max_right ..).trans (le_max_right ..)
  refine ⟨C, fun k => ?_⟩
  induction k with
  | zero => simp [C]
  | succ k ih =>
    cases k with
    | zero => simpa using h₁
    | succ k =>
      rcases h k with hc | hb
      · calc
          _ ≤ r * (C * r ^ (k + 1)) := hc.trans (mul_le_mul_of_nonneg_left ih hr.le)
          _ = _ := by ring
      · calc
          _ ≤ (C * r ^ 2) * r ^ k := hb.trans (mul_le_mul_of_nonneg_right hD (by positivity))
          _ = _ := by ring

private lemma step_bounds {n : ℕ} {μ e : Fin n → ℝ} {m L a : ℝ}
    (hm : 0 < m) (hL : 0 < L) (hlower : ∀ i, m ≤ μ i) (hupper : ∀ i, μ i ≤ L)
    (he : ∀ i, 0 ≤ e i) (hsum : 0 < ∑ i, e i) (ha : 0 ≤ a)
    (hbalance : a * (∑ i, μ i * e i) = ∑ i, e i) :
    1 / L ≤ a ∧ a ≤ 1 / m := by
  have h₁ : m * (∑ i, e i) ≤ ∑ i, μ i * e i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hlower i) (he i)
  have h₂ : ∑ i, μ i * e i ≤ L * (∑ i, e i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hupper i) (he i)
  constructor
  · apply (div_le_iff₀ hL).mpr
    apply le_of_mul_le_mul_right (a := ∑ i, e i) _ hsum
    simpa only [one_mul, mul_assoc] using
      hbalance.ge.trans (mul_le_mul_of_nonneg_left h₂ ha)
  · apply (le_div_iff₀ hm).mpr
    apply le_of_mul_le_mul_right (a := ∑ i, e i) _ hsum
    simpa only [one_mul, mul_assoc] using
      (mul_le_mul_of_nonneg_left h₁ ha).trans hbalance.le

private lemma component_tendsto_zero {n : ℕ} {μ : Fin n → ℝ} {e : ℕ → Fin n → ℝ}
    {α : ℕ → ℝ} (hμ : Antitone μ) (hpos : ∀ i, 0 < μ i) (he : ∀ k i, 0 ≤ e k i)
    (hsum : ∀ k, 0 < ∑ i, e k i) (ha : ∀ k, 0 < α k)
    (hrec : ∀ k i, e (k + 1) i = (1 - α k * μ i) ^ 2 * e k i)
    (hbalance : ∀ k, α (k + 1) * (∑ i, μ i * e k i) = ∑ i, e k i) (i : Fin n) :
    Tendsto (fun k => e k i) atTop (𝓝 0) := by
  obtain ⟨lo, _, hmin⟩ := Finset.univ.exists_min_image μ ⟨i, Finset.mem_univ _⟩
  obtain ⟨hi, _, hmax⟩ := Finset.univ.exists_max_image μ ⟨i, Finset.mem_univ _⟩
  let m := μ lo
  let L := μ hi
  have hm : 0 < m := hpos lo
  have hL : 0 < L := hpos hi
  have hb k := step_bounds hm hL (fun j => hmin j (Finset.mem_univ j))
    (fun j => hmax j (Finset.mem_univ j)) (he k) (hsum k) (ha (k + 1)).le (hbalance k)
  let r := max (1 / 2 : ℝ) (1 - m / L)
  have hr : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (le_max_left ..)
  have hr₁ : r < 1 := max_lt (by norm_num) (by linarith [div_pos hm hL])
  let B := 1 + max (α 0) (1 / m) * L
  have hB (k j) : (1 - α k * μ j) ^ 2 ≤ B ^ 2 := by
    have hak : α k ≤ max (α 0) (1 / m) := by
      cases k with
      | zero => exact le_max_left ..
      | succ k => exact (hb k).2.trans (le_max_right ..)
    have hprod := mul_le_mul hak (hmax j (Finset.mem_univ j)) (hpos j).le
      ((ha k).le.trans hak)
    dsimp [B]
    apply sq_le_sq' <;> linarith [mul_pos (ha k) (hpos j)]
  have hgrowth k j : e (k + 1) j ≤ B ^ 2 * e k j := by
    rw [hrec]
    exact mul_le_mul_of_nonneg_right (hB k j) (he k j)
  suffices hgeom : ∀ j, ∃ C : ℝ, ∀ k, e k j ≤ C * r ^ k by
    obtain ⟨C, hC⟩ := hgeom i
    apply squeeze_zero (fun k => he k i) hC
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr₁).const_mul C
  intro j
  induction j using (wellFounded_gt (α := Fin n)).induction with
  | h j ih =>
    choose! C hC using ih
    let S := ∑ l with j < l, C l
    have hsmall k : ∑ l with j < l, e k l ≤ S * r ^ k := by
      dsimp [S]
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun l hl => hC l (Finset.mem_filter.mp hl).2 k
    apply geometric_of_two_steps hr (D := B ^ 2 * (B ^ 2 * (2 * S)))
    intro k
    by_cases h : α (k + 1) * μ j ≤ 3 / 2
    · left
      have hlow : m / L ≤ α (k + 1) * μ j := by
        rw [div_eq_inv_mul]
        apply mul_le_mul _ (hmin j (Finset.mem_univ j)) hm.le (ha _).le
        simpa only [one_div] using (hb k).1
      have hc : (1 - α (k + 1) * μ j) ^ 2 ≤ r ^ 2 := sq_le_sq'
        (by linarith [show 1 / 2 ≤ r from le_max_left ..])
        (by linarith [show 1 - m / L ≤ r from le_max_right ..])
      rw [hrec (k + 1)]
      have hr₂ : r ^ 2 ≤ r := by nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hr₁.le)]
      exact mul_le_mul_of_nonneg_right (hc.trans hr₂) (he _ _)
    · right
      have hj := mass_of_large_step hμ (fun l => (hpos l).le) (he k)
        (ha (k + 1)).le (hbalance k) j (lt_of_not_ge h)
      calc
        e (k + 2) j ≤ B ^ 2 * e (k + 1) j := hgrowth _ _
        _ ≤ B ^ 2 * (B ^ 2 * e k j) := by gcongr; exact hgrowth _ _
        _ ≤ B ^ 2 * (B ^ 2 * (2 * (S * r ^ k))) := by
          gcongr
          exact hj.trans (mul_le_mul_of_nonneg_left (hsmall k) (by norm_num))
        _ = _ := by ring

/-- **Raydan's theorem.** Let `A` be a symmetric positive definite operator on a
finite-dimensional real inner product space and `f(x) = ½ ⟪A x, x⟫ - ⟪b, x⟫`, with gradient
`A x - b`. Run the two-point step-size gradient method `x (k + 1) = x k - α k • (A (x k) - b)`
from any `x 0`, with any `α 0 > 0` and the Barzilai–Borwein step
`α (k + 1) = ‖s‖² / ⟪s, y⟫`, `s = x (k + 1) - x k`, `y = (A (x (k + 1)) - b) - (A (x k) - b)`.
Then the gradients converge to zero, i.e. `x k` converges to the minimiser `A⁻¹ b`.

M. Raydan, *On the Barzilai and Borwein choice of steplength for the gradient method*, IMA J.
Numer. Anal. 13 (1993), 321-326, as reported in Section 1 of Y. H. Dai, J. Y. Yuan and Y. Yuan,
Comput. Optim. Appl. 22 (2002), 103-109. (If some gradient vanishes, the iterates stop moving, and
the conclusion holds trivially.) -/
theorem raydan_tendsto_gradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {A : E →L[ℝ] E} (hsymm : ∀ u v, ⟪A u, v⟫ = ⟪u, A v⟫)
    (hpos : ∀ v, v ≠ 0 → 0 < ⟪A v, v⟫) (b : E) {x : ℕ → E} {α : ℕ → ℝ} (hα0 : 0 < α 0)
    (hx : ∀ k, x (k + 1) = x k - α k • (A (x k) - b))
    (hα : ∀ k, α (k + 1) = bbStep (x (k + 1) - x k) ((A (x (k + 1)) - b) - (A (x k) - b))) :
    Tendsto (fun k => A (x k) - b) atTop (𝓝 0) := by
  classical
  let g k := A (x k) - b
  change Tendsto g atTop (𝓝 0)
  have hg k : g (k + 1) = g k - α k • A (g k) := by
    dsimp [g]
    rw [hx, map_sub, map_smul]
    abel
  by_cases hz : ∃ k, g k = 0
  · obtain ⟨k, hk⟩ := hz
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop k] with l hl
    symm
    induction l, hl using Nat.le_induction with
    | base => exact hk
    | succ t _ ht => rw [hg, ht]; simp
  push Not at hz
  have hden k : 0 < ⟪g k, A (g k)⟫ := by
    rw [real_inner_comm]
    exact hpos _ (hz k)
  have hstep k (ha : α k ≠ 0) : α (k + 1) = ‖g k‖ ^ 2 / ⟪g k, A (g k)⟫ := by
    have hs : x (k + 1) - x k = (-α k) • g k := by rw [hx, sub_sub_cancel_left, neg_smul]
    rw [hα, sub_sub_sub_cancel_right, ← map_sub, hs, bbStep, map_smul, norm_smul,
      real_inner_smul_left, real_inner_smul_right, Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp [ha, (hden k).ne']
  have ha k : 0 < α k := by
    induction k with
    | zero => exact hα0
    | succ k ih =>
      rw [hstep k ih.ne']
      exact div_pos (sq_pos_of_pos (norm_pos_iff.mpr (hz k))) (hden k)
  let T := A.toLinearMap
  have hT : T.IsSymmetric := hsymm
  let n := Module.finrank ℝ E
  let μ : Fin n → ℝ := hT.eigenvalues rfl
  let v : OrthonormalBasis (Fin n) ℝ E := hT.eigenvectorBasis rfl
  have hv i : A (v i) = μ i • v i := hT.apply_eigenvectorBasis rfl i
  have hμ i : 0 < μ i := by
    have h := hpos (v i) (v.toBasis.ne_zero i)
    simpa [hv, real_inner_smul_left, real_inner_self_eq_norm_sq, v.orthonormal.norm_eq_one]
      using h
  have hdiag i (z : E) : ⟪v i, A z⟫ = μ i * ⟪v i, z⟫ := by
    rw [← hsymm, hv, real_inner_smul_left]
  let e k i := ⟪v i, g k⟫ ^ 2
  have hnorm k : ∑ i, e k i = ‖g k‖ ^ 2 := v.sum_sq_inner_right _
  have hquad k : ∑ i, μ i * e k i = ⟪g k, A (g k)⟫ := by
    rw [← v.sum_inner_mul_inner (g k) (A (g k))]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm (v i) (g k), hdiag]
    dsimp [e]
    ring
  have hrec k i : e (k + 1) i = (1 - α k * μ i) ^ 2 * e k i := by
    dsimp only [e]
    rw [hg, inner_sub_right, real_inner_smul_right, hdiag]
    ring
  have hbalance k : α (k + 1) * (∑ i, μ i * e k i) = ∑ i, e k i := by
    rw [hquad, hnorm, hstep k (ha k).ne', div_mul_cancel₀ _ (hden k).ne']
  have hlim i : Tendsto (fun k => e k i) atTop (𝓝 0) :=
    component_tendsto_zero (hT.eigenvalues_antitone rfl) hμ (fun k j => sq_nonneg ⟪v j, g k⟫)
      (fun k => (hnorm k).symm ▸ sq_pos_of_pos (norm_pos_iff.mpr (hz k))) ha hrec hbalance i
  have hsq : Tendsto (fun k => ‖g k‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hnorm, Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun i _ => hlim i)
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa using hsq.sqrt)

end WantedExt.Analysis.Optimization.BarzilaiBorweinWanted
