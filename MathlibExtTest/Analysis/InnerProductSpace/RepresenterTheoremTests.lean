/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.RepresenterTheorem
public import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tests for the representer theorem

Concrete checks in `EuclideanSpace ℝ (Fin 2)` with the single functional
`L 0 = ⟪e₀, ·⟫`, whose Riesz representer is `e₀ = (1, 0)`:

* projection of `(3, 4)` onto the span of the representer is `(3, 0)`
  (Pythagorean residual `(0, 4)`);
* the ridge problem `(g 0 - 1) ^ 2 + ‖g‖ ^ 2` has minimizer `(1 / 2, 0)`,
  which lies on the representer line with coefficient `1 / 2`;
* every element of the representer span has second coordinate `0`.
-/

@[expose] public section

namespace MathlibExtTest.Analysis.InnerProductSpace.RepresenterTheoremTests

open MathlibExt.Analysis.InnerProductSpace.RepresenterTheorem

noncomputable section

/-- The two-dimensional Euclidean space used in the tests. -/
private abbrev H2 : Type := EuclideanSpace ℝ (Fin 2)

/-- The first coordinate vector in `ℝ²`. -/
private abbrev e₀ : H2 := EuclideanSpace.single 0 (1 : ℝ)

/-- The second coordinate vector in `ℝ²`. -/
private abbrev e₁ : H2 := EuclideanSpace.single 1 (1 : ℝ)

/-- The single functional `L 0 = ⟪e₀, ·⟫`. -/
private abbrev L2 : Fin 1 → (H2 →L[ℝ] ℝ) :=
  fun _ => InnerProductSpace.toDual ℝ H2 e₀

/-- The functional `L2 0` is the first coordinate. -/
private theorem L2_apply (x : H2) : L2 0 x = x 0 := by
  simp [L2, InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_single_left,
    map_one, one_mul]

/-- The Riesz representers of `L2` are all `e₀`. -/
private theorem representers_eq : (fun i => (InnerProductSpace.toDual ℝ H2).symm (L2 i)) =
    fun _ => e₀ := by
  funext i
  exact LinearIsometryEquiv.symm_apply_apply _ _

/-- The squared norm on `ℝ²` is the sum of the squared coordinates. -/
private theorem norm_sq_eq (x : H2) : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _),
    Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs]

/-- Projection of `(3, 4)` onto the representer span is `(3, 0)`. -/
example : ∃ s : H2, s = (3 : ℝ) • e₀ ∧ ‖s‖ = 3 ∧
    ‖((3 : ℝ) • e₀ + (4 : ℝ) • e₁) - s‖ = 4 := by
  obtain ⟨s, hsS, hvals, hnorm⟩ :=
    exists_mem_span_norm_sq_add L2 ((3 : ℝ) • e₀ + (4 : ℝ) • e₁)
  have hg0 : ((3 : ℝ) • e₀ + (4 : ℝ) • e₁) 0 = 3 := by
    simp [PiLp.add_apply, PiLp.smul_apply]
  have hg1 : ((3 : ℝ) • e₀ + (4 : ℝ) • e₁) 1 = 4 := by
    simp [PiLp.add_apply, PiLp.smul_apply]
  have hgnorm : ‖(3 : ℝ) • e₀ + (4 : ℝ) • e₁‖ = 5 := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, hg0, hg1]
    have h25 : ‖(3 : ℝ)‖ ^ 2 + ‖(4 : ℝ)‖ ^ 2 = (5 : ℝ) ^ 2 := by
      simp only [Real.norm_ofNat]
      norm_num
    rw [h25, Real.sqrt_sq (by norm_num)]
  rw [representers_eq, Set.range_const] at hsS
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hsS
  have hts : t = 3 := by
    have h1 : (t • e₀) 0 = t := by
      simp [PiLp.smul_apply]
    rw [ht] at h1
    have h2 := hvals 0
    rw [L2_apply, L2_apply, hg0] at h2
    rw [h1] at h2
    exact h2
  have hseq : s = (3 : ℝ) • e₀ := by rw [← ht, hts]
  have hs3 : ‖s‖ = 3 := by
    rw [hseq, norm_smul, PiLp.norm_single]
    norm_num
  refine ⟨s, hseq, hs3, ?_⟩
  have h1 : ‖(3 : ℝ) • e₀ + (4 : ℝ) • e₁‖ ^ 2 = 25 := by rw [hgnorm]; norm_num
  have h2 : ‖s‖ ^ 2 = 9 := by rw [hs3]; norm_num
  have h16 : ‖((3 : ℝ) • e₀ + (4 : ℝ) • e₁) - s‖ ^ 2 = 16 := by linarith [hnorm, h1, h2]
  have hprod : (‖((3 : ℝ) • e₀ + (4 : ℝ) • e₁) - s‖ - 4) *
      (‖((3 : ℝ) • e₀ + (4 : ℝ) • e₁) - s‖ + 4) = 0 := by
    nlinarith [h16]
  rcases mul_eq_zero.mp hprod with h | h
  · linarith
  · have hnn := norm_nonneg (((3 : ℝ) • e₀ + (4 : ℝ) • e₁) - s)
    linarith

/-- The ridge minimizer `(1 / 2, 0)` lies on the representer line. -/
example : ∃ t : ℝ, ((1 / 2 : ℝ) • e₀) = t • e₀ ∧ t = 1 / 2 := by
  have hmin : IsMinOn
      (fun g : H2 => (fun v : Fin 1 → ℝ => (v 0 - 1) ^ 2) (fun i => L2 i g) +
        1 * ‖g‖ ^ 2)
      Set.univ ((1 / 2 : ℝ) • e₀) := by
    intro g _
    have hLg : L2 0 g = g 0 := L2_apply g
    have hLf : L2 0 ((1 / 2 : ℝ) • e₀) = 1 / 2 := by
      rw [L2_apply]
      simp [PiLp.smul_apply]
    have hf0 : ((1 / 2 : ℝ) • e₀) 0 = 1 / 2 := by
      simp [PiLp.smul_apply]
    have hf1 : ((1 / 2 : ℝ) • e₀) 1 = 0 := by
      simp [PiLp.smul_apply]
    show ((L2 0 ((1 / 2 : ℝ) • e₀) - 1) ^ 2 + 1 * ‖(1 / 2 : ℝ) • e₀‖ ^ 2) ≤
      ((L2 0 g - 1) ^ 2 + 1 * ‖g‖ ^ 2)
    rw [hLg, hLf, norm_sq_eq g, norm_sq_eq ((1 / 2 : ℝ) • e₀), hf0, hf1]
    nlinarith [sq_nonneg (g 0 - 1 / 2), sq_nonneg (g 1)]
  have hmem := mem_span_of_isMinOn L2 (fun v : Fin 1 → ℝ => (v 0 - 1) ^ 2)
    (Λ := 1) (by norm_num) hmin
  rw [representers_eq, Set.range_const] at hmem
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨t, ht.symm, ?_⟩
  have h0 : (t • e₀) 0 = t := by
    simp [PiLp.smul_apply]
  have h1 : ((1 / 2 : ℝ) • e₀) 0 = 1 / 2 := by
    simp [PiLp.smul_apply]
  rw [ht] at h0
  rw [h1] at h0
  exact h0.symm

/-- Every element of the representer span has second coordinate `0`. -/
example : ∀ s ∈ Submodule.span ℝ
    (Set.range fun i => (InnerProductSpace.toDual ℝ H2).symm (L2 i)), s 1 = 0 := by
  intro s hs
  rw [representers_eq, Set.range_const] at hs
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hs
  rw [← ht]
  simp [PiLp.smul_apply]

end

end MathlibExtTest.Analysis.InnerProductSpace.RepresenterTheoremTests
