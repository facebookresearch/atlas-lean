/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_LanglandsTunnell_Converse_ArchDatumR_exists_lincomb.lean`,
`Definitions/Def_LanglandsTunnell_JLConverse.lean`
and
`P2M/Sol/S_LanglandsTunnell_Converse_ArchDatumR_exists_lincomb.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib - https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.Analysis.MellinArchDatum

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Separation.Hausdorff

/-!
# Linear combinations of real archimedean Whittaker data

A complex linear combination of the Whittaker functions of two real archimedean
Whittaker data for the same parameter is again the Whittaker function of such a datum:
every defining law, the zeta data and the decay bounds are stable under linear
combinations.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory

namespace LanglandsTunnell.Converse

open ArchR

namespace ArchDatumR

private theorem isK_det_ne_zero {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : IsK k) : k.det ≠ 0 := by
  have h := congrArg Matrix.det ((Matrix.mem_orthogonalGroup_iff _ _).mp hk)
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact left_ne_zero_of_mul_eq_one h

private theorem continuous_detCoord :
    Continuous (fun m : Fin 2 → Fin 2 → ℝ => (Matrix.of m).det) := by
  simp only [Matrix.det_fin_two, Matrix.of_apply]
  fun_prop

private theorem isOpen_glSet : IsOpen glSet :=
  isOpen_ne_fun continuous_detCoord continuous_const

private theorem det_of_diagOneMulCoords (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ) :
    (Matrix.of (diagOneMulCoords y k)).det = y * k.det := by
  have h : Matrix.of (diagOneMulCoords y k) = diagOne y * k := Matrix.of.apply_symm_apply _
  rw [h, Matrix.det_mul]
  simp [diagOne, Matrix.det_fin_two_of]

private theorem diagOneMulCoords_mem_glSet {y : ℝ} (hy : y ≠ 0)
    {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : IsK k) : diagOneMulCoords y k ∈ glSet := by
  change (Matrix.of (diagOneMulCoords y k)).det ≠ 0
  rw [det_of_diagOneMulCoords]
  exact mul_ne_zero hy (isK_det_ne_zero hk)

variable {P : RealArchParam}

private theorem asPi_lincomb (c₁ c₂ : ℂ) (W₁ W₂ : Matrix (Fin 2) (Fin 2) ℝ → ℂ) :
    asPi (fun g => c₁ * W₁ g + c₂ * W₂ g) = c₁ • asPi W₁ + c₂ • asPi W₂ := rfl

private theorem zetaIntegrand_lincomb (c₁ c₂ : ℂ) (W₁ W₂ : Matrix (Fin 2) (Fin 2) ℝ → ℂ)
    (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ) (a : ZMod 2) (s : ℂ) :
    zetaIntegrand (fun g => c₁ * W₁ g + c₂ * W₂ g) g u a s
      = fun y => c₁ * zetaIntegrand W₁ g u a s y + c₂ * zetaIntegrand W₂ g u a s y := by
  funext y
  simp only [zetaIntegrand]
  ring

private def lincomb (c₁ c₂ : ℂ) (D₁ D₂ : ArchDatumR P) : ArchDatumR P where
  W g := c₁ * D₁.W g + c₂ * D₂.W g
  smooth := by
    rw [asPi_lincomb]
    exact (D₁.smooth.const_smul c₁).add (D₂.smooth.const_smul c₂)
  unip_law x g := by
    simp only [D₁.unip_law, D₂.unip_law]
    ring
  central_law z g hz := by
    simp only [D₁.central_law z g hz, D₂.central_law z g hz]
    ring
  zetaEntire g u a s := c₁ * D₁.zetaEntire g u a s + c₂ * D₂.zetaEntire g u a s
  zetaEntire_differentiable g u a :=
    ((D₁.zetaEntire_differentiable g u a).const_mul c₁).add
      ((D₂.zetaEntire_differentiable g u a).const_mul c₂)
  zeta_abscissa := max D₁.zeta_abscissa D₂.zeta_abscissa
  zeta_integrable g u a s hg hs := by
    rw [zetaIntegrand_lincomb]
    exact ((D₁.zeta_integrable g u a s hg ((le_max_left _ _).trans_lt hs)).const_mul c₁).add
      ((D₂.zeta_integrable g u a s hg ((le_max_right _ _).trans_lt hs)).const_mul c₂)
  zeta_eq g u a s hg hs := by
    have h₁ := D₁.zeta_integrable g u a s hg ((le_max_left _ _).trans_lt hs)
    have h₂ := D₂.zeta_integrable g u a s hg ((le_max_right _ _).trans_lt hs)
    rw [zetaIntegrand_lincomb, integral_add (h₁.const_mul c₁) (h₂.const_mul c₂),
      integral_const_mul, integral_const_mul,
      D₁.zeta_eq g u a s hg ((le_max_left _ _).trans_lt hs),
      D₂.zeta_eq g u a s hg ((le_max_right _ _).trans_lt hs)]
    ring
  functional_equation g u a s hg := by
    simp only [D₁.functional_equation g u a s hg, D₂.functional_equation g u a s hg]
    ring
  zetaEntire_finiteOrder g u a A B := by
    obtain ⟨C₁, E₁, h₁⟩ := D₁.zetaEntire_finiteOrder g u a A B
    obtain ⟨C₂, E₂, h₂⟩ := D₂.zetaEntire_finiteOrder g u a A B
    refine ⟨‖c₁‖ * |C₁| + ‖c₂‖ * |C₂|, |E₁| + |E₂|, fun s hA hB => ?_⟩
    have e₁ : Real.exp (E₁ * |s.im|) ≤ Real.exp ((|E₁| + |E₂|) * |s.im|) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        (by linarith [le_abs_self E₁, abs_nonneg E₂]) (abs_nonneg _))
    have e₂ : Real.exp (E₂ * |s.im|) ≤ Real.exp ((|E₁| + |E₂|) * |s.im|) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        (by linarith [le_abs_self E₂, abs_nonneg E₁]) (abs_nonneg _))
    have b₁ : ‖D₁.zetaEntire g u a s‖ ≤ |C₁| * Real.exp ((|E₁| + |E₂|) * |s.im|) :=
      (h₁ s hA hB).trans (mul_le_mul (le_abs_self C₁) e₁ (Real.exp_pos _).le (abs_nonneg _))
    have b₂ : ‖D₂.zetaEntire g u a s‖ ≤ |C₂| * Real.exp ((|E₁| + |E₂|) * |s.im|) :=
      (h₂ s hA hB).trans (mul_le_mul (le_abs_self C₂) e₂ (Real.exp_pos _).le (abs_nonneg _))
    calc ‖c₁ * D₁.zetaEntire g u a s + c₂ * D₂.zetaEntire g u a s‖
        ≤ ‖c₁‖ * ‖D₁.zetaEntire g u a s‖ + ‖c₂‖ * ‖D₂.zetaEntire g u a s‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ ‖c₁‖ * (|C₁| * Real.exp ((|E₁| + |E₂|) * |s.im|))
            + ‖c₂‖ * (|C₂| * Real.exp ((|E₁| + |E₂|) * |s.im|)) :=
          add_le_add (mul_le_mul_of_nonneg_left b₁ (norm_nonneg _))
            (mul_le_mul_of_nonneg_left b₂ (norm_nonneg _))
      _ = (‖c₁‖ * |C₁| + ‖c₂‖ * |C₂|) * Real.exp ((|E₁| + |E₂|) * |s.im|) := by ring
  decay_top j N := by
    obtain ⟨C₁, h₁⟩ := D₁.decay_top j N
    obtain ⟨C₂, h₂⟩ := D₂.decay_top j N
    refine ⟨‖c₁‖ * C₁ + ‖c₂‖ * C₂, fun y k hk hy => ?_⟩
    have hy0 : y ≠ 0 := fun h0 => by rw [h0, abs_zero] at hy; exact absurd hy (by norm_num)
    have hq : diagOneMulCoords y k ∈ glSet := diagOneMulCoords_mem_glSet hy0 hk
    have hu : UniqueDiffOn ℝ glSet := isOpen_glSet.uniqueDiffOn
    rw [asPi_lincomb, iteratedFDerivWithin_add_apply (f := c₁ • asPi D₁.W)
        (g := c₂ • asPi D₂.W)
        (((D₁.smooth.const_smul c₁) _ hq).of_le (by exact_mod_cast le_top))
        (((D₂.smooth.const_smul c₂) _ hq).of_le (by exact_mod_cast le_top)) hu hq,
      iteratedFDerivWithin_const_smul_apply
        ((D₁.smooth _ hq).of_le (by exact_mod_cast le_top)) hu hq,
      iteratedFDerivWithin_const_smul_apply
        ((D₂.smooth _ hq).of_le (by exact_mod_cast le_top)) hu hq]
    calc ‖c₁ • iteratedFDerivWithin ℝ j (asPi D₁.W) glSet (diagOneMulCoords y k)
            + c₂ • iteratedFDerivWithin ℝ j (asPi D₂.W) glSet (diagOneMulCoords y k)‖
        ≤ ‖c₁‖ * ‖iteratedFDerivWithin ℝ j (asPi D₁.W) glSet (diagOneMulCoords y k)‖
            + ‖c₂‖ * ‖iteratedFDerivWithin ℝ j (asPi D₂.W) glSet (diagOneMulCoords y k)‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul]
      _ ≤ ‖c₁‖ * (C₁ * |y| ^ (-(N : ℝ))) + ‖c₂‖ * (C₂ * |y| ^ (-(N : ℝ))) :=
          add_le_add (mul_le_mul_of_nonneg_left (h₁ y k hk hy) (norm_nonneg _))
            (mul_le_mul_of_nonneg_left (h₂ y k hk hy) (norm_nonneg _))
      _ = (‖c₁‖ * C₁ + ‖c₂‖ * C₂) * |y| ^ (-(N : ℝ)) := by ring
  decay_zero j := by
    obtain ⟨C₁, σ₁, h₁⟩ := D₁.decay_zero j
    obtain ⟨C₂, σ₂, h₂⟩ := D₂.decay_zero j
    refine ⟨‖c₁‖ * |C₁| + ‖c₂‖ * |C₂|, max σ₁ σ₂, fun y k hk hy hy1 => ?_⟩
    have hq : diagOneMulCoords y k ∈ glSet := diagOneMulCoords_mem_glSet hy hk
    have hu : UniqueDiffOn ℝ glSet := isOpen_glSet.uniqueDiffOn
    have hypos : 0 < |y| := abs_pos.mpr hy
    have r₁ : |y| ^ (-σ₁) ≤ |y| ^ (-(max σ₁ σ₂)) :=
      Real.rpow_le_rpow_of_exponent_ge hypos hy1 (neg_le_neg (le_max_left _ _))
    have r₂ : |y| ^ (-σ₂) ≤ |y| ^ (-(max σ₁ σ₂)) :=
      Real.rpow_le_rpow_of_exponent_ge hypos hy1 (neg_le_neg (le_max_right _ _))
    have b₁ : ‖iteratedFDerivWithin ℝ j (asPi D₁.W) glSet (diagOneMulCoords y k)‖
        ≤ |C₁| * |y| ^ (-(max σ₁ σ₂)) :=
      (h₁ y k hk hy hy1).trans
        (mul_le_mul (le_abs_self C₁) r₁ (Real.rpow_nonneg hypos.le _) (abs_nonneg _))
    have b₂ : ‖iteratedFDerivWithin ℝ j (asPi D₂.W) glSet (diagOneMulCoords y k)‖
        ≤ |C₂| * |y| ^ (-(max σ₁ σ₂)) :=
      (h₂ y k hk hy hy1).trans
        (mul_le_mul (le_abs_self C₂) r₂ (Real.rpow_nonneg hypos.le _) (abs_nonneg _))
    rw [asPi_lincomb, iteratedFDerivWithin_add_apply (f := c₁ • asPi D₁.W)
        (g := c₂ • asPi D₂.W)
        (((D₁.smooth.const_smul c₁) _ hq).of_le (by exact_mod_cast le_top))
        (((D₂.smooth.const_smul c₂) _ hq).of_le (by exact_mod_cast le_top)) hu hq,
      iteratedFDerivWithin_const_smul_apply
        ((D₁.smooth _ hq).of_le (by exact_mod_cast le_top)) hu hq,
      iteratedFDerivWithin_const_smul_apply
        ((D₂.smooth _ hq).of_le (by exact_mod_cast le_top)) hu hq]
    calc ‖c₁ • iteratedFDerivWithin ℝ j (asPi D₁.W) glSet (diagOneMulCoords y k)
            + c₂ • iteratedFDerivWithin ℝ j (asPi D₂.W) glSet (diagOneMulCoords y k)‖
        ≤ ‖c₁‖ * ‖iteratedFDerivWithin ℝ j (asPi D₁.W) glSet (diagOneMulCoords y k)‖
            + ‖c₂‖ * ‖iteratedFDerivWithin ℝ j (asPi D₂.W) glSet (diagOneMulCoords y k)‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul]
      _ ≤ ‖c₁‖ * (|C₁| * |y| ^ (-(max σ₁ σ₂))) + ‖c₂‖ * (|C₂| * |y| ^ (-(max σ₁ σ₂))) :=
          add_le_add (mul_le_mul_of_nonneg_left b₁ (norm_nonneg _))
            (mul_le_mul_of_nonneg_left b₂ (norm_nonneg _))
      _ = (‖c₁‖ * |C₁| + ‖c₂‖ * |C₂|) * |y| ^ (-(max σ₁ σ₂)) := by ring

private theorem lincomb_W (c₁ c₂ : ℂ) (D₁ D₂ : ArchDatumR P) (g : Matrix (Fin 2) (Fin 2) ℝ) :
    (lincomb c₁ c₂ D₁ D₂).W g = c₁ * D₁.W g + c₂ * D₂.W g := rfl

/-- A complex linear combination of the Whittaker functions of two real archimedean
Whittaker data for the same parameter is the Whittaker function of a real archimedean
Whittaker datum for that parameter. -/
public theorem exists_lincomb (D₁ D₂ : ArchDatumR P) (c₁ c₂ : ℂ) :
    ∃ D : ArchDatumR P, D.W = fun g => c₁ * D₁.W g + c₂ * D₂.W g :=
  ⟨lincomb c₁ c₂ D₁ D₂, funext fun g => lincomb_W c₁ c₂ D₁ D₂ g⟩

end ArchDatumR

end LanglandsTunnell.Converse
