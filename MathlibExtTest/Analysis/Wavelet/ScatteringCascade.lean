/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Wavelet.ScatteringCascade
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Tests for scattering cascades

A one-dimensional layer with a modulus nonlinearity, `A f = (3/5) f` and `U f = (4/5) |f|`,
preserves energy and is nonexpansive, so both hypotheses of the cascade theorems are
satisfiable by a nonlinear layer.
-/

open scoped ENNReal
open MathlibExt.Analysis.Wavelet.ScatteringCascade

namespace MathlibExtTest.Analysis.Wavelet.ScatteringCascade

private lemma sq_ofReal_abs (x : ℝ) : ENNReal.ofReal |x| ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [← ENNReal.ofReal_pow (abs_nonneg x), sq_abs]

/-- The modulus layer preserves energy. -/
theorem layer_energy (f : ℝ) :
    ‖(3 / 5 : ℝ) * f‖ₑ ^ 2 + ∑' _ : Unit, ‖(4 / 5 : ℝ) * |f|‖ₑ ^ 2 = ‖f‖ₑ ^ 2 := by
  simp only [tsum_fintype, Finset.univ_unique, Finset.sum_singleton,
    Real.enorm_eq_ofReal_abs, sq_ofReal_abs]
  rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  congr 1
  rw [mul_pow, mul_pow, sq_abs]
  ring

/-- The modulus layer is nonexpansive. -/
theorem layer_nonexpansive (f h : ℝ) :
    edist ((3 / 5 : ℝ) * f) ((3 / 5 : ℝ) * h) ^ 2 +
        ∑' _ : Unit, edist ((4 / 5 : ℝ) * |f|) ((4 / 5 : ℝ) * |h|) ^ 2 ≤ edist f h ^ 2 := by
  simp only [tsum_fintype, Finset.univ_unique, Finset.sum_singleton, edist_dist,
    Real.dist_eq]
  rw [← ENNReal.ofReal_pow (abs_nonneg _), ← ENNReal.ofReal_pow (abs_nonneg _),
    ← ENNReal.ofReal_pow (abs_nonneg _), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hmod : |(|f| - |h|)| ≤ |f - h| := abs_abs_sub_abs_le_abs_sub f h
  have hsq : (|f| - |h|) ^ 2 ≤ (f - h) ^ 2 := by
    rw [← sq_abs (|f| - |h|), ← sq_abs (f - h)]
    exact pow_le_pow_left₀ (abs_nonneg _) hmod 2
  rw [sq_abs, sq_abs, sq_abs, ← mul_sub, ← mul_sub, mul_pow, mul_pow]
  nlinarith [sq_nonneg (f - h)]

/-- Proposition 2.5 applied to the modulus layer. -/
example (f h : ℝ) :
    ∑' p : (Σ n, Fin n → Unit),
        edist ((3 / 5 : ℝ) * propagator (fun _ x => (4 / 5 : ℝ) * |x|) p.2 f)
          ((3 / 5 : ℝ) * propagator (fun _ x => (4 / 5 : ℝ) * |x|) p.2 h) ^ 2 ≤
      edist f h ^ 2 :=
  tsum_edist_sq_le (fun x : ℝ => (3 / 5 : ℝ) * x) (fun (_ : Unit) x => (4 / 5 : ℝ) * |x|)
    layer_nonexpansive f h

/-- The energy identity (34) at depth `2` for the modulus layer. -/
example (f : ℝ) :
    ∑ n ∈ Finset.range 2, ∑' p : Fin n → Unit,
        ‖(3 / 5 : ℝ) * propagator (fun _ x => (4 / 5 : ℝ) * |x|) p f‖ₑ ^ 2 +
      ∑' p : Fin 2 → Unit, ‖propagator (fun _ x => (4 / 5 : ℝ) * |x|) p f‖ₑ ^ 2 =
      ‖f‖ₑ ^ 2 :=
  sum_enorm_sq_eq (fun x : ℝ => (3 / 5 : ℝ) * x) (fun (_ : Unit) x => (4 / 5 : ℝ) * |x|)
    layer_energy 2 f

/-- A propagator along a path of length two applies the first index first. -/
example : propagator (fun (b : Bool) (x : ℝ) => if b then 2 * x else x + 1) ![true, false] 3 =
    7 := by
  simp [propagator, Fin.tail]
  norm_num

end MathlibExtTest.Analysis.Wavelet.ScatteringCascade
