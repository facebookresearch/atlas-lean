/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Polynomial
import Mathlib.FieldTheory.Finite.Basic

open MeasureTheory MvPolynomial

-- The original source signature, including every topological assumption.
example (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [LocallyCompactSpace F] [T2Space F] [SecondCountableTopology F]
    [MeasurableSpace F] [BorelSpace F] (hF : ¬ DiscreteTopology F)
    (ι : Type) [Fintype ι] (p : MvPolynomial ι F) (hp : p ≠ 0)
    (μ : Measure (ι → F)) [μ.IsAddHaarMeasure] :
    μ {x : ι → F | eval x p = 0} = 0 :=
  measure_setOf_eval_eq_zero_of_ne_zero F hF ι p hp μ

-- No nonempty-variable assumption: even an atomic Haar measure is allowed here.
example (μ : Measure (Empty → ℝ)) [μ.IsAddHaarMeasure] :
    μ {x | eval x (1 : MvPolynomial Empty ℝ) = 0} = 0 := by
  apply measure_setOf_eval_eq_zero_of_ne_zero ℝ _ Empty _ one_ne_zero μ
  intro h
  have := @DenselyOrdered.subsingleton_of_discreteTopology ℝ _ _ _ _ h
  exact zero_ne_one (Subsingleton.elim (0 : ℝ) 1)

-- A nonconstant polynomial with an infinite zero set, not a finite-set shortcut.
private theorem real_hyperbola_null (μ : Measure (Fin 2 → ℝ))
    [μ.IsAddHaarMeasure] : μ {x | x 0 * x 1 - 1 = 0} = 0 := by
  have hp : (X (0 : Fin 2) * X 1 - 1 : MvPolynomial (Fin 2) ℝ) ≠ 0 := by
    intro h
    have := congrArg (eval (fun _ => (0 : ℝ))) h
    norm_num at this
  have hR : ¬ DiscreteTopology ℝ := by
    intro h
    have := @DenselyOrdered.subsingleton_of_discreteTopology ℝ _ _ _ _ h
    exact zero_ne_one (Subsingleton.elim (0 : ℝ) 1)
  simpa using measure_setOf_eval_eq_zero_of_ne_zero ℝ hR (Fin 2)
    (X 0 * X 1 - 1) hp μ

-- Consume nullity as almost-everywhere nondegeneracy.
example (μ : Measure (Fin 2 → ℝ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ x ∂μ, x 0 * x 1 ≠ 1 := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (real_hyperbola_null μ)] with x hx
  simpa only [Set.mem_ofPred_eq, sub_eq_zero] using hx

-- Changing an integrand on this singular locus does not change its integral.
example (μ : Measure (Fin 2 → ℝ)) [μ.IsAddHaarMeasure]
    (f : (Fin 2 → ℝ) → ℝ) :
    (∫ x, (if x 0 * x 1 = 1 then 0 else f x) ∂μ) = ∫ x, f x ∂μ := by
  apply integral_congr_ae
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (real_hyperbola_null μ)] with x hx
  have h : x 0 * x 1 ≠ 1 := by
    simpa only [Set.mem_ofPred_eq, sub_eq_zero] using hx
  simp [h]

-- Dropping the nonzero-polynomial premise makes the conclusion false.
example (μ : Measure (Empty → ℝ)) [μ.IsAddHaarMeasure] :
    μ {x | eval x (0 : MvPolynomial Empty ℝ) = 0} ≠ 0 := by
  simpa using (isOpen_univ.measure_pos μ Set.univ_nonempty).ne'

-- Dropping Haar fails even over the reals, for a nonzero linear polynomial.
example : (Measure.dirac (0 : Fin 1 → ℝ))
    {x | eval x (X 0 : MvPolynomial (Fin 1) ℝ) = 0} = 1 := by
  simp

-- A formally nonzero polynomial can vanish everywhere over a discrete field.
example : (X (0 : Fin 1) ^ 2 - X 0 : MvPolynomial (Fin 1) (ZMod 2)) ≠ 0 := by
  intro h
  have hc := congrArg
    (fun q : MvPolynomial (Fin 1) (ZMod 2) => q.coeff (Finsupp.single 0 2)) h
  norm_num [X_pow_eq_monomial, coeff_monomial] at hc

example (x : Fin 1 → ZMod 2) :
    eval x (X 0 ^ 2 - X 0 : MvPolynomial (Fin 1) (ZMod 2)) = 0 := by
  simp only [map_sub, map_pow, eval_X]
  have h := ZMod.pow_card (x 0)
  exact sub_eq_zero.mpr h
