/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































































import Mathlib
import Code.Inequalities.OSSS
import Code.Walls.oc3_vcubeprob

open scoped BigOperators ENNReal
open Finset MeasureTheory
open StatMech.OSSS

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech
namespace Walls

variable {E : Type*} [Fintype E] [DecidableEq E]










theorem oc3_siteSum (ν : E → Bool → ℝ) (hν : IsProbWeight ν) (e : E) :
    ∑ b, ENNReal.ofReal (ν e b) = 1 := by
  rw [Fintype.sum_bool, add_comm,
      ← ENNReal.ofReal_add (hν.nonneg e false) (hν.nonneg e true), hν.normalized e]
  simp




noncomputable def oc3_siteMeasure (ν : E → Bool → ℝ) (hν : IsProbWeight ν) (e : E) :
    Measure Bool :=
  (PMF.ofFintype (fun b => ENNReal.ofReal (ν e b)) (oc3_siteSum ν hν e)).toMeasure


instance oc3_siteMeasure_isProb (ν : E → Bool → ℝ) (hν : IsProbWeight ν) (e : E) :
    IsProbabilityMeasure (oc3_siteMeasure ν hν e) := by
  unfold oc3_siteMeasure; infer_instance


theorem oc3_siteMeasure_singleton (ν : E → Bool → ℝ) (hν : IsProbWeight ν) (e : E) (b : Bool) :
    oc3_siteMeasure ν hν e {b} = ENNReal.ofReal (ν e b) := by
  unfold oc3_siteMeasure
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.ofFintype_apply]










noncomputable def oc3_pwMeasure (ν : E → Bool → ℝ) (hν : IsProbWeight ν) :
    Measure (ConfigSpace E) :=
  Measure.pi (fun e => oc3_siteMeasure ν hν e)





instance oc3_pwMeasure_isProb (ν : E → Bool → ℝ) (hν : IsProbWeight ν) :
    IsProbabilityMeasure (oc3_pwMeasure ν hν) := by
  unfold oc3_pwMeasure; infer_instance




theorem oc3_pwMeasure_singleton (ν : E → Bool → ℝ) (hν : IsProbWeight ν) (ω : ConfigSpace E) :
    oc3_pwMeasure ν hν {ω} = ∏ e, ENNReal.ofReal (ν e (ω e)) := by
  unfold oc3_pwMeasure
  rw [Measure.pi_singleton]
  exact Finset.prod_congr rfl (fun e _ => oc3_siteMeasure_singleton ν hν e (ω e))








theorem oc3_pwMeasure_real_singleton (ν : E → Bool → ℝ) (hν : IsProbWeight ν)
    (ω : ConfigSpace E) :
    (oc3_pwMeasure ν hν).real {ω} = weight ν ω := by
  rw [Measure.real, oc3_pwMeasure_singleton, ENNReal.toReal_prod]
  unfold weight
  refine Finset.prod_congr rfl (fun e _ => ?_)
  rw [ENNReal.toReal_ofReal (hν.nonneg e (ω e))]





















theorem oc3_expect_eq_integral (ν : E → Bool → ℝ) (hν : IsProbWeight ν)
    (g : ConfigSpace E → ℝ) :
    expect ν g = ∫ ω, g ω ∂(oc3_pwMeasure ν hν) := by
  rw [integral_fintype (Integrable.of_finite)]
  unfold OSSS.expect
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [oc3_pwMeasure_real_singleton ν hν ω, smul_eq_mul, mul_comm]






theorem oc3_integral_one (ν : E → Bool → ℝ) (hν : IsProbWeight ν) :
    ∫ _ω, (1 : ℝ) ∂(oc3_pwMeasure ν hν) = 1 := by
  rw [integral_const, probReal_univ, smul_eq_mul, mul_one]









theorem oc3_expect_const_eq_integral (ν : E → Bool → ℝ) (hν : IsProbWeight ν) :
    expect ν (fun _ => (1 : ℝ)) = 1 := by
  rw [oc3_expect_eq_integral ν hν (fun _ => 1), oc3_integral_one ν hν]








noncomputable def oc3_bernoulliWeight (p : ℝ) : E → Bool → ℝ :=
  fun _ b => if b then p else 1 - p


theorem oc3_bernoulliWeight_isProb {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbWeight (oc3_bernoulliWeight (E := E) p) where
  nonneg := by
    intro e b
    cases b <;> simp only [oc3_bernoulliWeight, Bool.false_eq_true, if_false, if_true] <;>
      linarith
  normalized := by
    intro e
    simp only [oc3_bernoulliWeight, Bool.false_eq_true, if_false, if_true]
    ring





theorem oc3_expect_eq_integral_bernoulli {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (g : ConfigSpace E → ℝ) :
    expect (oc3_bernoulliWeight (E := E) p) g
      = ∫ ω, g ω ∂(oc3_pwMeasure (oc3_bernoulliWeight (E := E) p)
          (oc3_bernoulliWeight_isProb hp0 hp1)) :=
  oc3_expect_eq_integral _ (oc3_bernoulliWeight_isProb hp0 hp1) g








section FK

variable {V : Type*} [Fintype V] [DecidableEq V]










theorem oc3_fk_expect_eq_integral {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (g : ConfigSpace (Sym2 V) → ℝ) :
    expect (oc3_bernoulliWeight (E := Sym2 V) p) g
      = ∫ ω, g ω ∂(oc3_pwMeasure (oc3_bernoulliWeight (E := Sym2 V) p)
          (oc3_bernoulliWeight_isProb hp0 hp1)) :=
  oc3_expect_eq_integral _ (oc3_bernoulliWeight_isProb hp0 hp1) g

end FK












theorem oc3_vcubeProb_dep (n : ℕ) :
    IsProbabilityMeasure (StatMech.OSSS.GrandCoupling.Vcube n) :=
  oc3_vcube_isProbabilityMeasure n

end Walls
end StatMech
