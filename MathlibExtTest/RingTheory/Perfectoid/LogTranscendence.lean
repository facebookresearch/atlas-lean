/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.Perfectoid.LogTranscendence

/-! Tests for the logarithms in `B_dR^+`, the rings `A_max ⊆ B_max^+ ⊆ B_max`, and the
transcendence of `log [p̃]` over `B_max`: the logarithm is additive, `log [ε]` is a nonzero
element of `A_max` for `ε ≠ 1`, `B_max` is Galois stable, `σ(log [p̃]) - log [p̃] ∈ B_max`,
`log [p̃]` is not in the fraction field of `B_max`, and no nonzero polynomial over `B_max` vanishes
at it. -/

open Ideal WittVector PowerSeries Polynomial PadicComplexInt

variable (p : ℕ) [Fact p.Prime]

local notation "𝔸" => WittVector p (PreTilt 𝓞_ℂ_[p] p)
local notation "𝔸ₚ" => Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))
local notation "𝕀" => RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)
local notation "𝔹⁺" => BDeRhamPlus 𝓞_ℂ_[p] p
local notation "𝔹" => BDeRham 𝓞_ℂ_[p] p

-- Evaluation of power series: constants, `X`, and naturality.
example {A : Type*} [CommRing A] (I : Ideal A) {x : A} (hx : x ∈ I) (a : A) :
    AdicCompletion.evalPowerSeries I hx (PowerSeries.C a + PowerSeries.X) =
      AdicCompletion.of I A a + AdicCompletion.of I A x := by
  rw [map_add, AdicCompletion.evalPowerSeries_C, AdicCompletion.evalPowerSeries_X]

-- The logarithm series is the image of `PowerSeries.log ℚ_[p]`; its coefficient of `X²` is `-1/2`.
example : logSeries p = PowerSeries.map (algebraMap ℚ_[p] 𝔸ₚ) (PowerSeries.log ℚ_[p]) := rfl

example : PowerSeries.coeff 2 (logSeries p) = -algebraMap ℚ_[p] 𝔸ₚ (2 : ℚ_[p])⁻¹ := by
  rw [coeff_logSeries]
  norm_num

-- With the inverses of a `ℚ`-algebra field, the series `log(1 - X)` of Fontaine's lemma is
-- `PowerSeries.log` at `-X`; its coefficient of `X` is `-1`.
example : AdicCompletion.logOneSubSeries (fun n => algebraMap ℚ_[p] 𝔸ₚ (n : ℚ_[p])⁻¹) =
    PowerSeries.map (algebraMap ℚ_[p] 𝔸ₚ) (PowerSeries.rescale (-1) (PowerSeries.log ℚ_[p])) :=
  AdicCompletion.logOneSubSeries_eq_map_rescale_log

example : PowerSeries.coeff 1 (AdicCompletion.logOneSubSeries fun n : ℕ => (n : ℚ)⁻¹) = -1 := by
  simp [AdicCompletion.logOneSubSeries]

-- `log((1 + y)(1 + z)) = log(1 + y) + log(1 + z)`; in particular `log [ε ε'] = log [ε] + log [ε']`.
example {y z : 𝔸ₚ} (hy : y ∈ 𝕀) (hz : z ∈ 𝕀) :
    logOneAdd p (add_mem (add_mem hy hz) (Ideal.mul_mem_right z _ hy)) =
      logOneAdd p hy + logOneAdd p hz :=
  logOneAdd_add p hy hz _

example {ε ε' : PreTilt 𝓞_ℂ_[p] p} (h : ε.untilt = 1) (h' : ε'.untilt = 1)
    (hεε' : (ε * ε').untilt = 1) :
    logTeichmuller p hεε' = logTeichmuller p h + logTeichmuller p h' := by
  rw [logTeichmuller, logTeichmuller, logTeichmuller, ← logOneAdd_add p]
  · apply logOneAdd_congr
    rw [map_mul]
    simp only [map_sub, map_one, map_mul]
    ring
  · exact add_mem (add_mem (algebraMap_teichmuller_sub_one_mem_ker p h)
      (algebraMap_teichmuller_sub_one_mem_ker p h'))
      (Ideal.mul_mem_right _ _ (algebraMap_teichmuller_sub_one_mem_ker p h))

-- `log [ε]` is a nonzero element of `A_max` for `ε♯ = 1`, `ε ≠ 1`; Fontaine's `ε` is an example.
example : logTeichmuller p (untilt_epsilon p) ≠ 0 :=
  logTeichmuller_ne_zero p (untilt_epsilon p) (epsilon_ne_one p)

example {ε : PreTilt 𝓞_ℂ_[p] p} (h : ε.untilt = 1) : logTeichmuller p h ∈ aMax p :=
  logTeichmuller_mem_aMax p h

example : algebraMap 𝔸 𝔹⁺ (xi p) ∈ aMax p := algebraMap_mem_aMax p (xi p)

-- `B_max` contains `t = log [ε]` and `1/t`.
example : algebraMap 𝔹⁺ 𝔹 (logTeichmuller p (untilt_epsilon p)) ∈ bMax p :=
  algebraMap_mem_bMax p (logTeichmuller_mem_aMax p _)

example : (algebraMap 𝔹⁺ 𝔹 (logTeichmuller p (untilt_epsilon p)))⁻¹ ∈ bMax p :=
  Algebra.subset_adjoin (Or.inr ⟨epsilon p, untilt_epsilon p, epsilon_ne_one p, rfl⟩)

example : bMaxPlus p ≤ bMax p := bMaxPlus_le_bMax p

-- `B_max` is Galois stable and `σ(log [p̃]) - log [p̃] ∈ B_max`.
example (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) {x : 𝔹} (hx : x ∈ bMax p) :
    galoisBDeRham p σ x ∈ bMax p :=
  bMax_le_comap p σ hx

example (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    galoisBDeRham p σ (algebraMap 𝔹⁺ 𝔹 (logPTilde p)) - algebraMap 𝔹⁺ 𝔹 (logPTilde p) ∈
      bMax p := by
  obtain ⟨u, hu, hu1⟩ := exists_preTiltMap_pFlat_eq_mul p σ
  rw [galoisBDeRham_algebraMap, galoisBDeRhamPlus_logPTilde p σ hu hu1, map_add,
    add_sub_cancel_right]
  exact algebraMap_mem_bMax p (logTeichmuller_mem_aMax p hu1)

-- `log [p̃]` is not in the fraction field of `B_max`.
example {a b : 𝔹} (ha : a ∈ bMax p) (hb : b ∈ bMax p) (ha0 : a ≠ 0) :
    a * algebraMap 𝔹⁺ 𝔹 (logPTilde p) ≠ b :=
  mul_algebraMap_logPTilde_ne p ha hb ha0

-- In particular `log [p̃]` itself does not lie in `B_max`.
example : algebraMap 𝔹⁺ 𝔹 (logPTilde p) ∉ bMax p := fun h =>
  mul_algebraMap_logPTilde_ne p (Subalgebra.one_mem _) h one_ne_zero (one_mul _)

-- `log [p̃]` is transcendental over `B_max`: no nonzero polynomial over `B_max` vanishes at it.
example : Transcendental (bMax p) (algebraMap 𝔹⁺ 𝔹 (logPTilde p)) :=
  transcendental_logPTilde p

example (P : (bMax p)[X]) (hP : aeval (algebraMap 𝔹⁺ 𝔹 (logPTilde p)) P = 0) : P = 0 :=
  aeval_logPTilde_injective p (hP.trans (map_zero _).symm)
