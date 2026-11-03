/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.MeasureTheory.Group.ActionCutoff
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Topology.Instances.ZMod

/-! # Consumers and boundary checks for normalized action cutoffs -/

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

section Consumers

variable {A X : Type*} [Group A] [MulAction A X]
  [MeasurableSpace A] [MeasurableInv A] [MeasurableSpace X]
  (τ : Measure A) [SFinite τ] [τ.IsInvInvariant]
  (μ : Measure X) [SFinite μ]
  (hact : Measurable fun p : A × X => p.1 • p.2)
  (hμ : ∀ a : A, MeasurePreserving (fun x : X => a • x) μ μ)

/-- Invariant conjugate pairings retain integrability and their value when
changing normalized weights. Neither function is assumed bounded, and `X`
is an action space, not an ambient group. -/
example (f g : X → ℂ) (hf : Measurable f) (hg : Measurable g)
    (hfi : ∀ (a : A) x, f (a • x) = f x)
    (hgi : ∀ (a : A) x, g (a • x) = g x)
    (w₁ w₂ : X → ℝ) (hw₁ : Measurable w₁) (hw₂ : Measurable w₂)
    (hw₁0 : ∀ x, 0 ≤ w₁ x) (hw₂0 : ∀ x, 0 ≤ w₂ x)
    (h₁ : ∀ x, f x ≠ 0 → ∫⁻ a, ENNReal.ofReal (w₁ (a • x)) ∂τ = 1)
    (h₂ : ∀ x, f x ≠ 0 → ∫⁻ a, ENNReal.ofReal (w₂ (a • x)) ∂τ = 1)
    (hi : Integrable (fun x => f x * (starRingEnd ℂ) (g x) * (w₁ x : ℂ)) μ) :
    Integrable (fun x => f x * (starRingEnd ℂ) (g x) * (w₂ x : ℂ)) μ ∧
      (∫ x, f x * (starRingEnd ℂ) (g x) * (w₁ x : ℂ) ∂μ) =
        ∫ x, f x * (starRingEnd ℂ) (g x) * (w₂ x : ℂ) ∂μ := by
  have hm : Measurable fun x => f x * (starRingEnd ℂ) (g x) :=
    hf.mul (Complex.continuous_conj.measurable.comp hg)
  have hinv (a : A) (x : X) :
      f (a • x) * (starRingEnd ℂ) (g (a • x)) =
        f x * (starRingEnd ℂ) (g x) := by rw [hfi, hgi]
  have hsupport (x : X) (hx : f x * (starRingEnd ℂ) (g x) ≠ 0) : f x ≠ 0 :=
    fun h => hx (by simp [h])
  have hnorm₁ x hx := h₁ x (hsupport x hx)
  have hnorm₂ x hx := h₂ x (hsupport x hx)
  exact ⟨(integrable_mul_iff_of_normalized_smul τ μ hact hμ hm hinv
      hw₁ hw₂ hw₁0 hw₂0 hnorm₁ hnorm₂).mp hi,
    integral_mul_eq_of_normalized_smul τ μ hact hμ hm hinv
      hw₁ hw₂ hw₁0 hw₂0 hnorm₁ hnorm₂⟩

/-- The nonnegative API also controls squared-norm energies, including
infinite energies, without converting ENNReal weights to real numbers. -/
example (f : X → ℂ) (hf : Measurable f)
    (hfi : ∀ (a : A) x, f (a • x) = f x)
    (w₁ w₂ : X → ℝ≥0∞) (hw₁ : Measurable w₁) (hw₂ : Measurable w₂)
    (h₁ : ∀ x, f x ≠ 0 → ∫⁻ a, w₁ (a • x) ∂τ = 1)
    (h₂ : ∀ x, f x ≠ 0 → ∫⁻ a, w₂ (a • x) ∂τ = 1) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 * w₁ x ∂μ = ∫⁻ x, ‖f x‖ₑ ^ 2 * w₂ x ∂μ := by
  apply lintegral_mul_eq_of_normalized_smul τ μ hact hμ
    (hf.enorm.pow_const 2) (fun a x => by simp only [hfi]) hw₁ hw₂
  · exact fun x hx => h₁ x (fun h => hx (by simp [h]))
  · exact fun x hx => h₂ x (fun h => hx (by simp [h]))

/-- A zero observable needs no orbit normalization anywhere, even when the
acting measure is zero and the weights have no compact support. -/
example (w₁ w₂ : X → ℝ) (hw₁ : Measurable w₁) (hw₂ : Measurable w₂)
    (hw₁0 : ∀ x, 0 ≤ w₁ x) (hw₂0 : ∀ x, 0 ≤ w₂ x) :
    (∫ x, (0 : ℂ) * (w₁ x : ℂ) ∂μ) = ∫ x, (0 : ℂ) * (w₂ x : ℂ) ∂μ := by
  exact integral_mul_eq_of_normalized_smul τ μ hact hμ measurable_const (by simp)
    hw₁ hw₂ hw₁0 hw₂0 (fun _ h => (h rfl).elim) (fun _ h => (h rfl).elim)

end Consumers

namespace NonHaarFinite

private abbrev C2 := Multiplicative (ZMod 2)
private abbrev A := C2 × C2
private def other : C2 := Multiplicative.ofAdd (1 : ZMod 2)
private theorem other_ne_one : other ≠ (1 : C2) := by decide
private def s : A := (other, 1)
private def t : A := (1, other)

local instance : MeasurableSpace A := borel A
local instance : BorelSpace A := ⟨rfl⟩

private noncomputable def τ : Measure A := Measure.dirac 1 + Measure.dirac s
local instance : SFinite τ := by unfold τ; infer_instance
local instance : τ.IsInvInvariant where
  inv_eq_self := by
    have hs : s⁻¹ = s := by decide
    simp [τ, Measure.inv, Measure.map_add _ _ measurable_inv, hs]

private theorem not_left_invariant : ¬ τ.IsMulLeftInvariant := by
  intro h
  have hm := congrArg (fun ν : Measure A => ν {1}) (h.map_mul_left_eq_self t)
  have hf : Measurable (fun x : A => t * x) := measurable_const_mul t
  dsimp only [τ] at hm
  rw [Measure.map_add _ _ hf] at hm
  simp [t, s, other_ne_one] at hm

private noncomputable def weight (r : C2) (x : A) : ℝ := if x.1 = r then 1 else 0

private theorem orbit_normalized (r : C2) (x : A) :
    (∫⁻ a, ENNReal.ofReal (weight r (a • x)) ∂τ) = 1 := by
  have cases : ∀ a : C2, a = 1 ∨ a = other := by decide
  have hs : other * other = (1 : C2) := by decide
  rcases cases r with rfl | rfl <;> rcases cases x.1 with hx | hx <;>
    simp [τ, lintegral_add_measure, weight, s, smul_eq_mul, hx,
      hs, other_ne_one, Ne.symm other_ne_one]

/-- A non-Haar acting measure, a nontrivial action and unequal cutoffs give
the same nonzero value. The orbit measure is supported on a proper subgroup
of the Klein four group, so it is not left-invariant on the acting group. -/
example : ¬ τ.IsMulLeftInvariant ∧ weight 1 ≠ weight other ∧
    (∫ x, (13 : ℂ) * (weight 1 x : ℂ) ∂Measure.count) = 26 ∧
    (∫ x, (13 : ℂ) * (weight other x : ℂ) ∂Measure.count) = 26 := by
  have nonneg (r : C2) (x : A) : 0 ≤ weight r x := by
    simp only [weight]
    split_ifs <;> norm_num
  have heq := integral_mul_eq_of_normalized_smul τ (Measure.count : Measure A)
    (hact := Measurable.of_discrete) (fun a => measurePreserving_mul_left _ a)
    (f := fun _ => (13 : ℂ)) measurable_const (by simp)
    (w₁ := weight 1) (w₂ := weight other) Measurable.of_discrete Measurable.of_discrete
    (nonneg 1) (nonneg other)
    (fun x _ => orbit_normalized 1 x) (fun x _ => orbit_normalized other x)
  have hvalue : (∫ x, (13 : ℂ) * (weight 1 x : ℂ) ∂Measure.count) = 26 := by
    rw [integral_count]
    have hu : (Finset.univ : Finset A) =
        {(1, 1), (1, other), (other, 1), (other, other)} := by decide
    rw [hu]
    norm_num [weight, other_ne_one, Ne.symm other_ne_one]
  refine ⟨not_left_invariant, ?_, hvalue, heq.symm.trans hvalue⟩
  intro h
  have he := congrFun h 1
  norm_num [weight, Ne.symm other_ne_one] at he

end NonHaarFinite

namespace InfiniteActionSpace

private abbrev A := Multiplicative (ZMod 2)
local instance : MeasurableSpace A := borel A
local instance : BorelSpace A := ⟨rfl⟩
local instance : MulAction A ℕ where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
local instance : (Measure.dirac (1 : A)).IsInvInvariant where
  inv_eq_self := by simp [Measure.inv]

private theorem not_integrable_one :
    ¬ Integrable (fun _ : ℕ => (1 : ℂ)) Measure.count := by
  rw [integrable_const_iff]
  rintro (h | h)
  · exact one_ne_zero h
  · exact h.measure_univ_lt_top.ne
      (Measure.count_apply_infinite (Set.infinite_univ : (Set.univ : Set ℕ).Infinite))

/-- On an infinite action space, normalized weights do not imply a finite
norm integral. The API transports nonintegrability and the default-zero
Bochner integral rather than asserting integrability. -/
example :
    (∫⁻ _ : ℕ, ‖(1 : ℂ)‖ₑ ∂Measure.count) = ∞ ∧
    ¬ Integrable (fun _ : ℕ => (1 : ℂ) * ((1 : ℝ) : ℂ)) Measure.count ∧
    (∫ _ : ℕ, (1 : ℂ) * ((1 : ℝ) : ℂ) ∂Measure.count) = 0 := by
  have hact : Measurable fun p : A × ℕ => p.1 • p.2 := measurable_snd
  have hμ (a : A) : MeasurePreserving (fun n : ℕ => a • n)
      Measure.count Measure.count := MeasurePreserving.id _
  have hn (n : ℕ) (_ : (1 : ℂ) ≠ 0) :
      (∫⁻ a : A, ENNReal.ofReal ((fun _ : ℕ => (1 : ℝ)) (a • n))
        ∂Measure.dirac (1 : A)) = 1 := by simp
  have hiff := integrable_mul_iff_of_normalized_smul (Measure.dirac (1 : A))
    (Measure.count : Measure ℕ) hact hμ (f := fun _ => (1 : ℂ))
    measurable_const (by simp) (w₁ := fun _ => 1) (w₂ := fun _ => 1)
    measurable_const measurable_const (by simp) (by simp) hn hn
  have heq := integral_mul_eq_of_normalized_smul (Measure.dirac (1 : A))
    (Measure.count : Measure ℕ) hact hμ (f := fun _ => (1 : ℂ))
    measurable_const (by simp) (w₁ := fun _ => 1) (w₂ := fun _ => 1)
    measurable_const measurable_const (by simp) (by simp) hn hn
  refine ⟨?_, fun h => not_integrable_one (by simpa using hiff.mpr h), ?_⟩
  · simp [lintegral_const, Measure.count_apply_infinite Set.infinite_univ]
  · rw [← heq]
    simpa only [Complex.ofReal_one, mul_one] using integral_undef not_integrable_one

end InfiniteActionSpace
