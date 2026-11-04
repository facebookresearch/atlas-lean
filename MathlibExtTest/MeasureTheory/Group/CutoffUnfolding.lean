/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The source-type consumer is adapted from the theorem wrapper in
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_MeasureTheory_integral_mul_eq_integral_integral_subgroup_mul_mul_of_forall_integral_translate_eq_one.lean
Copyright (c) 2026 Anthropic, PBC. Licensed under Apache 2.0:
https://www.apache.org/licenses/LICENSE-2.0.
The source NOTICE also credits the respective Mathlib authors, Apache 2.0.
-/

import MathlibExt.MeasureTheory.Group.CutoffUnfolding

open MeasureTheory

namespace CutoffUnfoldingTest

/-- The complete original nested-subgroup type, including the source-redundant
compact-support hypotheses on the two ending cutoffs. -/
theorem source_type
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (S : Subgroup G) (hS : IsClosed (S : Set G)) (hST : S ≤ T) [MeasurableSpace S] [BorelSpace S]
    (μ : Measure G) [μ.IsHaarMeasure]
    (τ : Measure T) [τ.IsHaarMeasure] [τ.IsInvInvariant]
    (τS : Measure S) [τS.IsHaarMeasure] [τS.IsInvInvariant]
    (F : G → ℂ) (hFm : Measurable F) (hFb : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C)
    (hFS : ∀ (s : S) (x : G), F ((s : G) * x) = F x)
    (wS : G → ℝ) (hwS0 : ∀ x, 0 ≤ wS x) (hwSm : Measurable wS) (hwSc : HasCompactSupport wS)
    (hwS1 : ∀ x : G, F x ≠ 0 → ∫ s : S, wS ((s : G) * x) ∂τS = 1)
    (β : T → ℝ) (hβ0 : ∀ t, 0 ≤ β t) (hβm : Measurable β) (_hβc : HasCompactSupport β)
    (hβ1 : ∀ t : T, ∫ s : S, β (⟨(s : G), hST s.2⟩ * t) ∂τS = 1)
    (W : G → ℝ) (hW0 : ∀ x, 0 ≤ W x) (hWm : Measurable W) (_hWc : HasCompactSupport W)
    (hW1 : ∀ x : G, F x ≠ 0 → ∫ t : T, W ((t : G) * x) ∂τ = 1) :
    ∫ x, F x * (wS x : ℂ) ∂μ =
      ∫ x, (∫ t : T, F ((t : G) * x) * (β t : ℂ) ∂τ) * (W x : ℂ) ∂μ := by
  exact integral_mul_eq_integral_subgroup_average T hT S hS hST μ τ τS
    F hFm hFb hFS wS hwS0 hwSm hwSc hwS1 β hβ0 hβm hβ1 W hW0 hWm hW1

/-- A finite noncommutative group is allowed, with an arbitrary observable. -/
theorem finite_group_unfolding
    {A : Type*} [Group A] [Fintype A] [DecidableEq A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (g : A → ℂ) :
    ∫ x, g x ∂Measure.count =
      ∫ x, (∫ a, g (a * x) ∂Measure.count) *
        ((if x = 1 then 1 else 0 : ℝ) : ℂ) ∂Measure.count := by
  apply integral_eq_integral_smul_mul_of_normalized
    (A := A) (X := A) Measure.count Measure.count
    (measurable_of_countable _) (fun a => measurePreserving_mul_left _ a)
    (measurable_of_countable _) (by simp) (measurable_of_countable _)
    (fun x => by split <;> norm_num)
  intro x _
  change ∫ a : A, (if a * x = 1 then (1 : ℝ) else 0) ∂Measure.count = 1
  rw [integral_mul_right_eq_self (fun y : A => if y = 1 then (1 : ℝ) else 0) x]
  simp

namespace PermutationExample

private abbrev P := Equiv.Perm (Fin 3)
local instance : MeasurableSpace P := ⊤

/-- A populated, non-invariant observable on the six-element group. -/
def spike (x : P) : ℂ := if x = 1 then 7 else 0

/-- A point-mass cutoff, rather than a constant weight. -/
def cutoff (x : P) : ℝ := if x = 1 then 1 else 0

theorem noncommutative :
    (Equiv.swap 0 1 : P) * Equiv.swap 1 2 ≠ Equiv.swap 1 2 * Equiv.swap 0 1 := by
  decide

theorem spike_not_invariant : ¬∀ a x : P, spike (a * x) = spike x := by
  intro h
  have he := h (Equiv.swap 0 1) 1
  norm_num [spike, show (Equiv.swap 0 1 : P) ≠ 1 by decide] at he

theorem cutoff_normalized (x : P) :
    ∫ a : P, cutoff (a * x) ∂Measure.count = 1 := by
  rw [integral_mul_right_eq_self]
  simp [cutoff]

theorem spike_integrable : Integrable spike Measure.count := by simp

theorem spike_integral : ∫ x, spike x ∂Measure.count = 7 := by simp [spike]

theorem unfolded_nonzero :
    ∫ x, (∫ a : P, spike (a * x) ∂Measure.count) * (cutoff x : ℂ)
      ∂Measure.count = 7 :=
  (finite_group_unfolding spike).symm.trans spike_integral

theorem kernel_integrable :
    Integrable (fun p : P × P => spike (p.1 * p.2) * (cutoff p.2 : ℂ))
      (Measure.count.prod Measure.count) :=
  integrable_comp_smul_mul_of_normalized Measure.count Measure.count
    (measurable_of_countable _) (fun a => measurePreserving_mul_left _ a)
    (measurable_of_countable _) spike_integrable (measurable_of_countable _)
    (fun x => by unfold cutoff; split <;> norm_num) (fun x _ => cutoff_normalized x)

theorem weighted_average_integrable :
    Integrable (fun x : P => (∫ a : P, spike (a * x) ∂Measure.count) * (cutoff x : ℂ))
      Measure.count := by
  simpa only [integral_mul_const] using kernel_integrable.integral_prod_right

theorem zero_cutoff_rejected :
    ¬∀ x : P, spike x ≠ 0 → ∫ _a : P, (0 : ℝ) ∂Measure.count = 1 := by
  intro h
  simpa [spike] using h 1 (by norm_num [spike])

theorem scaled_cutoff_rejected :
    ∫ a : P, 2 * cutoff (a * 1) ∂Measure.count ≠ 1 := by
  rw [integral_const_mul, cutoff_normalized]
  norm_num

local instance : TopologicalSpace P := ⊥
local instance : DiscreteTopology P := ⟨rfl⟩
local instance : BorelSpace P := ⟨by rw [borel_eq_top_of_discrete]; rfl⟩
local instance (H : Subgroup P) : MeasurableSpace H := ⊤
local instance (H : Subgroup P) : BorelSpace H := ⟨by rw [borel_eq_top_of_discrete]; rfl⟩
local instance : (Measure.count : Measure P).IsHaarMeasure := {}
local instance (H : Subgroup P) : (Measure.count : Measure H).IsHaarMeasure := {}

theorem top_cutoff_normalized (x : P) :
    ∫ a : (⊤ : Subgroup P), cutoff ((a : P) * x) ∂Measure.count = 1 := by
  classical
  have he : (fun a : (⊤ : Subgroup P) => cutoff ((a : P) * x)) =
      (fun a => if a = ⟨x⁻¹, Subgroup.mem_top _⟩ then (1 : ℝ) else 0) := by
    funext a
    simp [cutoff, mul_eq_one_iff_eq_inv, Subtype.ext_iff]
  rw [he]
  simp

/-- All source hypotheses are jointly inhabited for a nonzero observable
that is invariant under the proper subgroup `⊥`, but not under `⊤`. -/
theorem nested_spike :
    ∫ x : P, spike x * (1 : ℂ) ∂Measure.count =
      ∫ x : P, (∫ t : (⊤ : Subgroup P), spike ((t : P) * x) * (1 : ℂ)
        ∂Measure.count) * (cutoff x : ℂ) ∂Measure.count := by
  classical
  apply source_type (⊤ : Subgroup P) (by simp)
    (⊥ : Subgroup P) (by simp) bot_le
    Measure.count Measure.count Measure.count spike (measurable_of_countable _)
    ⟨7, fun x => by unfold spike; split <;> norm_num⟩
    (fun s x => by
      have hs : (s : P) = 1 := Subgroup.mem_bot.mp s.property
      simp [hs])
    (fun _ => 1) (fun _ => by norm_num) measurable_const
    (HasCompactSupport.of_compactSpace _) (fun _ _ => by simp)
    (fun _ => 1) (fun _ => by norm_num) measurable_const
    (HasCompactSupport.of_compactSpace _) (fun _ => by simp)
    cutoff (fun x => by unfold cutoff; split <;> norm_num)
    (measurable_of_countable _) (HasCompactSupport.of_compactSpace _)
    (fun x _ => top_cutoff_normalized x)

theorem nested_spike_nonzero :
    ∫ x : P, (∫ t : (⊤ : Subgroup P), spike ((t : P) * x) * (1 : ℂ)
      ∂Measure.count) * (cutoff x : ℂ) ∂Measure.count = 7 := by
  rw [← nested_spike]
  simpa using spike_integral

theorem nested_average_integrable :
    Integrable (fun x : P =>
      (∫ t : (⊤ : Subgroup P), spike ((t : P) * x) * (1 : ℂ) ∂Measure.count) *
        (cutoff x : ℂ)) Measure.count := by
  simp

end PermutationExample

/-- Zero observable and empty-support cutoff are admitted together, without
an impossible global normalization assumption. -/
theorem zero_unfolding
    {A X : Type*} [Group A] [MulAction A X]
    [MeasurableSpace A] [MeasurableInv A] [MeasurableSpace X]
    (τ : Measure A) [SFinite τ] [τ.IsInvInvariant] (μ : Measure X) [SFinite μ]
    (ha : Measurable fun p : A × X => p.1 • p.2)
    (hμ : ∀ a : A, MeasurePreserving (fun x : X => a • x) μ μ) :
    ∫ _x : X, (0 : ℂ) ∂μ =
      ∫ _x : X, (∫ _a : A, (0 : ℂ) ∂τ) * (0 : ℂ) ∂μ :=
  integral_eq_integral_smul_mul_of_normalized τ μ ha hμ
    (g := fun _ => 0) (w := fun _ => 0) measurable_const (by simp)
    measurable_const (fun _ => le_rfl) (fun _ hx => (hx rfl).elim)

end CutoffUnfoldingTest
