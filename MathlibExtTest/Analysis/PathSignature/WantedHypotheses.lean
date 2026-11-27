/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PathSignature.RoughPath
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

@[expose] public section

open MeasureTheory MathlibExt.Analysis.PathSignature

namespace MathlibExtTest.Analysis.PathSignature.WantedHypotheses

/-- The zero function is a control. -/
theorem isControl_zero (J : Set ℝ) : IsControl (fun _ _ => 0) J :=
  ⟨continuousOn_const, fun _ _ => rfl, fun _ _ _ _ _ => le_rfl, fun _ _ _ _ _ _ _ _ => by simp⟩

/-- The signature of the constant path has vanishing levels of positive degree. -/
theorem levelNorm_signature_zero (s t : ℝ) (hst : s ≤ t) {i : ℕ} (hi : 1 ≤ i) :
    levelNorm (signature (fun (_ : Fin 2) (_ : ℝ) => (0 : ℝ)) s t) i = 0 := by
  have h := signature_of_eqOn_Ioc (v := fun (_ : Fin 2) (_ : ℝ) => (0 : ℝ)) (s := s) (t := t) 0
    hst (fun _ _ _ => rfl)
  rw [h]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hi
  simp [levelNorm, tensorExp, List.ofFn_succ]

/-- Hypotheses of `ExtensionTheoremWanted.exists_unique_extension` and of
`ExtensionTheoremWanted.isControlledBy_extension` at `p = 2` (degree `⌊2⌋ = 2`, a genuinely
rough exponent): the signature of the constant path in `ℝ²` on `[0, 1]` is a multiplicative
functional of degree `2`, controlled by the zero control with any `β > 0`, hence of finite
`2`-variation. -/
example : IsMultiplicativeFunctional ⌊(2 : ℝ)⌋₊ (signature fun (_ : Fin 2) (_ : ℝ) => (0 : ℝ))
      (Set.Icc 0 1) ∧
    IsControlledBy 2 1 ⌊(2 : ℝ)⌋₊ (signature fun (_ : Fin 2) (_ : ℝ) => (0 : ℝ)) (fun _ _ => 0)
      (Set.Icc 0 1) ∧
    HasFinitePVariation 2 ⌊(2 : ℝ)⌋₊ (signature fun (_ : Fin 2) (_ : ℝ) => (0 : ℝ))
      (Set.Icc 0 1) := by
  have hctl : IsControlledBy 2 1 ⌊(2 : ℝ)⌋₊ (signature fun (_ : Fin 2) (_ : ℝ) => (0 : ℝ))
      (fun _ _ => 0) (Set.Icc 0 1) := by
    intro i hi _ s _ t _ hst
    rw [levelNorm_signature_zero s t hst hi, Real.zero_rpow (by positivity), zero_div]
  exact ⟨isMultiplicativeFunctional_signature (fun _ _ _ => intervalIntegrable_const) _ _, hctl,
    _, isControl_zero _, 1, one_pos, hctl⟩

/-- Hypotheses of `ExtensionTheoremWanted.exists_unique_extension` at `p = 1` for a non-constant
path: the signature of the unit-speed diagonal path has degree `⌊1⌋ = 1` and finite
`1`-variation. -/
example : IsMultiplicativeFunctional ⌊(1 : ℝ)⌋₊ (signature fun (_ : Fin 2) (_ : ℝ) => (1 : ℝ))
      (Set.Icc 0 1) ∧
    HasFinitePVariation 1 ⌊(1 : ℝ)⌋₊ (signature fun (_ : Fin 2) (_ : ℝ) => (1 : ℝ))
      (Set.Icc 0 1) :=
  ⟨isMultiplicativeFunctional_signature (fun _ _ _ => intervalIntegrable_const) _ _,
    hasFinitePVariation_signature (fun _ => continuous_const) _ _⟩

/-- Hypotheses of `UniversalApproximationWanted.exists_signature_linear_approx` with `d = 0`: the
singleton of the constant velocity `1` (the path `X_t = t`) in `L¹([0, 1])` is compact, its time
coordinate is `1` almost everywhere, and every function is continuous on it. -/
example (g : Lp (Fin 1 → ℝ) 1 (volume.restrict (Set.Icc (0 : ℝ) 1)) → ℝ) :
    let K : Set (Lp (Fin 1 → ℝ) 1 (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
      {Lp.const 1 (volume.restrict (Set.Icc (0 : ℝ) 1)) (fun _ => (1 : ℝ))}
    IsCompact K ∧ (∀ f ∈ K, ∀ᵐ u ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), f u 0 = 1) ∧
      ContinuousOn g K := by
  intro K
  refine ⟨isCompact_singleton, fun f hf => ?_, continuousOn_singleton _ _⟩
  rw [Set.mem_singleton_iff] at hf
  subst hf
  filter_upwards [Lp.coeFn_const (p := 1) (μ := volume.restrict (Set.Icc (0 : ℝ) 1))
    (fun _ : Fin 1 => (1 : ℝ))] with u hu
  rw [hu]
  rfl

end MathlibExtTest.Analysis.PathSignature.WantedHypotheses
