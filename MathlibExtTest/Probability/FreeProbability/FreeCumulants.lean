/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FreeProbability.FreeCumulants
public import MathlibExt.Probability.FreeProbability.Freeness

/-!
# Tests for free independence, free cumulants and the R-transform

Non-vacuity of free independence, in trivial instances only (a scalar is free from any element, so
the additivity entry's hypotheses hold for `b = 0`; a family with one member is free), the first free cumulant, the
semicircle cumulants and the semicircle R-transform.
-/

open MathlibExt.Probability.FreeProbability

namespace MathlibExtTest.Probability.FreeProbability.FreeCumulants

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- Any element is free from `0`, whose generated algebra is the scalars. -/
example (φ : A →ₗ[ℂ] ℂ) (hφ : φ 1 = 1) (a : A) : AreFree φ hφ ![a, 0] := by
  refine isFreelyIndependent_of_eq_bot hφ _ 0 fun i hi => ?_
  have hi1 : i = 1 := by fin_cases i <;> simp_all
  subst hi1
  simp

/-- A single element is free (a family with one member). -/
example (φ : A →ₗ[ℂ] ℂ) (hφ : φ 1 = 1) (a : A) : AreFree φ hφ ![a] :=
  IsFreelyIndependent.of_subsingleton φ hφ _

/-- Freeness forces `φ (x y) = 0` for centred `x ∈ B 0`, `y ∈ B 1`: the length-two word. -/
example (φ : A →ₗ[ℂ] ℂ) (hφ : φ 1 = 1) (B : Fin 2 → Subalgebra ℂ A)
    (hB : IsFreelyIndependent φ hφ B)
    (x y : A) (hx : x ∈ B 0) (hy : y ∈ B 1) (hx0 : φ x = 0) (hy0 : φ y = 0) :
    φ (x * y) = 0 := by
  have := hB 1 ![0, 1] ![x, y] (by intro i; fin_cases i; decide)
    (by intro i; fin_cases i <;> simpa) (by intro i; fin_cases i <;> simpa)
  simpa using this

/-- Free elements are uncorrelated: `φ (x y) = φ x φ y` for `x, y` free. -/
example (φ : A →ₗ[ℂ] ℂ) (hφ : φ 1 = 1) (x y : A) (h : AreFree φ hφ ![x, y]) :
    φ (x * y) = φ x * φ y :=
  h.map_mul hφ (i := 0) (j := 1) (by decide) (by simp) (by simp)

/-! Freeness is defined for a noncommutative probability space: for `φ = 0`, for which every
family would be free, the proof of `φ 1 = 1` that `AreFree` takes cannot be given. -/

/--
error: unsolved goals
A : Type u_1
inst✝¹ : Ring A
inst✝ : Algebra ℂ A
⊢ False
-/
#guard_msgs in
example : Prop := AreFree (0 : ℂ →ₗ[ℂ] ℂ) (by simp) ![(1 : ℂ)]

/-- The second free cumulant of the semicircle moments is its variance `1 - 0²`. -/
example (m : ℕ → ℂ) (h1 : m 1 = 0) (h2 : m 2 = 1) : freeCumulant m 2 = 1 := by
  rw [freeCumulant_two, h1, h2]; norm_num

/-- The first free cumulant is the mean. -/
example (m : ℕ → ℂ) : freeCumulant m 1 = m 1 := freeCumulant_one m

/-- The semicircle law has variance-cumulant `κ₂ = 1`. -/
example : freeCumulant semicircleMoment 2 = 1 := by
  simpa using freeCumulant_semicircle (n := 2) (by norm_num)

/-- The semicircle law has vanishing fourth free cumulant, although its fourth moment is `2`. -/
example : freeCumulant semicircleMoment 4 = 0 := by
  simpa using freeCumulant_semicircle (n := 4) (by norm_num)

/-- The moment-cumulant formula at `n = 1`. -/
example (m : ℕ → ℂ) :
    m 1 = ∑ π : NoncrossingPartition 1, ∏ V ∈ π.val.parts, freeCumulant m V.card :=
  moment_eq_sum_noncrossing_prod_freeCumulant m (by norm_num)

/-- The R-transform of the semicircle law has linear coefficient `1` and no constant term. -/
example : PowerSeries.coeff 1 (rTransform semicircleMoment) = 1 ∧
    PowerSeries.coeff 0 (rTransform semicircleMoment) = 0 := by
  rw [rTransform_semicircle]; simp

end MathlibExtTest.Probability.FreeProbability.FreeCumulants
