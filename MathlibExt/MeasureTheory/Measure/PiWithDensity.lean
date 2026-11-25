/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Marginal
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Products of measures with densities

For finitely many σ-finite measures `μ i` and measurable functions `g i`, `f i`:

* `lmarginal_prod`: the iterated integral of `y ↦ ∏ i, g i (y i)` over the coordinates in a finset
  `s` replaces the factors indexed by `s` with their integrals;
* `lintegral_fintype_prod_eq_prod`: `∫⁻ y, ∏ i, g i (y i) ∂(Measure.pi μ) = ∏ i, ∫⁻ t, g i t ∂μ i`,
  the lower-integral counterpart of Mathlib's `MeasureTheory.integral_fintype_prod_eq_prod`;
* `Measure.pi_withDensity`: if moreover each weighted measure `(μ i).withDensity (f i)` is
  σ-finite, then `Measure.pi (fun i ↦ (μ i).withDensity (f i))` is
  `(Measure.pi μ).withDensity (fun y ↦ ∏ i, f i (y i))`. For instance, the law of independent
  observations with densities has the product density. The extra hypothesis is not automatic:
  Lebesgue measure with the density `∞` is not σ-finite. It holds for probability densities and
  for any finite-valued density (`SigmaFinite.withDensity_of_ne_top`).
-/

@[expose] public section

set_option autoImplicit false

open Finset
open scoped ENNReal

namespace MeasureTheory

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] {μ : ∀ i, Measure (X i)}
  [∀ i, SigmaFinite (μ i)]

/-- **Iterated integrals of a product of one-variable functions.** Let $\mu_i$ be σ-finite
measures on measurable spaces $X_i$, indexed by a finite type $\iota$, and let
$g_i : X_i \to [0, \infty]$ be measurable functions. For a finite set $s \subseteq \iota$ and a
point $x \in \prod_i X_i$, integrating $y \mapsto \prod_{i \in \iota} g_i(y_i)$ over the
coordinates $y_i$ with $i \in s$, each against $\mu_i$, while the other coordinates are fixed to
those of $x$, gives $\left(\prod_{i \in s} \int g_i \, d\mu_i\right) \cdot
\prod_{i \notin s} g_i(x_i)$. -/
theorem lmarginal_prod [DecidableEq ι] [Fintype ι] {g : ∀ i, X i → ℝ≥0∞}
    (hg : ∀ i, Measurable (g i)) (s : Finset ι) (x : ∀ i, X i) :
    (∫⋯∫⁻_s, (fun y ↦ ∏ i, g i (y i)) ∂μ) x =
      (∏ i ∈ s, ∫⁻ t, g i t ∂μ i) * ∏ i ∈ univ \ s, g i (x i) := by
  have hm : Measurable fun y : ∀ i, X i ↦ ∏ i, g i (y i) :=
    Finset.measurable_prod _ fun i _ ↦ (hg i).comp (measurable_pi_apply i)
  induction s using Finset.induction_on generalizing x with
  | empty => simp
  | insert i s hi ih =>
    rw [lmarginal_insert _ hm hi]
    simp_rw [ih]
    have hsplit : ∀ t, ∏ j ∈ univ \ s, g j (Function.update x i t j) =
        g i t * ∏ j ∈ univ \ insert i s, g j (x j) := fun t ↦ by
      have hmem : i ∈ univ \ s := by simp [hi]
      rw [← Finset.mul_prod_erase _ _ hmem, Function.update_self]
      congr 1
      refine Finset.prod_congr (by ext j; simp) fun j hj ↦ ?_
      have hji : j ≠ i := by
        intro h
        simp [h] at hj
      rw [Function.update_of_ne hji]
    simp_rw [hsplit]
    rw [prod_insert hi]
    rw [show (fun t ↦ (∏ i ∈ s, ∫⁻ t, g i t ∂μ i) *
        (g i t * ∏ j ∈ univ \ insert i s, g j (x j))) =
        fun t ↦ ((∏ i ∈ s, ∫⁻ t, g i t ∂μ i) * ∏ j ∈ univ \ insert i s, g j (x j)) * g i t by
      funext t; ring]
    rw [lintegral_const_mul _ (hg i)]
    ring

/-- **Tonelli for products.** Let $\mu_i$ be σ-finite measures on measurable spaces $X_i$,
indexed by a finite type $\iota$, and let $g_i : X_i \to [0, \infty]$ be measurable functions.
Then the integral of $y \mapsto \prod_{i \in \iota} g_i(y_i)$ with respect to the product measure
$\prod_i \mu_i$ equals $\prod_{i \in \iota} \int g_i \, d\mu_i$. -/
theorem lintegral_fintype_prod_eq_prod [Fintype ι] {g : ∀ i, X i → ℝ≥0∞}
    (hg : ∀ i, Measurable (g i)) :
    ∫⁻ y, ∏ i, g i (y i) ∂Measure.pi μ = ∏ i, ∫⁻ t, g i t ∂μ i := by
  classical
  rcases isEmpty_or_nonempty (∀ i, X i) with hX | ⟨⟨x⟩⟩
  · obtain ⟨i, hi⟩ := isEmpty_pi.mp hX
    rw [Measure.eq_zero_of_isEmpty (Measure.pi μ), lintegral_zero_measure,
      Finset.prod_eq_zero (mem_univ i)]
    rw [Measure.eq_zero_of_isEmpty (μ i), lintegral_zero_measure]
  · rw [lintegral_eq_lmarginal_univ x, lmarginal_prod hg, sdiff_self, bot_eq_empty, prod_empty,
      mul_one]

/-- **A product of measures with densities.** Let $\mu_i$ be σ-finite measures on measurable
spaces $X_i$, indexed by a finite type $\iota$, and let $f_i : X_i \to [0, \infty]$ be measurable
functions such that, for each $i$, the measure $f_i \mu_i$ with density $f_i$ with respect to
$\mu_i$ is σ-finite. Then the product measure $\prod_i f_i \mu_i$ equals the measure with density
$y \mapsto \prod_{i \in \iota} f_i(y_i)$ with respect to the product measure $\prod_i \mu_i$.

The σ-finiteness of the weighted measures guarantees that their product measure is characterized
on boxes. -/
theorem Measure.pi_withDensity [Fintype ι] {f : ∀ i, X i → ℝ≥0∞} (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i ↦ (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity fun y ↦ ∏ i, f i (y i) := by
  refine Measure.pi_eq fun s hs ↦ ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi,
    lintegral_fintype_prod_eq_prod hf]
  exact Finset.prod_congr rfl fun i _ ↦ (withDensity_apply _ (hs i)).symm

end MeasureTheory
