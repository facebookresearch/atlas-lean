/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite CT design agreement

## i. Overview

For a finite basis of functions and a ray measure, the line
measurement of a coefficient superposition equals the finite
design sum of coefficient-weighted basis measurements. This is
forward linearity only; no inverse or uniqueness claim is made.

## ii. Key results

* `ct_design_apply`: measurement of a superposition is the design sum.
* `ct_design_entry`: the same statement at a chosen ray.

## iii. Table of contents

* A. Design linearity.
-/

@[expose] public section

open MeasureTheory Finset

namespace PhyslibExt.BiomedicalImaging.CTFiniteDesign

/-- **Finite CT design linearity.** For a finite basis `phi`
of functions, coefficients `x`, and a measure `mu`, the line
measurement of the superposition equals the finite sum of
coefficient-weighted basis measurements whenever each basis
restriction is integrable. -/
lemma ct_design_apply {ι α : Type*} [MeasurableSpace α] {s : Finset ι}
    (mu : Measure α) (phi : ι → α → ℝ) (x : ι → ℝ)
    (hint : ∀ i ∈ s, Integrable (phi i) mu) :
    (∫ a, (∑ i ∈ s, x i * phi i a) ∂mu) =
      ∑ i ∈ s, x i * (∫ a, phi i a ∂mu) := by
  have hsum : (∫ a, (∑ i ∈ s, x i * phi i a) ∂mu)
      = ∑ i ∈ s, (∫ a, x i * phi i a ∂mu) :=
    integral_finsetSum _ (fun i hi => (hint i hi).const_mul _)
  rw [hsum]
  exact sum_congr rfl (fun i _ => integral_const_mul _ _)

/-- **Design matrix entry agreement.** The `j`-th ray entry of
the finite design applied to `x` is the sum over basis elements
of `x i` times the ray transform of `phi i`. -/
lemma ct_design_entry {ι α ρ : Type*} [MeasurableSpace α] {s : Finset ι}
    (mu : ρ → Measure α) (ray : ρ) (phi : ι → α → ℝ) (x : ι → ℝ)
    (hint : ∀ i ∈ s, Integrable (phi i) (mu ray)) :
    (∫ a, (∑ i ∈ s, x i * phi i a) ∂(mu ray)) =
      ∑ i ∈ s, x i * (∫ a, phi i a ∂(mu ray)) := by
  exact ct_design_apply _ _ _ hint



end PhyslibExt.BiomedicalImaging.CTFiniteDesign
