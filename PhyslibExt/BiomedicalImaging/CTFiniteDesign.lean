/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Analysis.IntegralGeometry.RadonTransform

/-!
# Finite CT design agreement

## i. Overview

For a finite basis of functions and a ray measure, the line
measurement of a coefficient superposition equals the finite
design sum of coefficient-weighted basis measurements. This is
forward linearity only; no inverse or uniqueness claim is made.

## ii. Key results

* `ct_design_apply`: measurement of a superposition is the design sum.
* `ct_design_radon_apply`: the application law for the Radon design entries.

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

/-- The finite CT design entry for basis element `phi i` at
Radon parameters `xi, p` (an arbitrary hyperplane level; the
signed-distance reading additionally needs `‖xi‖ = 1`): the
Euclidean Radon transform of the basis element. -/
noncomputable def ctDesignEntry {ι : Type*} (phi : ι → EuclideanSpace ℝ (Fin 2) → ℝ)
    (xi : EuclideanSpace ℝ (Fin 2)) (p : ℝ) (i : ι) : ℝ :=
  MetaMathlibExt.euclideanRadonTransform (phi i) xi p

/-- **Finite design application law.** The Radon measurement of
a coefficient superposition equals the finite design sum of
coefficient-weighted design entries, whenever every basis
restriction to the ray hyperplane is integrable. -/
lemma ct_design_radon_apply {ι : Type*} {s : Finset ι}
    (phi : ι → EuclideanSpace ℝ (Fin 2) → ℝ) (x : ι → ℝ)
    (xi : EuclideanSpace ℝ (Fin 2)) (p : ℝ)
    (hint : ∀ i ∈ s, MeasureTheory.IntegrableOn (phi i)
      {y : EuclideanSpace ℝ (Fin 2) | @inner ℝ _ _ y xi = p}
      (MeasureTheory.Measure.euclideanHausdorffMeasure 1)) :
    MetaMathlibExt.euclideanRadonTransform
        (fun a => ∑ i ∈ s, x i * phi i a) xi p =
      ∑ i ∈ s, x i * ctDesignEntry phi xi p i := by
  unfold MetaMathlibExt.euclideanRadonTransform ctDesignEntry
  exact ct_design_apply _ _ _ hint

end PhyslibExt.BiomedicalImaging.CTFiniteDesign
