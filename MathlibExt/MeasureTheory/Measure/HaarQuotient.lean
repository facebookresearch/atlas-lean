/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_HaarQuotient_measurable_lintegral_mul_out.lean` and
`P2M/Sol/S_HaarQuotient_measurable_lintegral_mul_out.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of
the Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style. Only the measurability
argument needed for the stated theorem is ported; the quotient density
and measure constructions of the source are not used in its statement.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.Algebra.Group.Basic

import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Topology.Algebra.Group.ClosedSubgroup

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace HaarQuotient

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G]

private noncomputable def orb (H : Subgroup G) (μH : Measure H)
    (φ : G → ℝ≥0∞) (g : G) : ℝ≥0∞ :=
  ∫⁻ x : H, φ ((x : G) * g) ∂μH

private theorem orb_mul_left (H : Subgroup G) (μH : Measure H)
    [μH.IsMulRightInvariant] (φ : G → ℝ≥0∞) (x₀ : H) (g : G) :
    orb H μH φ ((x₀ : G) * g) = orb H μH φ g := by
  unfold orb
  have h : (fun x : H => φ ((x : G) * ((x₀ : G) * g))) =
      fun x : H => φ (((x * x₀ : H) : G) * g) := by
    funext x
    simp [mul_assoc]
  rw [h]
  exact lintegral_mul_right_eq_self (fun x : H => φ ((x : G) * g)) x₀

private theorem orb_out_mk (H : Subgroup G) (μH : Measure H)
    [μH.IsMulRightInvariant] (φ : G → ℝ≥0∞) (g : G) :
    orb H μH φ (Quotient.mk (MulAction.orbitRel H G) g).out = orb H μH φ g := by
  have h : (MulAction.orbitRel H G)
      ((Quotient.mk (MulAction.orbitRel H G) g).out) g :=
    Quotient.mk_out g
  rw [MulAction.orbitRel_apply] at h
  obtain ⟨x₀, hx₀⟩ := h
  rw [← hx₀]
  exact orb_mul_left H μH φ x₀ g

private theorem measurable_comp_mul (H : Subgroup G) {φ : G → ℝ≥0∞}
    (hφ : Measurable φ) : Measurable fun p : G × H => φ ((p.2 : G) * p.1) := by
  apply hφ.comp
  have hcont : Continuous fun p : G × H => (p.2 : G) * p.1 :=
    (continuous_subtype_val.comp continuous_snd).mul continuous_fst
  exact hcont.measurable

private theorem measurable_subtype_mul (H : Subgroup G) (g : G) :
    Measurable fun x : H => (x : G) * g :=
  (continuous_subtype_val.mul continuous_const).measurable

private theorem measurable_orb (H : Subgroup G) (μH : Measure H) [SFinite μH]
    {φ : G → ℝ≥0∞} (hφ : Measurable φ) : Measurable (orb H μH φ) := by
  unfold orb
  exact (measurable_comp_mul H hφ).lintegral_prod_right'

private theorem secondCountable_subgroup (H : Subgroup G) :
    SecondCountableTopology H :=
  Topology.IsInducing.subtypeVal.secondCountableTopology

private theorem sigmaFinite_of_isClosed (H : Subgroup G)
    (hH : IsClosed (H : Set G)) (μH : Measure H) [μH.IsHaarMeasure] :
    SigmaFinite μH := by
  haveI : LocallyCompactSpace H :=
    hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := secondCountable_subgroup H
  infer_instance

/-- For a nonnegative measurable function `f` on a locally compact second
countable group `G`, integration over a closed subgroup `H` against a Haar
measure that is also right-invariant gives a measurable function on the quotient
`H \ G`, evaluated at the chosen representative `q.out`. -/
public theorem measurable_lintegral_mul_out
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (f : G → ℝ≥0∞) (hf : Measurable f) :
    Measurable fun q : MulAction.orbitRel.Quotient H G =>
      ∫⁻ x, f ((x : G) * q.out) ∂μH := by
  haveI : SigmaFinite μH := sigmaFinite_of_isClosed H hH μH
  rw [measurable_from_quotient]
  have hF : (fun q : MulAction.orbitRel.Quotient H G =>
        ∫⁻ x, f ((x : G) * q.out) ∂μH) ∘ Quotient.mk'' = orb H μH f := by
    funext g
    exact orb_out_mk H μH f g
  rw [hF]
  exact measurable_orb H μH hf

end HaarQuotient
