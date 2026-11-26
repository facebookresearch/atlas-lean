/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptFiberCross

/-!
# Factorization of one coordinate in the fiber cross term

Factors out one coordinate from the fiber cross term of the adaptive coupling.

## i. Overview

A single technical identity used in the tail conditional law argument. Unconditional. Its statement
is the same as `TailSelMPSplice.otc_factor_step`; the two live in modules with no common import and
are listed as a cross-module duplicate in the lane report.

## ii. Key results

- `ofh_factor_one_component`: one-coordinate factorization.

## iii. Table of contents

- A. Factorization

## iv. References

* R. O'Donnell, M. Saks, O. Schramm, R. Servedio, *Every decision tree has an influential variable*,
  FOCS 2005.
-/

@[expose] public section

open scoped BigOperators ENNReal
open Finset MeasureTheory


namespace StatMech

namespace OSSS

namespace AdaptDisintegration

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly
open StatMech.Probability OSSS.AdaptiveTau OSSS.AdaptMConditional

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ## A. Factorization -/

lemma ofh_factor_one_component (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ)
    {G : (Fin n → ℝ) → ℝ} (hGm : Measurable G) {CG : ℝ} (hGC : ∀ U, |G U| ≤ CG) :
    (∫ U, truncInd μ σ f U (t + 1) * G U ∂(cube n))
      = ∫ A, acp_truncHead μ σ f t A
          * (∫ B, G (acp_join t A B) ∂(ubfTail n t)) ∂(ubfHead n t) :=
  ubf_integral_factor_of_factors n t
    (h := fun U => truncInd μ σ f U (t + 1))
    (h₀ := acp_truncHead μ σ f t)
    (fun U => acp_truncInd_factors μ σ f t U)
    (acp_measurable_truncHead μ σ f t)
    (fun A => acp_truncHead_le_one μ σ f t A)
    hGm hGC

end AdaptDisintegration

end OSSS

end StatMech
