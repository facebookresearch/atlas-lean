/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The disorder law and operator formula are adapted from the `openai/math` comparator
`lean/ComparatorChallenges/PlanarAndersonSpectrum.lean` at revision
`3344da59991ed94f9ba711217b29c1d760badfa6`.
The companion bounded realization at the same revision is in
`lean/OAI/MathematicalPhysics/PlanarAnderson/Spectrum.lean`; no proof code was copied.

The source's `lean/LICENSE` at that revision provides the Apache License,
Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: OpenAI (project attribution in lean/formalization.yaml).
Neither cited Lean file nor the applicable license names a copyright holder or
individual authors for these portions.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.ProductMeasure

/-! # The square-lattice Anderson operator

The bounded self-adjoint realization under independent uniform disorder.
- Two-dimensional nearest-neighbor hopping uses the adjacency convention, without a diagonal shift.
- Real multiplication by the potential adds a diagonal term.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace WantedExt.Physics

open MeasureTheory
open scoped ENNReal lp

/-- **Almost-sure existence of the planar Anderson operator.** Let $h>0$ and sample the
values $V_{i,j}$ independently and uniformly in $[-h,h]$. For almost every configuration $V$,
there is a bounded self-adjoint operator $H$ on $\ell^2(\mathbb Z^2;\mathbb C)$ with

$$
(Hu)_{i,j}=u_{i+1,j}+u_{i-1,j}+u_{i,j+1}+u_{i,j-1}+V_{i,j}u_{i,j}
$$

for every $u$ and every site $(i,j)$. This assertion specifies the operator, not its spectrum.

Source: OpenAI, [square-lattice Anderson model, bounded realization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/MathematicalPhysics/PlanarAnderson/Spectrum.lean#L179-L208),
the existence and self-adjointness part of the
[Comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PlanarAndersonSpectrum.lean#L11-L28). -/
theorem_wanted anderson_operator_exists_ae {h : ℝ} (hh : 0 < h) :
    ∀ᵐ v ∂Measure.infinitePi (fun _ : ℤ × ℤ =>
      ProbabilityTheory.cond (volume : Measure ℝ) (Set.Icc (-h) h)),
      ∃ H : ℓ²(ℤ × ℤ, ℂ) →L[ℂ] ℓ²(ℤ × ℤ, ℂ), IsSelfAdjoint H ∧
        ∀ (u : ℓ²(ℤ × ℤ, ℂ)) (x : ℤ × ℤ),
          (H u) x = u (x.1 + 1, x.2) + u (x.1 - 1, x.2) +
            u (x.1, x.2 + 1) + u (x.1, x.2 - 1) + (v x : ℂ) * u x

end WantedExt.Physics
