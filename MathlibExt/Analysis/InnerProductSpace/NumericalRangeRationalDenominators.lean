/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`openai/math` at revision `3344da59991ed94f9ba711217b29c1d760badfa6`.

* `lean/ComparatorChallenges/HilbertCrouzeix.lean`: the statement of
  `rational_denominator_isUnit` and its numerical range and pole-avoidance definitions.
* `lean/OAI/Analysis/HilbertCrouzeix/Calculus.lean`: the proof of
  `rational_denominator_isUnit` by polynomial spectral mapping.

Licensed under the Apache License, Version 2.0; see `lean/LICENSE` at that revision.
Authors: OpenAI (project attribution in lean/formalization.yaml).
The cited files and accompanying notices name no copyright holder or individual authors.
-/

module

import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.FieldTheory.RatFunc.Basic
public import MathlibExt.Analysis.InnerProductSpace.ToeplitzHausdorff
import MathlibExt.Analysis.InnerProductSpace.NumericalRangeSpectrum

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MathlibExt.Analysis.InnerProductSpace.NumericalRangeSpectrum

namespace ContinuousLinearMap

/-- **Invertibility of rational matrix denominators off the closed numerical range.** Let $H$
be a nonzero complex Hilbert space, let $A$ be a bounded operator on $H$, and let $R$ be a
square matrix of complex rational functions. Use the inner product linear in its second argument.
If none of the entry denominators in reduced form vanish anywhere in the closure of
$\{\langle x,Ax\rangle:\|x\|=1\}$, then for every entry $(i,j)$ the polynomial evaluation
$\operatorname{denom}(R_{ij})(A)$ is invertible.
The premise is on the whole matrix and the conclusion is for its indicated entry.

Source: OpenAI, [Hilbert-space Crouzeix support statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/HilbertCrouzeix.lean#L131-L135). -/
theorem isUnit_aeval_ratFunc_denom_of_no_poles_on_numericalRange
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
    (A : H →L[ℂ] H) {m : ℕ} (R : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (hR : ∀ z ∈ star '' closure
      (MathlibExt.Analysis.InnerProductSpace.ToeplitzHausdorffWanted.numericalRange A),
      ∀ i j : Fin m, (R i j).denom.eval z ≠ 0)
    (i j : Fin m) : IsUnit (Polynomial.aeval A (R i j).denom) := by
  apply (spectrum.zero_notMem_iff (R := ℂ)).1
  rw [spectrum.map_polynomial_aeval]
  intro h
  obtain ⟨z, hz, hEval⟩ := h
  have hz' := spectrum_subset_star_image_closure_numericalRange A hz
  exact hR z hz' i j hEval

end ContinuousLinearMap
