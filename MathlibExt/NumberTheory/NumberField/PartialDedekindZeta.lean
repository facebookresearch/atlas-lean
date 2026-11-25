/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# Partial Dedekind zeta functions

This file defines the Euler product over a selected set of prime ideals of a number field.
-/

@[expose] public section

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- **Partial Dedekind zeta function.** Let $K$ be a number field and $S$ a set of nonzero prime
ideals of its ring of integers $\mathcal{O}_K$. For such a prime $\mathfrak{p}$ let
$N(\mathfrak{p}) = |\mathcal{O}_K / \mathfrak{p}|$ be its absolute norm. The partial Dedekind zeta
function of $S$ is the function $\zeta_{K,S} : \mathbb{C} \to \mathbb{C}$ given by the Euler product
$$\zeta_{K,S}(s) = \prod_{\mathfrak{p} \in S} \left(1 - N(\mathfrak{p})^{-s}\right)^{-1}.$$

Here a factor with $N(\mathfrak{p})^{-s} = 1$ is taken to be $0$, and the product is an
unconditional infinite product, defined without any convergence hypothesis: where it does not
converge unconditionally its value is $1$, so analytic results must state the required region of
convergence explicitly. -/
noncomputable def partialDedekindZeta
    (S : Set (IsDedekindDomain.HeightOneSpectrum (RingOfIntegers K))) : ℂ → ℂ :=
  fun s ↦ ∏' (𝔭 : S), (1 - (Ideal.absNorm 𝔭.1.asIdeal : ℂ) ^ (-s))⁻¹

@[simp]
theorem partialDedekindZeta_empty (s : ℂ) :
    partialDedekindZeta K ∅ s = 1 := by
  simp [partialDedekindZeta]

@[simp]
theorem partialDedekindZeta_singleton
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (RingOfIntegers K)) (s : ℂ) :
    partialDedekindZeta K {𝔭} s =
      (1 - (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s))⁻¹ := by
  simp [partialDedekindZeta]

end NumberField
