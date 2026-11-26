/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.AdelicLevel

@[expose] public section

open IsDedekindDomain NumberField NumberField.AdelicLevel

namespace AdelicLevelTest

/-- The balls are closed under subtraction and grow with the ideal: `(4) ≤ (2)`. -/
example {x y : FiniteAdeleRing (𝓞 ℚ) ℚ} (hx : x ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {4}))
    (hy : y ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {4})) :
    x - y ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {2}) :=
  idealBall_mono (Ideal.span_singleton_le_span_singleton.mpr ⟨2, by norm_num⟩)
    (sub_mem_idealBall hx hy)

/-- Monotonicity needs no hypothesis on the smaller ideal: the ball of the zero ideal lies in
every ball. -/
example (N : Ideal (𝓞 ℚ)) : idealBall (𝓞 ℚ) ℚ ⊥ ⊆ idealBall (𝓞 ℚ) ℚ N :=
  idealBall_mono bot_le

/-- Negation stays in the ball. -/
example {N : Ideal (𝓞 ℚ)} {x : FiniteAdeleRing (𝓞 ℚ) ℚ} (hx : x ∈ idealBall (𝓞 ℚ) ℚ N) :
    -x ∈ idealBall (𝓞 ℚ) ℚ N :=
  neg_mem_idealBall hx

end AdelicLevelTest
