/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

@[expose] public section

open scoped BigOperators

namespace MathlibExt.Analysis.Calculus.TaylorLittleoRemainderWanted

/-- **Taylor's theorem with little-o remainder in several variables.** Let $E$ and $F$ be normed
vector spaces over $\mathbb{R}$, let $n$ be a natural number, and let $f : E \to F$ be $n$ times
continuously differentiable on a neighbourhood of a point $x_0 \in E$. Write $D^k f(x_0)$ for the
$k$-th Fréchet derivative of $f$ at $x_0$, a continuous $k$-linear map from $E^k$ to $F$. Then, as
$x$ tends to $x_0$,
$$f(x) - \sum_{k=0}^{n} \frac{1}{k!}\, D^k f(x_0)(x - x_0, \ldots, x - x_0) =
o\bigl(\|x - x_0\|^n\bigr).$$

Sources:
- Mathlib `docs/undergrad.yaml`, section "Multivariable calculus / Differential
  calculus", entry "Taylor's theorem with little-o remainder" (currently missing:
  empty entry, no Mathlib declaration). The integral-remainder form exists as
  `map_add_eq_sum_add_integral_iteratedFDeriv`.
- H. Cartan, *Differential Calculus*, Ch. III, Taylor's formula with remainder.
- https://en.wikipedia.org/wiki/Taylor%27s_theorem#Taylor's_theorem_in_several_variables
-/
public theorem_wanted taylor_isLittleO_multivariable
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x₀ : E} {n : ℕ} (hf : ContDiffAt ℝ n f x₀) :
    (fun x ↦ f x - ∑ k ∈ Finset.range (n + 1),
      ((Nat.factorial k : ℝ))⁻¹ •
        iteratedFDeriv ℝ k f x₀ (fun _ ↦ x - x₀)) =o[nhds x₀]
      fun x ↦ ‖x - x₀‖ ^ n

end MathlibExt.Analysis.Calculus.TaylorLittleoRemainderWanted
