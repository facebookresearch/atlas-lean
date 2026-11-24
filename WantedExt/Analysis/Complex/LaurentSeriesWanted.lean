/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

@[expose] public section

namespace MathlibExt.Analysis.Complex.LaurentSeriesWanted

/--
**Laurent expansion on an annulus.** Let $c \in \mathbb{C}$, let $r$ and $R$ be real numbers, and
let $f : \mathbb{C} \to \mathbb{C}$ be holomorphic on the annulus
$A = \{z \in \mathbb{C} : r < |z - c| < R\}$. Then there are coefficients $a_n \in \mathbb{C}$
for $n \in \mathbb{Z}$ such that for every $z \in A$ the series
$\sum_{n \in \mathbb{Z}} a_n (z - c)^n$ is unconditionally summable with sum $f(z)$. Here
$0^n = 0$ for $n < 0$, which matters only at $z = c$ when $r < 0$.

Sources: Mathlib `docs/undergrad.yaml`, section "Functions on one complex variable",
entry "Laurent series"; L. V. Ahlfors, Complex Analysis, 3rd ed.,
Ch. 5, §1.3 (the Laurent series).
-/
theorem_wanted laurentExpansion
    {c : ℂ} {r R : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z : ℂ | r < ‖z - c‖ ∧ ‖z - c‖ < R}) :
    ∃ a : ℤ → ℂ, ∀ z ∈ {z : ℂ | r < ‖z - c‖ ∧ ‖z - c‖ < R},
      HasSum (fun n : ℤ => a n * (z - c) ^ n) (f z)

end MathlibExt.Analysis.Complex.LaurentSeriesWanted
