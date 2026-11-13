/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic

@[expose] public section

namespace MathlibExt.Analysis.ScottishBook181Wanted

/--
**Steinhaus's periodization problem (Scottish Book Problem 181).** There is a continuous function
$f : \mathbb{R} \to \mathbb{R}$ with $f(x) > 0$ for every real $x$ such that, for every real $x$,
the series $\sum_{n \in \mathbb{Z}} f(x + n)$ converges and its sum is $1$.

Source:
H. Steinhaus, Problem 181 of the Scottish Book; the addendum Ad 181
records that the Gaussian `(1 / √π) exp (-x ^ 2)` does not have the
property, while Mazur's note gives a construction, taking a positive
continuous `g` with finite periodization and dividing `g` by that
periodization (e.g. `g(x) = exp (-x ^ 2)`). See the commentary in
R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem_wanted steinhaus181_periodization_one :
    ∃ f : ℝ → ℝ, Continuous f ∧ (∀ x, 0 < f x) ∧
      ∀ x, tsum (fun n : ℤ => f (x + (n : ℝ))) = 1

end MathlibExt.Analysis.ScottishBook181Wanted
