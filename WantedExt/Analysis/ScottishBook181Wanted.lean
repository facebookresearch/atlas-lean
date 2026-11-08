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
Steinhaus's Problem 181 from the Scottish Book, existence form: there
is a positive continuous function `f` on `ℝ` whose periodization
`∑' n : ℤ, f (x + n)` equals `1` identically in `x`. Source:
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
