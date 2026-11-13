/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Topology.Instances.Complex

@[expose] public section

namespace MathlibExt.Analysis.Complex.ScottishBook39Wanted

/-- **Discontinuous subadditive multiplicative functions on $\mathbb{C}$.** There is a function
$\varphi : \mathbb{C} \to \mathbb{R}$ that is not continuous, satisfies $\varphi(x) \ge 0$ for
all $x \in \mathbb{C}$, is not identically $0$ and not identically $1$, and satisfies
$\varphi(x + y) \le \varphi(x) + \varphi(y)$ and $\varphi(xy) = \varphi(x)\varphi(y)$ for all
$x, y \in \mathbb{C}$.

This answers Problem 39 of the Scottish Book (Auerbach), which notes that the continuous
functions with these properties are exactly $\varphi(x) = |x|^\alpha$ with $0 < \alpha \le 1$ and
asks whether discontinuous ones exist. Mazur's answer is $\varphi(x) = |f(x)|$ for a
discontinuous field automorphism $f$ of $\mathbb{C}$.

Source: H. Auerbach, Problem 39 of the Scottish Book; addendum of S. Mazur,
10 April 1937, in the Scottish Book, via Lebesgue's theorem on the existence
of a discontinuous automorphism of `ℂ` (Kamke); see the commentary in
R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem_wanted exists_discontinuous_subadditive_multiplicative :
    ∃ φ : ℂ → ℝ, ¬ Continuous φ ∧ (∀ x, 0 ≤ φ x) ∧
      ¬ (∀ x, φ x = 0) ∧ ¬ (∀ x, φ x = 1) ∧
      (∀ x y, φ (x + y) ≤ φ x + φ y) ∧ (∀ x y, φ (x * y) = φ x * φ y)

end MathlibExt.Analysis.Complex.ScottishBook39Wanted
