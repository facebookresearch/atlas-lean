/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.PrimeCounting.BrunConstant

@[expose] public section

namespace MathlibExt.NumberTheory.PrimeCounting

/-!
# Explicit bounds on Brun's constant

These established numerical bounds are recorded as wishlist theorems pending Lean proofs.
-/

/-- **Lower bound for Brun's constant.** Brun's constant $B$, the sum of
$\frac{1}{p} + \frac{1}{p + 2}$ over all primes $p$ such that $p + 2$ is also prime, satisfies
$B > 1.840503$.

Source: Dave Platt and Tim Trudgian, “Improved bounds on Brun's constant,” Experimental
Mathematics 28 (2019), no. 2, 179–184; arXiv:1803.01925. The bound is also recorded in
teorth/optimizationproblems, `constants/81a.md`.
-/
public theorem_wanted brunConstant_lower_bound :
    1.840503 < brunConstant

/-- **Upper bound for Brun's constant.** Brun's constant $B$, the sum of
$\frac{1}{p} + \frac{1}{p + 2}$ over all primes $p$ such that $p + 2$ is also prime, satisfies
$B < 2.288513$.

Source: Dave Platt and Tim Trudgian, “Improved bounds on Brun's constant,” Experimental
Mathematics 28 (2019), no. 2, 179–184; arXiv:1803.01925. The bound is also recorded in
teorth/optimizationproblems, `constants/81a.md`.
-/
public theorem_wanted brunConstant_upper_bound :
    brunConstant < 2.288513

end MathlibExt.NumberTheory.PrimeCounting
