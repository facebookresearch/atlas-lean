/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Totient
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MetaMathlibExt

/-- **Ford's theorem on totient multiplicities.** For every natural number $k \ge 2$ there is a
natural number $m$ such that exactly $k$ natural numbers $x$ satisfy $\varphi(x) = m$, where
$\varphi$ is Euler's totient function.

Source: Kevin Ford, *The Number of Solutions of phi(x) = m*,
Annals of Mathematics 150 (1999), DOI 10.2307/121103.
Also: https://en.wikipedia.org/wiki/Euler%27s_totient_function -/
theorem_wanted ford_totient_multiplicity :
    ∀ k : ℕ, 1 < k → ∃ m : ℕ, Set.ncard {x : ℕ | Nat.totient x = m} = k

end MetaMathlibExt
