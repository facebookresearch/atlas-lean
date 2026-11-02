/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MetaMathlibExt

/-! # The abc conjecture
-/

/--
**The abc conjecture.** For every real $\varepsilon > 0$ there is a real $C_\varepsilon > 0$
such that for all integers $a$, $b$, $c$ with $a + b = c$ and $\gcd(a, b) = 1$,
$$\max(|a|, |b|, |c|) \le C_\varepsilon \operatorname{rad}(abc)^{1 + \varepsilon},$$
where $\operatorname{rad}(m)$ is the product of the distinct primes dividing $|m|$, with
$\operatorname{rad}(0) = 1$.

Source: Tsz Ho Chan, "Arithmetic Progressions Among Powerful Numbers",
Journal of Integer Sequences 26 (2023), Article 23.1.1, Conjecture `abc` at
source lines 111–117,
https://cs.uwaterloo.ca/journals/JIS/VOL26/Chan/chan33.tex
-/
public theorem_wanted abc_conjecture :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ a b c : ℤ, a + b = c → Int.gcd a b = 1 →
      ((max (max a.natAbs b.natAbs) c.natAbs : ℕ) : ℝ) ≤
        C * ((∏ p ∈ (a * b * c).natAbs.primeFactors, (p : ℝ)) ^ (1 + ε))

end MetaMathlibExt
