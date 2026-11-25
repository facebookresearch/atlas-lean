/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.SpecialFunctions.HypergeometricNIntegrality

@[expose] public section

namespace MathlibExt.Analysis.SpecialFunctions.ChristolHypergeometricIntegralityWanted

open MetaMathlibExt.HypergeometricNIntegrality

/-!
# Christol's criterion and the least hypergeometric rescaling

Wanted statements for E. Delaygue, T. Rivoal and J. Roques, *On
Dwork's `p`-adic formal congruences theorem and hypergeometric
mirror maps*, Mem. Amer. Math. Soc. **246** (2017), no. 1163,
Theorems 3 and 4 (§2.1).  Theorem 3 is Christol's criterion
(G. Christol, *Fonctions hypergéométriques bornées*, Groupe de
Travail d'Analyse Ultramétrique **14** (1986–1987), exp. 8, 1–16),
in the form stated by Delaygue–Rivoal–Roques; their §5.1 derives it
from Christol's Proposition 1, whose original hypotheses are more
restrictive.  All definitions are in
`MathlibExt.Analysis.SpecialFunctions.HypergeometricNIntegrality`.

The proofs are deferred: they need `p`-adic valuation estimates for
rational Pochhammer symbols (Delaygue–Rivoal–Roques, §5), which are
not yet in the library.

Statement notes:

* `NIntegral` requires a *positive* rescaling constant.  The
  source's introductory "there exists `c ∈ ℚ`" cannot include
  `c = 0`, which trivialises the notion, and its least constant is
  taken over positive rationals.
* The source defines its least constant `C_{α,β}` as the least
  positive good scaling.  Theorem 4 is therefore stated as:
  `K • baseConstant` (resp. `baseConstant` itself) is a good scaling
  and is below every positive good scaling.  The source's stronger
  parenthetical that the good scalings are exactly the integer
  multiples of the least one is not included.
* `lambda` counts parameters with `p ∤ den`, the rational form of
  the source's `ℤₚ`-membership count.
-/

/-- **Christol's criterion** (Delaygue–Rivoal–Roques, Theorem 3,
after Christol).  For admissible rational parameters `α β` (no
parameter in `ℤ_{≤ 0}`), the hypergeometric series with coefficients
`pochhammerCoeff α β` is `N`-integral if and only if Christol's
counting function `christolXi α β a x` is nonnegative for every
`a ∈ {1, …, d}` coprime to the denominator lcm `d = paramDenLcm α β`
and every real `x`.

Source: E. Delaygue, T. Rivoal, J. Roques, *On Dwork's `p`-adic
formal congruences theorem and hypergeometric mirror maps*, Mem.
Amer. Math. Soc. **246** (2017), no. 1163, Theorem 3; G. Christol,
*Fonctions hypergéométriques bornées*, Groupe de Travail d'Analyse
Ultramétrique **14** (1986–1987), exp. 8, 1–16. -/
public theorem_wanted christol_criterion (α β : Multiset ℚ)
    (hα : AdmissibleParams α) (hβ : AdmissibleParams β) :
    NIntegral α β ↔
      ∀ a : ℕ, a ∈ Finset.Icc 1 (paramDenLcm α β) →
        Nat.Coprime a (paramDenLcm α β) →
        ∀ x : ℝ, 0 ≤ christolXi α β a x

/-- **Least rescaling, general form** (Delaygue–Rivoal–Roques,
Theorem 4, first part).  If the series is `N`-integral, then for
some positive integer `K`, the product `K * baseConstant α β` is
the least positive good scaling: it makes every coefficient
integral, and no smaller positive rational does.  In general `K`
is not specified further; see `least_scaling_eq_baseConstant` for
the case `K = 1`.

Source: E. Delaygue, T. Rivoal, J. Roques, *On Dwork's `p`-adic
formal congruences theorem and hypergeometric mirror maps*, Mem.
Amer. Math. Soc. **246** (2017), no. 1163, Theorem 4. -/
public theorem_wanted least_scaling_nat_mul_baseConstant (α β : Multiset ℚ)
    (hα : AdmissibleParams α) (hβ : AdmissibleParams β) (hN : NIntegral α β) :
    ∃ K : ℕ, 0 < K ∧ GoodScaling α β ((K : ℚ) * baseConstant α β) ∧
      ∀ C : ℚ, 0 < C → GoodScaling α β C → (K : ℚ) * baseConstant α β ≤ C

/-- **Least rescaling, exact form** (Delaygue–Rivoal–Roques,
Theorem 4, second part).  If `α` and `β` have the same cardinality
and every parameter lies in `(0, 1]`, then `baseConstant α β`
itself is the least positive good scaling.  For example, with
`α = {1/2, 1/2}` and `β = {1, 1}` the base constant is `16`, and
the rescaled coefficients are the squared central binomial
coefficients.

Source: E. Delaygue, T. Rivoal, J. Roques, *On Dwork's `p`-adic
formal congruences theorem and hypergeometric mirror maps*, Mem.
Amer. Math. Soc. **246** (2017), no. 1163, Theorem 4. -/
public theorem_wanted least_scaling_eq_baseConstant (α β : Multiset ℚ)
    (hα : AdmissibleParams α) (hβ : AdmissibleParams β) (hN : NIntegral α β)
    (hcard : α.card = β.card)
    (hα01 : ∀ t ∈ α, 0 < t ∧ t ≤ 1) (hβ01 : ∀ t ∈ β, 0 < t ∧ t ≤ 1) :
    GoodScaling α β (baseConstant α β) ∧
      ∀ C : ℚ, 0 < C → GoodScaling α β C → baseConstant α β ≤ C

end MathlibExt.Analysis.SpecialFunctions.ChristolHypergeometricIntegralityWanted
