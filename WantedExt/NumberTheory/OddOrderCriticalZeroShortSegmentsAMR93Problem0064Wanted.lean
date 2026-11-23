/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Odd-order zeros of ζ(1/2 + it) between T and T + T^(1/4 + ε) (first Hardy–Littlewood conjecture)

The first of the 'Hardy–Littlewood zeta function conjectures' as listed by Wikipedia: for every ε >
0 there is T₀(ε) such that for T ≥ T₀ and H = T^(1/4 + ε) the interval (T, T + H] contains a zero of
odd order of ζ(1/2 + it). Despite the name it is a theorem of Hardy and Littlewood (Acta Math. 41,
Theorem 4.41).
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.NumberTheory.LSeries.RiemannZeta

@[expose] public section

namespace MathlibExt.NumberTheory.OddOrderCriticalZeroShortSegmentsAMR93Problem0064Wanted

/-!
Source: Wikipedia, Hardy–Littlewood zeta function conjectures, conjecture 1 (revision 1366636767),
as listed in Wikipedia's List of unsolved problems in mathematics; the statement is Theorem 4.41 of
G. H. Hardy and J. E. Littlewood, Contributions to the theory of the Riemann zeta-function and the
theory of the distribution of primes, Acta Math. 41 (1916), 119-196. UnsolvedMath record UM-09400064
(`AMR-093-0064`), dataset ulamai/UnsolvedMath v1.8.0.

A zero of odd order of ζ(1/2 + it) at `t` is a point where the order of vanishing of `riemannZeta`
at `s = 1/2 + it` (`analyticOrderNatAt`; ζ is analytic away from `s = 1`) is odd. An odd natural
number is positive, and the order is then finite: an identically vanishing germ or a non-zero value
gives `analyticOrderNatAt = 0`. The order of `t ↦ ζ(1/2 + it)` at `t` is the order of ζ at `1/2 +
it` (affine change of variable). The interval is the record's half-open `(T, T + T^(1/4 + ε)]`, for
every `T > T₀(ε)`. This implies the closed-segment form of Hardy–Littlewood's Theorem 4.41 (from
`1/2 + iT` to `1/2 + i(T + T^(1/4 + ε))`) and follows from it, applied with `ε / 2` at `T + 1`.
-/

open Complex

/-- `t` is the ordinate of a zero of odd order of the Riemann zeta function on the critical line:
the order of vanishing of `riemannZeta` at `1/2 + i t` is odd (in particular finite and positive;
an infinite order or a non-zero value gives `analyticOrderNatAt = 0`, which is even). -/
noncomputable def IsOddOrderCriticalZero (t : ℝ) : Prop :=
  Odd (analyticOrderNatAt riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I))

/-- Hardy–Littlewood (Acta Math. 41, Theorem 4.41), in the record's half-open form: for every
`ε > 0` there is `T₀` such that for every `T > T₀` some `t` with `T < t ≤ T + T^{1/4 + ε}` is the
ordinate of a zero of `ζ` of odd order on the critical line. -/
def oddOrderZeroInShortSegments : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ < T →
    ∃ t ∈ Set.Ioc T (T + T ^ ((1 : ℝ) / 4 + ε)), IsOddOrderCriticalZero t

/--
Resolved true: the 'conjecture' is a theorem of Hardy and Littlewood (Acta Math. 41, Theorem 4.41):
for every ε > 0 there is T₀(ε) such that for every T > T₀(ε) the segment of the critical line from
1/2 + iT to 1/2 + i(T + T^(1/4 + ε)) contains a zero of ζ of odd order, and the half-open form
stated here follows by applying this with ε / 2 at T + 1. Source: Wikipedia,
Hardy–Littlewood zeta function conjectures, conjecture 1 (revision 1366636767), as listed in
Wikipedia's List of unsolved problems in mathematics; the statement is Theorem 4.41 of G. H. Hardy
and J. E. Littlewood, Contributions to the theory of the Riemann zeta-function and the theory of the
distribution of primes, Acta Math. 41 (1916), 119-196; resolution: G. H. Hardy and J. E. Littlewood,
Contributions to the theory of the Riemann zeta-function and the theory of the distribution of
primes, Acta Math. 41 (1916), 119-196, Theorem 4.41: 'Let ε be any positive number. Then there is a
number T₀(ε) such that the segment (1/2 + Ti, 1/2 + (T + T^(1/4+ε))i), where T > T₀(ε), contains at
least one zero of ζ(s) of odd order'; §4.1 announces it as 'at least one zero of odd order between T
and T + T^(1/4+ε) for all sufficiently large values of T' (open copy at
projecteuclid.org/euclid.acta/1485887467), https://doi.org/10.1007/BF02422942.
-/
public theorem_wanted oddOrderZeroInShortSegments_holds : oddOrderZeroInShortSegments

end MathlibExt.NumberTheory.OddOrderCriticalZeroShortSegmentsAMR93Problem0064Wanted
