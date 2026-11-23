/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Hawaii conjecture for G₁ (Shapiro, Conjecture 11)

B. Shapiro, Problems around polynomials, Conjecture 11: for any real polynomial `p(x)` of degree `k`
with simple real zeros, `#_r[(k - 1)(p′(x))² - k p(x) p″(x)] ≤ #_nr p(x)`, i.e. the Hawaii
conjecture holds for `G₁(x)` as well (`#_r`, `#_nr`: numbers of real and non-real zeros).
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

namespace MathlibExt.Algebra.WeightedHawaiiConjectureAMR21Problem0018Wanted

/-!
Source: B. Shapiro, Problems around polynomials: the good, the bad and the ugly..., Arnold Math. J.
1 (2015), arXiv:1503.05295, Conjecture 11 (B. Shapiro). UnsolvedMath record UM-02200018
(`AMR-021-0018`), dataset ulamai/UnsolvedMath v1.8.0.

As in Shapiro's statement of the Hawaii conjecture ('any real polynomial with simple real zeros (and
arbitrary complex-conjugate pairs of zeros)'), `p` ranges over real polynomials all of whose real
zeros are simple (`p.roots.Nodup`), with arbitrary non-real zeros. Zeros are counted with
multiplicity, as in the Hawaii conjecture and in Tyaglov–Atia and Katkova–Tyaglov–Vishnyakova
(`Z_R`, `Z_C` count multiplicities); the counterexamples below rely on it. The non-real zeros of `p`
are its complex roots with non-zero imaginary part. The degree is `k ≥ 2` as in
Katkova–Tyaglov–Vishnyakova's Conjecture 1.4 (for `k ≤ 1` the polynomial `G₁` vanishes).
-/

open Polynomial

/-- Shapiro's Conjecture 11 ("Hawaiian" conjecture for `G₁`): for every real polynomial `p` of
degree `k ≥ 2` all of whose real zeros are simple (`p.roots.Nodup`; non-real zeros are
arbitrary), the number of real zeros of `G₁ = (k - 1) (p')² - k p p''` is at most the number of
non-real zeros of `p`, both counted with multiplicity. -/
def weightedHawaiiConjecture : Prop :=
  ∀ p : ℝ[X], 2 ≤ p.natDegree → p.roots.Nodup →
    Multiset.card (((p.natDegree : ℝ) - 1) • derivative p ^ 2 -
        (p.natDegree : ℝ) • (p * derivative (derivative p))).roots ≤
      Multiset.card ((p.map (algebraMap ℝ ℂ)).roots.filter fun z => z.im ≠ 0)

/--
Resolved false: for `p(x) = (x² + a²)(x + a²)(x - 1)` with `a ∉ {-1, 0, 1}` (degree 4, simple real
zeros `-a²` and `1`, non-real zeros `±ia`), Tyaglov and Atia show `(4/3) H_{3/4}[p] = [(a - 1)x -
a(a + 1)]² [(a + 1)x + a(a - 1)]²` with `G₁ = 4 H_{3/4}[p]`, so `G₁` has four real zeros counted
with multiplicity against two non-real zeros of `p`; Katkova, Tyaglov and Vishnyakova give
counterexamples in every degree `n ≥ 5`. Source: B. Shapiro, Problems around polynomials: the good,
the bad and the ugly..., Arnold Math. J. 1 (2015), arXiv:1503.05295, Conjecture 11 (B. Shapiro);
resolution: M. Tyaglov and M. J. Atia, On the number of non-real zeroes of a homogeneous
differential polynomial and a generalisation of the Laguerre inequalities, J. Math. Anal. Appl. 494
(2021), no. 2, 124652, DOI 10.1016/j.jmaa.2020.124652; O. Katkova, M. Tyaglov and A. Vishnyakova,
Some generalizations of the Hawaii conjecture and beyond, Complex Anal. Oper. Theory 19 (2025), DOI
10.1007/s11785-025-01664-z, arXiv:2406.00686, Theorem C of Katkova–Tyaglov–Vishnyakova (attributed
to Tyaglov–Atia and reproved in their §3): for p(x) = (x² + a²)(x + a²)(x - 1), a ∉ {-1, 0, 1},
(4/3) H_{3/4}[p] = [(a - 1)x - a(a + 1)]² [(a + 1)x + a(a - 1)]² has Z_R = 4 > 2 = Z_C(p), where
H_κ[p] = κ(p′)² - p p″, so that G₁ = 4 H_{3/4}[p] in degree 4; their Proposition 2.1: p(x) = (x -
1)ⁿ + (x + 1)ⁿ is a counterexample for every n ≥ 5, https://doi.org/10.1016/j.jmaa.2020.124652.
-/
public theorem_wanted weightedHawaiiConjecture_refuted : ¬ weightedHawaiiConjecture

end MathlibExt.Algebra.WeightedHawaiiConjectureAMR21Problem0018Wanted
