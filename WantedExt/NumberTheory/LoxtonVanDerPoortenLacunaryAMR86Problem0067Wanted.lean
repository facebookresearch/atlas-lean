/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Loxton–van der Poorten conjecture on lacunary decimal numbers (Waldschmidt, Conj. 5.4)

M. Waldschmidt, Open Diophantine Problems, Conjecture 5.4 (Loxton and van der Poorten): let
`(n_i)_{i ≥ 0}` be an increasing sequence of positive integers. Assume there is a prime `p` such
that `∑ z^{n_i} ∈ 𝔽_p[[z]]` is algebraic over `𝔽_p(z)` and irrational (not in `𝔽_p(z)`). Then the
real number `∑ 10^{-n_i}` is transcendental.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.LoxtonVanDerPoortenLacunaryAMR86Problem0067Wanted

/-!
Source: M. Waldschmidt, Open Diophantine Problems, Moscow Math. J. 4 (2004), arXiv:math/0312440,
Conjecture 5.4 (Loxton and van der Poorten). UnsolvedMath record UM-08700067 (`AMR-086-0067`),
dataset ulamai/UnsolvedMath v1.8.0.

Algebraicity and rationality of `∑ z^{n_i}` are taken in the field `𝔽_p((z))` of Laurent series,
made an `𝔽_p(z)`-algebra by Mathlib's (scoped) `RatFunc.liftAlgebra`, the embedding of `𝔽_p(z)`
extending `𝔽_p[z] ⊆ 𝔽_p((z))`. Increasing means strictly increasing, and positivity is `0 < n 0`.
Transcendental means over `ℚ`.
-/

/-- The real number `∑_i 10^{-n_i}`. -/
noncomputable def decimalLacunary (n : ℕ → ℕ) : ℝ :=
  ∑' i, (10 : ℝ)⁻¹ ^ n i

open Classical in
/-- The power series `∑_i z^{n_i} ∈ 𝔽_p[[z]]`: the coefficient of `z^k` is `1` if `k` is one of the
`n_i` and `0` otherwise. -/
noncomputable def lacunarySeries (p : ℕ) (n : ℕ → ℕ) : PowerSeries (ZMod p) :=
  PowerSeries.mk fun k => if k ∈ Set.range n then 1 else 0

open scoped RatFunc in
/-- The conjecture of Loxton and van der Poorten in Waldschmidt's form (Open Diophantine Problems,
Conjecture 5.4): let `(n_i)` be an increasing sequence of positive integers and `p` a prime such
that `∑ z^{n_i} ∈ 𝔽_p[[z]]` is algebraic over `𝔽_p(z)` and not in `𝔽_p(z)` (inside the field of
Laurent series `𝔽_p((z))`, an `𝔽_p(z)`-algebra through Mathlib's scoped `RatFunc.liftAlgebra`);
then `∑ 10^{-n_i}` is transcendental. -/
def loxtonVanDerPoortenConjecture : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ → ℕ), StrictMono n → 0 < n 0 →
    IsAlgebraic (RatFunc (ZMod p)) (lacunarySeries p n : LaurentSeries (ZMod p)) →
    (lacunarySeries p n : LaurentSeries (ZMod p)) ∉
      Set.range (algebraMap (RatFunc (ZMod p)) (LaurentSeries (ZMod p))) →
    Transcendental ℚ (decimalLacunary n)

/--
Resolved true: Adamczewski and Bugeaud proved that irrational automatic numbers are transcendental
(Theorem 2) and, with Christol's theorem, that `∑ u_k X^k ∈ 𝔽_p[[X]]` and `∑ u_k b^{-k}` are both
algebraic only when both are rational (Theorem 7); for `u` the indicator of `{n_i}` and `b = 10` an
algebraic irrational series forces `∑ 10^{-n_i}` to be transcendental. Source: M. Waldschmidt, Open
Diophantine Problems, Moscow Math. J. 4 (2004), arXiv:math/0312440, Conjecture 5.4 (Loxton and van
der Poorten); resolution: B. Adamczewski and Y. Bugeaud, On the complexity of algebraic numbers I.
Expansions in integer bases, Ann. of Math. (2) 165 (2007), 547-565, arXiv:math/0511674, Theorem 7
(§7): for b ≥ 2 and p prime, ∑ u_k X^k and ∑ u_k b^{-k} are both algebraic (over 𝔽_p(X) and over ℚ)
if and only if they are rational; with u the indicator of {n_i} and b = 10 this is the conjecture.
Theorem 2 (irrational automatic numbers are transcendental) with Christol's theorem gives Theorem 7,
https://arxiv.org/abs/math/0511674.
-/
public theorem_wanted loxtonVanDerPoortenConjecture_holds : loxtonVanDerPoortenConjecture

end MathlibExt.NumberTheory.LoxtonVanDerPoortenLacunaryAMR86Problem0067Wanted
