/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# AMR 22, Problem 4015
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.RingTheory.SimpleRing.Principal
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Analysis.AMR22Problem4015Wanted

/-! Source record `UM-02304015-Q001`. -/
open Polynomial

/-- `P(z) = ∑_{k=1}^n ε_k z^k` with `ε_k ∈ {-1, 1}`, encoded via `Bool` (true = 1, false = -1);
the exponents are `i.val + 1` for `i : Fin n`, i.e. `1, ..., n`. -/
noncomputable def signPoly (n : ℕ) (sgn : Fin n → Bool) : Polynomial ℂ :=
  ∑ i : Fin n, Polynomial.C (if sgn i then (1 : ℂ) else (-1 : ℂ)) * Polynomial.X ^ (i.val + 1)

/-- The number of zeros in the open unit disc `D = {z : ℂ | ‖z‖ < 1}`, counted with multiplicity:
the multiset of complex roots, filtered by `‖z‖ < 1`. -/
noncomputable def discRootCount (p : Polynomial ℂ) : ℕ :=
  (p.roots.filter (fun z : ℂ => ‖z‖ < 1)).card

/-- For large `n`, all but `o(2^n)` of the `2^n` sign polynomials have `n/2 + o(n)` zeros in `D`:
for all `ε, δ > 0`, eventually fewer than `ε·2^n` sign patterns have `|count - n/2| ≥ δ·n`.
"For large `n`" is `∃ N, ∀ n ≥ N`, and `N` may depend on both `ε` and `δ` (the `o(2^n)` and
`o(n)` bounds). -/
def conjecture : Prop :=
  ∀ (epsOuter : ℝ), epsOuter > 0 → ∀ (delta : ℝ), delta > 0 →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ((Finset.univ.filter (fun sgn : Fin n → Bool =>
        |(discRootCount (signPoly n sgn) : ℝ) - (n : ℝ) / 2| ≥ delta * (n : ℝ))).card : ℝ)
        < epsOuter * ((2 : ℝ) ^ n)

-- Carried source audit `UM-02304015-Q001` (see the Moved/ record).

/--
Resolved true: Yakir (Studia Math. 261 (2021) 227-240, arXiv:2011.06234) proved that all but
o(2^n) Littlewood polynomials sum_{k<n} ±z^k have n/2 + O(n^{9/10}) roots in the open unit disk.
Multiplying by z adds one root at 0, giving the Lean target. Source: Oren Yakir, Approximately
half of the roots of a random Littlewood polynomial are inside the disk, Studia Mathematica 261
(2021) 227-240, arXiv:2011.06234, https://arxiv.org/abs/2011.06234. Moved from
`OpenConjectures/Analysis/AMR22Problem4015`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Analysis.AMR22Problem4015Wanted
