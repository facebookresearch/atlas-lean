/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The secant conjecture, divisor form (Eremenko, Disconjugacy and the Secant Conjecture)

A. Eremenko, Disconjugacy and the Secant Conjecture, Arnold Math. J. 1 (2015): let `m, p ≥ 2`, `d =
m + p - 1` and `F(x) = (1, x, …, x^d)`. Suppose each of the `mp` subspaces `X_j` is spanned by `p`
distinct real vectors `F(x_{j,k})` and the sets `{x_{j,k}}` are separated, i.e. `x_{j,k} ∈ I_j` for
disjoint intervals `I_j ⊂ ℝℙ¹`. Then all `m`-subspaces which intersect all `X_j` non-trivially are
real.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.SecantConjectureDivisorFormAMR17Problem0002Wanted

/-!
Source: A. Eremenko, Disconjugacy and the Secant Conjecture, Arnold Math. J. 1 (2015), Secant
Conjecture, https://amj.math.stonybrook.edu/html-articles/Files-2015-2024/15-23/. UnsolvedMath
record UM-01800002 (`AMR-017-0002`), dataset ulamai/UnsolvedMath v1.8.0.

Subspaces of `ℂ^{m+p}` (`d + 1 = m + p`); a complex subspace is real when it is stable under
coordinatewise conjugation (equivalently, spanned by real vectors). The parameters `x_{j,k}` are
real and distinct within each block. An interval of `ℝℙ¹` meets `ℝ` in an interval or, when it
contains `∞`, in a set whose complement in `ℝ` is an interval, hence the condition `(I
j).OrdConnected ∨ (I j)ᶜ.OrdConnected` with pairwise disjoint `I j`.
-/

/-- The rational normal (moment) curve `F(x) = (1, x, x², …, x^{N-1})` in `ℂ^N`, at a real
parameter `x`. -/
noncomputable def momentCurve (N : ℕ) (x : ℝ) : Fin N → ℂ :=
  fun i => (x : ℂ) ^ (i : ℕ)

/-- A complex subspace of `ℂ^N` is real (defined over `ℝ`) when it is stable under coordinatewise
complex conjugation. -/
def IsRealSubspace {N : ℕ} (Y : Submodule ℂ (Fin N → ℂ)) : Prop :=
  ∀ v ∈ Y, (fun i => star (v i)) ∈ Y

/-- The secant conjecture as stated by Eremenko: for `m, p ≥ 2`, `d = m + p - 1`, and `mp` real
parameter blocks `x_{j,0}, …, x_{j,p-1}` (distinct within each block) lying in pairwise disjoint
intervals of `ℝℙ¹` (an interval of `ℝ`, or the trace on `ℝ` of an arc through `∞`, i.e. a set
whose complement in `ℝ` is an interval), every complex `m`-dimensional subspace of `ℂ^{d+1}` that
meets each secant `p`-plane `X_j = span (F(x_{j,0}), …, F(x_{j,p-1}))` non-trivially is real. -/
def secantConjecture : Prop :=
  ∀ m p : ℕ, 2 ≤ m → 2 ≤ p → ∀ x : Fin (m * p) → Fin p → ℝ, (∀ j, Function.Injective (x j)) →
    (∃ I : Fin (m * p) → Set ℝ, (∀ j, (I j).OrdConnected ∨ (I j)ᶜ.OrdConnected) ∧
        Pairwise (Function.onFun Disjoint I) ∧ ∀ j k, x j k ∈ I j) →
      ∀ Y : Submodule ℂ (Fin (m + p) → ℂ), Module.finrank ℂ Y = m →
        (∀ j, Y ⊓ Submodule.span ℂ (Set.range fun k => momentCurve (m + p) (x j k)) ≠ ⊥) →
          IsRealSubspace Y

/--
Resolved true: Karp and Purbhoo proved the divisor form of the secant conjecture (Theorem 1.8,
cyclic intervals of `ℝℙ¹` allowed in this rectangular case): every `m`-dimensional complex subspace
meeting the `mp` separated secant `p`-planes non-trivially is real. Source: A. Eremenko,
Disconjugacy and the Secant Conjecture, Arnold Math. J. 1 (2015), Secant Conjecture,
https://amj.math.stonybrook.edu/html-articles/Files-2015-2024/15-23/; resolution: S. N. Karp and K.
Purbhoo, Universal Plücker coordinates for the Wronski map and positivity in real Schubert calculus,
J. Amer. Math. Soc. (2026), DOI 10.1090/jams/1087, arXiv:2309.04645; Eremenko's unsolved-problems
page: 'Steven Karp and Kevin Purbhoo solved it completely, accepted in JAMS', arXiv:2309.04645v2,
Theorem 1.8 (secant conjecture, divisor form): for pairwise disjoint real intervals I_1, …, I_n and
generalized secants W_i ∈ Gr(m - d, m) to the moment curve along I_i, the Schubert problem has
exactly f_ν distinct solutions and all solutions are real; for ν the full rectangle and n = d(m - d)
(Eremenko's setting) it remains true for cyclic intervals of ℝℙ¹ (remark after Theorem 1.8, via the
PGL₂-action); the abstract lists the disconjugacy conjecture of Eremenko (2015) and the divisor form
of the secant conjecture among the verified conjectures, https://arxiv.org/abs/2309.04645.
-/
public theorem_wanted secantConjecture_holds : secantConjecture

end MathlibExt.AlgebraicGeometry.SecantConjectureDivisorFormAMR17Problem0002Wanted
