/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Servedio–Tan–Verbin junta conjecture (O'Donnell, Problem 24)

R. O'Donnell, Open Problems in Analysis of Boolean Functions, Problem 24 (Servedio–Tan–Verbin
Conjecture, marked disproved in the list): fix any `ε > 0`. Then every monotone `f : {-1,1}ⁿ →
{-1,1}` is `ε`-close to a `poly(deg(f))`-junta.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Logic.Function.DependsOn
public import MathlibExt.Analysis.Fourier.BooleanCube

@[expose] public section

namespace MathlibExt.Combinatorics.MonotoneJuntaApproximationAMR127Problem0022Wanted

/-!
Source: R. O'Donnell, Open Problems in Analysis of Boolean Functions (2012), arXiv:1204.6447,
Problem 24 (Servedio–Tan–Verbin Conjecture). UnsolvedMath record UM-00800453 (`AMR-127-0022`),
dataset ulamai/UnsolvedMath v1.8.0.

Boolean functions are `f : {0,1}ⁿ → {0,1}` on `Fin n → Bool` with the coordinatewise order (`false <
true`), as in Kane's paper; the `{-1,1}` encoding of the source is the same up to relabeling and
does not change monotonicity, distances or degrees. `deg f` is MathlibExt's
`BooleanCube.booleanDegree` (total degree of the unique real multilinear extension, the Fourier
degree). A `poly(d)` bound is written `(d + 2) ^ C`: every polynomial is bounded by such a power for
`d ≥ 0` and conversely. `ε`-close means disagreeing on at most `ε 2ⁿ` inputs, and a `k`-junta is a
function of at most `k` coordinates: Mathlib's `DependsOn g J` with `|J| ≤ k`.
-/

/-- **The Servedio–Tan–Verbin conjecture.** Order $\{0,1\}^n$ coordinatewise with $0 < 1$, and
write $\deg f$ for the Boolean degree of a function $f : \{0,1\}^n \to \{0,1\}$. This is the
statement that for every real $\varepsilon > 0$ there is a natural number $C$ such that for every
$n \in \mathbb{N}$ and every monotone $f : \{0,1\}^n \to \{0,1\}$ there are a set $J$ of at most
$(\deg f + 2)^C$ coordinates and a function $g : \{0,1\}^n \to \{0,1\}$ that depends only on the
coordinates in $J$ such that $f(x) \ne g(x)$ for at most $\varepsilon 2^n$ points
$x \in \{0,1\}^n$.

The junta size $(\deg f + 2)^C$ expresses a polynomial bound in $\deg f$: every polynomial in
$d \ge 0$ is at most $(d + 2)^C$ for some $C$. -/
def servedioTanVerbinConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℕ, ∀ (n : ℕ) (f : (Fin n → Bool) → Bool), Monotone f →
    ∃ (J : Finset (Fin n)) (g : (Fin n → Bool) → Bool),
      J.card ≤ (BooleanCube.booleanDegree f + 2) ^ C ∧ DependsOn g (J : Set (Fin n)) ∧
        ((Finset.univ.filter fun x => f x ≠ g x).card : ℝ) ≤ ε * 2 ^ n

/-- **The Servedio–Tan–Verbin conjecture is false.** Order $\{0,1\}^n$ coordinatewise with
$0 < 1$, and write $\deg f$ for the Boolean degree of a function $f : \{0,1\}^n \to \{0,1\}$. It
is not the case that for every real $\varepsilon > 0$ there is a natural number $C$ such that for
every $n \in \mathbb{N}$ and every monotone $f : \{0,1\}^n \to \{0,1\}$ there are a set $J$ of at
most $(\deg f + 2)^C$ coordinates and a function $g : \{0,1\}^n \to \{0,1\}$ that depends only on
the coordinates in $J$ such that $f(x) \ne g(x)$ for at most $\varepsilon 2^n$ points
$x \in \{0,1\}^n$.

Kane constructed, for a fixed $\varepsilon > 0$, a constant $c > 0$ and every $d$, monotone
functions of decision-tree depth $d$ (hence degree at most $d$) that are $\varepsilon$-far from
every junta on $\exp(c \sqrt{d})$ coordinates; since $\exp(c \sqrt{d})$ eventually exceeds
$(d + 2)^C$, no polynomial junta size works for $\varepsilon / 2$. O'Donnell's list records the
conjecture as resolved in the negative by Kane.

Source: R.
O'Donnell, Open Problems in Analysis of Boolean Functions (2012), arXiv:1204.6447, Problem 24
(Servedio–Tan–Verbin Conjecture); resolution: D. M. Kane, A low-depth monotone function that is not
an approximate junta, arXiv:1206.6541 (2012); recorded as "RESOLVED (in the negative) by Daniel
Kane, 2012" in O'Donnell's list, Problem 24, Kane, Theorem 2: there is a constant ε > 0 such that
for every d there are k = exp(Ω(√d)) and a monotone f : {0,1}ⁿ → {0,1} computed by a depth-d
decision tree (so deg f ≤ d) that disagrees with every k-junta on at least an ε-fraction of inputs,
https://arxiv.org/abs/1206.6541.
-/
public theorem_wanted servedioTanVerbinConjecture_refuted : ¬ servedioTanVerbinConjecture

end MathlibExt.Combinatorics.MonotoneJuntaApproximationAMR127Problem0022Wanted
