/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
EP-190: let H(k) be the smallest N such that in any finite colouring of
{1, ..., N} there is a monochromatic k-term arithmetic progression or a
rainbow k-term arithmetic progression. Does H(k)^(1/k) / k tend to infinity
as k tends to infinity?

Colourings are formalized as functions `ℕ → ℕ` (any number of colours),
with the interval condition that every progression term lies in `[0, N)`.
Since only finitely many values occur on a finite interval, this agrees
with finite colourings of `{1, ..., N}` up to translation. If no witness
`N` exists, `H k` defaults to `0`; the cases `k = 0, 1` are degenerate.
The trailing survey clause "Estimate H(k)" is not formalized.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosRainbowAPGrowthWanted

/-! Source record `EP-190`. -/
open Filter

/-- **Good arithmetic progressions.** Let $f : \mathbb{N} \to \mathbb{N}$ be a colouring and let
$N$ and $k$ be natural numbers. The colouring $f$ has a good $k$-term arithmetic progression below
$N$ if there are natural numbers $a$ and $d > 0$ with $a + d(k - 1) < N$, where $k - 1$ is
natural-number subtraction (so it is $0$ when $k = 0$), such that the colours $f(a + di)$ for
$i < k$ are either all equal (the progression is monochromatic) or pairwise distinct (it is
rainbow). For $k \ge 1$ the condition $a + d(k - 1) < N$ says that every term $a + di$ with
$i < k$ lies in $\{0, \dots, N - 1\}$. -/
def HasGoodAP (f : ℕ → ℕ) (N k : ℕ) : Prop :=
  ∃ a d : ℕ,
    0 < d ∧
      a + d * (k - 1) < N ∧
        ((∀ i j : Fin k, f (a + d * (i : ℕ)) = f (a + d * (j : ℕ))) ∨
          ∀ i j : Fin k, i ≠ j → f (a + d * (i : ℕ)) ≠ f (a + d * (j : ℕ)))

/-- **Monochromatic-or-rainbow progression number.** For a natural number $k$, $H(k)$ is the least
natural number $N$ such that every colouring $f : \mathbb{N} \to \mathbb{N}$ has a good $k$-term
arithmetic progression below $N$, that is, there are natural numbers $a$ and $d > 0$ with
$a + d(k - 1) < N$, where $k - 1$ is natural-number subtraction, such that the colours $f(a + di)$
for $i < k$ are all equal or pairwise distinct. If no such $N$ exists, then $H(k) = 0$. -/
noncomputable def H (k : ℕ) : ℕ :=
  haveI := Classical.propDecidable (∃ N, ∀ f : ℕ → ℕ, HasGoodAP f N k)
  if h : ∃ N, ∀ f : ℕ → ℕ, HasGoodAP f N k then
    @Nat.find (fun N => ∀ f : ℕ → ℕ, HasGoodAP f N k) (Classical.decPred _) h
  else
    0

/-- **Erdős Problem 190 on monochromatic or rainbow progressions.** For a natural number $k$, let
$H(k)$ be the least natural number $N$ such that every colouring $f : \mathbb{N} \to \mathbb{N}$
has a good $k$-term arithmetic progression below $N$, that is, there are natural numbers $a$ and
$d > 0$ with $a + d(k - 1) < N$, where $k - 1$ is natural-number subtraction, such that the colours
$f(a + di)$ for $i < k$ are all equal or pairwise distinct; let $H(k) = 0$ if no such $N$ exists.
The proposition asserts that $H(k)^{1/k}/k \to \infty$ as $k \to \infty$. -/
def conjecture : Prop :=
  Tendsto (fun k : ℕ => ((H k : ℝ) ^ ((k : ℝ)⁻¹)) / (k : ℝ)) atTop atTop

/--
**Solution of Erdős Problem 190 on monochromatic or rainbow progressions.** For a natural number
$k$, let $H(k)$ be the least natural number $N$ such that every colouring
$f : \mathbb{N} \to \mathbb{N}$ has a good $k$-term arithmetic progression below $N$, that is,
there are natural numbers $a$ and $d > 0$ with $a + d(k - 1) < N$, where $k - 1$ is natural-number
subtraction, such that the colours $f(a + di)$ for $i < k$ are all equal or pairwise distinct;
let $H(k) = 0$ if no such $N$ exists. Then $H(k)^{1/k}/k \to \infty$ as $k \to \infty$.

This answers Erdős Problem 190 affirmatively; it was proved by Bae and, independently, by Fox and
Hunter.

Source: T. F. Bloom, Erdős Problem #190,
erdosproblems.com (live page, LaTeX source and forum threads read 2026-10-22),
https://www.erdosproblems.com/190; J. H. Bae, A resolution of Erdős Problem #190 via
Erdős-Lovász, BCT, and Baker-Harman-Pintz, arXiv:2604.20588 (2026),
https://arxiv.org/abs/2604.20588; J. Fox and Z. Hunter, Three-color van der Waerden numbers grow
super-exponentially, arXiv:2606.02541 (2026), https://arxiv.org/abs/2606.02541. Moved from
`OpenConjectures/Combinatorics/ErdosRainbowAPGrowth`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.ErdosRainbowAPGrowthWanted
