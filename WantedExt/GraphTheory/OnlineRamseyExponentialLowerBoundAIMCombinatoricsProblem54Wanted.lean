/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# An exponential improvement for diagonal online Ramsey numbers (AIM Graph Ramsey theory, Problem 7)

AIM workshop Graph Ramsey theory, Problem 7: show that the online Ramsey number satisfies `r̃(n, n)
≥ (√2 + ε)ⁿ` for some `ε > 0`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Sym.Sym2

@[expose] public section

namespace MathlibExt.GraphTheory.OnlineRamseyExponentialLowerBoundAIMCombinatoricsProblem54Wanted

/-!
Source: AIM workshop Graph Ramsey theory, problem list, https://www.overleaf.com/read/mnvcscjjysvg,
Problem 7 (online Ramsey numbers). UnsolvedMath record UM-20000929 (`AIM-COMBINATORICS-0054`),
dataset ulamai/UnsolvedMath v1.8.0.

The online Ramsey game is the one of Conlon, Fox, Grinshpun and He: on the vertex set `ℕ`, Builder
draws a new edge each turn and Painter colours it red or blue; `r̃(n, n)` is the least number of
turns after which Builder can force a monochromatic `K_n`. Painter's choices are universally
quantified at every move, so `BuilderForcesWithin n k []` says `r̃(n, n) ≤ k`. The bound is read for
all large `n`: `r̃(1, 1) = 0` and `r̃(2, 2) = 1` fail it for every `ε`.
-/

/-- A position of the online Ramsey game on the vertex set `ℕ`: the edges Builder has drawn so
far, each with the colour Painter gave it (`true` red, `false` blue). -/
abbrev OnlineRamseyPosition : Type := List (Sym2 ℕ × Bool)

/-- Some colour class of the position contains a complete graph on `n` vertices. -/
def HasMonochromaticClique (n : ℕ) (P : OnlineRamseyPosition) : Prop :=
  ∃ b : Bool, ∃ S : Finset ℕ, S.card = n ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → (s(x, y), b) ∈ P

/-- From position `P`, Builder can force a monochromatic `K_n` within `k` more moves: each move
draws a new edge `xy` and Painter colours it either way. -/
def BuilderForcesWithin (n : ℕ) : ℕ → OnlineRamseyPosition → Prop
  | 0, P => HasMonochromaticClique n P
  | k + 1, P => HasMonochromaticClique n P ∨
      ∃ x y : ℕ, x ≠ y ∧ (∀ b : Bool, (s(x, y), b) ∉ P) ∧
        ∀ b : Bool, BuilderForcesWithin n k ((s(x, y), b) :: P)

/-- The AIM question (Graph Ramsey theory, Problem 7): for some `ε > 0` the diagonal online
Ramsey number satisfies `r̃(n, n) ≥ (√2 + ε)ⁿ` for all large `n`, i.e. Builder cannot force a
monochromatic `K_n` from the empty position in fewer than `(√2 + ε)ⁿ` moves. -/
def onlineRamseyExceedsSqrtTwoPower : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ k : ℕ,
    BuilderForcesWithin n k [] → (Real.sqrt 2 + ε) ^ n ≤ k

/--
Resolved true: Conlon, Fox, Grinshpun and He proved `r̃(n, n) ≥ 2^{(2 - √2) n - O(1)}` (Corollary
2), an exponential improvement on the classical `2^{n/2 - 1}`; since `2^{2 - √2} ≈ 1.5009 > √2`,
this gives the bound with any `ε < 2^{2 - √2} - √2` for large `n`. Source: AIM workshop Graph Ramsey
theory, problem list, https://www.overleaf.com/read/mnvcscjjysvg, Problem 7 (online Ramsey numbers);
resolution: D. Conlon, J. Fox, A. Grinshpun and X. He, Online Ramsey numbers and the subgraph query
problem, in Building Bridges II, Bolyai Soc. Math. Stud., Springer (2019), 159-194,
arXiv:1806.09726, Corollary 2: r̃(n) ≥ 2^{(2 - √2) n - O(1)} for the diagonal online Ramsey numbers
(from Theorem 1 with Painter playing randomly); 2^{2 - √2} ≈ 1.5009 > √2,
https://doi.org/10.1007/978-3-662-59204-5_4.
-/
public theorem_wanted onlineRamseyExceedsSqrtTwoPower_holds : onlineRamseyExceedsSqrtTwoPower

end MathlibExt.GraphTheory.OnlineRamseyExponentialLowerBoundAIMCombinatoricsProblem54Wanted
