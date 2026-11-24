/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Data.Set.Card

/-! # Bimatrix games and the Lemke–Howson algorithm

A bimatrix game is a two-player game in strategic form given by two payoff matrices `A` and
`B` indexed by the pure strategies `M` of player 1 (rows) and `N` of player 2 (columns); both
players maximise. Mixed strategies are probability vectors (`Convexity.StdSimplex ℝ M` and
`Convexity.StdSimplex ℝ N`), and the expected payoffs of `(x, y)` are `xᵀAy` and `xᵀBy`.

The Lemke–Howson algorithm follows a path of "almost completely labelled" vertex pairs of the
two best-response polytopes, starting from the artificial equilibrium `(0, 0)`. For a
nondegenerate game these pairs and the edges joining them form a graph in which every vertex
has degree `1` or `2`; its degree-`1` vertices are the artificial equilibrium and the Nash
equilibria. A finite graph has an even number of path endpoints, so a nondegenerate bimatrix
game has an *odd* number of Nash equilibria. This is the parity argument that Papadimitriou
abstracted into the class PPAD (Papadimitriou, *Algorithmic Game Theory*, Chapter 2,
Section 2.4).

The statement is recorded as wanted: it needs the combinatorics of the best-response
polytopes, which the repository does not have. Existence of an equilibrium for every bimatrix
game is the two-player case of Nash's theorem, proved from Brouwer's theorem as
`MathlibExt.GameTheory.MixedNashExistence.exists_isMixedNash`.

## References

* C. E. Lemke, J. T. Howson, Jr., "Equilibrium points of bimatrix games", J. SIAM 12 (1964),
  413–423.
* B. von Stengel, "Equilibrium computation for two-player games in strategic and extensive
  form", Chapter 3 of *Algorithmic Game Theory* (Nisan, Roughgarden, Tardos, Vazirani eds.),
  Cambridge University Press 2007: Definition 3.2 (nondegenerate game), Algorithm 3.6
  (Lemke–Howson), Corollary 3.7 (odd number of equilibria).
* C. H. Papadimitriou, "The complexity of finding Nash equilibria", Chapter 2 of the same book,
  Sections 2.3–2.4.
-/

@[expose] public section

namespace MathlibExt.GameTheory.LemkeHowsonWanted

open Convexity

variable {M N : Type*} [Fintype M] [Fintype N]

/-- **Expected payoffs in a bimatrix game.** The expected value `xᵀCy = ∑ᵢ ∑ⱼ xᵢ Cᵢⱼ yⱼ` of the
payoff matrix `C` when player 1 plays the mixed strategy `x` and player 2 independently plays
`y` (von Stengel, *Algorithmic Game Theory*, Section 3.2). -/
noncomputable def bilinPayoff (C : M → N → ℝ) (x : StdSimplex ℝ M) (y : StdSimplex ℝ N) : ℝ :=
  ∑ i, ∑ j, x.weights i * C i j * y.weights j

/-- **Nash equilibrium of a bimatrix game.** The mixed pair `(x, y)` is a Nash equilibrium of
the game `(A, B)` if `x` maximises player 1's expected payoff `x'ᵀAy` against `y` and `y`
maximises player 2's expected payoff `xᵀBy'` against `x` (von Stengel, *Algorithmic Game
Theory*, Section 3.2). -/
def IsBimatrixNash (A B : M → N → ℝ) (x : StdSimplex ℝ M) (y : StdSimplex ℝ N) : Prop :=
  (∀ x' : StdSimplex ℝ M, bilinPayoff A x' y ≤ bilinPayoff A x y) ∧
    ∀ y' : StdSimplex ℝ N, bilinPayoff B x y' ≤ bilinPayoff B x y

/-- **Pure best responses of player 1.** The rows `i` that maximise `(Ay)ᵢ = ∑ⱼ Aᵢⱼ yⱼ`
against the mixed strategy `y` of player 2. -/
noncomputable def bestResponses₁ (A : M → N → ℝ) (y : StdSimplex ℝ N) : Finset M := by
  classical
  exact Finset.univ.filter fun i => ∀ i', ∑ j, A i' j * y.weights j ≤ ∑ j, A i j * y.weights j

/-- **Pure best responses of player 2.** The columns `j` that maximise `(xᵀB)ⱼ = ∑ᵢ xᵢ Bᵢⱼ`
against the mixed strategy `x` of player 1. -/
noncomputable def bestResponses₂ (B : M → N → ℝ) (x : StdSimplex ℝ M) : Finset N := by
  classical
  exact Finset.univ.filter fun j => ∀ j', ∑ i, x.weights i * B i j' ≤ ∑ i, x.weights i * B i j

/-- **Nondegenerate bimatrix game.** No mixed strategy with support of size `k` has more than
`k` pure best responses, for either player (von Stengel, *Algorithmic Game Theory*,
Definition 3.2). -/
def IsNondegenerate (A B : M → N → ℝ) : Prop :=
  (∀ x : StdSimplex ℝ M, (bestResponses₂ B x).card ≤ x.weights.support.card) ∧
    ∀ y : StdSimplex ℝ N, (bestResponses₁ A y).card ≤ y.weights.support.card

/-- **A nondegenerate bimatrix game has an odd number of Nash equilibria.** If both players
have at least one pure strategy and the game `(A, B)` is nondegenerate, then the set of Nash
equilibria `(x, y)` is finite and has odd cardinality. (`Set.ncard` of an infinite set is `0`,
so oddness of `ncard` includes finiteness.)

Source: B. von Stengel, "Equilibrium computation for two-player games in strategic and
extensive form", *Algorithmic Game Theory* (Cambridge University Press 2007), Corollary 3.7,
proved by the Lemke–Howson path-following argument (Algorithm 3.6; C. E. Lemke and
J. T. Howson, J. SIAM 12 (1964), 413–423). -/
theorem_wanted odd_ncard_isBimatrixNash [Nonempty M] [Nonempty N] (A B : M → N → ℝ)
    (h : IsNondegenerate A B) :
    Odd {p : StdSimplex ℝ M × StdSimplex ℝ N | IsBimatrixNash A B p.1 p.2}.ncard

end MathlibExt.GameTheory.LemkeHowsonWanted
