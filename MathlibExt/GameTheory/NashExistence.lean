/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.MixedNashExistence

/-!
# Nash's theorem, proved from Brouwer's fixed-point theorem

A finite strategic game has finitely many players `ι`, a finite nonempty strategy set `S i`
for every player and payoffs `u i : (∀ j, S j) → ℝ`, which players maximise. A mixed strategy
of player `i` is a probability vector on `S i` (a `Convexity.StdSimplex ℝ (S i)`); players
randomise independently, so the expected payoff of a mixed profile `σ` is
`∑ₛ (∏ⱼ σⱼ(sⱼ)) uᵢ(s)`. Every finite game has a mixed Nash equilibrium.

The proof is Nash's 1951 argument: on the product of the players' mixed-strategy simplices
define

  `σᵢ'(t) = (σᵢ(t) + gᵢ(t)) / (1 + ∑ₜ' gᵢ(t'))`,  with  `gᵢ(t) = max(0, vᵢ(t, σ) - uᵢ(σ))`,

where `uᵢ(σ)` is player `i`'s expected payoff and `vᵢ(t, σ)` the payoff of the pure strategy `t`
against the others' mixed strategies. The map is continuous, so it has a fixed point by
Brouwer's theorem. At a fixed point every gain `gᵢ(t)` vanishes: some pure strategy in the
support of `σᵢ` does no better than `σᵢ`, so its gain is `0`, and the fixed-point equation for it
forces `∑ₜ' gᵢ(t') = 0`. Since expected payoff is linear in a player's own mixed strategy, no
mixed deviation is profitable either. The argument is carried out in
`MathlibExt.GameTheory.MixedNashExistence`, from which the declarations here are restated.

The two-player zero-sum case is von Neumann's minimax theorem, proved in MathlibExt as
`matrixGame_exists_isSaddlePointOn`; games with an exact potential have pure equilibria
(`MathlibExt.GameTheory.PotentialGame.IsExactPotential.exists_isPureNash`).

## Relation to `MathlibExt.GameTheory.MixedNashExistence`

`expectedPayoff`, `IsMixedNash` and `exists_isMixedNash` restate that module's declarations of
the same names: the two definitions are abbreviations of that module's, and the theorem is
proved from that module's `exists_isMixedNash`. They are kept as this library's entry points
(see #4334). That module applies Nash's map to probability vectors in `∀ i, A i → ℝ` and takes
the fixed point from Brouwer's theorem for compact convex sets
(`MathlibExt.Analysis.Convex.BrouwerFixedPoint.exists_fixedPoint`).

## References

* J. Nash, "Equilibrium points in n-person games", Proc. Natl. Acad. Sci. USA 36 (1950),
  48–49.
* J. Nash, "Non-cooperative games", Ann. of Math. 54 (1951), 286–295, Theorem 1 and its proof.
* C. H. Papadimitriou, "The complexity of finding Nash equilibria", Chapter 2 of *Algorithmic
  Game Theory* (Cambridge University Press 2007), Section 2.2.1 (Nash's proof as a reduction to
  Brouwer) and Theorem 2.1 (best responses and supports).
-/

@[expose] public section

namespace MathlibExt.GameTheory.NashExistence

open Convexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)]

/-- The expected payoff of player `i` when every player `j` independently plays the mixed
strategy `σ j` (Nash 1951, §2): `∑ₛ (∏ⱼ σⱼ(sⱼ)) uᵢ(s)`.

Same definition as `MathlibExt.GameTheory.MixedNashExistence.expectedPayoff`; kept as this
library's entry point; see #4334. -/
abbrev expectedPayoff (u : ι → (∀ j, S j) → ℝ) (σ : ∀ j, StdSimplex ℝ (S j)) (i : ι) : ℝ :=
  MixedNashExistence.expectedPayoff u σ i

/-- The mixed profile `σ` is a Nash equilibrium: no player can raise its expected payoff by
switching to another mixed strategy while the others keep theirs (Nash 1951, §2, "equilibrium
point").

Same definition as `MathlibExt.GameTheory.MixedNashExistence.IsMixedNash`; kept as this
library's entry point; see #4334. -/
abbrev IsMixedNash (u : ι → (∀ j, S j) → ℝ) (σ : ∀ j, StdSimplex ℝ (S j)) : Prop :=
  MixedNashExistence.IsMixedNash u σ

/-- **Nash's theorem.** Every finite game, with finitely many players and finitely many (and
at least one) pure strategies for each, has a mixed Nash equilibrium.

Source: J. Nash, "Non-cooperative games", Ann. of Math. 54 (1951), 286–295, Theorem 1
("Every finite game has an equilibrium point"); announced in Proc. Natl. Acad. Sci. USA 36
(1950), 48–49.

Same statement as `MathlibExt.GameTheory.MixedNashExistence.exists_isMixedNash`; kept as this
library's entry point; see #4334. -/
theorem exists_isMixedNash [∀ i, Nonempty (S i)] (u : ι → (∀ j, S j) → ℝ) :
    ∃ σ : ∀ j, StdSimplex ℝ (S j), IsMixedNash u σ :=
  MixedNashExistence.exists_isMixedNash u

end MathlibExt.GameTheory.NashExistence
