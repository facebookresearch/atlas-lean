/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Hawk–Dove game: the unique evolutionarily stable strategy

In the Hawk–Dove game with value of the resource `V > 0` and cost of injury `C > 0`, the
row-player payoff matrix (rows and columns ordered Hawk, Dove) is
`A = [[(V - C) / 2, V], [0, V / 2]]`. A mixed strategy is the probability `p ∈ [0, 1]` of playing
Hawk, that is the vector `(p, 1 - p)` of the two-strategy simplex, with payoff
`E(p, q) = (p, 1 - p) · A (q, 1 - q)` against `q`. In Maynard Smith's sense `p` is an
evolutionarily stable strategy (ESS) if for every `q ≠ p` either `E(q, p) < E(p, p)`, or
`E(q, p) = E(p, p)` and `E(q, q) < E(p, q)`: under `p ↦ (p, 1 - p)` this is the library's
matrix-game predicate `MathlibExt.Biology.Dynamics.Replicator.IsESS`
(`Domains.Biology.Dynamics.ReplicatorStability`) for `A`. Maynard Smith (1982, Ch. 2): if `C > V`
there is no pure ESS and the unique ESS plays Hawk with probability `V / C`; if `V ≥ C`, pure
Hawk is the unique ESS (at `V = C` it meets the first condition with equality and the second
strictly).

Recorded here: the complete ESS characterization for all `V, C > 0`, stated with
`Replicator.IsESS` for the Hawk–Dove matrix at `(p, 1 - p)`. The book was not read; the
statement follows the Encyclopedia of Mathematics entry on evolutionarily stable strategies and
the direct computation `E(q, p) - E(p, p) = (q - p)(V - p C) / 2`; Maynard Smith and Price (1973)
introduce the game but do not contain this result.

Sources: J. Maynard Smith, *Evolution and the Theory of Games*, Cambridge Univ. Press (1982),
Ch. 2; J. Maynard Smith and G. R. Price, "The logic of animal conflict", Nature 246 (1973)
15–18, doi:10.1038/246015a0.
-/
module

public import Batteries.Util.ProofWanted
public import Domains.Biology.Dynamics.ReplicatorStability
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

namespace WantedExt.Biology.Ecology.HawkDoveWanted

open Matrix
open MathlibExt.Biology.Dynamics.Replicator (IsESS)

/-- **Hawk–Dove payoff matrix.** The row player's payoffs `[[(V - C) / 2, V], [0, V / 2]]` for
the value of the resource `V` and the cost of injury `C`, with rows and columns ordered Hawk
(index `0`), Dove (index `1`). The mixed strategy that plays Hawk with probability `p` is the
vector `(p, 1 - p)`, and its expected payoff `(p, 1 - p) · A (q, 1 - q)` against `(q, 1 - q)` is
`p q (V - C)/2 + p (1 - q) V + (1 - p)(1 - q) V/2`. -/
noncomputable def payoffMatrix (V C : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(V - C) / 2, V; 0, V / 2]

/-- **Hawk–Dove with costly fights.** Let `V > 0` and `C > V`. The mixed strategy `(p, 1 - p)`,
which plays Hawk with probability `p`, is an evolutionarily stable state of the Hawk–Dove matrix
game (`Replicator.IsESS` for `payoffMatrix V C`) if and only if `p = V / C`; in particular
neither pure Hawk (`p = 1`) nor pure Dove (`p = 0`) is an ESS.

Source: Maynard Smith (1982), Ch. 2. -/
public theorem_wanted isESS_iff_of_lt (V C : ℝ) (hV : 0 < V) (hVC : V < C) (p : ℝ) :
    IsESS (payoffMatrix V C) ![p, 1 - p] ↔ p = V / C

/-- **Hawk–Dove with cheap fights.** Let `C > 0` and `V ≥ C`. The mixed strategy `(p, 1 - p)`,
which plays Hawk with probability `p`, is an evolutionarily stable state of the Hawk–Dove matrix
game (`Replicator.IsESS` for `payoffMatrix V C`) if and only if `p = 1` (pure Hawk).

Source: Maynard Smith (1982), Ch. 2. -/
public theorem_wanted isESS_iff_of_le (V C : ℝ) (hC : 0 < C) (hCV : C ≤ V) (p : ℝ) :
    IsESS (payoffMatrix V C) ![p, 1 - p] ↔ p = 1

end WantedExt.Biology.Ecology.HawkDoveWanted
