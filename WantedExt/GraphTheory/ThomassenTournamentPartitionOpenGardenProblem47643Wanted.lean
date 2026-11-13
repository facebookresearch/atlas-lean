/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Partitioning a tournament into strongly connected subtournaments (Open Problem Garden 47643)

Open Problem Garden, Partitionning a tournament into k-strongly connected subtournaments (C.
Thomassen): for positive integers `k₁, …, k_p`, is there `g(k₁, …, k_p)` such that every `g(k₁, …,
k_p)`-strong tournament `T` has a partition `(V₁, …, V_p)` of its vertex set with `T[Vᵢ]` a
non-trivial `kᵢ`-strong tournament for every `i`?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.Combinatorics.TransitiveSubtournamentLogErdosProblem1216Wanted
public import WantedExt.GraphTheory.TournamentStrongConnectivityShared

@[expose] public section

namespace MathlibExt.GraphTheory.ThomassenTournamentPartitionOpenGardenProblem47643Wanted

/-!
Source: Open Problem Garden, Partitionning a tournament into k-strongly connected subtournaments
(node 47643; C. Thomassen),
http://www.openproblemgarden.org/op/partitionning_a_tournament_into_k_strongly_connected_subtournaments.
UnsolvedMath record UM-00003279 (`OPG-47643`), dataset ulamai/UnsolvedMath v1.8.0.

`k`-strong means strongly `k`-connected: more than `k` vertices and strongly connected after
deleting any fewer than `k` vertices (Kühn-Osthus-Townsend, Section 1). Since every `kᵢ ≥ 1`, a
`kᵢ`-strong part has at least two vertices, so "non-trivial" adds nothing. The number of parts is `t
≥ 1` (for `t = 0` no partition of a nonempty vertex set exists). The partition is a map `part : Fin
n → Fin t` with classes `Vᵢ = part⁻¹(i)`.
-/

open MathlibExt.Combinatorics.TransitiveSubtournamentLogErdosProblem1216Wanted
open MathlibExt.GraphTheory.TournamentStrongConnectivityShared

/-- Thomassen's problem, answered affirmatively: for positive integers `k₁, …, k_t` (`t ≥ 1`) there
is `g` such that every strongly `g`-connected tournament `T` has a partition `V₁, …, V_t` of its
vertex set with `T[Vᵢ]` strongly `kᵢ`-connected for every `i`. -/
def thomassenTournamentPartition : Prop :=
  ∀ (t : ℕ), 0 < t → ∀ k : Fin t → ℕ, (∀ i, 0 < k i) → ∃ g : ℕ,
    ∀ (n : ℕ) (T : Fin n → Fin n → Prop), IsTournament T →
      IsStronglyKConnectedOn T Finset.univ g →
        ∃ part : Fin n → Fin t,
          ∀ i, IsStronglyKConnectedOn T (Finset.univ.filter fun v => part v = i) (k i)

/--
Resolved true: Kühn, Osthus and Townsend proved (Theorem 1.2) that every strongly `10⁷ k⁶ t³ log(k
t²)`-connected tournament has a vertex partition into `t` strongly `k`-connected subtournaments, and
state that this answers all cases of Thomassen's problem with `k₁, …, k_t` in the affirmative.
Source: Open Problem Garden, Partitionning a tournament into k-strongly connected subtournaments
(node 47643; C. Thomassen),
http://www.openproblemgarden.org/op/partitionning_a_tournament_into_k_strongly_connected_subtournaments;
resolution: D. Kühn, D. Osthus and T. Townsend, Proof of a tournament partition conjecture and an
application to 1-factors with prescribed cycle lengths, Combinatorica 36 (2016), 451-469,
doi:10.1007/s00493-015-3186-8; arXiv:1309.7677, Problem 1.1 (Thomassen's problem with k_1, ..., k_t)
and the sentence after it: 'Our main result answers all cases of the above problem of Thomassen in
the affirmative'; Theorem 1.2: for t ≥ 2 every strongly 10^7 k^6 t^3 log(kt^2)-connected tournament
has a partition into t classes each inducing a strongly k-connected subtournament,
https://doi.org/10.1007/s00493-015-3186-8.
-/
public theorem_wanted thomassenTournamentPartition_holds : thomassenTournamentPartition

end MathlibExt.GraphTheory.ThomassenTournamentPartitionOpenGardenProblem47643Wanted
