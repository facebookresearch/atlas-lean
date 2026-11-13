/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Strong connectivity of tournaments (shared helper)

Strong connectivity and strong `k`-connectivity of subtournaments, for the Open Problem Garden
tournament problems of C. Thomassen (nodes 47031 and 47643). Tournaments on `Fin n` are the
relations of `TransitiveSubtournamentLogErdosProblem1216Wanted.IsTournament`.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Logic.Relation

@[expose] public section

namespace MathlibExt.GraphTheory.TournamentStrongConnectivityShared

/-- The vertex set `W` induces a strongly connected subdigraph of the arc relation `T` on `Fin n`:
for all `u, v ∈ W` there is a directed path from `u` to `v` all of whose vertices lie in `W`.
Mathlib's `Quiver.IsStronglyConnected` is the same notion for a whole quiver; it is needed here for
the subdigraphs induced on vertex subsets `W`, so it is stated with `Relation.ReflTransGen`. -/
def IsStronglyConnectedOn {n : ℕ} (T : Fin n → Fin n → Prop) (W : Finset (Fin n)) : Prop :=
  ∀ u ∈ W, ∀ v ∈ W, Relation.ReflTransGen (fun x y => x ∈ W ∧ y ∈ W ∧ T x y) u v

/-- The subdigraph of `T` induced by `W` is strongly `k`-connected: `|W| > k` and, for every set
`S ⊆ W` of fewer than `k` vertices, `W \ S` induces a strongly connected subdigraph (the definition
of Kühn, Lapinskas, Osthus and Patel, Section 2, and of Kühn, Osthus and Townsend, Section 1). -/
def IsStronglyKConnectedOn {n : ℕ} (T : Fin n → Fin n → Prop) (W : Finset (Fin n)) (k : ℕ) :
    Prop :=
  k < W.card ∧ ∀ S ⊆ W, S.card < k → IsStronglyConnectedOn T (W \ S)

end MathlibExt.GraphTheory.TournamentStrongConnectivityShared
