/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Perfect phylogeny is polynomial for a fixed number of states

For an `n × m` character-state matrix with states in a finite type, a
c-cluster is a set of taxa sharing one state in one character. There are at
most `2^r * m` of them (`r` the number of states). A perfect phylogeny exists
exactly when the c-clusters are laminar, and the Agarwala-Fernandez-Baca
procedure runs in `O(2^(3r) * (n * m^3 + m^4))` time: polynomial for fixed
`r` (indeed for `r = O(log (m + n))`). The time bound itself needs a RAM
cost model and is context here, not a formal claim.

Overlap (partial): `CSLibExt/Bioinformatics/Phylogenetics/Splits.lean`
`exists_perfectPhylogeny_iff` is the binary four-gamete case (`r = 2`); the
r-state cluster bound and laminar characterization are new.

Sources: R. Agarwala and D. Fernandez-Baca, "A polynomial-time algorithm for
the perfect phylogeny problem when the number of character states is fixed",
SIAM Journal on Computing 23(6):1216-1224, 1994,
doi:10.1137/S0097539793244587; statement after the Encyclopedia of Algorithms
(2016) entry (the journal article itself was not held when this was written).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Powerset

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.PerfectPhylogenyWanted

open Classical

variable {n m : ℕ} {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Rooted binary trees on taxa. -/
inductive BinTree (α : Type*) where
  | leaf (a : α) : BinTree α
  | node (l r : BinTree α) : BinTree α
  deriving DecidableEq

/-- Leaf set of a tree. -/
def leafSet : BinTree (Fin n) → Finset (Fin n)
  | .leaf a => {a}
  | .node l r => leafSet l ∪ leafSet r

/-- All subtree leaf sets (clusters) of a tree. -/
def clustersOf : BinTree (Fin n) → Finset (Finset (Fin n))
  | .leaf a => {{a}}
  | .node l r => clustersOf l ∪ clustersOf r ∪ {leafSet (.node l r)}

/-- A character block is a cluster: displayed by the tree. -/
def Displays (T : BinTree (Fin n)) (M : Fin n → Fin m → σ) : Prop :=
  ∀ j t, Finset.univ.filter (fun i => M i j = t) ∈ clustersOf T

/-- A perfect phylogeny displays every character block. -/
def HasPerfectPhylogeny (M : Fin n → Fin m → σ) : Prop :=
  ∃ T : BinTree (Fin n), Displays T M

/-- A c-cluster shares one state in one character. -/
def IsCCluster (M : Fin n → Fin m → σ) (C : Finset (Fin n)) : Prop :=
  ∃ j : Fin m, ∃ t : σ, C = Finset.univ.filter fun i => M i j = t

/-- All c-clusters of a matrix. -/
noncomputable def cClusters (M : Fin n → Fin m → σ) :
    Finset (Finset (Fin n)) :=
  Finset.univ.filter (IsCCluster M)

/-- Laminar family: any two members nest or are disjoint. -/
def Laminar (F : Finset (Finset (Fin n))) : Prop :=
  ∀ C₁ ∈ F, ∀ C₂ ∈ F, C₁ ⊆ C₂ ∨ C₂ ⊆ C₁ ∨ Disjoint C₁ C₂

/-- **Fixed-state perfect phylogeny** (Agarwala-Fernandez-Baca 1994):
hypotheses are matrix dimensions (`hn`, `hm`) and the matrix `M` itself.
Conclusions: at most `2^r * m` c-clusters (`hbound`, `r` the state count),
and a perfect phylogeny exists exactly when the c-clusters are laminar
(`hchar`).

Source: Agarwala-Fernandez-Baca (1994), via the Encyclopedia of Algorithms
entry. -/
theorem_wanted perfectPhylogeny_fixed_states (n m : ℕ) (hn : 2 ≤ n)
    (hm : 1 ≤ m) (M : Fin n → Fin m → σ) :
    (cClusters M).card ≤ 2 ^ Fintype.card σ * m ∧
      (HasPerfectPhylogeny M ↔ Laminar (cClusters M))

end WantedExt.Biology.ComputationalBiology.PerfectPhylogenyWanted
