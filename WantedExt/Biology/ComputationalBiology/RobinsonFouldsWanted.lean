/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Linear-time tree comparison via cluster tables (Robinson-Foulds)

After renumbering the leaves of the first tree in postorder, every cluster is
an interval of leaf numbers, stored in a table with one row per leaf; a
cluster of the second tree is then tested for membership in constant time.
Two traversals and a table scan yield the shared clusters, hence the
Robinson-Foulds distance on the same `n` leaves, in `O(n)` time. Unrooted
trees reduce to rooted ones by rooting at an arbitrary common leaf. The `O(n)`
running-time reading needs a RAM cost model and is context here.

Overlap (partial): `CSLibExt/Bioinformatics/Phylogenetics/Splits.lean` proves
`rfDist_self/comm/triangle/eq_zero_iff/le` and lists linear-time
Robinson-Foulds as not covered; the interval characterization and table-count
correctness are new.

Sources: W. H. E. Day, "Optimal algorithms for comparing trees with labeled
leaves", Journal of Classification 2(1):7-28, 1985,
doi:10.1007/BF01908061; restated in S. Briand, C. Dessimoz, N. El-Mabrouk and
Y. Nevers, "A linear time solution to the labeled Robinson-Foulds distance
problem", Systematic Biology 71(6):1391-1403, 2022,
doi:10.1093/sysbio/syac028.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.RobinsonFouldsWanted

open Classical

variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Rooted tree: parent links, root, and leaf labels into `Fin n`. -/
structure RootedTree (V : Type*) (n : ℕ) [Fintype V] [DecidableEq V] where
  parent : V → Option V
  root : V
  label : V → Option (Fin n)

/-- Reachability up parent links. -/
inductive Reaches {V : Type*} (parent : V → Option V) : V → V → Prop where
  | refl (v) : Reaches parent v v
  | step (u v w) : Reaches parent u v → parent v = some w → Reaches parent u w

/-- Descendant leaf-labels of `v`: its cluster. -/
noncomputable def clusterOf (T : RootedTree V n) (v : V) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ w, T.label w = some i ∧ Reaches T.parent w v

/-- All clusters of a tree. -/
noncomputable def familyOf (T : RootedTree V n) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun K => ∃ v, K = clusterOf T v

/-- Renumbered clusters through a leaf permutation. -/
noncomputable def normalize (C : Finset (Finset (Fin n)))
    (σ : Fin n → Fin n) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun K => ∃ K₀ ∈ C, K = K₀.image fun i => σ i

/-- Interval sets: closed intervals of leaf numbers. -/
def IsIntervalSet (I : Finset (Fin n)) : Prop :=
  ∃ a b, I = Finset.Icc a b

/-- Table membership test (constant-time lookup abstraction). -/
noncomputable def lookup (T : Finset (Finset (Fin n)))
    (K : Finset (Fin n)) : Bool :=
  decide (K ∈ T)

/-- Shared-cluster count: scan of `C₂` against the table of `C₁`. -/
noncomputable def sharedCount (T₁ C₂ : Finset (Finset (Fin n))) : ℕ :=
  Finset.card (C₂.filter fun K => lookup T₁ K)

/-- **Day's linear-time comparison**: hypotheses are two rooted trees on the
same `n` leaves (`hleaves`: labels biject onto leaves, i.e. every leaf
number occurs and labels are injective on labeled vertices), well-founded
parent links (`hwf`: every vertex reaches the root in fewer than `card`
steps), and a postorder numbering `σ` (`hpost`: every normalized cluster is
an interval). Conclusion: the table scan counts exactly the shared clusters.

Source: Day (1985), via Briand et al. (2022). -/
theorem_wanted day_linear (T₁ T₂ : RootedTree V n)
    (hleaves : (∀ i : Fin n, ∃ w, T₁.label w = some i) ∧
      (∀ i : Fin n, ∃ w, T₂.label w = some i) ∧
      ∀ w₁ w₂ i, T₁.label w₁ = some i → T₁.label w₂ = some i → w₁ = w₂)
    (hwf : (∀ v : V, Reaches T₁.parent v T₁.root) ∧
      ∀ v : V, Reaches T₂.parent v T₂.root)
    (σ : Fin n → Fin n)
    (hpost : ∀ K ∈ normalize (familyOf T₁) σ, IsIntervalSet K) :
    sharedCount (normalize (familyOf T₁) σ) (normalize (familyOf T₂) σ) =
      ((normalize (familyOf T₁) σ) ∩ (normalize (familyOf T₂) σ)).card

end WantedExt.Biology.ComputationalBiology.RobinsonFouldsWanted
