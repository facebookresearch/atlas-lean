/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Combinatorics.Perm.ShuffleDescents
public import MathlibExt.Data.Sym.Containing

/-!
# Exact ordered-cut counts for Eulerian permutations

Each original adjacent descent forces its original successor position to
appear among the ordered cut boundaries. Removing one copy of each actual
required boundary is the symmetric-power bijection. Native stars
and bars proves the resulting binomial count, without a supplied Eulerian
coefficient or label-count certificate.
-/

@[expose] public section
noncomputable section

namespace Equiv.Perm

/-- The actual successor positions of the original adjacent descents. -/
def descentBoundaries {n : ℕ} (σ : Perm (Fin n)) : Finset (Fin (n + 1)) :=
  (descentPositions σ).map ⟨Fin.succ, Fin.succ_injective n⟩

/-- Every original descent contributes exactly one actual cut boundary. -/
theorem card_descentBoundaries {n : ℕ} (σ : Perm (Fin n)) :
    (descentBoundaries σ).card = descentNumber σ := by
  rw [descentBoundaries, Finset.card_map]
  rfl

/-- Original cut boundaries contain no more positions than the original word length. -/
theorem descentBoundaries_card_le {n : ℕ} (σ : Perm (Fin n)) :
    (descentBoundaries σ).card ≤ n := by
  rw [card_descentBoundaries]
  exact (Finset.card_le_univ (descentPositions σ)).trans_eq (Fintype.card_fin n)

/-- The actual weak ordered cut multiset containing every original descent boundary. -/
abbrev CompatibleEulerianCuts {n : ℕ} (σ : Perm (Fin n)) (m : ℕ) :=
  {c : Sym (Fin (n + 1)) m // (descentBoundaries σ).val ≤ c.val}

/-- The compatible-cut count is the original descent-binomial coefficient. -/
theorem card_compatibleEulerianCuts {n : ℕ} (σ : Perm (Fin n)) (m : ℕ) :
    Fintype.card (CompatibleEulerianCuts σ m) = (n + m - descentNumber σ).choose n := by
  classical
  have h := Sym.card_containing_fixed_fin n m (descentBoundaries σ).val
    (by change (descentBoundaries σ).card ≤ n; exact descentBoundaries_card_le σ)
  change Fintype.card (CompatibleEulerianCuts σ m) = (n + m - (descentBoundaries σ).card).choose n at h
  rw [card_descentBoundaries] at h
  exact h

end Equiv.Perm
