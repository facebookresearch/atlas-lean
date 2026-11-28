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
# Descent-compatible cut multisets

For a permutation `σ ∈ S_n`, every descent at position `j` determines the cut boundary `j+1`
in `Fin(n+1)`. A compatible multiset of `m` cuts contains every one of these boundaries at
least once.

Writing `d = descentNumber σ`, its cardinality is `Nat.choose (n+m-d) n`. Repeated cuts and
the endpoint cut positions are allowed.

Reference: Stanley, *Enumerative Combinatorics*, Volume 1, Chapter 1.
-/

@[expose] public section
noncomputable section

namespace Equiv.Perm

/-- Let `n : ℕ`, `σ ∈ S_n = Equiv.Perm (Fin n)`, and `Des(σ) = {j | j+1<n and σ(j)>σ(j+1)}`. Put
`d = |Des(σ)|`. `descentBoundaries σ` is the subset `{j+1 | j ∈ Des(σ)}` of `Fin(n+1)`,
obtained by the injective successor map. -/
def descentBoundaries {n : ℕ} (σ : Perm (Fin n)) : Finset (Fin (n + 1)) :=
  (descentPositions σ).map ⟨Fin.succ, Fin.succ_injective n⟩

/-- Let `n : ℕ`, `σ ∈ S_n = Equiv.Perm (Fin n)`, and `Des(σ) = {j | j+1<n and σ(j)>σ(j+1)}`. Put
`d = |Des(σ)|`. The successor-boundary set has cardinality `(descentBoundaries σ).card =
descentNumber σ = d`. -/
theorem card_descentBoundaries {n : ℕ} (σ : Perm (Fin n)) :
    (descentBoundaries σ).card = descentNumber σ := by
  rw [descentBoundaries, Finset.card_map]
  rfl

/-- Let `n : ℕ`, `σ ∈ S_n = Equiv.Perm (Fin n)`, and `Des(σ) = {j | j+1<n and σ(j)>σ(j+1)}`. Put
`d = |Des(σ)|`. `(descentBoundaries σ).card ≤ n`, including the empty word `n=0`. -/
theorem descentBoundaries_card_le {n : ℕ} (σ : Perm (Fin n)) :
    (descentBoundaries σ).card ≤ n := by
  rw [card_descentBoundaries]
  exact (Finset.card_le_univ (descentPositions σ)).trans_eq (Fintype.card_fin n)

/-- Let `n : ℕ`, `σ ∈ S_n = Equiv.Perm (Fin n)`, and `Des(σ) = {j | j+1<n and σ(j)>σ(j+1)}`. Put
`d = |Des(σ)|`. For `m : ℕ`, `CompatibleEulerianCuts σ m` consists of multisets `c : Sym
(Fin(n+1)) m` containing one copy of every element of `descentBoundaries σ`. These are weakly
ordered cut positions, with repetitions permitted. -/
abbrev CompatibleEulerianCuts {n : ℕ} (σ : Perm (Fin n)) (m : ℕ) :=
  {c : Sym (Fin (n + 1)) m // (descentBoundaries σ).val ≤ c.val}

/-- Let `n : ℕ`, `σ ∈ S_n = Equiv.Perm (Fin n)`, and `Des(σ) = {j | j+1<n and σ(j)>σ(j+1)}`. Put
`d = |Des(σ)|`. For every `m : ℕ`, `Fintype.card (CompatibleEulerianCuts σ m) = Nat.choose
(n+m-d) n`. -/
theorem card_compatibleEulerianCuts {n : ℕ} (σ : Perm (Fin n)) (m : ℕ) :
    Fintype.card (CompatibleEulerianCuts σ m) = (n + m - descentNumber σ).choose n := by
  classical
  have h := Sym.card_containing_fixed_fin n m (descentBoundaries σ).val
    (by change (descentBoundaries σ).card ≤ n; exact descentBoundaries_card_le σ)
  change Fintype.card (CompatibleEulerianCuts σ m) =
    (n + m - (descentBoundaries σ).card).choose n at h
  rw [card_descentBoundaries] at h
  exact h

end Equiv.Perm
