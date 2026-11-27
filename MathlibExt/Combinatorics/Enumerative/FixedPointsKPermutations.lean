/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Stirling
import Mathlib.Combinatorics.Derangements.Basic
import Mathlib.Data.Finset.Powerset

/-!
# Fixed points in permutations with a given number of cycles

Choose the fixed points, then count derangements of their complement.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Permutations counted by cycles and fixed points.** For natural numbers $n$, $k$ and $j$,
$a(n, k, j)$ is the number of permutations of $\{0, 1, \dots, n - 1\}$ with exactly $k$ cycles
(fixed points counted as cycles of length one) and exactly $j$ fixed points.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Proposition 3 (definition of `a(n, k, j)`). -/
public noncomputable def kPermFixedPointCount (n k j : ℕ) : ℕ :=
  Fintype.card {σ : Equiv.Perm (Fin n) //
    cycleQuotientCount σ = k ∧ Fintype.card (Function.fixedPoints σ) = j}

private theorem derangement_iff_card_fixedPoints_eq_zero {m : ℕ}
    (τ : Equiv.Perm (Fin m)) :
    τ ∈ derangements (Fin m) ↔ Fintype.card (Function.fixedPoints τ) = 0 := by
  rw [Fintype.card_eq_zero_iff]
  exact ⟨fun h => ⟨fun x => h x.val x.property⟩, fun h x hx => h.false ⟨x, hx⟩⟩

/-- **Fixed points split off a derangement.** Write $a(n, k, j)$ for the number of permutations of
an $n$-element set with exactly $k$ cycles (fixed points counted as cycles of length one) and
exactly $j$ fixed points, and $d(m, i) = a(m, i, 0)$ for the number of derangements of an
$m$-element set with $i$ cycles. For all natural numbers $n$, $k$ and $j$ with $j \le k$,
$a(n, k, j) = \binom{n}{j} \, d(n - j, k - j)$, where $n - j$ is read as $0$ when $j > n$.

The paper assumes $n \ge k \ge 1$; the identity holds for all $n$ and all $k \ge j$.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Proposition 3 (i) (`integers-2024-A54-prop-3`). -/
public theorem kPermFixedPointCount_eq_choose_mul_derangement {n k j : ℕ} (hjk : j ≤ k) :
    kPermFixedPointCount n k j = n.choose j * kPermFixedPointCount (n - j) (k - j) 0 := by
  classical
  let valid (σ : Equiv.Perm (Fin n)) : Prop :=
    cycleQuotientCount σ = k ∧ Fintype.card (Function.fixedPoints σ) = j
  let S := ↥((Finset.univ : Finset (Fin n)).powersetCard j)
  let D := {τ : Equiv.Perm (Fin (n - j)) //
    cycleQuotientCount τ = k - j ∧ Fintype.card (Function.fixedPoints τ) = 0}
  let fixedSet (σ : Equiv.Perm (Fin n)) := (Function.fixedPoints σ).toFinset
  let chosen (σ : Subtype valid) : S :=
    ⟨fixedSet σ.val, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, (Set.toFinset_card _).trans σ.property.2⟩⟩
  -- Over each choice of fixed points, restrict to the complement and relabel it.
  let fiber (s : S) : D ≃ {σ : Subtype valid // chosen σ = s} := by
    have hs := (Finset.mem_powersetCard.mp s.property).2
    let e : Fin (n - j) ≃ ↥s.valᶜ :=
      (Finset.equivFinOfCardEq (by rw [Finset.card_compl, Fintype.card_fin, hs])).symm
    let d : derangements (Fin (n - j)) ≃ {σ : Equiv.Perm (Fin n) // fixedSet σ = s.val} :=
      e.derangementsCongr.trans ((derangements.subtypeEquiv (· ∈ s.valᶜ)).trans
        (Equiv.subtypeEquivRight fun σ => by
          simp only [fixedSet, Finset.ext_iff, Set.mem_toFinset, Finset.mem_compl, not_not]
          exact forall_congr' fun _ => iff_comm))
    have hcard (σ : Equiv.Perm (Fin n)) (h : fixedSet σ = s.val) :
        Fintype.card (Function.fixedPoints σ) = j :=
      (Set.toFinset_card _).symm.trans ((congrArg Finset.card h).trans hs)
    calc
      D ≃ {τ : Equiv.Perm (Fin (n - j)) //
          τ ∈ derangements (Fin (n - j)) ∧ cycleQuotientCount τ = k - j} :=
        Equiv.subtypeEquivRight fun τ => by
          rw [derangement_iff_card_fixedPoints_eq_zero, and_comm]
      _ ≃ {τ : derangements (Fin (n - j)) // cycleQuotientCount τ.val = k - j} :=
        (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm
      _ ≃ {σ : {σ : Equiv.Perm (Fin n) // fixedSet σ = s.val} //
          cycleQuotientCount σ.val = k} := d.subtypeEquiv fun τ => by
        -- Extension preserves nontrivial cycles and adds exactly the j singleton cycles.
        have htype : (d τ).val.cycleType = τ.val.cycleType :=
          Equiv.Perm.cycleType_extendDomain e
        rw [cycleQuotientCount_eq τ.val, cycleQuotientCount_eq (d τ).val,
          (derangement_iff_card_fixedPoints_eq_zero τ.val).mp τ.property,
          hcard _ (d τ).property, htype]
        omega
      _ ≃ {σ : Equiv.Perm (Fin n) // fixedSet σ = s.val ∧ cycleQuotientCount σ = k} :=
        Equiv.subtypeSubtypeEquivSubtypeInter (fun σ => fixedSet σ = s.val)
          (fun σ => cycleQuotientCount σ = k)
      _ ≃ {σ : Equiv.Perm (Fin n) // valid σ ∧ fixedSet σ = s.val} :=
        Equiv.subtypeEquivRight fun σ =>
          ⟨fun ⟨hfix, hk⟩ => ⟨⟨hk, hcard σ hfix⟩, hfix⟩,
           fun ⟨hvalid, hfix⟩ => ⟨hfix, hvalid.1⟩⟩
      _ ≃ {σ : Subtype valid // fixedSet σ.val = s.val} :=
        (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm
      _ ≃ {σ : Subtype valid // chosen σ = s} :=
        Equiv.subtypeEquivRight fun σ => by
          change (chosen σ).val = s.val ↔ chosen σ = s
          exact Subtype.ext_iff.symm
  let split : Subtype valid ≃ S × D :=
    (Equiv.sigmaFiberEquiv chosen).symm.trans
      (Equiv.sigmaEquivProdOfEquiv fun s => (fiber s).symm)
  -- When n < j the type S is empty; the same equivalence still applies.
  change Fintype.card (Subtype valid) = n.choose j * Fintype.card D
  rw [Fintype.card_congr split, Fintype.card_prod]
  simp [S]

end

end MetaMathlibExt
