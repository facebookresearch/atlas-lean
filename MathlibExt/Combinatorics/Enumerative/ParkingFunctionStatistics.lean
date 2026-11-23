/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Order
import Mathlib.Order.SuccPred.Archimedean
import Mathlib.Order.SuccPred.Fin
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.Combinatorics.Enumerative.ParkingFunction

/-!
# Ascent and descent sets of parking functions

Cut a word after each position in a prescribed set. A word has descents only at the cuts
exactly when it is weakly increasing within each block. Reversing the blocks in place
gives a word with ascents only at the cuts and preserves the parking condition.
Induction over subsets then gives the equality of the counts for exact sets.
-/

namespace MetaMathlibExt

set_option quotPrecheck false in
/-- The parking functions of length `n`. -/
local notation "pfSet" n:max =>
  Finset.filter (fun f : Fin n → Fin n => IsParkingFunction n f) Finset.univ

set_option quotPrecheck false in
/-- Descent set (1-based positions) of a word `w : Fin m → Fin n`. -/
local notation "desSet" w:max =>
  Finset.image (fun i => i.val + 1)
    (Finset.filter (fun i => ∃ j, j.val = i.val + 1 ∧ w j < w i) Finset.univ)

set_option quotPrecheck false in
/-- Ascent set (1-based positions) of a word `w : Fin m → Fin n`. -/
local notation "ascSet" w:max =>
  Finset.image (fun i => i.val + 1)
    (Finset.filter (fun i => ∃ j, j.val = i.val + 1 ∧ w i < w j) Finset.univ)

namespace parkingFunction_descentSet_card_eq_ascentSet

variable {n : ℕ}

-- Positions belong to the same block when they have passed the same cuts.
private def cuts (I : Finset ℕ) (i : Fin n) : Finset ℕ := I.filter (· ≤ i.val)

private lemma cuts_mono (I : Finset ℕ) : Monotone (cuts (n := n) I) := by
  intro i j hij
  exact Finset.monotone_filter_right _ fun _ _ hk => hk.trans hij

private lemma cuts_eq_iff {I : Finset ℕ} {i j : Fin n} (hij : j.val = i.val + 1) :
    cuts I i = cuts I j ↔ j.val ∉ I := by
  constructor
  · intro h hj
    have hm : j.val ∈ cuts I j := Finset.mem_filter.mpr ⟨hj, le_rfl⟩
    rw [← h] at hm
    have := (Finset.mem_filter.mp hm).2
    omega
  · intro hj
    ext k
    simp only [cuts, Finset.mem_filter]
    constructor
    · rintro ⟨hk, hki⟩
      exact ⟨hk, by omega⟩
    · rintro ⟨hk, hkj⟩
      have : k ≠ j.val := fun h => hj (h ▸ hk)
      exact ⟨hk, by omega⟩

private abbrev Block (I b : Finset ℕ) (n : ℕ) := {i : Fin n // cuts I i = b}

private lemma descents_subset_iff {α : Type*} [LinearOrder α] (f : Fin n → α) (I : Finset ℕ) :
    desSet f ⊆ I ↔ ∀ b, Monotone (fun i : Block I b n => f i) := by
  constructor
  · intro h b
    have connected : Set.OrdConnected {i : Fin n | cuts I i = b} :=
      (Set.ordConnected_singleton (a := b)).preimage_mono (cuts_mono I)
    apply Set.monotoneOn_iff_monotone.mp (monotoneOn_of_le_succ (f := f) connected ?_)
    intro i hi hbi hbj
    cases n with
    | zero => exact i.elim0
    | succ n =>
      obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last (by simpa using! hi)
      rw [Fin.orderSucc_castSucc] at hbj ⊢
      apply le_of_not_gt
      intro hd
      have hcut := h (Finset.mem_image.mpr ⟨k.castSucc,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, k.succ, rfl, hd⟩, rfl⟩)
      exact (cuts_eq_iff (i := k.castSucc) (j := k.succ) rfl).mp (hbi.trans hbj.symm) hcut
  · intro h t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨j, hij, hd⟩ := (Finset.mem_filter.mp hi).2
    by_contra hn
    have he := (cuts_eq_iff (I := I) hij).mpr (hij ▸ hn)
    exact hd.not_ge (@h (cuts I j) ⟨i, he⟩ ⟨j, rfl⟩
      (show i.val ≤ j.val by omega))

-- Reverse the order on each fiber and assemble the resulting permutations of positions.
private noncomputable def reverseBlock (I b : Finset ℕ) :
    Block I b n ≃o (Block I b n)ᵒᵈ :=
  let e := Fintype.orderIsoFinOfCardEq (Block I b n) rfl
  e.symm.trans (Fin.revOrderIso.symm.trans e.dual)

private noncomputable def reverseBlocks (I : Finset ℕ) : Equiv.Perm (Fin n) :=
  Equiv.ofFiberEquiv (f := cuts I) (g := cuts I) fun b => (reverseBlock I b).toEquiv

private lemma reverseBlocks_apply (I b : Finset ℕ) (i : Block I b n) :
    reverseBlocks I i = (reverseBlock I b i : Block I b n).val := by
  obtain ⟨i, rfl⟩ := i
  rfl

private lemma descents_subset_iff_ascents_subset (I : Finset ℕ) (f : Fin n → Fin n) :
    desSet f ⊆ I ↔ ascSet (f ∘ reverseBlocks I) ⊆ I := by
  -- Ascents are descents in the dual order on the preferences.
  let g : Fin n → (Fin n)ᵒᵈ := f ∘ reverseBlocks I
  change desSet f ⊆ I ↔ desSet g ⊆ I
  rw [descents_subset_iff, descents_subset_iff]
  constructor
  · intro h b i j hij
    change f (reverseBlocks I j) ≤ f (reverseBlocks I i)
    rw [reverseBlocks_apply, reverseBlocks_apply]
    exact h b ((reverseBlock I b).monotone hij)
  · intro h b i j hij
    let e := reverseBlock (n := n) I b
    have hh := @h b (e.symm j) (e.symm i) (e.symm.monotone hij)
    change f (reverseBlocks I (e.symm i)) ≤ f (reverseBlocks I (e.symm j)) at hh
    rw [reverseBlocks_apply, reverseBlocks_apply] at hh
    exact (e.apply_symm_apply i) ▸ (e.apply_symm_apply j) ▸ hh

private lemma parking_comp_perm (σ : Equiv.Perm (Fin n)) (f : Fin n → Fin n) :
    IsParkingFunction n f ↔ IsParkingFunction n (f ∘ σ) := by
  have counts (k : Fin n) : (Finset.univ.filter (fun i => k ≤ (f ∘ σ) i)).card =
      (Finset.univ.filter (fun i => k ≤ f i)).card :=
    Finset.card_equiv σ fun i => by simp
  unfold IsParkingFunction IsPartialParkingFunction
  simp only [counts]

private lemma card_subset (I : Finset ℕ) :
    ((pfSet n).filter (fun f => desSet f ⊆ I)).card =
      ((pfSet n).filter (fun f => ascSet f ⊆ I)).card := by
  apply Finset.card_equiv ((reverseBlocks I).symm.arrowCongr (Equiv.refl (Fin n)))
  intro f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_congr (parking_comp_perm _ f) (descents_subset_iff_ascents_subset I f)

end parkingFunction_descentSet_card_eq_ascentSet

open parkingFunction_descentSet_card_eq_ascentSet

open Classical in
/-- **Descent sets and ascent sets of parking functions are equidistributed.** Write a parking
function $f$ of length $n$ as the sequence $(a_1, \dots, a_n)$ with $a_j = f(j-1) + 1$. Its
descent set is the set of $j \in \{1, \dots, n-1\}$ with $a_j > a_{j+1}$, and its ascent set the
set of such $j$ with $a_j < a_{j+1}$. For every $n$ and every $I \subseteq \{1, \dots, n-1\}$, the
number of parking functions of length $n$ with descent set $I$ equals the number of parking
functions of length $n$ with ascent set $I$.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Corollary 15
(`jis-2024-24.8.6-cor-15`). -/
public theorem parkingFunction_descentSet_card_eq_ascentSet (n : ℕ) (I : Finset ℕ)
    (hI : I ⊆ Finset.Ico 1 n) :
    ((pfSet n).filter (fun f => desSet f = I)).card =
      ((pfSet n).filter (fun f => ascSet f = I)).card := by
  induction I using Finset.strongInductionOn with
  | _ I ih =>
    let D (J : Finset ℕ) := ((pfSet n).filter (fun f => desSet f = J)).card
    let A (J : Finset ℕ) := ((pfSet n).filter (fun f => ascSet f = J)).card
    have totals : ∑ J ∈ I.powerset, D J = ∑ J ∈ I.powerset, A J := by
      simpa only [D, A, Finset.sum_card_fiberwise_eq_card_filter, Finset.mem_powerset]
        using card_subset (n := n) I
    have smaller : ∑ J ∈ I.ssubsets, D J = ∑ J ∈ I.ssubsets, A J := by
      apply Finset.sum_congr rfl
      intro J hJ
      have hlt := Finset.mem_ssubsets.mp hJ
      exact ih J hlt (hlt.subset.trans hI)
    have hmem : I ∈ I.powerset := Finset.mem_powerset.mpr (Finset.Subset.refl _)
    rw [← Finset.sum_erase_add _ D hmem, ← Finset.sum_erase_add _ A hmem] at totals
    change D I = A I
    unfold Finset.ssubsets at smaller
    omega

end MetaMathlibExt
