/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Set.Order
import Mathlib.Order.SuccPred.Archimedean
import Mathlib.Order.SuccPred.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.Combinatorics.Enumerative.ParkingFunction

/-!
# Ascents, descents, peaks and ties of parking functions

Cut a word after each position in a prescribed set. A word has descents only at the cuts
exactly when it is weakly increasing within each block. Reversing the blocks in place
gives a word with ascents only at the cuts and preserves the parking condition.
Induction over subsets then gives the equality of the counts for exact sets.
Reversing the whole word instead sends a descent at position `i` to an ascent at `n - i`.
Sorting by preference partitions the parking functions with a given descent set
according to their multiset of entries.
A word of length `n` with `n - 1` ties is constant, and in the only constant parking function
every car prefers the first spot, so for `n ≥ 1` exactly one peakless parking function of
length `n` has `n - 1` ties.
Prepending the smallest preference and shifting the others gives a bijection for
valleyless-tieless parking functions with prescribed endpoints.
-/

namespace MetaMathlibExt

set_option quotPrecheck false in
/-- The parking functions of length `n`. -/
local notation "pfSet" n:max =>
  Finset.filter (fun f : Fin n → Fin n => IsParkingFunction n f) Finset.univ

set_option quotPrecheck false in
/-- The nondecreasing parking functions of length `n`. -/
local notation "ndpfSet" n:max =>
  Finset.filter (fun f : Fin n → Fin n => IsParkingFunction n f ∧ Monotone f) Finset.univ

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

set_option quotPrecheck false in
/-- `w` has no peaks. -/
local notation "NoPeaks" w:max =>
  ∀ i j k, j.val = i.val + 1 → k.val = j.val + 1 → ¬ (w i < w j ∧ w k < w j)

set_option quotPrecheck false in
/-- `w` has no ties. -/
local notation "NoTies" w:max => ∀ i j, j.val = i.val + 1 → w i ≠ w j

set_option quotPrecheck false in
/-- `w` has no valleys. -/
local notation "NoValleys" w:max =>
  ∀ i j k, j.val = i.val + 1 → k.val = j.val + 1 → ¬ (w j < w i ∧ w j < w k)

set_option quotPrecheck false in
/-- The valleyless-tieless parking functions `VTPF_n`. -/
local notation "vtpfSet" n:max =>
  Finset.filter (fun f : Fin n → Fin n => IsParkingFunction n f ∧ (NoTies f) ∧ NoValleys f)
    Finset.univ

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

namespace parkingFunction_descentSet_card_eq_ascentSet_reflect

private lemma ascSet_rev {n : ℕ} (f : Fin n → Fin n) :
    ascSet (f ∘ Fin.rev) = (desSet f).image (fun i => n - i) := by
  ext k
  simp only [Finset.image_image, Function.comp_apply, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, ⟨j, hij, hlt⟩, rfl⟩
    refine ⟨j.rev, ⟨i.rev, ?_, hlt⟩, ?_⟩ <;> simp only [Fin.val_rev] <;> omega
  · rintro ⟨i, ⟨j, hij, hlt⟩, rfl⟩
    refine ⟨j.rev, ⟨i.rev, ?_, by simpa only [Fin.rev_rev] using hlt⟩, ?_⟩ <;>
      simp only [Fin.val_rev] <;> omega

end parkingFunction_descentSet_card_eq_ascentSet_reflect

open Classical in
/-- **Descent sets versus reflected ascent sets of parking functions.** Write a parking function
$f$ of length $n$ as the sequence $(a_1, \dots, a_n)$ with $a_j = f(j-1) + 1$. Its descent set is
the set of $j \in \{1, \dots, n-1\}$ with $a_j > a_{j+1}$, and its ascent set the set of such $j$
with $a_j < a_{j+1}$. For every $n$ and every $I \subseteq \{1, \dots, n-1\}$, let
$J = \{n - i : i \in I\}$. Then the number of parking functions of length $n$ with descent set
$I$ equals the number of parking functions of length $n$ with ascent set $J$.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Proposition 6
(`jis-2024-24.8.6-prop-6`). -/
public theorem parkingFunction_descentSet_card_eq_ascentSet_reflect (n : ℕ)
    (I : Finset ℕ) (hI : I ⊆ Finset.Ico 1 n) :
    ((pfSet n).filter (fun f => desSet f = I)).card =
      ((pfSet n).filter (fun f => ascSet f = I.image (fun i => n - i))).card := by
  apply Finset.card_equiv (Fin.revPerm.arrowCongr (Equiv.refl (Fin n)))
  intro f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine and_congr (parking_comp_perm Fin.revPerm f) ?_
  change desSet f = I ↔ ascSet (f ∘ Fin.rev) = I.image (fun i => n - i)
  rw [parkingFunction_descentSet_card_eq_ascentSet_reflect.ascSet_rev]
  apply (Finset.image_eq_image_iff_of_injOn (s := Finset.Ico 1 n) _ _ hI).symm
  · intro i hi j hj hij
    simp only [Finset.mem_coe, Finset.mem_Ico] at hi hj
    change n - i = n - j at hij
    omega
  · intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨j, hij, _⟩ := (Finset.mem_filter.mp hi).2
    exact Finset.mem_Ico.mpr ⟨by omega, hij ▸ j.isLt⟩

open Classical in
/-- **Reflection symmetry of descent sets of parking functions.** Write a parking function $f$ of
length $n$ as the sequence $(a_1, \dots, a_n)$ with $a_j = f(j-1) + 1$. Its descent set is the set
of $j \in \{1, \dots, n-1\}$ with $a_j > a_{j+1}$. For every $n$ and every
$I \subseteq \{1, \dots, n-1\}$, let $J = \{n - i : i \in I\}$. Then the number of parking
functions of length $n$ with descent set $I$ equals the number with descent set $J$.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Theorem 16
(`jis-2024-24.8.6-thm-16`). -/
public theorem parkingFunction_descentSet_card_reflect (n : ℕ) (I : Finset ℕ)
    (hI : I ⊆ Finset.Ico 1 n) :
    ((pfSet n).filter (fun f => desSet f = I)).card =
      ((pfSet n).filter (fun f => desSet f = I.image (fun i => n - i))).card := by
  refine (parkingFunction_descentSet_card_eq_ascentSet_reflect n I hI).trans
    (parkingFunction_descentSet_card_eq_ascentSet n _ ?_).symm
  intro j hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  obtain ⟨hil, hiu⟩ := Finset.mem_Ico.mp (hI hi)
  exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩

namespace sum_ndpf_multisetDescent_eq

private lemma content_eq_iff_sorted_eq {n : ℕ} (w β : Fin n → Fin n) (hβ : Monotone β) :
    Finset.univ.val.map w = Finset.univ.val.map β ↔ w ∘ Tuple.sort w = β := by
  rw [Fin.univ_val_map, Fin.univ_val_map, Multiset.coe_eq_coe]
  have hperm := (Tuple.sort w).ofFn_comp_perm w
  constructor
  · intro h
    exact List.ofFn_injective ((hperm.trans h).eq_of_pairwise'
      (Tuple.monotone_sort w).sortedLE_ofFn.pairwise hβ.sortedLE_ofFn.pairwise)
  · rintro rfl
    exact hperm.symm

end sum_ndpf_multisetDescent_eq

open Classical sum_ndpf_multisetDescent_eq in
set_option linter.unusedVariables false in
/-- **Counting parking functions with a given descent set by their content.** The descent set
of a word $w = (w_1, \dots, w_n)$ is $\{i : 1 \le i \le n - 1,\ w_i > w_{i+1}\}$. Let
$n \in \mathbb{N}$ and $I \subseteq \{1, \dots, n - 1\}$. Then the number of parking functions of
length $n$ with descent set $I$ equals the sum, over the nondecreasing parking functions $\beta$
of length $n$, of the number of words of length $n$ with descent set $I$ whose multiset of
letters is the multiset of entries of $\beta$.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Lemma 17
(`jis-2024-24.8.6-lem-17`). -/
public theorem sum_ndpf_multisetDescent_eq (n : ℕ) (I : Finset ℕ)
    (hI : I ⊆ Finset.Ico 1 n) :
    ∑ β ∈ ndpfSet n, (Finset.univ.filter (fun w : Fin n → Fin n =>
        Finset.univ.val.map w = Finset.univ.val.map β ∧ desSet w = I)).card =
      ((pfSet n).filter (fun f => desSet f = I)).card := by
  let words := Finset.univ.filter (fun w : Fin n → Fin n => desSet w = I)
  calc
    _ = ∑ β ∈ ndpfSet n, (words.filter (fun w => w ∘ Tuple.sort w = β)).card := by
      apply Finset.sum_congr rfl
      intro β hβ
      congr 1
      ext w
      simp only [words, Finset.mem_filter, Finset.mem_univ, true_and,
        content_eq_iff_sorted_eq w β (Finset.mem_filter.mp hβ).2.2]
      exact and_comm
    _ = _ := by
      rw [Finset.sum_card_fiberwise_eq_card_filter]
      congr 1
      ext w
      simp [words, Tuple.monotone_sort, ← parking_comp_perm, and_comm]

namespace card_peakless_parkingFunction_max_ties

-- Exactly the `n - 1` positions other than the last have a successor.
private lemma card_filter_exists_succ (n : ℕ) :
    (Finset.univ.filter (fun i : Fin n => ∃ j : Fin n, j.val = i.val + 1)).card = n - 1 := by
  rcases n with _ | m
  · rfl
  · have h : Finset.univ.filter (fun i : Fin (m + 1) => ∃ j : Fin (m + 1), j.val = i.val + 1) =
        Finset.univ.erase (Fin.last m) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq,
        and_true, Fin.ext_iff, Fin.val_last]
      constructor
      · rintro ⟨j, hj⟩
        have := j.isLt
        omega
      · intro hi
        exact ⟨⟨i.val + 1, by omega⟩, rfl⟩
    rw [h, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

end card_peakless_parkingFunction_max_ties

open card_peakless_parkingFunction_max_ties in
/-- **Peakless parking functions with $n - 1$ ties.** For every $n \ge 1$, exactly one parking
function $(a_1, \dots, a_n)$ of length $n$ has no peaks (no $i$ with $a_{i-1} < a_i$ and
$a_i > a_{i+1}$) and exactly $n - 1$ ties (indices $i \in \{1, \dots, n - 1\}$ with
$a_i = a_{i+1}$).

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Lemma 42
(`jis-2024-24.8.6-lem-42`). -/
public theorem card_peakless_parkingFunction_max_ties (n : ℕ) (hn : 1 ≤ n) :
    ((pfSet n).filter (fun f => (NoPeaks f) ∧
      (Finset.univ.filter (fun i : Fin n => ∃ j : Fin n, j.val = i.val + 1 ∧ f i = f j)).card =
        n - 1)).card = 1 := by
  -- The unique such parking function is the zero map, the constant word `1 1 ⋯ 1`.
  rw [Finset.card_eq_one]
  refine ⟨fun _ => ⟨0, hn⟩, ?_⟩
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨hpf, -, hties⟩
    -- With `n - 1` ties, every position that has a successor is a tie.
    have hall : ∀ i j : Fin n, j.val = i.val + 1 → f i = f j := by
      have hsub : Finset.univ.filter (fun i : Fin n => ∃ j : Fin n, j.val = i.val + 1 ∧ f i = f j)
          ⊆ Finset.univ.filter (fun i : Fin n => ∃ j : Fin n, j.val = i.val + 1) :=
        Finset.monotone_filter_right _ fun i _ ⟨j, hj, _⟩ => ⟨j, hj⟩
      have heq := Finset.eq_of_subset_of_card_le hsub
        (by rw [hties, card_filter_exists_succ])
      intro i j hij
      have hi : i ∈ Finset.univ.filter (fun i : Fin n => ∃ j : Fin n, j.val = i.val + 1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hij⟩
      rw [← heq] at hi
      obtain ⟨j', hj', hfj'⟩ := (Finset.mem_filter.mp hi).2
      rwa [show j = j' from Fin.ext (hij.trans hj'.symm)]
    -- Hence `f` is constant.
    have hconst : ∀ i : Fin n, f i = f ⟨0, hn⟩ := by
      rintro ⟨i, hi⟩
      induction i with
      | zero => rfl
      | succ i ih => exact (hall ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl).symm.trans (ih (by omega))
    -- Some car prefers the first spot, so the constant value is `0`.
    have h0 : f ⟨0, hn⟩ = ⟨0, hn⟩ := by
      obtain ⟨i, hi⟩ := Finset.card_pos.mp
        ((isParkingFunction_iff_card_filter_le n f).mp hpf ⟨0, hn⟩)
      rw [← hconst i]
      exact Fin.ext (Nat.le_zero.mp (Finset.mem_filter.mp hi).2)
    funext i
    rw [hconst i, h0]
  · rintro rfl
    refine ⟨?_, fun i j k _ _ h => lt_irrefl _ h.1, ?_⟩
    · rw [isParkingFunction_iff_card_filter_le]
      intro k
      simp only [Fin.le_iff_val_le_val, Nat.zero_le, Finset.filter_true, Finset.card_univ,
        Fintype.card_fin]
      exact k.isLt
    · simpa using card_filter_exists_succ n

namespace valleyless_tieless_prepend_one_bijOn

variable {n : ℕ}

private abbrev prepend (f : Fin n → Fin n) : Fin (n + 1) → Fin (n + 1) :=
  Fin.cons 0 fun i => (f i).succ

-- Above threshold zero, exactly the old cars meet the shifted threshold.
private lemma parking_prepend_iff (f : Fin n → Fin n) :
    IsParkingFunction (n + 1) (prepend f) ↔ IsParkingFunction n f := by
  unfold IsParkingFunction IsPartialParkingFunction
  rw [Fin.forall_fin_succ]
  simp [prepend, Fin.card_filter_univ_succ]

private lemma mem_prepend_iff (f : Fin n → Fin n) :
    prepend f ∈ vtpfSet (n + 1) ↔ f ∈ vtpfSet n := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, parking_prepend_iff]
  simp [prepend, Fin.forall_fin_succ, eq_comm (a := (0 : Fin (n + 1)))]

-- A zero in the interior has two strictly larger neighbors, since neither can tie it.
private lemma tail_ne_zero {g : Fin (n + 1) → Fin (n + 1)}
    (ht : NoTies g) (hv : NoValleys g) (hlast : g (Fin.last n) ≠ 0) (i : Fin n) :
    g i.succ ≠ 0 := by
  by_cases h : i.succ = Fin.last n
  · rwa [h]
  obtain ⟨j, hj⟩ := Fin.eq_castSucc_of_ne_last h
  have hadj : j.succ.val = i.succ.val + 1 := by rw [← hj]; rfl
  have hleft := ht i.castSucc i.succ rfl
  have hright := ht i.succ j.succ hadj
  intro hzero
  rw [hzero] at hleft hright
  apply hv i.castSucc i.succ j.succ rfl hadj
  rw [hzero]
  exact ⟨Fin.pos_iff_ne_zero.mpr hleft, Fin.pos_iff_ne_zero.mpr hright.symm⟩

end valleyless_tieless_prepend_one_bijOn

open Classical valleyless_tieless_prepend_one_bijOn in
/-- **Prepending $1$ to valleyless-tieless parking functions.** Identify a parking function $f$
of length $m$ with the word $(f(0) + 1, \dots, f(m-1) + 1)$. A word $(a_1, \dots, a_m)$ has a
tie if $a_k = a_{k+1}$ for some $k$, and a valley if $a_{k-1} > a_k < a_{k+1}$ for some $k$;
write $\mathrm{VTPF}_m$ for the set of parking functions of length $m$ with no ties and no
valleys. For $n \ge 1$, the map $(a_1, \dots, a_n) \mapsto (1, a_1 + 1, \dots, a_n + 1)$ is a
bijection from $\mathrm{VTPF}_n$ onto the set of $(b_1, \dots, b_{n+1}) \in \mathrm{VTPF}_{n+1}$
with $b_1 = 1$ and $b_{n+1} > 1$.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Lemma 34
(`jis-2024-24.8.6-lem-34`). -/
public theorem valleyless_tieless_prepend_one_bijOn (n : ℕ) (hn : 1 ≤ n) :
    Set.BijOn (fun f : Fin n → Fin n => (Fin.cons (0 : Fin (n + 1)) (fun i => (f i).succ) :
        Fin (n + 1) → Fin (n + 1)))
      (vtpfSet n : Set (Fin n → Fin n))
      {g | g ∈ vtpfSet (n + 1) ∧ g 0 = 0 ∧ g (Fin.last n) ≠ 0} := by
  change Set.BijOn prepend _ _
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    refine ⟨(mem_prepend_iff f).2 hf, Fin.cons_zero .., ?_⟩
    obtain ⟨i, hi⟩ := Fin.exists_succ_eq_of_ne_zero
      (show Fin.last n ≠ 0 by simpa [Fin.ext_iff] using Nat.ne_of_gt hn)
    rw [← hi]
    exact Fin.succ_ne_zero (f i)
  · intro f _ f' _ h
    funext i
    exact Fin.succ_injective n (by simpa [prepend] using congrFun h i.succ)
  · rintro g ⟨hg, hfirst, hlast⟩
    obtain ⟨_, ht, hv⟩ := (Finset.mem_filter.mp hg).2
    let f (i : Fin n) := (g i.succ).pred (tail_ne_zero ht hv hlast i)
    have hf : prepend f = g := by
      funext i
      cases i using Fin.cases with
      | zero => exact hfirst.symm
      | succ j => exact Fin.succ_pred _ (tail_ne_zero ht hv hlast j)
    exact ⟨f, (mem_prepend_iff f).mp (hf ▸ hg), hf⟩

end MetaMathlibExt
