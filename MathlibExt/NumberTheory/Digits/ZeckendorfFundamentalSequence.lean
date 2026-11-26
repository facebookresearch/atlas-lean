/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Fib.Zeckendorf

/-!
# The Zeckendorf fundamental sequence

The shifted Fibonacci numbers are the unique strictly increasing positive weights whose
nonadjacent finite sums represent every natural number exactly once.
-/

namespace MetaMathlibExt

namespace bijective_nonadjacent_finset_sum_iff_eq_fib

private abbrev Support := {s : Finset ℕ // ∀ k ∈ s, k + 1 ∉ s}

private abbrev weightSum (H : ℕ → ℕ) (s : Support) := ∑ k ∈ s.val, H k

-- Mathlib lists Fibonacci indices in descending order, starting at index two.
private def indices (s : Finset ℕ) : List ℕ := (s.sort (· ≥ ·)).map (· + 2)

private abbrev Gap (a b : ℕ) := b + 2 ≤ a

local instance gapTrans : IsTrans ℕ Gap := ⟨fun _ _ _ hab hbc => by unfold Gap at *; omega⟩

private theorem rep_iff {l : List ℕ} :
    l.IsZeckendorfRep ↔ l.Pairwise Gap ∧ ∀ a ∈ l, 2 ≤ a := by
  change List.IsChain Gap (l ++ [0]) ↔ _
  simp [List.isChain_iff_pairwise, List.pairwise_append, Gap]

private theorem indices_rep (s : Support) : (indices s.val).IsZeckendorfRep := by
  apply rep_iff.mpr
  constructor
  · apply List.pairwise_map.mpr
    apply s.val.sortedGT_sort.pairwise.imp_of_mem
    intro a b ha hb hlt
    have hne : b + 1 ≠ a := by
      rintro rfl
      exact s.property b ((Finset.mem_sort _).mp hb) ((Finset.mem_sort _).mp ha)
    change b + 2 + 2 ≤ a + 2
    omega
  · simp [indices]

private theorem exists_indices {l : List ℕ} (hl : l.IsZeckendorfRep) :
    ∃ s : Support, indices s.val = l := by
  induction l with
  | nil => exact ⟨⟨∅, by simp⟩, by simp [indices]⟩
  | cons a l ih =>
    obtain ⟨hp, hmin⟩ := rep_iff.mp hl
    obtain ⟨hgap, htail⟩ := List.pairwise_cons.mp hp
    obtain ⟨s, hs⟩ := ih (rep_iff.mpr ⟨htail, fun b hb => hmin b (by simp [hb])⟩)
    have ha := hmin a (by simp)
    have hbound (k) (hk : k ∈ s.val) : k + 2 ≤ a - 2 := by
      have hmem : k + 2 ∈ l := hs ▸ List.mem_map_of_mem ((Finset.mem_sort _).mpr hk)
      have := hgap _ hmem
      unfold Gap at this
      omega
    refine ⟨⟨insert (a - 2) s.val, ?_⟩, ?_⟩
    · intro k hk hnext
      simp only [Finset.mem_insert] at hk hnext
      have := s.property k
      grind
    · have hsort := Finset.sort_insert (· ≥ ·) (a := a - 2) (s := s.val)
          (fun k hk => by have := hbound k hk; omega) (by intro hk; have := hbound _ hk; omega)
      simpa [indices, hsort, Nat.sub_add_cancel ha] using congrArg (List.cons a) hs

private theorem fib_bijective : Function.Bijective (weightSum (fun k => Nat.fib (k + 2))) := by
  have hsum (s : Support) :
      weightSum (fun k => Nat.fib (k + 2)) s = ((indices s.val).map Nat.fib).sum := by
    simpa [weightSum, indices, List.map_map, Function.comp_def] using
      List.sum_toFinset (fun k => Nat.fib (k + 2)) (s.val.sort_nodup (· ≥ ·))
  constructor
  · intro s t heq
    rw [hsum, hsum] at heq
    have hl := congrArg Nat.zeckendorf heq
    rw [Nat.zeckendorf_sum_fib (indices_rep s), Nat.zeckendorf_sum_fib (indices_rep t)] at hl
    have hsort := (List.map_injective_iff (f := fun k : ℕ => k + 2)).mpr
      (fun _ _ h => Nat.add_right_cancel h) hl
    exact Subtype.ext (by simpa using congrArg List.toFinset hsort)
  · intro n
    obtain ⟨s, hs⟩ := exists_indices (Nat.isZeckendorfRep_zeckendorf n)
    exact ⟨s, by rw [hsum, hs, Nat.sum_zeckendorf_fib]⟩

-- If H n < G n, a G-representation of H n can only use earlier indices.
-- When the earlier weights agree it duplicates the singleton H-representation.
private theorem weight_le {G H : ℕ → ℕ} (hpos : ∀ k, 0 < G k) (hmono : StrictMono G)
    (hsurj : Function.Surjective (weightSum G)) (hinj : Function.Injective (weightSum H))
    {n : ℕ} (ih : ∀ k < n, G k = H k) : G n ≤ H n := by
  by_contra! hlt
  obtain ⟨s, hs⟩ := hsurj (H n)
  have hindex (k) (hk : k ∈ s.val) : k < n := by
    have hle : G k ≤ H n := (Finset.single_le_sum (fun j _ => (hpos j).le) hk).trans_eq hs
    exact hmono.lt_iff_lt.mp (hle.trans_lt hlt)
  let t : Support := ⟨{n}, by simp⟩
  have heq : s = t := hinj (calc
    weightSum H s = weightSum G s := Finset.sum_congr rfl fun k hk => (ih k (hindex k hk)).symm
    _ = H n := hs
    _ = weightSum H t := by simp [weightSum, t])
  exact (lt_irrefl n) (hindex n (by simp [heq, t]))

end bijective_nonadjacent_finset_sum_iff_eq_fib

open bijective_nonadjacent_finset_sum_iff_eq_fib in
/-- **The Fibonacci numbers are the only Zeckendorf fundamental sequence.** Let
$H \colon \mathbb{N} \to \mathbb{N}$ be a strictly increasing sequence of positive integers, and
call a finite set $s \subseteq \mathbb{N}$ nonadjacent if $k \in s$ implies $k + 1 \notin s$.
Then every natural number (including $0$) equals $\sum_{k \in s} H_k$ for exactly one nonadjacent
finite set $s$ if and only if $H_k = F_{k+2}$ for all $k$, where $F_0 = 0$, $F_1 = 1$ and
$F_{n+2} = F_{n+1} + F_n$ are the Fibonacci numbers.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 1 (`integers-2025-A25-lem-1`). -/
public theorem bijective_nonadjacent_finset_sum_iff_eq_fib {H : ℕ → ℕ}
    (hpos : ∀ k, 0 < H k) (hmono : StrictMono H) :
    Function.Bijective (fun s : {s : Finset ℕ // ∀ k ∈ s, k + 1 ∉ s} => ∑ k ∈ s.1, H k) ↔
      ∀ k, H k = Nat.fib (k + 2) := by
  constructor
  · intro h n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      exact le_antisymm (weight_le hpos hmono h.surjective fib_bijective.injective ih)
        (weight_le (fun k => Nat.fib_pos.mpr (by omega)) Nat.fib_add_two_strictMono
          fib_bijective.surjective h.injective (fun k hk => (ih k hk).symm))
  · intro h
    simpa only [h] using fib_bijective

end MetaMathlibExt
