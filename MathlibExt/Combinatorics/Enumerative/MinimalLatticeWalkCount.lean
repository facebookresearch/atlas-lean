/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi

@[expose] public section

open scoped BigOperators

namespace MetaMathlibExt

/-! # Minimal lattice-walk counts are binomial coefficients
-/

/-- Auxiliary counting lemma: sequences `f : Fin n → Fin 3` whose `u`-coordinate
sums to the full length `n` (forcing every entry to avoid the value `o`) and
whose `w`-coordinate sums to `k` (counting the entries equal to `2`) are in
bijection with `k`-element subsets of `Fin n`, hence number `choose n k`. -/
private theorem lattice_walk_count_aux (n k : ℕ) (c o : Fin 3) (u w : Fin 3 → ℕ)
    (hc2 : c ≠ 2)
    (huo : ∀ v : Fin 3, u v + (if v = o then 1 else 0) = 1)
    (hw1 : ∀ v : Fin 3, v ≠ o → w v = (if v = 2 then 1 else 0))
    (huI : ∀ (S : Finset (Fin n)) (i : Fin n), u (if i ∈ S then 2 else c) = 1)
    (hwI : ∀ (S : Finset (Fin n)) (i : Fin n),
      w (if i ∈ S then 2 else c) = (if i ∈ S then 1 else 0))
    (hcov : ∀ v : Fin 3, v ≠ o → v ≠ 2 → v = c) :
    Finset.card (Finset.univ.filter (fun f : Fin n → Fin 3 =>
      (∑ i, u (f i)) = n ∧ (∑ i, w (f i)) = k)) =
    Nat.choose n k := by
  have hbij : (Finset.powersetCard k (Finset.univ : Finset (Fin n))).card =
      (Finset.univ.filter (fun f : Fin n → Fin 3 =>
        (∑ i, u (f i)) = n ∧ (∑ i, w (f i)) = k)).card := by
    refine Finset.card_bij
      (fun (S : Finset (Fin n)) (_ : S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n))) =>
        fun i => if i ∈ S then (2 : Fin 3) else c) ?_ ?_ ?_
    · intro S hS
      rw [Finset.mem_powersetCard] at hS
      obtain ⟨-, hScard⟩ := hS
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      change (∑ i, u (if i ∈ S then 2 else c)) = n ∧
        (∑ i, w (if i ∈ S then 2 else c)) = k
      constructor
      · calc (∑ i, u (if i ∈ S then 2 else c))
              = (∑ i ∈ (Finset.univ : Finset (Fin n)), 1) :=
            Finset.sum_congr rfl (fun i _ => huI S i)
          _ = n := by
            rw [← Finset.card_eq_sum_ones, Finset.card_univ, Fintype.card_fin]
      · calc (∑ i, w (if i ∈ S then 2 else c))
              = (∑ i ∈ (Finset.univ : Finset (Fin n)),
                (if i ∈ S then (1 : ℕ) else 0)) :=
            Finset.sum_congr rfl (fun i _ => hwI S i)
          _ = S.card := by
            have hSS : ((Finset.univ : Finset (Fin n)).filter fun x => x ∈ S) = S := by
              ext x
              simp
            rw [← Finset.card_filter, hSS]
          _ = k := hScard
    · intro S₁ _ S₂ _ heq
      have hi : ∀ i : Fin n, (if i ∈ S₁ then (2 : Fin 3) else c) =
          (if i ∈ S₂ then 2 else c) := fun i => congrFun heq i
      ext i
      have hii := hi i
      by_cases h1 : i ∈ S₁ <;> by_cases h2 : i ∈ S₂
      · exact iff_of_true h1 h2
      · exfalso
        rw [ite_eq_left h1, ite_eq_right h2] at hii
        exact hc2 hii.symm
      · exfalso
        rw [ite_eq_right h1, ite_eq_left h2] at hii
        exact hc2 hii
      · exact iff_of_false h1 h2
    · intro g hg
      rw [Finset.mem_filter] at hg
      obtain ⟨-, hu, hw⟩ := hg
      have go : ∀ i, g i ≠ o := by
        have hsum : (∑ i, u (g i)) + (∑ i ∈ (Finset.univ : Finset (Fin n)),
            (if g i = o then (1 : ℕ) else 0)) = n := by
          have e : ∀ i ∈ (Finset.univ : Finset (Fin n)),
              u (g i) + (if g i = o then (1 : ℕ) else 0) = 1 :=
            fun i _ => huo (g i)
          have hdist : (∑ i ∈ (Finset.univ : Finset (Fin n)),
              (u (g i) + (if g i = o then (1 : ℕ) else 0)))
            = (∑ i ∈ (Finset.univ : Finset (Fin n)), u (g i)) +
              (∑ i ∈ (Finset.univ : Finset (Fin n)),
                (if g i = o then (1 : ℕ) else 0)) :=
            Finset.sum_add_distrib
          rw [← hdist, Finset.sum_congr rfl e, ← Finset.card_eq_sum_ones,
            Finset.card_univ, Fintype.card_fin]
        have hzero : (∑ i ∈ (Finset.univ : Finset (Fin n)),
            (if g i = o then (1 : ℕ) else 0)) = 0 := by omega
        intro i
        have hii := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
          Nat.zero_le (if g j = o then (1 : ℕ) else 0))).mp hzero i
          (Finset.mem_univ i)
        intro hcon
        rw [ite_eq_left hcon] at hii
        exact one_ne_zero hii
      refine ⟨(Finset.univ : Finset (Fin n)).filter (fun i => g i = 2), ?_, ?_⟩
      · rw [Finset.mem_powersetCard]
        refine ⟨Finset.subset_univ _, ?_⟩
        rw [Finset.card_filter]
        have e : ∀ i ∈ (Finset.univ : Finset (Fin n)),
            (if g i = 2 then (1 : ℕ) else 0) = w (g i) := by
          intro i _
          have h1 := hw1 (g i) (go i)
          by_cases h2 : g i = 2
          · rw [ite_eq_left h2, h1, ite_eq_left h2]
          · rw [ite_eq_right h2, h1, ite_eq_right h2]
        calc (∑ i ∈ (Finset.univ : Finset (Fin n)),
                (if g i = 2 then (1 : ℕ) else 0))
              = (∑ i ∈ (Finset.univ : Finset (Fin n)), w (g i)) :=
            Finset.sum_congr rfl e
          _ = k := hw
      · show (fun i => if i ∈ (Finset.univ : Finset (Fin n)).filter (fun j => g j = 2) then
          (2 : Fin 3) else c) = g
        funext i
        show (if i ∈ (Finset.univ : Finset (Fin n)).filter (fun j => g j = 2) then
          (2 : Fin 3) else c) = g i
        by_cases h2 : g i = 2
        · have hiS : i ∈ (Finset.univ : Finset (Fin n)).filter (fun j => g j = 2) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ i, h2⟩
          rw [ite_eq_left hiS, h2]
        · have hiS : i ∉ (Finset.univ : Finset (Fin n)).filter (fun j => g j = 2) :=
            fun h => h2 (Finset.mem_filter.mp h).2
          rw [ite_eq_right hiS]
          exact (hcov (g i) (go i) h2).symm
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at hbij
  exact hbij.symm

/--
**Minimal lattice walks with unit and diagonal steps.** For all natural numbers $a$ and $b$,
the number of sequences of $\max(a, b)$ steps, each taken from $\{(1,0), (0,1), (1,1)\}$,
whose sum is $(a, b)$ equals $\binom{\max(a, b)}{\min(a, b)}$.

Every walk from the origin to $(a, b)$ with these steps has at least $\max(a, b)$ steps, since
each step raises each coordinate by at most $1$, and walks of exactly that length exist; so the
sequences counted are the minimal-length walks from the origin to $(a, b)$.

Proves `Wanted` entry `minimal_lattice_walk_count`.

Source: Jackson Evoniuk, Steven Klee, and Van Magnan, "Enumerating Minimal
Length Lattice Paths," Journal of Integer Sequences 21 (2018),
Article 18.3.6, Theorem (section Minimal walks for S = {(1,0),(0,1),(1,1)},
label sec2), lines 273–275,
https://cs.uwaterloo.ca/journals/JIS/VOL21/Klee/klee2.tex
-/
theorem minimal_lattice_walk_count (a b : ℕ) :
    Finset.card (Finset.univ.filter (fun f : Fin (max a b) → Fin 3 =>
      (∑ i, (![1, 0, 1] : Fin 3 → ℕ) (f i)) = a ∧
      (∑ i, (![0, 1, 1] : Fin 3 → ℕ) (f i)) = b)) =
    Nat.choose (max a b) (min a b) := by
  rcases le_total a b with h | h
  · have hmax : max a b = b := by omega
    have hmin : min a b = a := by omega
    rw [hmax, hmin]
    have hswap : (Finset.univ.filter (fun f : Fin b → Fin 3 =>
        (∑ i, (![1, 0, 1] : Fin 3 → ℕ) (f i)) = a ∧
        (∑ i, (![0, 1, 1] : Fin 3 → ℕ) (f i)) = b))
      = (Finset.univ.filter (fun f : Fin b → Fin 3 =>
        (∑ i, (![0, 1, 1] : Fin 3 → ℕ) (f i)) = b ∧
        (∑ i, (![1, 0, 1] : Fin 3 → ℕ) (f i)) = a)) := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact and_comm
    rw [hswap]
    refine lattice_walk_count_aux b a 1 0 (![0, 1, 1]) (![1, 0, 1])
      (by decide) (by decide) (by decide) ?_ ?_ (by decide)
    · intro S i
      by_cases hi : i ∈ S
      · rw [ite_eq_left hi]
        decide
      · rw [ite_eq_right hi]
        decide
    · intro S i
      by_cases hi : i ∈ S
      · rw [ite_eq_left hi, ite_eq_left hi]
        decide
      · rw [ite_eq_right hi, ite_eq_right hi]
        decide
  · have hmax : max a b = a := by omega
    have hmin : min a b = b := by omega
    rw [hmax, hmin]
    refine lattice_walk_count_aux a b 0 1 (![1, 0, 1]) (![0, 1, 1])
      (by decide) (by decide) (by decide) ?_ ?_ (by decide)
    · intro S i
      by_cases hi : i ∈ S
      · rw [ite_eq_left hi]
        decide
      · rw [ite_eq_right hi]
        decide
    · intro S i
      by_cases hi : i ∈ S
      · rw [ite_eq_left hi, ite_eq_left hi]
        decide
      · rw [ite_eq_right hi, ite_eq_right hi]
        decide

end MetaMathlibExt
