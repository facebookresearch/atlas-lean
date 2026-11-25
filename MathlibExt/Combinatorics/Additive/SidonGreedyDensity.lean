/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import MathlibExt.Combinatorics.Additive.Sidon
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# A greedy Sidon set of cube-root density

Scan the positive naturals in order, keeping each number whose insertion preserves the
Sidon property. Rejected numbers are determined by pairs or triples of accepted numbers.
-/

namespace MetaMathlibExt

open Finset

/-- The greedy Sidon set after considering the numbers from `1` through `n`. -/
private noncomputable def greedyPrefix : ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 => by
    classical
    exact if (insert (n + 1) (greedyPrefix n) : Set ℕ).IsSidon then
      insert (n + 1) (greedyPrefix n) else greedyPrefix n

private theorem mem_greedyPrefix_succ {x n : ℕ} :
    x ∈ greedyPrefix (n + 1) ↔ x ∈ greedyPrefix n ∨
      x = n + 1 ∧ (insert (n + 1) (greedyPrefix n) : Set ℕ).IsSidon := by
  classical
  rw [greedyPrefix]
  split <;> simp_all [or_comm]

private theorem greedyPrefix_mono : Monotone greedyPrefix :=
  monotone_nat_of_le_succ fun _ _ hx => mem_greedyPrefix_succ.mpr (Or.inl hx)

private theorem greedyPrefix_subset_Icc (n : ℕ) : (greedyPrefix n : Set ℕ) ⊆ Set.Icc 1 n := by
  intro x hx
  induction n with
  | zero => simp [greedyPrefix] at hx
  | succ n ih =>
    rcases mem_greedyPrefix_succ.mp hx with hx | ⟨rfl, _⟩
    · exact ⟨(ih hx).1, (ih hx).2.trans (Nat.le_succ _)⟩
    · exact ⟨Nat.succ_pos _, le_rfl⟩

private theorem greedyPrefix_isSidon (n : ℕ) : (greedyPrefix n : Set ℕ).IsSidon := by
  classical
  induction n with
  | zero => simp [greedyPrefix, Set.IsSidon]
  | succ n ih =>
    rw [greedyPrefix]
    split
    next h => simpa only [Finset.coe_insert] using h
    next => exact ih

/-- The union of the finite greedy prefixes. -/
private noncomputable def greedySidon : Set ℕ := ⋃ n : ℕ, (greedyPrefix n : Set ℕ)

private theorem greedySidon_isSidon : greedySidon.IsSidon := by
  intro a ha b hb c hc d hd h
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hb
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hc
  obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hd
  let n := max (max i j) (max k l)
  exact greedyPrefix_isSidon n a (greedyPrefix_mono ((le_max_left i j).trans (le_max_left ..)) hi)
    b (greedyPrefix_mono ((le_max_right i j).trans (le_max_left ..)) hj)
    c (greedyPrefix_mono ((le_max_left k l).trans (le_max_right ..)) hk)
    d (greedyPrefix_mono ((le_max_right k l).trans (le_max_right ..)) hl) h

private theorem greedySidon_inter_Icc (n : ℕ) :
    greedySidon ∩ Set.Icc 1 n = (greedyPrefix n : Set ℕ) := by
  ext x
  constructor
  · rintro ⟨hx, _, hxn⟩
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
    induction m with
    | zero => simp [greedyPrefix] at hm
    | succ m ih =>
      rcases mem_greedyPrefix_succ.mp hm with hm | ⟨rfl, _⟩
      · exact ih hm
      · exact greedyPrefix_mono hxn hm
  · intro hx
    exact ⟨Set.mem_iUnion.mpr ⟨n, hx⟩, greedyPrefix_subset_Icc n hx⟩

private theorem greedyPrefix_rejects {x n : ℕ} (hx : x ∈ Set.Icc 1 n)
    (h : x ∉ greedyPrefix n) : ¬ (insert x (greedyPrefix n) : Set ℕ).IsSidon := by
  have hx1 := hx.1
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : x ≠ 0)
  intro hs
  apply h
  apply greedyPrefix_mono hx.2
  apply mem_greedyPrefix_succ.mpr (Or.inr ⟨rfl, ?_⟩)
  have hmn : m ≤ n := (Nat.le_succ m).trans hx.2
  have hsub : insert (m + 1) (greedyPrefix m : Set ℕ) ⊆
      insert (m + 1) (greedyPrefix n : Set ℕ) :=
    Set.insert_subset_insert (greedyPrefix_mono hmn)
  intro a ha b hb c hc d hd heq
  exact hs a (hsub ha) b (hsub hb) c (hsub hc) d (hsub hd) heq

/-- Possible obstructions with the new number appearing twice. -/
private def forbiddenPairs (s : Finset ℕ) : Finset ℕ :=
  (s ×ˢ s).image fun p => (p.1 + p.2) / 2

/-- Possible obstructions with the new number appearing once. -/
private def forbiddenTriples (s : Finset ℕ) : Finset ℕ :=
  (s ×ˢ (s ×ˢ s)).image fun p => p.2.1 + p.2.2 - p.1

private theorem mem_forbidden_of_not_isSidon_insert {s : Finset ℕ} {x : ℕ}
    (hs : (s : Set ℕ).IsSidon) (h : ¬ (insert x s : Set ℕ).IsSidon) :
    x ∈ forbiddenPairs s ∪ forbiddenTriples s := by
  by_contra hx
  simp only [Finset.mem_union, not_or] at hx
  apply h
  -- If the new number appears on both sides, cancellation makes the equality trivial.
  -- Otherwise its one or two occurrences determine it from three or two old summands.
  have left (b c d : ℕ) (hb : b ∈ insert x (s : Set ℕ)) (hc : c ∈ insert x (s : Set ℕ))
      (hd : d ∈ insert x (s : Set ℕ)) (heq : x + b = c + d) :
      (x = c ∧ b = d) ∨ (x = d ∧ b = c) := by
    rcases Set.mem_insert_iff.mp hc with hcx | hc
    · exact Or.inl ⟨hcx.symm, by omega⟩
    rcases Set.mem_insert_iff.mp hd with hdx | hd
    · exact Or.inr ⟨hdx.symm, by omega⟩
    rcases Set.mem_insert_iff.mp hb with hbx | hb
    · apply (hx.1 _).elim
      exact Finset.mem_image.mpr ⟨(c, d), Finset.mem_product.mpr ⟨hc, hd⟩, by dsimp; omega⟩
    · apply (hx.2 _).elim
      exact Finset.mem_image.mpr ⟨(b, c, d), Finset.mem_product.mpr
        ⟨hb, Finset.mem_product.mpr ⟨hc, hd⟩⟩, by dsimp; omega⟩
  intro a ha b hb c hc d hd heq
  rcases Set.mem_insert_iff.mp ha with hax | ha'
  · subst a
    exact left b c d hb hc hd heq
  rcases Set.mem_insert_iff.mp hb with hbx | hb'
  · subst b
    have := left a c d ha hc hd (by simpa only [add_comm a x] using heq)
    tauto
  rcases Set.mem_insert_iff.mp hc with hcx | hc'
  · subst c
    have := left d a b hd ha hb heq.symm
    tauto
  rcases Set.mem_insert_iff.mp hd with hdx | hd'
  · subst d
    have := left c a b hc ha hb (by simpa only [add_comm c x] using heq.symm)
    tauto
  exact hs a ha' b hb' c hc' d hd' heq

private theorem le_greedyPrefix_card_add (n : ℕ) :
    n ≤ (greedyPrefix n).card + (greedyPrefix n).card ^ 2 + (greedyPrefix n).card ^ 3 := by
  let s := greedyPrefix n
  have hcover : Finset.Icc 1 n ⊆ s ∪ (forbiddenPairs s ∪ forbiddenTriples s) := by
    intro x hx
    by_cases hs : x ∈ s
    · exact Finset.mem_union_left _ hs
    · exact Finset.mem_union_right _ <| mem_forbidden_of_not_isSidon_insert
        (greedyPrefix_isSidon n) (greedyPrefix_rejects (by simpa using hx) hs)
  have hp : (forbiddenPairs s).card ≤ s.card ^ 2 := by
    simpa [forbiddenPairs, Finset.card_product, pow_two] using
      (Finset.card_image_le (s := s ×ˢ s) (f := fun p => (p.1 + p.2) / 2))
  have ht : (forbiddenTriples s).card ≤ s.card ^ 3 := by
    simpa [forbiddenTriples, Finset.card_product, pow_succ, mul_assoc] using
      (Finset.card_image_le (s := s ×ˢ (s ×ˢ s)) (f := fun p => p.2.1 + p.2.2 - p.1))
  have h := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  rw [Nat.card_Icc] at h
  have hu := Finset.card_union_le (forbiddenPairs s) (forbiddenTriples s)
  change n ≤ s.card + s.card ^ 2 + s.card ^ 3
  omega

private theorem one_mem_greedyPrefix : 1 ∈ greedyPrefix 1 := by
  apply mem_greedyPrefix_succ.mpr (Or.inr ⟨rfl, ?_⟩)
  simp [greedyPrefix, Set.IsSidon]

/-- **Mian–Chowla lower bound for an infinite Sidon set.** There exist a Sidon set
$A \subseteq \mathbb{N}$ and a real constant $c > 0$ such that
$|A \cap \{1, \dots, n\}| > c\, n^{1/3}$ for every natural number $n \ge 1$.

Source: Andrzej Nowik, *On the Sidon Ideal*, INTEGERS 25 (2025), Article A91,
Theorem 3 (`integers-2025-A91-thm-3`), item 1, quoting A. M. Mian and S. Chowla,
*On the B₂ sequences of Sidon*, Proc. Nat. Acad. Sci. India Sect. A 14 (1944). -/
public theorem exists_isSidon_card_gt_cbrt :
    ∃ A : Set ℕ, A.IsSidon ∧ ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, 1 ≤ n → c * (n : ℝ) ^ ((1 : ℝ) / 3) < (A ∩ Set.Icc 1 n).ncard := by
  refine ⟨greedySidon, greedySidon_isSidon, 1 / 2, by norm_num, fun n hn => ?_⟩
  rw [greedySidon_inter_Icc, Set.ncard_coe_finset]
  let k := (greedyPrefix n).card
  have hk : 1 ≤ k := card_pos.mpr ⟨1, greedyPrefix_mono hn one_mem_greedyPrefix⟩
  have h₁ : k ≤ k ^ 3 := by
    simpa using pow_le_pow_right₀ hk (show 1 ≤ (3 : ℕ) by decide)
  have h₂ : k ^ 2 ≤ k ^ 3 := pow_le_pow_right₀ hk (by decide)
  have hbound : n ≤ 3 * k ^ 3 := by
    have := le_greedyPrefix_card_add n
    change n ≤ k + k ^ 2 + k ^ 3 at this
    omega
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hboundR : (n : ℝ) ≤ 3 * (k : ℝ) ^ 3 := by exact_mod_cast hbound
  have hcube : (n : ℝ) < (2 * (k : ℝ)) ^ 3 := by
    nlinarith only [hboundR, pow_pos hkR 3]
  have hroot : ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = n := by
    rw [← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ n)]
    norm_num
  change (1 / 2 : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 3) < (k : ℝ)
  by_contra! h
  have hle : 2 * (k : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 3) := by linarith
  have := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * (k : ℝ)) hle 3
  rw [hroot] at this
  exact (not_le_of_gt hcube) this

end MetaMathlibExt
