/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Sqrt
import Mathlib.GroupTheory.Perm.DomMulAct

/-!
# Union-free families have vanishing density (Erdős Problem 447)

A family $F$ of subsets of $\{0, \dots, n-1\}$ is union-free if no three pairwise distinct
members satisfy $A \cup B = C$. The main result, `maxUnionFreeSizeLittleO_holds`, states that the
largest union-free family has $o(2^n)$ members. Here `[n]` is `Fin n`, and the maximum is an
`sSup` over a bounded set of natural numbers.

The proof counts the hits of a union-free family $F$ along the $n!$ maximal chains
$\emptyset \subset \{\sigma(0)\} \subset \{\sigma(0), \sigma(1)\} \subset \cdots$ inside a window
of levels around $n/2$. If the chain of $\sigma$ meets $F$ at level $l$, swapping a block of
positions below level $k < l$ with the block between $k$ and $l$ gives $q$ chains with the same
level-$l$ set whose level-$k$ sets pairwise have that set as their union, so at most one of them
lies in $F$. This bounds the second moment of the number of hits, and the Cauchy–Schwarz
inequality then bounds the number of members of $F$ in the window by a constant multiple of
$\binom{n}{\lfloor n/2 \rfloor}$. A window of width of order $\sqrt{n}$ suffices: the middle
binomial coefficient is at most $2^n / \sqrt{n}$, and Chebyshev's inequality bounds the number of
sets outside the window.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.UnionFreeFamiliesErdosProblem447Wanted

open Asymptotics

/-- **Union-free family.** A family $F$ of subsets of $\{0, \dots, n-1\}$ is union-free if there
are no pairwise distinct $A, B, C \in F$ with $A \cup B = C$. -/
def IsUnionFree {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, ∀ C ∈ F, A ≠ B → A ≠ C → B ≠ C → A ∪ B ≠ C

/-- **Maximum size of a union-free family.** For a natural number $n$, the largest size $|F|$ of a
union-free family $F$ of subsets of $\{0, \dots, n-1\}$. -/
noncomputable def maxUnionFreeSize (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ F : Finset (Finset (Fin n)), IsUnionFree F ∧ F.card = k}

/-- **Erdős Problem 447, first question.** The assertion that the maximum size of a union-free
family of subsets of $\{0, \dots, n-1\}$ is $o(2^n)$ as $n \to \infty$. -/
def maxUnionFreeSizeLittleO : Prop :=
  (fun n : ℕ => (maxUnionFreeSize n : ℝ)) =o[Filter.atTop] fun n : ℕ => (2 : ℝ) ^ n

open Finset

section Chains

variable {n : ℕ}

/-- The first `k` positions `0, …, k - 1` of `Fin n`. -/
private def seg (n k : ℕ) : Finset (Fin n) := univ.filter fun j => (j : ℕ) < k

private lemma mem_seg {k : ℕ} {j : Fin n} : j ∈ seg n k ↔ (j : ℕ) < k := by
  simp [seg]

private lemma card_seg {k : ℕ} (hk : k ≤ n) : (seg n k).card = k := by
  have : seg n k = (univ : Finset (Fin k)).map (Fin.castLEEmb hk) := by
    ext j
    simp only [mem_seg, mem_map, mem_univ, true_and]
    constructor
    · intro h
      exact ⟨⟨j, h⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      simp
  rw [this, card_map, card_univ, Fintype.card_fin]

/-- The level-`k` set of the maximal chain of a permutation `σ`: the images under `σ` of the
first `k` positions. -/
private def chain (σ : Equiv.Perm (Fin n)) (k : ℕ) : Finset (Fin n) :=
  (seg n k).map σ.toEmbedding

private lemma mem_chain {σ : Equiv.Perm (Fin n)} {k : ℕ} {x : Fin n} :
    x ∈ chain σ k ↔ ((σ.symm x : Fin n) : ℕ) < k := by
  rw [chain, mem_map_equiv, mem_seg]

private lemma card_chain (σ : Equiv.Perm (Fin n)) {k : ℕ} (hk : k ≤ n) :
    (chain σ k).card = k := by
  rw [chain, card_map, card_seg hk]

/-- Each set of size `k` is the level-`k` set of the chains of exactly `k! (n - k)!`
permutations. -/
private lemma card_fiber (A : Finset (Fin n)) {k : ℕ} (hk : k ≤ n) (hA : A.card = k) :
    (univ.filter fun σ : Equiv.Perm (Fin n) => chain σ k = A).card =
      k.factorial * (n - k).factorial := by
  classical
  set f : Fin n → Bool := fun j => decide ((j : ℕ) < k) with hf
  set g : Fin n → Bool := fun x => decide (x ∈ A) with hg
  have key : ∀ σ : Equiv.Perm (Fin n), chain σ k = A ↔ g ∘ σ = f := by
    intro σ
    constructor
    · intro h
      funext j
      simp only [Function.comp, hf, hg, ← h, mem_chain, Equiv.symm_apply_apply]
    · intro h
      ext x
      rw [mem_chain]
      have := congrFun h (σ.symm x)
      simp only [Function.comp, Equiv.apply_symm_apply, hf, hg] at this
      exact (decide_eq_decide.mp this).symm
  have h1 : Fintype.card {j : Fin n // (j : ℕ) < k} = Fintype.card {x : Fin n // x ∈ A} := by
    rw [Fintype.card_subtype, Fintype.card_coe, hA]
    exact card_seg hk
  have h2 : Fintype.card {j : Fin n // ¬ (j : ℕ) < k} = Fintype.card {x : Fin n // x ∉ A} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h1]
  set σ₀ : Equiv.Perm (Fin n) :=
    Equiv.subtypeCongr (Fintype.equivOfCardEq h1) (Fintype.equivOfCardEq h2) with hσ₀
  have hσ₀f : g ∘ σ₀ = f := by
    funext j
    simp only [Function.comp, hf, hg]
    by_cases hj : (j : ℕ) < k
    · have hmem := (Fintype.equivOfCardEq h1 ⟨j, hj⟩).2
      simp [hσ₀, Equiv.subtypeCongr, hj, hmem]
    · have hmem := (Fintype.equivOfCardEq h2 ⟨j, hj⟩).2
      simp [hσ₀, Equiv.subtypeCongr, hj, hmem]
  have hcard : (univ.filter fun σ : Equiv.Perm (Fin n) => chain σ k = A).card
      = (univ.filter fun τ : Equiv.Perm (Fin n) => f ∘ τ = f).card := by
    refine Finset.card_bij' (fun σ _ => σ₀⁻¹ * σ) (fun τ _ => σ₀ * τ) ?_ ?_ ?_ ?_
    · intro σ hσ
      simp only [mem_filter, mem_univ, true_and] at hσ ⊢
      rw [key] at hσ
      calc f ∘ ⇑(σ₀⁻¹ * σ) = (g ∘ σ₀) ∘ ⇑(σ₀⁻¹ * σ) := by rw [hσ₀f]
        _ = g ∘ σ := by funext j; simp
        _ = f := hσ
    · intro τ hτ
      simp only [mem_filter, mem_univ, true_and] at hτ ⊢
      rw [key]
      calc g ∘ ⇑(σ₀ * τ) = (g ∘ σ₀) ∘ τ := by funext j; simp
        _ = f ∘ τ := by rw [hσ₀f]
        _ = f := hτ
    · intro σ _
      simp
    · intro τ _
      simp
  rw [hcard, ← Fintype.card_subtype, DomMulAct.stabilizer_card, Fintype.prod_bool]
  have e1 : Fintype.card {a // f a = true} = k := by
    rw [Fintype.card_subtype]
    simpa [hf, seg] using card_seg (n := n) hk
  have e2 : Fintype.card {a // f a = false} = n - k := by
    rw [Fintype.card_subtype]
    have : (univ.filter fun a : Fin n => f a = false) = (seg n k)ᶜ := by
      ext j
      simp [hf, mem_seg]
    rw [this, card_compl, card_seg hk, Fintype.card_fin]
  rw [e1, e2]

/-- Swap the position blocks `[s, s + t)` and `[k, k + t)`. -/
private def swapFun (s t k j : ℕ) : ℕ :=
  if s ≤ j ∧ j < s + t then j + (k - s) else if k ≤ j ∧ j < k + t then j - (k - s) else j

private lemma swapFun_swapFun {s t k : ℕ} (h : s + t ≤ k) (j : ℕ) :
    swapFun s t k (swapFun s t k j) = j := by
  unfold swapFun
  split_ifs <;> omega

private lemma swapFun_lt {s t k j : ℕ} (hn : k + t ≤ n) (hj : j < n) :
    swapFun s t k j < n := by
  unfold swapFun
  split_ifs <;> omega

private lemma swapFun_lt_iff {s t k j : ℕ} (h : s + t ≤ k) :
    swapFun s t k j < k ↔ j < k + t ∧ ¬ (s ≤ j ∧ j < s + t) := by
  unfold swapFun
  split_ifs <;> omega

private lemma swapFun_lt_add_iff {s t k j : ℕ} (h : s + t ≤ k) :
    swapFun s t k j < k + t ↔ j < k + t := by
  unfold swapFun
  split_ifs <;> omega

/-- The block swap as a function on `Fin n`. -/
private def blockSwapFun (n s t k : ℕ) (hn : k + t ≤ n) (j : Fin n) : Fin n :=
  ⟨swapFun s t k j, swapFun_lt hn j.isLt⟩

private lemma blockSwapFun_involutive {s t k : ℕ} (h : s + t ≤ k) (hn : k + t ≤ n) :
    Function.Involutive (blockSwapFun n s t k hn) :=
  fun j => Fin.ext (swapFun_swapFun h j)

/-- The block swap as a permutation of `Fin n`. -/
private def blockSwap (n s t k : ℕ) (h : s + t ≤ k) (hn : k + t ≤ n) : Equiv.Perm (Fin n) :=
  Function.Involutive.toPerm _ (blockSwapFun_involutive h hn)

private lemma val_blockSwap_symm {s t k : ℕ} (h : s + t ≤ k) (hn : k + t ≤ n) (j : Fin n) :
    (((blockSwap n s t k h hn).symm j : Fin n) : ℕ) = swapFun s t k j := by
  rw [blockSwap, Function.Involutive.toPerm_symm, Function.Involutive.coe_toPerm]
  rfl

private lemma mem_chain_mul_blockSwap {σ : Equiv.Perm (Fin n)} {s t k : ℕ} (h : s + t ≤ k)
    (hn : k + t ≤ n) {x : Fin n} :
    x ∈ chain (σ * blockSwap n s t k h hn) k ↔
      ((σ.symm x : Fin n) : ℕ) < k + t ∧
        ¬ (s ≤ ((σ.symm x : Fin n) : ℕ) ∧ ((σ.symm x : Fin n) : ℕ) < s + t) := by
  rw [mem_chain, Equiv.Perm.mul_def, Equiv.symm_trans_apply, val_blockSwap_symm]
  exact swapFun_lt_iff h

private lemma chain_mul_blockSwap_add {σ : Equiv.Perm (Fin n)} {s t k : ℕ} (h : s + t ≤ k)
    (hn : k + t ≤ n) : chain (σ * blockSwap n s t k h hn) (k + t) = chain σ (k + t) := by
  ext x
  rw [mem_chain, mem_chain, Equiv.Perm.mul_def, Equiv.symm_trans_apply, val_blockSwap_symm]
  exact swapFun_lt_add_iff h

/-- Indicator that the `k`-th chain set of `σ` lies in `F`. -/
private def ind (F : Finset (Finset (Fin n))) (k : ℕ) (σ : Equiv.Perm (Fin n)) : ℕ :=
  if chain σ k ∈ F then 1 else 0

private lemma ind_mul_self (F : Finset (Finset (Fin n))) (k : ℕ) (σ : Equiv.Perm (Fin n)) :
    ind F k σ * ind F k σ = ind F k σ := by
  unfold ind
  split_ifs <;> simp

/-- **Block-swap bound.** Let `F` be union-free and `k < l ≤ n` with `q (l - k) ≤ k`. Then `q`
times the number of permutations whose chain meets `F` at both levels `k` and `l` is at most the
number of permutations whose chain meets `F` at level `l`: the `q` block swaps of the positions
below `k` with those between `k` and `l` fix the level-`l` set and give level-`k` sets that
pairwise have it as their union. -/
private lemma pair_bound {F : Finset (Finset (Fin n))} (hF : IsUnionFree F) {k l q : ℕ}
    (hkl : k < l) (hl : l ≤ n) (hq : q * (l - k) ≤ k) :
    q * ∑ σ : Equiv.Perm (Fin n), ind F k σ * ind F l σ ≤ ∑ σ : Equiv.Perm (Fin n), ind F l σ := by
  classical
  obtain ⟨t, rfl⟩ : ∃ t, l = k + t := ⟨l - k, by omega⟩
  rw [Nat.add_sub_cancel_left] at hq
  have ht1 : 1 ≤ t := by omega
  have hn : k + t ≤ n := hl
  have hblock : ∀ m < q, m * t + t ≤ k := by
    intro m hm
    have : (m + 1) * t ≤ q * t := Nat.mul_le_mul_right _ hm
    rw [Nat.add_mul, one_mul] at this
    omega
  let ρ : ℕ → Equiv.Perm (Fin n) := fun m =>
    if h : m * t + t ≤ k then blockSwap n (m * t) t k h hn else 1
  have hρ : ∀ m < q, ∀ σ : Equiv.Perm (Fin n), ∀ x : Fin n,
      x ∈ chain (σ * ρ m) k ↔ ((σ.symm x : Fin n) : ℕ) < k + t ∧
        ¬ (m * t ≤ ((σ.symm x : Fin n) : ℕ) ∧ ((σ.symm x : Fin n) : ℕ) < m * t + t) := by
    intro m hm σ x
    simp only [ρ, dite_eq_left (hblock m hm)]
    exact mem_chain_mul_blockSwap (hblock m hm) hn
  have hρl : ∀ m < q, ∀ σ : Equiv.Perm (Fin n), chain (σ * ρ m) (k + t) = chain σ (k + t) := by
    intro m hm σ
    simp only [ρ, dite_eq_left (hblock m hm)]
    exact chain_mul_blockSwap_add (hblock m hm) hn
  -- at most one of the swapped chain sets lies in `F`
  have hone : ∀ σ : Equiv.Perm (Fin n), chain σ (k + t) ∈ F →
      ((range q).filter fun m => chain (σ * ρ m) k ∈ F).card ≤ 1 := by
    intro σ hσ
    rw [card_le_one]
    intro m hm m' hm'
    simp only [mem_filter, mem_range] at hm hm'
    by_contra hne
    have hdisj : m * t + t ≤ m' * t ∨ m' * t + t ≤ m * t := by
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · left
        have : (m + 1) * t ≤ m' * t := Nat.mul_le_mul_right _ h
        rw [Nat.add_mul, one_mul] at this
        exact this
      · right
        have : (m' + 1) * t ≤ m * t := Nat.mul_le_mul_right _ h
        rw [Nat.add_mul, one_mul] at this
        exact this
    have hmk := hblock m hm.1
    have hmk' := hblock m' hm'.1
    -- a witness position in the block of `m₁`
    have hwit : ∀ m₁ < q, ∃ x : Fin n, x ∉ chain (σ * ρ m₁) k ∧ x ∈ chain σ (k + t) ∧
        (m₁ * t ≤ ((σ.symm x : Fin n) : ℕ) ∧ ((σ.symm x : Fin n) : ℕ) < m₁ * t + t) := by
      intro m₁ hm₁
      have hm₁k := hblock m₁ hm₁
      refine ⟨σ ⟨m₁ * t, by omega⟩, ?_, ?_, ?_⟩
      · rw [hρ m₁ hm₁]
        simp only [Equiv.symm_apply_apply]
        omega
      · rw [mem_chain]
        simp only [Equiv.symm_apply_apply]
        omega
      · simp only [Equiv.symm_apply_apply]
        omega
    refine hF _ hm.2 _ hm'.2 _ hσ ?_ ?_ ?_ ?_
    · intro heq
      obtain ⟨x, hx1, hx2, hx3⟩ := hwit m hm.1
      apply hx1
      rw [heq, hρ m' hm'.1]
      rw [mem_chain] at hx2
      omega
    · intro heq
      obtain ⟨x, hx1, hx2, -⟩ := hwit m hm.1
      exact hx1 (heq ▸ hx2)
    · intro heq
      obtain ⟨x, hx1, hx2, -⟩ := hwit m' hm'.1
      exact hx1 (heq ▸ hx2)
    · ext x
      rw [mem_union, hρ m hm.1, hρ m' hm'.1, mem_chain]
      omega
  -- double counting
  have hindl : ∀ m < q, ∀ σ : Equiv.Perm (Fin n), ind F (k + t) (σ * ρ m) = ind F (k + t) σ := by
    intro m hm σ
    unfold ind
    rw [hρl m hm σ]
  have hsum : ∀ m < q, ∑ σ : Equiv.Perm (Fin n), ind F k (σ * ρ m) * ind F (k + t) σ
      = ∑ σ : Equiv.Perm (Fin n), ind F k σ * ind F (k + t) σ := by
    intro m hm
    refine Fintype.sum_equiv (Equiv.mulRight (ρ m)) _ _ fun σ => ?_
    simp only [Equiv.coe_mulRight]
    rw [hindl m hm σ]
  calc q * ∑ σ : Equiv.Perm (Fin n), ind F k σ * ind F (k + t) σ
      = ∑ m ∈ range q, ∑ σ : Equiv.Perm (Fin n), ind F k (σ * ρ m) * ind F (k + t) σ := by
        rw [sum_congr rfl fun m hm => hsum m (mem_range.mp hm), sum_const, card_range,
          smul_eq_mul]
    _ = ∑ σ : Equiv.Perm (Fin n), (∑ m ∈ range q, ind F k (σ * ρ m)) * ind F (k + t) σ := by
        rw [sum_comm]
        simp_rw [sum_mul]
    _ ≤ ∑ σ : Equiv.Perm (Fin n), ind F (k + t) σ := by
        refine sum_le_sum fun σ _ => ?_
        by_cases hσ : chain σ (k + t) ∈ F
        · have h1 : ind F (k + t) σ = 1 := ite_eq_left hσ
          rw [h1, mul_one]
          simp only [ind]
          rw [sum_boole, Nat.cast_id]
          exact hone σ hσ
        · have h0 : ind F (k + t) σ = 0 := ite_eq_right hσ
          rw [h0, mul_zero]

/-- The number of permutations whose `k`-th chain set lies in `F` counts the members of `F` of
size `k`, each `k! (n - k)!` times. -/
private lemma sum_ind (F : Finset (Finset (Fin n))) {k : ℕ} (hk : k ≤ n) :
    ∑ σ : Equiv.Perm (Fin n), ind F k σ =
      (F.filter fun A => A.card = k).card * (k.factorial * (n - k).factorial) := by
  classical
  simp only [ind]
  rw [sum_boole, Nat.cast_id]
  rw [card_eq_sum_card_fiberwise (f := fun σ => chain σ k) (t := F.filter fun A => A.card = k)]
  · rw [← smul_eq_mul, ← sum_const]
    refine sum_congr rfl fun A hA => ?_
    rw [mem_filter] at hA
    rw [← card_fiber A hk hA.2, filter_filter]
    congr 1
    refine filter_congr fun σ _ => ?_
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨h ▸ hA.1, h⟩
  · intro σ hσ
    simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hσ ⊢
    exact ⟨hσ, card_chain σ hk⟩

/-- **Window bound.** A union-free family has few members with sizes in a window of levels
`[a, b]`, provided the window is narrow compared with its lowest level. -/
private lemma window_bound {F : Finset (Finset (Fin n))} (hF : IsUnionFree F) {a b q : ℕ}
    (hb : b ≤ n) (hq : q * (b - a) ≤ a) :
    q * (F.filter fun A => a ≤ A.card ∧ A.card ≤ b).card ≤
      n.choose (n / 2) * (q + 2 * (b + 1 - a)) := by
  classical
  set I := Icc a b with hI
  set T : ℕ → ℕ := fun k => ∑ σ : Equiv.Perm (Fin n), ind F k σ with hT
  set S := ∑ k ∈ I, T k with hS
  -- pairwise bounds
  have hpair : ∀ k ∈ I, ∀ l ∈ I, q * ∑ σ : Equiv.Perm (Fin n), ind F k σ * ind F l σ ≤
      (if k = l then q * T k else 0) + (T k + T l) := by
    intro k hk l hl
    rw [hI, mem_Icc] at hk hl
    rcases lt_trichotomy k l with h | rfl | h
    · have := pair_bound hF h (hl.2.trans hb)
        (le_trans (Nat.mul_le_mul_left _ (by omega)) (hq.trans hk.1))
      rw [ite_eq_right h.ne]
      simp only [hT]
      omega
    · rw [ite_eq_left rfl]
      have : ∑ σ : Equiv.Perm (Fin n), ind F k σ * ind F k σ = T k := by
        simp only [hT, ind_mul_self]
      rw [this]
      omega
    · have := pair_bound hF h (hk.2.trans hb)
        (le_trans (Nat.mul_le_mul_left _ (by omega)) (hq.trans hl.1))
      rw [ite_eq_right h.ne']
      have hc : ∑ σ : Equiv.Perm (Fin n), ind F k σ * ind F l σ =
          ∑ σ : Equiv.Perm (Fin n), ind F l σ * ind F k σ :=
        sum_congr rfl fun σ _ => mul_comm _ _
      rw [hc]
      simp only [hT]
      omega
  -- second moment
  have hsq : q * ∑ σ : Equiv.Perm (Fin n), (∑ k ∈ I, ind F k σ) ^ 2 ≤ (q + 2 * I.card) * S := by
    have e : ∑ σ : Equiv.Perm (Fin n), (∑ k ∈ I, ind F k σ) ^ 2 =
        ∑ k ∈ I, ∑ l ∈ I, ∑ σ : Equiv.Perm (Fin n), ind F k σ * ind F l σ := by
      simp_rw [sq, sum_mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun k _ => ?_
      rw [sum_comm]
    rw [e, mul_sum]
    calc ∑ k ∈ I, q * ∑ l ∈ I, ∑ σ : Equiv.Perm (Fin n), ind F k σ * ind F l σ
        = ∑ k ∈ I, ∑ l ∈ I, q * ∑ σ : Equiv.Perm (Fin n), ind F k σ * ind F l σ := by
          simp_rw [mul_sum]
      _ ≤ ∑ k ∈ I, ∑ l ∈ I, ((if k = l then q * T k else 0) + (T k + T l)) :=
          sum_le_sum fun k hk => sum_le_sum fun l hl => hpair k hk l hl
      _ = (q + 2 * I.card) * S := by
          have inner : ∀ k ∈ I, ∑ l ∈ I, ((if k = l then q * T k else 0) + (T k + T l)) =
              q * T k + I.card * T k + S := by
            intro k hk
            rw [sum_add_distrib, sum_add_distrib, sum_ite_eq, ite_eq_left hk, sum_const,
              smul_eq_mul, hS, add_assoc]
          rw [sum_congr rfl inner, sum_add_distrib, sum_add_distrib, sum_const, smul_eq_mul,
            ← mul_sum, ← mul_sum, ← hS]
          ring
  -- Cauchy–Schwarz over all permutations
  have hcs : S ^ 2 ≤ n.factorial * ∑ σ : Equiv.Perm (Fin n), (∑ k ∈ I, ind F k σ) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Equiv.Perm (Fin n))))
      (f := fun σ => ∑ k ∈ I, ind F k σ)
    rw [card_univ, Fintype.card_perm, Fintype.card_fin, sum_comm] at this
    exact this
  -- the second moment controls the first
  have hS_le : q * S ≤ n.factorial * (q + 2 * I.card) := by
    rcases Nat.eq_zero_or_pos S with h0 | hpos
    · rw [h0, mul_zero]
      exact Nat.zero_le _
    · have : q * S * S ≤ n.factorial * (q + 2 * I.card) * S := by
        calc q * S * S = q * S ^ 2 := by ring
          _ ≤ q * (n.factorial * ∑ σ : Equiv.Perm (Fin n), (∑ k ∈ I, ind F k σ) ^ 2) :=
            Nat.mul_le_mul_left _ hcs
          _ = n.factorial * (q * ∑ σ : Equiv.Perm (Fin n), (∑ k ∈ I, ind F k σ) ^ 2) := by ring
          _ ≤ n.factorial * ((q + 2 * I.card) * S) := Nat.mul_le_mul_left _ hsq
          _ = n.factorial * (q + 2 * I.card) * S := by ring
      exact Nat.le_of_mul_le_mul_right this hpos
  -- the first moment counts the members of `F` in the window
  have hlow : n.factorial * (F.filter fun A => a ≤ A.card ∧ A.card ≤ b).card ≤
      n.choose (n / 2) * S := by
    have hW : (F.filter fun A => a ≤ A.card ∧ A.card ≤ b).card =
        ∑ k ∈ I, (F.filter fun A => A.card = k).card := by
      rw [card_eq_sum_card_fiberwise (f := fun A => A.card) (t := I)]
      · refine sum_congr rfl fun k hk => ?_
        rw [filter_filter]
        congr 1
        refine filter_congr fun A _ => ?_
        rw [hI, mem_Icc] at hk
        constructor
        · exact fun h => h.2
        · intro h
          exact ⟨⟨h ▸ hk.1, h ▸ hk.2⟩, h⟩
      · intro A hA
        simp only [coe_filter, Set.mem_ofPred_eq] at hA
        rw [mem_coe, hI, mem_Icc]
        exact hA.2
    rw [hW, mul_sum, hS, mul_sum]
    refine sum_le_sum fun k hk => ?_
    rw [hI, mem_Icc] at hk
    have hkn : k ≤ n := hk.2.trans hb
    simp only [hT]
    rw [sum_ind F hkn, ← Nat.choose_mul_factorial_mul_factorial hkn]
    calc n.choose k * k.factorial * (n - k).factorial * (F.filter fun A => A.card = k).card
        = n.choose k * ((F.filter fun A => A.card = k).card * (k.factorial * (n - k).factorial))
          := by ring
      _ ≤ n.choose (n / 2) * ((F.filter fun A => A.card = k).card *
            (k.factorial * (n - k).factorial)) :=
          Nat.mul_le_mul_right _ (Nat.choose_le_middle k n)
  have hfin : n.factorial * (q * (F.filter fun A => a ≤ A.card ∧ A.card ≤ b).card) ≤
      n.factorial * (n.choose (n / 2) * (q + 2 * (b + 1 - a))) := by
    calc n.factorial * (q * (F.filter fun A => a ≤ A.card ∧ A.card ≤ b).card)
        = q * (n.factorial * (F.filter fun A => a ≤ A.card ∧ A.card ≤ b).card) := by ring
      _ ≤ q * (n.choose (n / 2) * S) := Nat.mul_le_mul_left _ hlow
      _ = n.choose (n / 2) * (q * S) := by ring
      _ ≤ n.choose (n / 2) * (n.factorial * (q + 2 * I.card)) := Nat.mul_le_mul_left _ hS_le
      _ = n.factorial * (n.choose (n / 2) * (q + 2 * (b + 1 - a))) := by
          rw [hI, Nat.card_Icc]
          ring
  exact Nat.le_of_mul_le_mul_left hfin (Nat.factorial_pos n)

end Chains

section Estimates

/-- The variance identity behind Chebyshev's bound for the sizes of subsets. -/
private lemma sum_sq_dev {α : Type*} (s : Finset α) :
    ∑ t ∈ s.powerset, ((s.card : ℤ) - 2 * t.card) ^ 2 = (s.card : ℤ) * 2 ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [sum_powerset_insert ha, card_insert_of_notMem ha]
    have h2 : ∀ t ∈ s.powerset, (((s.card + 1 : ℕ) : ℤ) - 2 * ((insert a t).card : ℕ)) ^ 2 =
        (((s.card : ℤ) - 2 * t.card) ^ 2 - 2 * ((s.card : ℤ) - 2 * t.card) + 1) := by
      intro t ht
      rw [card_insert_of_notMem fun h => ha (mem_powerset.mp ht h)]
      push_cast
      ring
    have h1 : ∀ t ∈ s.powerset, (((s.card + 1 : ℕ) : ℤ) - 2 * (t.card : ℕ)) ^ 2 =
        (((s.card : ℤ) - 2 * t.card) ^ 2 + 2 * ((s.card : ℤ) - 2 * t.card) + 1) := by
      intro t _
      push_cast
      ring
    rw [sum_congr rfl h1, sum_congr rfl h2, ← sum_add_distrib]
    have h3 : ∀ t ∈ s.powerset,
        ((((s.card : ℤ) - 2 * t.card) ^ 2 + 2 * ((s.card : ℤ) - 2 * t.card) + 1) +
          (((s.card : ℤ) - 2 * t.card) ^ 2 - 2 * ((s.card : ℤ) - 2 * t.card) + 1)) =
        2 * ((s.card : ℤ) - 2 * t.card) ^ 2 + 2 := by
      intro t _
      ring
    rw [sum_congr rfl h3, sum_add_distrib, ← mul_sum, ih, sum_const, card_powerset]
    push_cast
    ring

/-- **Chebyshev's bound** for the number of subsets of `Fin n` whose size is far from `n / 2`. -/
private lemma card_far_mul_le (n d : ℕ)
    (S : Finset (Finset (Fin n))) (hS : ∀ A ∈ S, (d : ℤ) ≤ |(n : ℤ) - 2 * A.card|) :
    S.card * d ^ 2 ≤ n * 2 ^ n := by
  have hsum := sum_sq_dev (univ : Finset (Fin n))
  rw [powerset_univ, card_univ, Fintype.card_fin] at hsum
  have key : ((S.card * d ^ 2 : ℕ) : ℤ) ≤ ((n * 2 ^ n : ℕ) : ℤ) := by
    push_cast
    rw [← hsum]
    calc (S.card : ℤ) * (d : ℤ) ^ 2 = ∑ A ∈ S, (d : ℤ) ^ 2 := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ A ∈ S, ((n : ℤ) - 2 * A.card) ^ 2 := by
          refine sum_le_sum fun A hA => ?_
          have h := hS A hA
          rw [← sq_abs ((n : ℤ) - 2 * A.card)]
          exact pow_le_pow_left₀ (by positivity) h 2
      _ ≤ ∑ A : Finset (Fin n), ((n : ℤ) - 2 * A.card) ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (subset_univ S) fun A _ _ => sq_nonneg _
  exact_mod_cast key

/-- The central binomial coefficient satisfies `centralBinom m ^ 2 * (2 m + 1) ≤ 16 ^ m`. -/
private lemma centralBinom_sq_mul_le (m : ℕ) : m.centralBinom ^ 2 * (2 * m + 1) ≤ 16 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := Nat.succ_mul_centralBinom_succ m
    have hpos : 0 < (m + 1) ^ 2 := by positivity
    have key : (m + 1) ^ 2 * ((m + 1).centralBinom ^ 2 * (2 * (m + 1) + 1)) ≤
        (m + 1) ^ 2 * 16 ^ (m + 1) := by
      calc (m + 1) ^ 2 * ((m + 1).centralBinom ^ 2 * (2 * (m + 1) + 1))
          = ((m + 1) * (m + 1).centralBinom) ^ 2 * (2 * m + 3) := by ring
        _ = (2 * (2 * m + 1) * m.centralBinom) ^ 2 * (2 * m + 3) := by rw [h]
        _ = 4 * (2 * m + 1) * (2 * m + 3) * (m.centralBinom ^ 2 * (2 * m + 1)) := by ring
        _ ≤ 4 * (2 * m + 1) * (2 * m + 3) * 16 ^ m := Nat.mul_le_mul_left _ ih
        _ ≤ 16 * (m + 1) ^ 2 * 16 ^ m := by
            apply Nat.mul_le_mul_right
            nlinarith
        _ = (m + 1) ^ 2 * 16 ^ (m + 1) := by ring
    exact Nat.le_of_mul_le_mul_left key hpos

/-- The middle binomial coefficient is at most `2 ^ n / √n`. -/
private lemma choose_half_sq_mul_le (n : ℕ) : n.choose (n / 2) ^ 2 * n ≤ 4 ^ n := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [show 2 * m / 2 = m by omega, ← Nat.centralBinom_eq_two_mul_choose]
    calc m.centralBinom ^ 2 * (2 * m) ≤ m.centralBinom ^ 2 * (2 * m + 1) :=
          Nat.mul_le_mul_left _ (by omega)
      _ ≤ 16 ^ m := centralBinom_sq_mul_le m
      _ = 4 ^ (2 * m) := by rw [pow_mul]; norm_num
  · rw [show (2 * m + 1) / 2 = m by omega]
    have h1 : (m + 1).centralBinom = 2 * (2 * m + 1).choose m := by
      rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (m + 1) = (2 * m + 1) + 1 by ring,
        Nat.choose_succ_succ', Nat.choose_symm_half]
      ring
    have h2 := centralBinom_sq_mul_le (m + 1)
    rw [h1] at h2
    have : 4 * ((2 * m + 1).choose m ^ 2 * (2 * m + 1)) ≤ 4 * 4 ^ (2 * m + 1) := by
      calc 4 * ((2 * m + 1).choose m ^ 2 * (2 * m + 1))
          ≤ (2 * (2 * m + 1).choose m) ^ 2 * (2 * (m + 1) + 1) := by
            rw [mul_pow]
            nlinarith [Nat.zero_le ((2 * m + 1).choose m ^ 2)]
        _ ≤ 16 ^ (m + 1) := h2
        _ = 4 * 4 ^ (2 * m + 1) := by
            rw [show (16 : ℕ) = 4 ^ 2 by norm_num, ← pow_mul]
            ring
    omega

end Estimates

section Final

/-- Arithmetic for the window condition `q * (b - a) ≤ a`. -/
private lemma arith_window_cond {K s a m n : ℕ} (hK : 1 ≤ K) (hs : 8 * K + 8 ≤ s)
    (hs1 : s ^ 2 ≤ n) (hm : n ≤ 2 * m + 1) (ha : a + K * (s + 1) = m) :
    s * (2 * (K * (s + 1)) + 1) ≤ 8 * K * a := by
  have e1 : (8 * K + 8) * (4 * K * s) ≤ s * (4 * K * s) := Nat.mul_le_mul_right _ hs
  have e2 : K * s ^ 2 ≤ K * n := Nat.mul_le_mul_left _ hs1
  have e3 : K * n ≤ K * (2 * m + 1) := Nat.mul_le_mul_left _ hm
  have e4 : K * (a + K * (s + 1)) = K * m := by rw [ha]
  have e5 : K ^ 2 * 1 ≤ K ^ 2 * s := Nat.mul_le_mul_left _ (by omega)
  have e6 : 1 * s ≤ K * s := Nat.mul_le_mul_right _ hK
  have e7 : K * 1 ≤ K * s := Nat.mul_le_mul_left _ (by omega)
  nlinarith [e1, e2, e3, e4, e5, e6, e7]

/-- Arithmetic for the window estimate. -/
private lemma arith_window {K s q : ℕ} (hK : 1 ≤ K) (hs : 128 * K ^ 3 + 128 ≤ s)
    (hq1 : 8 * K * q ≤ s) (hq2 : s + 1 ≤ 8 * K * q + 8 * K) :
    2 * K * (q + 2 * (2 * (K * (s + 1)) + 2)) ≤ q * s := by
  set L := K ^ 3 with hL
  have hKL : K ≤ L := by
    rw [hL]
    calc K = K * 1 * 1 := by ring
      _ ≤ K * K * K := Nat.mul_le_mul (Nat.mul_le_mul_left _ hK) hK
      _ = K ^ 3 := by ring
  have hK2L : K ^ 2 ≤ L := by
    rw [hL]
    calc K ^ 2 = K ^ 2 * 1 := by ring
      _ ≤ K ^ 2 * K := Nat.mul_le_mul_left _ hK
      _ = K ^ 3 := by ring
  have e1 : (128 * L + 128) * s ≤ s * s := Nat.mul_le_mul_right _ hs
  have e2 : K * s ≤ L * s := Nat.mul_le_mul_right _ hKL
  have e3 : L * 128 ≤ L * s := Nat.mul_le_mul_left _ (by omega)
  have e4 : (s + 1) * s ≤ (8 * K * q + 8 * K) * s := Nat.mul_le_mul_right _ hq2
  have e5 : 2 * K * (8 * K * q) ≤ 2 * K * s := Nat.mul_le_mul_left _ hq1
  have key : 8 * K * (2 * K * (q + 2 * (2 * (K * (s + 1)) + 2))) ≤ 8 * K * (q * s) := by
    have h1 : 8 * K * (2 * K * (q + 2 * (2 * (K * (s + 1)) + 2))) =
        2 * K * (8 * K * q) + 64 * (K ^ 3) * (s + 1) + 64 * K ^ 2 := by ring
    have h2 : 8 * K * (q * s) = (8 * K * q) * s := by ring
    rw [h1, h2, ← hL]
    nlinarith [e1, e2, e3, e4, e5, hK2L]
  exact Nat.le_of_mul_le_mul_left key (by omega)

/-- Arithmetic for the tail estimate. -/
private lemma arith_tail {K s n : ℕ} (hK : 1 ≤ K) (hn : n < (s + 1) ^ 2) :
    2 * K * n ≤ (2 * (K * (s + 1)) + 1) ^ 2 := by
  have e1 : K ^ 2 * n ≤ K ^ 2 * (s + 1) ^ 2 := Nat.mul_le_mul_left _ hn.le
  have e2 : K * n ≤ K ^ 2 * n := by
    rw [sq, mul_assoc]
    exact Nat.le_mul_of_pos_left _ (by omega)
  have e3 : (2 * (K * (s + 1)) + 1) ^ 2 = 4 * (K ^ 2 * (s + 1) ^ 2) + 4 * (K * (s + 1)) + 1 := by
    ring
  rw [e3, mul_assoc]
  omega

/-- For large `n`, every union-free family of subsets of `Fin n` has at most `2 ^ n / K`
members. -/
private lemma mul_card_le_of_large {K : ℕ} (hK : 1 ≤ K) {n : ℕ}
    (hn : (128 * K ^ 3 + 128) ^ 2 ≤ n) {F : Finset (Finset (Fin n))} (hF : IsUnionFree F) :
    K * F.card ≤ 2 ^ n := by
  classical
  set s := Nat.sqrt n with hs_def
  have hs : 128 * K ^ 3 + 128 ≤ s := Nat.le_sqrt.mpr (by rw [← sq]; exact hn)
  have hs1 : s ^ 2 ≤ n := Nat.sqrt_le' n
  have hs2 : n < (s + 1) ^ 2 := Nat.lt_succ_sqrt' n
  have hK3 : K ≤ K ^ 3 := by
    calc K = K * 1 * 1 := by ring
      _ ≤ K * K * K := Nat.mul_le_mul (Nat.mul_le_mul_left _ hK) hK
      _ = K ^ 3 := by ring
  have hs8 : 8 * K + 8 ≤ s := by omega
  set w := K * (s + 1) with hw
  set m := n / 2 with hm
  have hm2 : 2 * m ≤ n ∧ n ≤ 2 * m + 1 := by omega
  have hwm : w + 1 ≤ m := by
    have e1 : (8 * K + 8) * s ≤ s * s := Nat.mul_le_mul_right _ hs8
    have e2 : K * s ≤ s * s := le_trans (Nat.mul_le_mul_right _ (by omega)) e1
    nlinarith [e1, e2]
  set a := m - w with ha
  set b := m + w + 1 with hb
  have haw : a + w = m := by omega
  have hbn : b ≤ n := by omega
  set q := s / (8 * K) with hq
  have hq1 : 8 * K * q ≤ s := Nat.mul_div_le s (8 * K)
  have hq2 : s + 1 ≤ 8 * K * q + 8 * K := by
    have := Nat.lt_mul_div_succ s (show 0 < 8 * K by omega)
    rw [← hq, mul_add, mul_one] at this
    omega
  have hqpos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · rw [h0, mul_zero, zero_add] at hq2
      omega
    · exact h0
  -- the window condition
  have hqa : q * (b - a) ≤ a := by
    have hba : b - a = 2 * w + 1 := by omega
    rw [hba]
    have h1 : 8 * K * (q * (2 * w + 1)) ≤ s * (2 * w + 1) := by
      rw [← mul_assoc]
      exact Nat.mul_le_mul_right _ hq1
    have h2 := arith_window_cond hK hs8 hs1 hm2.2 haw
    exact Nat.le_of_mul_le_mul_left (h1.trans h2) (by omega)
  -- members of `F` in the window
  have hW : 2 * K * (F.filter fun A => a ≤ A.card ∧ A.card ≤ b).card ≤ 2 ^ n := by
    have hwin := window_bound hF hbn hqa
    have hba : b + 1 - a = 2 * w + 2 := by omega
    rw [hba] at hwin
    have hC : n.choose (n / 2) * s ≤ 2 ^ n := by
      have h1 : (n.choose (n / 2) * s) ^ 2 ≤ (2 ^ n) ^ 2 := by
        calc (n.choose (n / 2) * s) ^ 2 = n.choose (n / 2) ^ 2 * s ^ 2 := by ring
          _ ≤ n.choose (n / 2) ^ 2 * n := Nat.mul_le_mul_left _ hs1
          _ ≤ 4 ^ n := choose_half_sq_mul_le n
          _ = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h1
    have harith := arith_window hK hs hq1 hq2
    have key : q * (2 * K * (F.filter fun A => a ≤ A.card ∧ A.card ≤ b).card) ≤ q * 2 ^ n := by
      calc q * (2 * K * (F.filter fun A => a ≤ A.card ∧ A.card ≤ b).card)
          = 2 * K * (q * (F.filter fun A => a ≤ A.card ∧ A.card ≤ b).card) := by ring
        _ ≤ 2 * K * (n.choose (n / 2) * (q + 2 * (2 * w + 2))) := Nat.mul_le_mul_left _ hwin
        _ = n.choose (n / 2) * (2 * K * (q + 2 * (2 * w + 2))) := by ring
        _ ≤ n.choose (n / 2) * (q * s) := Nat.mul_le_mul_left _ harith
        _ = q * (n.choose (n / 2) * s) := by ring
        _ ≤ q * 2 ^ n := Nat.mul_le_mul_left _ hC
    exact Nat.le_of_mul_le_mul_left key hqpos
  -- sets far from the middle level
  set T := (univ : Finset (Finset (Fin n))).filter fun A => ¬ (a ≤ A.card ∧ A.card ≤ b) with hT
  have hT : 2 * K * T.card ≤ 2 ^ n := by
    have hfar : ∀ A ∈ T, ((2 * w + 1 : ℕ) : ℤ) ≤ |(n : ℤ) - 2 * A.card| := by
      intro A hA
      rw [hT, mem_filter] at hA
      rcases not_and_or.mp hA.2 with h | h
      · exact le_abs.mpr (Or.inl (by push_cast; omega))
      · exact le_abs.mpr (Or.inr (by push_cast; omega))
    have h1 := card_far_mul_le n (2 * w + 1) T hfar
    have h2 := arith_tail (s := s) hK hs2
    have hnpos : 0 < n := by
      have : 0 < (128 * K ^ 3 + 128) ^ 2 := by positivity
      omega
    have key : n * (2 * K * T.card) ≤ n * 2 ^ n := by
      calc n * (2 * K * T.card) = T.card * (2 * K * n) := by ring
        _ ≤ T.card * (2 * w + 1) ^ 2 := Nat.mul_le_mul_left _ h2
        _ ≤ n * 2 ^ n := h1
    exact Nat.le_of_mul_le_mul_left key hnpos
  -- combine
  have hsplit : F.card ≤ (F.filter fun A => a ≤ A.card ∧ A.card ≤ b).card + T.card := by
    rw [← card_filter_add_card_filter_not (s := F) (fun A => a ≤ A.card ∧ A.card ≤ b)]
    exact Nat.add_le_add_left (card_le_card (filter_subset_filter _ (subset_univ F))) _
  have := Nat.mul_le_mul_left K hsplit
  rw [mul_add] at this
  rw [mul_assoc] at hW hT
  omega

/-- For large `n`, the maximum size of a union-free family is at most `2 ^ n / K`. -/
private lemma mul_maxUnionFreeSize_le {K : ℕ} (hK : 1 ≤ K) {n : ℕ}
    (hn : (128 * K ^ 3 + 128) ^ 2 ≤ n) : K * maxUnionFreeSize n ≤ 2 ^ n := by
  classical
  have hne : {k : ℕ | ∃ F : Finset (Finset (Fin n)), IsUnionFree F ∧ F.card = k}.Nonempty :=
    ⟨0, ∅, fun A hA => absurd hA (Finset.notMem_empty A), card_empty⟩
  have hbdd : BddAbove {k : ℕ | ∃ F : Finset (Finset (Fin n)), IsUnionFree F ∧ F.card = k} := by
    refine ⟨Fintype.card (Finset (Fin n)), ?_⟩
    rintro k ⟨F, -, rfl⟩
    exact card_le_univ F
  obtain ⟨F, hF, hFk⟩ := Nat.sSup_mem hne hbdd
  rw [maxUnionFreeSize, ← hFk]
  exact mul_card_le_of_large hK hn hF

end Final

/--
**Union-free families have vanishing density (Erdős Problem 447).** The maximum size of a
union-free family of subsets of $\{0, \dots, n-1\}$ is $o(2^n)$ as $n \to \infty$.

This follows from Kleitman's bound $(1 + o(1))\binom{n}{\lfloor n/2 \rfloor}$; Erdős reported an
earlier unpublished proof by Sárközy and Szemerédi.

Source: T. F.
Bloom, Erdős Problems, Problem #447, https://www.erdosproblems.com/447 (status PROVED (LEAN));
resolution: D. Kleitman, Collections of subsets containing no two sets and their union, Proceedings
of the LA Meeting AMS (1971), 153-155, |F| < (1 + o(1)) C(n, ⌊n/2⌋) (erdosproblems.com/447).
-/
theorem maxUnionFreeSizeLittleO_holds : maxUnionFreeSizeLittleO := by
  rw [maxUnionFreeSizeLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / c)
  have hKpos : (0 : ℝ) < K := lt_trans (by positivity) hK
  have hK1 : 1 ≤ K := by
    have : 0 < K := by exact_mod_cast hKpos
    omega
  filter_upwards [Filter.eventually_ge_atTop ((128 * K ^ 3 + 128) ^ 2)] with n hn
  have h' : (K : ℝ) * maxUnionFreeSize n ≤ 2 ^ n := by exact_mod_cast mul_maxUnionFreeSize_le hK1 hn
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  have hcK : 1 ≤ c * K := by
    rw [div_lt_iff₀ hc] at hK
    linarith
  calc (maxUnionFreeSize n : ℝ) ≤ c * K * maxUnionFreeSize n :=
        le_mul_of_one_le_left (by positivity) hcK
    _ = c * (K * maxUnionFreeSize n) := by ring
    _ ≤ c * 2 ^ n := by gcongr

end MathlibExt.Combinatorics.UnionFreeFamiliesErdosProblem447Wanted
