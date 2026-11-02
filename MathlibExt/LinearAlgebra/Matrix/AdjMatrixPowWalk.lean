/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

@[expose] public section

namespace MetaMathlibExt

open scoped BigOperators

private theorem cons_prod_aux {k : ℕ} {R : Type*} [CommSemiring R]
    (A : Matrix (Fin k) (Fin k) R) (n : ℕ) (a : Fin k) (q : Fin (n + 1) → Fin k) :
    ∏ t : Fin (n + 1), A ((Fin.cons (α := fun _ => Fin k) a q) t.castSucc) ((Fin.cons (α := fun _ => Fin k) a q) t.succ)
      = A a (q 0) * ∏ t : Fin n, A (q t.castSucc) (q t.succ) := by
  rw [Fin.prod_univ_succ]
  have h0 : (Fin.cons (α := fun _ => Fin k) a q) (Fin.castSucc (0 : Fin (n+1)))
      = a := by
    rw [Fin.castSucc_zero]
    exact Fin.cons_zero (α := fun _ => Fin k) a q
  have h1 : (Fin.cons (α := fun _ => Fin k) a q) (Fin.succ (0 : Fin (n+1)))
      = q 0 := by
    exact Fin.cons_succ (α := fun _ => Fin k) a q 0
  have h2 : ∀ i : Fin n,
      (Fin.cons (α := fun _ => Fin k) a q) ((i.succ).castSucc)
      = q (i.castSucc) := by
    intro i
    rw [Fin.castSucc_succ]
    exact Fin.cons_succ (α := fun _ => Fin k) a q (i.castSucc)
  have h3 : ∀ i : Fin n,
      (Fin.cons (α := fun _ => Fin k) a q) ((i.succ).succ)
      = q (i.succ) := by
    intro i
    exact Fin.cons_succ (α := fun _ => Fin k) a q (i.succ)
  rw [h0, h1]
  have hprod : (∏ i : Fin n, A ((Fin.cons (α := fun _ => Fin k) a q) (i.succ.castSucc))
      ((Fin.cons (α := fun _ => Fin k) a q) (i.succ.succ)))
      = (∏ t : Fin n, A (q t.castSucc) (q t.succ)) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [h2 i, h3 i]
  rw [hprod]

private theorem cons_last_aux {k : ℕ} (n : ℕ) (a : Fin k) (q : Fin (n + 1) → Fin k) :
    (Fin.cons (α := fun _ => Fin k) a q) (Fin.last (n + 1)) = q (Fin.last n) := by
  have h : Fin.last (n + 1) = (Fin.last n).succ := by
    simp [Fin.succ_last]
  rw [h]
  exact Fin.cons_succ (α := fun _ => Fin k) a q (Fin.last n)

/--
**Powers of a weighted adjacency matrix sum the weights of walks.** Let $R$ be a commutative
semiring, let $k$ and $n$ be natural numbers, and let $A$ be a $k \times k$ matrix over $R$ with
rows and columns indexed by $\{0, \dots, k-1\}$, viewed as the weighted adjacency matrix of a
weighted digraph on these $k$ vertices. Then for all vertices $i$ and $j$,

$$(A^n)_{ij} = \sum_{p} \prod_{t=0}^{n-1} A_{p_t p_{t+1}},$$

where the sum runs over all sequences $p = (p_0, \dots, p_n)$ of vertices with $p_0 = i$ and
$p_n = j$, that is, over all walks of length $n$ from $i$ to $j$, each weighted by the product
of the entries of $A$ along its edges.

The source states $n \ge 1$; the case $n = 0$ is included, where both sides equal $1$ if
$i = j$ and $0$ otherwise.

Proves `Wanted` entry `adjMatrix_pow_weighted_walk_sum`.

Source: Thomas Koshy, "A Graph-Theoretic Model for a Generalized Fibonacci
Gem," Journal of Integer Sequences 22 (2019), Article 19.4.1, Theorem (label
theorem01), lines 128–130,
https://cs.uwaterloo.ca/journals/JIS/VOL22/Koshy/koshy7.tex
-/
theorem adjMatrix_pow_weighted_walk_sum
    {k : ℕ} {R : Type*} [CommSemiring R]
    (A : Matrix (Fin k) (Fin k) R) (n : ℕ) (i j : Fin k) :
    (A ^ n) i j =
      ∑ p ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => (Finset.univ : Finset (Fin k)))).filter
        (fun p => p 0 = i ∧ p (Fin.last n) = j),
        ∏ t : Fin n, A (p t.castSucc) (p t.succ) := by
  induction n generalizing i j with
  | zero =>
    simp only [pow_zero]
    rw [Matrix.one_apply]
    by_cases h : i = j
    · subst h
      have hS : ((Fintype.piFinset (fun _ : Fin (0 + 1) => (Finset.univ : Finset (Fin k)))).filter
          (fun p => p 0 = i ∧ p (Fin.last 0) = i)) = {(fun _ => i)} := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_singleton, Fintype.mem_piFinset,
          Finset.mem_univ, forall_const, true_and]
        constructor
        · rintro ⟨h0, _hlast⟩
          funext x
          have hx : x = 0 := by fin_cases x; rfl
          simp [hx, h0]
        · intro hp
          subst hp
          simp
      rw [hS, Finset.sum_singleton]
      simp
    · have hS : ((Fintype.piFinset (fun _ : Fin (0 + 1) => (Finset.univ : Finset (Fin k)))).filter
          (fun p => p 0 = i ∧ p (Fin.last 0) = j)) = ∅ := by
        ext p
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro _ h0 hlast
        rw [Fin.last_zero] at hlast
        rw [h0] at hlast
        exact h hlast
      rw [hS, Finset.sum_empty]
      simp [h]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    have hLHS : (∑ x : Fin k, A i x * (A ^ n) x j)
        = ∑ x : Fin k, ∑ q ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => (Finset.univ : Finset (Fin k)))).filter
          (fun p => p 0 = x ∧ p (Fin.last n) = j),
          A i x * ∏ t : Fin n, A (q t.castSucc) (q t.succ) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [ih x j, Finset.mul_sum]
    rw [hLHS]
    have hBij : (∑ q ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => (Finset.univ : Finset (Fin k)))).filter
        (fun q => q (Fin.last n) = j), A i (q 0) * ∏ t : Fin n, A (q t.castSucc) (q t.succ))
        = ∑ p ∈ (Fintype.piFinset (fun _ : Fin (n + 1 + 1) => (Finset.univ : Finset (Fin k)))).filter
          (fun p => p 0 = i ∧ p (Fin.last (n + 1)) = j),
          ∏ t : Fin (n + 1), A (p t.castSucc) (p t.succ) := by
      apply Finset.sum_bij (fun q _ => Fin.cons (α := fun _ => Fin k) i q)
      · intro q hq
        simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_univ,
          forall_const, true_and] at hq ⊢
        constructor
        · exact Fin.cons_zero (α := fun _ => Fin k) i q
        · rw [cons_last_aux n i q, hq]
      · intro q1 hq1 q2 hq2 hEq
        have hTail : Fin.tail (Fin.cons (α := fun _ => Fin k) i q1)
            = Fin.tail (Fin.cons (α := fun _ => Fin k) i q2) := by rw [hEq]
        rw [Fin.tail_cons, Fin.tail_cons] at hTail
        exact hTail
      · intro p hp
        simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_univ,
          forall_const, true_and] at hp
        obtain ⟨hp0, hplast⟩ := hp
        refine ⟨Fin.tail p, ?_, ?_⟩
        · simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_univ,
            forall_const, true_and]
          have hEq : (Fin.tail (p : Fin (n + 1 + 1) → Fin k)) (Fin.last n)
              = p (Fin.last (n + 1)) := by
            have hLast : Fin.last (n + 1) = (Fin.last n).succ := by
              simp [Fin.succ_last]
            show p ((Fin.last n).succ) = p (Fin.last (n + 1))
            rw [hLast]
          rw [hEq, hplast]
        · have hCons : Fin.cons (α := fun _ => Fin k) (p 0) (Fin.tail p) = p :=
            Fin.cons_self_tail (α := fun _ => Fin k) p
          rw [hp0] at hCons
          exact hCons
      · intro q hq
        simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_univ,
          forall_const, true_and] at hq
        rw [cons_prod_aux]
    have hFiber : (∑ q ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => (Finset.univ : Finset (Fin k)))).filter
        (fun q => q (Fin.last n) = j), A i (q 0) * ∏ t : Fin n, A (q t.castSucc) (q t.succ))
        = ∑ x : Fin k, ∑ q ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => (Finset.univ : Finset (Fin k)))).filter
          (fun p => p 0 = x ∧ p (Fin.last n) = j),
          A i x * ∏ t : Fin n, A (q t.castSucc) (q t.succ) := by
      have hFib := Finset.sum_fiberwise
        (s := (Fintype.piFinset (fun _ : Fin (n + 1) => (Finset.univ : Finset (Fin k)))).filter
          (fun q => q (Fin.last n) = j))
        (g := fun q : Fin (n + 1) → Fin k => q 0)
        (f := fun q : Fin (n + 1) → Fin k => A i (q 0) * ∏ t : Fin n, A (q t.castSucc) (q t.succ))
      rw [← hFib]
      apply Finset.sum_congr rfl
      intro x _
      have hEq : ((Fintype.piFinset (fun _ : Fin (n + 1) => (Finset.univ : Finset (Fin k)))).filter
          (fun q => q (Fin.last n) = j)).filter (fun q => q 0 = x)
          = (Fintype.piFinset (fun _ : Fin (n + 1) => (Finset.univ : Finset (Fin k)))).filter
            (fun p => p 0 = x ∧ p (Fin.last n) = j) := by
        ext q
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨hmem, hlast⟩, h0⟩
          exact ⟨hmem, h0, hlast⟩
        · rintro ⟨hmem, h0, hlast⟩
          exact ⟨⟨hmem, hlast⟩, h0⟩
      have hInner : (∑ q ∈ ((Fintype.piFinset (fun _ : Fin (n + 1) => (Finset.univ : Finset (Fin k)))).filter
          (fun q => q (Fin.last n) = j)) with (q 0 = x), A i (q 0) * ∏ t : Fin n, A (q t.castSucc) (q t.succ))
          = ∑ q ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => (Finset.univ : Finset (Fin k)))).filter
            (fun p => p 0 = x ∧ p (Fin.last n) = j),
            A i x * ∏ t : Fin n, A (q t.castSucc) (q t.succ) := by
        rw [← hEq]
        apply Finset.sum_congr rfl
        intro q hq
        simp only [Finset.mem_filter] at hq
        obtain ⟨_, hqx⟩ := hq
        rw [hqx]
      exact hInner
    exact hFiber.symm.trans hBij

end MetaMathlibExt
