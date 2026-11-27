/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import MathlibExt.Combinatorics.SimpleGraph.GridDominationTransfer

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Domination polynomials of tori

The domination polynomial of a torus is the trace of the corresponding power of its row
transfer matrix.
-/

open Polynomial SimpleGraph

namespace MetaMathlibExt

namespace dominationPolynomial_torus_eq_trace_transferMatrix_pow

open DominationState

/-- Expand a matrix entry as a sum over the intermediate indices of a walk. -/
private theorem pow_succ_apply_eq_sum {α K : Type*} [Fintype α] [DecidableEq α] [CommSemiring K]
    (A : Matrix α α K) (k : ℕ) (a b : α) :
    (A ^ (k + 1)) b a =
      ∑ f : Fin k → α, ∏ i : Fin (k + 1),
        A (Fin.snoc (α := fun _ => α) f b i) (Fin.cons (α := fun _ => α) a f i) := by
  induction k generalizing a with
  | zero => simp [Finset.univ_unique, Fin.snoc_zero]
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply, ← (Fin.consEquiv (fun _ : Fin (k + 1) => α)).sum_comp,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [ih, Finset.sum_mul]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Fin.consEquiv_apply, ← Fin.cons_snoc_eq_snoc_cons, Fin.prod_univ_succ (n := k + 1)]
    simp only [Fin.cons_zero, Fin.cons_succ, mul_comm (A c a)]

/-- The trace sums over all sequences of indices with a transition back to the first index. -/
private theorem trace_pow_succ_eq_sum {α K : Type*} [Fintype α] [DecidableEq α] [CommSemiring K]
    (A : Matrix α α K) (n : ℕ) :
    Matrix.trace (A ^ (n + 1)) =
      ∑ f : Fin (n + 1) → α, ∏ j : Fin (n + 1), A (f (finRotate _ j)) (f j) := by
  rw [Matrix.trace, ← (Fin.consEquiv (fun _ : Fin (n + 1) => α)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.diag_apply, pow_succ_apply_eq_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp only [Fin.consEquiv_apply, Fin.snoc_eq_cons_rotate]

variable {V : Type*} {n : ℕ} {R : SimpleGraph V}

/-- The two directions around the cycle give its adjacency, with loops removed. -/
private theorem cycle_adj_iff {j k : Fin (n + 1)} :
    (cycleGraph (n + 1)).Adj j k ↔
      j ≠ k ∧ (k = finRotate _ j ∨ j = finRotate _ k) := by
  rw [cycleGraph_eq_circulantGraph, circulantGraph_adj]
  simp only [Set.mem_singleton_iff, sub_eq_iff_eq_add, finRotate_apply, or_comm,
    add_comm (1 : Fin (n + 1))]

/-- Coverage by an occupied vertex in the same row or at the preceding row index. -/
private def coveredFromPrevious (R : SimpleGraph V) (S : Finset (V × Fin n))
    (i : V) (j : Fin n) : Prop :=
  (i, (finRotate n).symm j) ∈ S ∨ ∃ x, R.Adj i x ∧ (x, j) ∈ S

open scoped Classical in
/-- The row state records coverage from the current and preceding row. -/
private noncomputable def rowSignature (R : SimpleGraph V) (S : Finset (V × Fin n))
    (j : Fin n) : DominationSignature R :=
  ⟨fun i => if (i, j) ∈ S then occupied else
      if coveredFromPrevious R S i j then covered else uncovered, by
    rintro i x hix ⟨hi, hx⟩
    have hx' : (x, j) ∈ S := by
      by_contra h
      simp [h, apply_ite (· = occupied)] at hx
    have hc : coveredFromPrevious R S i j := Or.inr ⟨x, hix, hx'⟩
    simp [hc, apply_ite (· = uncovered)] at hi⟩

private theorem row_occupied_iff (S : Finset (V × Fin n)) (i : V) (j : Fin n) :
    (rowSignature R S j).1 i = occupied ↔ (i, j) ∈ S := by
  simp [rowSignature, apply_ite (· = occupied)]

private theorem row_covered_iff (S : Finset (V × Fin n)) (i : V) (j : Fin n) :
    (rowSignature R S j).1 i = covered ↔ (i, j) ∉ S ∧ coveredFromPrevious R S i j := by
  simp [rowSignature, apply_ite (· = covered)]

private theorem row_uncovered_iff (S : Finset (V × Fin n)) (i : V) (j : Fin n) :
    (rowSignature R S j).1 i = uncovered ↔ (i, j) ∉ S ∧ ¬ coveredFromPrevious R S i j := by
  simp [rowSignature, apply_ite (· = uncovered)]

/-- A vertex is dominated by itself, by an occupied vertex in its own row, or by an occupied
vertex in one of the two cyclically adjacent rows. -/
private theorem dominates_iff (S : Finset (V × Fin (n + 1))) :
    (R □ cycleGraph (n + 1)).IsDominating (S : Set _) ↔
      ∀ i j, (i, j) ∈ S ∨ coveredFromPrevious R S i j ∨ (i, finRotate _ j) ∈ S := by
  constructor
  · intro h i j
    rcases h (i, j) with hmem | ⟨⟨x, k⟩, hmem, hadj⟩
    · exact Or.inl hmem
    change (x, k) ∈ S at hmem
    rcases boxProd_adj.mp hadj with ⟨hrow, rfl : k = j⟩ | ⟨hcol, rfl : x = i⟩
    · exact Or.inr (Or.inl (Or.inr ⟨x, hrow.symm, hmem⟩))
    rcases (cycle_adj_iff.mp hcol).2 with hj | rfl
    · rw [← (finRotate _).symm_apply_apply k, ← hj] at hmem
      exact Or.inr (Or.inl (Or.inl hmem))
    · exact Or.inr (Or.inr hmem)
  · rintro h ⟨i, j⟩
    rcases h i j with hmem | (hprev | ⟨x, hx, hmem⟩) | hnext
    · exact Or.inl hmem
    · by_cases hprev_eq : (finRotate (n + 1)).symm j = j
      · exact Or.inl (hprev_eq ▸ hprev)
      exact Or.inr ⟨_, hprev, boxProd_adj_right.mpr
        (cycle_adj_iff.mpr ⟨hprev_eq, Or.inl ((finRotate _).apply_symm_apply j).symm⟩)⟩
    · exact Or.inr ⟨_, hmem, boxProd_adj_left.mpr hx.symm⟩
    · by_cases hnext_eq : finRotate (n + 1) j = j
      · exact Or.inl (hnext_eq ▸ hnext)
      exact Or.inr ⟨_, hnext, boxProd_adj_right.mpr
        (cycle_adj_iff.mpr ⟨hnext_eq, Or.inr rfl⟩)⟩

/-- The canonical signatures are compatible around the cycle exactly for dominating sets. -/
private theorem compatible_rowSignature_iff (S : Finset (V × Fin (n + 1))) :
    (∀ j, DominationCompatible R (rowSignature R S (finRotate _ j)).1
      (rowSignature R S j).1) ↔ (R □ cycleGraph (n + 1)).IsDominating (S : Set _) := by
  rw [dominates_iff]
  constructor
  · intro h i j
    by_cases hmem : (i, j) ∈ S
    · exact Or.inl hmem
    by_cases hcov : coveredFromPrevious R S i j
    · exact Or.inr (Or.inl hcov)
    have hu := (row_uncovered_iff (R := R) S i j).mpr ⟨hmem, hcov⟩
    exact Or.inr (Or.inr ((row_occupied_iff S i _).mp ((h j i).1 hu)))
  · intro h j i
    simp only [ne_eq, row_occupied_iff, row_covered_iff, row_uncovered_iff,
      coveredFromPrevious, Equiv.symm_apply_apply]
    refine ⟨?_, ?_, fun hc => hc.2⟩
    · rintro ⟨hmem, hcov⟩
      exact ((h i j).resolve_left hmem).resolve_left hcov
    · intro hmem hu
      exact hu.2 (Or.inl hmem)

variable [Fintype V]

/-- Recover the vertex set by taking the occupied entries of all the signatures. -/
private noncomputable def occupiedVertices (σ : Fin n → DominationSignature R) :
    Finset (V × Fin n) :=
  Finset.univ.filter fun v => (σ v.2).1 v.1 = occupied

private theorem occupiedVertices_rowSignature (S : Finset (V × Fin n)) :
    occupiedVertices (rowSignature R S) = S := by
  ext ⟨i, j⟩
  simp [occupiedVertices, row_occupied_iff]

/-- For cyclically compatible signatures, the occupied entries determine every row state. -/
private theorem rowSignature_occupiedVertices (σ : Fin n → DominationSignature R)
    (h : ∀ j, DominationCompatible R (σ (finRotate _ j)).1 (σ j).1) :
    rowSignature R (occupiedVertices σ) = σ := by
  funext j
  apply Subtype.ext
  funext i
  have hprev := h ((finRotate n).symm j) i
  rw [Equiv.apply_symm_apply] at hprev
  have hcov : coveredFromPrevious R (occupiedVertices σ) i j ↔
      (σ ((finRotate n).symm j)).1 i = occupied ∨ ∃ x, R.Adj i x ∧ (σ j).1 x = occupied := by
    simp [coveredFromPrevious, occupiedVertices]
  cases hs : (σ j).1 i with
  | occupied => exact (row_occupied_iff ..).mpr (by simp [occupiedVertices, hs])
  | covered =>
    exact (row_covered_iff ..).mpr ⟨by simp [occupiedVertices, hs], hcov.mpr (hprev.2.2 hs)⟩
  | uncovered =>
    refine (row_uncovered_iff ..).mpr ⟨by simp [occupiedVertices, hs], ?_⟩
    intro hc
    rcases hcov.mp hc with hp | ⟨x, hx, hxocc⟩
    · exact hprev.2.1 hp hs
    · exact (σ j).2 i x hx ⟨hs, hxocc⟩

/-- The number of occupied entries summed over the rows counts the vertices of the set. -/
private theorem sum_occupiedCount_rowSignature (S : Finset (V × Fin n)) :
    ∑ j : Fin n, occupiedCount (rowSignature R S j).1 = S.card := by
  have hrow (j : Fin n) :
      occupiedCount (rowSignature R S j).1 = (S.filter fun v => v.2 = j).card := by
    unfold occupiedCount
    refine Finset.card_nbij' (fun i => (i, j)) Prod.fst ?_ ?_ ?_ ?_
    · intro i hi
      simpa [row_occupied_iff] using hi
    · rintro ⟨i, k⟩ hk
      obtain ⟨hm, rfl⟩ := Finset.mem_filter.mp hk
      simpa [row_occupied_iff] using hm
    · intro i _
      rfl
    · rintro ⟨i, k⟩ hk
      obtain ⟨_, rfl⟩ := Finset.mem_filter.mp hk
      rfl
  simp_rw [hrow]
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  simp

variable [DecidableEq V]

/-- Sum the transfer weights over compatible cyclic signatures, reindexing by dominating sets. -/
private theorem dominationPolynomial_box_cycle_eq_trace (R : SimpleGraph V) (n : ℕ) :
    dominationPolynomial (R □ cycleGraph (n + 1)) =
      Matrix.trace (dominationTransferMatrix R ^ (n + 1)) := by
  classical
  have weight (σ : Fin (n + 1) → DominationSignature R) :
      (∏ j, dominationTransferMatrix R (σ (finRotate _ j)) (σ j)) =
        if ∀ j, DominationCompatible R (σ (finRotate _ j)).1 (σ j).1 then
          X ^ (∑ j, occupiedCount (σ j).1) else 0 := by
    simp only [dominationTransferMatrix, Fintype.prod_ite_zero, Finset.prod_pow_eq_pow_sum]
    rw [Equiv.sum_comp (finRotate (n + 1)) (fun j => occupiedCount (σ j).1)]
  rw [trace_pow_succ_eq_sum]
  simp_rw [weight]
  rw [← Finset.sum_filter]
  unfold dominationPolynomial
  refine Finset.sum_nbij' (rowSignature R) occupiedVertices ?_ ?_ ?_ ?_ ?_
  · intro S hS
    simpa using (compatible_rowSignature_iff S).mpr ((Finset.mem_filter.mp hS).2)
  · intro σ hσ
    have hc := (Finset.mem_filter.mp hσ).2
    have he := rowSignature_occupiedVertices σ hc
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, (compatible_rowSignature_iff _).mp ?_⟩
    rw [he]
    exact hc
  · intro S _
    exact occupiedVertices_rowSignature S
  · intro σ hσ
    exact rowSignature_occupiedVertices σ (Finset.mem_filter.mp hσ).2
  · intro S _
    rw [sum_occupiedCount_rowSignature]

end dominationPolynomial_torus_eq_trace_transferMatrix_pow

@[expose] public section

open dominationPolynomial_torus_eq_trace_transferMatrix_pow in
/-- **Transfer-matrix formula for the domination polynomial of the torus.** For all natural
numbers $m$ and $n$ with $n \ge 1$, let $C_k$ denote the cycle graph on the vertices
$0, \dots, k - 1$, in which distinct $i$ and $j$ are adjacent when $i - j \equiv \pm 1 \pmod k$,
and let $\bar A$ be the domination transfer matrix of the row graph $C_m$. Then the domination
polynomial of the torus $C_m \mathbin{\square} C_n$ equals the trace of $\bar A^n$.

The hypothesis $n \ge 1$ is needed: for $n = 0$ the trace counts the signatures of $C_m$, while
the torus $C_m \mathbin{\square} C_0$ has no vertices, so its domination polynomial is $1$. For
$n = 1$ and $n = 2$ the cycle $C_n$ is a single vertex and a single edge respectively.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Theorem 8
(`jis-2024-24.7.6-thm-8`). -/
theorem dominationPolynomial_torus_eq_trace_transferMatrix_pow (m n : ℕ)
    (hn : 1 ≤ n) :
    dominationPolynomial (cycleGraph m □ cycleGraph n) =
      Matrix.trace (dominationTransferMatrix (cycleGraph m) ^ n) := by
  cases n with
  | zero => omega
  | succ n =>
    exact dominationPolynomial_box_cycle_eq_trace (cycleGraph m) n

end

end MetaMathlibExt
