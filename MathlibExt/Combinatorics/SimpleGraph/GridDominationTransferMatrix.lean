/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.GridDominationTransfer

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# The grid domination transfer formula

The domination polynomial of a grid is the sum of the entries of a power of the row transfer
matrix from the all-covered signature to signatures with no uncovered vertices.
-/

open Polynomial SimpleGraph

namespace MetaMathlibExt

namespace dominationPolynomial_grid_eq_sum_transferMatrix_pow

open DominationState

/-- Expand a power entry over sequences of destination indices, with the initial index prepended
to give the sources of the steps. -/
private theorem pow_apply_eq_sum {α K : Type*} [Fintype α] [DecidableEq α] [CommSemiring K]
    (A : Matrix α α K) (a b : α) (n : ℕ) :
    (A ^ n) b a =
      ∑ σ : Fin n → α, if Fin.cons (α := fun _ => α) a σ (Fin.last n) = b then
        ∏ j : Fin n, A (σ j) (Fin.cons (α := fun _ => α) a σ j.castSucc) else 0 := by
  induction n generalizing b with
  | zero =>
    simp [Matrix.one_apply, Finset.univ_unique, eq_comm]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply, ← (Fin.snocEquiv (fun _ : Fin (n + 1) => α)).sum_comp,
      Fintype.sum_prod_type]
    simp_rw [ih, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Fin.snocEquiv_apply, Fin.cons_snoc_eq_snoc_cons, Fin.snoc_last,
      Fin.prod_univ_castSucc, Fin.snoc_castSucc, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_comm]

variable {V : Type*} {n : ℕ} {R : SimpleGraph V}

/-- Coverage already supplied when the row is introduced comes from its predecessor or its
own occupied neighbors. -/
private def coveredFromPrevious (R : SimpleGraph V) (S : Finset (V × Fin n))
    (i : V) (j : Fin n) : Prop :=
  (∃ k : Fin n, k.val + 1 = j.val ∧ (i, k) ∈ S) ∨ ∃ x, R.Adj i x ∧ (x, j) ∈ S

open scoped Classical in
/-- Read the row state before adding any vertices from its successor. -/
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

/-- Prepend the all-covered boundary row. -/
private def withInitial (σ : Fin n → DominationSignature R) : Fin (n + 1) → DominationSignature R :=
  Fin.cons (α := fun _ => DominationSignature R) (allCoveredSignature R) σ

private theorem previous_eq (σ : Fin n → DominationSignature R) {k j : Fin n}
    (h : k.val + 1 = j.val) : withInitial σ j.castSucc = σ k := by
  have hk : k.succ = j.castSucc := Fin.ext h
  rw [← hk]
  exact Fin.cons_succ ..

private theorem previous_state_iff (σ : Fin n → DominationSignature R) (i : V) (j : Fin n)
    {s : DominationState} (hs : s ≠ covered) :
    (withInitial σ j.castSucc).1 i = s ↔
      ∃ k : Fin n, k.val + 1 = j.val ∧ (σ k).1 i = s := by
  constructor
  · intro h
    rcases Fin.eq_zero_or_eq_succ j.castSucc with hzero | ⟨k, hk⟩
    · rw [hzero] at h
      exact (hs h.symm).elim
    · have hkj : k.val + 1 = j.val := congrArg Fin.val hk.symm
      exact ⟨k, hkj, previous_eq σ hkj ▸ h⟩
  · rintro ⟨k, hkj, hk⟩
    simpa only [previous_eq σ hkj] using hk

/-- Domination is equivalent to every still-uncovered vertex being occupied in the next row
at the same column. -/
private theorem dominates_iff (S : Finset (V × Fin n)) :
    (R □ pathGraph n).IsDominating (S : Set _) ↔
      ∀ i j, (rowSignature R S j).1 i = uncovered →
        ∃ k : Fin n, j.val + 1 = k.val ∧ (i, k) ∈ S := by
  constructor
  · intro h i j hu
    obtain ⟨hnm, hnc⟩ := (row_uncovered_iff S i j).mp hu
    rcases h (i, j) with hm | ⟨⟨x, k⟩, hm, ha⟩
    · exact (hnm hm).elim
    rcases boxProd_adj.mp ha with ⟨hrow, rfl : k = j⟩ | ⟨hcol, rfl : x = i⟩
    · exact (hnc (Or.inr ⟨x, hrow.symm, hm⟩)).elim
    rcases pathGraph_adj.mp hcol with hprev | hnext
    · exact (hnc (Or.inl ⟨k, hprev, hm⟩)).elim
    · exact ⟨k, hnext, hm⟩
  · rintro h ⟨i, j⟩
    by_cases hm : (i, j) ∈ S
    · exact Or.inl hm
    by_cases hc : coveredFromPrevious R S i j
    · rcases hc with ⟨k, hk, hm'⟩ | ⟨x, hx, hm'⟩
      · exact Or.inr ⟨_, hm', boxProd_adj_right.mpr (pathGraph_adj.mpr (Or.inl hk))⟩
      · exact Or.inr ⟨_, hm', boxProd_adj_left.mpr hx.symm⟩
    · obtain ⟨k, hk, hm'⟩ := h i j ((row_uncovered_iff S i j).mpr ⟨hm, hc⟩)
      exact Or.inr ⟨_, hm', boxProd_adj_right.mpr (pathGraph_adj.mpr (Or.inr hk))⟩

/-- Accepted sequences start from the all-covered boundary, have compatible consecutive
signatures, and end with no uncovered vertices. -/
private def accepts (σ : Fin n → DominationSignature R) : Prop :=
  (∀ j, DominationCompatible R (σ j).1 (withInitial σ j.castSucc).1) ∧
    ∀ i, (withInitial σ (Fin.last n)).1 i ≠ uncovered

/-- The compatible complete sequences obtained from vertex sets are exactly those of
dominating sets. -/
private theorem accepts_rowSignature_iff (S : Finset (V × Fin n)) :
    accepts (rowSignature R S) ↔ (R □ pathGraph n).IsDominating (S : Set _) := by
  rw [dominates_iff]
  constructor
  · rintro ⟨hsteps, hfinal⟩ i j hu
    by_cases hj : j.val + 1 = n
    · have he : j.succ = Fin.last n := Fin.ext hj
      exact (hfinal i (by simpa [← he, withInitial] using hu)).elim
    · let k : Fin n := ⟨j.val + 1, by omega⟩
      have hk : j.val + 1 = k.val := rfl
      have hstep := (hsteps k i).1
      rw [previous_eq _ hk] at hstep
      exact ⟨k, hk, (row_occupied_iff S i k).mp (hstep hu)⟩
  · intro h
    refine ⟨fun j i => ⟨?_, ?_, ?_⟩, ?_⟩
    · intro hu
      obtain ⟨k, hk, hku⟩ := (previous_state_iff _ i j (by decide)).mp hu
      obtain ⟨l, hl, hocc⟩ := h i k hku
      have he : l = j := Fin.ext (hl.symm.trans hk)
      exact (row_occupied_iff S i j).mpr (he ▸ hocc)
    · intro hp hu
      obtain ⟨k, hk, hko⟩ := (previous_state_iff _ i j (by decide)).mp hp
      exact ((row_uncovered_iff S i j).mp hu).2
        (Or.inl ⟨k, hk, (row_occupied_iff S i k).mp hko⟩)
    · intro hc
      rcases ((row_covered_iff S i j).mp hc).2 with ⟨k, hk, hmem⟩ | ⟨x, hx, hmem⟩
      · exact Or.inl ((previous_state_iff _ i j (by decide)).mpr
          ⟨k, hk, (row_occupied_iff S i k).mpr hmem⟩)
      · exact Or.inr ⟨x, hx, (row_occupied_iff S x j).mpr hmem⟩
    · intro i hu
      rcases Fin.eq_zero_or_eq_succ (Fin.last n) with hzero | ⟨j, hj⟩
      · rw [hzero] at hu
        exact DominationState.noConfusion hu
      · rw [hj, withInitial, Fin.cons_succ] at hu
        obtain ⟨k, hk, _⟩ := h i j hu
        have hlast : n = j.val + 1 := congrArg Fin.val hj
        omega

variable [Fintype V]

open scoped Classical in
/-- Recover the vertex set from all occupied entries. -/
private noncomputable def occupiedVertices (σ : Fin n → DominationSignature R) :
    Finset (V × Fin n) :=
  Finset.univ.filter fun v => (σ v.2).1 v.1 = occupied

private theorem occupiedVertices_rowSignature (S : Finset (V × Fin n)) :
    occupiedVertices (rowSignature R S) = S := by
  ext ⟨i, j⟩
  simp [occupiedVertices, row_occupied_iff]

/-- Compatibility makes the occupied entries determine every state of every row. -/
private theorem rowSignature_occupiedVertices (σ : Fin n → DominationSignature R)
    (h : accepts σ) : rowSignature R (occupiedVertices σ) = σ := by
  funext j
  apply Subtype.ext
  funext i
  have hstep := h.1 j i
  have hcov : coveredFromPrevious R (occupiedVertices σ) i j ↔
      (withInitial σ j.castSucc).1 i = occupied ∨ ∃ x, R.Adj i x ∧ (σ j).1 x = occupied := by
    rw [previous_state_iff σ i j (s := occupied) (by decide)]
    simp [coveredFromPrevious, occupiedVertices]
  cases hs : (σ j).1 i with
  | occupied => exact (row_occupied_iff ..).mpr (by simp [occupiedVertices, hs])
  | covered =>
    exact (row_covered_iff ..).mpr ⟨by simp [occupiedVertices, hs], hcov.mpr (hstep.2.2 hs)⟩
  | uncovered =>
    refine (row_uncovered_iff ..).mpr ⟨by simp [occupiedVertices, hs], ?_⟩
    intro hc
    rcases hcov.mp hc with hp | ⟨x, hx, hxo⟩
    · exact hstep.2.1 hp hs
    · exact (σ j).2 i x hx ⟨hs, hxo⟩

/-- Summing the occupied counts over the rows counts the vertices of the set. -/
private theorem sum_occupiedCount_rowSignature (S : Finset (V × Fin n)) :
    ∑ j : Fin n, occupiedCount (rowSignature R S j).1 = S.card := by
  classical
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

open scoped Classical in
/-- Reindex the sum of the weights of accepted sequences by their dominating vertex sets. -/
private theorem dominationPolynomial_box_path_eq_sum {m : ℕ} (R : SimpleGraph (Fin m)) (n : ℕ) :
    dominationPolynomial (R □ pathGraph n) =
      ∑ σ ∈ (Finset.univ : Finset (DominationSignature R)).filter
          (fun σ => ∀ i, σ.1 i ≠ uncovered),
        (dominationTransferMatrix R ^ n) σ (allCoveredSignature R) := by
  classical
  simp_rw [pow_apply_eq_sum]
  rw [Finset.sum_comm]
  have weight (σ : Fin n → DominationSignature R) :
      (∏ j : Fin n, dominationTransferMatrix R (σ j) (withInitial σ j.castSucc)) =
        if ∀ j, DominationCompatible R (σ j).1 (withInitial σ j.castSucc).1 then
          X ^ (∑ j, occupiedCount (σ j).1) else 0 := by
    simp only [dominationTransferMatrix, Fintype.prod_ite_zero, Finset.prod_pow_eq_pow_sum]
  have sum_eq (σ : Fin n → DominationSignature R) :
      (∑ b ∈ (Finset.univ : Finset (DominationSignature R)).filter
          (fun b => ∀ i, b.1 i ≠ uncovered),
        if withInitial σ (Fin.last n) = b then
          ∏ j : Fin n, dominationTransferMatrix R (σ j) (withInitial σ j.castSucc)
        else 0) =
        if accepts σ then X ^ (∑ j, occupiedCount (σ j).1) else 0 := by
    rw [Finset.sum_ite_eq, weight]
    simp [accepts, ite_and, and_comm]
  change _ = ∑ σ : Fin n → DominationSignature R,
    ∑ b ∈ (Finset.univ : Finset (DominationSignature R)).filter
      (fun b => ∀ i, b.1 i ≠ uncovered),
      if withInitial σ (Fin.last n) = b then
        ∏ j : Fin n, dominationTransferMatrix R (σ j) (withInitial σ j.castSucc) else 0
  simp_rw [sum_eq]
  rw [← Finset.sum_filter]
  unfold dominationPolynomial
  refine Finset.sum_nbij' (rowSignature R) occupiedVertices ?_ ?_ ?_ ?_ ?_
  · intro S hS
    simpa using (accepts_rowSignature_iff S).mpr ((Finset.mem_filter.mp hS).2)
  · intro σ hσ
    have hc := (Finset.mem_filter.mp hσ).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (accepts_rowSignature_iff _).mp ?_⟩
    rwa [rowSignature_occupiedVertices σ hc]
  · intro S _
    exact occupiedVertices_rowSignature S
  · intro σ hσ
    exact rowSignature_occupiedVertices σ (Finset.mem_filter.mp hσ).2
  · intro S _
    rw [sum_occupiedCount_rowSignature]

end dominationPolynomial_grid_eq_sum_transferMatrix_pow

@[expose] public section

open DominationState

open scoped Classical in
/-- **Transfer-matrix formula for the domination polynomial of the grid.** For all natural
numbers $m$ and $n$, let $P_k$ denote the path on the vertices $0, \dots, k - 1$, let $A$ be the
domination transfer matrix of the row graph $P_m$, indexed by the signatures of $P_m$, and let
$\sigma_\bullet$ be the all-covered signature. Then the domination polynomial of the grid
$P_m \mathbin{\square} P_n$ is

$$\sum_\sigma (A^n)_{\sigma, \sigma_\bullet},$$

the sum running over the signatures $\sigma$ of $P_m$ with no uncovered vertex.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Theorem 7
(`jis-2024-24.7.6-thm-7`). -/
theorem dominationPolynomial_grid_eq_sum_transferMatrix_pow (m n : ℕ) :
    dominationPolynomial (pathGraph m □ pathGraph n) =
      ∑ σ ∈ (Finset.univ : Finset (DominationSignature (pathGraph m))).filter
          (fun σ => ∀ i, σ.1 i ≠ uncovered),
        (dominationTransferMatrix (pathGraph m) ^ n) σ (allCoveredSignature _) :=
  dominationPolynomial_grid_eq_sum_transferMatrix_pow.dominationPolynomial_box_path_eq_sum
    (pathGraph m) n

end

end MetaMathlibExt
