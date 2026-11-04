/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.LinearCombination
import MathlibExt.Combinatorics.Words.LyndonWord

namespace MetaMathlibExt

@[expose] public section

section

variable {R : Type*} [CommRing R] (a : ℕ → R)

/-- The Hessenberg–Toeplitz matrix: `a (i + 1 - j)` on and below the first
superdiagonal, `0` above it. -/
private def tH (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  fun i j => if (j : ℕ) ≤ (i : ℕ) + 1 then a ((i : ℕ) + 1 - (j : ℕ)) else 0

/-- The signed sum over ordered compositions of `n`. -/
private def cS (n : ℕ) : R :=
  Finset.univ.sum (fun c : Composition n =>
    (-a 0) ^ (n - c.length) *
      Finset.univ.prod (fun r : Fin c.length => a (c.blocksFun r)))

private lemma comp_length_le {n : ℕ} (c : Composition n) : c.length ≤ n := by
  have h := List.length_le_sum_of_one_le c.blocks (fun i hi => c.blocks_pos hi)
  rwa [c.blocks_sum] at h

/-- Forward map for `splitEquiv`: values `< iv` go left, the rest go right. -/
private def splitTo (N iv : ℕ) (r : Fin N) : Fin iv ⊕ Fin (N - iv) :=
  if hr : r.val < iv then Sum.inl ⟨r.val, hr⟩
  else Sum.inr ⟨r.val - iv, by have h1 := r.isLt; omega⟩

/-- Backward map for `splitEquiv`. -/
private def splitInv (N iv : ℕ) (h : iv ≤ N) : Fin iv ⊕ Fin (N - iv) → Fin N :=
  Sum.elim (fun r => ⟨r.val, by have h1 := r.isLt; omega⟩)
    (fun r => ⟨r.val + iv, by have h1 := r.isLt; omega⟩)

/-- Splitting `Fin N` into values `< iv` and values `≥ iv`. -/
private def splitEquiv (N iv : ℕ) (h : iv ≤ N) : Fin N ≃ Fin iv ⊕ Fin (N - iv) where
  toFun := splitTo N iv
  invFun := splitInv N iv h
  left_inv := fun r => by
    simp only [splitTo]
    split
    · next hr =>
      have e : splitInv N iv h (Sum.inl ⟨r.val, hr⟩)
          = (⟨r.val, by have h1 := r.isLt; omega⟩ : Fin N) := rfl
      rw [e]
    · next hr =>
      have e : splitInv N iv h (Sum.inr ⟨r.val - iv, by have h1 := r.isLt; omega⟩)
          = (⟨r.val - iv + iv, by have h1 := r.isLt; omega⟩ : Fin N) := rfl
      rw [e]
      ext
      dsimp only
      omega
  right_inv := fun x => by
    rcases x with r | c
    · have e1 : splitInv N iv h (Sum.inl r)
          = (⟨r.val, by have h1 := r.isLt; omega⟩ : Fin N) := rfl
      rw [e1]
      simp only [splitTo, dite_eq_left r.isLt]
    · have e2 : splitInv N iv h (Sum.inr c)
          = (⟨c.val + iv, by have h1 := c.isLt; omega⟩ : Fin N) := rfl
      rw [e2]
      simp only [splitTo, dite_eq_right (show ¬ c.val + iv < iv by omega)]
      congr 1
      ext
      dsimp only
      omega

private lemma splitEquiv_symm_inl {N iv : ℕ} (h : iv ≤ N) (r : Fin iv) :
    (splitEquiv N iv h).symm (Sum.inl r)
      = (⟨r.val, by have h1 := r.isLt; omega⟩ : Fin N) := rfl

private lemma splitEquiv_symm_inr {N iv : ℕ} (h : iv ≤ N) (c : Fin (N - iv)) :
    (splitEquiv N iv h).symm (Sum.inr c)
      = (⟨c.val + iv, by have h1 := c.isLt; omega⟩ : Fin N) := rfl

private lemma succAbove_val_lt {N : ℕ} (i : Fin (N + 1)) {rv : ℕ} (hrv : rv < N)
    (hr : rv < i.val) : (i.succAbove (⟨rv, hrv⟩ : Fin N)).val = rv := by
  have hlt : (⟨rv, hrv⟩ : Fin N).castSucc < i := by
    rw [Fin.lt_def]
    change rv < i.val
    exact hr
  unfold Fin.succAbove
  rw [ite_eq_left hlt, Fin.val_castSucc]

private lemma succAbove_val_ge {N : ℕ} (i : Fin (N + 1)) {rv : ℕ} (hrv : rv < N)
    (hr : i.val ≤ rv) : (i.succAbove (⟨rv, hrv⟩ : Fin N)).val = rv + 1 := by
  have hlt : ¬ (⟨rv, hrv⟩ : Fin N).castSucc < i := by
    rw [Fin.lt_def]
    change ¬ rv < i.val
    omega
  unfold Fin.succAbove
  rw [ite_eq_right hlt, Fin.val_succ]

/-- Forward map: a composition of `n + 1` gives its first block and the rest. -/
private def compConsTo (n : ℕ) (c : Composition (n + 1))
    : Σ _i : Fin (n + 1), Composition (n - _i.val) :=
  have hne : c.blocks ≠ [] := by
    intro hcon
    have hs := c.blocks_sum
    rw [hcon] at hs
    simp at hs
  have hpos : 0 < c.blocks.head hne := c.blocks_pos (List.head_mem hne)
  have hsum : c.blocks.head hne + c.blocks.tail.sum = n + 1 := by
    have hs := c.blocks_sum
    rw [← List.cons_head_tail hne, List.sum_cons] at hs
    exact hs
  ⟨⟨c.blocks.head hne - 1, by omega⟩,
    ⟨c.blocks.tail,
      fun {i} hi => c.blocks_pos (by
        rw [← List.cons_head_tail hne]
        exact List.mem_cons_of_mem _ hi),
      by
        change c.blocks.tail.sum = n - (c.blocks.head hne - 1)
        omega⟩⟩

/-- Backward map: prepend a first block to a composition. -/
private def compConsInv (n : ℕ) (x : Σ _i : Fin (n + 1), Composition (n - _i.val))
    : Composition (n + 1) :=
  ⟨(x.1.val + 1) :: x.2.blocks,
    fun {i} hi => by
      rcases List.mem_cons.mp hi with rfl | hm
      · omega
      · exact x.2.blocks_pos hm,
    by
      have hs := x.2.blocks_sum
      have hlt := x.1.isLt
      rw [List.sum_cons]
      omega⟩

/-- A composition of `n + 1` is a first block together with a composition of
the rest. -/
private def compCons (n : ℕ) :
    Composition (n + 1) ≃ Σ _i : Fin (n + 1), Composition (n - _i.val) where
  toFun := compConsTo n
  invFun := compConsInv n
  left_inv := fun c => by
    have hne : c.blocks ≠ [] := by
      intro hcon
      have hs := c.blocks_sum
      rw [hcon] at hs
      simp at hs
    have hpos : 0 < c.blocks.head hne := c.blocks_pos (List.head_mem hne)
    apply Composition.ext
    simp only [compConsTo, compConsInv]
    rw [Nat.sub_add_cancel hpos, List.cons_head_tail hne]
  right_inv := fun x => by
    obtain ⟨i, d⟩ := x
    have h1 : (compConsTo n (compConsInv n ⟨i, d⟩)).1 = i := by
      simp only [compConsTo, compConsInv]
      exact Fin.ext (Nat.add_sub_cancel _ _)
    have h2 : (compConsTo n (compConsInv n ⟨i, d⟩)).2 ≍ d := by
      simp only [compConsTo, compConsInv]
      exact HEq.rfl
    exact Sigma.ext h1 h2

private lemma cS_term_cons (n : ℕ) (i : Fin (n + 1)) (d : Composition (n - i.val)) :
    (fun c : Composition (n + 1) => (-a 0) ^ ((n + 1) - c.length) *
        Finset.univ.prod (fun r : Fin c.length => a (c.blocksFun r)))
      ((compCons n).symm ⟨i, d⟩)
      = a (i.val + 1) * (-a 0) ^ i.val *
        (((-a 0) ^ ((n - i.val) - d.length)) *
          Finset.univ.prod (fun r : Fin d.length => a (d.blocksFun r))) := by
  have hprod : (∏ r : Fin (d.length + 1), a (((i.val + 1) :: d.blocks).get r))
      = a (i.val + 1) * ∏ r : Fin d.length, a (d.blocksFun r) := by
    rw [Fin.prod_univ_succ]
    refine congrArg₂ _ ?_ ?_
    · congr 1
    · apply Finset.prod_congr rfl
      intro r _
      congr 1
  have hexp : (n + 1) - (d.length + 1) = n - d.length := by omega
  have hsplit : n - d.length = i.val + ((n - i.val) - d.length) := by
    have hle := comp_length_le d
    have hlt := i.isLt
    omega
  change (-a 0) ^ ((n + 1) - (d.length + 1)) *
      (∏ r : Fin (d.length + 1), a (((i.val + 1) :: d.blocks).get r)) = _
  rw [hexp, hsplit, pow_add, hprod]
  ring

private lemma cS_succ (n : ℕ) :
    cS a (n + 1)
      = ∑ i : Fin (n + 1), a (i.val + 1) * (-a 0) ^ i.val * cS a (n - i.val) := by
  unfold cS
  rw [← Equiv.sum_comp (compCons n).symm, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  exact cS_term_cons a n i d

/-- Entries of the reindexed minor, top-left block. -/
private lemma minor_inl_inl (N : ℕ) (i : Fin (N + 1)) (r c : Fin i.val) :
    (Matrix.reindex (splitEquiv N i.val (Nat.le_of_lt_succ i.isLt))
        (splitEquiv N i.val (Nat.le_of_lt_succ i.isLt))
        ((tH a (N + 1)).submatrix i.succAbove Fin.succ)) (Sum.inl r) (Sum.inl c)
      = if c.val ≤ r.val then a (r.val - c.val) else 0 := by
  have hiv : i.val ≤ N := Nat.le_of_lt_succ i.isLt
  have hR : (i.succAbove (⟨r.val, by have h1 := r.isLt; omega⟩ : Fin N)).val = r.val :=
    succAbove_val_lt i _ r.isLt
  have hC : (Fin.succ (⟨c.val, by have h1 := c.isLt; omega⟩ : Fin N)).val = c.val + 1 := rfl
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, splitEquiv_symm_inl]
  unfold tH
  rw [hR, hC]
  by_cases h : c.val ≤ r.val
  · rw [ite_eq_left h, ite_eq_left (by omega)]
    congr 1
    omega
  · rw [ite_eq_right h, ite_eq_right (by omega)]

/-- Entries of the reindexed minor, top-right block: all zero. -/
private lemma minor_inl_inr (N : ℕ) (i : Fin (N + 1)) (r : Fin i.val) (c : Fin (N - i.val)) :
    (Matrix.reindex (splitEquiv N i.val (Nat.le_of_lt_succ i.isLt))
        (splitEquiv N i.val (Nat.le_of_lt_succ i.isLt))
        ((tH a (N + 1)).submatrix i.succAbove Fin.succ)) (Sum.inl r) (Sum.inr c)
      = 0 := by
  have hiv : i.val ≤ N := Nat.le_of_lt_succ i.isLt
  have hR : (i.succAbove (⟨r.val, by have h1 := r.isLt; omega⟩ : Fin N)).val = r.val :=
    succAbove_val_lt i _ r.isLt
  have hC : (Fin.succ (⟨c.val + i.val, by have h1 := c.isLt; omega⟩ : Fin N)).val
      = c.val + i.val + 1 := rfl
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, splitEquiv_symm_inl,
    splitEquiv_symm_inr]
  unfold tH
  rw [hR, hC, ite_eq_right (by have h1 := r.isLt; omega)]

/-- Entries of the reindexed minor, bottom-right block: the smaller matrix. -/
private lemma minor_inr_inr (N : ℕ) (i : Fin (N + 1)) (r c : Fin (N - i.val)) :
    (Matrix.reindex (splitEquiv N i.val (Nat.le_of_lt_succ i.isLt))
        (splitEquiv N i.val (Nat.le_of_lt_succ i.isLt))
        ((tH a (N + 1)).submatrix i.succAbove Fin.succ)) (Sum.inr r) (Sum.inr c)
      = tH a (N - i.val) r c := by
  have hiv : i.val ≤ N := Nat.le_of_lt_succ i.isLt
  have hR : (i.succAbove (⟨r.val + i.val, by have h1 := r.isLt; omega⟩ : Fin N)).val
      = r.val + i.val + 1 := by
    apply succAbove_val_ge i _ _
    have h1 := r.isLt
    omega
  have hC : (Fin.succ (⟨c.val + i.val, by have h1 := c.isLt; omega⟩ : Fin N)).val
      = c.val + i.val + 1 := rfl
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, splitEquiv_symm_inr]
  unfold tH
  rw [hR, hC]
  by_cases h : c.val ≤ r.val + 1
  · rw [ite_eq_left h, ite_eq_left (by omega)]
    congr 1
    omega
  · rw [ite_eq_right h, ite_eq_right (by omega)]

/-- The minor deleting row `i` and column `0` factors as `(a 0)^i * D (N - i)`. -/
private lemma minor_det_zero (N : ℕ) (i : Fin (N + 1)) :
    ((tH a (N + 1)).submatrix i.succAbove Fin.succ).det
      = (a 0) ^ i.val * (tH a (N - i.val)).det := by
  have hiv : i.val ≤ N := Nat.le_of_lt_succ i.isLt
  rw [← Matrix.det_reindex_self (splitEquiv N i.val hiv)]
  have hB : Matrix.reindex (splitEquiv N i.val hiv) (splitEquiv N i.val hiv)
        ((tH a (N + 1)).submatrix i.succAbove Fin.succ)
      = Matrix.fromBlocks
        (fun r c => Matrix.reindex (splitEquiv N i.val hiv) (splitEquiv N i.val hiv)
          ((tH a (N + 1)).submatrix i.succAbove Fin.succ) (Sum.inl r) (Sum.inl c)) 0
        (fun r c => Matrix.reindex (splitEquiv N i.val hiv) (splitEquiv N i.val hiv)
          ((tH a (N + 1)).submatrix i.succAbove Fin.succ) (Sum.inr r) (Sum.inl c))
        (fun r c => Matrix.reindex (splitEquiv N i.val hiv) (splitEquiv N i.val hiv)
          ((tH a (N + 1)).submatrix i.succAbove Fin.succ) (Sum.inr r) (Sum.inr c)) := by
    apply Matrix.ext
    intro x y
    rcases x with r | r <;> rcases y with c | c
    · rfl
    · change (Matrix.reindex (splitEquiv N i.val hiv) (splitEquiv N i.val hiv)
          ((tH a (N + 1)).submatrix i.succAbove Fin.succ)) (Sum.inl r) (Sum.inr c) = 0
      have h := minor_inl_inr a N i r c
      have he : splitEquiv N i.val (Nat.le_of_lt_succ i.isLt) = splitEquiv N i.val hiv :=
        rfl
      rw [he] at h
      exact h
    · rfl
    · rfl
  rw [hB]
  have hdet := Matrix.det_fromBlocks_zero₁₂
    (fun r c => Matrix.reindex (splitEquiv N i.val hiv) (splitEquiv N i.val hiv)
      ((tH a (N + 1)).submatrix i.succAbove Fin.succ) (Sum.inl r) (Sum.inl c))
    (fun r c => Matrix.reindex (splitEquiv N i.val hiv) (splitEquiv N i.val hiv)
      ((tH a (N + 1)).submatrix i.succAbove Fin.succ) (Sum.inr r) (Sum.inl c))
    (fun r c => Matrix.reindex (splitEquiv N i.val hiv) (splitEquiv N i.val hiv)
      ((tH a (N + 1)).submatrix i.succAbove Fin.succ) (Sum.inr r) (Sum.inr c))
  rw [hdet]
  set Ablk : Matrix (Fin i.val) (Fin i.val) R :=
    fun r c => Matrix.reindex (splitEquiv N i.val hiv) (splitEquiv N i.val hiv)
      ((tH a (N + 1)).submatrix i.succAbove Fin.succ) (Sum.inl r) (Sum.inl c) with hAblk
  have htri : Ablk.IsLowerTriangular := by
    intro p q hpq
    have hpq' : p.val < q.val := by
      have h2 := OrderDual.toDual_lt_toDual.mp hpq
      rwa [Fin.lt_def] at h2
    change (Matrix.reindex (splitEquiv N i.val hiv) (splitEquiv N i.val hiv)
        ((tH a (N + 1)).submatrix i.succAbove Fin.succ)) (Sum.inl p) (Sum.inl q) = 0
    have h := minor_inl_inl a N i p q
    have he : splitEquiv N i.val (Nat.le_of_lt_succ i.isLt) = splitEquiv N i.val hiv :=
      rfl
    rw [he, ite_eq_right (by omega)] at h
    exact h
  have hA : Ablk.det = (a 0) ^ i.val := by
    rw [Matrix.det_of_isLowerTriangular _ htri]
    have hdiag : ∀ r : Fin i.val, Ablk r r = a 0 := by
      intro r
      change (Matrix.reindex (splitEquiv N i.val hiv) (splitEquiv N i.val hiv)
          ((tH a (N + 1)).submatrix i.succAbove Fin.succ)) (Sum.inl r) (Sum.inl r)
          = a 0
      have h := minor_inl_inl a N i r r
      have he : splitEquiv N i.val (Nat.le_of_lt_succ i.isLt)
          = splitEquiv N i.val hiv := rfl
      rw [he, ite_eq_left le_rfl] at h
      have hsub : r.val - r.val = 0 := by omega
      rw [hsub] at h
      exact h
    have hprod : (∏ r : Fin i.val, Ablk r r) = ∏ _r : Fin i.val, a 0 :=
      Finset.prod_congr rfl (fun r _ => hdiag r)
    rw [hprod, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hD : (fun r c => Matrix.reindex (splitEquiv N i.val hiv) (splitEquiv N i.val hiv)
      ((tH a (N + 1)).submatrix i.succAbove Fin.succ)
        (Sum.inr r) (Sum.inr c)) = tH a (N - i.val) := by
    apply Matrix.ext
    intro r c
    show (Matrix.reindex (splitEquiv N i.val hiv) (splitEquiv N i.val hiv)
        ((tH a (N + 1)).submatrix i.succAbove Fin.succ)) (Sum.inr r) (Sum.inr c)
        = tH a (N - i.val) r c
    have h := minor_inr_inr a N i r c
    have he : splitEquiv N i.val (Nat.le_of_lt_succ i.isLt) = splitEquiv N i.val hiv :=
      rfl
    rw [he] at h
    exact h
  rw [hA, hD]

/-- Determinant recurrence from expansion along the first column. -/
private lemma det_succ (n : ℕ) :
    (tH a (n + 1)).det
      = ∑ i : Fin (n + 1), a (i.val + 1) * (-a 0) ^ i.val * (tH a (n - i.val)).det := by
  have hexp := Matrix.det_succ_column_zero (tH a (n + 1))
  rw [hexp]
  apply Finset.sum_congr rfl
  intro i _
  have hi : i.val ≤ n := Nat.le_of_lt_succ i.isLt
  rw [minor_det_zero a n i]
  have hM : tH a (n + 1) i 0 = a (i.val + 1) := by
    unfold tH
    have h0 : ((0 : Fin (n + 1)).val) = 0 := rfl
    rw [h0, ite_eq_left (Nat.zero_le _)]
    congr 1
  rw [hM, neg_pow]
  ring

private lemma base0 : (tH a 0).det = cS a 0 := by
  rw [Matrix.det_fin_zero]
  set c0 : Composition 0 :=
    ⟨[], fun {i} hi => by simp at hi, rfl⟩ with hc0
  have h0 : ∀ c : Composition 0, c = c0 := by
    intro c
    apply Composition.ext
    have hlen : c.blocks.length = 0 := Nat.le_zero.mp (comp_length_le c)
    exact List.length_eq_zero_iff.mp hlen
  have hU : (Finset.univ : Finset (Composition 0)) = {c0} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    exact ⟨Finset.mem_univ _, fun c _ => h0 c⟩
  have hl : c0.length = 0 := rfl
  have hterm : (-a 0) ^ (0 - c0.length) *
      Finset.univ.prod (fun r : Fin c0.length => a (c0.blocksFun r)) = 1 := by
    have hl : c0.length = 0 := rfl
    have hempty : (Finset.univ : Finset (Fin c0.length)) = ∅ := by
      rw [← Finset.card_eq_zero, Finset.card_univ, Fintype.card_fin, hl]
    rw [hempty, Finset.prod_empty, hl, Nat.sub_zero, pow_zero, one_mul]
  unfold cS
  rw [hU, Finset.sum_singleton]
  exact hterm.symm

private lemma step (N : ℕ) (IH : ∀ m, m ≤ N → (tH a m).det = cS a m) :
    (tH a (N + 1)).det = cS a (N + 1) := by
  rw [det_succ a N, cS_succ a N]
  apply Finset.sum_congr rfl
  intro i _
  rw [IH (N - i.val) (Nat.sub_le _ _)]

end

/-- **Trudi's formula for Toeplitz–Hessenberg determinants, general case.** Let $R$ be a
commutative ring, let $n \ge 0$, and let $a_0, a_1, a_2, \dots$ be any elements of $R$. Let $A_n$
be the $n \times n$ matrix whose entry in row $i$ and column $j$ ($0 \le i, j < n$) is $a_{i+1-j}$
if $j \le i + 1$ and $0$ otherwise; for $n = 0$ it is the empty matrix, whose determinant is $1$.
Then
$$\det A_n = \sum_{c} (-a_0)^{n - \ell(c)} \, a_{c_1} a_{c_2} \cdots a_{c_{\ell(c)}},$$
where $c = (c_1, \dots, c_{\ell(c)})$ runs over the compositions of $n$, that is, the finite
sequences of positive integers with sum $n$, and $\ell(c)$ is the number of parts of $c$.

No hypothesis $n \ge 1$ or $a_0 \ne 0$ is needed. -/
theorem Matrix.det_toeplitzHessenberg_eq_sum_compositions_general {R : Type*}
    [CommRing R] (n : Nat) (a : Nat → R) :
    Matrix.det (fun i j : Fin n =>
      if (j : Nat) ≤ (i : Nat) + 1 then a ((i : Nat) + 1 - (j : Nat)) else 0) =
    Finset.univ.sum (fun c : Composition n =>
      (-a 0) ^ (n - c.length) *
        Finset.univ.prod (fun r : Fin c.length => a (c.blocksFun r))) := by
  have hall : ∀ N m, m ≤ N → (tH a m).det = cS a m := by
    intro N
    induction N with
    | zero =>
      intro m hm
      have hm0 : m = 0 := Nat.le_zero.mp hm
      subst hm0
      exact base0 a
    | succ N IH =>
      intro m hm
      rcases Nat.eq_zero_or_pos m with rfl | hmpos
      · exact base0 a
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
        exact step a k (fun m' hm' => IH m' (by omega))
  exact hall n n le_rfl

set_option linter.unusedVariables false in
/-- **Trudi's formula for Toeplitz–Hessenberg determinants.** Let $R$ be a commutative ring, let
$n \ge 1$, and let $a_0, a_1, a_2, \dots$ be elements of $R$ with $a_0 \ne 0$. Let $A_n$ be the
$n \times n$ matrix whose entry in row $i$ and column $j$ ($0 \le i, j < n$) is $a_{i+1-j}$ if
$j \le i + 1$ and $0$ otherwise. Then
$$\det A_n = \sum_{c} (-a_0)^{n - \ell(c)} \, a_{c_1} a_{c_2} \cdots a_{c_{\ell(c)}},$$
where $c = (c_1, \dots, c_{\ell(c)})$ runs over the compositions of $n$, that is, the finite
sequences of positive integers with sum $n$, and $\ell(c)$ is the number of parts of $c$.

Proves `Wanted` entry `Matrix.det_toeplitzHessenberg_eq_sum_compositions`.
It follows from `Matrix.det_toeplitzHessenberg_eq_sum_compositions_general`; the hypotheses `hn`
and `ha0` are unused and keep the source's shape. The multinomial partition-indexed display over
`s_1 + 2 * s_2 + … + n * s_n = n` is a source-declared equivalent encoding of this composition
sum and is not stated separately; Brioschi's formula is the `a_0 = 1` specialization (line 167).

Source: Taras Goy and Mark Shattuck, *Determinants of Some
Hessenberg-Toeplitz Matrices with Motzkin Number Entries*, Journal of Integer
Sequences 26 (2023), Article 23.3.4, matrix display `DetHess` lines 146–155,
Lemma `lem1` lines 157–166 with equation `Trudi` at lines 159–161 and the
equivalent composition sum at lines 163–165,
<https://cs.uwaterloo.ca/journals/JIS/VOL26/Shattuck/sh36.tex>.
-/
theorem Matrix.det_toeplitzHessenberg_eq_sum_compositions {R : Type*}
    [CommRing R] (n : Nat) (hn : 0 < n) (a : Nat → R) (ha0 : a 0 ≠ 0) :
    Matrix.det (fun i j : Fin n =>
      if (j : Nat) ≤ (i : Nat) + 1 then a ((i : Nat) + 1 - (j : Nat)) else 0) =
    Finset.univ.sum (fun c : Composition n =>
      (-a 0) ^ (n - c.length) *
        Finset.univ.prod (fun r : Fin c.length => a (c.blocksFun r))) :=
  Matrix.det_toeplitzHessenberg_eq_sum_compositions_general n a


/-! ### The Toeplitz–Hessenberg determinant and Trudi's partition sum -/

/-- **Toeplitz–Hessenberg determinant.** Let $R$ be a commutative ring, let $a_0, a_1, a_2, \dots$
be elements of $R$ and let $n \ge 0$. The Toeplitz–Hessenberg determinant $\det A_n$ is the
determinant of the $n \times n$ matrix $A_n = A_n(a_0; a_1, \dots, a_n)$ whose entry in row $i$
and column $j$ ($0 \le i, j < n$) is $a_{i+1-j}$ if $j \le i + 1$ and $0$ otherwise. Thus $a_0$
fills the superdiagonal, $a_1$ the diagonal, and every entry above the superdiagonal is $0$. For
$n = 0$ the determinant is $1$.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Section 2, display
(1) and the notation `D_±`. -/
def toeplitzHessenbergDet {R : Type*} [CommRing R] (a : ℕ → R) (n : ℕ) : R :=
  (Matrix.of fun i j : Fin n =>
    if (j : ℕ) ≤ (i : ℕ) + 1 then a ((i : ℕ) + 1 - (j : ℕ)) else 0).det

/-- **The $1 \times 1$ Toeplitz–Hessenberg determinant.** For every commutative ring $R$ and every
sequence $a_0, a_1, a_2, \dots$ in $R$, the Toeplitz–Hessenberg determinant of size $1$ built
from $a$ is $\det A_1 = a_1$.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Section 2,
display (1). -/
theorem toeplitzHessenbergDet_one {R : Type*} [CommRing R] (a : ℕ → R) :
    toeplitzHessenbergDet a 1 = a 1 := by
  rw [toeplitzHessenbergDet, Matrix.det_fin_one]
  simp

/-- **The $2 \times 2$ Toeplitz–Hessenberg determinant.** For every commutative ring $R$ and every
sequence $a_0, a_1, a_2, \dots$ in $R$, the Toeplitz–Hessenberg determinant of size $2$ built
from $a$ is $\det A_2 = a_1^2 - a_0 a_2$.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Section 2,
display (1). -/
theorem toeplitzHessenbergDet_two {R : Type*} [CommRing R] (a : ℕ → R) :
    toeplitzHessenbergDet a 2 = a 1 ^ 2 - a 0 * a 2 := by
  rw [toeplitzHessenbergDet, Matrix.det_fin_two]
  simp
  ring

/-- **Trudi's formula in composition form.** Let $R$ be a commutative ring, let
$a_0, a_1, a_2, \dots$ be elements of $R$ and let $n \ge 0$. The Toeplitz–Hessenberg determinant
$\det A_n$ of size $n$ built from $a$ satisfies
$$\det A_n = \sum_{c} (-a_0)^{n - \ell(c)} \, a_{c_1} a_{c_2} \cdots a_{c_{\ell(c)}},$$
where $c = (c_1, \dots, c_{\ell(c)})$ runs over the compositions of $n$, that is, the finite
sequences of positive integers with sum $n$, and $\ell(c)$ is the number of parts of $c$.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Lemma 1 and
Section 3 (the composition form of the determinant). -/
theorem toeplitzHessenbergDet_eq_sum_compositions {R : Type*} [CommRing R] (a : ℕ → R)
    (n : ℕ) :
    toeplitzHessenbergDet a n =
      ∑ c : Composition n, (-a 0) ^ (n - c.length) * ∏ r : Fin c.length, a (c.blocksFun r) :=
  Matrix.det_toeplitzHessenberg_eq_sum_compositions_general n a

/-- **Trudi's partition sum.** Let $R$ be a commutative semiring, let $s \in R$, let $n$ be a
natural number, and let $a : \mathbb{N} \to R$ (only $a_1, \dots, a_n$ enter). Trudi's
partition sum is
$$
\sum_{\alpha} s^{|\alpha|} \, m_n(\alpha) \, a_1^{\alpha_1} a_2^{\alpha_2} \cdots a_n^{\alpha_n},
$$
where $\alpha = (\alpha_1, \dots, \alpha_n)$ runs over the tuples of natural numbers with
$\alpha_1 + 2\alpha_2 + \cdots + n\alpha_n = n$, $|\alpha| = \alpha_1 + \cdots + \alpha_n$, and
$m_n(\alpha) = |\alpha|! / (\alpha_1! \cdots \alpha_n!)$ is the multinomial coefficient, taken in
$R$. Such a tuple records a partition of $n$ with $\alpha_i$ parts equal to $i$. For $n = 0$ the
sum has the single empty term and equals $1$.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Lemma 1 (notation
`α̃`, `|α|`, `m_n(α)`). -/
def trudiPartitionSum {R : Type*} [CommSemiring R] (s : R) (a : ℕ → R) (n : ℕ) : R :=
  ∑ α ∈ (Fintype.piFinset fun _ : Fin n => Finset.range (n + 1)).filter
      (fun α => ∑ i : Fin n, ((i : ℕ) + 1) * α i = n),
    s ^ (∑ i : Fin n, α i) * (Nat.multinomial Finset.univ α : R) *
      ∏ i : Fin n, a ((i : ℕ) + 1) ^ α i


variable {n : ℕ}

private def compContent (c : Composition n) : Fin n → ℕ := fun i => c.blocks.count ((i : ℕ) + 1)

private lemma sum_map_eq_sum_count {M : Type*} [AddCommMonoid M] (l : List ℕ)
    (hl : ∀ b ∈ l, 1 ≤ b ∧ b ≤ n) (f : ℕ → M) :
    (l.map f).sum = ∑ i : Fin n, l.count ((i : ℕ) + 1) • f ((i : ℕ) + 1) := by
  classical
  rw [Finset.sum_list_map_count, Fin.sum_univ_eq_sum_range (fun i => l.count (i + 1) • f (i + 1))]
  have hsub : l.toFinset ⊆ Finset.range (n + 1) := fun b hb => by
    have := hl b (List.mem_toFinset.1 hb); simp only [Finset.mem_range]; omega
  rw [Finset.sum_subset hsub (fun m _ hm => by
    rw [List.count_eq_zero_of_not_mem (fun h => hm (List.mem_toFinset.2 h)), zero_smul]),
    Finset.sum_range_succ']
  have h0 : l.count 0 = 0 := List.count_eq_zero_of_not_mem (fun h => by have := hl 0 h; omega)
  rw [h0, zero_smul, add_zero]

private lemma prod_map_eq_prod_count {M : Type*} [CommMonoid M] (l : List ℕ)
    (hl : ∀ b ∈ l, 1 ≤ b ∧ b ≤ n) (f : ℕ → M) :
    (l.map f).prod = ∏ i : Fin n, f ((i : ℕ) + 1) ^ l.count ((i : ℕ) + 1) := by
  classical
  rw [Finset.prod_list_map_count, Fin.prod_univ_eq_prod_range (fun i => f (i + 1) ^ l.count (i + 1))]
  have hsub : l.toFinset ⊆ Finset.range (n + 1) := fun b hb => by
    have := hl b (List.mem_toFinset.1 hb); simp only [Finset.mem_range]; omega
  rw [Finset.prod_subset hsub (fun m _ hm => by
    rw [List.count_eq_zero_of_not_mem (fun h => hm (List.mem_toFinset.2 h)), pow_zero]),
    Finset.prod_range_succ']
  have h0 : l.count 0 = 0 := List.count_eq_zero_of_not_mem (fun h => by have := hl 0 h; omega)
  rw [h0, pow_zero, mul_one]

private lemma blocks_bounds (c : Composition n) : ∀ b ∈ c.blocks, 1 ≤ b ∧ b ≤ n := fun _ hb =>
  ⟨c.one_le_blocks hb, c.blocks_sum ▸ List.le_sum_of_mem hb⟩

private lemma card_compContent_fiber (α : Fin n → ℕ)
    (hα : ∑ i : Fin n, ((i : ℕ) + 1) * α i = n) :
    (Finset.univ.filter fun c : Composition n => compContent c = α).card =
      Nat.multinomial Finset.univ α := by
  classical
  rw [← card_wordsOfContent_eq_multinomial, ← Fintype.card_subtype, Fintype.card_eq_nat_card,
    Fintype.card_eq_nat_card]
  have hg : Function.Injective (fun i : Fin n => (i : ℕ) + 1) := fun i j h =>
    Fin.ext (by simpa using h)
  have hb : ∀ w : List (Fin n), ∀ b ∈ w.map (fun i : Fin n => (i : ℕ) + 1), 1 ≤ b ∧ b ≤ n :=
    fun w b hb => by obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb; exact ⟨by omega, by omega⟩
  let f : {w : List (Fin n) // wittWordContent w = α} → {c : Composition n // compContent c = α} :=
    fun w =>
    ⟨{ blocks := w.1.map (fun i : Fin n => (i : ℕ) + 1)
       blocks_pos := fun hb' => (hb w.1 _ hb').1
       blocks_sum := by
         have key := sum_map_eq_sum_count (w.1.map (fun i : Fin n => (i : ℕ) + 1)) (hb w.1) id
         rw [List.map_id] at key
         refine key.trans (Eq.trans ?_ hα)
         refine Finset.sum_congr rfl fun i _ => ?_
         have hi : w.1.count i = α i := congrFun w.2 i
         rw [List.count_map_of_injective _ _ hg, hi, smul_eq_mul, mul_comm]; rfl },
     by
       funext i
       have hi : w.1.count i = α i := congrFun w.2 i
       change (w.1.map (fun i : Fin n => (i : ℕ) + 1)).count ((i : ℕ) + 1) = α i
       rw [List.count_map_of_injective _ _ hg, hi]⟩
  have hbij : Function.Bijective f := by
    refine ⟨fun w v h => ?_, fun ⟨c, hc⟩ => ?_⟩
    · have h1 := congrArg (fun x => x.1.blocks) h
      exact Subtype.ext ((List.map_injective_iff.2 hg) h1)
    · have hlt : ∀ b ∈ c.blocks, b - 1 < n := fun b hb => by
        have := blocks_bounds c b hb; omega
      let w : List (Fin n) := c.blocks.pmap (fun b hb => (⟨b - 1, hb⟩ : Fin n)) hlt
      have hw : w.map (fun i : Fin n => (i : ℕ) + 1) = c.blocks := by
        simp only [w, List.map_pmap]
        rw [List.pmap_eq_self]
        intro b hb
        have := blocks_bounds c b hb; omega
      refine ⟨⟨w, ?_⟩, ?_⟩
      · funext i
        change w.count i = α i
        rw [← List.count_map_of_injective _ _ hg, hw, ← hc]; rfl
      · apply Subtype.ext
        apply Composition.ext
        exact hw
  exact (Nat.card_eq_of_bijective f hbij).symm

/-- **Trudi's partition sum as a sum over compositions.** Let $R$ be a commutative semiring, let
$s \in R$, let $a_0, a_1, a_2, \dots$ be elements of $R$ and let $n \ge 0$. Trudi's partition sum
$$\sum_\alpha s^{|\alpha|} m_n(\alpha) \, a_1^{\alpha_1} a_2^{\alpha_2} \cdots a_n^{\alpha_n},$$
taken over the tuples $\alpha = (\alpha_1, \dots, \alpha_n)$ of nonnegative integers with
$\alpha_1 + 2\alpha_2 + \dots + n\alpha_n = n$, where $|\alpha| = \alpha_1 + \dots + \alpha_n$ and
$m_n(\alpha) = |\alpha|! / (\alpha_1! \cdots \alpha_n!)$, equals
$$\sum_c s^{\ell(c)} \, a_{c_1} a_{c_2} \cdots a_{c_{\ell(c)}},$$
where $c = (c_1, \dots, c_{\ell(c)})$ runs over the compositions of $n$, that is, the finite
sequences of positive integers with sum $n$, and $\ell(c)$ is the number of parts of $c$.

The multinomial coefficient $m_n(\alpha)$ counts the compositions of $n$ in which each part $i$
occurs $\alpha_i$ times.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Lemma 1 and the
composition reading of `det(A_n)` in Section 3. -/
theorem trudiPartitionSum_eq_sum_compositions {R : Type*} [CommSemiring R] (s : R) (a : ℕ → R) (n : ℕ) :
    trudiPartitionSum s a n =
      ∑ c : Composition n, s ^ c.length * ∏ r : Fin c.length, a (c.blocksFun r) := by
  classical
  have hterm : ∀ c : Composition n, s ^ c.length * ∏ r : Fin c.length, a (c.blocksFun r) =
      s ^ (∑ i, compContent c i) * ∏ i : Fin n, a ((i : ℕ) + 1) ^ compContent c i := by
    intro c
    have hprod : ∏ r : Fin c.length, a (c.blocksFun r) = (c.blocks.map a).prod := by
      rw [← List.prod_ofFn, ← c.ofFn_blocksFun, List.map_ofFn]; rfl
    have hlen : c.length = ∑ i, compContent c i := by
      have := sum_map_eq_sum_count c.blocks (blocks_bounds c) (fun _ => (1 : ℕ))
      simpa [compContent] using this
    rw [hprod, prod_map_eq_prod_count c.blocks (blocks_bounds c), hlen]; rfl
  have hmaps : ∀ c ∈ (Finset.univ : Finset (Composition n)),
      compContent c ∈ (Fintype.piFinset fun _ : Fin n => Finset.range (n + 1)).filter
        (fun α => ∑ i : Fin n, ((i : ℕ) + 1) * α i = n) := by
    intro c _
    refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => Finset.mem_range.2 ?_, ?_⟩
    · exact Nat.lt_succ_of_le ((List.count_le_length).trans c.length_le)
    · have := sum_map_eq_sum_count c.blocks (blocks_bounds c) id
      rw [List.map_id, c.blocks_sum] at this
      refine Eq.trans ?_ this.symm
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [compContent, mul_comm]
  rw [Finset.sum_congr rfl (fun c _ => hterm c), ← Finset.sum_fiberwise_of_maps_to hmaps, trudiPartitionSum]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [Finset.sum_congr rfl (g := fun _ => s ^ (∑ i, α i) * ∏ i : Fin n, a ((i : ℕ) + 1) ^ α i)
      (fun c hc => by rw [(Finset.mem_filter.1 hc).2]),
    Finset.sum_const, card_compContent_fiber α (Finset.mem_filter.1 hα).2, nsmul_eq_mul]
  ring


/-- **Brioschi's formula: the case $a_0 = 1$ of Trudi's formula.** Let $R$ be a commutative ring
and let $a_0, a_1, a_2, \dots$ be elements of $R$ with $a_0 = 1$. For every $n \ge 0$, the
Toeplitz–Hessenberg determinant $\det A_n$ of size $n$ built from $a$ satisfies
$$\det A_n = (-1)^n \sum_\alpha (-1)^{|\alpha|} m_n(\alpha) a_1^{\alpha_1} \cdots a_n^{\alpha_n},$$
where the sum, Trudi's partition sum with weight $-1$ per part, runs over the tuples
$\alpha = (\alpha_1, \dots, \alpha_n)$ of nonnegative integers with
$\alpha_1 + 2\alpha_2 + \dots + n\alpha_n = n$, with $|\alpha| = \alpha_1 + \dots + \alpha_n$ and
$m_n(\alpha) = |\alpha|! / (\alpha_1! \cdots \alpha_n!)$.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Lemma 1 with
`a_0 = 1` (the sign `D_+`). -/
theorem toeplitzHessenbergDet_eq_neg_one_pow_mul_trudiPartitionSum {R : Type*} [CommRing R]
    (a : ℕ → R) (ha : a 0 = 1) (n : ℕ) :
    toeplitzHessenbergDet a n = (-1) ^ n * trudiPartitionSum (-1) a n := by
  rw [toeplitzHessenbergDet_eq_sum_compositions, trudiPartitionSum_eq_sum_compositions,
    Finset.mul_sum, ha]
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le c.length_le
  have hsq : ((-1 : R) ^ c.length) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; simp
  have hn : n - c.length = k := by omega
  rw [hn]
  have hpow : (-1 : R) ^ n = (-1) ^ c.length * (-1) ^ k := by rw [← pow_add, ← hk]
  rw [hpow]
  linear_combination (-(-1 : R) ^ k * ∏ r : Fin c.length, a (c.blocksFun r)) * hsq

/-- **Trudi's formula when $a_0 = -1$.** Let $R$ be a commutative ring and let
$a_0, a_1, a_2, \dots$ be elements of $R$ with $a_0 = -1$. For every $n \ge 0$, the
Toeplitz–Hessenberg determinant $\det A_n$ of size $n$ built from $a$ satisfies
$$\det A_n = \sum_\alpha m_n(\alpha) \, a_1^{\alpha_1} a_2^{\alpha_2} \cdots a_n^{\alpha_n},$$
where the sum, Trudi's partition sum with weight $1$ per part, runs over the tuples
$\alpha = (\alpha_1, \dots, \alpha_n)$ of nonnegative integers with
$\alpha_1 + 2\alpha_2 + \dots + n\alpha_n = n$, with $|\alpha| = \alpha_1 + \dots + \alpha_n$ and
$m_n(\alpha) = |\alpha|! / (\alpha_1! \cdots \alpha_n!)$.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Lemma 1 with
`a_0 = -1` (the sign `D_-`). -/
theorem toeplitzHessenbergDet_eq_trudiPartitionSum_one {R : Type*} [CommRing R] (a : ℕ → R)
    (ha : a 0 = -1) (n : ℕ) :
    toeplitzHessenbergDet a n = trudiPartitionSum 1 a n := by
  rw [toeplitzHessenbergDet_eq_sum_compositions, trudiPartitionSum_eq_sum_compositions, ha]
  simp

/-- **Two values of Trudi's partition sum.** For an integer $s$, integers $a_1, a_2, \dots$ and
$n \ge 0$, write
$T_n(s; a) = \sum_\alpha s^{|\alpha|} m_n(\alpha) \, a_1^{\alpha_1} \cdots a_n^{\alpha_n}$ for
Trudi's partition sum, where $\alpha = (\alpha_1, \dots, \alpha_n)$ runs over the tuples of
nonnegative integers with $\alpha_1 + 2\alpha_2 + \dots + n\alpha_n = n$, with
$|\alpha| = \alpha_1 + \dots + \alpha_n$ and
$m_n(\alpha) = |\alpha|! / (\alpha_1! \cdots \alpha_n!)$. Then $T_4(1; a) = 8$, the number of
compositions of $4$, when $a_i = 1$ for all $i$; and $T_3(-1; a) = -1 + 4 - 3 = 0$ when $a_i = i$
for all $i$.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Lemma 1. -/
theorem trudiPartitionSum_examples :
    trudiPartitionSum (1 : ℤ) (fun _ => 1) 4 = 8 ∧
      trudiPartitionSum (-1 : ℤ) (fun i => i) 3 = 0 := by
  decide

end

end MetaMathlibExt
