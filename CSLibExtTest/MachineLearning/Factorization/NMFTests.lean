/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Factorization.NMF
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
import Mathlib.Combinatorics.Pigeonhole

/-!
# Nonnegative matrix factorization tests

The reals are not computable, so the fixtures are checked by proof.

* A `1 × 1` Lee–Seung step: `X = 2`, `W = H = 1` moves `H` to `2` and the objective from `1` to
  `0`. With `W = 0` every denominator vanishes and the update returns `0` (Lean's `x / 0 = 0`),
  which leaves `W * H = 0` and the objective unchanged.
* Stationarity: `X = W = H = 1` is a fixed point of the sweep and a KKT point (non-vacuity of
  `IsKKTPoint`). `X = W = 1`, `H = 0` is a fixed point of the `H` update whose gradient `-2` is
  negative, so it is not a KKT point: fixed points with zero entries need not be stationary.
* Separability: the identity is separable (non-vacuity of `IsSeparable`); a monomial matrix with
  a monomial inverse is decoded by `exists_perm_of_mul_eq_one`; every nonnegative factorization of
  the `2 × 2` identity through `ℝ²` is a scaled permutation (`eq_of_isSeparable`).
* Nonnegative rank: the `4 × 4` cyclic matrix `C₄` with ones at `(i, i)` and `(i, i + 1)` has
  rank at most `3` (its rows satisfy `r₀ - r₁ + r₂ - r₃ = 0`) and nonnegative rank `4`: in a
  nonnegative factorization each one of `C₄` lies in the support rectangle of some rank-one term,
  a rectangle containing three of the eight ones would contain a zero of `C₄`, and eight ones in
  rectangles of at most two ones need four terms. A matrix with a negative entry has the junk
  nonnegative rank `0`.
* Applications: a two-signature catalog and a two-cell-type mixture.
-/

namespace Cslib.MachineLearning.NMF

open Matrix

/-! ### Lee–Seung updates -/

example : objective !![(2 : ℝ)] !![1] !![1] = 1 := by
  simp [objective]; norm_num

example : updateH !![(2 : ℝ)] !![1] !![1] = !![2] := by
  ext a j; fin_cases a; fin_cases j; simp [updateH, Matrix.mul_apply]

example : objective !![(2 : ℝ)] !![1] !![2] = 0 := by
  simp [objective]

/-- With `W = 0` every denominator `(Wᵀ W H) a j` is `0`, and the update returns `0`. -/
example (H : Matrix (Fin 2) (Fin 3) ℝ) (X : Matrix (Fin 1) (Fin 3) ℝ) :
    updateH X (0 : Matrix (Fin 1) (Fin 2) ℝ) H = 0 := by
  ext a j; simp [updateH]

example (X : Matrix (Fin 2) (Fin 3) ℝ) (W : Matrix (Fin 2) (Fin 4) ℝ)
    (H : Matrix (Fin 4) (Fin 3) ℝ) (hX : ∀ i j, 0 ≤ X i j) (hW : ∀ i a, 0 ≤ W i a)
    (hH : ∀ a j, 0 ≤ H a j) (t : ℕ) :
    objective X ((sweep X)^[t + 1] (W, H)).1 ((sweep X)^[t + 1] (W, H)).2 ≤
      objective X ((sweep X)^[t] (W, H)).1 ((sweep X)^[t] (W, H)).2 :=
  objective_sweep_iterate_antitone (p := (W, H)) hX hW hH (Nat.le_succ t)

example (X : Matrix (Fin 2) (Fin 3) ℝ) : ∃ W : Matrix (Fin 2) (Fin 1) ℝ,
    ∃ H : Matrix (Fin 1) (Fin 3) ℝ, (∀ i a, 0 ≤ W i a) ∧ (∀ a j, 0 ≤ H a j) ∧
      ∀ (W' : Matrix (Fin 2) (Fin 1) ℝ) (H' : Matrix (Fin 1) (Fin 3) ℝ),
        (∀ i a, 0 ≤ W' i a) → (∀ a j, 0 ≤ H' a j) → objective X W H ≤ objective X W' H' :=
  exists_minimizer X

/-! ### Stationarity -/

private lemma sweep_one :
    sweep !![(1 : ℝ)] (!![1], !![1]) = (!![1], !![1]) := by
  have hH : updateH !![(1 : ℝ)] !![1] !![1] = !![1] := by
    ext a j; fin_cases a; fin_cases j; simp [updateH, Matrix.mul_apply]
  simp only [sweep, hH, Prod.mk.injEq, and_true]
  ext i a; fin_cases i; fin_cases a; simp [updateW, Matrix.mul_apply]

/-- Non-vacuity of `IsKKTPoint`: `X = W = H = 1`. -/
example : IsKKTPoint !![(1 : ℝ)] !![1] !![1] :=
  (isKKTPoint_of_sweep_eq sweep_one (by simp) (by simp)).1

/-- `H = 0` is a fixed point of the `H` update for `X = W = 1` (the update is `0 * 1 / 0`). -/
example : updateH !![(1 : ℝ)] !![1] !![0] = !![0] := by
  ext a j; fin_cases a; fin_cases j; simp [updateH]

/-- At that fixed point the gradient is `-2 < 0`, so it is not a KKT point. -/
example : gradH !![(1 : ℝ)] !![1] !![0] 0 0 = -2 := by
  simp [gradH, Matrix.mul_apply]

example : ¬ IsKKTPoint !![(1 : ℝ)] !![1] !![0] := fun h => by
  have := h.gradH_nonneg 0 0
  simp [gradH, Matrix.mul_apply] at this
  norm_num at this

example : HasDerivAt (fun t : ℝ => objective !![(2 : ℝ)] !![1] (!![1] + Matrix.single 0 0 t))
    (gradH !![(2 : ℝ)] !![1] !![1] 0 0) 0 :=
  hasDerivAt_objective_H _ _ _ 0 0

/-! ### Separability -/

/-- Non-vacuity of `IsSeparable`: the identity matrix. -/
example : IsSeparable (1 : Matrix (Fin 3) (Fin 3) ℝ) := fun a =>
  ⟨a, 1, one_pos, fun b => by simp [Matrix.one_apply]⟩

/-- A column of a separable matrix may be any positive multiple of a unit vector. -/
example : IsSeparable !![(0 : ℝ), 2, 5; 3, 0, 1] := by
  intro a
  fin_cases a
  · exact ⟨1, 2, by norm_num, fun b => by fin_cases b <;> simp⟩
  · exact ⟨0, 3, by norm_num, fun b => by fin_cases b <;> simp⟩

example : ¬ IsSeparable !![(1 : ℝ), 1; 1, 1] := fun h => by
  obtain ⟨j, c, -, hj⟩ := h 0
  have := hj 1
  fin_cases j <;> simp at this

example : ∃ σ : Fin 2 ≃ Fin 2, ∃ d : Fin 2 → ℝ, (∀ b, 0 < d b) ∧
    ∀ a b, !![(0 : ℝ), 2; 3, 0] a b = if a = σ b then d b else 0 :=
  exists_perm_of_mul_eq_one (K := !![0, 1 / 3; 1 / 2, 0])
    (fun a b => by fin_cases a <;> fin_cases b <;> norm_num)
    (fun a b => by fin_cases a <;> fin_cases b <;> norm_num)
    (by ext a b; fin_cases a <;> fin_cases b <;> norm_num [Matrix.one_apply])

/-- Every nonnegative factorization `1 = W' * H'` of the `2 × 2` identity through `ℝ²` is a
permutation with positive scalings (`W = H = 1` are separable). -/
example (W' H' : Matrix (Fin 2) (Fin 2) ℝ) (hW' : ∀ i a, 0 ≤ W' i a) (hH' : ∀ a j, 0 ≤ H' a j)
    (h : 1 = W' * H') :
    ∃ σ : Fin 2 ≃ Fin 2, ∃ d : Fin 2 → ℝ, (∀ a, 0 < d a) ∧
      (∀ i a, W' i a = d a * (1 : Matrix (Fin 2) (Fin 2) ℝ) i (σ a)) ∧
      ∀ a j, H' a j = (d a)⁻¹ * (1 : Matrix (Fin 2) (Fin 2) ℝ) (σ a) j :=
  eq_of_isSeparable (Matrix.mul_one 1).symm h hW' hH'
    (by rw [transpose_one]; exact fun a => ⟨a, 1, one_pos, fun b => by simp [Matrix.one_apply]⟩)
    (fun a => ⟨a, 1, one_pos, fun b => by simp [Matrix.one_apply]⟩)

/-! ### Nonnegative rank: the cyclic `4 × 4` matrix -/

/-- The support pattern of `C₄`: ones at `(i, i)` and `(i, i + 1)` (indices mod 4). -/
private def pat (i j : Fin 4) : Bool := decide (j = i ∨ j = i + 1)

/-- The cyclic matrix `C₄`. -/
private noncomputable def C4 : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => if pat i j then 1 else 0

private lemma C4_nonneg (i j : Fin 4) : 0 ≤ C4 i j := by
  simp only [C4, of_apply]; split_ifs <;> norm_num

/-- `C₄` factors through `ℝ³` (`r₃ = r₀ - r₁ + r₂`), so its rank is at most `3`. -/
private lemma C4_eq_mul : C4 = !![(1 : ℝ), 0, 0; 0, 1, 0; 0, 0, 1; 1, -1, 1] *
    !![(1 : ℝ), 1, 0, 0; 0, 1, 1, 0; 0, 0, 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C4, pat, Matrix.mul_apply, Fin.sum_univ_three]

private lemma rank_C4_le : C4.rank ≤ 3 := by
  rw [C4_eq_mul]
  exact (rank_mul_le_left _ _).trans (rank_le_width _)

/-- Two distinct ones `e`, `f` of `C₄` whose all-ones rectangle `{e.1, f.1} × {e.2, f.2}` lies
in the support of `C₄`. -/
private def compat (e f : Fin 4 × Fin 4) : Bool :=
  pat e.1 e.2 && pat f.1 f.2 && pat e.1 f.2 && pat f.1 e.2 && decide (e ≠ f)

/-- No three ones of `C₄` are pairwise compatible. -/
private lemma no_three : ∀ e₁ e₂ e₃ : Fin 4 × Fin 4,
    (compat e₁ e₂ && compat e₁ e₃ && compat e₂ e₃) = false := by
  decide

private lemma card_support : (Finset.univ.filter fun e : Fin 4 × Fin 4 => pat e.1 e.2 = true).card
    = 8 := by
  decide

private lemma four_le_nonnegRank_C4 : 4 ≤ nonnegRank C4 := by
  by_contra hlt
  have hlt : nonnegRank C4 < 4 := by omega
  obtain ⟨W, H, hW, hH, hWH⟩ := exists_mul_eq_nonnegRank C4_nonneg
  have hent : ∀ i j, ∑ a, W i a * H a j = C4 i j := fun i j => by rw [← mul_apply, hWH]
  -- every one of `C₄` is covered by a positive term `W i a * H a j`
  have hcov : ∀ e : Fin 4 × Fin 4, pat e.1 e.2 = true → ∃ a, 0 < W e.1 a ∧ 0 < H a e.2 := by
    intro e he
    have h1 : ∑ a, W e.1 a * H a e.2 = 1 := by rw [hent]; simp [C4, he]
    by_contra hno
    simp only [not_exists, not_and, not_lt] at hno
    have : ∑ a, W e.1 a * H a e.2 ≤ 0 := Finset.sum_nonpos fun a _ => by
      rcases (hW e.1 a).lt_or_eq with hpos | hzero
      · nlinarith [hno a hpos, hH a e.2]
      · rw [← hzero, zero_mul]
    linarith
  -- a positive term `W i a * H a j'` forces a one of `C₄` at `(i, j')`
  have hrect : ∀ a i j', 0 < W i a → 0 < H a j' → pat i j' = true := by
    intro a i j' hWi hHj
    by_contra hp
    have h0 : ∑ b, W i b * H b j' = 0 := by rw [hent]; simp [C4, hp]
    have : W i a * H a j' ≤ ∑ b, W i b * H b j' :=
      Finset.single_le_sum (f := fun b => W i b * H b j')
        (fun b _ => mul_nonneg (hW i b) (hH b j')) (Finset.mem_univ a)
    nlinarith [mul_pos hWi hHj]
  classical
  let a₀ := (hcov (0, 0) (by decide)).choose
  let f : Fin 4 × Fin 4 → Fin (nonnegRank C4) := fun e =>
    if he : pat e.1 e.2 = true then (hcov e he).choose else a₀
  obtain ⟨a, -, ha⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := Finset.univ.filter fun e : Fin 4 × Fin 4 => pat e.1 e.2 = true)
    (t := (Finset.univ : Finset (Fin (nonnegRank C4)))) (f := f) (n := 2)
    (fun _ _ => Finset.mem_univ _)
    (by rw [card_support, Finset.card_univ, Fintype.card_fin]; omega)
  obtain ⟨e₁, he₁, e₂, he₂, e₃, he₃, h12, h13, h23⟩ := Finset.two_lt_card.mp ha
  have spec : ∀ e, e ∈ (Finset.univ.filter fun e : Fin 4 × Fin 4 => pat e.1 e.2 = true).filter
      (fun e => f e = a) → pat e.1 e.2 = true ∧ 0 < W e.1 a ∧ 0 < H a e.2 := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨hp, hfa⟩ := he
    have := (hcov e hp).choose_spec
    simp only [f, hp, dite_true] at hfa
    rw [← hfa]
    exact ⟨hp, this⟩
  obtain ⟨p1, w1, k1⟩ := spec e₁ he₁
  obtain ⟨p2, w2, k2⟩ := spec e₂ he₂
  obtain ⟨p3, w3, k3⟩ := spec e₃ he₃
  have c12 : compat e₁ e₂ = true := by
    simp [compat, p1, p2, hrect a _ _ w1 k2, hrect a _ _ w2 k1, h12]
  have c13 : compat e₁ e₃ = true := by
    simp [compat, p1, p3, hrect a _ _ w1 k3, hrect a _ _ w3 k1, h13]
  have c23 : compat e₂ e₃ = true := by
    simp [compat, p2, p3, hrect a _ _ w2 k3, hrect a _ _ w3 k2, h23]
  have := no_three e₁ e₂ e₃
  rw [c12, c13, c23] at this
  simp at this

/-- **The nonnegative rank of `C₄` is `4`.** -/
example : nonnegRank C4 = 4 :=
  le_antisymm ((nonnegRank_le_card_width C4_nonneg).trans_eq (Fintype.card_fin 4))
    four_le_nonnegRank_C4

/-- **Nonnegative rank can exceed rank**: `rank C₄ ≤ 3 < 4 = nonnegRank C₄`. -/
example : C4.rank < nonnegRank C4 :=
  lt_of_le_of_lt rank_C4_le (by have := four_le_nonnegRank_C4; omega)

example : C4.rank ≤ nonnegRank C4 := rank_le_nonnegRank C4_nonneg

/-- Junk value: a matrix with a negative entry has no nonnegative factorization, and its
`nonnegRank` is `sInf ∅ = 0`. -/
example : nonnegRank !![(-1 : ℝ)] = 0 := by
  refine Nat.sInf_eq_zero.mpr (Or.inr (Set.eq_empty_iff_forall_notMem.mpr ?_))
  rintro r ⟨W, H, hW, hH, hWH⟩
  have h := congrFun (congrFun hWH 0) 0
  have : 0 ≤ (W * H) 0 0 := by
    rw [mul_apply]; exact Finset.sum_nonneg fun a _ => mul_nonneg (hW 0 a) (hH a 0)
  simp at h
  linarith

/-! ### Applications -/

/-- Two signatures over two mutation types, each a probability vector; one sample with exposures
`3` and `4` has `7` mutations. -/
example : ∑ i, (!![(1 / 2 : ℝ), 1; 1 / 2, 0] * !![(3 : ℝ); 4]) i 0 = 7 := by
  rw [sum_mul_apply_of_sum_eq_one (fun a => by fin_cases a <;> norm_num [Fin.sum_univ_two])]
  simp; norm_num

/-- Two cell types expressing a gene at `2` and `6`, mixed `1/4 : 3/4`: the bulk level `5` lies
in `[2, 6]`. -/
example : (!![(2 : ℝ), 6] * !![(1 / 4 : ℝ); 3 / 4]) 0 0 ∈ Set.Icc 2 6 :=
  mul_apply_mem_Icc (fun a => by fin_cases a <;> norm_num)
    (by simp [Fin.sum_univ_two]; norm_num) (fun a => by fin_cases a <;> norm_num)

example : (!![(2 : ℝ), 6] * !![(1 / 4 : ℝ); 3 / 4]) 0 0 = 5 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]; norm_num

end Cslib.MachineLearning.NMF
