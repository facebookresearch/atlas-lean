/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.RootPowerSums
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Basic.Real.Basic

/-!
# Root-power-sum consumers and separating examples

These proofs are independently authored. The exact polynomial statement is
from anthropics/fermats-last-theorem at
6e837e75355538c7f80bab5b956861e86c4eacc2,
`Theorems/Thm_Polynomial_eq_of_forall_sum_roots_pow_eq.lean`, lines 7-12.
No source proof or source-specific definition is copied into these tests.
-/

public section

open Polynomial
open scoped BigOperators

namespace RootPowerSumsTest

universe u v

/-- The exact source statement, with a genuinely arbitrary universe. -/
theorem source_consumer {K : Type u} [Field K] [CharZero K]
    (P Q : Polynomial K) (hP : P.Monic) (hQ : Q.Monic)
    (hPs : P.Splits) (hQs : Q.Splits) (hdeg : P.natDegree = Q.natDegree)
    (h : ∀ n : ℕ, 0 < n →
      (P.roots.map (fun z => z ^ n)).sum =
        (Q.roots.map (fun z => z ^ n)).sum) : P = Q :=
  Polynomial.eq_of_forall_sum_roots_pow_eq P Q hP hQ hPs hQs hdeg h

/-- The source polynomial principle also reconstructs arbitrary multisets.
The premise is the principle being compared, not an application conclusion. -/
theorem multiset_of_polynomial_principle {K : Type u} [Field K] [CharZero K]
    (principle : ∀ (P Q : Polynomial K), P.Monic → Q.Monic →
      P.Splits → Q.Splits → P.natDegree = Q.natDegree →
      (∀ n : ℕ, 0 < n → (P.roots.map (fun z => z ^ n)).sum =
        (Q.roots.map (fun z => z ^ n)).sum) → P = Q)
    (s t : Multiset K) (hcard : s.card = t.card)
    (h : ∀ n : ℕ, 0 < n →
      (s.map (fun z => z ^ n)).sum = (t.map (fun z => z ^ n)).sum) :
    s = t := by
  have hp := principle (s.map (X - C ·)).prod (t.map (X - C ·)).prod
    (monic_multisetProd_X_sub_C s) (monic_multisetProd_X_sub_C t)
    (Splits.multisetProd (by simp)) (Splits.multisetProd (by simp))
    (by simpa using hcard) (by simpa using h)
  simpa using congrArg Polynomial.roots hp

/-- Power traces reconstruct the characteristic polynomial of a diagonal
matrix, without an arbitrary-matrix Newton theorem. -/
theorem diagonal_charpoly_eq {K : Type u} [Field K] [CharZero K]
    {ι : Type v} [Fintype ι] [DecidableEq ι] (a b : ι → K)
    (h : ∀ n : ℕ, 0 < n →
      Matrix.trace (Matrix.diagonal a ^ n) =
        Matrix.trace (Matrix.diagonal b ^ n)) :
    (Matrix.diagonal a).charpoly = (Matrix.diagonal b).charpoly := by
  have hm : Finset.univ.val.map a = Finset.univ.val.map b :=
    Multiset.eq_of_card_eq_of_forall_sum_pow_eq _ _ (by simp) (by
      intro n hn
      simpa only [Matrix.diagonal_pow, Matrix.trace_diagonal, Finset.sum,
        Multiset.map_map, Function.comp_def, Pi.pow_apply] using h n hn)
  simpa only [Matrix.charpoly_diagonal, Finset.prod, Multiset.map_map,
    Function.comp_def] using
    congrArg (fun s : Multiset K => (s.map (X - C ·)).prod) hm

/-- All powers agree for a permutation with zeros and a repeated value. -/
theorem rational_diagonal_traces (n : ℕ) :
    Matrix.trace (Matrix.diagonal ![0, 2, 2, (-1 : ℚ)] ^ n) =
      Matrix.trace (Matrix.diagonal ![-1, 2, 0, (2 : ℚ)] ^ n) := by
  simp only [Matrix.diagonal_pow, Matrix.trace_diagonal, Pi.pow_apply,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero]
  ring

/-- The equal characteristic polynomials are obtained through reconstruction. -/
theorem rational_diagonal_charpoly :
    (Matrix.diagonal ![0, 2, 2, (-1 : ℚ)]).charpoly =
      (Matrix.diagonal ![-1, 2, 0, (2 : ℚ)]).charpoly :=
  diagonal_charpoly_eq _ _ (fun n _ => rational_diagonal_traces n)

/-- Equal power traces do not recover the matrix itself. -/
theorem rational_diagonal_ne :
    Matrix.diagonal ![0, 2, 2, (-1 : ℚ)] ≠
      Matrix.diagonal ![-1, 2, 0, (2 : ℚ)] := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℚ => M 0 0) h
  norm_num [Matrix.diagonal_apply] at h00

/-- A finite counting distribution is recovered from its total mass and
positive moments. No matrix or characteristic-polynomial premise is used. -/
theorem counting_distribution_eq {K : Type u} [Field K] [CharZero K]
    (f g : K →₀ ℕ) (hmass : f.sum (fun _ k => k) = g.sum (fun _ k => k))
    (h : ∀ n : ℕ, 0 < n →
      f.sum (fun x k => (k : K) * x ^ n) =
        g.sum (fun x k => (k : K) * x ^ n)) : f = g := by
  classical
  have hm : f.toMultiset = g.toMultiset :=
    Multiset.eq_of_card_eq_of_forall_sum_pow_eq _ _
      (by simpa [Function.id_def] using hmass) (by
        intro n hn
        simpa only [Finset.sum_multiset_map_count,
          Finsupp.toFinset_toMultiset, Finsupp.count_toMultiset,
          nsmul_eq_mul, Finsupp.sum] using h n hn)
  simpa using congrArg Multiset.toFinsupp hm

/-- The repeated-point data satisfy the mass and every-moment assumptions. -/
theorem repeated_points_data :
    ({0, 0, 2, 2, (-1 : ℚ)} : Multiset ℚ).card = 5 ∧
      ∀ n : ℕ, 0 < n →
        (({0, 0, 2, 2, (-1 : ℚ)} : Multiset ℚ).map (fun x => x ^ n)).sum =
          2 * (2 : ℚ) ^ n + (-1 : ℚ) ^ n := by
  constructor
  · decide
  · intro n hn
    simp [zero_pow (Nat.ne_of_gt hn), two_mul, add_assoc]

/-- Reconstruction retains zero multiplicity and repeated nonzero points. -/
theorem repeated_points_recovered (s : Multiset ℚ) (hmass : s.card = 5)
    (h : ∀ n : ℕ, 0 < n →
      (s.map (fun x => x ^ n)).sum = 2 * (2 : ℚ) ^ n + (-1 : ℚ) ^ n) :
    s.count 0 = 2 ∧ s.count 2 = 2 ∧ s.count (-1) = 1 := by
  have hs : s = {0, 0, 2, 2, -1} :=
    Multiset.eq_of_card_eq_of_forall_sum_pow_eq _ _
      (hmass.trans repeated_points_data.1.symm)
      (fun n hn => (h n hn).trans (repeated_points_data.2 n hn).symm)
  rw [hs]
  norm_num

/-- Empty counting data are included, not excluded by nonemptiness. -/
theorem empty_distribution {K : Type u} [Field K] [CharZero K]
    (f : K →₀ ℕ) (hmass : f.sum (fun _ k => k) = 0)
    (h : ∀ n : ℕ, 0 < n → f.sum (fun x k => (k : K) * x ^ n) = 0) :
    f = 0 :=
  counting_distribution_eq f 0 (by simpa using hmass) (by simpa using h)

/-- Positive moments cannot see an extra zero point. -/
theorem cardinality_boundary :
    ({1} : Multiset ℚ).card ≠ ({0, 1} : Multiset ℚ).card ∧
      (∀ n : ℕ, 0 < n →
        (({1} : Multiset ℚ).map (fun x => x ^ n)).sum =
          (({0, 1} : Multiset ℚ).map (fun x => x ^ n)).sum) ∧
      ({1} : Multiset ℚ) ≠ {0, 1} := by
  refine ⟨by decide, ?_, by decide⟩
  intro n hn
  simp [zero_pow (Nat.ne_of_gt hn)]

/-- The corresponding split monic polynomials have unequal degrees. -/
theorem degree_boundary :
    let P : ℚ[X] := X - C 1
    let Q : ℚ[X] := X * (X - C 1)
    P.Monic ∧ Q.Monic ∧ P.Splits ∧ Q.Splits ∧
      P.natDegree ≠ Q.natDegree ∧
      (∀ n : ℕ, 0 < n → (P.roots.map (fun x => x ^ n)).sum =
        (Q.roots.map (fun x => x ^ n)).sum) ∧ P ≠ Q := by
  dsimp only
  have hne : (X * (X - C (1 : ℚ))) ≠ 0 :=
    mul_ne_zero X_ne_zero (X_sub_C_ne_zero 1)
  refine ⟨monic_X_sub_C _, monic_X.mul (monic_X_sub_C _),
    Splits.X_sub_C _, Splits.X.mul (Splits.X_sub_C _), ?_, ?_, ?_⟩
  · rw [natDegree_mul X_ne_zero (X_sub_C_ne_zero (1 : ℚ)),
      natDegree_X_sub_C, natDegree_X]
    decide
  · intro n hn
    rw [roots_mul hne, roots_X_sub_C, roots_X]
    simp [zero_pow (Nat.ne_of_gt hn)]
  · intro he
    have h0 := congrArg (fun p : ℚ[X] => p.eval 0) he
    norm_num at h0

/-- In characteristic two, even equal mass and every positive moment fail. -/
theorem characteristic_two_multisets :
    ({0, 0} : Multiset (ZMod 2)).card = ({1, 1} : Multiset (ZMod 2)).card ∧
      (∀ n : ℕ, 0 < n →
        (({0, 0} : Multiset (ZMod 2)).map (fun x => x ^ n)).sum =
          (({1, 1} : Multiset (ZMod 2)).map (fun x => x ^ n)).sum) ∧
      ({0, 0} : Multiset (ZMod 2)) ≠ {1, 1} := by
  refine ⟨rfl, ?_, by decide⟩
  intro n hn
  norm_num [zero_pow (Nat.ne_of_gt hn)]
  decide

/-- The characteristic-two counterexample also consists of split monic
polynomials of the same natural degree. -/
theorem characteristic_two_polynomials :
    let P : (ZMod 2)[X] := X ^ 2
    let Q : (ZMod 2)[X] := (X - C 1) ^ 2
    P.Monic ∧ Q.Monic ∧ P.Splits ∧ Q.Splits ∧
      P.natDegree = Q.natDegree ∧
      (∀ n : ℕ, 0 < n → (P.roots.map (fun x => x ^ n)).sum =
        (Q.roots.map (fun x => x ^ n)).sum) ∧ P ≠ Q := by
  dsimp only
  refine ⟨monic_X.pow _, (monic_X_sub_C _).pow _, Splits.X_pow _,
    (Splits.X_sub_C _).pow _, ?_, ?_, ?_⟩
  · rw [natDegree_pow, natDegree_pow, natDegree_X, natDegree_X_sub_C]
  · intro n hn
    rw [roots_X_pow, roots_pow, roots_X_sub_C, two_nsmul, two_nsmul]
    norm_num [zero_pow (Nat.ne_of_gt hn)]
    decide
  · intro he
    have h0 := congrArg (fun p : (ZMod 2)[X] => p.eval 0) he
    norm_num at h0

/-- Without monicity, scalar multiples have the same roots and moments. -/
theorem monicity_boundary :
    let P : ℚ[X] := X - C 1
    let Q : ℚ[X] := C 2 * (X - C 1)
    P.Monic ∧ ¬Q.Monic ∧ P.Splits ∧ Q.Splits ∧
      P.natDegree = Q.natDegree ∧ P.roots = Q.roots ∧
      (∀ n : ℕ, 0 < n → (P.roots.map (fun x => x ^ n)).sum =
        (Q.roots.map (fun x => x ^ n)).sum) ∧ P ≠ Q := by
  dsimp only
  have hroots : (X - C (1 : ℚ)).roots =
      (C (2 : ℚ) * (X - C 1)).roots := by
    rw [roots_C_mul _ (by norm_num : (2 : ℚ) ≠ 0)]
  refine ⟨monic_X_sub_C _, ?_, Splits.X_sub_C _,
    (Splits.X_sub_C _).C_mul _, ?_, hroots, ?_, ?_⟩
  · intro hm
    have hc := hm.leadingCoeff
    rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X_sub_C, mul_one] at hc
    norm_num at hc
  · rw [natDegree_C_mul (by norm_num : (2 : ℚ) ≠ 0)]
  · intro n _
    rw [hroots]
  · intro he
    have h0 := congrArg (fun p : ℚ[X] => p.eval 0) he
    norm_num at h0

/-- A positive constant added to a real square has no roots. -/
theorem real_quadratic_roots (c : ℝ) (hc : 0 < c) :
    (X ^ 2 + C c).roots = 0 := by
  apply Multiset.eq_zero_of_forall_notMem
  intro x hx
  have he := Polynomial.isRoot_of_mem_roots hx
  simp only [IsRoot, eval_add, eval_pow, eval_X, eval_C] at he
  nlinarith [sq_nonneg x]

/-- Nonsplit monic real quadratics can have identical empty root multisets. -/
theorem splitting_boundary :
    let P : ℝ[X] := X ^ 2 + C 1
    let Q : ℝ[X] := X ^ 2 + C 2
    P.Monic ∧ Q.Monic ∧ P.natDegree = Q.natDegree ∧
      P.roots = 0 ∧ Q.roots = 0 ∧ ¬P.Splits ∧ ¬Q.Splits ∧
      (∀ n : ℕ, 0 < n → (P.roots.map (fun x => x ^ n)).sum =
        (Q.roots.map (fun x => x ^ n)).sum) ∧ P ≠ Q := by
  dsimp only
  have h1 := real_quadratic_roots 1 (by norm_num)
  have h2 := real_quadratic_roots 2 (by norm_num)
  refine ⟨monic_X_pow_add_C _ (by decide),
    monic_X_pow_add_C _ (by decide), ?_, h1, h2, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_pow_add_C, natDegree_X_pow_add_C]
  · intro hs
    have hd := hs.natDegree_eq_card_roots
    rw [natDegree_X_pow_add_C, h1] at hd
    norm_num at hd
  · intro hs
    have hd := hs.natDegree_eq_card_roots
    rw [natDegree_X_pow_add_C, h2] at hd
    norm_num at hd
  · intro n _
    rw [h1, h2]
  · intro he
    have h0 := congrArg (fun p : ℝ[X] => p.eval 0) he
    norm_num at h0

/-- A single moment does not determine even a two-point multiset.
This makes no claim against a sufficiently long finite moment prefix. -/
theorem one_moment_boundary :
    let s : Multiset ℚ := {-1, 1}
    let t : Multiset ℚ := {-2, 2}
    s.card = t.card ∧
      (s.map (fun x => x ^ 1)).sum = (t.map (fun x => x ^ 1)).sum ∧
      (s.map (fun x => x ^ 2)).sum ≠ (t.map (fun x => x ^ 2)).sum ∧
      s ≠ t := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · decide

/-- The polynomial API includes the degree-zero split monic polynomial. -/
theorem degree_zero {K : Type u} [Field K] [CharZero K] :
    (1 : K[X]) = 1 :=
  Polynomial.eq_of_forall_sum_roots_pow_eq 1 1 monic_one monic_one
    Splits.one Splits.one rfl (by simp)

/-- The multiset API includes empty data. -/
theorem empty_multiset {K : Type u} [Field K] [CharZero K] :
    (0 : Multiset K) = 0 :=
  Multiset.eq_of_card_eq_of_forall_sum_pow_eq 0 0 rfl (by simp)

/-- The same repeated-point data give a natural-valued counting distribution. -/
theorem repeated_distribution_data :
    let f := ({0, 0, 2, 2, (-1 : ℚ)} : Multiset ℚ).toFinsupp
    f.sum (fun _ k => k) = 5 ∧ ∀ n : ℕ, 0 < n →
      f.sum (fun x k => (k : ℚ) * x ^ n) =
        2 * (2 : ℚ) ^ n + (-1 : ℚ) ^ n := by
  constructor
  · simpa only [Function.id_def] using
      (Multiset.toFinsupp_sum_eq ({0, 0, 2, 2, (-1 : ℚ)} : Multiset ℚ)).trans
        repeated_points_data.1
  · intro n hn
    simpa only [Finset.sum_multiset_map_count, Finsupp.sum,
      Multiset.toFinsupp_support, Multiset.toFinsupp_apply, nsmul_eq_mul] using
      repeated_points_data.2 n hn

/-- Recover the full finitely supported distribution from explicit moments. -/
theorem repeated_distribution_recovered (f : ℚ →₀ ℕ)
    (hmass : f.sum (fun _ k => k) = 5)
    (h : ∀ n : ℕ, 0 < n → f.sum (fun x k => (k : ℚ) * x ^ n) =
      2 * (2 : ℚ) ^ n + (-1 : ℚ) ^ n) :
    f = ({0, 0, 2, 2, (-1 : ℚ)} : Multiset ℚ).toFinsupp :=
  counting_distribution_eq _ _ (hmass.trans repeated_distribution_data.1.symm)
    (fun n hn => (h n hn).trans (repeated_distribution_data.2 n hn).symm)

end RootPowerSumsTest
