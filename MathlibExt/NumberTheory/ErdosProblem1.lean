/-
Copyright 2026 Tom Adamczewski / Epoch AI
Licensed under the Apache License, Version 2.0 (see LICENSE).

Adapted from `Erdos1/Resolutions/Erdos1_219usd_38h.lean`:
https://github.com/tadamcz/erdos1/blob/0e395153306f34b3829d118b85bdd704136f2843/Erdos1/Resolutions/Erdos1_219usd_38h.lean

The upstream NOTICE also credits the statement copied from Formal Conjectures
(`FormalConjectures/ErdosProblems/1.lean` at 488aade228ec37880b8fec178c173c07d279bb53,
https://github.com/google-deepmind/formal-conjectures), copyright 2025 The Formal Conjectures
Authors, licensed under the Apache License, Version 2.0. The formal statement was given to the
AI system by the FrontierMath Erdős benchmark of Tom Adamczewski and Thomas F. Bloom
(LeanOpenProblems, https://github.com/epoch-research/LeanOpenProblems, commit
77882c437ca1dfefab3b27fa00f1d29788100311), Epoch AI, MIT License. The Lean proofs were
produced by a pre-release version of GPT-6 Astra (OpenAI) running in that benchmark.

ATLAS modifications: narrowed imports, made the proof helpers module-private, and connected the
original proof to the existing ATLAS statement. Ported proof syntax and lemmas to the pinned
Lean and Mathlib versions.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 1

The conjecture that every sum-distinct subset of $\{1, \ldots, N\}$ satisfies
$N > C 2^{|A|}$ for some uniform positive constant $C$ is false.

The proof turns a putative uniform bound into a positive lower bound on determinants of
rational matrices satisfying an open-cube exclusion condition. Iterating an odd-cycle
construction and taking a suitable minor produces admissible matrices with arbitrarily
small determinants. See [Erdős Problem 1](https://www.erdosproblems.com/1).

Statement source record: `FC-ErdosProblem1`, ported from Formal Conjectures' `erdos_1`.
-/

namespace MathlibExt.NumberTheory.ErdosProblem1Wanted

@[expose] public section

abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective

def conjecture : Prop :=
  ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ) (_ : IsSumDistinctSet A N),
    N ≠ 0 → C * 2 ^ A.card < N

end

namespace ErdosCounter

open Filter
open scoped Topology Real

/-- The exact subset-sum injectivity property used in the specification. -/
def SumDistinct (A : Finset ℕ) : Prop :=
  (fun (s : A.powerset) => s.val.sum id).Injective

/-- The conjectural uniform estimate, split into its elementary hypotheses. -/
def UniformSubsetBound : Prop :=
  ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ),
    A ⊆ Finset.Icc 1 N → SumDistinct A →
    N ≠ 0 → C * 2 ^ A.card < N

/-- No bounded integer relation among an indexed family of natural weights. -/
def RelationFree {ι : Type*} [Fintype ι] (a : ι → ℕ) (Q : ℕ) : Prop :=
  ∀ c : ι → ℤ, (∀ i, |c i| < (Q : ℤ)) →
    (∑ i, (a i : ℤ) * c i) = 0 → c = 0

/-
# Binary blocks of a relation-free family

This module proves that the weights `a i * 2^j` have distinct subset sums when
`a` has no nonzero integer relation with coefficients of absolute value less
than `2^k`.
-/

/-- A signed binary sum with digits in `[-1,1]` has absolute value less than `2^k`. -/
private theorem binary_sum_abs_lt (k : ℕ) (e : Fin k → ℤ)
    (he : ∀ j, |e j| ≤ 1) :
    |∑ j, e j * (2 : ℤ) ^ j.val| < (2 : ℤ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsmall := ih (fun j => e j.castSucc) (fun j => he j.castSucc)
    have hp : 0 < (2 : ℤ) ^ k := by positivity
    have hlast : |e (Fin.last k) * (2 : ℤ) ^ k| ≤ (2 : ℤ) ^ k := by
      rw [abs_mul, abs_of_pos hp]
      simpa using mul_le_mul_of_nonneg_right (he (Fin.last k)) hp.le
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    calc
      |(∑ j : Fin k, e j.castSucc * (2 : ℤ) ^ j.val) +
          e (Fin.last k) * (2 : ℤ) ^ k| ≤
          |∑ j : Fin k, e j.castSucc * (2 : ℤ) ^ j.val| +
            |e (Fin.last k) * (2 : ℤ) ^ k| := abs_add_le _ _
      _ < (2 : ℤ) ^ k + (2 : ℤ) ^ k := add_lt_add_of_lt_of_le hsmall hlast
      _ = (2 : ℤ) ^ (k + 1) := by ring

/-- No nonzero signed binary digit vector in `[-1,1]` can have value zero. -/
private theorem binary_sum_eq_zero (k : ℕ) (e : Fin k → ℤ)
    (he : ∀ j, |e j| ≤ 1)
    (hs : (∑ j, e j * (2 : ℤ) ^ j.val) = 0) : e = 0 := by
  induction k with
  | zero => exact Subsingleton.elim _ _
  | succ k ih =>
    have hp : 0 < (2 : ℤ) ^ k := by positivity
    have hsmall := binary_sum_abs_lt k (fun j => e j.castSucc)
      (fun j => he j.castSucc)
    rw [Fin.sum_univ_castSucc] at hs
    simp only [Fin.val_castSucc, Fin.val_last] at hs
    have hneg : (∑ j : Fin k, e j.castSucc * (2 : ℤ) ^ j.val) =
        -(e (Fin.last k) * (2 : ℤ) ^ k) := by linarith
    have hlast : e (Fin.last k) = 0 := by
      rw [hneg, abs_neg, abs_mul, abs_of_pos hp] at hsmall
      have habs : |e (Fin.last k)| < 1 := by nlinarith
      have := abs_lt.mp habs
      omega
    have hrest : (fun j : Fin k => e j.castSucc) = 0 :=
      ih (fun j => e j.castSucc) (fun j => he j.castSucc) (by simpa [hlast] using hs)
    funext j
    change e j = 0
    exact Fin.lastCases hlast (fun j => congrFun hrest j) j

/-- Bounded-relation freeness separates all signed sums of the binary blocks. -/
private theorem binary_block_relation_zero {d k : ℕ} (a : Fin d → ℕ)
    (hf : RelationFree a (2 ^ k)) (e : Fin d × Fin k → ℤ)
    (he : ∀ p, |e p| ≤ 1)
    (hs : (∑ p, (a p.1 : ℤ) * (2 : ℤ) ^ p.2.val * e p) = 0) : e = 0 := by
  let c : Fin d → ℤ := fun i => ∑ j, e (i, j) * (2 : ℤ) ^ j.val
  have hc : c = 0 := by
    apply hf c
    · intro i
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        binary_sum_abs_lt k (fun j => e (i, j)) (fun j => he (i, j))
    · calc
        (∑ i, (a i : ℤ) * c i) =
            ∑ p, (a p.1 : ℤ) * (2 : ℤ) ^ p.2.val * e p := by
          simp only [c, Finset.mul_sum, Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = 0 := hs
  funext p
  have hci : (∑ j, e (p.1, j) * (2 : ℤ) ^ j.val) = 0 := congrFun hc p.1
  exact congrFun (binary_sum_eq_zero k (fun j => e (p.1, j))
    (fun j => he (p.1, j)) hci) p.2

/-- The subset sums are already injective on the indices of the binary blocks. -/
private theorem binary_block_sum_injective {d k : ℕ} (a : Fin d → ℕ)
    (hf : RelationFree a (2 ^ k)) :
    Function.Injective (fun s : Finset (Fin d × Fin k) =>
      ∑ p ∈ s, a p.1 * 2 ^ p.2.val) := by
  classical
  intro s t hst
  let e : Fin d × Fin k → ℤ := fun p =>
    (if p ∈ s then 1 else 0) - (if p ∈ t then 1 else 0)
  have he : ∀ p, |e p| ≤ 1 := by
    intro p
    dsimp [e]
    split_ifs <;> norm_num
  have hst' : (∑ p ∈ s, (a p.1 : ℤ) * (2 : ℤ) ^ p.2.val) =
      ∑ p ∈ t, (a p.1 : ℤ) * (2 : ℤ) ^ p.2.val := by
    exact_mod_cast hst
  have hs : (∑ p, (a p.1 : ℤ) * (2 : ℤ) ^ p.2.val * e p) = 0 := by
    simpa [e, mul_sub, mul_ite, Finset.sum_sub_distrib] using sub_eq_zero.mpr hst'
  have he0 := binary_block_relation_zero a hf e he hs
  ext p
  have hp : e p = 0 := congrFun he0 p
  by_cases hps : p ∈ s <;> by_cases hpt : p ∈ t <;> simp [e, hps, hpt] at hp ⊢

/-- Binary blocks from a bounded-relation-free family form a sum-distinct set. -/
theorem exists_binary_block_set (d k W : ℕ) (_hd : 0 < d) (hk : 0 < k)
    (a : Fin d → ℕ) (ha : ∀ i, 0 < a i) (hW : ∀ i, a i ≤ W)
    (hf : RelationFree a (2 ^ k)) :
    ∃ A : Finset ℕ, A.card = d * k ∧
      A ⊆ Finset.Icc 1 (2 ^ (k - 1) * W) ∧ SumDistinct A := by
  classical
  -- The argument in fact also permits an empty indexed family.
  clear _hd
  let w : Fin d × Fin k → ℕ := fun p => a p.1 * 2 ^ p.2.val
  have hsum : Function.Injective (fun s : Finset (Fin d × Fin k) => s.sum w) :=
    binary_block_sum_injective a hf
  have hw : Function.Injective w := by
    intro p q hpq
    have hsingle : ({p} : Finset (Fin d × Fin k)) = {q} :=
      hsum (by simpa using hpq)
    simpa using hsingle
  let A : Finset ℕ := Finset.univ.image w
  refine ⟨A, ?_, ?_, ?_⟩
  · simp [A, Finset.card_image_of_injective _ hw]
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_Icc.mpr
    change 1 ≤ a p.1 * 2 ^ p.2.val ∧ a p.1 * 2 ^ p.2.val ≤ 2 ^ (k - 1) * W
    constructor
    · exact Nat.succ_le_of_lt (Nat.mul_pos (ha p.1) (by positivity))
    · have hj : p.2.val ≤ k - 1 := by omega
      calc
        a p.1 * 2 ^ p.2.val ≤ W * 2 ^ (k - 1) :=
          Nat.mul_le_mul (hW p.1) (pow_le_pow_right' (by norm_num) hj)
        _ = 2 ^ (k - 1) * W := Nat.mul_comm _ _
  · intro s t hst
    obtain ⟨S, hS⟩ := Finset.subset_univ_image_iff.mp (Finset.mem_powerset.mp s.property)
    obtain ⟨T, hT⟩ := Finset.subset_univ_image_iff.mp (Finset.mem_powerset.mp t.property)
    have himage (U : Finset (Fin d × Fin k)) : (U.image w).sum id = U.sum w := by
      exact Finset.sum_image (fun p hp q hq hpq => hw hpq)
    have hST : S = T := hsum (by
      change S.sum w = T.sum w
      rw [← himage S, ← himage T, hS, hT]
      exact hst)
    apply Subtype.ext
    exact hS.symm.trans ((congrArg (Finset.image w) hST).trans hT)

/-
# Integer normal form used by the counterexample transfer

Only changes of integral bases are used here. In particular, no covolume
normalizations or choices of Haar measure enter the argument.
-/

open Matrix Module

/-- A nonsingular integral matrix has injective action on integral vectors. -/
theorem integer_mulVec_injective {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : A.det ≠ 0) : Function.Injective A.mulVec := by
  intro x y hxy
  have hz : A *ᵥ (x - y) = 0 := by simp [Matrix.mulVec_sub, hxy]
  have hzero : x - y = 0 := by
    by_contra hne
    exact hA (Matrix.exists_mulVec_eq_zero_iff.mp ⟨x - y, hne, hz⟩)
  exact sub_eq_zero.mp hzero

/-- Matrix form of the full-rank Smith normal form. The factors on the left
and right are integral changes of basis. No divisibility ordering is needed. -/
theorem integer_diagonalization {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : A.det ≠ 0) :
    ∃ (P W : Matrix (Fin n) (Fin n) ℤ) (s : Fin n → ℤ),
      IsUnit P.det ∧ IsUnit W.det ∧ (∀ i, s i ≠ 0) ∧
      A * W = P * Matrix.diagonal s := by
  classical
  let f := A.mulVecLin
  have hf : Function.Injective f := integer_mulVec_injective A hA
  let e := LinearEquiv.ofInjective f hf
  let b := Pi.basisFun ℤ (Fin n)
  obtain ⟨bM, s, bN, hs⟩ :=
    (LinearMap.range f).exists_smith_normal_form_of_rank_eq b
      (LinearMap.finrank_range_of_inj hf)
  let bW := bN.map e.symm
  let P := b.toMatrix bM
  let W := b.toMatrix bW
  have hP : IsUnit P.det := by
    let := b.invertibleToMatrix bM
    exact (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_of_invertible P)
  have hW : IsUnit W.det := by
    let := b.invertibleToMatrix bW
    exact (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_of_invertible W)
  refine ⟨P, W, s, hP, hW, ?_, ?_⟩
  · intro i hi
    have hz : bN i = 0 := by
      apply Subtype.ext
      simpa [hi] using hs i
    exact bN.ne_zero i hz
  · ext i j
    have he : f (bW j) = (bN j : Fin n → ℤ) := by
      exact LinearEquiv.ofInjective_symm_apply (f := f) (h := hf) (bN j)
    have hj := congrFun (he.trans (hs j)) i
    rw [Matrix.mul_diagonal]
    simpa [P, W, b, Matrix.mul_apply,
      Basis.toMatrix_apply, Pi.basisFun_repr, f, Matrix.mulVecLin_apply,
      Matrix.mulVec, dotProduct, mul_comm] using hj

/-- The product of the normal-form coefficients has the same absolute value
as the original integral determinant. -/
theorem diagonalization_abs_det {n : ℕ} {A P W : Matrix (Fin n) (Fin n) ℤ}
    {s : Fin n → ℤ} (hP : IsUnit P.det) (hW : IsUnit W.det)
    (h : A * W = P * Matrix.diagonal s) : |∏ i, s i| = |A.det| := by
  have hd := congrArg Matrix.det h
  simp only [Matrix.det_mul, Matrix.det_diagonal] at hd
  have hab := congrArg abs hd
  simpa [abs_mul, Int.isUnit_iff_abs_eq.mp hP, Int.isUnit_iff_abs_eq.mp hW] using hab.symm

/-- The signs of the normal-form entries can be absorbed into a change of basis. -/
theorem integer_positive_diagonalization {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : A.det ≠ 0) :
    ∃ (P W : Matrix (Fin n) (Fin n) ℤ) (s : Fin n → ℤ),
      IsUnit P.det ∧ IsUnit W.det ∧ (∀ i, 0 < s i) ∧
      A * W = P * Matrix.diagonal s := by
  classical
  obtain ⟨P, W, s, hP, hW, hs, h⟩ := integer_diagonalization A hA
  let T := Matrix.diagonal (fun i => (s i).sign)
  have hT : IsUnit T.det := by
    apply Int.isUnit_iff_abs_eq.mpr
    simp only [T, Matrix.det_diagonal, Finset.abs_prod]
    simp [Int.abs_sign_of_ne_zero, hs]
  refine ⟨P, W * T, fun i => |s i|, hP, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul]
    exact hW.mul hT
  · exact fun i => abs_pos.mpr (hs i)
  · dsimp only [T]
    rw [← Matrix.mul_assoc, h, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
    congr 2
    funext i
    simp

/-- A positive common denominator for any finite rational matrix. -/
theorem rational_matrix_integer_multiple {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) :
    ∃ (D : ℕ) (A : Matrix (Fin n) (Fin n) ℤ),
      0 < D ∧ ∀ i j, (A i j : ℚ) = (D : ℚ) * B i j := by
  classical
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (fun p : Fin n × Fin n => B p.1 p.2)
  have hd0 : (d : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d.property
  have hdpos : 0 < (d : ℤ) ^ 2 := sq_pos_of_ne_zero hd0
  choose a ha using hd
  refine ⟨((d : ℤ) ^ 2).toNat, fun i j => (d : ℤ) * a (i,j), ?_, ?_⟩
  · omega
  · intro i j
    have hc : (((d : ℤ) ^ 2).toNat : ℚ) = ((d : ℤ) : ℚ) ^ 2 := by
      exact_mod_cast Int.toNat_of_nonneg hdpos.le
    rw [Int.cast_mul, hc]
    have he : (a (i,j) : ℚ) = ((d : ℤ) : ℚ) * B i j := by
      simpa [Algebra.smul_def] using ha (i,j)
    rw [he]
    ring

/-- Determinant scaling after clearing denominators. -/
theorem rational_integer_multiple_det {n : ℕ} {B : Matrix (Fin n) (Fin n) ℚ}
    {D : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    (h : ∀ i j, (A i j : ℚ) = (D : ℚ) * B i j) :
    (A.det : ℚ) = (D : ℚ) ^ n * B.det := by
  have he : A.map (fun z => (z : ℚ)) = (D : ℚ) • B := by
    ext i j
    exact h i j
  rw [Int.cast_det, he, Matrix.det_smul, Fintype.card_fin]

/-
# Primitive perturbations of full-rank integral lattices

The bidiagonal chain has a primitive integral annihilator and a saturated
column span. These elementary facts are the arithmetic part of the transfer.
-/

open Matrix Finset Filter
open scoped Topology

/-- Prefix products, including the empty prefix. -/
def chainWeights : (n : ℕ) → (Fin n → ℤ) → Fin (n + 1) → ℤ
  | 0, _ => fun _ => 1
  | n + 1, q => Fin.cons 1 (fun i => q 0 * chainWeights n (fun j => q j.succ) i)

@[local simp] theorem chainWeights_zero (n : ℕ) (q : Fin n → ℤ) :
    chainWeights n q 0 = 1 := by
  cases n <;> simp [chainWeights]

@[local simp] theorem chainWeights_last (n : ℕ) (q : Fin n → ℤ) :
    chainWeights n q (Fin.last n) = ∏ j, q j := by
  induction n with
  | zero => simp [chainWeights]
  | succ n ih => simp [chainWeights, ih, Fin.prod_univ_succ]

/-- Consecutive prefix products satisfy the bidiagonal recurrence. -/
theorem chainWeights_succ (n : ℕ) (q : Fin n → ℤ) (i : Fin n) :
    chainWeights n q i.succ = q i * chainWeights n q i.castSucc := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [chainWeights]
    · simp only [chainWeights, Fin.castSucc_succ, Fin.cons_succ]
      rw [ih]
      ring

/-- Scaling the diagonal scales the `i`th prefix by the `i`th power. -/
theorem chainWeights_scale (n : ℕ) (s : Fin n → ℤ) (t : ℤ) (i : Fin (n + 1)) :
    chainWeights n (fun j => t * s j) i = t ^ i.val * chainWeights n s i := by
  induction n with
  | zero => simp [chainWeights, Fin.eq_zero i]
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [chainWeights]
    · simp only [chainWeights, Fin.cons_succ, Fin.val_succ, ih, pow_succ]
      ring

/-- A diagonal matrix with an extra zero row. -/
def topMatrix {n : ℕ} {R : Type*} [Zero R] (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + 1)) (Fin n) R :=
  Matrix.of (Fin.snoc (fun i j => A i j) (fun _ => 0))

/-- The shift with ones immediately below the diagonal. -/
def chainShift (n : ℕ) : Matrix (Fin (n + 1)) (Fin n) ℤ :=
  Matrix.of (Fin.cons (fun _ => 0) (fun i j => (1 : Matrix (Fin n) (Fin n) ℤ) i j))

/-- The bidiagonal primitive perturbation. -/
def chainMatrix {n : ℕ} (q : Fin n → ℤ) : Matrix (Fin (n + 1)) (Fin n) ℤ :=
  topMatrix (Matrix.diagonal q) - chainShift n

@[local simp] theorem topMatrix_mulVec {n : ℕ} {R : Type*} [NonUnitalNonAssocSemiring R]
    (A : Matrix (Fin n) (Fin n) R) (z : Fin n → R) :
    topMatrix A *ᵥ z = Fin.snoc (A *ᵥ z) 0 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [topMatrix, Matrix.mulVec, dotProduct]

@[local simp] theorem chainShift_mulVec (n : ℕ) (z : Fin n → ℤ) :
    chainShift n *ᵥ z = Fin.cons 0 z := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [chainShift, Matrix.mulVec, dotProduct, Matrix.one_apply]

@[local simp] theorem chainMatrix_mulVec {n : ℕ} (q z : Fin n → ℤ) :
    chainMatrix q *ᵥ z = Fin.snoc (fun i => q i * z i) 0 - Fin.cons 0 z := by
  simp [chainMatrix, Matrix.sub_mulVec, funext (Matrix.mulVec_diagonal q z)]

/-- Every column of the bidiagonal chain is killed by the prefix products. -/
theorem chainWeights_annihilate {n : ℕ} (q z : Fin n → ℤ) :
    dotProduct (chainWeights n q) (chainMatrix q *ᵥ z) = 0 := by
  rw [chainMatrix_mulVec, dotProduct_sub]
  have h₁ : dotProduct (chainWeights n q) (Fin.snoc (fun i => q i * z i) 0) =
      ∑ i, chainWeights n q i.castSucc * (q i * z i) := by
    simp [dotProduct, Fin.sum_univ_castSucc]
  have h₂ : dotProduct (chainWeights n q) (Fin.cons 0 z) =
      ∑ i, chainWeights n q i.succ * z i := by
    simp [dotProduct, Fin.sum_univ_succ]
  rw [h₁, h₂]
  apply sub_eq_zero.mpr
  apply Finset.sum_congr rfl
  intro i hi
  rw [chainWeights_succ]
  ring

/-- Off-diagonal entries of the extended diagonal vanish. -/
theorem topDiagonal_apply_ne {n : ℕ} (q : Fin n → ℤ) (i : Fin (n + 1))
    (j : Fin n) (hne : i ≠ j.castSucc) : topMatrix (Matrix.diagonal q) i j = 0 := by
  revert hne
  refine Fin.lastCases ?_ (fun k hk => ?_) i
  · simp [topMatrix]
  · have hkj : k ≠ j := fun h => hk (congrArg Fin.castSucc h)
    simp [topMatrix, hkj]

/-- Deleting the first row leaves an upper triangular matrix with diagonal `-1`. -/
theorem chainMatrix_tail_unit {n : ℕ} (q : Fin n → ℤ) :
    IsUnit (chainMatrix q |>.submatrix Fin.succ id).det := by
  classical
  let T := (chainMatrix q).submatrix Fin.succ id
  have htri : T.BlockTriangular id := by
    intro i j hij
    have hne : i.succ ≠ j.castSucc := by
      intro he
      have := congrArg Fin.val he
      simp at this
      simp only [id_eq] at hij
      omega
    have hijne : i ≠ j := ne_of_gt hij
    have htop := topDiagonal_apply_ne q i.succ j hne
    simp [T, chainMatrix, Matrix.sub_apply, chainShift, htop, hijne]
  have hdiag : ∀ i, T i i = -1 := by
    intro i
    have hne : i.succ ≠ i.castSucc := by
      intro he
      have := congrArg Fin.val he
      simp at this
    have htop := topDiagonal_apply_ne q i.succ i hne
    simp [T, chainMatrix, Matrix.sub_apply, chainShift, htop]
  change IsUnit T.det
  rw [Matrix.det_of_isUpperTriangular htri]
  simp_rw [hdiag]
  simpa using (isUnit_neg_one : IsUnit (-1 : ℤ)).pow n

/-- The column lattice of the chain is the *full* integral kernel of its
primitive annihilator, not merely a finite-index sublattice. -/
theorem chainMatrix_saturated {n : ℕ} (q : Fin n → ℤ) (c : Fin (n + 1) → ℤ)
    (hc : dotProduct (chainWeights n q) c = 0) :
    ∃ z : Fin n → ℤ, chainMatrix q *ᵥ z = c := by
  classical
  let T := (chainMatrix q).submatrix Fin.succ id
  have hT : IsUnit T.det := chainMatrix_tail_unit q
  let z := T⁻¹ *ᵥ (fun i => c i.succ)
  have hz : T *ᵥ z = fun i => c i.succ := by
    dsimp [z]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hT, Matrix.one_mulVec]
  have htail : ∀ i : Fin n, (chainMatrix q *ᵥ z) i.succ = c i.succ := by
    intro i
    exact congrFun hz i
  refine ⟨z, ?_⟩
  have hzero : (chainMatrix q *ᵥ z) 0 = c 0 := by
    have h := chainWeights_annihilate q z
    simp only [dotProduct, Fin.sum_univ_succ, chainWeights_zero, one_mul, htail] at h hc
    linarith
  funext i
  exact Fin.cases hzero htail i

/-- The zero-sum lift of a square matrix, obtained by appending minus its row sum. -/
def zeroSumLift {n : ℕ} {R : Type*} [AddCommGroup R]
    (A : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n + 1)) (Fin n) R :=
  Matrix.of (Fin.snoc (fun i j => A i j) (fun j => -∑ i, A i j))

/-- The integral shear whose last row is all ones. -/
def snfShear {n : ℕ} {R : Type*} [Zero R] [One R]
    (U : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of (Fin.snoc (fun i => Fin.snoc (U i) 0) (fun _ => 1))

/-- The inverse shear, when `P` is inverse to `U`. -/
def snfUnshear {n : ℕ} {R : Type*} [AddCommGroup R] [One R]
    (P : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of (Fin.snoc (fun i => Fin.snoc (P i) 0) (Fin.snoc (fun j => -∑ i, P i j) 1))

theorem zeroSumLift_mulVec {n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin n) (Fin n) R) (z : Fin n → R) :
    zeroSumLift A *ᵥ z = Fin.snoc (A *ᵥ z) (-∑ i, (A *ᵥ z) i) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [zeroSumLift, Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.snoc_last,
      neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
    exact congrArg Neg.neg (Finset.sum_comm)
  · simp [zeroSumLift, Matrix.mulVec, dotProduct]

theorem snfShear_mulVec {n : ℕ} {R : Type*} [CommRing R]
    (U : Matrix (Fin n) (Fin n) R) (c : Fin (n + 1) → R) :
    snfShear U *ᵥ c = Fin.snoc (U *ᵥ (fun i => c i.castSucc)) (∑ i, c i) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [snfShear, Matrix.mulVec, dotProduct]
  · simp [snfShear, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]

theorem snfUnshear_mulVec {n : ℕ} {R : Type*} [CommRing R]
    (P : Matrix (Fin n) (Fin n) R) (c : Fin (n + 1) → R) :
    snfUnshear P *ᵥ c = Fin.snoc (P *ᵥ (fun i => c i.castSucc))
      (c (Fin.last n) - ∑ i, (P *ᵥ (fun i => c i.castSucc)) i) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [snfUnshear, Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.snoc_last,
      Fin.sum_univ_castSucc, Fin.snoc_castSucc, one_mul, neg_mul,
      Finset.sum_neg_distrib, Finset.sum_mul]
    rw [Finset.sum_comm]
    ring
  · simp [snfUnshear, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]

/-- The shear and unshear are inverse integral transformations. -/
theorem snfUnshear_mul_snfShear {n : ℕ} {R : Type*} [CommRing R]
    (P U : Matrix (Fin n) (Fin n) R) (h : P * U = 1) :
    snfUnshear P * snfShear U = 1 := by
  apply Matrix.mulVec_injective
  funext c
  rw [← Matrix.mulVec_mulVec, snfShear_mulVec, snfUnshear_mulVec]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Matrix.mulVec_mulVec, h,
    Matrix.one_mulVec]
  have hsum : (∑ i, c i) - ∑ i : Fin n, c i.castSucc = c (Fin.last n) := by
    rw [Fin.sum_univ_castSucc]
    ring
  rw [hsum]
  funext i
  exact Fin.lastCases (by simp) (fun j => by simp) i

/-- The unshear sends a zero-extended matrix to the corresponding zero-sum lift. -/
theorem snfUnshear_mul_topMatrix {n : ℕ} {R : Type*} [CommRing R]
    (P A : Matrix (Fin n) (Fin n) R) :
    snfUnshear P * topMatrix A = zeroSumLift (P * A) := by
  apply Matrix.mulVec_injective
  funext z
  rw [← Matrix.mulVec_mulVec, topMatrix_mulVec, snfUnshear_mulVec,
    zeroSumLift_mulVec]
  simp [Matrix.mulVec_mulVec]

/-- Explicit weights of the primitive perturbed relation. -/
def transferWeights {n : ℕ} (U : Matrix (Fin n) (Fin n) ℤ)
    (s : Fin n → ℤ) (t : ℤ) : Fin (n + 1) → ℤ :=
  (snfShear U).transpose *ᵥ chainWeights n (fun i => t * s i)

theorem transferWeights_castSucc {n : ℕ} (U : Matrix (Fin n) (Fin n) ℤ)
    (s : Fin n → ℤ) (t : ℤ) (i : Fin n) :
    transferWeights U s t i.castSucc =
      (∑ j, U j i * chainWeights n (fun j => t * s j) j.castSucc) +
        chainWeights n (fun j => t * s j) (Fin.last n) := by
  simp [transferWeights, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    snfShear, Fin.sum_univ_castSucc]

theorem transferWeights_last {n : ℕ} (U : Matrix (Fin n) (Fin n) ℤ)
    (s : Fin n → ℤ) (t : ℤ) :
    transferWeights U s t (Fin.last n) =
      chainWeights n (fun j => t * s j) (Fin.last n) := by
  simp [transferWeights, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    snfShear, Fin.sum_univ_castSucc]

/-- Saturation is preserved by the integral shear. -/
theorem transferWeights_saturated {n : ℕ} (P U : Matrix (Fin n) (Fin n) ℤ)
    (hPU : P * U = 1) (s : Fin n → ℤ) (t : ℤ) (c : Fin (n + 1) → ℤ)
    (hc : dotProduct (transferWeights U s t) c = 0) :
    ∃ z : Fin n → ℤ, (snfUnshear P * chainMatrix (fun i => t * s i)) *ᵥ z = c := by
  have hrel : dotProduct (chainWeights n (fun i => t * s i)) (snfShear U *ᵥ c) = 0 := by
    simpa [transferWeights, Matrix.mulVec_transpose, Matrix.dotProduct_mulVec] using hc
  obtain ⟨z, hz⟩ := chainMatrix_saturated _ _ hrel
  refine ⟨z, ?_⟩
  rw [← Matrix.mulVec_mulVec, hz, Matrix.mulVec_mulVec, snfUnshear_mul_snfShear P U hPU,
    Matrix.one_mulVec]

/-- The perturbation is affine in the scaling parameter, with a fixed integral error. -/
theorem transferMatrix_affine {n : ℕ} (P A W : Matrix (Fin n) (Fin n) ℤ)
    (s : Fin n → ℤ) (h : A * W = P * Matrix.diagonal s) (t : ℤ) :
    snfUnshear P * chainMatrix (fun i => t * s i) =
      t • zeroSumLift (A * W) - snfUnshear P * chainShift n := by
  have htop : topMatrix (Matrix.diagonal (fun i => t * s i)) =
      t • topMatrix (Matrix.diagonal s) := by
    ext i j
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp [topMatrix]
    · by_cases hkj : k = j <;> simp [topMatrix, Matrix.diagonal, hkj]
  rw [chainMatrix, Matrix.mul_sub, htop, Matrix.mul_smul,
    snfUnshear_mul_topMatrix, ← h]

/-- Any fixed error matrix is bounded relative to an invertible square block.
The constant may depend on the block and the dimension; it is an additive
buffer, rather than a multiplicative loss in the final estimate. -/
theorem exists_perturbation_buffer {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ)
    (hF : F.det ≠ 0) (E : Matrix (Fin (n + 1)) (Fin n) ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : Fin n → ℝ,
      ‖E *ᵥ z‖ ≤ K * ‖zeroSumLift F *ᵥ z‖ := by
  let L : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
    LinearMap.toContinuousLinearMap (E * F⁻¹).mulVecLin
  refine ⟨‖L‖, norm_nonneg _, ?_⟩
  intro z
  have hunit : IsUnit F.det := isUnit_iff_ne_zero.mpr hF
  have hL : L (F *ᵥ z) = E *ᵥ z := by
    change (E * F⁻¹) *ᵥ (F *ᵥ z) = E *ᵥ z
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit,
      Matrix.mul_one]
  have hproj : ‖F *ᵥ z‖ ≤ ‖zeroSumLift F *ᵥ z‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    have h := norm_le_pi_norm (zeroSumLift F *ᵥ z) i.castSucc
    simpa [zeroSumLift_mulVec] using h
  calc
    ‖E *ᵥ z‖ = ‖L (F *ᵥ z)‖ := congrArg norm hL.symm
    _ ≤ ‖L‖ * ‖F *ᵥ z‖ := L.le_opNorm _
    _ ≤ ‖L‖ * ‖zeroSumLift F *ᵥ z‖ := mul_le_mul_of_nonneg_left hproj (norm_nonneg _)

/-- The additive-buffer estimate for a fixed perturbation. -/
theorem perturbation_norm_lower {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ)
    (E : Matrix (Fin (n + 1)) (Fin n) ℝ) {K : ℝ}
    (hK : ∀ z : Fin n → ℝ, ‖E *ᵥ z‖ ≤ K * ‖zeroSumLift F *ᵥ z‖)
    (u : ℝ) (hu : 0 ≤ u) (z : Fin n → ℝ) :
    (u - K) * ‖zeroSumLift F *ᵥ z‖ ≤ ‖(u • zeroSumLift F - E) *ᵥ z‖ := by
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec]
  have hn : ‖u • (zeroSumLift F *ᵥ z)‖ = u * ‖zeroSumLift F *ᵥ z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hu]
  calc
    (u - K) * ‖zeroSumLift F *ᵥ z‖ =
        ‖u • (zeroSumLift F *ᵥ z)‖ - K * ‖zeroSumLift F *ᵥ z‖ := by rw [hn]; ring
    _ ≤ ‖u • (zeroSumLift F *ᵥ z)‖ - ‖E *ᵥ z‖ := sub_le_sub_left (hK z) _
    _ ≤ ‖u • (zeroSumLift F *ᵥ z) - E *ᵥ z‖ := norm_sub_norm_le _ _

/-- Integral scaling just above the desired binary scale and its fixed buffer. -/
noncomputable def binaryScale (D : ℕ) (K : ℝ) (k : ℕ) : ℤ :=
  (⌈((2 : ℝ) ^ k + K) / (D : ℝ)⌉₊ : ℤ)

theorem binaryScale_nonneg (D : ℕ) (K : ℝ) (k : ℕ) : 0 ≤ binaryScale D K k := by
  simp [binaryScale]

/-- Rounding costs at most one denominator unit, regardless of dimension. -/
theorem binaryScale_buffer {D : ℕ} (hD : 0 < D) (K : ℝ) (k : ℕ) :
    (2 : ℝ) ^ k + K ≤ (D : ℝ) * (binaryScale D K k : ℝ) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have h := Nat.le_ceil (((2 : ℝ) ^ k + K) / (D : ℝ))
  have h' := (div_le_iff₀ hD').mp h
  simpa [binaryScale, mul_comm] using h'

/-- The relative rounding error tends to zero along powers of two. -/
theorem binaryScale_limit {D : ℕ} (hD : 0 < D) {K : ℝ} (hK : 0 ≤ K) :
    Tendsto (fun k => (binaryScale D K k : ℝ) / (2 : ℝ) ^ k)
      atTop (𝓝 (1 / (D : ℝ))) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hpow : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hu : Tendsto (fun k : ℕ => 1 / (D : ℝ) + (K / (D : ℝ) + 1) / (2 : ℝ) ^ k)
      atTop (𝓝 (1 / (D : ℝ))) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hpow)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · intro k
    have hp : (0 : ℝ) < 2 ^ k := by positivity
    have hb := binaryScale_buffer hD K k
    apply (le_div_iff₀ hp).mpr
    have hh : (2 : ℝ) ^ k / D ≤ (binaryScale D K k : ℝ) :=
      (div_le_iff₀ hD').mpr (by nlinarith)
    convert hh using 1; ring
  · intro k
    have hp : (0 : ℝ) < 2 ^ k := by positivity
    have hc := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (2 ^ k + K) / D by positivity)
    have hceil : (binaryScale D K k : ℝ) < (2 ^ k + K) / D + 1 := by
      simpa [binaryScale] using hc
    apply (div_le_iff₀ hp).mpr
    have he : (1 / (D : ℝ) + (K / (D : ℝ) + 1) / 2 ^ k) * 2 ^ k =
        (2 ^ k + K) / D + 1 := by field_simp; ring
    rw [he]
    exact hceil.le

/-- Lower powers of a scale asymptotic to `l * 2^k` disappear after normalization. -/
theorem binaryScale_lower_power_limit (t : ℕ → ℤ) (l : ℝ)
    (ht : Tendsto (fun k => (t k : ℝ) / (2 : ℝ) ^ k) atTop (𝓝 l))
    {p n : ℕ} (hpn : p < n) :
    Tendsto (fun k => (t k : ℝ) ^ p / ((2 : ℝ) ^ k) ^ n) atTop (𝓝 0) := by
  have hpow : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hz := (tendsto_pow_div_pow_atTop_zero (𝕜 := ℝ) hpn).comp hpow
  have hh := (ht.pow p).mul hz
  simp only [mul_zero] at hh
  convert hh using 1
  funext k
  dsimp
  rw [div_pow]
  field_simp

/-- Every transferred weight has exactly the same leading coefficient. -/
theorem transferWeights_limit {n : ℕ} (U : Matrix (Fin n) (Fin n) ℤ)
    (s : Fin n → ℤ) (t : ℕ → ℤ) (l : ℝ)
    (ht : Tendsto (fun k => (t k : ℝ) / (2 : ℝ) ^ k) atTop (𝓝 l))
    (i : Fin (n + 1)) :
    Tendsto (fun k => (transferWeights U s (t k) i : ℝ) / ((2 : ℝ) ^ k) ^ n)
      atTop (𝓝 (l ^ n * (∏ j, s j : ℤ))) := by
  have hlast : Tendsto
      (fun k => (chainWeights n (fun j => t k * s j) (Fin.last n) : ℝ) /
        ((2 : ℝ) ^ k) ^ n) atTop (𝓝 (l ^ n * (∏ j, s j : ℤ))) := by
    convert (ht.pow n).mul_const ((∏ j, s j : ℤ) : ℝ) using 1
    funext k
    rw [chainWeights_scale, chainWeights_last]
    simp only [Int.cast_mul, Int.cast_pow, Fin.val_last, div_pow]
    ring
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simpa only [transferWeights_last] using hlast
  · have hlow (j : Fin n) : Tendsto
        (fun k => (U j i : ℝ) *
          (chainWeights n (fun j => t k * s j) j.castSucc : ℝ) / ((2 : ℝ) ^ k) ^ n)
        atTop (𝓝 0) := by
      have h := (binaryScale_lower_power_limit t l ht j.isLt).const_mul
        ((U j i : ℝ) * (chainWeights n s j.castSucc : ℝ))
      simp only [mul_zero] at h
      convert h using 1
      funext k
      rw [chainWeights_scale]
      simp only [Int.cast_mul, Int.cast_pow, Fin.val_castSucc]
      ring
    have hsum := tendsto_finsetSum Finset.univ (fun j _ => hlow j)
    have htot := hsum.add hlast
    simp only [Finset.sum_const_zero, zero_add] at htot
    convert htot using 1
    funext k
    rw [transferWeights_castSucc]
    simp only [Int.cast_add, Int.cast_sum, Int.cast_mul, add_div, Finset.sum_div]

/-- Zero-sum lifting commutes with a change of column basis. -/
theorem zeroSumLift_mul {n : ℕ} {R : Type*} [CommRing R]
    (A W : Matrix (Fin n) (Fin n) R) :
    zeroSumLift (A * W) = zeroSumLift A * W := by
  apply Matrix.mulVec_injective
  funext z
  rw [← Matrix.mulVec_mulVec, zeroSumLift_mulVec, zeroSumLift_mulVec,
    Matrix.mulVec_mulVec]

/-- Zero-sum lifting commutes with scalar multiplication. -/
theorem zeroSumLift_smul {n : ℕ} {R : Type*} [CommRing R]
    (u : R) (A : Matrix (Fin n) (Fin n) R) :
    zeroSumLift (u • A) = u • zeroSumLift A := by
  ext i j
  refine Fin.lastCases ?_ (fun k => ?_) i <;>
    simp [zeroSumLift, Finset.mul_sum]

/-- Zero-sum lifting commutes with ring maps. -/
theorem zeroSumLift_map {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A : Matrix (Fin n) (Fin n) R) :
    (zeroSumLift A).map f = zeroSumLift (A.map f) := by
  ext i j
  refine Fin.lastCases ?_ (fun k => ?_) i <;> simp [zeroSumLift]

/-- A saturated integer kernel inherits a relation gap from its admissible
leading matrix and an additive perturbation buffer. -/
theorem integer_kernel_no_small_relation {n : ℕ}
    (a : Fin (n + 1) → ℤ) (M : Matrix (Fin (n + 1)) (Fin n) ℤ)
    (hsat : ∀ c : Fin (n + 1) → ℤ, dotProduct a c = 0 → ∃ z, M *ᵥ z = c)
    (F : Matrix (Fin n) (Fin n) ℝ) (E : Matrix (Fin (n + 1)) (Fin n) ℝ)
    (hadm : ∀ z : Fin n → ℤ,
      ‖zeroSumLift F *ᵥ (fun i => (z i : ℝ))‖ < 1 → z = 0)
    (K u : ℝ) (hu : 0 ≤ u)
    (hK : ∀ z : Fin n → ℝ, ‖E *ᵥ z‖ ≤ K * ‖zeroSumLift F *ᵥ z‖)
    (hM : M.map (Int.castRingHom ℝ) = u • zeroSumLift F - E)
    (Q : ℕ) (hQ : 0 < Q) (hscale : (Q : ℝ) + K ≤ u) :
    ∀ c : Fin (n + 1) → ℤ, (∀ i, |c i| < (Q : ℤ)) →
      dotProduct a c = 0 → c = 0 := by
  intro c hc hrel
  obtain ⟨z, hz⟩ := hsat c hrel
  have hcR : ‖(fun i => (c i : ℝ))‖ < (Q : ℝ) := by
    apply (pi_norm_lt_iff (by exact_mod_cast hQ)).mpr
    intro i
    rw [Real.norm_eq_abs]
    exact_mod_cast hc i
  have hcast : (u • zeroSumLift F - E) *ᵥ (fun i => (z i : ℝ)) =
      (fun i => (c i : ℝ)) := by
    rw [← hM]
    funext i
    have hh := (Int.castRingHom ℝ).map_mulVec M z i
    simpa only [Int.coe_castRingHom, Function.comp_def, hz] using hh.symm
  have hlow := perturbation_norm_lower F E hK u hu (fun i => (z i : ℝ))
  rw [hcast] at hlow
  have hgap : (Q : ℝ) * ‖zeroSumLift F *ᵥ (fun i => (z i : ℝ))‖ < (Q : ℝ) := by
    calc
      (Q : ℝ) * ‖zeroSumLift F *ᵥ (fun i => (z i : ℝ))‖ ≤
          (u - K) * ‖zeroSumLift F *ᵥ (fun i => (z i : ℝ))‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ ≤ ‖(fun i => (c i : ℝ))‖ := hlow
      _ < (Q : ℝ) := hcR
  have hzsmall : ‖zeroSumLift F *ᵥ (fun i => (z i : ℝ))‖ < 1 := by
    nlinarith [show (0 : ℝ) < Q by exact_mod_cast hQ]
  have hz0 := hadm z hzsmall
  simpa [hz0] using hz.symm

/-
# Generic transfer from subset sums to admissible rational determinants

The input is the elementary open-cube admissibility condition on the zero-sum
lift of a rational matrix. The proof uses integral changes of basis, saturated
bidiagonal perturbations, and binary blocks. No covolume definitions are used.
-/

open Matrix Finset Filter
open scoped Topology

/-- The zero-sum lift of `B` has no nonzero integral vector in the open cube. -/
def CubeAdmissible {r : ℕ} (B : Matrix (Fin r) (Fin r) ℚ) : Prop :=
  ∀ z : Fin r → ℤ,
    (∀ i : Fin r, |∑ j, B i j * (z j : ℚ)| < 1) →
    |∑ i, ∑ j, B i j * (z j : ℚ)| < 1 → z = 0

/-- The coordinate and sup-norm formulations of cube admissibility agree. -/
theorem cubeAdmissible_iff_norm {r : ℕ} (B : Matrix (Fin r) (Fin r) ℚ) :
    CubeAdmissible B ↔ ∀ z : Fin r → ℤ,
      ‖zeroSumLift (B.map (fun q => (q : ℝ))) *ᵥ (fun i => (z i : ℝ))‖ < 1 → z = 0 := by
  constructor
  · intro h z hz
    have hc := (pi_norm_lt_iff (show (0 : ℝ) < 1 by norm_num)).mp hz
    apply h z
    · intro i
      have hi := hc i.castSucc
      rw [zeroSumLift_mulVec] at hi
      simp only [Fin.snoc_castSucc, Real.norm_eq_abs,
        Matrix.mulVec, dotProduct, Matrix.map_apply] at hi
      exact_mod_cast hi
    · have hi := hc (Fin.last r)
      rw [zeroSumLift_mulVec] at hi
      simp only [Fin.snoc_last, Real.norm_eq_abs, abs_neg,
        Matrix.mulVec, dotProduct, Matrix.map_apply] at hi
      exact_mod_cast hi
  · intro h z hz hsum
    apply h z
    apply (pi_norm_lt_iff (show (0 : ℝ) < 1 by norm_num)).mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [zeroSumLift_mulVec]
      simp only [Fin.snoc_last, Real.norm_eq_abs, abs_neg,
        Matrix.mulVec, dotProduct, Matrix.map_apply]
      exact_mod_cast hsum
    · rw [zeroSumLift_mulVec]
      simp only [Fin.snoc_castSucc, Real.norm_eq_abs,
        Matrix.mulVec, dotProduct, Matrix.map_apply]
      exact_mod_cast hz j

/-- Integral changes of column basis preserve the cube gap. -/
theorem cubeAdmissible_integral_basis {r : ℕ} {B : Matrix (Fin r) (Fin r) ℚ}
    (hB : CubeAdmissible B) (W : Matrix (Fin r) (Fin r) ℤ) (hW : IsUnit W.det) :
    ∀ z : Fin r → ℤ,
      ‖zeroSumLift (B.map (fun q => (q : ℝ)) * W.map (Int.castRingHom ℝ)) *ᵥ
        (fun i => (z i : ℝ))‖ < 1 → z = 0 := by
  intro z hz
  have hcast : W.map (Int.castRingHom ℝ) *ᵥ (fun i => (z i : ℝ)) =
      fun i => ((W *ᵥ z) i : ℝ) := by
    funext i
    exact ((Int.castRingHom ℝ).map_mulVec W z i).symm
  rw [zeroSumLift_mul, ← Matrix.mulVec_mulVec, hcast] at hz
  have hw0 := (cubeAdmissible_iff_norm B).mp hB (W *ᵥ z) hz
  apply integer_mulVec_injective W hW.ne_zero
  simpa using hw0

/-- Integer-valued version of the relation gap, before eventual positivity is used. -/
def IntegerRelationFree {ι : Type*} [Fintype ι] (a : ι → ℤ) (Q : ℕ) : Prop :=
  ∀ c : ι → ℤ, (∀ i, |c i| < (Q : ℤ)) → (∑ i, a i * c i) = 0 → c = 0

/-- Every nonsingular cube-admissible rational matrix yields primitive integer
weight families with a binary relation gap and determinant leading coefficient. -/
theorem exists_integer_transfer_family {r : ℕ} (B : Matrix (Fin r) (Fin r) ℚ)
    (hB : B.det ≠ 0) (hadm : CubeAdmissible B) :
    ∃ a : ℕ → Fin (r + 1) → ℤ,
      (∀ k, IntegerRelationFree (a k) (2 ^ k)) ∧
      ∀ i, Tendsto (fun k => (a k i : ℝ) / ((2 : ℝ) ^ k) ^ r)
        atTop (𝓝 |(B.det : ℝ)|) := by
  classical
  obtain ⟨D, A, hD, hA⟩ := rational_matrix_integer_multiple B
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hAD := rational_integer_multiple_det hA
  have hA0 : A.det ≠ 0 := by
    have h : (A.det : ℚ) ≠ 0 := by
      rw [hAD]
      exact mul_ne_zero (pow_ne_zero _ hDq) hB
    exact_mod_cast h
  obtain ⟨P, W, s, hP, hW, hs, hdiag⟩ := integer_positive_diagonalization A hA0
  let U := P⁻¹
  have hPU : P * U = 1 := Matrix.mul_nonsing_inv P hP
  let F := B.map (fun q => (q : ℝ)) * W.map (Int.castRingHom ℝ)
  let E := (snfUnshear P * chainShift r).map (Int.castRingHom ℝ)
  have hF : F.det ≠ 0 := by
    dsimp [F]
    rw [Matrix.det_mul, ← Rat.cast_det, ← Int.cast_det]
    apply mul_ne_zero
    · exact_mod_cast hB
    · exact_mod_cast hW.ne_zero
  have hadmF : ∀ z : Fin r → ℤ,
      ‖zeroSumLift F *ᵥ (fun i => (z i : ℝ))‖ < 1 → z = 0 :=
    cubeAdmissible_integral_basis hadm W hW
  obtain ⟨K, hK0, hK⟩ := exists_perturbation_buffer F hF E
  let t := binaryScale D K
  let a : ℕ → Fin (r + 1) → ℤ := fun k => transferWeights U s (t k)
  have hmapA : A.map (Int.castRingHom ℝ) = (D : ℝ) • B.map (fun q => (q : ℝ)) := by
    ext i j
    change (A i j : ℝ) = (D : ℝ) * (B i j : ℝ)
    exact_mod_cast hA i j
  have hmapAW : (A * W).map (Int.castRingHom ℝ) = (D : ℝ) • F := by
    rw [Matrix.map_mul, hmapA, Matrix.smul_mul]
  have hmapLift : (zeroSumLift (A * W)).map (Int.castRingHom ℝ) =
      (D : ℝ) • zeroSumLift F := by
    rw [zeroSumLift_map, hmapAW, zeroSumLift_smul]
  have hlead : (1 / (D : ℝ)) ^ r * (∏ i, s i : ℤ) = |(B.det : ℝ)| := by
    have hsprod : (0 : ℤ) < ∏ i, s i := Finset.prod_pos (fun i _ => hs i)
    have habs : (∏ i, s i : ℤ) = |A.det| := by
      simpa [abs_of_pos hsprod] using diagonalization_abs_det hP hW hdiag
    have habsR : ((∏ i, s i : ℤ) : ℝ) = |(A.det : ℝ)| := by exact_mod_cast habs
    have hADR : (A.det : ℝ) = (D : ℝ) ^ r * (B.det : ℝ) := by
      simpa only [Rat.cast_intCast, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast] using
        congrArg (fun q : ℚ => (q : ℝ)) hAD
    have hDR : (0 : ℝ) < D := by exact_mod_cast hD
    rw [habsR, hADR, abs_mul, abs_pow, abs_of_pos hDR]
    rw [div_pow]
    field_simp
    simp
  refine ⟨a, ?_, ?_⟩
  · intro k
    let M := snfUnshear P * chainMatrix (fun i => t k * s i)
    have hsat : ∀ c : Fin (r + 1) → ℤ, dotProduct (a k) c = 0 → ∃ z, M *ᵥ z = c :=
      transferWeights_saturated P U hPU s (t k)
    have hMR : M.map (Int.castRingHom ℝ) =
        (t k : ℝ) • (zeroSumLift (A * W)).map (Int.castRingHom ℝ) - E := by
      ext i j
      have h := congrArg (fun z : ℤ => (z : ℝ))
        (congrFun (congrFun (transferMatrix_affine P A W s hdiag (t k)) i) j)
      simpa only [M, E, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        Int.coe_castRingHom, Int.cast_sub, Int.cast_mul] using h
    have hM : M.map (Int.castRingHom ℝ) =
        ((D : ℝ) * (t k : ℝ)) • zeroSumLift F - E := by
      rw [hMR, hmapLift, smul_smul, mul_comm (t k : ℝ) (D : ℝ)]
    have ht0 : (0 : ℝ) ≤ (t k : ℝ) := by
      exact_mod_cast binaryScale_nonneg D K k
    apply integer_kernel_no_small_relation (a k) M hsat F E hadmF K
      ((D : ℝ) * (t k : ℝ)) (by positivity) hK hM (2 ^ k) (by positivity)
    simpa [t] using binaryScale_buffer hD K k
  · intro i
    simpa only [hlead] using transferWeights_limit U s t (1 / (D : ℝ))
      (binaryScale_limit hD hK0) i

/-- Eventual nonnegativity lets us read integer weights as natural weights. -/
theorem IntegerRelationFree.toNat {ι : Type*} [Fintype ι] {a : ι → ℤ} {Q : ℕ}
    (hf : IntegerRelationFree a Q) (ha : ∀ i, 0 ≤ a i) :
    RelationFree (fun i => (a i).toNat) Q := by
  intro c hc hrel
  apply hf c hc
  simpa only [Int.toNat_of_nonneg (ha _)] using hrel

/-- A deliberately weakened binary-block estimate. Dropping the factor `1/2`
is enough for the requested dimension-independent lower bound. -/
theorem uniform_relationFree_lower {C : ℝ}
    (hC : ∀ (N : ℕ) (A : Finset ℕ), A ⊆ Finset.Icc 1 N → SumDistinct A →
      N ≠ 0 → C * 2 ^ A.card < (N : ℝ))
    (r k W : ℕ) (hk : 0 < k) (a : Fin (r + 1) → ℕ)
    (ha : ∀ i, 0 < a i) (hW : ∀ i, a i ≤ W) (hf : RelationFree a (2 ^ k)) :
    C * ((2 : ℝ) ^ k) ^ r < (W : ℝ) := by
  obtain ⟨A, hcard, hsub, hsum⟩ :=
    exists_binary_block_set (r + 1) k W (by omega) hk a ha hW hf
  have hWpos : 0 < W := lt_of_lt_of_le (ha 0) (hW 0)
  have hN0 : 2 ^ (k - 1) * W ≠ 0 := by positivity
  have hbound := hC (2 ^ (k - 1) * W) A hsub hsum hN0
  rw [hcard] at hbound
  have hpow : (0 : ℝ) < 2 ^ k := by positivity
  have hbig : C * ((2 : ℝ) ^ k) ^ (r + 1) < (2 : ℝ) ^ k * (W : ℝ) := by
    calc
      C * ((2 : ℝ) ^ k) ^ (r + 1) = C * (2 : ℝ) ^ ((r + 1) * k) := by
        rw [← pow_mul, Nat.mul_comm k (r + 1)]
      _ < ((2 ^ (k - 1) * W : ℕ) : ℝ) := hbound
      _ ≤ (2 : ℝ) ^ k * (W : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_right W
          (pow_le_pow_right' (show 1 ≤ (2 : ℕ) by norm_num) (Nat.sub_le k 1))
  apply (mul_lt_mul_iff_right₀ hpow).mp
  calc
    (2 : ℝ) ^ k * (C * ((2 : ℝ) ^ k) ^ r) = C * ((2 : ℝ) ^ k) ^ (r + 1) := by ring
    _ < (2 : ℝ) ^ k * (W : ℝ) := hbig

/-- Binary blocks transfer a uniform subset-sum constant to the common positive
leading coefficient of any integer family with the binary relation gap. -/
theorem uniform_bound_le_transfer_limit {C δ : ℝ}
    (hC : ∀ (N : ℕ) (A : Finset ℕ), A ⊆ Finset.Icc 1 N → SumDistinct A →
      N ≠ 0 → C * 2 ^ A.card < (N : ℝ))
    (hδ : 0 < δ) (r : ℕ) (a : ℕ → Fin (r + 1) → ℤ)
    (hf : ∀ k, IntegerRelationFree (a k) (2 ^ k))
    (hlim : ∀ i, Tendsto (fun k => (a k i : ℝ) / ((2 : ℝ) ^ k) ^ r)
      atTop (𝓝 δ)) : C ≤ δ := by
  classical
  by_contra hnot
  have hδC : δ < C := lt_of_not_ge hnot
  have hev : ∀ᶠ k in atTop, ∀ i : Fin (r + 1),
      0 < (a k i : ℝ) / ((2 : ℝ) ^ k) ^ r ∧
      (a k i : ℝ) / ((2 : ℝ) ^ k) ^ r < C := by
    apply Filter.eventually_all.mpr
    intro i
    exact ((hlim i).eventually_const_lt hδ).and ((hlim i).eventually_lt_const hδC)
  obtain ⟨k, hk, hki⟩ := ((eventually_gt_atTop 0).and hev).exists
  have hp : (0 : ℝ) < ((2 : ℝ) ^ k) ^ r := by positivity
  have ha : ∀ i, 0 < a k i := by
    intro i
    have hpos : (0 : ℝ) < a k i := by
      simpa using (lt_div_iff₀ hp).mp (hki i).1
    exact_mod_cast hpos
  let b : Fin (r + 1) → ℕ := fun i => (a k i).toNat
  have hb : ∀ i, 0 < b i := by
    intro i
    have := ha i
    dsimp [b]
    omega
  have hbcast : ∀ i, (b i : ℝ) = (a k i : ℝ) := by
    intro i
    exact_mod_cast Int.toNat_of_nonneg (ha i).le
  let W := Finset.univ.sup b
  have hW : ∀ i, b i ≤ W := fun i => Finset.le_sup (Finset.mem_univ i)
  have hfre : RelationFree b (2 ^ k) := (hf k).toNat (fun i => (ha i).le)
  have hbound := uniform_relationFree_lower hC r k W hk b hb hW hfre
  obtain ⟨i, hi, hWi⟩ := Finset.exists_mem_eq_sup Finset.univ
    (show (Finset.univ : Finset (Fin (r + 1))).Nonempty from ⟨0, Finset.mem_univ _⟩) b
  have hWeq : W = b i := hWi
  rw [hWeq, hbcast i] at hbound
  have hupper := (div_lt_iff₀ hp).mp (hki i).2
  linarith

/-- Generic transfer: a uniform subset-sum bound supplies one positive lower
bound for the absolute determinant of every nonsingular cube-admissible
rational matrix, independently of its dimension. -/
theorem lattice_lower_bound : UniformSubsetBound →
    ∃ c > (0 : ℝ), ∀ (r : ℕ) (_hr : 0 < r) (B : Matrix (Fin r) (Fin r) ℚ),
      B.det ≠ 0 → CubeAdmissible B → c ≤ |(B.det : ℝ)| := by
  rintro ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro r hr B hB hadm
  obtain ⟨a, hf, hlim⟩ := exists_integer_transfer_family B hB hadm
  have hδ : (0 : ℝ) < |(B.det : ℝ)| := by
    apply abs_pos.mpr
    exact_mod_cast hB
  exact uniform_bound_le_transfer_limit hC hδ r a hf hlim

/-
# Determinant of the odd-cycle matrix

The cyclic shift is indexed by `Fin b` and sends column `j` to row `(j + 1) % b`.
Expanding the first row of `1 + t • P` leaves two triangular minors.
-/

open Finset Matrix

/-- The cyclic permutation matrix: its column `j` is the standard basis vector
with index `(j + 1) % b`. The definition also makes sense for `b = 0`. -/
def cycleShift (R : Type*) [Zero R] [One R] (b : ℕ) : Matrix (Fin b) (Fin b) R :=
  fun i j ↦ if i.val = (j.val + 1) % b then 1 else 0

/-- Identity plus a scalar multiple of the cyclic shift. -/
def cycleMatrix {R : Type*} [Ring R] (b : ℕ) (t : R) : Matrix (Fin b) (Fin b) R :=
  1 + t • cycleShift R b

@[local simp] theorem cycleMatrix_apply {R : Type*} [Ring R] (b : ℕ) (t : R)
    (i j : Fin b) :
    cycleMatrix b t i j = (if i = j then 1 else 0) +
      (if i.val = (j.val + 1) % b then t else 0) := by
  simp only [cycleMatrix, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
    cycleShift, smul_eq_mul]
  split_ifs <;> simp

private theorem cycle_mod_succ {b : ℕ} (j : Fin b) :
    (j.val + 1) % b = if j.val + 1 = b then 0 else j.val + 1 := by
  by_cases h : j.val + 1 = b
  · simp [h]
  · rw [ite_eq_right h, Nat.mod_eq_of_lt (by omega)]

@[local simp] theorem cycleMatrix_diag {R : Type*} [Ring R] {b : ℕ} (hb : 2 ≤ b)
    (t : R) (i : Fin b) : cycleMatrix b t i i = 1 := by
  have h : i.val ≠ (i.val + 1) % b := by
    rw [cycle_mod_succ]
    split_ifs <;> omega
  simp [h]

private theorem cycleMatrix_minor_zero_det {R : Type*} [CommRing R]
    (n : ℕ) (hn : 1 ≤ n) (t : R) :
    ((cycleMatrix (n + 1) t).submatrix Fin.succ Fin.succ).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp only [Matrix.submatrix_apply, cycleMatrix_diag (by omega : 2 ≤ n + 1),
      Finset.prod_const_one]
  · intro i j hij
    have hij' : i.val < j.val := hij
    have hne : i.succ ≠ j.succ := by simpa using (ne_of_lt hij : i ≠ j)
    have hshift : i.succ.val ≠ (j.succ.val + 1) % (n + 1) := by
      rw [cycle_mod_succ]
      simp only [Fin.val_succ]
      split_ifs <;> omega
    simp only [Matrix.submatrix_apply, cycleMatrix_apply, ite_eq_right hne, ite_eq_right hshift,
      add_zero]

private theorem cycleMatrix_minor_last_det {R : Type*} [CommRing R]
    (n : ℕ) (t : R) :
    ((cycleMatrix (n + 1) t).submatrix Fin.succ Fin.castSucc).det = t ^ n := by
  rw [Matrix.det_of_isUpperTriangular]
  · have hdiag : ∀ i : Fin n, cycleMatrix (n + 1) t i.succ i.castSucc = t := by
      intro i
      have hne : i.succ ≠ i.castSucc := by
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_succ, Fin.val_castSucc] at this
        omega
      have hshift : i.succ.val = (i.castSucc.val + 1) % (n + 1) := by
        rw [Nat.mod_eq_of_lt (by simp only [Fin.val_castSucc]; omega)]
        rfl
      simp only [cycleMatrix_apply, ite_eq_right hne, ite_eq_left hshift, zero_add]
    simp only [Matrix.submatrix_apply, hdiag, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  · intro i j hij
    have hij' : j.val < i.val := hij
    have hne : i.succ ≠ j.castSucc := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_castSucc] at this
      omega
    have hshift : i.succ.val ≠ (j.castSucc.val + 1) % (n + 1) := by
      rw [Nat.mod_eq_of_lt (by simp only [Fin.val_castSucc]; omega)]
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    simp only [Matrix.submatrix_apply, cycleMatrix_apply, ite_eq_right hne, ite_eq_right hshift,
      add_zero]

/-- A first-row expansion formula for the cyclic matrix. -/
theorem det_cycleMatrix_succ {R : Type*} [CommRing R]
    (n : ℕ) (hn : 1 ≤ n) (t : R) :
    (cycleMatrix (n + 1) t).det = 1 + (-1 : R) ^ n * t ^ (n + 1) := by
  have hne : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hlast : cycleMatrix (n + 1) t 0 (Fin.last n) = t := by
    simp [hne]
  rw [Matrix.det_succ_row_zero]
  rw [Finset.sum_eq_add_of_mem (0 : Fin (n + 1)) (Fin.last n)
    (Finset.mem_univ _) (Finset.mem_univ _) hne]
  · simp only [Fin.val_zero, pow_zero, cycleMatrix_diag (by omega : 2 ≤ n + 1),
      mul_one, Fin.succAbove_zero, cycleMatrix_minor_zero_det n hn t,
      Fin.val_last, hlast, Fin.succAbove_last, cycleMatrix_minor_last_det]
    rw [pow_succ]
    ring
  · intro j _ hj
    have hzero : cycleMatrix (n + 1) t 0 j = 0 := by
      have hne' : (0 : Fin (n + 1)) ≠ j := Ne.symm hj.1
      have hshift : (0 : Fin (n + 1)).val ≠ (j.val + 1) % (n + 1) := by
        rw [cycle_mod_succ]
        have hjlast : j.val ≠ n := by
          intro h
          exact hj.2 (Fin.ext h)
        split_ifs <;> simp only [Fin.val_zero] <;> omega
      simp only [cycleMatrix_apply, ite_eq_right hne', ite_eq_right hshift, add_zero]
    simp only [hzero, mul_zero, zero_mul]

/-- The characteristic determinant identity for every nonempty cycle. -/
theorem det_cycleMatrix {R : Type*} [CommRing R] {b : ℕ}
    (hb : 0 < b) (t : R) :
    (cycleMatrix b t).det = 1 - (-t) ^ b := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  by_cases hn : n = 0
  · subst n
    simp
  · rw [det_cycleMatrix_succ n (by omega), neg_pow t (n + 1), pow_succ (-1 : R)]
    ring

/-- The usual identity `det (I - xP) = 1 - x^b`. -/
theorem det_one_sub_smul_cycleShift {R : Type*} [CommRing R] {b : ℕ}
    (hb : 0 < b) (x : R) :
    (1 - x • cycleShift R b).det = 1 - x ^ b := by
  simpa only [cycleMatrix, neg_smul, sub_eq_add_neg, neg_neg] using
    det_cycleMatrix hb (-x)

/-- The determinant formula for an odd cycle. -/
theorem det_cycleMatrix_odd {R : Type*} [CommRing R] {b : ℕ}
    (hb : 3 ≤ b) (hodd : Odd b) (t : R) :
    (cycleMatrix b t).det = 1 + t ^ b := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  rw [det_cycleMatrix_succ n (by omega)]
  have hn : Even n := by
    obtain ⟨m, hm⟩ := hodd
    exact ⟨m, by omega⟩
  rw [hn.neg_one_pow, one_mul]

/-- The rational matrix used for the odd-cycle counterexample. -/
def cycleB (b : ℕ) : Matrix (Fin b) (Fin b) ℚ := cycleMatrix b (1 / 2 : ℚ)

/-- The odd-cycle determinant is `1 + 2⁻ᵇ`. -/
theorem det_cycleB {b : ℕ} (hb : 3 ≤ b) (hodd : Odd b) :
    (cycleB b).det = 1 + (1 / 2 : ℚ) ^ b :=
  det_cycleMatrix_odd hb hodd _

/-- The anchor-coordinate change: keep nonanchor coordinates, and replace
coordinate zero by coordinate zero minus the sum of all other coordinates. -/
def cycleAnchorU (R : Type*) [Ring R] (b : ℕ) : Matrix (Fin b) (Fin b) R :=
  fun i j ↦ if i = j then 1 else if i.val = 0 then -1 else 0

@[local simp] theorem cycleAnchorU_diag {R : Type*} [Ring R] (b : ℕ) (i : Fin b) :
    cycleAnchorU R b i i = 1 := by
  simp [cycleAnchorU]

/-- The anchor-coordinate change is unipotent and has determinant one. -/
@[local simp] theorem det_cycleAnchorU {R : Type*} [CommRing R] (b : ℕ) :
    (cycleAnchorU R b).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp
  · intro i j hij
    have hne : i ≠ j := ne_of_gt hij
    have hi : i.val ≠ 0 := by
      have hij' : j.val < i.val := hij
      omega
    simp [cycleAnchorU, hne, hi]

/-- The nonanchor coordinates are unchanged. -/
theorem cycleAnchorU_mulVec_of_ne_zero {R : Type*} [Ring R] (b : ℕ)
    (x : Fin b → R) (i : Fin b) (hi : i.val ≠ 0) :
    (cycleAnchorU R b *ᵥ x) i = x i := by
  simp [Matrix.mulVec, dotProduct, cycleAnchorU, hi, ite_mul]

/-- The zeroth coordinate subtracts the sum of the nonanchor coordinates. -/
theorem cycleAnchorU_mulVec_zero {R : Type*} [Ring R] (b : ℕ) [NeZero b]
    (x : Fin b → R) :
    (cycleAnchorU R b *ᵥ x) 0 = x 0 - ∑ j ∈ Finset.univ.erase 0, x j := by
  change (∑ j, cycleAnchorU R b 0 j * x j) = _
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin b))]
  have hsum : (∑ j ∈ Finset.univ.erase (0 : Fin b), cycleAnchorU R b 0 j * x j) =
      -∑ j ∈ Finset.univ.erase (0 : Fin b), x j := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hne : (0 : Fin b) ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
    simp [cycleAnchorU, hne]
  rw [hsum, cycleAnchorU_diag, one_mul]
  exact (sub_eq_neg_add _ _).symm

/-- The complete rational anchor matrix, as a product of the cycle matrix and
the determinant-one anchor-coordinate change. -/
def cycleAnchorH (b : ℕ) : Matrix (Fin b) (Fin b) ℚ :=
  cycleB b * cycleAnchorU ℚ b

/-- Passing to the full anchor matrix preserves the odd-cycle determinant. -/
theorem det_cycleAnchorH {b : ℕ} (hb : 3 ≤ b) (hodd : Odd b) :
    (cycleAnchorH b).det = 1 + (1 / 2 : ℚ) ^ b := by
  simp only [cycleAnchorH, Matrix.det_mul, det_cycleAnchorU, mul_one, det_cycleB hb hodd]

/-
# Scalar asymptotics for the odd-cycle counterexample

The exponent appearing in the recursively constructed determinant is a finite
geometric sum. Its polynomial growth, for fixed depth, is dominated by `2 ^ b`.
-/

open Filter Finset
open scoped Topology

/-- The exponent in a depth-`k` recursive determinant with branching number `b`. -/
def cycleDetExponent (b k : ℕ) : ℕ := ∑ j ∈ Finset.range k, b ^ j

@[local simp] theorem cycleDetExponent_zero (b : ℕ) : cycleDetExponent b 0 = 0 := by
  simp [cycleDetExponent]

@[local simp] theorem cycleDetExponent_succ (b k : ℕ) :
    cycleDetExponent b (k + 1) = cycleDetExponent b k + b ^ k := by
  simp [cycleDetExponent, Finset.sum_range_succ]

/-- The recurrence of the geometric exponent, in the form used in recursive gadgets. -/
theorem cycleDetExponent_succ_mul (b k : ℕ) :
    cycleDetExponent b (k + 1) = 1 + b * cycleDetExponent b k := by
  simp only [cycleDetExponent, Finset.sum_range_succ', pow_succ',
    Finset.mul_sum, pow_zero]
  exact add_comm _ _

/-- The scalar determinant recurrence. -/
noncomputable def cycleDrec (b : ℕ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => (1 + (1 / 2 : ℝ) ^ b) * cycleDrec b k ^ b

/-- Closed form for the scalar recurrence. -/
theorem cycleDrec_eq (b k : ℕ) :
    cycleDrec b k = (1 + (1 / 2 : ℝ) ^ b) ^ cycleDetExponent b k := by
  induction k with
  | zero => simp [cycleDrec]
  | succ k ih =>
    rw [cycleDrec, ih, cycleDetExponent_succ_mul, pow_add, pow_one,
      mul_comm b (cycleDetExponent b k), pow_mul]

/-- A convenient polynomial bound on the geometric-sum exponent. -/
theorem cycleDetExponent_lt_pow {b : ℕ} (hb : 2 ≤ b) (k : ℕ) :
    cycleDetExponent b k < b ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [cycleDetExponent_succ, pow_succ]
    calc
      cycleDetExponent b k + b ^ k < b ^ k + b ^ k := Nat.add_lt_add_right ih _
      _ ≤ b ^ k * b := by nlinarith [Nat.zero_le (b ^ k)]

/-- The simple power bound for the recursive determinant. -/
theorem cycleDrec_le_pow {b : ℕ} (hb : 2 ≤ b) (k : ℕ) :
    cycleDrec b k ≤ (1 + (1 / 2 : ℝ) ^ b) ^ (b ^ k) := by
  rw [cycleDrec_eq]
  exact pow_le_pow_right₀ (le_add_of_nonneg_right (by positivity))
    (cycleDetExponent_lt_pow hb k).le

/-- The closed-form determinant is bounded by an exponential with a vanishing
exponent as the branching number grows. -/
theorem cycleDet_pow_le_exp {b : ℕ} (hb : 2 ≤ b) (k : ℕ) :
    (1 + (1 / 2 : ℝ) ^ b) ^ cycleDetExponent b k ≤
      Real.exp ((b : ℝ) ^ k * (1 / 2 : ℝ) ^ b) := by
  calc
    (1 + (1 / 2 : ℝ) ^ b) ^ cycleDetExponent b k ≤
        (Real.exp ((1 / 2 : ℝ) ^ b)) ^ cycleDetExponent b k := by
      apply pow_le_pow_left₀ (by positivity)
      simpa [add_comm] using Real.add_one_le_exp ((1 / 2 : ℝ) ^ b)
    _ = Real.exp ((cycleDetExponent b k : ℝ) * (1 / 2 : ℝ) ^ b) :=
      (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp ((b : ℝ) ^ k * (1 / 2 : ℝ) ^ b) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (cycleDetExponent_lt_pow hb k).le

/-- For each fixed depth, the determinant is eventually smaller than `2`. -/
theorem cycleDet_eventually_lt_two (k : ℕ) :
    ∀ᶠ b : ℕ in atTop, (1 + (1 / 2 : ℝ) ^ b) ^ cycleDetExponent b k < 2 := by
  have hlim : Tendsto (fun b : ℕ ↦ Real.exp ((b : ℝ) ^ k * (1 / 2 : ℝ) ^ b))
      atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.exp_zero] using
      (Real.continuous_exp.continuousAt (x := 0)).tendsto.comp
      (tendsto_pow_const_mul_const_pow_of_lt_one k
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2)),
    eventually_ge_atTop 2] with b hb hb2
  exact (cycleDet_pow_le_exp hb2 k).trans_lt hb

/-- Arbitrarily small normalized recursive determinant, with positive depth and
an odd branching number at least three. This is the scalar form used by the
recursive counterexample. -/
theorem exists_odd_cycle_small_normalized_det {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, 0 < k ∧ ∃ b : ℕ, 3 ≤ b ∧ Odd b ∧
      (1 + (1 / 2 : ℝ) ^ b) ^ (∑ j ∈ Finset.range k, b ^ j) /
        (3 / 2 : ℝ) ^ k < ε := by
  have hlim : Tendsto (fun k : ℕ ↦ (2 : ℝ) / (3 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3 / 2)).const_div_atTop 2
  obtain ⟨k, hk, hkε⟩ :=
    ((eventually_gt_atTop 0).and (hlim.eventually (gt_mem_nhds hε))).exists
  obtain ⟨N, hN⟩ := eventually_atTop.mp (cycleDet_eventually_lt_two k)
  let b := 2 * (N + 1) + 1
  have hbN : N ≤ b := by dsimp [b]; omega
  refine ⟨k, hk, b, ?_, ?_, ?_⟩
  · dsimp [b]; omega
  · exact ⟨N + 1, rfl⟩
  · have hbdet := hN b hbN
    change (1 + (1 / 2 : ℝ) ^ b) ^ cycleDetExponent b k / (3 / 2 : ℝ) ^ k < ε
    exact (div_lt_div_of_pos_right hbdet (by positivity)).trans hkε

/-- The same existence statement for the recursively defined determinant. -/
theorem exists_odd_cycle_small_Drec {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, 0 < k ∧ ∃ b : ℕ, 3 ≤ b ∧ Odd b ∧
      cycleDrec b k / (3 / 2 : ℝ) ^ k < ε := by
  simpa only [cycleDrec_eq, cycleDetExponent] using
    exists_odd_cycle_small_normalized_det hε

/- # Rational cube gadgets with a distinguished real coordinate -/

open Matrix

/-- A rational full-rank cube packing together with an all-real strip property.
The nonanchor columns span a lattice in the zero-sum hyperplane. -/
structure CubeGadget (ι : Type*) [Fintype ι] [DecidableEq ι] where
  H : Matrix ι ι ℚ
  anchor : ι
  height : ℚ
  height_pos : 0 < height
  det_pos : 0 < H.det
  sum_mulVec : ∀ x : ι → ℚ, ∑ i, (H *ᵥ x) i = height * x anchor
  strip : ∀ x : ι → ℚ, (∀ i, i ≠ anchor → ∃ z : ℤ, x i = (z : ℚ)) →
    (∀ i, |(H *ᵥ x) i| < 1) → |x anchor| < 1
  admissible : ∀ z : ι → ℤ,
    (∀ i, |(H *ᵥ (fun j => (z j : ℚ))) i| < 1) → z = 0

/-
# Odd-cycle cube gadgets

For `B = I + (1/2) P`, short vectors have every coordinate of absolute value
less than two. When all but coordinate zero are integral, their successive
partial sums alternate between zero and minus the sign of coordinate zero.
This proves the strip property, even without an oddness hypothesis. Oddness
excludes the nonzero alternating integral cycle and gives admissibility.
-/

open Finset Matrix

private theorem cycleShift_mulVec_zero (n : ℕ) (z : Fin (n + 1) → ℚ) :
    (cycleShift ℚ (n + 1) *ᵥ z) 0 = z (Fin.last n) := by
  change (∑ j, (if (0 : Fin (n + 1)).val = (j.val + 1) % (n + 1)
    then (1 : ℚ) else 0) * z j) = _
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp
  · intro j _ hj
    have hj' : j.val ≠ n := fun h => hj (Fin.ext h)
    have hlt : j.val + 1 < n + 1 := by omega
    simp [Nat.mod_eq_of_lt hlt]
  · simp

private theorem cycleShift_mulVec_succ (n : ℕ) (z : Fin (n + 1) → ℚ)
    (i : Fin n) :
    (cycleShift ℚ (n + 1) *ᵥ z) i.succ = z i.castSucc := by
  change (∑ j, (if i.succ.val = (j.val + 1) % (n + 1)
    then (1 : ℚ) else 0) * z j) = _
  rw [Finset.sum_eq_single i.castSucc]
  · simp [Nat.mod_eq_of_lt (show i.val + 1 < n + 1 by omega)]
  · intro j _ hj
    have hne : i.succ.val ≠ (j.val + 1) % (n + 1) := by
      by_cases hjlast : j.val = n
      · simp [hjlast]
      · rw [Nat.mod_eq_of_lt (show j.val + 1 < n + 1 by omega)]
        intro h
        apply hj
        apply Fin.ext
        simp only [Fin.val_succ, Fin.val_castSucc] at h ⊢
        omega
    simp only [ite_eq_right hne, zero_mul]
  · simp

/-- The closing edge of the cycle. -/
theorem cycleB_mulVec_zero (n : ℕ) (z : Fin (n + 1) → ℚ) :
    (cycleB (n + 1) *ᵥ z) 0 = z 0 + (1 / 2 : ℚ) * z (Fin.last n) := by
  simp [cycleB, cycleMatrix, Matrix.add_mulVec, Matrix.smul_mulVec,
    cycleShift_mulVec_zero]

/-- The ordinary edges of the cycle. -/
theorem cycleB_mulVec_succ (n : ℕ) (z : Fin (n + 1) → ℚ) (i : Fin n) :
    (cycleB (n + 1) *ᵥ z) i.succ = z i.succ + (1 / 2 : ℚ) * z i.castSucc := by
  simp [cycleB, cycleMatrix, Matrix.add_mulVec, Matrix.smul_mulVec,
    cycleShift_mulVec_succ]

/-- A maximum-coordinate argument bounds every short cycle coordinate by two. -/
theorem cycleB_short_coord_lt_two (n : ℕ) (z : Fin (n + 1) → ℚ)
    (hz : ∀ i, |(cycleB (n + 1) *ᵥ z) i| < 1) : ∀ i, |z i| < 2 := by
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (fun i => |z i|)
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin (n + 1))).Nonempty)
  have hmax : ∀ i, |z i| ≤ |z j| := fun i => hj i (Finset.mem_univ i)
  have hprev : ∃ k, |z j + (1 / 2 : ℚ) * z k| < 1 := by
    refine Fin.cases ?_ (fun i => ?_) j
    · exact ⟨Fin.last n, by simpa only [cycleB_mulVec_zero] using hz 0⟩
    · exact ⟨i.castSucc, by simpa only [cycleB_mulVec_succ] using hz i.succ⟩
  obtain ⟨k, hk⟩ := hprev
  have htriangle : |z j| ≤ |z j + (1 / 2 : ℚ) * z k| + (1 / 2 : ℚ) * |z k| := by
    have h := abs_add_le (z j + (1 / 2 : ℚ) * z k) (-(1 / 2 : ℚ) * z k)
    norm_num [abs_mul] at h
    convert h using 1
  have hjlt : |z j| < 2 := by linarith [hmax k]
  exact fun i => lt_of_le_of_lt (hmax i) hjlt

private theorem integral_ternary {q : ℚ} (hq : ∃ k : ℤ, q = (k : ℚ))
    (h : |q| < 2) : q = -1 ∨ q = 0 ∨ q = 1 := by
  obtain ⟨k, rfl⟩ := hq
  have hk : |k| < 2 := by exact_mod_cast h
  have hb := abs_lt.mp hk
  have : k = -1 ∨ k = 0 ∨ k = 1 := by omega
  rcases this with rfl | rfl | rfl <;> norm_num

private theorem ternary_next_zero {p q : ℚ}
    (hq : q = -1 ∨ q = 0 ∨ q = 1)
    (hshort : |q + (1 / 2 : ℚ) * p| < 1) (hp : p = 0) : q = 0 := by
  subst p
  rcases hq with rfl | rfl | rfl <;> norm_num at *

private theorem ternary_next_nonzero {p q : ℚ}
    (hp : p = -1 ∨ p = 0 ∨ p = 1) (hq : q = -1 ∨ q = 0 ∨ q = 1)
    (hshort : |q + (1 / 2 : ℚ) * p| < 1) (hne : q ≠ 0) : q = -p := by
  rcases hp with rfl | rfl | rfl <;>
    rcases hq with rfl | rfl | rfl <;> norm_num at *

/-- Zero propagates forward through an integral short chain. -/
private theorem chain_zero (n : ℕ) (z : Fin (n + 1) → ℚ)
    (ht : ∀ i : Fin n, z i.succ = -1 ∨ z i.succ = 0 ∨ z i.succ = 1)
    (hs : ∀ i : Fin n, |z i.succ + (1 / 2 : ℚ) * z i.castSucc| < 1)
    (hzero : z 0 = 0) : z = 0 := by
  funext i
  exact Fin.induction hzero (fun j hj => ternary_next_zero (ht j) (hs j) hj) i

/-- If the initial coordinate is nonnegative, the sum of the subsequent
integral coordinates is either zero (with a nonnegative last coordinate), or
minus one (with a nonpositive last coordinate). -/
private theorem chain_sum (n : ℕ) (z : Fin (n + 1) → ℚ) (hzero : 0 ≤ z 0)
    (ht : ∀ i : Fin n, z i.succ = -1 ∨ z i.succ = 0 ∨ z i.succ = 1)
    (hs : ∀ i : Fin n, |z i.succ + (1 / 2 : ℚ) * z i.castSucc| < 1) :
    ((∑ i : Fin n, z i.succ) = 0 ∧ 0 ≤ z (Fin.last n)) ∨
      ((∑ i : Fin n, z i.succ) = -1 ∧ z (Fin.last n) ≤ 0) := by
  induction n with
  | zero =>
    left
    simpa using hzero
  | succ n ih =>
    have hrec := ih (fun i => z i.castSucc) (by simpa using hzero)
      (fun i => by simpa only [Fin.castSucc_succ] using ht i.castSucc)
      (fun i => by simpa only [Fin.castSucc_succ] using hs i.castSucc)
    have hlast := ht (Fin.last n)
    have hedge := abs_lt.mp (hs (Fin.last n))
    simp only [Fin.succ_last] at hlast hedge
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.succ_castSucc, Fin.succ_last]
    rcases hrec with ⟨hsum, hprev⟩ | ⟨hsum, hprev⟩
    · rcases hlast with hlast | hlast | hlast
      · right
        constructor <;> linarith
      · left
        constructor <;> linarith
      · exfalso
        linarith [hedge.2]
    · rcases hlast with hlast | hlast | hlast
      · exfalso
        linarith [hedge.1]
      · right
        constructor <;> linarith
      · left
        constructor <;> linarith

/-- A nonzero last coordinate forces the entire integral chain to alternate. -/
private theorem chain_alternates (n : ℕ) (z : Fin (n + 1) → ℚ)
    (ht : ∀ i, z i = -1 ∨ z i = 0 ∨ z i = 1)
    (hs : ∀ i : Fin n, |z i.succ + (1 / 2 : ℚ) * z i.castSucc| < 1)
    (hne : z (Fin.last n) ≠ 0) : z (Fin.last n) = (-1 : ℚ) ^ n * z 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hedge : z (Fin.last (n + 1)) = -z (Fin.last n).castSucc := by
      simpa only [Fin.succ_last] using ternary_next_nonzero
        (ht (Fin.last n).castSucc) (ht (Fin.last n).succ) (hs (Fin.last n))
        (by simpa only [Fin.succ_last] using hne)
    have hprev : z (Fin.last n).castSucc ≠ 0 := by
      intro h
      apply hne
      rw [hedge, h, neg_zero]
    have hrec := ih (fun i => z i.castSucc) (fun i => ht i.castSucc)
      (fun i => by simpa only [Fin.castSucc_succ] using hs i.castSucc) hprev
    simp only [Fin.castSucc_zero] at hrec
    rw [hedge, hrec]
    simp [pow_succ]

private theorem cycleB_strip_nonneg (n : ℕ) (z : Fin (n + 1) → ℚ)
    (hint : ∀ i : Fin n, ∃ k : ℤ, z i.succ = (k : ℚ))
    (hz : ∀ i, |(cycleB (n + 1) *ᵥ z) i| < 1) (hzero : 0 ≤ z 0) :
    |∑ i, z i| < 1 := by
  have hbound := cycleB_short_coord_lt_two n z hz
  have ht := fun i => integral_ternary (hint i) (hbound i.succ)
  have hs : ∀ i : Fin n, |z i.succ + (1 / 2 : ℚ) * z i.castSucc| < 1 := by
    intro i
    simpa only [cycleB_mulVec_succ] using hz i.succ
  by_cases heq : z 0 = 0
  · rw [chain_zero n z ht hs heq]
    simp
  · have hpos : 0 < z 0 := lt_of_le_of_ne hzero (Ne.symm heq)
    rcases chain_sum n z hzero ht hs with ⟨hsum, hlast⟩ | ⟨hsum, hlast⟩
    · rw [Fin.sum_univ_succ, hsum, add_zero]
      have hclose := abs_lt.mp (by simpa only [cycleB_mulVec_zero] using hz 0)
      apply abs_lt.mpr
      constructor <;> linarith
    · rw [Fin.sum_univ_succ, hsum]
      have hsmall := abs_lt.mp (hbound 0)
      apply abs_lt.mpr
      constructor <;> linarith

/-- The all-rational strip property for the cycle matrix. No oddness is needed:
only coordinate zero may be nonintegral, and the sum has absolute value below one. -/
theorem cycleB_strip {b : ℕ} [NeZero b] (z : Fin b → ℚ)
    (hint : ∀ i, i ≠ 0 → ∃ k : ℤ, z i = (k : ℚ))
    (hz : ∀ i, |(cycleB b *ᵥ z) i| < 1) : |∑ i, z i| < 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne b)
  have hint' : ∀ i : Fin n, ∃ k : ℤ, z i.succ = (k : ℚ) :=
    fun i => hint i.succ (Fin.succ_ne_zero i)
  by_cases hzero : 0 ≤ z 0
  · exact cycleB_strip_nonneg n z hint' hz hzero
  · have hneg := cycleB_strip_nonneg n (-z)
      (fun i => by
        obtain ⟨k, hk⟩ := hint' i
        exact ⟨-k, by simpa only [Pi.neg_apply, Int.cast_neg] using congrArg Neg.neg hk⟩)
      (fun i => by simpa only [Matrix.mulVec_neg, Pi.neg_apply, abs_neg] using hz i)
      (by simp only [Pi.neg_apply]; linarith)
    simpa only [Pi.neg_apply, Finset.sum_neg_distrib, abs_neg] using hneg

/-- An odd cycle has no nonzero integral vector with short image under `B`. -/
theorem cycleB_integral_short_eq_zero {b : ℕ} (hb : 3 ≤ b) (hodd : Odd b)
    (z : Fin b → ℚ) (hint : ∀ i, ∃ k : ℤ, z i = (k : ℚ))
    (hz : ∀ i, |(cycleB b *ᵥ z) i| < 1) : z = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  have ht := fun i => integral_ternary (hint i) (cycleB_short_coord_lt_two n z hz i)
  have hs : ∀ i : Fin n, |z i.succ + (1 / 2 : ℚ) * z i.castSucc| < 1 := by
    intro i
    simpa only [cycleB_mulVec_succ] using hz i.succ
  have hzero : z 0 = 0 := by
    by_contra hne
    have hclose : z 0 = -z (Fin.last n) := ternary_next_nonzero
      (ht (Fin.last n)) (ht 0) (by simpa only [cycleB_mulVec_zero] using hz 0) hne
    have hlast : z (Fin.last n) ≠ 0 := by
      intro h
      apply hne
      rw [hclose, h, neg_zero]
    have heven : Even n := by
      obtain ⟨m, hm⟩ := hodd
      exact ⟨m, by omega⟩
    have halt := chain_alternates n z ht hs hlast
    rw [heven.neg_one_pow, one_mul] at halt
    apply hne
    linarith
  exact chain_zero n z (fun i => ht i.succ) hs hzero

/-- Lattice admissibility of the odd cycle matrix. -/
theorem cycleB_admissible {b : ℕ} (hb : 3 ≤ b) (hodd : Odd b)
    (z : Fin b → ℤ) (hz : ∀ i, |(cycleB b *ᵥ (fun j => (z j : ℚ))) i| < 1) :
    z = 0 := by
  have h := cycleB_integral_short_eq_zero hb hodd (fun j => (z j : ℚ))
    (fun i => ⟨z i, rfl⟩) hz
  funext i
  have hi : (z i : ℚ) = 0 := congrFun h i
  exact_mod_cast hi

/-- Summing the cycle image multiplies the coordinate sum by `3/2`. -/
theorem sum_cycleB_mulVec (b : ℕ) (z : Fin b → ℚ) :
    (∑ i, (cycleB b *ᵥ z) i) = (3 / 2 : ℚ) * ∑ i, z i := by
  cases b with
  | zero => simp
  | succ n =>
    have hshift : (∑ i, (cycleShift ℚ (n + 1) *ᵥ z) i) = ∑ i, z i := by
      rw [Fin.sum_univ_succ, cycleShift_mulVec_zero]
      simp only [cycleShift_mulVec_succ]
      rw [Fin.sum_univ_castSucc z]
      ring
    simp only [cycleB, cycleMatrix, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum, hshift]
    ring

/-- The anchor coordinate change converts the coordinate sum to coordinate zero. -/
theorem sum_cycleAnchorU_mulVec (b : ℕ) [NeZero b] (x : Fin b → ℚ) :
    (∑ i, (cycleAnchorU ℚ b *ᵥ x) i) = x 0 := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin b)),
    cycleAnchorU_mulVec_zero]
  have hsum : (∑ i ∈ Finset.univ.erase (0 : Fin b), (cycleAnchorU ℚ b *ᵥ x) i) =
      ∑ i ∈ Finset.univ.erase (0 : Fin b), x i := by
    apply Finset.sum_congr rfl
    intro i hi
    apply cycleAnchorU_mulVec_of_ne_zero
    intro h
    exact (Finset.mem_erase.mp hi).1 (Fin.ext h)
  rw [hsum]
  ring

/-- The anchor change preserves integral vectors. -/
theorem cycleAnchorU_mulVec_intCast (b : ℕ) (z : Fin b → ℤ) :
    (cycleAnchorU ℚ b *ᵥ (fun j => (z j : ℚ))) =
      (fun i => ((cycleAnchorU ℤ b *ᵥ z) i : ℚ)) := by
  funext i
  simp [Matrix.mulVec, dotProduct, cycleAnchorU, Int.cast_sum]

/-- The nonanchor columns of the complete matrix have sum zero. -/
theorem sum_cycleAnchorH_mulVec (b : ℕ) [NeZero b] (x : Fin b → ℚ) :
    (∑ i, (cycleAnchorH b *ᵥ x) i) = (3 / 2 : ℚ) * x 0 := by
  rw [cycleAnchorH, ← Matrix.mulVec_mulVec, sum_cycleB_mulVec, sum_cycleAnchorU_mulVec]

/-- The all-rational strip property after the anchor coordinate change. -/
theorem cycleAnchorH_strip (b : ℕ) [NeZero b] (x : Fin b → ℚ)
    (hint : ∀ i, i ≠ 0 → ∃ k : ℤ, x i = (k : ℚ))
    (hx : ∀ i, |(cycleAnchorH b *ᵥ x) i| < 1) : |x 0| < 1 := by
  have hint' : ∀ i, i ≠ 0 → ∃ k : ℤ, (cycleAnchorU ℚ b *ᵥ x) i = (k : ℚ) := by
    intro i hi
    rw [cycleAnchorU_mulVec_of_ne_zero b x i (fun h => hi (Fin.ext h))]
    exact hint i hi
  have hs := cycleB_strip (cycleAnchorU ℚ b *ᵥ x) hint'
    (by simpa only [Matrix.mulVec_mulVec, cycleAnchorH] using hx)
  simpa only [sum_cycleAnchorU_mulVec] using hs

/-- Integral admissibility after the determinant-one anchor change. -/
theorem cycleAnchorH_admissible {b : ℕ} (hb : 3 ≤ b) (hodd : Odd b)
    (z : Fin b → ℤ) (hz : ∀ i, |(cycleAnchorH b *ᵥ (fun j => (z j : ℚ))) i| < 1) :
    z = 0 := by
  have h := cycleB_integral_short_eq_zero hb hodd
    (cycleAnchorU ℚ b *ᵥ (fun j => (z j : ℚ)))
    (fun i => ⟨(cycleAnchorU ℤ b *ᵥ z) i, congrFun (cycleAnchorU_mulVec_intCast b z) i⟩)
    (by simpa only [Matrix.mulVec_mulVec, cycleAnchorH] using hz)
  have hu : IsUnit (cycleAnchorU ℚ b) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (by simp)
  have hz' : (fun j => (z j : ℚ)) = 0 :=
    Matrix.mulVec_injective_of_isUnit hu (by simpa only [Matrix.mulVec_zero] using h)
  funext i
  have hi : (z i : ℚ) = 0 := congrFun hz' i
  exact_mod_cast hi

/-- The rational odd-cycle cube gadget, with height `3/2` and anchor zero. -/
noncomputable def oddCycleGadget (b : ℕ) (hb : 3 ≤ b) (hodd : Odd b) :
    CubeGadget (Fin b) := by
  letI : NeZero b := ⟨by omega⟩
  exact {
    H := cycleAnchorH b
    anchor := 0
    height := 3 / 2
    height_pos := by norm_num
    det_pos := by rw [det_cycleAnchorH hb hodd]; positivity
    sum_mulVec := sum_cycleAnchorH_mulVec b
    strip := cycleAnchorH_strip b
    admissible := cycleAnchorH_admissible hb hodd
  }

@[local simp] theorem oddCycleGadget_H (b : ℕ) (hb : 3 ≤ b) (hodd : Odd b) :
    (oddCycleGadget b hb hodd).H = cycleAnchorH b := rfl

@[local simp] theorem oddCycleGadget_anchor (b : ℕ) (hb : 3 ≤ b) (hodd : Odd b) :
    (oddCycleGadget b hb hodd).anchor = ⟨0, by omega⟩ := rfl

@[local simp] theorem oddCycleGadget_height (b : ℕ) (hb : 3 ≤ b) (hodd : Odd b) :
    (oddCycleGadget b hb hodd).height = (3 / 2 : ℚ) := rfl

-- Simplify the determinant before simplifying the `H` projection.
@[local simp↓] theorem oddCycleGadget_det (b : ℕ) (hb : 3 ≤ b) (hodd : Odd b) :
    (oddCycleGadget b hb hodd).H.det = 1 + (1 / 2 : ℚ) ^ b :=
  det_cycleAnchorH hb hodd

/-
# Composition and iteration of cube gadgets

The outer matrix acts on the child anchor coordinates first. Then a copy of the
child matrix acts in each block. The distinguished coordinate is the pair of
anchors. All strip arguments retain the possibly nonintegral anchor coordinate.
-/

namespace CubeGadget

open Finset Matrix

universe u v

variable {I : Type u} {J : Type v}
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Independent copies of the child matrix, indexed with the block first. -/
def childMatrix (F : CubeGadget J) : Matrix (I × J) (I × J) ℚ :=
  fun r c => if r.1 = c.1 then F.H r.2 c.2 else 0

/-- The outer matrix on anchor coordinates, and the identity on all others. -/
def anchorMatrix (G : CubeGadget I) (a : J) : Matrix (I × J) (I × J) ℚ :=
  fun r c => if c.2 = a then (if r.2 = a then G.H r.1 c.1 else 0)
    else if r = c then 1 else 0

/-- The matrix of the composed gadget. Multiplication is in the order in which
vectors are transformed: outer anchors first, then independent children. -/
def composeMatrix (G : CubeGadget I) (F : CubeGadget J) :
    Matrix (I × J) (I × J) ℚ :=
  childMatrix F * anchorMatrix G F.anchor

omit [Fintype I] in
/-- The child factor is a reindexed block diagonal matrix. -/
theorem childMatrix_eq_reindex (F : CubeGadget J) :
    (childMatrix F : Matrix (I × J) (I × J) ℚ) =
      Matrix.reindex (Equiv.prodComm J I) (Equiv.prodComm J I)
        (Matrix.blockDiagonal (fun _ : I => F.H)) := by
  rfl

@[local simp] theorem det_childMatrix (F : CubeGadget J) :
    (childMatrix F : Matrix (I × J) (I × J) ℚ).det = F.H.det ^ Fintype.card I := by
  rw [childMatrix_eq_reindex, Matrix.det_reindex_self, Matrix.det_blockDiagonal]
  simp

/-- Split the coordinates into all child anchors and the remaining coordinates. -/
def anchorSplit (a : J) : (I ⊕ (I × {j : J // j ≠ a})) ≃ (I × J) where
  toFun := Sum.elim (fun p => (p, a)) (fun r => (r.1, r.2.1))
  invFun := fun r => if h : r.2 = a then Sum.inl r.1 else Sum.inr (r.1, ⟨r.2, h⟩)
  left_inv := by
    intro r
    rcases r with p | ⟨p, k, hk⟩
    · simp
    · simp [hk]
  right_inv := by
    rintro ⟨p, k⟩
    by_cases h : k = a
    · simp [h]
    · simp [h]

omit [Fintype J] in
/-- In the split coordinates the embedded outer matrix is `diag(G.H, 1)`. -/
theorem anchorMatrix_submatrix (G : CubeGadget I) (a : J) :
    (anchorMatrix G a).submatrix (anchorSplit (I := I) a) (anchorSplit (I := I) a) =
      Matrix.fromBlocks G.H 0 0 (1 : Matrix (I × {j : J // j ≠ a})
        (I × {j : J // j ≠ a}) ℚ) := by
  ext r c
  rcases r with p | ⟨p, k, hk⟩ <;> rcases c with q | ⟨q, l, hl⟩
  · simp [Matrix.submatrix, anchorSplit, anchorMatrix]
  · simp [Matrix.submatrix, anchorSplit, anchorMatrix, hl, Ne.symm hl, Prod.mk.injEq]
  · simp [Matrix.submatrix, anchorSplit, anchorMatrix, hk]
  · simp [Matrix.submatrix, anchorSplit, anchorMatrix, hl, Matrix.one_apply,
      Prod.mk.injEq, Subtype.mk.injEq]

@[local simp] theorem det_anchorMatrix (G : CubeGadget I) (a : J) :
    (anchorMatrix G a).det = G.H.det := by
  rw [← Matrix.det_submatrix_equiv_self (anchorSplit (I := I) a),
    anchorMatrix_submatrix, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

/-- Determinant factorization for composition. -/
@[local simp] theorem det_composeMatrix (G : CubeGadget I) (F : CubeGadget J) :
    (composeMatrix G F).det = G.H.det * F.H.det ^ Fintype.card I := by
  rw [composeMatrix, Matrix.det_mul, det_childMatrix, det_anchorMatrix, mul_comm]

/-- Explicit entries of the composed matrix. -/
theorem composeMatrix_apply (G : CubeGadget I) (F : CubeGadget J)
    (p q : I) (k l : J) :
    composeMatrix G F (p, k) (q, l) =
      if l = F.anchor then F.H k F.anchor * G.H p q
      else if p = q then F.H k l else 0 := by
  simp only [composeMatrix, Matrix.mul_apply, Fintype.sum_prod_type,
    childMatrix, ite_mul, zero_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
  by_cases hl : l = F.anchor
  · simp [anchorMatrix, hl, mul_ite]
  · by_cases hpq : p = q
    · simp [anchorMatrix, hl, hpq, mul_ite]
    · simp [anchorMatrix, hl, hpq, mul_ite, Prod.mk.injEq]

/-- The child factor acts independently on each block. -/
theorem childMatrix_mulVec (F : CubeGadget J) (x : I × J → ℚ) (p : I) (k : J) :
    (childMatrix F *ᵥ x) (p, k) = (F.H *ᵥ (fun l => x (p, l))) k := by
  simp [Matrix.mulVec, dotProduct, childMatrix, Fintype.sum_prod_type, ite_mul]

/-- The embedded outer factor only changes child anchors. -/
theorem anchorMatrix_mulVec (G : CubeGadget I) (a : J) (x : I × J → ℚ)
    (p : I) (k : J) :
    (anchorMatrix G a *ᵥ x) (p, k) =
      if k = a then (G.H *ᵥ (fun q => x (q, a))) p else x (p, k) := by
  by_cases hk : k = a
  · subst k
    have hrow : anchorMatrix G a (p, a) =
        (fun c : I × J => if c.2 = a then G.H p c.1 else 0) := by
      funext c
      rcases c with ⟨q, l⟩
      by_cases hl : l = a
      · simp [anchorMatrix, hl]
      · simp [anchorMatrix, hl, Ne.symm hl, Prod.mk.injEq]
    change (∑ c, anchorMatrix G a (p, a) c * x c) = _
    rw [hrow]
    simp [Fintype.sum_prod_type, ite_mul, Matrix.mulVec, dotProduct]
  · have hrow : anchorMatrix G a (p, k) = (1 : Matrix (I × J) (I × J) ℚ) (p, k) := by
      funext c
      rcases c with ⟨q, l⟩
      by_cases hl : l = a
      · simp [anchorMatrix, hl, hk, Prod.mk.injEq]
      · simp [anchorMatrix, hl, Matrix.one_apply]
    change (∑ c, anchorMatrix G a (p, k) c * x c) = _
    rw [hrow, ite_eq_right hk]
    exact congrFun (Matrix.one_mulVec x) (p, k)

/-- Input to child `p` after applying the outer matrix to all anchors. -/
def childInput (G : CubeGadget I) (F : CubeGadget J) (x : I × J → ℚ) (p : I) : J → ℚ :=
  fun k => if k = F.anchor then (G.H *ᵥ (fun q => x (q, F.anchor))) p else x (p, k)

@[local simp] theorem childInput_anchor (G : CubeGadget I) (F : CubeGadget J)
    (x : I × J → ℚ) (p : I) :
    childInput G F x p F.anchor = (G.H *ᵥ (fun q => x (q, F.anchor))) p := by
  simp [childInput]

@[local simp] theorem childInput_of_ne (G : CubeGadget I) (F : CubeGadget J)
    (x : I × J → ℚ) (p : I) {k : J} (hk : k ≠ F.anchor) :
    childInput G F x p k = x (p, k) := by
  simp [childInput, hk]

/-- The composed image in each block is precisely the child image. -/
theorem composeMatrix_mulVec (G : CubeGadget I) (F : CubeGadget J)
    (x : I × J → ℚ) (p : I) (k : J) :
    (composeMatrix G F *ᵥ x) (p, k) = (F.H *ᵥ childInput G F x p) k := by
  rw [composeMatrix, ← Matrix.mulVec_mulVec, childMatrix_mulVec]
  congr 2
  funext l
  exact anchorMatrix_mulVec G F.anchor x p l

/-- Column sums compose by multiplication of the two heights. -/
theorem composeMatrix_sum_mulVec (G : CubeGadget I) (F : CubeGadget J)
    (x : I × J → ℚ) :
    ∑ r, (composeMatrix G F *ᵥ x) r =
      (G.height * F.height) * x (G.anchor, F.anchor) := by
  rw [Fintype.sum_prod_type]
  simp_rw [composeMatrix_mulVec, F.sum_mulVec, childInput_anchor]
  rw [← Finset.mul_sum, G.sum_mulVec]
  ring

/-- Short output bounds every intermediate child anchor, even when the original
anchor coordinate is not integral. -/
theorem composeMatrix_child_anchor_lt_one (G : CubeGadget I) (F : CubeGadget J)
    (x : I × J → ℚ)
    (hint : ∀ r, r ≠ (G.anchor, F.anchor) → ∃ z : ℤ, x r = (z : ℚ))
    (hshort : ∀ r, |(composeMatrix G F *ᵥ x) r| < 1) (p : I) :
    |(G.H *ᵥ (fun q => x (q, F.anchor))) p| < 1 := by
  rw [← childInput_anchor G F x p]
  apply F.strip (childInput G F x p)
  · intro k hk
    rw [childInput_of_ne G F x p hk]
    exact hint (p, k) (fun h => hk (congrArg Prod.snd h))
  · intro k
    rw [← composeMatrix_mulVec]
    exact hshort (p, k)

/-- The strip property is preserved by composition. -/
theorem composeMatrix_strip (G : CubeGadget I) (F : CubeGadget J)
    (x : I × J → ℚ)
    (hint : ∀ r, r ≠ (G.anchor, F.anchor) → ∃ z : ℤ, x r = (z : ℚ))
    (hshort : ∀ r, |(composeMatrix G F *ᵥ x) r| < 1) :
    |x (G.anchor, F.anchor)| < 1 := by
  apply G.strip (fun p => x (p, F.anchor))
  · intro p hp
    exact hint (p, F.anchor) (fun h => hp (congrArg Prod.fst h))
  · exact composeMatrix_child_anchor_lt_one G F x hint hshort

/-- Admissibility is preserved by composition: outer admissibility first kills
all anchor inputs, and then child admissibility kills each entire block. -/
theorem composeMatrix_admissible (G : CubeGadget I) (F : CubeGadget J)
    (z : I × J → ℤ)
    (hshort : ∀ r, |(composeMatrix G F *ᵥ (fun s => (z s : ℚ))) r| < 1) : z = 0 := by
  have hanchors : (fun p => z (p, F.anchor)) = 0 :=
    G.admissible _ (composeMatrix_child_anchor_lt_one G F (fun r => (z r : ℚ))
      (fun r _ => ⟨z r, rfl⟩) hshort)
  have hzanchor : ∀ p, z (p, F.anchor) = 0 := fun p => congrFun hanchors p
  have hinput (p : I) : childInput G F (fun r => (z r : ℚ)) p =
      (fun k => (z (p, k) : ℚ)) := by
    funext k
    by_cases hk : k = F.anchor
    · subst k
      simp [childInput, hzanchor, Matrix.mulVec, dotProduct]
    · simp [childInput, hk]
  have hblock (p : I) : (fun k => z (p, k)) = 0 := by
    apply F.admissible
    intro k
    have h := hshort (p, k)
    rw [composeMatrix_mulVec, hinput] at h
    exact h
  funext r
  exact congrFun (hblock r.1) r.2

/-- Compose an outer cube gadget with identical child gadgets. -/
def compose (G : CubeGadget I) (F : CubeGadget J) : CubeGadget (I × J) where
  H := composeMatrix G F
  anchor := (G.anchor, F.anchor)
  height := G.height * F.height
  height_pos := mul_pos G.height_pos F.height_pos
  det_pos := by
    rw [det_composeMatrix]
    exact mul_pos G.det_pos (pow_pos F.det_pos _)
  sum_mulVec := composeMatrix_sum_mulVec G F
  strip := composeMatrix_strip G F
  admissible := composeMatrix_admissible G F

@[local simp] theorem compose_H (G : CubeGadget I) (F : CubeGadget J) :
    (G.compose F).H = composeMatrix G F := rfl

@[local simp] theorem compose_anchor (G : CubeGadget I) (F : CubeGadget J) :
    (G.compose F).anchor = (G.anchor, F.anchor) := rfl

@[local simp] theorem compose_height (G : CubeGadget I) (F : CubeGadget J) :
    (G.compose F).height = G.height * F.height := rfl

@[local simp↓] theorem compose_det (G : CubeGadget I) (F : CubeGadget J) :
    (G.compose F).H.det = G.H.det * F.H.det ^ Fintype.card I :=
  det_composeMatrix G F

theorem compose_apply (G : CubeGadget I) (F : CubeGadget J)
    (p q : I) (k l : J) :
    (G.compose F).H (p, k) (q, l) =
      if l = F.anchor then F.H k F.anchor * G.H p q
      else if p = q then F.H k l else 0 :=
  composeMatrix_apply G F p q k l

theorem compose_mulVec (G : CubeGadget I) (F : CubeGadget J)
    (x : I × J → ℚ) (p : I) (k : J) :
    ((G.compose F).H *ᵥ x) (p, k) = (F.H *ᵥ childInput G F x p) k :=
  composeMatrix_mulVec G F x p k

omit [DecidableEq J] in
/-- Reindexing a matrix transports its action on coordinate vectors. -/
theorem reindexMatrix_mulVec (G : CubeGadget I) (e : I ≃ J) (x : J → ℚ) :
    Matrix.reindex e e G.H *ᵥ x = (G.H *ᵥ (x ∘ e)) ∘ e.symm :=
  Matrix.submatrix_mulVec_equiv G.H x e.symm e.symm

/-- Transport a cube gadget through an arbitrary bijection of coordinates. -/
def reindex (G : CubeGadget I) (e : I ≃ J) : CubeGadget J where
  H := Matrix.reindex e e G.H
  anchor := e G.anchor
  height := G.height
  height_pos := G.height_pos
  det_pos := by rw [Matrix.det_reindex_self]; exact G.det_pos
  sum_mulVec := by
    intro x
    rw [reindexMatrix_mulVec]
    change (∑ j, (G.H *ᵥ (x ∘ e)) (e.symm j)) = _
    rw [Equiv.sum_comp]
    exact G.sum_mulVec (x ∘ e)
  strip := by
    intro x hint hshort
    apply G.strip (x ∘ e)
    · intro i hi
      exact hint (e i) (fun h => hi (e.injective h))
    · intro i
      have h := hshort (e i)
      rw [reindexMatrix_mulVec] at h
      simpa only [Function.comp_apply, Equiv.symm_apply_apply] using h
  admissible := by
    intro z hshort
    have hzero : (fun i => z (e i)) = 0 := by
      apply G.admissible
      intro i
      have h := hshort (e i)
      rw [reindexMatrix_mulVec] at h
      rw [Function.comp_apply, Equiv.symm_apply_apply] at h
      exact h
    funext j
    simpa only [Pi.zero_apply, Equiv.apply_symm_apply] using congrFun hzero (e.symm j)

@[local simp] theorem reindex_H (G : CubeGadget I) (e : I ≃ J) :
    (G.reindex e).H = Matrix.reindex e e G.H := rfl

@[local simp] theorem reindex_anchor (G : CubeGadget I) (e : I ≃ J) :
    (G.reindex e).anchor = e G.anchor := rfl

@[local simp] theorem reindex_height (G : CubeGadget I) (e : I ≃ J) :
    (G.reindex e).height = G.height := rfl

@[local simp↓] theorem reindex_det (G : CubeGadget I) (e : I ≃ J) :
    (G.reindex e).H.det = G.H.det := Matrix.det_reindex_self e G.H

theorem reindex_apply (G : CubeGadget I) (e : I ≃ J) (i j : J) :
    (G.reindex e).H i j = G.H (e.symm i) (e.symm j) := rfl

theorem reindex_mulVec (G : CubeGadget I) (e : I ≃ J) (x : J → ℚ) (j : J) :
    ((G.reindex e).H *ᵥ x) j = (G.H *ᵥ (x ∘ e)) (e.symm j) :=
  congrFun (reindexMatrix_mulVec G e x) j

/-- The one-coordinate leaf gadget. -/
def leaf : CubeGadget PUnit.{u + 1} where
  H := 1
  anchor := PUnit.unit
  height := 1
  height_pos := by norm_num
  det_pos := by simp
  sum_mulVec := by intro x; simp
  strip := by
    intro x _ hshort
    simpa using hshort PUnit.unit
  admissible := by
    intro z hshort
    funext i
    have h : |(z i : ℚ)| < 1 := by simpa using hshort i
    have hz : |z i| < (1 : ℤ) := by exact_mod_cast h
    exact Int.abs_lt_one_iff.mp hz

@[local simp] theorem leaf_H : leaf.H = (1 : Matrix PUnit.{u + 1} PUnit ℚ) := rfl

@[local simp] theorem leaf_anchor : leaf.anchor = PUnit.unit.{u + 1} := rfl

@[local simp] theorem leaf_height : leaf.{u}.height = 1 := rfl

@[local simp] theorem leaf_det : leaf.{u}.H.det = 1 := Matrix.det_one

/-- Leaves of a depth-`k` regular tree. At depth zero there is a single leaf. -/
def IterIndex (I : Type u) : ℕ → Type u
  | 0 => PUnit
  | k + 1 => I × IterIndex I k

/-- Finite enumeration of the recursive index family. -/
instance instFintypeIterIndex : (k : ℕ) → Fintype (IterIndex I k)
  | 0 => inferInstanceAs (Fintype PUnit)
  | k + 1 => by
      letI := instFintypeIterIndex k
      exact inferInstanceAs (Fintype (I × IterIndex I k))

/-- Decidable equality on the recursive index family. -/
instance instDecidableEqIterIndex : (k : ℕ) → DecidableEq (IterIndex I k)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | k + 1 => by
      letI := instDecidableEqIterIndex k
      exact inferInstanceAs (DecidableEq (I × IterIndex I k))

omit [DecidableEq I] in
/-- The number of leaves is the branching number raised to the depth. -/
@[local simp] theorem card_iterIndex (k : ℕ) :
    Fintype.card (IterIndex I k) = Fintype.card I ^ k := by
  induction k with
  | zero =>
    rw [pow_zero]
    exact Fintype.card_punit
  | succ k ih =>
    change Fintype.card (I × IterIndex I k) = Fintype.card I ^ (k + 1)
    rw [Fintype.card_prod, ih, pow_succ']

/-- The coordinate obtained by choosing the anchor at every level. -/
def iterAnchor (a : I) : (k : ℕ) → IterIndex I k
  | 0 => PUnit.unit
  | k + 1 => (a, iterAnchor a k)

/-- Iterate the same outer gadget, starting from the one-point leaf. -/
def iterate (G : CubeGadget I) : (k : ℕ) → CubeGadget (IterIndex I k)
  | 0 => leaf
  | k + 1 => G.compose (iterate G k)

@[local simp] theorem iterate_zero (G : CubeGadget I) : G.iterate 0 = leaf := rfl

@[local simp] theorem iterate_succ (G : CubeGadget I) (k : ℕ) :
    G.iterate (k + 1) = G.compose (G.iterate k) := rfl

@[local simp] theorem iterate_anchor (G : CubeGadget I) (k : ℕ) :
    (G.iterate k).anchor = iterAnchor G.anchor k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (G.anchor, (G.iterate k).anchor) = (G.anchor, iterAnchor G.anchor k)
    rw [ih]

/-- Heights multiply along a root-to-leaf path. -/
@[local simp] theorem iterate_height (G : CubeGadget I) (k : ℕ) :
    (G.iterate k).height = G.height ^ k := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih, pow_succ']

/-- The determinant exponent counts all internal vertices of the tree. -/
@[local simp↓] theorem iterate_det (G : CubeGadget I) (k : ℕ) :
    (G.iterate k).H.det = G.H.det ^ cycleDetExponent (Fintype.card I) k := by
  induction k with
  | zero =>
    change (1 : Matrix PUnit.{u + 1} PUnit ℚ).det = _
    rw [Matrix.det_one, cycleDetExponent_zero, pow_zero]
  | succ k ih =>
    change (G.compose (G.iterate k)).H.det = _
    rw [compose_det, ih, cycleDetExponent_succ_mul, pow_add, pow_one,
      mul_comm (Fintype.card I) (cycleDetExponent (Fintype.card I) k), pow_mul]

/-- The determinant formula with the finite geometric sum written explicitly. -/
theorem iterate_det_sum (G : CubeGadget I) (k : ℕ) :
    (G.iterate k).H.det = G.H.det ^ (∑ j ∈ Finset.range k, Fintype.card I ^ j) := by
  simpa only [cycleDetExponent] using iterate_det G k

theorem iterate_sum_mulVec (G : CubeGadget I) (k : ℕ) (x : IterIndex I k → ℚ) :
    ∑ i, ((G.iterate k).H *ᵥ x) i = G.height ^ k * x (iterAnchor G.anchor k) := by
  simpa only [iterate_height, iterate_anchor] using (G.iterate k).sum_mulVec x

theorem iterate_strip (G : CubeGadget I) (k : ℕ) (x : IterIndex I k → ℚ)
    (hint : ∀ i, i ≠ iterAnchor G.anchor k → ∃ z : ℤ, x i = (z : ℚ))
    (hshort : ∀ i, |((G.iterate k).H *ᵥ x) i| < 1) :
    |x (iterAnchor G.anchor k)| < 1 := by
  simpa only [iterate_anchor] using
    (G.iterate k).strip x (by simpa only [iterate_anchor] using hint) hshort

theorem iterate_admissible (G : CubeGadget I) (k : ℕ) (z : IterIndex I k → ℤ)
    (hshort : ∀ i, |((G.iterate k).H *ᵥ (fun j => (z j : ℚ))) i| < 1) : z = 0 :=
  (G.iterate k).admissible z hshort

/-- A standard finite-index version, convenient for taking matrix minors. -/
noncomputable def iterateFin (G : CubeGadget I) (k : ℕ) :
    CubeGadget (Fin (Fintype.card I ^ k)) :=
  (G.iterate k).reindex (Fintype.equivFinOfCardEq (card_iterIndex (I := I) k))

@[local simp] theorem iterateFin_height (G : CubeGadget I) (k : ℕ) :
    (G.iterateFin k).height = G.height ^ k := by
  simp [iterateFin]

@[local simp↓] theorem iterateFin_det (G : CubeGadget I) (k : ℕ) :
    (G.iterateFin k).H.det = G.H.det ^ cycleDetExponent (Fintype.card I) k := by
  simp [iterateFin]

theorem iterateFin_det_sum (G : CubeGadget I) (k : ℕ) :
    (G.iterateFin k).H.det = G.H.det ^ (∑ j ∈ Finset.range k, Fintype.card I ^ j) := by
  simpa only [cycleDetExponent] using iterateFin_det G k

/-- An existential API requiring no reference to the recursive index family. -/
theorem exists_iterate_fin (G : CubeGadget I) (k : ℕ) :
    ∃ F : CubeGadget (Fin (Fintype.card I ^ k)),
      F.height = G.height ^ k ∧
      F.H.det = G.H.det ^ (∑ j ∈ Finset.range k, Fintype.card I ^ j) :=
  ⟨G.iterateFin k, iterateFin_height G k, iterateFin_det_sum G k⟩

/-- A version with an explicitly supplied branching cardinality. This fixes the
`Fin` index at construction time, avoiding transport of dependent gadget fields.
For `G : CubeGadget (Fin b)`, supply `Fintype.card_fin b`. -/
noncomputable def iterateFinOfCardEq (G : CubeGadget I) {b : ℕ}
    (hcard : Fintype.card I = b) (k : ℕ) : CubeGadget (Fin (b ^ k)) :=
  (G.iterate k).reindex (Fintype.equivFinOfCardEq (by rw [card_iterIndex, hcard]))

@[local simp] theorem iterateFinOfCardEq_height (G : CubeGadget I) {b : ℕ}
    (hcard : Fintype.card I = b) (k : ℕ) :
    (G.iterateFinOfCardEq hcard k).height = G.height ^ k := by
  simp [iterateFinOfCardEq]

@[local simp↓] theorem iterateFinOfCardEq_det (G : CubeGadget I) {b : ℕ}
    (hcard : Fintype.card I = b) (k : ℕ) :
    (G.iterateFinOfCardEq hcard k).H.det = G.H.det ^ cycleDetExponent b k := by
  simp [iterateFinOfCardEq, hcard]

theorem iterateFinOfCardEq_det_sum (G : CubeGadget I) {b : ℕ}
    (hcard : Fintype.card I = b) (k : ℕ) :
    (G.iterateFinOfCardEq hcard k).H.det =
      G.H.det ^ (∑ j ∈ Finset.range k, b ^ j) := by
  simpa only [cycleDetExponent] using iterateFinOfCardEq_det G hcard k

/-- The explicit-cardinality existential API. In particular, cycle gadgets give
an output indexed by exactly `Fin (b ^ k)`. -/
theorem exists_iterate_fin_of_card_eq (G : CubeGadget I) {b : ℕ}
    (hcard : Fintype.card I = b) (k : ℕ) :
    ∃ F : CubeGadget (Fin (b ^ k)), F.height = G.height ^ k ∧
      F.H.det = G.H.det ^ (∑ j ∈ Finset.range k, b ^ j) :=
  ⟨G.iterateFinOfCardEq hcard k, iterateFinOfCardEq_height G hcard k,
    iterateFinOfCardEq_det_sum G hcard k⟩

end CubeGadget

/-
# Cube-admissible minors of cube gadgets

After moving the anchor to the last coordinate, delete the last row and column.
The row-sum shear has determinant one and gives the determinant factorization
`det H = det B * height`.  The remaining columns are exactly the zero-sum lift
of `B`, so gadget admissibility implies `CubeAdmissible B`.

Only the sum law and admissibility of the gadget are used; its strip property
is not needed.
-/

open Matrix Finset

/-- The shear with identity top block preserves determinants. -/
private theorem gadgetMinor_det_shear {r : ℕ} :
    (snfShear (1 : Matrix (Fin r) (Fin r) ℚ)).det = 1 := by
  rw [Matrix.det_succ_column _ (Fin.last r), Fin.sum_univ_castSucc]
  simpa [snfShear, Fin.succAbove_last, Matrix.submatrix, pow_add, ← mul_pow] using
    (show (Matrix.of fun i j => (1 : Matrix (Fin r) (Fin r) ℚ) i j).det = 1 from
      Matrix.det_one)

/-- Summing the rows isolates the anchor entry and factors off the height. -/
theorem gadgetMinor_det_mul_height {r : ℕ}
    (H : Matrix (Fin (r + 1)) (Fin (r + 1)) ℚ) (h : ℚ)
    (hsum : ∀ x : Fin (r + 1) → ℚ, ∑ i, (H *ᵥ x) i = h * x (Fin.last r)) :
    H.det = (H.submatrix Fin.castSucc Fin.castSucc).det * h := by
  let S := snfShear (1 : Matrix (Fin r) (Fin r) ℚ)
  have hcol (j : Fin (r + 1)) : ∑ i, H i j = if j = Fin.last r then h else 0 := by
    have hx := hsum (fun k => if k = j then 1 else 0)
    simpa [Matrix.mulVec, dotProduct, mul_ite, eq_comm] using hx
  have htop (i : Fin r) (j : Fin (r + 1)) : (S * H) i.castSucc j = H i.castSucc j := by
    simp [S, snfShear, Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.one_apply]
  have hlast (j : Fin (r + 1)) :
      (S * H) (Fin.last r) j = if j = Fin.last r then h else 0 := by
    simpa [S, snfShear, Matrix.mul_apply] using hcol j
  have hminor : (S * H).submatrix Fin.castSucc Fin.castSucc =
      H.submatrix Fin.castSucc Fin.castSucc := by
    ext i j
    exact htop i j.castSucc
  have hsign : (-1 : ℚ) ^ (r + r) = 1 := (show Even (r + r) from ⟨r, rfl⟩).neg_one_pow
  calc
    H.det = (S * H).det := by
      rw [Matrix.det_mul, gadgetMinor_det_shear, one_mul]
    _ = (H.submatrix Fin.castSucc Fin.castSucc).det * h := by
      rw [Matrix.det_succ_row _ (Fin.last r), Fin.sum_univ_castSucc]
      simp [hlast, Fin.succAbove_last, hminor, hsign, mul_comm]

/-- A zero anchor input produces the zero-sum lift of the top minor's output. -/
theorem gadgetMinor_mulVec_snoc {r : ℕ}
    (H : Matrix (Fin (r + 1)) (Fin (r + 1)) ℚ) (h : ℚ)
    (hsum : ∀ x : Fin (r + 1) → ℚ, ∑ i, (H *ᵥ x) i = h * x (Fin.last r))
    (x : Fin r → ℚ) :
    H *ᵥ Fin.snoc x 0 =
      Fin.snoc ((H.submatrix Fin.castSucc Fin.castSucc) *ᵥ x)
        (-∑ i, ((H.submatrix Fin.castSucc Fin.castSucc) *ᵥ x) i) := by
  have htop (i : Fin r) : (H *ᵥ Fin.snoc x 0) i.castSucc =
      ((H.submatrix Fin.castSucc Fin.castSucc) *ᵥ x) i := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
  have htotal := hsum (Fin.snoc x 0)
  simp only [Fin.sum_univ_castSucc, htop, Fin.snoc_last, mul_zero] at htotal
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    linarith
  · simpa only [Fin.snoc_castSucc] using htop j

/-- Anchor-last minor extraction, stated without the unused strip hypothesis. -/
theorem gadget_minor_of_sum_mulVec {r : ℕ}
    (H : Matrix (Fin (r + 1)) (Fin (r + 1)) ℚ) (h : ℚ)
    (hh : 0 < h) (hdet : 0 < H.det)
    (hsum : ∀ x : Fin (r + 1) → ℚ, ∑ i, (H *ᵥ x) i = h * x (Fin.last r))
    (hadm : ∀ z : Fin (r + 1) → ℤ,
      (∀ i, |(H *ᵥ (fun j => (z j : ℚ))) i| < 1) → z = 0) :
    let B := H.submatrix Fin.castSucc Fin.castSucc
    B.det ≠ 0 ∧ CubeAdmissible B ∧ |(B.det : ℝ)| = (H.det : ℝ) / (h : ℝ) := by
  let B := H.submatrix Fin.castSucc Fin.castSucc
  change B.det ≠ 0 ∧ CubeAdmissible B ∧ |(B.det : ℝ)| = (H.det : ℝ) / (h : ℝ)
  have hfactor : H.det = B.det * h := gadgetMinor_det_mul_height H h hsum
  have hBpos : 0 < B.det := (mul_pos_iff_of_pos_right hh).mp (hfactor ▸ hdet)
  refine ⟨ne_of_gt hBpos, ?_, ?_⟩
  · intro z hz htotal
    have hcast : (fun i => ((Fin.snoc z 0 : Fin (r + 1) → ℤ) i : ℚ)) =
        Fin.snoc (fun j => (z j : ℚ)) 0 := by
      simpa only [Function.comp_def, Int.cast_zero] using
        Fin.comp_snoc (fun t : ℤ => (t : ℚ)) z 0
    have hzero := hadm (Fin.snoc z 0) (by
      rw [hcast, gadgetMinor_mulVec_snoc H h hsum]
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [B, Matrix.mulVec, dotProduct, abs_neg] using htotal
      · simpa [B, Matrix.mulVec, dotProduct] using hz j)
    funext j
    simpa using congrFun hzero j.castSucc
  · have hBposR : (0 : ℝ) < (B.det : ℝ) := by exact_mod_cast hBpos
    have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
    rw [abs_of_pos hBposR]
    apply (eq_div_iff hhR).mpr
    exact_mod_cast hfactor.symm

/-- Every cube gadget with at least two coordinates has a positive-dimensional
nonsingular cube-admissible minor whose determinant is its determinant/height
ratio.  The index type and the location of the anchor are arbitrary. -/
theorem exists_gadget_minor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : CubeGadget ι) (hcard : 2 ≤ Fintype.card ι) :
    ∃ r : ℕ, 0 < r ∧ ∃ B : Matrix (Fin r) (Fin r) ℚ,
      B.det ≠ 0 ∧ CubeAdmissible B ∧
        |(B.det : ℝ)| = (G.H.det : ℝ) / (G.height : ℝ) := by
  classical
  let r := Fintype.card ι - 1
  have hr : 0 < r := by dsimp [r]; omega
  have hcardeq : Fintype.card ι = r + 1 := by dsimp [r]; omega
  let f : ι ≃ Fin (r + 1) := Fintype.equivFinOfCardEq hcardeq
  let e : Fin (r + 1) ≃ ι := (Equiv.swap (Fin.last r) (f G.anchor)).trans f.symm
  have he : e (Fin.last r) = G.anchor := by simp [e]
  let H := G.H.submatrix e e
  have hdet : H.det = G.H.det := Matrix.det_submatrix_equiv_self e G.H
  have hsum (x : Fin (r + 1) → ℚ) :
      ∑ i, (H *ᵥ x) i = G.height * x (Fin.last r) := by
    dsimp only [H]
    rw [Matrix.submatrix_mulVec_equiv]
    change (∑ i, (G.H *ᵥ (x ∘ e.symm)) (e i)) = _
    rw [e.sum_comp, G.sum_mulVec, Function.comp_apply, ← he, e.symm_apply_apply]
  have hadm (z : Fin (r + 1) → ℤ)
      (hz : ∀ i, |(H *ᵥ (fun j => (z j : ℚ))) i| < 1) : z = 0 := by
    have hzero := G.admissible (z ∘ e.symm) (by
      intro i
      have hi := hz (e.symm i)
      dsimp only [H] at hi
      rw [Matrix.submatrix_mulVec_equiv] at hi
      rw [Function.comp_apply, e.apply_symm_apply] at hi
      exact hi)
    funext i
    simpa using congrFun hzero (e i)
  refine ⟨r, hr, H.submatrix Fin.castSucc Fin.castSucc, ?_⟩
  simpa only [hdet] using
    gadget_minor_of_sum_mulVec H G.height G.height_pos (hdet.symm ▸ G.det_pos) hsum hadm

/- # Contradiction to a uniform distinct-subset-sums bound -/

open Finset Matrix

theorem no_uniform_subset_bound : ¬ UniformSubsetBound := by
  intro hu
  obtain ⟨c, hc, hbound⟩ := lattice_lower_bound hu
  obtain ⟨k, hk, b, hb, hodd, hsmall⟩ := exists_odd_cycle_small_normalized_det hc
  obtain ⟨F, hheight, hdet⟩ : ∃ F : CubeGadget (Fin (b ^ k)),
      F.height = (3 / 2 : ℚ) ^ k ∧
      F.H.det = (1 + (1 / 2 : ℚ) ^ b) ^ (∑ j ∈ range k, b ^ j) := by
    simpa only [Fintype.card_fin, oddCycleGadget_height, oddCycleGadget_det] using
      CubeGadget.exists_iterate_fin_of_card_eq
        (oddCycleGadget b hb hodd) (Fintype.card_fin b) k
  have hcard : 2 ≤ Fintype.card (Fin (b ^ k)) := by
    rw [Fintype.card_fin]
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    have hp : 0 < b ^ l := pow_pos (by omega : 0 < b) _
    rw [pow_succ]
    nlinarith
  obtain ⟨r, hr, B, hB, hadm, hratio⟩ := exists_gadget_minor F hcard
  have hlow := hbound r hr B hB hadm
  rw [hratio, hdet, hheight] at hlow
  norm_num only [Rat.cast_pow, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] at hlow
  exact (not_le_of_gt hsmall) hlow

end ErdosCounter

/-- **Disproof of Erdős Problem 1 on distinct subset sums.** There is no real number $C > 0$
such that for every natural number $N \ne 0$ and every finite set $A \subseteq \{1, \dots, N\}$
whose distinct subsets have distinct sums, $C \cdot 2^{|A|} < N$. -/
public theorem conjecture_refuted : ¬ conjecture := by
  intro h
  apply ErdosCounter.no_uniform_subset_bound
  rcases h with ⟨C, hC, h⟩
  refine ⟨C, hC, ?_⟩
  intro N A hsub hinj hN
  exact h N A ⟨hsub, hinj⟩ hN

end MathlibExt.NumberTheory.ErdosProblem1Wanted
