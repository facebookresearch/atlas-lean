/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Finite matrix discrepancy

The finite sign minimum uses the actual coordinate supremum norm of a matrix
product. The implemented core is reference-guided by the retained Codex
`audit_c1a_final` Komlós model; current API author is Codex `finish_c32_saved`.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace MatrixDiscrepancy

noncomputable section

variable {m n : ℕ}

/-- **Signs indexed by two elements.** For $s \in \{0, 1\}$, the associated real sign is $-1$
if $s = 0$ and $1$ if $s = 1$. -/
def signValue (s : Fin 2) : ℝ := if s = 0 then -1 else 1

@[simp] theorem abs_signValue (s : Fin 2) : |signValue s| = 1 := by
  unfold signValue
  split_ifs <;> norm_num

/-- **Discrepancy of a real matrix.** For a real $m \times n$ matrix $A$, the discrepancy of $A$
is the infimum, over all sign vectors $x \in \{-1, 1\}^n$, of the maximum norm
$\|Ax\|_\infty = \max_i |(Ax)_i|$ (which is $0$ when $m = 0$), taken in $[0, \infty]$. -/
def discrepancy (A : Matrix (Fin m) (Fin n) ℝ) : ENNReal :=
  ⨅ x : Fin n → Fin 2, ENNReal.ofReal ‖A.mulVec (fun j => signValue (x j))‖

/-- **Matrices with columns in the unit ball.** A real $m \times n$ matrix $A$ is column
admissible when every column of $A$ lies in the closed Euclidean unit ball, that is,
$\sum_{i=1}^{m} A_{ij}^2 \le 1$ for every column index $j$. -/
def ColumnAdmissible (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ j, ∑ i, (A i j) ^ 2 ≤ 1

/-- **Komlós constant in a fixed dimension.** For a natural number $n$, this is the supremum of
the discrepancy of $A$ over all real $n \times n$ matrices $A$ whose columns all have Euclidean
norm at most $1$, taken in $[0, \infty]$. The definition also applies to $n = 0$. -/
def dimensionConstant (n : ℕ) : ENNReal :=
  ⨆ A : {A : Matrix (Fin n) (Fin n) ℝ // ColumnAdmissible A}, discrepancy A.1

/-- **Komlós constant.** The Komlós constant is the supremum, over all integers $n \ge 1$, of the
Komlós constant in dimension $n$, namely the supremum of the discrepancy of $A$ over all real
$n \times n$ matrices $A$ whose columns all have Euclidean norm at most $1$. It is taken in
$[0, \infty]$. -/
def komlosConstant : ENNReal :=
  ⨆ n : {n : ℕ // 1 ≤ n}, dimensionConstant n.1

theorem discrepancy_le_signing (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → Fin 2) :
    discrepancy A ≤ ENNReal.ofReal ‖A.mulVec (fun j => signValue (x j))‖ :=
  iInf_le _ x

/-- **The discrepancy is attained.** For every real $m \times n$ matrix $A$, including the cases
$m = 0$ and $n = 0$, there is a sign vector $x \in \{-1, 1\}^n$ such that the discrepancy of $A$
equals $\|Ax\|_\infty$. -/
theorem discrepancy_attained (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ x : Fin n → Fin 2,
      discrepancy A = ENNReal.ofReal ‖A.mulVec (fun j => signValue (x j))‖ := by
  obtain ⟨x, hx⟩ := exists_eq_ciInf_of_finite
    (f := fun x : Fin n → Fin 2 => ENNReal.ofReal ‖A.mulVec (fun j => signValue (x j))‖)
  exact ⟨x, hx.symm⟩

theorem discrepancy_isLeast (A : Matrix (Fin m) (Fin n) ℝ) :
    IsLeast (Set.range (fun x : Fin n → Fin 2 =>
      ENNReal.ofReal ‖A.mulVec (fun j => signValue (x j))‖)) (discrepancy A) := by
  obtain ⟨x, hx⟩ := discrepancy_attained A
  refine ⟨⟨x, hx.symm⟩, ?_⟩
  rintro y ⟨z, rfl⟩
  exact discrepancy_le_signing A z

theorem discrepancy_le_iff (A : Matrix (Fin m) (Fin n) ℝ) (r : ENNReal) :
    discrepancy A ≤ r ↔
      ∃ x : Fin n → Fin 2, ENNReal.ofReal ‖A.mulVec (fun j => signValue (x j))‖ ≤ r := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := discrepancy_attained A
    exact ⟨x, hx ▸ h⟩
  · rintro ⟨x, hx⟩
    exact (discrepancy_le_signing A x).trans hx

theorem columnAdmissible_iff_euclidean (A : Matrix (Fin m) (Fin n) ℝ) :
    ColumnAdmissible A ↔
      ∀ j, ‖(WithLp.toLp 2 (fun i => A i j) : EuclideanSpace ℝ (Fin m))‖ ≤ 1 := by
  simp [ColumnAdmissible, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs,
    Real.sqrt_le_one]

theorem entry_abs_le_one {A : Matrix (Fin m) (Fin n) ℝ} (hA : ColumnAdmissible A)
    (i : Fin m) (j : Fin n) : |A i j| ≤ 1 := by
  have h := le_trans (Finset.single_le_sum (fun k _ => sq_nonneg (A k j))
    (Finset.mem_univ i)) (hA j)
  nlinarith [sq_abs (A i j), abs_nonneg (A i j)]

theorem signing_norm_le_dimension {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : ColumnAdmissible A) (x : Fin n → Fin 2) :
    ‖A.mulVec (fun j => signValue (x j))‖ ≤ n := by
  apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg n)).2
  intro i
  change ‖∑ j, A i j * signValue (x j)‖ ≤ n
  calc
    ‖∑ j, A i j * signValue (x j)‖ ≤ ∑ j, ‖A i j * signValue (x j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      simpa [Real.norm_eq_abs, abs_mul] using entry_abs_le_one hA i j
    _ = n := by simp

theorem dimensionConstant_le_dimension (n : ℕ) : dimensionConstant n ≤ n := by
  apply iSup_le
  intro A
  exact (discrepancy_le_signing A.1 (fun _ => 0)).trans
    ((ENNReal.ofReal_le_ofReal (signing_norm_le_dimension A.2 _)).trans_eq (by simp))

theorem discrepancy_zero (m n : ℕ) :
    discrepancy (0 : Matrix (Fin m) (Fin n) ℝ) = 0 := by
  simp [discrepancy]

theorem columnAdmissible_zero (m n : ℕ) :
    ColumnAdmissible (0 : Matrix (Fin m) (Fin n) ℝ) := by
  simp [ColumnAdmissible]

theorem dimensionConstant_zero : dimensionConstant 0 = 0 := by
  exact le_antisymm (by simpa using dimensionConstant_le_dimension 0) bot_le

theorem discrepancy_unit : discrepancy (fun _ _ : Fin 1 => (1 : ℝ)) = 1 := by
  have hnorm (x : Fin 1 → Fin 2) :
      ‖Matrix.mulVec (fun _ _ : Fin 1 => (1 : ℝ)) (fun j => signValue (x j))‖ = 1 := by
    rw [Pi.norm_def]
    simp [Matrix.mulVec, dotProduct]
  simp [discrepancy, hnorm]

theorem columnAdmissible_unit : ColumnAdmissible (fun _ _ : Fin 1 => (1 : ℝ)) := by
  simp [ColumnAdmissible]

theorem one_le_dimensionConstant_one : 1 ≤ dimensionConstant 1 := by
  rw [dimensionConstant]
  apply le_iSup_of_le ⟨(fun _ _ : Fin 1 => (1 : ℝ)), columnAdmissible_unit⟩
  rw [discrepancy_unit]

theorem dimensionConstant_one : dimensionConstant 1 = 1 :=
  le_antisymm (by simpa using dimensionConstant_le_dimension 1) one_le_dimensionConstant_one

theorem one_le_komlosConstant : 1 ≤ komlosConstant := by
  apply le_iSup_of_le ⟨1, le_rfl⟩
  apply le_iSup_of_le ⟨(fun _ _ : Fin 1 => (1 : ℝ)), columnAdmissible_unit⟩
  rw [discrepancy_unit]

theorem dimensionConstant_le_iff (n : ℕ) (r : ENNReal) :
    dimensionConstant n ≤ r ↔
      ∀ A : Matrix (Fin n) (Fin n) ℝ, ColumnAdmissible A → discrepancy A ≤ r := by
  constructor
  · intro h A hA
    have hle : discrepancy A ≤ dimensionConstant n :=
      le_iSup (fun B : {B : Matrix (Fin n) (Fin n) ℝ // ColumnAdmissible B} =>
        discrepancy B.1) ⟨A, hA⟩
    exact hle.trans h
  · intro h
    exact iSup_le (fun A => h A.1 A.2)

theorem komlosConstant_le_iff (r : ENNReal) :
    komlosConstant ≤ r ↔ ∀ n : ℕ, 1 ≤ n → dimensionConstant n ≤ r := by
  constructor
  · intro h n hn
    have hle : dimensionConstant n ≤ komlosConstant :=
      le_iSup (fun k : {k : ℕ // 1 ≤ k} => dimensionConstant k.1) ⟨n, hn⟩
    exact hle.trans h
  · intro h
    exact iSup_le (fun n => h n.1 n.2)

theorem komlosConstant_lt_top_iff_uniform :
    komlosConstant < ⊤ ↔ ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, 1 ≤ n → dimensionConstant n ≤ ENNReal.ofReal c := by
  constructor
  · intro h
    refine ⟨komlosConstant.toReal + 1, ?_, ?_⟩
    · linarith [ENNReal.toReal_nonneg (a := komlosConstant)]
    · intro n hn
      have hle : dimensionConstant n ≤ komlosConstant :=
        le_iSup (fun k : {k : ℕ // 1 ≤ k} => dimensionConstant k.1) ⟨n, hn⟩
      refine hle.trans ?_
      calc
        komlosConstant = ENNReal.ofReal komlosConstant.toReal :=
          (ENNReal.ofReal_toReal h.ne).symm
        _ ≤ ENNReal.ofReal (komlosConstant.toReal + 1) :=
          ENNReal.ofReal_le_ofReal (by linarith)
  · rintro ⟨c, _hc, h⟩
    exact ((komlosConstant_le_iff _).2 h).trans_lt ENNReal.ofReal_lt_top

theorem komlosConstant_lt_top_iff_eventual :
    komlosConstant < ⊤ ↔ ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n → dimensionConstant n ≤ ENNReal.ofReal c := by
  constructor
  · intro h
    obtain ⟨c, hc, hbound⟩ := komlosConstant_lt_top_iff_uniform.1 h
    exact ⟨c, hc, 1, le_rfl, hbound⟩
  · rintro ⟨c, hc, N, _hN, hbound⟩
    refine komlosConstant_lt_top_iff_uniform.2 ⟨max c (N : ℝ),
      lt_of_lt_of_le hc (le_max_left _ _), ?_⟩
    intro n _hn
    by_cases hNn : N ≤ n
    · exact (hbound n hNn).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    · have hnN : n ≤ N := Nat.le_of_lt (Nat.lt_of_not_ge hNn)
      refine (dimensionConstant_le_dimension n).trans ?_
      calc
        (n : ENNReal) = ENNReal.ofReal (n : ℝ) := by simp
        _ ≤ ENNReal.ofReal (N : ℝ) := ENNReal.ofReal_le_ofReal (by exact_mod_cast hnN)
        _ ≤ ENNReal.ofReal (max c (N : ℝ)) := ENNReal.ofReal_le_ofReal (le_max_right _ _)

/-- **Uniform discrepancy bound for vectors in the unit ball.** The statement that there is a real
constant $C > 0$ such that for all natural numbers $n$ and $d$ and all vectors
$v_1, \dots, v_n \in \mathbb{R}^d$ of Euclidean norm at most $1$, writing $v_{ij}$ for the
$j$-th coordinate of $v_i$, there are signs $\varepsilon_1, \dots, \varepsilon_n \in \{-1, 1\}$
with $\left|\sum_{i=1}^{n} \varepsilon_i v_{ij}\right| \le C$ for every coordinate index $j$. -/
def UniformRectangularBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (n d : ℕ) (v : Fin n → Fin d → ℝ),
      (∀ i, ∑ j, (v i j) ^ 2 ≤ 1) →
        ∃ epsilon : Fin n → ℝ,
          (∀ i, epsilon i = 1 ∨ epsilon i = -1) ∧
          ∀ j, |∑ i, epsilon i * v i j| ≤ C

end

end MatrixDiscrepancy
