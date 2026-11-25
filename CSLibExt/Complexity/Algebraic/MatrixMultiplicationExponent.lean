/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Find
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.NormNum

/-!
# Matrix-multiplication exponents

This file defines concrete square and rectangular matrix-multiplication tensors, finite
rank-one decompositions, and their asymptotic rank exponents over an arbitrary field. The
definitions are reusable infrastructure: no conjecture or literature-bound assertion is included.

The rectangular exponent uses inner dimension `ceil (n ^ k)`. The dual exponent is the supremum
of nonnegative aspects whose rectangular exponent equals two.
-/

set_option autoImplicit false

@[expose] public section

open scoped BigOperators TensorProduct

namespace Cslib.Complexity.Algebraic.MatrixMultiplicationExponent

universe u v w x

/-- **Rank-one trilinear term.** For a type $F$ with multiplication and types $A$, $B$, $C$, a
rank-one trilinear term is a triple of functions $u : A \to F$, $v : B \to F$, $w : C \to F$ (its
left, middle and right factors), representing one rank-one summand $u \otimes v \otimes w$ of a
trilinear tensor decomposition. -/
structure RankOneTrilinearTerm (F : Type u) (A : Type v) (B : Type w) (C : Type x)
    [Mul F] where
  left : A → F
  middle : B → F
  right : C → F

/-- **Value of a rank-one trilinear term.** For a rank-one trilinear term over a semigroup $F$
with factors $u : A \to F$, $v : B \to F$ and $w : C \to F$, its value at $a \in A$, $b \in B$,
$c \in C$ is the product $u(a)\,v(b)\,w(c)$. -/
def RankOneTrilinearTerm.eval {F : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Semigroup F] (term : RankOneTrilinearTerm F A B C) (a : A) (b : B) (c : C) : F :=
  term.left a * term.middle b * term.right c

/-- **Trilinear rank at most $r$.** Let $F$ be a semiring and $A$, $B$, $C$ types. An array
$T : A \to B \to C \to F$ has trilinear rank at most $r$ when there are $s \le r$ and functions
$u_i : A \to F$, $v_i : B \to F$, $w_i : C \to F$ for $i = 1, \dots, s$ such that
$T(a, b, c) = \sum_{i=1}^{s} u_i(a)\,v_i(b)\,w_i(c)$ for all $a \in A$, $b \in B$, $c \in C$. -/
def HasTrilinearRankAtMost {F : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Semiring F] (T : A → B → C → F) (r : ℕ) : Prop :=
  ∃ terms : List (RankOneTrilinearTerm F A B C), terms.length ≤ r ∧
    ∀ a b c, T a b c = (terms.map fun term ↦ term.eval a b c).sum

/-- **Monotonicity of trilinear rank bounds.** Let $F$ be a semiring and $T : A \to B \to C \to F$
an array. If $T$ has trilinear rank at most $r$ and $r \le s$, then $T$ has trilinear rank at
most $s$. -/
theorem HasTrilinearRankAtMost.mono {F : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Semiring F] {T : A → B → C → F} {r s : ℕ}
    (h : HasTrilinearRankAtMost T r) (hrs : r ≤ s) : HasTrilinearRankAtMost T s := by
  obtain ⟨terms, hlength, heval⟩ := h
  exact ⟨terms, hlength.trans hrs, heval⟩

private noncomputable def coordinateTerms {F : Type u} {A : Type v} {B : Type w}
    {C : Type x} [Semiring F] [Fintype A] [Fintype B] [Fintype C]
    (T : A → B → C → F) : List (RankOneTrilinearTerm F A B C) := by
  classical
  exact (Finset.univ : Finset (A × B × C)).toList.map fun abc ↦ {
    left := fun a ↦ if a = abc.1 then T abc.1 abc.2.1 abc.2.2 else 0
    middle := fun b ↦ if b = abc.2.1 then 1 else 0
    right := fun c ↦ if c = abc.2.2 then 1 else 0
  }

/-- **Trivial upper bound on trilinear rank.** Let $F$ be a semiring and $A$, $B$, $C$ finite
types. Every array $T : A \to B \to C \to F$ has trilinear rank at most
$|A| \cdot |B| \cdot |C|$. -/
theorem hasTrilinearRankAtMost_card {F : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Semiring F] [Fintype A] [Fintype B] [Fintype C] (T : A → B → C → F) :
    HasTrilinearRankAtMost T (Fintype.card A * Fintype.card B * Fintype.card C) := by
  classical
  refine ⟨coordinateTerms T, ?_, ?_⟩
  · simp [coordinateTerms, Nat.mul_assoc]
  · intro a b c
    simp only [coordinateTerms, List.map_map, Finset.sum_map_toList, Function.comp_apply,
      RankOneTrilinearTerm.eval]
    simp_rw [Fintype.sum_prod_type]
    simp [mul_ite]

/-- **Trilinear rank.** Let $F$ be a semiring and let $A$, $B$, $C$ be finite types. The trilinear
rank of a coefficient array $T : A \to B \to C \to F$ is the least $r \in \mathbb{N}$ for which
there are $s \le r$ functions $u_i : A \to F$, $v_i : B \to F$, $w_i : C \to F$ with
$T(a, b, c) = \sum_{i=1}^{s} u_i(a)\,v_i(b)\,w_i(c)$ for all $a \in A$, $b \in B$, $c \in C$.

Such an $r$ exists because $|A| \cdot |B| \cdot |C|$ coordinate terms always suffice. -/
noncomputable def trilinearRank {F : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Semiring F] [Fintype A] [Fintype B] [Fintype C] (T : A → B → C → F) : ℕ := by
  classical
  exact Nat.find ⟨_, hasTrilinearRankAtMost_card T⟩

/-- **The trilinear rank is attained.** Let $F$ be a semiring, let $A$, $B$, $C$ be finite types,
let $T : A \to B \to C \to F$ be a coefficient array, and let $R(T)$ be its trilinear rank. Then
there are $s \le R(T)$ functions $u_i : A \to F$, $v_i : B \to F$, $w_i : C \to F$ with
$T(a, b, c) = \sum_{i=1}^{s} u_i(a)\,v_i(b)\,w_i(c)$ for all $a \in A$, $b \in B$, $c \in C$. -/
theorem trilinearRank_spec {F : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Semiring F] [Fintype A] [Fintype B] [Fintype C] (T : A → B → C → F) :
    HasTrilinearRankAtMost T (trilinearRank T) := by
  classical
  exact Nat.find_spec ⟨_, hasTrilinearRankAtMost_card T⟩

/-- **Decompositions bound the trilinear rank.** Let $F$ be a semiring, let $A$, $B$, $C$ be finite
types, and let $T : A \to B \to C \to F$ be a coefficient array. If there are $s \le r$ functions
$u_i : A \to F$, $v_i : B \to F$, $w_i : C \to F$ with
$T(a, b, c) = \sum_{i=1}^{s} u_i(a)\,v_i(b)\,w_i(c)$ for all $a \in A$, $b \in B$, $c \in C$,
then the trilinear rank of $T$ is at most $r$. -/
theorem trilinearRank_le {F : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Semiring F] [Fintype A] [Fintype B] [Fintype C] {T : A → B → C → F} {r : ℕ}
    (h : HasTrilinearRankAtMost T r) : trilinearRank T ≤ r := by
  classical
  exact Nat.find_min' ⟨_, hasTrilinearRankAtMost_card T⟩ h

/-- **Rank bounds via the trilinear rank.** Let $F$ be a semiring and $A$, $B$, $C$ finite types.
For every array $T : A \to B \to C \to F$ and every natural number $r$, $T$ has trilinear rank at
most $r$ if and only if the trilinear rank of $T$ (the least length of a decomposition of $T$
into rank-one arrays) is at most $r$. -/
theorem hasTrilinearRankAtMost_iff {F : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Semiring F] [Fintype A] [Fintype B] [Fintype C] (T : A → B → C → F) (r : ℕ) :
    HasTrilinearRankAtMost T r ↔ trilinearRank T ≤ r :=
  ⟨trilinearRank_le, fun h ↦ (trilinearRank_spec T).mono h⟩

/-- **Trilinear tensors.** For a field $F$ and types $A$, $B$, $C$, write $F^X$ for the
$F$-vector space of functions $X \to F$. The space of trilinear tensors over $F$ indexed by
$A$, $B$, $C$ is the tensor product $(F^A \otimes_F F^B) \otimes_F F^C$ over $F$. -/
abbrev TrilinearTensor (F : Type u) [Field F] (A : Type v) (B : Type w) (C : Type x) :=
  ((A → F) ⊗[F] (B → F)) ⊗[F] (C → F)

/-- **Coefficient array of a trilinear tensor.** Let $F$ be a field, let $A$ and $C$ be finite
types, let $B$ be a type, and write $F^X$ for the space of functions $X \to F$. The coefficient
map is the $F$-linear isomorphism from $(F^A \otimes_F F^B) \otimes_F F^C$ to the space
of arrays $A \to B \to C \to F$ that sends each pure tensor $(u \otimes v) \otimes w$ to the
array $(a, b, c) \mapsto u(a)\,v(b)\,w(c)$. -/
noncomputable def trilinearTensorCoefficients (F : Type u) [Field F]
    (A : Type v) (B : Type w) (C : Type x) [Fintype A] [Fintype C] :
    TrilinearTensor F A B C ≃ₗ[F] (A → B → C → F) := by
  classical
  exact (TensorProduct.piScalarRight F F ((A → F) ⊗[F] (B → F)) C).trans
    ((LinearEquiv.piCongrRight fun _ ↦
      (TensorProduct.comm F (A → F) (B → F)).trans
        (TensorProduct.piScalarRight F F (B → F) A)).trans {
      toFun f a b c := f c a b
      invFun f c a b := f a b c
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
    })

/-- **Coefficients of a pure tensor.** Let $F$ be a field, let $A$ and $C$ be finite types and
let $B$ be a type. For $u : A \to F$, $v : B \to F$, $w : C \to F$ and $a \in A$, $b \in B$,
$c \in C$, the coefficient array of the pure tensor $(u \otimes v) \otimes w$ takes the value
$u(a)\,v(b)\,w(c)$ at $(a, b, c)$. -/
@[simp] theorem trilinearTensorCoefficients_tmul (F : Type u) [Field F]
    (A : Type v) (B : Type w) (C : Type x) [Fintype A] [Fintype C]
    (left : A → F) (middle : B → F) (right : C → F) (a : A) (b : B) (c : C) :
    trilinearTensorCoefficients F A B C ((left ⊗ₜ[F] middle) ⊗ₜ[F] right) a b c =
      left a * middle b * right c := by
  simp [trilinearTensorCoefficients, mul_comm, mul_left_comm]

/-- **The pure tensor of a rank-one term.** Let $F$ be a field and $A$, $B$, $C$ types. A
rank-one trilinear term with factors $u : A \to F$, $v : B \to F$ and $w : C \to F$ determines
the pure tensor $(u \otimes v) \otimes w$ in the trilinear tensor space over $F$ indexed by
$A$, $B$, $C$. -/
def RankOneTrilinearTerm.tensor {F : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Field F] (term : RankOneTrilinearTerm F A B C) : TrilinearTensor F A B C :=
  (term.left ⊗ₜ[F] term.middle) ⊗ₜ[F] term.right

/-- **Tensor rank at most $r$.** Let $F$ be a field and $A$, $B$, $C$ types. An element $T$ of
$(F^A \otimes_F F^B) \otimes_F F^C$ has tensor rank at most $r$ when there are $s \le r$ and
functions $u_i : A \to F$, $v_i : B \to F$, $w_i : C \to F$ for $i = 1, \dots, s$ such that
$T = \sum_{i=1}^{s} (u_i \otimes v_i) \otimes w_i$. -/
def HasTensorRankAtMost {F : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Field F] (T : TrilinearTensor F A B C) (r : ℕ) : Prop :=
  ∃ terms : List (RankOneTrilinearTerm F A B C), terms.length ≤ r ∧
    T = (terms.map RankOneTrilinearTerm.tensor).sum

private theorem coefficients_list_sum {F : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Field F] [Fintype A] [Fintype C] (terms : List (RankOneTrilinearTerm F A B C))
    (a : A) (b : B) (c : C) :
    trilinearTensorCoefficients F A B C (terms.map RankOneTrilinearTerm.tensor).sum a b c =
      (terms.map fun term ↦ term.eval a b c).sum := by
  induction terms with
  | nil => simp
  | cons term terms ih =>
    simp [RankOneTrilinearTerm.tensor, RankOneTrilinearTerm.eval, ih]

/-- **Tensor rank bounds agree with coefficient rank bounds.** Let $F$ be a field and $A$, $B$,
$C$ types with $A$ and $C$ finite, and let $T$ be an element of $(F^A \otimes_F F^B) \otimes_F F^C$.
For every natural number $r$, $T$ has tensor rank at most $r$ if and only if its coefficient
array $A \to B \to C \to F$, obtained by the canonical linear equivalence, has trilinear rank at
most $r$. -/
theorem hasTensorRankAtMost_iff {F : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Field F] [Fintype A] [Fintype C] (T : TrilinearTensor F A B C) (r : ℕ) :
    HasTensorRankAtMost T r ↔
      HasTrilinearRankAtMost (trilinearTensorCoefficients F A B C T) r := by
  constructor
  · rintro ⟨terms, hlength, heq⟩
    refine ⟨terms, hlength, ?_⟩
    intro a b c
    rw [heq, coefficients_list_sum]
  · rintro ⟨terms, hlength, heq⟩
    refine ⟨terms, hlength, ?_⟩
    apply (trilinearTensorCoefficients F A B C).injective
    ext a b c
    rw [coefficients_list_sum]
    exact heq a b c

/-- **Tensor rank.** Let $F$ be a field and let $A$, $B$, $C$ be finite types. The tensor rank of
a trilinear tensor $T$ over $F$ indexed by $A$, $B$, $C$ is the least $r \in \mathbb{N}$ such
that $T$ is a sum of at most $r$ pure tensors $(u \otimes v) \otimes w$ with $u : A \to F$,
$v : B \to F$ and $w : C \to F$.

It is defined as the trilinear rank of the coefficient array of $T$. -/
noncomputable def tensorRank {F : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Field F] [Fintype A] [Fintype B] [Fintype C] (T : TrilinearTensor F A B C) : ℕ :=
  trilinearRank (trilinearTensorCoefficients F A B C T)

/-- **The tensor rank is attained.** Let $F$ be a field, let $A$, $B$, $C$ be finite types, let
$T$ be a trilinear tensor over $F$ indexed by $A$, $B$, $C$, and let $R(T)$ be its tensor rank.
Then $T$ is a sum of at most $R(T)$ pure tensors $(u \otimes v) \otimes w$ with $u : A \to F$,
$v : B \to F$ and $w : C \to F$. -/
theorem tensorRank_spec {F : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Field F] [Fintype A] [Fintype B] [Fintype C] (T : TrilinearTensor F A B C) :
    HasTensorRankAtMost T (tensorRank T) :=
  (hasTensorRankAtMost_iff T _).mpr (trilinearRank_spec _)

/-- **Decompositions bound the tensor rank.** Let $F$ be a field, let $A$, $B$, $C$ be finite
types, and let $T$ be a trilinear tensor over $F$ indexed by $A$, $B$, $C$. If $T$ is a sum of at
most $r$ pure tensors $(u \otimes v) \otimes w$ with $u : A \to F$, $v : B \to F$ and
$w : C \to F$, then the tensor rank of $T$ is at most $r$. -/
theorem tensorRank_le {F : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Field F] [Fintype A] [Fintype B] [Fintype C] {T : TrilinearTensor F A B C} {r : ℕ}
    (h : HasTensorRankAtMost T r) : tensorRank T ≤ r :=
  trilinearRank_le ((hasTensorRankAtMost_iff T r).mp h)

/-- **Matrix coordinates.** The index set of an $m \times n$ matrix: pairs $(i, j)$ of a row index
$i \in \{0, \dots, m-1\}$ and a column index $j \in \{0, \dots, n-1\}$. -/
abbrev MatrixCoordinate (m n : ℕ) := Fin m × Fin n

/-- **Matrix multiplication tensor.** For a field $F$ and natural numbers $m$, $n$, $p$, the matrix
multiplication tensor is the array over $F$ indexed by triples $((i, j), (j', k), (k', i'))$ of an
$m \times n$, an $n \times p$ and a $p \times m$ matrix coordinate, whose entry is $1$ if $j = j'$,
$k = k'$ and $i' = i$, and $0$ otherwise.

These are the coefficients of $\sum_{i, j, k} e_{(i,j)} \otimes e_{(j,k)} \otimes e_{(k,i)}$, the
tensor of multiplying an $m \times n$ matrix by an $n \times p$ matrix. -/
def matrixMultiplicationTensor (F : Type u) [Field F] (m n p : ℕ) :
    MatrixCoordinate m n → MatrixCoordinate n p → MatrixCoordinate p m → F :=
  fun a b c ↦ if a.2 = b.1 ∧ b.2 = c.1 ∧ c.2 = a.1 then 1 else 0

/-- **Square matrix multiplication tensor.** For a field $F$ and a natural number $n$, the square
matrix multiplication tensor over $F$ is the matrix multiplication tensor for multiplying an
$n \times n$ matrix by an $n \times n$ matrix. Its value at a triple of matrix coordinates
$((i, j), (j', k), (k', i'))$ is $1$ when $j = j'$, $k = k'$ and $i = i'$, and $0$ otherwise. -/
def squareMatrixMultiplicationTensor (F : Type u) [Field F] (n : ℕ) :
    MatrixCoordinate n n → MatrixCoordinate n n → MatrixCoordinate n n → F :=
  matrixMultiplicationTensor F n n n

/-- **Matrix multiplication structure tensor.** For a field $F$ and natural numbers $m, n, p$, the
structure tensor of multiplying an $m \times n$ matrix by an $n \times p$ matrix over $F$ is
the element $\sum_{i < m} \sum_{j < n} \sum_{k < p} e_{(i,j)} \otimes e_{(j,k)} \otimes e_{(k,i)}$
of the trilinear tensor space
$F^{[m] \times [n]} \otimes F^{[n] \times [p]} \otimes F^{[p] \times [m]}$, where
$[m] = \{0, \dots, m - 1\}$ and $e_x$ is the standard basis vector at the matrix coordinate $x$. -/
noncomputable def matrixMultiplicationStructureTensor (F : Type u) [Field F] (m n p : ℕ) :
    TrilinearTensor F (MatrixCoordinate m n) (MatrixCoordinate n p) (MatrixCoordinate p m) :=
  ∑ i : Fin m, ∑ j : Fin n, ∑ k : Fin p,
    (Pi.single (i, j) (1 : F) ⊗ₜ[F] Pi.single (j, k) (1 : F)) ⊗ₜ[F]
      Pi.single (k, i) (1 : F)

/-- **Coefficients of the matrix multiplication structure tensor.** Let $F$ be a field, let
$m, n, p$ be natural numbers, and write $e_x$ for the standard basis vector with index $x$. The
coordinates of the structure tensor
$\sum_{i < m,\, j < n,\, k < p} e_{(i,j)} \otimes e_{(j,k)} \otimes e_{(k,i)}$ in
$F^{m \times n} \otimes F^{n \times p} \otimes F^{p \times m}$ are the matrix multiplication
coefficients: the coordinate at $((i, j), (j', k), (k', i'))$ is $1$ if $j = j'$, $k = k'$ and
$i = i'$, and $0$ otherwise. -/
theorem matrixMultiplicationStructureTensor_coefficients (F : Type u) [Field F] (m n p : ℕ) :
    trilinearTensorCoefficients F _ _ _ (matrixMultiplicationStructureTensor F m n p) =
      matrixMultiplicationTensor F m n p := by
  classical
  ext a b c
  rcases a with ⟨ai, aj⟩
  rcases b with ⟨bi, bk⟩
  rcases c with ⟨ck, ci⟩
  simp only [matrixMultiplicationStructureTensor, map_sum, Finset.sum_apply,
    trilinearTensorCoefficients_tmul, Pi.single_apply, Prod.mk.injEq]
  simp only [ite_and, mul_ite, ite_mul, one_mul, zero_mul]
  by_cases h₁ : aj = bi
  · subst bi
    by_cases h₂ : bk = ck
    · subst ck
      by_cases h₃ : ci = ai
      · subst ci
        simp [matrixMultiplicationTensor]
      · have h₃' : ¬ ai = ci := fun h ↦ h₃ h.symm
        simp [matrixMultiplicationTensor, h₃, h₃']
    · simp [matrixMultiplicationTensor, h₂]
  · simp [matrixMultiplicationTensor, h₁]

/-- **Square matrix multiplication rank.** For a field $F$ and a natural number $n$, the square
matrix multiplication rank of $F$ at $n$ is the tensor rank of the structure tensor of
multiplying two $n \times n$ matrices over $F$: the least number of pure tensors whose sum is that
structure tensor. -/
noncomputable def squareMatrixMultiplicationRank (F : Type u) [Field F] (n : ℕ) : ℕ :=
  tensorRank (matrixMultiplicationStructureTensor F n n n)

/-- **Square matrix multiplication rank equals the coefficient tensor rank.** For every field $F$
and natural number $n$, the square matrix multiplication rank of $F$ at $n$ equals the trilinear
rank of the square $n \times n$ matrix multiplication tensor over $F$. -/
theorem squareMatrixMultiplicationRank_eq (F : Type u) [Field F] (n : ℕ) :
    squareMatrixMultiplicationRank F n = trilinearRank (squareMatrixMultiplicationTensor F n) := by
  simp only [squareMatrixMultiplicationRank, tensorRank,
    matrixMultiplicationStructureTensor_coefficients, squareMatrixMultiplicationTensor]

/-- **Matrix multiplication tensor contraction.** Let $F$ be a field, let $m, n, p$ be natural
numbers, let $A \in F^{m \times n}$ and $B \in F^{n \times p}$, and let $i < m$ and $k < p$. Write
$T$ for the matrix multiplication tensor over $F$ for $m, n, p$ and, for a natural number $q$,
$[q] = \{0, \dots, q - 1\}$. The contraction of $T$ against $A$ and $B$ at output coordinate
$(i, k)$ is
$$\sum_{a \in [m] \times [n]} \sum_{b \in [n] \times [p]} T(a, b, (k, i)) \, A_a \, B_b,$$
where $A_a$ and $B_b$ are the entries of $A$ and $B$ at the matrix coordinates $a$ and $b$. -/
noncomputable def matrixMultiplicationTensorContraction (F : Type u) [Field F]
    {m n p : ℕ} (A : Matrix (Fin m) (Fin n) F) (B : Matrix (Fin n) (Fin p) F)
    (i : Fin m) (k : Fin p) : F :=
  ∑ a : MatrixCoordinate m n, ∑ b : MatrixCoordinate n p,
    matrixMultiplicationTensor F m n p a b (k, i) * A a.1 a.2 * B b.1 b.2

/-- **Contracting the matrix multiplication tensor gives the matrix product.** For a field $F$,
matrices $A \in F^{m \times n}$ and $B \in F^{n \times p}$, and indices $i < m$ and $k < p$, the
contraction of the matrix multiplication tensor against $A$ and $B$ at output coordinate
$(i, k)$ equals the entry $(AB)_{ik}$ of the matrix product. -/
theorem matrixMultiplicationTensorContraction_eq_mul (F : Type u) [Field F]
    {m n p : ℕ} (A : Matrix (Fin m) (Fin n) F) (B : Matrix (Fin n) (Fin p) F)
    (i : Fin m) (k : Fin p) :
    matrixMultiplicationTensorContraction F A B i k = (A * B) i k := by
  rw [matrixMultiplicationTensorContraction, Matrix.mul_apply]
  simp_rw [Fintype.sum_prod_type]
  simp only [matrixMultiplicationTensor, ite_mul, one_mul, zero_mul]
  have indicator (a₁ : Fin m) (a₂ b₁ : Fin n) (b₂ : Fin p) :
      (if a₂ = b₁ ∧ b₂ = k ∧ i = a₁ then A a₁ a₂ * B b₁ b₂ else 0) =
        if i = a₁ then
          if a₂ = b₁ then
            if b₂ = k then A a₁ a₂ * B b₁ b₂ else 0
          else 0
        else 0 := by
    by_cases hia : i = a₁ <;> by_cases hab : a₂ = b₁ <;> by_cases hbk : b₂ = k <;>
      simp_all
  simp_rw [indicator]
  simp

/-- **Matrix multiplication rank exponent.** A real number $w$ is a matrix multiplication rank
exponent over a field $F$ when $w \ge 0$ and there are a real $C > 0$ and a natural number
$N_0 \ge 1$ such that for every $n \ge N_0$ the $n \times n$ matrix multiplication coefficient
tensor over $F$ is a sum of at most $C n^w$ rank-one trilinear terms. -/
def HasMatrixMultiplicationRankExponent (F : Type u) [Field F] (w : ℝ) : Prop :=
  0 ≤ w ∧ ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
    ∀ n : ℕ, N₀ ≤ n → ∃ r : ℕ,
      HasTrilinearRankAtMost (squareMatrixMultiplicationTensor F n) r ∧
        (r : ℝ) ≤ C * Real.rpow (n : ℝ) w

/-- **Rank exponents via the minimum tensor rank.** Let $F$ be a field and $w$ a real number. Then
$w$ is a matrix multiplication rank exponent over $F$ if and only if $w \ge 0$ and there are a real
$C > 0$ and a natural number $N_0 \ge 1$ such that for every $n \ge N_0$ the tensor rank of the
$n \times n$ matrix multiplication structure tensor over $F$ is at most $C n^w$. -/
theorem hasMatrixMultiplicationRankExponent_iff (F : Type u) [Field F] (w : ℝ) :
    HasMatrixMultiplicationRankExponent F w ↔
      0 ≤ w ∧ ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
        ∀ n : ℕ, N₀ ≤ n →
          (squareMatrixMultiplicationRank F n : ℝ) ≤ C * Real.rpow (n : ℝ) w := by
  constructor
  · rintro ⟨hw, C, hC, N₀, hN₀, h⟩
    refine ⟨hw, C, hC, N₀, hN₀, ?_⟩
    intro n hn
    obtain ⟨r, hr, hbound⟩ := h n hn
    rw [squareMatrixMultiplicationRank_eq]
    exact (Nat.cast_le.mpr (trilinearRank_le hr)).trans hbound
  · rintro ⟨hw, C, hC, N₀, hN₀, h⟩
    refine ⟨hw, C, hC, N₀, hN₀, ?_⟩
    intro n hn
    refine ⟨trilinearRank (squareMatrixMultiplicationTensor F n), trilinearRank_spec _, ?_⟩
    simpa only [squareMatrixMultiplicationRank_eq] using h n hn

/-- **Monotonicity of matrix multiplication rank exponents.** Let $F$ be a field and let
$w \le w'$ be real numbers. If $w$ is a matrix multiplication rank exponent for $F$, then so
is $w'$. -/
theorem HasMatrixMultiplicationRankExponent.mono (F : Type u) [Field F] {w w' : ℝ}
    (h : HasMatrixMultiplicationRankExponent F w) (hww' : w ≤ w') :
    HasMatrixMultiplicationRankExponent F w' := by
  obtain ⟨hw, C, hC, N₀, hN₀, hbound⟩ := h
  refine ⟨hw.trans hww', C, hC, N₀, hN₀, ?_⟩
  intro n hn
  obtain ⟨r, hr, hbound⟩ := hbound n hn
  refine ⟨r, hr, hbound.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow_of_exponent_le _ hww'
  exact_mod_cast hN₀.trans hn

/-- **Matrix multiplication exponent.** The matrix multiplication exponent $\omega(F)$ of a field
$F$ is the infimum, taken in $[0, \infty]$, of the real numbers $w$ that are matrix multiplication
rank exponents over $F$; it is $\infty$ when there is no such $w$. -/
noncomputable def matrixMultiplicationExponent (F : Type u) [Field F] : ENNReal :=
  sInf {W : ENNReal | ∃ w : ℝ, W = ENNReal.ofReal w ∧
    HasMatrixMultiplicationRankExponent F w}

/-- **Rank exponents bound the matrix multiplication exponent.** If a real number $w$ is a matrix
multiplication rank exponent over a field $F$, then the matrix multiplication exponent
$\omega(F)$ of $F$ satisfies $\omega(F) \le w$. -/
theorem matrixMultiplicationExponent_le_of_admissible (F : Type u) [Field F] {w : ℝ}
    (h : HasMatrixMultiplicationRankExponent F w) :
    matrixMultiplicationExponent F ≤ ENNReal.ofReal w :=
  sInf_le ⟨w, rfl, h⟩

/-- **Lower bounds for the matrix multiplication exponent.** Let $F$ be a field and let $W$ be an
element of $[0, \infty]$. If $W \le w$ for every real number $w$ that is a matrix multiplication
rank exponent over $F$, then $W$ is at most the matrix multiplication exponent $\omega(F)$. -/
theorem le_matrixMultiplicationExponent (F : Type u) [Field F] {W : ENNReal}
    (h : ∀ w : ℝ, HasMatrixMultiplicationRankExponent F w → W ≤ ENNReal.ofReal w) :
    W ≤ matrixMultiplicationExponent F := by
  apply le_sInf
  rintro _ ⟨w, rfl, hw⟩
  exact h w hw

private def basisTerm (F : Type u) [Field F] {m n p : ℕ}
    (i : Fin m) (j : Fin n) (k : Fin p) :
    RankOneTrilinearTerm F (MatrixCoordinate m n) (MatrixCoordinate n p)
      (MatrixCoordinate p m) where
  left := fun a ↦ (if a.1 = i then 1 else 0) * (if a.2 = j then 1 else 0)
  middle := fun b ↦ (if b.1 = j then 1 else 0) * (if b.2 = k then 1 else 0)
  right := fun c ↦ (if c.1 = k then 1 else 0) * (if c.2 = i then 1 else 0)

private noncomputable def basisTerms (F : Type u) [Field F] (m n p : ℕ) :
    List (RankOneTrilinearTerm F (MatrixCoordinate m n) (MatrixCoordinate n p)
      (MatrixCoordinate p m)) :=
  ((Finset.univ : Finset (Fin m)).product
      ((Finset.univ : Finset (Fin n)).product (Finset.univ : Finset (Fin p)))).toList.map
    fun ijk ↦ basisTerm F ijk.1 ijk.2.1 ijk.2.2

/-- **Direct rank bound for the matrix multiplication tensor.** For every field $F$ and natural
numbers $m, n, p$, the coefficient tensor of multiplying an $m \times n$ matrix by an $n \times p$
matrix over $F$ is a sum of at most $mnp$ rank-one trilinear terms.

The decomposition is the direct algorithm, with one term for each triple $(i, j, k)$ with
$i < m$, $j < n$ and $k < p$. -/
theorem matrixMultiplicationTensor_rank_le_product (F : Type u) [Field F] (m n p : ℕ) :
    HasTrilinearRankAtMost (matrixMultiplicationTensor F m n p) (m * n * p) := by
  classical
  refine ⟨basisTerms F m n p, ?_, ?_⟩
  · simp [basisTerms, Nat.mul_assoc]
  · intro a b c
    rcases a with ⟨ai, aj⟩
    rcases b with ⟨bi, bk⟩
    rcases c with ⟨ck, ci⟩
    simp only [matrixMultiplicationTensor, RankOneTrilinearTerm.eval, basisTerms, basisTerm,
      mul_ite, mul_one, mul_zero, Finset.product_eq_sprod, Finset.univ_product_univ,
      List.map_map, Finset.sum_map_toList, Function.comp_apply]
    simp_rw [Fintype.sum_prod_type]
    by_cases h₁ : aj = bi
    · subst bi
      by_cases h₂ : bk = ck
      · subst ck
        by_cases h₃ : ci = ai
        · subst ci
          simp
        · have h₃' : ¬ ai = ci := fun h ↦ h₃ h.symm
          simp [h₃, h₃']
      · simp [h₂]
    · simp [h₁]

/-- **Direct decomposition of the structure tensor.** Let $F$ be a field, let $m, n, p$ be
natural numbers, and write $e_x$ for the standard basis vector with index $x$. The matrix
multiplication structure tensor
$\sum_{i < m,\, j < n,\, k < p} e_{(i,j)} \otimes e_{(j,k)} \otimes e_{(k,i)}$ in
$F^{m \times n} \otimes F^{n \times p} \otimes F^{p \times m}$ is a sum of at most $mnp$ pure
tensors $u \otimes v \otimes w$. -/
theorem matrixMultiplicationStructureTensor_rank_le_product (F : Type u) [Field F] (m n p : ℕ) :
    HasTensorRankAtMost (matrixMultiplicationStructureTensor F m n p) (m * n * p) := by
  rw [hasTensorRankAtMost_iff, matrixMultiplicationStructureTensor_coefficients]
  exact matrixMultiplicationTensor_rank_le_product F m n p

private def strassenTerms (F : Type u) [Field F] :
    List (RankOneTrilinearTerm F (MatrixCoordinate 2 2) (MatrixCoordinate 2 2)
      (MatrixCoordinate 2 2)) :=
  let v (x₀₀ x₀₁ x₁₀ x₁₁ : F) : MatrixCoordinate 2 2 → F := fun a ↦
    if a.1 = 0 then (if a.2 = 0 then x₀₀ else x₀₁)
    else (if a.2 = 0 then x₁₀ else x₁₁)
  [⟨v 1 0 0 1, v 1 0 0 1, v 1 0 0 1⟩,
   ⟨v 0 0 1 1, v 1 0 0 0, v 0 1 0 (-1)⟩,
   ⟨v 1 0 0 0, v 0 1 0 (-1), v 0 0 1 1⟩,
   ⟨v 0 0 0 1, v (-1) 0 1 0, v 1 1 0 0⟩,
   ⟨v 1 1 0 0, v 0 0 0 1, v (-1) 0 1 0⟩,
   ⟨v (-1) 0 1 0, v 1 1 0 0, v 0 0 0 1⟩,
   ⟨v 0 1 0 (-1), v 0 0 1 1, v 1 0 0 0⟩]

/-- **Strassen's rank bound for $2 \times 2$ matrix multiplication.** For every field $F$, the
square $2 \times 2$ matrix multiplication tensor over $F$ is a sum of at most $7$ rank-one
trilinear terms.

The seven terms are Strassen's, and the decomposition holds in every characteristic. -/
theorem squareMatrixMultiplicationTensor_rank_le_seven (F : Type u) [Field F] :
    HasTrilinearRankAtMost (squareMatrixMultiplicationTensor F 2) 7 := by
  classical
  refine ⟨strassenTerms F, by simp [strassenTerms], ?_⟩
  rintro ⟨ai, aj⟩ ⟨bi, bj⟩ ⟨ci, cj⟩
  fin_cases ai <;> fin_cases aj <;> fin_cases bi <;> fin_cases bj <;>
    fin_cases ci <;> fin_cases cj <;>
    norm_num [strassenTerms, RankOneTrilinearTerm.eval, squareMatrixMultiplicationTensor,
      matrixMultiplicationTensor]

/-- **Strassen's decomposition of the structure tensor.** Let $F$ be a field and write $e_x$ for
the standard basis vector with index $x$. The $2 \times 2$ matrix multiplication structure tensor
$\sum_{i, j, k < 2} e_{(i,j)} \otimes e_{(j,k)} \otimes e_{(k,i)}$ in
$F^{2 \times 2} \otimes F^{2 \times 2} \otimes F^{2 \times 2}$ is a sum of at most $7$ pure
tensors $u \otimes v \otimes w$. -/
theorem matrixMultiplicationStructureTensor_rank_le_seven (F : Type u) [Field F] :
    HasTensorRankAtMost (matrixMultiplicationStructureTensor F 2 2 2) 7 := by
  rw [hasTensorRankAtMost_iff, matrixMultiplicationStructureTensor_coefficients]
  exact squareMatrixMultiplicationTensor_rank_le_seven F

/-- **Direct rank bound for the square matrix multiplication tensor.** For every field $F$ and
natural number $n$, the square $n \times n$ matrix multiplication tensor over $F$ is a sum of at
most $n^3$ rank-one trilinear terms. -/
theorem squareMatrixMultiplicationTensor_rank_le_cube (F : Type u) [Field F] (n : ℕ) :
    HasTrilinearRankAtMost (squareMatrixMultiplicationTensor F n) (n * n * n) :=
  matrixMultiplicationTensor_rank_le_product F n n n

/-- **Exponent three for matrix multiplication rank.** For every field $F$, the number $3$ is a
matrix multiplication rank exponent over $F$.

It is witnessed by the direct decomposition of the $n \times n$ matrix multiplication tensor into
$n^3$ rank-one terms. -/
theorem hasMatrixMultiplicationRankExponent_three (F : Type u) [Field F] :
    HasMatrixMultiplicationRankExponent F 3 := by
  refine ⟨by norm_num, 1, by norm_num, 1, by norm_num, ?_⟩
  intro n hn
  refine ⟨n * n * n, squareMatrixMultiplicationTensor_rank_le_cube F n, ?_⟩
  norm_num [Real.rpow_natCast, pow_succ, mul_assoc]

/-- **The matrix multiplication exponent is at most three.** For every field $F$, the matrix
multiplication exponent $\omega(F)$ of $F$ satisfies $\omega(F) \le 3$. -/
theorem matrixMultiplicationExponent_le_three (F : Type u) [Field F] :
    matrixMultiplicationExponent F ≤ ENNReal.ofReal 3 := by
  apply sInf_le
  exact ⟨3, by norm_num, hasMatrixMultiplicationRankExponent_three F⟩

/-- **The matrix multiplication exponent is finite.** For every field $F$, the matrix
multiplication exponent of $F$, an element of $[0, \infty]$, is not $\infty$. -/
theorem matrixMultiplicationExponent_ne_top (F : Type u) [Field F] :
    matrixMultiplicationExponent F ≠ ⊤ :=
  (lt_of_le_of_lt (matrixMultiplicationExponent_le_three F) (by simp)).ne

/-- **Exponents above the matrix multiplication exponent admit rank bounds.** Let $F$ be a field,
let $\omega(F)$ be its matrix multiplication exponent and let $w > 0$ be real. If
$\omega(F) < w$, then there are $C > 0$ and $N_0 \ge 1$ such that for every $n \ge N_0$ the
$n \times n$ matrix multiplication tensor over $F$ has rank at most $C n^w$. -/
theorem hasMatrixMultiplicationRankExponent_of_inf_lt (F : Type u) [Field F] {w : ℝ}
    (hw : 0 < w) (h : matrixMultiplicationExponent F < ENNReal.ofReal w) :
    HasMatrixMultiplicationRankExponent F w := by
  obtain ⟨_, ⟨v, rfl, hv⟩, hvw⟩ := sInf_lt_iff.mp h
  exact hv.mono F ((ENNReal.ofReal_lt_ofReal_iff hw).mp hvw).le

/-- **Upper bounds on the matrix multiplication exponent.** Let $F$ be a field, let $\omega(F)$
be its matrix multiplication exponent and let $w \ge 0$ be real. Then $\omega(F) \le w$ if and
only if for every real $\varepsilon > 0$ there are $C > 0$ and $N_0 \ge 1$ such that for every
$n \ge N_0$ the $n \times n$ matrix multiplication tensor over $F$ has rank at most
$C n^{w + \varepsilon}$.

The right-hand side bounds the rank by $C n^{w + \varepsilon}$ for each $\varepsilon > 0$;
it is not an $O(n^w)$ rank bound. -/
theorem matrixMultiplicationExponent_le_iff (F : Type u) [Field F] (w : ℝ) (hw : 0 ≤ w) :
    matrixMultiplicationExponent F ≤ ENNReal.ofReal w ↔
      ∀ ε : ℝ, 0 < ε → HasMatrixMultiplicationRankExponent F (w + ε) := by
  constructor
  · intro h ε hε
    have hpos : 0 < w + ε := add_pos_of_nonneg_of_pos hw hε
    apply hasMatrixMultiplicationRankExponent_of_inf_lt F hpos
    exact h.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hpos).mpr (lt_add_of_pos_right w hε))
  · intro h
    apply (ENNReal.le_ofReal_iff_toReal_le (matrixMultiplicationExponent_ne_top F) hw).mpr
    apply le_of_forall_pos_le_add
    intro ε hε
    exact ENNReal.toReal_le_of_le_ofReal (add_nonneg hw hε.le)
      (matrixMultiplicationExponent_le_of_admissible F (h ε hε))

/-- **Rank bounds just above the matrix multiplication exponent.** Let $F$ be a field and let
$\omega(F)$ be its matrix multiplication exponent, a finite real number. For every real
$\varepsilon > 0$ there are $C > 0$ and $N_0 \ge 1$ such that for every $n \ge N_0$ the
$n \times n$ matrix multiplication tensor over $F$ has rank at most
$C n^{\omega(F) + \varepsilon}$. -/
theorem matrixMultiplicationExponent_endpoint (F : Type u) [Field F] :
    ∀ ε : ℝ, 0 < ε →
      HasMatrixMultiplicationRankExponent F ((matrixMultiplicationExponent F).toReal + ε) := by
  apply (matrixMultiplicationExponent_le_iff F _ ENNReal.toReal_nonneg).mp
  rw [ENNReal.ofReal_toReal (matrixMultiplicationExponent_ne_top F)]

/-- **Rectangular inner dimension.** For a natural number $n$ and a real aspect $k$, the
rectangular inner dimension is $\lceil n^k \rceil$, the least natural number that is at least
the real power $n^k$.

It is the inner dimension in the product of an $n \times \lceil n^k \rceil$ matrix and a
$\lceil n^k \rceil \times n$ matrix. -/
noncomputable def rectangularInnerDimension (n : ℕ) (k : ℝ) : ℕ :=
  Nat.ceil (Real.rpow (n : ℝ) k)

/-- **Rectangular inner dimension at aspect zero.** For every natural number $n$, including
$n = 0$, the rectangular inner dimension at dimension $n$ and aspect $0$, namely
$\lceil n^0 \rceil$, equals $1$, so aspect $0$ is the outer product of an $n \times 1$ matrix
and a $1 \times n$ matrix. -/
@[simp] theorem rectangularInnerDimension_zero (n : ℕ) :
    rectangularInnerDimension n 0 = 1 := by
  simp [rectangularInnerDimension, Real.rpow_zero]

/-- **Rectangular inner dimension at aspect one.** For every natural number $n$, the rectangular
inner dimension at dimension $n$ and aspect $1$, namely $\lceil n^1 \rceil$, equals $n$, so
aspect $1$ is square matrix multiplication without rounding. -/
@[simp] theorem rectangularInnerDimension_one (n : ℕ) :
    rectangularInnerDimension n 1 = n := by
  simp [rectangularInnerDimension, Real.rpow_one]

/-- **Rectangular inner dimension at dimension one.** For every real aspect $k$, the rectangular
inner dimension at dimension $1$ and aspect $k$, namely $\lceil 1^k \rceil$, equals $1$. -/
@[simp] theorem rectangularInnerDimension_one_base (k : ℝ) :
    rectangularInnerDimension 1 k = 1 := by
  simp [rectangularInnerDimension, Real.one_rpow]

/-- **Rank exponents for rectangular matrix multiplication.** Let $F$ be a field and let $k, w$ be
real. Then $w$ is a rank exponent for rectangular matrix multiplication over $F$ at aspect $k$
when $k \ge 0$, $w \ge 0$, and for every $\varepsilon > 0$ there are $C > 0$ and $N_0 \ge 1$
such that for every $n \ge N_0$ the tensor of multiplying an $n \times \lceil n^k \rceil$
matrix by a $\lceil n^k \rceil \times n$ matrix over $F$ has rank at most
$C n^{w + \varepsilon}$.

The coefficient $C$ and the threshold $N_0$ may depend on $\varepsilon$, but not on $n$. -/
def HasRectangularMatrixMultiplicationRankExponent (F : Type u) [Field F]
    (k w : ℝ) : Prop :=
  0 ≤ k ∧ 0 ≤ w ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
    ∀ n : ℕ, N₀ ≤ n → ∃ r : ℕ,
      HasTrilinearRankAtMost
        (matrixMultiplicationTensor F n (rectangularInnerDimension n k) n) r ∧
      (r : ℝ) ≤ C * Real.rpow (n : ℝ) (w + ε)

/-- **Rectangular matrix multiplication exponent.** For a field $F$ and a real number $k$, the
rectangular matrix multiplication exponent $\omega(k)$ of $F$ is the infimum in $[0, \infty]$ of
all real $w \ge 0$ with the following property: for every $\varepsilon > 0$ there are a real
$C > 0$ and a natural number $N_0 \ge 1$ such that for every $n \ge N_0$, the coefficient tensor
$\sum e_{ij} \otimes e_{jl} \otimes e_{li}$ of multiplying an $n \times \lceil n^k \rceil$ matrix
by an $\lceil n^k \rceil \times n$ matrix over $F$ is a sum of at most $C n^{w + \varepsilon}$
rank-one trilinear terms. If $k < 0$, no $w$ qualifies and $\omega(k) = \infty$. -/
noncomputable def rectangularMatrixMultiplicationExponent (F : Type u) [Field F]
    (k : ℝ) : ENNReal :=
  sInf {W : ENNReal | ∃ w : ℝ, W = ENNReal.ofReal w ∧
    HasRectangularMatrixMultiplicationRankExponent F k w}

/-- **Dual matrix multiplication exponent.** For a field $F$, the dual matrix multiplication
exponent of $F$ is the supremum, taken in the extended nonnegative reals $[0, \infty]$, of the
set of real aspects $k \ge 0$ for which the rectangular matrix multiplication exponent of $F$ at
aspect $k$ equals $2$. -/
noncomputable def dualMatrixMultiplicationExponent (F : Type u) [Field F] : ENNReal :=
  sSup {K : ENNReal | ∃ k : ℝ, 0 ≤ k ∧ K = ENNReal.ofReal k ∧
    rectangularMatrixMultiplicationExponent F k = 2}

end Cslib.Complexity.Algebraic.MatrixMultiplicationExponent
