/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Mark Sepanski
-/
module

public import Mathlib.Combinatorics.Young.YoungDiagram
public import Mathlib.Data.List.GetD
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Tactic.IntervalCases

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 490, Combinatorics 494, Combinatorics 495, Combinatorics 497, Combinatorics 498, Combinatorics 500

/-!
# `MathlibExt.Combinatorics.SymmetricFunctionsYoungTableaux`

## References

* ec2 7.8.2 (for `MvPolynomial.omegaAlgHom`)
* ec2 7.8 p 304 (for `MvPowerSeries.exponentialSpecialization`)
* ec2 7.15 p 336 (for `symmetricScalarProduct`)
* ec2 7.10 p 309 (for `SkewShape`, `SkewSemistandardYoungTableau`)
* ec2 7.10 p 312 (for `SkewStandardYoungTableau`)
-/

namespace MetaMathlibExt

-- Combinatorics 490: Omega Involution


/-! ### Informal statement of `MvPolynomial.omegaAlgHom`

Let R be a commutative ring, let n∈ℤ_{≥ 0}, and
let V be a finite set with n elements. A polynomial f in
the polynomial ring R[xᵥ:v∈ V] is symmetric if, for every
bijection π: V→ V, substituting x_{π(v)} for xᵥ
for every v∈ V leaves f unchanged. For
k∈ℤ_{≥ 0}, the elementary symmetric polynomial
eₖ and the complete homogeneous symmetric polynomial hₖ are

  eₖ=∑_T∏_{v∈ T}xᵥ

and

  hₖ=∑_M∏_{v∈ M}xᵥ,

where T runs over all k-element subsets of V, M runs over
all multisets of size k with elements from V, and each
element of M appears in the product as often as it occurs in
M. In particular e₀=h₀=1. By the fundamental theorem of
symmetric polynomials, every symmetric polynomial f equals
P(e₁,…,eₙ) for exactly one polynomial
P∈ R[y₁,…,yₙ], where P(e₁,…,eₙ) is obtained
from P by substituting eᵢ for yᵢ for 1≤ i≤ n. The
omega involution ω sends such an f to

  ω(f)=P(h₁,…,hₙ),

obtained from P by substituting hᵢ for yᵢ for
1≤ i≤ n. Thus ω is the R-algebra homomorphism
from the symmetric polynomials to the symmetric polynomials with
ω(eₖ)=hₖ for 1≤ k≤ n. When n=0, every
polynomial is a constant and ω(f)=f.
-/

/-- Let R be a commutative ring, let n∈ℤ_{≥ 0}, and let V be a finite set with n elements. A
polynomial f in the polynomial ring R[xᵥ:v∈ V] is symmetric if, for every bijection π: V→ V,
substituting x_{π(v)} for xᵥ for every v∈ V leaves f unchanged.

The full informal statement is in the module documentation directly above.
-/
noncomputable def MvPolynomial.omegaAlgHom (σ R : Type*)
    [CommRing R] [Fintype σ] [DecidableEq σ] :
    MvPolynomial.symmetricSubalgebra σ R →ₐ[R]
      MvPolynomial.symmetricSubalgebra σ R :=
  (MvPolynomial.aeval fun i : Fin (Fintype.card σ) =>
      (⟨MvPolynomial.hsymm σ R (i + 1),
        (MvPolynomial.mem_symmetricSubalgebra _).2
          (MvPolynomial.hsymm_isSymmetric σ R _)⟩ :
        MvPolynomial.symmetricSubalgebra σ R)).comp
    (MvPolynomial.esymmAlgEquiv σ R rfl).symm.toAlgHom

-- Combinatorics 494: Exponential Specialization


/-- Let ℚ[[x₁,x₂,…]] be the ring of formal power
series in the variables x₁,x₂,… with rational
coefficients. Its elements are the formal sums
f=∑_αc_α x^α, where
α=(α₁,α₂,…) runs over the sequences of
nonnegative integers with only finitely many nonzero terms,
c_α∈ℚ, and
x^α=x₁^{α₁}x₂^{α₂}⋯. For
m∈ℤ_{≥ 0}, write [x₁⋯ xₘ]f for the
coefficient c_α of the sequence α in which, for
each i∈ℤ_{≥ 1}, αᵢ=1 if i≤ m and
αᵢ=0 if i>m. For m=0 this is the constant term of
f. Let ℚ[[t]] be the ring of formal power series in
one variable t. The exponential specialization of f is

  ex(f)=∑_{m∈ℤ_{≥ 0}}
  tᵐ/(m!) [x₁⋯ xₘ]f.
-/
noncomputable def _root_.MvPowerSeries.exponentialSpecialization
    (f : MvPowerSeries ℕ ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun m => (Nat.factorial m : ℚ)⁻¹ *
    MvPowerSeries.coeff
      (∑ i ∈ Finset.range m, Finsupp.single i 1) f

-- Combinatorics 495: Scalar Product of Symmetric Polynomials


/-- Let n∈ℤ_{≥ 0}, write [n]={1,…,n}, so
that [0]=∅, and let R be a commutative ring. A
polynomial f in R[x₁,…,xₙ] is symmetric if, for every
bijection π:[n]→[n], substituting x_{π(i)} for
xᵢ for every i∈[n] leaves f unchanged. Let

  a_δ=∏_{1≤ i<j≤ n}(xᵢ-xⱼ),

so that a_δ=1 when n≤ 1. For a polynomial P and a
sequence λ=[λ₁,…,λₙ] of integers with
λᵢ≥ 0 for every i∈[n] and
λᵢ≥λᵢ₊₁ for 1≤ i≤ n-1, write
[x^{λ+δ}]P for the coefficient in P of the
monomial

  x^{λ+δ}=∏ᵢ₌₁ⁿxᵢ^{λᵢ+n-i}.

When n=0, the only such sequence is the empty one, and
x^{λ+δ}=1. For symmetric polynomials f and g in
R[x₁,…,xₙ], the scalar product of f and g is

  ⟨ f,g⟩ₙ=∑_λ
  [x^{λ+δ}](a_δ f)
  [x^{λ+δ}](a_δ g),

the sum taken over all sequences λ as above.
-/
noncomputable def symmetricScalarProduct {n : ℕ} {R : Type*}
    [CommRing R]
    (f g : MvPolynomial.symmetricSubalgebra (Fin n) R) : R :=
  let a : MvPolynomial (Fin n) R :=
    ∏ i, ∏ j ∈ Finset.Ioi i,
      (MvPolynomial.X i - MvPolynomial.X j)
  ∑ β ∈ (a * (f : MvPolynomial (Fin n) R)).support.filter
      (fun β => ∀ i j : Fin n, i < j → β j < β i),
    (a * f).coeff β * (a * g).coeff β

-- Combinatorics 497: Skew Shape


/-- Let m∈ℤ_{≥ 0}. A partition is a list
λ=[λ₁,…,λₘ] of integers, called its
parts, such that, if m≥ 1,

  λ₁≥λ₂≥⋯≥λₘ≥ 1.

If m=0, then λ is the empty list, called the empty
partition and written ∅. Set λₖ=0 for every
k∈ℤ_{≥ 1} with k>m. The diagram of λ is
the set

  D(λ)={(i,j)∈ℤ_{≥ 1}×ℤ_{≥ 1}
  :j≤λᵢ},

whose elements are called cells. The cell (i,j) is in row i
and column j, with rows numbered from 1 starting at the top
and columns numbered from 1 starting at the left. If m=0,
then D(∅)=∅. A partition is identified with
its diagram. For partitions λ and μ, write
μ⊆λ when D(μ)⊆ D(λ), that is,
when every cell of D(μ) is a cell of D(λ).

A skew shape is an ordered pair of partitions, an outer
partition λ and an inner partition μ, with
μ⊆λ. It is written λ/μ.
-/
structure SkewShape where
  outer : YoungDiagram
  inner : YoungDiagram
  inner_le_outer : inner ≤ outer

-- Combinatorics 498: Semistandard Young Tableau of Skew Shape


/-- Let λ/μ be a skew shape. For k∈ℤ_{≥ 1},
write λₖ for the k-th part of λ if λ
has at least k parts, and λₖ=0 otherwise, and define
μₖ in the same way. The cells of λ/μ are the pairs
(i,j)∈ℤ_{≥ 1}×ℤ_{≥ 1} with

  μᵢ<j≤λᵢ,

that is, the cells of D(λ) that are not cells of
D(μ).

A semistandard Young tableau of shape λ/μ is a
function T that assigns to each pair
(i,j)∈ℤ_{≥ 1}×ℤ_{≥ 1} an integer
T_{i,j}∈ℤ_{≥ 0}, subject to four conditions.
First, T_{i,j}≥ 1 for every cell (i,j) of λ/μ.
Second, the rows weakly increase from left to right, meaning
that

  T_{i,j}≤ T_{i,j'}

whenever (i,j) and (i,j') are cells of λ/μ with
j<j'. Third, the columns strictly increase from top to bottom,
meaning that

  T_{i,j}<T_{i',j}

whenever (i,j) and (i',j) are cells of λ/μ with
i<i'. Fourth, T_{i,j}=0 for every pair
(i,j)∈ℤ_{≥ 1}×ℤ_{≥ 1} that is
not a cell of λ/μ.
-/
structure SkewSemistandardYoungTableau (s : SkewShape) where
  entry : ℕ → ℕ → ℕ
  pos : ∀ {i j : ℕ}, (i, j) ∈ s.outer → (i, j) ∉ s.inner →
    0 < entry i j
  row_weak : ∀ {i j1 j2 : ℕ}, j1 < j2 →
    (i, j1) ∈ s.outer → (i, j1) ∉ s.inner →
    (i, j2) ∈ s.outer → (i, j2) ∉ s.inner →
    entry i j1 ≤ entry i j2
  col_strict : ∀ {i1 i2 j : ℕ}, i1 < i2 →
    (i1, j) ∈ s.outer → (i1, j) ∉ s.inner →
    (i2, j) ∈ s.outer → (i2, j) ∉ s.inner →
    entry i1 j < entry i2 j
  zeros : ∀ {i j : ℕ}, ¬ ((i, j) ∈ s.outer ∧ (i, j) ∉ s.inner) →
    entry i j = 0

-- Combinatorics 500: Standard Young Tableau of Skew Shape


/-- Let λ/μ be a skew shape. For k∈ℤ_{≥ 1},
write λₖ for the k-th part of λ if λ
has at least k parts, and λₖ=0 otherwise, and define
μₖ in the same way. The cells of λ/μ are the pairs
(i,j)∈ℤ_{≥ 1}×ℤ_{≥ 1} with

  μᵢ<j≤λᵢ,

that is, the cells of D(λ) that are not cells of
D(μ). Let n∈ℤ_{≥ 0} be the number of cells of
λ/μ, and write [n]={1,…,n}, so that
[0]=∅.

A standard Young tableau of shape λ/μ is a
semistandard Young tableau T of shape λ/μ such that
the map (i,j)↦ T_{i,j} sends the cells of λ/μ
bijectively onto [n]. If μ=∅, a standard Young
tableau of shape λ/∅ is also called a standard
Young tableau of shape λ.
-/
structure SkewStandardYoungTableau (s : SkewShape) extends
    SkewSemistandardYoungTableau s where
  bijOn : Set.BijOn (fun c : ℕ × ℕ => entry c.1 c.2)
    ↑(s.outer.cells \ s.inner.cells)
    (Set.Icc 1 (s.outer.cells \ s.inner.cells).card)

end MetaMathlibExt

end
