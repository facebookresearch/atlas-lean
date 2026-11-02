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

/-- **The omega homomorphism on symmetric polynomials.** Let $R$ be a commutative ring and let $V$
be a finite set with $n$ elements. A polynomial in $R[x_v : v \in V]$ is symmetric if it is
unchanged by every permutation of the variables. For $k \ge 0$, the elementary symmetric polynomial
$e_k$ is the sum of $\prod_{v \in T} x_v$ over all $k$-element subsets $T \subseteq V$, and the
complete homogeneous symmetric polynomial $h_k$ is the sum of $\prod_{v \in M} x_v$ over all
multisets $M$ of size $k$ with elements from $V$, each element counted with its multiplicity.
Every symmetric polynomial $f$ equals $P(e_1, \dots, e_n)$ for exactly one polynomial
$P \in R[y_1, \dots, y_n]$. The omega homomorphism $\omega$ is the $R$-algebra homomorphism from the
symmetric polynomials in $R[x_v : v \in V]$ to themselves given by
$\omega(P(e_1, \dots, e_n)) = P(h_1, \dots, h_n)$; equivalently, it is the unique $R$-algebra
homomorphism with $\omega(e_k) = h_k$ for $1 \le k \le n$. -/
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


/-- **Exponential specialization.** Let $\mathbb{Q}[[x_1, x_2, \dots]]$ be the ring of formal
power series in the variables $x_1, x_2, \dots$ with rational coefficients: its elements are the
formal sums $f = \sum_\alpha c_\alpha x^\alpha$, where $\alpha = (\alpha_1, \alpha_2, \dots)$
runs over the sequences of nonnegative integers with only finitely many nonzero terms,
$c_\alpha \in \mathbb{Q}$ and $x^\alpha = x_1^{\alpha_1} x_2^{\alpha_2} \cdots$. For $m \ge 0$,
write $[x_1 \cdots x_m] f$ for the coefficient in $f$ of the monomial $x_1 x_2 \cdots x_m$; for
$m = 0$ this is the constant term of $f$. The exponential specialization of $f$ is the formal
power series in one variable $t$

$$\operatorname{ex}(f) = \sum_{m \ge 0} \frac{[x_1 \cdots x_m] f}{m!} \, t^m \in \mathbb{Q}[[t]].$$
-/
noncomputable def _root_.MvPowerSeries.exponentialSpecialization
    (f : MvPowerSeries ℕ ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun m => (Nat.factorial m : ℚ)⁻¹ *
    MvPowerSeries.coeff
      (∑ i ∈ Finset.range m, Finsupp.single i 1) f

-- Combinatorics 495: Scalar Product of Symmetric Polynomials


/-- **Scalar product of symmetric polynomials.** Let $n \ge 0$, let $R$ be a commutative ring, and
call a polynomial in $R[x_1, \dots, x_n]$ symmetric if it is unchanged by every permutation of the
variables. Let $a_\delta = \prod_{1 \le i < j \le n} (x_i - x_j)$, so that $a_\delta = 1$ when
$n \le 1$. For a sequence $\lambda = (\lambda_1, \dots, \lambda_n)$ of
integers with $\lambda_1 \ge \lambda_2 \ge \dots \ge \lambda_n \ge 0$, write $c_\lambda(P)$ for the
coefficient in a polynomial $P$ of the monomial
$x^{\lambda+\delta} = \prod_{i=1}^{n} x_i^{\lambda_i + n - i}$; when $n = 0$ the only such sequence
is the empty one and $x^{\lambda+\delta} = 1$. The scalar product of symmetric polynomials $f$ and
$g$ in $R[x_1, \dots, x_n]$ is

$$\langle f, g \rangle_n = \sum_{\lambda} c_\lambda(a_\delta f) \, c_\lambda(a_\delta g),$$

the sum taken over all sequences $\lambda$ as above; only finitely many terms are nonzero. -/
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


/-- **Skew shape.** A partition is a finite weakly decreasing sequence
$\lambda = (\lambda_1 \ge \lambda_2 \ge \dots \ge \lambda_m)$ of positive integers, possibly empty
($m = 0$); set $\lambda_k = 0$ for $k > m$. Its diagram is the set
$D(\lambda) = \{(i, j) \in \mathbb{Z}_{\ge 1} \times \mathbb{Z}_{\ge 1} : j \le \lambda_i\}$ of
cells, where the cell $(i, j)$ lies in row $i$ and column $j$, and a partition is identified with
its diagram. For partitions $\lambda$ and $\mu$ write $\mu \subseteq \lambda$ when
$D(\mu) \subseteq D(\lambda)$. A skew shape $\lambda/\mu$ is an ordered pair of partitions, an
outer partition $\lambda$ and an inner partition $\mu$, with $\mu \subseteq \lambda$. -/
structure SkewShape where
  outer : YoungDiagram
  inner : YoungDiagram
  inner_le_outer : inner ≤ outer

-- Combinatorics 498: Semistandard Young Tableau of Skew Shape


/-- **Semistandard Young tableau of skew shape.** Let $\lambda/\mu$ be a skew shape, and write
$\lambda_k$ and $\mu_k$ for the $k$-th parts of $\lambda$ and $\mu$, with $\lambda_k = 0$
($\mu_k = 0$) when $\lambda$ ($\mu$) has fewer than $k$ parts. The cells of $\lambda/\mu$ are the
pairs $(i, j) \in \mathbb{Z}_{\ge 1} \times \mathbb{Z}_{\ge 1}$ with $\mu_i < j \le \lambda_i$,
that is, the cells of $D(\lambda)$ that are not cells of $D(\mu)$. A semistandard Young tableau
of shape $\lambda/\mu$ is a function $T$ assigning a nonnegative integer $T_{i,j}$ to every pair
$(i, j) \in \mathbb{Z}_{\ge 1} \times \mathbb{Z}_{\ge 1}$ such that $T_{i,j} \ge 1$ for every cell
$(i, j)$ of $\lambda/\mu$; $T_{i,j} \le T_{i,j'}$ whenever $(i, j)$ and $(i, j')$ are cells of
$\lambda/\mu$ with $j < j'$ (rows weakly increase); $T_{i,j} < T_{i',j}$ whenever $(i, j)$ and
$(i', j)$ are cells of $\lambda/\mu$ with $i < i'$ (columns strictly increase); and $T_{i,j} = 0$
for every pair $(i, j)$ that is not a cell of $\lambda/\mu$. -/
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


/-- **Standard Young tableau of skew shape.** Let $\lambda/\mu$ be a skew shape, let $n$ be the
number of cells of $\lambda/\mu$ (the cells of $D(\lambda)$ that are not cells of $D(\mu)$), and
write $[n] = \{1, \dots, n\}$, so that $[0] = \emptyset$. A standard Young tableau of shape
$\lambda/\mu$ is a semistandard Young tableau $T$ of shape $\lambda/\mu$ such that the map
$(i, j) \mapsto T_{i,j}$ sends the cells of $\lambda/\mu$ bijectively onto $[n]$. If
$\mu = \emptyset$, a standard Young tableau of shape $\lambda/\emptyset$ is also called a standard
Young tableau of shape $\lambda$. -/
structure SkewStandardYoungTableau (s : SkewShape) extends
    SkewSemistandardYoungTableau s where
  bijOn : Set.BijOn (fun c : ℕ × ℕ => entry c.1 c.2)
    ↑(s.outer.cells \ s.inner.cells)
    (Set.Icc 1 (s.outer.cells \ s.inner.cells).card)

end MetaMathlibExt

end
