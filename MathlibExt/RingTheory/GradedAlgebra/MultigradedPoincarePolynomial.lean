/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.GradedAlgebra.MultigradedPoincareFiniteSupport

/-!
# Multigraded Poincaré polynomial

This file packages the raw edge-6 Poincaré coefficient function as an
`AddMonoidAlgebra` element over homological degree times multidegree, and
pins each of its coefficients to the corresponding edge-3 Betti number.

Source: Benjamin Braun and Brian Davis, “Antichain Simplices,”
Journal of Integer Sequences 23 (2020),
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`,
exact line 876. That line states the Hilbert syzygy consequence: over a
polynomial ring, the Poincaré series of every finitely generated module
is a polynomial. This edge formalizes the conditional polynomial
realization behind that line: under the two structural resolution
hypotheses — every homogeneous basis index type is finite, and those
types are empty above the bound — the edge-6 coefficient function has
finite support and hence defines a polynomial.

Conditional finite-resolution bridge, not the full Hilbert syzygy
theorem: the hypotheses describe the terms of an already-supplied
finite-rank terminating resolution and say nothing about Betti numbers
or coefficient supports, so the polynomial and its coefficient equation
are genuinely derived from the resolution geometry. In particular,
nothing here constructs such a resolution for every finitely generated
module over `MvPolynomial`, proves the classical bound by the number of
variables, or assumes minimality or comparison data. That existence step
is a later Hilbert-syzygy edge.

Main definitions and results:

* `MetaMathlibExt.multigradedPoincarePolynomial`: the Poincaré
  coefficient family packaged as an `AddMonoidAlgebra` element, using
  edge-6 finite support from the two structural resolution hypotheses.
* `MetaMathlibExt.multigradedPoincarePolynomial_coeff`: evaluating the
  polynomial at `(i, α)` returns exactly
  `multigradedBettiNumber data α i`.
-/

@[expose] public section

namespace MetaMathlibExt

universe u

/-- **Multigraded Poincaré polynomial.** Let $K$ be a field, let $R = K[x_1, \dots, x_n]$, let
$M$ be a multigraded $R$-module, and let $D$ be base-change data for a multigraded free
resolution $F_\bullet$ of $M$ in which $F_i$ has a homogeneous basis indexed by a finite set
$\iota_i$, with $\iota_i$ empty for every $i > b$ for a fixed $b \in \mathbb{N}$. The
multigraded Poincaré polynomial of $D$ is the element of the monoid algebra
$\mathbb{N}[\mathbb{N} \times \mathbb{Z}^n]$ whose coefficient at $(i, \alpha)$ is the
multigraded Betti number $\beta_{i,\alpha}(D)$ of $D$ in homological degree $i$ and multidegree
$\alpha$; the hypotheses on the $\iota_i$ make these coefficients finitely supported. -/
public noncomputable def multigradedPoincarePolynomial {K : Type u} [Field K] {n : ℕ}
    {M : Type u} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    {targetGraded : MultigradedPolynomialModule K n M}
    {resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M)}
    {ι : ℕ → Type u}
    {res : MultigradedFreeResolution K n M targetGraded resolution ι}
    (data : MultigradedBaseChange targetGraded resolution ι res)
    (bound : ℕ)
    (finiteBasis : ∀ i, Finite (ι i))
    (emptyAbove : ∀ i, bound < i → IsEmpty (ι i)) :
    AddMonoidAlgebra Nat (Nat × (Fin n →₀ Int)) :=
  AddMonoidAlgebra.ofCoeff (Finsupp.ofSupportFinite (multigradedPoincareCoefficients data) (by
    have h : Function.HasFiniteSupport (multigradedPoincareCoefficients data) :=
      multigradedPoincareCoefficients_hasFiniteSupport_of_finiteResolution data
        bound finiteBasis emptyAbove
    unfold Function.HasFiniteSupport at h
    exact h))

/-- **Coefficients of the multigraded Poincaré polynomial.** Let $K$ be a field, let
$R = K[x_1, \dots, x_n]$, let $M$ be a multigraded $R$-module, and let $D$ be base-change data
for a multigraded free resolution $F_\bullet$ of $M$ in which $F_i$ has a homogeneous basis
indexed by a finite set $\iota_i$, with $\iota_i$ empty for every $i > b$ for a fixed
$b \in \mathbb{N}$. For every $i \in \mathbb{N}$ and $\alpha \in \mathbb{Z}^n$, the coefficient
at $(i, \alpha)$ of the multigraded Poincaré polynomial of $D$ is the multigraded Betti number
$\beta_{i,\alpha}(D)$ of $D$ in homological degree $i$ and multidegree $\alpha$. -/
public theorem multigradedPoincarePolynomial_coeff {K : Type u} [Field K] {n : ℕ}
    {M : Type u} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    {targetGraded : MultigradedPolynomialModule K n M}
    {resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M)}
    {ι : ℕ → Type u}
    {res : MultigradedFreeResolution K n M targetGraded resolution ι}
    (data : MultigradedBaseChange targetGraded resolution ι res)
    (bound : ℕ)
    (finiteBasis : ∀ i, Finite (ι i))
    (emptyAbove : ∀ i, bound < i → IsEmpty (ι i))
    (i : ℕ) (α : Fin n →₀ Int) :
    (multigradedPoincarePolynomial data bound finiteBasis emptyAbove).coeff (i, α) =
      multigradedBettiNumber data α i := by
  unfold multigradedPoincarePolynomial
  rw [AddMonoidAlgebra.coeff_ofCoeff, Finsupp.ofSupportFinite_coe]
  exact multigradedPoincareCoefficients_apply data i α

end MetaMathlibExt
