/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv

@[expose] public section

namespace MvPolynomial

/-- **Mixed differential operator.** Let $R$ be a commutative ring, let $\sigma$ be an index
type, and write $\partial_s$ for the partial derivative with respect to $x_s$ on the polynomial
ring $R[x_s : s \in \sigma]$. For a finite list $(i_1, \dots, i_k)$ of indices in $\sigma$
(repetitions allowed) and a polynomial $p \in R[x_s : s \in \sigma]$, the mixed differential of
$p$ along the list is $(1 - \partial_{i_k}) \cdots (1 - \partial_{i_1})\, p$: the operator
$1 - \partial_{i_1}$ is applied first and $1 - \partial_{i_k}$ last. Along the empty list it is
$p$. -/
public noncomputable def mixedDifferential {σ R : Type*} [CommRing R]
    (indices : List σ) (p : MvPolynomial σ R) : MvPolynomial σ R :=
  indices.foldl (fun q i ↦ q - pderiv i q) p

/-- **Mixed differential along the empty list.** Let $R$ be a commutative ring, let $\sigma$ be
an index type, and let $p \in R[x_s : s \in \sigma]$. The mixed differential of $p$ along the
empty list of indices is $p$ itself. -/
@[simp]
public theorem mixedDifferential_nil {σ R : Type*} [CommRing R]
    (p : MvPolynomial σ R) : mixedDifferential [] p = p := by
  rfl

/-- **Mixed differential along a list with a given first index.** Let $R$ be a commutative ring,
let $\sigma$ be an index type, let $i \in \sigma$, let $L$ be a finite list of indices in
$\sigma$, and let $p \in R[x_s : s \in \sigma]$. The mixed differential of $p$ along the list
that starts with $i$ and continues with $L$ equals the mixed differential along $L$ of
$p - \partial_i p$, where $\partial_i$ is the partial derivative with respect to $x_i$. -/
public theorem mixedDifferential_cons {σ R : Type*} [CommRing R]
    (i : σ) (is : List σ) (p : MvPolynomial σ R) :
    mixedDifferential (i :: is) p = mixedDifferential is (p - pderiv i p) := by
  rfl

/-- **The mixed differential ignores the order of the indices.** Let $R$ be a commutative ring,
let $\sigma$ be an index type, and let $p \in R[x_s : s \in \sigma]$. If two finite lists $L$ and
$L'$ of indices in $\sigma$ are permutations of each other, then the mixed differentials of $p$
along $L$ and along $L'$ are equal. -/
public theorem mixedDifferential_eq_of_perm {σ R : Type*} [CommRing R]
    {is js : List σ} (h : is.Perm js) (p : MvPolynomial σ R) :
    mixedDifferential is p = mixedDifferential js p := by
  induction h generalizing p with
  | nil => rfl
  | cons i h ih =>
      rw [mixedDifferential_cons, mixedDifferential_cons]
      exact ih _
  | swap i j is =>
      rw [mixedDifferential_cons, mixedDifferential_cons, mixedDifferential_cons,
        mixedDifferential_cons]
      congr 1
      rw [map_sub, map_sub, pderiv_comm]
      abel
  | trans h₁ h₂ ih₁ ih₂ => exact (ih₁ p).trans (ih₂ p)

/-- **Mixed differential along a concatenated list.** Let $R$ be a commutative ring, let $\sigma$
be an index type, let $p \in R[x_s : s \in \sigma]$, and let $L$ and $L'$ be finite lists of
indices in $\sigma$. The mixed differential of $p$ along the concatenation of $L$ followed by
$L'$ equals the mixed differential along $L'$ of the mixed differential of $p$ along $L$. -/
public theorem mixedDifferential_append {σ R : Type*} [CommRing R]
    (is js : List σ) (p : MvPolynomial σ R) :
    mixedDifferential (is ++ js) p = mixedDifferential js (mixedDifferential is p) := by
  simp only [mixedDifferential, List.foldl_append]

/-- **Partial derivatives commute with the mixed differential.** Let $R$ be a commutative ring,
let $i \in \sigma$, let $L$ be a finite list of indices in $\sigma$, and let
$p \in R[x_s : s \in \sigma]$. Writing $\partial_i$ for the partial derivative with respect to
$x_i$, the partial derivative $\partial_i$ of the mixed differential of $p$ along $L$ equals the
mixed differential along $L$ of $\partial_i p$. -/
public theorem pderiv_mixedDifferential {σ R : Type*} [CommRing R]
    (i : σ) (is : List σ) (p : MvPolynomial σ R) :
    pderiv i (mixedDifferential is p) = mixedDifferential is (pderiv i p) := by
  induction is generalizing p with
  | nil => rfl
  | cons j js ih =>
      rw [mixedDifferential_cons, mixedDifferential_cons, ih]
      congr 1
      rw [map_sub, pderiv_comm]

end MvPolynomial
