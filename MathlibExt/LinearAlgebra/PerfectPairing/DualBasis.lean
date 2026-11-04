/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

@[expose] public section

open Module

/-!
# Dual bases for perfect pairings

Given a perfect pairing `B : M →ₗ[A] N →ₗ[A] A` between `A`-modules `M`
and `N`, and a basis `b` of `N` indexed by a finite decidable type, the
canonical left dual basis is obtained by transporting the ordinary dual
basis along the inverse of the pairing equivalence.

## Main definitions

* `LinearMap.IsPerfPair.dualBasis`: the canonical left dual basis,
  `b.dualBasis.map B.toPerfPair.symm`.

## Main results

* `LinearMap.IsPerfPair.dualBasis_apply`: evaluation formula
  `B (dualBasis B b i) (b j) = if j = i then 1 else 0`.
* `LinearMap.IsPerfPair.eq_dualBasis_of`: uniqueness of any basis
  satisfying that formula.
* `LinearMap.IsPerfPair.exists_dualBasis` and
  `LinearMap.IsPerfPair.existsUnique_dualBasis`: existence and unique
  existence wrappers.
-/

namespace LinearMap.IsPerfPair

variable {A M N ι : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N]
variable [DecidableEq ι] [Finite ι]
variable (B : M →ₗ[A] N →ₗ[A] A) [B.IsPerfPair]

/-- **Dual basis with respect to a perfect pairing.** Let $A$ be a commutative ring, let $M$
and $N$ be $A$-modules, and let $B : M \times N \to A$ be a perfect pairing, that is, an
$A$-bilinear map such that $x \mapsto B(x, \cdot)$ is a linear isomorphism $M \to N^*$ and
$y \mapsto B(\cdot, y)$ is a linear isomorphism $N \to M^*$. Let $b = (b_i)_{i \in \iota}$ be
a basis of $N$ indexed by a finite type $\iota$, and let $(b_i^*)_{i \in \iota}$ be its dual
basis of $N^*$, where $b_i^*(b_j)$ is $1$ if $j = i$ and $0$ otherwise. The dual basis of $b$
with respect to $B$ is the basis of $M$ whose $i$-th vector is the image of $b_i^*$ under the
inverse of the isomorphism $M \to N^*$, $x \mapsto B(x, \cdot)$. -/
noncomputable def dualBasis (b : Basis ι A N) : Basis ι A M :=
  b.dualBasis.map B.toPerfPair.symm

/-- **Evaluation of the dual basis.** Let $A$ be a commutative ring, let $M$ and $N$ be
$A$-modules, let $B : M \times N \to A$ be a perfect pairing, and let $b = (b_i)_{i \in \iota}$
be a basis of $N$ indexed by a finite type $\iota$. Write $(b_i^\vee)_{i \in \iota}$ for the
dual basis of $b$ with respect to $B$, a basis of $M$. Then for all $i, j \in \iota$, the value
$B(b_i^\vee, b_j)$ equals $1$ if $j = i$ and $0$ otherwise. -/
@[simp]
theorem dualBasis_apply (b : Basis ι A N) (i j : ι) :
    B (dualBasis B b i) (b j) = if j = i then 1 else 0 := by
  rw [dualBasis, Basis.map_apply, ← LinearMap.toPerfPair_apply,
    LinearEquiv.apply_symm_apply, Basis.dualBasis_apply_self]

/-- **Uniqueness of the dual basis.** Let $A$ be a commutative ring, let $M$ and $N$ be
$A$-modules, let $B : M \times N \to A$ be a perfect pairing, and let $b = (b_i)_{i \in \iota}$
be a basis of $N$ indexed by a finite type $\iota$. If $b' = (b'_i)_{i \in \iota}$ is a basis
of $M$ such that for all $i, j \in \iota$ the value $B(b'_i, b_j)$ equals $1$ if $j = i$ and
$0$ otherwise, then $b'$ is the dual basis of $b$ with respect to $B$. -/
theorem eq_dualBasis_of (b : Basis ι A N) (b' : Basis ι A M)
    (h : ∀ i j, B (b' i) (b j) = if j = i then 1 else 0) :
    b' = dualBasis B b := by
  refine Basis.eq_of_apply_eq fun i => ?_
  have key : B.toPerfPair (b' i) = b.dualBasis i := by
    apply b.ext
    intro j
    rw [LinearMap.toPerfPair_apply, h i j, b.dualBasis_apply_self]
  calc b' i = B.toPerfPair.symm (B.toPerfPair (b' i)) :=
        (B.toPerfPair.symm_apply_apply (b' i)).symm
    _ = B.toPerfPair.symm (b.dualBasis i) := by rw [key]
    _ = dualBasis B b i := by simp only [dualBasis, Basis.map_apply]

/-- **Existence of a dual basis for a perfect pairing.** Let $A$ be a commutative ring, let $M$
and $N$ be $A$-modules, let $B : M \times N \to A$ be a perfect pairing, and let
$b = (b_i)_{i \in \iota}$ be a basis of $N$ indexed by a finite type $\iota$. Then there is a
basis $(b'_i)_{i \in \iota}$ of $M$ such that for all $i, j \in \iota$ the value $B(b'_i, b_j)$
equals $1$ if $j = i$ and $0$ otherwise. -/
theorem exists_dualBasis (b : Basis ι A N) :
    ∃ b' : Basis ι A M, ∀ i j, B (b' i) (b j) = if j = i then 1 else 0 :=
  ⟨dualBasis B b, fun i j => dualBasis_apply B b i j⟩

/-- **Existence and uniqueness of the dual basis for a perfect pairing.** Let $A$ be a
commutative ring, let $M$ and $N$ be $A$-modules, let $B : M \times N \to A$ be a perfect
pairing, and let $b = (b_i)_{i \in \iota}$ be a basis of $N$ indexed by a finite type $\iota$.
Then there is exactly one basis $(b'_i)_{i \in \iota}$ of $M$ such that for all
$i, j \in \iota$ the value $B(b'_i, b_j)$ equals $1$ if $j = i$ and $0$ otherwise. -/
theorem existsUnique_dualBasis (b : Basis ι A N) :
    ∃! b' : Basis ι A M, ∀ i j, B (b' i) (b j) = if j = i then 1 else 0 := by
  refine ⟨dualBasis B b, fun i j => dualBasis_apply B b i j, fun b' hb' => ?_⟩
  exact eq_dualBasis_of B b b' hb'

end LinearMap.IsPerfPair
