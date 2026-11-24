/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

@[expose] public section

/-!
# Principal minors of cyclic Fourier matrices

Given a chosen primitive `M`-th root of unity and a finite subset of
`ZMod M`, this file defines the corresponding principal Fourier minor and its
determinant.
-/

namespace Fourier

/-- **Primitive root of unity data.** For a natural number $M$ and a commutative ring $R$, root
data of order $M$ in $R$ consists of an element $\zeta \in R$ that is a primitive $M$-th root of
unity, together with the condition $M \ge 2$. -/
structure RootData (M : ℕ) (R : Type*) [CommRing R] where
  zeta : R
  order_ge : 2 ≤ M
  isPrimitiveRoot : IsPrimitiveRoot zeta M

/-- **Principal Fourier minor.** Let $M \ge 2$, let $R$ be a commutative ring, let $\zeta \in R$
be a primitive $M$-th root of unity, and let $S$ be a finite subset of $\mathbb{Z}/M\mathbb{Z}$.
The principal Fourier minor indexed by $S$ is the $S \times S$ matrix over $R$ whose $(i, j)$
entry is $\zeta^{n}$, where $n \in \{0, \dots, M-1\}$ is the representative of the product $ij$
in $\mathbb{Z}/M\mathbb{Z}$. -/
noncomputable def principalMinorMatrix (M : ℕ) {R : Type*} [CommRing R]
    (root : RootData M R) (S : Finset (ZMod M)) : Matrix S S R := by
  letI : NeZero M := ⟨by have := root.order_ge; omega⟩
  exact fun i j ↦ root.zeta ^ (i.val * j.val).val

/-- **Determinant of a principal Fourier minor.** Let $M \ge 2$, let $R$ be a commutative ring,
let $\zeta \in R$ be a primitive $M$-th root of unity, and let $S$ be a finite subset of
$\mathbb{Z}/M\mathbb{Z}$. The principal Fourier minor determinant of $S$ is the determinant in $R$
of the principal Fourier minor indexed by $S$. -/
noncomputable def principalMinorDet (M : ℕ) {R : Type*} [CommRing R]
    (root : RootData M R) (S : Finset (ZMod M)) : R :=
  (principalMinorMatrix M root S).det

/-- **Entries of a principal Fourier minor.** Let $M \ge 2$, let $R$ be a commutative ring, let
$\zeta \in R$ be a primitive $M$-th root of unity, and let $S$ be a finite subset of
$\mathbb{Z}/M\mathbb{Z}$. For all $i, j \in S$, the $(i, j)$ entry of the principal Fourier minor
indexed by $S$ equals $\zeta^{n}$, where $n \in \{0, \dots, M-1\}$ is the representative of $ij$
in $\mathbb{Z}/M\mathbb{Z}$. -/
@[simp]
theorem principalMinorMatrix_apply (M : ℕ) {R : Type*} [CommRing R]
    (root : RootData M R) (S : Finset (ZMod M)) (i j : S) :
    principalMinorMatrix M root S i j = root.zeta ^ (i.val * j.val).val := by
  simp [principalMinorMatrix]

/-- **Determinant of the empty principal Fourier minor.** Let $M \ge 2$, let $R$ be a commutative
ring and let $\zeta \in R$ be a primitive $M$-th root of unity. The determinant of the principal
Fourier minor indexed by the empty subset of $\mathbb{Z}/M\mathbb{Z}$ equals $1$. -/
@[simp]
theorem principalMinorDet_empty (M : ℕ) {R : Type*} [CommRing R]
    (root : RootData M R) : principalMinorDet M root ∅ = 1 := by
  simp [principalMinorDet]

/-- **Determinant of a singleton principal Fourier minor.** Let $M \ge 2$, let $R$ be a
commutative ring, let $\zeta \in R$ be a primitive $M$-th root of unity, and let
$a \in \mathbb{Z}/M\mathbb{Z}$. The determinant of the principal Fourier minor indexed by $\{a\}$
equals $\zeta^{n}$, where $n \in \{0, \dots, M-1\}$ is the representative of $a^2$ in
$\mathbb{Z}/M\mathbb{Z}$. -/
@[simp]
theorem principalMinorDet_singleton (M : ℕ) {R : Type*} [CommRing R]
    (root : RootData M R) (a : ZMod M) :
    principalMinorDet M root {a} = root.zeta ^ (a * a).val := by
  simp [principalMinorDet]

end Fourier
