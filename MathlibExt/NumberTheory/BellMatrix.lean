/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Bell matrices

A Bell matrix is the Riordan array `(g(X), X * g(X))`. The source works over integer power
series normalized by `g(0) = 1`; here this is generalized to power series over a commutative ring
whose constant coefficient is a unit, the usual condition needed for a ring-valued Riordan array.

Source: Paul Barry, *On the Central Coefficients of Bell Matrices*,
<https://cs.uwaterloo.ca/journals/JIS/VOL14/Barry3/barry132.tex>.

JIS concept: `jis_sem_70c33473bf189e979a585e79`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Bell matrix.** Let $R$ be a commutative ring. A Bell matrix over $R$ is given by a formal
power series $g \in R[[X]]$ whose constant coefficient is a unit of $R$. The corresponding
Riordan-array pair is $(g, Xg)$. -/
structure BellMatrix (R : Type*) [CommRing R] where
  g : PowerSeries R
  isUnit_const : IsUnit g.constantCoeff

/-- **Second component of a Bell matrix.** For a Bell matrix over a commutative ring $R$ given by
the power series $g$, the second component of its Riordan-array pair is the power series
$h = Xg \in R[[X]]$. -/
noncomputable def BellMatrix.h {R : Type*} [CommRing R] (M : BellMatrix R) :
    PowerSeries R :=
  PowerSeries.X * M.g

/-- **Entries of a Bell matrix.** For a Bell matrix over a commutative ring $R$ given by the
power series $g$, and natural numbers $n$ and $k$, the entry in row $n$ and column $k$ is the
coefficient of $X^n$ in $g \cdot (Xg)^k$. -/
noncomputable def BellMatrix.entry {R : Type*} [CommRing R] (M : BellMatrix R)
    (n k : ℕ) : R :=
  (M.g * (PowerSeries.X * M.g) ^ k).coeff n

end

end MetaMathlibExt
