/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.QuadraticForm.Prod

@[expose] public section

/-!
# Systems of quadratic forms

This file defines the pointwise orthogonal sum of two systems of quadratic
forms with the same index type.
-/

namespace QuadraticForm

variable {R M N ι : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/-- **Orthogonal sum of systems of quadratic forms.** Let $R$ be a commutative semiring, let
$M$ and $N$ be $R$-modules, and let $(Q_i)_{i \in \iota}$ and $(Q'_i)_{i \in \iota}$ be families
of quadratic forms on $M$ and on $N$ indexed by the same type $\iota$. Their pointwise
orthogonal sum is the family $(Q_i \oplus Q'_i)_{i \in \iota}$ of quadratic forms on
$M \times N$, where $Q_i \oplus Q'_i$ is the orthogonal sum given by
$(Q_i \oplus Q'_i)(x, y) = Q_i(x) + Q'_i(y)$. -/
def systemOrthogonalSum (Q : ι → QuadraticForm R M) (Q' : ι → QuadraticForm R N) :
    ι → QuadraticForm R (M × N) :=
  fun i ↦ (Q i).prod (Q' i)

/-- **Evaluating an orthogonal sum of systems of quadratic forms.** Let $R$ be a commutative
semiring, let $M$ and $N$ be $R$-modules, and let $(Q_i)_{i \in \iota}$ and
$(Q'_i)_{i \in \iota}$ be families of quadratic forms on $M$ and on $N$ indexed by the same
type $\iota$. For every index $i$ and every $(x, y) \in M \times N$, the $i$-th form of their
pointwise orthogonal sum takes the value $Q_i(x) + Q'_i(y)$ at $(x, y)$. -/
@[simp]
theorem systemOrthogonalSum_apply (Q : ι → QuadraticForm R M)
    (Q' : ι → QuadraticForm R N) (i : ι) (x : M × N) :
    systemOrthogonalSum Q Q' i x = Q i x.1 + Q' i x.2 := by
  simp [systemOrthogonalSum]

/-- **Orthogonal sum of systems on the left summand.** Let $R$ be a commutative semiring,
let $M$ and $N$ be $R$-modules, and let $(Q_i)_{i \in \iota}$ and $(Q'_i)_{i \in \iota}$ be
families of quadratic forms on $M$ and on $N$ indexed by the same type $\iota$. For every
index $i$ and every $x \in M$, the $i$-th form of their pointwise orthogonal sum takes the
value $Q_i(x)$ at $(x, 0) \in M \times N$. -/
@[simp]
theorem systemOrthogonalSum_inl (Q : ι → QuadraticForm R M)
    (Q' : ι → QuadraticForm R N) (i : ι) (x : M) :
    systemOrthogonalSum Q Q' i (x, 0) = Q i x := by
  simp

/-- **Orthogonal sum of systems on the right summand.** Let $R$ be a commutative semiring,
let $M$ and $N$ be $R$-modules, and let $(Q_i)_{i \in \iota}$ and $(Q'_i)_{i \in \iota}$ be
families of quadratic forms on $M$ and on $N$ indexed by the same type $\iota$. For every
index $i$ and every $y \in N$, the $i$-th form of their pointwise orthogonal sum takes the
value $Q'_i(y)$ at $(0, y) \in M \times N$. -/
@[simp]
theorem systemOrthogonalSum_inr (Q : ι → QuadraticForm R M)
    (Q' : ι → QuadraticForm R N) (i : ι) (y : N) :
    systemOrthogonalSum Q Q' i (0, y) = Q' i y := by
  simp

end QuadraticForm
