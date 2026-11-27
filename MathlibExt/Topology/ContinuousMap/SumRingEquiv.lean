/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Logic.Equiv.Functor

/-!
# Continuous functions on a binary disjoint sum

For arbitrary topological spaces `X,Y` and a topological semiring `R`,
restriction along the two inclusions identifies `C(X⊕Y,R)` with
`C(X,R) × C(Y,R)` as semirings. The inverse uses the sum eliminator and
has exactly the prescribed function on each summand. The two domain
universes and coefficient universe are independent.

Either summand may be empty. No compactness, norm, additive inverses or
commutative-multiplication assumption is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe uX uY v

namespace ContinuousMap

variable (X : Type uX) (Y : Type uY) (R : Type v)
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace R]
variable [Semiring R] [IsTopologicalSemiring R]

/-- The semiring equivalence given by left and right restriction, with sum-eliminator recombination
as inverse.

Here `X,Y` are arbitrary topological spaces and `R` is a topological semiring, with independent
universes. -/
def sumRingEquiv : C(X ⊕ Y, R) ≃+* C(X, R) × C(Y, R) where
  toFun f :=
    (⟨fun x => f (Sum.inl x), f.continuous.comp continuous_inl⟩,
     ⟨fun y => f (Sum.inr y), f.continuous.comp continuous_inr⟩)
  invFun p := ⟨Sum.elim p.1 p.2, p.1.continuous.sumElim p.2.continuous⟩
  left_inv f := by
    apply ContinuousMap.ext
    intro z
    exact congrFun ((Equiv.sumArrowEquivProdArrow X Y R).left_inv f) z
  right_inv p := by
    apply Prod.ext
    · apply ContinuousMap.ext
      intro x
      rfl
    · apply ContinuousMap.ext
      intro y
      rfl
  map_mul' f g := by
    apply Prod.ext <;> apply ContinuousMap.ext <;> intro z <;> rfl
  map_add' f g := by
    apply Prod.ext <;> apply ContinuousMap.ext <;> intro z <;> rfl

/-- The first restricted function has value `f(inl x)` on the left summand.

Here `X,Y` are arbitrary topological spaces and `R` is a topological semiring, with independent
universes.

```lean
theorem sumRingEquiv_fst_apply (f : C(X ⊕ Y, R)) (x : X) :
    (sumRingEquiv X Y R f).1 x = f (Sum.inl x)
``` -/
@[simp]
theorem sumRingEquiv_fst_apply (f : C(X ⊕ Y, R)) (x : X) :
    (sumRingEquiv X Y R f).1 x = f (Sum.inl x) := rfl

/-- The second restricted function has value `f(inr y)` on the right summand.

Here `X,Y` are arbitrary topological spaces and `R` is a topological semiring, with independent
universes.

```lean
theorem sumRingEquiv_snd_apply (f : C(X ⊕ Y, R)) (y : Y) :
    (sumRingEquiv X Y R f).2 y = f (Sum.inr y)
``` -/
@[simp]
theorem sumRingEquiv_snd_apply (f : C(X ⊕ Y, R)) (y : Y) :
    (sumRingEquiv X Y R f).2 y = f (Sum.inr y) := rfl

/-- Recombination returns the first component function on the left summand.

Here `X,Y` are arbitrary topological spaces and `R` is a topological semiring, with independent
universes.

```lean
theorem sumRingEquiv_symm_inl (p : C(X, R) × C(Y, R)) (x : X) :
    (sumRingEquiv X Y R).symm p (Sum.inl x) = p.1 x
``` -/
@[simp]
theorem sumRingEquiv_symm_inl (p : C(X, R) × C(Y, R)) (x : X) :
    (sumRingEquiv X Y R).symm p (Sum.inl x) = p.1 x := rfl

/-- Recombination returns the second component function on the right summand.

Here `X,Y` are arbitrary topological spaces and `R` is a topological semiring, with independent
universes.

```lean
theorem sumRingEquiv_symm_inr (p : C(X, R) × C(Y, R)) (y : Y) :
    (sumRingEquiv X Y R).symm p (Sum.inr y) = p.2 y
``` -/
@[simp]
theorem sumRingEquiv_symm_inr (p : C(X, R) × C(Y, R)) (y : Y) :
    (sumRingEquiv X Y R).symm p (Sum.inr y) = p.2 y := rfl

end ContinuousMap
