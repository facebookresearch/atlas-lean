/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Continuous functions on a disjoint indexed sum

For an arbitrary index type `ι`, topological spaces `X(i)` and a
topological semiring `R`, restriction to each summand identifies continuous
functions `C(Σi X(i),R)` with the dependent product `Πi C(X(i),R)` as
semirings. The inverse joins the component functions by the sigma eliminator.
The coordinate formulas give the original values in both directions.

The index, fiber and coefficient universes are independent. Empty index
and summand types are allowed. Neither additive inverses, commutative
multiplication, compactness nor a norm is a hypothesis.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace ContinuousMap

variable {ι : Type w} (X : ι → Type u) (R : Type v)
variable [∀ i, TopologicalSpace (X i)] [TopologicalSpace R]
variable [Semiring R] [IsTopologicalSemiring R]

/-- The semiring equivalence restricting a continuous function on a disjoint indexed sum to its
summands, with recombination as inverse.

The fibers are arbitrary topological spaces and `R` is a topological semiring; index, fiber and
coefficient universes are independent. -/
def sigmaRingEquiv : C((Σ i, X i), R) ≃+* ∀ i, C(X i, R) where
  toEquiv := (sigmaEquiv R X).symm
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The component at index `i` has value `f(i,x)` at `x ∈ X(i)`.

The fibers are arbitrary topological spaces and `R` is a topological semiring; index, fiber and
coefficient universes are independent.

```lean
theorem sigmaRingEquiv_apply (f : C((Σ i, X i), R)) (i : ι) (x : X i) :
    sigmaRingEquiv X R f i x = f ⟨i, x⟩
``` -/
@[simp]
theorem sigmaRingEquiv_apply (f : C((Σ i, X i), R)) (i : ι) (x : X i) :
    sigmaRingEquiv X R f i x = f ⟨i, x⟩ := rfl

/-- Recombining the family has value `f(i)(x)` at the sigma point `(i,x)`.

The fibers are arbitrary topological spaces and `R` is a topological semiring; index, fiber and
coefficient universes are independent.

```lean
theorem sigmaRingEquiv_symm_apply (f : ∀ i, C(X i, R)) (i : ι) (x : X i) :
    (sigmaRingEquiv X R).symm f ⟨i, x⟩ = f i x
``` -/
@[simp]
theorem sigmaRingEquiv_symm_apply (f : ∀ i, C(X i, R)) (i : ι) (x : X i) :
    (sigmaRingEquiv X R).symm f ⟨i, x⟩ = f i x := rfl

end ContinuousMap
