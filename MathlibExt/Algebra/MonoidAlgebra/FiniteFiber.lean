/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Logic.Equiv.Sum

/-!
# Finite sums grouped by their output fibers

For finite types `I,G`, a semiring `R`, a function `f : I → G`, and coefficients `c : G → R`,
the sum of single-coordinate functions at `f(i)` can be grouped by the fibers of `f`.

The resulting term at `g` is the fiber cardinality times `single g (c g)`, where this
multiplication is repeated addition. The identity uses the finitely supported additive carrier
of `MonoidAlgebra R G`.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MonoidAlgebra

variable {I G R : Type*} [Fintype I] [Fintype G] [Semiring R]

/-- Let `I,G` be finite types, `R` a semiring, `f : I → G`, and `c : G → R`. Then `∑ i : I, single
(f i) (c(f i)) = ∑ g : G, |{i : I | f i=g}| • single g (c g)`. The natural-number scalar is
repeated addition in the finitely supported `R`-valued functions on `G`. -/
theorem sum_single_eq_sum_fiber (f : I → G) (c : G → R) :
    (∑ i : I, single (f i) (c (f i))) =
      ∑ g : G, (Fintype.card {i : I // f i = g}) • single g (c g) := by
  classical
  rw [← Fintype.sum_fiberwise' f (fun g => single g (c g))]
  simp only [Finset.sum_const, Finset.card_univ]

end MonoidAlgebra
