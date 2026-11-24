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
# Actual finite-fiber sums in native monoid algebras

The native fiber equivalence reindexes an original finite sum into
its original output fibers. A coefficient depending only on that original
output therefore receives the actual fiber cardinality. No multiplicative
or counting certificate is supplied.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MonoidAlgebra

variable {I G R : Type*} [Fintype I] [Fintype G] [Semiring R]

/-- The original finite generator sum is the actual output-fiber cardinality sum. -/
theorem sum_single_eq_sum_fiber (f : I → G) (c : G → R) :
    (∑ i : I, single (f i) (c (f i))) =
      ∑ g : G, (Fintype.card {i : I // f i = g}) • single g (c g) := by
  classical
  let e := Equiv.sigmaFiberEquiv f
  rw [← e.sum_comp (fun i => single (f i) (c (f i))), Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro g _
  have hconst (i : {i : I // f i = g}) :
      single (f (e ⟨g, i⟩)) (c (f (e ⟨g, i⟩))) = single g (c g) := by
    change single (f i.val) (c (f i.val)) = _
    rw [i.property]
  simp_rw [hconst]
  rw [Finset.sum_const, Finset.card_univ]

end MonoidAlgebra
