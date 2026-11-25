/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Monoidal.Sequence.Index

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.SequenceIndexTests

#check Sequence.Index
#check Sequence.index
#check Sequence.degree
#check Sequence.degree_index
#check Sequence.index_degree
#check Sequence.tensorUnit_eq_index_zero
#check Sequence.tensorObj_index

example : Sequence.degree (Sequence.index 0) = 0 := by simp
example : Sequence.degree (Sequence.index 1) = 1 := by simp
example : Sequence.degree (Sequence.index 2) = 2 := by simp
example : Sequence.index 2 ⊗ Sequence.index 3 = Sequence.index 5 := by simp

example : (𝟙_ Sequence.Index) = Sequence.index 0 := by simp

-- The symmetric structure is deliberately not active on import alone.
example : True := by
  fail_if_success let _ : SymmetricCategory Sequence.Index := inferInstance
  trivial

section Scoped

open scoped CategoryTheory.Sequence

example : SymmetricCategory Sequence.Index := inferInstance

example (X Y : Sequence.Index) :
    (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y) := by simp

end Scoped

-- Closing the scope restores the original instance environment.
example : True := by
  fail_if_success let _ : SymmetricCategory Sequence.Index := inferInstance
  trivial

#print axioms Sequence.degree_index
#print axioms Sequence.index_degree
#print axioms Sequence.tensorUnit_eq_index_zero
#print axioms Sequence.tensorObj_index

end CategoryTheory.SequenceIndexTests
