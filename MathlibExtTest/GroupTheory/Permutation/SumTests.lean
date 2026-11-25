/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.GroupTheory.Permutation.Sum

set_option autoImplicit false

universe u v

open Equiv

section IndependentSummands
variable (A : Type u) (B : Type v)

example (p q : Perm A) :
    Perm.sumInlHom A B (p * q) = Perm.sumInlHom A B p * Perm.sumInlHom A B q :=
  (Perm.sumInlHom A B).map_mul p q

example (s : Perm (A ⊕ B)) (h : ∀ b : B, s (Sum.inr b) = Sum.inr b) :
    ∃ p : Perm A, Perm.sumInlHom A B p = s :=
  (Perm.mem_sumInlHom_range_iff A B s).mpr h

end IndependentSummands

-- Infinite summands require no finite-cardinality witness.
example (s : Perm (ℕ ⊕ ℕ)) :
    s ∈ (Perm.sumInlHom ℕ ℕ).range ↔ ∀ n : ℕ, s (Sum.inr n) = Sum.inr n :=
  Perm.mem_sumInlHom_range_iff ℕ ℕ s

#print axioms Equiv.Perm.sumInlHom
#print axioms Equiv.Perm.mem_sumInlHom_range_iff
