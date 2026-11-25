/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.PartialTotalSuccessor

/-! Client tests for retained-cell coordinates and successor quotients. -/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

example (p j n : ℕ) (hn : p + j = n) :
    B.partialTotalComponent p ⟨p, Nat.lt_succ_self p⟩ j n hn ≫
        (B.partialTotalRowQuotient p).f n =
      (B.totalRowXIso p j n hn).inv :=
  B.partialTotalComponent_comp_partialTotalRowQuotient p j n hn

example (p : ℕ) (i : Fin (p + 1)) (j n : ℕ)
    (hn : i.1 + j = n) (hi : i.1 ≠ p) :
    B.partialTotalComponent p i j n hn ≫
        (B.partialTotalRowQuotient p).f n = 0 :=
  B.partialTotalComponent_comp_partialTotalRowQuotient_eq_zero
    p i j n hn hi

#print axioms HomologicalComplex₂.partialTotalComponent_comp_partialTotalRowQuotient
#print axioms HomologicalComplex₂.partialTotalComponent_comp_partialTotalRowQuotient_eq_zero

end HomologicalComplex₂
