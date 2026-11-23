/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.AlgebraicTopology.SingularHomology.IntegerData
public import MathlibExt.AlgebraicTopology.SingularHomology.IntegerDimension

/-!
# The dimension axiom for integer-graded singular homology
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicTopology

universe w v u

variable (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

noncomputable instance singularHomologyIntData_satisfiesDimensionAxiom
    (R : C) :
    (singularHomologyIntData C R).SatisfiesDimensionAxiom where
  isZero_point := isZero_singularHomologyInt_punit C R

end AlgebraicTopology
