/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.JoyalTierneyAdjunction
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyRowConstancy
import MathlibExt.AlgebraicTopology.SimplicialSpace.RowWeakContainment
import MathlibExt.AlgebraicTopology.SimplicialSpace.JoyalTierneyQuillen

/-!
# The original and derived comparison counit

Every original row of the comparison counit is the canonical zero-to-n row
map. Categorical constancy and genuine all-arrow weak containment make this
counit Rezk weak at a complete Segal space. For every supplied original
source-model weak map q into the actual right image, the actual left weak
preservation theorem and composition give weakness of L.map q followed by
the original counit. In particular this retains every actual cofibrant
replacement q, without selecting or replacing it.

Joyal–Tierney Theorem 4.5 and Proposition 4.7 give the ordinary counit route.
The supplied-replacement clause is the native Brown consequence for the
same actual comparison pair and models.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace SimplicialSpace

/-- Every original counit row is the actual canonical zero-to-n row map. -/
lemma comparisonAdjunction_counit_row_eq_rowZeroTo (X : SimplicialSpace.{u}) (n : ℕ) :
    (rowFunctor n).map (comparisonAdjunction.counit.app X) = (rowZeroTo n).app X := by
  ext m x
  exact congr($(comparisonAdjunction_counit_app X m (op ⦋n⦌)) x)

private lemma comparisonAdjunction_counit_rowwise (X : SimplicialSpace.{u})
    (hX : completeSegalSpaces X) :
    rowwiseCategoricalEquivalences (comparisonAdjunction.counit.app X) := by
  intro n
  rw [comparisonAdjunction_counit_row_eq_rowZeroTo]
  exact categoricallyConstant_of_completeSegalSpaces X hX n

/-- The literal original counit at every complete Segal space is Rezk weak. -/
theorem comparisonAdjunction_counit_rezkWeak (X : SimplicialSpace.{u})
    (hX : completeSegalSpaces X) :
    rezkWeakEquivalences (comparisonAdjunction.counit.app X) :=
  rowwiseCategoricalEquivalences_le_rezkWeakEquivalences _
    (comparisonAdjunction_counit_rowwise X hX)

/-- The original derived counit retains every supplied actual source-model
weak map q. Every genuine cofibrant replacement is included. -/
theorem comparisonAdjunction_derivedCounit_rezkWeak (X : SimplicialSpace.{u})
    (hX : completeSegalSpaces X) {Q : JoyalSSet.{u}}
    (q : Q ⟶ comparisonRight.obj X)
    (hq : JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences q) :
    rezkWeakEquivalences (comparisonLeft.map q ≫ comparisonAdjunction.counit.app X) := by
  have hq' : SSet.categoricalEquivalences (JoyalSSet.forget.map q) := by
    change (SSet.categoricalEquivalences.inverseImage JoyalSSet.forget) q
    rw [← JoyalSSet.modelCategory_weakEquivalences]
    exact hq
  exact rezkWeakEquivalences.comp_mem _ _
    (comparisonLeft_rezkWeak_of_categoricalEquivalence q hq')
    (comparisonAdjunction_counit_rezkWeak X hX)

end SimplicialSpace
