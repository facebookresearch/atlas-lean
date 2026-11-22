/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectNativeSectionReadback

/-!
# The original fixed-object section under the actual extra degeneracy

The canonical original first degeneracy preserves the same entire identity
section. Both the original shifted-simplex map and original fixed-object
coefficient are checked through the actual row pullback.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

set_option backward.isDefEq.respectTransparency false in
/-- The same original section is preserved by the canonical original extra-degeneracy map. -/
theorem nativeSection_extra (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) :
    (nativeSection W x).app (op (SimplexCategory.mk n)) ≫ (extraDegeneracy W x).s n =
      (nativeSection W x).app (op (SimplexCategory.mk (n + 1))) := by
  apply (cancel_mono (rowIso W x (n + 1)).hom).mp
  apply pullback.hom_ext
  · simp only [Category.assoc, rowIso_fst]
    have he := SimplicialObject.Augmented.ExtraDegeneracy.baseChangeExtraMap_fst
      (ed := SimplicialObject.LeftDecalage.extraDegeneracy W.diagram)
      (p := SSet.yonedaEquiv.symm x) n
    change (extraDegeneracy W x).s n ≫ (toDecalage W x).app (op (SimplexCategory.mk (n + 1))) =
      (toDecalage W x).app (op (SimplexCategory.mk n)) ≫
        W.diagram.map (SimplexCategory.σ (0 : Fin (n + 2))).op at he
    rw [he, ← Category.assoc, nativeSection_fst,
      Category.assoc, ← W.diagram.map_comp, ← op_comp]
    rw [nativeSection_fst]
    apply congrArg (fun q : SimplexCategory.mk (n + 2) ⟶ SimplexCategory.mk 0 =>
      SSet.yonedaEquiv.symm x ≫ W.diagram.map q.op)
    exact SimplexCategory.isTerminalZero.hom_ext _ _
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

end SimplicialSpace.LeftDecalageObject
