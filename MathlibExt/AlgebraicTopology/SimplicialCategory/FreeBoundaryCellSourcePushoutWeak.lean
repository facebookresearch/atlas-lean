/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeIndexedMonoSourcePushoutWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeBoundaryCellScalarPresentation

/-!
# Genuine weak source gluing for the SAME full original free boundary cells

The complete actual boundary-cell attachment retains its original cell
occurrences, complete coproducts and actual pushout maps. The canonical
free-quiver presentations identify those SAME maps with an indexed mono
attachment. Its full original Hom map is monic, and genuine Homwise weak
source maps survive actual cobase change along this full original step.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FreeBoundaryCells
variable {O : Type u} {C P D E : FixedObjects O} {f : C ⟶ P}
  (a : AttachCells.{u} (boundaryFamily O).homFamily f)

include a in
/-- The SAME complete original boundary-cell step is monic on every full original Hom object. -/
theorem leftHom_mono (x y : O) : Mono (homMap f x y) :=
  FreeIndexedMonoPushout.leftHom_mono (fun i => quiverMap (index (a.π i)))
    (fun i => quiverMap_mono (index (a.π i)))
    (domainCofan a) (targetCofan a) (domainIsColimit a) (targetIsColimit a)
    a.m (coproductMap a) a.g₁ f a.g₂ a.isPushout x y

include a in
/-- Actual cobase change along the full original boundary-cell step preserves the SAME genuine weak source map. -/
theorem sourcePushout_weak (F : C ⟶ D) (hF : FixedObjectModel.weakEquivalences O F)
    (d : P ⟶ E) (c : D ⟶ E) (sq : IsPushout f F d c) :
    FixedObjectModel.weakEquivalences O d :=
  FreeIndexedMonoPushout.sourcePushout_weak (fun i => quiverMap (index (a.π i)))
    (fun i => quiverMap_mono (index (a.π i)))
    (domainCofan a) (targetCofan a) (domainIsColimit a) (targetIsColimit a)
    a.m (coproductMap a) a.g₁ f a.g₂ a.isPushout F hF d c sq

end CategoryTheory.SimplicialEnrichment.FixedObjects.FreeBoundaryCells
