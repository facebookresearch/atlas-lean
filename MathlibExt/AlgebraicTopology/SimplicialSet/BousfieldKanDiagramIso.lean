/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanHocolim

/-!
# The SAME Bousfield--Kan maps preserve diagram isomorphisms

Both maps of an actual diagram isomorphism induce inverse maps of the
original terminal-weight Bousfield--Kan carriers. Their exact formulas
are the existing original diagram maps, with independent indexing
object and Hom universes.
-/

noncomputable section

universe uJ vJ

open CategoryTheory

namespace SSet

variable {J : Type uJ} [Category.{vJ} J]

/-- Both SAME original diagram maps give the full original Bousfield--Kan carrier isomorphism. -/
def bkHocolimDiagramIso {D E : J ⥤ SSet.{max uJ vJ}} (e : D ≅ E) : bkHocolim D ≅ bkHocolim E where
  hom := bkHocolimMap e.hom
  inv := bkHocolimMap e.inv
  hom_inv_id := by rw [← bkHocolimMap_comp, e.hom_inv_id, bkHocolimMap_id]
  inv_hom_id := by rw [← bkHocolimMap_comp, e.inv_hom_id, bkHocolimMap_id]

/-- The original forward diagram isomorphism induces its SAME literal Bousfield--Kan map. -/
theorem bkHocolimDiagramIso_hom {D E : J ⥤ SSet.{max uJ vJ}} (e : D ≅ E) :
    (bkHocolimDiagramIso e).hom = bkHocolimMap e.hom := rfl

/-- The original inverse diagram isomorphism induces its SAME literal Bousfield--Kan map. -/
theorem bkHocolimDiagramIso_inv {D E : J ⥤ SSet.{max uJ vJ}} (e : D ≅ E) :
    (bkHocolimDiagramIso e).inv = bkHocolimMap e.inv := rfl

end SSet
