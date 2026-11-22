/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeFiltrationOrder
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.TopMarkedCylinder

/-!
# The original whole cone-stage prism

The actual maximum-filtration order isomorphism gives the full original
simplicial cylinder coordinates. Its maps commute with every original
simplex operator, including degeneracies. The coefficient is the entire
preceding subset and the interval records whether the new maximum was
present. This file identifies the whole carrier; the exact marking is
treated separately.
-/

noncomputable section
universe u
open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The actual preceding-subset reader is the native functor on all original inclusions. -/
def coneEraseTopFunctor {n : ℕ} {i k : Vertex.{u} n} (hi : i < k) :
    ConeAtMost i k ⥤ ConeBefore i k := (coneEraseTop_mono hi).functor

/-- The original top-coordinate reader is the native monotone two-vertex functor. -/
def coneFiltrationLevelFunctor {n : ℕ} (i k : Vertex.{u} n) :
    ConeAtMost i k ⥤ Vertex.{u} 1 := coneFiltrationLevel_mono.functor

/-- The original subset reconstruction is a genuine functor on the complete preceding-stage prism. -/
def coneFromFiltrationFunctor {n : ℕ} {i k : Vertex.{u} n} (hi : i < k) :
    ConeBefore i k × Vertex.{u} 1 ⥤ ConeAtMost i k where
  obj := coneFromFiltration hi
  map f := homOfLE (coneFromFiltration_mono hi ⟨leOfHom f.1, leOfHom f.2⟩)

/-- The full original stage simplex reads as its whole preceding simplex and exact minimal-interval simplex. -/
def coneFiltrationPrism {n : ℕ} {i k : Vertex.{u} n} (hi : i < k) :
    (coneAtMostWeight i k).toSSet ⟶ (topMarkedCylinder (coneBeforeWeight i k)).toSSet where
  app q := ↾fun a => (a ⋙ coneEraseTopFunctor hi,
    (SSet.stdSimplex.isoNerve 1).inv.app q (a ⋙ coneFiltrationLevelFunctor i k))
  naturality q r f := by
    ext a
    apply Prod.ext
    · rfl
    · exact congr($((SSet.stdSimplex.isoNerve 1).inv.naturality f)
        (a ⋙ coneFiltrationLevelFunctor i k)).symm

/-- The inverse whole prism map inserts exactly the original top vertex at every original scalar position. -/
def coneFiltrationFromPrism {n : ℕ} {i k : Vertex.{u} n} (hi : i < k) :
    (topMarkedCylinder (coneBeforeWeight i k)).toSSet ⟶ (coneAtMostWeight i k).toSSet where
  app q := ↾fun a => a.1.prod' ((SSet.stdSimplex.isoNerve 1).hom.app q a.2) ⋙
    coneFromFiltrationFunctor hi
  naturality q r f := by
    ext a
    refine CategoryTheory.Functor.ext (fun t => rfl) (fun _ _ _ => Subsingleton.elim _ _)

/-- The original maximum-stage carrier is the entire original preceding-stage cylinder, with both whole
  simplicial inverses proved. -/
def coneFiltrationPrismIso {n : ℕ} {i k : Vertex.{u} n} (hi : i < k) :
    (coneAtMostWeight i k).toSSet ≅ (topMarkedCylinder (coneBeforeWeight i k)).toSSet where
  hom := coneFiltrationPrism hi
  inv := coneFiltrationFromPrism hi
  hom_inv_id := by
    ext q a
    refine CategoryTheory.Functor.ext (fun t => ?_) (fun _ _ _ => Subsingleton.elim _ _)
    exact coneFromFiltration_erase hi (a.obj t)
  inv_hom_id := by
    ext q a
    apply Prod.ext
    · refine CategoryTheory.Functor.ext (fun t => ?_) (fun _ _ _ => Subsingleton.elim _ _)
      exact congrArg Prod.fst (coneErase_fromFiltration hi
        (a.1.obj t, ((SSet.stdSimplex.isoNerve 1).hom.app q a.2).obj t))
    · apply SSet.stdSimplex.ext
      intro t
      exact congrArg (fun z : ConeBefore i k × Vertex.{u} 1 => z.2.down)
        (coneErase_fromFiltration hi
          (a.1.obj t, ((SSet.stdSimplex.isoNerve 1).hom.app q a.2).obj t))

/-- Every original scalar vertex reads the same preceding subset and the exact original maximum-presence coordinate. -/
theorem coneFiltrationPrism_vertex {n : ℕ} {i k : Vertex.{u} n} (hi : i < k)
    (d : ℕ) (a : (coneAtMostWeight i k).toSSet _⦋d⦌) (t : Fin (d + 1)) :
    (((coneFiltrationPrism hi).app (op ⦋d⦌) a).1.obj t,
      (SSet.stdSimplex.objEquiv ((coneFiltrationPrism hi).app (op ⦋d⦌) a).2).toOrderHom t) =
      (coneEraseTop hi (a.obj t), (coneFiltrationLevel (a.obj t)).down) := rfl

end SSet.Marked.CoherentWeight
