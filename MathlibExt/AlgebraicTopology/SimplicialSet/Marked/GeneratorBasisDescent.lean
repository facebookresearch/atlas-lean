/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.GeneratorBasisCover

/-!
# Native marked descent from the whole simplex and edge basis

The original simplex cocone maps define every component of the actual
underlying simplicial map. Their whole operator equations prove
naturality. The original marked interval object proves preservation
of every supplied marking; no presentation-density hypothesis is used.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.GeneratorBasis

/-- Every whole marked basis cocone gives its actual underlying simplicial map by original Yoneda evaluation. -/
def underlyingMap (X : Marked.{u}) (s : Cocone (diagram X)) : X.toSSet ⟶ s.pt.toSSet where
  app n := ↾fun x => SSet.yonedaEquiv (s.ι.app (simplex X n.unop x)).hom
  naturality n m f := by
    ext x
    let a : min (SSet.stdSimplex.obj n.unop) ⟶ s.pt := s.ι.app (simplex X n.unop x)
    let b : min (SSet.stdSimplex.obj m.unop) ⟶ s.pt :=
      s.ι.app (simplex X m.unop (X.toSSet.map f x))
    have h := congrArg Hom.hom (s.ι.naturality (simplexRestriction X f.unop x))
    have he : SSet.yonedaEquiv (SSet.stdSimplex.map f.unop ≫ a.hom) = SSet.yonedaEquiv b.hom :=
      congrArg SSet.yonedaEquiv (h.trans (Category.comp_id b.hom))
    exact he.symm.trans (SSet.yonedaEquiv_naturality f.unop a.hom).symm

/-- The marked interval part of the original basis proves every actual marked-edge preservation equation. -/
def descent (X : Marked.{u}) (s : Cocone (diagram X)) : X ⟶ s.pt where
  hom := underlyingMap X s
  preserve {e} he := by
    let a : min (Δ[1] : SSet.{u}) ⟶ s.pt := s.ι.app (simplex X ⦋1⦌ e)
    let b : max (Δ[1] : SSet.{u}) ⟶ s.pt := s.ι.app (markedEdge X e he)
    have h := congrArg Hom.hom (s.ι.naturality (edgeMarking X e he))
    have hb : b.hom = a.hom := (Category.id_comp b.hom).symm.trans (h.trans (Category.comp_id a.hom))
    have hm : SSet.yonedaEquiv b.hom ∈ s.pt.marking := b.preserve (Set.mem_univ _)
    exact (congrArg SSet.yonedaEquiv hb) ▸ hm

/-- The entire original simplex leg factors through the native marked descent map. -/
theorem simplex_descent (X : Marked.{u}) (s : Cocone (diagram X))
    (n : SimplexCategory) (x : X.toSSet.obj (op n)) :
    (simplex X n x).hom ≫ descent X s = s.ι.app (simplex X n x) := by
  apply Hom.ext
  apply SSet.yonedaEquiv.injective
  change SSet.yonedaEquiv (SSet.yonedaEquiv.symm x ≫ underlyingMap X s) =
    SSet.yonedaEquiv (s.ι.app (simplex X n x)).hom
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  rfl

end SSet.Marked.GeneratorBasis
