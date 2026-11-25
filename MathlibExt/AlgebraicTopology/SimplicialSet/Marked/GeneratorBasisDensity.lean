/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.GeneratorBasisDescent

/-!
# The actual marked simplex and edge basis is dense

Every original basis map has its proved minimally marked simplex
cover. The whole cover and simplex equations show that native descent
factors every original marked cocone leg. Original simplex evaluation
also proves uniqueness, giving the actual colimit presentation of
every supplied marked total space without a density outcome input.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.GeneratorBasis

/-- The original full marked basis leg factors through the native marked descent. -/
theorem basis_descent (X : Marked.{u}) (s : Cocone (diagram X)) (i : Index X) :
    i.hom ≫ descent X s = s.ι.app i := by
  let e := underlyingIso i.left
  let t := sourceSimplex X i
  let l : min (Δ[dimension i.left] : SSet.{u}) ⟶ s.pt := s.ι.app t
  let g : generatorFunctor.obj i.left ⟶ s.pt := s.ι.app i
  have hs : t.hom.hom = e.inv ≫ i.hom.hom := SSet.yonedaEquiv.symm_apply_apply _
  have hc := congrArg Hom.hom (s.ι.naturality (cover X i))
  have hw : e.inv ≫ g.hom = l.hom :=
    (congrArg (fun f => f ≫ g.hom) (cover_hom X i)).symm.trans (hc.trans (Category.comp_id l.hom))
  have hf : t.hom.hom ≫ (descent X s).hom = l.hom := congrArg Hom.hom
    (simplex_descent X s ⦋dimension i.left⦌ (SSet.yonedaEquiv (e.inv ≫ i.hom.hom)))
  apply Hom.ext
  apply (cancel_epi e.inv).mp
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (descent X s).hom) hs.symm).trans (hf.trans hw.symm))

/-- The original marked simplex and interval cocone is a genuine colimit of the entire original total space. -/
def isColimit (X : Marked.{u}) : IsColimit (cocone X) where
  desc := descent X
  fac s i := basis_descent X s i
  uniq s m hm := by
    apply Hom.ext
    ext n x
    have h := congrArg Hom.hom (hm (simplex X n.unop x))
    have hy := congrArg SSet.yonedaEquiv h
    change SSet.yonedaEquiv (SSet.yonedaEquiv.symm x ≫ m.hom) =
      SSet.yonedaEquiv (s.ι.app (simplex X n.unop x)).hom at hy
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at hy
    exact hy

end SSet.Marked.GeneratorBasis
