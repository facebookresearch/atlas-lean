/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingComplex
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.NatIso

/-!
# Actual marked source restrictions into a maximal target

Every original underlying map to a maximally marked target is marked.
Consequently an isomorphism of the underlying source induces a genuine
isomorphism on each whole parameter-map set, with its original inverse
and both product coordinates. The original Yoneda restriction maps give
an isomorphism of the complete simplicial mapping complexes.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The original full marked mapping restriction into a maximal target is invertible whenever its underlying
  source map is invertible. -/
theorem mappingComplexPre_max_isIso (k : ParameterMarking) {X X' : Marked.{u}}
    (f : X' ⟶ X) [IsIso f.hom] (B : SSet.{u}) :
    IsIso (mappingComplexPre k f (max B)) := by
  let inst : ∀ n : SimplexCategoryᵒᵖ, IsIso ((mappingComplexPre k f (max B)).app n) := fun n => by
    apply (CategoryTheory.isIso_iff_bijective _).mpr
    let q : ((simplexParameter k).obj n.unop).toSSet ⊗ X'.toSSet ⟶
        ((simplexParameter k).obj n.unop).toSSet ⊗ X.toSSet :=
      𝟙 _ ⊗ₘ f.hom
    let e := ((curriedTensor SSet.{u}).obj ((simplexParameter k).obj n.unop).toSSet).mapIso (asIso f.hom)
    have he : e.hom = q := by
      change 𝟙 _ ⊗ₘ f.hom = 𝟙 _ ⊗ₘ f.hom
      rfl
    constructor
    · intro F G h
      apply Hom.ext
      apply (cancel_epi e.hom).mp
      have hh : q ≫ F.hom = q ≫ G.hom := congrArg Hom.hom h
      exact (congrArg (fun z => z ≫ F.hom) he).trans
        (hh.trans (congrArg (fun z => z ≫ G.hom) he.symm))
    · intro F
      refine ⟨toMax (e.inv ≫ F.hom), ?_⟩
      apply Hom.ext
      change q ≫ (e.inv ≫ F.hom) = F.hom
      have hq : q ≫ e.inv = 𝟙 _ :=
        (congrArg (fun z => z ≫ e.inv) he.symm).trans e.hom_inv_id
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ F.hom) hq).trans (Category.id_comp _))
  let _ := inst
  exact NatIso.isIso_of_isIso_app _

end SSet.Marked
