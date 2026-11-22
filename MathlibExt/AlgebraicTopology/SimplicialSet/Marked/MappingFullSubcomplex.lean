/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingUnderlying
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ParameterSections
import MathlibExt.AlgebraicTopology.SimplicialSet.FullSubcomplex

/-!
# The exact full vertex subcomplex of minimally parameter-marked maps

A map from the minimally marked parameter product preserves markings
exactly when every original parameter-vertex restriction is a marked map.
Thus the actual mapping complex is the full vertex subcomplex of the
original unmarked prism complex on those vertices. Both directions of the
isomorphism retain each entire prism.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The original zero-prisms whose unit restriction preserves the supplied source marking. -/
def markedMappingVertices (X Y : Marked.{u}) :
    Set ((parameterMapping X.toSSet Y.toSSet) _⦋0⦌) :=
  {f | ∀ (e : X.toSSet _⦋1⦌), e ∈ X.marking →
    ((zeroParameterUnitIso .minimal X).inv.hom ≫ f).app (op ⦋1⦌) e ∈ Y.marking}

/-- Whole minimal-parameter prisms preserve marks exactly when all original vertex maps do. -/
theorem preserves_minParameter_iff_vertices (X Y : Marked.{u}) (n : ℕ)
    (f : (Δ[n] : SSet.{u}) ⊗ X.toSSet ⟶ Y.toSSet) :
    (∀ (e : (prod (min (Δ[n] : SSet.{u})) X).toSSet _⦋1⦌),
      e ∈ (prod (min (Δ[n] : SSet.{u})) X).marking →
        f.app (op ⦋1⦌) e ∈ Y.marking) ↔
    f ∈ (Subcomplex.full (markedMappingVertices X Y)).obj (op ⦋n⦌) := by
  constructor
  · intro hf a
    let fm : prod (min (Δ[n] : SSet.{u})) X ⟶ Y := ⟨f, fun h => hf _ h⟩
    let g : X ⟶ Y := (zeroParameterUnitIso .minimal X).inv ≫
      prodMap (minimal.map (SSet.stdSimplex.map a)) (𝟙 X) ≫ fm
    intro e he
    let s : X.toSSet ⟶ (Δ[0] : SSet.{u}) ⊗ X.toSSet :=
      (zeroParameterUnitIso .minimal X).inv.hom
    change (s ≫ ((SSet.stdSimplex.map a ▷ X.toSSet) ≫ f)).app (op ⦋1⦌) e ∈ Y.marking
    have hg : g.hom = (s ≫ (SSet.stdSimplex.map a ▷ X.toSSet)) ≫ f := rfl
    rw [← Category.assoc, ← hg]
    exact g.preserve he
  · intro hf e he
    obtain ⟨v, hv⟩ := he.1
    let a : ⦋0⦌ ⟶ ⦋n⦌ := SSet.stdSimplex.objEquiv v
    have ha : SSet.stdSimplex.map a = SSet.yonedaEquiv.symm v := by
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_map, Equiv.apply_symm_apply]
      exact Equiv.symm_apply_apply _ v
    have hvertex := hf a e.2 he.2
    let s : X.toSSet ⟶ (Δ[0] : SSet.{u}) ⊗ X.toSSet :=
      (zeroParameterUnitIso .minimal X).inv.hom
    change (s ≫
      (SSet.stdSimplex.map a ▷ X.toSSet) ≫ f).app (op ⦋1⦌) e.2 ∈ Y.marking at hvertex
    have hsection : s ≫
        (SSet.stdSimplex.map a ▷ X.toSSet) = (parameterSection X v).hom := by
      rw [ha]
      exact congrArg Hom.hom (zeroParameterSection_comp_map X v)
    rw [← Category.assoc, hsection] at hvertex
    change f.app (op ⦋1⦌) ((parameterSection X v).hom.app (op ⦋1⦌) e.2) ∈ Y.marking at hvertex
    rw [parameterSection_app_one, hv] at hvertex
    change f.app (op ⦋1⦌) (e.1, e.2) ∈ Y.marking
    exact hvertex

/-- The actual minimal marked mapping complex is exactly the full subcomplex on marked-map vertices. -/
def mappingComplexMinFullIso (X Y : Marked.{u}) :
    mappingComplex .minimal X Y ≅
      (Subcomplex.full (markedMappingVertices X Y) : SSet.{u}) :=
  NatIso.ofComponents (fun n =>
    (show (mappingComplex .minimal X Y).obj n ≃
      (Subcomplex.full (markedMappingVertices X Y) : SSet.{u}).obj n from
      { toFun := fun f => ⟨f.hom, (preserves_minParameter_iff_vertices X Y n.unop.len f.hom).mp
          (fun _ h => f.preserve h)⟩
        invFun := fun f => ⟨f.val, fun h =>
          (preserves_minParameter_iff_vertices X Y n.unop.len f.val).mpr f.property _ h⟩
        left_inv := fun f => Hom.ext rfl
        right_inv := fun f => Subtype.ext rfl }).toIso) (by
      intro n m a
      apply ConcreteCategory.hom_ext
      intro f
      apply Subtype.ext
      rfl)

/-- The whole original prism is retained by the full-subcomplex identification. -/
theorem mappingComplexMinFullIso_hom_ι (X Y : Marked.{u}) :
    (mappingComplexMinFullIso X Y).hom ≫ (Subcomplex.full (markedMappingVertices X Y)).ι =
      mappingComplexUnderlying .minimal X Y := by
  ext n f
  rfl

end SSet.Marked
