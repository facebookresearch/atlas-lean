/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverMappingFunctor

/-!
# Whole fixed-base marked target maps

Every original marked map over the supplied base postcomposes the same
whole relative prism. The original base-point coordinate is unchanged.
Identities, composition and source restriction retain these literal maps,
without an intrinsic-fibration or marked-model hypothesis.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- An original marked target map over the same base acts on every full relative prism. -/
def relativeMappingPost (k : ParameterMarking) {X Y Y' Z : Marked.{u}}
    (r : X ⟶ Z) (f : Y ⟶ Y') (p : Y ⟶ Z) (p' : Y' ⟶ Z) (hf : f ≫ p' = p) :
    relativeMappingComplex k r p ⟶ relativeMappingComplex k r p' := by
  let a : relativeMappingComplex k r p ⟶ mappingComplex k X Y :=
    pullback.fst (mappingComplexPost k X p) (mappingBasePoint k r)
  let b : relativeMappingComplex k r p ⟶ (Δ[0] : SSet.{u}) :=
    pullback.snd (mappingComplexPost k X p) (mappingBasePoint k r)
  have hw : a ≫ mappingComplexPost k X p = b ≫ mappingBasePoint k r := pullback.condition
  exact pullback.lift (a ≫ mappingComplexPost k X f) b (by
    rw [Category.assoc, ← mappingComplexPost_comp, hf, hw])

/-- Relative postcomposition retains the original full prism as its first coordinate. -/
@[reassoc]
theorem relativeMappingPost_fst (k : ParameterMarking) {X Y Y' Z : Marked.{u}}
    (r : X ⟶ Z) (f : Y ⟶ Y') (p : Y ⟶ Z) (p' : Y' ⟶ Z) (hf : f ≫ p' = p) :
    relativeMappingPost k r f p p' hf ≫
        pullback.fst (mappingComplexPost k X p') (mappingBasePoint k r) =
      pullback.fst (mappingComplexPost k X p) (mappingBasePoint k r) ≫ mappingComplexPost k X f :=
  pullback.lift_fst _ _ _

/-- The actual fixed-base point is unchanged by relative target postcomposition. -/
@[reassoc]
theorem relativeMappingPost_snd (k : ParameterMarking) {X Y Y' Z : Marked.{u}}
    (r : X ⟶ Z) (f : Y ⟶ Y') (p : Y ⟶ Z) (p' : Y' ⟶ Z) (hf : f ≫ p' = p) :
    relativeMappingPost k r f p p' hf ≫
        pullback.snd (mappingComplexPost k X p') (mappingBasePoint k r) =
      pullback.snd (mappingComplexPost k X p) (mappingBasePoint k r) :=
  pullback.lift_snd _ _ _

/-- Identity target maps retain every original marked relative simplex. -/
theorem relativeMappingPost_id (k : ParameterMarking) {X Y Z : Marked.{u}}
    (r : X ⟶ Z) (p : Y ⟶ Z) :
    relativeMappingPost k r (𝟙 Y) p p (Category.id_comp p) = 𝟙 (relativeMappingComplex k r p) := by
  let a : relativeMappingComplex k r p ⟶ mappingComplex k X Y :=
    pullback.fst (mappingComplexPost k X p) (mappingBasePoint k r)
  let b : relativeMappingComplex k r p ⟶ (Δ[0] : SSet.{u}) :=
    pullback.snd (mappingComplexPost k X p) (mappingBasePoint k r)
  apply (IsPullback.of_hasPullback (mappingComplexPost k X p) (mappingBasePoint k r)).hom_ext
  · change relativeMappingPost k r (𝟙 Y) p p (Category.id_comp p) ≫ a = 𝟙 _ ≫ a
    exact (relativeMappingPost_fst k r (𝟙 Y) p p (Category.id_comp p)).trans
      ((congrArg (fun t => a ≫ t) (mappingComplexPost_id k X Y)).trans
        ((Category.comp_id a).trans (Category.id_comp a).symm))
  · change relativeMappingPost k r (𝟙 Y) p p (Category.id_comp p) ≫ b = 𝟙 _ ≫ b
    exact (relativeMappingPost_snd k r (𝟙 Y) p p (Category.id_comp p)).trans (Category.id_comp b).symm

/-- Two original target maps act by their same whole composite on relative marked prisms. -/
theorem relativeMappingPost_comp (k : ParameterMarking) {X Y Y' Y'' Z : Marked.{u}}
    (r : X ⟶ Z) (f : Y ⟶ Y') (g : Y' ⟶ Y'')
    (p : Y ⟶ Z) (p' : Y' ⟶ Z) (p'' : Y'' ⟶ Z) (hf : f ≫ p' = p) (hg : g ≫ p'' = p') :
    relativeMappingPost k r (f ≫ g) p p''
      ((Category.assoc _ _ _).trans ((congrArg (fun t => f ≫ t) hg).trans hf)) =
      relativeMappingPost k r f p p' hf ≫ relativeMappingPost k r g p' p'' hg := by
  let P := relativeMappingPost k r f p p' hf
  let Q := relativeMappingPost k r g p' p'' hg
  let T := relativeMappingPost k r (f ≫ g) p p''
    ((Category.assoc _ _ _).trans ((congrArg (fun t => f ≫ t) hg).trans hf))
  let a : relativeMappingComplex k r p ⟶ mappingComplex k X Y :=
    pullback.fst (mappingComplexPost k X p) (mappingBasePoint k r)
  let a' : relativeMappingComplex k r p' ⟶ mappingComplex k X Y' :=
    pullback.fst (mappingComplexPost k X p') (mappingBasePoint k r)
  let a'' : relativeMappingComplex k r p'' ⟶ mappingComplex k X Y'' :=
    pullback.fst (mappingComplexPost k X p'') (mappingBasePoint k r)
  let b : relativeMappingComplex k r p ⟶ (Δ[0] : SSet.{u}) :=
    pullback.snd (mappingComplexPost k X p) (mappingBasePoint k r)
  let b' : relativeMappingComplex k r p' ⟶ (Δ[0] : SSet.{u}) :=
    pullback.snd (mappingComplexPost k X p') (mappingBasePoint k r)
  let b'' : relativeMappingComplex k r p'' ⟶ (Δ[0] : SSet.{u}) :=
    pullback.snd (mappingComplexPost k X p'') (mappingBasePoint k r)
  have ha : P ≫ a' = a ≫ mappingComplexPost k X f := relativeMappingPost_fst _ _ _ _ _ _
  have ha' : Q ≫ a'' = a' ≫ mappingComplexPost k X g := relativeMappingPost_fst _ _ _ _ _ _
  have ha'' : T ≫ a'' = a ≫ mappingComplexPost k X (f ≫ g) := relativeMappingPost_fst _ _ _ _ _ _
  have hb : P ≫ b' = b := relativeMappingPost_snd _ _ _ _ _ _
  have hb' : Q ≫ b'' = b' := relativeMappingPost_snd _ _ _ _ _ _
  have hb'' : T ≫ b'' = b := relativeMappingPost_snd _ _ _ _ _ _
  apply (IsPullback.of_hasPullback (mappingComplexPost k X p'') (mappingBasePoint k r)).hom_ext
  · change T ≫ a'' = (P ≫ Q) ≫ a''
    calc
      _ = a ≫ mappingComplexPost k X (f ≫ g) := ha''
      _ = a ≫ (mappingComplexPost k X f ≫ mappingComplexPost k X g) :=
        congrArg (fun t => a ≫ t) (mappingComplexPost_comp k X f g)
      _ = (a ≫ mappingComplexPost k X f) ≫ mappingComplexPost k X g := (Category.assoc _ _ _).symm
      _ = (P ≫ a') ≫ mappingComplexPost k X g := congrArg (fun t => t ≫ mappingComplexPost k X g) ha.symm
      _ = P ≫ (a' ≫ mappingComplexPost k X g) := Category.assoc _ _ _
      _ = P ≫ (Q ≫ a'') := congrArg (fun t => P ≫ t) ha'.symm
      _ = _ := (Category.assoc _ _ _).symm
  · change T ≫ b'' = (P ≫ Q) ≫ b''
    exact hb''.trans ((Category.assoc _ _ _).trans ((congrArg (fun t => P ≫ t) hb').trans hb)).symm

/-- The actual relative marked mapping complex is covariant on every original target over the base. -/
def overTargetMappingFunctor (k : ParameterMarking) (Z : Marked.{u}) (X : Over Z) :
    Over Z ⥤ SSet.{u} where
  obj Y := relativeMappingComplex k X.hom Y.hom
  map {Y Y'} f := relativeMappingPost k X.hom f.left Y.hom Y'.hom (Over.w f)
  map_id Y := relativeMappingPost_id k X.hom Y.hom
  map_comp f g := relativeMappingPost_comp k X.hom f.left g.left _ _ _ (Over.w f) (Over.w g)

end SSet.Marked
