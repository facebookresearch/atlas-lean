/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeTargetIso
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingZeroUnit
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingNaturality
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Original relative marked mapping complexes are functorial in the source

The precomposition map keeps the actual whole marked parameter prism and
its original fixed-base point. Native pullback lifting uses the original
source base equation. Identities and composition retain those same maps.
This constructs the genuine contravariant mapping functor on every
original marked slice, without a marked-model or fibrancy premise.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The original mapping base point precomposes with the actual source map. -/
theorem mappingBasePoint_pre (k : ParameterMarking) {X X' Z : Marked.{u}}
    (f : X' ⟶ X) (r : X ⟶ Z) :
    mappingBasePoint k (f ≫ r) = mappingBasePoint k r ≫ mappingComplexPre k f Z := by
  rw [mappingBasePoint, mappingBasePoint, yonedaEquiv_symm_comp]
  congr 1

/-- Actual source precomposition acts on the full original relative marked prism. -/
def relativeMappingPre (k : ParameterMarking) {X X' Y Z : Marked.{u}}
    (f : X' ⟶ X) (r : X ⟶ Z) (r' : X' ⟶ Z) (p : Y ⟶ Z) (hf : f ≫ r = r') :
    relativeMappingComplex k r p ⟶ relativeMappingComplex k r' p := by
  let a : relativeMappingComplex k r p ⟶ mappingComplex k X Y :=
    pullback.fst (mappingComplexPost k X p) (mappingBasePoint k r)
  let b : relativeMappingComplex k r p ⟶ (Δ[0] : SSet.{u}) :=
    pullback.snd (mappingComplexPost k X p) (mappingBasePoint k r)
  have hw : a ≫ mappingComplexPost k X p = b ≫ mappingBasePoint k r := pullback.condition
  exact pullback.lift (a ≫ mappingComplexPre k f Y) b (by
    rw [Category.assoc, mappingComplexPre_post, ← Category.assoc, hw,
      Category.assoc, ← mappingBasePoint_pre, hf])

/-- Precomposition retains the actual full prism precomposition as its first coordinate. -/
@[reassoc]
theorem relativeMappingPre_fst (k : ParameterMarking) {X X' Y Z : Marked.{u}}
    (f : X' ⟶ X) (r : X ⟶ Z) (r' : X' ⟶ Z) (p : Y ⟶ Z) (hf : f ≫ r = r') :
    relativeMappingPre k f r r' p hf ≫
        pullback.fst (mappingComplexPost k X' p) (mappingBasePoint k r') =
      pullback.fst (mappingComplexPost k X p) (mappingBasePoint k r) ≫ mappingComplexPre k f Y :=
  pullback.lift_fst _ _ _

/-- The original fixed-base point coordinate is unchanged by source precomposition. -/
@[reassoc]
theorem relativeMappingPre_snd (k : ParameterMarking) {X X' Y Z : Marked.{u}}
    (f : X' ⟶ X) (r : X ⟶ Z) (r' : X' ⟶ Z) (p : Y ⟶ Z) (hf : f ≫ r = r') :
    relativeMappingPre k f r r' p hf ≫
        pullback.snd (mappingComplexPost k X' p) (mappingBasePoint k r') =
      pullback.snd (mappingComplexPost k X p) (mappingBasePoint k r) :=
  pullback.lift_snd _ _ _

/-- Source identity precomposition keeps every original relative marked simplex. -/
theorem relativeMappingPre_id (k : ParameterMarking) {X Y Z : Marked.{u}}
    (r : X ⟶ Z) (p : Y ⟶ Z) :
    relativeMappingPre k (𝟙 X) r r p (Category.id_comp r) = 𝟙 (relativeMappingComplex k r p) := by
  let a : relativeMappingComplex k r p ⟶ mappingComplex k X Y :=
    pullback.fst (mappingComplexPost k X p) (mappingBasePoint k r)
  let b : relativeMappingComplex k r p ⟶ (Δ[0] : SSet.{u}) :=
    pullback.snd (mappingComplexPost k X p) (mappingBasePoint k r)
  apply (IsPullback.of_hasPullback (mappingComplexPost k X p) (mappingBasePoint k r)).hom_ext
  · change relativeMappingPre k (𝟙 X) r r p (Category.id_comp r) ≫ a = 𝟙 _ ≫ a
    calc
      _ = a ≫ mappingComplexPre k (𝟙 X) Y := relativeMappingPre_fst _ _ _ _ _ _
      _ = a ≫ 𝟙 _ := congrArg (fun t => a ≫ t) (mappingComplexPre_id k X Y)
      _ = _ := (Category.comp_id a).trans (Category.id_comp a).symm
  · change relativeMappingPre k (𝟙 X) r r p (Category.id_comp r) ≫ b = 𝟙 _ ≫ b
    exact (relativeMappingPre_snd k (𝟙 X) r r p (Category.id_comp r)).trans (Category.id_comp b).symm

/-- Two native source precompositions equal precomposition with the same original composite. -/
theorem relativeMappingPre_comp (k : ParameterMarking) {X X' X'' Y Z : Marked.{u}}
    (f : X' ⟶ X) (g : X'' ⟶ X') (r : X ⟶ Z) (r' : X' ⟶ Z) (r'' : X'' ⟶ Z)
    (p : Y ⟶ Z) (hf : f ≫ r = r') (hg : g ≫ r' = r'') :
    relativeMappingPre k (g ≫ f) r r'' p
      ((Category.assoc _ _ _).trans ((congrArg (fun t => g ≫ t) hf).trans hg)) =
      relativeMappingPre k f r r' p hf ≫ relativeMappingPre k g r' r'' p hg := by
  let P := relativeMappingPre k f r r' p hf
  let Q := relativeMappingPre k g r' r'' p hg
  let T := relativeMappingPre k (g ≫ f) r r'' p
    ((Category.assoc _ _ _).trans ((congrArg (fun t => g ≫ t) hf).trans hg))
  let a : relativeMappingComplex k r p ⟶ mappingComplex k X Y :=
    pullback.fst (mappingComplexPost k X p) (mappingBasePoint k r)
  let a' : relativeMappingComplex k r' p ⟶ mappingComplex k X' Y :=
    pullback.fst (mappingComplexPost k X' p) (mappingBasePoint k r')
  let a'' : relativeMappingComplex k r'' p ⟶ mappingComplex k X'' Y :=
    pullback.fst (mappingComplexPost k X'' p) (mappingBasePoint k r'')
  let b : relativeMappingComplex k r p ⟶ (Δ[0] : SSet.{u}) :=
    pullback.snd (mappingComplexPost k X p) (mappingBasePoint k r)
  let b' : relativeMappingComplex k r' p ⟶ (Δ[0] : SSet.{u}) :=
    pullback.snd (mappingComplexPost k X' p) (mappingBasePoint k r')
  let b'' : relativeMappingComplex k r'' p ⟶ (Δ[0] : SSet.{u}) :=
    pullback.snd (mappingComplexPost k X'' p) (mappingBasePoint k r'')
  have ha : P ≫ a' = a ≫ mappingComplexPre k f Y := relativeMappingPre_fst _ _ _ _ _ _
  have ha' : Q ≫ a'' = a' ≫ mappingComplexPre k g Y := relativeMappingPre_fst _ _ _ _ _ _
  have ha'' : T ≫ a'' = a ≫ mappingComplexPre k (g ≫ f) Y := relativeMappingPre_fst _ _ _ _ _ _
  have hb : P ≫ b' = b := relativeMappingPre_snd _ _ _ _ _ _
  have hb' : Q ≫ b'' = b' := relativeMappingPre_snd _ _ _ _ _ _
  have hb'' : T ≫ b'' = b := relativeMappingPre_snd _ _ _ _ _ _
  apply (IsPullback.of_hasPullback (mappingComplexPost k X'' p) (mappingBasePoint k r'')).hom_ext
  · change T ≫ a'' = (P ≫ Q) ≫ a''
    calc
      _ = a ≫ mappingComplexPre k (g ≫ f) Y := ha''
      _ = a ≫ (mappingComplexPre k f Y ≫ mappingComplexPre k g Y) :=
        congrArg (fun t => a ≫ t) (mappingComplexPre_comp k g f Y)
      _ = (a ≫ mappingComplexPre k f Y) ≫ mappingComplexPre k g Y := (Category.assoc _ _ _).symm
      _ = (P ≫ a') ≫ mappingComplexPre k g Y := congrArg (fun t => t ≫ mappingComplexPre k g Y) ha.symm
      _ = P ≫ (a' ≫ mappingComplexPre k g Y) := Category.assoc _ _ _
      _ = P ≫ (Q ≫ a'') := congrArg (fun t => P ≫ t) ha'.symm
      _ = _ := (Category.assoc _ _ _).symm
  · change T ≫ b'' = (P ≫ Q) ≫ b''
    have h : (P ≫ Q) ≫ b'' = b := (Category.assoc _ _ _).trans
      ((congrArg (fun t => P ≫ t) hb').trans hb)
    exact hb''.trans h.symm

/-- The actual original relative marked mapping complex is contravariant on all marked objects over the base. -/
def overMappingFunctor (k : ParameterMarking) (Z : Marked.{u}) (Y : Over Z) :
    (Over Z)ᵒᵖ ⥤ SSet.{u} where
  obj X := relativeMappingComplex k X.unop.hom Y.hom
  map {X X'} f := relativeMappingPre k f.unop.left X.unop.hom X'.unop.hom Y.hom (Over.w f.unop)
  map_id X := relativeMappingPre_id k X.unop.hom Y.hom
  map_comp {X X' X''} f g := relativeMappingPre_comp k f.unop.left g.unop.left
    X.unop.hom X'.unop.hom X''.unop.hom Y.hom (Over.w f.unop) (Over.w g.unop)

end SSet.Marked
