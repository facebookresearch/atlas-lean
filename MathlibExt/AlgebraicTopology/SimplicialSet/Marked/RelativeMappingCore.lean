/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativePrisms
import MathlibExt.AlgebraicTopology.SimplicialSet.FullSubcomplexKan

/-!
# The native fixed-base function core on marked-map vertices

This is the full subcomplex of the already existing native core of the
original unmarked fixed-base pullback, on vertices that preserve the
supplied marking. Its map into the minimal marked complex retains the
same entire prism and the same base equation. The carrier is Kan whenever
the original target map is inner; no marked model structure is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The original core vertices whose whole zero-prism is a marked-map vertex. -/
def relativeMappingCoreVertices {X Y Z : Marked.{u}} (r : X ⟶ Z) (p : Y ⟶ Z) :
    Set ((core (parameterRelative r p) : SSet.{u}) _⦋0⦌) :=
  ((core (parameterRelative r p)).ι ≫
    pullback.fst (parameterMappingPost X.toSSet p.hom) (parameterBasePoint r)).app (op ⦋0⦌) ⁻¹'
      markedMappingVertices X Y

/-- The actual fixed-base native core, restricted to the original marked-map vertices. -/
def relativeMappingCore {X Y Z : Marked.{u}} (r : X ⟶ Z) (p : Y ⟶ Z) : SSet.{u} :=
  Subcomplex.full (relativeMappingCoreVertices r p)

/-- Both full-subcomplex and core inclusions retain the original unmarked relative simplex. -/
def relativeMappingCoreToUnderlying {X Y Z : Marked.{u}} (r : X ⟶ Z) (p : Y ⟶ Z) :
    relativeMappingCore r p ⟶ parameterRelative r p :=
  (Subcomplex.full (relativeMappingCoreVertices r p)).ι ≫ (core (parameterRelative r p)).ι

/-- The two original subcomplex inclusions identify no native simplex. -/
theorem relativeMappingCoreToUnderlying_mono {X Y Z : Marked.{u}} (r : X ⟶ Z) (p : Y ⟶ Z) :
    Mono (relativeMappingCoreToUnderlying r p) := by
  let _ : ∀ n : SimplexCategoryᵒᵖ, Mono ((relativeMappingCoreToUnderlying r p).app n) := fun n =>
    (CategoryTheory.mono_iff_injective _).mpr (by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact h)
  exact NatTrans.mono_of_mono_app _

/-- The same original core prism gives its actual minimally parameter-marked map. -/
def relativeMappingCoreToMin {X Y Z : Marked.{u}} (r : X ⟶ Z) (p : Y ⟶ Z) :
    relativeMappingCore r p ⟶ mappingComplex .minimal X Y :=
  Subcomplex.mapFull (S := relativeMappingCoreVertices r p) (T := markedMappingVertices X Y)
    ((core (parameterRelative r p)).ι ≫
    pullback.fst (parameterMappingPost X.toSSet p.hom) (parameterBasePoint r))
      (fun {_} h => h) ≫ (mappingComplexMinFullIso X Y).inv

/-- The minimal marked map retains precisely the original native-core prism. -/
theorem relativeMappingCoreToMin_forget {X Y Z : Marked.{u}} (r : X ⟶ Z) (p : Y ⟶ Z) :
    relativeMappingCoreToMin r p ≫ mappingComplexUnderlying .minimal X Y =
      relativeMappingCoreToUnderlying r p ≫
        pullback.fst (parameterMappingPost X.toSSet p.hom) (parameterBasePoint r) := by
  ext n t
  rfl

/-- This same minimal marked map lies over the supplied original source projection. -/
theorem relativeMappingCoreToMin_post {X Y Z : Marked.{u}} (r : X ⟶ Z) (p : Y ⟶ Z) :
    relativeMappingCoreToMin r p ≫ mappingComplexPost .minimal X p =
      relativeMappingCoreToUnderlying r p ≫
        pullback.snd (parameterMappingPost X.toSSet p.hom) (parameterBasePoint r) ≫
          mappingBasePoint .minimal r := by
  let _ : Mono (mappingComplexUnderlying .minimal X Z) := mappingComplexUnderlying_mono .minimal X Z
  apply (cancel_mono (mappingComplexUnderlying .minimal X Z)).mp
  let a : parameterRelative r p ⟶ parameterMapping X.toSSet Y.toSSet :=
    pullback.fst (parameterMappingPost X.toSSet p.hom) (parameterBasePoint r)
  let b : parameterRelative r p ⟶ (Δ[0] : SSet.{u}) :=
    pullback.snd (parameterMappingPost X.toSSet p.hom) (parameterBasePoint r)
  let j : relativeMappingCore r p ⟶ parameterRelative r p := relativeMappingCoreToUnderlying r p
  let l : relativeMappingCore r p ⟶ mappingComplex .minimal X Y := relativeMappingCoreToMin r p
  have hl : l ≫ mappingComplexUnderlying .minimal X Y = j ≫ a := relativeMappingCoreToMin_forget r p
  have hb : a ≫ parameterMappingPost X.toSSet p.hom = b ≫ parameterBasePoint r := pullback.condition
  change (l ≫ mappingComplexPost .minimal X p) ≫ mappingComplexUnderlying .minimal X Z =
    (j ≫ b ≫ mappingBasePoint .minimal r) ≫ mappingComplexUnderlying .minimal X Z
  rw [Category.assoc, mappingComplexUnderlying_post, ← Category.assoc, hl, Category.assoc, hb]
  simp only [Category.assoc, mappingBasePoint_underlying]

/-- The whole original prism of a core simplex preserves its supplied fixed-base equation. -/
theorem relativeMappingCoreToMin_prism_over {X Y Z : Marked.{u}} (r : X ⟶ Z) (p : Y ⟶ Z)
    (n : SimplexCategoryᵒᵖ) (t : (relativeMappingCore r p).obj n) :
    ((relativeMappingCoreToMin r p).app n t).hom ≫ p.hom =
      CartesianMonoidalCategory.snd (SSet.stdSimplex.obj n.unop) X.toSSet ≫ r.hom := by
  have h := ConcreteCategory.congr_hom (congr_app (relativeMappingCoreToMin_post r p) n) t
  have h' := congrArg Hom.hom h
  change ((relativeMappingCoreToMin r p).app n t).hom ≫ p.hom =
    ((mappingBasePoint .minimal r).app n
      ((relativeMappingCoreToUnderlying r p ≫
        pullback.snd (parameterMappingPost X.toSSet p.hom) (parameterBasePoint r)).app n t)).hom at h'
  rw [mappingBasePoint_app_hom] at h'
  exact h'

/-- The same whole minimal prism is in the existing native function core. -/
theorem relativeMappingCoreToMin_mem_core {X Y Z : Marked.{u}} (r : X ⟶ Z) (p : Y ⟶ Z)
    (n : SimplexCategoryᵒᵖ) (t : (relativeMappingCore r p).obj n) :
    ((relativeMappingCoreToMin r p).app n t).hom ∈
      (core (parameterMapping X.toSSet Y.toSSet)).obj n := by
  let a : (core (parameterRelative r p) : SSet.{u}).obj n :=
    (Subcomplex.full (relativeMappingCoreVertices r p)).ι.app n t
  let b := (core.map
    (pullback.fst (parameterMappingPost X.toSSet p.hom) (parameterBasePoint r))).app n a
  have h := ConcreteCategory.congr_hom (congr_app (relativeMappingCoreToMin_forget r p) n) t
  have hb : ((relativeMappingCoreToMin r p).app n t).hom = b.val := h
  exact hb.symm ▸ b.property

/-- This original fixed-base full core carrier has genuine native Kan fibrancy. -/
theorem relativeMappingCore_kanComplex {X Y Z : Marked.{u}} (r : X ⟶ Z) (p : Y ⟶ Z)
    [InnerFibration p.hom] : KanComplex (relativeMappingCore r p) := by
  let _ : Quasicategory (parameterRelative r p) := parameterRelative_quasicategory r p
  let _ : KanComplex (core (parameterRelative r p) : SSet.{u}) := inferInstance
  exact Subcomplex.kanComplex_full (relativeMappingCoreVertices r p)

end SSet.Marked
