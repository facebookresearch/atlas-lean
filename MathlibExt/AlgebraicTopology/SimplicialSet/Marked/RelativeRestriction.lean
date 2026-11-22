/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ParameterRestriction
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverMappingFunctor
import MathlibExt.AlgebraicTopology.Quasicategory.CoreFibration

/-!
# Categorical and core fibrations on original relative source restriction

Restriction of full ordinary fixed-base prisms is the actual pullback of
the native function comparison. Its literal core restriction is therefore
a Kan fibration whenever the original projection is inner with strict
equivalence lifting over a quasicategory. Both original coordinates and
all marked forgetful maps are preserved, for arbitrary source markings.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- Forgetting source restriction keeps the same whole original prism. -/
theorem mappingComplexUnderlying_pre (k : ParameterMarking) {X X' : Marked.{u}}
    (f : X' ⟶ X) (Y : Marked.{u}) :
    mappingComplexPre k f Y ≫ mappingComplexUnderlying k X' Y =
      mappingComplexUnderlying k X Y ≫ parameterMappingPre f.hom Y.toSSet := by
  cases k <;> ext n F <;> rfl

/-- The original unmarked fixed-base point restricts to the original composite map. -/
theorem parameterBasePoint_pre {X X' Z : Marked.{u}} (f : X' ⟶ X) (r : X ⟶ Z) :
    parameterBasePoint (f ≫ r) = parameterBasePoint r ≫ parameterMappingPre f.hom Z.toSSet := by
  unfold parameterBasePoint
  rw [mappingBasePoint_pre, Category.assoc, mappingComplexUnderlying_pre, ← Category.assoc]

/-- The ordinary relative restriction uses precisely the original total prism and base point. -/
def parameterRelativePre {X X' Y Z : Marked.{u}} (f : X' ⟶ X)
    (r : X ⟶ Z) (r' : X' ⟶ Z) (p : Y ⟶ Z) (hf : f ≫ r = r') :
    parameterRelative r p ⟶ parameterRelative r' p :=
  fibreRestriction (parameterMappingPre f.hom Y.toSSet)
    (parameterMappingPost X.toSSet p.hom) (parameterMappingPost X'.toSSet p.hom)
    (parameterMappingPre f.hom Z.toSSet) (parameterMappingPre_post f.hom p.hom)
    (parameterBasePoint r) (parameterBasePoint r')
    (by rw [← parameterBasePoint_pre, hf])

/-- The whole original prism coordinate of relative source restriction. -/
@[reassoc]
theorem parameterRelativePre_fst {X X' Y Z : Marked.{u}} (f : X' ⟶ X)
    (r : X ⟶ Z) (r' : X' ⟶ Z) (p : Y ⟶ Z) (hf : f ≫ r = r') :
    parameterRelativePre f r r' p hf ≫
        pullback.fst (parameterMappingPost X'.toSSet p.hom) (parameterBasePoint r') =
      pullback.fst (parameterMappingPost X.toSSet p.hom) (parameterBasePoint r) ≫
        parameterMappingPre f.hom Y.toSSet := fibreRestriction_fst ..

/-- Relative restriction retains the original point coordinate. -/
@[reassoc]
theorem parameterRelativePre_snd {X X' Y Z : Marked.{u}} (f : X' ⟶ X)
    (r : X ⟶ Z) (r' : X' ⟶ Z) (p : Y ⟶ Z) (hf : f ≫ r = r') :
    parameterRelativePre f r r' p hf ≫
        pullback.snd (parameterMappingPost X'.toSSet p.hom) (parameterBasePoint r') =
      pullback.snd (parameterMappingPost X.toSSet p.hom) (parameterBasePoint r) :=
  fibreRestriction_snd ..

/-- Forgetting all relative marks commutes with the same original source map. -/
theorem relativeMappingForget_pre (k : ParameterMarking) {X X' Y Z : Marked.{u}}
    (f : X' ⟶ X) (r : X ⟶ Z) (r' : X' ⟶ Z) (p : Y ⟶ Z) (hf : f ≫ r = r') :
    relativeMappingPre k f r r' p hf ≫ relativeMappingForget k r' p =
      relativeMappingForget k r p ≫ parameterRelativePre f r r' p hf := by
  let a : relativeMappingComplex k r p ⟶ relativeMappingComplex k r' p :=
    relativeMappingPre k f r r' p hf
  let b : relativeMappingComplex k r' p ⟶ parameterRelative r' p := relativeMappingForget k r' p
  let c : relativeMappingComplex k r p ⟶ parameterRelative r p := relativeMappingForget k r p
  let d : parameterRelative r p ⟶ parameterRelative r' p := parameterRelativePre f r r' p hf
  let u : parameterRelative r p ⟶ parameterMapping X.toSSet Y.toSSet := pullback.fst _ _
  let u' : parameterRelative r' p ⟶ parameterMapping X'.toSSet Y.toSSet := pullback.fst _ _
  let v : parameterRelative r p ⟶ (Δ[0] : SSet.{u}) := pullback.snd _ _
  let v' : parameterRelative r' p ⟶ (Δ[0] : SSet.{u}) := pullback.snd _ _
  let t : relativeMappingComplex k r p ⟶ mappingComplex k X Y := pullback.fst _ _
  let t' : relativeMappingComplex k r' p ⟶ mappingComplex k X' Y := pullback.fst _ _
  let w : relativeMappingComplex k r p ⟶ (Δ[0] : SSet.{u}) := pullback.snd _ _
  let w' : relativeMappingComplex k r' p ⟶ (Δ[0] : SSet.{u}) := pullback.snd _ _
  have hb : b ≫ u' = t' ≫ mappingComplexUnderlying k X' Y := relativeMappingForget_fst _ _ _
  have hc : c ≫ u = t ≫ mappingComplexUnderlying k X Y := relativeMappingForget_fst _ _ _
  have hd : d ≫ u' = u ≫ parameterMappingPre f.hom Y.toSSet := parameterRelativePre_fst _ _ _ _ _
  have ha : a ≫ t' = t ≫ mappingComplexPre k f Y := relativeMappingPre_fst _ _ _ _ _ _
  have hb' : b ≫ v' = w' := relativeMappingForget_snd _ _ _
  have hc' : c ≫ v = w := relativeMappingForget_snd _ _ _
  have hd' : d ≫ v' = v := parameterRelativePre_snd _ _ _ _ _
  have ha' : a ≫ w' = w := relativeMappingPre_snd _ _ _ _ _ _
  apply (IsPullback.of_hasPullback (parameterMappingPost X'.toSSet p.hom) (parameterBasePoint r')).hom_ext
  · change (a ≫ b) ≫ u' = (c ≫ d) ≫ u'
    rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc,
      mappingComplexUnderlying_pre, ← Category.assoc, ← hc, Category.assoc, ← hd, ← Category.assoc]
  · change (a ≫ b) ≫ v' = (c ≫ d) ≫ v'
    rw [Category.assoc, hb', ha', Category.assoc, hd', hc']

/-- Original relative restriction is a categorical fibration under the genuine native hypotheses. -/
theorem parameterRelativePre_categoricalFibrations {X X' Y Z : Marked.{u}}
    (f : X' ⟶ X) [Mono f.hom] (r : X ⟶ Z) (r' : X' ⟶ Z)
    (p : Y ⟶ Z) (hf : f ≫ r = r') [InnerFibration p.hom]
    [Quasicategory Z.toSSet] [HasStrictEquivalenceLifting p.hom] :
    categoricalFibrations (parameterRelativePre f r r' p hf) := by
  let sq := IsPullback.of_hasPullback
    (parameterMappingPost X'.toSSet p.hom) (parameterMappingPre f.hom Z.toSSet)
  let d := parameterUnderlyingComparison f.hom p.hom
  have hPB := fibreRestriction_isPullback
    (parameterMappingPre f.hom Y.toSSet)
    (parameterMappingPost X.toSSet p.hom) (parameterMappingPost X'.toSSet p.hom)
    (parameterMappingPre f.hom Z.toSSet) (parameterMappingPre_post f.hom p.hom)
    (parameterBasePoint r) (parameterBasePoint r')
    (by rw [← parameterBasePoint_pre, hf]) sq d
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  exact categoricalFibrations.of_isPullback hPB
    (parameterUnderlyingComparison_categoricalFibrations f.hom p.hom)

open scoped SSet.modelCategoryQuillen in
/-- The literal core restriction of original fixed-base prisms is a Kan fibration. -/
theorem fibration_core_parameterRelativePre {X X' Y Z : Marked.{u}}
    (f : X' ⟶ X) [Mono f.hom] (r : X ⟶ Z) (r' : X' ⟶ Z)
    (p : Y ⟶ Z) (hf : f ≫ r = r') [InnerFibration p.hom]
    [Quasicategory Z.toSSet] [HasStrictEquivalenceLifting p.hom] :
    HomotopicalAlgebra.Fibration (core.map (parameterRelativePre f r r' p hf)) := by
  let q := parameterRelativePre f r r' p hf
  let _ : Quasicategory (parameterRelative r' p) := parameterRelative_quasicategory r' p
  have h := (categoricalFibrations_iff_innerFibration_and_hasStrictEquivalenceLifting q).mp
    (parameterRelativePre_categoricalFibrations f r r' p hf)
  let _ : InnerFibration q := h.1
  let _ : HasStrictEquivalenceLifting q := h.2
  exact fibration_core_map_of_hasStrictEquivalenceLifting q

end SSet.Marked
