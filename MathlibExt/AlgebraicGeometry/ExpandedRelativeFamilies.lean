/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ExpansionScalingModels
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Actual expanded relative families and native base change

An arbitrary family has actual total/boundary schemes and contraction.
Etale neighborhoods identify it with actual pullbacks of the recursively
defined standard expansions, preserving projection, contraction and the
entire boundary map. Thus the expansion length may change in a family;
it is not fixed by a constant chain of ruled components.

Arrows are the actual boundary/contraction-preserving scheme isomorphisms.
Reindexing is normalized to native Cartesian pullbacks and their actual
boundary lifts. Source: Jun Li arXiv:math/0009097v1, Definition4.5 and
the family/pullback definitions in Section4.2, printed pp41--42.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ExpandedRelativeFamilies

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry
open ExpandedTargetChainGeometry ExpansionParameterModels StandardRelativeExpansionModels
open RelativeProjectiveLineModels CartierIdealModels

variable {k : Type} [Field k]
  (P : RelativePair (k := k)) (R : ProjectiveLine P.divisor.left (normalLineModule P))
  (S : StandardSystem P R)

def standardBoundaryLift {m : ℕ} (T : Over (Spec (.of k))) (f : T ⟶ ParameterSpace k m) :
    prod P.divisor T ⟶ pullback (S.chart m).projection f :=
  pullback.lift (prod.map (𝟙 P.divisor) f ≫ (S.chart m).boundary) prod.snd (by
    rw [Category.assoc]
    have hp : (S.chart m).boundary ≫ (S.chart m).projection = prod.snd := by
      rw [← (S.chart m).projection_eq, ← Category.assoc,
        (S.chart m).boundary_contraction, prod.map_snd, Category.comp_id]
    rw [hp, prod.map_snd])

structure LocalPresentation (T : Over (Spec (.of k))) (X : Over (Spec (.of k)))
    (p : X ⟶ T) (c : X ⟶ P.target) (d : prod P.divisor T ⟶ X) (t : T.left) where
  neighborhood : Over (Spec (.of k))
  map : neighborhood ⟶ T
  etale : Etale map.left
  contains : t ∈ Set.range map.left
  length : ℕ
  parameter : neighborhood ⟶ ParameterSpace k length
  comparison : pullback p map ≅ pullback (S.chart length).projection parameter
  projection : comparison.hom ≫ pullback.snd (S.chart length).projection parameter = pullback.snd p map
  contraction : comparison.hom ≫ pullback.fst (S.chart length).projection parameter ≫
    (S.chart length).contraction ≫ prod.fst = pullback.fst p map ≫ c
  boundary : ∀ h : d ≫ p = prod.snd,
    pullback.lift (prod.map (𝟙 P.divisor) map ≫ d) prod.snd
      (by rw [Category.assoc, h, prod.map_snd]) ≫ comparison.hom =
        standardBoundaryLift P R S neighborhood parameter

structure ExpandedFamily (T : Over (Spec (.of k))) where
  scheme : Over (Spec (.of k))
  projection : scheme ⟶ T
  contraction : scheme ⟶ P.target
  boundary : prod P.divisor T ⟶ scheme
  [closed : IsClosedImmersion boundary.left]
  cartier : IsEffectiveCartier boundary.left.ker
  boundary_projection : boundary ≫ projection = prod.snd
  boundary_contraction : boundary ≫ contraction = prod.fst ≫ P.inclusion
  localPresentation : ∀ t : T.left,
    LocalPresentation P R S T scheme projection contraction boundary t

attribute [instance] ExpandedFamily.closed

/-- Identification with an effective standard family preserves all actual maps. -/
structure StandardFamilyIdentification {T : Over (Spec (.of k))}
    (F : ExpandedFamily P R S T) (m : ℕ) (f : T ⟶ ParameterSpace k m) where
  comparison : F.scheme ≅ pullback (S.chart m).projection f
  projection : comparison.hom ≫ pullback.snd (S.chart m).projection f = F.projection
  contraction : comparison.hom ≫ pullback.fst (S.chart m).projection f ≫
    (S.chart m).contraction ≫ prod.fst = F.contraction
  boundary : F.boundary ≫ comparison.hom = standardBoundaryLift P R S T f

structure ExpandedIso {T : Over (Spec (.of k))} (F G : ExpandedFamily P R S T) where
  iso : F.scheme ≅ G.scheme
  over : iso.hom ≫ G.projection = F.projection
  contraction : iso.hom ≫ G.contraction = F.contraction
  boundary : F.boundary ≫ iso.hom = G.boundary

@[ext] theorem ExpandedIso.ext {T : Over (Spec (.of k))} {F G : ExpandedFamily P R S T}
    (f g : ExpandedIso P R S F G) (h : f.iso = g.iso) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance expandedGroupoid (T : Over (Spec (.of k))) : Groupoid (ExpandedFamily P R S T) where
  Hom F G := ExpandedIso P R S F G
  id F := ⟨Iso.refl _, by simp, by simp, by simp⟩
  comp f g := ⟨f.iso ≪≫ g.iso, by simp [Category.assoc, g.over, f.over],
    by simp [Category.assoc, g.contraction, f.contraction],
    by simp [← Category.assoc, f.boundary, g.boundary]⟩
  inv f := ⟨f.iso.symm, by rw [← f.over]; simp,
    by rw [← f.contraction]; simp, by rw [← f.boundary]; simp⟩
  id_comp f := by apply ExpandedIso.ext; ext; simp
  comp_id f := by apply ExpandedIso.ext; ext; simp
  assoc f g h := by apply ExpandedIso.ext; ext; simp
  inv_comp f := by apply ExpandedIso.ext; ext; simp

structure ExpandedReindex {T U : Over (Spec (.of k))} (f : T ⟶ U)
    (F : ExpandedFamily P R S U) where
  family : ExpandedFamily P R S T
  comparison : family.scheme ≅ pullback F.projection f
  projection : comparison.hom ≫ pullback.snd F.projection f = family.projection
  contraction : comparison.hom ≫ pullback.fst F.projection f ≫ F.contraction = family.contraction
  boundary : family.boundary ≫ comparison.hom =
    pullback.lift (prod.map (𝟙 P.divisor) f ≫ F.boundary) prod.snd
      (by rw [Category.assoc, F.boundary_projection, prod.map_snd])

end MathlibExt.AlgebraicGeometry.ExpandedRelativeFamilies
