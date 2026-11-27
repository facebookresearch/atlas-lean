/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MarkedUntiltingPeriodModels
public import MathlibExt.AlgebraicGeometry.RelativeFFCurveFamilies
public import MathlibExt.AlgebraicGeometry.AnalyticBundlePrestackModels
public import MathlibExt.AlgebraicGeometry.RelativePerfectoidBases

/-!
# Actual untilt spaces, refinements and Cartier kernel ideals

The untilt analytic space is the existing affine realization on its
original ring, with E coefficients from the actual field action.
Refinement maps are the actual original untilt morphisms and their
residue-linear tilt maps. The Cartier ideal is the kernel of the
displayed native structure-presheaf map. Its generator agrees on
every restricted open, and is regular on every actual stalk.

Local period/completion comparisons are separate outputs; no global
affinoid neighbourhood containing an arbitrary entire untilt is assumed.
Source: Fargues--Scholze, arXiv:2102.13459v4, Sections I.2 and VI.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.UntiltingCartierModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite TopologicalSpace Topology
open _root_.AlgebraicGeometry
open LocalWittCoefficientFields RelativeFarguesFontaineRings RelativeFarguesFontaineMaps
open MarkedUntiltingPeriodModels AnalyticTateAdicModels AnalyticAdicDiamondification
open AnalyticGroupTorsorSites RelativeFFCurveFamilies

variable (p : ℕ) [Fact p.Prime] {E : MixedField p} (C : CoefficientData p E)
  (R : AffineRealization p) {S : Base p C}

def untiltObject (T : Untilting p C S) : ESpace p E.field :=
  CostructuredArrow.mk (Y := (realizationFunctor p R).obj T.affine)
    (CommRingCat.ofHom (((R.model T.affine).globalRing.toRingHom).comp
      (algebraMap E.field T.affine.pair.ring))).op

def selfWitness (T : Untilting p C S) :
    AnalyticAdicDiamondification.UntiltingWitness p R (untiltObject p C R T).left S.pair :=
  { affine := T.affine, tiltIso := T.tiltIso, map := 𝟙 _ }

/-- The marking point is the actual Kan unit followed by native v-sheafification. -/
def markingPoint (T : Untilting p C S) :
    ((AnalyticAdicDiamondification.diamondFunctor p R).obj
      (untiltObject p C R T).left).obj.obj (op S.pair) :=
  (toSheafify (AffinePerfectoidVSite.topology p)
    ((AnalyticAdicDiamondification.rawDiamondFunctor p R).obj (untiltObject p C R T).left)).app
      (op S.pair) (AnalyticAdicDiamondification.witnessMap (selfWitness p C R T))

structure TiltComparison (T : Untilting p C S) where
  comparison : (AnalyticAdicDiamondification.diamondFunctor p R).obj
    (untiltObject p C R T).left ≅ PerfectoidDiamondModels.affineSheaf p S.pair
  normalized : comparison.inv.hom.app (op S.pair)
    (RelativePerfectoidBases.affinePoint p (𝟙 S.pair)) = markingPoint p C R T

variable (I : LocalCoefficientScalarFrames.IntegerPresentation p C)
  (A : RelativeFFCurveFamilies.Family p C I) (T : Untilting p C S)

/-- The ideal is the literal kernel of the actual analytic closed-map structure homomorphism. -/
def kernelIdeal {X Y : ESpace p E.field} (f : X ⟶ Y) (U : Opens Y.left.obj.space) :
    Ideal (Y.left.obj.space.presheaf.obj (op U)) :=
  RingHom.ker ((f.left.hom.val.c.app (op U)).hom)

def IsCartier {X Y : ESpace p E.field} (f : X ⟶ Y) : Prop :=
  ∀ x : Y.left.obj.space, ∃ (U : Opens Y.left.obj.space), x ∈ U ∧
    ∃ a : Y.left.obj.space.presheaf.obj (op U),
      (∀ y hy, IsRegular (Y.left.obj.space.presheaf.germ U y hy a)) ∧
      (∀ (V : Opens Y.left.obj.space) (h : V ≤ U),
        kernelIdeal p f V = Ideal.span {Y.left.obj.space.presheaf.map (homOfLE h).op a})

def IsClosed {X Y : ESpace p E.field} (f : X ⟶ Y) : Prop :=
  IsClosedEmbedding f.left.hom.val.base ∧
    ∀ x : X.left.obj.space, Function.Surjective (f.left.hom.val.stalkMap x)

structure Refinement where
  base : Base p C
  baseMap : base ⟶ S
  untilt : Untilting p C base
  original : untilt.affine ⟶ T.affine
  tilt_normalized : (AffineUntiltingGeometry.tiltFunctor p).map original ≫ T.tiltIso.hom =
    untilt.tiltIso.hom ≫ baseMap.val
  map : untiltObject p C R untilt ⟶ untiltObject p C R T
  original_normalized : map.left = (realizationFunctor p R).map original
  open_embedding : IsOpenEmbedding map.left.hom.val.base
  stalk_iso : ∀ x, IsIso (map.left.hom.val.stalkMap x)

/-- A marked untilt determines an actual Cartier closed map into its actual relative curve. -/
structure Divisor where
  map : untiltObject p C R T ⟶ (A.frame S).object p C I
  closed : IsClosed p map
  cartier : IsCartier p map

end MathlibExt.AlgebraicGeometry.UntiltingCartierModels
