/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PlacewiseMetrizedLineModels
public import MathlibExt.AlgebraicGeometry.GenericSectionMaps

/-!
# Common arithmetic models and genuine placewise integral frames

The arithmetic model is one actual scheme over a common base, with an
actual proper generic compactification of the possibly nonproper X.
Every place centre has the fixed base and generic-fibre equations.
Integral frames are sections of that same model line, and completed
fibre bases equal their actual pulled-back germs. Norms are the native
norms of those frame coordinates.

This permits open quasi-projective varieties: X is an open in the full
generic fibre, rather than being forced to be the whole proper fibre.
Reference: Yuan--Zhang, arXiv:2105.13587v9, Sections 2.1--2.2 and A.5.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AdelicArithmeticModelFrames

open CategoryTheory CategoryTheory.Limits Opposite Module
open _root_.AlgebraicGeometry
open PlacewiseMetrizedLineModels CoherentCurveLinearSeries
open GenericSectionMaps ValuedLineFibres ModelLineMetrics

variable {K : Type} [Field K] (A : AdelicField K)

/-- The actual common arithmetic base, with every valuation-ring centre. -/
structure ArithmeticBase where
  scheme : Scheme.{0}
  generic : Spec (.of K) ⟶ scheme
  centre : ∀ (v : A.places) (h : ∀ a b : A.completion v, ‖a + b‖ ≤ max ‖a‖ ‖b‖),
    Spec (.of (integerRing (A.completion v) h)) ⟶ scheme
  generic_square : ∀ (v : A.places)
    (h : ∀ a b : A.completion v, ‖a + b‖ ≤ max ‖a‖ ‖b‖),
    Spec.map (CommRingCat.ofHom (integerRing (A.completion v) h).subtype) ≫ centre v h =
      Spec.map (CommRingCat.ofHom (A.embedding v)) ≫ generic

variable (X : Over (Spec (.of K))) (L : X.left.Modules)

/-- An actual common model of a generic compactification and its line. -/
structure ArithmeticModel where
  base : ArithmeticBase A
  scheme : Scheme.{0}
  structureMap : scheme ⟶ base.scheme
  [proper : IsProper structureMap]
  [flat : Flat structureMap]
  [presentation : LocallyOfFinitePresentation structureMap]
  compactification : Over (Spec (.of K))
  [generic_proper : IsProper compactification.hom]
  openMap : X ⟶ compactification
  [openImmersion : IsOpenImmersion openMap.left]
  dense : DenseRange openMap.left
  genericMap : compactification.left ⟶ scheme
  genericSquare : IsPullback genericMap compactification.hom structureMap base.generic
  line : scheme.Modules
  isLine : IsLineBundle line
  genericLine : (Scheme.Modules.pullback (openMap.left ≫ genericMap)).obj line ≅ L

variable {A X L} (M : ArithmeticModel A X L)

def placeModelMap (v : A.places) : (placeScheme A X v).left ⟶ M.scheme :=
  placeProjection A X v ≫ M.openMap.left ≫ M.genericMap

def placeModelLine (v : A.places) :
    (Scheme.Modules.pullback (placeModelMap M v)).obj M.line ≅ placeLine A X L v :=
  ((Scheme.Modules.pullbackComp (placeProjection A X v)
    (M.openMap.left ≫ M.genericMap)).app M.line).symm ≪≫
      (Scheme.Modules.pullback (placeProjection A X v)).mapIso M.genericLine

structure Centre (v : A.places)
    (h : ∀ a b : A.completion v, ‖a + b‖ ≤ max ‖a‖ ‖b‖)
    (p : NonArchPoint (A.completion v) (placeScheme A X v)) where
  map : Spec (.of (residueIntegers (A.completion v) (placeScheme A X v) p)) ⟶ M.scheme
  base : map ≫ M.structureMap =
    Spec.map (CommRingCat.ofHom (integralScalar (A.completion v) (placeScheme A X v) h p)) ≫
      M.base.centre v h
  generic : Spec.map (CommRingCat.ofHom (residueIntegers _ _ p).subtype) ≫ map =
    Spec.map (CommRingCat.ofHom (completionUnit _ _ p.val)) ≫
      (placeScheme A X v).left.fromSpecResidueField p.val.schemePoint ≫ placeModelMap M v

def pullModelSection (v : A.places) {U : M.scheme.Opens} (s : Γ(M.line,U)) :
    Γ(placeLine A X L v, placeModelMap M v ⁻¹ᵁ U) :=
  (placeModelLine M v).hom.app (placeModelMap M v ⁻¹ᵁ U)
    (((Scheme.Modules.pullbackPushforwardAdjunction (placeModelMap M v)).unit.app M.line).app U s)

/-- A model frame is an actual local section and its completed generic germ. -/
structure FrameAt {v : A.places}
    {h : ∀ a b : A.completion v, ‖a + b‖ ≤ max ‖a‖ ‖b‖}
    {p : NonArchPoint (A.completion v) (placeScheme A X v)} (C : Centre M v h p) where
  openSet : M.scheme.Opens
  centre_mem : ∀ y : Spec (.of (residueIntegers _ _ p)), C.map y ∈ openSet
  point_mem : placeModelMap M v p.val.schemePoint ∈ openSet
  sectionValue : Γ(M.line,openSet)
  basis : ∀ (y : M.scheme) (_hy : y ∈ openSet),
    Basis Unit (M.scheme.presheaf.stalk y)
      (↑(TopCat.Presheaf.stalk M.line.val.presheaf y : AddCommGrpCat.{0}))
  local_generator : ∀ (y : M.scheme) (hy : y ∈ openSet),
    basis y hy () = TopCat.Presheaf.germ M.line.val.presheaf openSet y hy sectionValue
  fibreBasis : Basis Unit (CompletedResidue _ _ p.val)
    (ValuedLineFibres.Fibre (A.completion v) (placeScheme A X v) (placeLine A X L v) p.val)
  fibre_generator : fibreBasis () =
    evaluateSection _ _ _ (pullModelSection M v sectionValue) p.val point_mem

def frameNorm {v : A.places}
    {h : ∀ a b : A.completion v, ‖a + b‖ ≤ max ‖a‖ ‖b‖}
    {p : NonArchPoint (A.completion v) (placeScheme A X v)} {C : Centre M v h p}
    (F : FrameAt M C)
    (z : ValuedLineFibres.Fibre (A.completion v) (placeScheme A X v)
      (placeLine A X L v) p.val) : ℝ :=
  ‖F.fibreBasis.repr z ()‖

end MathlibExt.AlgebraicGeometry.AdelicArithmeticModelFrames
