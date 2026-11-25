/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BehrendEulerObstructionModels
public import MathlibExt.AlgebraicGeometry.HallFamilyStackModels

/-!
# Genuine scheme-source points and smooth Behrend descent on Artin stacks

A scheme-source point is computed from the full represented-category
equivalence, its counit and its actual over-base comparison. The point
of the target is then the component of the original strong map.

The stack weight is fixed on every genuine smooth scheme chart by
ν_U=(-1)^relativeRank p*ν_stack, using the canonical normal-cone/Nash
scheme weight. Every complex-valued stack object is covered by such
a chart, and values are invariant under the actual groupoid arrows.
No independently chosen stack weight is an input.

References: Behrend, arXiv:math/0507523v2, Proposition 1.5;
Bridgeland, arXiv:1002.4374v3, Theorem 5.1, equation (25).
Ordinary Behrend-Euler integration requires no orientation data.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.StackBehrendModels

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open GeneralStackGeometry StackCycleGeometry StackFibreModels
open GeometricHallStackFunctions HallFamilyStackModels
open IntegralChowChernModels BehrendEulerObstructionModels
open ComplexAnalytification ConstructibleEulerCharacteristics

variable {Z : FiniteTypeStack}

/-- The native total-category object representing the actual scheme point. -/
def sourceParameter (S : SchemeSource Z) (p : space S.scheme) : Total Z.stack :=
  S.comparison.inverse.obj (Over.mk p.hom)

/-- Its base is canonically the complex point via the counit and over-base normalization. -/
def sourceBaseIso (S : SchemeSource Z) (p : space S.scheme) :
    (sourceParameter S p).base ≅ complexPoint :=
  S.overBase.symm.app (sourceParameter S p) ≪≫
    (Over.map S.scheme.hom).mapIso (S.comparison.counitIso.app (Over.mk p.hom)) ≪≫
      eqToIso (congrArg (fun f : base ⟶ base => Over.mk f) p.hom_comp)

/-- The actual stack object corresponding to this genuine complex scheme point. -/
def sourcePoint (S : SchemeSource Z) (p : space S.scheme) : Z.stack.Fibre complexPoint :=
  (pull Z.stack (sourceBaseIso S p).inv).obj (sourceParameter S p).fiber

/-- Its target image is computed by the original strong map. -/
def imagePoint {M : ComplexStack} (g : Generator M) (S : SchemeSource g.source)
    (p : space S.scheme) : M.Fibre complexPoint :=
  (component g.map complexPoint).obj (sourcePoint S p)

/-- Constant relative rank is tested on every actual scheme fibre. -/
def SmoothStackMap {A B : ComplexStack} (f : StackHom A B) (r : ℕ) : Prop :=
  ∀ (T : Over base) (x : B.Fibre T),
    ∃ F : SchemeFibreModel f T x, SmoothOfRelativeDimension r F.scheme.hom

/-- A scheme-source canonical weight uses the same represented scheme, with no replacement. -/
structure SourceSchemeWeight {Z : FiniteTypeStack} (S : SchemeSource Z) where
  data : SchemeData
  normalized : data.scheme=S.scheme
  model : SchemeBehrendModel data

def SourceSchemeWeight.value {Z : FiniteTypeStack} {S : SchemeSource Z}
    (W : SourceSchemeWeight S) (p : space S.scheme) : ℤ :=
  W.model.value (spaceMap (eqToHom W.normalized.symm) p)

/-- The invariant value is prescribed by canonical smooth-chart weights on a real cover. -/
structure StackBehrendModel (M : LocallyFiniteTypeStack) where
  value : M.stack.Fibre complexPoint → ℤ
  isoInvariant : ∀ (x y : M.stack.Fibre complexPoint), Nonempty (x ≅ y) → value x=value y
  chart : ∀ (g : Generator M.stack) (S : SchemeSource g.source) (r : ℕ)
    (_h : SmoothStackMap g.map r), SourceSchemeWeight S
  normalized : ∀ (g : Generator M.stack) (S : SchemeSource g.source) (r : ℕ)
    (h : SmoothStackMap g.map r) (p : space S.scheme),
    (chart g S r h).value p = (-1 : ℤ)^r * value (imagePoint g S p)
  covered : ∀ x : M.stack.Fibre complexPoint,
    ∃ (g : Generator M.stack) (S : SchemeSource g.source) (r : ℕ)
      (_h : SmoothStackMap g.map r) (p : space S.scheme),
      Nonempty (imagePoint g S p ≅ x)

/-- Pull the canonical stack weight along this actual regular source map. -/
def pulledStackWeight {M : LocallyFiniteTypeStack} (W : StackBehrendModel M)
    (g : Generator M.stack) (S : SchemeSource g.source) : space S.scheme → ℤ :=
  fun p => W.value (imagePoint g S p)

/-- Its weighted compact-support integral uses the actual stratum Betti ranks. -/
def weightedGenerator {M : LocallyFiniteTypeStack} (W : StackBehrendModel M)
    (g : Generator M.stack) (S : SchemeSource g.source)
    (P : EulerPresentation S.scheme (pulledStackWeight W g S)) : ℤ := weightedEuler P

end MathlibExt.AlgebraicGeometry.StackBehrendModels
