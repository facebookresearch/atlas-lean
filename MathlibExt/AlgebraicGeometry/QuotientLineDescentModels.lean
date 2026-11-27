/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GroupTorsorGeometry

/-!
# Actual equivariant-line descent along a quotient-stack point

The line on the torsor is the literal pullback of the given linearized
line. Its action comparison is computed from that original linearization
and the actual equivariant map. A descended line is required to match
this full comparison through the native pullback identity square.
Affinewise line isomorphisms alone do not provide that descent data.

References: Stacks Project, Tag 03LF; Ciocan-Fontanine--Kim--Maulik,
arXiv:1106.3724v2, Sections 2.4 and 7.1. The generic fppf equivariant
descent theorem is completed public source integration; these are native
map and result-type adapters.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.QuotientLineDescentModels

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open _root_.AlgebraicGeometry
open GroupTorsorGeometry LinearizedLineBundles CoherentCurveLinearSeries

universe u

variable {S : Scheme.{u}} (G W : Over S) [GrpObj G] [ModObj G W]
variable {T : Over S} (P : QuotientObject G W T)

/-- The actual module on the total torsor. -/
def pulledModule (E : LinearizedLineBundle G W) : P.torsor.total.left.Modules :=
  (Scheme.Modules.pullback P.map.left).obj E.module

/-- The source projection identity of the equivariant map. -/
theorem projection_square :
    (G ◁ P.map) ≫ snd G W = snd G P.torsor.total ≫ P.map :=
  whiskerLeft_snd _ _

/-- The complete action comparison is pulled from the original actual line. -/
def pulledComparison (E : LinearizedLineBundle G W) :
    (Scheme.Modules.pullback (action G P.torsor.total)).obj (pulledModule G W P E) ⟶
      (Scheme.Modules.pullback (projection G P.torsor.total)).obj (pulledModule G W P E) :=
  (Scheme.Modules.pullbackComp (action G P.torsor.total) P.map.left).hom.app E.module ≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left P.equivariant)).hom.app E.module ≫
      reindexHom (G ◁ P.map).left E.linearization.comparison.hom ≫
        (Scheme.Modules.pullbackCongr
          (congrArg Over.Hom.left (projection_square G W P))).hom.app E.module ≫
            (Scheme.Modules.pullbackComp (projection G P.torsor.total) P.map.left).inv.app E.module

/-- Pulling a parameter line back to its torsor gives the native invariant comparison. -/
def parameterComparison (L : T.left.Modules) :
    (Scheme.Modules.pullback (action G P.torsor.total)).obj
        ((Scheme.Modules.pullback P.torsor.projection.left).obj L) ⟶
      (Scheme.Modules.pullback (projection G P.torsor.total)).obj
        ((Scheme.Modules.pullback P.torsor.projection.left).obj L) :=
  (Scheme.Modules.pullbackComp (action G P.torsor.total)
    P.torsor.projection.left).hom.app L ≫
    (Scheme.Modules.pullbackCongr
      (congrArg Over.Hom.left P.torsor.invariant)).hom.app L ≫
        (Scheme.Modules.pullbackComp (projection G P.torsor.total)
          P.torsor.projection.left).inv.app L

/-- The full descended module-line comparison, including every actual action arrow. -/
structure DescendedLine (E : LinearizedLineBundle G W) where
  module : T.left.Modules
  line : IsLineBundle module
  comparison : (Scheme.Modules.pullback P.torsor.projection.left).obj module ≅
    pulledModule G W P E
  normalized : parameterComparison G W P module ≫
      (Scheme.Modules.pullback (projection G P.torsor.total)).map comparison.hom =
    (Scheme.Modules.pullback (action G P.torsor.total)).map comparison.hom ≫
      pulledComparison G W P E

end MathlibExt.AlgebraicGeometry.QuotientLineDescentModels
