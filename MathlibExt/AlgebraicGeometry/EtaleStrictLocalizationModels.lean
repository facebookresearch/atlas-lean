/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import MathlibExt.AlgebraicGeometry.CotangentBundleTestModels

/-!
# Native pointed étale limits and Milnor fibres

Strict localization is a limit of the actual affine étale neighbourhoods
of the given geometric point. The diagram is Mathlib's category of
elements of its native étale point fibre functor, followed by the actual
affine Spec/forgetful functors. Its closed geometric point is the native
limit lift of the cone of those neighbourhood points.

A Milnor fibre is the actual scheme pullback X_(x) ×_Y_(y) t, with the
local scheme map fixed over the original map and its geometric point.
No substitute fibre space, stalk or specialization map is stored here.

Reference: Saito, arXiv:1510.03018v4, Section 1.1, printed pages 4--5;
SGA 4, strict localization as the pointed étale limit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.EtaleStrictLocalizationModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open CotangentBundleTestModels

variable {X : Scheme.{0}} (Ω : GeometricField) (x : Spec (.of Ω.carrier) ⟶ X)

abbrev neighbourhoodFibre := Scheme.AffineEtale.Spec X ⋙ (Scheme.pointSmallEtale x).fiber

abbrev Neighbourhoods := (neighbourhoodFibre Ω x).Elements

def neighbourhoodDiagram : Neighbourhoods Ω x ⥤ Over X :=
  Functor.Elements.π (neighbourhoodFibre Ω x) ⋙ Scheme.AffineEtale.Spec X ⋙ Scheme.Etale.forget X

def geometricPointCone : Cone (neighbourhoodDiagram Ω x) where
  pt := Over.mk x
  π :=
    { app N := N.val
      naturality N M f := by
        change 𝟙 (Over.mk x) ≫ M.val = N.val ≫ (neighbourhoodDiagram Ω x).map f
        simpa [neighbourhoodFibre, neighbourhoodDiagram, Scheme.pointSmallEtale]
          using f.map_val.symm }

/-- The native limit over actual pointed affine étale neighbourhoods. -/
structure StrictLocalization where
  cone : Cone (neighbourhoodDiagram Ω x)
  isLimit : IsLimit cone

namespace StrictLocalization

variable {Ω x} (L : StrictLocalization Ω x)

abbrev scheme : Scheme.{0} := L.cone.pt.left
abbrev map : L.scheme ⟶ X := L.cone.pt.hom

def pointOver : Over.mk x ⟶ L.cone.pt := L.isLimit.lift (geometricPointCone Ω x)

def point : Spec (.of Ω.carrier) ⟶ L.scheme := L.pointOver.left

@[simp] theorem point_map : L.point ≫ L.map = x := L.pointOver.w

/-- The map to each original pointed affine étale scheme. -/
def component (N : Neighbourhoods Ω x) :
    L.scheme ⟶ ((neighbourhoodDiagram Ω x).obj N).left :=
  (L.cone.π.app N).left

end StrictLocalization

variable {Y : Scheme.{0}} (f : X ⟶ Y)
  (LX : StrictLocalization Ω x) (LY : StrictLocalization Ω (x ≫ f))

/-- A morphism of strict localizations over $f$: for a morphism of schemes $f : X \to Y$, a
geometric point $x$ of $X$ and chosen strict localizations $X_{(x)}$ of $X$ at $x$ and
$Y_{(f(x))}$ of $Y$ at $f \circ x$ (`StrictLocalization`), a morphism $X_{(x)} \to Y_{(f(x))}$
whose composite with $Y_{(f(x))} \to Y$ is the composite of $X_{(x)} \to X$ with $f$, and which
sends the geometric point of $X_{(x)}$ to that of $Y_{(f(x))}$. -/
structure LocalMorphism where
  map : LX.scheme ⟶ LY.scheme
  over : map ≫ LY.map = LX.map ≫ f
  point : LX.point ≫ map = LY.point

/-- The geometric generization is an actual point of the strict local base. -/
structure Generization where
  field : GeometricField
  point : Spec (.of field.carrier) ⟶ LY.scheme

variable (M : LocalMorphism Ω x f LX LY) (t : Generization Ω x f LY)

variable {Ω x f LY} in
/-- The image point of a generization in the strict local base. -/
def Generization.base : LY.scheme :=
  (Scheme.SpecToEquivOfField t.field.carrier LY.scheme t.point).1

variable {Ω x f LY} in
/-- The generization is algebraic: its field is algebraic (equivalently, integral) over the
residue field of its image point. Saito, *The characteristic cycle and the singular support of a constructible
sheaf*, §1.2, tests local acyclicity on a separable closure of that residue field; an
algebraic closure differs from it by a purely inseparable extension, which étale
cohomology does not see (Stacks, Tag 04DY). A transcendental extension does change the
Milnor fibre, so local acyclicity quantifies over algebraic generizations only. -/
def Generization.IsAlgebraic : Prop :=
  (Scheme.SpecToEquivOfField t.field.carrier LY.scheme t.point).2.hom.IsIntegral

/-- Saito's Milnor fibre, as the literal scheme fibre product. -/
abbrev milnorFibre : Scheme.{0} := pullback M.map t.point

abbrev milnorProjection : milnorFibre Ω x f LX LY M t ⟶ LX.scheme :=
  pullback.fst M.map t.point

end MathlibExt.AlgebraicGeometry.EtaleStrictLocalizationModels
