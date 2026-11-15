/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Adapted from AxiomMath/Stacks at
c496df0d9beea9deaeabcea8492605f9a0a2313b, licensed under Apache 2.0:
StacksFrontier/AlgebraicGeometry/Etale/NormalCrossings/Defs.lean,
StacksFrontier/AlgebraicGeometry/Morphisms/EtaleBasics/NormalCrossings/Components.lean.
These source files have no individual author or copyright notice.
Modification notice: use actual minimal generators of the maximal stalk
ideal, actual regular local rings, and the canonical reduced global
components with their smoothness over the coefficient field.
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.RegularLocalRing.Defs

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# Actual strict normal crossings boundary models

The stalk equation is a product of a nonempty initial segment of a
minimal regular parameter system in the actual ambient local ring. The
actual global irreducible components carry their canonical reduced closed
scheme structures and must be smooth. This rules out self-intersecting
global components. The reduced pullback is the actual radical boundary
of the scheme pullback, not a new chosen closed set.

References: Stacks Project, Tags 0BI9 and 0BIA; ILO, Exposé X, Theorem 2.1.
-/

namespace MathlibExt.AlgebraicGeometry.NormalCrossingsModels

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open _root_.CategoryTheory _root_.TopologicalSpace

universe u

/-- A genuine global irreducible component with its canonical reduced
closed subscheme structure in the ambient scheme. -/
def componentIdeal {X : Scheme.{u}} (D : X.IdealSheafData)
    (C : irreducibleComponents D.subscheme) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨closure (D.subschemeι '' (C : Set D.subscheme)), isClosed_closure⟩

/-- The precise strict local equation in the actual stalk, including
minimal parameter cardinality and the effective Cartier condition. -/
def StrictStalkCrossings {X : Scheme.{u}} (D : X.IdealSheafData) : Prop :=
  ∀ y : D.subscheme,
    let x : X := D.subschemeι y
    let R := X.presheaf.stalk x
    IsRegularLocalRing R ∧
      ∃ (rs : List R) (r : ℕ),
        Ideal.span {a : R | a ∈ rs} = IsLocalRing.maximalIdeal R ∧
        ringKrullDim R = (rs.length : WithBot ℕ∞) ∧
        1 ≤ r ∧ r ≤ rs.length ∧
        (∀ a : R, (rs.take r).prod * a = 0 → a = 0) ∧
        RingHom.ker (D.subschemeι.stalkMap y).hom = Ideal.span {(rs.take r).prod}

/-- Strict normal crossings over a field, using actual reduced global
components as well as the strict local parameter equations. -/
def IsStrictNormalCrossings {k : Type u} [Field k]
    (X : Over (Spec (.of k))) (D : X.left.IdealSheafData) : Prop :=
  IsReduced D.subscheme ∧ StrictStalkCrossings D ∧
    ∀ C : irreducibleComponents D.subscheme,
      Smooth ((componentIdeal D C).subschemeι ≫ X.hom)

/-- The actual reduced boundary of the scheme-theoretic pullback. -/
def reducedPullbackBoundary {X Y : Scheme.{u}} (f : Y ⟶ X) (D : X.IdealSheafData) :
    Y.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (D.comap f).support

/-- Its underlying closed support is precisely the geometric inverse image. -/
theorem reducedPullbackBoundary_support {X Y : Scheme.{u}} (f : Y ⟶ X)
    (D : X.IdealSheafData) :
    (reducedPullbackBoundary f D).support = D.support.preimage f.continuous := by
  change (D.comap f).support = D.support.preimage f.continuous
  exact Scheme.IdealSheafData.support_comap D f

end MathlibExt.AlgebraicGeometry.NormalCrossingsModels
