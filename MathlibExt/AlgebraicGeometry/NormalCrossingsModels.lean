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

/-!
# Actual strict normal crossings boundary models

The ambient scheme is locally Noetherian and, at every boundary point, the
stalk equation is a product of a nonempty initial segment of a minimal
regular parameter system in the actual ambient local ring; on a locally
Noetherian scheme this makes the boundary an effective Cartier divisor
(Stacks, Tag 0BI9). Relative to a field, every nonempty finite
scheme-theoretic intersection of the global irreducible components, each
with its canonical reduced closed scheme structure, must be smooth over the
field, as in ILO, Exposé X, after Theorem 2.1. Over an imperfect field this is
stronger than smoothness of the components, and it rules out
self-intersecting global components. The reduced pullback is the actual
radical boundary of the scheme pullback, not a new chosen closed set.

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

/-- The scheme-theoretic intersection of a finite set of global components of the boundary:
the sum of their reduced ideal sheaves. -/
def componentIntersectionIdeal {X : Scheme.{u}} (D : X.IdealSheafData)
    (S : Finset (irreducibleComponents D.subscheme)) : X.IdealSheafData :=
  ⨆ C ∈ S, componentIdeal D C

@[simp]
theorem componentIntersectionIdeal_singleton {X : Scheme.{u}} (D : X.IdealSheafData)
    (C : irreducibleComponents D.subscheme) :
    componentIntersectionIdeal D {C} = componentIdeal D C := by
  simp [componentIntersectionIdeal]

/-- Strict normal crossings relative to a field: the ambient scheme is locally Noetherian, the
boundary is reduced with strict local parameter equations (Stacks, Tag 0BI9), and every nonempty
finite scheme-theoretic intersection of its actual reduced global components is smooth over the
field (ILO, Exposé X, after Theorem 2.1). -/
def IsStrictNormalCrossings {k : Type u} [Field k]
    (X : Over (Spec (.of k))) (D : X.left.IdealSheafData) : Prop :=
  IsLocallyNoetherian X.left ∧ IsReduced D.subscheme ∧ StrictStalkCrossings D ∧
    ∀ S : Finset (irreducibleComponents D.subscheme), S.Nonempty →
      Smooth ((componentIntersectionIdeal D S).subschemeι ≫ X.hom)

/-- Each global component of a strict normal crossings boundary is smooth over the field. -/
theorem IsStrictNormalCrossings.smooth_componentIdeal {k : Type u} [Field k]
    {X : Over (Spec (.of k))} {D : X.left.IdealSheafData} (h : IsStrictNormalCrossings X D)
    (C : irreducibleComponents D.subscheme) :
    Smooth ((componentIdeal D C).subschemeι ≫ X.hom) := by
  have hC := h.2.2.2 {C} (Finset.singleton_nonempty C)
  rwa [componentIntersectionIdeal_singleton] at hC

/-- On a locally Noetherian scheme, a boundary with empty support, such as the unit ideal, has
strict normal crossings: its subscheme is empty, so the stalk and component conditions are
vacuous. -/
theorem isStrictNormalCrossings_of_support_eq_bot {k : Type u} [Field k]
    {X : Over (Spec (.of k))} [IsLocallyNoetherian X.left] {D : X.left.IdealSheafData}
    (h : D.support = ⊥) : IsStrictNormalCrossings X D := by
  have : IsEmpty D.subscheme := ⟨fun y => by
    have hy : D.subschemeι y ∈ (D.support : Set X.left) := by
      rw [← D.range_subschemeι]
      exact ⟨y, rfl⟩
    simp [h] at hy⟩
  have : ∀ y : D.subscheme, _root_.IsReduced (D.subscheme.presheaf.stalk y) := isEmptyElim
  exact ⟨inferInstance, isReduced_of_isReduced_stalk _, isEmptyElim,
    fun S hS => isEmptyElim hS.choose.2.1.nonempty.some⟩

/-- The actual reduced boundary of the scheme-theoretic pullback. -/
def reducedPullbackBoundary {X Y : Scheme.{u}} (f : Y ⟶ X) (D : X.IdealSheafData) :
    Y.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (D.comap f).support

/-- It is the radical of the scheme-theoretic pullback. -/
theorem reducedPullbackBoundary_eq_radical {X Y : Scheme.{u}} (f : Y ⟶ X)
    (D : X.IdealSheafData) : reducedPullbackBoundary f D = (D.comap f).radical :=
  Scheme.IdealSheafData.vanishingIdeal_support

/-- Its underlying closed support is precisely the geometric inverse image. -/
theorem reducedPullbackBoundary_support {X Y : Scheme.{u}} (f : Y ⟶ X)
    (D : X.IdealSheafData) :
    (reducedPullbackBoundary f D).support = D.support.preimage f.continuous := by
  change (D.comap f).support = D.support.preimage f.continuous
  exact Scheme.IdealSheafData.support_comap D f

end MathlibExt.AlgebraicGeometry.NormalCrossingsModels
