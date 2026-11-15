/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import MathlibExt.AlgebraicGeometry.CurveVectorBundles
public import MathlibExt.AlgebraicGeometry.HarderNarasimhanFiltration
public import MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies

@[expose] public noncomputable section

/-!
# Actual stable-bundle families and their moduli property

Stability tests positive-rank saturated subbundles by their actual rational
slopes. Families are actual vector bundles on C times T, with fixed
fiber degree. The moduli property compares their actual universal pullbacks
up to tensoring by a line bundle from the base, retaining the scalar
automorphism ambiguity.

Source: Huybrechts--Lehn, The Geometry of Moduli Spaces of Sheaves,
Chapters 4 and 6, especially the universal-family criterion.
-/

namespace MathlibExt.AlgebraicGeometry.StableBundleModuli

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open _root_.MathlibExt.AlgebraicGeometry.CurveVectorBundles
open _root_.MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies

universe u

/-- Stability with actual saturated-subobject strict slope inequalities. -/
def IsStable {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (E : X.Modules) (r : ℕ) : Prop :=
  0 < r ∧ HarderNarasimhanFiltration.IsSemistable f E r ∧
    ∀ (s : ℕ), 0 < s → s < r →
      ∀ (F : X.Modules) (i : F ⟶ E), Mono i → IsVectorBundle F s →
        IsVectorBundle (cokernel i) (r - s) → slope f F s < slope f E r

/-- Stable degree-d rank-r families, tested on all closed field points. -/
def IsStableFamily {k : Type u} [Field k]
    (C T : Over (Spec (.of k))) (r : ℕ) (d : ℤ)
    (E : (prod C T).left.Modules) : Prop :=
  IsVectorBundle E r ∧
    ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ T,
      let F := (Scheme.Modules.pullback (pointSection C T x).left).obj E
      IsStable C.hom F r ∧ bundleDegree C.hom F r = d

/-- The scalar automorphism ambiguity is tensor by an actual base line bundle. -/
def IsBaseTwist {k : Type u} [Field k] (C T : Over (Spec (.of k)))
    (E F : (prod C T).left.Modules) : Prop :=
  ∃ L : T.left.Modules, IsLineBundle L ∧
    Nonempty (moduleTensor (prod C T).left E
      ((Scheme.Modules.pullback (prod.snd : prod C T ⟶ T).left).obj L) ≅ F)

/-- Proper smooth moduli with an actual universal bundle, modulo base twists. -/
structure StableModuliModel {k : Type u} [Field k]
    (C : Over (Spec (.of k))) (r : ℕ) (d : ℤ) where
  M : Over (Spec (.of k))
  [proper : IsProper M.hom]
  [smoothDimension : SmoothOfRelativeDimension
    (r * r * (genus C.hom - 1) + 1) M.hom]
  [connected : GeometricallyConnected M.hom]
  universalBundle : (prod C M).left.Modules
  stableFamily : IsStableFamily C M r d universalBundle
  universal : ∀ (T : Over (Spec (.of k))),
    LocallyOfFiniteType T.hom → QuasiCompact T.hom →
      ∀ E : (prod C T).left.Modules, IsStableFamily C T r d E →
        ∃! f : T ⟶ M,
          IsBaseTwist C T (familyPullback C M T universalBundle f) E

end MathlibExt.AlgebraicGeometry.StableBundleModuli
