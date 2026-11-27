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
public import MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies

@[expose] public noncomputable section

/-!
# Stable-bundle families on a curve and their moduli property

Let `C` be a smooth proper integral curve over an algebraically closed field
`k`. A vector bundle of positive rank on `C` is stable when every saturated
subbundle of smaller positive rank has strictly smaller slope. A family over a
parameter scheme `T` is a vector bundle on `C × T` whose restriction to the
fibre `C × {t}` over every rational point `t` of `T` is stable of the given
degree, for `T` of finite type over the algebraically closed field `k`: the
rational points are then exactly the closed points, and stability is open in
families, so this tests every fibre. The moduli property compares universal
pullbacks up to tensoring by a line bundle from the base, the scalar
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

/-- Stability of a vector bundle `E` of positive rank `r` on a smooth integral proper
curve: every saturated subbundle of rank `0 < s < r`, an actual monomorphism from a
vector bundle of rank `s` whose cokernel is a vector bundle of rank `r - s`, has
strictly smaller slope. -/
def IsStable {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProperCurve f] [SmoothOfRelativeDimension 1 f] [IsIntegral X]
    (E : X.Modules) (r : ℕ) (hE : IsVectorBundle E r) (hr : 0 < r) : Prop :=
  ∀ (s : ℕ) (hs : 0 < s), s < r →
    ∀ (F : X.Modules) (i : F ⟶ E), Mono i → ∀ hF : IsVectorBundle F s,
      IsVectorBundle (cokernel i) (r - s) → slope f F s hF hs < slope f E r hE hr

/-- A family of stable bundles of rank `r` and degree `d` on `C`, parametrized by a
scheme `T` of finite type over `k`: a vector bundle on `C × T` whose restriction to the
fibre over every rational point of `T` is a stable vector bundle of rank `r` and degree
`d`. The rational points of `T` are its closed points, since `k` is algebraically
closed and `T` of finite type. -/
def IsStableFamily {k : Type u} [Field k] [IsAlgClosed k]
    (C T : Over (Spec (.of k))) [IsProperCurve C.hom] [SmoothOfRelativeDimension 1 C.hom]
    [IsIntegral C.left] (r : ℕ) (hr : 0 < r) (d : ℤ)
    (E : (prod C T).left.Modules) : Prop :=
  LocallyOfFiniteType T.hom ∧ QuasiCompact T.hom ∧ IsVectorBundle E r ∧
    ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ T,
      let F := (Scheme.Modules.pullback (pointSection C T x).left).obj E
      ∃ hF : IsVectorBundle F r, IsStable C.hom F r hF hr ∧ bundleDegree C.hom F r hF = d

/-- The scalar automorphism ambiguity is tensor by an actual base line bundle. -/
def IsBaseTwist {k : Type u} [Field k] (C T : Over (Spec (.of k)))
    (E F : (prod C T).left.Modules) : Prop :=
  ∃ L : T.left.Modules, IsLineBundle L ∧
    Nonempty (moduleTensor (prod C T).left E
      ((Scheme.Modules.pullback (prod.snd : prod C T ⟶ T).left).obj L) ≅ F)

/-- A proper, smooth, geometrically connected moduli space of stable bundles of rank
`r` and degree `d` on `C`, of dimension `r²(g - 1) + 1` (computed in `ℤ`), with a
universal bundle that represents stable families over parameter schemes of finite
type up to base twists. -/
structure StableModuliModel {k : Type u} [Field k] [IsAlgClosed k]
    (C : Over (Spec (.of k))) [IsProperCurve C.hom] [SmoothOfRelativeDimension 1 C.hom]
    [IsIntegral C.left] (r : ℕ) (hr : 0 < r) (d : ℤ) where
  /-- The moduli space. -/
  M : Over (Spec (.of k))
  [proper : IsProper M.hom]
  /-- The dimension of the moduli space. -/
  dimension : ℕ
  dimension_eq : (dimension : ℤ) = (r : ℤ) * r * ((genus C.hom : ℤ) - 1) + 1
  [smoothDimension : SmoothOfRelativeDimension dimension M.hom]
  [connected : GeometricallyConnected M.hom]
  /-- The universal bundle on `C × M`. -/
  universalBundle : (prod C M).left.Modules
  stableFamily : IsStableFamily C M r hr d universalBundle
  universal : ∀ (T : Over (Spec (.of k))) (E : (prod C T).left.Modules),
    IsStableFamily C T r hr d E →
      ∃! f : T ⟶ M, IsBaseTwist C T (familyPullback C M T universalBundle f) E

end MathlibExt.AlgebraicGeometry.StableBundleModuli
