/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import MathlibExt.AlgebraicGeometry.StableBundleModuli

@[expose] public noncomputable section

/-!
# A global universal stable-bundle family without a properness assumption

The representing scheme is finite type and separated. Its actual global
bundle must represent every finite-type stable family, uniquely at the
level of classifying maps and up to tensoring by an actual line from
the base. Properness is absent, so failure of this property detects the
universal-bundle obstruction on the stable open.

Sources: Newstead, *A non-existence theorem for families of stable
bundles*; Ramanan, *The moduli spaces of vector bundles over an algebraic
curve*; Biswas--Brambila-Paz--Newstead, *Stability of projective
Poincaré and Picard bundles*, Introduction and §2.
-/

namespace MathlibExt.AlgebraicGeometry.UniversalBundleObstruction

open CategoryTheory
open _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies
open _root_.MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open _root_.MathlibExt.AlgebraicGeometry.StableBundleModuli

universe u

/-- A global universal family of stable bundles of rank $r > 0$ and degree $d$ on a smooth proper
integral curve $C$ over an algebraically closed field $k$: a separated $k$-scheme $M$ with a bundle
on $C \times M$ that is a family of such stable bundles (so $M$ is of finite type over $k$), such
that for every family $E$ of such stable bundles over a $k$-scheme $T$ of finite type there is a
unique map $f : T \to M$ for which the pullback of the universal bundle along $f$, tensored with the
pullback of some line bundle on $T$, is isomorphic to $E$. -/
structure GlobalUniversalStableFamily {k : Type u} [Field k] [IsAlgClosed k]
    (C : Over (Spec (.of k))) [IsProperCurve C.hom] [SmoothOfRelativeDimension 1 C.hom]
    [IsIntegral C.left] (r : ℕ) (hr : 0 < r) (d : ℤ) where
  /-- The parameter scheme. -/
  M : Over (Spec (.of k))
  [separated : IsSeparated M.hom]
  /-- The universal bundle on `C × M`. -/
  universalBundle : (CategoryTheory.Limits.prod C M).left.Modules
  stableFamily : IsStableFamily C M r hr d universalBundle
  universal : ∀ (T : Over (Spec (.of k))) (E : (CategoryTheory.Limits.prod C T).left.Modules),
    IsStableFamily C T r hr d E →
      ∃! f : T ⟶ M, IsBaseTwist C T (familyPullback C M T universalBundle f) E

attribute [instance] GlobalUniversalStableFamily.separated

namespace GlobalUniversalStableFamily

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Over (Spec (.of k))} [IsProperCurve C.hom]
  [SmoothOfRelativeDimension 1 C.hom] [IsIntegral C.left] {r : ℕ} {hr : 0 < r} {d : ℤ}

/-- The parameter scheme is of finite type, as a stable family is. -/
instance (G : GlobalUniversalStableFamily C r hr d) : LocallyOfFiniteType G.M.hom :=
  G.stableFamily.1

/-- The parameter scheme is quasi-compact, as a stable family is. -/
instance (G : GlobalUniversalStableFamily C r hr d) : QuasiCompact G.M.hom :=
  G.stableFamily.2.1

end GlobalUniversalStableFamily

end MathlibExt.AlgebraicGeometry.UniversalBundleObstruction
