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
open _root_.MathlibExt.AlgebraicGeometry.StableBundleModuli

universe u

/-- A genuine global universal stable family on a finite-type parameter
scheme. No universal object or conclusion is supplied as an assumption
to the nonexistence theorem. -/
structure GlobalUniversalStableFamily {k : Type u} [Field k]
    (C : Over (Spec (.of k))) (r : ℕ) (d : ℤ) where
  M : Over (Spec (.of k))
  [finiteType : LocallyOfFiniteType M.hom]
  [quasiCompact : QuasiCompact M.hom]
  [separated : IsSeparated M.hom]
  universalBundle : (CategoryTheory.Limits.prod C M).left.Modules
  stableFamily : IsStableFamily C M r d universalBundle
  universal : ∀ (T : Over (Spec (.of k))),
    LocallyOfFiniteType T.hom → QuasiCompact T.hom →
      ∀ E : (CategoryTheory.Limits.prod C T).left.Modules,
        IsStableFamily C T r d E →
          ∃! f : T ⟶ M,
            IsBaseTwist C T (familyPullback C M T universalBundle f) E

end MathlibExt.AlgebraicGeometry.UniversalBundleObstruction

