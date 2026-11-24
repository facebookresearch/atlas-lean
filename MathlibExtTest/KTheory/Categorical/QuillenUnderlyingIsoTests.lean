/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

import Mathlib.Algebra.Category.ModuleCat.Biproducts
import MathlibExt.CategoryTheory.ExactCategory.Abelian
import MathlibExt.KTheory.Exact.Quillen.UnderlyingIso

/-!
# Quillen underlying-iso consumer tests

Consumer-style checks for the public underlying-isomorphism lift over `ModuleCat ℚ`:
bundled type/orientation of `QuillenQ.underlyingIso`, forward and inverse
representative formulas, and reflexivity. No private spans are named; no
implementation proofs are reproduced. Nothing is claimed about zero objects,
nerve edges, realization paths, or pointed coherence.
-/

open CategoryTheory
open CategoryTheory.Limits

universe u
universe v₁ u₁ v₂ u₂

/-- Underlying iso has the expected bundled forward type over `ModuleCat ℚ`. -/
noncomputable example (X Y : ModuleCat ℚ) (e : X ≅ Y) :
    (⟨X⟩ : AlgebraicKTheory.QuillenQ (ModuleCat ℚ)) ≅ ⟨Y⟩ :=
  AlgebraicKTheory.QuillenQ.underlyingIso e

/-- Forward representative exposes apex `X` with legs `𝟙 X` and `e.hom`. -/
example (X Y : ModuleCat ℚ) (e : X ≅ Y) :
    (AlgebraicKTheory.QuillenQ.underlyingIso e).hom =
      AlgebraicKTheory.QuillenQ.mkHom
        { apex := X, l := 𝟙 X, r := e.hom,
          wl := CategoryTheory.ExactCategory.IsAdmissibleEpi.id X,
          wr := CategoryTheory.ExactCategory.IsAdmissibleMono.of_isIso e.hom } :=
  AlgebraicKTheory.QuillenQ.underlyingIso_hom e

/-- Inverse representative exposes apex `X` with legs `e.hom` and `𝟙 X`. -/
example (X Y : ModuleCat ℚ) (e : X ≅ Y) :
    (AlgebraicKTheory.QuillenQ.underlyingIso e).inv =
      AlgebraicKTheory.QuillenQ.mkHom
        { apex := X, l := e.hom, r := 𝟙 X,
          wl := CategoryTheory.ExactCategory.IsAdmissibleEpi.of_isIso e.hom,
          wr := CategoryTheory.ExactCategory.IsAdmissibleMono.id X } :=
  AlgebraicKTheory.QuillenQ.underlyingIso_inv e

/-- Reflexivity lift is the identity isomorphism. -/
example (X : ModuleCat ℚ) :
    AlgebraicKTheory.QuillenQ.underlyingIso (Iso.refl X) = Iso.refl _ :=
  AlgebraicKTheory.QuillenQ.underlyingIso_refl X

/-- Composition lift preserves transitivity. -/
example (X Y Z : ModuleCat ℚ) (e : X ≅ Y) (f : Y ≅ Z) :
    AlgebraicKTheory.QuillenQ.underlyingIso (e.trans f) =
      (AlgebraicKTheory.QuillenQ.underlyingIso e).trans
        (AlgebraicKTheory.QuillenQ.underlyingIso f) :=
  AlgebraicKTheory.QuillenQ.underlyingIso_trans e f

/-- Exact-functor transport commutes with the lift. -/
example (F : ModuleCat.{u} ℚ ⥤ ModuleCat.{u} ℚ) [F.Additive] [F.IsExact]
    {X Y : ModuleCat.{u} ℚ} (e : X ≅ Y) :
    (AlgebraicKTheory.QuillenQ.map F).mapIso
      (AlgebraicKTheory.QuillenQ.underlyingIso e) =
      AlgebraicKTheory.QuillenQ.underlyingIso (F.mapIso e) :=
  AlgebraicKTheory.QuillenQ.underlyingIso_map F e

/-- Cross-universe exact-functor transport commutes with the lift. -/
example {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [CategoryTheory.ExactCategory C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasZeroObject D]
    [HasBinaryBiproducts D] [CategoryTheory.ExactCategory D]
    (F : C ⥤ D) [F.Additive] [F.IsExact] {X Y : C} (e : X ≅ Y) :
    (AlgebraicKTheory.QuillenQ.map F).mapIso
      (AlgebraicKTheory.QuillenQ.underlyingIso e) =
      AlgebraicKTheory.QuillenQ.underlyingIso (F.mapIso e) :=
  AlgebraicKTheory.QuillenQ.underlyingIso_map F e
