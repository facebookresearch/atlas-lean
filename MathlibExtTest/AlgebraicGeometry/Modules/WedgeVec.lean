/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Modules.WedgeVec

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.CurveVectorBundles

universe u v

/-- Consumer with the original binders. -/
example {X : Scheme.{u}} {n : ℕ} (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (h₁ : IsVectorBundle S.X₁ n) (h₃ : IsLineBundle S.X₃) :
    Epi (((Scheme.Modules.exteriorPower X n).map S.f ▷ S.X₂) ≫
      Scheme.Modules.wedgeVec n S.X₂) :=
  Scheme.Modules.epi_whiskerRight_wedgeVec_of_shortExact S hS h₁ h₃

/-- The statement is universe polymorphic. -/
example {X : Scheme.{v + 1}} (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (h₁ : IsVectorBundle S.X₁ 2) (h₃ : IsLineBundle S.X₃) :
    Epi (((Scheme.Modules.exteriorPower X 2).map S.f ▷ S.X₂) ≫
      Scheme.Modules.wedgeVec 2 S.X₂) :=
  Scheme.Modules.epi_whiskerRight_wedgeVec_of_shortExact S hS h₁ h₃

/-- The invertibility hypothesis is satisfiable: the structure sheaf is invertible. -/
example (X : Scheme.{u}) : IsLineBundle (SheafOfModules.unit X.ringCatSheaf) :=
  isLineBundle_structureModule X

/-- `exteriorPower X n` is the sheafified sectionwise exterior power. -/
example {X : Scheme.{u}} (n : ℕ) (M : X.Modules) :
    (Scheme.Modules.exteriorPower X n).obj M =
      (Scheme.Modules.sheafify X).obj ((Scheme.Modules.presheafExteriorPower X n).obj M.val) :=
  Scheme.Modules.exteriorPower_obj n M
