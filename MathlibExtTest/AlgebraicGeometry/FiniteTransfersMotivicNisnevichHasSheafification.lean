/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FiniteTransfersMotivicNisnevichHasSheafification

namespace MathlibExtTest.AlgebraicGeometry.FiniteTransfersMotivicNisnevichHasSheafification

open CategoryTheory CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry.FiniteTransferCycleModels
open MathlibExt.AlgebraicGeometry.NisnevichTransferModels

/-- The Nisnevich topology on smooth rational schemes admits `ℤ`-module sheafification. -/
example : HasSheafify (nisnevichTopology (k := ℚ)) (ModuleCat.{1} ℤ) :=
  motivic_nisnevich_has_sheafification ℚ

/-- Sheafification on smooth rational schemes sends a presheaf to a sheaf. -/
noncomputable example (P : (SmoothScheme ℚ)ᵒᵖ ⥤ ModuleCat.{1} ℤ) :
    Sheaf (nisnevichTopology (k := ℚ)) (ModuleCat.{1} ℤ) :=
  haveI := motivic_nisnevich_has_sheafification ℚ
  (presheafToSheaf _ _).obj P

/-- The inclusion of sheaves into presheaves on smooth rational schemes has a left adjoint. -/
example : HasWeakSheafify (nisnevichTopology (k := ℚ)) (ModuleCat.{1} ℤ) :=
  (motivic_nisnevich_has_sheafification ℚ).isRightAdjoint

end MathlibExtTest.AlgebraicGeometry.FiniteTransfersMotivicNisnevichHasSheafification
