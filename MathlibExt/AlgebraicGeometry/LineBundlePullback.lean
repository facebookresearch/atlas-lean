/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

/-!
# Pullbacks of invertible sheaves

The pullback of the structure sheaf along a morphism of schemes is the structure
sheaf, through the canonical comparison map, and so the pullback of an invertible
sheaf is invertible: a local trivialization on an open `U` pulls back to one on its
preimage.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

open CategoryTheory _root_.AlgebraicGeometry

universe u

/-- The canonical isomorphism from the pullback of the structure sheaf to the structure
sheaf. -/
def pullbackStructureModuleIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (structureModule Y) ≅ structureModule X := by
  have : (TopologicalSpace.Opens.map f.base).Final := by infer_instance
  have : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint := by
    change (Scheme.Modules.pushforward f).IsRightAdjoint
    infer_instance
  let m : (Scheme.Modules.pullback f).obj (structureModule Y) ⟶ structureModule X :=
    SheafOfModules.pullbackObjUnitToUnit (F := TopologicalSpace.Opens.map f.base)
      f.toRingCatSheafHom
  have : IsIso m := by
    dsimp [m]
    exact SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal
      (F := TopologicalSpace.Opens.map f.base) f.toRingCatSheafHom
  exact asIso m

/-- The pullback of an invertible sheaf is invertible. -/
theorem IsLineBundle.pullback {X Y : Scheme.{u}} (f : X ⟶ Y) {L : Y.Modules}
    (hL : IsLineBundle L) : IsLineBundle ((Scheme.Modules.pullback f).obj L) := by
  intro x
  obtain ⟨U, hU, ⟨e⟩⟩ := hL (f x)
  exact ⟨f ⁻¹ᵁ U, hU, ⟨((Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).app L) ≪≫
    ((Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app L) ≪≫
    ((Scheme.Modules.pullbackComp (f ∣_ U) U.ι).symm.app L) ≪≫
    (Scheme.Modules.pullback (f ∣_ U)).mapIso e ≪≫ pullbackStructureModuleIso (f ∣_ U)⟩⟩

end MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
