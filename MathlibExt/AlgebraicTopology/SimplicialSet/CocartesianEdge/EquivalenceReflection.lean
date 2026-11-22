/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.CocartesianEdge.InverseLift
import MathlibExt.AlgebraicTopology.SimplicialSet.CocartesianEdge.HomotopyCancellation
import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncatedQuasicategory

/-!
# Cocartesian equivalence reflection for the original projection

The specified first inverse triangle lifts through the actual cocartesian
edge. A native inner three-horn and the left cancellation horn prove the
other inverse equation in the original total homotopy category.
-/

noncomputable section
universe u
open CategoryTheory
open scoped Simplicial

namespace SSet.CocartesianEdge

/-- A cocartesian edge over an equivalence is an actual equivalence in the original total space. -/
theorem isEquivalence_of_map {X B : SSet.{u}} (p : X ⟶ B) [InnerFibration p] [Quasicategory B]
    {x y : X _⦋0⦌} (e : Edge x y) (he : IsPCocartesian p (yonedaEquiv.symm e.edge))
    (heB : (e.map p).IsEquivalence) : e.IsEquivalence := by
  let _ : Quasicategory X := quasicategory_of_innerFibration p
  obtain ⟨I⟩ := heB.nonempty_invStruct
  obtain ⟨g, Heg, -⟩ := exists_inverse_triangle p e he I
  have hcomp : Nonempty (Σ h : Edge y y, Edge.CompStruct g e h) :=
    Truncated.Quasicategory₂.fill21 g.toTruncated e.toTruncated
  obtain ⟨⟨h, Hge⟩⟩ := hcomp
  have htriangle : Nonempty (Edge.CompStruct e h e) :=
    Truncated.Quasicategory₂.fill32 Heg.toTruncated Hge.toTruncated
      (Edge.CompStruct.idComp e).toTruncated
  obtain ⟨Heh⟩ := htriangle
  have hh := toHoHom_eq_id_of_compStruct p e he heB h Heh
  have he_g : e.toHoHom ≫ g.toHoHom = 𝟙 (HomotopyCategory.mk x : hoFunctor.obj X) := by
    rw [Edge.toHoHom_comp Heg, Edge.toHoHom_id]
  have hg_e : g.toHoHom ≫ e.toHoHom = 𝟙 (HomotopyCategory.mk y : hoFunctor.obj X) := by
    rw [Edge.toHoHom_comp Hge, hh]
  change IsIso e.toHoHom
  exact ⟨g.toHoHom, he_g, hg_e⟩

end SSet.CocartesianEdge
