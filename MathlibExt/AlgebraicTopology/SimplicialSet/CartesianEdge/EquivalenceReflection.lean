/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.InverseLift
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.HomotopyCancellation
import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncatedQuasicategory

/-!
# A Cartesian edge over an equivalence is an actual equivalence

The original base inverse triangle lifts through the Cartesian critical
edge. Quasicategory composition produces the other composite; an actual
three-horn cancellation identifies it with the original identity in the
homotopy category. Both inverse equations are then proved, without
assuming an equivalence-reflection certificate.
-/

noncomputable section
universe u

open CategoryTheory
open scoped Simplicial

namespace SSet.CartesianEdge

/-- A p-Cartesian edge with equivalence image is an equivalence in the original total space. -/
theorem isEquivalence_of_map {X B : SSet.{u}} (p : X ⟶ B) [InnerFibration p] [Quasicategory B]
    {x y : X _⦋0⦌} (e : Edge x y) (he : IsPCartesian p (yonedaEquiv.symm e.edge))
    (heB : (e.map p).IsEquivalence) : e.IsEquivalence := by
  let _ : Quasicategory X := quasicategory_of_innerFibration p
  obtain ⟨I⟩ := heB.nonempty_invStruct
  obtain ⟨g, Hge, -⟩ := exists_inverse_triangle p e he I
  have hcomp : Nonempty (Σ h : Edge x x, Edge.CompStruct e g h) :=
    Truncated.Quasicategory₂.fill21 e.toTruncated g.toTruncated
  obtain ⟨⟨h, Heg⟩⟩ := hcomp
  have htriangle : Nonempty (Edge.CompStruct h e e) :=
    Truncated.Quasicategory₂.fill31 Heg.toTruncated Hge.toTruncated
      (Edge.CompStruct.compId e).toTruncated
  obtain ⟨Hhe⟩ := htriangle
  have hh := toHoHom_eq_id_of_compStruct p e he heB h Hhe
  have he_g : e.toHoHom ≫ g.toHoHom = 𝟙 (HomotopyCategory.mk x : hoFunctor.obj X) := by
    rw [Edge.toHoHom_comp Heg, hh]
  have hg_e : g.toHoHom ≫ e.toHoHom = 𝟙 (HomotopyCategory.mk y : hoFunctor.obj X) := by
    rw [Edge.toHoHom_comp Hge, Edge.toHoHom_id]
  change IsIso e.toHoHom
  exact ⟨g.toHoHom, he_g, hg_e⟩

end SSet.CartesianEdge
