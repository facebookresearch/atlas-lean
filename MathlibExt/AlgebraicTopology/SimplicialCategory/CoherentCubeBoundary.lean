/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentCubeBoxes

/-!
# Actual coherent cube boundary and open-box subcomplex

The boundary is the union of actual scalar coordinate-boundary preimages.
The distinguished upper open box is the actual range of the proved chart
inclusion. Its membership condition uses exactly the original coordinate
labels and full scalar words. No enriched horn-compatibility conclusion
is taken as an input.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.CubeBoundary
open MappingCube CubeBoxes
variable {I : Type u}

/-- The union of all actual scalar coordinate-boundary preimages in the original cube. -/
def boundary (I : Type u) : (cube I).Subcomplex :=
  ⨆ i : I, (∂Δ[1]).preimage (Limits.Pi.π (fun _ : I => (Δ[1] : SSet.{u})) i)

/-- A whole original cube simplex is on the boundary exactly when some original coordinate
word is on the
  interval boundary. -/
theorem mem_boundary_iff {q : SimplexCategoryᵒᵖ} (x : (cube I).obj q) :
    x ∈ (boundary I).obj q ↔
      ∃ i : I, (Limits.Pi.π (fun _ : I => (Δ[1] : SSet.{u})) i).app q x ∈ (∂Δ[1]).obj q := by
  simp only [boundary, Subfunctor.iSup_obj, SSet.Subcomplex.preimage_obj, Set.mem_iUnion,
    Set.mem_preimage]

/-- The actual upper distinguished-coordinate open-box subcomplex of the original cube. -/
def upperBox (j : I) : (cube I).Subcomplex :=
  SSet.Subcomplex.range (boxι j (boundary (Remaining j)))

/-- The actual split distinguished coordinate reads back its same original scalar word. -/
theorem split_self (j : I) (q : SimplexCategoryᵒᵖ) (x : (cube I).obj q) :
    ((splitIso j).hom.app q x).2 =
      (Limits.Pi.π (fun _ : I => (Δ[1] : SSet.{u})) j).app q x :=
  congr($(CartesianMonoidalCategory.lift_snd
    (Limits.Pi.lift (fun i : Remaining j => Limits.Pi.π (fun _ : I => (Δ[1] : SSet.{u})) i.val))
    (Limits.Pi.π (fun _ : I => (Δ[1] : SSet.{u})) j)).app q x)

/-- Every other split original coordinate reads back its same original scalar word. -/
theorem split_other (j : I) (i : Remaining j) (q : SimplexCategoryᵒᵖ) (x : (cube I).obj q) :
    (Limits.Pi.π (fun _ : Remaining j => (Δ[1] : SSet.{u})) i).app q (((splitIso
      j).hom.app q x).1) =
      (Limits.Pi.π (fun _ : I => (Δ[1] : SSet.{u})) i.val).app q x := by
  have h := (congrArg (fun f => f ≫ Limits.Pi.π (fun _ : Remaining j => (Δ[1] : SSet.{u})) i)
    (CartesianMonoidalCategory.lift_fst
      (Limits.Pi.lift (fun i : Remaining j => Limits.Pi.π (fun _ : I => (Δ[1] : SSet.{u})) i.val))
      (Limits.Pi.π (fun _ : I => (Δ[1] : SSet.{u})) j))).trans
        (Limits.Pi.lift_comp_π _ i)
  exact congr($(h).app q x)

/-- The actual assembled distinguished coordinate is the same supplied interval word. -/
theorem assemble_self (j : I) (q : SimplexCategoryᵒᵖ) (x : (cube (Remaining j) ⊗ Δ[1]).obj q) :
    (Limits.Pi.π (fun _ : I => (Δ[1] : SSet.{u})) j).app q ((splitIso j).inv.app q x) = x.2 :=
  congr($(assembleHom_self j).app q x)

/-- The actual assembled other coordinate is the same original remaining-coordinate word. -/
theorem assemble_other (j : I) (i : Remaining j) (q : SimplexCategoryᵒᵖ)
    (x : (cube (Remaining j) ⊗ Δ[1]).obj q) :
    (Limits.Pi.π (fun _ : I => (Δ[1] : SSet.{u})) i.val).app q ((splitIso j).inv.app q x) =
      (Limits.Pi.π (fun _ : Remaining j => (Δ[1] : SSet.{u})) i).app q x.1 :=
  congr($(assembleHom_other j i).app q x)

/-- Actual whole open-box membership is exactly the retained top coordinate or another
original boundary coordinate. -/
theorem mem_upperBox_iff (j : I) {q : SimplexCategoryᵒᵖ} (x : (cube I).obj q) :
    x ∈ (upperBox j).obj q ↔
      (Limits.Pi.π (fun _ : I => (Δ[1] : SSet.{u})) j).app q x ∈ (Λ[1, (1 : Fin 2)]).obj q ∨
        ∃ i : Remaining j,
          (Limits.Pi.π (fun _ : I => (Δ[1] : SSet.{u})) i.val).app q x ∈ (∂Δ[1]).obj q := by
  change (∃ y : (boxDomain j (boundary (Remaining j))).obj q,
    (boxι j (boundary (Remaining j))).app q y = x) ↔ _
  constructor
  · rintro ⟨y, rfl⟩
    have hy := (SSet.Subcomplex.mem_unionProd_iff (boundary (Remaining j)) Λ[1,
      (1 : Fin 2)] y.val).mp y.property
    rcases hy with hy | hy
    · left
      exact (congrArg (fun z => z ∈ (Λ[1, (1 : Fin 2)]).obj q) (assemble_self j q y.val)).mpr hy
    · right
      obtain ⟨i, hi⟩ := (mem_boundary_iff y.val.1).mp hy
      exact ⟨i, (congrArg (fun z => z ∈ (∂Δ[1]).obj q) (assemble_other j i q y.val)).mpr hi⟩
  · intro hx
    have hy : (splitIso j).hom.app q x ∈ (OpenBox.upper (boundary (Remaining j))).obj q := by
      apply (SSet.Subcomplex.mem_unionProd_iff (boundary (Remaining j)) Λ[1, (1 : Fin 2)] _).mpr
      rcases hx with hx | ⟨i, hi⟩
      · left
        exact (congrArg (fun z => z ∈ (Λ[1, (1 : Fin 2)]).obj q) (split_self j q x)).mpr hx
      · right
        exact (mem_boundary_iff _).mpr ⟨i,
          (congrArg (fun z => z ∈ (∂Δ[1]).obj q) (split_other j i q x)).mpr hi⟩
    refine ⟨⟨(splitIso j).hom.app q x, hy⟩, ?_⟩
    exact congr($((splitIso j).hom_inv_id).app q x)

end CategoryTheory.CoherentRealization.CubeBoundary
