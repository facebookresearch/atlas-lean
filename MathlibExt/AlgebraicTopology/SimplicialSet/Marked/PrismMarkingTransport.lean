/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MaximalPrismCriterion
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ParameterCore

/-!
# Intrinsic markings along the original equivalence prisms

The two original product triangles compare the horizontal edges at the
parameter endpoints. Pointwise equivalences are both Cartesian and
cocartesian. Cartesian markings transport from the target parameter
endpoint to the source endpoint; cocartesian markings transport in the
opposite direction. Applying this to the inverse edge of the native Kan
core gives invariance in both directions. Every original mixed edge and
whole two-simplex is retained.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The original zero-prism section detects precisely the supplied marked source edges. -/
theorem markedMappingVertices_section_iff {T : SSet.{u}} (X : Marked.{u}) (Y : Marked.{u})
    (F : T ⊗ X.toSSet ⟶ Y.toSSet) (v : T _⦋0⦌) :
    ((yonedaEquiv.symm v ▷ X.toSSet) ≫ F) ∈ markedMappingVertices X Y ↔
      ∀ e : X.toSSet _⦋1⦌, e ∈ X.marking →
        F.app (op ⦋1⦌) (T.σ (0 : Fin 1) v, e) ∈ Y.marking := by
  let s : X.toSSet ⟶ (Δ[0] : SSet.{u}) ⊗ X.toSSet := (zeroParameterUnitIso .minimal X).inv.hom
  have hs : s ≫ (yonedaEquiv.symm v ▷ X.toSSet) =
      CartesianMonoidalCategory.lift (SSet.const v) (𝟙 X.toSSet) := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · rw [yonedaEquiv_symm_zero]
      rfl
    · rfl
  have hv (e : X.toSSet _⦋1⦌) :
      ((s ≫ ((yonedaEquiv.symm v ▷ X.toSSet) ≫ F)).app (op ⦋1⦌)) e =
        F.app (op ⦋1⦌) (T.σ (0 : Fin 1) v, e) := by
    rw [← Category.assoc, hs]
    change F.app (op ⦋1⦌) ((SSet.const v).app (op ⦋1⦌) e, e) = _
    exact congrArg (fun z => F.app (op ⦋1⦌) (z, e))
      (const_app_one (X := X) (Y := min T) v e)
  change (∀ e, e ∈ X.marking → (s ≫ ((yonedaEquiv.symm v ▷ X.toSSet) ≫ F)).app (op ⦋1⦌) e ∈ Y.marking) ↔ _
  simp only [hv]

/-- The exact mixed triangles transport a target horizontal Cartesian edge to the source horizontal edge. -/
theorem cartesian_horizontal_source_of_target {T X E B : SSet.{u}}
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B] (F : T ⊗ X ⟶ E)
    {t₀ t₁ : T _⦋0⦌} (a : Edge t₀ t₁) {x₀ x₁ : X _⦋0⦌} (b : Edge x₀ x₁)
    (hv₀ : ((a.tensor (Edge.id x₀)).map F).IsEquivalence)
    (hv₁ : ((a.tensor (Edge.id x₁)).map F).IsEquivalence)
    (hb : CartesianEdge.IsPCartesian p
      (yonedaEquiv.symm (((Edge.id t₁).tensor b).map F).edge)) :
    CartesianEdge.IsPCartesian p (yonedaEquiv.symm (((Edge.id t₀).tensor b).map F).edge) := by
  let v₀ := (a.tensor (Edge.id x₀)).map F
  let v₁ := (a.tensor (Edge.id x₁)).map F
  let b₀ := ((Edge.id t₀).tensor b).map F
  let b₁ := ((Edge.id t₁).tensor b).map F
  let d := (a.tensor b).map F
  have h₀ : CartesianEdge.IsPCartesian p (yonedaEquiv.symm v₀.edge) :=
    CartesianEdge.isPCartesian_of_isEquivalence p _
      (hv₀.of_edge_eq (Equiv.apply_symm_apply yonedaEquiv v₀.edge).symm)
  have h₁ : CartesianEdge.IsPCartesian p (yonedaEquiv.symm v₁.edge) :=
    CartesianEdge.isPCartesian_of_isEquivalence p _
      (hv₁.of_edge_eq (Equiv.apply_symm_apply yonedaEquiv v₁.edge).symm)
  have H : Edge.CompStruct v₀ b₁ d :=
    ((Edge.CompStruct.compId a).tensor (Edge.CompStruct.idComp b)).map F
  have H' : Edge.CompStruct b₀ v₁ d :=
    ((Edge.CompStruct.idComp a).tensor (Edge.CompStruct.compId b)).map F
  exact (CartesianEdge.isPCartesian_iff_of_compStruct p H' h₁).mpr
    (CartesianEdge.isPCartesian_of_compStruct p H h₀ hb)

/-- The same two original mixed triangles transport a source horizontal cocartesian edge to the target edge. -/
theorem cocartesian_horizontal_target_of_source {T X E B : SSet.{u}}
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B] (F : T ⊗ X ⟶ E)
    {t₀ t₁ : T _⦋0⦌} (a : Edge t₀ t₁) {x₀ x₁ : X _⦋0⦌} (b : Edge x₀ x₁)
    (hv₀ : ((a.tensor (Edge.id x₀)).map F).IsEquivalence)
    (hv₁ : ((a.tensor (Edge.id x₁)).map F).IsEquivalence)
    (hb : CocartesianEdge.IsPCocartesian p
      (yonedaEquiv.symm (((Edge.id t₀).tensor b).map F).edge)) :
    CocartesianEdge.IsPCocartesian p (yonedaEquiv.symm (((Edge.id t₁).tensor b).map F).edge) := by
  let v₀ := (a.tensor (Edge.id x₀)).map F
  let v₁ := (a.tensor (Edge.id x₁)).map F
  let b₀ := ((Edge.id t₀).tensor b).map F
  let b₁ := ((Edge.id t₁).tensor b).map F
  let d := (a.tensor b).map F
  have h₀ : CocartesianEdge.IsPCocartesian p (yonedaEquiv.symm v₀.edge) :=
    CocartesianEdge.isPCocartesian_of_isEquivalence p _
      (hv₀.of_edge_eq (Equiv.apply_symm_apply yonedaEquiv v₀.edge).symm)
  have h₁ : CocartesianEdge.IsPCocartesian p (yonedaEquiv.symm v₁.edge) :=
    CocartesianEdge.isPCocartesian_of_isEquivalence p _
      (hv₁.of_edge_eq (Equiv.apply_symm_apply yonedaEquiv v₁.edge).symm)
  have H : Edge.CompStruct v₀ b₁ d :=
    ((Edge.CompStruct.compId a).tensor (Edge.CompStruct.idComp b)).map F
  have H' : Edge.CompStruct b₀ v₁ d :=
    ((Edge.CompStruct.idComp a).tensor (Edge.CompStruct.compId b)).map F
  exact (CocartesianEdge.isPCocartesian_iff_of_compStruct p H h₀).mpr
    (CocartesianEdge.isPCocartesian_of_compStruct p H' hb h₁)

end SSet.Marked
