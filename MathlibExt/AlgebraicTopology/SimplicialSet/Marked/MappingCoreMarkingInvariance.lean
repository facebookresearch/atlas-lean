/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.PrismMarkingTransport
import MathlibExt.AlgebraicTopology.SimplicialSet.FullSubcomplexKan

/-!
# Original intrinsic marked-map vertices are invariant in the native core

The native core edge is a whole equivalence prism. The exact mixed
triangles transport the intrinsic edge condition at its endpoints. The
inverse of the same edge in the actual Kan core gives the other direction.
Thus the supplied source marking selects whole components of this core.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked

private theorem standard_endpoint {ε : Fin 2} :
    yonedaEquiv.symm ((Δ[1] : SSet.{u}).δ ε (yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))) =
      stdSimplex.δ ε := by
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, ← stdSimplex.yonedaEquiv_δ_comp, Category.comp_id]

/-- The target vertex of an original Cartesian equivalence prism being marked forces its source vertex to be marked. -/
theorem cartesian_markedVertex_backward {X : Marked.{u}} {E B : SSet.{u}}
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B]
    (F : (Δ[1] : SSet.{u}) ⊗ X.toSSet ⟶ E)
    (hF : F ∈ (core (parameterMapping X.toSSet E)).obj (op ⦋1⦌))
    (ht : (parameterMapping X.toSSet E).δ 0 F ∈ markedMappingVertices X (cartesian p)) :
    (parameterMapping X.toSSet E).δ 1 F ∈ markedMappingVertices X (cartesian p) := by
  let _ : Quasicategory E := quasicategory_of_innerFibration p
  let t₀ : (Δ[1] : SSet.{u}) _⦋0⦌ := (Δ[1] : SSet.{u}).δ 1 (yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))
  let t₁ : (Δ[1] : SSet.{u}) _⦋0⦌ := (Δ[1] : SSet.{u}).δ 0 (yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))
  let a : Edge t₀ t₁ :=
    Edge.mk' (yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))
  have hv := (mem_core_parameterMapping_iff F).mp hF
  have he₀ : yonedaEquiv.symm t₀ = stdSimplex.δ (1 : Fin 2) := standard_endpoint
  have he₁ : yonedaEquiv.symm t₁ = stdSimplex.δ (0 : Fin 2) := standard_endpoint
  have htarget : ((yonedaEquiv.symm t₁ ▷ X.toSSet) ≫ F) ∈ markedMappingVertices X (cartesian p) := by
    rw [he₁]
    exact ht
  have hmarked := (markedMappingVertices_section_iff X (cartesian p) F t₁).mp htarget
  have hsource : ((yonedaEquiv.symm t₀ ▷ X.toSSet) ≫ F) ∈ markedMappingVertices X (cartesian p) := by
    apply (markedMappingVertices_section_iff X (cartesian p) F t₀).mpr
    intro e he
    let b : Edge (X.toSSet.δ 1 e) (X.toSSet.δ 0 e) := Edge.mk' e
    have hv₀ : ((a.tensor (Edge.id (X.toSSet.δ 1 e))).map F).IsEquivalence :=
      (hv a.edge _).of_edge_eq rfl
    have hv₁ : ((a.tensor (Edge.id (X.toSSet.δ 0 e))).map F).IsEquivalence :=
      (hv a.edge _).of_edge_eq rfl
    have hb : CartesianEdge.IsPCartesian p (yonedaEquiv.symm (((Edge.id t₁).tensor b).map F).edge) :=
      hmarked e he
    exact cartesian_horizontal_source_of_target p F a b hv₀ hv₁ hb
  rw [he₀] at hsource
  exact hsource

/-- An original cocartesian equivalence prism transports marked vertices from its source to its target. -/
theorem cocartesian_markedVertex_forward {X : Marked.{u}} {E B : SSet.{u}}
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B]
    (F : (Δ[1] : SSet.{u}) ⊗ X.toSSet ⟶ E)
    (hF : F ∈ (core (parameterMapping X.toSSet E)).obj (op ⦋1⦌))
    (hs : (parameterMapping X.toSSet E).δ 1 F ∈ markedMappingVertices X (cocartesian p)) :
    (parameterMapping X.toSSet E).δ 0 F ∈ markedMappingVertices X (cocartesian p) := by
  let _ : Quasicategory E := quasicategory_of_innerFibration p
  let t₀ : (Δ[1] : SSet.{u}) _⦋0⦌ := (Δ[1] : SSet.{u}).δ 1 (yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))
  let t₁ : (Δ[1] : SSet.{u}) _⦋0⦌ := (Δ[1] : SSet.{u}).δ 0 (yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))
  let a : Edge t₀ t₁ :=
    Edge.mk' (yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))
  have hv := (mem_core_parameterMapping_iff F).mp hF
  have he₀ : yonedaEquiv.symm t₀ = stdSimplex.δ (1 : Fin 2) := standard_endpoint
  have he₁ : yonedaEquiv.symm t₁ = stdSimplex.δ (0 : Fin 2) := standard_endpoint
  have hsource : ((yonedaEquiv.symm t₀ ▷ X.toSSet) ≫ F) ∈ markedMappingVertices X (cocartesian p) := by
    rw [he₀]
    exact hs
  have hmarked := (markedMappingVertices_section_iff X (cocartesian p) F t₀).mp hsource
  have htarget : ((yonedaEquiv.symm t₁ ▷ X.toSSet) ≫ F) ∈ markedMappingVertices X (cocartesian p) := by
    apply (markedMappingVertices_section_iff X (cocartesian p) F t₁).mpr
    intro e he
    let b : Edge (X.toSSet.δ 1 e) (X.toSSet.δ 0 e) := Edge.mk' e
    have hv₀ : ((a.tensor (Edge.id (X.toSSet.δ 1 e))).map F).IsEquivalence :=
      (hv a.edge _).of_edge_eq rfl
    have hv₁ : ((a.tensor (Edge.id (X.toSSet.δ 0 e))).map F).IsEquivalence :=
      (hv a.edge _).of_edge_eq rfl
    have hb : CocartesianEdge.IsPCocartesian p (yonedaEquiv.symm (((Edge.id t₀).tensor b).map F).edge) :=
      hmarked e he
    exact cocartesian_horizontal_target_of_source p F a b hv₀ hv₁ hb
  rw [he₁] at htarget
  exact htarget

/-- The original Cartesian marked-map vertex condition is invariant across every edge of the native core. -/
theorem cartesian_markedVertices_core_edgeInvariant {X : Marked.{u}} {E B : SSet.{u}}
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B]
    (z : (core (parameterMapping X.toSSet E) : SSet.{u}) _⦋1⦌) :
    ((core (parameterMapping X.toSSet E) : SSet.{u}).δ 1 z).val ∈ markedMappingVertices X (cartesian p) ↔
      ((core (parameterMapping X.toSSet E) : SSet.{u}).δ 0 z).val ∈ markedMappingVertices X (cartesian p) := by
  let _ : Quasicategory E := quasicategory_of_innerFibration p
  let _ : Quasicategory (parameterMapping X.toSSet E) := parameterMapping_quasicategory X.toSSet E
  let K := (core (parameterMapping X.toSSet E) : SSet.{u})
  let _ : KanComplex K := inferInstance
  constructor
  · intro h
    let e : Edge (K.δ 1 z) (K.δ 0 z) := Edge.mk' z
    let I := e.invStruct
    have htarget : (parameterMapping X.toSSet E).δ 0 I.inv.edge.val ∈ markedMappingVertices X (cartesian p) := by
      have ht := congrArg Subtype.val I.inv.tgt_eq
      change (K.δ 0 I.inv.edge).val ∈ markedMappingVertices X (cartesian p)
      exact ht.symm ▸ h
    have hs := cartesian_markedVertex_backward p I.inv.edge.val I.inv.edge.property htarget
    have ht := congrArg Subtype.val I.inv.src_eq
    change (K.δ 1 I.inv.edge).val ∈ markedMappingVertices X (cartesian p) at hs
    exact ht ▸ hs
  · exact cartesian_markedVertex_backward p z.val z.property

/-- The original cocartesian marked-map vertex condition is invariant on the same whole native core edges. -/
theorem cocartesian_markedVertices_core_edgeInvariant {X : Marked.{u}} {E B : SSet.{u}}
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B]
    (z : (core (parameterMapping X.toSSet E) : SSet.{u}) _⦋1⦌) :
    ((core (parameterMapping X.toSSet E) : SSet.{u}).δ 1 z).val ∈ markedMappingVertices X (cocartesian p) ↔
      ((core (parameterMapping X.toSSet E) : SSet.{u}).δ 0 z).val ∈ markedMappingVertices X (cocartesian p) := by
  let _ : Quasicategory E := quasicategory_of_innerFibration p
  let _ : Quasicategory (parameterMapping X.toSSet E) := parameterMapping_quasicategory X.toSSet E
  let K := (core (parameterMapping X.toSSet E) : SSet.{u})
  let _ : KanComplex K := inferInstance
  constructor
  · exact cocartesian_markedVertex_forward p z.val z.property
  · intro h
    let e : Edge (K.δ 1 z) (K.δ 0 z) := Edge.mk' z
    let I := e.invStruct
    have hsource : (parameterMapping X.toSSet E).δ 1 I.inv.edge.val ∈ markedMappingVertices X (cocartesian p) := by
      have ht := congrArg Subtype.val I.inv.src_eq
      change (K.δ 1 I.inv.edge).val ∈ markedMappingVertices X (cocartesian p)
      exact ht.symm ▸ h
    have ht := cocartesian_markedVertex_forward p I.inv.edge.val I.inv.edge.property hsource
    have hs := congrArg Subtype.val I.inv.tgt_eq
    change (K.δ 0 I.inv.edge).val ∈ markedMappingVertices X (cocartesian p) at ht
    exact hs ▸ ht

end SSet.Marked
