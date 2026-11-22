/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentUnstraighteningVerticalEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeUnstraighteningCompositionMarking
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.InverseTriangleBase
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MarkingCompleteness

/-!
# The SAME native unstraightening has its exact original Cartesian marking

Original vertical equivalences admit two actual inverse triangles over
the SAME prescribed constant base. The full original coherent unit
pullback equation identifies their entire constant-base sections. Their
shared original edge and original long unit marks detect the SAME root
coefficient marking through actual coefficient fibrancy. Comparing an
arbitrary original Cartesian edge with its actual marked target lift
and using original composition then proves exact Cartesian marking.
The literal original native Un object is consequently intrinsically
fibrant in the actual Cartesian marked model over every quasicategory
base, including non-Kan bases. Full Quillen and derived results remain
separate claims.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory coefficientMarkedModelCategory

/-- The SAME native pullback over an original constant base two-simplex retains the ENTIRE original constant
coherent base and every original Hom map. -/
theorem nativeUnstraightening_constant_base_two (B : SSet.{u})
    (F : EnrichedDiagram (realization B)ᵒᵖ) (b : B _⦋0⦌)
    (a : (nativeUnstraighteningTotal B F).toSSet _⦋2⦌)
    (ha : (nativeUnstraighteningProjection B F).hom.app (op ⦋2⦌) a = B.σ 0 (B.σ 0 b)) :
    ((nativeUnstraighteningCoherentProjection B F).hom.app (op ⦋2⦌) a).base =
      originalConstantBase ((unit B).app (op ⦋0⦌) b) 2 := by
  have h := congrArg (fun f => f.hom.app (op ⦋2⦌) a) (nativeUnstraightening_pullback_condition B F)
  change ((nativeUnstraighteningCoherentProjection B F).hom.app (op ⦋2⦌) a).base =
    (unit B).app (op ⦋2⦌) ((nativeUnstraighteningProjection B F).hom.app (op ⦋2⦌) a) at h
  exact h.trans ((congrArg ((unit B).app (op ⦋2⦌)) ha).trans
    ((SSet.σ_naturality_apply (unit B) (0 : Fin 2) (B.σ 0 b)).trans
      ((congrArg ((coherentBase (realization B)).σ (0 : Fin 2))
        (SSet.σ_naturality_apply (unit B) (0 : Fin 1) b)).trans
          (originalConstantBase_two ((unit B).app (op ⦋0⦌) b)))))

/-- A SAME original vertical equivalence edge of the literal native projection is marked, through two actual
original inverse triangles and their ENTIRE prescribed original constant base. -/
theorem nativeUnstraightening_vertical_equivalence_marked (B : SSet.{u}) [Quasicategory B]
    (F : EnrichedDiagram (realization B)ᵒᵖ) :
    let _ := coherentDiagramModelCategory B
    IsFibrant F → ∀ {x y : (nativeUnstraighteningTotal B F).toSSet _⦋0⦌}
      (e : Edge x y), e.IsEquivalence →
      (e.map (nativeUnstraighteningProjection B F).hom).edge =
        (Edge.id ((nativeUnstraighteningProjection B F).hom.app (op ⦋0⦌) y)).edge →
      e.edge ∈ (nativeUnstraighteningTotal B F).marking := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hF x y e he hB
  let p := nativeUnstraighteningProjection B F
  let π := nativeUnstraighteningCoherentProjection B F
  let _ : InnerFibration p.hom := nativeUnstraighteningProjection_innerFibration B F hF
  let _ : Quasicategory (max B).toSSet := by change Quasicategory B; infer_instance
  have heCart : CartesianEdge.IsPCartesian p.hom (yonedaEquiv.symm e.edge) :=
    CartesianEdge.isPCartesian_of_isEquivalence p.hom _
      (he.of_edge_eq (Equiv.apply_symm_apply yonedaEquiv e.edge).symm)
  obtain ⟨g, Hge, hgB, hHge⟩ := CartesianEdge.exists_vertical_inverse_triangle_base p.hom e heCart hB
  let _ : IsIso e.toHoHom := he
  let _ : IsIso (g.toHoHom ≫ e.toHoHom) := by
    rw [Edge.toHoHom_comp Hge, Edge.toHoHom_id]
    infer_instance
  have hg : g.IsEquivalence := IsIso.of_isIso_comp_right g.toHoHom e.toHoHom
  have hgCart : CartesianEdge.IsPCartesian p.hom (yonedaEquiv.symm g.edge) :=
    CartesianEdge.isPCartesian_of_isEquivalence p.hom _
      (hg.of_edge_eq (Equiv.apply_symm_apply yonedaEquiv g.edge).symm)
  have hxy : p.hom.app (op ⦋0⦌) x = p.hom.app (op ⦋0⦌) y :=
    (e.map p.hom).src_eq.symm.trans
      ((congrArg (B.δ (1 : Fin 2)) hB).trans (Edge.id (p.hom.app (op ⦋0⦌) y)).src_eq)
  have hgB' : (g.map p.hom).edge = (Edge.id (p.hom.app (op ⦋0⦌) x)).edge :=
    hgB.trans (congrArg (fun b => (Edge.id b).edge) hxy.symm)
  obtain ⟨k, Hkg, _, hHkg⟩ := CartesianEdge.exists_vertical_inverse_triangle_base p.hom g hgCart hgB'
  have hHkg' : p.hom.app (op ⦋2⦌) Hkg.simplex = B.σ 0 (B.σ 0 (p.hom.app (op ⦋0⦌) y)) :=
    hHkg.trans (congrArg (fun b => B.σ (0 : Fin 2) (B.σ (0 : Fin 1) b)) hxy)
  let v := (unit B).app (op ⦋0⦌) (p.hom.app (op ⦋0⦌) y)
  let a := π.hom.app (op ⦋2⦌) Hge.simplex
  let b := π.hom.app (op ⦋2⦌) Hkg.simplex
  have ha : a.base = originalConstantBase v 2 :=
    nativeUnstraightening_constant_base_two B F _ Hge.simplex hHge
  have hb : b.base = originalConstantBase v 2 :=
    nativeUnstraightening_constant_base_two B F _ Hkg.simplex hHkg'
  let s := fixedSectionEquiv F (originalConstantBase v 2) ⟨a, ha⟩
  let t := fixedSectionEquiv F (originalConstantBase v 2) ⟨b, hb⟩
  have hsRecord : UnstraighteningSimplex.mk (originalConstantBase v 2) s = a :=
    congrArg Subtype.val ((fixedSectionEquiv F (originalConstantBase v 2)).symm_apply_apply ⟨a, ha⟩)
  have htRecord : UnstraighteningSimplex.mk (originalConstantBase v 2) t = b :=
    congrArg Subtype.val ((fixedSectionEquiv F (originalConstantBase v 2)).symm_apply_apply ⟨b, hb⟩)
  let f₀ := (coneCofaceEmbedding.{u} (0 : Fin 3)).toOrderHom
  let f₁ := (coneCofaceEmbedding.{u} (1 : Fin 3)).toOrderHom
  let f₂ := (coneCofaceEmbedding.{u} (2 : Fin 3)).toOrderHom
  have hag : a.pull f₂ = π.hom.app (op ⦋1⦌) g.edge :=
    (SSet.δ_naturality_apply π.hom (2 : Fin 3) Hge.simplex).symm.trans
      (congrArg (π.hom.app (op ⦋1⦌)) Hge.d₂)
  have hbg : b.pull f₀ = π.hom.app (op ⦋1⦌) g.edge :=
    (SSet.δ_naturality_apply π.hom (0 : Fin 3) Hkg.simplex).symm.trans
      (congrArg (π.hom.app (op ⦋1⦌)) Hkg.d₀)
  have hshared : originalConstantSectionFace F v f₂ s = originalConstantSectionFace F v f₀ t :=
    originalConstantSectionFace_eq_of_simplex_eq F v f₂ f₀ s t
      ((congrArg (fun c : UnstraighteningSimplex F 2 => c.pull f₂) hsRecord).trans
        ((hag.trans hbg.symm).trans
          (congrArg (fun c : UnstraighteningSimplex F 2 => c.pull f₀) htRecord).symm))
  have hay : a.pull f₁ = π.hom.app (op ⦋1⦌) (Edge.id y).edge :=
    (SSet.δ_naturality_apply π.hom (1 : Fin 3) Hge.simplex).symm.trans
      (congrArg (π.hom.app (op ⦋1⦌)) Hge.d₁)
  have hbx : b.pull f₁ = π.hom.app (op ⦋1⦌) (Edge.id x).edge :=
    (SSet.δ_naturality_apply π.hom (1 : Fin 3) Hkg.simplex).symm.trans
      (congrArg (π.hom.app (op ⦋1⦌)) Hkg.d₁)
  have hsLong : originalConstantSectionRead F v (originalConstantSectionFace F v f₁ s) ∈
      (F.obj (op (v.obj (SimplicialThickening.mk (ULift.up (0 : Fin 1)))))).marking := by
    have h := (originalConstantSectionFace_simplex F v f₁ s).trans
      ((congrArg (fun c : UnstraighteningSimplex F 2 => c.pull f₁) hsRecord).trans hay)
    have hm : UnstraighteningSimplex.mk (originalConstantBase v 1)
        (originalConstantSectionFace F v f₁ s) ∈ (coherentUnstraightening (realization B) F).marking :=
      h.symm ▸ π.preserve ((nativeUnstraighteningTotal B F).degenerate_mem y)
    exact hm
  have htLong : originalConstantSectionRead F v (originalConstantSectionFace F v f₁ t) ∈
      (F.obj (op (v.obj (SimplicialThickening.mk (ULift.up (0 : Fin 1)))))).marking := by
    have h := (originalConstantSectionFace_simplex F v f₁ t).trans
      ((congrArg (fun c : UnstraighteningSimplex F 2 => c.pull f₁) htRecord).trans hbx)
    have hm : UnstraighteningSimplex.mk (originalConstantBase v 1)
        (originalConstantSectionFace F v f₁ t) ∈ (coherentUnstraightening (realization B) F).marking :=
      h.symm ▸ π.preserve ((nativeUnstraighteningTotal B F).degenerate_mem x)
    exact hm
  have hm := originalConstantSections_inverse_marking F v
    (coherentDiagramCoefficient_isFibrant B F _ hF) s t hshared hsLong htLong
  have hae : a.pull f₀ = π.hom.app (op ⦋1⦌) e.edge :=
    (SSet.δ_naturality_apply π.hom (0 : Fin 3) Hge.simplex).symm.trans
      (congrArg (π.hom.app (op ⦋1⦌)) Hge.d₀)
  have heRecord := (originalConstantSectionFace_simplex F v f₀ s).trans
    ((congrArg (fun c : UnstraighteningSimplex F 2 => c.pull f₀) hsRecord).trans hae)
  have hm' : UnstraighteningSimplex.mk (originalConstantBase v 1)
      (originalConstantSectionFace F v f₀ s) ∈ (coherentUnstraightening (realization B) F).marking := hm
  exact (nativeUnstraightening_marking_coherent_iff B F e.edge).mpr (heRecord ▸ hm')

/-- Every SAME original Cartesian edge of the literal native projection is marked, using its actual original marked
target lift and whole original vertical equivalence comparison. -/
theorem nativeUnstraighteningProjection_cartesian_marked (B : SSet.{u}) [Quasicategory B]
    (F : EnrichedDiagram (realization B)ᵒᵖ) :
    let _ := coherentDiagramModelCategory B
    IsFibrant F → ∀ e : (nativeUnstraighteningTotal B F).toSSet _⦋1⦌,
      CartesianEdge.IsPCartesian (nativeUnstraighteningProjection B F).hom (yonedaEquiv.symm e) →
        e ∈ (nativeUnstraighteningTotal B F).marking := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hF e hcart
  let p := nativeUnstraighteningProjection B F
  let _ : InnerFibration p.hom := nativeUnstraighteningProjection_innerFibration B F hF
  let a := Edge.mk' e
  obtain ⟨x, f, hf, hmap⟩ := exists_marked_target_lift p
    (nativeUnstraighteningProjection_originalCartesianEndpointLifting B F hF) _ _ (a.map p.hom)
  have hfCart : CartesianEdge.IsPCartesian p.hom (yonedaEquiv.symm f.edge) :=
    nativeUnstraighteningProjection_marked_cartesian B F hF f.edge hf
  obtain ⟨k, H, hk, _, hkB⟩ := CartesianEdge.exists_equivalence_comparison p.hom a f hcart hfCart hmap.symm
  have hkMark : k.edge ∈ (nativeUnstraighteningTotal B F).marking :=
    nativeUnstraightening_vertical_equivalence_marked B F hF k hk hkB
  exact compStruct_long_mem_marking p (nativeUnstraighteningProjection_compositionLifting B F hF) H hkMark hf

/-- The SAME literal original native projection has precisely its full original Cartesian edge set marked over every
original quasicategory base. -/
theorem nativeUnstraighteningProjection_marking_iff_cartesian (B : SSet.{u}) [Quasicategory B]
    (F : EnrichedDiagram (realization B)ᵒᵖ) :
    let _ := coherentDiagramModelCategory B
    IsFibrant F → ∀ e : (nativeUnstraighteningTotal B F).toSSet _⦋1⦌,
      e ∈ (nativeUnstraighteningTotal B F).marking ↔
        CartesianEdge.IsPCartesian (nativeUnstraighteningProjection B F).hom (yonedaEquiv.symm e) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hF e
  exact ⟨nativeUnstraighteningProjection_marked_cartesian B F hF e,
    nativeUnstraighteningProjection_cartesian_marked B F hF e⟩

/-- The SAME actual original native Un object is an intrinsic Cartesian fibration with its COMPLETE unchanged
Cartesian marking. -/
theorem nativeUnstraightening_original_intrinsic (B : SSet.{u}) [Quasicategory B]
    (F : EnrichedDiagram (realization B)ᵒᵖ) :
    let _ := coherentDiagramModelCategory B
    IsFibrant F → cartesianObjects B ((nativeUnstraightening B).obj F) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hF
  exact ⟨nativeUnstraighteningProjection_cartesianFibration B F hF,
    nativeUnstraighteningProjection_marking_iff_cartesian B F hF⟩

/-- Actual coherent-model fibrancy gives actual Cartesian marked model fibrancy of the SAME literal original native
Un object, through the TWO genuine original model choices. -/
theorem nativeUnstraightening_original_fibrant (B : SSet.{u}) [Quasicategory B]
    (F : EnrichedDiagram (realization B)ᵒᵖ) :
    let _ := markedCofibrationStructure (max B)
    let _ := cartesianMarkedFibrationStructure B
    let _ := cartesianMarkedWeakStructure B
    let _ := cartesianMarkedModelCategory B
    let _ := coherentDiagramModelCategory B
    IsFibrant F → IsFibrant ((nativeUnstraightening B).obj F) := by
  let _ := markedCofibrationStructure (max B)
  let _ := cartesianMarkedFibrationStructure B
  let _ := cartesianMarkedWeakStructure B
  let _ := cartesianMarkedModelCategory B
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hF
  exact (cartesianMarkedModel_fibrant_iff B ((nativeUnstraightening B).obj F)).mpr
    (nativeUnstraightening_original_intrinsic B F hF)

end SSet.Marked
