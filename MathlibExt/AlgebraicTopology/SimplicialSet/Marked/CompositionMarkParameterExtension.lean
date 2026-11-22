/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CompositionCell
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MaximalPrismCriterion
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ParameterAdjunction

/-!
# The original composition marking cell under arbitrary marked parameters

The entire original two-simplex is retained when its long edge is marked.
For every original marked parameter, the mixed long edge is the actual
composition of a mixed short edge and the other short edge at the
parameter endpoint. Their native product triangle proves that the same
long edge is marked in an intrinsic Cartesian or cocartesian target.
Thus the actual maximal mapping restriction is an isomorphism; no Kan
parameter, Kan base or marked-model premise is imposed.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked

private theorem longEdge_parameter_cartesian {P : Marked.{u}} {E B : SSet.{u}}
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B]
    (f : prod P compositionCellSource.{u} ⟶ cartesian p)
    (a : P.toSSet _⦋1⦌) (ha : a ∈ P.marking) :
    CartesianEdge.IsPCartesian p (yonedaEquiv.symm
      (f.hom.app (op ⦋1⦌) (a, compositionLongEdge.{u}))) := by
  let F : P.toSSet ⊗ (Δ[2] : SSet.{u}) ⟶ E := f.hom
  obtain ⟨x₀, x₁, x₂, b, c, d, H, hH⟩ :=
    Edge.CompStruct.exists_of_simplex (yonedaEquiv (𝟙 (Δ[2] : SSet.{u})))
  have face (i : Fin 3) : (Δ[2] : SSet.{u}).δ i H.simplex = yonedaEquiv (stdSimplex.δ i) := by
    rw [hH, ← stdSimplex.yonedaEquiv_δ_comp, Category.comp_id]
  have hb : b.edge = yonedaEquiv (stdSimplex.δ (2 : Fin 3)) := H.d₂.symm.trans (face 2)
  have hc : c.edge = yonedaEquiv (stdSimplex.δ (0 : Fin 3)) := H.d₀.symm.trans (face 0)
  have hd : d.edge = compositionLongEdge.{u} := H.d₁.symm.trans (face 1)
  let e := Edge.mk' a
  let v := (e.tensor b).map F
  let w := ((Edge.id (P.toSSet.δ 0 a)).tensor c).map F
  let z := (e.tensor d).map F
  have hv : CartesianEdge.IsPCartesian p (yonedaEquiv.symm v.edge) :=
    @f.preserve (a, b.edge) ⟨ha, Or.inr (Or.inl hb)⟩
  have hw : CartesianEdge.IsPCartesian p (yonedaEquiv.symm w.edge) :=
    @f.preserve (P.toSSet.σ (0 : Fin 1) (P.toSSet.δ 0 a), c.edge)
      ⟨P.degenerate_mem _, Or.inr (Or.inr hc)⟩
  let T : Edge.CompStruct v w z := ((Edge.CompStruct.compId e).tensor H).map F
  have hz := CartesianEdge.isPCartesian_of_compStruct p T hv hw
  exact hd ▸ hz

private theorem longEdge_parameter_cocartesian {P : Marked.{u}} {E B : SSet.{u}}
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B]
    (f : prod P compositionCellSource.{u} ⟶ cocartesian p)
    (a : P.toSSet _⦋1⦌) (ha : a ∈ P.marking) :
    CocartesianEdge.IsPCocartesian p (yonedaEquiv.symm
      (f.hom.app (op ⦋1⦌) (a, compositionLongEdge.{u}))) := by
  let F : P.toSSet ⊗ (Δ[2] : SSet.{u}) ⟶ E := f.hom
  obtain ⟨x₀, x₁, x₂, b, c, d, H, hH⟩ :=
    Edge.CompStruct.exists_of_simplex (yonedaEquiv (𝟙 (Δ[2] : SSet.{u})))
  have face (i : Fin 3) : (Δ[2] : SSet.{u}).δ i H.simplex = yonedaEquiv (stdSimplex.δ i) := by
    rw [hH, ← stdSimplex.yonedaEquiv_δ_comp, Category.comp_id]
  have hb : b.edge = yonedaEquiv (stdSimplex.δ (2 : Fin 3)) := H.d₂.symm.trans (face 2)
  have hc : c.edge = yonedaEquiv (stdSimplex.δ (0 : Fin 3)) := H.d₀.symm.trans (face 0)
  have hd : d.edge = compositionLongEdge.{u} := H.d₁.symm.trans (face 1)
  let e := Edge.mk' a
  let v := (e.tensor b).map F
  let w := ((Edge.id (P.toSSet.δ 0 a)).tensor c).map F
  let z := (e.tensor d).map F
  have hv : CocartesianEdge.IsPCocartesian p (yonedaEquiv.symm v.edge) :=
    @f.preserve (a, b.edge) ⟨ha, Or.inr (Or.inl hb)⟩
  have hw : CocartesianEdge.IsPCocartesian p (yonedaEquiv.symm w.edge) :=
    @f.preserve (P.toSSet.σ (0 : Fin 1) (P.toSSet.δ 0 a), c.edge)
      ⟨P.degenerate_mem _, Or.inr (Or.inr hc)⟩
  let T : Edge.CompStruct v w z := ((Edge.CompStruct.compId e).tensor H).map F
  have hz := CocartesianEdge.isPCocartesian_of_compStruct p T hv hw
  exact hd ▸ hz

/-- The original whole prism extends the composition long-edge marking into the Cartesian target. -/
def extendCompositionMarkCartesian {P : Marked.{u}} {E B : SSet.{u}}
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B]
    (f : prod P compositionCellSource.{u} ⟶ cartesian p) :
    prod P compositionCellTarget.{u} ⟶ cartesian p where
  hom := f.hom
  preserve {e} he := by
    rcases he.2 with hdeg | hlong | hshort
    · exact @f.preserve e ⟨he.1, Or.inl hdeg⟩
    · change CartesianEdge.IsPCartesian p (yonedaEquiv.symm
        (f.hom.app (op ⦋1⦌) (e.1, e.2)))
      rw [hlong]
      exact longEdge_parameter_cartesian p f e.1 he.1
    · exact @f.preserve e ⟨he.1, Or.inr hshort⟩

/-- The same original prism extends the long-edge marking into the cocartesian target. -/
def extendCompositionMarkCocartesian {P : Marked.{u}} {E B : SSet.{u}}
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B]
    (f : prod P compositionCellSource.{u} ⟶ cocartesian p) :
    prod P compositionCellTarget.{u} ⟶ cocartesian p where
  hom := f.hom
  preserve {e} he := by
    rcases he.2 with hdeg | hlong | hshort
    · exact @f.preserve e ⟨he.1, Or.inl hdeg⟩
    · change CocartesianEdge.IsPCocartesian p (yonedaEquiv.symm
        (f.hom.app (op ⦋1⦌) (e.1, e.2)))
      rw [hlong]
      exact longEdge_parameter_cocartesian p f e.1 he.1
    · exact @f.preserve e ⟨he.1, Or.inr hshort⟩

/-- Cartesian mapping restriction across the exact original composition marking cell is a native isomorphism. -/
def compositionMarkCartesianMappingIso {E B : SSet.{u}} (p : E ⟶ B)
    [InnerFibration p] [Quasicategory B] :
    mappingComplex .maximal compositionCellTarget.{u} (cartesian p) ≅
      mappingComplex .maximal compositionCellSource.{u} (cartesian p) where
  hom := mappingComplexPre .maximal compositionCell.{u} (cartesian p)
  inv :=
    { app n := ↾fun f => extendCompositionMarkCartesian p f
      naturality n m a := by ext f; apply Hom.ext; rfl }
  hom_inv_id := by ext n f; apply Hom.ext; ext q a; rfl
  inv_hom_id := by ext n f; apply Hom.ext; ext q a; rfl

/-- The dual maximal mapping restriction keeps the same actual original composition marking isomorphism. -/
def compositionMarkCocartesianMappingIso {E B : SSet.{u}} (p : E ⟶ B)
    [InnerFibration p] [Quasicategory B] :
    mappingComplex .maximal compositionCellTarget.{u} (cocartesian p) ≅
      mappingComplex .maximal compositionCellSource.{u} (cocartesian p) where
  hom := mappingComplexPre .maximal compositionCell.{u} (cocartesian p)
  inv :=
    { app n := ↾fun f => extendCompositionMarkCocartesian p f
      naturality n m a := by ext f; apply Hom.ext; rfl }
  hom_inv_id := by ext n f; apply Hom.ext; ext q a; rfl
  inv_hom_id := by ext n f; apply Hom.ext; ext q a; rfl

end SSet.Marked
