/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.KanMarkCells
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MaximalPrismCriterion
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ParameterAdjunction

/-!
# Whole parameter products preserve the original Kan marking extension

For an arbitrary originally marked parameter and an actual Kan source,
changing the source marking from minimal to maximal extends every full
marked prism into an intrinsic Cartesian or cocartesian target uniquely
on its original simplicial map. A mixed product edge is the original
composition of a marked parameter edge and a Kan-source edge. The latter
has an actual equivalence image; the native triangle calculus proves the
same full mixed edge is marked. No Kan parameter or Kan base is assumed.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked

private theorem horizontal_image_equivalence {P : Marked.{u}} {K E : SSet.{u}} [KanComplex K]
    (F : P.toSSet ⊗ K ⟶ E) (x : P.toSSet _⦋0⦌) (b : K _⦋1⦌) :
    (Edge.mk' (F.app (op ⦋1⦌) (P.toSSet.σ (0 : Fin 1) x, b))).IsEquivalence := by
  let t : K ⟶ E := CartesianMonoidalCategory.lift (SSet.const x) (𝟙 K) ≫ F
  have h := (Edge.isEquivalence_of_kanComplex (Edge.mk' b)).map t
  have hσ : SimplexCategory.const ⦋1⦌ ⦋0⦌ 0 = SimplexCategory.σ (0 : Fin 1) := by
    ext i
    fin_cases i <;> rfl
  have ht : t.app (op ⦋1⦌) b = F.app (op ⦋1⦌) (P.toSSet.σ (0 : Fin 1) x, b) := by
    change F.app (op ⦋1⦌) (P.toSSet.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op x, b) = _
    rw [hσ]
    rfl
  exact h.of_edge_eq ht

private theorem kan_parameter_marks_cartesian {P : Marked.{u}} {K E B : SSet.{u}} [KanComplex K]
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B] (F : P.toSSet ⊗ K ⟶ E)
    (hF : ∀ (a : P.toSSet _⦋1⦌) (x : K _⦋0⦌), a ∈ P.marking →
      CartesianEdge.IsPCartesian p (SSet.yonedaEquiv.symm (F.app (op ⦋1⦌) (a, K.σ (0 : Fin 1) x))))
    (z : P.toSSet _⦋1⦌ × K _⦋1⦌) (hz : z.1 ∈ P.marking) :
    CartesianEdge.IsPCartesian p (SSet.yonedaEquiv.symm (F.app (op ⦋1⦌) z)) := by
  let a : Edge (P.toSSet.δ 1 z.1) (P.toSSet.δ 0 z.1) := Edge.mk' z.1
  let b : Edge (K.δ 1 z.2) (K.δ 0 z.2) := Edge.mk' z.2
  let v := (a.tensor (Edge.id (K.δ 1 z.2))).map F
  let w := ((Edge.id (P.toSSet.δ 0 z.1)).tensor b).map F
  let d := (a.tensor b).map F
  have hv : CartesianEdge.IsPCartesian p (SSet.yonedaEquiv.symm v.edge) := hF z.1 (K.δ 1 z.2) hz
  have hwE : w.IsEquivalence := (horizontal_image_equivalence (P := P) (K := K) (E := E) F _ z.2).of_edge_eq rfl
  have hw : CartesianEdge.IsPCartesian p (SSet.yonedaEquiv.symm w.edge) :=
    CartesianEdge.isPCartesian_of_isEquivalence p _
      (hwE.of_edge_eq (Equiv.apply_symm_apply SSet.yonedaEquiv w.edge).symm)
  let H : Edge.CompStruct v w d :=
    ((Edge.CompStruct.compId a).tensor (Edge.CompStruct.idComp b)).map F
  exact CartesianEdge.isPCartesian_of_compStruct (e₀₁ := v) (e₁₂ := w) (e₀₂ := d) p H hv hw

/-- The original whole prism extends every Kan-source mark into the intrinsic cartesian target. -/
def extendKanMarkCartesian {P : Marked.{u}} {K E B : SSet.{u}} [KanComplex K]
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B]
    (f : prod P (min K) ⟶ cartesian p) : prod P (max K) ⟶ cartesian p where
  hom := f.hom
  preserve {e} he := by
    let F : P.toSSet ⊗ K ⟶ E := f.hom
    exact kan_parameter_marks_cartesian (P := P) (K := K) p F
      (fun a x ha => @f.preserve (a, K.σ (0 : Fin 1) x) ⟨ha, ⟨x, rfl⟩⟩) e he.1

private theorem kan_parameter_marks_cocartesian {P : Marked.{u}} {K E B : SSet.{u}} [KanComplex K]
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B] (F : P.toSSet ⊗ K ⟶ E)
    (hF : ∀ (a : P.toSSet _⦋1⦌) (x : K _⦋0⦌), a ∈ P.marking →
      CocartesianEdge.IsPCocartesian p (SSet.yonedaEquiv.symm (F.app (op ⦋1⦌) (a, K.σ (0 : Fin 1) x))))
    (z : P.toSSet _⦋1⦌ × K _⦋1⦌) (hz : z.1 ∈ P.marking) :
    CocartesianEdge.IsPCocartesian p (SSet.yonedaEquiv.symm (F.app (op ⦋1⦌) z)) := by
  let a : Edge (P.toSSet.δ 1 z.1) (P.toSSet.δ 0 z.1) := Edge.mk' z.1
  let b : Edge (K.δ 1 z.2) (K.δ 0 z.2) := Edge.mk' z.2
  let v := (a.tensor (Edge.id (K.δ 1 z.2))).map F
  let w := ((Edge.id (P.toSSet.δ 0 z.1)).tensor b).map F
  let d := (a.tensor b).map F
  have hv : CocartesianEdge.IsPCocartesian p (SSet.yonedaEquiv.symm v.edge) := hF z.1 (K.δ 1 z.2) hz
  have hwE : w.IsEquivalence := (horizontal_image_equivalence (P := P) (K := K) (E := E) F _ z.2).of_edge_eq rfl
  have hw : CocartesianEdge.IsPCocartesian p (SSet.yonedaEquiv.symm w.edge) :=
    CocartesianEdge.isPCocartesian_of_isEquivalence p _
      (hwE.of_edge_eq (Equiv.apply_symm_apply SSet.yonedaEquiv w.edge).symm)
  let H : Edge.CompStruct v w d :=
    ((Edge.CompStruct.compId a).tensor (Edge.CompStruct.idComp b)).map F
  exact CocartesianEdge.isPCocartesian_of_compStruct (e₀₁ := v) (e₁₂ := w) (e₀₂ := d) p H hv hw

/-- The original whole prism extends every Kan-source mark into the intrinsic cocartesian target. -/
def extendKanMarkCocartesian {P : Marked.{u}} {K E B : SSet.{u}} [KanComplex K]
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B]
    (f : prod P (min K) ⟶ cocartesian p) : prod P (max K) ⟶ cocartesian p where
  hom := f.hom
  preserve {e} he := by
    let F : P.toSSet ⊗ K ⟶ E := f.hom
    exact kan_parameter_marks_cocartesian (P := P) (K := K) p F
      (fun a x ha => @f.preserve (a, K.σ (0 : Fin 1) x) ⟨ha, ⟨x, rfl⟩⟩) e he.1

/-- Cartesian Kan-marking extension keeps the entire original simplicial map literally. -/
@[simp]
theorem extendKanMarkCartesian_hom {P : Marked.{u}} {K E B : SSet.{u}} [KanComplex K]
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B] (f : prod P (min K) ⟶ cartesian p) :
    (extendKanMarkCartesian p f).hom = f.hom := rfl

/-- The dual extension also keeps every original simplex literally. -/
@[simp]
theorem extendKanMarkCocartesian_hom {P : Marked.{u}} {K E B : SSet.{u}} [KanComplex K]
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B] (f : prod P (min K) ⟶ cocartesian p) :
    (extendKanMarkCocartesian p f).hom = f.hom := rfl

/-- The actual maximal mapping complexes into a Cartesian target agree across the complete original
  Kan-source marking cell. -/
def kanMarkCartesianMappingIso (K : SSet.{u}) [KanComplex K] {E B : SSet.{u}}
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    mappingComplex .maximal (max K) (cartesian p) ≅ mappingComplex .maximal (min K) (cartesian p) where
  hom := mappingComplexPre .maximal (kanMarkCell K) (cartesian p)
  inv :=
    { app n := ↾fun f => extendKanMarkCartesian p f
      naturality n m a := by
        ext f
        apply Hom.ext
        rfl }
  hom_inv_id := by ext n f; apply Hom.ext; ext q a; rfl
  inv_hom_id := by ext n f; apply Hom.ext; ext q a; rfl

/-- The same original full mapping-complex comparison is an isomorphism for intrinsic cocartesian targets. -/
def kanMarkCocartesianMappingIso (K : SSet.{u}) [KanComplex K] {E B : SSet.{u}}
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    mappingComplex .maximal (max K) (cocartesian p) ≅ mappingComplex .maximal (min K) (cocartesian p) where
  hom := mappingComplexPre .maximal (kanMarkCell K) (cocartesian p)
  inv :=
    { app n := ↾fun f => extendKanMarkCocartesian p f
      naturality n m a := by
        ext f
        apply Hom.ext
        rfl }
  hom_inv_id := by ext n f; apply Hom.ext; ext q a; rfl
  inv_hom_id := by ext n f; apply Hom.ext; ext q a; rfl

end SSet.Marked
