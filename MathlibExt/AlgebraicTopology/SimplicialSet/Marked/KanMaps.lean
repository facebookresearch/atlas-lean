/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Fibrations

/-!
# Original groupoidal maps into the relative markings

Every edge of a Kan source is an equivalence. Its image lies in both
relative edge classes of an inner fibration over a quasicategory. Thus
the maximally marked Kan source has exactly the original simplicial maps
into either relative marking. Over a fixed base this identifies the
actual marked section maps with their original strict projection
equations. This is a groupoidal mapping result, not general category-
valued straightening.
-/

noncomputable section
universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked

private theorem imageEquivalence {K X : SSet.{u}} [KanComplex K] (f : K ⟶ X) (e : K _⦋1⦌) :
    (Edge.mk' (f.app (op ⦋1⦌) e)).IsEquivalence :=
  (Edge.isEquivalence_iff_of_edge_eq (show
    (Edge.mk' (f.app (op ⦋1⦌) e)).edge = ((Edge.mk' e).map f).edge from rfl)).mpr
      ((Edge.isEquivalence_of_kanComplex (Edge.mk' e)).map f)

variable {K X B : SSet.{u}} [KanComplex K] (p : X ⟶ B) [InnerFibration p] [Quasicategory B]

/-- The original map from a Kan source preserves the exact Cartesian marking. -/
def ofMaxKanCartesian (f : K ⟶ X) : max K ⟶ cartesian p where
  hom := f
  preserve {e} _ := by
    let e₀ : K _⦋1⦌ := e
    have he := imageEquivalence f e₀
    have he' : (Edge.mk' (yonedaEquiv (yonedaEquiv.symm (f.app (op ⦋1⦌) e₀)))).IsEquivalence :=
      (Equiv.apply_symm_apply yonedaEquiv (f.app (op ⦋1⦌) e₀)).symm ▸ he
    exact CartesianEdge.isPCartesian_of_isEquivalence p _ he'

/-- The original map from a Kan source preserves the exact cocartesian marking. -/
def ofMaxKanCocartesian (f : K ⟶ X) : max K ⟶ cocartesian p where
  hom := f
  preserve {e} _ := by
    let e₀ : K _⦋1⦌ := e
    have he := imageEquivalence f e₀
    have he' : (Edge.mk' (yonedaEquiv (yonedaEquiv.symm (f.app (op ⦋1⦌) e₀)))).IsEquivalence :=
      (Equiv.apply_symm_apply yonedaEquiv (f.app (op ⦋1⦌) e₀)).symm ▸ he
    exact CocartesianEdge.isPCocartesian_of_isEquivalence p _ he'

/-- The Cartesian marked lift retains precisely the supplied full simplicial map. -/
@[simp] theorem ofMaxKanCartesian_hom (f : K ⟶ X) : (ofMaxKanCartesian p f).hom = f := rfl

/-- The cocartesian marked lift retains precisely the supplied full simplicial map. -/
@[simp] theorem ofMaxKanCocartesian_hom (f : K ⟶ X) : (ofMaxKanCocartesian p f).hom = f := rfl

/-- All marked maps from the maximally marked Kan source are the original simplicial maps. -/
def kanCartesianHomEquiv : (max K ⟶ cartesian p) ≃ (K ⟶ X) where
  toFun f := f.hom
  invFun f := ofMaxKanCartesian p f
  left_inv _ := Hom.ext rfl
  right_inv _ := rfl

/-- The same full Hom comparison for the actual cocartesian marking. -/
def kanCocartesianHomEquiv : (max K ⟶ cocartesian p) ≃ (K ⟶ X) where
  toFun f := f.hom
  invFun f := ofMaxKanCocartesian p f
  left_inv _ := Hom.ext rfl
  right_inv _ := rfl

/-- Cartesian lifting of a groupoidal map commutes with the original source precomposition. -/
theorem ofMaxKanCartesian_pre {L : SSet.{u}} [KanComplex L] (a : L ⟶ K) (f : K ⟶ X) :
    ofMaxKanCartesian p (a ≫ f) = maximal.map a ≫ ofMaxKanCartesian p f := Hom.ext rfl

/-- Cocartesian lifting of a groupoidal map commutes with the same source precomposition. -/
theorem ofMaxKanCocartesian_pre {L : SSet.{u}} [KanComplex L] (a : L ⟶ K) (f : K ⟶ X) :
    ofMaxKanCocartesian p (a ≫ f) = maximal.map a ≫ ofMaxKanCocartesian p f := Hom.ext rfl

/-- Cartesian lifting commutes with every actual marked target map. -/
theorem ofMaxKanCartesian_post {Y C : SSet.{u}} (q : Y ⟶ C) [InnerFibration q] [Quasicategory C]
    (f : K ⟶ X) (g : cartesian p ⟶ cartesian q) :
    ofMaxKanCartesian q (f ≫ g.hom) = ofMaxKanCartesian p f ≫ g := Hom.ext rfl

/-- Cocartesian lifting commutes with every actual marked target map. -/
theorem ofMaxKanCocartesian_post {Y C : SSet.{u}} (q : Y ⟶ C) [InnerFibration q] [Quasicategory C]
    (f : K ⟶ X) (g : cocartesian p ⟶ cocartesian q) :
    ofMaxKanCocartesian q (f ≫ g.hom) = ofMaxKanCocartesian p f ≫ g := Hom.ext rfl

/-- Actual Cartesian marked sections from a Kan source retain exactly the strict base equation. -/
def kanCartesianSectionEquiv (b : K ⟶ B) :
    (Over.mk (maximal.map b) ⟶ Over.mk (cartesianProjection p)) ≃
      {f : K ⟶ X // f ≫ p = b} where
  toFun f := ⟨f.left.hom, congrArg Hom.hom (Over.w f)⟩
  invFun f := Over.homMk (ofMaxKanCartesian p f.1) (Hom.ext f.2)
  left_inv f := by
    apply CostructuredArrow.hom_ext
    exact Hom.ext rfl
  right_inv f := Subtype.ext rfl

/-- Actual cocartesian marked sections from the same Kan source retain that strict equation. -/
def kanCocartesianSectionEquiv (b : K ⟶ B) :
    (Over.mk (maximal.map b) ⟶ Over.mk (cocartesianProjection p)) ≃
      {f : K ⟶ X // f ≫ p = b} where
  toFun f := ⟨f.left.hom, congrArg Hom.hom (Over.w f)⟩
  invFun f := Over.homMk (ofMaxKanCocartesian p f.1) (Hom.ext f.2)
  left_inv f := by
    apply CostructuredArrow.hom_ext
    exact Hom.ext rfl
  right_inv f := Subtype.ext rfl

end SSet.Marked
