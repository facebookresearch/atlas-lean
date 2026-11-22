/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontContractionVertices
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.VertexFixedHomotopy

/-!
# The SAME original fixed-front quotient has its genuine Joyal deformation

The entire original contraction prism descends through the original
front relation, fixes both original quotient vertices along degenerate
verticals and connects the SAME constant-front retraction to the identity.
The existing actual pointed cosimplicial maps supply the retraction and
section. Quasicategory test targets prove its categorical equivalence.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFixedFrontContraction

open FixedFrontCollapse

/-- The SAME full original fixed-front prism on its original structural quotient. -/
def quotientPrism (n : ℕ) : FixedFrontCollapse.object.{u} n ⊗ (Δ[1] : SSet.{u}) ⟶ FixedFrontCollapse.object.{u} n where
  app q := ↾fun p => _root_.Quotient.lift
    (fun a => _root_.Quotient.mk (FixedFrontCollapse.relation q) (simplex a p.2))
    (by
      rintro a b (rfl | hab)
      · rfl
      · exact _root_.Quotient.sound (Or.inr ⟨simplex_front a hab.1 p.2, simplex_front b hab.2 p.2⟩)) p.1
  naturality _q _r θ := by
    apply ConcreteCategory.hom_ext
    rintro ⟨p, t⟩
    induction p using _root_.Quotient.inductionOn' with
    | h a => rfl

/-- The SAME actual original constant-front cosimplicial retraction. -/
def toZero (n : ℕ) : FixedFrontCollapse.object.{u} n ⟶ FixedFrontCollapse.object.{u} 0 :=
  FixedFrontOperators.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0)

/-- The SAME actual original first-front cosimplicial section. -/
def fromZero (n : ℕ) : FixedFrontCollapse.object.{u} 0 ⟶ FixedFrontCollapse.object.{u} n :=
  FixedFrontOperators.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0)

/-- Both SAME original maps retain the exact original section/retraction identity. -/
theorem fromZero_toZero (n : ℕ) : fromZero.{u} n ≫ toZero n = 𝟙 (FixedFrontCollapse.object.{u} 0) := by
  have he : SimplexCategory.const ⦋0⦌ ⦋n⦌ 0 ≫ SimplexCategory.const ⦋n⦌ ⦋0⦌ 0 = 𝟙 ⦋0⦌ := by
    ext j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    rfl
  exact (FixedFrontOperators.map_comp _ _).symm.trans
    ((congrArg FixedFrontOperators.map he).trans (FixedFrontOperators.map_id 0))

private theorem simplex_time_zero {X : SSet.{u}} (n d : ℕ) (a : (Δ[n + 1] : SSet.{u}) _⦋d⦌)
    (x : X _⦋d⦌) :
    simplex a (((SSet.ι₀ (X := X)).app (op ⦋d⦌) x).2) =
      (SSet.stdSimplex.map (PathMaximumOperators.extension
        (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0 ≫ SimplexCategory.const ⦋0⦌ ⦋n⦌ 0))).app (op ⦋d⦌) a := by
  apply SSet.stdSimplex.ext
  intro i
  have ht := SSet.ι₀_app_snd_apply (X := X) x i
  have hv : vertex n (a i) 0 = (PathMaximumOperators.extension
      (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0 ≫ SimplexCategory.const ⦋0⦌ ⦋n⦌ 0)).toOrderHom (a i) := by
    cases a i using Fin.lastCases with
    | last => exact (ite_eq_left (Or.inl rfl)).trans (PathMaximumOperators.extension_last _).symm
    | cast j =>
      have hf := PathMaximumOperators.extension_front
        (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0 ≫ SimplexCategory.const ⦋0⦌ ⦋n⦌ 0) j
      have hz : ((SimplexCategory.const ⦋n⦌ ⦋0⦌ 0 ≫
        SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).toOrderHom j).castSucc = (0 : Fin (n + 2)) := rfl
      exact (ite_eq_right (by simp)).trans (hz.symm.trans hf.symm)
  exact (congrArg (vertex n (a i)) ht).trans hv

private theorem simplex_time_one {X : SSet.{u}} (n d : ℕ) (a : (Δ[n + 1] : SSet.{u}) _⦋d⦌)
    (x : X _⦋d⦌) : simplex a (((SSet.ι₁ (X := X)).app (op ⦋d⦌) x).2) = a := by
  apply SSet.stdSimplex.ext
  intro i
  have ht := SSet.ι₁_app_snd_apply (X := X) x i
  exact (congrArg (vertex n (a i)) ht).trans (ite_eq_left (Or.inr rfl))

/-- The full original first-time prism is the SAME original constant-front retraction composite. -/
theorem quotientPrism_zero (n : ℕ) :
    (SSet.ι₀ : FixedFrontCollapse.object.{u} n ⟶ FixedFrontCollapse.object.{u} n ⊗ Δ[1]) ≫ quotientPrism n =
      toZero n ≫ fromZero n := by
  have hm := (FixedFrontOperators.map_comp
    (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0) (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0)).symm
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro p
  induction p using _root_.Quotient.inductionOn' with
  | h a =>
    have hmap := ConcreteCategory.congr_hom (congr_app hm (op ⦋d⦌)) (_root_.Quotient.mk _ a)
    exact (congrArg (_root_.Quotient.mk (FixedFrontCollapse.relation (op ⦋d⦌)))
      (simplex_time_zero n d a
        (show (FixedFrontCollapse.object.{u} n) _⦋d⦌ from _root_.Quotient.mk _ a))).trans hmap.symm

/-- The full original other-time prism is the SAME original quotient identity. -/
theorem quotientPrism_one (n : ℕ) :
    (SSet.ι₁ : FixedFrontCollapse.object.{u} n ⟶ FixedFrontCollapse.object.{u} n ⊗ Δ[1]) ≫ quotientPrism n =
      𝟙 (FixedFrontCollapse.object.{u} n) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro p
  induction p using _root_.Quotient.inductionOn' with
  | h a =>
    exact congrArg (_root_.Quotient.mk (FixedFrontCollapse.relation (op ⦋d⦌)))
      (simplex_time_one n d a (show (FixedFrontCollapse.object.{u} n) _⦋d⦌ from _root_.Quotient.mk _ a))

/-- The actual full original quotient homotopy between its SAME constant-front composite and identity. -/
def deformation (n : ℕ) : SSet.Homotopy (toZero.{u} n ≫ fromZero n) (𝟙 (FixedFrontCollapse.object.{u} n)) :=
  SSet.Homotopy.mkOfH (quotientPrism n) (quotientPrism_zero n) (quotientPrism_one n)

/-- Every original quotient vertex has its SAME degenerate full vertical in the original deformation. -/
theorem deformation_degenerateVerticals (n : ℕ) : (deformation.{u} n).HasDegenerateVerticals := by
  intro p
  induction p using _root_.Quotient.inductionOn' with
  | h a =>
    have hσ : ∀ i : Fin 2, ((Δ[n + 1] : SSet.{u}).σ 0 a) i = a 0 := by
      intro i
      rw [SSet.stdSimplex.σ_apply]
      exact congrArg (fun j => a j) (Fin.eq_zero _)
    by_cases ha : a 0 = Fin.last (n + 1)
    · apply congrArg (_root_.Quotient.mk (FixedFrontCollapse.relation (op ⦋1⦌)))
      apply SSet.stdSimplex.ext
      intro i
      change vertex n (((Δ[n + 1] : SSet.{u}).σ 0 a) i) _ = ((Δ[n + 1] : SSet.{u}).σ 0 a) i
      rw [hσ]
      exact ite_eq_left (Or.inl ha)
    · have hfront : InFront ((Δ[n + 1] : SSet.{u}).σ 0 a) := by
        intro i
        change (((Δ[n + 1] : SSet.{u}).σ 0 a) i) ≠ Fin.last (n + 1)
        rw [hσ]
        exact ha
      exact _root_.Quotient.sound (Or.inr ⟨simplex_front _ hfront _, hfront⟩)

/-- The SAME actual original constant-front retraction is a categorical equivalence in every original dimension. -/
theorem toZero_categoricalEquivalence (n : ℕ) : SSet.categoricalEquivalences (toZero.{u} n) :=
  SSet.categoricalEquivalences_of_vertexFixed_deformation (toZero n) (fromZero n) (fromZero_toZero n)
    (deformation n) (deformation_degenerateVerticals n)

end CategoryTheory.CoherentRealization.OriginalFixedFrontContraction
