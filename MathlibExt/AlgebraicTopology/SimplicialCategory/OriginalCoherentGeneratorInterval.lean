/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentBead
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentBeadInterval

/-!
# Original coherent generators as full endpoint beads

Every original coherent generator has an actual full endpoint-interval
bead representing the same Hom simplex. Its coefficient is the entire
original interval preimage, and evaluation agrees through the original
outer-operator relation.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalBead

open SimplicialEnrichment

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q r : SimplexCategoryᵒᵖ}

/-- The whole original coefficient supplies the original endpoint order. -/
theorem original_order (a : Arrow K x y q) : a.source.as.down ≤ a.target.as.down :=
  HomUnitsAndEmpty.source_order (a := a.source.as) (b := a.target.as) a.hom

/-- The same original endpoint-interval dimension. -/
def trimDimension (a : Arrow K x y q) : ℕ :=
  OriginalBeadInterval.length a.source.as.down a.target.as.down

/-- The actual original interval simplex operator. -/
def trimOperator (a : Arrow K x y q) : ⦋trimDimension a⦌ ⟶ a.degree :=
  SimplexCategory.Hom.mk
    (OriginalBeadInterval.embedding a.source.as.down a.target.as.down
      (original_order a)).toOrderHom

/-- The full original coefficient interval isomorphism. -/
def trimHomIso (a : Arrow K x y q) :
    ((initial (trimDimension a)) ⟶[SSet.{u}] (terminal (trimDimension a))) ≅
      (a.source ⟶[SSet.{u}] a.target) :=
  OriginalBeadInterval.homIso a.source.as.down a.target.as.down (original_order a)

/-- The original interval operator starts at the original source object. -/
theorem trim_source (a : Arrow K x y q) :
    (coherentSimplexMap (trimOperator a)).obj (initial (trimDimension a)) = a.source :=
  congrArg SimplicialThickening.mk
    (OriginalBeadInterval.lifted_zero a.source.as.down a.target.as.down (original_order a))

/-- The original interval operator ends at the original target object. -/
theorem trim_target (a : Arrow K x y q) :
    (coherentSimplexMap (trimOperator a)).obj (terminal (trimDimension a)) = a.target :=
  congrArg SimplicialThickening.mk
    (OriginalBeadInterval.lifted_last a.source.as.down a.target.as.down (original_order a))

/-- The full original interval map retains its same original coefficient operator. -/
theorem trimHomIso_hom (a : Arrow K x y q) :
    (trimHomIso a).hom =
      (coherentSimplexMap (trimOperator a)).map
        (initial (trimDimension a)) (terminal (trimDimension a)) ≫
      eqToHom (congrArg₂
        (fun i j : coherentSimplex.{u} a.degree => i ⟶[SSet.{u}] j)
        (trim_source a) (trim_target a)) :=
  OriginalBeadInterval.homIso_hom a.source.as.down a.target.as.down (original_order a)

/-- The complete original endpoint bead of an original coherent generator. -/
def trim (a : Arrow K x y q) : Bead K x y q where
  dimension := trimDimension a
  simplex := K.map (trimOperator a).op a.simplex
  source_eq := (vertex_operator K (trimOperator a) a.simplex
    (initial (trimDimension a))).trans
      ((congrArg (vertex K a.simplex) (trim_source a)).trans a.source_eq)
  target_eq := (vertex_operator K (trimOperator a) a.simplex
    (terminal (trimDimension a))).trans
      ((congrArg (vertex K a.simplex) (trim_target a)).trans a.target_eq)
  coefficient := (trimHomIso a).inv.app q a.hom

/-- Evaluation of the same original coherent generator. -/
def originalEvaluation (a : Arrow K x y q) : (hom K x y).obj q :=
  (simplexHom K a.simplex a.source a.target a.source_eq a.target_eq).app q a.hom

private theorem inverse_coefficient {X Y : SSet.{u}} (e : X ≅ Y)
    (q : SimplexCategoryᵒᵖ) (p : Y.obj q) :
    e.hom.app q (e.inv.app q p) = p :=
  ConcreteCategory.congr_hom (congr_app e.inv_hom_id q) p

/-- The complete original generator is evaluated through the same full interval map. -/
theorem trim_evaluation_factor (a : Arrow K x y q) :
    simplexHom K (trim a).simplex
      (initial (trimDimension a)) (terminal (trimDimension a))
      (trim a).source_eq (trim a).target_eq =
      (trimHomIso a).hom ≫
        simplexHom K a.simplex a.source a.target a.source_eq a.target_eq := by
  change simplexHom K (K.map (trimOperator a).op a.simplex)
    (initial (trimDimension a)) (terminal (trimDimension a)) _ _ = _
  have ho := simplexHom_operator (trimOperator a) a.simplex
    (initial (trimDimension a)) (terminal (trimDimension a))
    (trim a).source_eq (trim a).target_eq
  have hs := simplexHom_source_transport a.simplex (trim_source a) (trim_target a)
    ((vertex_operator K (trimOperator a) a.simplex
      (initial (trimDimension a))).symm.trans (trim a).source_eq)
    ((vertex_operator K (trimOperator a) a.simplex
      (terminal (trimDimension a))).symm.trans (trim a).target_eq)
    a.source_eq a.target_eq
  exact ho.trans ((congrArg
    (fun g => (coherentSimplexMap (trimOperator a)).map
      (initial (trimDimension a)) (terminal (trimDimension a)) ≫ g) hs.symm).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫
          simplexHom K a.simplex a.source a.target a.source_eq a.target_eq)
            (trimHomIso_hom a).symm)))

/-- Every original coherent generator has the same Hom value as its full endpoint bead. -/
theorem evaluation_trim (a : Arrow K x y q) :
    (trim a).evaluation = originalEvaluation a := by
  have h := ConcreteCategory.congr_hom (congr_app (trim_evaluation_factor a) q)
    ((trimHomIso a).inv.app q a.hom)
  change _ = (simplexHom K a.simplex a.source a.target a.source_eq a.target_eq).app q
    ((trimHomIso a).hom.app q ((trimHomIso a).inv.app q a.hom)) at h
  rw [inverse_coefficient] at h
  exact h

private theorem inverse_operator {X Y : SSet.{u}} (e : X ≅ Y)
    {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r) (p : Y.obj q) :
    e.inv.app r (Y.map f p) = X.map f (e.inv.app q p) :=
  ConcreteCategory.congr_hom (e.inv.naturality f) p

private theorem bead_coefficient_congr {K : SSet.{u}} {x y : K _⦋0⦌}
    {q : SimplexCategoryᵒᵖ} (n : ℕ) (σ : K _⦋n⦌)
    (hx : vertex K σ (initial n) = x) (hy : vertex K σ (terminal n) = y)
    (p r : ((initial n) ⟶[SSet.{u}] (terminal n)).obj q) (h : p = r) :
    (Bead.mk n σ hx hy p : Bead K x y q) = Bead.mk n σ hx hy r := by
  cases h
  rfl

/-- The complete original interval bead retains every scalar operator. -/
theorem trim_map (a : Arrow K x y q) (f : q ⟶ r) :
    trim (a.map f) = (trim a).map f :=
  bead_coefficient_congr (trimDimension a) (trim a).simplex
    (trim a).source_eq (trim a).target_eq _ _
      (inverse_operator (trimHomIso a) f a.hom)

/-- Every original generator is represented by a full original endpoint bead. -/
theorem exists_full_bead (a : Arrow K x y q) :
    ∃ b : Bead K x y q, b.evaluation = originalEvaluation a :=
  ⟨trim a, evaluation_trim a⟩

end CategoryTheory.CoherentRealization.OriginalBead
