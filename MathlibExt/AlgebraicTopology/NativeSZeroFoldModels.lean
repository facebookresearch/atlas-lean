/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.StableInfinityKSpectra
public import MathlibExt.AlgebraicTopology.NativeDiagramFamilies

/-!
# Native zero-fold evaluation and object-circle maps

The zero-fold diagram is the actual coherent functor on the empty
product index. Object-circle maps use its original object vertex, the
native pointed unit generator and the native circle insertion. This
does not identify the object core with K0.

Source: Blumberg--Gepner--Tabuada, arXiv:1001.2282v4, Definition 7.5
and the one-skeleton structure-map description on page 45.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeSZeroFoldModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open QuasicategoricalModels StableInfinityCategoryModels
open StableInfinityFiniteDiagrams StableInfinityMultiSConstruction
open StableInfinityIntervalInsertion NativeDiagramFamilies
open MathlibExt.SpectraSource
open scoped Simplicial

universe u

/-- The actual degenerate identity edge has its two native inverse triangles. -/
theorem identity_edge_isEquivalence (X : SSet.{u}) (x : X _⦋0⦌) :
    IsEquivalenceEdge X (X.σ 0 x) := by
  have hx₀ : X.δ 0 (X.σ 0 x) = x :=
    X.δ_comp_σ_self'_apply (j := 0) (i := 0) rfl x
  have hx₁ : X.δ 1 (X.σ 0 x) = x :=
    X.δ_comp_σ_succ'_apply (j := 1) (i := 0) rfl x
  have h₀ : X.δ 0 (X.σ 0 (X.σ 0 x)) = X.σ 0 x :=
    X.δ_comp_σ_self'_apply (j := 0) (i := 0) rfl (X.σ 0 x)
  have h₁ : X.δ 1 (X.σ 0 (X.σ 0 x)) = X.σ 0 x :=
    X.δ_comp_σ_succ'_apply (j := 1) (i := 0) rfl (X.σ 0 x)
  have h₂ : X.δ 2 (X.σ 0 (X.σ 0 x)) = X.σ 0 x := by
    have h := X.δ_comp_σ_of_gt_apply (i := (1 : Fin 2))
      (j := (0 : Fin 1)) (by decide) (X.σ 0 x)
    change X.δ 2 (X.σ 0 (X.σ 0 x)) = X.σ 0 (X.δ 1 (X.σ 0 x)) at h
    simpa only [hx₁] using h
  exact ⟨X.σ 0 x, X.σ 0 (X.σ 0 x), X.σ 0 (X.σ 0 x),
    h₂, h₀, by rw [h₁, hx₁], h₂, h₀, by rw [h₁, hx₀]⟩

/-- Every original vertex gives its native maximal-core vertex. -/
def coreVertex (X : SSet.{u}) (x : X _⦋0⦌) : (core X) _⦋0⦌ :=
  ⟨x, by
    intro i j h
    fin_cases i
    fin_cases j
    change IsEquivalenceEdge X (X.map (edgeInclusion (0 : Fin 1) 0 h).op x)
    have he : edgeInclusion (0 : Fin 1) 0 h = SimplexCategory.σ (0 : Fin 1) := by
      ext k
      fin_cases k <;> rfl
    rw [he]
    exact identity_edge_isEquivalence X x⟩

/-- The original object is a whole zero-fold diagram, with no interval coordinates. -/
def zeroFoldFullVertex (C : StableInfinityCategory.{u}) (x : C.toSSet _⦋0⦌) :
    (multiGapCategory C 0 (fun _ => 0)) _⦋0⦌ := by
  let d : indexNerve (MultiIntervalCategory 0 (fun _ => 0)) ⟶ C.toSSet := SSet.const x
  let a := mappingZero _ _ d
  have ha : IsMultiGapVertex C 0 (fun _ => 0) a := by
    constructor
    · intro p r
      exact Fin.elim0 r
    · intro p r
      exact Fin.elim0 r
  exact ⟨a, (SSet.mem_fullEnhancedSubcategory_obj_zero_iff _ a).mpr ha⟩

/-- The actual zero-fold core object, inside the fixed all-coordinate diagonal. -/
def zeroFoldVertex (C : StableInfinityCategory.{u}) (x : C.toSSet _⦋0⦌) :
    (multiSDiagonal C 0) _⦋0⦌ :=
  coreVertex (multiGapCategory C 0 (fun _ => 0)) (zeroFoldFullVertex C x)

/-- Its native constant point retains every simplicial degeneracy. -/
def zeroFoldPoint (C : StableInfinityCategory.{u}) (x : C.toSSet _⦋0⦌) :
    Δ[0] ⟶ multiSDiagonal C 0 := SSet.const (zeroFoldVertex C x)

/-- The actual based unit map sends the nonbasepoint generator to the specified vertex. -/
def pointedUnitMap (X : PointedSSet.{u}) (x : X.right _⦋0⦌) :
    (𝟙_ PointedSSet.{u}) ⟶ X := by
  classical
  exact Under.homMk
    { app n := ↾fun s => if s = PointedSSet.tensorUnitSimplex n then
        (SSet.const x).app n (SSet.stdSimplex.const 0 0 n) else X.point n
      naturality n m f := by
        ext s
        change (if (𝟙_ PointedSSet.{u}).right.map f s =
            PointedSSet.tensorUnitSimplex m then
            (SSet.const x).app m (SSet.stdSimplex.const 0 0 m) else X.point m) =
          X.right.map f (if s = PointedSSet.tensorUnitSimplex n then
            (SSet.const x).app n (SSet.stdSimplex.const 0 0 n) else X.point n)
        rcases PointedSSet.eq_point_or_eq_tensorUnitSimplex s with hs | hs
        · subst s
          simp only [PointedSSet.map_point,
            Ne.symm (PointedSSet.tensorUnitSimplex_ne_point n),
            Ne.symm (PointedSSet.tensorUnitSimplex_ne_point m), ite_false]
        · subst s
          simp only [PointedSSet.map_tensorUnitSimplex, ite_true]
          simpa using congrArg (fun a => a (SSet.stdSimplex.const 0 0 n))
            ((SSet.const x).naturality f) }
    (by
      ext n t
      change (if (𝟙_ PointedSSet.{u}).hom.app n t =
          PointedSSet.tensorUnitSimplex n then
          (SSet.const x).app n (SSet.stdSimplex.const 0 0 n) else X.point n) =
        X.hom.app n t
      simp only [PointedSSet.hom_app,
        Ne.symm (PointedSSet.tensorUnitSimplex_ne_point n), ite_false])

/-- The actual object-circle map uses the native unit generator and actual S insertion. -/
def objectCircleMap {C : StableInfinityCategory.{0}}
    (I : CircleInsertion C) (x : C.toSSet _⦋0⦌) :
    PointedSSet.circle ⟶ pointedDiagonal I.pointing 1 :=
  (ρ_ PointedSSet.circle).inv ≫
    PointedSSet.circle ◁ pointedUnitMap (pointedDiagonal I.pointing 0)
      (zeroFoldVertex C x) ≫ I.map 0

/-- Evaluate the zero-fold diagram at its actual unique empty-product object. -/
def zeroFoldEvaluationComponent (C : StableInfinityCategory.{u})
    (k : SimplexCategoryᵒᵖ) :
    multiGapCore C 0 (fun _ => k.unop.len) ⟶ core C.toSSet :=
  coreMap (multiGapInclusion C 0 (fun _ => k.unop.len) ≫
    evaluateAt _ C.toSSet
      (ULift.up (ComposableArrows.mk₀ (fun i : Fin 0 => Fin.elim0 i))))

/-- The complete zero-fold comparison is normalized on each actual parameter simplex. -/
structure ZeroFoldEvaluationComparison (C : StableInfinityCategory.{u}) where
  map : multiSDiagonal C 0 ⟶ core C.toSSet
  normalization : ∀ k : SimplexCategoryᵒᵖ,
    map.app k = (zeroFoldEvaluationComponent C k).app k
  weak : WeakEquivalence map

end MathlibExt.AlgebraicTopology.NativeSZeroFoldModels
