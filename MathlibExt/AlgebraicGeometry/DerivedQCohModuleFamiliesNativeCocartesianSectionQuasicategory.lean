/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.CategoricalCocartesianSections
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
import MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
import MathlibExt.AlgebraicGeometry.DerivedPrestackEvaluation

/-!
# Native cocartesian section quasicategory

For quasicategories `A`, `B` and `E`, a cocartesian fibration `p : E ⟶ B` and
a map `q : A ⟶ B`, the simplicial set of cocartesian sections of `p` over `q`
is a quasicategory. Inner horns in the section complex
are filled by lifting against postcomposition with the fibration, which is
an inner fibration, then checking the filler lies over the base map and has
cocartesian horizontal edges at every parameter vertex.

References: Lurie HTT Cor. 2.3.2.5, applied to `∅ → A`, for the step that
`Fun(A,E) → Fun(A,B)` is an inner fibration when `p` is one. Comparing the
sections with a limit (Lurie HTT §3.3.3) is separate background and is not
proved here.
-/

open CategoryTheory Opposite
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicTopology.CategoricalCocartesianSections
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels
open MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open CategoryTheory.MonoidalClosed
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open scoped Simplicial

universe u

/-- The constant map into the mapping space at the base map `q`. -/
private def constMap (A B : SSet.{u}) (q : A ⟶ B) (n : ℕ) : Δ[n] ⟶ mapping A B where
  app m := ↾fun _ : Δ[n].obj m ↦ (Functor.HomObj.ofNatTrans q : (mapping A B).obj m)
  naturality m m' g := by
    ext w
    rfl

/-- A horn into the section complex postcomposed with `p` is the constant map at `q`. -/
private theorem horn_over (A B E : SSet.{u}) (p : E ⟶ B) (q : A ⟶ B)
    (n : ℕ) (i : Fin (n + 3)) (σ₀ : (Λ[n + 2, i] : SSet.{u}) ⟶ sectionsOver p q) :
    (σ₀ ≫ (sectionSubcomplexOver p q).ι) ≫ (ihom A).map p =
      Λ[n + 2, i].ι ≫ constMap A B q (n + 2) := by
  ext m lam
  refine Functor.functorHom_ext (fun d f ↦ ?_)
  ext x
  exact (σ₀.app m lam).property.1 d f x

/-- The parameter edge at a vertex is the edge of the vertex section. -/
private theorem app_vertexParameter {A E : SSet.{u}} {n : SimplexCategoryᵒᵖ}
    (a : (mapping A E).obj n) (j : Fin (n.unop.len + 1)) :
    (a.app (op ⦋1⦌) (vertexParameter n j)) =
      (((mapping A E).map (SimplexCategory.const ⦋0⦌ n.unop j).op a).app
        (op ⦋1⦌) (vertexParameter (op ⦋0⦌) ⟨0, by decide⟩)) := rfl

/-- The lifted filler lies over `q` in every degree. -/
private theorem filler_over (A B E : SSet.{u}) (p : E ⟶ B) (q : A ⟶ B)
    (n : ℕ) (s : Δ[n + 2] ⟶ mapping A E)
    (hs : s ≫ (ihom A).map p = constMap A B q (n + 2))
    (m d : SimplexCategoryᵒᵖ) (w : Δ[n + 2].obj m) (g : m ⟶ d) (y : A.obj d) :
    p.app d (((s.app m w).app d g) y) = q.app d y := by
  have h2 := congrArg (fun t ↦ ((t.app m w).app d g) y) hs
  exact h2

/-- The lifted filler has cocartesian horizontal edges at every parameter vertex. -/
private theorem filler_cocartesian (A B E : SSet.{u}) (p : E ⟶ B) (q : A ⟶ B)
    (n : ℕ) (i : Fin (n + 3)) (σ₀ : (Λ[n + 2, i] : SSet.{u}) ⟶ sectionsOver p q)
    (s : Δ[n + 2] ⟶ mapping A E)
    (hleft : Λ[n + 2, i].ι ≫ s = σ₀ ≫ (sectionSubcomplexOver p q).ι)
    (m : SimplexCategoryᵒᵖ) (w : Δ[n + 2].obj m) (j : Fin (m.unop.len + 1))
    (e : A _⦋1⦌) :
    IsCocartesianEdge p (((s.app m w).app (op ⦋1⦌) (vertexParameter m j)) e) := by
  obtain ⟨lam, hlam⟩ : ∃ lam : (Λ[n + 2, i] : SSet.{u}) _⦋0⦌,
      Λ[n + 2, i].ι.app _ lam =
        Δ[n + 2].map (SimplexCategory.const ⦋0⦌ m.unop j).op w :=
    ⟨⟨Δ[n + 2].map (SimplexCategory.const ⦋0⦌ m.unop j).op w, by simp⟩, rfl⟩
  have hnat : s.app (op ⦋0⦌) (Δ[n + 2].map (SimplexCategory.const ⦋0⦌ m.unop j).op w) =
      (mapping A E).map (SimplexCategory.const ⦋0⦌ m.unop j).op (s.app m w) :=
    congrArg (fun t ↦ t w)
      (s.naturality (SimplexCategory.const ⦋0⦌ m.unop j).op)
  have hfac : s.app (op ⦋0⦌) (Λ[n + 2, i].ι.app (op ⦋0⦌) lam) =
      (σ₀.app (op ⦋0⦌) lam).val :=
    congrArg (fun t : (Λ[n + 2, i] : SSet.{u}) ⟶ mapping A E ↦
      t.app (op ⦋0⦌) lam) hleft
  have hvertex : (mapping A E).map (SimplexCategory.const ⦋0⦌ m.unop j).op (s.app m w) =
      (σ₀.app (op ⦋0⦌) lam).val := by
    rw [← hnat, ← hlam]
    exact hfac
  rw [app_vertexParameter, hvertex]
  exact (σ₀.app (op ⦋0⦌) lam).property.2 ⟨0, by decide⟩ e

/-- For quasicategories `A`, `B` and `E`, a cocartesian fibration `p : E ⟶ B` and a map
`q : A ⟶ B`, the simplicial set of cocartesian sections of `p` over `q` is a quasicategory. -/
public theorem native_cocartesian_section_quasicategory (A B E : SSet.{u})
    [SSet.Quasicategory A] [SSet.Quasicategory B] [SSet.Quasicategory E]
    (p : E ⟶ B) (q : A ⟶ B) (P : CocartesianFibration p) :
  SSet.Quasicategory (sectionsOver p q) := by
  have hP := P.inner
  refine { hornFilling' := fun {n i} σ₀ h0 hn ↦ ?_ }
  have hsq : (σ₀ ≫ (sectionSubcomplexOver p q).ι) ≫ (ihom A).map p =
      Λ[n + 2, i].ι ≫ constMap A B q (n + 2) :=
    horn_over A B E p q n i σ₀
  have hlp : HasLiftingProperty Λ[n + 2, i].ι ((ihom A).map p) :=
    SSet.mem_innerFibrations ((ihom A).map p) _
      (SSet.horn_ι_mem_innerHornInclusions h0 hn)
  have hH : (CommSq.mk hsq).HasLift := hlp.sq_hasLift (CommSq.mk hsq)
  let s : Δ[n + 2] ⟶ mapping A E := (CommSq.mk hsq).lift
  have hfac_left : Λ[n + 2, i].ι ≫ s = σ₀ ≫ (sectionSubcomplexOver p q).ι :=
    (CommSq.mk hsq).fac_left
  have hfac_right : s ≫ (ihom A).map p = constMap A B q (n + 2) :=
    (CommSq.mk hsq).fac_right
  have hrange : SSet.Subcomplex.range s ≤ sectionSubcomplexOver p q := by
    rw [Subfunctor.le_def]
    intro m w hw
    rw [Subfunctor.range_obj] at hw
    obtain ⟨w', rfl⟩ := hw
    refine ⟨fun d g y ↦ filler_over A B E p q n s hfac_right m d w' g y, ?_⟩
    intro j e
    exact filler_cocartesian A B E p q n i σ₀ s hfac_left m w' j e
  refine ⟨SSet.Subcomplex.lift s hrange, ?_⟩
  ext m lam
  apply Subtype.ext
  have hfac : ((Λ[n + 2, i].ι ≫ s).app m lam) =
      ((σ₀ ≫ (sectionSubcomplexOver p q).ι).app m lam) := by rw [hfac_left]
  exact hfac.symm
