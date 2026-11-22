/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Avocado
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# Quotient presentation of geometric realization

The realization of a simplicial set is the quotient of the sigma of its
nondegenerate simplices and their realized standard simplices. This neutral
provider requires neither finiteness nor a generated-topology specialization.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopCat
open scoped Simplicial

namespace SSet

noncomputable def sigmaToTop (T : SSet.{u}) :
    (Σ s : T.N, Convexity.StdSimplex ℝ (Fin (s.dim + 1))) → SSet.toTop.obj T :=
  fun ⟨s, x⟩ =>
    SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)
      ((SimplexCategory.toTopHomeo (⦋s.dim⦌)).symm x)

private lemma continuous_sigmaToTop (T : SSet.{u}) :
    Continuous (sigmaToTop (T := T)) := by
  apply continuous_sigma
  intro s
  dsimp [sigmaToTop]
  apply Continuous.comp
  · exact (SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)).hom.continuous
  · exact (SimplexCategory.toTopHomeo (⦋s.dim⦌)).symm.continuous
/-- Every point of the geometric realization has a presentation by a
nondegenerate simplex and a point of the corresponding realized standard
simplex.

This factors the surjectivity half of the compactness argument into a reusable
provider that hides the tautological-cocone presentation. It will be used next
with `T = SSet.boundary n` to discharge the realized-boundary factorization in
`SSetRealizationCellInterior`; no boundary-factorization result is claimed here. -/
theorem exists_nonDegenerate_toTop_presentation (T : SSet.{u})
    (x : SSet.toTop.obj T) :
    ∃ (n : ℕ) (s : T _⦋n⦌) (_ : s ∈ T.nonDegenerate n)
      (y : SSet.toTop.obj (SSet.stdSimplex.obj ⦋n⦌)),
      SSet.toTop.map (SSet.yonedaEquiv.symm s) y = x := by
  let c := Presheaf.tautologicalCocone' (C := SimplexCategory) (P := T)
  have hc : IsColimit c := Presheaf.isColimitTautologicalCocone' T
  have hcTop : IsColimit (SSet.toTop.mapCocone c) :=
    isColimitOfPreserves SSet.toTop hc
  have hcType : IsColimit ((SSet.toTop ⋙ forget TopCat).mapCocone c) :=
    isColimitOfPreserves (forget TopCat) hcTop
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hcType x
  let s : T _⦋j.left.len⦌ := CategoryTheory.uliftYonedaEquiv (C := SimplexCategory) j.hom
  have hjEq : j.hom = CategoryTheory.uliftYonedaEquiv.symm s := by
    simp [s]
  obtain ⟨m, f, _hf, t, hs⟩ := T.exists_nonDegenerate s
  let yStd : Convexity.StdSimplex ℝ (Fin (j.left.len + 1)) :=
    (SimplexCategory.toTopHomeo j.left) (y)
  refine ⟨m, t.val, t.property,
    (SimplexCategory.toTopHomeo ⦋m⦌).symm (Convexity.StdSimplex.map f yStd), ?_⟩
  have h1 : (SSet.toTop.map j.hom) y = x := hy
  have h2 : SSet.toTop.map (SSet.yonedaEquiv.symm t.val)
      ((SimplexCategory.toTopHomeo (⦋m⦌)).symm (Convexity.StdSimplex.map f yStd))
      = SSet.toTop.map (SSet.yonedaEquiv.symm s) y := by
    calc SSet.toTop.map (SSet.yonedaEquiv.symm t.val)
          ((SimplexCategory.toTopHomeo (⦋m⦌)).symm (Convexity.StdSimplex.map f yStd))
        = SSet.toTop.map (SSet.yonedaEquiv.symm t)
          ((SimplexCategory.toTopHomeo (⦋m⦌)).symm (Convexity.StdSimplex.map f yStd)) := rfl
      _ = SSet.toTop.map (SSet.yonedaEquiv.symm t)
          (SSet.toTop.map (SSet.stdSimplex.map f)
              ((SimplexCategory.toTopHomeo j.left).symm yStd)) := by
        rw [SimplexCategory.toTopHomeo_symm_naturality_apply]
      _ = (SSet.toTop.map (SSet.stdSimplex.map f) ≫
            SSet.toTop.map (SSet.yonedaEquiv.symm t))
          ((SimplexCategory.toTopHomeo j.left).symm yStd) := rfl
      _ = SSet.toTop.map (SSet.stdSimplex.map f ≫ SSet.yonedaEquiv.symm t)
          ((SimplexCategory.toTopHomeo j.left).symm yStd) := by
        rw [← SSet.toTop.map_comp]
      _ = SSet.toTop.map (SSet.yonedaEquiv.symm (T.map f.op t))
          ((SimplexCategory.toTopHomeo j.left).symm yStd) := by
        rw [SSet.yonedaEquiv_symm_naturality_left]
      _ = SSet.toTop.map (SSet.yonedaEquiv.symm s)
          ((SimplexCategory.toTopHomeo j.left).symm yStd) := by
        rw [← hs]
      _ = SSet.toTop.map (SSet.yonedaEquiv.symm s) y := by
        have : (SimplexCategory.toTopHomeo j.left).symm yStd = y :=
          Homeomorph.symm_apply_apply (SimplexCategory.toTopHomeo j.left) y
        rw [this]
  have h3 : SSet.toTop.map (SSet.yonedaEquiv.symm s) y
      = SSet.toTop.map j.hom y := by
    rw [hjEq]
    rfl
  exact h2.trans (h3.trans h1)

lemma surjective_sigmaToTop (T : SSet.{u}) :
    Function.Surjective (sigmaToTop (T := T)) := by
  intro x
  obtain ⟨n, s, hs, y, hy⟩ := exists_nonDegenerate_toTop_presentation T x
  refine ⟨⟨N.mk s hs, (SimplexCategory.toTopHomeo ⦋n⦌) y⟩, ?_⟩
  change SSet.toTop.map (SSet.yonedaEquiv.symm s)
      ((SimplexCategory.toTopHomeo ⦋n⦌).symm ((SimplexCategory.toTopHomeo ⦋n⦌) y)) = x
  rw [Homeomorph.symm_apply_apply]
  exact hy

/-- The nondegenerate-simplex sigma presentation maps onto geometric
realization as a quotient map.  This is universe-polymorphic and requires no
finiteness, compactness, separation, nonsingularity, Kan, or model-category
hypothesis. -/
theorem isQuotientMap_sigmaToTop (T : SSet.{u}) :
    Topology.IsQuotientMap (sigmaToTop (T := T)) := by
  refine ⟨?_, surjective_sigmaToTop T⟩
  · apply Topology.IsCoinducing.of_isOpen_preimage_iff_isOpen
    intro U
    refine ⟨fun hOpen => ?_, fun hU => hU.preimage (continuous_sigmaToTop T)⟩
    let c := Presheaf.tautologicalCocone' (C := SimplexCategory) (P := T)
    have hc : IsColimit c := Presheaf.isColimitTautologicalCocone' T
    have hcTop : IsColimit (SSet.toTop.mapCocone c) :=
      isColimitOfPreserves SSet.toTop hc
    apply (TopCat.isOpen_iff_of_isColimit (SSet.toTop.mapCocone c) hcTop
      (show Set ((SSet.toTop.mapCocone c).pt) from U)).mpr
    intro j
    let s : T _⦋j.left.len⦌ := CategoryTheory.uliftYonedaEquiv j.hom
    obtain ⟨m, f, _hf, t, hs⟩ := T.exists_nonDegenerate s
    let s0 : T.N := N.mk (t : T _⦋m⦌) t.property
    have hj : j.hom = CategoryTheory.uliftYonedaEquiv.symm s := by
      simp [s]
    have hYeq :
        CategoryTheory.uliftYonedaEquiv.symm (T.map f.op (t : T _⦋m⦌)) =
          SSet.yonedaEquiv.symm (T.map f.op (t : T _⦋m⦌)) := rfl
    have hjY : j.hom = SSet.yonedaEquiv.symm (T.map f.op (t : T _⦋m⦌)) := by
      rw [hj, hs]
      exact hYeq
    have hMap : SSet.toTop.map j.hom =
        SSet.toTop.map (SSet.stdSimplex.map f) ≫
          SSet.toTop.map (SSet.yonedaEquiv.symm (t : T _⦋m⦌)) := by
      rw [hjY, ← SSet.yonedaEquiv_symm_naturality_left]
      exact Functor.map_comp _ _ _
    have hLeg : (SSet.toTop.mapCocone c).ι.app j = SSet.toTop.map j.hom := rfl
    let fiberIncl : Convexity.StdSimplex ℝ (Fin (m + 1)) →
        (Σ s : T.N, Convexity.StdSimplex ℝ (Fin (s.dim + 1))) :=
      fun x => ⟨s0, x⟩
    have hfiberCont : Continuous fiberIncl := by
      have h : Continuous
          (fun x : Convexity.StdSimplex ℝ (Fin (m + 1)) =>
            (⟨s0, x⟩ : Σ s : T.N, Convexity.StdSimplex ℝ (Fin (s.dim + 1)))) :=
        (continuous_sigmaMk (ι := T.N)
          (σ := fun s : T.N => Convexity.StdSimplex ℝ (Fin (s.dim + 1))) (i := s0)).congr
          (fun x => rfl)
      simpa only [fiberIncl] using h
    have hFiberOpen : IsOpen (fiberIncl ⁻¹' ((sigmaToTop (T := T)) ⁻¹' U)) :=
      hOpen.preimage hfiberCont
    have hPt : ∀ x : Convexity.StdSimplex ℝ (Fin (m + 1)),
        (sigmaToTop (T := T)) (fiberIncl x) =
          SSet.toTop.map (SSet.yonedaEquiv.symm (t : T _⦋m⦌))
            ((SimplexCategory.toTopHomeo ⦋m⦌).symm x) := fun x => rfl
    have hFiberEq :
        (SSet.toTop.map (SSet.yonedaEquiv.symm (t : T _⦋m⦌)) ⁻¹' U) =
          ((SimplexCategory.toTopHomeo ⦋m⦌) ⁻¹' (fiberIncl ⁻¹'
            ((sigmaToTop (T := T)) ⁻¹' U))) := by
      ext y
      simp only [Set.mem_preimage]
      constructor
      · intro hy
        have hEq : (sigmaToTop (T := T)) (fiberIncl ((SimplexCategory.toTopHomeo ⦋m⦌) y)) =
            SSet.toTop.map (SSet.yonedaEquiv.symm (t : T _⦋m⦌)) y := by
          rw [hPt, Homeomorph.symm_apply_apply]
        rw [hEq]
        exact hy
      · intro hy
        have hEq : (sigmaToTop (T := T)) (fiberIncl ((SimplexCategory.toTopHomeo ⦋m⦌) y)) =
            SSet.toTop.map (SSet.yonedaEquiv.symm (t : T _⦋m⦌)) y := by
          rw [hPt, Homeomorph.symm_apply_apply]
        rw [← hEq]
        exact hy
    have hBOpen :
        IsOpen (SSet.toTop.map (SSet.yonedaEquiv.symm (t : T _⦋m⦌)) ⁻¹' U) := by
      rw [hFiberEq]
      exact hFiberOpen.preimage (SimplexCategory.toTopHomeo ⦋m⦌).continuous
    rw [hLeg, hMap]
    exact hBOpen.preimage (SSet.toTop.map (SSet.stdSimplex.map f)).hom.continuous

end SSet
