/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryDesc
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteMultiequalizer
public import Mathlib.Data.Finset.BooleanAlgebra
public import MathlibExt.Topology.Category.TopCat.Embedding.ClosedT1Embedding
public import MathlibExt.Topology.Category.TopCat.Colimits.FiniteClosedColimit
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizedBoundaryZeroRangeEmpty
public import MathlibExt.Analysis.Convex.StdSimplex

/-!
# Boundary realizations and their face coordinates

The simplicial boundary `∂Δ[n]` is the union of the codimension-one faces `face {i}ᶜ`. Its
multicoequalizer diagram uses those faces and the pair intersections `face {i,j}ᶜ`. Geometric
realization preserves the diagram's colimit, and every leg of the resulting cocone is a closed
embedding.

The realized boundary inclusion `|∂Δ[n]| → |Δ[n]|` is a closed T1-embedding. Every point of
its image comes from a codimension-one face and therefore has a zero barycentric coordinate
under the standard-simplex homeomorphism. Equal images from two distinct faces lift to the
realization of their pair intersection.
-/

@[expose] public section

universe u

open CategoryTheory Limits Simplicial TopCat

namespace SSet

namespace boundary

variable (n : ℕ)

/-- For `n : ℕ` and universe `u`, the boundary `SSet.boundary.{u} n` has the subcomplex
multicoequalizer diagram with faces `U_i=SSet.stdSimplex.face.{u} (n := n) {i}ᶜ` for `i : Fin
(n+1)` and intersections `V_{i,j}=face {i,j}ᶜ`. The diagram glues these codimension-one faces
along their pairwise intersections. -/
@[deprecated multicoequalizerDiagram (since := "2026-10-22")]
theorem realizationMulticoequalizerDiagram :
    Subcomplex.MulticoequalizerDiagram (SSet.boundary.{u} n)
      (fun i : Fin (n + 1) => SSet.stdSimplex.face.{u} (n := n) {i}ᶜ)
      (fun i j : Fin (n + 1) => SSet.stdSimplex.face.{u} (n := n) {i, j}ᶜ) :=
  multicoequalizerDiagram n

/-- For `n : ℕ` and universe `u`, the cocone obtained by realizing the linear-order multicofork of
`multicoequalizerDiagram n`, after mapping its subcomplexes to simplicial sets, is colimiting
in `TopCat`. Its apex is the realization of `∂Δ[n]`; the realization functor preserves this
boundary colimit. -/
noncomputable def isColimitToTop' :
    IsColimit
      (SSet.toTop.{u}.mapCocone
        ((multicoequalizerDiagram n).multicofork.toLinearOrder.map
          Subcomplex.toSSetFunctor)) :=
  isColimitOfPreserves SSet.toTop.{u} (boundary.isColimit n)

end boundary

end SSet

namespace SSet

namespace boundary

private def emptyFace_isInitialBot (n : ℕ) :
    IsInitial ((⊥ : (SSet.stdSimplex.obj ⦋n⦌ : SSet.{u}).Subcomplex) : SSet.{u}) :=
  SSet.Subcomplex.isInitialBot

private def botSubcomplex (n : ℕ) : (SSet.stdSimplex.obj ⦋n⦌ : SSet.{u}).Subcomplex := ⊥

private noncomputable def botSSet (n : ℕ) : SSet.{u} :=
  (botSubcomplex (n := n) : SSet.{u})

private noncomputable def botTop (n : ℕ) : TopCat.{u} :=
  SSet.toTop.obj (botSSet (n := n))

private lemma isClosedEmbedding_realizedFaceInclusion (n : ℕ) (i : Fin (n + 1)) :
    Topology.IsClosedEmbedding (SSet.toTop.{u}.map (SSet.stdSimplex.face (n := n) {i}ᶜ).ι) := by
  cases n with
  | zero =>
    -- For `n = 0`, `Fin 1` has the unique element `0`; then `{i}ᶜ = ∅`
    -- and `face ∅ = ⊥`. The realized inclusion `|⊥| → |Δ[0]|` is the
    -- initial map `∅ → point`, a closed embedding.
    have hi : i = 0 := by
      have h0 : i.val = 0 := by
        have := i.isLt
        omega
      exact Fin.ext h0
    subst hi
    have h_compl : (({(0 : Fin 1)}ᶜ : Finset (Fin 1)) = ∅) := by
      ext x
      simp only [Finset.mem_compl, Finset.mem_singleton, Finset.notMem_empty]
      have hx : x = 0 := by
        have : x.val = 0 := by
          have := x.isLt
          omega
        exact Fin.ext this
      simp [hx]
    have h_face : SSet.stdSimplex.face (n := 0) ({(0 : Fin 1)}ᶜ : Finset (Fin 1)) = ⊥ := by
      rw [h_compl, SSet.stdSimplex.face_empty]
    rw [h_face]
    have hInitSSet : IsInitial (botSSet (n := 0) : SSet.{u}) := emptyFace_isInitialBot 0
    have hInitTop : IsInitial (botTop (n := 0) : TopCat.{u}) :=
      hInitSSet.isInitialObj (G := SSet.toTop.{u})
    have hIso : botTop (n := 0) ≅ (TopCat.of PEmpty : TopCat.{u}) :=
      hInitTop.uniqueUpToIso TopCat.isInitialPEmpty
    have hElim : ∀ x : ↑(botTop (n := 0) : TopCat.{u}), False := fun x =>
      PEmpty.elim ((TopCat.homeoOfIso hIso) x)
    refine Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
      (by fun_prop) (fun x => (hElim x).elim) ?_
    intro s hs
    have : s = ∅ := by
      ext x
      exact (hElim x).elim
    rw [this, Set.image_empty]
    exact isClosed_empty
  | succ n =>
    have hEq : SSet.toTop.map (SSet.stdSimplex.face (n := n + 1) {i}ᶜ).ι =
        SSet.toTop.map (SSet.stdSimplex.faceSingletonComplIso (n := n) i).inv ≫
          SSet.toTop.map (SSet.stdSimplex.δ (n := n) i) := by
      have h := SSet.stdSimplex.faceSingletonComplIso_hom_ι (n := n) (i := i)
      calc SSet.toTop.map (SSet.stdSimplex.face (n := n + 1) {i}ᶜ).ι
          = SSet.toTop.map ((SSet.stdSimplex.faceSingletonComplIso (n := n) i).inv ≫
              (SSet.stdSimplex.faceSingletonComplIso (n := n) i).hom ≫
                (SSet.stdSimplex.face (n := n + 1) {i}ᶜ).ι) := by
                simp only [Iso.inv_hom_id_assoc]
        _ = SSet.toTop.map ((SSet.stdSimplex.faceSingletonComplIso (n := n) i).inv ≫
              SSet.stdSimplex.δ (n := n) i) := by rw [h]
        _ = SSet.toTop.map (SSet.stdSimplex.faceSingletonComplIso (n := n) i).inv ≫
              SSet.toTop.map (SSet.stdSimplex.δ (n := n) i) := by
                rw [Functor.map_comp]
    let hHomeo_n : SSet.toTop.obj Δ[n] ≃ₜ Convexity.StdSimplex ℝ (Fin (n + 1)) :=
      SimplexCategory.toTopHomeo (SimplexCategory.mk n)
    let hHomeo_succ : SSet.toTop.obj Δ[n + 1] ≃ₜ Convexity.StdSimplex ℝ (Fin (n + 2)) :=
      SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1))
    have hδ_eq : ⇑(SSet.toTop.map (SSet.stdSimplex.δ (n := n) i)) =
        ⇑hHomeo_succ.symm ∘ (Convexity.StdSimplex.map (Fin.succAbove i) : _ → _) ∘ ⇑hHomeo_n := by
      funext x
      have h_nat :
          hHomeo_succ ((ConcreteCategory.hom (SSet.toTop.map (SSet.stdSimplex.δ (n := n) i))) x) =
          (Convexity.StdSimplex.map (Fin.succAbove i)) (hHomeo_n x) := by
        have h_fun : (hHomeo_succ : _ → _) ∘ ⇑(SSet.toTop.map (SSet.stdSimplex.δ (n := n) i)) =
            (Convexity.StdSimplex.map (Fin.succAbove i) : _ → _) ∘ ⇑hHomeo_n := by
            have h1 :
                (SSet.stdSimplex.δ.{u} (n := n) i : Δ[n] ⟶ Δ[n + 1]) =
                SSet.stdSimplex.{u}.map (SimplexCategory.δ (n := n) i) := rfl
            have h2 :
                (⇑(SimplexCategory.δ (n := n) i) : Fin (n + 1) → Fin (n + 2)) =
                Fin.succAbove i := rfl
            have h_nat' :
                (SimplexCategory.toTopHomeo.{u} (SimplexCategory.mk (n + 1)) : SSet.toTop.{u}.obj
                Δ[n + 1] → Convexity.StdSimplex ℝ (Fin (n + 2))) ∘
                ⇑(SSet.toTop.{u}.map (SSet.stdSimplex.{u}.map (SimplexCategory.δ (n := n) i))) =
                (Convexity.StdSimplex.map (Fin.succAbove i) : _ → _) ∘
                ⇑(SimplexCategory.toTopHomeo.{u} (SimplexCategory.mk n)) := by
              simpa [h1, h2] using SimplexCategory.toTopHomeo_naturality (f :=
                  SimplexCategory.δ (n := n) i)
            change (hHomeo_succ : _ → _) ∘ ⇑(SSet.toTop.map (SSet.stdSimplex.δ (n := n) i)) =
                (Convexity.StdSimplex.map (Fin.succAbove i) : _ → _) ∘ ⇑hHomeo_n
            change (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1)) : _ → _) ∘
                ⇑(SSet.toTop.map (SSet.stdSimplex.δ (n := n) i)) =
                (Convexity.StdSimplex.map (Fin.succAbove i) : _ → _) ∘
                ⇑(SimplexCategory.toTopHomeo (SimplexCategory.mk n)) at h_nat'
            exact h_nat'
        exact congr_fun h_fun x
      apply hHomeo_succ.injective
      simpa only [Function.comp_apply, Homeomorph.apply_symm_apply] using h_nat
    have hEq_fun : ⇑(SSet.toTop.map (SSet.stdSimplex.face (n := n + 1) {i}ᶜ).ι) =
        ⇑hHomeo_succ.symm ∘ (Convexity.StdSimplex.map (Fin.succAbove i) : _ → _) ∘ ⇑hHomeo_n ∘
          ⇑(SSet.toTop.map (SSet.stdSimplex.faceSingletonComplIso (n := n) i).inv) := by
      funext x
      apply hHomeo_succ.injective
      have h1 := ConcreteCategory.congr_hom hEq x
      simp only [CategoryTheory.comp_apply] at h1 ⊢
      rw [h1]
      have h2 := congr_fun hδ_eq (SSet.toTop.map (SSet.stdSimplex.faceSingletonComplIso (n :=
          n) i).inv x)
      simp only [Function.comp_apply] at h2 ⊢
      rw [h2]
    rw [hEq_fun]
    have hCoord : Topology.IsClosedEmbedding
        (Convexity.StdSimplex.map (R := ℝ) (Fin.succAbove i)) :=
      Convexity.StdSimplex.isClosedEmbedding_map_succAbove i
    have hHomeo_n_emb : Topology.IsClosedEmbedding (⇑hHomeo_n : _ → _) :=
      Homeomorph.isClosedEmbedding hHomeo_n
    have hHomeo_succ_emb : Topology.IsClosedEmbedding (⇑hHomeo_succ.symm : _ → _) :=
      Homeomorph.isClosedEmbedding hHomeo_succ.symm
    have hIso_emb :
        Topology.IsClosedEmbedding (SSet.toTop.map (SSet.stdSimplex.faceSingletonComplIso (n :=
        n) i).inv) :=
      (TopCat.homeoOfIso (SSet.toTop.mapIso (SSet.stdSimplex.faceSingletonComplIso (n :=
          n) i |>.symm))).isClosedEmbedding
    exact (hHomeo_succ_emb.comp (hCoord.comp hHomeo_n_emb)).comp hIso_emb

private lemma isClosedEmbedding_realizedFacePair (n : ℕ) (i j : Fin (n + 1)) (h : i < j) :
    Topology.IsClosedEmbedding (SSet.toTop.{u}.map (SSet.stdSimplex.face (n := n) {i, j}ᶜ).ι) := by
  cases n with
  | zero =>
    have hi : i.val < 1 := i.isLt
    have hj : j.val < 1 := j.isLt
    have hij : i.val < j.val := h
    omega
  | succ n =>
    cases n with
    | zero =>
      have h_pair : (({i, j} : Finset (Fin 2)) = Finset.univ) := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ, iff_true]
        have hi0 : i = 0 := by
          have : i.val = 0 := by
            have hiLt : i.val < 2 := i.isLt
            have hjLt : j.val < 2 := j.isLt
            have hij : i.val < j.val := h
            omega
          exact Fin.ext this
        have hj1 : j = 1 := by
          have : j.val = 1 := by
            have hiLt : i.val < 2 := i.isLt
            have hjLt : j.val < 2 := j.isLt
            have hij : i.val < j.val := h
            omega
          exact Fin.ext this
        simp [hi0, hj1]
        omega
      have h_compl : (({i, j}ᶜ : Finset (Fin 2)) = ∅) := by
        rw [h_pair, Finset.compl_univ]
      have h_face : SSet.stdSimplex.face (n := 1) ({i, j}ᶜ) = ⊥ := by
        rw [h_compl, SSet.stdSimplex.face_empty]
      rw [h_face]
      have hInitSSet : IsInitial (botSSet (n := 1) : SSet.{u}) := emptyFace_isInitialBot 1
      have hInitTop : IsInitial (botTop (n := 1) : TopCat.{u}) :=
        hInitSSet.isInitialObj (G := SSet.toTop.{u})
      have hIso : botTop (n := 1) ≅ (TopCat.of PEmpty : TopCat.{u}) :=
        hInitTop.uniqueUpToIso TopCat.isInitialPEmpty
      have hElim : ∀ x : ↑(botTop (n := 1) : TopCat.{u}), False := fun x =>
        PEmpty.elim ((TopCat.homeoOfIso hIso) x)
      refine Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
        (by fun_prop) (fun x => (hElim x).elim) ?_
      intro s hs
      have : s = ∅ := by
        ext x
        exact (hElim x).elim
      rw [this, Set.image_empty]
      exact isClosed_empty
    | succ n =>
      have hEq : SSet.toTop.map (SSet.stdSimplex.face (n := n + 2) {i, j}ᶜ).ι =
          SSet.toTop.map (SSet.stdSimplex.facePairComplIso (n := n) i j h).inv ≫
            SSet.toTop.map (SSet.stdSimplex.δ (n := n) (i.castPred (Fin.ne_last_of_lt h))) ≫
              SSet.toTop.map (SSet.stdSimplex.δ (n := n + 1) j) := by
        have h' := SSet.stdSimplex.facePairComplIso_hom_ι (n := n) (i := i) (j := j) (h := h)
        calc SSet.toTop.map (SSet.stdSimplex.face (n := n + 2) {i, j}ᶜ).ι
            = SSet.toTop.map ((SSet.stdSimplex.facePairComplIso (n := n) i j h).inv ≫
                (SSet.stdSimplex.facePairComplIso (n := n) i j h).hom ≫
                  (SSet.stdSimplex.face (n := n + 2) {i, j}ᶜ).ι) := by
                simp only [Iso.inv_hom_id_assoc]
          _ = SSet.toTop.map ((SSet.stdSimplex.facePairComplIso (n := n) i j h).inv ≫
                (SSet.stdSimplex.δ (n := n) (i.castPred (Fin.ne_last_of_lt h)) ≫
                    SSet.stdSimplex.δ (n := n + 1) j)) := by rw [h']
          _ = SSet.toTop.map (SSet.stdSimplex.facePairComplIso (n := n) i j h).inv ≫
                SSet.toTop.map (SSet.stdSimplex.δ (n := n) (i.castPred (Fin.ne_last_of_lt h))) ≫
                  SSet.toTop.map (SSet.stdSimplex.δ (n := n + 1) j) := by
                simp only [Functor.map_comp]
      let hHomeo_n : SSet.toTop.obj Δ[n] ≃ₜ Convexity.StdSimplex ℝ (Fin (n + 1)) :=
        SimplexCategory.toTopHomeo (SimplexCategory.mk n)
      let hHomeo_mid : SSet.toTop.obj Δ[n + 1] ≃ₜ Convexity.StdSimplex ℝ (Fin (n + 2)) :=
        SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1))
      let hHomeo_succ : SSet.toTop.obj Δ[n + 2] ≃ₜ Convexity.StdSimplex ℝ (Fin (n + 3)) :=
        SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 2))
      have hδ1_eq :
          ⇑(SSet.toTop.map (SSet.stdSimplex.δ (n := n) (i.castPred (Fin.ne_last_of_lt h)))) =
          ⇑hHomeo_mid.symm ∘
              (Convexity.StdSimplex.map (Fin.succAbove (i.castPred (Fin.ne_last_of_lt h))) : _ →
              _) ∘ ⇑hHomeo_n := by
        funext x
        have h_nat :
            hHomeo_mid ((ConcreteCategory.hom (SSet.toTop.map (SSet.stdSimplex.δ (n :=
            n) (i.castPred (Fin.ne_last_of_lt h))))) x) =
            (Convexity.StdSimplex.map (Fin.succAbove (i.castPred (Fin.ne_last_of_lt h)))) (hHomeo_n
                x) := by
          have h_fun :
              (hHomeo_mid : _ → _) ∘ ⇑(SSet.toTop.map (SSet.stdSimplex.δ (n :=
              n) (i.castPred (Fin.ne_last_of_lt h)))) =
              (Convexity.StdSimplex.map (Fin.succAbove (i.castPred (Fin.ne_last_of_lt h))) : _ →
                  _) ∘ ⇑hHomeo_n := by
            have h1 :
                (SSet.stdSimplex.δ.{u} (n :=
                n) (i.castPred (Fin.ne_last_of_lt h)) : Δ[n] ⟶ Δ[n + 1]) =
                SSet.stdSimplex.{u}.map (SimplexCategory.δ (n :=
                n) (i.castPred (Fin.ne_last_of_lt h))) := rfl
            have h2 :
                (⇑(SimplexCategory.δ (n :=
                n) (i.castPred (Fin.ne_last_of_lt h))) : Fin (n + 1) → Fin (n + 2)) =
                Fin.succAbove (i.castPred (Fin.ne_last_of_lt h)) := rfl
            have h_nat' :
                (SimplexCategory.toTopHomeo.{u} (SimplexCategory.mk (n + 1)) : SSet.toTop.{u}.obj
                Δ[n + 1] → Convexity.StdSimplex ℝ (Fin (n + 2))) ∘
                ⇑(SSet.toTop.{u}.map (SSet.stdSimplex.{u}.map (SimplexCategory.δ (n :=
                n) (i.castPred (Fin.ne_last_of_lt h))))) =
                (Convexity.StdSimplex.map (Fin.succAbove (i.castPred (Fin.ne_last_of_lt h))) : _ →
                _) ∘ ⇑(SimplexCategory.toTopHomeo.{u} (SimplexCategory.mk n)) := by
              simpa [h1, h2] using SimplexCategory.toTopHomeo_naturality (f :=
                  SimplexCategory.δ (n := n) (i.castPred (Fin.ne_last_of_lt h)))
            change (hHomeo_mid : _ → _) ∘ ⇑(SSet.toTop.map (SSet.stdSimplex.δ (n :=
                n) (i.castPred (Fin.ne_last_of_lt h)))) =
                (Convexity.StdSimplex.map (Fin.succAbove (i.castPred (Fin.ne_last_of_lt h))) : _ →
                _) ∘ ⇑hHomeo_n
            change (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1)) : _ → _) ∘
                ⇑(SSet.toTop.map (SSet.stdSimplex.δ (n :=
                n) (i.castPred (Fin.ne_last_of_lt h)))) =
                (Convexity.StdSimplex.map (Fin.succAbove (i.castPred (Fin.ne_last_of_lt h))) : _ →
                _) ∘ ⇑(SimplexCategory.toTopHomeo (SimplexCategory.mk n)) at h_nat'
            exact h_nat'
          exact congr_fun h_fun x
        apply hHomeo_mid.injective
        simpa only [Function.comp_apply, Homeomorph.apply_symm_apply] using h_nat
      have hδ2_eq : ⇑(SSet.toTop.map (SSet.stdSimplex.δ (n := n + 1) j)) =
          ⇑hHomeo_succ.symm ∘ (Convexity.StdSimplex.map (Fin.succAbove j) : _ → _) ∘
              ⇑hHomeo_mid := by
        funext x
        have h_nat :
            hHomeo_succ ((ConcreteCategory.hom (SSet.toTop.map (SSet.stdSimplex.δ (n :=
            n + 1) j))) x) =
            (Convexity.StdSimplex.map (Fin.succAbove j)) (hHomeo_mid x) := by
          have h_fun :
              (hHomeo_succ : _ → _) ∘ ⇑(SSet.toTop.map (SSet.stdSimplex.δ (n := n + 1) j)) =
              (Convexity.StdSimplex.map (Fin.succAbove j) : _ → _) ∘ ⇑hHomeo_mid := by
            have h1 :
                (SSet.stdSimplex.δ.{u} (n := n + 1) j : Δ[n + 1] ⟶ Δ[n + 2]) =
                SSet.stdSimplex.{u}.map (SimplexCategory.δ (n := n + 1) j) := rfl
            have h2 :
                (⇑(SimplexCategory.δ (n := n + 1) j) : Fin (n + 2) → Fin (n + 3)) =
                Fin.succAbove j := rfl
            have h_nat' :
                (SimplexCategory.toTopHomeo.{u} (SimplexCategory.mk (n + 2)) : SSet.toTop.{u}.obj
                Δ[n + 2] → Convexity.StdSimplex ℝ (Fin (n + 3))) ∘
                ⇑(SSet.toTop.{u}.map (SSet.stdSimplex.{u}.map (SimplexCategory.δ (n :=
                n + 1) j))) = (Convexity.StdSimplex.map (Fin.succAbove j) : _ → _) ∘
                ⇑(SimplexCategory.toTopHomeo.{u} (SimplexCategory.mk (n + 1))) := by
              simpa [h1, h2] using SimplexCategory.toTopHomeo_naturality (f :=
                  SimplexCategory.δ (n := n + 1) j)
            change (hHomeo_succ : _ → _) ∘ ⇑(SSet.toTop.map (SSet.stdSimplex.δ (n :=
                n + 1) j)) = (Convexity.StdSimplex.map (Fin.succAbove j) : _ → _) ∘ ⇑hHomeo_mid
            change (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 2)) : _ → _) ∘
                ⇑(SSet.toTop.map (SSet.stdSimplex.δ (n := n + 1) j)) =
                (Convexity.StdSimplex.map (Fin.succAbove j) : _ → _) ∘
                ⇑(SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1))) at h_nat'
            exact h_nat'
          exact congr_fun h_fun x
        apply hHomeo_succ.injective
        simpa only [Function.comp_apply, Homeomorph.apply_symm_apply] using h_nat
      have hEq_fun : ⇑(SSet.toTop.map (SSet.stdSimplex.face (n := n + 2) {i, j}ᶜ).ι) =
          ⇑hHomeo_succ.symm ∘ (Convexity.StdSimplex.map (Fin.succAbove j) ∘
              Convexity.StdSimplex.map (Fin.succAbove (i.castPred (Fin.ne_last_of_lt h)))) ∘
            ⇑hHomeo_n ∘ ⇑(SSet.toTop.map (SSet.stdSimplex.facePairComplIso (n :=
                n) i j h).inv) := by
        funext x
        apply hHomeo_succ.injective
        have h1 := ConcreteCategory.congr_hom hEq x
        simp only [CategoryTheory.comp_apply, Function.comp_apply] at h1 ⊢
        rw [h1]
        have h2 := congr_fun hδ1_eq (SSet.toTop.map (SSet.stdSimplex.facePairComplIso (n :=
            n) i j h).inv x)
        have h3 := congr_fun hδ2_eq (SSet.toTop.map (SSet.stdSimplex.δ (n :=
            n) (i.castPred (Fin.ne_last_of_lt h))) (SSet.toTop.map (SSet.stdSimplex.facePairComplIso
            (n := n) i j h).inv x))
        simp only [Function.comp_apply, Homeomorph.apply_symm_apply] at h2 h3 ⊢
        rw [h3]
        simp only [h2, Homeomorph.apply_symm_apply]
      rw [hEq_fun]
      have hCoord1 : Topology.IsClosedEmbedding
          (Convexity.StdSimplex.map (R := ℝ) (Fin.succAbove (i.castPred (Fin.ne_last_of_lt h)))) :=
        Convexity.StdSimplex.isClosedEmbedding_map_succAbove _
      have hCoord2 : Topology.IsClosedEmbedding
          (Convexity.StdSimplex.map (R := ℝ) (Fin.succAbove j)) :=
        Convexity.StdSimplex.isClosedEmbedding_map_succAbove j
      have hIso_emb :
          Topology.IsClosedEmbedding (SSet.toTop.map (SSet.stdSimplex.facePairComplIso (n :=
          n) i j h).inv) :=
        (TopCat.homeoOfIso (SSet.toTop.mapIso (SSet.stdSimplex.facePairComplIso (n :=
            n) i j h |>.symm))).isClosedEmbedding
      have hHomeo_n_emb : Topology.IsClosedEmbedding (hHomeo_n : _ → _) :=
        Homeomorph.isClosedEmbedding hHomeo_n
      have hHomeo_succ_emb : Topology.IsClosedEmbedding (hHomeo_succ.symm : _ → _) :=
        Homeomorph.isClosedEmbedding hHomeo_succ.symm
      -- The pair face inclusion is `hHomeo_succ.symm ∘ (StdSimplex.map (succAbove j) ∘
      -- StdSimplex.map (succAbove i.castPred)) ∘ hHomeo_n ∘ isoInv`
      -- after cancelling the middle `hHomeo_mid` terms; this is a composite of closed embeddings.
      have hPairCoord : Topology.IsClosedEmbedding
          (Convexity.StdSimplex.map (R := ℝ) (Fin.succAbove j) ∘ Convexity.StdSimplex.map (R :=
              ℝ) (Fin.succAbove (i.castPred (Fin.ne_last_of_lt h)))) :=
        hCoord2.comp hCoord1
      have hTotal : Topology.IsClosedEmbedding
          ((hHomeo_succ.symm : _ → _) ∘ (Convexity.StdSimplex.map (Fin.succAbove j) ∘
              Convexity.StdSimplex.map (Fin.succAbove (i.castPred (Fin.ne_last_of_lt h))) ) ∘
              (hHomeo_n : _ → _)) :=
        hHomeo_succ_emb.comp (hPairCoord.comp hHomeo_n_emb)
      exact hTotal.comp hIso_emb

/-- Let `n : ℕ`, `i : Fin (n+2)`, and `p` lie in the realization of `face (n := n+1) {i}ᶜ :
SSet.{u}`. Let `w : Convexity.StdSimplex ℝ (Fin (n+2))` equal the image of `p` under the
realized face inclusion followed by `SimplexCategory.toTopHomeo ⦋n+1⦌`. Then `w.weights i=0`. -/
lemma singleton_face_coord_zero {n : ℕ} (i : Fin (n + 2))
    (p : SSet.toTop.obj (SSet.stdSimplex.face (n := n + 1) {i}ᶜ : SSet.{u}))
    (w : Convexity.StdSimplex ℝ (Fin (n + 2)))
    (hw : w = (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1)))
        (SSet.toTop.map (SSet.stdSimplex.face (n := n + 1) {i}ᶜ).ι p)) :
    w.weights i = 0 := by
  have h_range : w ∈ Set.range (Convexity.StdSimplex.map (R := ℝ) (Fin.succAbove i)) := by
    let e := SSet.stdSimplex.faceSingletonComplIso (n := n) i
    have hEq :
        (SSet.stdSimplex.face (n := n + 1) {i}ᶜ).ι = e.inv ≫ SSet.stdSimplex.δ (n :=
        n) i := by
      calc (SSet.stdSimplex.face (n := n + 1) {i}ᶜ).ι
          = e.inv ≫ e.hom ≫ (SSet.stdSimplex.face (n := n + 1) {i}ᶜ).ι := by simp
        _ = e.inv ≫ SSet.stdSimplex.δ (n :=
            n) i := by rw [SSet.stdSimplex.faceSingletonComplIso_hom_ι]
    have hEqTop : SSet.toTop.map (SSet.stdSimplex.face (n := n + 1) {i}ᶜ).ι =
        SSet.toTop.map e.inv ≫ SSet.toTop.map (SSet.stdSimplex.δ (n := n) i) := by
      rw [hEq, Functor.map_comp]
    have hEqFun : SSet.toTop.map (SSet.stdSimplex.face (n := n + 1) {i}ᶜ).ι p =
        SSet.toTop.map (SSet.stdSimplex.δ (n := n) i) (SSet.toTop.map e.inv p) := by
      have h1 := ConcreteCategory.congr_hom hEqTop p
      simpa [CategoryTheory.comp_apply] using h1
    have h_nat :
        (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1)) : SSet.toTop.{u}.obj Δ[n + 1] →
        Convexity.StdSimplex ℝ (Fin (n + 2))) (SSet.toTop.map (SSet.stdSimplex.δ (n :=
        n) i) (SSet.toTop.map e.inv p)) = (Convexity.StdSimplex.map (Fin.succAbove i) : _ →
        _) (SimplexCategory.toTopHomeo (SimplexCategory.mk n) (SSet.toTop.map e.inv p)) := by
      have h1 :
          (SSet.stdSimplex.δ.{u} (n := n) i : Δ[n] ⟶ Δ[n + 1]) =
          SSet.stdSimplex.{u}.map (SimplexCategory.δ (n := n) i) := rfl
      have h2 :
          (⇑(SimplexCategory.δ (n := n) i) : Fin (n + 1) → Fin (n + 2)) = Fin.succAbove i :=
          rfl
      have h_nat' :
          (SimplexCategory.toTopHomeo.{u} (SimplexCategory.mk (n + 1)) : _ → _) ∘
          ⇑(SSet.toTop.{u}.map (SSet.stdSimplex.{u}.map (SimplexCategory.δ (n := n) i))) =
          (Convexity.StdSimplex.map (Fin.succAbove i) : _ → _) ∘
          ⇑(SimplexCategory.toTopHomeo.{u} (SimplexCategory.mk n)) := by
        simpa [h1, h2] using SimplexCategory.toTopHomeo_naturality (f := SimplexCategory.δ (n :=
            n) i)
      exact congr_fun h_nat' (SSet.toTop.map e.inv p)
    rw [hw, hEqFun]
    simp only at ⊢
    rw [h_nat]
    exact ⟨_, rfl⟩
  rw [Convexity.StdSimplex.mem_range_map_iff] at h_range
  exact h_range i (by simp)

/-- Let `n : ℕ`, `i₀,j₀ : Fin (n+1)` with `i₀<j₀`, and let `p₀` and `q₀` be points in the
realizations of `face {i₀}ᶜ` and `face {j₀}ᶜ` of `Δ[n] : SSet.{u}`. If their images under the
two realized face inclusions are equal, there exists a point `r` of the realized pair face
`face {i₀,j₀}ᶜ` whose image in `|Δ[n]|` equals both of those images. -/
lemma realizedFacePair_lift {n : ℕ} (i₀ j₀ : Fin (n + 1)) (h_lt : i₀ < j₀)
    (p₀ : SSet.toTop.obj (SSet.stdSimplex.face (n := n) {i₀}ᶜ : SSet.{u}))
    (q₀ : SSet.toTop.obj (SSet.stdSimplex.face (n := n) {j₀}ᶜ : SSet.{u}))
    (h_eq : SSet.toTop.map (SSet.stdSimplex.face (n := n) {i₀}ᶜ).ι p₀ =
        SSet.toTop.map (SSet.stdSimplex.face (n := n) {j₀}ᶜ).ι q₀) :
    ∃ r : SSet.toTop.obj (SSet.stdSimplex.face (n := n) {i₀, j₀}ᶜ : SSet.{u}),
      SSet.toTop.map (SSet.stdSimplex.face (n := n) {i₀, j₀}ᶜ).ι r =
        SSet.toTop.map (SSet.stdSimplex.face (n := n) {i₀}ᶜ).ι p₀ ∧
      SSet.toTop.map (SSet.stdSimplex.face (n := n) {i₀, j₀}ᶜ).ι r =
        SSet.toTop.map (SSet.stdSimplex.face (n := n) {j₀}ᶜ).ι q₀ := by
  cases n with
  | zero =>
    have hi : i₀.val < 1 := i₀.isLt
    have hj : j₀.val < 1 := j₀.isLt
    have hij : i₀.val < j₀.val := h_lt
    omega
  | succ n =>
    cases n with
    | zero =>
      have hi0 : i₀ = 0 := by
        have : i₀.val = 0 := by omega
        exact Fin.ext this
      have hj1 : j₀ = 1 := by
        have : j₀.val = 1 := by omega
        exact Fin.ext this
      subst hi0
      subst hj1
      let hHomeo := SimplexCategory.toTopHomeo (SimplexCategory.mk 1)
      have hDistinct : SSet.toTop.map (SSet.stdSimplex.face (n := 1) {0}ᶜ).ι p₀ ≠
          SSet.toTop.map (SSet.stdSimplex.face (n := 1) {1}ᶜ).ι q₀ := by
        intro heq
        have hw_eq : hHomeo (SSet.toTop.map (SSet.stdSimplex.face (n := 1) {0}ᶜ).ι p₀) =
            hHomeo (SSet.toTop.map (SSet.stdSimplex.face (n := 1) {1}ᶜ).ι q₀) := congrArg hHomeo heq
        have h_zero_0 : (hHomeo
            (SSet.toTop.map (SSet.stdSimplex.face (n := 1) {0}ᶜ).ι p₀)).weights 0 = 0 :=
          singleton_face_coord_zero (n := 0) (0 : Fin 2) p₀ _ (by rfl)
        have h_zero_1 : (hHomeo
            (SSet.toTop.map (SSet.stdSimplex.face (n := 1) {1}ᶜ).ι q₀)).weights 1 = 0 :=
          singleton_face_coord_zero (n := 0) (1 : Fin 2) q₀ _ (by rfl)
        have h_sum : (hHomeo (SSet.toTop.map (SSet.stdSimplex.face (n := 1) {0}ᶜ).ι p₀)).weights 0 +
            (hHomeo (SSet.toTop.map (SSet.stdSimplex.face (n := 1) {0}ᶜ).ι p₀)).weights 1 = 1 :=
          Convexity.StdSimplex.total_fin_two _
        have h_zero_0' : (hHomeo
            (SSet.toTop.map (SSet.stdSimplex.face (n := 1) {1}ᶜ).ι q₀)).weights 0 = 0 := by
          rw [← hw_eq]; exact h_zero_0
        have h_sum' :
            (hHomeo (SSet.toTop.map (SSet.stdSimplex.face (n := 1) {1}ᶜ).ι q₀)).weights 0 +
            (hHomeo (SSet.toTop.map (SSet.stdSimplex.face (n := 1) {1}ᶜ).ι q₀)).weights 1 = 1 := by
          rw [← hw_eq]; exact h_sum
        rw [h_zero_0', h_zero_1] at h_sum'
        simp at h_sum'
      exact absurd h_eq hDistinct
    | succ n =>
      let hHomeo := SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 2))
      let w : Convexity.StdSimplex ℝ (Fin (n + 3)) :=
        hHomeo (SSet.toTop.map (SSet.stdSimplex.face (n := n + 2) {i₀}ᶜ).ι p₀)
      have h_w_eq : w = hHomeo (SSet.toTop.map (SSet.stdSimplex.face (n := n + 2) {j₀}ᶜ).ι q₀) := by
        dsimp [w]
        rw [h_eq]
      have h_w_i0 : w.weights i₀ = 0 :=
        singleton_face_coord_zero (n := n + 1) i₀ p₀ w (by rfl)
      have h_w_j0 : w.weights j₀ = 0 :=
        singleton_face_coord_zero (n := n + 1) j₀ q₀ w (by
          dsimp [w] at h_w_eq ⊢
          exact h_w_eq)
      let pairMap : Fin (n + 1) → Fin (n + 3) := fun k =>
          (SSet.stdSimplex.finOrderIsoPairCompl (n := n + 1) i₀ j₀ h_lt k).val
      have h_mem_pair : w ∈ Set.range (Convexity.StdSimplex.map (R := ℝ) pairMap) := by
        rw [Convexity.StdSimplex.mem_range_map_iff]
        intro a ha
        by_cases ha_i : a = i₀
        · rw [ha_i, h_w_i0]
        · by_cases ha_j : a = j₀
          · rw [ha_j, h_w_j0]
          · exfalso
            have hmem : a ∈ Set.range pairMap := by
              have h_a_mem : a ∈ ({i₀, j₀}ᶜ : Finset (Fin (n + 3))) := by
                simp [Finset.mem_compl, ha_i, ha_j]
              have h_pair_val :
                  pairMap ((SSet.stdSimplex.finOrderIsoPairCompl i₀ j₀ h_lt).symm ⟨a,
                  h_a_mem⟩) = a := by
                simp only [pairMap]
                have h_eq : (SSet.stdSimplex.finOrderIsoPairCompl i₀ j₀ h_lt)
                    ((SSet.stdSimplex.finOrderIsoPairCompl i₀ j₀ h_lt).symm ⟨a, h_a_mem⟩) =
                        ⟨a, h_a_mem⟩ := by
                  simp
                exact congrArg Subtype.val h_eq
              exact ⟨(SSet.stdSimplex.finOrderIsoPairCompl i₀ j₀ h_lt).symm ⟨a, h_a_mem⟩,
                  h_pair_val⟩
            exact ha hmem
      obtain ⟨y, hy⟩ := h_mem_pair
      have h_pair_range : SSet.toTop.map (SSet.stdSimplex.face (n := n + 2) {i₀}ᶜ).ι p₀ ∈
          Set.range (SSet.toTop.map (SSet.stdSimplex.face (n := n + 2) {i₀, j₀}ᶜ).ι) := by
        let hIsoPair : Δ[n] ≅ (SSet.stdSimplex.face (n := n + 2) {i₀, j₀}ᶜ : SSet.{u}) :=
          SSet.stdSimplex.facePairComplIso (n := n) i₀ j₀ h_lt
        have h_y : w = Convexity.StdSimplex.map (R := ℝ) pairMap y := hy.symm
        have hTop_eq : SSet.toTop.map (SSet.stdSimplex.face (n := n + 2) {i₀, j₀}ᶜ).ι
            (SSet.toTop.map hIsoPair.hom ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm
                y)) =
            SSet.toTop.map (SSet.stdSimplex.face (n := n + 2) {i₀}ᶜ).ι p₀ := by
          have hEq : hIsoPair.hom ≫ (SSet.stdSimplex.face (n := n + 2) {i₀, j₀}ᶜ).ι =
              SSet.stdSimplex.δ (i₀.castPred (Fin.ne_last_of_lt h_lt)) ≫ SSet.stdSimplex.δ j₀ :=
            SSet.stdSimplex.facePairComplIso_hom_ι (n := n) i₀ j₀ h_lt
          have hEqTop :
              SSet.toTop.map hIsoPair.hom ≫ SSet.toTop.map (SSet.stdSimplex.face (n :=
              n + 2) {i₀, j₀}ᶜ).ι =
              SSet.toTop.map (SSet.stdSimplex.δ (i₀.castPred (Fin.ne_last_of_lt h_lt)) ≫
                  SSet.stdSimplex.δ j₀) := by
            rw [← hEq, Functor.map_comp]
          have hEqFun : SSet.toTop.map (SSet.stdSimplex.face (n := n + 2) {i₀, j₀}ᶜ).ι
                (SSet.toTop.map hIsoPair.hom ((SimplexCategory.toTopHomeo (SimplexCategory.mk
                    n)).symm y)) =
              SSet.toTop.map (SSet.stdSimplex.δ (i₀.castPred (Fin.ne_last_of_lt h_lt)) ≫
                  SSet.stdSimplex.δ j₀)
                  ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm y) := by
            have h1 :=
                ConcreteCategory.congr_hom hEqTop ((SimplexCategory.toTopHomeo (SimplexCategory.mk
                n)).symm y)
            simpa [CategoryTheory.comp_apply] using h1
          calc SSet.toTop.map (SSet.stdSimplex.face (n := n + 2) {i₀, j₀}ᶜ).ι
                (SSet.toTop.map hIsoPair.hom ((SimplexCategory.toTopHomeo (SimplexCategory.mk
                    n)).symm y))
              = SSet.toTop.map (SSet.stdSimplex.δ (i₀.castPred (Fin.ne_last_of_lt h_lt)) ≫
                  SSet.stdSimplex.δ j₀)
                  ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm y) := hEqFun
            _ = SSet.toTop.map (SSet.stdSimplex.δ j₀)
                  (SSet.toTop.map (SSet.stdSimplex.δ (i₀.castPred (Fin.ne_last_of_lt h_lt)))
                    ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm y)) := by
                simp only [Functor.map_comp, CategoryTheory.comp_apply]
            _ = (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 2))).symm
                  (Convexity.StdSimplex.map (Fin.succAbove j₀)
                    (Convexity.StdSimplex.map (Fin.succAbove (i₀.castPred (Fin.ne_last_of_lt h_lt)))
                        y)) := by
                have hδ₁ :
                    (SSet.stdSimplex.δ.{u} (n :=
                    n) (i₀.castPred (Fin.ne_last_of_lt h_lt)) : Δ[n] ⟶ Δ[n + 1]) =
                    SSet.stdSimplex.{u}.map (SimplexCategory.δ (n :=
                        n) (i₀.castPred (Fin.ne_last_of_lt h_lt))) := rfl
                have hδ₂ : (SSet.stdSimplex.δ.{u} (n := n + 1) j₀ : Δ[n + 1] ⟶ Δ[n + 2]) =
                    SSet.stdSimplex.{u}.map (SimplexCategory.δ (n := n + 1) j₀) := rfl
                have hSucc₁ :
                    (⇑(SimplexCategory.δ (n :=
                    n) (i₀.castPred (Fin.ne_last_of_lt h_lt))) : Fin (n + 1) → Fin (n + 2)) =
                    Fin.succAbove (i₀.castPred (Fin.ne_last_of_lt h_lt)) := rfl
                have hSucc₂ : (⇑(SimplexCategory.δ (n := n + 1) j₀) : Fin (n + 2) → Fin (n + 3)) =
                    Fin.succAbove j₀ := rfl
                have hNat₁ :
                    SSet.toTop.map (SSet.stdSimplex.δ.{u} (n :=
                    n) (i₀.castPred (Fin.ne_last_of_lt h_lt))) ((SimplexCategory.toTopHomeo
                    (SimplexCategory.mk n)).symm y) =
                    (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1))).symm
                        (Convexity.StdSimplex.map (Fin.succAbove (i₀.castPred (Fin.ne_last_of_lt
                        h_lt))) y) := by
                  have h1 :
                      (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1)) : SSet.toTop.obj Δ[n
                      + 1] → Convexity.StdSimplex ℝ (Fin (n + 2))) ∘
                      ⇑(SSet.toTop.map (SSet.stdSimplex.{u}.map (SimplexCategory.δ (n :=
                      n) (i₀.castPred (Fin.ne_last_of_lt h_lt))))) =
                      (Convexity.StdSimplex.map (Fin.succAbove (i₀.castPred (Fin.ne_last_of_lt
                          h_lt))) : _ → _) ∘
                          ⇑(SimplexCategory.toTopHomeo (SimplexCategory.mk n)) := by
                    simpa [hδ₁, hSucc₁] using SimplexCategory.toTopHomeo_naturality (f :=
                        SimplexCategory.δ (n := n) (i₀.castPred (Fin.ne_last_of_lt h_lt)))
                  have h2 :=
                      congr_fun h1 ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm y)
                  have h := SimplexCategory.toTopHomeo_symm_naturality_apply (f :=
                      SimplexCategory.δ (n := n) (i₀.castPred (Fin.ne_last_of_lt h_lt))) (x := y)
                  change SSet.toTop.map (SSet.stdSimplex.δ (n :=
                      n) (i₀.castPred (Fin.ne_last_of_lt h_lt))) ((SimplexCategory.toTopHomeo
                      (SimplexCategory.mk n)).symm y) =
                      (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1))).symm
                      (Convexity.StdSimplex.map (Fin.succAbove (i₀.castPred (Fin.ne_last_of_lt
                      h_lt))) y)
                  simpa [hδ₁, hSucc₁] using h.symm
                have hNat₂ :
                    SSet.toTop.map (SSet.stdSimplex.δ.{u} (n :=
                    n + 1) j₀) ((SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1))).symm
                    (Convexity.StdSimplex.map (Fin.succAbove (i₀.castPred (Fin.ne_last_of_lt h_lt)))
                    y)) =
                    (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 2))).symm
                        (Convexity.StdSimplex.map (Fin.succAbove j₀) (Convexity.StdSimplex.map
                        (Fin.succAbove (i₀.castPred (Fin.ne_last_of_lt h_lt))) y)) := by
                  have h1 :
                      (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 2)) : SSet.toTop.obj Δ[n
                      + 2] → Convexity.StdSimplex ℝ (Fin (n + 3))) ∘
                      ⇑(SSet.toTop.map (SSet.stdSimplex.{u}.map (SimplexCategory.δ (n :=
                      n + 1) j₀))) =
                      (Convexity.StdSimplex.map (Fin.succAbove j₀) : _ → _) ∘
                          ⇑(SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1))) := by
                    simpa [hδ₂, hSucc₂] using SimplexCategory.toTopHomeo_naturality (f :=
                        SimplexCategory.δ (n := n + 1) j₀)
                  have h2 :=
                      congr_fun h1 ((SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1))).symm
                      (Convexity.StdSimplex.map (Fin.succAbove (i₀.castPred (Fin.ne_last_of_lt
                      h_lt))) y))
                  have h := SimplexCategory.toTopHomeo_symm_naturality_apply (f :=
                      SimplexCategory.δ (n := n + 1) j₀) (x :=
                      Convexity.StdSimplex.map
                          (Fin.succAbove (i₀.castPred (Fin.ne_last_of_lt h_lt)))
                      y)
                  change SSet.toTop.map (SSet.stdSimplex.δ (n :=
                      n + 1) j₀) ((SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1))).symm
                      (Convexity.StdSimplex.map (Fin.succAbove (i₀.castPred (Fin.ne_last_of_lt
                      h_lt))) y)) =
                      (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 2))).symm
                      (Convexity.StdSimplex.map (Fin.succAbove j₀) (Convexity.StdSimplex.map
                      (Fin.succAbove (i₀.castPred (Fin.ne_last_of_lt h_lt))) y))
                  simpa [hδ₂, hSucc₂] using h.symm
                rw [hNat₁, hNat₂]
            _ = (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 2))).symm
                  (Convexity.StdSimplex.map pairMap y) := by
                have h_pair_eq : pairMap =
                    (Fin.succAbove j₀) ∘
                        (Fin.succAbove (i₀.castPred (Fin.ne_last_of_lt h_lt))) := by
                  funext k
                  simp only [pairMap, SSet.stdSimplex.finOrderIsoPairCompl_apply_val,
                      Function.comp_apply]
                have h_map_pair : Convexity.StdSimplex.map (R := ℝ) pairMap y =
                    Convexity.StdSimplex.map (R := ℝ)
                      ((Fin.succAbove j₀) ∘
                          (Fin.succAbove (i₀.castPred (Fin.ne_last_of_lt h_lt)))) y := by
                  rw [h_pair_eq]
                have h_map_comp : Convexity.StdSimplex.map (R := ℝ)
                      ((Fin.succAbove j₀) ∘
                          (Fin.succAbove (i₀.castPred (Fin.ne_last_of_lt h_lt)))) y =
                    Convexity.StdSimplex.map (R := ℝ) (Fin.succAbove j₀)
                      (Convexity.StdSimplex.map (R :=
                          ℝ) (Fin.succAbove (i₀.castPred (Fin.ne_last_of_lt h_lt))) y) :=
                  Convexity.StdSimplex.map_comp y _ _
                have h_eq : Convexity.StdSimplex.map (R := ℝ) (Fin.succAbove j₀)
                      (Convexity.StdSimplex.map (R :=
                          ℝ) (Fin.succAbove (i₀.castPred (Fin.ne_last_of_lt h_lt))) y) =
                    Convexity.StdSimplex.map (R := ℝ) pairMap y := by
                  rw [← h_map_comp, ← h_map_pair]
                rw [h_eq]
            _ = (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 2))).symm w := by rw [h_y]
            _ = SSet.toTop.map (SSet.stdSimplex.face (n := n + 2) {i₀}ᶜ).ι p₀ := by
                simp only [w, hHomeo, Homeomorph.symm_apply_apply]
        exact Set.mem_range.mpr ⟨SSet.toTop.map hIsoPair.hom ((SimplexCategory.toTopHomeo
            (SimplexCategory.mk n)).symm y), hTop_eq⟩
      obtain ⟨r, hr⟩ := h_pair_range
      have hr₁ :
          SSet.toTop.map (SSet.stdSimplex.face (n := n + 2) {i₀, j₀}ᶜ).ι r =
          SSet.toTop.map (SSet.stdSimplex.face (n := n + 2) {i₀}ᶜ).ι p₀ := hr
      have hr₂ :
          SSet.toTop.map (SSet.stdSimplex.face (n := n + 2) {i₀, j₀}ᶜ).ι r =
          SSet.toTop.map (SSet.stdSimplex.face (n := n + 2) {j₀}ᶜ).ι q₀ := hr.trans h_eq
      exact ⟨r, hr₁, hr₂⟩

/-- For `n : ℕ` and universe `u`,
`TopCat.closedT1Embeddings (SSet.toTop.{u}.map (SSet.boundary.{u} n).ι)`.
Thus `|∂Δ[n]| → |Δ[n]|` is a closed embedding with the relative T1 property. The face images are the closed coordinate
faces of the real standard simplex. -/
theorem closedT1Embeddings_toTop_map_ι (n : ℕ) :
    TopCat.closedT1Embeddings (SSet.toTop.{u}.map (SSet.boundary.{u} n).ι) := by
  classical
  let S := MultispanShape.ofLinearOrder (Fin (n + 1))
  let DI : MultispanIndex S SSet.{u} :=
    ((multicoequalizerDiagram (n := n)).multispanIndex.toLinearOrder.map Subcomplex.toSSetFunctor)
  let D : Cocone DI.multispan :=
    (multicoequalizerDiagram (n := n)).multicofork.toLinearOrder.map Subcomplex.toSSetFunctor
  let c : Cocone (DI.multispan ⋙ SSet.toTop.{u}) := SSet.toTop.mapCocone D
  have hc : IsColimit c := isColimitToTop' (n := n)
  have hinj : Function.Injective (SSet.toTop.{u}.map (SSet.boundary.{u} n).ι) := by
    intro x y h
    have hcType : IsColimit ((forget TopCat).mapCocone c) :=
      isColimitOfPreserves (forget TopCat) hc
    have hx : ∃ (i₀ : Fin (n + 1))
        (p₀ : SSet.toTop.obj (SSet.stdSimplex.face (n := n) {i₀}ᶜ : SSet.{u})),
        c.ι.app (WalkingMultispan.right (i₀ : S.R)) p₀ = x := by
      obtain ⟨j, z, hz⟩ := Types.jointly_surjective_of_isColimit hcType x
      cases j with
      | right i =>
        exact ⟨(i : Fin (n + 1)), z, hz⟩
      | left p =>
        let i : Fin (n + 1) := p.1.1
        let j : Fin (n + 1) := p.1.2
        have h_p_fst : (S.fst p : Fin (n + 1)) = i := rfl
        have h_p_snd : (S.snd p : Fin (n + 1)) = j := rfl
        have hLE :
            SSet.stdSimplex.face (n := n) ({i,
            j}ᶜ : Finset (Fin (n + 1))) ≤ SSet.stdSimplex.face (n :=
            n) ({i}ᶜ : Finset (Fin (n + 1))) := by
          rw [SSet.stdSimplex.face_le_face_iff]
          simp
        have hOrigLE :
            SSet.stdSimplex.face (n := n) ({i,
            j}ᶜ : Finset (Fin (n + 1))) ≤ SSet.stdSimplex.face (n :=
            n) ({i}ᶜ : Finset (Fin (n + 1))) := hLE
        have hDI_fst : DI.fst p = SSet.Subcomplex.homOfLE hLE := by
          dsimp [DI, S, MultispanShape.ofLinearOrder]
          change SSet.Subcomplex.homOfLE hOrigLE = SSet.Subcomplex.homOfLE hLE
          congr 1
        have hFst_eq :
            (DI.multispan ⋙ SSet.toTop.{u}).map (WalkingMultispan.Hom.fst p) =
            SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) := by
          change SSet.toTop.map (DI.fst p) = SSet.toTop.map (SSet.Subcomplex.homOfLE hLE)
          rw [hDI_fst]
          rfl
        have hW : c.ι.app (WalkingMultispan.left p) z =
            c.ι.app (WalkingMultispan.right (S.fst p)) (SSet.toTop.map (SSet.Subcomplex.homOfLE
                hLE) z) := by
          have hEq :
              SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) ≫
              c.ι.app (WalkingMultispan.right (S.fst p)) = c.ι.app (WalkingMultispan.left p) := by
            rw [← hFst_eq]
            exact c.w (WalkingMultispan.Hom.fst p)
          have hEq_congr : (SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) ≫
              c.ι.app (WalkingMultispan.right (S.fst p))) z =
              c.ι.app (WalkingMultispan.left p) z :=
            ConcreteCategory.congr_hom hEq z
          have hcomp : (SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) ≫
              c.ι.app (WalkingMultispan.right (S.fst p))) z =
              c.ι.app (WalkingMultispan.right (S.fst p)) (SSet.toTop.map (SSet.Subcomplex.homOfLE
              hLE) z) :=
            ConcreteCategory.comp_apply (C :=
                TopCat) (SSet.toTop.map (SSet.Subcomplex.homOfLE hLE)) (c.ι.app
                (WalkingMultispan.right (S.fst p))) z
          exact hEq_congr.symm.trans hcomp
        exact ⟨S.fst p, SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) z, by
          simpa using hW.symm.trans hz⟩
    have hy : ∃ (j₀ : Fin (n + 1))
        (q₀ : SSet.toTop.obj (SSet.stdSimplex.face (n := n) {j₀}ᶜ : SSet.{u})),
        c.ι.app (WalkingMultispan.right j₀) q₀ = y := by
      obtain ⟨j, z, hz⟩ := Types.jointly_surjective_of_isColimit hcType y
      cases j with
      | right i => exact ⟨(i : Fin (n+1)), z, hz⟩
      | left p =>
        let i : Fin (n + 1) := p.1.1
        let j : Fin (n + 1) := p.1.2
        have h_p_fst : (S.fst p : Fin (n + 1)) = i := rfl
        have h_p_snd : (S.snd p : Fin (n + 1)) = j := rfl
        have hLE :
            SSet.stdSimplex.face (n := n) ({i,
            j}ᶜ : Finset (Fin (n + 1))) ≤ SSet.stdSimplex.face (n :=
            n) ({i}ᶜ : Finset (Fin (n + 1))) := by
          rw [SSet.stdSimplex.face_le_face_iff]
          simp
        have hOrigLE :
            SSet.stdSimplex.face (n := n) ({i,
            j}ᶜ : Finset (Fin (n + 1))) ≤ SSet.stdSimplex.face (n :=
            n) ({i}ᶜ : Finset (Fin (n + 1))) := hLE
        have hDI_fst : DI.fst p = SSet.Subcomplex.homOfLE hLE := by
          dsimp [DI, S, MultispanShape.ofLinearOrder]
          change SSet.Subcomplex.homOfLE hOrigLE = SSet.Subcomplex.homOfLE hLE
          congr 1
        have hFst_eq :
            (DI.multispan ⋙ SSet.toTop.{u}).map (WalkingMultispan.Hom.fst p) =
            SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) := by
          change SSet.toTop.map (DI.fst p) = SSet.toTop.map (SSet.Subcomplex.homOfLE hLE)
          rw [hDI_fst]
          rfl
        have hW : c.ι.app (WalkingMultispan.left p) z =
            c.ι.app (WalkingMultispan.right (S.fst p)) (SSet.toTop.map (SSet.Subcomplex.homOfLE
                hLE) z) := by
          have hEq :
              SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) ≫
              c.ι.app (WalkingMultispan.right (S.fst p)) = c.ι.app (WalkingMultispan.left p) := by
            rw [← hFst_eq]
            exact c.w (WalkingMultispan.Hom.fst p)
          have hEq_congr : (SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) ≫
              c.ι.app (WalkingMultispan.right (S.fst p))) z =
              c.ι.app (WalkingMultispan.left p) z :=
            ConcreteCategory.congr_hom hEq z
          have hcomp : (SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) ≫
              c.ι.app (WalkingMultispan.right (S.fst p))) z =
              c.ι.app (WalkingMultispan.right (S.fst p)) (SSet.toTop.map (SSet.Subcomplex.homOfLE
              hLE) z) :=
            ConcreteCategory.comp_apply (C :=
                TopCat) (SSet.toTop.map (SSet.Subcomplex.homOfLE hLE)) (c.ι.app
                (WalkingMultispan.right (S.fst p))) z
          exact hEq_congr.symm.trans hcomp
        exact ⟨S.fst p, SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) z, by
          simpa using hW.symm.trans hz⟩
    obtain ⟨i₀, p₀, rfl⟩ := hx
    obtain ⟨j₀, q₀, rfl⟩ := hy
    have h_eq : SSet.toTop.map (SSet.stdSimplex.face (n := n) ({i₀}ᶜ : Finset (Fin (n + 1)))).ι p₀ =
        SSet.toTop.map (SSet.stdSimplex.face (n := n) ({j₀}ᶜ : Finset (Fin (n + 1)))).ι q₀ := by
      have hD_right_i :
          D.ι.app (WalkingMultispan.right (i₀ : S.R)) =
          SSet.Subcomplex.homOfLE (SSet.face_singleton_compl_le_boundary i₀) := by
        dsimp [D, S, MultispanShape.ofLinearOrder]
        rfl
      have hD_right_j :
          D.ι.app (WalkingMultispan.right (j₀ : S.R)) =
          SSet.Subcomplex.homOfLE (SSet.face_singleton_compl_le_boundary j₀) := by
        dsimp [D, S, MultispanShape.ofLinearOrder]
        rfl
      have hSSet_i :
          D.ι.app (WalkingMultispan.right (i₀ : S.R)) ≫ (SSet.boundary n).ι =
          (SSet.stdSimplex.face (n := n) ({i₀}ᶜ : Finset (Fin (n + 1)))).ι := by
        rw [hD_right_i]
        exact SSet.Subcomplex.homOfLE_ι (SSet.face_singleton_compl_le_boundary i₀)
      have hSSet_j :
          D.ι.app (WalkingMultispan.right (j₀ : S.R)) ≫ (SSet.boundary n).ι =
          (SSet.stdSimplex.face (n := n) ({j₀}ᶜ : Finset (Fin (n + 1)))).ι := by
        rw [hD_right_j]
        exact SSet.Subcomplex.homOfLE_ι (SSet.face_singleton_compl_le_boundary j₀)
      have hC_i :
          c.ι.app (WalkingMultispan.right (i₀ : S.R)) =
          SSet.toTop.map (D.ι.app (WalkingMultispan.right (i₀ : S.R))) := rfl
      have hC_j :
          c.ι.app (WalkingMultispan.right (j₀ : S.R)) =
          SSet.toTop.map (D.ι.app (WalkingMultispan.right (j₀ : S.R))) := rfl
      have hEq_i : c.ι.app (WalkingMultispan.right (i₀ : S.R)) ≫
          SSet.toTop.map (SSet.boundary n).ι =
            SSet.toTop.map (SSet.stdSimplex.face (n := n) ({i₀}ᶜ : Finset (Fin (n + 1)))).ι := by
        erw [hC_i, ← SSet.toTop.map_comp, hSSet_i]
        rfl
      have hEq_j : c.ι.app (WalkingMultispan.right (j₀ : S.R)) ≫
          SSet.toTop.map (SSet.boundary n).ι =
            SSet.toTop.map (SSet.stdSimplex.face (n := n) ({j₀}ᶜ : Finset (Fin (n + 1)))).ι := by
        erw [hC_j, ← SSet.toTop.map_comp, hSSet_j]
        rfl
      have hfi : SSet.toTop.map (SSet.boundary n).ι (c.ι.app (WalkingMultispan.right i₀) p₀) =
          SSet.toTop.map (SSet.stdSimplex.face (n := n) ({i₀}ᶜ : Finset (Fin (n + 1)))).ι p₀ :=
        ConcreteCategory.congr_hom hEq_i p₀
      have hfj : SSet.toTop.map (SSet.boundary n).ι (c.ι.app (WalkingMultispan.right j₀) q₀) =
          SSet.toTop.map (SSet.stdSimplex.face (n := n) ({j₀}ᶜ : Finset (Fin (n + 1)))).ι q₀ :=
        ConcreteCategory.congr_hom hEq_j q₀
      have h' : SSet.toTop.map (SSet.boundary n).ι (c.ι.app (WalkingMultispan.right i₀) p₀) =
          SSet.toTop.map (SSet.boundary n).ι (c.ι.app (WalkingMultispan.right j₀) q₀) := h
      rw [hfi, hfj] at h'
      exact h'
    by_cases hij : i₀ = j₀
    · subst hij
      have hInjFace :
          Function.Injective (SSet.toTop.map (SSet.stdSimplex.face (n :=
          n) ({i₀}ᶜ : Finset (Fin (n + 1)))).ι) :=
        (isClosedEmbedding_realizedFaceInclusion n i₀).injective
      have hpq : p₀ = q₀ := hInjFace h_eq
      rw [hpq]
    · have hDistinct : i₀ ≠ j₀ := hij
      have h_or : i₀ < j₀ ∨ j₀ < i₀ := hDistinct.lt_or_gt
      rcases h_or with h_lt | h_lt
      · -- Case `i₀ < j₀`: lift to the pair face via reusable helper
        have hPairExists := realizedFacePair_lift (n := n) i₀ j₀ h_lt p₀ q₀ h_eq
        obtain ⟨r, hr₁, hr₂⟩ := hPairExists
        let ij : S.L := ⟨⟨i₀, j₀⟩, h_lt⟩
        have h_left_right₁ : c.ι.app (WalkingMultispan.left ij) r =
            c.ι.app (WalkingMultispan.right (S.fst ij)) p₀ := by
          have hLE :
              SSet.stdSimplex.face (n := n) ({i₀,
              j₀}ᶜ : Finset (Fin (n + 1))) ≤ SSet.stdSimplex.face (n :=
              n) ({i₀}ᶜ : Finset (Fin (n + 1))) := by
            rw [SSet.stdSimplex.face_le_face_iff]
            simp
          have hOrigLE :
              SSet.stdSimplex.face (n := n) ({i₀,
              j₀}ᶜ : Finset (Fin (n + 1))) ≤ SSet.stdSimplex.face (n :=
              n) ({i₀}ᶜ : Finset (Fin (n + 1))) := hLE
          have hMap_eq : SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) r = p₀ := by
            have h_comp :
                SSet.Subcomplex.homOfLE hLE ≫ (SSet.stdSimplex.face (n :=
                n) ({i₀}ᶜ : Finset (Fin (n + 1)))).ι = (SSet.stdSimplex.face (n := n) ({i₀,
                j₀}ᶜ : Finset (Fin (n + 1)))).ι :=
              SSet.Subcomplex.homOfLE_ι hLE
            have h_eq2 :
                (SSet.toTop.map (SSet.stdSimplex.face (n :=
                n) ({i₀}ᶜ : Finset (Fin (n + 1)))).ι) (SSet.toTop.map (SSet.Subcomplex.homOfLE
                hLE) r) =
                SSet.toTop.map (SSet.stdSimplex.face (n := n) ({i₀,
                    j₀}ᶜ : Finset (Fin (n + 1)))).ι r := by
              have h1 :
                  SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) ≫
                  SSet.toTop.map (SSet.stdSimplex.face (n :=
                  n) ({i₀}ᶜ : Finset (Fin (n + 1)))).ι =
                  SSet.toTop.map (SSet.stdSimplex.face (n := n) ({i₀,
                  j₀}ᶜ : Finset (Fin (n + 1)))).ι := by
                rw [← SSet.toTop.map_comp, h_comp]
              have h2 := ConcreteCategory.congr_hom h1 r
              simpa only [CategoryTheory.comp_apply] using h2
            have h_eq3 :
                (SSet.toTop.map (SSet.stdSimplex.face (n :=
                n) ({i₀}ᶜ : Finset (Fin (n + 1)))).ι) (SSet.toTop.map (SSet.Subcomplex.homOfLE
                hLE) r) =
                (SSet.toTop.map (SSet.stdSimplex.face (n :=
                    n) ({i₀}ᶜ : Finset (Fin (n + 1)))).ι) p₀ := by
              rw [h_eq2, hr₁]
            exact (isClosedEmbedding_realizedFaceInclusion n (i₀ : S.R)).injective h_eq3
          have hDI_fst : DI.fst ij = SSet.Subcomplex.homOfLE hLE := by
            dsimp [DI, S, MultispanShape.ofLinearOrder]
            change SSet.Subcomplex.homOfLE hOrigLE = SSet.Subcomplex.homOfLE hLE
            congr 1
          have hFst_eq :
              (DI.multispan ⋙ SSet.toTop.{u}).map (WalkingMultispan.Hom.fst ij) =
              SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) := by
            change SSet.toTop.map (DI.fst ij) = SSet.toTop.map (SSet.Subcomplex.homOfLE hLE)
            rw [hDI_fst]
            rfl
          have hEq :
              SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) ≫
              c.ι.app (WalkingMultispan.right (S.fst ij)) =
              c.ι.app (WalkingMultispan.left ij) := by
            rw [← hFst_eq]
            exact c.w (WalkingMultispan.Hom.fst ij)
          have hEq_congr : c.ι.app (WalkingMultispan.left ij) r =
              (SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) ≫
              c.ι.app (WalkingMultispan.right (S.fst ij))) r :=
            ConcreteCategory.congr_hom hEq.symm r
          have hcomp : (SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) ≫
              c.ι.app (WalkingMultispan.right (S.fst ij))) r =
              c.ι.app (WalkingMultispan.right (S.fst ij)) (SSet.toTop.map (SSet.Subcomplex.homOfLE
              hLE) r) :=
            ConcreteCategory.comp_apply (C :=
                TopCat) (SSet.toTop.map (SSet.Subcomplex.homOfLE hLE)) (c.ι.app
                (WalkingMultispan.right (S.fst ij))) r
          have hEq_apply : c.ι.app (WalkingMultispan.left ij) r =
              c.ι.app (WalkingMultispan.right (S.fst ij)) (SSet.toTop.map (SSet.Subcomplex.homOfLE
              hLE) r) :=
            hEq_congr.trans hcomp
          simpa only [hMap_eq] using hEq_apply
        have h_left_right₂ : c.ι.app (WalkingMultispan.left ij) r =
            c.ι.app (WalkingMultispan.right (S.snd ij)) q₀ := by
          have hLE :
              SSet.stdSimplex.face (n := n) ({i₀,
              j₀}ᶜ : Finset (Fin (n + 1))) ≤ SSet.stdSimplex.face (n :=
              n) ({j₀}ᶜ : Finset (Fin (n + 1))) := by
            rw [SSet.stdSimplex.face_le_face_iff]
            simp
          have hOrigLE :
              SSet.stdSimplex.face (n := n) ({i₀,
              j₀}ᶜ : Finset (Fin (n + 1))) ≤ SSet.stdSimplex.face (n :=
              n) ({j₀}ᶜ : Finset (Fin (n + 1))) := hLE
          have hMap_eq : SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) r = q₀ := by
            have h_comp :
                SSet.Subcomplex.homOfLE hLE ≫ (SSet.stdSimplex.face (n :=
                n) ({j₀}ᶜ : Finset (Fin (n + 1)))).ι = (SSet.stdSimplex.face (n := n) ({i₀,
                j₀}ᶜ : Finset (Fin (n + 1)))).ι :=
              SSet.Subcomplex.homOfLE_ι hLE
            have h_eq2 :
                (SSet.toTop.map (SSet.stdSimplex.face (n :=
                n) ({j₀}ᶜ : Finset (Fin (n + 1)))).ι) (SSet.toTop.map (SSet.Subcomplex.homOfLE
                hLE) r) =
                SSet.toTop.map (SSet.stdSimplex.face (n := n) ({i₀,
                    j₀}ᶜ : Finset (Fin (n + 1)))).ι r := by
              have h1 :
                  SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) ≫
                  SSet.toTop.map (SSet.stdSimplex.face (n :=
                  n) ({j₀}ᶜ : Finset (Fin (n + 1)))).ι =
                  SSet.toTop.map (SSet.stdSimplex.face (n := n) ({i₀,
                  j₀}ᶜ : Finset (Fin (n + 1)))).ι := by
                rw [← SSet.toTop.map_comp, h_comp]
              have h2 := ConcreteCategory.congr_hom h1 r
              simpa only [CategoryTheory.comp_apply] using h2
            have h_eq3 :
                (SSet.toTop.map (SSet.stdSimplex.face (n :=
                n) ({j₀}ᶜ : Finset (Fin (n + 1)))).ι) (SSet.toTop.map (SSet.Subcomplex.homOfLE
                hLE) r) =
                (SSet.toTop.map (SSet.stdSimplex.face (n :=
                    n) ({j₀}ᶜ : Finset (Fin (n + 1)))).ι) q₀ := by
              rw [h_eq2, hr₂]
            exact (isClosedEmbedding_realizedFaceInclusion n (j₀ : S.R)).injective h_eq3
          have hDI_snd : DI.snd ij = SSet.Subcomplex.homOfLE hLE := by
            dsimp [DI, S, MultispanShape.ofLinearOrder]
            change SSet.Subcomplex.homOfLE hOrigLE = SSet.Subcomplex.homOfLE hLE
            congr 1
          have hSnd_eq :
              (DI.multispan ⋙ SSet.toTop.{u}).map (WalkingMultispan.Hom.snd ij) =
              SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) := by
            change SSet.toTop.map (DI.snd ij) = SSet.toTop.map (SSet.Subcomplex.homOfLE hLE)
            rw [hDI_snd]
            rfl
          have hEq :
              SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) ≫
              c.ι.app (WalkingMultispan.right (S.snd ij)) =
              c.ι.app (WalkingMultispan.left ij) := by
            rw [← hSnd_eq]
            exact c.w (WalkingMultispan.Hom.snd ij)
          have hEq_congr : c.ι.app (WalkingMultispan.left ij) r =
              (SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) ≫
              c.ι.app (WalkingMultispan.right (S.snd ij))) r :=
            ConcreteCategory.congr_hom hEq.symm r
          have hcomp : (SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) ≫
              c.ι.app (WalkingMultispan.right (S.snd ij))) r =
              c.ι.app (WalkingMultispan.right (S.snd ij)) (SSet.toTop.map (SSet.Subcomplex.homOfLE
              hLE) r) :=
            ConcreteCategory.comp_apply (C :=
                TopCat) (SSet.toTop.map (SSet.Subcomplex.homOfLE hLE)) (c.ι.app
                (WalkingMultispan.right (S.snd ij))) r
          have hEq_apply : c.ι.app (WalkingMultispan.left ij) r =
              c.ι.app (WalkingMultispan.right (S.snd ij)) (SSet.toTop.map (SSet.Subcomplex.homOfLE
              hLE) r) :=
            hEq_congr.trans hcomp
          simpa only [hMap_eq] using hEq_apply
        have h_trans : c.ι.app (WalkingMultispan.right (S.fst ij)) p₀ =
            c.ι.app (WalkingMultispan.right (S.snd ij)) q₀ := by
          rw [← h_left_right₁, h_left_right₂]
        exact h_trans
      · -- Case `j₀ < i₀`: symmetric via helper
        have h_lt' : j₀ < i₀ := h_lt
        have hPairExists := realizedFacePair_lift (n := n) j₀ i₀ h_lt' q₀ p₀ h_eq.symm
        obtain ⟨r, hr₁, hr₂⟩ := hPairExists
        let ji : S.L := ⟨⟨j₀, i₀⟩, h_lt'⟩
        have h_left_right₁ : c.ι.app (WalkingMultispan.left ji) r =
            c.ι.app (WalkingMultispan.right (S.fst ji)) q₀ := by
          have hLE :
              SSet.stdSimplex.face (n := n) ({j₀,
              i₀}ᶜ : Finset (Fin (n + 1))) ≤ SSet.stdSimplex.face (n :=
              n) ({j₀}ᶜ : Finset (Fin (n + 1))) := by
            rw [SSet.stdSimplex.face_le_face_iff]
            simp
          have hOrigLE :
              SSet.stdSimplex.face (n := n) ({j₀,
              i₀}ᶜ : Finset (Fin (n + 1))) ≤ SSet.stdSimplex.face (n :=
              n) ({j₀}ᶜ : Finset (Fin (n + 1))) := hLE
          have hMap_eq : SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) r = q₀ := by
            have h_comp :
                SSet.Subcomplex.homOfLE hLE ≫ (SSet.stdSimplex.face (n :=
                n) ({j₀}ᶜ : Finset (Fin (n + 1)))).ι = (SSet.stdSimplex.face (n := n) ({j₀,
                i₀}ᶜ : Finset (Fin (n + 1)))).ι :=
              SSet.Subcomplex.homOfLE_ι hLE
            have h_eq2 :
                (SSet.toTop.map (SSet.stdSimplex.face (n :=
                n) ({j₀}ᶜ : Finset (Fin (n + 1)))).ι) (SSet.toTop.map (SSet.Subcomplex.homOfLE
                hLE) r) =
                SSet.toTop.map (SSet.stdSimplex.face (n := n) ({j₀,
                    i₀}ᶜ : Finset (Fin (n + 1)))).ι r := by
              have h1 :
                  SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) ≫
                  SSet.toTop.map (SSet.stdSimplex.face (n :=
                  n) ({j₀}ᶜ : Finset (Fin (n + 1)))).ι =
                  SSet.toTop.map (SSet.stdSimplex.face (n := n) ({j₀,
                  i₀}ᶜ : Finset (Fin (n + 1)))).ι := by
                rw [← SSet.toTop.map_comp, h_comp]
              have h2 := ConcreteCategory.congr_hom h1 r
              simpa only [CategoryTheory.comp_apply] using h2
            have h_eq3 :
                (SSet.toTop.map (SSet.stdSimplex.face (n :=
                n) ({j₀}ᶜ : Finset (Fin (n + 1)))).ι) (SSet.toTop.map (SSet.Subcomplex.homOfLE
                hLE) r) =
                (SSet.toTop.map (SSet.stdSimplex.face (n :=
                    n) ({j₀}ᶜ : Finset (Fin (n + 1)))).ι) q₀ := by
              rw [h_eq2, hr₁]
            exact (isClosedEmbedding_realizedFaceInclusion n (j₀ : S.R)).injective h_eq3
          have hDI_fst : DI.fst ji = SSet.Subcomplex.homOfLE hLE := by
            dsimp [DI, S, MultispanShape.ofLinearOrder]
            change SSet.Subcomplex.homOfLE hOrigLE = SSet.Subcomplex.homOfLE hLE
            congr 1
          have hFst_eq :
              (DI.multispan ⋙ SSet.toTop.{u}).map (WalkingMultispan.Hom.fst ji) =
              SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) := by
            change SSet.toTop.map (DI.fst ji) = SSet.toTop.map (SSet.Subcomplex.homOfLE hLE)
            rw [hDI_fst]
            rfl
          have hEq :
              SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) ≫
              c.ι.app (WalkingMultispan.right (S.fst ji)) =
              c.ι.app (WalkingMultispan.left ji) := by
            rw [← hFst_eq]
            exact c.w (WalkingMultispan.Hom.fst ji)
          have hEq_congr : c.ι.app (WalkingMultispan.left ji) r =
              (SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) ≫
              c.ι.app (WalkingMultispan.right (S.fst ji))) r :=
            ConcreteCategory.congr_hom hEq.symm r
          have hcomp : (SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) ≫
              c.ι.app (WalkingMultispan.right (S.fst ji))) r =
              c.ι.app (WalkingMultispan.right (S.fst ji)) (SSet.toTop.map (SSet.Subcomplex.homOfLE
              hLE) r) :=
            ConcreteCategory.comp_apply (C :=
                TopCat) (SSet.toTop.map (SSet.Subcomplex.homOfLE hLE)) (c.ι.app
                (WalkingMultispan.right (S.fst ji))) r
          have hEq_apply : c.ι.app (WalkingMultispan.left ji) r =
              c.ι.app (WalkingMultispan.right (S.fst ji)) (SSet.toTop.map (SSet.Subcomplex.homOfLE
              hLE) r) :=
            hEq_congr.trans hcomp
          simpa only [hMap_eq] using hEq_apply
        have h_left_right₂ : c.ι.app (WalkingMultispan.left ji) r =
            c.ι.app (WalkingMultispan.right (S.snd ji)) p₀ := by
          have hLE :
              SSet.stdSimplex.face (n := n) ({j₀,
              i₀}ᶜ : Finset (Fin (n + 1))) ≤ SSet.stdSimplex.face (n :=
              n) ({i₀}ᶜ : Finset (Fin (n + 1))) := by
            rw [SSet.stdSimplex.face_le_face_iff]
            simp
          have hOrigLE :
              SSet.stdSimplex.face (n := n) ({j₀,
              i₀}ᶜ : Finset (Fin (n + 1))) ≤ SSet.stdSimplex.face (n :=
              n) ({i₀}ᶜ : Finset (Fin (n + 1))) := hLE
          have hMap_eq : SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) r = p₀ := by
            have h_comp :
                SSet.Subcomplex.homOfLE hLE ≫ (SSet.stdSimplex.face (n :=
                n) ({i₀}ᶜ : Finset (Fin (n + 1)))).ι = (SSet.stdSimplex.face (n := n) ({j₀,
                i₀}ᶜ : Finset (Fin (n + 1)))).ι :=
              SSet.Subcomplex.homOfLE_ι hLE
            have h_eq2 :
                (SSet.toTop.map (SSet.stdSimplex.face (n :=
                n) ({i₀}ᶜ : Finset (Fin (n + 1)))).ι) (SSet.toTop.map (SSet.Subcomplex.homOfLE
                hLE) r) =
                SSet.toTop.map (SSet.stdSimplex.face (n := n) ({j₀,
                    i₀}ᶜ : Finset (Fin (n + 1)))).ι r := by
              have h1 :
                  SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) ≫
                  SSet.toTop.map (SSet.stdSimplex.face (n :=
                  n) ({i₀}ᶜ : Finset (Fin (n + 1)))).ι =
                  SSet.toTop.map (SSet.stdSimplex.face (n := n) ({j₀,
                  i₀}ᶜ : Finset (Fin (n + 1)))).ι := by
                rw [← SSet.toTop.map_comp, h_comp]
              have h2 := ConcreteCategory.congr_hom h1 r
              simpa only [CategoryTheory.comp_apply] using h2
            have h_eq3 :
                (SSet.toTop.map (SSet.stdSimplex.face (n :=
                n) ({i₀}ᶜ : Finset (Fin (n + 1)))).ι) (SSet.toTop.map (SSet.Subcomplex.homOfLE
                hLE) r) =
                (SSet.toTop.map (SSet.stdSimplex.face (n :=
                    n) ({i₀}ᶜ : Finset (Fin (n + 1)))).ι) p₀ := by
              rw [h_eq2, hr₂]
            exact (isClosedEmbedding_realizedFaceInclusion n (i₀ : S.R)).injective h_eq3
          have hDI_snd : DI.snd ji = SSet.Subcomplex.homOfLE hLE := by
            dsimp [DI, S, MultispanShape.ofLinearOrder]
            change SSet.Subcomplex.homOfLE hOrigLE = SSet.Subcomplex.homOfLE hLE
            congr 1
          have hSnd_eq :
              (DI.multispan ⋙ SSet.toTop.{u}).map (WalkingMultispan.Hom.snd ji) =
              SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) := by
            change SSet.toTop.map (DI.snd ji) = SSet.toTop.map (SSet.Subcomplex.homOfLE hLE)
            rw [hDI_snd]
            rfl
          have hEq :
              SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) ≫
              c.ι.app (WalkingMultispan.right (S.snd ji)) =
              c.ι.app (WalkingMultispan.left ji) := by
            rw [← hSnd_eq]
            exact c.w (WalkingMultispan.Hom.snd ji)
          have hEq_congr : c.ι.app (WalkingMultispan.left ji) r =
              (SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) ≫
              c.ι.app (WalkingMultispan.right (S.snd ji))) r :=
            ConcreteCategory.congr_hom hEq.symm r
          have hcomp : (SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) ≫
              c.ι.app (WalkingMultispan.right (S.snd ji))) r =
              c.ι.app (WalkingMultispan.right (S.snd ji)) (SSet.toTop.map (SSet.Subcomplex.homOfLE
              hLE) r) :=
            ConcreteCategory.comp_apply (C :=
                TopCat) (SSet.toTop.map (SSet.Subcomplex.homOfLE hLE)) (c.ι.app
                (WalkingMultispan.right (S.snd ji))) r
          have hEq_apply : c.ι.app (WalkingMultispan.left ji) r =
              c.ι.app (WalkingMultispan.right (S.snd ji)) (SSet.toTop.map (SSet.Subcomplex.homOfLE
              hLE) r) :=
            hEq_congr.trans hcomp
          simpa only [hMap_eq] using hEq_apply
        have h_trans : c.ι.app (WalkingMultispan.right (S.snd ji)) p₀ =
            c.ι.app (WalkingMultispan.right (S.fst ji)) q₀ := by
          rw [← h_left_right₂, h_left_right₁]
        exact h_trans
  have hf : ∀ (j : WalkingMultispan S),
      Topology.IsClosedEmbedding (c.ι.app j ≫ SSet.toTop.{u}.map (SSet.boundary.{u} n).ι) := by
    intro j
    match j with
    | WalkingMultispan.right i =>
      have hD_right :
          D.ι.app (WalkingMultispan.right (i : S.R)) =
          SSet.Subcomplex.homOfLE (SSet.face_singleton_compl_le_boundary (n := n) (i : S.R)) := by
        dsimp [D, S, MultispanShape.ofLinearOrder]
        rfl
      have hSSet : D.ι.app (WalkingMultispan.right (i : S.R)) ≫ (SSet.boundary (n := n)).ι =
            (SSet.stdSimplex.face (n := n) ({(i : Fin (n + 1))}ᶜ : Finset (Fin (n + 1)))).ι := by
        rw [hD_right]
        exact SSet.Subcomplex.homOfLE_ι (SSet.face_singleton_compl_le_boundary (n := n) (i : S.R))
      have hC :
          c.ι.app (WalkingMultispan.right (i : S.R)) =
          SSet.toTop.map (D.ι.app (WalkingMultispan.right (i : S.R))) := rfl
      have h1 : c.ι.app (WalkingMultispan.right (i : S.R)) ≫ SSet.toTop.map (SSet.boundary n).ι =
          SSet.toTop.map (D.ι.app (WalkingMultispan.right (i : S.R))) ≫
              SSet.toTop.map (SSet.boundary n).ι :=
        congrArg (· ≫ SSet.toTop.map (SSet.boundary n).ι) hC
      have h2 : SSet.toTop.map (D.ι.app (WalkingMultispan.right (i : S.R))) ≫
          SSet.toTop.map (SSet.boundary n).ι =
          SSet.toTop.map (D.ι.app (WalkingMultispan.right (i : S.R)) ≫ (SSet.boundary n).ι) :=
        (SSet.toTop.map_comp _ _).symm
      have h3 : SSet.toTop.map (D.ι.app (WalkingMultispan.right (i : S.R)) ≫ (SSet.boundary n).ι) =
          SSet.toTop.map (SSet.stdSimplex.face (n :=
              n) ({(i : Fin (n + 1))}ᶜ : Finset (Fin (n + 1)))).ι :=
        congrArg SSet.toTop.map hSSet
      have hEq : c.ι.app (WalkingMultispan.right (i : S.R)) ≫ SSet.toTop.map (SSet.boundary n).ι =
          SSet.toTop.map (SSet.stdSimplex.face (n :=
              n) ({(i : Fin (n + 1))}ᶜ : Finset (Fin (n + 1)))).ι :=
        h1.trans (h2.trans h3)
      rw [hEq]
      exact isClosedEmbedding_realizedFaceInclusion n (i : S.R)
    | WalkingMultispan.left p =>
      have h_le :
          SSet.stdSimplex.face (n := n) ({p.1.1,
          p.1.2}ᶜ : Finset (Fin (n + 1))) ≤ SSet.boundary (n := n) := by
        calc SSet.stdSimplex.face ({p.1.1, p.1.2}ᶜ : Finset (Fin (n + 1)))
              ≤ SSet.stdSimplex.face ({p.1.1}ᶜ : Finset (Fin (n + 1))) := by
                rw [SSet.stdSimplex.face_le_face_iff]
                simp
            _ ≤ SSet.boundary n := SSet.face_singleton_compl_le_boundary (p.1.1 : S.R)
      have hOrig_le :
          SSet.stdSimplex.face (n := n) ({p.1.1,
          p.1.2}ᶜ : Finset (Fin (n + 1))) ≤ SSet.boundary (n := n) := h_le
      have hD_left : D.ι.app (WalkingMultispan.left p) = SSet.Subcomplex.homOfLE h_le := by
        dsimp [D, S, MultispanShape.ofLinearOrder]
        change SSet.Subcomplex.homOfLE hOrig_le = SSet.Subcomplex.homOfLE h_le
        congr 1
      have hSSet : D.ι.app (WalkingMultispan.left p) ≫ (SSet.boundary (n := n)).ι =
            (SSet.stdSimplex.face (n := n) ({p.1.1, p.1.2}ᶜ : Finset (Fin (n + 1)))).ι := by
        rw [hD_left]
        exact SSet.Subcomplex.homOfLE_ι h_le
      have hC :
          c.ι.app (WalkingMultispan.left p) =
          SSet.toTop.map (D.ι.app (WalkingMultispan.left p)) := rfl
      have h1 : c.ι.app (WalkingMultispan.left p) ≫ SSet.toTop.map (SSet.boundary n).ι =
          SSet.toTop.map (D.ι.app (WalkingMultispan.left p)) ≫ SSet.toTop.map (SSet.boundary n).ι :=
        congrArg (· ≫ SSet.toTop.map (SSet.boundary n).ι) hC
      have h2 : SSet.toTop.map (D.ι.app (WalkingMultispan.left p)) ≫
          SSet.toTop.map (SSet.boundary n).ι =
          SSet.toTop.map (D.ι.app (WalkingMultispan.left p) ≫ (SSet.boundary n).ι) :=
        (SSet.toTop.map_comp _ _).symm
      have h3 : SSet.toTop.map (D.ι.app (WalkingMultispan.left p) ≫ (SSet.boundary n).ι) =
          SSet.toTop.map (SSet.stdSimplex.face (n := n) ({p.1.1,
              p.1.2}ᶜ : Finset (Fin (n + 1)))).ι :=
        congrArg SSet.toTop.map hSSet
      have hEq : c.ι.app (WalkingMultispan.left p) ≫ SSet.toTop.map (SSet.boundary n).ι =
          SSet.toTop.map (SSet.stdSimplex.face (n := n) ({p.1.1,
              p.1.2}ᶜ : Finset (Fin (n + 1)))).ι :=
        h1.trans (h2.trans h3)
      rw [hEq]
      exact isClosedEmbedding_realizedFacePair n (p.1.1 : S.R) (p.1.2 : S.R) p.2
  have : Fintype (WalkingMultispan S) := by
    dsimp [S, MultispanShape.ofLinearOrder]
    infer_instance
  have : Finite (WalkingMultispan S) := by
    dsimp [S, MultispanShape.ofLinearOrder]
    infer_instance
  have hClosed : Topology.IsClosedEmbedding (SSet.toTop.{u}.map (SSet.boundary.{u} n).ι) :=
    TopCat.isClosedEmbedding_of_isColimit (c := c) (f :=
        SSet.toTop.map (SSet.boundary n).ι) hc hinj hf
  refine ⟨hClosed, fun y hy => ?_⟩
  let _ : T2Space (Convexity.StdSimplex ℝ (Fin (n + 1))) :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).t2Space
  let _ : T2Space (SSet.toTop.{u}.obj (SSet.stdSimplex.obj (SimplexCategory.mk n))) :=
    (SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm.t2Space
  let _ : T1Space (SSet.toTop.{u}.obj (SSet.stdSimplex.obj (SimplexCategory.mk n))) :=
    inferInstance
  exact isClosed_singleton

/-- For `n : ℕ`, universe `u`, and `j : WalkingMultispan (MultispanShape.ofLinearOrder (Fin
(n+1)))`, the `j`-th leg of the realized linear-order boundary multicoequalizer cocone is a
closed embedding. This applies to the legs from singleton-complement faces and from
pair-complement intersection faces into the realized boundary. -/
theorem isClosedEmbedding_toTop_mapCocone_ι (n : ℕ)
    (j : WalkingMultispan (MultispanShape.ofLinearOrder (Fin (n + 1)))) :
    Topology.IsClosedEmbedding
      ((SSet.toTop.{u}.mapCocone
        ((multicoequalizerDiagram (n := n)).multicofork.toLinearOrder.map
          Subcomplex.toSSetFunctor)).ι.app j) := by
  classical
  let S := MultispanShape.ofLinearOrder (Fin (n + 1))
  let DI : MultispanIndex S SSet.{u} :=
    ((multicoequalizerDiagram (n := n)).multispanIndex.toLinearOrder.map
      Subcomplex.toSSetFunctor)
  let D : Cocone DI.multispan :=
    (multicoequalizerDiagram (n := n)).multicofork.toLinearOrder.map
      Subcomplex.toSSetFunctor
  let c : Cocone (DI.multispan ⋙ SSet.toTop.{u}) := SSet.toTop.mapCocone D
  change Topology.IsClosedEmbedding (c.ι.app j)
  have hbEmbed : Topology.IsEmbedding (SSet.toTop.{u}.map (SSet.boundary.{u} n).ι) :=
    (TopCat.closedT1Embeddings_le_isClosedEmbedding _
      (closedT1Embeddings_toTop_map_ι n)).isEmbedding
  match j with
  | WalkingMultispan.right i =>
    have hD_right : D.ι.app (WalkingMultispan.right (i : S.R)) =
        SSet.Subcomplex.homOfLE (SSet.face_singleton_compl_le_boundary (n := n) (i : S.R)) := by
      dsimp [D, S, MultispanShape.ofLinearOrder]
      rfl
    have hSSet : D.ι.app (WalkingMultispan.right (i : S.R)) ≫ (SSet.boundary (n := n)).ι =
        (SSet.stdSimplex.face (n := n) ({(i : Fin (n + 1))}ᶜ : Finset (Fin (n + 1)))).ι := by
      rw [hD_right]
      exact SSet.Subcomplex.homOfLE_ι (SSet.face_singleton_compl_le_boundary (n := n) (i : S.R))
    have hC : c.ι.app (WalkingMultispan.right (i : S.R)) =
        SSet.toTop.map (D.ι.app (WalkingMultispan.right (i : S.R))) := rfl
    have h1 : c.ι.app (WalkingMultispan.right (i : S.R)) ≫ SSet.toTop.map (SSet.boundary n).ι =
        SSet.toTop.map (D.ι.app (WalkingMultispan.right (i : S.R))) ≫
          SSet.toTop.map (SSet.boundary n).ι :=
      congrArg (· ≫ SSet.toTop.map (SSet.boundary n).ι) hC
    have h2 : SSet.toTop.map (D.ι.app (WalkingMultispan.right (i : S.R))) ≫
          SSet.toTop.map (SSet.boundary n).ι =
        SSet.toTop.map (D.ι.app (WalkingMultispan.right (i : S.R)) ≫ (SSet.boundary n).ι) :=
      (SSet.toTop.map_comp _ _).symm
    have h3 : SSet.toTop.map (D.ι.app (WalkingMultispan.right (i : S.R)) ≫ (SSet.boundary n).ι) =
        SSet.toTop.map
          (SSet.stdSimplex.face (n := n) ({(i : Fin (n + 1))}ᶜ : Finset (Fin (n + 1)))).ι :=
      congrArg SSet.toTop.map hSSet
    have hEq : c.ι.app (WalkingMultispan.right (i : S.R)) ≫ SSet.toTop.map (SSet.boundary n).ι =
        SSet.toTop.map
          (SSet.stdSimplex.face (n := n) ({(i : Fin (n + 1))}ᶜ : Finset (Fin (n + 1)))).ι :=
      h1.trans (h2.trans h3)
    have hFace := isClosedEmbedding_realizedFaceInclusion n (i : S.R)
    have hComp : Topology.IsClosedEmbedding
        (c.ι.app (WalkingMultispan.right (i : S.R)) ≫ SSet.toTop.map (SSet.boundary n).ι) := by
      rw [hEq]
      exact hFace
    have hComp' : Topology.IsClosedEmbedding
        ((SSet.toTop.{u}.map (SSet.boundary.{u} n).ι : _ → _) ∘
          (c.ι.app (WalkingMultispan.right (i : S.R)) : _ → _)) := by
      convert hComp using 1
      funext x
      rfl
    exact Topology.IsClosedEmbedding.of_comp hbEmbed hComp'
  | WalkingMultispan.left p =>
    have h_le : SSet.stdSimplex.face (n := n) ({p.1.1, p.1.2}ᶜ : Finset (Fin (n + 1))) ≤
        SSet.boundary (n := n) := by
      calc SSet.stdSimplex.face ({p.1.1, p.1.2}ᶜ : Finset (Fin (n + 1)))
            ≤ SSet.stdSimplex.face ({p.1.1}ᶜ : Finset (Fin (n + 1))) := by
              rw [SSet.stdSimplex.face_le_face_iff]
              simp
        _ ≤ SSet.boundary n := SSet.face_singleton_compl_le_boundary (p.1.1 : S.R)
    have hOrig_le : SSet.stdSimplex.face (n := n) ({p.1.1, p.1.2}ᶜ : Finset (Fin (n + 1))) ≤
        SSet.boundary (n := n) := h_le
    have hD_left : D.ι.app (WalkingMultispan.left p) = SSet.Subcomplex.homOfLE h_le := by
      dsimp [D, S, MultispanShape.ofLinearOrder]
      change SSet.Subcomplex.homOfLE hOrig_le = SSet.Subcomplex.homOfLE h_le
      congr 1
    have hSSet : D.ι.app (WalkingMultispan.left p) ≫ (SSet.boundary (n := n)).ι =
        (SSet.stdSimplex.face (n := n) ({p.1.1, p.1.2}ᶜ : Finset (Fin (n + 1)))).ι := by
      rw [hD_left]
      exact SSet.Subcomplex.homOfLE_ι h_le
    have hC : c.ι.app (WalkingMultispan.left p) =
        SSet.toTop.map (D.ι.app (WalkingMultispan.left p)) := rfl
    have h1 : c.ι.app (WalkingMultispan.left p) ≫ SSet.toTop.map (SSet.boundary n).ι =
        SSet.toTop.map (D.ι.app (WalkingMultispan.left p)) ≫ SSet.toTop.map (SSet.boundary n).ι :=
      congrArg (· ≫ SSet.toTop.map (SSet.boundary n).ι) hC
    have h2 : SSet.toTop.map (D.ι.app (WalkingMultispan.left p)) ≫
          SSet.toTop.map (SSet.boundary n).ι =
        SSet.toTop.map (D.ι.app (WalkingMultispan.left p) ≫ (SSet.boundary n).ι) :=
      (SSet.toTop.map_comp _ _).symm
    have h3 : SSet.toTop.map (D.ι.app (WalkingMultispan.left p) ≫ (SSet.boundary n).ι) =
        SSet.toTop.map (SSet.stdSimplex.face (n := n) ({p.1.1, p.1.2}ᶜ : Finset (Fin (n + 1)))).ι :=
      congrArg SSet.toTop.map hSSet
    have hEq : c.ι.app (WalkingMultispan.left p) ≫ SSet.toTop.map (SSet.boundary n).ι =
        SSet.toTop.map (SSet.stdSimplex.face (n := n) ({p.1.1, p.1.2}ᶜ : Finset (Fin (n + 1)))).ι :=
      h1.trans (h2.trans h3)
    have hFace := isClosedEmbedding_realizedFacePair n (p.1.1 : S.R) (p.1.2 : S.R) p.2
    have hComp : Topology.IsClosedEmbedding
        (c.ι.app (WalkingMultispan.left p) ≫ SSet.toTop.map (SSet.boundary n).ι) := by
      rw [hEq]
      exact hFace
    have hComp' : Topology.IsClosedEmbedding
        ((SSet.toTop.{u}.map (SSet.boundary.{u} n).ι : _ → _) ∘
          (c.ι.app (WalkingMultispan.left p) : _ → _)) := by
      convert hComp using 1
      funext x
      rfl
    exact Topology.IsClosedEmbedding.of_comp hbEmbed hComp'

/-- Let `N : ℕ`, `u` a universe, and `q ∈ |Δ[N]|` lie in the image of `SSet.toTop.map
(SSet.boundary.{u} N).ι`. There exist `j : Fin (N+1)` and a point `y` of `|face {j}ᶜ|` whose
image under the realized face inclusion is `q`. The witnesses describe a codimension-one face
containing the realized boundary point. -/
theorem exists_face_of_mem_realizedBoundaryRange (N : ℕ)
    (q : SSet.toTop.obj (Δ[N] : SSet.{u}))
    (hq : q ∈ Set.range ⇑(SSet.toTop.map (SSet.boundary.{u} N).ι)) :
    ∃ (j : Fin (N + 1))
      (y : SSet.toTop.obj (SSet.stdSimplex.face (n := N) {j}ᶜ : SSet.{u})),
      SSet.toTop.map (SSet.stdSimplex.face (n := N) {j}ᶜ).ι y = q := by
  classical
  cases N with
  | zero =>
      have hEmpty : Set.range ⇑(SSet.toTop.map (SSet.boundary.{u} (0 : ℕ)).ι) = ∅ := by
        simpa using realizedBoundaryZero_range_empty
      rw [hEmpty] at hq
      simp at hq
  | succ n =>
      let S := MultispanShape.ofLinearOrder (Fin (n + 2))
      let DI : MultispanIndex S SSet.{u} :=
        ((multicoequalizerDiagram (n := n + 1)).multispanIndex.toLinearOrder.map
          Subcomplex.toSSetFunctor)
      let D : Cocone DI.multispan :=
        (multicoequalizerDiagram (n := n + 1)).multicofork.toLinearOrder.map
          Subcomplex.toSSetFunctor
      let c : Cocone (DI.multispan ⋙ SSet.toTop.{u}) := SSet.toTop.mapCocone D
      have hc : IsColimit c := isColimitToTop' (n := n + 1)
      have hcType : IsColimit ((forget TopCat).mapCocone c) :=
        isColimitOfPreserves (forget TopCat) hc
      obtain ⟨x, hx⟩ := hq
      obtain ⟨j, z, hz⟩ := Types.jointly_surjective_of_isColimit hcType x
      have hRight : ∃ (i : Fin (n + 2))
          (p : SSet.toTop.obj (SSet.stdSimplex.face (n := n + 1) {i}ᶜ : SSet.{u})),
          c.ι.app (WalkingMultispan.right (i : S.R)) p = x := by
        cases j with
        | right i =>
            exact ⟨(i : Fin (n + 2)), z, hz⟩
        | left p =>
            let i : Fin (n + 2) := p.1.1
            let jj : Fin (n + 2) := p.1.2
            have hLE : SSet.stdSimplex.face (n := n + 1)
                    ({i, jj}ᶜ : Finset (Fin (n + 2))) ≤
                  SSet.stdSimplex.face (n := n + 1) ({i}ᶜ : Finset (Fin (n + 2))) := by
              rw [SSet.stdSimplex.face_le_face_iff]
              simp
            have hOrigLE : SSet.stdSimplex.face (n := n + 1)
                    ({i, jj}ᶜ : Finset (Fin (n + 2))) ≤
                  SSet.stdSimplex.face (n := n + 1) ({i}ᶜ : Finset (Fin (n + 2))) := hLE
            have hDI_fst : DI.fst p = SSet.Subcomplex.homOfLE hLE := by
              dsimp [DI, S, MultispanShape.ofLinearOrder]
              change SSet.Subcomplex.homOfLE hOrigLE = SSet.Subcomplex.homOfLE hLE
              congr 1
            have hFst_eq : (DI.multispan ⋙ SSet.toTop.{u}).map (WalkingMultispan.Hom.fst p) =
                SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) := by
              change SSet.toTop.map (DI.fst p) = SSet.toTop.map (SSet.Subcomplex.homOfLE hLE)
              rw [hDI_fst]
              rfl
            have hW : c.ι.app (WalkingMultispan.left p) z =
                c.ι.app (WalkingMultispan.right (S.fst p))
                  (SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) z) := by
              have hEq : SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) ≫
                      c.ι.app (WalkingMultispan.right (S.fst p)) =
                    c.ι.app (WalkingMultispan.left p) := by
                rw [← hFst_eq]
                exact c.w (WalkingMultispan.Hom.fst p)
              have hEq_congr := ConcreteCategory.congr_hom hEq z
              have hcomp := ConcreteCategory.comp_apply (C := TopCat)
                (SSet.toTop.map (SSet.Subcomplex.homOfLE hLE))
                (c.ι.app (WalkingMultispan.right (S.fst p))) z
              exact hEq_congr.symm.trans hcomp
            exact ⟨S.fst p, SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) z, by
              simpa using hW.symm.trans hz⟩
      obtain ⟨i₀, p₀, hp₀⟩ := hRight
      refine ⟨i₀, p₀, ?_⟩
      have hD_right : D.ι.app (WalkingMultispan.right (i₀ : S.R)) =
          SSet.Subcomplex.homOfLE
            (SSet.face_singleton_compl_le_boundary (n := n + 1) (i₀ : S.R)) := by
        dsimp [D, S, MultispanShape.ofLinearOrder]
        rfl
      have hFaceEq : SSet.Subcomplex.homOfLE
              (SSet.face_singleton_compl_le_boundary (n := n + 1) (i₀ : Fin (n + 2))) =
            SSet.boundary.faceι (i₀ : Fin (n + 2)) := rfl
      have hSSet : D.ι.app (WalkingMultispan.right (i₀ : S.R)) ≫
              (SSet.boundary (n + 1)).ι =
            (SSet.stdSimplex.face (n := n + 1) ({i₀}ᶜ : Finset (Fin (n + 2)))).ι := by
        rw [hD_right, hFaceEq]
        exact SSet.boundary.faceι_ι (i₀ : Fin (n + 2))
      have hC : c.ι.app (WalkingMultispan.right (i₀ : S.R)) =
          SSet.toTop.map (D.ι.app (WalkingMultispan.right (i₀ : S.R))) := rfl
      have hEq : c.ι.app (WalkingMultispan.right (i₀ : S.R)) ≫
              SSet.toTop.map (SSet.boundary (n + 1)).ι =
            SSet.toTop.map
              (SSet.stdSimplex.face (n := n + 1) ({i₀}ᶜ : Finset (Fin (n + 2)))).ι := by
        erw [hC, ← SSet.toTop.map_comp, hSSet]
        rfl
      have h_congr := ConcreteCategory.congr_hom hEq p₀
      have hcomp := ConcreteCategory.comp_apply (C := TopCat)
        (c.ι.app (WalkingMultispan.right (i₀ : S.R)))
        (SSet.toTop.map (SSet.boundary (n + 1)).ι) p₀
      rw [hcomp, hp₀] at h_congr
      exact h_congr.symm.trans hx

/-- For `N : ℕ` and `q : SSet.toTop.obj (Δ[N] : SSet.{u})` in the image of the realized boundary inclusion, there exists
`j : Fin (N+1)` with
`(⦋N⦌.toTopHomeo q).weights j=0`.
The standard-simplex homeomorphism therefore sends that point to a barycentric coordinate face. -/
theorem mem_zeroCoord_of_mem_realizedBoundaryRange (N : ℕ)
    (q : SSet.toTop.obj (Δ[N] : SSet.{u}))
    (hq : q ∈ Set.range ⇑(SSet.toTop.map (SSet.boundary.{u} N).ι)) :
    ∃ j : Fin (N + 1), (⦋N⦌.toTopHomeo q).weights j = 0 := by
  cases N with
  | zero =>
      have hEmpty : Set.range ⇑(SSet.toTop.map (SSet.boundary.{u} (0 : ℕ)).ι) = ∅ := by
        simpa using realizedBoundaryZero_range_empty
      rw [hEmpty] at hq
      simp at hq
  | succ n =>
      obtain ⟨j, y, hy⟩ := exists_face_of_mem_realizedBoundaryRange (n + 1) q hq
      exact ⟨j, singleton_face_coord_zero j y _ (by rw [hy])⟩

end boundary

end SSet
