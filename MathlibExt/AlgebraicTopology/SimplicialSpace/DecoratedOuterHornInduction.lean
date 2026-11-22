/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.DecoratedOuterTwoHornMapping
import MathlibExt.AlgebraicTopology.SimplicialSpace.OuterHornCMappingRestriction
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalOuterHornCMappingPresentation
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalInitialIntervalCover
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerHomColimits

/-!
# The original higher initial decorated outer-horn restrictions

The two overlaps in the induction are the original first coface and the
original zero-coface tail. Every decoration tests all original edges.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SimplicialSpace.Inner SSet.modelCategoryQuillen

namespace SimplicialSpace.DecoratedOuterHorn
open SegalHomotopy

private def simplexFactor {X : SSet.{u}} (A : X.Subcomplex) {n : ℕ}
    (f : (Δ[n] : SSet.{u}) ⟶ X) (hf : SSet.yonedaEquiv f ∈ A.obj (op ⦋n⦌)) :
    (Δ[n] : SSet.{u}) ⟶ A :=
  SSet.Subcomplex.lift f (by
    rw [SSet.Subcomplex.range_eq_ofSimplex, SSet.Subcomplex.ofSimplex_le_iff]
    exact hf)

private theorem simplexFactor_ι {X : SSet.{u}} (A : X.Subcomplex) {n : ℕ}
    (f : (Δ[n] : SSet.{u}) ⟶ X) (hf : SSet.yonedaEquiv f ∈ A.obj (op ⦋n⦌)) :
    simplexFactor A f hf ≫ A.ι = f := SSet.Subcomplex.lift_ι _ _

private def pointArrow (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (g : (W.diagram _⦋1⦌) _⦋0⦌)
    (hs : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g = x)
    (ht : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g = y) :
    (Δ[0] : SSet.{u}) ⟶ mappingFibre W x y :=
  pullback.lift (SSet.yonedaEquiv.symm g) (𝟙 _) (by
    apply prod.hom_ext
    · rw [Category.assoc, mappingEndpoint_fst, Category.id_comp,
        mappingPointPair_fst, SSet.yonedaEquiv_symm_comp, hs]
    · rw [Category.assoc, mappingEndpoint_snd, Category.id_comp,
        mappingPointPair_snd, SSet.yonedaEquiv_symm_comp, ht])

private def point (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (g : (W.diagram _⦋1⦌) _⦋0⦌)
    (hs : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g = x)
    (ht : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g = y) :
    (mappingFibre W x y) _⦋0⦌ := SSet.yonedaEquiv (pointArrow W x y g hs ht)

private theorem point_fst (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (g : (W.diagram _⦋1⦌) _⦋0⦌)
    (hs : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g = x)
    (ht : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g = y) :
    (mappingFibre.fst W x y).app (op ⦋0⦌) (point W x y g hs ht) = g := by
  change SSet.yonedaEquiv (pointArrow W x y g hs ht ≫ mappingFibre.fst W x y) = g
  rw [show pointArrow W x y g hs ht ≫ mappingFibre.fst W x y =
    SSet.yonedaEquiv.symm g from pullback.lift_fst _ _ _, Equiv.apply_symm_apply]

private theorem triangleEquivalence (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (t : (W.diagram _⦋2⦌) _⦋0⦌)
    (ha : IsEquivalenceEdge W hW ((W.diagram.δ (2 : Fin 3)).app (op ⦋0⦌) t))
    (hb : IsEquivalenceEdge W hW ((W.diagram.δ (0 : Fin 3)).app (op ⦋0⦌) t)) :
    IsEquivalenceEdge W hW ((W.diagram.δ (1 : Fin 3)).app (op ⦋0⦌) t) := by
  let a₀ := (W.diagram.δ (2 : Fin 3)).app (op ⦋0⦌) t
  let b₀ := (W.diagram.δ (0 : Fin 3)).app (op ⦋0⦌) t
  let c₀ := (W.diagram.δ (1 : Fin 3)).app (op ⦋0⦌) t
  let x := (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) a₀
  let y := (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) a₀
  let z := (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) b₀
  have hb₀ : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) b₀ = y := by
    exact congrArg (fun f => f.app (op ⦋0⦌) t)
      (W.diagram.δ_comp_δ (i := (0 : Fin 2)) (j := 1) (by decide)).symm
  have hc₀ : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) c₀ = x := by
    exact congrArg (fun f => f.app (op ⦋0⦌) t)
      (W.diagram.δ_comp_δ_self (i := (1 : Fin 2)))
  have hc₁ : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) c₀ = z := by
    exact congrArg (fun f => f.app (op ⦋0⦌) t)
      (W.diagram.δ_comp_δ_self (i := (0 : Fin 2))).symm
  let a := point W x y a₀ rfl rfl
  let b := point W y z b₀ hb₀ rfl
  let c := point W x z c₀ hc₀ hc₁
  have ha' : (mappingFibre.fst W x y).app (op ⦋0⦌) a = a₀ := point_fst ..
  have hb' : (mappingFibre.fst W y z).app (op ⦋0⦌) b = b₀ := point_fst ..
  have hc' : (mappingFibre.fst W x z).app (op ⦋0⦌) c = c₀ := point_fst ..
  have he : compose W hW (SSet.π₀.mk a) (SSet.π₀.mk b) = SSet.π₀.mk c :=
    compose_of_original_triangle W hW t a b c ha' hb' hc'
  let _ : IsIso (C := Object W hW) (X := ⟨x⟩) (Y := ⟨y⟩) (SSet.π₀.mk a) :=
    (isEquivalenceEdge_iff_of_fibre W hW a₀ a ha').mp ha
  let _ : IsIso (C := Object W hW) (X := ⟨y⟩) (Y := ⟨z⟩) (SSet.π₀.mk b) :=
    (isEquivalenceEdge_iff_of_fibre W hW b₀ b hb').mp hb
  apply (isEquivalenceEdge_iff_of_fibre W hW c₀ c hc').mpr
  rw [← he]
  exact IsIso.comp_isIso (C := Object W hW) (X := ⟨x⟩) (Y := ⟨y⟩) (Z := ⟨z⟩)
    (f := SSet.π₀.mk a) (h := SSet.π₀.mk b)

private theorem selectedEvaluation {A B : SSet.{u}} (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (i : A ⟶ B)
    (q : ((discreteSourceMapping W).obj (op B)) _⦋0⦌)
    (hq : ((discreteSourceMapping W).map i.op).app (op ⦋0⦌) q ∈
      (EquivalenceMapping.subcomplex W hW A).obj (op ⦋0⦌))
    (γ : (Δ[1] : SSet.{u}) ⟶ B) (δ : (Δ[1] : SSet.{u}) ⟶ A)
    (hδ : δ ≫ i = γ) :
    IsEquivalenceEdge W hW ((EquivalenceMapping.edgeEvaluation W γ).app (op ⦋0⦌) q) := by
  have h := (mem_equivalenceSubcomplex_zero W hW _).mp
    ((EquivalenceMapping.mem_subcomplex W hW A _ _).mp hq δ)
  change IsEquivalenceEdge W hW
    (((discreteSourceMapping W).map i.op ≫ EquivalenceMapping.edgeEvaluation W δ).app
      (op ⦋0⦌) q) at h
  rw [EquivalenceMapping.edgeEvaluation_source, hδ] at h
  exact h

private theorem constantEvaluation {A : SSet.{u}} (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (q : ((discreteSourceMapping W).obj (op A)) _⦋0⦌)
    (v : (Δ[0] : SSet.{u}) ⟶ A) :
    IsEquivalenceEdge W hW
      ((EquivalenceMapping.edgeEvaluation W (SSet.stdSimplex.σ (0 : Fin 1) ≫ v)).app
        (op ⦋0⦌) q) := by
  rw [← EquivalenceMapping.edgeEvaluation_source]
  change IsEquivalenceEdge W hW
    (((discreteSourceMapping W).map v.op ≫
      ((discreteSourceMapping W).map (SSet.stdSimplex.map (SimplexCategory.σ 0)).op ≫
        (discreteYonedaIso W 1).hom)).app (op ⦋0⦌) q)
  rw [discreteYonedaIso_naturality_index]
  exact identity_isEquivalenceEdge W hW _

private theorem selectedSubsetEdge {X : SSet.{u}} (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (A B : X.Subcomplex) (hBA : B ≤ A)
    (q : ((discreteSourceMapping W).obj (op (A : SSet.{u}))) _⦋0⦌)
    (hq : ((discreteSourceMapping W).map (SSet.Subcomplex.homOfLE hBA).op).app
      (op ⦋0⦌) q ∈ (EquivalenceMapping.subcomplex W hW (B : SSet.{u})).obj (op ⦋0⦌))
    (γ : (Δ[1] : SSet.{u}) ⟶ A)
    (hγ : SSet.yonedaEquiv (γ ≫ A.ι) ∈ B.obj (op ⦋1⦌)) :
    IsEquivalenceEdge W hW ((EquivalenceMapping.edgeEvaluation W γ).app (op ⦋0⦌) q) := by
  let δ := simplexFactor B (γ ≫ A.ι) hγ
  have hδ : δ ≫ SSet.Subcomplex.homOfLE hBA = γ := by
    apply (cancel_mono A.ι).mp
    rw [Category.assoc, SSet.Subcomplex.homOfLE_ι, simplexFactor_ι]
  exact selectedEvaluation W hW _ q hq γ δ hδ

private theorem restrictionPullback {A B : SSet.{u}} (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (i : A ⟶ B)
    (he : EquivalenceMapping.subcomplex W hW B =
      (EquivalenceMapping.subcomplex W hW A).preimage ((discreteSourceMapping W).map i.op)) :
    IsPullback (EquivalenceMapping.subcomplex W hW B).ι
      (EquivalenceMapping.restriction W hW i)
      ((discreteSourceMapping W).map i.op) (EquivalenceMapping.subcomplex W hW A).ι := by
  have aux (U : ((discreteSourceMapping W).obj (op B)).Subcomplex)
      (hU : U = (EquivalenceMapping.subcomplex W hW A).preimage
        ((discreteSourceMapping W).map i.op))
      (hR : SSet.Subcomplex.range (U.ι ≫ (discreteSourceMapping W).map i.op) ≤
        EquivalenceMapping.subcomplex W hW A) :
      IsPullback U.ι (SSet.Subcomplex.lift (U.ι ≫ (discreteSourceMapping W).map i.op) hR)
        ((discreteSourceMapping W).map i.op) (EquivalenceMapping.subcomplex W hW A).ι := by
    subst U
    exact Subfunctor.preimage_isPullback _ _
  exact aux _ he _

private def rootOrder (m : ℕ) (b : Fin (m + 3)) (hb : 2 ≤ b.val) : ⦋2⦌ ⟶ ⦋m + 2⦌ :=
  SimplexCategory.Hom.mk
    ⟨Fin.cases 0 (Fin.cases 1 (fun _ => b)), by
      intro i j hij
      fin_cases i <;> fin_cases j
      · exact le_rfl
      · change (0 : ℕ) ≤ 1; omega
      · exact Fin.zero_le b
      · exact False.elim ((by decide : ¬ ((1 : Fin 3) ≤ 0)) hij)
      · exact le_rfl
      · change 1 ≤ b.val; omega
      · exact False.elim ((by decide : ¬ ((2 : Fin 3) ≤ 0)) hij)
      · exact False.elim ((by decide : ¬ ((2 : Fin 3) ≤ 1)) hij)
      · exact le_rfl⟩

private theorem rootOrder_zero (m : ℕ) (b : Fin (m + 3)) (hb : 2 ≤ b.val) :
    (rootOrder m b hb).toOrderHom 0 = 0 := rfl

private theorem rootOrder_one (m : ℕ) (b : Fin (m + 3)) (hb : 2 ≤ b.val) :
    (rootOrder m b hb).toOrderHom 1 = 1 := rfl

private theorem rootOrder_two (m : ℕ) (b : Fin (m + 3)) (hb : 2 ≤ b.val) :
    (rootOrder m b hb).toOrderHom 2 = b := rfl

private theorem rootOrder_mem_C (m : ℕ) (hm : 1 ≤ m) (b : Fin (m + 3)) (hb : 2 ≤ b.val) :
    SSet.yonedaEquiv.{u} (SSet.stdSimplex.map (rootOrder m b hb)) ∈
      (SSet.Rezk.outerHornC (m + 2)).obj (op ⦋2⦌) := by
  rw [SSet.Rezk.mem_outerHornC_iff]
  let j : Fin (m + 3) := ⟨if b.val = 2 then 3 else 2, by split_ifs <;> omega⟩
  refine ⟨j, by dsimp [j]; split_ifs <;> omega, ?_⟩
  rintro ⟨i, hi⟩
  rw [SSet.yonedaEquiv_map] at hi
  have hv := congrArg Fin.val hi
  fin_cases i
  · change 0 = (if b.val = 2 then 3 else 2) at hv
    by_cases h : b.val = 2 <;> simp [h] at hv
  · change 1 = (if b.val = 2 then 3 else 2) at hv
    split_ifs at hv <;> omega
  · change b.val = (if b.val = 2 then 3 else 2) at hv
    split_ifs at hv <;> omega

private def rootTriangleC (m : ℕ) (hm : 1 ≤ m) (b : Fin (m + 3)) (hb : 2 ≤ b.val) :
    (Δ[2] : SSet.{u}) ⟶ (SSet.Rezk.outerHornC (m + 2) : SSet.{u}) :=
  simplexFactor _ (SSet.stdSimplex.map (rootOrder m b hb)) (rootOrder_mem_C m hm b hb)

private theorem rootTriangleC_ι (m : ℕ) (hm : 1 ≤ m) (b : Fin (m + 3)) (hb : 2 ≤ b.val) :
    rootTriangleC.{u} m hm b hb ≫ (SSet.Rezk.outerHornC (m + 2)).ι =
      SSet.stdSimplex.map (rootOrder m b hb) := simplexFactor_ι _ _ _

private theorem triangleEvaluation_face {A : SSet.{u}} (W : SimplicialSpace.{u})
    (τ : (Δ[2] : SSet.{u}) ⟶ A) (i : Fin 3) :
    EquivalenceMapping.edgeEvaluation W (SSet.stdSimplex.δ i ≫ τ) =
      (discreteSourceMapping W).map τ.op ≫ (discreteYonedaIso W 2).hom ≫ W.diagram.δ i := by
  rw [← EquivalenceMapping.edgeEvaluation_source]
  change (discreteSourceMapping W).map τ.op ≫
      ((discreteSourceMapping W).map (SSet.stdSimplex.map (SimplexCategory.δ i)).op ≫
        (discreteYonedaIso W 1).hom) = _
  rw [discreteYonedaIso_naturality_index]
  rfl

private theorem triangleEvaluation {A : SSet.{u}} (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (q : ((discreteSourceMapping W).obj (op A)) _⦋0⦌)
    (τ : (Δ[2] : SSet.{u}) ⟶ A)
    (ha : IsEquivalenceEdge W hW
      ((EquivalenceMapping.edgeEvaluation W (SSet.stdSimplex.δ (2 : Fin 3) ≫ τ)).app
        (op ⦋0⦌) q))
    (hb : IsEquivalenceEdge W hW
      ((EquivalenceMapping.edgeEvaluation W (SSet.stdSimplex.δ (0 : Fin 3) ≫ τ)).app
        (op ⦋0⦌) q)) :
    IsEquivalenceEdge W hW
      ((EquivalenceMapping.edgeEvaluation W (SSet.stdSimplex.δ (1 : Fin 3) ≫ τ)).app
        (op ⦋0⦌) q) := by
  rw [triangleEvaluation_face] at ha hb ⊢
  exact triangleEquivalence W hW _ ha hb

private theorem tailEdge_mem_U (m : ℕ) (a : (Δ[m + 2] : SSet.{u}) _⦋1⦌)
    (ha : a ∈ (SSet.Rezk.outerHornC (m + 2)).obj (op ⦋1⦌))
    (hz : ∀ i : Fin 2, a i ≠ 0) : a ∈ (SSet.Rezk.outerHornCU m).obj (op ⦋1⦌) := by
  rw [SSet.Rezk.outerHornCU, SSet.Rezk.outerHorn_image_cofaceZero]
  refine Or.inl ⟨ha, ?_⟩
  rw [SSet.stdSimplex.mem_face_iff]
  simpa only [Finset.mem_compl, Finset.mem_singleton] using hz

private theorem firstEdge_mem_U (m : ℕ) (a : (Δ[m + 2] : SSet.{u}) _⦋1⦌)
    (ha : ∀ i : Fin 2, a i = 0 ∨ a i = 1) :
    a ∈ (SSet.Rezk.outerHornCU m).obj (op ⦋1⦌) := by
  refine Or.inr ?_
  rw [SSet.stdSimplex.mem_face_iff]
  simpa only [Finset.mem_insert, Finset.mem_singleton] using ha

private theorem rootTriangleC_first (m : ℕ) (hm : 1 ≤ m) (b : Fin (m + 3)) (hb : 2 ≤ b.val) :
    SSet.yonedaEquiv
      ((SSet.stdSimplex.δ (2 : Fin 3) ≫ rootTriangleC.{u} m hm b hb) ≫
        (SSet.Rezk.outerHornC (m + 2)).ι) ∈
      (SSet.Rezk.outerHornCU m).obj (op ⦋1⦌) := by
  apply firstEdge_mem_U
  intro i
  change (SSet.yonedaEquiv
    ((SSet.stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) ≫ rootTriangleC.{u} m hm b hb) ≫
      (SSet.Rezk.outerHornC (m + 2)).ι)) i = 0 ∨ _
  rw [Category.assoc, rootTriangleC_ι, ← SSet.stdSimplex.map_comp, SSet.yonedaEquiv_map]
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem rootTriangleC_last (m : ℕ) (hm : 1 ≤ m) (b : Fin (m + 3)) (hb : 2 ≤ b.val) :
    SSet.yonedaEquiv
      ((SSet.stdSimplex.δ (0 : Fin 3) ≫ rootTriangleC.{u} m hm b hb) ≫
        (SSet.Rezk.outerHornC (m + 2)).ι) ∈
      (SSet.Rezk.outerHornCU m).obj (op ⦋1⦌) := by
  apply tailEdge_mem_U
  · rw [← SSet.Subcomplex.yonedaEquiv_coe]
    exact (SSet.yonedaEquiv (SSet.stdSimplex.δ (0 : Fin 3) ≫ rootTriangleC.{u} m hm b hb)).property
  · intro i
    change (SSet.yonedaEquiv
      ((SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 3)) ≫ rootTriangleC.{u} m hm b hb) ≫
        (SSet.Rezk.outerHornC (m + 2)).ι)) i ≠ 0
    rw [Category.assoc, rootTriangleC_ι, ← SSet.stdSimplex.map_comp, SSet.yonedaEquiv_map]
    fin_cases i
    · intro h; have hv := congrArg Fin.val h; change 1 = 0 at hv; omega
    · intro h; have hv := congrArg Fin.val h; change b.val = 0 at hv; omega

private theorem allC_zero (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (m : ℕ) (hm : 1 ≤ m)
    (q : ((discreteSourceMapping W).obj (op (SSet.Rezk.outerHornC (m + 2) : SSet.{u}))) _⦋0⦌)
    (hq : (OuterHornCMapping.restriction W m).app (op ⦋0⦌) q ∈
      (EquivalenceMapping.subcomplex W hW (SSet.Rezk.outerHornCU m : SSet.{u})).obj (op ⦋0⦌)) :
    ∀ γ : (Δ[1] : SSet.{u}) ⟶ (SSet.Rezk.outerHornC (m + 2) : SSet.{u}),
      IsEquivalenceEdge W hW ((EquivalenceMapping.edgeEvaluation W γ).app (op ⦋0⦌) q) := by
  intro γ
  obtain ⟨θ, hθ⟩ := SSet.stdSimplex.map_surjective (γ ≫ (SSet.Rezk.outerHornC (m + 2)).ι)
  have hγ : γ ≫ (SSet.Rezk.outerHornC (m + 2)).ι = SSet.stdSimplex.map θ := hθ.symm
  have hC : SSet.yonedaEquiv (γ ≫ (SSet.Rezk.outerHornC (m + 2)).ι) ∈
      (SSet.Rezk.outerHornC (m + 2)).obj (op ⦋1⦌) := by
    rw [← SSet.Subcomplex.yonedaEquiv_coe]
    exact (SSet.yonedaEquiv γ).property
  by_cases h0 : θ.toOrderHom 0 = 0
  · by_cases hb : (θ.toOrderHom 1).val ≤ 1
    · apply selectedSubsetEdge W hW _ _ (SSet.Rezk.outerHornCU_le_C m) q hq γ
      apply firstEdge_mem_U
      intro i
      rw [hγ, SSet.yonedaEquiv_map]
      fin_cases i
      · exact Or.inl h0
      · by_cases h : (θ.toOrderHom 1).val = 0
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext (by change (θ.toOrderHom 1).val = 1; omega))
    · have hb' : 2 ≤ (θ.toOrderHom 1).val := by omega
      let τ := rootTriangleC.{u} m hm (θ.toOrderHom 1) hb'
      have hτ : SSet.stdSimplex.δ (1 : Fin 3) ≫ τ = γ := by
        apply (cancel_mono (SSet.Rezk.outerHornC (m + 2)).ι).mp
        rw [Category.assoc, rootTriangleC_ι, hγ]
        change SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 3)) ≫
          SSet.stdSimplex.map (rootOrder m (θ.toOrderHom 1) hb') = SSet.stdSimplex.map θ
        rw [← SSet.stdSimplex.map_comp]
        congr 1
        exact SimplexCategory.Hom.ext_one_left _ _ h0.symm rfl
      rw [← hτ]
      apply triangleEvaluation W hW q τ
      · exact selectedSubsetEdge W hW _ _ (SSet.Rezk.outerHornCU_le_C m) q hq _
          (rootTriangleC_first m hm (θ.toOrderHom 1) hb')
      · exact selectedSubsetEdge W hW _ _ (SSet.Rezk.outerHornCU_le_C m) q hq _
          (rootTriangleC_last m hm (θ.toOrderHom 1) hb')
  · apply selectedSubsetEdge W hW _ _ (SSet.Rezk.outerHornCU_le_C m) q hq γ
    apply tailEdge_mem_U m _ hC
    intro i hi
    rw [hγ, SSet.yonedaEquiv_map] at hi
    change θ.toOrderHom i = 0 at hi
    have hle := θ.toOrderHom.monotone (Fin.zero_le i)
    rw [hi] at hle
    exact h0 (le_antisymm hle (Fin.zero_le _))

/-- The actual C decoration is the semantic preimage of the original U decoration. -/
theorem cDecoration_preimage (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (m : ℕ) (hm : 1 ≤ m) :
    EquivalenceMapping.subcomplex W hW (SSet.Rezk.outerHornC (m + 2) : SSet.{u}) =
      (EquivalenceMapping.subcomplex W hW (SSet.Rezk.outerHornCU m : SSet.{u})).preimage
        (OuterHornCMapping.restriction W m) := by
  ext n q
  constructor
  · intro hq
    exact ((EquivalenceMapping.restriction W hW (OuterHornCMapping.inclusion m)).app
      n ⟨q, hq⟩).property
  · intro hq
    let α := SimplexCategory.const ⦋0⦌ n.unop 0
    let q₀ := ((discreteSourceMapping W).obj
      (op (SSet.Rezk.outerHornC (m + 2) : SSet.{u}))).map α.op q
    have hq₀ : (OuterHornCMapping.restriction W m).app (op ⦋0⦌) q₀ ∈
        (EquivalenceMapping.subcomplex W hW (SSet.Rezk.outerHornCU m : SSet.{u})).obj
          (op ⦋0⦌) := by
      have h := (EquivalenceMapping.mem_subcomplex_operator W hW _ α.op _).mp hq
      rw [← (OuterHornCMapping.restriction W m).naturality_apply] at h
      exact h
    exact (EquivalenceMapping.mem_subcomplex_vertex W hW _ n q α).mpr
      (allC_zero W hW m hm q₀ hq₀)

/-- Both original inclusions give the actual decorated C/U pullback. -/
theorem cRestriction_isPullback (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (m : ℕ) (hm : 1 ≤ m) :
    IsPullback (EquivalenceMapping.subcomplex W hW
      (SSet.Rezk.outerHornC (m + 2) : SSet.{u})).ι
      (EquivalenceMapping.restriction W hW (OuterHornCMapping.inclusion m))
      (OuterHornCMapping.restriction W m)
      (EquivalenceMapping.subcomplex W hW (SSet.Rezk.outerHornCU m : SSet.{u})).ι :=
  restrictionPullback W hW _ (cDecoration_preimage W hW m hm)

/-- The original C/U restriction is trivial on the exact all-edge decorations. -/
theorem cRestriction_trivialFibration (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (m : ℕ) (hm : 1 ≤ m) :
    trivialFibrations SSet.{u}
      (EquivalenceMapping.restriction W hW (OuterHornCMapping.inclusion m)) :=
  (trivialFibrations SSet.{u}).of_isPullback (cRestriction_isPullback W hW m hm)
    (OuterHornCMapping.restriction_trivialFibration W hW m)

private theorem tailEdge_mem_T (m : ℕ) (a : (Δ[m + 2] : SSet.{u}) _⦋1⦌)
    (hz : ∀ i : Fin 2, a i ≠ 0) :
    a ∈ (SSet.Rezk.initialIntervalCover (m + 2)).obj (op ⦋1⦌) := by
  refine Or.inl ?_
  rw [SSet.stdSimplex.mem_face_iff]
  simpa only [Finset.mem_compl, Finset.mem_singleton] using hz

private theorem firstEdge_mem_T (m : ℕ) (a : (Δ[m + 2] : SSet.{u}) _⦋1⦌)
    (ha : ∀ i : Fin 2, a i = 0 ∨ a i = 1) :
    a ∈ (SSet.Rezk.initialIntervalCover (m + 2)).obj (op ⦋1⦌) := by
  refine Or.inr ?_
  rw [SSet.stdSimplex.mem_face_iff]
  simpa only [Finset.mem_insert, Finset.mem_singleton] using ha

private theorem selectedIntervalEdge (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (m : ℕ) (q : ((discreteSourceMapping W).obj (op (Δ[m + 2] : SSet.{u}))) _⦋0⦌)
    (hq : ((discreteSourceMapping W).map (SSet.Rezk.initialIntervalCover (m + 2)).ι.op).app
      (op ⦋0⦌) q ∈
      (EquivalenceMapping.subcomplex W hW (SSet.Rezk.initialIntervalCover (m + 2) : SSet.{u})).obj
        (op ⦋0⦌)) (γ : (Δ[1] : SSet.{u}) ⟶ Δ[m + 2])
    (hγ : SSet.yonedaEquiv γ ∈ (SSet.Rezk.initialIntervalCover (m + 2)).obj (op ⦋1⦌)) :
    IsEquivalenceEdge W hW ((EquivalenceMapping.edgeEvaluation W γ).app (op ⦋0⦌) q) :=
  selectedEvaluation W hW _ q hq γ (simplexFactor _ γ hγ) (simplexFactor_ι _ _ _)

private theorem allDelta_zero (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (m : ℕ) (q : ((discreteSourceMapping W).obj (op (Δ[m + 2] : SSet.{u}))) _⦋0⦌)
    (hq : ((discreteSourceMapping W).map (SSet.Rezk.initialIntervalCover (m + 2)).ι.op).app
      (op ⦋0⦌) q ∈
      (EquivalenceMapping.subcomplex W hW (SSet.Rezk.initialIntervalCover (m + 2) : SSet.{u})).obj
        (op ⦋0⦌)) :
    ∀ γ : (Δ[1] : SSet.{u}) ⟶ Δ[m + 2],
      IsEquivalenceEdge W hW ((EquivalenceMapping.edgeEvaluation W γ).app (op ⦋0⦌) q) := by
  intro γ
  obtain ⟨θ, rfl⟩ := SSet.stdSimplex.map_surjective γ
  by_cases h0 : θ.toOrderHom 0 = 0
  · by_cases hb : (θ.toOrderHom 1).val ≤ 1
    · apply selectedIntervalEdge W hW m q hq
      apply firstEdge_mem_T
      intro i
      rw [SSet.yonedaEquiv_map]
      fin_cases i
      · exact Or.inl h0
      · by_cases h : (θ.toOrderHom 1).val = 0
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext (by change (θ.toOrderHom 1).val = 1; omega))
    · have hb' : 2 ≤ (θ.toOrderHom 1).val := by omega
      let τ : (Δ[2] : SSet.{u}) ⟶ Δ[m + 2] :=
        SSet.stdSimplex.map (rootOrder m (θ.toOrderHom 1) hb')
      have hτ : SSet.stdSimplex.δ (1 : Fin 3) ≫ τ = SSet.stdSimplex.map θ := by
        change SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 3)) ≫
          SSet.stdSimplex.map (rootOrder m (θ.toOrderHom 1) hb') = SSet.stdSimplex.map θ
        rw [← SSet.stdSimplex.map_comp]
        congr 1
        exact SimplexCategory.Hom.ext_one_left _ _ h0.symm rfl
      rw [← hτ]
      apply triangleEvaluation W hW q τ
      · apply selectedIntervalEdge W hW m q hq
        apply firstEdge_mem_T
        intro i
        change (SSet.yonedaEquiv.{u} (SSet.stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) ≫
          SSet.stdSimplex.map (rootOrder m (θ.toOrderHom 1) hb'))) i = 0 ∨ _
        rw [← SSet.stdSimplex.map_comp, SSet.yonedaEquiv_map]
        fin_cases i
        · exact Or.inl rfl
        · exact Or.inr rfl
      · apply selectedIntervalEdge W hW m q hq
        apply tailEdge_mem_T
        intro i hi
        change (SSet.yonedaEquiv.{u} (SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 3)) ≫
          SSet.stdSimplex.map (rootOrder m (θ.toOrderHom 1) hb'))) i = 0 at hi
        rw [← SSet.stdSimplex.map_comp, SSet.yonedaEquiv_map] at hi
        have hv := congrArg Fin.val hi
        fin_cases i
        · change 1 = 0 at hv; omega
        · change (θ.toOrderHom 1).val = 0 at hv; omega
  · apply selectedIntervalEdge W hW m q hq
    apply tailEdge_mem_T
    intro i hi
    rw [SSet.yonedaEquiv_map] at hi
    change θ.toOrderHom i = 0 at hi
    have hle := θ.toOrderHom.monotone (Fin.zero_le i)
    rw [hi] at hle
    exact h0 (le_antisymm hle (Fin.zero_le _))

/-- Selection on the original simplex is exactly the preimage from its tail-edge cover. -/
theorem deltaDecoration_preimage (W : SimplicialSpace.{u}) (hW : segalSpaces W) (m : ℕ) :
    EquivalenceMapping.subcomplex W hW (Δ[m + 2] : SSet.{u}) =
      (EquivalenceMapping.subcomplex W hW
        (SSet.Rezk.initialIntervalCover (m + 2) : SSet.{u})).preimage
          ((discreteSourceMapping W).map (SSet.Rezk.initialIntervalCover (m + 2)).ι.op) := by
  ext n q
  constructor
  · intro hq
    exact ((EquivalenceMapping.restriction W hW (SSet.Rezk.initialIntervalCover (m + 2)).ι).app
      n ⟨q, hq⟩).property
  · intro hq
    let α := SimplexCategory.const ⦋0⦌ n.unop 0
    let q₀ := ((discreteSourceMapping W).obj (op (Δ[m + 2] : SSet.{u}))).map α.op q
    have hq₀ : ((discreteSourceMapping W).map (SSet.Rezk.initialIntervalCover (m + 2)).ι.op).app
        (op ⦋0⦌) q₀ ∈
        (EquivalenceMapping.subcomplex W hW
          (SSet.Rezk.initialIntervalCover (m + 2) : SSet.{u})).obj (op ⦋0⦌) := by
      have h := (EquivalenceMapping.mem_subcomplex_operator W hW _ α.op _).mp hq
      rw [← ((discreteSourceMapping W).map
        (SSet.Rezk.initialIntervalCover (m + 2)).ι.op).naturality_apply] at h
      exact h
    exact (EquivalenceMapping.mem_subcomplex_vertex W hW _ n q α).mpr
      (allDelta_zero W hW m q₀ hq₀)

/-- The chosen simplex/interval restriction retains both literal pullback inclusions. -/
theorem deltaRestriction_isPullback (W : SimplicialSpace.{u}) (hW : segalSpaces W) (m : ℕ) :
    IsPullback (EquivalenceMapping.subcomplex W hW (Δ[m + 2] : SSet.{u})).ι
      (EquivalenceMapping.restriction W hW (SSet.Rezk.initialIntervalCover (m + 2)).ι)
      ((discreteSourceMapping W).map (SSet.Rezk.initialIntervalCover (m + 2)).ι.op)
      (EquivalenceMapping.subcomplex W hW
        (SSet.Rezk.initialIntervalCover (m + 2) : SSet.{u})).ι :=
  restrictionPullback W hW _ (deltaDecoration_preimage W hW m)

/-- The full simplex-to-interval restriction is trivial on all original equivalence decorations. -/
theorem deltaRestriction_trivialFibration (W : SimplicialSpace.{u}) (hW : segalSpaces W) (m : ℕ) :
    trivialFibrations SSet.{u}
      (EquivalenceMapping.restriction W hW (SSet.Rezk.initialIntervalCover (m + 2)).ι) :=
  (trivialFibrations SSet.{u}).of_isPullback (deltaRestriction_isPullback W hW m)
    (initialIntervalCover_trivialFibration W (m + 2) hW)

private theorem rawMappingPullback {S A B D : SSet.{u}} (W : SimplicialSpace.{u})
    (i : S ⟶ A) (j : S ⟶ B) (a : A ⟶ D) (b : B ⟶ D)
    (h : IsPushout i j a b) :
    IsPullback ((discreteSourceMapping W).map a.op) ((discreteSourceMapping W).map b.op)
      ((discreteSourceMapping W).map i.op) ((discreteSourceMapping W).map j.op) := by
  let H := innerHomFunctor.flip.obj W
  let _ : PreservesColimitsOfShape WalkingSpan H.rightOp :=
    innerHom_rightOp_preservesColimitsOfShape WalkingSpan W
  have hd : IsPushout (SSet.simplicialSpaceDiscrete.map i) (SSet.simplicialSpaceDiscrete.map j)
      (SSet.simplicialSpaceDiscrete.map a) (SSet.simplicialSpaceDiscrete.map b) := by
    apply IsPushout.of_forall_isPushout_app
    intro d
    apply IsPushout.of_forall_isPushout_app
    intro e
    exact h.app d
  exact ((hd.map ofSimplicialObject).map H.rightOp).unop.flip

private theorem decoratedMappingPullback {S A B D : SSet.{u}} (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (i : S ⟶ A) (j : S ⟶ B) (a : A ⟶ D) (b : B ⟶ D)
    (h : IsPushout i j a b)
    (hc : ∀ γ : (Δ[1] : SSet.{u}) ⟶ D,
      (∃ δ : (Δ[1] : SSet.{u}) ⟶ A, δ ≫ a = γ) ∨
      (∃ δ : (Δ[1] : SSet.{u}) ⟶ B, δ ≫ b = γ)) :
    IsPullback (EquivalenceMapping.restriction W hW a) (EquivalenceMapping.restriction W hW b)
      (EquivalenceMapping.restriction W hW i) (EquivalenceMapping.restriction W hW j) := by
  let r : {X Y : SSet.{u}} → (X ⟶ Y) →
      ((EquivalenceMapping.subcomplex W hW Y : SSet.{u}) ⟶
        (EquivalenceMapping.subcomplex W hW X : SSet.{u})) :=
    fun {X Y} f => EquivalenceMapping.restriction W hW f
  let raw := rawMappingPullback W i j a b h
  have w : r a ≫ r i = r b ≫ r j := by
    rw [← EquivalenceMapping.restriction_comp, ← EquivalenceMapping.restriction_comp, h.w]
  refine IsPullback.of_isLimit (PullbackCone.isLimitAux' (PullbackCone.mk _ _ w) (fun s => ?_))
  have ws : (s.fst ≫ (EquivalenceMapping.subcomplex W hW A).ι) ≫
      (discreteSourceMapping W).map i.op =
        (s.snd ≫ (EquivalenceMapping.subcomplex W hW B).ι) ≫
          (discreteSourceMapping W).map j.op := by
    have hs := congrArg (fun f => f ≫ (EquivalenceMapping.subcomplex W hW S).ι) s.condition
    dsimp only [r] at hs
    simpa only [Category.assoc, EquivalenceMapping.restriction_ι] using hs
  let l := raw.lift (s.fst ≫ (EquivalenceMapping.subcomplex W hW A).ι)
    (s.snd ≫ (EquivalenceMapping.subcomplex W hW B).ι) ws
  have lf : l ≫ (discreteSourceMapping W).map a.op =
      s.fst ≫ (EquivalenceMapping.subcomplex W hW A).ι := raw.lift_fst _ _ _
  have lg : l ≫ (discreteSourceMapping W).map b.op =
      s.snd ≫ (EquivalenceMapping.subcomplex W hW B).ι := raw.lift_snd _ _ _
  have hl : SSet.Subcomplex.range l ≤ EquivalenceMapping.subcomplex W hW D := by
    intro n q hq
    rcases hq with ⟨t, rfl⟩
    apply (EquivalenceMapping.mem_subcomplex W hW D n _).mpr
    intro γ
    rcases hc γ with ⟨δ, hδ⟩ | ⟨δ, hδ⟩
    · rw [← hδ, ← EquivalenceMapping.edgeEvaluation_source]
      change (EquivalenceMapping.edgeEvaluation W δ).app n
        (((discreteSourceMapping W).map a.op).app n (l.app n t)) ∈ _
      have hv := congrArg (fun f => f.app n t) lf
      change ((discreteSourceMapping W).map a.op).app n (l.app n t) =
        (s.fst.app n t).val at hv
      rw [hv]
      exact (EquivalenceMapping.mem_subcomplex W hW A n _).mp (s.fst.app n t).property δ
    · rw [← hδ, ← EquivalenceMapping.edgeEvaluation_source]
      change (EquivalenceMapping.edgeEvaluation W δ).app n
        (((discreteSourceMapping W).map b.op).app n (l.app n t)) ∈ _
      have hv := congrArg (fun f => f.app n t) lg
      change ((discreteSourceMapping W).map b.op).app n (l.app n t) =
        (s.snd.app n t).val at hv
      rw [hv]
      exact (EquivalenceMapping.mem_subcomplex W hW B n _).mp (s.snd.app n t).property δ
  let L := SSet.Subcomplex.lift l hl
  have Lf : L ≫ r a = s.fst := by
    apply (cancel_mono (EquivalenceMapping.subcomplex W hW A).ι).mp
    rw [Category.assoc, EquivalenceMapping.restriction_ι, ← Category.assoc,
      SSet.Subcomplex.lift_ι]
    exact lf
  have Lg : L ≫ r b = s.snd := by
    apply (cancel_mono (EquivalenceMapping.subcomplex W hW B).ι).mp
    rw [Category.assoc, EquivalenceMapping.restriction_ι, ← Category.assoc,
      SSet.Subcomplex.lift_ι]
    exact lg
  refine ⟨L, Lf, Lg, ?_⟩
  intro t hf hg
  change t ≫ EquivalenceMapping.restriction W hW a = s.fst at hf
  change t ≫ EquivalenceMapping.restriction W hW b = s.snd at hg
  apply (cancel_mono (EquivalenceMapping.subcomplex W hW D).ι).mp
  apply raw.hom_ext
  · rw [Category.assoc, ← EquivalenceMapping.restriction_ι, ← Category.assoc, hf,
      SSet.Subcomplex.lift_ι, lf]
  · rw [Category.assoc, ← EquivalenceMapping.restriction_ι, ← Category.assoc, hg,
      SSet.Subcomplex.lift_ι, lg]

private theorem edgeCoverRange {X A B D : SSet.{u}}
    (a : A ⟶ D) (b : B ⟶ D) (d : D ⟶ X) [Mono d]
    (h : SSet.Subcomplex.range (a ≫ d) ⊔ SSet.Subcomplex.range (b ≫ d) =
      SSet.Subcomplex.range d) :
    ∀ γ : (Δ[1] : SSet.{u}) ⟶ D,
      (∃ δ : (Δ[1] : SSet.{u}) ⟶ A, δ ≫ a = γ) ∨
      (∃ δ : (Δ[1] : SSet.{u}) ⟶ B, δ ≫ b = γ) := by
  intro γ
  have hv : d.app (op ⦋1⦌) (SSet.yonedaEquiv γ) ∈
      (SSet.Subcomplex.range d).obj (op ⦋1⦌) := ⟨SSet.yonedaEquiv γ, rfl⟩
  rw [← h] at hv
  rcases hv with ⟨x, hx⟩ | ⟨x, hx⟩
  · refine Or.inl ⟨SSet.yonedaEquiv.symm x, ?_⟩
    apply (cancel_mono d).mp
    apply SSet.yonedaEquiv.injective
    simpa only [Category.assoc, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using hx
  · refine Or.inr ⟨SSet.yonedaEquiv.symm x, ?_⟩
    apply (cancel_mono d).mp
    apply SSet.yonedaEquiv.injective
    simpa only [Category.assoc, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using hx

private theorem rangeInclusion {X : SSet.{u}} (A : X.Subcomplex) :
    SSet.Subcomplex.range A.ι = A := by
  ext n x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- The original first-coface overlap gives the full decorated H/C pullback. -/
theorem hcRestriction_isPullback (W : SimplicialSpace.{u}) (hW : segalSpaces W) (n : ℕ) :
    IsPullback (EquivalenceMapping.restriction W hW (SSet.Rezk.outerHornCInclusion n))
      (EquivalenceMapping.restriction W hW
        (SSet.horn.ι 0 (1 : Fin (n + 2)) (by
          intro h; have hv := congrArg Fin.val h; change 1 = 0 at hv; omega)))
      (EquivalenceMapping.restriction W hW (SSet.Rezk.outerHornCoface n))
      (EquivalenceMapping.restriction W hW (SSet.horn n 0).ι) := by
  apply IsPullback.flip
  apply decoratedMappingPullback W hW _ _ _ _ (SSet.Rezk.outerHornC_isPushout n)
  apply edgeCoverRange _ _ (SSet.horn (n + 1) 0).ι
  rw [SSet.horn.ι_ι, SSet.Rezk.outerHornCInclusion_ι, SSet.stdSimplex.range_δ,
    rangeInclusion, rangeInclusion, sup_comm, ← SSet.Rezk.outerHorn_eq_sup_C_face]

private theorem u_le_T (m : ℕ) :
    SSet.Rezk.outerHornCU.{u} m ≤ SSet.Rezk.initialIntervalCover (m + 2) := by
  change (SSet.horn (m + 1) 0).image (SSet.stdSimplex.δ (0 : Fin (m + 3))) ⊔
      SSet.stdSimplex.face {0, 1} ≤
    SSet.stdSimplex.face {(0 : Fin (m + 3))}ᶜ ⊔ SSet.stdSimplex.face {0, 1}
  apply sup_le
  · have h : (SSet.horn (m + 1) 0).image (SSet.stdSimplex.δ (0 : Fin (m + 3))) ≤
        SSet.stdSimplex.face {(0 : Fin (m + 3))}ᶜ := by
      simpa only [SSet.stdSimplex.range_δ] using
        (SSet.horn.{u} (m + 1) 0).image_le_range (SSet.stdSimplex.δ (0 : Fin (m + 3)))
    exact h.trans le_sup_left
  · exact le_sup_right

/-- The original zero-coface horn union includes in the full tail-edge cover. -/
def uToT (m : ℕ) : (SSet.Rezk.outerHornCU m : SSet.{u}) ⟶
    (SSet.Rezk.initialIntervalCover (m + 2) : SSet.{u}) :=
  SSet.Subcomplex.homOfLE (u_le_T m)

/-- The inclusion retains the original ambient simplex. -/
@[reassoc (attr := simp)]
theorem uToT_ι (m : ℕ) : uToT.{u} m ≫ (SSet.Rezk.initialIntervalCover (m + 2)).ι =
    (SSet.Rezk.outerHornCU m).ι := rfl

/-- The original initial edge enters the full interval cover through its ordered-pair face. -/
def edgeToT (m : ℕ) : (Δ[1] : SSet.{u}) ⟶
    (SSet.Rezk.initialIntervalCover (m + 2) : SSet.{u}) :=
  (SSet.stdSimplex.facePairIso (0 : Fin (m + 3)) 1 (by change (0 : ℕ) < 1; omega)).hom ≫
    SSet.Subcomplex.homOfLE (show SSet.stdSimplex.face {0, 1} ≤
      SSet.Rezk.initialIntervalCover (m + 2) from le_sup_right)

/-- The same initial edge is unchanged by the original U-to-T inclusion. -/
@[reassoc (attr := simp)]
theorem uToT_edge (m : ℕ) :
    SSet.Rezk.OuterHornCPresentation.edgeToU.{u} m ≫ uToT m = edgeToT m := by
  dsimp only [SSet.Rezk.OuterHornCPresentation.edgeToU, uToT, edgeToT]
  rw [Category.assoc, SSet.Subcomplex.homOfLE_comp]

/-- The tail square retains the actual zero coface and the original smaller horn inclusion. -/
@[reassoc (attr := simp)]
theorem uToT_tail (m : ℕ) :
    SSet.Rezk.OuterHornCPresentation.tailToU.{u} m ≫ uToT m =
      (SSet.horn (m + 1) 0).ι ≫ SSet.Rezk.initialCoverTail m := by
  apply (cancel_mono (SSet.Rezk.initialIntervalCover (m + 2)).ι).mp
  rw [Category.assoc, uToT_ι, SSet.Rezk.OuterHornCPresentation.tailToU_ι,
    Category.assoc, SSet.Rezk.initialCoverTail_ι]

private theorem tailEdgeT_isPushout (m : ℕ) :
    IsPushout (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋m + 1⦌ 0))
      (SSet.stdSimplex.δ (0 : Fin 2)) (SSet.Rezk.initialCoverTail.{u} m) (edgeToT m) := by
  let F := SSet.stdSimplex.face.{u} {(0 : Fin (m + 3))}ᶜ
  let E := SSet.stdSimplex.face.{u} {(0 : Fin (m + 3)), 1}
  let I := SSet.stdSimplex.face.{u} {(1 : Fin (m + 3))}
  have sq : SSet.Subcomplex.BicartSq I F E (SSet.Rezk.initialIntervalCover (m + 2)) :=
    { sup_eq := rfl
      inf_eq := by
        change SSet.stdSimplex.face.{u} {(0 : Fin (m + 3))}ᶜ ⊓ SSet.stdSimplex.face {0, 1} =
          SSet.stdSimplex.face {(1 : Fin (m + 3))}
        rw [SSet.stdSimplex.face_inter_face]
        apply congrArg (fun S : Finset (Fin (m + 3)) => SSet.stdSimplex.face.{u} S)
        ext j
        simp only [Finset.inf_eq_inter, Finset.mem_inter, Finset.mem_compl,
          Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hn, h0 | h1⟩
          · exact False.elim (hn h0)
          · exact h1
        · intro hj
          exact ⟨by intro h; rw [hj] at h; have hv := congrArg Fin.val h; change 1 = 0 at hv; omega,
            Or.inr hj⟩ }
  apply sq.isPushout.of_iso' (SSet.stdSimplex.faceSingletonIso (1 : Fin (m + 3)))
    (SSet.stdSimplex.faceSingletonComplIso (0 : Fin (m + 3)))
    (SSet.stdSimplex.facePairIso (0 : Fin (m + 3)) 1 (by change (0 : ℕ) < 1; omega)) (Iso.refl _)
  · apply (cancel_mono F.ι).mp
    simp only [Category.assoc, SSet.Subcomplex.homOfLE_ι]
    change SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋m + 2⦌ 1) =
      SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋m + 1⦌ 0) ≫
        SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin (m + 3)))
    rw [← SSet.stdSimplex.map_comp]
    congr 1
  · apply (cancel_mono E.ι).mp
    simp only [Category.assoc, SSet.Subcomplex.homOfLE_ι]
    apply SSet.yonedaEquiv.injective
    apply SSet.stdSimplex.ext
    intro j
    fin_cases j
    rfl
  · rfl
  · rfl

private theorem rangeEpi {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [Epi f] :
    SSet.Subcomplex.range (f ≫ g) = SSet.Subcomplex.range g := by
  rw [SSet.Subcomplex.range_comp, SSet.Subcomplex.range_eq_top, SSet.Subcomplex.image_top]

/-- The original horn-tail and initial edge give the decorated U pullback over original vertex
one. -/
theorem uTailEdge_isPullback (W : SimplicialSpace.{u}) (hW : segalSpaces W) (m : ℕ) :
    IsPullback
      (EquivalenceMapping.restriction W hW (SSet.Rezk.OuterHornCPresentation.tailToU m))
      (EquivalenceMapping.restriction W hW (SSet.Rezk.OuterHornCPresentation.edgeToU m))
      (EquivalenceMapping.restriction W hW (SSet.Rezk.OuterHornCPresentation.tailVertex m))
      (EquivalenceMapping.restriction W hW (SSet.stdSimplex.δ (0 : Fin 2))) := by
  apply decoratedMappingPullback W hW _ _ _ _
      (SSet.Rezk.OuterHornCPresentation.tailEdge_isPushout m)
  apply edgeCoverRange _ _ (SSet.Rezk.outerHornCU m).ι
  have he : SSet.Subcomplex.range
      (SSet.Rezk.OuterHornCPresentation.edgeToU.{u} m ≫ (SSet.Rezk.outerHornCU m).ι) =
        SSet.stdSimplex.face {0, 1} := by
    rw [SSet.Rezk.OuterHornCPresentation.edgeToU, Category.assoc,
      SSet.Subcomplex.homOfLE_ι, rangeEpi, rangeInclusion]
  rw [SSet.Rezk.OuterHornCPresentation.tailToU_ι, he,
    ← SSet.Subcomplex.image_eq_range, rangeInclusion]
  rfl

/-- The original full tail and initial edge give the decorated T pullback over original vertex
one. -/
theorem tTailEdge_isPullback (W : SimplicialSpace.{u}) (hW : segalSpaces W) (m : ℕ) :
    IsPullback (EquivalenceMapping.restriction W hW (SSet.Rezk.initialCoverTail m))
      (EquivalenceMapping.restriction W hW (edgeToT m))
      (EquivalenceMapping.restriction W hW
        (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋m + 1⦌ 0)))
      (EquivalenceMapping.restriction W hW (SSet.stdSimplex.δ (0 : Fin 2))) := by
  apply decoratedMappingPullback W hW _ _ _ _ (tailEdgeT_isPushout m)
  apply edgeCoverRange _ _ (SSet.Rezk.initialIntervalCover (m + 2)).ι
  have he : SSet.Subcomplex.range (edgeToT.{u} m ≫
      (SSet.Rezk.initialIntervalCover (m + 2)).ι) = SSet.stdSimplex.face {0, 1} := by
    rw [edgeToT, Category.assoc, SSet.Subcomplex.homOfLE_ι, rangeEpi, rangeInclusion]
  rw [SSet.Rezk.initialCoverTail_ι, he, SSet.stdSimplex.range_δ, rangeInclusion]
  rfl

/-- The original smaller horn restriction is the right side of the decorated T/U pullback. -/
theorem tuRestriction_isPullback (W : SimplicialSpace.{u}) (hW : segalSpaces W) (m : ℕ) :
    IsPullback (EquivalenceMapping.restriction W hW (SSet.Rezk.initialCoverTail m))
      (EquivalenceMapping.restriction W hW (uToT m))
      (EquivalenceMapping.restriction W hW (SSet.horn (m + 1) 0).ι)
      (EquivalenceMapping.restriction W hW (SSet.Rezk.OuterHornCPresentation.tailToU m)) := by
  have h := tTailEdge_isPullback W hW m
  rw [← uToT_edge, EquivalenceMapping.restriction_comp,
    ← SSet.Rezk.OuterHornCPresentation.tailVertex_ι,
    EquivalenceMapping.restriction_comp] at h
  apply h.of_bot _ (uTailEdge_isPullback W hW m)
  rw [← EquivalenceMapping.restriction_comp, ← EquivalenceMapping.restriction_comp, uToT_tail]

private theorem initialStep (W : SimplicialSpace.{u}) (hW : segalSpaces W) (m : ℕ)
    (hm : 1 ≤ m)
    (hp : trivialFibrations SSet.{u}
      (EquivalenceMapping.restriction W hW (SSet.horn (m + 1) 0).ι)) :
    trivialFibrations SSet.{u}
      (EquivalenceMapping.restriction W hW (SSet.horn (m + 2) 0).ι) := by
  have hc : trivialFibrations SSet.{u}
      (EquivalenceMapping.restriction W hW (SSet.Rezk.outerHornCInclusion (m + 1))) :=
    (trivialFibrations SSet.{u}).of_isPullback (hcRestriction_isPullback W hW (m + 1)).flip hp
  have htu : trivialFibrations SSet.{u} (EquivalenceMapping.restriction W hW (uToT m)) :=
    (trivialFibrations SSet.{u}).of_isPullback (tuRestriction_isPullback W hW m) hp
  have hdu : trivialFibrations SSet.{u}
      (EquivalenceMapping.restriction W hW (SSet.Rezk.outerHornCU m).ι) := by
    rw [← uToT_ι, EquivalenceMapping.restriction_comp]
    exact (trivialFibrations SSet.{u}).comp_mem _ _
      (deltaRestriction_trivialFibration W hW m) htu
  have hcu : SSet.realizationWeakEquivalences
      (EquivalenceMapping.restriction W hW (OuterHornCMapping.inclusion m)) :=
    (cRestriction_trivialFibration W hW m hm).2
  have hcw : SSet.realizationWeakEquivalences
      (EquivalenceMapping.restriction W hW (SSet.Rezk.outerHornCInclusion (m + 1))) := hc.2
  have hdc : SSet.realizationWeakEquivalences
      (EquivalenceMapping.restriction W hW (SSet.Rezk.outerHornC (m + 2)).ι) := by
    apply SSet.realizationWeakEquivalences.of_postcomp
      (EquivalenceMapping.restriction W hW (SSet.Rezk.outerHornC (m + 2)).ι)
      (EquivalenceMapping.restriction W hW (OuterHornCMapping.inclusion m))
      hcu
    rw [← EquivalenceMapping.restriction_comp, OuterHornCMapping.inclusion_ambient]
    exact hdu.2
  refine ⟨(HomotopicalAlgebra.fibration_iff _).mp
    (EquivalenceMapping.restriction_fibration W hW (SSet.horn (m + 2) 0).ι), ?_⟩
  change SSet.realizationWeakEquivalences
    (EquivalenceMapping.restriction W hW (SSet.horn (m + 2) 0).ι)
  apply SSet.realizationWeakEquivalences.of_postcomp
    (EquivalenceMapping.restriction W hW (SSet.horn (m + 2) 0).ι)
    (EquivalenceMapping.restriction W hW (SSet.Rezk.outerHornCInclusion (m + 1))) hcw
  rw [← EquivalenceMapping.restriction_comp, SSet.Rezk.outerHornCInclusion_ι]
  exact hdc

private theorem allInitial (W : SimplicialSpace.{u}) (hW : segalSpaces W) (m : ℕ) :
    trivialFibrations SSet.{u}
      (EquivalenceMapping.restriction W hW (SSet.horn (m + 2) 0).ι) := by
  induction m with
  | zero => exact DecoratedOuterTwoHorn.firstAllRestriction_trivialFibration W hW
  | succ m ih => exact initialStep W hW (m + 1) (by omega) ih

/-- Every original higher initial horn restricts to a genuine all-edge decorated trivial
fibration. -/
theorem initialRestriction_trivialFibration (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (k : ℕ) (hk : 3 ≤ k) :
    trivialFibrations SSet.{u} (EquivalenceMapping.restriction W hW (SSet.horn k 0).ι) := by
  have e : k = (k - 2) + 2 := (Nat.sub_add_cancel (by omega : 2 ≤ k)).symm
  rw [e]
  exact allInitial W hW (k - 2)

/-- The same original higher-horn map satisfies the complete native boundary-family lifting
property. -/
theorem initialRestriction_boundaryRLP (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (k : ℕ) (hk : 3 ≤ k) :
    SSet.modelCategoryQuillen.I.rlp
      (EquivalenceMapping.restriction W hW (SSet.horn k 0).ι) := by
  have h := initialRestriction_trivialFibration W hW k hk
  rw [← cofibrations_rlp] at h
  change (CategoryTheory.MorphismProperty.monomorphisms SSet.{u}).rlp
    (EquivalenceMapping.restriction W hW (SSet.horn k 0).ι) at h
  rw [SSet.rlp_monomorphisms] at h
  exact h

/-- The original higher decorated restriction induces all realization homotopy-group
equivalences. -/
theorem initialRestriction_realizationWeak (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (k : ℕ) (hk : 3 ≤ k) :
    SSet.realizationWeakEquivalences
      (EquivalenceMapping.restriction W hW (SSet.horn k 0).ι) :=
  (initialRestriction_trivialFibration W hW k hk).2

end SimplicialSpace.DecoratedOuterHorn
