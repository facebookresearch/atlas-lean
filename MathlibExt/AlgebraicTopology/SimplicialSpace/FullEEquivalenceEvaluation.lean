/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.EquivalenceMappingComponents
import MathlibExt.AlgebraicTopology.SimplicialSpace.WalkingIsomorphismStages
import MathlibExt.AlgebraicTopology.SimplicialSpace.FiniteCompletenessComparison

/-!
# Original full-E evaluation into equivalence edges

Every original edge of the full walking-isomorphism nerve has both inverse
triangles. Their images under the actual inner mapping end are inverse homs
in the existing intrinsic category. The canonical factor retains the same
original evaluation, all operators and both endpoints.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SimplicialSpace.Inner SSet.modelCategoryQuillen

namespace SimplicialSpace.FullEEquivalence

private def simplexEvaluation (W : SimplicialSpace.{u}) {n : ℕ}
    (α : (Δ[n] : SSet.{u}) ⟶ SSet.coherentIso) :
    (discreteSourceMapping W).obj (op SSet.coherentIso) ⟶ W.diagram _⦋n⦌ :=
  (discreteSourceMapping W).map α.op ≫ (discreteYonedaIso W n).hom

private theorem simplexEvaluation_map (W : SimplicialSpace.{u}) {m n : ℕ}
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (α : (Δ[n] : SSet.{u}) ⟶ SSet.coherentIso) :
    simplexEvaluation W (SSet.stdSimplex.map θ ≫ α) =
      simplexEvaluation W α ≫ W.diagram.map θ.op := by
  dsimp only [simplexEvaluation]
  rw [op_comp, Functor.map_comp, Category.assoc,
    discreteYonedaIso_naturality_index]
  exact (Category.assoc _ _ _).symm

private theorem simplexEvaluation_yoneda_map (W : SimplicialSpace.{u}) {m n : ℕ}
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (s : SSet.coherentIso.{u} _⦋n⦌) :
    simplexEvaluation W (SSet.yonedaEquiv.symm (SSet.coherentIso.map θ.op s)) =
      simplexEvaluation W (SSet.yonedaEquiv.symm s) ≫ W.diagram.map θ.op := by
  rw [← SSet.yonedaEquiv_symm_naturality_left]
  exact simplexEvaluation_map W θ (SSet.yonedaEquiv.symm s)

/-- The actual full-E end evaluated at an original vertex of the same nerve. -/
def pointEvaluation (W : SimplicialSpace.{u}) (x : SSet.coherentIso.{u} _⦋0⦌) :
    (discreteSourceMapping W).obj (op SSet.coherentIso) ⟶ W.diagram _⦋0⦌ :=
  (discreteSourceMapping W).map (SSet.yonedaEquiv.symm x).op ≫
    (discreteYonedaIso W 0).hom

private def localPointArrow (W : SimplicialSpace.{u})
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

private theorem localPointArrow_fst (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (g : (W.diagram _⦋1⦌) _⦋0⦌)
    (hs : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g = x)
    (ht : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g = y) :
    localPointArrow W x y g hs ht ≫ mappingFibre.fst W x y = SSet.yonedaEquiv.symm g :=
  pullback.lift_fst _ _ _

private theorem localPointArrow_snd (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (g : (W.diagram _⦋1⦌) _⦋0⦌)
    (hs : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g = x)
    (ht : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g = y) :
    localPointArrow W x y g hs ht ≫ mappingFibre.snd W x y = 𝟙 _ :=
  pullback.lift_snd _ _ _

private theorem localPointArrow_source (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (g : (W.diagram _⦋1⦌) _⦋0⦌)
    (hs : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g = x)
    (ht : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g = y) :
    localPointArrow W x y g hs ht ≫ mappingFibre.fst W x y ≫
        W.diagram.δ (1 : Fin 2) = SSet.yonedaEquiv.symm x := by
  rw [mappingFibre.source_eq, ← Category.assoc, localPointArrow_snd, Category.id_comp]

private theorem localPointArrow_target (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (g : (W.diagram _⦋1⦌) _⦋0⦌)
    (hs : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g = x)
    (ht : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g = y) :
    localPointArrow W x y g hs ht ≫ mappingFibre.fst W x y ≫
        W.diagram.δ (0 : Fin 2) = SSet.yonedaEquiv.symm y := by
  rw [mappingFibre.target_eq, ← Category.assoc, localPointArrow_snd, Category.id_comp]

private def localPoint (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (g : (W.diagram _⦋1⦌) _⦋0⦌)
    (hs : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g = x)
    (ht : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g = y) :
    (mappingFibre W x y) _⦋0⦌ :=
  SSet.yonedaEquiv (localPointArrow W x y g hs ht)

private theorem localPoint_fst (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (g : (W.diagram _⦋1⦌) _⦋0⦌)
    (hs : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g = x)
    (ht : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g = y) :
    (mappingFibre.fst W x y).app (op ⦋0⦌) (localPoint W x y g hs ht) = g := by
  change SSet.yonedaEquiv (localPointArrow W x y g hs ht ≫ mappingFibre.fst W x y) = g
  rw [localPointArrow_fst, Equiv.apply_symm_apply]

private theorem eval_source (W : SimplicialSpace.{u}) {a b : WalkingIso.{u}} (f : a ⟶ b) :
    EquivalenceMapping.edgeEvaluation W (SSet.yonedaEquiv.symm (ComposableArrows.mk₁ f)) ≫
      W.diagram.δ (1 : Fin 2) = pointEvaluation W (ComposableArrows.mk₀ a) := by
  have h := simplexEvaluation_yoneda_map W (SimplexCategory.δ (1 : Fin 2))
    (ComposableArrows.mk₁ f)
  have hs : SSet.coherentIso.map (SimplexCategory.δ (1 : Fin 2)).op
      (ComposableArrows.mk₁ f) = ComposableArrows.mk₀ a := ComposableArrows.ext₀ rfl
  rw [hs] at h
  exact h.symm

private theorem eval_target (W : SimplicialSpace.{u}) {a b : WalkingIso.{u}} (f : a ⟶ b) :
    EquivalenceMapping.edgeEvaluation W (SSet.yonedaEquiv.symm (ComposableArrows.mk₁ f)) ≫
      W.diagram.δ (0 : Fin 2) = pointEvaluation W (ComposableArrows.mk₀ b) := by
  have h := simplexEvaluation_yoneda_map W (SimplexCategory.δ (0 : Fin 2))
    (ComposableArrows.mk₁ f)
  have ht : SSet.coherentIso.map (SimplexCategory.δ (0 : Fin 2)).op
      (ComposableArrows.mk₁ f) = ComposableArrows.mk₀ b := ComposableArrows.ext₀ rfl
  rw [ht] at h
  exact h.symm

private theorem eval_first (W : SimplicialSpace.{u}) {a b c : WalkingIso.{u}}
    (f : a ⟶ b) (g : b ⟶ c) :
    simplexEvaluation W (SSet.yonedaEquiv.symm (ComposableArrows.mk₂ f g)) ≫
      W.diagram.δ (2 : Fin 3) =
      EquivalenceMapping.edgeEvaluation W (SSet.yonedaEquiv.symm (ComposableArrows.mk₁ f)) := by
  have h := simplexEvaluation_yoneda_map W (SimplexCategory.δ (2 : Fin 3))
    (ComposableArrows.mk₂ f g)
  have hd : SSet.coherentIso.map (SimplexCategory.δ (2 : Fin 3)).op
      (ComposableArrows.mk₂ f g) = ComposableArrows.mk₁ f :=
    ComposableArrows.ext₁ rfl rfl rfl
  rw [hd] at h
  exact h.symm

private theorem eval_last (W : SimplicialSpace.{u}) {a b c : WalkingIso.{u}}
    (f : a ⟶ b) (g : b ⟶ c) :
    simplexEvaluation W (SSet.yonedaEquiv.symm (ComposableArrows.mk₂ f g)) ≫
      W.diagram.δ (0 : Fin 3) =
      EquivalenceMapping.edgeEvaluation W (SSet.yonedaEquiv.symm (ComposableArrows.mk₁ g)) := by
  have h := simplexEvaluation_yoneda_map W (SimplexCategory.δ (0 : Fin 3))
    (ComposableArrows.mk₂ f g)
  have hd : SSet.coherentIso.map (SimplexCategory.δ (0 : Fin 3)).op
      (ComposableArrows.mk₂ f g) = ComposableArrows.mk₁ g :=
    ComposableArrows.ext₁ rfl rfl rfl
  rw [hd] at h
  exact h.symm

private theorem eval_middle (W : SimplicialSpace.{u}) {a b c : WalkingIso.{u}}
    (f : a ⟶ b) (g : b ⟶ c) :
    simplexEvaluation W (SSet.yonedaEquiv.symm (ComposableArrows.mk₂ f g)) ≫
      W.diagram.δ (1 : Fin 3) =
      EquivalenceMapping.edgeEvaluation W
          (SSet.yonedaEquiv.symm (ComposableArrows.mk₁ (f ≫ g))) := by
  have h := simplexEvaluation_yoneda_map W (SimplexCategory.δ (1 : Fin 3))
    (ComposableArrows.mk₂ f g)
  have hd : SSet.coherentIso.map (SimplexCategory.δ (1 : Fin 3)).op
      (ComposableArrows.mk₂ f g) = ComposableArrows.mk₁ (f ≫ g) :=
    ComposableArrows.ext₁ rfl rfl rfl
  rw [hd] at h
  exact h.symm

private theorem eval_identity (W : SimplicialSpace.{u}) (a : WalkingIso.{u}) :
    EquivalenceMapping.edgeEvaluation W (SSet.yonedaEquiv.symm (ComposableArrows.mk₁ (𝟙 a))) =
      pointEvaluation W (ComposableArrows.mk₀ a) ≫ W.diagram.σ (0 : Fin 1) := by
  have h := simplexEvaluation_yoneda_map W (SimplexCategory.σ (0 : Fin 1))
    (ComposableArrows.mk₀ a)
  have hd : SSet.coherentIso.map (SimplexCategory.σ (0 : Fin 1)).op
      (ComposableArrows.mk₀ a) = ComposableArrows.mk₁ (𝟙 a) :=
    ComposableArrows.ext₁ rfl rfl rfl
  rw [hd] at h
  exact h

private theorem eval_iso_isEquivalence (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    {a b : WalkingIso.{u}} (e : a ≅ b)
    (q : ((discreteSourceMapping W).obj (op SSet.coherentIso)) _⦋0⦌) :
    SegalHomotopy.IsEquivalenceEdge W hW
      ((EquivalenceMapping.edgeEvaluation W
        (SSet.yonedaEquiv.symm (ComposableArrows.mk₁ e.hom))).app (op ⦋0⦌) q) := by
  let x := (pointEvaluation W (ComposableArrows.mk₀ a)).app (op ⦋0⦌) q
  let y := (pointEvaluation W (ComposableArrows.mk₀ b)).app (op ⦋0⦌) q
  let g := (EquivalenceMapping.edgeEvaluation W
    (SSet.yonedaEquiv.symm (ComposableArrows.mk₁ e.hom))).app (op ⦋0⦌) q
  let h := (EquivalenceMapping.edgeEvaluation W
    (SSet.yonedaEquiv.symm (ComposableArrows.mk₁ e.inv))).app (op ⦋0⦌) q
  have gs : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g = x :=
    congrArg (fun k => k.app (op ⦋0⦌) q) (eval_source W e.hom)
  have gt : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g = y :=
    congrArg (fun k => k.app (op ⦋0⦌) q) (eval_target W e.hom)
  have hs : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) h = y :=
    congrArg (fun k => k.app (op ⦋0⦌) q) (eval_source W e.inv)
  have ht : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) h = x :=
    congrArg (fun k => k.app (op ⦋0⦌) q) (eval_target W e.inv)
  let g₀ := localPoint W x y g gs gt
  let h₀ := localPoint W y x h hs ht
  let t := (simplexEvaluation W
    (SSet.yonedaEquiv.symm (ComposableArrows.mk₂ e.hom e.inv))).app (op ⦋0⦌) q
  let s := (simplexEvaluation W
    (SSet.yonedaEquiv.symm (ComposableArrows.mk₂ e.inv e.hom))).app (op ⦋0⦌) q
  have hab := SegalHomotopy.compose_of_original_triangle W hW t g₀ h₀
    (SegalHomotopy.identityVertex W x)
    ((localPoint_fst W x y g gs gt).trans
      (congrArg (fun k => k.app (op ⦋0⦌) q) (eval_first W e.hom e.inv)).symm)
    ((localPoint_fst W y x h hs ht).trans
      (congrArg (fun k => k.app (op ⦋0⦌) q) (eval_last W e.hom e.inv)).symm)
    (by
      rw [SegalHomotopy.identityVertex_fst]
      have hm := eval_middle W e.hom e.inv
      rw [e.hom_inv_id, eval_identity] at hm
      exact (congrArg (fun k => k.app (op ⦋0⦌) q) hm).symm)
  have hba := SegalHomotopy.compose_of_original_triangle W hW s h₀ g₀
    (SegalHomotopy.identityVertex W y)
    ((localPoint_fst W y x h hs ht).trans
      (congrArg (fun k => k.app (op ⦋0⦌) q) (eval_first W e.inv e.hom)).symm)
    ((localPoint_fst W x y g gs gt).trans
      (congrArg (fun k => k.app (op ⦋0⦌) q) (eval_last W e.inv e.hom)).symm)
    (by
      rw [SegalHomotopy.identityVertex_fst]
      have hm := eval_middle W e.inv e.hom
      rw [e.inv_hom_id, eval_identity] at hm
      exact (congrArg (fun k => k.app (op ⦋0⦌) q) hm).symm)
  let _ : IsIso (C := SegalHomotopy.Object W hW) (X := ⟨x⟩) (Y := ⟨y⟩)
      (SSet.π₀.mk g₀) := ⟨⟨SSet.π₀.mk h₀, hab, hba⟩⟩
  exact (SegalHomotopy.isEquivalenceEdge_iff_of_fibre W hW g g₀
    (localPoint_fst W x y g gs gt)).mpr inferInstance

private theorem eval_edge_isEquivalence (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (γ : (Δ[1] : SSet.{u}) ⟶ SSet.coherentIso)
    (q : ((discreteSourceMapping W).obj (op SSet.coherentIso)) _⦋0⦌) :
    SegalHomotopy.IsEquivalenceEdge W hW
        ((EquivalenceMapping.edgeEvaluation W γ).app (op ⦋0⦌) q) := by
  let s : ComposableArrows WalkingIso.{u} 1 := SSet.yonedaEquiv γ
  let e := Codiscrete.iso (s.obj 0) (s.obj 1)
  have hg : γ = SSet.yonedaEquiv.symm (ComposableArrows.mk₁ e.hom) := by
    apply SSet.yonedaEquiv.injective
    change s = ComposableArrows.mk₁ e.hom
    apply SSet.coherentIso.eq_of_forall_vertexBool_eq
    intro i
    fin_cases i <;> rfl
  rw [hg]
  exact eval_iso_isEquivalence W hW e q

/-- Every original edge evaluation on the full E lands in the original equivalence-arrow
subcomplex. -/
theorem edgeEvaluation_range (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (γ : (Δ[1] : SSet.{u}) ⟶ SSet.coherentIso) :
    SSet.Subcomplex.range (EquivalenceMapping.edgeEvaluation W γ) ≤
      SegalHomotopy.equivalenceSubcomplex W hW := by
  intro n r hr
  rcases hr with ⟨q, rfl⟩
  rw [SegalHomotopy.mem_equivalenceSubcomplex]
  rw [← (EquivalenceMapping.edgeEvaluation W γ).naturality_apply]
  exact eval_edge_isEquivalence W hW γ _

/-- For the full walking-isomorphism nerve, every original mapping simplex passes every edge
test. -/
theorem selection_eq_top (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    EquivalenceMapping.subcomplex W hW SSet.coherentIso = ⊤ := by
  apply top_unique
  intro n q _
  apply (EquivalenceMapping.mem_subcomplex W hW SSet.coherentIso n q).mpr
  intro γ
  exact edgeEvaluation_range W hW γ n ⟨q, rfl⟩

/-- The canonical factor retains the actual evaluation on every original edge of full E. -/
def evaluation (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (γ : (Δ[1] : SSet.{u}) ⟶ SSet.coherentIso) :
    (discreteSourceMapping W).obj (op SSet.coherentIso) ⟶
      (SegalHomotopy.equivalenceSubcomplex W hW : SSet.{u}) :=
  SSet.Subcomplex.lift (EquivalenceMapping.edgeEvaluation W γ) (edgeEvaluation_range W hW γ)

/-- The canonical factor followed by the original inclusion is exactly the original evaluation. -/
@[reassoc (attr := simp)]
theorem evaluation_ι (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (γ : (Δ[1] : SSet.{u}) ⟶ SSet.coherentIso) :
    evaluation W hW γ ≫ (SegalHomotopy.equivalenceSubcomplex W hW).ι =
      EquivalenceMapping.edgeEvaluation W γ :=
  SSet.Subcomplex.lift_ι _ _

/-- Every original inner-degree value is the same evaluated edge under the inclusion. -/
@[simp]
theorem evaluation_app_val (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (γ : (Δ[1] : SSet.{u}) ⟶ SSet.coherentIso) (n : SimplexCategoryᵒᵖ)
    (q : ((discreteSourceMapping W).obj (op SSet.coherentIso)).obj n) :
    dsimp% ((evaluation W hW γ).app n q).val =
        (EquivalenceMapping.edgeEvaluation W γ).app n q := rfl

/-- Every original inner simplex operator commutes with the same canonical factor. -/
theorem evaluation_operator (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (γ : (Δ[1] : SSet.{u}) ⟶ SSet.coherentIso) {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    ((discreteSourceMapping W).obj (op SSet.coherentIso)).map θ ≫ (evaluation W hW γ).app m =
      (evaluation W hW γ).app n ≫
        (SegalHomotopy.equivalenceSubcomplex W hW : SSet.{u}).map θ :=
  (evaluation W hW γ).naturality θ

/-- Every original target map preserves the full-E factor and the actual equivalence-subcomplex
map. -/
@[reassoc]
theorem evaluation_naturality_target {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V)
    (γ : (Δ[1] : SSet.{u}) ⟶ SSet.coherentIso) :
    (discreteSourceMappingMap f).app (op SSet.coherentIso) ≫ evaluation V hV γ =
      evaluation W hW γ ≫ SegalHomotopy.equivalenceMap f hW hV := by
  apply (cancel_mono (SegalHomotopy.equivalenceSubcomplex V hV).ι).mp
  simp only [Category.assoc, evaluation_ι, SegalHomotopy.equivalenceMap_ι,
    evaluation_ι_assoc]
  exact EquivalenceMapping.edgeEvaluation_target f γ

/-- Original full-E precomposition keeps the same original edge under the canonical factor. -/
@[reassoc]
theorem evaluation_precompose (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (f : SSet.coherentIso.{u} ⟶ SSet.coherentIso)
    (γ : (Δ[1] : SSet.{u}) ⟶ SSet.coherentIso) :
    (discreteSourceMapping W).map f.op ≫ evaluation W hW γ =
      evaluation W hW (γ ≫ f) := by
  apply (cancel_mono (SegalHomotopy.equivalenceSubcomplex W hW).ι).mp
  rw [Category.assoc, evaluation_ι, evaluation_ι]
  exact EquivalenceMapping.edgeEvaluation_source W f γ

/-- Point evaluation retains the actual target map in outer degree zero. -/
@[reassoc]
theorem pointEvaluation_naturality_target {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (x : SSet.coherentIso.{u} _⦋0⦌) :
    (discreteSourceMappingMap f).app (op SSet.coherentIso) ≫ pointEvaluation V x =
      pointEvaluation W x ≫ f.hom.app (op ⦋0⦌) := by
  unfold pointEvaluation
  rw [← Category.assoc, ← (discreteSourceMappingMap f).naturality
    (SSet.yonedaEquiv.symm x).op, Category.assoc,
    discreteYonedaIso_naturality_target]
  exact (Category.assoc _ _ _).symm

/-- The canonical evaluation keeps the original source endpoint of every original E edge. -/
@[reassoc]
theorem evaluation_source (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (γ : (Δ[1] : SSet.{u}) ⟶ SSet.coherentIso) :
    evaluation W hW γ ≫ (SegalHomotopy.equivalenceSubcomplex W hW).ι ≫
        W.diagram.δ (1 : Fin 2) =
      pointEvaluation W
        (SSet.coherentIso.map (SimplexCategory.δ (1 : Fin 2)).op (SSet.yonedaEquiv γ)) := by
  rw [evaluation_ι_assoc]
  change simplexEvaluation W γ ≫ W.diagram.map (SimplexCategory.δ (1 : Fin 2)).op =
    simplexEvaluation W (SSet.yonedaEquiv.symm
      (SSet.coherentIso.map (SimplexCategory.δ (1 : Fin 2)).op (SSet.yonedaEquiv γ)))
  have h := simplexEvaluation_yoneda_map W (SimplexCategory.δ (1 : Fin 2))
    (SSet.yonedaEquiv γ)
  simpa only [Equiv.symm_apply_apply] using h.symm

/-- The same canonical evaluation keeps the original target endpoint of every E edge. -/
@[reassoc]
theorem evaluation_target (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (γ : (Δ[1] : SSet.{u}) ⟶ SSet.coherentIso) :
    evaluation W hW γ ≫ (SegalHomotopy.equivalenceSubcomplex W hW).ι ≫
        W.diagram.δ (0 : Fin 2) =
      pointEvaluation W
        (SSet.coherentIso.map (SimplexCategory.δ (0 : Fin 2)).op (SSet.yonedaEquiv γ)) := by
  rw [evaluation_ι_assoc]
  change simplexEvaluation W γ ≫ W.diagram.map (SimplexCategory.δ (0 : Fin 2)).op =
    simplexEvaluation W (SSet.yonedaEquiv.symm
      (SSet.coherentIso.map (SimplexCategory.δ (0 : Fin 2)).op (SSet.yonedaEquiv γ)))
  have h := simplexEvaluation_yoneda_map W (SimplexCategory.δ (0 : Fin 2))
    (SSet.yonedaEquiv γ)
  simpa only [Equiv.symm_apply_apply] using h.symm

/-- The original forward evaluation has the original zero source vertex. -/
@[reassoc]
theorem forwardEvaluation_source (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    evaluation W hW SSet.coherentIso.forwardMap ≫
        (SegalHomotopy.equivalenceSubcomplex W hW).ι ≫ W.diagram.δ (1 : Fin 2) =
      pointEvaluation W SSet.coherentIso.x₀ := by
  rw [evaluation_ι_assoc]
  exact eval_source W WalkingIso.iso.hom

/-- The original forward evaluation has the original one target vertex. -/
@[reassoc]
theorem forwardEvaluation_target (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    evaluation W hW SSet.coherentIso.forwardMap ≫
        (SegalHomotopy.equivalenceSubcomplex W hW).ι ≫ W.diagram.δ (0 : Fin 2) =
      pointEvaluation W SSet.coherentIso.x₁ := by
  rw [evaluation_ι_assoc]
  exact eval_target W WalkingIso.iso.hom

private def selectionIso (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (EquivalenceMapping.subcomplex W hW SSet.coherentIso : SSet.{u}) ≅
      (discreteSourceMapping W).obj (op SSet.coherentIso) :=
  SSet.Subcomplex.eqToIso (selection_eq_top W hW) ≪≫ SSet.Subcomplex.topIso _

private theorem selectionIso_inv_ι (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (selectionIso W hW).inv ≫ (EquivalenceMapping.subcomplex W hW SSet.coherentIso).ι = 𝟙 _ := by
  have hi : (SSet.Subcomplex.eqToIso (selection_eq_top W hW)).inv ≫
      (EquivalenceMapping.subcomplex W hW SSet.coherentIso).ι =
      (⊤ : ((discreteSourceMapping W).obj (op SSet.coherentIso)).Subcomplex).ι := rfl
  change ((SSet.Subcomplex.topIso _).inv ≫
    (SSet.Subcomplex.eqToIso (selection_eq_top W hW)).inv) ≫ _ = _
  rw [Category.assoc, hi, SSet.Subcomplex.topIso_inv_ι]

/-- The full original E mapping space is Kan from the same named Reedy-fibrant Segal object. -/
theorem mapping_kan (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    SSet.KanComplex ((discreteSourceMapping W).obj (op SSet.coherentIso)) :=
  EquivalenceMapping.rawMapping_kan W hW SSet.coherentIso

/-- The original equivalence-arrow subcomplex is Kan through the actual restricted Yoneda
isomorphism. -/
theorem equivalenceSubcomplex_kan (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    SSet.KanComplex (SegalHomotopy.equivalenceSubcomplex W hW : SSet.{u}) := by
  let _ : SSet.KanComplex (EquivalenceMapping.subcomplex W hW Δ[1] : SSet.{u}) :=
    EquivalenceMapping.subcomplex_kan W hW Δ[1]
  exact isFibrant_of_fibration (EquivalenceMapping.yonedaIsoOne W hW).inv

/-- The canonical full-E forward evaluation is a Kan fibration, derived without completeness. -/
theorem forwardEvaluation_fibration (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    Fibration (evaluation W hW SSet.coherentIso.forwardMap) := by
  have he : (selectionIso W hW).inv ≫
      EquivalenceMapping.restriction W hW SSet.coherentIso.forwardMap ≫
        (EquivalenceMapping.yonedaIsoOne W hW).hom =
      evaluation W hW SSet.coherentIso.forwardMap := by
    apply (cancel_mono (SegalHomotopy.equivalenceSubcomplex W hW).ι).mp
    simp only [Category.assoc, EquivalenceMapping.yonedaIsoOne_hom_ι,
      EquivalenceMapping.restriction_ι_assoc, evaluation_ι]
    rw [← Category.assoc, selectionIso_inv_ι, Category.id_comp]
    rfl
  rw [← he]
  let _ : Fibration (EquivalenceMapping.restriction W hW SSet.coherentIso.forwardMap) :=
    EquivalenceMapping.restriction_fibration W hW SSet.coherentIso.forwardMap
  infer_instance

/-- The original full-E collapse gives the constant full-E map on the same degree-zero object. -/
def constantMap (W : SimplicialSpace.{u}) : W.diagram _⦋0⦌ ⟶
    (discreteSourceMapping W).obj (op SSet.coherentIso) :=
  (discreteYonedaIso W 0).inv ≫ (innerHomFunctor.flip.obj W).map
    (ofSimplicialObject.map SSet.Rezk.FiniteCompleteness.epsilon).op

private theorem point_epsilon (x : SSet.coherentIso.{u} _⦋0⦌) :
    SSet.simplicialSpaceDiscrete.map (SSet.yonedaEquiv.symm x) ≫
      SSet.Rezk.FiniteCompleteness.epsilon = 𝟙 (SSet.Rezk.representable.{u} 0) := by
  ext m n q
  change ULift.up (SimplexCategory.const m.unop ⦋0⦌ 0) = q
  apply ULift.ext
  exact (SimplexCategory.eq_const_to_zero _).symm

private theorem edge_epsilon (γ : (Δ[1] : SSet.{u}) ⟶ SSet.coherentIso) :
    SSet.simplicialSpaceDiscrete.map γ ≫ SSet.Rezk.FiniteCompleteness.epsilon =
      SSet.Rezk.FiniteCompleteness.representableCollapse.{u} 1 := by
  ext m n q
  change ULift.up (SimplexCategory.const m.unop ⦋0⦌ 0) =
    ULift.up (SSet.stdSimplex.objEquiv q ≫ SimplexCategory.const ⦋1⦌ ⦋0⦌ 0)
  apply ULift.ext
  exact (SimplexCategory.eq_const_to_zero _).symm

/-- Every original point of full E evaluates its original constant map to the identity on W₀. -/
@[reassoc]
theorem constant_pointEvaluation (W : SimplicialSpace.{u}) (x : SSet.coherentIso.{u} _⦋0⦌) :
    constantMap W ≫ pointEvaluation W x = 𝟙 (W.diagram _⦋0⦌) := by
  let F := innerHomFunctor.flip.obj W
  let e₀ : F.obj (op (ofSimplicialObject.obj (SSet.Rezk.representable.{u} 0))) ≅
      W.diagram _⦋0⦌ := discreteYonedaIso W 0
  have hc : ofSimplicialObject.map
      (SSet.simplicialSpaceDiscrete.map (SSet.yonedaEquiv.symm x)) ≫
      ofSimplicialObject.map SSet.Rezk.FiniteCompleteness.epsilon = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, point_epsilon, CategoryTheory.Functor.map_id]
  have hf : F.map (ofSimplicialObject.map SSet.Rezk.FiniteCompleteness.epsilon).op ≫
      F.map (ofSimplicialObject.map
        (SSet.simplicialSpaceDiscrete.map (SSet.yonedaEquiv.symm x))).op = 𝟙 _ := by
    rw [← F.map_comp, ← op_comp, hc, op_id, F.map_id]
  change (e₀.inv ≫ F.map (ofSimplicialObject.map SSet.Rezk.FiniteCompleteness.epsilon).op) ≫
    (F.map (ofSimplicialObject.map
      (SSet.simplicialSpaceDiscrete.map (SSet.yonedaEquiv.symm x))).op ≫ e₀.hom) = _
  calc
    _ = e₀.inv ≫
        (F.map (ofSimplicialObject.map SSet.Rezk.FiniteCompleteness.epsilon).op ≫
          F.map (ofSimplicialObject.map
            (SSet.simplicialSpaceDiscrete.map (SSet.yonedaEquiv.symm x))).op) ≫ e₀.hom := by
      simp only [Category.assoc]
    _ = 𝟙 _ := by rw [hf, Category.id_comp, Iso.inv_hom_id]

/-- The original zero-point evaluation is a strict section of the same constant full-E map. -/
@[reassoc]
theorem constant_source (W : SimplicialSpace.{u}) :
    constantMap W ≫ pointEvaluation W SSet.coherentIso.x₀ = 𝟙 (W.diagram _⦋0⦌) :=
  constant_pointEvaluation W SSet.coherentIso.x₀

/-- The original one-point evaluation is the other strict section of the same constant full-E
map. -/
@[reassoc]
theorem constant_target (W : SimplicialSpace.{u}) :
    constantMap W ≫ pointEvaluation W SSet.coherentIso.x₁ = 𝟙 (W.diagram _⦋0⦌) :=
  constant_pointEvaluation W SSet.coherentIso.x₁

/-- Evaluating the original constant full-E map on any original edge gives the original identity
degeneracy factor. -/
@[reassoc]
theorem constant_evaluation (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (γ : (Δ[1] : SSet.{u}) ⟶ SSet.coherentIso) :
    constantMap W ≫ evaluation W hW γ = SegalHomotopy.equivalenceIdentity W hW := by
  apply (cancel_mono (SegalHomotopy.equivalenceSubcomplex W hW).ι).mp
  rw [Category.assoc, evaluation_ι, SegalHomotopy.equivalenceIdentity_ι]
  let F := innerHomFunctor.flip.obj W
  let e₀ : F.obj (op (ofSimplicialObject.obj (SSet.Rezk.representable.{u} 0))) ≅
      W.diagram _⦋0⦌ := discreteYonedaIso W 0
  let e₁ : F.obj (op (ofSimplicialObject.obj (SSet.Rezk.representable.{u} 1))) ≅
      W.diagram _⦋1⦌ := discreteYonedaIso W 1
  have hc : ofSimplicialObject.map (SSet.simplicialSpaceDiscrete.map γ) ≫
      ofSimplicialObject.map SSet.Rezk.FiniteCompleteness.epsilon =
      ofSimplicialObject.map (SSet.Rezk.FiniteCompleteness.representableCollapse.{u} 1) := by
    rw [← CategoryTheory.Functor.map_comp, edge_epsilon]
  have hf : F.map (ofSimplicialObject.map SSet.Rezk.FiniteCompleteness.epsilon).op ≫
      F.map (ofSimplicialObject.map (SSet.simplicialSpaceDiscrete.map γ)).op =
      F.map
          (ofSimplicialObject.map
            (SSet.Rezk.FiniteCompleteness.representableCollapse.{u} 1)).op := by
    rw [← F.map_comp, ← op_comp, hc]
  have hσ : SSet.Rezk.FiniteCompleteness.representableCollapse.{u} 1 =
      SSet.simplicialSpaceDiscrete.map (SSet.stdSimplex.map (SimplexCategory.σ (0 : Fin 1))) := by
    unfold SSet.Rezk.FiniteCompleteness.representableCollapse
    rw [(SimplexCategory.eq_const_to_zero (SimplexCategory.σ (0 : Fin 1))).symm]
  have hy : F.map (ofSimplicialObject.map
      (SSet.simplicialSpaceDiscrete.map (SSet.stdSimplex.map (SimplexCategory.σ (0 : Fin 1))))).op ≫
      e₁.hom = e₀.hom ≫ W.diagram.σ (0 : Fin 1) :=
    discreteYonedaIso_naturality_index W (SimplexCategory.σ (0 : Fin 1))
  change (e₀.inv ≫ F.map (ofSimplicialObject.map SSet.Rezk.FiniteCompleteness.epsilon).op) ≫
      (F.map (ofSimplicialObject.map (SSet.simplicialSpaceDiscrete.map γ)).op ≫ e₁.hom) = _
  calc
    _ = e₀.inv ≫
        (F.map (ofSimplicialObject.map SSet.Rezk.FiniteCompleteness.epsilon).op ≫
          F.map (ofSimplicialObject.map (SSet.simplicialSpaceDiscrete.map γ)).op) ≫ e₁.hom := by
      simp only [Category.assoc]
    _ = e₀.inv ≫ e₀.hom ≫ W.diagram.σ (0 : Fin 1) := by
      rw [hf, hσ, hy]
    _ = _ := by rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Constant full-E maps preserve every original target arrow. -/
@[reassoc]
theorem constantMap_naturality_target {W V : SimplicialSpace.{u}} (f : W ⟶ V) :
    f.hom.app (op ⦋0⦌) ≫ constantMap V =
      constantMap W ≫ (discreteSourceMappingMap f).app (op SSet.coherentIso) := by
  let FW := innerHomFunctor.flip.obj W
  let FV := innerHomFunctor.flip.obj V
  let t := innerHomFunctor.flip.map f
  let eW : FW.obj (op (ofSimplicialObject.obj (SSet.Rezk.representable.{u} 0))) ≅
      W.diagram _⦋0⦌ := discreteYonedaIso W 0
  let eV : FV.obj (op (ofSimplicialObject.obj (SSet.Rezk.representable.{u} 0))) ≅
      V.diagram _⦋0⦌ := discreteYonedaIso V 0
  have hz : t.app (op (ofSimplicialObject.obj (SSet.Rezk.representable.{u} 0))) ≫ eV.hom =
      eW.hom ≫ f.hom.app (op ⦋0⦌) := discreteYonedaIso_naturality_target f 0
  have h₀ : f.hom.app (op ⦋0⦌) ≫ eV.inv =
      eW.inv ≫ t.app (op (ofSimplicialObject.obj (SSet.Rezk.representable.{u} 0))) := by
    apply (cancel_mono eV.hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Category.assoc, hz, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have he := t.naturality (ofSimplicialObject.map SSet.Rezk.FiniteCompleteness.epsilon).op
  change f.hom.app (op ⦋0⦌) ≫
    (eV.inv ≫ FV.map (ofSimplicialObject.map SSet.Rezk.FiniteCompleteness.epsilon).op) =
    (eW.inv ≫ FW.map (ofSimplicialObject.map SSet.Rezk.FiniteCompleteness.epsilon).op) ≫
      t.app (op (ofSimplicialObject.obj SSet.Rezk.walkingIsomorphism.{u}))
  rw [← Category.assoc, h₀, Category.assoc, ← he, ← Category.assoc]

/-- The actual full-nerve involution swaps the two original objects and their inverse arrows. -/
def involution : SSet.coherentIso.{u} ⟶ SSet.coherentIso :=
  CategoryTheory.nerveMap (WalkingIso.fromIso WalkingIso.iso.symm)

/-- The actual involution negates every original Boolean vertex coordinate. -/
theorem involution_vertexBool {n : ℕ} (q : SSet.coherentIso.{u} _⦋n⦌) (i : Fin (n + 1)) :
    SSet.coherentIso.vertexBool (involution.app (op ⦋n⦌) q) i =
      !(SSet.coherentIso.vertexBool q i) := by
  change WalkingIso.equivBool ((WalkingIso.fromIso WalkingIso.iso.symm).obj (q.obj i)) =
    !(WalkingIso.equivBool (q.obj i))
  generalize q.obj i = x
  induction x <;> rfl

/-- The same original full-nerve involution is its own inverse in every degree. -/
@[reassoc (attr := simp)]
theorem involution_comp_self : involution.{u} ≫ involution = 𝟙 SSet.coherentIso := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro q
  change involution.app (op ⦋n.unop.len⦌) (involution.app (op ⦋n.unop.len⦌) q) = q
  apply SSet.coherentIso.eq_of_forall_vertexBool_eq
  intro i
  rw [involution_vertexBool, involution_vertexBool]
  exact Bool.not_not _

/-- The original forward E01 edge becomes the original backward E10 edge under the actual
involution. -/
@[reassoc]
theorem forwardMap_involution : SSet.coherentIso.forwardMap.{u} ≫ involution =
    SSet.yonedaEquiv.symm SSet.coherentIso.inv.edge := by
  dsimp only [SSet.coherentIso.forwardMap]
  rw [SSet.yonedaEquiv_symm_comp]
  apply congrArg SSet.yonedaEquiv.symm
  apply SSet.coherentIso.eq_of_forall_vertexBool_eq
  intro i
  fin_cases i <;> rfl

/-- The actual involution sends the original zero point to the original one point. -/
@[reassoc]
theorem zeroMap_involution : SSet.coherentIso.zeroMap.{u} ≫ involution =
    SSet.yonedaEquiv.symm SSet.coherentIso.x₁ := by
  dsimp only [SSet.coherentIso.zeroMap]
  rw [SSet.yonedaEquiv_symm_comp]
  apply congrArg SSet.yonedaEquiv.symm
  exact ComposableArrows.ext₀ rfl

/-- The same involution sends the original one point back to the original zero point. -/
@[reassoc]
theorem oneMap_involution : SSet.yonedaEquiv.symm SSet.coherentIso.x₁ ≫ involution.{u} =
    SSet.coherentIso.zeroMap := by
  dsimp only [SSet.coherentIso.zeroMap]
  rw [SSet.yonedaEquiv_symm_comp]
  apply congrArg SSet.yonedaEquiv.symm
  exact ComposableArrows.ext₀ rfl

/-- The original central12 edge follows the original simplex through both chosen finite-K
pushouts. -/
def centralMap : SSet.Rezk.representable.{u} 1 ⟶ SSet.Rezk.FiniteCompleteness.K :=
  SSet.simplicialSpaceDiscrete.map
      (SSet.stdSimplex.map (SimplexCategory.mkOfLe (1 : Fin 4) (2 : Fin 4) (by decide))) ≫
    SSet.Rezk.FiniteCompleteness.stage1Cocone.inr ≫
    SSet.Rezk.FiniteCompleteness.stage2Cocone.inl

/-- The literal original j maps central K12 to backward E10, with the actual discrete embedding. -/
@[reassoc]
theorem centralMap_comparison : centralMap.{u} ≫ SSet.Rezk.FiniteCompleteness.comparison =
    SSet.simplicialSpaceDiscrete.map (SSet.coherentIso.forwardMap ≫ involution) := by
  unfold centralMap
  simp only [Category.assoc]
  rw [SSet.Rezk.FiniteCompleteness.comparison_mid]
  rw [forwardMap_involution]
  unfold SSet.Rezk.FiniteCompleteness.comparisonSimplex
  rw [← Functor.map_comp]
  apply congrArg SSet.simplicialSpaceDiscrete.map
  let t : SSet.coherentIso.{u} _⦋3⦌ :=
    ComposableArrows.mk₃ WalkingIso.iso.hom WalkingIso.iso.inv WalkingIso.iso.hom
  change SSet.stdSimplex.map (SimplexCategory.mkOfLe (1 : Fin 4) (2 : Fin 4) (by decide)) ≫
    SSet.yonedaEquiv.symm t = SSet.yonedaEquiv.symm SSet.coherentIso.inv.edge
  rw [SSet.yonedaEquiv_symm_naturality_left]
  apply congrArg SSet.yonedaEquiv.symm
  apply SSet.coherentIso.eq_of_forall_vertexBool_eq
  intro i
  fin_cases i <;> rfl

/-- The retained literal raw j has its original whole inner-end comparison to backward E
evaluation. -/
@[reassoc]
theorem centralMap_evaluation (W : SimplicialSpace.{u}) :
    (innerHomFunctor.map
      (ofSimplicialObject.map SSet.Rezk.FiniteCompleteness.comparison).op).app W ≫
      (innerHomFunctor.map (ofSimplicialObject.map centralMap.{u}).op).app W ≫
      (discreteYonedaIso W 1).hom =
    (discreteSourceMapping W).map involution.op ≫
      EquivalenceMapping.edgeEvaluation W SSet.coherentIso.forwardMap := by
  let F := innerHomFunctor.flip.obj W
  let e₁ : F.obj (op (ofSimplicialObject.obj (SSet.Rezk.representable.{u} 1))) ≅
      W.diagram _⦋1⦌ := discreteYonedaIso W 1
  have hraw : ofSimplicialObject.map centralMap.{u} ≫
      ofSimplicialObject.map SSet.Rezk.FiniteCompleteness.comparison =
      ofSimplicialObject.map
        (SSet.simplicialSpaceDiscrete.map (SSet.coherentIso.forwardMap ≫ involution)) := by
    rw [← CategoryTheory.Functor.map_comp, centralMap_comparison]
  have hc : F.map (ofSimplicialObject.map SSet.Rezk.FiniteCompleteness.comparison).op ≫
      F.map (ofSimplicialObject.map centralMap.{u}).op =
      F.map (ofSimplicialObject.map
        (SSet.simplicialSpaceDiscrete.map (SSet.coherentIso.forwardMap ≫ involution))).op := by
    rw [← F.map_comp, ← op_comp, hraw]
  have hs : F.map (ofSimplicialObject.map
      (SSet.simplicialSpaceDiscrete.map (SSet.coherentIso.forwardMap ≫ involution))).op =
      F.map (ofSimplicialObject.map (SSet.simplicialSpaceDiscrete.map involution)).op ≫
      F.map (ofSimplicialObject.map
        (SSet.simplicialSpaceDiscrete.map SSet.coherentIso.forwardMap)).op := by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      op_comp, F.map_comp]
  change F.map (ofSimplicialObject.map SSet.Rezk.FiniteCompleteness.comparison).op ≫
    F.map (ofSimplicialObject.map centralMap.{u}).op ≫ e₁.hom =
    F.map (ofSimplicialObject.map (SSet.simplicialSpaceDiscrete.map involution)).op ≫
      F.map (ofSimplicialObject.map
        (SSet.simplicialSpaceDiscrete.map SSet.coherentIso.forwardMap)).op ≫ e₁.hom
  rw [← Category.assoc, hc, hs, Category.assoc]

end SimplicialSpace.FullEEquivalence
