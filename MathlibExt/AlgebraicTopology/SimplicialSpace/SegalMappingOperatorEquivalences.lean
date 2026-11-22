/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalMappingComposition
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceHomotopyInvariance
import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure

/-!
# Intrinsic equivalences give weak maps on the original full mapping spaces

The two inverse points are read from the original inverse-test three-simplex.
They need not agree. All operator comparisons are full simplicial homotopies.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace

open SegalHomotopy

private def terminalHomotopy {X Y : SSet.{u}} {f g : X ⟶ Y}
    (p : Y ⟶ (Δ[0] : SSet.{u})) (H : SSet.Homotopy f g) :
    SSet.HomotopyRelOver p f g (⊥ : X.Subcomplex) where
  toHomotopyRel :=
    { h := H.h
      h₀ := H.h₀
      h₁ := H.h₁
      stationary := by intro n a ha t; cases ha }
  over := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

private def reverseOperatorHomotopy {X Y : SSet.{u}} {f g : X ⟶ Y}
    (p : Y ⟶ (Δ[0] : SSet.{u})) [Fibration p] (H : SSet.Homotopy f g) :
    SSet.Homotopy g f :=
  (SSet.HomotopyRelOver.symm (terminalHomotopy p H)).toHomotopyRel.toHomotopy

private def joinOperatorHomotopy {X Y : SSet.{u}} {f g h : X ⟶ Y}
    (p : Y ⟶ (Δ[0] : SSet.{u})) [Fibration p]
    (H₀ : SSet.Homotopy f g) (H₁ : SSet.Homotopy g h) : SSet.Homotopy f h :=
  (SSet.HomotopyRelOver.trans (terminalHomotopy p H₀)
    (terminalHomotopy p H₁)).toHomotopyRel.toHomotopy

private theorem scalarWeakOfTwoComposites {X Y : SSet.{u}}
    (f : X ⟶ Y) (gₗ gᵣ : Y ⟶ X)
    (hₗ : SSet.Homotopy (f ≫ gₗ) (𝟙 X))
    (hᵣ : SSet.Homotopy (gᵣ ≫ f) (𝟙 Y)) :
    SSet.realizationWeakEquivalences f := by
  let : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  have hwₗ : SSet.realizationWeakEquivalences (f ≫ gₗ) :=
    (SSet.realizationWeakEquivalences_iff_of_homotopy hₗ).mpr
      ((weakEquivalence_iff (𝟙 X)).mp inferInstance)
  have hwᵣ : SSet.realizationWeakEquivalences (gᵣ ≫ f) :=
    (SSet.realizationWeakEquivalences_iff_of_homotopy hᵣ).mpr
      ((weakEquivalence_iff (𝟙 Y)).mp inferInstance)
  let L := toHomotopyCategory SSet.{u}
  have hiₗ : IsIso (L.map (f ≫ gₗ)) :=
    (weakEquivalence_iff_isIso_toHomotopyCategory_map _).mp hwₗ
  have hiᵣ : IsIso (L.map (gᵣ ≫ f)) :=
    (weakEquivalence_iff_isIso_toHomotopyCategory_map _).mp hwᵣ
  let : IsIso (L.map (f ≫ gₗ)) := hiₗ
  let : IsIso (L.map (gᵣ ≫ f)) := hiᵣ
  let l := L.map gₗ ≫ inv (L.map (f ≫ gₗ))
  let r := inv (L.map (gᵣ ≫ f)) ≫ L.map gᵣ
  have hl : L.map f ≫ l = 𝟙 (L.obj X) := by
    dsimp only [l]
    rw [← Category.assoc, ← L.map_comp]
    exact IsIso.hom_inv_id _
  have hr : r ≫ L.map f = 𝟙 (L.obj Y) := by
    dsimp only [r]
    rw [Category.assoc, ← L.map_comp]
    exact IsIso.inv_hom_id _
  have he : l = r := by
    calc
      l = (𝟙 (L.obj Y)) ≫ l := (Category.id_comp _).symm
      _ = (r ≫ L.map f) ≫ l := by rw [hr]
      _ = r ≫ (L.map f ≫ l) := Category.assoc _ _ _
      _ = r := by rw [hl, Category.comp_id]
  have hf : IsIso (L.map f) := ⟨⟨l, hl, by rw [he]; exact hr⟩⟩
  exact (weakEquivalence_iff_isIso_toHomotopyCategory_map f).mpr hf

private def edgeMap (W : SimplicialSpace.{u}) (i j : Fin 4) (hij : i ≤ j) :
    W.diagram _⦋3⦌ ⟶ W.diagram _⦋1⦌ :=
  W.diagram.map (SimplexCategory.mkOfLe i j hij).op

private def vertexMap (W : SimplicialSpace.{u}) (i : Fin 4) :
    W.diagram _⦋3⦌ ⟶ W.diagram _⦋0⦌ :=
  W.diagram.map (SimplexCategory.const ⦋0⦌ ⦋3⦌ i).op

private theorem edgeMap_source (W : SimplicialSpace.{u}) (i j : Fin 4) (hij : i ≤ j) :
    edgeMap W i j hij ≫ W.diagram.δ (1 : Fin 2) = vertexMap W i := by
  change W.diagram.map (SimplexCategory.mkOfLe i j hij).op ≫
    W.diagram.map (SimplexCategory.δ (1 : Fin 2)).op = _
  have h : SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.mkOfLe i j hij =
      SimplexCategory.const ⦋0⦌ ⦋3⦌ i := by
    ext a
    fin_cases a
    rfl
  simpa only [edgeMap, vertexMap, Functor.map_comp, op_comp] using
    congrArg (fun q => W.diagram.map q.op) h

private theorem edgeMap_target (W : SimplicialSpace.{u}) (i j : Fin 4) (hij : i ≤ j) :
    edgeMap W i j hij ≫ W.diagram.δ (0 : Fin 2) = vertexMap W j := by
  change W.diagram.map (SimplexCategory.mkOfLe i j hij).op ≫
    W.diagram.map (SimplexCategory.δ (0 : Fin 2)).op = _
  have h : SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.mkOfLe i j hij =
      SimplexCategory.const ⦋0⦌ ⦋3⦌ j := by
    ext a
    fin_cases a
    rfl
  simpa only [edgeMap, vertexMap, Functor.map_comp, op_comp] using
    congrArg (fun q => W.diagram.map q.op) h

private theorem faceEdge (W : SimplicialSpace.{u}) (k : Fin 4) (l : Fin 3)
    (i j : Fin 4) (hij : i ≤ j)
    (h : SimplexCategory.δ l ≫ SimplexCategory.δ k = SimplexCategory.mkOfLe i j hij) :
    W.diagram.δ k ≫ W.diagram.δ l = edgeMap W i j hij := by
  change W.diagram.map (SimplexCategory.δ k).op ≫ W.diagram.map (SimplexCategory.δ l).op = _
  simpa only [edgeMap, Functor.map_comp, op_comp] using
    congrArg (fun q => W.diagram.map q.op) h

private def fibrePoint (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (e : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋1⦌)
    (hs : e ≫ W.diagram.δ (1 : Fin 2) = SSet.yonedaEquiv.symm x)
    (ht : e ≫ W.diagram.δ (0 : Fin 2) = SSet.yonedaEquiv.symm y) :
    (Δ[0] : SSet.{u}) ⟶ mappingFibre W x y :=
  pullback.lift e (𝟙 _) (by
    apply prod.hom_ext
    · rw [Category.assoc, mappingEndpoint_fst, Category.id_comp, mappingPointPair_fst, hs]
    · rw [Category.assoc, mappingEndpoint_snd, Category.id_comp, mappingPointPair_snd, ht])

private theorem fibrePoint_fst (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (e : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋1⦌)
    (hs : e ≫ W.diagram.δ (1 : Fin 2) = SSet.yonedaEquiv.symm x)
    (ht : e ≫ W.diagram.δ (0 : Fin 2) = SSet.yonedaEquiv.symm y) :
    fibrePoint W x y e hs ht ≫ mappingFibre.fst W x y = e :=
  pullback.lift_fst _ _ _

private def offeredTriangle (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌)
    (t : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋2⦌)
    (a : (Δ[0] : SSet.{u}) ⟶ mappingFibre W x y)
    (b : (Δ[0] : SSet.{u}) ⟶ mappingFibre W y z)
    (ha : a ≫ mappingFibre.fst W x y = t ≫ W.diagram.δ (2 : Fin 3))
    (hb : b ≫ mappingFibre.fst W y z = t ≫ W.diagram.δ (0 : Fin 3)) :
    (Δ[0] : SSet.{u}) ⟶ triangleSpace W x y z :=
  pullback.lift t (prod.lift a b) (by
    apply pullback.hom_ext
    · rw [Category.assoc, twoEdgeComparison_fst, Category.assoc, twoEdgePair_fst,
        prod.lift_fst_assoc, ha]
    · rw [Category.assoc, twoEdgeComparison_snd, Category.assoc, twoEdgePair_snd,
        prod.lift_snd_assoc, hb])

private theorem offeredTriangle_first (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌)
    (t : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋2⦌)
    (a : (Δ[0] : SSet.{u}) ⟶ mappingFibre W x y)
    (b : (Δ[0] : SSet.{u}) ⟶ mappingFibre W y z)
    (ha : a ≫ mappingFibre.fst W x y = t ≫ W.diagram.δ (2 : Fin 3))
    (hb : b ≫ mappingFibre.fst W y z = t ≫ W.diagram.δ (0 : Fin 3)) :
    offeredTriangle W x y z t a b ha hb ≫ triangleComparison W x y z ≫ prod.fst = a := by
  simp only [offeredTriangle, triangleComparison, pullback.lift_snd_assoc, prod.lift_fst]

private theorem offeredTriangle_last (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌)
    (t : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋2⦌)
    (a : (Δ[0] : SSet.{u}) ⟶ mappingFibre W x y)
    (b : (Δ[0] : SSet.{u}) ⟶ mappingFibre W y z)
    (ha : a ≫ mappingFibre.fst W x y = t ≫ W.diagram.δ (2 : Fin 3))
    (hb : b ≫ mappingFibre.fst W y z = t ≫ W.diagram.δ (0 : Fin 3)) :
    offeredTriangle W x y z t a b ha hb ≫ triangleComparison W x y z ≫ prod.snd = b := by
  simp only [offeredTriangle, triangleComparison, pullback.lift_snd_assoc, prod.lift_snd]

private theorem offeredTriangle_middle (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌)
    (t : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋2⦌)
    (a : (Δ[0] : SSet.{u}) ⟶ mappingFibre W x y)
    (b : (Δ[0] : SSet.{u}) ⟶ mappingFibre W y z)
    (ha : a ≫ mappingFibre.fst W x y = t ≫ W.diagram.δ (2 : Fin 3))
    (hb : b ≫ mappingFibre.fst W y z = t ≫ W.diagram.δ (0 : Fin 3)) :
    offeredTriangle W x y z t a b ha hb ≫ triangleMiddle W x y z ≫
      mappingFibre.fst W x z = t ≫ W.diagram.δ (1 : Fin 3) := by
  rw [triangleMiddle_fst]
  simp only [offeredTriangle, triangleProjection, pullback.lift_fst_assoc]

private theorem point_source (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W x y) _⦋0⦌) :
    (SSet.yonedaEquiv.symm a ≫ mappingFibre.fst W x y) ≫ W.diagram.δ (1 : Fin 2) =
      SSet.yonedaEquiv.symm x := by
  rw [Category.assoc, mappingFibre.source_eq, ← Category.assoc,
    SSet.stdSimplex.isTerminalObj₀.hom_ext
      (SSet.yonedaEquiv.symm a ≫ mappingFibre.snd W x y) (𝟙 _), Category.id_comp]

private theorem point_target (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W x y) _⦋0⦌) :
    (SSet.yonedaEquiv.symm a ≫ mappingFibre.fst W x y) ≫ W.diagram.δ (0 : Fin 2) =
      SSet.yonedaEquiv.symm y := by
  rw [Category.assoc, mappingFibre.target_eq, ← Category.assoc,
    SSet.stdSimplex.isTerminalObj₀.hom_ext
      (SSet.yonedaEquiv.symm a ≫ mappingFibre.snd W x y) (𝟙 _), Category.id_comp]

private theorem identityPoint_fst (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.yonedaEquiv.symm (identityVertex W x) ≫ mappingFibre.fst W x x =
      SSet.yonedaEquiv.symm x ≫ W.diagram.σ (0 : Fin 1) := by
  rw [SSet.yonedaEquiv_symm_comp, identityVertex_fst, SSet.yonedaEquiv_symm_comp]

private theorem inverseTriangles (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W x y) _⦋0⦌)
    (ha : IsEquivalenceEdge W hW ((mappingFibre.fst W x y).app (op ⦋0⦌) a)) :
    ∃ (b c : (mappingFibre W y x) _⦋0⦌)
      (kₗ : (triangleSpace W y x y) _⦋0⦌) (kᵣ : (triangleSpace W x y x) _⦋0⦌),
      (triangleComparison W y x y ≫ prod.fst).app (op ⦋0⦌) kₗ = b ∧
      (triangleComparison W y x y ≫ prod.snd).app (op ⦋0⦌) kₗ = a ∧
      (triangleMiddle W y x y).app (op ⦋0⦌) kₗ = identityVertex W y ∧
      (triangleComparison W x y x ≫ prod.fst).app (op ⦋0⦌) kᵣ = a ∧
      (triangleComparison W x y x ≫ prod.snd).app (op ⦋0⦌) kᵣ = c ∧
      (triangleMiddle W x y x).app (op ⦋0⦌) kᵣ = identityVertex W x := by
  obtain ⟨t, ht⟩ := hasInverseData_of_isEquivalenceEdge W hW
    ((mappingFibre.fst W x y).app (op ⦋0⦌) a) ha
  let A := SSet.yonedaEquiv.symm a
  let T := SSet.yonedaEquiv.symm t
  have hinv : T ≫ inverseRestriction W = A ≫ mappingFibre.fst W x y ≫ identityTriple W := by
    simpa only [T, A, SSet.yonedaEquiv_symm_comp, SSet.comp_app,
      CategoryTheory.comp_apply] using congrArg SSet.yonedaEquiv.symm ht
  have h02 : T ≫ edgeMap W 0 2 (by decide) =
      SSet.yonedaEquiv.symm y ≫ W.diagram.σ (0 : Fin 1) := by
    calc
      _ = (A ≫ mappingFibre.fst W x y ≫ W.diagram.δ (0 : Fin 2)) ≫
          W.diagram.σ (0 : Fin 1) := by
        simpa only [edgeMap, Category.assoc, inverseRestriction_first, identityTriple_first]
          using congrArg (fun f => f ≫ inverseFirst W) hinv
      _ = _ := by rw [← Category.assoc A, point_target]
  have h12 : T ≫ edgeMap W 1 2 (by decide) = A ≫ mappingFibre.fst W x y := by
    simpa only [edgeMap, Category.assoc, inverseRestriction_middle, identityTriple_middle,
      Category.comp_id] using congrArg (fun f => f ≫ inverseMiddle W) hinv
  have h13 : T ≫ edgeMap W 1 3 (by decide) =
      SSet.yonedaEquiv.symm x ≫ W.diagram.σ (0 : Fin 1) := by
    calc
      _ = (A ≫ mappingFibre.fst W x y ≫ W.diagram.δ (1 : Fin 2)) ≫
          W.diagram.σ (0 : Fin 1) := by
        simpa only [edgeMap, Category.assoc, inverseRestriction_last, identityTriple_last]
          using congrArg (fun f => f ≫ inverseLast W) hinv
      _ = _ := by rw [← Category.assoc A, point_source]
  have hv₀ : T ≫ vertexMap W 0 = SSet.yonedaEquiv.symm y := by
    have hs : W.diagram.σ (0 : Fin 1) ≫ W.diagram.δ (1 : Fin 2) = 𝟙 _ :=
      W.diagram.δ_comp_σ_succ (i := (0 : Fin 1))
    rw [← edgeMap_source W 0 2 (by decide), ← Category.assoc, h02, Category.assoc,
      hs, Category.comp_id]
  have hv₁ : T ≫ vertexMap W 1 = SSet.yonedaEquiv.symm x := by
    rw [← edgeMap_source W 1 2 (by decide), ← Category.assoc, h12]
    exact point_source W x y a
  have hv₂ : T ≫ vertexMap W 2 = SSet.yonedaEquiv.symm y := by
    rw [← edgeMap_target W 1 2 (by decide), ← Category.assoc, h12]
    exact point_target W x y a
  have hv₃ : T ≫ vertexMap W 3 = SSet.yonedaEquiv.symm x := by
    have hs : W.diagram.σ (0 : Fin 1) ≫ W.diagram.δ (0 : Fin 2) = 𝟙 _ :=
      W.diagram.δ_comp_σ_self (i := (0 : Fin 1))
    rw [← edgeMap_target W 1 3 (by decide), ← Category.assoc, h13, Category.assoc,
      hs, Category.comp_id]
  have hbs : (T ≫ edgeMap W 0 1 (by decide)) ≫ W.diagram.δ (1 : Fin 2) =
      SSet.yonedaEquiv.symm y := by rw [Category.assoc, edgeMap_source, hv₀]
  have hbt : (T ≫ edgeMap W 0 1 (by decide)) ≫ W.diagram.δ (0 : Fin 2) =
      SSet.yonedaEquiv.symm x := by rw [Category.assoc, edgeMap_target, hv₁]
  have hcs : (T ≫ edgeMap W 2 3 (by decide)) ≫ W.diagram.δ (1 : Fin 2) =
      SSet.yonedaEquiv.symm y := by rw [Category.assoc, edgeMap_source, hv₂]
  have hct : (T ≫ edgeMap W 2 3 (by decide)) ≫ W.diagram.δ (0 : Fin 2) =
      SSet.yonedaEquiv.symm x := by rw [Category.assoc, edgeMap_target, hv₃]
  let B := fibrePoint W y x (T ≫ edgeMap W 0 1 (by decide)) hbs hbt
  let C := fibrePoint W y x (T ≫ edgeMap W 2 3 (by decide)) hcs hct
  have hb : B ≫ mappingFibre.fst W y x =
      (T ≫ W.diagram.δ (3 : Fin 4)) ≫ W.diagram.δ (2 : Fin 3) := by
    rw [Category.assoc, faceEdge W 3 2 0 1 (by decide) (by decide)]
    exact fibrePoint_fst W y x _ hbs hbt
  have haₗ : A ≫ mappingFibre.fst W x y =
      (T ≫ W.diagram.δ (3 : Fin 4)) ≫ W.diagram.δ (0 : Fin 3) := by
    rw [Category.assoc, faceEdge W 3 0 1 2 (by decide) (by decide)]
    exact h12.symm
  have haᵣ : A ≫ mappingFibre.fst W x y =
      (T ≫ W.diagram.δ (0 : Fin 4)) ≫ W.diagram.δ (2 : Fin 3) := by
    rw [Category.assoc, faceEdge W 0 2 1 2 (by decide) (by decide)]
    exact h12.symm
  have hc : C ≫ mappingFibre.fst W y x =
      (T ≫ W.diagram.δ (0 : Fin 4)) ≫ W.diagram.δ (0 : Fin 3) := by
    rw [Category.assoc, faceEdge W 0 0 2 3 (by decide) (by decide)]
    exact fibrePoint_fst W y x _ hcs hct
  let Kₗ := offeredTriangle W y x y (T ≫ W.diagram.δ (3 : Fin 4)) B A hb haₗ
  let Kᵣ := offeredTriangle W x y x (T ≫ W.diagram.δ (0 : Fin 4)) A C haᵣ hc
  have hmₗ : Kₗ ≫ triangleMiddle W y x y = SSet.yonedaEquiv.symm (identityVertex W y) := by
    apply pullback.hom_ext
    · calc
        (Kₗ ≫ triangleMiddle W y x y) ≫ mappingFibre.fst W y y =
            T ≫ edgeMap W 0 2 (by decide) := by
          dsimp only [Kₗ]
          rw [Category.assoc, offeredTriangle_middle, Category.assoc,
            faceEdge W 3 1 0 2 (by decide) (by decide)]
        _ = _ := h02
        _ = _ := (identityPoint_fst W y).symm
    · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have hmᵣ : Kᵣ ≫ triangleMiddle W x y x = SSet.yonedaEquiv.symm (identityVertex W x) := by
    apply pullback.hom_ext
    · calc
        (Kᵣ ≫ triangleMiddle W x y x) ≫ mappingFibre.fst W x x =
            T ≫ edgeMap W 1 3 (by decide) := by
          dsimp only [Kᵣ]
          rw [Category.assoc, offeredTriangle_middle, Category.assoc,
            faceEdge W 0 1 1 3 (by decide) (by decide)]
        _ = _ := h13
        _ = _ := (identityPoint_fst W x).symm
    · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  refine ⟨SSet.yonedaEquiv B, SSet.yonedaEquiv C,
    SSet.yonedaEquiv Kₗ, SSet.yonedaEquiv Kᵣ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [SSet.yonedaEquiv_comp] using congrArg SSet.yonedaEquiv
      (offeredTriangle_first W y x y _ B A hb haₗ)
  · simpa only [SSet.yonedaEquiv_comp, A, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv (offeredTriangle_last W y x y _ B A hb haₗ)
  · simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv hmₗ
  · simpa only [SSet.yonedaEquiv_comp, A, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv (offeredTriangle_first W x y x _ A C haᵣ hc)
  · simpa only [SSet.yonedaEquiv_comp] using congrArg SSet.yonedaEquiv
      (offeredTriangle_last W x y x _ A C haᵣ hc)
  · simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv hmᵣ

private theorem mappingFibration (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) : Fibration (mappingFibre.snd W x y) := by
  let : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  exact ReedyModel.mappingFibre_snd_fibration W x y hW.1

/-- Every intrinsic equivalence gives realization weakness of the same full postcomposition map. -/
theorem mappingPostcomposition_realizationWeakEquivalence
    (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W x y) _⦋0⦌)
    (ha : IsEquivalenceEdge W hW ((mappingFibre.fst W x y).app (op ⦋0⦌) a))
    (w : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.realizationWeakEquivalences (mappingPostcomposition W hW w x y a) := by
  obtain ⟨b, c, kₗ, kᵣ, hb, haₗ, hmₗ, haᵣ, hc, hmᵣ⟩ := inverseTriangles W hW x y a ha
  let : Fibration (mappingFibre.snd W w x) := mappingFibration W hW w x
  let : Fibration (mappingFibre.snd W w y) := mappingFibration W hW w y
  have Hᵣ : SSet.Homotopy
      (mappingPostcomposition W hW w x x (identityVertex W x))
      (mappingPostcomposition W hW w x y a ≫ mappingPostcomposition W hW w y x c) := by
    simpa only [haᵣ, hc, hmᵣ] using mappingPostcompositionTriangle W hW w x y x kᵣ
  have Hₗ : SSet.Homotopy
      (mappingPostcomposition W hW w y y (identityVertex W y))
      (mappingPostcomposition W hW w y x b ≫ mappingPostcomposition W hW w x y a) := by
    simpa only [hb, haₗ, hmₗ] using mappingPostcompositionTriangle W hW w y x y kₗ
  exact scalarWeakOfTwoComposites (mappingPostcomposition W hW w x y a)
    (mappingPostcomposition W hW w y x c) (mappingPostcomposition W hW w y x b)
    (joinOperatorHomotopy (mappingFibre.snd W w x)
      (reverseOperatorHomotopy (mappingFibre.snd W w x) Hᵣ)
      (mappingCompositionRightUnit W hW w x))
    (joinOperatorHomotopy (mappingFibre.snd W w y)
      (reverseOperatorHomotopy (mappingFibre.snd W w y) Hₗ)
      (mappingCompositionRightUnit W hW w y))

/-- The original precomposition map is realization weak, with its two inverse points kept
distinct. -/
theorem mappingPrecomposition_realizationWeakEquivalence
    (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W x y) _⦋0⦌)
    (ha : IsEquivalenceEdge W hW ((mappingFibre.fst W x y).app (op ⦋0⦌) a))
    (z : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.realizationWeakEquivalences (mappingPrecomposition W hW x y z a) := by
  obtain ⟨b, c, kₗ, kᵣ, hb, haₗ, hmₗ, haᵣ, hc, hmᵣ⟩ := inverseTriangles W hW x y a ha
  let : Fibration (mappingFibre.snd W y z) := mappingFibration W hW y z
  let : Fibration (mappingFibre.snd W x z) := mappingFibration W hW x z
  have Hₗ : SSet.Homotopy
      (mappingPrecomposition W hW y y z (identityVertex W y))
      (mappingPrecomposition W hW x y z a ≫ mappingPrecomposition W hW y x z b) := by
    simpa only [hb, haₗ, hmₗ] using mappingPrecompositionTriangle W hW y x y z kₗ
  have Hᵣ : SSet.Homotopy
      (mappingPrecomposition W hW x x z (identityVertex W x))
      (mappingPrecomposition W hW y x z c ≫ mappingPrecomposition W hW x y z a) := by
    simpa only [haᵣ, hc, hmᵣ] using mappingPrecompositionTriangle W hW x y x z kᵣ
  exact scalarWeakOfTwoComposites (mappingPrecomposition W hW x y z a)
    (mappingPrecomposition W hW y x z b) (mappingPrecomposition W hW y x z c)
    (joinOperatorHomotopy (mappingFibre.snd W y z)
      (reverseOperatorHomotopy (mappingFibre.snd W y z) Hₗ)
      (mappingCompositionLeftUnit W hW y z))
    (joinOperatorHomotopy (mappingFibre.snd W x z)
      (reverseOperatorHomotopy (mappingFibre.snd W x z) Hᵣ)
      (mappingCompositionLeftUnit W hW x z))

/-- Membership in the full Kan weak class retains the original postcomposition map and all π
maps. -/
theorem mappingPostcomposition_W
    (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W x y) _⦋0⦌)
    (ha : IsEquivalenceEdge W hW ((mappingFibre.fst W x y).app (op ⦋0⦌) a))
    (w : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.KanComplex.W (mappingPostcomposition W hW w x y a) := by
  let : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let : SSet.KanComplex (mappingFibre W w x) := ReedyModel.mappingFibre_kanComplex W w x hW.1
  let : SSet.KanComplex (mappingFibre W w y) := ReedyModel.mappingFibre_kanComplex W w y hW.1
  exact (SSet.KanComplex.W_iff_realizationWeakEquivalence _).mpr
    (mappingPostcomposition_realizationWeakEquivalence W hW x y a ha w)

/-- The same original precomposition map belongs to the full Kan weak class. -/
theorem mappingPrecomposition_W
    (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W x y) _⦋0⦌)
    (ha : IsEquivalenceEdge W hW ((mappingFibre.fst W x y).app (op ⦋0⦌) a))
    (z : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.KanComplex.W (mappingPrecomposition W hW x y z a) := by
  let : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let : SSet.KanComplex (mappingFibre W y z) := ReedyModel.mappingFibre_kanComplex W y z hW.1
  let : SSet.KanComplex (mappingFibre W x z) := ReedyModel.mappingFibre_kanComplex W x z hW.1
  exact (SSet.KanComplex.W_iff_realizationWeakEquivalence _).mpr
    (mappingPrecomposition_realizationWeakEquivalence W hW x y a ha z)

end SimplicialSpace
