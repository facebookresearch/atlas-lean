/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWHomotopy
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.PathSpace
import MathlibExt.AlgebraicTopology.SimplicialSet.MonoidalCompat
import MathlibExt.AlgebraicTopology.SimplicialSet.ProdStdSimplexCompat
import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying

/-!
# Based paths and loop spaces

For a pointed simplicial set `(X,x)`, this module defines the paths beginning
at `x`, their endpoint fibration, and its strict fiber of loops.  The based
path space contracts from the constant path to the identity by precomposition
with the monotone map `(s,t) ↦ min s t` on the simplicial interval.

The endpoint-pair fibration is reused from `PathSpace`; boundary-one and
internal-hom comparison machinery is not duplicated here.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory
  Simplicial SSet HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace SSet

/-- Paths in `X` whose initial vertex is `x`. -/
noncomputable def basedPath (X : SSet.{u}) (x : X _⦋0⦌) : SSet.{u} :=
  Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x

/-- The constant based path, used as the distinguished point. -/
noncomputable def basedPathPoint (X : SSet.{u}) (x : X _⦋0⦌) :
    basedPath X x _⦋0⦌ :=
  Subcomplex.fiber.basePoint ((constPath X).app _ x) (by
    have h := ConcreteCategory.congr_hom
      (congr_app (eval₀_constPath X) (op ⦋0⦌)) x
    change (eval₀.app (op ⦋0⦌)) ((constPath X).app (op ⦋0⦌) x) = x
    exact h)

/-- Evaluate a based path at its final vertex. -/
noncomputable def basedPathProj (X : SSet.{u}) (x : X _⦋0⦌) :
    basedPath X x ⟶ X :=
  (Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι ≫ eval₁

/-- The strict loop space is the fiber of final-point evaluation over `x`. -/
noncomputable def loopSpace (X : SSet.{u}) (x : X _⦋0⦌) : SSet.{u} :=
  Subcomplex.fiber (basedPathProj X x) x

@[simp]
lemma basedPathProj_basedPathPoint (X : SSet.{u}) (x : X _⦋0⦌) :
    (basedPathProj X x).app _ (basedPathPoint X x) = x := by
  have h := ConcreteCategory.congr_hom
    (congr_app (eval₁_constPath X) (op ⦋0⦌)) x
  change (eval₁.app (op ⦋0⦌)) ((constPath X).app (op ⦋0⦌) x) = x
  exact h

private theorem basedPath_isPullback (X : SSet.{u}) (x : X _⦋0⦌) :
    IsPullback (Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι
      (basedPathProj X x) evalPair (lift (SSet.const x) (𝟙 X)) := by
  dsimp [basedPathProj, basedPath]
  refine { w := ?_, isLimit' := ?_ }
  · apply CartesianMonoidalCategory.hom_ext
    · simp [Category.assoc]
    · simp [Category.assoc]
  · have hRange :
        ∀ (s : PullbackCone evalPair (lift (SSet.const x) (𝟙 X))),
          Subcomplex.range s.fst ≤
            Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x := by
      intro s
      rw [Subcomplex.range_le_fiber_iff]
      calc
        s.fst ≫ eval₀ = s.fst ≫ evalPair ≫ fst X X := by
          simp
        _ = s.snd ≫ lift (SSet.const x) (𝟙 X) ≫ fst X X := by
          simpa only [← Category.assoc] using s.condition =≫ fst X X
        _ = SSet.const x := by simp
    refine ⟨PullbackCone.IsLimit.mk (by
        apply CartesianMonoidalCategory.hom_ext
        · simp [Category.assoc]
        · simp [Category.assoc])
      (fun s ↦ Subcomplex.lift s.fst (hRange s))
      (fun s ↦ Subcomplex.lift_ι s.fst (hRange s))
      (fun s ↦ ?_)
      (fun s m h₁ h₂ ↦ ?_)⟩
    · rw [← Category.assoc, Subcomplex.lift_ι]
      have h := s.condition =≫ snd X X
      simpa [Category.assoc] using h
    · apply (cancel_mono
        (Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι).mp
      rw [h₁, Subcomplex.lift_ι]

instance basedPathProj_fibration (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) : Fibration (basedPathProj X x) := by
  rw [modelCategoryQuillen.fibration_iff]
  exact MorphismProperty.of_isPullback (basedPath_isPullback X x) (by
    rw [← modelCategoryQuillen.fibration_iff]
    infer_instance)

instance basedPath_kanComplex (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) : KanComplex (basedPath X x) := by
  dsimp [basedPath]
  infer_instance

instance loopSpace_kanComplex (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) : KanComplex (loopSpace X x) := by
  dsimp [loopSpace]
  infer_instance

/-- The based-path fibration sequence, whose strict fiber is the loop space. -/
noncomputable def loopFibrationSequence (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) : FibrationSequence.{u} where
  E := basedPath X x
  B := X
  p := basedPathProj X x
  fibration_p := inferInstance
  fibrant_B := inferInstance
  e := basedPathPoint X x
  b := x
  hb := basedPathProj_basedPathPoint X x

/-! ## The minimum map on the simplicial interval -/

private def intervalMinOrderHom : Fin 2 × Fin 2 →o Fin 2 where
  toFun p := min p.1 p.2
  monotone' _ _ h := min_le_min h.1 h.2

private def intervalMinMap : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[1] where
  app _ := ↾fun z ↦ stdSimplex.objEquiv.symm
    (SimplexCategory.Hom.mk (intervalMinOrderHom.comp (prodStdSimplex.objEquiv z)))
  naturality _ _ f := by
    ext z
    apply stdSimplex.objEquiv.injective
    ext i
    rfl

private lemma intervalMinMap_objEquiv_toFun_apply (a : SimplexCategoryᵒᵖ)
    (z : ((Δ[1] : SSet.{u}) ⊗ Δ[1]).obj a)
    (i : Fin (a.unop.len + 1)) :
    (stdSimplex.objEquiv
        ((ConcreteCategory.hom (NatTrans.app intervalMinMap a)).toFun z)).toOrderHom i =
      min ((prodStdSimplex.objEquiv z i).1) ((prodStdSimplex.objEquiv z i).2) :=
  rfl

private lemma constZero_toFun_apply_apply (A : SSet.{u}) (d : ℕ)
    (z : A _⦋d⦌) (i : Fin (d + 1)) :
    (((ConcreteCategory.hom
      (NatTrans.app
        (SSet.const (Y := (Δ[1] : SSet.{u}))
          (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2))) _)).toFun z) :
            (Δ[1] : SSet.{u}) _⦋d⦌) i = 0 :=
  rfl

private lemma constOne_toFun_apply_apply (A : SSet.{u}) (d : ℕ)
    (z : A _⦋d⦌) (i : Fin (d + 1)) :
    (((ConcreteCategory.hom
      (NatTrans.app
        (SSet.const (Y := (Δ[1] : SSet.{u}))
          (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2))) _)).toFun z) :
            (Δ[1] : SSet.{u}) _⦋d⦌) i = 1 :=
  rfl

private lemma intervalMinMap_timeZero :
    (Δ[1] : SSet.{u}) ◁ (stdSimplex.δ (1 : Fin 2) : Δ[0] ⟶ Δ[1]) ≫
        intervalMinMap =
      SSet.const (stdSimplex.obj₀Equiv.{u}.symm 0) := by
  ext ⟨⟨n⟩⟩ z i
  let q : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) _⦋n⦌ :=
    ⟨z.1, NatTrans.app (stdSimplex.δ (1 : Fin 2)) (op ⦋n⦌) z.2⟩
  rw [SSet.comp_app]
  have hcomp :
        (ConcreteCategory.hom
          ((NatTrans.app ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ (1 : Fin 2)) (op ⦋n⦌)) ≫
            NatTrans.app intervalMinMap (op ⦋n⦌))).toFun z =
        (ConcreteCategory.hom (NatTrans.app intervalMinMap (op ⦋n⦌))).toFun q := by
    calc
      _ = (ConcreteCategory.hom (NatTrans.app intervalMinMap (op ⦋n⦌))).toFun
          ((ConcreteCategory.hom
            (NatTrans.app ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ (1 : Fin 2))
              (op ⦋n⦌))).toFun z) :=
        CategoryTheory.types_comp_apply _ _ z
      _ = _ := by rfl
  rw [hcomp]
  have hfin :
      (((ConcreteCategory.hom (NatTrans.app intervalMinMap (op ⦋n⦌))).toFun q :
          (Δ[1] : SSet.{u}) _⦋n⦌) i) =
        (((ConcreteCategory.hom
          (NatTrans.app (SSet.const (stdSimplex.obj₀Equiv.{u}.symm 0)) (op ⦋n⦌))).toFun z :
            (Δ[1] : SSet.{u}) _⦋n⦌) i) := by
    calc
      _ = min ((prodStdSimplex.objEquiv q i).1)
          ((prodStdSimplex.objEquiv q i).2) := by
        simpa only [stdSimplex.objEquiv_toOrderHom_apply] using
          intervalMinMap_objEquiv_toFun_apply.{u} (op ⦋n⦌) q i
      _ = min (q.1 i) (q.2 i) := rfl
      _ = 0 := by
        have hb : q.2 i = 0 := by
          dsimp [q]
          rw [stdSimplex.δ_one_eq_const]
          exact constZero_toFun_apply_apply _ n z.2 i
        rw [hb]
        exact min_eq_right (Fin.zero_le _)
      _ = _ := (constZero_toFun_apply_apply _ n z i).symm
  exact congrArg Fin.val hfin

private lemma intervalMinMap_timeOne :
    (Δ[1] : SSet.{u}) ◁ (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1]) ≫
        intervalMinMap =
      (stdSimplex.rightUnitor (Δ[1] : SSet.{u})).hom := by
  ext ⟨⟨n⟩⟩ z i
  let q : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) _⦋n⦌ :=
    ⟨z.1, NatTrans.app (stdSimplex.δ (0 : Fin 2)) (op ⦋n⦌) z.2⟩
  rw [SSet.comp_app]
  have hcomp :
        (ConcreteCategory.hom
          ((NatTrans.app ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ (0 : Fin 2)) (op ⦋n⦌)) ≫
            NatTrans.app intervalMinMap (op ⦋n⦌))).toFun z =
        (ConcreteCategory.hom (NatTrans.app intervalMinMap (op ⦋n⦌))).toFun q := by
    calc
      _ = (ConcreteCategory.hom (NatTrans.app intervalMinMap (op ⦋n⦌))).toFun
          ((ConcreteCategory.hom
            (NatTrans.app ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ (0 : Fin 2))
              (op ⦋n⦌))).toFun z) :=
        CategoryTheory.types_comp_apply _ _ z
      _ = _ := by rfl
  rw [hcomp]
  have hfin :
      (((ConcreteCategory.hom (NatTrans.app intervalMinMap (op ⦋n⦌))).toFun q :
          (Δ[1] : SSet.{u}) _⦋n⦌) i) =
        (((ConcreteCategory.hom
          (NatTrans.app (stdSimplex.rightUnitor (Δ[1] : SSet.{u})).hom
            (op ⦋n⦌))).toFun z : (Δ[1] : SSet.{u}) _⦋n⦌) i) := by
    calc
      _ = min ((prodStdSimplex.objEquiv q i).1)
          ((prodStdSimplex.objEquiv q i).2) := by
        simpa only [stdSimplex.objEquiv_toOrderHom_apply] using
          intervalMinMap_objEquiv_toFun_apply.{u} (op ⦋n⦌) q i
      _ = min (q.1 i) (q.2 i) := rfl
      _ = min (z.1 i) 1 := by
        have hb : q.2 i = 1 := by
          dsimp [q]
          rw [stdSimplex.δ_zero_eq_const]
          exact constOne_toFun_apply_apply _ n z.2 i
        rw [hb]
      _ = z.1 i := min_eq_left (Fin.le_last _)
      _ = _ := rfl
  exact congrArg Fin.val hfin

private lemma intervalMinMap_firstZero (Z : SSet.{u}) :
    (SSet.const (X := Z) (stdSimplex.obj₀Equiv.{u}.symm 0) ▷ (Δ[1] : SSet.{u})) ≫
        intervalMinMap =
      SSet.const (stdSimplex.obj₀Equiv.{u}.symm 0) := by
  ext ⟨⟨n⟩⟩ z i
  let q : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) _⦋n⦌ :=
    ⟨NatTrans.app (SSet.const (stdSimplex.obj₀Equiv.{u}.symm 0)) (op ⦋n⦌) z.1, z.2⟩
  rw [SSet.comp_app]
  have hcomp :
        (ConcreteCategory.hom
          (NatTrans.app
              (SSet.const (X := Z) (stdSimplex.obj₀Equiv.{u}.symm 0) ▷
                (Δ[1] : SSet.{u})) (op ⦋n⦌) ≫
              NatTrans.app intervalMinMap (op ⦋n⦌))).toFun z =
        (ConcreteCategory.hom (NatTrans.app intervalMinMap (op ⦋n⦌))).toFun q := by
    calc
      _ = (ConcreteCategory.hom (NatTrans.app intervalMinMap (op ⦋n⦌))).toFun
          ((ConcreteCategory.hom
            (NatTrans.app
              (SSet.const (X := Z) (stdSimplex.obj₀Equiv.{u}.symm 0) ▷
                (Δ[1] : SSet.{u})) (op ⦋n⦌))).toFun z) :=
        CategoryTheory.types_comp_apply _ _ z
      _ = _ := by rfl
  rw [hcomp]
  have hfin :
      (((ConcreteCategory.hom (NatTrans.app intervalMinMap (op ⦋n⦌))).toFun q :
          (Δ[1] : SSet.{u}) _⦋n⦌) i) =
        (((ConcreteCategory.hom
          (NatTrans.app (SSet.const (stdSimplex.obj₀Equiv.{u}.symm 0)) (op ⦋n⦌))).toFun z :
            (Δ[1] : SSet.{u}) _⦋n⦌) i) := by
    calc
      _ = min ((prodStdSimplex.objEquiv q i).1)
          ((prodStdSimplex.objEquiv q i).2) := by
        simpa only [stdSimplex.objEquiv_toOrderHom_apply] using
          intervalMinMap_objEquiv_toFun_apply.{u} (op ⦋n⦌) q i
      _ = min (q.1 i) (q.2 i) := rfl
      _ = min 0 (z.2 i) := by
        have ha : q.1 i = 0 := by
          dsimp [q]
          exact constZero_toFun_apply_apply _ n z.1 i
        rw [ha]
      _ = 0 := min_eq_left (Fin.zero_le _)
      _ = _ := (constZero_toFun_apply_apply _ n z i).symm
  exact congrArg Fin.val hfin

/-! ## Contraction of based paths -/

private noncomputable def pathContractionCurried (X : SSet.{u}) :
    pathSpace X ⟶ (ihom (Δ[1] : SSet.{u})).obj (pathSpace X) :=
  (MonoidalClosed.pre intervalMinMap).app X ≫
    MonoidalClosed.ihomCurry (Δ[1] : SSet.{u}) Δ[1] X

private noncomputable def pathContractionMap (X : SSet.{u}) :
    pathSpace X ⊗ Δ[1] ⟶ pathSpace X :=
  (β_ (pathSpace X) (Δ[1] : SSet.{u})).hom ≫
    MonoidalClosed.uncurry (pathContractionCurried X)

private lemma pathContractionMap_eq (X : SSet.{u}) :
    pathContractionMap X =
      (β_ (pathSpace X) (Δ[1] : SSet.{u})).hom ≫
        MonoidalClosed.curry ((α_ (Δ[1] : SSet.{u}) Δ[1] (pathSpace X)).inv ≫
          MonoidalClosed.uncurry ((MonoidalClosed.pre intervalMinMap).app X)) := by
  dsimp [pathContractionMap, pathContractionCurried]
  rw [MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_ihomCurry, ← MonoidalClosed.curry_natural_left]
  congr 1

private lemma pathContractionMap_timeZero (X : SSet.{u}) :
    ι₀ ≫ pathContractionMap X = eval₀ ≫ constPath X := by
  rw [pathContractionMap_eq, MonoidalClosed.uncurry_pre,
    ← cancel_epi (stdSimplex.rightUnitor _).hom,
    stdSimplex.rightUnitor_hom_ι₀_assoc,
    BraidedCategory.braiding_naturality_right_assoc,
    ← MonoidalClosed.curry_natural_left,
    associator_inv_naturality_middle_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc,
    intervalMinMap_timeZero,
    ← MonoidalClosed.curry_natural_left,
    eval₀_constPath_eq_pre_constZero]
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_pre]
  rfl

private lemma pathContractionMap_timeOne (X : SSet.{u}) :
    ι₁ ≫ pathContractionMap X = 𝟙 (pathSpace X) := by
  rw [pathContractionMap_eq, MonoidalClosed.uncurry_pre,
    ← cancel_epi (stdSimplex.rightUnitor _).hom,
    stdSimplex.rightUnitor_hom_ι₁_assoc,
    BraidedCategory.braiding_naturality_right_assoc,
    Category.comp_id,
    ← MonoidalClosed.curry_natural_left,
    associator_inv_naturality_middle_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc,
    intervalMinMap_timeOne]
  apply MonoidalClosed.uncurry_injective
  rfl

private lemma pathContractionMap_preZero (X : SSet.{u}) :
    pathContractionMap X ≫
        (MonoidalClosed.pre
          (SSet.const (X := (Δ[1] : SSet.{u}))
            (stdSimplex.obj₀Equiv.{u}.symm 0))).app X =
      CartesianMonoidalCategory.fst (pathSpace X) (Δ[1] : SSet.{u}) ≫
        (MonoidalClosed.pre
          (SSet.const (X := (Δ[1] : SSet.{u}))
            (stdSimplex.obj₀Equiv.{u}.symm 0))).app X := by
  rw [pathContractionMap_eq, Category.assoc,
    MonoidalClosed.curry_pre_app]
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry,
    MonoidalClosed.uncurry_pre_app]
  rfl

private lemma basedPathCylinder_evalZero (X : SSet.{u}) (x : X _⦋0⦌) :
    ((Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι ▷
        (Δ[1] : SSet.{u})) ≫ pathContractionMap X ≫ eval₀ =
      SSet.const x := by
  let _ : IsSplitMono (constPath X) :=
    IsSplitMono.mk'
      { retraction := eval₀
        id := eval₀_constPath X }
  apply (cancel_mono (constPath X)).mp
  calc
    ((((Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι ▷
        (Δ[1] : SSet.{u})) ≫ pathContractionMap X ≫ eval₀) ≫ constPath X) =
        ((Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι ▷
          (Δ[1] : SSet.{u})) ≫
            (pathContractionMap X ≫ (eval₀ ≫ constPath X)) := by
              simp only [Category.assoc]
    _ = ((Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι ▷
          (Δ[1] : SSet.{u})) ≫
            (pathContractionMap X ≫
              (MonoidalClosed.pre
                (SSet.const (X := (Δ[1] : SSet.{u}))
                  (stdSimplex.obj₀Equiv.{u}.symm 0))).app X) := by
                    rw [eval₀_constPath_eq_pre_constZero]
    _ = ((Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι ▷
          (Δ[1] : SSet.{u})) ≫
            (CartesianMonoidalCategory.fst (pathSpace X) (Δ[1] : SSet.{u}) ≫
              (MonoidalClosed.pre
                (SSet.const (X := (Δ[1] : SSet.{u}))
                  (stdSimplex.obj₀Equiv.{u}.symm 0))).app X) := by
                    rw [pathContractionMap_preZero]
    _ = CartesianMonoidalCategory.fst
          ((Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x) : SSet.{u})
            (Δ[1] : SSet.{u}) ≫
            (Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι ≫
              (MonoidalClosed.pre
                (SSet.const (X := (Δ[1] : SSet.{u}))
                  (stdSimplex.obj₀Equiv.{u}.symm 0))).app X := by
                    rw [← Category.assoc,
                      CartesianMonoidalCategory.whiskerRight_fst,
                      Category.assoc]
    _ = CartesianMonoidalCategory.fst
          ((Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x) : SSet.{u})
            (Δ[1] : SSet.{u}) ≫
            (Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι ≫
              eval₀ ≫ constPath X := by
                rw [← eval₀_constPath_eq_pre_constZero]
    _ = SSet.const x ≫ constPath X := by
      simp

private noncomputable def basedPathContractionMap
    (X : SSet.{u}) (x : X _⦋0⦌) :
    basedPath X x ⊗ Δ[1] ⟶ basedPath X x :=
  Subcomplex.lift
    (((Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι ▷
      (Δ[1] : SSet.{u})) ≫ pathContractionMap X)
    (by
      rw [Subcomplex.range_le_fiber_iff]
      exact basedPathCylinder_evalZero X x)

private lemma const_basedPathPoint_ι (X : SSet.{u}) (x : X _⦋0⦌) :
    SSet.const (X := basedPath X x) (basedPathPoint X x) ≫
        (Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι =
      SSet.const (X := basedPath X x) x ≫ constPath X := by
  dsimp [basedPath, basedPathPoint]
  rw [const_comp, const_comp]
  rfl

private lemma basedPathContractionMap_timeZero
    (X : SSet.{u}) (x : X _⦋0⦌) :
    ι₀ ≫ basedPathContractionMap X x =
      SSet.const (basedPathPoint X x) := by
  dsimp [basedPath, basedPathPoint, basedPathContractionMap]
  apply (cancel_mono
    (Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι).mp
  simp only [Category.assoc, Subcomplex.lift_ι]
  rw [← Category.assoc, ι₀_comp, Category.assoc, pathContractionMap_timeZero,
    ← Category.assoc, Subcomplex.fiber_ι_comp]
  exact (const_basedPathPoint_ι X x).symm

private lemma basedPathContractionMap_timeOne
    (X : SSet.{u}) (x : X _⦋0⦌) :
    ι₁ ≫ basedPathContractionMap X x =
      𝟙 (basedPath X x) := by
  dsimp [basedPath, basedPathContractionMap]
  apply (cancel_mono
    (Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι).mp
  simp only [Category.assoc, Subcomplex.lift_ι]
  rw [← Category.assoc, ι₁_comp, Category.assoc, pathContractionMap_timeOne]
  simp

/-- The based path space contracts from its constant path to the identity. -/
noncomputable opaque basedPathContraction (X : SSet.{u}) (x : X _⦋0⦌) :
    SSet.Homotopy
      (SSet.const (basedPathPoint X x))
      (𝟙 (basedPath X x)) := by
  change SSet.RelativeMorphism.Homotopy
    (SSet.RelativeMorphism.botEquiv.symm _)
    (SSet.RelativeMorphism.botEquiv.symm _)
  refine
    { h := basedPathContractionMap X x
      h₀ := basedPathContractionMap_timeZero X x
      h₁ := basedPathContractionMap_timeOne X x
      rel := ?_ }
  ext m ⟨⟨y, hy⟩, t⟩
  cases hy

private theorem basedPath_toPoint_W (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) :
    KanComplex.W
      (stdSimplex.isTerminalObj₀.from (basedPath X x)) := by
  let q : basedPath X x ⟶ (Δ[0] : SSet.{u}) :=
    stdSimplex.isTerminalObj₀.from (basedPath X x)
  let s : (Δ[0] : SSet.{u}) ⟶ basedPath X x :=
    SSet.const (basedPathPoint X x)
  let _ : KanComplex (Δ[0] : SSet.{u}) := by
    rw [KanComplex.iff]
    intro n i f hf
    exact ⟨stdSimplex.isTerminalObj₀.from _,
      fun j hj ↦ stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  apply KanComplex.W.of_homotopy q s
  · have hqs : q ≫ s = SSet.const (basedPathPoint X x) := by
      simp [q, s]
    rw [hqs]
    exact basedPathContraction X x
  · have hsq : s ≫ q = 𝟙 (Δ[0] : SSet.{u}) :=
      stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [hsq]
    change SSet.RelativeMorphism.Homotopy
      (SSet.RelativeMorphism.botEquiv.symm _)
      (SSet.RelativeMorphism.botEquiv.symm _)
    exact SSet.RelativeMorphism.Homotopy.refl _

private theorem subsingleton_pi_stdSimplexZero
    [KanComplex (Δ[0] : SSet.{u})]
    (z : (Δ[0] : SSet.{u}) _⦋0⦌) (n : ℕ) :
    Subsingleton (KanComplex.π n (Δ[0] : SSet.{u}) z) := by
  constructor
  intro a b
  induction a using KanComplex.π.rec with
  | mk p =>
    induction b using KanComplex.π.rec with
    | mk q =>
      rw [KanComplex.π.mk_eq_mk_iff]
      have hpq : p = q := by
        apply SSet.RelativeMorphism.ext
        exact stdSimplex.isTerminalObj₀.hom_ext _ _
      subst q
      exact ⟨SSet.PtSimplex.RelStruct₀.refl p⟩

/-- Every homotopy group of the based path space is subsingleton. -/
theorem subsingleton_pi_basedPath (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) (n : ℕ) :
    Subsingleton
      (KanComplex.π n (basedPath X x) (basedPathPoint X x)) := by
  let q : basedPath X x ⟶ (Δ[0] : SSet.{u}) :=
    stdSimplex.isTerminalObj₀.from (basedPath X x)
  have hW : KanComplex.W q := by
    simpa [q] using basedPath_toPoint_W X x
  let _ : KanComplex (Δ[0] : SSet.{u}) := hW.kanComplex_target
  have hInjective :=
    (hW.bijective_piMap n (basedPathPoint X x)).1
  constructor
  intro a b
  apply hInjective
  exact (subsingleton_pi_stdSimplexZero
    (q.app (op ⦋0⦌) (basedPathPoint X x)) n).elim _ _

end SSet
