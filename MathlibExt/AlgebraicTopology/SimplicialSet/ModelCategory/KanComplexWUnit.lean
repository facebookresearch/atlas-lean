/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationFibrationSequence
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RealizationUnitPiZero
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidPiOne

/-!
# The realization and singular adjunction unit on Kan complexes

Let X be a Kan complex and ηX:X→Sing(|X|) the unit of the geometric-realization and
singular-complex adjunction. For every vertex x and positive degree n+1, ηX induces a bijection
on based homotopy groups.

The unit also induces an equivalence of fundamental groupoids and bijective based homotopy maps
in all degrees, so it belongs to KanComplex.W. The statement holds in every universe u.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section
universe u

open CategoryTheory HomotopicalAlgebra Simplicial
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.KanComplex

private theorem bijective_of_bijective_connecting_square
    {A B C D : Type u} (sourceConnecting : A → B)
    (targetConnecting : C → D) (topMap : A → C)
    (bottomMap : B → D)
    (hSource : Function.Bijective sourceConnecting)
    (hTarget : Function.Bijective targetConnecting)
    (hBottom : Function.Bijective bottomMap)
    (hcomm : ∀ a, bottomMap (sourceConnecting a) =
      targetConnecting (topMap a)) :
    Function.Bijective topMap := by
  constructor
  · intro a b hab
    apply hSource.1
    apply hBottom.1
    rw [hcomm, hcomm, hab]
  · intro c
    obtain ⟨d, hd⟩ := hBottom.2 (targetConnecting c)
    obtain ⟨a, ha⟩ := hSource.2 d
    refine ⟨a, hTarget.1 ?_⟩
    rw [← hcomm, ha, hd]

private theorem bijective_piMap_unit_succ_of_fiber
    (n : ℕ) (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌)
    (hFiber : Function.Bijective
      (KanComplex.π.map
        (x := (SSet.loopFibrationSequence X x).fiberPoint)
        (sSetTopAdj.unit.app
          (SSet.loopFibrationSequence X x).fiber)
        rfl n)) :
    Function.Bijective
      (KanComplex.π.map (x := x)
        (sSetTopAdj.unit.app X) rfl (n + 1)) := by
  let S := SSet.loopFibrationSequence X x
  let T := S.realSingSequence
  let f := S.unitSequenceHom
  let e := S.realSingFiberIso
  have hSource : Function.Bijective (S.connectingMap n) := by
    apply S.connectingMap_bijective_of_subsingleton_total
    intro k
    simpa [S, SSet.loopFibrationSequence] using
      SSet.subsingleton_pi_basedPath X x k
  have hTarget : Function.Bijective (T.connectingMap n) := by
    simpa [S, T] using
      SSet.FibrationSequence.realSingLoop_connectingMap_bijective X x n
  have hePoint :
      e.hom.app _
          ((sSetTopAdj.unit.app S.fiber).app _ S.fiberPoint) =
        T.fiberPoint := by
    simpa only [NatTrans.comp_app, types_comp_apply] using
      S.unitSequenceHom_fiberPoint
  have heMap : Function.Bijective
      (KanComplex.π.map e.hom hePoint n) :=
    (KanComplex.π.equivOfIso e hePoint n).bijective
  have hBottomApply (q : KanComplex.π n S.fiber S.fiberPoint) :
      KanComplex.π.map f.fiberMap f.fiberMap_app_basePoint n q =
        KanComplex.π.map e.hom hePoint n
          (KanComplex.π.map
            (sSetTopAdj.unit.app S.fiber) rfl n q) := by
    have hcomp := KanComplex.π.map_comp_apply
      (sSetTopAdj.unit.app S.fiber) e.hom rfl hePoint
      S.unitSequenceHom_fiberPoint q
    simpa only [f, e, S.unitSequenceHom_fiberMap] using hcomp
  have hBottom : Function.Bijective
      (KanComplex.π.map f.fiberMap
        f.fiberMap_app_basePoint n) := by
    constructor
    · intro a b hab
      apply hFiber.1
      apply heMap.1
      rw [← hBottomApply, ← hBottomApply]
      exact hab
    · intro q
      obtain ⟨b, hb⟩ := heMap.2 q
      obtain ⟨a, ha⟩ := hFiber.2 b
      exact ⟨a, by rw [hBottomApply, ha, hb]⟩
  apply bijective_of_bijective_connecting_square
    (S.connectingMap n) (T.connectingMap n)
    (KanComplex.π.map (x := x)
      (sSetTopAdj.unit.app X) rfl (n + 1))
    (KanComplex.π.map f.fiberMap
      f.fiberMap_app_basePoint n)
    hSource hTarget hBottom
  intro q
  simpa [S, T, f, SSet.FibrationSequence.unitSequenceHom,
    SSet.FibrationSequence.realSingSequence,
    SSet.loopFibrationSequence] using
      SSet.FibrationSequence.connectingMap_naturality f q

/-- For a Kan complex X, a vertex x and n∈ℕ, the adjunction unit ηX:X→Sing(|X|) induces a bijection
π(n+1)(X,x)→π(n+1)(Sing(|X|),ηX(x)). -/
theorem bijective_piMap_sSetTopAdj_unit_app_succ
    (n : ℕ) (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) :
    Function.Bijective
      (KanComplex.π.map (x := x)
        (sSetTopAdj.unit.app X) rfl (n + 1)) := by
  induction n generalizing X with
  | zero =>
      let S := SSet.loopFibrationSequence X x
      let _ : KanComplex ((Functor.id SSet.{u}).obj S.fiber) := by
        change KanComplex S.fiber
        infer_instance
      let _ : KanComplex
          ((SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).obj S.fiber) :=
        TopCat.toSSet_obj_kanComplex _
      apply bijective_piMap_unit_succ_of_fiber 0 X x
      apply (bijective_mapπ₀_iff_bijective_mapπ_zero
        (sSetTopAdj.unit.app S.fiber) S.fiberPoint
        ((sSetTopAdj.unit.app S.fiber).app _ S.fiberPoint) rfl).2
      exact SSet.bijective_mapπ₀_sSetTopAdj_unit_app S.fiber
  | succ n ih =>
      apply bijective_piMap_unit_succ_of_fiber (n + 1) X x
      exact ih (SSet.loopFibrationSequence X x).fiber
        (SSet.loopFibrationSequence X x).fiberPoint

/-- For every Kan complex X, its adjunction unit X→Sing(|X|) is a Kan weak equivalence: both objects
are Kan, the fundamental-groupoid map is an equivalence, and every based homotopy map is
bijective. -/
theorem W.sSetTopAdj_unit_app
    (X : SSet.{u}) [KanComplex X] :
    KanComplex.W (sSetTopAdj.unit.app X) := by
  let _ : KanComplex ((Functor.id SSet.{u}).obj X) := by
    change KanComplex X
    infer_instance
  let _ : KanComplex
      ((SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).obj X) :=
    TopCat.toSSet_obj_kanComplex _
  rw [KanComplex.W_iff]
  exact ⟨SSet.bijective_mapπ₀_sSetTopAdj_unit_app X,
    fun n x => bijective_piMap_sSetTopAdj_unit_app_succ n X x⟩

end SSet.KanComplex
