/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.TopCat.HomotopyFiberHomotopySquare

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits Topology HomotopicalAlgebra
open scoped unitInterval

namespace MathlibExtTest.TopCat.HomotopyFiberHomotopySquare

universe u

section Surface

#check TopCat.homotopyFiberMapOfHomotopy.{u}
#check TopCat.homotopyFiberMapOfHomotopy.{1}
#check TopCat.homotopyFiberMapOfHomotopy.{0}
#check TopCat.homotopyFiberMapOfHomotopy_toTotal.{u}
#check TopCat.homotopyFiberMapOfHomotopy_toTotal.{1}
#check TopCat.homotopyFiberMapOfHomotopy_toTotal.{0}
#check TopCat.homotopyFiberMapOfHomotopy_path.{u}
#check TopCat.homotopyFiberMapOfHomotopy_path.{1}
#check TopCat.homotopyFiberMapOfHomotopy_path.{0}
#check TopCat.homotopyFiberMapOfHomotopy_mem_weakHomotopyEquivalences.{u}
#check TopCat.homotopyFiberMapOfHomotopy_mem_weakHomotopyEquivalences.{1}
#check TopCat.homotopyFiberMapOfHomotopy_mem_weakHomotopyEquivalences.{0}
#check TopCat.homotopyFiberIdentitySquareHomotopy.{u}
#check TopCat.homotopyFiberIdentitySquareHomotopy.{1}
#check TopCat.homotopyFiberIdentitySquareHomotopy.{0}
#check TopCat.homotopyFiberStrictSquareHomotopy.{u}
#check TopCat.homotopyFiberStrictSquareHomotopy.{1}
#check TopCat.homotopyFiberStrictSquareHomotopy.{0}
#check TopCat.homotopyFiberCompositeSquareHomotopy.{u}
#check TopCat.homotopyFiberCompositeSquareHomotopy.{1}
#check TopCat.homotopyFiberCompositeSquareHomotopy.{0}
#check TopCat.homotopyFiberMapOfHomotopyIdHomotopy.{u}
#check TopCat.homotopyFiberMapOfHomotopyIdHomotopy.{1}
#check TopCat.homotopyFiberMapOfHomotopyIdHomotopy.{0}
#check TopCat.homotopyFiberMapOfHomotopyStrictHomotopy.{u}
#check TopCat.homotopyFiberMapOfHomotopyStrictHomotopy.{1}
#check TopCat.homotopyFiberMapOfHomotopyStrictHomotopy.{0}
#check TopCat.homotopyFiberMapOfHomotopyCompHomotopy.{u}
#check TopCat.homotopyFiberMapOfHomotopyCompHomotopy.{1}
#check TopCat.homotopyFiberMapOfHomotopyCompHomotopy.{0}

end Surface

section PublicLaws

variable {X Y B : TopCat.{u}}
variable (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
variable (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom)

example :
    TopCat.homotopyFiberMapOfHomotopy s p q b H ≫
        TopCat.homotopyFiberToTotal q b =
      TopCat.homotopyFiberToTotal p b ≫ s :=
  TopCat.homotopyFiberMapOfHomotopy_toTotal s p q b H

example (z : TopCat.homotopyFiber p b) (t : TopCat.I.{u}) :
    TopCat.homotopyFiberPath q b
        (TopCat.homotopyFiberMapOfHomotopy s p q b H z) t =
      if h : ((TopCat.I.homeomorph t : unitInterval) : ℝ) ≤ 1 / 2 then
        H (⟨2 * TopCat.I.homeomorph t,
          (unitInterval.mul_pos_mem_iff zero_lt_two).2
            ⟨(TopCat.I.homeomorph t).2.1, h⟩⟩,
          TopCat.homotopyFiberToTotal p b z)
      else
        TopCat.homotopyFiberPath p b z
          (TopCat.I.homeomorph.symm
            ⟨2 * TopCat.I.homeomorph t - 1,
              unitInterval.two_mul_sub_one_mem_iff.2
                ⟨(not_le.1 h).le, (TopCat.I.homeomorph t).2.2⟩⟩) :=
  TopCat.homotopyFiberMapOfHomotopy_path s p q b H z t

end PublicLaws

section PublicCoherenceLaws

variable {X Y Z B : TopCat.{u}}

example (p : X ⟶ B) (b : B) :
    ContinuousMap.Homotopy
      (TopCat.homotopyFiberMapOfHomotopy (𝟙 X) p p b
        (TopCat.homotopyFiberIdentitySquareHomotopy p)).hom
      ((𝟙 (TopCat.homotopyFiber p b) :
        TopCat.homotopyFiber p b ⟶ TopCat.homotopyFiber p b).hom) :=
  TopCat.homotopyFiberMapOfHomotopyIdHomotopy p b

example (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (h : s ≫ q = p) :
    ContinuousMap.Homotopy
      (TopCat.homotopyFiberMapOfHomotopy s p q b
        (TopCat.homotopyFiberStrictSquareHomotopy s p q h)).hom
      (TopCat.homotopyPullbackMap s (𝟙 (TopCat.of PUnit)) (𝟙 B)
        (by simp [h]) (by simp)).hom :=
  TopCat.homotopyFiberMapOfHomotopyStrictHomotopy s p q b h

example (s : X ⟶ Y) (t : Y ⟶ Z) (p : X ⟶ B)
    (q : Y ⟶ B) (r : Z ⟶ B) (b : B)
    (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom)
    (K : ContinuousMap.Homotopy (t ≫ r).hom q.hom) :
    ContinuousMap.Homotopy
      (TopCat.homotopyFiberMapOfHomotopy s p q b H ≫
        TopCat.homotopyFiberMapOfHomotopy t q r b K).hom
      (TopCat.homotopyFiberMapOfHomotopy (s ≫ t) p r b
        (TopCat.homotopyFiberCompositeSquareHomotopy
          s t p q r H K)).hom :=
  TopCat.homotopyFiberMapOfHomotopyCompHomotopy
    s t p q r b H K

end PublicCoherenceLaws

section NonidentityWeakMap

private def pointToInterval :
    C(PUnit.{u + 1}, TopCat.I.{u}) where
  toFun _ := 0
  continuous_toFun := continuous_const

private def intervalToPoint :
    C(TopCat.I.{u}, PUnit.{u + 1}) where
  toFun _ := PUnit.unit
  continuous_toFun := continuous_const

private def intervalZeroToIdHomotopy :
    ContinuousMap.Homotopy
      (pointToInterval.{u}.comp intervalToPoint.{u})
      (ContinuousMap.id TopCat.I.{u}) where
  toFun z := TopCat.I.homeomorph.symm
    (z.1 * TopCat.I.homeomorph z.2)
  continuous_toFun := by fun_prop
  map_zero_left x := by
    apply TopCat.I.homeomorph.injective
    simp [pointToInterval, intervalToPoint]
  map_one_left x := by
    apply TopCat.I.homeomorph.injective
    simp

private noncomputable def pointIntervalHomotopyEquiv :
    ContinuousMap.HomotopyEquiv PUnit.{u + 1} TopCat.I.{u} where
  toFun := pointToInterval
  invFun := intervalToPoint
  left_inv := by
    have h : intervalToPoint.{u}.comp pointToInterval.{u} =
        ContinuousMap.id PUnit := by
      ext x
    rw [h]
  right_inv := ⟨intervalZeroToIdHomotopy⟩

private def nonidentityWeakMap :
    TopCat.of PUnit.{u + 1} ⟶ TopCat.of TopCat.I.{u} :=
  TopCat.ofHom pointToInterval

private theorem nonidentityWeakMap_mem :
    TopCat.weakHomotopyEquivalences nonidentityWeakMap.{u} :=
  TopCat.homotopyEquiv_toFun_mem pointIntervalHomotopyEquiv

private def pointMap :
    TopCat.of PUnit.{u + 1} ⟶ TopCat.of PUnit.{u + 1} :=
  𝟙 _

private def intervalMap :
    TopCat.of TopCat.I.{u} ⟶ TopCat.of PUnit.{u + 1} :=
  TopCat.const PUnit.unit

private theorem nonidentitySquare :
    nonidentityWeakMap.{u} ≫ intervalMap.{u} = pointMap.{u} := by
  apply TopCat.isTerminalPUnit.hom_ext

private def nonidentityHomotopy :
    ContinuousMap.Homotopy
      (nonidentityWeakMap.{u} ≫ intervalMap.{u}).hom pointMap.hom :=
  (ContinuousMap.Homotopy.refl pointMap.hom).cast
    (by rw [nonidentitySquare]) rfl

example : TopCat.weakHomotopyEquivalences
    (TopCat.homotopyFiberMapOfHomotopy
      nonidentityWeakMap.{u} pointMap intervalMap PUnit.unit
        nonidentityHomotopy) :=
  TopCat.homotopyFiberMapOfHomotopy_mem_weakHomotopyEquivalences
    nonidentityWeakMap pointMap intervalMap PUnit.unit
      nonidentityHomotopy nonidentityWeakMap_mem

end NonidentityWeakMap

/-! Independently reconstruct the coherence targets as a regression check in
addition to consuming the public witnesses above. -/

section IndependentCoherenceRegression

private def identitySquareHomotopy {X B : TopCat.{u}} (p : X ⟶ B) :
    ContinuousMap.Homotopy ((𝟙 X) ≫ p).hom p.hom :=
  (ContinuousMap.Homotopy.refl p.hom).cast (by simp) rfl

private def strictSquareHomotopy
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (h : s ≫ q = p) :
    ContinuousMap.Homotopy (s ≫ q).hom p.hom :=
  (ContinuousMap.Homotopy.refl p.hom).cast (by rw [h]) rfl

private def precomposeSquareHomotopy
    {X Y Z B : TopCat.{u}} (s : X ⟶ Y) (t : Y ⟶ Z)
    (q : Y ⟶ B) (r : Z ⟶ B)
    (K : ContinuousMap.Homotopy (t ≫ r).hom q.hom) :
    ContinuousMap.Homotopy ((s ≫ t) ≫ r).hom (s ≫ q).hom :=
  (K.comp (ContinuousMap.Homotopy.refl s.hom)).cast rfl rfl

private def compositeSquareHomotopy
    {X Y Z B : TopCat.{u}}
    (s : X ⟶ Y) (t : Y ⟶ Z) (p : X ⟶ B)
    (q : Y ⟶ B) (r : Z ⟶ B)
    (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom)
    (K : ContinuousMap.Homotopy (t ≫ r).hom q.hom) :
    ContinuousMap.Homotopy ((s ≫ t) ≫ r).hom p.hom :=
  (precomposeSquareHomotopy s t q r K).trans H

private def fiberRootPath
    {X B : TopCat.{u}} (f : X ⟶ B) (b : B)
    (z : TopCat.homotopyFiber f b) :
    Path (f (TopCat.homotopyFiberToTotal f b z)) b where
  toFun t := TopCat.homotopyFiberPath f b z (TopCat.I.homeomorph.symm t)
  continuous_toFun :=
    (TopCat.homotopyFiberPath f b z).continuous.comp
      TopCat.I.homeomorph.symm.continuous
  source' := by
    have h := ConcreteCategory.congr_hom
      (TopCat.homotopyPullbackPath_evalZero f
        (TopCat.const (X := TopCat.of PUnit) b)) z
    exact h
  target' := by
    have hOne : TopCat.I.homeomorph.symm (1 : unitInterval) =
        (1 : TopCat.I.{u}) := by
      apply TopCat.I.homeomorph.injective
      simp
    have h := ConcreteCategory.congr_hom
      (TopCat.homotopyPullbackPath_evalOne f
        (TopCat.const (X := TopCat.of PUnit) b)) z
    change TopCat.homotopyFiberPath f b z
      (TopCat.I.homeomorph.symm 1) = b
    rw [hOne]
    exact h

private theorem fiberRootPath_continuous_family
    {X B : TopCat.{u}} (f : X ⟶ B) (b : B) :
    Continuous (fun z : TopCat.homotopyFiber f b × unitInterval =>
      fiberRootPath f b z.1 z.2) := by
  exact continuous_eval.comp
    (((TopCat.homotopyFiberPath f b).hom.continuous.comp continuous_fst).prodMk
      (TopCat.I.homeomorph.symm.continuous.comp continuous_snd))

/-- The pointwise path supplied by a homotopy, with its literal orientation. -/
private def homotopyPointPath
    {X B : TopCat.{u}} {a₀ a₁ : X ⟶ B}
    (H : ContinuousMap.Homotopy a₀.hom a₁.hom) (x : X) :
    Path (a₀ x) (a₁ x) where
  toFun t := H (t, x)
  continuous_toFun := H.continuous.comp
    (continuous_id.prodMk continuous_const)
  source' := H.map_zero_left x
  target' := H.map_one_left x

private theorem homotopyPointPath_continuous_family
    {X B : TopCat.{u}} {a₀ a₁ : X ⟶ B}
    (H : ContinuousMap.Homotopy a₀.hom a₁.hom) :
    Continuous (fun z : X × unitInterval => homotopyPointPath H z.1 z.2) := by
  exact H.continuous.comp (continuous_snd.prodMk continuous_fst)

private theorem prependHomotopyFiberPath_continuous_family
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    Continuous (fun z : TopCat.homotopyFiber p b × unitInterval =>
      ((homotopyPointPath (a₀ := s ≫ q) (a₁ := p) H
        (TopCat.homotopyFiberToTotal p b z.1)).trans
          (fiberRootPath p b z.1)) z.2) := by
  have hH : Continuous (fun z : TopCat.homotopyFiber p b × unitInterval =>
      homotopyPointPath (a₀ := s ≫ q) (a₁ := p) H
        (TopCat.homotopyFiberToTotal p b z.1) z.2) :=
    (homotopyPointPath_continuous_family (a₀ := s ≫ q) (a₁ := p) H).comp
      (((TopCat.homotopyFiberToTotal p b).hom.continuous.comp
        continuous_fst).prodMk continuous_snd)
  exact Path.trans_continuous_family
    (fun z : TopCat.homotopyFiber p b =>
      homotopyPointPath (a₀ := s ≫ q) (a₁ := p) H
        (TopCat.homotopyFiberToTotal p b z)) hH
    (fun z : TopCat.homotopyFiber p b => fiberRootPath p b z)
    (fiberRootPath_continuous_family p b)

private theorem prependHomotopyFiberPath_continuous
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    Continuous (fun z : TopCat.homotopyFiber p b × TopCat.I.{u} =>
      ((homotopyPointPath (a₀ := s ≫ q) (a₁ := p) H
        (TopCat.homotopyFiberToTotal p b z.1)).trans
          (fiberRootPath p b z.1)) (TopCat.I.homeomorph z.2)) := by
  have hinterval : Continuous (fun z : TopCat.homotopyFiber p b × TopCat.I.{u} =>
      (z.1, TopCat.I.homeomorph z.2)) :=
    continuous_fst.prodMk
      (TopCat.I.homeomorph.continuous.comp continuous_snd)
  have hcomp :=
    (prependHomotopyFiberPath_continuous_family s p q b H).comp hinterval
  refine hcomp.congr ?_
  intro z
  rfl

private def prependHomotopyFiberPath
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    TopCat.homotopyFiber p b ⟶ TopCat.pathObject B :=
  TopCat.ofHom <| ContinuousMap.curry
    ({ toFun := (fun z : TopCat.homotopyFiber p b × TopCat.I.{u} =>
          ((homotopyPointPath (a₀ := s ≫ q) (a₁ := p) H
            (TopCat.homotopyFiberToTotal p b z.1)).trans
              (fiberRootPath p b z.1)) (TopCat.I.homeomorph z.2))
       continuous_toFun := prependHomotopyFiberPath_continuous s p q b H } :
      C(TopCat.homotopyFiber p b × TopCat.I.{u}, B))

@[reassoc]

private theorem homotopyFiberMapOfHomotopy_path_map
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    TopCat.homotopyFiberMapOfHomotopy s p q b H ≫
        TopCat.homotopyFiberPath q b =
      prependHomotopyFiberPath s p q b H := by
  apply TopCat.ext
  intro z
  apply ContinuousMap.ext
  intro t
  have hpath := TopCat.homotopyFiberMapOfHomotopy_path s p q b H z t
  have htrans := Path.trans_apply
    (homotopyPointPath (a₀ := s ≫ q) (a₁ := p) H
      (TopCat.homotopyFiberToTotal p b z)) (fiberRootPath p b z)
    (TopCat.I.homeomorph t)
  exact hpath.trans htrans.symm

private theorem homotopyFiberMapOfHomotopy_path
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom)
    (z : TopCat.homotopyFiber p b) (t : TopCat.I.{u}) :
    TopCat.homotopyFiberPath q b
        (TopCat.homotopyFiberMapOfHomotopy s p q b H z) t =
      ((homotopyPointPath H (TopCat.homotopyFiberToTotal p b z)).trans
        (fiberRootPath p b z)) (TopCat.I.homeomorph t) := by
  have h := ConcreteCategory.congr_hom
    (homotopyFiberMapOfHomotopy_path_map s p q b H) z
  exact congrArg (fun path => path t) h

private def blendReparam (r : unitInterval → unitInterval)
    (s t : unitInterval) : unitInterval :=
  ⟨(unitInterval.symm s : ℝ) • (r t : ℝ) + (s : ℝ) • (t : ℝ),
    convex_Icc _ _ (r t).2 t.2 (by unit_interval) (by unit_interval)
      (by simp) ⟩

private theorem blendReparam_continuous (r : unitInterval → unitInterval)
    (hr : Continuous r) :
    Continuous (fun st : unitInterval × unitInterval =>
      blendReparam r st.1 st.2) := by
  apply Continuous.subtype_mk
  fun_prop

private theorem blendReparam_zero (r : unitInterval → unitInterval)
    (t : unitInterval) : blendReparam r 0 t = r t := by
  apply Subtype.ext
  simp [blendReparam]

private theorem blendReparam_one (r : unitInterval → unitInterval)
    (t : unitInterval) : blendReparam r 1 t = t := by
  apply Subtype.ext
  simp [blendReparam]

private theorem blendReparam_left (r : unitInterval → unitInterval)
    (hr0 : r 0 = 0) (s : unitInterval) :
    blendReparam r s 0 = 0 := by
  apply Subtype.ext
  simp [blendReparam, hr0]

private theorem blendReparam_right (r : unitInterval → unitInterval)
    (hr1 : r 1 = 1) (s : unitInterval) :
    blendReparam r s 1 = 1 := by
  apply Subtype.ext
  simp [blendReparam, hr1]

private def intervalZero (A : TopCat.{u}) :
    A ⟶ TopCat.of (unitInterval × (A : Type u)) :=
  TopCat.ofHom
    { toFun := fun a => (0, a)
      continuous_toFun := continuous_const.prodMk continuous_id }

private def intervalOne (A : TopCat.{u}) :
    A ⟶ TopCat.of (unitInterval × (A : Type u)) :=
  TopCat.ofHom
    { toFun := fun a => (1, a)
      continuous_toFun := continuous_const.prodMk continuous_id }

private def intervalSnd (A : TopCat.{u}) :
    TopCat.of (unitInterval × (A : Type u)) ⟶ A :=
  TopCat.ofHom ContinuousMap.snd

@[simp]
private theorem intervalZero_snd (A : TopCat.{u}) :
    intervalZero A ≫ intervalSnd A = 𝟙 A := by
  rfl

@[simp]
private theorem intervalOne_snd (A : TopCat.{u}) :
    intervalOne A ≫ intervalSnd A = 𝟙 A := by
  rfl

/-- Reparametrize a whole compact-open path family, blending from `r` to the
identity as the outer parameter runs from zero to one. -/
private def reparamPathFamily {A B : TopCat.{u}}
    (p : A ⟶ TopCat.pathObject B) (r : unitInterval → unitInterval)
    (hr : Continuous r) :
    TopCat.of (unitInterval × (A : Type u)) ⟶ TopCat.pathObject B :=
  TopCat.ofHom <| ContinuousMap.curry
    { toFun := fun z =>
        p z.1.2
          (TopCat.I.homeomorph.symm
            (blendReparam r z.1.1 (TopCat.I.homeomorph z.2)))
      continuous_toFun := by
        have hp : Continuous (fun z :
            (unitInterval × (A : Type u)) × (TopCat.I.{u} : Type u) =>
            p z.1.2) :=
          p.hom.continuous.comp (continuous_snd.comp continuous_fst)
        have htI : Continuous (fun z :
            (unitInterval × (A : Type u)) × (TopCat.I.{u} : Type u) =>
            TopCat.I.homeomorph z.2) :=
          TopCat.I.homeomorph.continuous.comp continuous_snd
        have hs : Continuous (fun z :
            (unitInterval × (A : Type u)) × (TopCat.I.{u} : Type u) =>
            z.1.1) := continuous_fst.comp continuous_fst
        have hblend : Continuous (fun z :
            (unitInterval × (A : Type u)) × (TopCat.I.{u} : Type u) =>
            blendReparam r z.1.1 (TopCat.I.homeomorph z.2)) :=
          (blendReparam_continuous r hr).comp (hs.prodMk htI)
        exact continuous_eval.comp
          (hp.prodMk (TopCat.I.homeomorph.symm.continuous.comp hblend)) }

private theorem reparamPathFamily_evalZero {A B : TopCat.{u}}
    (p : A ⟶ TopCat.pathObject B) (r : unitInterval → unitInterval)
    (hr : Continuous r) (hr0 : r 0 = 0) :
    reparamPathFamily p r hr ≫ TopCat.pathEvalZero B =
      intervalSnd A ≫ p ≫ TopCat.pathEvalZero B := by
  apply TopCat.ext
  rintro ⟨s, a⟩
  have hTopZero : TopCat.I.homeomorph.symm (0 : unitInterval) =
      (0 : TopCat.I.{u}) := by
    apply TopCat.I.homeomorph.injective
    simp
  change p a (TopCat.I.homeomorph.symm
      (blendReparam r s (TopCat.I.homeomorph (0 : TopCat.I.{u})))) = p a 0
  rw [TopCat.I.homeomorph_zero, blendReparam_left r hr0, hTopZero]

private theorem reparamPathFamily_evalOne {A B : TopCat.{u}}
    (p : A ⟶ TopCat.pathObject B) (r : unitInterval → unitInterval)
    (hr : Continuous r) (hr1 : r 1 = 1) :
    reparamPathFamily p r hr ≫ TopCat.pathEvalOne B =
      intervalSnd A ≫ p ≫ TopCat.pathEvalOne B := by
  apply TopCat.ext
  rintro ⟨s, a⟩
  have hTopOne : TopCat.I.homeomorph.symm (1 : unitInterval) =
      (1 : TopCat.I.{u}) := by
    apply TopCat.I.homeomorph.injective
    simp
  change p a (TopCat.I.homeomorph.symm
      (blendReparam r s (TopCat.I.homeomorph (1 : TopCat.I.{u})))) = p a 1
  rw [TopCat.I.homeomorph_one, blendReparam_right r hr1, hTopOne]

private theorem intervalOne_comp_reparamPathFamily {A B : TopCat.{u}}
    (p : A ⟶ TopCat.pathObject B) (r : unitInterval → unitInterval)
    (hr : Continuous r) :
    intervalOne A ≫ reparamPathFamily p r hr = p := by
  apply TopCat.ext
  intro a
  apply ContinuousMap.ext
  intro t
  change p a (TopCat.I.homeomorph.symm
      (blendReparam r 1 (TopCat.I.homeomorph t))) = p a t
  rw [blendReparam_one, TopCat.I.homeomorph.symm_apply_apply]

/-! ## Reparametrization inside a homotopy fiber -/

private def homotopyFiberReparamLift
    {A X B : TopCat.{u}} (f : X ⟶ B) (b : B)
    (target : A ⟶ TopCat.homotopyFiber f b)
    (r : unitInterval → unitInterval) (hr : Continuous r)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1) :
    TopCat.of (unitInterval × (A : Type u)) ⟶ TopCat.homotopyFiber f b :=
  pullback.lift
    (Limits.prod.lift
      (intervalSnd A ≫ target ≫ TopCat.homotopyFiberToTotal f b)
      (intervalSnd A ≫ target ≫
        TopCat.homotopyPullbackRight f (TopCat.const b)))
    (reparamPathFamily (target ≫ TopCat.homotopyFiberPath f b) r hr)
    (by
      apply Limits.prod.hom_ext
      · calc
          (Limits.prod.lift
                (intervalSnd A ≫ target ≫ TopCat.homotopyFiberToTotal f b)
                (intervalSnd A ≫ target ≫
                  TopCat.homotopyPullbackRight f (TopCat.const b)) ≫
              Limits.prod.map f (TopCat.const b)) ≫ Limits.prod.fst =
              intervalSnd A ≫ target ≫
                TopCat.homotopyFiberToTotal f b ≫ f := by
                  simp [Category.assoc]
          _ = reparamPathFamily
                (target ≫ TopCat.homotopyFiberPath f b) r hr ≫
              TopCat.pathEvalZero B := by
                rw [reparamPathFamily_evalZero _ _ _ hr0]
                have h := congrArg
                  (fun k => intervalSnd A ≫ target ≫ k)
                  (TopCat.homotopyPullbackPath_evalZero f
                    (TopCat.const (X := TopCat.of PUnit) b))
                simpa [Category.assoc] using h.symm
          _ = (reparamPathFamily
                (target ≫ TopCat.homotopyFiberPath f b) r hr ≫
              TopCat.pathEndpoints B) ≫ Limits.prod.fst := by
                simp [TopCat.pathEndpoints]
      · calc
          (Limits.prod.lift
                (intervalSnd A ≫ target ≫ TopCat.homotopyFiberToTotal f b)
                (intervalSnd A ≫ target ≫
                  TopCat.homotopyPullbackRight f (TopCat.const b)) ≫
              Limits.prod.map f (TopCat.const b)) ≫ Limits.prod.snd =
              intervalSnd A ≫ target ≫
                TopCat.homotopyPullbackRight f (TopCat.const b) ≫
                  TopCat.const b := by
                    simp [Category.assoc]
          _ = reparamPathFamily
                (target ≫ TopCat.homotopyFiberPath f b) r hr ≫
              TopCat.pathEvalOne B := by
                rw [reparamPathFamily_evalOne _ _ _ hr1]
                have h := congrArg
                  (fun k => intervalSnd A ≫ target ≫ k)
                  (TopCat.homotopyPullbackPath_evalOne f
                    (TopCat.const (X := TopCat.of PUnit) b))
                simpa [Category.assoc] using h.symm
          _ = (reparamPathFamily
                (target ≫ TopCat.homotopyFiberPath f b) r hr ≫
              TopCat.pathEndpoints B) ≫ Limits.prod.snd := by
                simp [TopCat.pathEndpoints])

private theorem homotopyFiberReparamLift_toTotal
    {A X B : TopCat.{u}} (f : X ⟶ B) (b : B)
    (target : A ⟶ TopCat.homotopyFiber f b)
    (r : unitInterval → unitInterval) (hr : Continuous r)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1) :
    homotopyFiberReparamLift f b target r hr hr0 hr1 ≫
        TopCat.homotopyFiberToTotal f b =
      intervalSnd A ≫ target ≫ TopCat.homotopyFiberToTotal f b := by
  change homotopyFiberReparamLift f b target r hr hr0 hr1 ≫
      TopCat.homotopyPullbackLeft f (TopCat.const b) = _
  rw [homotopyFiberReparamLift,
    ← Category.assoc, pullback.lift_fst]
  simp

private theorem homotopyFiberReparamLift_path
    {A X B : TopCat.{u}} (f : X ⟶ B) (b : B)
    (target : A ⟶ TopCat.homotopyFiber f b)
    (r : unitInterval → unitInterval) (hr : Continuous r)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1) :
    homotopyFiberReparamLift f b target r hr hr0 hr1 ≫
        TopCat.homotopyFiberPath f b =
      reparamPathFamily (target ≫ TopCat.homotopyFiberPath f b) r hr := by
  change homotopyFiberReparamLift f b target r hr hr0 hr1 ≫
      TopCat.homotopyPullbackPath f (TopCat.const b) = _
  rw [homotopyFiberReparamLift, TopCat.homotopyPullbackPath,
    pullback.lift_snd]

private theorem intervalOne_comp_homotopyFiberReparamLift
    {A X B : TopCat.{u}} (f : X ⟶ B) (b : B)
    (target : A ⟶ TopCat.homotopyFiber f b)
    (r : unitInterval → unitInterval) (hr : Continuous r)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1) :
    intervalOne A ≫ homotopyFiberReparamLift f b target r hr hr0 hr1 =
      target := by
  apply TopCat.homotopyPullback_hom_ext
  · rw [Category.assoc, homotopyFiberReparamLift_toTotal]
    rw [← Category.assoc, intervalOne_snd, Category.id_comp]
  · apply TopCat.isTerminalPUnit.hom_ext
  · rw [Category.assoc, homotopyFiberReparamLift_path,
      intervalOne_comp_reparamPathFamily]

private def homotopyFiberReparamHomotopy
    {A X B : TopCat.{u}} (f : X ⟶ B) (b : B)
    (source target : A ⟶ TopCat.homotopyFiber f b)
    (r : unitInterval → unitInterval) (hr : Continuous r)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1)
    (htotal : source ≫ TopCat.homotopyFiberToTotal f b =
      target ≫ TopCat.homotopyFiberToTotal f b)
    (hpath : source ≫ TopCat.homotopyFiberPath f b =
      intervalZero A ≫
        reparamPathFamily (target ≫ TopCat.homotopyFiberPath f b) r hr) :
    ContinuousMap.Homotopy source.hom target.hom := by
  let lift := homotopyFiberReparamLift f b target r hr hr0 hr1
  have hzero : intervalZero A ≫ lift = source := by
    apply TopCat.homotopyPullback_hom_ext
    · rw [Category.assoc, homotopyFiberReparamLift_toTotal]
      rw [← Category.assoc, intervalZero_snd, Category.id_comp]
      exact htotal.symm
    · apply TopCat.isTerminalPUnit.hom_ext
    · rw [Category.assoc, homotopyFiberReparamLift_path]
      exact hpath.symm
  have hone : intervalOne A ≫ lift = target :=
    intervalOne_comp_homotopyFiberReparamLift f b target r hr hr0 hr1
  exact
    { toContinuousMap := lift.hom
      map_zero_left := fun a => by
        simpa [intervalZero] using ConcreteCategory.congr_hom hzero a
      map_one_left := fun a => by
        simpa [intervalOne] using ConcreteCategory.congr_hom hone a }

/-! ## Homotopy-coherent identity and composition -/

private def reflTransReparam (t : unitInterval) : unitInterval :=
  ⟨max 0 (2 * t - 1),
    ⟨le_max_left _ _, max_le (by norm_num) (by
      have ht := t.2.2
      linarith)⟩⟩

private theorem reflTransReparam_continuous :
    Continuous reflTransReparam := by
  apply Continuous.subtype_mk
  exact continuous_const.max
    ((continuous_const.mul continuous_subtype_val).sub continuous_const)

private theorem reflTransReparam_zero : reflTransReparam 0 = 0 := by
  apply Subtype.ext
  norm_num [reflTransReparam]

private theorem reflTransReparam_one : reflTransReparam 1 = 1 := by
  apply Subtype.ext
  norm_num [reflTransReparam]

private theorem refl_trans_eq_reparam {B : TopCat.{u}} {x y : B}
    (p : Path x y) :
    (Path.refl x).trans p =
      p.reparam reflTransReparam reflTransReparam_continuous
        reflTransReparam_zero reflTransReparam_one := by
  apply Path.ext
  funext t
  simp only [Path.trans_apply, Path.coe_reparam]
  split_ifs with ht
  · have hlin : 2 * (t : ℝ) - 1 ≤ 0 := by linarith
    simp [Path.refl, reflTransReparam, max_eq_left hlin]
    rfl
  · have hlin : 0 ≤ 2 * (t : ℝ) - 1 := by
      have ht' : 1 / 2 ≤ (t : ℝ) := (not_le.1 ht).le
      linarith
    simp [reflTransReparam, max_eq_right hlin]

private def assocReparam : unitInterval → unitInterval := fun t =>
  ⟨Path.Homotopy.transAssocReparamAux t,
    Path.Homotopy.transAssocReparamAux_mem_I t⟩

private theorem assocReparam_continuous : Continuous assocReparam := by
  apply Continuous.subtype_mk
  exact Path.Homotopy.continuous_transAssocReparamAux

private theorem assocReparam_zero : assocReparam 0 = 0 := by
  apply Subtype.ext
  exact Path.Homotopy.transAssocReparamAux_zero

private theorem assocReparam_one : assocReparam 1 = 1 := by
  apply Subtype.ext
  exact Path.Homotopy.transAssocReparamAux_one

private theorem trans_assoc_eq_reparam {B : TopCat.{u}}
    {x₀ x₁ x₂ x₃ : B} (p : Path x₀ x₁)
    (q : Path x₁ x₂) (r : Path x₂ x₃) :
    (p.trans q).trans r =
      (p.trans (q.trans r)).reparam assocReparam assocReparam_continuous
        assocReparam_zero assocReparam_one := by
  calc
    (p.trans q).trans r =
        (p.trans (q.trans r)).reparam
          (fun t => ⟨Path.Homotopy.transAssocReparamAux t,
            Path.Homotopy.transAssocReparamAux_mem_I t⟩)
          (by fun_prop)
          (Subtype.ext Path.Homotopy.transAssocReparamAux_zero)
          (Subtype.ext Path.Homotopy.transAssocReparamAux_one) :=
      Path.Homotopy.trans_assoc_reparam p q r
    _ = (p.trans (q.trans r)).reparam assocReparam
          assocReparam_continuous assocReparam_zero assocReparam_one := by
      apply Path.ext
      rfl


private def IdentityCoherenceTarget : Prop :=
  ∀ {X B : TopCat.{u}} (p : X ⟶ B) (b : B),
    Nonempty <| ContinuousMap.Homotopy
      (TopCat.homotopyFiberMapOfHomotopy (𝟙 X) p p b
        (identitySquareHomotopy p)).hom
      ((𝟙 (TopCat.homotopyFiber p b) :
        TopCat.homotopyFiber p b ⟶ TopCat.homotopyFiber p b).hom)

private def StrictSquareCoherenceTarget : Prop :=
  ∀ {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (h : s ≫ q = p),
    Nonempty <| ContinuousMap.Homotopy
      (TopCat.homotopyFiberMapOfHomotopy s p q b
        (strictSquareHomotopy s p q h)).hom
      (TopCat.homotopyPullbackMap s (𝟙 (TopCat.of PUnit)) (𝟙 B)
        (by simp [h]) (by simp)).hom

private def CompositionCoherenceTarget : Prop :=
  ∀ {X Y Z B : TopCat.{u}}
    (s : X ⟶ Y) (t : Y ⟶ Z) (p : X ⟶ B)
    (q : Y ⟶ B) (r : Z ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom)
    (K : ContinuousMap.Homotopy (t ≫ r).hom q.hom),
    Nonempty <| ContinuousMap.Homotopy
      (TopCat.homotopyFiberMapOfHomotopy s p q b H ≫
        TopCat.homotopyFiberMapOfHomotopy t q r b K).hom
      (TopCat.homotopyFiberMapOfHomotopy (s ≫ t) p r b
        (compositeSquareHomotopy s t p q r H K)).hom

private theorem identitySquareHomotopy_pointPath
    {X B : TopCat.{u}} (p : X ⟶ B) (x : X) :
    homotopyPointPath (identitySquareHomotopy p) x = Path.refl (p x) := by
  apply Path.ext
  funext t
  rfl

private theorem identityCoherenceStatement_proof :
    IdentityCoherenceTarget.{u} := by
  intro X B p b
  refine ⟨?_⟩
  apply homotopyFiberReparamHomotopy p b
    (TopCat.homotopyFiberMapOfHomotopy (𝟙 X) p p b
      (identitySquareHomotopy p))
    (𝟙 (TopCat.homotopyFiber p b)) reflTransReparam
    reflTransReparam_continuous reflTransReparam_zero
    reflTransReparam_one
  · exact TopCat.homotopyFiberMapOfHomotopy_toTotal
      (𝟙 X) p p b (identitySquareHomotopy p)
  · rw [homotopyFiberMapOfHomotopy_path_map]
    apply TopCat.ext
    intro z
    apply ContinuousMap.ext
    intro t
    have h := congrArg
      (fun path : Path
          (p (TopCat.homotopyFiberToTotal p b z)) b =>
        path (TopCat.I.homeomorph t))
      (refl_trans_eq_reparam (fiberRootPath p b z))
    change ((homotopyPointPath (identitySquareHomotopy p)
          (TopCat.homotopyFiberToTotal p b z)).trans
        (fiberRootPath p b z)) (TopCat.I.homeomorph t) =
      TopCat.homotopyFiberPath p b z
        (TopCat.I.homeomorph.symm
          (blendReparam reflTransReparam 0 (TopCat.I.homeomorph t)))
    rw [blendReparam_zero, identitySquareHomotopy_pointPath]
    change ((Path.refl (p (TopCat.homotopyFiberToTotal p b z))).trans
        (fiberRootPath p b z)) (TopCat.I.homeomorph t) =
      fiberRootPath p b z (reflTransReparam (TopCat.I.homeomorph t))
    exact h

private theorem constantSquareCoherenceStatement_proof :
    StrictSquareCoherenceTarget.{u} := by
  intro X Y B s p q b h
  subst p
  let target : TopCat.homotopyFiber (s ≫ q) b ⟶
      TopCat.homotopyFiber q b :=
    TopCat.homotopyPullbackMap s (𝟙 (TopCat.of PUnit)) (𝟙 B)
      (by simp) (by simp)
  refine ⟨?_⟩
  apply homotopyFiberReparamHomotopy q b
    (TopCat.homotopyFiberMapOfHomotopy s (s ≫ q) q b
      (strictSquareHomotopy s (s ≫ q) q rfl))
    target reflTransReparam reflTransReparam_continuous
    reflTransReparam_zero reflTransReparam_one
  · rw [TopCat.homotopyFiberMapOfHomotopy_toTotal]
    simp [target]
  · rw [homotopyFiberMapOfHomotopy_path_map]
    apply TopCat.ext
    intro z
    apply ContinuousMap.ext
    intro t
    have hpoint :
        homotopyPointPath
            (strictSquareHomotopy s (s ≫ q) q rfl)
            (TopCat.homotopyFiberToTotal (s ≫ q) b z) =
          Path.refl ((s ≫ q)
            (TopCat.homotopyFiberToTotal (s ≫ q) b z)) := by
      apply Path.ext
      funext τ
      rfl
    have hreparam := congrArg
      (fun path : Path
          ((s ≫ q) (TopCat.homotopyFiberToTotal (s ≫ q) b z)) b =>
        path (TopCat.I.homeomorph t))
      (refl_trans_eq_reparam (fiberRootPath (s ≫ q) b z))
    change ((homotopyPointPath
          (strictSquareHomotopy s (s ≫ q) q rfl)
          (TopCat.homotopyFiberToTotal (s ≫ q) b z)).trans
        (fiberRootPath (s ≫ q) b z)) (TopCat.I.homeomorph t) =
      (target ≫ TopCat.homotopyFiberPath q b) z
        (TopCat.I.homeomorph.symm
          (blendReparam reflTransReparam 0 (TopCat.I.homeomorph t)))
    rw [blendReparam_zero, hpoint]
    have htarget : target ≫ TopCat.homotopyFiberPath q b =
        TopCat.homotopyFiberPath (s ≫ q) b := by
      simp [target]
    rw [htarget]
    change ((Path.refl
          ((s ≫ q) (TopCat.homotopyFiberToTotal (s ≫ q) b z))).trans
        (fiberRootPath (s ≫ q) b z)) (TopCat.I.homeomorph t) =
      fiberRootPath (s ≫ q) b z
        (reflTransReparam (TopCat.I.homeomorph t))
    exact hreparam

private theorem precomposeSquareHomotopy_pointPath
    {X Y Z B : TopCat.{u}} (s : X ⟶ Y) (t : Y ⟶ Z)
    (q : Y ⟶ B) (r : Z ⟶ B)
    (K : ContinuousMap.Homotopy (t ≫ r).hom q.hom) (x : X) :
    homotopyPointPath (precomposeSquareHomotopy s t q r K) x =
      homotopyPointPath K (s x) := by
  apply Path.ext
  funext τ
  rfl

private theorem compositeSquareHomotopy_pointPath
    {X Y Z B : TopCat.{u}}
    (s : X ⟶ Y) (t : Y ⟶ Z) (p : X ⟶ B)
    (q : Y ⟶ B) (r : Z ⟶ B)
    (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom)
    (K : ContinuousMap.Homotopy (t ≫ r).hom q.hom) (x : X) :
    homotopyPointPath (compositeSquareHomotopy s t p q r H K) x =
      (homotopyPointPath K (s x)).trans (homotopyPointPath H x) := by
  rw [compositeSquareHomotopy]
  apply Path.ext
  funext τ
  change ((precomposeSquareHomotopy s t q r K).trans H) (τ, x) = _
  rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split_ifs with hτ
  · change homotopyPointPath (precomposeSquareHomotopy s t q r K) x
        ⟨2 * τ, _⟩ = _
    rw [precomposeSquareHomotopy_pointPath]
  · rfl

private theorem compositionCoherenceStatement_proof :
    CompositionCoherenceTarget.{u} := by
  intro X Y Z B s t p q r b H K
  let first := TopCat.homotopyFiberMapOfHomotopy s p q b H
  let second := TopCat.homotopyFiberMapOfHomotopy t q r b K
  let direct := TopCat.homotopyFiberMapOfHomotopy (s ≫ t) p r b
    (compositeSquareHomotopy s t p q r H K)
  have hDirectToSequential : ContinuousMap.Homotopy direct.hom
      (first ≫ second).hom := by
    apply homotopyFiberReparamHomotopy r b direct (first ≫ second)
      assocReparam assocReparam_continuous assocReparam_zero
        assocReparam_one
    · dsimp only [direct, first, second]
      simp [Category.assoc]
    · dsimp only [direct, first, second]
      rw [homotopyFiberMapOfHomotopy_path_map]
      apply TopCat.ext
      intro z
      apply ContinuousMap.ext
      intro τ
      let x := TopCat.homotopyFiberToTotal p b z
      let z₁ := TopCat.homotopyFiberMapOfHomotopy s p q b H z
      have hTotal : TopCat.homotopyFiberToTotal q b z₁ = s x :=
        ConcreteCategory.congr_hom
          (TopCat.homotopyFiberMapOfHomotopy_toTotal s p q b H) z
      have hSequential (v : TopCat.I.{u}) :
          TopCat.homotopyFiberPath r b
              (TopCat.homotopyFiberMapOfHomotopy t q r b K z₁) v =
            ((homotopyPointPath K (s x)).trans
              ((homotopyPointPath H x).trans (fiberRootPath p b z)))
                (TopCat.I.homeomorph v) := by
        rw [homotopyFiberMapOfHomotopy_path]
        rw [Path.trans_apply]
        split_ifs with hv
        · rw [hTotal]
          rw [Path.trans_apply]
          simp only [hv]
          simp only [dite_true]
        · let w : unitInterval :=
            ⟨2 * TopCat.I.homeomorph v - 1,
              unitInterval.two_mul_sub_one_mem_iff.2
                ⟨(not_le.1 hv).le, (TopCat.I.homeomorph v).2.2⟩⟩
          have hFirst := homotopyFiberMapOfHomotopy_path
            s p q b H z (TopCat.I.homeomorph.symm w)
          rw [Path.trans_apply]
          simp only [hv]
          change TopCat.homotopyFiberPath q b z₁
              (TopCat.I.homeomorph.symm w) =
            ((homotopyPointPath H x).trans (fiberRootPath p b z)) w
          simpa [z₁, x, w] using hFirst
      have hAssoc := congrArg
        (fun path : Path (((t ≫ r) (s x))) b =>
          path (TopCat.I.homeomorph τ))
        (trans_assoc_eq_reparam
          (homotopyPointPath K (s x))
          (homotopyPointPath H x) (fiberRootPath p b z))
      change ((homotopyPointPath
            (compositeSquareHomotopy s t p q r H K) x).trans
          (fiberRootPath p b z)) (TopCat.I.homeomorph τ) =
        TopCat.homotopyFiberPath r b
          (TopCat.homotopyFiberMapOfHomotopy t q r b K z₁)
          (TopCat.I.homeomorph.symm
            (blendReparam assocReparam 0 (TopCat.I.homeomorph τ)))
      rw [blendReparam_zero,
        compositeSquareHomotopy_pointPath]
      have hSeq := hSequential
        (TopCat.I.homeomorph.symm
          (assocReparam (TopCat.I.homeomorph τ)))
      rw [TopCat.I.homeomorph.apply_symm_apply] at hSeq
      exact hAssoc.trans hSeq.symm
  exact ⟨hDirectToSequential.symm⟩


#check IdentityCoherenceTarget.{u}
#check IdentityCoherenceTarget.{1}
#check IdentityCoherenceTarget.{0}
#check StrictSquareCoherenceTarget.{u}
#check StrictSquareCoherenceTarget.{1}
#check StrictSquareCoherenceTarget.{0}
#check CompositionCoherenceTarget.{u}
#check CompositionCoherenceTarget.{1}
#check CompositionCoherenceTarget.{0}

example : IdentityCoherenceTarget.{u} := identityCoherenceStatement_proof
example : IdentityCoherenceTarget.{1} := identityCoherenceStatement_proof
example : IdentityCoherenceTarget.{0} := identityCoherenceStatement_proof
example : StrictSquareCoherenceTarget.{u} :=
  constantSquareCoherenceStatement_proof
example : StrictSquareCoherenceTarget.{1} :=
  constantSquareCoherenceStatement_proof
example : StrictSquareCoherenceTarget.{0} :=
  constantSquareCoherenceStatement_proof
example : CompositionCoherenceTarget.{u} := compositionCoherenceStatement_proof
example : CompositionCoherenceTarget.{1} := compositionCoherenceStatement_proof
example : CompositionCoherenceTarget.{0} := compositionCoherenceStatement_proof

end IndependentCoherenceRegression

section PathReparametrizationControls

variable {B : TopCat.{u}} {x₀ x₁ x₂ x₃ : B}

example (p : Path x₀ x₁) :
    Nonempty (Path.Homotopy ((Path.refl x₀).trans p) p) :=
  ⟨Path.Homotopy.reflTrans p⟩

example (p : Path x₀ x₁) :
    Nonempty (Path.Homotopy (p.trans (Path.refl x₁)) p) :=
  ⟨Path.Homotopy.transRefl p⟩

example (p : Path x₀ x₁) (q : Path x₁ x₂) (r : Path x₂ x₃) :
    Nonempty (Path.Homotopy ((p.trans q).trans r) (p.trans (q.trans r))) :=
  ⟨Path.Homotopy.transAssoc p q r⟩

end PathReparametrizationControls

section PremiseAndInstanceControls

#guard_msgs (error, substring := true) in
example {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    TopCat.weakHomotopyEquivalences
      (TopCat.homotopyFiberMapOfHomotopy s p q b H) :=
  TopCat.homotopyFiberMapOfHomotopy_mem_weakHomotopyEquivalences
    s p q b H

example : True := by
  fail_if_success
    let _ : ModelCategory TopCat.{u} := inferInstance
  trivial

open scoped TopCat.modelCategory in
example (_B : TopCat.{u}) : True := by
  fail_if_success
    let _ : Fibration (TopCat.pathEndpoints _B) := inferInstance
  trivial

open scoped TopCat.modelCategory in
example : True := by
  fail_if_success
    let _ : IsRightProper TopCat.{u} := inferInstance
  trivial

end PremiseAndInstanceControls

section OppositeEndpoints

private def oppositeIntervalZero :
    TopCat.of PUnit.{u + 1} ⟶ TopCat.I.{u} :=
  TopCat.const 0

private def oppositeIntervalOne :
    TopCat.of PUnit.{u + 1} ⟶ TopCat.I.{u} :=
  TopCat.const 1

example : IsEmpty ↑(pullback oppositeIntervalZero.{u}
    oppositeIntervalOne.{u} : TopCat.{u}) := by
  constructor
  intro z
  have h := ConcreteCategory.congr_hom
    (pullback.condition :
      pullback.fst oppositeIntervalZero.{u} oppositeIntervalOne.{u} ≫
          oppositeIntervalZero.{u} =
        pullback.snd oppositeIntervalZero.{u} oppositeIntervalOne.{u} ≫
          oppositeIntervalOne.{u}) z
  change (0 : TopCat.I.{u}) = 1 at h
  have hreal : (0 : ℝ) = 1 :=
    congrArg (fun t : TopCat.I.{u} =>
      ((TopCat.I.homeomorph t : unitInterval) : ℝ)) h
  exact zero_ne_one hreal

example : Nonempty
    (TopCat.homotopyFiber oppositeIntervalZero.{u}
      (1 : TopCat.I.{u})) := by
  let witness : TopCat.of PUnit.{u + 1} ⟶
      TopCat.homotopyFiber oppositeIntervalZero.{u}
        (1 : TopCat.I.{u}) :=
    pullback.lift
      (Limits.prod.lift (𝟙 _) (𝟙 _))
      (TopCat.const (ContinuousMap.id TopCat.I.{u}))
      (by
        apply Limits.prod.hom_ext
        · simp [TopCat.pathEndpoints]
          apply ConcreteCategory.hom_ext
          intro z
          rfl
        · simp [TopCat.pathEndpoints]
          apply ConcreteCategory.hom_ext
          intro z
          rfl)
  exact ⟨witness PUnit.unit⟩

end OppositeEndpoints

section PrivacyAndNonclaims

#guard_msgs (error, substring := true) in
#check TopCatHomotopySquarePreflight.homotopyPointPath

#guard_msgs (error, substring := true) in
#check TopCatHomotopySquarePreflight.mappingPath

#guard_msgs (error, substring := true) in
#check TopCatHomotopySquarePreflight.mappingPathStrictFiberIso

#guard_msgs (error, substring := true) in
#check TopCat.modelCategory.pathEndpoints_fibration_data

#guard_msgs (error, substring := true) in
#check TopCatRealizedHornIntervalPrismRetractionPreflight.realizedPrismRetract

#guard_msgs (error, substring := true) in
#check TopCat.homotopyFiberMapOfHomotopy_id_eq

#guard_msgs (error, substring := true) in
#check TopCat.HomotopyFiberSquareFibration

#guard_msgs (error, substring := true) in
#check TopCat.HomotopyFiberSquareQuasifibration

#guard_msgs (error, substring := true) in
#check TopCat.QuillenBHomotopyFiberComparison

#guard_msgs (error, substring := true) in
#check TopCat.BKHomotopyFiberComparison

end PrivacyAndNonclaims

#print axioms TopCat.homotopyFiberMapOfHomotopy
#print axioms TopCat.homotopyFiberMapOfHomotopy_toTotal
#print axioms TopCat.homotopyFiberMapOfHomotopy_path
#print axioms TopCat.homotopyFiberIdentitySquareHomotopy
#print axioms TopCat.homotopyFiberStrictSquareHomotopy
#print axioms TopCat.homotopyFiberCompositeSquareHomotopy
#print axioms TopCat.homotopyFiberMapOfHomotopy_id_homotopy
#print axioms TopCat.homotopyFiberMapOfHomotopy_strict_homotopy
#print axioms TopCat.homotopyFiberMapOfHomotopy_comp_homotopy
#print axioms TopCat.homotopyFiberMapOfHomotopy_mem_weakHomotopyEquivalences

end MathlibExtTest.TopCat.HomotopyFiberHomotopySquare
