/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module
import MathlibExt.AlgebraicGeometry.GroupTorsorGeometry
import Mathlib.Algebra.Field.ZMod
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.GroupTorsorGeometry
/-! These actual quotient-stack objects over Z/4 are nonisomorphic,
although their parameters agree after every map to a field. -/
noncomputable section
private abbrev base : Scheme := Spec (.of (ZMod 4))
private abbrev point : Over base := 𝟙_ (Over base)
private def trivialTorsor : Torsor point point where
  total := point
  projection := 𝟙 point
  action := inferInstance
  invariant := by simp [leftUnitor_hom]
  flat := inferInstance
  presentation := inferInstance
  surjective := inferInstance
  relation_isIso := by
    let r := relation point γ[point,point] (𝟙 point) (by simp [leftUnitor_hom])
    have : IsIso (r ≫ pullback.fst (𝟙 base) (𝟙 base)) := by
      have h : r ≫ pullback.fst (𝟙 base) (𝟙 base) = (snd point point).left :=
        pullback.lift_fst _ _ _
      rw [h]
      simpa only [leftUnitor_hom] using
        (inferInstance : IsIso ((λ_ point).hom.left))
    exact IsIso.of_isIso_comp_right r (pullback.fst (𝟙 base) (𝟙 base))
private abbrev target : Over base :=
  Over.mk (Spec.map (CommRingCat.ofHom (Polynomial.C : ZMod 4 →+* Polynomial (ZMod 4))))
private def parameter (a : ZMod 4) : point ⟶ target :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))) (by
    change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)) ≫
      Spec.map (CommRingCat.ofHom Polynomial.C) = 𝟙 base
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h : (Polynomial.evalRingHom a).comp Polynomial.C = RingHom.id (ZMod 4) := by
      ext x
      exact Polynomial.eval_C
    rw [h, CommRingCat.ofHom_id, Spec.map_id])
private def objectAt (a : ZMod 4) : QuotientObject point target point where
  torsor := trivialTorsor
  map := parameter a
  equivariant := by
    change (λ_ point).hom ≫ parameter a = (point ◁ parameter a) ≫ (λ_ target).hom
    exact ((leftUnitorNatIso (Over base)).hom.naturality (parameter a)).symm
private theorem parameters_distinct : parameter 2 ≠ parameter 0 := by
  intro h
  have hs := congrArg Over.Hom.left h
  have hr := Spec.map_injective hs
  have hv := congrArg (fun f : CommRingCat.of (Polynomial (ZMod 4)) ⟶ CommRingCat.of (ZMod 4) =>
    f.hom Polynomial.X) hr
  have hh : (2 : ZMod 4) = 0 := by
    simpa only [CommRingCat.hom_ofHom, Polynomial.coe_evalRingHom, Polynomial.eval_X] using hv
  exact (by decide : (2 : ZMod 4) ≠ 0) hh
example : ¬ Nonempty (QuotientIso point target (objectAt 2) (objectAt 0)) := by
  rintro ⟨f⟩
  have hi : f.iso.hom = 𝟙 point := by
    have h := f.over
    simpa only [objectAt, trivialTorsor, Category.comp_id] using h
  have h := f.target
  dsimp only [objectAt, trivialTorsor] at h hi
  rw [hi] at h
  simp only [Category.id_comp] at h
  exact parameters_distinct h.symm

example (K : Type) [Field K] (f : ZMod 4 →+* K) : f 2 = f 0 := by
  rw [map_zero]
  have h : f 2 * f 2 = 0 := by
    simpa only [map_mul, map_zero] using congrArg f
      (by decide : (2 : ZMod 4) * 2 = 0)
  exact mul_self_eq_zero.mp h
