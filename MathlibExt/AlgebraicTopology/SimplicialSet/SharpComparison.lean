/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SharpMonoGluing
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RightProper

/-!
# Equivalent sharpness criteria

Comparison-based sharpness and preservation of weak equivalences under base change are equivalent for maps of simplicial sets. A weak map between sharp objects over the same base induces a weak ordinary pullback map along every test map; the base is arbitrary.
-/

public section
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped SSet.modelCategoryQuillen
namespace SSet.SharpComparisonDraft

/-- Precise weak-between-sharp pullback theorem; no Kan base hypothesis. -/
theorem ordinaryMap_weak {X X' B T : SSet.{u}}
    (f : X ⟶ X') (p : X' ⟶ B) (t : T ⟶ B)
    (hf : WeakEquivalence f) (hp : Sharp p) (hfp : Sharp (f ≫ p)) :
    WeakEquivalence (ordinaryMap f p t) := by
  let η := cospanMap f p t
  have hη (j : WalkingCospan) : WeakEquivalence (η.app j) := by
    cases j with
    | none => change WeakEquivalence (𝟙 B); infer_instance
    | some a =>
      cases a with
      | left => change WeakEquivalence f; exact hf
      | right => change WeakEquivalence (𝟙 T); infer_instance
  have hh := HomotopicalAlgebra.homotopyPullback_map_weakEquivalence η hη
  have hl := hfp T t
  have hr := hp T t
  let _ : WeakEquivalence (comparison (f ≫ p) t) := hl
  let _ : WeakEquivalence (comparison p t) := hr
  let _ : WeakEquivalence
      ((HomotopicalAlgebra.homotopyPullback (C := SSet.{u})).map η) := hh
  have hfac : lim.map η ≫ comparison p t = comparison (f ≫ p) t ≫
      (HomotopicalAlgebra.homotopyPullback (C := SSet.{u})).map η :=
    (HomotopicalAlgebra.homotopyPullbackComparison (C := SSet.{u})).naturality η
  have hcomp : WeakEquivalence (lim.map η ≫ comparison p t) := by
    rw [hfac]
    infer_instance
  let _ : WeakEquivalence (lim.map η ≫ comparison p t) := hcomp
  have hmap : WeakEquivalence (lim.map η) :=
    weakEquivalence_of_postcomp (lim.map η) (comparison p t)
  rw [ordinaryMap_eq_limMap f p t]
  exact hmap

/-- Homotopy-cartesian sharpness implies the original Rezk base-change condition. -/
theorem Sharp.baseChange {X B : SSet.{u}} (p : X ⟶ B) (hp : Sharp p) :
    SharpBaseChange p := by
  intro U V w v hw
  let η : cospan p (w ≫ v) ⟶ cospan p v :=
    cospanHomMk (𝟙 B) (𝟙 X) w (by simp) (by simp)
  have hη (k : WalkingCospan) : WeakEquivalence (η.app k) := by
    cases k with
    | none => change WeakEquivalence (𝟙 B); infer_instance
    | some a =>
      cases a with
      | left => change WeakEquivalence (𝟙 X); infer_instance
      | right => change WeakEquivalence w; exact hw
  let _ : WeakEquivalence (comparison p (w ≫ v)) := hp U (w ≫ v)
  let _ : WeakEquivalence (comparison p v) := hp V v
  let _ : WeakEquivalence
      ((HomotopicalAlgebra.homotopyPullback (C := SSet.{u})).map η) :=
    HomotopicalAlgebra.homotopyPullback_map_weakEquivalence η hη
  have hfac : lim.map η ≫ comparison p v = comparison p (w ≫ v) ≫
      (HomotopicalAlgebra.homotopyPullback (C := SSet.{u})).map η :=
    (HomotopicalAlgebra.homotopyPullbackComparison (C := SSet.{u})).naturality η
  have hc : WeakEquivalence (lim.map η ≫ comparison p v) := by
    rw [hfac]
    infer_instance
  let _ := hc
  have hmap := weakEquivalence_of_postcomp (lim.map η) (comparison p v)
  have he : lim.map η = pullback.map p (w ≫ v) p v (𝟙 X) w (𝟙 B)
      (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [η]
  rw [he] at hmap
  exact hmap

/-- Rezk's base-change condition gives the canonical native homotopy-pullback comparison.
The original scalar KQ factorization is selected internally; B is not assumed Kan. -/
theorem sharp_of_baseChange {X B : SSet.{u}} (p : X ⟶ B) (hp : SharpBaseChange p) :
    Sharp p := by
  intro T t
  let F := MorphismProperty.functorialFactorizationData
    (trivialCofibrations SSet.{u}) (fibrations SSet.{u})
  let d := F.factorizationData t
  have hw : WeakEquivalence d.i := (weakEquivalence_iff _).mpr d.hi.2
  let _ : Fibration d.p := (fibration_iff _).mpr d.hp
  let η : cospan p t ⟶ cospan p d.p :=
    cospanHomMk (𝟙 B) (𝟙 X) d.i (by simp) (by simp)
  have hm : WeakEquivalence (lim.map η) := by
    have hb := hp T d.Z d.i d.p hw
    have he : lim.map η =
        (pullback.congrHom (f₁ := p) (f₂ := p) (g₁ := t) (g₂ := d.i ≫ d.p)
          rfl d.fac.symm).hom ≫
        pullback.map p (d.i ≫ d.p) p d.p (𝟙 X) d.i (𝟙 B) (by simp) (by simp) := by
      apply pullback.hom_ext <;> simp [η]
    rw [he]
    let _ := hb
    infer_instance
  have hη (k : WalkingCospan) : WeakEquivalence (η.app k) := by
    cases k with
    | none => change WeakEquivalence (𝟙 B); infer_instance
    | some a =>
      cases a with
      | left => change WeakEquivalence (𝟙 X); infer_instance
      | right => change WeakEquivalence d.i; exact hw
  let _ := hm
  let _ := HomotopicalAlgebra.homotopyPullback_map_weakEquivalence η hη
  let _ : Fibration ((cospan p d.p).map WalkingCospan.Hom.inr) := by
    change Fibration d.p
    infer_instance
  let _ : WeakEquivalence (comparison p d.p) :=
    HomotopicalAlgebra.weakEquivalence_homotopyPullbackComparison_of_rightProper_inr
      (cospan p d.p)
  have hfac : lim.map η ≫ comparison p d.p = comparison p t ≫
      (HomotopicalAlgebra.homotopyPullback (C := SSet.{u})).map η :=
    (HomotopicalAlgebra.homotopyPullbackComparison (C := SSet.{u})).naturality η
  have hc : WeakEquivalence
      (comparison p t ≫ (HomotopicalAlgebra.homotopyPullback (C := SSet.{u})).map η) := by
    rw [← hfac]
    infer_instance
  let _ := hc
  exact weakEquivalence_of_postcomp (comparison p t)
    ((HomotopicalAlgebra.homotopyPullback (C := SSet.{u})).map η)

/-- The source-grounded two definitions of sharpness agree on arbitrary scalar bases. -/
theorem sharp_iff_baseChange {X B : SSet.{u}} (p : X ⟶ B) :
    Sharp p ↔ SharpBaseChange p :=
  ⟨Sharp.baseChange p, sharp_of_baseChange p⟩

end SSet.SharpComparisonDraft
