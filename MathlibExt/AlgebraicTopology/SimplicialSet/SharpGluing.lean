/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SharpComparison
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.LeftProper
public import MathlibExt.AlgebraicTopology.SimplicialSet.PreimagePushout

/-!
# Gluing sharp maps across monomorphism pushouts

Rezk’s gluing criterion propagates sharpness across a pushout of simplicial sets with a weak leg and at least one monic initial leg. It retains the map between bases and requires sharpness of both maps over the intermediate base and of the composite on the other side.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped SSet.modelCategoryQuillen
namespace SSet.SharpComparisonDraft

/-- Either mono-leg pushout propagates the weak original f to original g.
The Mono f case is trivial-cofibration cobase stability, not an invalid left-proper use. -/
theorem weak_right_of_pushout_either_mono {X Y X' Y' : SSet.{u}}
    {i : X ⟶ Y} {f : X ⟶ X'} {g : Y ⟶ Y'} {j : X' ⟶ Y'}
    (sq : IsPushout i f g j) (hf : WeakEquivalence f)
    (hm : Mono i ∨ Mono f) : WeakEquivalence g := by
  let _ : WeakEquivalence f := hf
  rcases hm with hi | hfmono
  · let _ : Mono i := hi
    let _ : Cofibration i := (SSet.modelCategoryQuillen.cofibration_iff i).mpr hi
    exact IsLeftProper.weakEquivalence_of_isPushout sq
  · let _ : Mono f := hfmono
    let _ : Cofibration f := (SSet.modelCategoryQuillen.cofibration_iff f).mpr hfmono
    have htf : trivialCofibrations SSet.{u} f := mem_trivialCofibrations f
    have htg : trivialCofibrations SSet.{u} g :=
      MorphismProperty.of_isPushout sq htf
    exact (weakEquivalence_iff g).mpr htg.2

/-- Reassociate the original scalar pullback along p≫a, with both explicit inverse maps. -/
def compositePullbackIso {X A B U : SSet.{u}}
    (p : X ⟶ A) (a : A ⟶ B) (u : U ⟶ B) :
    pullback (p ≫ a) u ≅ pullback p (pullback.fst a u) where
  hom := pullback.lift (pullback.fst (p ≫ a) u)
    (pullback.lift (pullback.fst (p ≫ a) u ≫ p) (pullback.snd (p ≫ a) u)
      (by simpa [Category.assoc] using (pullback.condition (f := p ≫ a) (g := u))))
    (by simp)
  inv := pullback.lift (pullback.fst p (pullback.fst a u))
    (pullback.snd p (pullback.fst a u) ≫ pullback.snd a u)
    (by
      calc
        pullback.fst p (pullback.fst a u) ≫ (p ≫ a) =
            (pullback.snd p (pullback.fst a u) ≫ pullback.fst a u) ≫ a := by
              rw [← Category.assoc, pullback.condition]
        _ = (pullback.snd p (pullback.fst a u) ≫ pullback.snd a u) ≫ u := by
              rw [Category.assoc, pullback.condition, ← Category.assoc])
  hom_inv_id := by
    apply pullback.hom_ext <;> simp [Category.assoc]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp [Category.assoc]
    · apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd]
        rw [pullback.lift_fst_assoc (f := p ≫ a) (g := u), Category.id_comp]
        exact pullback.condition (f := p) (g := pullback.fst a u)
      · simp [Category.assoc]

/-- The same map f commutes with the actual pullback reassociation. -/
theorem compositePullbackIso_map {X X' A B U : SSet.{u}}
    (f : X ⟶ X') (p : X' ⟶ A) (a : A ⟶ B) (u : U ⟶ B) :
    ordinaryMap f (p ≫ a) u ≫ (compositePullbackIso p a u).hom =
      (compositePullbackIso (f ≫ p) a u).hom ≫
        ordinaryMap f p (pullback.fst a u) := by
  apply pullback.hom_ext
  · simp [ordinaryMap, compositePullbackIso, Category.assoc]; rfl
  · apply pullback.hom_ext <;>
      simp [ordinaryMap, compositePullbackIso, Category.assoc] <;> rfl

/-- Weak-between-sharp is transported along the SAME bottom map a. -/
theorem compositeOrdinaryMap_weak {X X' A B U : SSet.{u}}
    (f : X ⟶ X') (p : X' ⟶ A) (a : A ⟶ B) (u : U ⟶ B)
    (hf : WeakEquivalence f) (hp : Sharp p) (hfp : Sharp (f ≫ p)) :
    WeakEquivalence (ordinaryMap f (p ≫ a) u) := by
  let _ : WeakEquivalence (ordinaryMap f p (pullback.fst a u)) :=
    ordinaryMap_weak f p (pullback.fst a u) hf hp hfp
  have hfac := compositePullbackIso_map f p a u
  have hcomp : WeakEquivalence
      (ordinaryMap f (p ≫ a) u ≫ (compositePullbackIso p a u).hom) := by
    rw [hfac]
    infer_instance
  let _ := hcomp
  exact weakEquivalence_of_postcomp (ordinaryMap f (p ≫ a) u)
    (compositePullbackIso p a u).hom

/-- Pullback of an apex preimage is the actual original composite pullback. -/
def apexPreimageIso {D E B U : SSet.{u}}
    (q : E ⟶ B) (t : D ⟶ E) (u : U ⟶ B) :
    pullback (pullback.fst q u) t ≅ pullback (t ≫ q) u where
  hom := pullback.lift (pullback.snd (pullback.fst q u) t)
    (pullback.fst (pullback.fst q u) t ≫ pullback.snd q u)
    (by
      calc
        pullback.snd (pullback.fst q u) t ≫ (t ≫ q) =
            (pullback.fst (pullback.fst q u) t ≫ pullback.fst q u) ≫ q := by
              rw [← Category.assoc, ← pullback.condition]
        _ = (pullback.fst (pullback.fst q u) t ≫ pullback.snd q u) ≫ u := by
              rw [Category.assoc, pullback.condition, ← Category.assoc])
  inv := pullback.lift
    (pullback.lift (pullback.fst (t ≫ q) u ≫ t) (pullback.snd (t ≫ q) u)
      (by simpa [Category.assoc] using (pullback.condition (f := t ≫ q) (g := u))))
    (pullback.fst (t ≫ q) u) (by simp)
  hom_inv_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst]
        rw [pullback.lift_fst_assoc (f := t ≫ q) (g := u), Category.id_comp]
        exact (pullback.condition (f := pullback.fst q u) (g := t)).symm
      · simp [Category.assoc]
    · simp [Category.assoc]
  inv_hom_id := by
    apply pullback.hom_ext <;> simp [Category.assoc]

/-- The original comparison f commutes with apex preimage reassociation. -/
theorem apexPreimageIso_map {D D' E B U : SSet.{u}}
    (f : D ⟶ D') (q : E ⟶ B) (t : D' ⟶ E) (u : U ⟶ B) :
    (pullback.map (pullback.fst q u) (f ≫ t) (pullback.fst q u) t
      (𝟙 _) f (𝟙 _) (by simp) (by simp)) ≫ (apexPreimageIso q t u).hom =
        (apexPreimageIso q (f ≫ t) u).hom ≫ ordinaryMap f (t ≫ q) u := by
  have hfst : (apexPreimageIso q (f ≫ t) u).hom ≫
      pullback.fst (f ≫ (t ≫ q)) u = pullback.snd (pullback.fst q u) (f ≫ t) := by
    change (apexPreimageIso q (f ≫ t) u).hom ≫
      pullback.fst ((f ≫ t) ≫ q) u = _
    dsimp only [apexPreimageIso]
    exact pullback.lift_fst _ _ _
  have hsnd : (apexPreimageIso q (f ≫ t) u).hom ≫
      pullback.snd (f ≫ (t ≫ q)) u =
        pullback.fst (pullback.fst q u) (f ≫ t) ≫ pullback.snd q u := by
    change (apexPreimageIso q (f ≫ t) u).hom ≫
      pullback.snd ((f ≫ t) ≫ q) u = _
    dsimp only [apexPreimageIso]
    exact pullback.lift_snd _ _ _
  apply pullback.hom_ext
  · simp only [Category.assoc, (ordinaryMap_legs f (t ≫ q) u).1]
    rw [← Category.assoc (apexPreimageIso q (f ≫ t) u).hom, hfst]
    simp [apexPreimageIso]
  · simp only [Category.assoc, (ordinaryMap_legs f (t ≫ q) u).2, hsnd]
    simp [apexPreimageIso]

/-- Native preimage boundary-to-cell is the same f comparison up to square equality.
The equality-congruence of pullback source maps must be used when sq.w is not definitional. -/
theorem boundaryToCell_weak {X Y X' Y' A B U : SSet.{u}}
    {i : X ⟶ Y} {f : X ⟶ X'} {g : Y ⟶ Y'} {j : X' ⟶ Y'}
    (sq : IsPushout i f g j) (p : X' ⟶ A) (q : Y' ⟶ B) (a : A ⟶ B)
    (h : p ≫ a = j ≫ q) (u : U ⟶ B)
    (hf : WeakEquivalence f) (hp : Sharp p) (hfp : Sharp (f ≫ p)) :
    WeakEquivalence (SSet.PreimagePushout.boundaryToCell sq (pullback.fst q u)) := by
  have hw : WeakEquivalence (ordinaryMap f (j ≫ q) u) := by
    rw [← h]
    exact compositeOrdinaryMap_weak f p a u hf hp hfp
  let _ := hw
  let eSource := pullback.congrHom (f₁ := pullback.fst q u)
    (f₂ := pullback.fst q u) (g₁ := i ≫ g) (g₂ := f ≫ j) rfl sq.w
  have hfac : SSet.PreimagePushout.boundaryToCell sq (pullback.fst q u) ≫
      (apexPreimageIso q j u).hom =
        eSource.hom ≫ (apexPreimageIso q (f ≫ j) u).hom ≫ ordinaryMap f (j ≫ q) u := by
    have hfst : (apexPreimageIso q (f ≫ j) u).hom ≫
        pullback.fst (f ≫ (j ≫ q)) u = pullback.snd (pullback.fst q u) (f ≫ j) := by
      change (apexPreimageIso q (f ≫ j) u).hom ≫
        pullback.fst ((f ≫ j) ≫ q) u = _
      dsimp only [apexPreimageIso]
      exact pullback.lift_fst _ _ _
    have hsnd : (apexPreimageIso q (f ≫ j) u).hom ≫
        pullback.snd (f ≫ (j ≫ q)) u =
          pullback.fst (pullback.fst q u) (f ≫ j) ≫ pullback.snd q u := by
      change (apexPreimageIso q (f ≫ j) u).hom ≫
        pullback.snd ((f ≫ j) ≫ q) u = _
      dsimp only [apexPreimageIso]
      exact pullback.lift_snd _ _ _
    apply pullback.hom_ext
    · simp only [Category.assoc, (ordinaryMap_legs f (j ≫ q) u).1]
      rw [← Category.assoc (apexPreimageIso q (f ≫ j) u).hom, hfst]
      simp [eSource, apexPreimageIso]
    · simp only [Category.assoc, (ordinaryMap_legs f (j ≫ q) u).2, hsnd]
      simp [eSource, apexPreimageIso]
  have hcomp : WeakEquivalence
      (SSet.PreimagePushout.boundaryToCell sq (pullback.fst q u) ≫
        (apexPreimageIso q j u).hom) := by
    rw [hfac]
    infer_instance
  let _ := hcomp
  exact weakEquivalence_of_postcomp
    (SSet.PreimagePushout.boundaryToCell sq (pullback.fst q u))
    (apexPreimageIso q j u).hom

/-- Every original base change of g is weak by the original preimage pushout. -/
theorem ordinaryMap_g_weak {X Y X' Y' A B U : SSet.{u}}
    {i : X ⟶ Y} {f : X ⟶ X'} {g : Y ⟶ Y'} {j : X' ⟶ Y'}
    (sq : IsPushout i f g j) (p : X' ⟶ A) (q : Y' ⟶ B) (a : A ⟶ B)
    (h : p ≫ a = j ≫ q) (u : U ⟶ B)
    (hf : WeakEquivalence f) (hm : Mono i ∨ Mono f)
    (hp : Sharp p) (hfp : Sharp (f ≫ p)) :
    WeakEquivalence (ordinaryMap g q u) := by
  have hbf := boundaryToCell_weak sq p q a h u hf hp hfp
  let r := pullback.fst q u
  let pre := SSet.PreimagePushout.boundaryToOld (t := i) (r := g) r
  have hmono : Mono pre ∨ Mono (SSet.PreimagePushout.boundaryToCell sq r) := by
    rcases hm with hi | hfm
    · let _ : Mono i := hi
      exact Or.inl
          ((SSet.PreimagePushout.boundaryToOld_isPullback (t := i) (r := g) r).mono_fst_of_mono)
    · let _ : Mono f := hfm
      exact Or.inr ((SSet.PreimagePushout.boundaryToCell_isPullback sq r).mono_fst_of_mono)
  have hpo : IsPushout pre (SSet.PreimagePushout.boundaryToCell sq r)
      (pullback.fst r g) (pullback.fst r j) := by
    rcases hm with hi | hfm
    · let _ : Mono i := hi
      let eCommon := pullback.congrHom (f₁ := r) (f₂ := r)
        (g₁ := i ≫ g) (g₂ := f ≫ j) rfl sq.w
      apply ((SSet.PreimagePushout.isPushout sq.flip r).flip).of_iso'
        eCommon (Iso.refl _) (Iso.refl _) (Iso.refl _)
      · apply pullback.hom_ext <;>
          simp [eCommon, pre, SSet.PreimagePushout.boundaryToOld,
            SSet.PreimagePushout.boundaryToCell, Category.assoc]
      · apply pullback.hom_ext <;>
          simp [eCommon, SSet.PreimagePushout.boundaryToOld,
            SSet.PreimagePushout.boundaryToCell, Category.assoc]
      · simp
      · simp
    · let _ : Mono f := hfm
      exact SSet.PreimagePushout.isPushout sq r
  have hout := weak_right_of_pushout_either_mono hpo hbf hmono
  have hfac : (pullback.fst r g) ≫ (𝟙 _) =
      (apexPreimageIso q g u).hom ≫ ordinaryMap g q u := by
    apply pullback.hom_ext <;>
      simp [ordinaryMap, apexPreimageIso, r, Category.assoc, pullback.condition]
  let _ := hout
  have hcomp : WeakEquivalence ((apexPreimageIso q g u).hom ≫ ordinaryMap g q u) := by
    rw [← hfac]
    infer_instance
  let _ := hcomp
  exact weakEquivalence_of_precomp
    (apexPreimageIso q g u).hom (ordinaryMap g q u)

/-- Full Rezk8.3 conclusion on the same original scalar maps; no base Kan. -/
theorem sharp_mono_gluing {X Y X' Y' A B : SSet.{u}}
    {i : X ⟶ Y} {f : X ⟶ X'} {g : Y ⟶ Y'} {j : X' ⟶ Y'}
    (sq : IsPushout i f g j) (p : X' ⟶ A) (q : Y' ⟶ B) (a : A ⟶ B)
    (h : p ≫ a = j ≫ q) (hf : WeakEquivalence f)
    (hm : Mono i ∨ Mono f)
    (hp : Sharp p) (hfp : Sharp (f ≫ p)) (hqg : Sharp (g ≫ q)) : Sharp q := by
  intro U u
  have hg := weak_right_of_pushout_either_mono sq hf hm
  let η := cospanMap g q u
  have hη (k : WalkingCospan) : WeakEquivalence (η.app k) := by
    cases k with
    | none => change WeakEquivalence (𝟙 B); infer_instance
    | some a =>
      cases a with
      | left => change WeakEquivalence g; exact hg
      | right => change WeakEquivalence (𝟙 U); infer_instance
  have hhp := HomotopicalAlgebra.homotopyPullback_map_weakEquivalence η hη
  have hrow := hqg U u
  have hordinary := ordinaryMap_g_weak sq p q a h u hf hm hp hfp
  let _ := hrow
  let _ := hhp
  have hfac : ordinaryMap g q u ≫ comparison q u = comparison (g ≫ q) u ≫
      (HomotopicalAlgebra.homotopyPullback (C := SSet.{u})).map η := by
    rw [ordinaryMap_eq_limMap]
    exact (HomotopicalAlgebra.homotopyPullbackComparison (C := SSet.{u})).naturality η
  have hcomp : WeakEquivalence (ordinaryMap g q u ≫ comparison q u) := by
    rw [hfac]
    infer_instance
  let _ := hordinary
  let _ := hcomp
  exact weakEquivalence_of_precomp (ordinaryMap g q u) (comparison q u)

end SSet.SharpComparisonDraft
