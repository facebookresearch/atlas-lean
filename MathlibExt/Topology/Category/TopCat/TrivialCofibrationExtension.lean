/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import MathlibExt.Topology.Category.TopCat.PathModelCategory
public import MathlibExt.Topology.Category.TopCat.HomotopyExtension
public import MathlibExt.Topology.Category.TopCat.HomotopyFiberHomotopySquare
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Realization.ContinuousWhitehead

/-!
# Actual extensions and relative homotopies along a trivial cofibration

The selected TopCat model structure and its actual compact-open path object
produce extensions and homotopies fixed on the entire original source.
The input is a genuine trivial cofibration. In a plus mapping application,
its weak equivalence must first be derived from the actual pushout's
coefficient and fundamental-group maps.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped TopCat.modelCategory

universe u

namespace TopCat

private def homotopyOfPathFamily
    {B H : TopCat.{u}} (l : B ⟶ pathObject H) (f g : B ⟶ H)
    (h₀ : l ≫ pathEvalZero H = f) (h₁ : l ≫ pathEvalOne H = g) :
    TopCat.Homotopy f g where
  toFun z := l.hom z.2 ((TopCat.I.homeomorph.{u}).symm z.1)
  continuous_toFun := continuous_eval.comp
    ((l.hom.continuous.comp continuous_snd).prodMk
      ((TopCat.I.homeomorph.{u}).symm.continuous.comp continuous_fst))
  map_zero_left b := by
    have ht : (TopCat.I.homeomorph.{u}).symm (0 : unitInterval) =
        (0 : TopCat.I.{u}) := by
      apply (TopCat.I.homeomorph.{u}).injective
      simp
    exact (congrArg (fun t : TopCat.I.{u} => l.hom b t) ht).trans
      (ConcreteCategory.congr_hom h₀ b)
  map_one_left b := by
    have ht : (TopCat.I.homeomorph.{u}).symm (1 : unitInterval) =
        (1 : TopCat.I.{u}) := by
      apply (TopCat.I.homeomorph.{u}).injective
      simp
    exact (congrArg (fun t : TopCat.I.{u} => l.hom b t) ht).trans
      (ConcreteCategory.congr_hom h₁ b)


/-- A map into any actual topological target extends strictly along a
trivial cofibration. Fibrancy of the target is derived internally. -/
public theorem exists_extension_of_trivialCofibration
    {A B H : TopCat.{u}} (j : A ⟶ B) [Cofibration j] [WeakEquivalence j]
    (f : A ⟶ H) : ∃ g : B ⟶ H, j ≫ g = f := by
  let : IsFibrant H := SSet.RealizationCWUpgrade.allTopCatObjectsFibrant H
  let : Fibration (terminal.from H) := (isFibrant_iff H).mp inferInstance
  let sq : CommSq f j (terminal.from H) (terminal.from B) :=
    ⟨terminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- Equal restrictions along a trivial cofibration give an actual
continuous homotopy fixed at every point of its whole source image. -/
public theorem homotopyRel_of_trivialCofibration
    {A B H : TopCat.{u}} (j : A ⟶ B) [Cofibration j] [WeakEquivalence j]
    (r₀ r₁ : B ⟶ H) (h : j ≫ r₀ = j ≫ r₁) :
    Nonempty (ContinuousMap.HomotopyRel r₀.hom r₁.hom (Set.range j)) := by
  let : Fibration (pathEndpoints H) := modelCategory.pathEndpoints_fibration H
  let top : A ⟶ pathObject H := (j ≫ r₀) ≫ pathConstant H
  let sq : CommSq top j (pathEndpoints H) (prod.lift r₀ r₁) := ⟨by
    apply prod.hom_ext
    · simp [top, pathEndpoints, Category.assoc]
    · simpa [top, pathEndpoints, Category.assoc] using h⟩
  let l : B ⟶ pathObject H := sq.lift
  have h₀ : l ≫ pathEvalZero H = r₀ := by
    have he := congrArg (fun k => k ≫ (prod.fst : H ⨯ H ⟶ H)) sq.fac_right
    simpa only [l, Category.assoc, pathEndpoints, prod.lift_fst] using he
  have h₁ : l ≫ pathEvalOne H = r₁ := by
    have he := congrArg (fun k => k ≫ (prod.snd : H ⨯ H ⟶ H)) sq.fac_right
    simpa only [l, Category.assoc, pathEndpoints, prod.lift_snd] using he
  refine ⟨{ toHomotopy := homotopyOfPathFamily l r₀ r₁ h₀ h₁, prop' := ?_ }⟩
  intro t b hb
  change l.hom b ((TopCat.I.homeomorph.{u}).symm t) = r₀.hom b
  obtain ⟨a, rfl⟩ := hb
  have he := ConcreteCategory.congr_hom sq.fac_left a
  change l.hom (j.hom a) = (pathConstant H).hom (r₀.hom (j.hom a)) at he
  exact congrArg
    (fun γ : C(TopCat.I.{u}, H) => γ ((TopCat.I.homeomorph.{u}).symm t)) he

/-- A genuine trivial right leg of the actual pushout gives a strict
factorization and relative uniqueness on the original source image.
No retraction, extension or relative-homotopy witness is supplied. -/
public theorem exists_pushout_extension_of_trivialCofibration
    {X A H : TopCat.{u}} (i : X ⟶ A) (f : X ⟶ H)
    [Cofibration (pushout.inr i f)] [WeakEquivalence (pushout.inr i f)] :
    ∃ F : A ⟶ H, i ≫ F = f ∧
      ∀ G : A ⟶ H, i ≫ G = f →
        Nonempty (ContinuousMap.HomotopyRel F.hom G.hom (Set.range i)) := by
  let a := pushout.inl i f
  let j := pushout.inr i f
  obtain ⟨r, hr⟩ := exists_extension_of_trivialCofibration j (𝟙 H)
  let F : A ⟶ H := a ≫ r
  have hF : i ≫ F = f := by
    calc
      i ≫ (a ≫ r) = (i ≫ a) ≫ r := (Category.assoc _ _ _).symm
      _ = (f ≫ j) ≫ r := congrArg (fun k => k ≫ r) (pushout.condition (f := i) (g := f))
      _ = f := by rw [Category.assoc, hr, Category.comp_id]
  refine ⟨F, hF, ?_⟩
  intro G hG
  let rG : pushout i f ⟶ H :=
    pushout.desc G (𝟙 H) (hG.trans (Category.comp_id f).symm)
  have hrG : j ≫ rG = 𝟙 H := pushout.inr_desc _ _ _
  have haG : a ≫ rG = G := pushout.inl_desc _ _ _
  obtain ⟨K⟩ := homotopyRel_of_trivialCofibration j r rG (hr.trans hrG.symm)
  refine ⟨{
    toFun := fun z => K (z.1, a.hom z.2)
    continuous_toFun := K.continuous_toFun.comp
      (continuous_fst.prodMk (a.hom.continuous.comp continuous_snd))
    map_zero_left := fun z => K.map_zero_left (a.hom z)
    map_one_left := fun z => (K.map_one_left (a.hom z)).trans
      (ConcreteCategory.congr_hom haG z)
    prop' := ?_ }⟩
  intro t z hz
  obtain ⟨x, rfl⟩ := hz
  have hp := ConcreteCategory.congr_hom (pushout.condition (f := i) (g := f)) x
  change a.hom (i.hom x) = j.hom (f.hom x) at hp
  exact K.eq_fst t ⟨f.hom x, hp.symm⟩

/-- Every cofibration in the selected model structure belongs to the
existing Hurewicz morphism property. The lift produces the standard raw
`Topology.HomotopyExtensionData` for every compatible source family. -/
public theorem cofibrations_le_hurewiczCofibrations :
    cofibrations TopCat.{u} ≤ hurewiczCofibrations := by
  intro A B i hi
  let : Cofibration i := (cofibration_iff i).mpr hi
  intro T _ f h h0
  let Y : TopCat.{u} := TopCat.of T
  let fB : B ⟶ Y := TopCat.ofHom f
  let gA : A ⟶ Y := TopCat.ofHom
    { toFun := fun a => h (1, a)
      continuous_toFun := h.continuous.comp (continuous_const.prodMk continuous_id) }
  let K : TopCat.Homotopy (i ≫ fB) gA :=
    { toFun := h
      continuous_toFun := h.continuous
      map_zero_left := h0
      map_one_left := fun _ => rfl }
  have ht := pathEvalZero_trivialFibration Y
  let : Fibration (pathEvalZero Y) := (fibration_iff _).mpr ht.1
  let : WeakEquivalence (pathEvalZero Y) := (weakEquivalence_iff _).mpr ht.2
  let p : A ⟶ pathObject Y := TopCat.ofHom K.h.hom.curry
  have hp₀ : p ≫ pathEvalZero Y = i ≫ fB := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro a
    change K.h.hom (a, (0 : TopCat.I.{u})) = (i ≫ fB).hom a
    have hK : K.h.hom (a, (0 : TopCat.I.{u})) =
        K (TopCat.I.homeomorph (0 : TopCat.I.{u}), a) :=
      TopCat.Homotopy.h_hom_apply K (a, (0 : TopCat.I.{u}))
    exact hK.trans
      ((congrArg (fun t => K (t, a)) TopCat.I.homeomorph_zero.{u}).trans (K.map_zero_left a))
  let sq : CommSq p i (pathEvalZero Y) fB := ⟨hp₀⟩
  let l : B ⟶ pathObject Y := sq.lift
  let gB : B ⟶ Y := l ≫ pathEvalOne Y
  let L : TopCat.Homotopy fB gB := homotopyOfPathFamily l fB gB sq.fac_right rfl
  refine ⟨{ extension := L.toContinuousMap
            extension_zero := ?_
            extension_subspace := ?_ }⟩
  · exact L.map_zero_left
  · intro t a
    change l.hom (i.hom a) ((TopCat.I.homeomorph.{u}).symm t) = h (t, a)
    have hs := ConcreteCategory.congr_hom sq.fac_left a
    change l.hom (i.hom a) = p.hom a at hs
    calc
      l.hom (i.hom a) ((TopCat.I.homeomorph.{u}).symm t) =
          p.hom a ((TopCat.I.homeomorph.{u}).symm t) :=
        congrArg (fun γ : C(TopCat.I.{u}, Y) =>
          γ ((TopCat.I.homeomorph.{u}).symm t)) hs
      _ = K (TopCat.I.homeomorph ((TopCat.I.homeomorph.{u}).symm t), a) :=
        TopCat.Homotopy.h_hom_apply K (a, (TopCat.I.homeomorph.{u}).symm t)
      _ = K (t, a) := congrArg (fun s => K (s, a))
        ((TopCat.I.homeomorph.{u}).apply_symm_apply t)
      _ = h (t, a) := rfl

/-- A genuine cofibration extends an original source homotopy into any
topological target. This convenience statement is derived from the existing
Hurewicz property and its chosen `HomotopyExtensionData`. -/
public theorem exists_homotopyExtension_of_cofibration
    {A B H : TopCat.{u}} (i : A ⟶ B) [Cofibration i]
    (f : B ⟶ H) (g : A ⟶ H) (K : TopCat.Homotopy (i ≫ f) g) :
    ∃ gB : B ⟶ H, ∃ L : TopCat.Homotopy f gB,
      i ≫ gB = g ∧ ∀ t : unitInterval, ∀ a : A, L (t, i a) = K (t, a) := by
  exact exists_homotopyExtension_of_hurewicz i
    (cofibrations_le_hurewiczCofibrations i (mem_cofibrations i)) f g K

end TopCat

namespace TopCat

/-- Extend an actual source-relative homotopy along a genuine cofibration.
The lifted family is fixed on the image of the original fixed subset and
still agrees with the original source family at every point and time. -/
public theorem exists_homotopyExtensionRel_of_cofibration
    {A B H : TopCat.{u}} (i : A ⟶ B) [Cofibration i] (S : Set A)
    (f : B ⟶ H) (g : A ⟶ H)
    (K : ContinuousMap.HomotopyRel (i ≫ f).hom g.hom S) :
    ∃ gB : B ⟶ H, ∃ L : ContinuousMap.HomotopyRel f.hom gB.hom (i '' S),
      i ≫ gB = g ∧ ∀ t : unitInterval, ∀ a : A, L (t, i a) = K (t, a) := by
  obtain ⟨gB, L, hgB, hL⟩ :=
    exists_homotopyExtension_of_cofibration i f g K.toHomotopy
  let LR : ContinuousMap.HomotopyRel f.hom gB.hom (i '' S) :=
    { toHomotopy := L
      prop' := by
        intro t b hb
        obtain ⟨a, ha, rfl⟩ := hb
        exact (hL t a).trans (K.eq_fst t ha) }
  exact ⟨gB, LR, hgB, hL⟩

end TopCat

end
