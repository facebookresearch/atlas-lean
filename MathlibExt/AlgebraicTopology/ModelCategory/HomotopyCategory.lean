/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Avocado
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.ModelCategory.FundamentalLemma

/-!
# The homotopy category of a model category

This file gives convenient names to the existing localization of a model
category at its weak equivalences and compares it with Mathlib's homotopy
category of bifibrant objects.  It also proves that every model of this
localization detects exactly the weak equivalences.
-/

@[expose] public section

noncomputable section

universe v v' u u'

open CategoryTheory MorphismProperty

namespace HomotopicalAlgebra

/-- The localization of a model category at its weak equivalences. -/
abbrev HomotopyCategory (C : Type u) [Category.{v} C] [ModelCategory C] :=
  (weakEquivalences C).Localization

/-- The canonical functor from a model category to its homotopy category. -/
abbrev toHomotopyCategory (C : Type u) [Category.{v} C] [ModelCategory C] :
    C ⥤ HomotopyCategory C :=
  (weakEquivalences C).Q

namespace BifibrantObject.HoCat

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- The bifibrant homotopy quotient is equivalent to the localization of the
model category at its weak equivalences. -/
noncomputable def equivalenceHomotopyCategory :
    BifibrantObject.HoCat C ≌ HomotopyCategory C :=
  Localization.uniq BifibrantObject.toHoCat
    (BifibrantObject.ι ⋙ toHomotopyCategory C)
    (weakEquivalences (BifibrantObject C))

/-- Compatibility of the bifibrant quotient functor with the canonical
localization functor. -/
def toHoCatCompEquivalenceHomotopyCategory :
    BifibrantObject.toHoCat ⋙
        (equivalenceHomotopyCategory (C := C)).functor ≅
      BifibrantObject.ι ⋙ toHomotopyCategory C :=
  Localization.compUniqFunctor BifibrantObject.toHoCat
    (BifibrantObject.ι ⋙ toHomotopyCategory C)
    (weakEquivalences (BifibrantObject C))

end BifibrantObject.HoCat

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- The fundamental lemma of homotopical algebra, packaged as an equivalence
between left homotopy classes and morphisms in any localization at the weak
equivalences. -/
noncomputable def leftHomotopyClassEquivOfIsLocalization
    {H : Type u'} [Category.{v'} H]
    (L : C ⥤ H) [L.IsLocalization (weakEquivalences C)]
    {X Y : C} [IsCofibrant X] [IsFibrant Y] :
    LeftHomotopyClass X Y ≃ (L.obj X ⟶ L.obj Y) :=
  Equiv.ofBijective (leftHomotopyClassToHom L)
    (bijective_leftHomotopyClassToHom L X Y)

@[simp]
lemma leftHomotopyClassEquivOfIsLocalization_mk
    {H : Type u'} [Category.{v'} H]
    (L : C ⥤ H) [L.IsLocalization (weakEquivalences C)]
    {X Y : C} [IsCofibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    leftHomotopyClassEquivOfIsLocalization L (.mk f) = L.map f :=
  leftHomotopyClassToHom_mk L f

private lemma weakEquivalence_of_leftHomotopyInverse
    {A B : C} [IsCofibrant A] [IsFibrant A]
    [IsCofibrant B] [IsFibrant B]
    (f : A ⟶ B) (g : B ⟶ A)
    (hfg : LeftHomotopyRel (f ≫ g) (𝟙 A))
    (hgf : LeftHomotopyRel (g ≫ f) (𝟙 B)) :
    WeakEquivalence f := by
  let d := factorizationData (trivialCofibrations C) (fibrations C) f
  let _ : Cofibration d.i := by
    rw [cofibration_iff]
    exact d.hi.1
  let _ : WeakEquivalence d.i := by
    rw [weakEquivalence_iff]
    exact d.hi.2
  let _ : Fibration d.p := by
    rw [fibration_iff]
    exact d.hp
  let _ : IsCofibrant d.Z := isCofibrant_of_cofibration d.i
  let _ : IsFibrant d.Z := isFibrant_of_fibration d.p
  obtain ⟨r, _, hri⟩ := LeftHomotopyClass.whitehead d.i
  obtain ⟨P, hP, ⟨H⟩⟩ := hgf.exists_good_cylinder
  let _ : P.IsGood := hP
  obtain ⟨q, Hq, hHq⟩ :=
    H.covering_homotopy d.p (g ≫ d.i) (by rw [Category.assoc, d.fac])
  have hqp : q ≫ d.p = 𝟙 B := by
    calc
      q ≫ d.p = (P.i₁ ≫ Hq.h) ≫ d.p := by rw [Hq.h₁]
      _ = P.i₁ ≫ (Hq.h ≫ d.p) := Category.assoc _ _ _
      _ = P.i₁ ≫ H.h := by rw [hHq]
      _ = 𝟙 B := H.h₁
  have h₁ : LeftHomotopyRel (d.p ≫ q) (d.p ≫ (g ≫ d.i)) :=
    (Hq.leftHomotopyRel.precomp d.p).symm
  have h₂ : LeftHomotopyRel (d.p ≫ (g ≫ d.i))
      ((r ≫ f) ≫ (g ≫ d.i)) := by
    simpa only [Category.id_comp, Category.comp_id, Category.assoc, d.fac] using
      ((hri.postcomp d.p).symm.postcomp (g ≫ d.i))
  have h₃ : LeftHomotopyRel ((r ≫ f) ≫ (g ≫ d.i)) (r ≫ d.i) := by
    simpa only [Category.comp_id, Category.assoc] using
      ((hfg.precomp r).postcomp d.i)
  have hpq : LeftHomotopyRel (d.p ≫ q) (𝟙 d.Z) :=
    ((h₁.trans h₂).trans h₃).trans hri
  obtain ⟨P', ⟨Hpq⟩⟩ := hpq
  let _ : WeakEquivalence (d.p ≫ q) :=
    (Hpq.weakEquivalence_iff).2 inferInstance
  have hr : RetractArrow d.p (d.p ≫ q) :=
    { i := Arrow.homMk (𝟙 _) q (by simp)
      r := Arrow.homMk (𝟙 _) d.p (by simp [Category.assoc, hqp])
      retract := by ext <;> simp [hqp] }
  have hp : weakEquivalences C d.p :=
    (weakEquivalences C).of_retract hr WeakEquivalence.mem
  let _ : WeakEquivalence d.p := (weakEquivalence_iff d.p).2 hp
  rw [← d.fac]
  infer_instance

/-- Weak equivalences in a model category are exactly the maps inverted by
any localization at the weak equivalences. -/
theorem weakEquivalence_iff_isIso_map_of_isLocalization
    {H : Type u'} [Category.{v'} H]
    (L : C ⥤ H) [L.IsLocalization (weakEquivalences C)]
    {X Y : C} (f : X ⟶ Y) :
    weakEquivalences C f ↔ IsIso (L.map f) := by
  constructor
  · intro hf
    exact Localization.inverts L (weakEquivalences C) f hf
  · intro hf
    let _ : IsIso (L.map f) := hf
    let qf := CofibrantObject.HoCat.resolutionMap f
    let pX := CofibrantObject.HoCat.pResolutionObj X
    let pY := CofibrantObject.HoCat.pResolutionObj Y
    let _ : IsIso (L.map pX) :=
      Localization.inverts L (weakEquivalences C) pX (by
        rw [← weakEquivalence_iff]
        infer_instance)
    let _ : IsIso (L.map pY) :=
      Localization.inverts L (weakEquivalences C) pY (by
        rw [← weakEquivalence_iff]
        infer_instance)
    have hqf : L.map qf ≫ L.map pY = L.map pX ≫ L.map f := by
      simpa only [qf, pX, pY, ← L.map_comp] using
        L.congr_map (CofibrantObject.HoCat.resolutionMap_fac f)
    let _ : IsIso (L.map qf) := IsIso.of_isIso_fac_right hqf
    let rf := FibrantObject.HoCat.resolutionMap qf
    let iX := FibrantObject.HoCat.iResolutionObj
      (CofibrantObject.HoCat.resolutionObj X)
    let iY := FibrantObject.HoCat.iResolutionObj
      (CofibrantObject.HoCat.resolutionObj Y)
    let _ : IsIso (L.map iX) :=
      Localization.inverts L (weakEquivalences C) iX (by
        rw [← weakEquivalence_iff]
        infer_instance)
    let _ : IsIso (L.map iY) :=
      Localization.inverts L (weakEquivalences C) iY (by
        rw [← weakEquivalence_iff]
        infer_instance)
    have hrf : L.map iX ≫ L.map rf = L.map qf ≫ L.map iY := by
      simpa only [rf, iX, iY, ← L.map_comp] using
        L.congr_map (FibrantObject.HoCat.resolutionMap_fac qf)
    let _ : IsIso (L.map rf) := IsIso.of_isIso_fac_left hrf
    obtain ⟨g, hg⟩ :=
      (map_surjective_of_isLocalization L
        (FibrantObject.HoCat.resolutionObj
          (CofibrantObject.HoCat.resolutionObj Y))
        (FibrantObject.HoCat.resolutionObj
          (CofibrantObject.HoCat.resolutionObj X)))
        (inv (L.map rf))
    have hfg : LeftHomotopyRel (rf ≫ g) (𝟙 _) := by
      rw [LeftHomotopyRel.iff_map_eq L]
      simp only [L.map_comp, hg, IsIso.hom_inv_id, L.map_id]
    have hgf : LeftHomotopyRel (g ≫ rf) (𝟙 _) := by
      rw [LeftHomotopyRel.iff_map_eq L]
      simp only [L.map_comp, hg, IsIso.inv_hom_id, L.map_id]
    let _ : WeakEquivalence rf :=
      weakEquivalence_of_leftHomotopyInverse rf g hfg hgf
    have hqf' : WeakEquivalence qf :=
      (FibrantObject.HoCat.weakEquivalence_resolutionMap_iff qf).1 inferInstance
    have hf' : WeakEquivalence f :=
      (CofibrantObject.HoCat.weakEquivalence_resolutionMap_iff f).1 hqf'
    exact hf'.mem

/-- The canonical homotopy-category functor detects weak equivalences. -/
theorem weakEquivalence_iff_isIso_toHomotopyCategory_map
    {X Y : C} (f : X ⟶ Y) :
    weakEquivalences C f ↔ IsIso ((toHomotopyCategory C).map f) :=
  weakEquivalence_iff_isIso_map_of_isLocalization (toHomotopyCategory C) f

end HomotopicalAlgebra
