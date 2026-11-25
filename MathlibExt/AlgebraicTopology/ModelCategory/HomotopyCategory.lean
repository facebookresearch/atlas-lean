/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.ModelCategory.FundamentalLemma

/-!
# Saturation of weak equivalences in a model category

A morphism is a weak equivalence if and only if it becomes an isomorphism in any
localization at the weak equivalences. In particular this applies to the canonical
localization `(weakEquivalences C).Q`.

The original Formal-Math development is by Tsutomu Okano and Avocado.
-/

open CategoryTheory MorphismProperty

namespace HomotopicalAlgebra

universe u v u' v'

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {H : Type u'} [Category.{v'} H] (L : C ⥤ H) [L.IsLocalization (weakEquivalences C)]

private theorem weakEquivalence_of_isIso_map_of_fibration
    {X Y : C} [IsCofibrant X] [IsFibrant X] [IsCofibrant Y] [IsFibrant Y]
    (p : X ⟶ Y) [Fibration p] [IsIso (L.map p)] : WeakEquivalence p := by
  obtain ⟨g, hg⟩ := map_surjective_of_isLocalization L Y X (inv (L.map p))
  have h : LeftHomotopyRel (g ≫ p) (𝟙 Y) := by
    rw [LeftHomotopyRel.iff_map_eq L, L.map_comp, L.map_id, hg, IsIso.inv_hom_id]
  obtain ⟨P, hP, ⟨lift⟩⟩ := h.exists_good_cylinder
  have : P.IsGood := hP
  obtain ⟨s, homotopy, hLift⟩ := lift.covering_homotopy p g
  have hs : s ≫ p = 𝟙 Y := by
    calc
      s ≫ p = (P.i₁ ≫ homotopy.h) ≫ p := by rw [homotopy.h₁]
      _ = P.i₁ ≫ lift.h := by rw [Category.assoc, hLift]
      _ = 𝟙 Y := lift.h₁
  have hs' : LeftHomotopyRel (p ≫ s) (𝟙 X) := by
    rw [LeftHomotopyRel.iff_map_eq L]
    apply (cancel_mono (L.map p)).1
    rw [L.map_id, Category.id_comp, ← L.map_comp, Category.assoc, hs, Category.comp_id]
  obtain ⟨_, ⟨homotopy'⟩⟩ := hs'
  have : WeakEquivalence (p ≫ s) := homotopy'.weakEquivalence_iff.mpr inferInstance
  -- The strict section makes `p` a retract of the map homotopic to the identity.
  have retract : RetractArrow p (p ≫ s) :=
    { i := Arrow.homMk (𝟙 _) s (by simp)
      r := Arrow.homMk (𝟙 _) p (by simp [Category.assoc, hs])
      retract := by ext <;> simp [hs] }
  exact (weakEquivalence_iff _).mpr ((weakEquivalences C).of_retract retract WeakEquivalence.mem)

private theorem weakEquivalence_of_isIso_map_of_bifibrant
    {X Y : C} [IsCofibrant X] [IsFibrant X] [IsCofibrant Y] [IsFibrant Y]
    (f : X ⟶ Y) [IsIso (L.map f)] : WeakEquivalence f := by
  let d := factorizationData (trivialCofibrations C) (fibrations C) f
  have : Cofibration d.i := (cofibration_iff _).mpr d.hi.1
  have : WeakEquivalence d.i := (weakEquivalence_iff _).mpr d.hi.2
  have : Fibration d.p := (fibration_iff _).mpr d.hp
  have : IsCofibrant d.Z := isCofibrant_of_cofibration d.i
  have : IsFibrant d.Z := isFibrant_of_fibration d.p
  have : IsIso (L.map d.i) := Localization.inverts L (weakEquivalences C) d.i d.hi.2
  have : IsIso (L.map d.p) := IsIso.of_isIso_fac_left (by rw [← L.map_comp, d.fac]
    : L.map d.i ≫ L.map d.p = L.map f)
  have : WeakEquivalence d.p := weakEquivalence_of_isIso_map_of_fibration L d.p
  rw [← d.fac]
  infer_instance

/-- The weak equivalences of a model category are exactly the maps inverted by any
localization at the weak equivalences. No cofibrancy or fibrancy assumptions on
the endpoints of `f` are needed. -/
public theorem weakEquivalence_iff_isIso_map_of_isLocalization
    {X Y : C} (f : X ⟶ Y) : weakEquivalences C f ↔ IsIso (L.map f) := by
  refine ⟨Localization.inverts L (weakEquivalences C) f, fun h ↦ ?_⟩
  let qf := CofibrantObject.HoCat.resolutionMap f
  let pX := CofibrantObject.HoCat.pResolutionObj X
  let pY := CofibrantObject.HoCat.pResolutionObj Y
  have : IsIso (L.map pX) := Localization.inverts L _ pX (mem_weakEquivalences _)
  have : IsIso (L.map pY) := Localization.inverts L _ pY (mem_weakEquivalences _)
  have hqf : L.map qf ≫ L.map pY = L.map pX ≫ L.map f := by
    simpa only [← L.map_comp] using L.congr_map (CofibrantObject.HoCat.resolutionMap_fac f)
  have : IsIso (L.map qf) := IsIso.of_isIso_fac_right hqf
  let rf := FibrantObject.HoCat.resolutionMap qf
  let iX := FibrantObject.HoCat.iResolutionObj (CofibrantObject.HoCat.resolutionObj X)
  let iY := FibrantObject.HoCat.iResolutionObj (CofibrantObject.HoCat.resolutionObj Y)
  have : IsIso (L.map iX) := Localization.inverts L _ iX (mem_weakEquivalences _)
  have : IsIso (L.map iY) := Localization.inverts L _ iY (mem_weakEquivalences _)
  have hrf : L.map iX ≫ L.map rf = L.map qf ≫ L.map iY := by
    simpa only [← L.map_comp] using L.congr_map (FibrantObject.HoCat.resolutionMap_fac qf)
  have : IsIso (L.map rf) := IsIso.of_isIso_fac_left hrf
  have hrfWeak : WeakEquivalence rf := weakEquivalence_of_isIso_map_of_bifibrant L rf
  exact (weakEquivalence_iff f).mp ((CofibrantObject.HoCat.weakEquivalence_resolutionMap_iff f).mp
    ((FibrantObject.HoCat.weakEquivalence_resolutionMap_iff qf).mp hrfWeak))

end HomotopicalAlgebra
