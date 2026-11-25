/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenRightMateHomotopyClasses

/-!
# Genuine weak recognition of original Quillen right mates

Actual model homotopy classes and the original adjunction Hom
equivalences supply the right-mate comparison. The weak recognition
step uses actual original homotopy inverse maps, constructed from those
class bijections, genuine factorization/lifting and retract closure. No weak
mate, derived adjunction or Quillen equivalence outcome is assumed.
-/

noncomputable section
universe u v u₁ u₂ v₁ v₂
open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopicalAlgebra

/-- Both actual model homotopy inverse equations make the SAME original map weak from a cofibrant
source to a bifibrant
target. -/
theorem weakEquivalence_of_rightHomotopyInverse {C : Type u} [Category.{v} C] [ModelCategory C]
    {X Y : C} [IsCofibrant X] [IsCofibrant Y] [IsFibrant Y]
    (f : X ⟶ Y) (g : Y ⟶ X) (hfg : RightHomotopyRel (f ≫ g) (𝟙 X))
    (hgf : RightHomotopyRel (g ≫ f) (𝟙 Y)) : WeakEquivalence f := by
  let d := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C) f
  let _ : Cofibration d.i := (cofibration_iff _).mpr d.hi.1
  let _ : WeakEquivalence d.i := (weakEquivalence_iff _).mpr d.hi.2
  let _ : Fibration d.p := (fibration_iff _).mpr d.hp
  let _ : IsCofibrant d.Z := isCofibrant_of_cofibration d.i
  let _ : IsFibrant d.Z := isFibrant_of_fibration d.p
  let g₀ : Y ⟶ d.Z := g ≫ d.i
  have hg₀ : RightHomotopyRel (g₀ ≫ d.p) (𝟙 Y) := by
    simpa only [g₀, Category.assoc, d.fac] using hgf
  have hp₀ : RightHomotopyRel (d.p ≫ g₀) (𝟙 d.Z) := by
    apply (RightHomotopyClass.mk_eq_mk_iff (d.p ≫ g₀) (𝟙 d.Z)).mp
    apply (RightHomotopyClass.precomp_bijective_of_weakEquivalence d.Z d.i).injective
    simpa only [RightHomotopyClass.precomp_mk, g₀, ← d.fac, Category.assoc,
      Category.id_comp, Category.comp_id] using RightHomotopyClass.sound (hfg.postcomp d.i)
  have hL : LeftHomotopyRel (g₀ ≫ d.p) (𝟙 Y) := leftHomotopyRel_iff_rightHomotopyRel.mpr hg₀
  obtain ⟨P, hP, ⟨h⟩⟩ := hL.exists_good_cylinder
  let _ : P.IsGood := hP
  obtain ⟨s, hs, hsp⟩ := h.covering_homotopy d.p g₀ rfl
  have hsP : s ≫ d.p = 𝟙 Y :=
    (congrArg (fun h => h ≫ d.p) hs.h₁.symm).trans
      ((Category.assoc _ _ _).trans ((congrArg (fun h => P.i₁ ≫ h) hsp).trans h.h₁))
  have hgs : RightHomotopyRel g₀ s := leftHomotopyRel_iff_rightHomotopyRel.mp hs.leftHomotopyRel
  have hps : RightHomotopyRel (d.p ≫ s) (𝟙 d.Z) := (hgs.precomp d.p).symm.trans hp₀
  obtain ⟨Q, ⟨hq⟩⟩ := hps
  have hw : WeakEquivalence (d.p ≫ s) := hq.weakEquivalence_iff.mpr inferInstance
  let r : RetractArrow d.p (d.p ≫ s) :=
    { i := Arrow.homMk (𝟙 d.Z) s (by simp)
      r := Arrow.homMk (𝟙 d.Z) d.p (by
        change (𝟙 d.Z) ≫ d.p = (d.p ≫ s) ≫ d.p
        rw [Category.id_comp, Category.assoc, hsP, Category.comp_id])
      retract := by
        apply Arrow.hom_ext
        · exact Category.id_comp _
        · exact hsP }
  let _ : WeakEquivalence d.p := (weakEquivalence_iff _).mpr
    (MorphismProperty.of_retract r ((weakEquivalence_iff _).mp hw))
  rw [← d.fac]
  infer_instance

end HomotopicalAlgebra

namespace CategoryTheory.Adjunction.IsQuillenAdjunction

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
    {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) [IsQuillenAdjunction adj₁] [IsQuillenAdjunction adj₂]

/-- A genuine weak left comparison makes its SAME original canonical right mate weak at fibrant
targets whose two
right-adjoint images are cofibrant. The inverse and both homotopies are constructed from actual
Quillen transposition
and weak-left precomposition. -/
theorem weakEquivalence_conjugate_app (α : L₁ ⟶ L₂)
    (hα : ∀ (X : C) [IsCofibrant X], WeakEquivalence (α.app X))
    (F : D) [IsFibrant F] [IsCofibrant (R₁.obj F)] [IsCofibrant (R₂.obj F)] :
    WeakEquivalence ((conjugateEquiv adj₂ adj₁ α).app F) := by
  let _ : IsFibrant (R₁.obj F) := preservesFibrantObjects (adj := adj₁) inferInstance
  let _ : IsFibrant (R₂.obj F) := preservesFibrantObjects (adj := adj₂) inferInstance
  let β := (conjugateEquiv adj₂ adj₁ α).app F
  have h₁ := rightMate_postcomp_rightHomotopyClass_bijective adj₁ adj₂ α hα (R₁.obj F) F
  obtain ⟨g, hg⟩ := h₁.surjective (RightHomotopyClass.mk (𝟙 (R₁.obj F)))
  obtain ⟨g, rfl⟩ := g.mk_surjective
  have hgβ : RightHomotopyRel (g ≫ β) (𝟙 (R₁.obj F)) := by
    apply (RightHomotopyClass.mk_eq_mk_iff _ _).mp
    exact hg
  have h₂ := rightMate_postcomp_rightHomotopyClass_bijective adj₁ adj₂ α hα (R₂.obj F) F
  have hβg : RightHomotopyRel (β ≫ g) (𝟙 (R₂.obj F)) := by
    apply (RightHomotopyClass.mk_eq_mk_iff _ _).mp
    apply h₂.injective
    change RightHomotopyClass.mk ((β ≫ g) ≫ β) =
      RightHomotopyClass.mk ((𝟙 (R₂.obj F)) ≫ β)
    apply RightHomotopyClass.sound
    simpa only [Category.assoc, Category.comp_id, Category.id_comp] using hgβ.precomp β
  exact weakEquivalence_of_rightHomotopyInverse β g hβg hgβ

end CategoryTheory.Adjunction.IsQuillenAdjunction
