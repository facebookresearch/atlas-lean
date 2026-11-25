/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.GivenFactorizationReplacements
import MathlibExt.CategoryTheory.MorphismProperty.FunctorialFactorizationEquivalence
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Transport of the whole given replacement data

The given original initial and terminal objects are mapped by the actual
equivalence. Their original universal properties supply the target endpoint
certificates. The full Arrow-family comparisons and the existing middle
counit then compare the two replacement functors on every object and map.
Both factors, including the original initial leg and terminal leg, are
preserved as whole natural transformations.
-/

set_option autoImplicit false
noncomputable section
universe uC vC uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.Functor

namespace HomotopicalAlgebra.GivenFactorizationReplacements

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- The original endpoint constant functor is transported by the actual stock comparison. -/
def endpointConstantComparisonIso (e : C ≌ D) (Z : C) :
    (Functor.const C).obj Z ⋙ e.functor ≅
      e.functor ⋙ (Functor.const D).obj (e.functor.obj Z) :=
  Functor.constComp C Z e.functor

/-- The actual mapped initial arrows compare by identity maps at both original endpoints. -/
def initialArrowsEquivalenceIso (e : C ≌ D) (Z : C) (hZ : IsInitial Z) :
    initialArrows Z hZ ⋙ e.functor.mapArrow ≅
      e.functor ⋙ initialArrows (e.functor.obj Z) (hZ.isInitialObj e.functor Z) :=
  NatIso.ofComponents (fun X =>
    Arrow.isoMk (Iso.refl _) (Iso.refl _)
      (by
        change 𝟙 (e.functor.obj Z) ≫
            (hZ.isInitialObj e.functor Z).to (e.functor.obj X) =
          e.functor.map (hZ.to X) ≫ 𝟙 (e.functor.obj X)
        simpa only [Category.id_comp, Category.comp_id] using
          (hZ.isInitialObj e.functor Z).hom_ext
            ((hZ.isInitialObj e.functor Z).to (e.functor.obj X)) (e.functor.map (hZ.to X))))
    (by
      intro X Y f
      apply Arrow.hom_ext
      · change e.functor.map (𝟙 Z) ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
        simp only [e.functor.map_id, Category.id_comp]
      · change e.functor.map f ≫ 𝟙 _ = 𝟙 _ ≫ e.functor.map f
        exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The terminal Arrow families retain the same entire source and mapped terminal endpoint. -/
def terminalArrowsEquivalenceIso (e : C ≌ D) (Z : C) (hZ : IsTerminal Z) :
    terminalArrows Z hZ ⋙ e.functor.mapArrow ≅
      e.functor ⋙ terminalArrows (e.functor.obj Z) (hZ.isTerminalObj e.functor Z) :=
  NatIso.ofComponents (fun X =>
    Arrow.isoMk (Iso.refl _) (Iso.refl _)
      (by
        change 𝟙 (e.functor.obj X) ≫
            (hZ.isTerminalObj e.functor Z).from (e.functor.obj X) =
          e.functor.map (hZ.from X) ≫ 𝟙 (e.functor.obj Z)
        simpa only [Category.id_comp, Category.comp_id] using
          (hZ.isTerminalObj e.functor Z).hom_ext
            ((hZ.isTerminalObj e.functor Z).from (e.functor.obj X))
            (e.functor.map (hZ.from X))))
    (by
      intro X Y f
      apply Arrow.hom_ext
      · change e.functor.map f ≫ 𝟙 _ = 𝟙 _ ≫ e.functor.map f
        exact (Category.comp_id _).trans (Category.id_comp _).symm
      · change e.functor.map (𝟙 Z) ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
        simp only [e.functor.map_id, Category.id_comp])

/-- All four maps of each original initial-arrow comparison are literal endpoint identities. -/
theorem initialArrowsEquivalenceIso_fields (e : C ≌ D) (Z : C) (hZ : IsInitial Z) (X : C) :
    ((initialArrowsEquivalenceIso e Z hZ).hom.app X).left = 𝟙 (e.functor.obj Z) ∧
      ((initialArrowsEquivalenceIso e Z hZ).hom.app X).right = 𝟙 (e.functor.obj X) ∧
      ((initialArrowsEquivalenceIso e Z hZ).inv.app X).left = 𝟙 (e.functor.obj Z) ∧
      ((initialArrowsEquivalenceIso e Z hZ).inv.app X).right = 𝟙 (e.functor.obj X) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Both directions of each terminal-arrow comparison retain the entire endpoint identities. -/
theorem terminalArrowsEquivalenceIso_fields (e : C ≌ D) (Z : C) (hZ : IsTerminal Z) (X : C) :
    ((terminalArrowsEquivalenceIso e Z hZ).hom.app X).left = 𝟙 (e.functor.obj X) ∧
      ((terminalArrowsEquivalenceIso e Z hZ).hom.app X).right = 𝟙 (e.functor.obj Z) ∧
      ((terminalArrowsEquivalenceIso e Z hZ).inv.app X).left = 𝟙 (e.functor.obj X) ∧
      ((terminalArrowsEquivalenceIso e Z hZ).inv.app X).right = 𝟙 (e.functor.obj Z) :=
  ⟨rfl, rfl, rfl, rfl⟩

variable {P Q : MorphismProperty D} [P.RespectsIso] [Q.RespectsIso]

/-- The whole given initial replacement is compared by its actual mapped Arrow and middle counit. -/
def initialReplacementEquivalenceIso (data : FunctorialFactorizationData P Q)
    (e : C ≌ D) (Z : C) (hZ : IsInitial Z) :
    initialReplacement (data.ofEquivalence e) Z hZ ⋙ e.functor ≅
      e.functor ⋙ initialReplacement data (e.functor.obj Z) (hZ.isInitialObj e.functor Z) :=
  isoWhiskerLeft (initialArrows Z hZ) (data.ofEquivalenceZComparisonIso e) ≪≫
    isoWhiskerRight (initialArrowsEquivalenceIso e Z hZ) data.Z

/-- The whole terminal replacement uses the same actual middle counit and terminal Arrow family. -/
def terminalReplacementEquivalenceIso (data : FunctorialFactorizationData P Q)
    (e : C ≌ D) (Z : C) (hZ : IsTerminal Z) :
    terminalReplacement (data.ofEquivalence e) Z hZ ⋙ e.functor ≅
      e.functor ⋙ terminalReplacement data (e.functor.obj Z) (hZ.isTerminalObj e.functor Z) :=
  isoWhiskerLeft (terminalArrows Z hZ) (data.ofEquivalenceZComparisonIso e) ≪≫
    isoWhiskerRight (terminalArrowsEquivalenceIso e Z hZ) data.Z

/-- Every forward initial comparison retains the original counit followed by the given Arrow map. -/
theorem initialReplacementEquivalenceIso_hom_app (data : FunctorialFactorizationData P Q)
    (e : C ≌ D) (Z : C) (hZ : IsInitial Z) (X : C) :
    (initialReplacementEquivalenceIso data e Z hZ).hom.app X =
      (data.ofEquivalenceZComparisonIso e).hom.app ((initialArrows Z hZ).obj X) ≫
        data.Z.map ((initialArrowsEquivalenceIso e Z hZ).hom.app X) := rfl

/-- The inverse initial function keeps the original inverse Arrow map and inverse middle counit. -/
theorem initialReplacementEquivalenceIso_inv_app (data : FunctorialFactorizationData P Q)
    (e : C ≌ D) (Z : C) (hZ : IsInitial Z) (X : C) :
    (initialReplacementEquivalenceIso data e Z hZ).inv.app X =
      data.Z.map ((initialArrowsEquivalenceIso e Z hZ).inv.app X) ≫
        (data.ofEquivalenceZComparisonIso e).inv.app ((initialArrows Z hZ).obj X) := rfl

/-- The forward terminal function keeps the actual counit and given terminal Arrow map. -/
theorem terminalReplacementEquivalenceIso_hom_app (data : FunctorialFactorizationData P Q)
    (e : C ≌ D) (Z : C) (hZ : IsTerminal Z) (X : C) :
    (terminalReplacementEquivalenceIso data e Z hZ).hom.app X =
      (data.ofEquivalenceZComparisonIso e).hom.app ((terminalArrows Z hZ).obj X) ≫
        data.Z.map ((terminalArrowsEquivalenceIso e Z hZ).hom.app X) := rfl

/-- The inverse terminal function retains the actual inverse terminal square and inverse counit. -/
theorem terminalReplacementEquivalenceIso_inv_app (data : FunctorialFactorizationData P Q)
    (e : C ≌ D) (Z : C) (hZ : IsTerminal Z) (X : C) :
    (terminalReplacementEquivalenceIso data e Z hZ).inv.app X =
      data.Z.map ((terminalArrowsEquivalenceIso e Z hZ).inv.app X) ≫
        (data.ofEquivalenceZComparisonIso e).inv.app ((terminalArrows Z hZ).obj X) := rfl

/-- The entire original initial leg is recovered through the same whole replacement comparison. -/
theorem initialReplacementEquivalenceIso_leg (data : FunctorialFactorizationData P Q)
    (e : C ≌ D) (Z : C) (hZ : IsInitial Z) (X : C) :
    e.functor.map ((initialLeg (data.ofEquivalence e) Z hZ).app X) ≫
        (initialReplacementEquivalenceIso data e Z hZ).hom.app X =
      (initialLeg data (e.functor.obj Z) (hZ.isInitialObj e.functor Z)).app (e.functor.obj X) := by
  change e.functor.map ((data.ofEquivalence e).i.app ((initialArrows Z hZ).obj X)) ≫
      ((data.ofEquivalenceZComparisonIso e).hom.app ((initialArrows Z hZ).obj X) ≫
        data.Z.map ((initialArrowsEquivalenceIso e Z hZ).hom.app X)) =
    data.i.app ((e.functor ⋙ initialArrows (e.functor.obj Z)
      (hZ.isInitialObj e.functor Z)).obj X)
  rw [← Category.assoc, data.ofEquivalence_mapped_i]
  exact (data.i.naturality ((initialArrowsEquivalenceIso e Z hZ).hom.app X)).symm.trans
    (Category.id_comp _)

/-- The complete initial projection retains its original value and unchanged target endpoint. -/
theorem initialReplacementEquivalenceIso_projection (data : FunctorialFactorizationData P Q)
    (e : C ≌ D) (Z : C) (hZ : IsInitial Z) (X : C) :
    (initialReplacementEquivalenceIso data e Z hZ).hom.app X ≫
        (initialProjection data (e.functor.obj Z)
          (hZ.isInitialObj e.functor Z)).app (e.functor.obj X) =
      e.functor.map ((initialProjection (data.ofEquivalence e) Z hZ).app X) := by
  let a := (initialArrows Z hZ).obj X
  let q := (initialArrowsEquivalenceIso e Z hZ).hom.app X
  have hp : data.Z.map q ≫ data.p.app ((e.functor ⋙ initialArrows (e.functor.obj Z)
      (hZ.isInitialObj e.functor Z)).obj X) = data.p.app (e.functor.mapArrow.obj a) := by
    have h := data.p.naturality q
    change data.Z.map q ≫ data.p.app ((e.functor ⋙ initialArrows (e.functor.obj Z)
        (hZ.isInitialObj e.functor Z)).obj X) =
      data.p.app (e.functor.mapArrow.obj a) ≫
        𝟙 (Arrow.rightFunc.obj (e.functor.mapArrow.obj a)) at h
    exact h.trans (Category.comp_id _)
  change ((data.ofEquivalenceZComparisonIso e).hom.app ((initialArrows Z hZ).obj X) ≫
      data.Z.map ((initialArrowsEquivalenceIso e Z hZ).hom.app X)) ≫
        data.p.app ((e.functor ⋙ initialArrows (e.functor.obj Z)
          (hZ.isInitialObj e.functor Z)).obj X) =
    e.functor.map ((data.ofEquivalence e).p.app ((initialArrows Z hZ).obj X))
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => (data.ofEquivalenceZComparisonIso e).hom.app a ≫ k) hp).trans
      (data.ofEquivalence_mapped_p e a))

/-- The same complete terminal comparison preserves the original replacement unit. -/
theorem terminalReplacementEquivalenceIso_unit (data : FunctorialFactorizationData P Q)
    (e : C ≌ D) (Z : C) (hZ : IsTerminal Z) (X : C) :
    e.functor.map ((terminalUnit (data.ofEquivalence e) Z hZ).app X) ≫
        (terminalReplacementEquivalenceIso data e Z hZ).hom.app X =
      (terminalUnit data (e.functor.obj Z)
        (hZ.isTerminalObj e.functor Z)).app (e.functor.obj X) := by
  change e.functor.map ((data.ofEquivalence e).i.app ((terminalArrows Z hZ).obj X)) ≫
      ((data.ofEquivalenceZComparisonIso e).hom.app ((terminalArrows Z hZ).obj X) ≫
        data.Z.map ((terminalArrowsEquivalenceIso e Z hZ).hom.app X)) =
    data.i.app ((e.functor ⋙ terminalArrows (e.functor.obj Z)
      (hZ.isTerminalObj e.functor Z)).obj X)
  rw [← Category.assoc, data.ofEquivalence_mapped_i]
  exact (data.i.naturality ((terminalArrowsEquivalenceIso e Z hZ).hom.app X)).symm.trans
    (Category.id_comp _)

/-- The complete terminal leg retains the same original terminal endpoint and right factor. -/
theorem terminalReplacementEquivalenceIso_leg (data : FunctorialFactorizationData P Q)
    (e : C ≌ D) (Z : C) (hZ : IsTerminal Z) (X : C) :
    (terminalReplacementEquivalenceIso data e Z hZ).hom.app X ≫
        (terminalLeg data (e.functor.obj Z)
          (hZ.isTerminalObj e.functor Z)).app (e.functor.obj X) =
      e.functor.map ((terminalLeg (data.ofEquivalence e) Z hZ).app X) := by
  let a := (terminalArrows Z hZ).obj X
  let q := (terminalArrowsEquivalenceIso e Z hZ).hom.app X
  have hp : data.Z.map q ≫ data.p.app ((e.functor ⋙ terminalArrows (e.functor.obj Z)
      (hZ.isTerminalObj e.functor Z)).obj X) = data.p.app (e.functor.mapArrow.obj a) := by
    have h := data.p.naturality q
    change data.Z.map q ≫ data.p.app ((e.functor ⋙ terminalArrows (e.functor.obj Z)
        (hZ.isTerminalObj e.functor Z)).obj X) =
      data.p.app (e.functor.mapArrow.obj a) ≫
        𝟙 (Arrow.rightFunc.obj (e.functor.mapArrow.obj a)) at h
    exact h.trans (Category.comp_id _)
  change ((data.ofEquivalenceZComparisonIso e).hom.app ((terminalArrows Z hZ).obj X) ≫
      data.Z.map ((terminalArrowsEquivalenceIso e Z hZ).hom.app X)) ≫
        data.p.app ((e.functor ⋙ terminalArrows (e.functor.obj Z)
          (hZ.isTerminalObj e.functor Z)).obj X) =
    e.functor.map ((data.ofEquivalence e).p.app ((terminalArrows Z hZ).obj X))
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => (data.ofEquivalenceZComparisonIso e).hom.app a ≫ k) hp).trans
      (data.ofEquivalence_mapped_p e a))

/-- Initial projection migration is an equality of the entire original natural transformations. -/
theorem initialReplacementEquivalenceIso_projection_natural
    (data : FunctorialFactorizationData P Q) (e : C ≌ D) (Z : C) (hZ : IsInitial Z) :
    (initialReplacementEquivalenceIso data e Z hZ).hom ≫
        whiskerLeft e.functor (initialProjection data (e.functor.obj Z)
          (hZ.isInitialObj e.functor Z)) =
      whiskerRight (initialProjection (data.ofEquivalence e) Z hZ) e.functor := by
  ext X
  exact initialReplacementEquivalenceIso_projection data e Z hZ X

/-- Terminal unit migration is an equality of the entire same original natural transformations. -/
theorem terminalReplacementEquivalenceIso_unit_natural
    (data : FunctorialFactorizationData P Q) (e : C ≌ D) (Z : C) (hZ : IsTerminal Z) :
    whiskerRight (terminalUnit (data.ofEquivalence e) Z hZ) e.functor ≫
        (terminalReplacementEquivalenceIso data e Z hZ).hom =
      whiskerLeft e.functor (terminalUnit data (e.functor.obj Z)
        (hZ.isTerminalObj e.functor Z)) := by
  ext X
  exact terminalReplacementEquivalenceIso_unit data e Z hZ X

/-- The actual inverse comparison recovers the whole original initial leg. -/
theorem initialReplacementEquivalenceIso_inverse_leg
    (data : FunctorialFactorizationData P Q) (e : C ≌ D) (Z : C) (hZ : IsInitial Z) (X : C) :
    (initialLeg data (e.functor.obj Z) (hZ.isInitialObj e.functor Z)).app (e.functor.obj X) ≫
        (initialReplacementEquivalenceIso data e Z hZ).inv.app X =
      e.functor.map ((initialLeg (data.ofEquivalence e) Z hZ).app X) := by
  let q := initialReplacementEquivalenceIso data e Z hZ
  have h := congrArg (fun k => k ≫ q.inv.app X)
    (initialReplacementEquivalenceIso_leg data e Z hZ X)
  exact h.symm.trans ((Category.assoc _ _ _).trans
    ((congrArg (fun k => e.functor.map ((initialLeg (data.ofEquivalence e) Z hZ).app X) ≫ k)
      (q.hom_inv_id_app X)).trans (Category.comp_id _)))

/-- The inverse initial comparison recovers the same entire original projection. -/
theorem initialReplacementEquivalenceIso_inverse_projection
    (data : FunctorialFactorizationData P Q) (e : C ≌ D) (Z : C) (hZ : IsInitial Z) (X : C) :
    (initialReplacementEquivalenceIso data e Z hZ).inv.app X ≫
        e.functor.map ((initialProjection (data.ofEquivalence e) Z hZ).app X) =
      (initialProjection data (e.functor.obj Z)
        (hZ.isInitialObj e.functor Z)).app (e.functor.obj X) := by
  let q := initialReplacementEquivalenceIso data e Z hZ
  have h := congrArg (fun k => q.inv.app X ≫ k)
    (initialReplacementEquivalenceIso_projection data e Z hZ X)
  exact h.symm.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (initialProjection data (e.functor.obj Z)
      (hZ.isInitialObj e.functor Z)).app (e.functor.obj X))
      (q.inv_hom_id_app X)).trans (Category.id_comp _)))

/-- The actual inverse terminal comparison recovers the complete original replacement unit. -/
theorem terminalReplacementEquivalenceIso_inverse_unit
    (data : FunctorialFactorizationData P Q) (e : C ≌ D) (Z : C) (hZ : IsTerminal Z) (X : C) :
    (terminalUnit data (e.functor.obj Z)
        (hZ.isTerminalObj e.functor Z)).app (e.functor.obj X) ≫
        (terminalReplacementEquivalenceIso data e Z hZ).inv.app X =
      e.functor.map ((terminalUnit (data.ofEquivalence e) Z hZ).app X) := by
  let q := terminalReplacementEquivalenceIso data e Z hZ
  have h := congrArg (fun k => k ≫ q.inv.app X)
    (terminalReplacementEquivalenceIso_unit data e Z hZ X)
  exact h.symm.trans ((Category.assoc _ _ _).trans
    ((congrArg (fun k => e.functor.map ((terminalUnit (data.ofEquivalence e) Z hZ).app X) ≫ k)
      (q.hom_inv_id_app X)).trans (Category.comp_id _)))

/-- The inverse terminal comparison retains the entire original terminal factor projection. -/
theorem terminalReplacementEquivalenceIso_inverse_leg
    (data : FunctorialFactorizationData P Q) (e : C ≌ D) (Z : C) (hZ : IsTerminal Z) (X : C) :
    (terminalReplacementEquivalenceIso data e Z hZ).inv.app X ≫
        e.functor.map ((terminalLeg (data.ofEquivalence e) Z hZ).app X) =
      (terminalLeg data (e.functor.obj Z)
        (hZ.isTerminalObj e.functor Z)).app (e.functor.obj X) := by
  let q := terminalReplacementEquivalenceIso data e Z hZ
  have h := congrArg (fun k => q.inv.app X ≫ k)
    (terminalReplacementEquivalenceIso_leg data e Z hZ X)
  exact h.symm.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (terminalLeg data (e.functor.obj Z)
      (hZ.isTerminalObj e.functor Z)).app (e.functor.obj X))
      (q.inv_hom_id_app X)).trans (Category.id_comp _)))

/-- The whole initial leg transformation uses the same original source and comparison functors. -/
theorem initialReplacementEquivalenceIso_leg_natural
    (data : FunctorialFactorizationData P Q) (e : C ≌ D) (Z : C) (hZ : IsInitial Z) :
    whiskerRight (initialLeg (data.ofEquivalence e) Z hZ) e.functor ≫
        (initialReplacementEquivalenceIso data e Z hZ).hom =
      (endpointConstantComparisonIso e Z).hom ≫
        whiskerLeft e.functor (initialLeg data (e.functor.obj Z)
          (hZ.isInitialObj e.functor Z)) := by
  ext X
  exact (initialReplacementEquivalenceIso_leg data e Z hZ X).trans
    (Category.id_comp _).symm

/-- The terminal-leg comparison is an equality of the entire original natural transformations. -/
theorem terminalReplacementEquivalenceIso_leg_natural
    (data : FunctorialFactorizationData P Q) (e : C ≌ D) (Z : C) (hZ : IsTerminal Z) :
    (terminalReplacementEquivalenceIso data e Z hZ).hom ≫
        whiskerLeft e.functor (terminalLeg data (e.functor.obj Z)
          (hZ.isTerminalObj e.functor Z)) =
      whiskerRight (terminalLeg (data.ofEquivalence e) Z hZ) e.functor ≫
        (endpointConstantComparisonIso e Z).hom := by
  ext X
  exact (terminalReplacementEquivalenceIso_leg data e Z hZ X).trans
    (Category.comp_id _).symm

end HomotopicalAlgebra.GivenFactorizationReplacements
