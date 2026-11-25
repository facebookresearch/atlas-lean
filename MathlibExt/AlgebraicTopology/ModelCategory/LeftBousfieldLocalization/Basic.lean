/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.InducedCategory

/-!
# Assembly of a recognized left Bousfield localization

Given a class of candidate local equivalences and a predicate for local-fibrant
objects, the recognition data below constructs the localized model on a tagged
copy of the base category. No model structure on that copy is assumed. This
file neither defines derived locality for a family of arrows nor proves that
any particular family admits a localization.

Adapted from the Formal-Math development by Tsutomu Okano and Avocado.
-/

@[expose] public section

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.LeftBousfieldLocalization

variable {C : Type*} [Category* C] [ModelCategory C]

/-- Recognition data for a proposed left Bousfield localization. `W` is the
candidate local-equivalence class, and `P` the candidate class of local-fibrant
objects. The last field is the local Whitehead theorem, not an assumption that
the localized model already exists. -/
structure Recognition (W : MorphismProperty C) (P : ObjectProperty C) : Prop where
  baseWeak_le : weakEquivalences C ≤ W
  twoOutOfThree : W.HasTwoOutOfThreeProperty
  localizedWfs : IsWeakFactorizationSystem (cofibrations C ⊓ W) (cofibrations C ⊓ W).rlp
  trivialFibrations_eq : (cofibrations C ⊓ W).rlp ⊓ W = trivialFibrations C
  fibrant_iff (X : C) : (cofibrations C ⊓ W).rlp (terminal.from X) ↔ P X
  weakEquivalence_iff_of_local {X Y : C} (f : X ⟶ Y) (hX : P X) (hY : P Y) :
    W f ↔ weakEquivalences C f

variable {W : MorphismProperty C} {P : ObjectProperty C} (h : Recognition W P)

/-- The original objects and morphisms, tagged so the new model does not
change typeclass inference on the original category. -/
abbrev Localized : Type _ := InducedCategory C (fun X : { _X : C // h = h } ↦ X.1)

/-- The underlying categorical equivalence. It does not identify the old
weak equivalences with the local equivalences. -/
def equivalence : C ≌ Localized h where
  functor :=
    { obj := fun X ↦ ⟨X, rfl⟩
      map f := InducedCategory.homMk f
      map_id _ := rfl
      map_comp _ _ := rfl }
  inverse := inducedFunctor _
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents (fun X ↦ InducedCategory.isoMk (Iso.refl X.1)) (by
    intro X Y f
    apply InducedCategory.hom_ext
    change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
    simp)
  functor_unitIso_comp X := by
    apply InducedCategory.hom_ext
    change 𝟙 X ≫ 𝟙 X = 𝟙 X
    simp

/-- The recognized model on the tagged copy, assembled from the two weak
factorization systems with Mathlib's `ModelCategory.mk'`. -/
@[instance_reducible]
instance : ModelCategory (Localized h) := by
  let send := (equivalence h).inverse
  letI : CategoryWithCofibrations (Localized h) := ⟨(cofibrations C).inverseImage send⟩
  letI : CategoryWithFibrations (Localized h) := ⟨(cofibrations C ⊓ W).rlp.inverseImage send⟩
  letI : CategoryWithWeakEquivalences (Localized h) := ⟨W.inverseImage send⟩
  haveI : send.IsEquivalence := inferInstanceAs (equivalence h).inverse.IsEquivalence
  have pullWfs (A B : MorphismProperty C) [A.IsStableUnderRetracts] [B.IsStableUnderRetracts]
      [IsWeakFactorizationSystem A B] :
      IsWeakFactorizationSystem (A.inverseImage send) (B.inverseImage send) := by
    apply IsWeakFactorizationSystem.mk'
    intro X Y U V i p hi hp
    exact (send.hasLiftingProperty_iff_of_isEquivalence i p).mp
      (hasLiftingProperty_of_wfs (send.map i) (send.map p) hi hp)
  haveI : W.HasTwoOutOfThreeProperty := h.twoOutOfThree
  haveI : (weakEquivalences (Localized h)).HasTwoOutOfThreeProperty := by
    change (W.inverseImage send).HasTwoOutOfThreeProperty
    infer_instance
  haveI : IsWeakFactorizationSystem (trivialCofibrations (Localized h))
      (fibrations (Localized h)) := by
    change IsWeakFactorizationSystem ((cofibrations C ⊓ W).inverseImage send)
      ((cofibrations C ⊓ W).rlp.inverseImage send)
    have : IsWeakFactorizationSystem (cofibrations C ⊓ W) (cofibrations C ⊓ W).rlp :=
      h.localizedWfs
    have : (cofibrations C ⊓ W).IsStableUnderRetracts := by
      rw [← llp_eq_of_wfs (cofibrations C ⊓ W) (cofibrations C ⊓ W).rlp]
      infer_instance
    exact pullWfs _ _
  haveI : IsWeakFactorizationSystem (cofibrations (Localized h))
      (trivialFibrations (Localized h)) := by
    change IsWeakFactorizationSystem ((cofibrations C).inverseImage send)
      (((cofibrations C ⊓ W).rlp ⊓ W).inverseImage send)
    rw [h.trivialFibrations_eq]
    exact pullWfs _ _
  haveI : HasFiniteLimits (Localized h) :=
    ⟨fun _ _ _ ↦ Adjunction.hasLimitsOfShape_of_equivalence send⟩
  haveI : HasFiniteColimits (Localized h) :=
    ⟨fun _ _ _ ↦ Adjunction.hasColimitsOfShape_of_equivalence send⟩
  exact ModelCategory.mk' (Localized h)

/-- Fibrancy for the recognized model is exactly the supplied local-fibrancy
predicate, evaluated on the underlying object. -/
theorem isFibrant_iff (X : Localized h) : IsFibrant X ↔ P X.1 := by
  let send := (equivalence h).inverse
  have hTerminal : IsTerminal (send.obj (⊤_ (Localized h))) :=
    terminalIsTerminal.isTerminalObj send _
  let e : Arrow.mk (send.map (terminal.from X)) ≅ Arrow.mk (terminal.from X.1) :=
    Arrow.isoMk (Iso.refl _) (hTerminal.uniqueUpToIso terminalIsTerminal)
      (terminalIsTerminal.hom_ext _ _)
  rw [HomotopicalAlgebra.isFibrant_iff, fibration_iff]
  change (cofibrations C ⊓ W).rlp (send.map (terminal.from X)) ↔ P X.1
  exact ((cofibrations C ⊓ W).rlp.arrow_mk_iso_iff e).trans (h.fibrant_iff X.1)

/-- A fibration between local-fibrant objects is the same in the old and new
models. The reverse direction uses the local Whitehead hypothesis on the
intermediate object of the localized factorization. -/
theorem fibration_iff_of_local {X Y : Localized h} (f : X ⟶ Y)
    (hX : P X.1) (hY : P Y.1) : fibrations (Localized h) f ↔ fibrations C f.hom := by
  change (cofibrations C ⊓ W).rlp f.hom ↔ fibrations C f.hom
  constructor
  · intro hf
    rw [← rlp_eq_of_wfs (trivialCofibrations C) (fibrations C)]
    intro A B i hi
    exact hf i ⟨hi.1, h.baseWeak_le i hi.2⟩
  · intro hf
    have : IsWeakFactorizationSystem (cofibrations C ⊓ W) (cofibrations C ⊓ W).rlp :=
      h.localizedWfs
    let fac := factorizationData (cofibrations C ⊓ W) (cofibrations C ⊓ W).rlp f.hom
    have hZ : P fac.Z := by
      apply (h.fibrant_iff fac.Z).mp
      rw [← terminalIsTerminal.hom_ext (fac.p ≫ terminal.from Y.1) (terminal.from fac.Z)]
      exact (cofibrations C ⊓ W).rlp.comp_mem fac.p _ fac.hp ((h.fibrant_iff Y.1).mpr hY)
    have : HasLiftingProperty fac.i f.hom := hasLiftingProperty_of_wfs _ _
      (show trivialCofibrations C fac.i from
        ⟨fac.hi.1, (h.weakEquivalence_iff_of_local fac.i hX hZ).mp fac.hi.2⟩) hf
    exact (cofibrations C ⊓ W).rlp.of_retract (RetractArrow.ofRightLiftingProperty fac.fac) fac.hp

end HomotopicalAlgebra.LeftBousfieldLocalization
