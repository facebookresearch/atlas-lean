/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.Local
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalence
public import Mathlib.CategoryTheory.InducedCategory

/-!
# Instance-safe left Bousfield localization

This file packages explicit recognition output for a left Bousfield
localization. The localized model structure is installed only on the
family-keyed wrapper `LeftLocalized L`; the original carrier receives no new
instance.

No existence theorem is proved here. In particular, Smith recognition and
Hirschhorn's cellular construction are independent future producers of
`LeftBousfieldLocalizationData`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w v u

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
variable [SimplicialCategory C]
variable [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]
variable [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]

/-- Localized fibrations have the right lifting property against the
cofibrations that are derived local equivalences. -/
def localizedFibrations {I : Type w} (S : I → Arrow C) :
    MorphismProperty C :=
  (cofibrations C ⊓ localEquivalences S).rlp

/-- Explicit output shared by constructions of a left Bousfield
localization.

Besides the two weak factorization systems needed for model-category
assembly, the packet records the local Whitehead theorem. This theorem is
proved by the existence route; it is not inferred from the weaker
presentation-independence interface for homotopy-function complexes. -/
structure LeftBousfieldLocalizationData {I : Type w}
    (S : I → Arrow C) : Prop where
  /-- Every selected localizing arrow is a local equivalence. -/
  localizingMaps (i : I) : localEquivalences S (S i).hom
  /-- Every base weak equivalence is a local equivalence. -/
  baseWeak_le : weakEquivalences C ≤ localEquivalences S
  /-- Local equivalences satisfy two-out-of-three. -/
  two_out_of_three :
    (localEquivalences S).HasTwoOutOfThreeProperty
  /-- Local equivalences are stable under retracts. -/
  retracts : (localEquivalences S).IsStableUnderRetracts
  /-- Local trivial cofibrations and localized fibrations form a weak
  factorization system. -/
  localized_wfs : IsWeakFactorizationSystem
    (cofibrations C ⊓ localEquivalences S) (localizedFibrations S)
  /-- Localized trivial fibrations are exactly the base trivial
  fibrations. -/
  trivialFibrations_eq :
    localizedFibrations S ⊓ localEquivalences S = trivialFibrations C
  /-- The fibrant objects in the localization are exactly the base-fibrant
  derived local objects. -/
  fibrant_iff (X : C) :
    localizedFibrations S (terminal.from X) ↔ isLocalFibrant S X
  /-- A local equivalence between local-fibrant objects is exactly a base
  weak equivalence. -/
  weakEquivalence_iff_of_local {X Y : C} (f : X ⟶ Y)
      (hX : isLocalFibrant S X) (hY : isLocalFibrant S Y) :
    localEquivalences S f ↔ weakEquivalences C f

/-- The carrier of a selected left Bousfield localization.

The recognition packet occurs in a unique tag on an induced category. Thus
the base model and several localization families can coexist without
competing instances. -/
abbrev LeftLocalized {I : Type w} {S : I → Arrow C}
    (L : LeftBousfieldLocalizationData S) : Type u :=
  InducedCategory C (fun X : { _X : C // L = L } ↦ X.1)

namespace LeftLocalized

variable {I : Type w} {S : I → Arrow C}
variable (L : LeftBousfieldLocalizationData S)

@[instance_reducible]
private def category : Category.{v} (LeftLocalized L) :=
  inferInstanceAs (Category.{v}
    (InducedCategory C (fun X : { _X : C // L = L } ↦ X.1)))

/-- Regard a base object or map as an object or map of the selected
localization. -/
def ofBase : C ⥤ LeftLocalized L where
  obj X := ⟨X, rfl⟩
  map f := InducedCategory.homMk f

/-- Forget the selected localization structure. -/
def toBase : LeftLocalized L ⥤ C where
  obj X := X.1
  map f := f.hom

/-- The wrapper is categorically equivalent to its base category. This does
not identify their weak-equivalence classes. -/
def equivalence : C ≌ LeftLocalized L where
  functor := ofBase L
  inverse := toBase L
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun X ↦ InducedCategory.isoMk (Iso.refl X.1)) (by
      intro X Y f
      apply InducedCategory.hom_ext
      change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
      simp)
  functor_unitIso_comp X := by
    apply InducedCategory.hom_ext
    change 𝟙 X ≫ 𝟙 X = 𝟙 X
    simp

@[instance_reducible]
private def categoryWithFibrations :
    CategoryWithFibrations (LeftLocalized L) where
  fibrations := (localizedFibrations S).inverseImage (toBase L)

@[instance_reducible]
private def categoryWithCofibrations :
    CategoryWithCofibrations (LeftLocalized L) where
  cofibrations := (cofibrations C).inverseImage (toBase L)

@[instance_reducible]
private def categoryWithWeakEquivalences :
    CategoryWithWeakEquivalences (LeftLocalized L) where
  weakEquivalences := (localEquivalences S).inverseImage (toBase L)

/-- The model category selected by explicit localization recognition data. -/
@[instance_reducible]
noncomputable instance modelCategory : ModelCategory (LeftLocalized L) := by
  let _ : CategoryWithFibrations (LeftLocalized L) :=
    { fibrations := (localizedFibrations S).inverseImage (toBase L) }
  let _ : CategoryWithCofibrations (LeftLocalized L) :=
    { cofibrations := (cofibrations C).inverseImage (toBase L) }
  let _ : CategoryWithWeakEquivalences (LeftLocalized L) :=
    { weakEquivalences := (localEquivalences S).inverseImage (toBase L) }
  let e := equivalence L
  haveI : (toBase L).IsEquivalence := by
    simpa only [equivalence] using
      (inferInstance : (equivalence L).inverse.IsEquivalence)
  haveI : (localEquivalences S).HasTwoOutOfThreeProperty :=
    L.two_out_of_three
  haveI : (localEquivalences S).IsStableUnderRetracts := L.retracts
  haveI :
      (cofibrations C ⊓ localEquivalences S).IsStableUnderRetracts :=
    inferInstance
  haveI : (localizedFibrations S).IsStableUnderRetracts := by
    dsimp [localizedFibrations]
    infer_instance
  haveI hLocalized : IsWeakFactorizationSystem
      (cofibrations C ⊓ localEquivalences S) (localizedFibrations S) :=
    L.localized_wfs
  haveI hLocalizedImage : IsWeakFactorizationSystem
      ((cofibrations C ⊓ localEquivalences S).inverseImage (toBase L))
      ((localizedFibrations S).inverseImage (toBase L)) := by
    apply IsWeakFactorizationSystem.mk'
    intro A B X Y i p hi hp
    rw [← (toBase L).hasLiftingProperty_iff_of_isEquivalence]
    exact hasLiftingProperty_of_wfs
      ((toBase L).map i) ((toBase L).map p) hi hp
  haveI :
      (weakEquivalences (LeftLocalized L)).HasTwoOutOfThreeProperty := by
    change
      ((localEquivalences S).inverseImage
        (toBase L)).HasTwoOutOfThreeProperty
    infer_instance
  have hTC : trivialCofibrations (LeftLocalized L) =
      (cofibrations C ⊓ localEquivalences S).inverseImage
        (toBase L) := by
    rfl
  have hFib : fibrations (LeftLocalized L) =
      (localizedFibrations S).inverseImage (toBase L) := by
    rfl
  haveI : IsWeakFactorizationSystem
      (trivialCofibrations (LeftLocalized L))
      (fibrations (LeftLocalized L)) := by
    rw [hTC, hFib]
    infer_instance
  haveI hBase : IsWeakFactorizationSystem
      (cofibrations C) (trivialFibrations C) := inferInstance
  haveI : (cofibrations C).IsStableUnderRetracts := inferInstance
  haveI : (trivialFibrations C).IsStableUnderRetracts := inferInstance
  haveI hBaseImage : IsWeakFactorizationSystem
      ((cofibrations C).inverseImage (toBase L))
      ((trivialFibrations C).inverseImage (toBase L)) := by
    apply IsWeakFactorizationSystem.mk'
    intro A B X Y i p hi hp
    rw [← (toBase L).hasLiftingProperty_iff_of_isEquivalence]
    exact hasLiftingProperty_of_wfs
      ((toBase L).map i) ((toBase L).map p) hi hp
  have hCof : cofibrations (LeftLocalized L) =
      (cofibrations C).inverseImage (toBase L) := by
    rfl
  have hTF : trivialFibrations (LeftLocalized L) =
      (trivialFibrations C).inverseImage (toBase L) := by
    change
      (localizedFibrations S ⊓ localEquivalences S).inverseImage
        (toBase L) = _
    rw [L.trivialFibrations_eq]
  haveI : IsWeakFactorizationSystem
      (cofibrations (LeftLocalized L))
      (trivialFibrations (LeftLocalized L)) := by
    rw [hCof, hTF]
    infer_instance
  haveI : HasFiniteLimits (LeftLocalized L) :=
    ⟨fun _ _ _ ↦
      Adjunction.hasLimitsOfShape_of_equivalence (toBase L)⟩
  haveI : HasFiniteColimits (LeftLocalized L) :=
    ⟨fun _ _ _ ↦
      Adjunction.hasColimitsOfShape_of_equivalence (toBase L)⟩
  exact ModelCategory.mk' (LeftLocalized L)

/-- Localized trivial fibrations are the inverse image of the base trivial
fibrations. -/
theorem trivialFibrations_eq :
    trivialFibrations (LeftLocalized L) =
      (trivialFibrations C).inverseImage (toBase L) := by
  change
    (localizedFibrations S ⊓ localEquivalences S).inverseImage
      (toBase L) = (trivialFibrations C).inverseImage (toBase L)
  rw [L.trivialFibrations_eq]

/-- Fibrant wrapper objects are precisely the base-fibrant derived local
objects. -/
theorem fibrant_iff (X : LeftLocalized L) :
    IsFibrant X ↔ isLocalFibrant S X.1 := by
  let _ : (toBase L).IsEquivalence := by
    simpa only [equivalence] using
      (inferInstance : (equivalence L).inverse.IsEquivalence)
  let _ : (localizedFibrations S).IsStableUnderRetracts := by
    dsimp only [localizedFibrations]
    infer_instance
  have hT : IsTerminal ((toBase L).obj (⊤_ (LeftLocalized L))) :=
    terminalIsTerminal.isTerminalObj (toBase L) _
  let eT : (toBase L).obj (⊤_ (LeftLocalized L)) ≅ ⊤_ C :=
    hT.uniqueUpToIso terminalIsTerminal
  let e : Arrow.mk ((toBase L).map (terminal.from X)) ≅
      Arrow.mk (terminal.from X.1) :=
    Arrow.isoMk (Iso.refl _) eT (by
      apply terminalIsTerminal.hom_ext)
  rw [isFibrant_iff, fibration_iff]
  change localizedFibrations S ((toBase L).map (terminal.from X)) ↔
    isLocalFibrant S X.1
  rw [(localizedFibrations S).arrow_mk_iso_iff e]
  exact L.fibrant_iff X.1

/-- Between local-fibrant objects, localized and base fibrations agree. -/
theorem fibration_iff_of_local {X Y : LeftLocalized L} (f : X ⟶ Y)
    (hX : isLocalFibrant S X.1)
    (hY : isLocalFibrant S Y.1) :
    fibrations (LeftLocalized L) f ↔
      fibrations C ((toBase L).map f) := by
  change localizedFibrations S ((toBase L).map f) ↔
    fibrations C ((toBase L).map f)
  constructor
  · intro hf
    rw [← rlp_eq_of_wfs (trivialCofibrations C) (fibrations C)]
    intro A B i hi
    exact hf i ⟨hi.1, L.baseWeak_le i hi.2⟩
  · intro hf
    let _ : IsWeakFactorizationSystem
        (cofibrations C ⊓ localEquivalences S)
        (localizedFibrations S) :=
      L.localized_wfs
    let _ : (localizedFibrations S).IsStableUnderComposition := by
      dsimp only [localizedFibrations]
      infer_instance
    let _ : (localizedFibrations S).IsStableUnderRetracts := by
      dsimp only [localizedFibrations]
      infer_instance
    let d := factorizationData
      (cofibrations C ⊓ localEquivalences S)
      (localizedFibrations S) ((toBase L).map f)
    have hZ : isLocalFibrant S d.Z := by
      apply (L.fibrant_iff d.Z).1
      have hpY :
          localizedFibrations S (terminal.from Y.1) :=
        (L.fibrant_iff Y.1).2 hY
      have heq : d.p ≫ terminal.from Y.1 = terminal.from d.Z :=
        terminalIsTerminal.hom_ext _ _
      rw [← heq]
      exact (localizedFibrations S).comp_mem d.p
        (terminal.from Y.1) d.hp hpY
    have hiW : weakEquivalences C d.i :=
      (L.weakEquivalence_iff_of_local d.i hX hZ).1 d.hi.2
    have hiTriv : trivialCofibrations C d.i := ⟨d.hi.1, hiW⟩
    let _ : HasLiftingProperty d.i ((toBase L).map f) :=
      hasLiftingProperty_of_wfs d.i ((toBase L).map f) hiTriv hf
    exact (localizedFibrations S).of_retract
      (RetractArrow.ofRightLiftingProperty d.fac) d.hp

/-- Between local-fibrant objects, local and base weak equivalences agree. -/
theorem weakEquivalence_iff_of_local {X Y : LeftLocalized L} (f : X ⟶ Y)
    (hX : isLocalFibrant S X.1)
    (hY : isLocalFibrant S Y.1) :
    weakEquivalences (LeftLocalized L) f ↔
      weakEquivalences C ((toBase L).map f) := by
  change localEquivalences S ((toBase L).map f) ↔
    weakEquivalences C ((toBase L).map f)
  exact L.weakEquivalence_iff_of_local ((toBase L).map f) hX hY

/-- The forward identity from the base to its left localization is a left
Quillen functor. -/
theorem ofBase_isLeftQuillen :
    Adjunction.IsQuillenAdjunction (equivalence L).toAdjunction where
  preservesCofibrations := by
    intro X Y f hf
    change cofibrations C f at hf
    change cofibrations C f
    exact hf
  preservesTrivialCofibrations := by
    intro X Y f hf
    change cofibrations C f ∧ weakEquivalences C f at hf
    change cofibrations C f ∧ localEquivalences S f
    exact ⟨hf.1, L.baseWeak_le f hf.2⟩

/-- For an empty localizing family, the categorical equivalence is the
underlying equivalence used by the recovered base model structure. -/
def emptyEquivalence (_data : HomotopyFunctionComplexData (C := C))
    [_emptyIndex : IsEmpty I] : C ≌ LeftLocalized L :=
  equivalence L

/-- The empty-family equivalence is a Quillen equivalence. -/
theorem empty_isQuillenEquivalence
    (data : HomotopyFunctionComplexData (C := C)) [IsEmpty I] :
    Adjunction.IsQuillenEquivalence
      (emptyEquivalence L data).toAdjunction where
  toIsQuillenAdjunction := ofBase_isLeftQuillen L
  homEquiv_weakEquivalence_iff {X Y} _ _ f := by
    change localEquivalences S f.hom ↔ weakEquivalences C _
    rw [localEquivalences_empty data S]
    have hmap : (emptyEquivalence L data).inverse.map f = f.hom := rfl
    rw [← hmap]
    rw [Adjunction.homEquiv_unit]
    have hu : weakEquivalences C
        ((emptyEquivalence L data).toAdjunction.unit.app X) :=
      mem_weakEquivalences _
    constructor
    · intro hf
      exact (weakEquivalences C).comp_mem _ _ hu hf
    · intro hcomp
      exact (weakEquivalences C).of_precomp _ _ hu hcomp

end LeftLocalized

end HomotopicalAlgebra
