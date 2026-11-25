/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.AlgebraicTopology.ModelCategory.Opposite
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-!
# Quillen adjunctions and preservation properties

For an adjunction between model categories, `IsQuillenAdjunction` requires
the left adjoint to preserve cofibrations and trivial cofibrations. This is
equivalent to preservation of fibrations and trivial fibrations by the right
adjoint, and implies preservation of cofibrant and fibrant objects on the
respective sides. Quillen adjunctions are stable under natural isomorphisms,
opposites and composition; identity adjunctions are Quillen.

The original Formal-Math development is by Tsutomu Okano and Avocado.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory HomotopicalAlgebra MorphismProperty Limits


namespace HomotopicalAlgebra

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

section PreservesCofibrations

variable [CategoryWithCofibrations C] [CategoryWithCofibrations D]

/-- A functor `F : C ⥤ D` preserves cofibrations if every cofibration in `C`
is sent to a cofibration in `D`. -/
def PreservesCofibrations (F : C ⥤ D) : Prop :=
  cofibrations C ≤ (cofibrations D).inverseImage F

@[simp]
lemma preservesCofibrations_iff (F : C ⥤ D) :
    PreservesCofibrations F ↔
      ∀ ⦃X Y : C⦄ (f : X ⟶ Y), cofibrations C f → cofibrations D (F.map f) :=
  Iff.rfl

lemma PreservesCofibrations.map_cofibration {F : C ⥤ D} (hF : PreservesCofibrations F)
    {X Y : C} {f : X ⟶ Y} (hf : cofibrations C f) : cofibrations D (F.map f) :=
  hF _ hf

end PreservesCofibrations

section PreservesTrivialCofibrations

variable [CategoryWithCofibrations C] [CategoryWithCofibrations D]
  [CategoryWithWeakEquivalences C] [CategoryWithWeakEquivalences D]

/-- A functor preserves trivial cofibrations. -/
def PreservesTrivialCofibrations (F : C ⥤ D) : Prop :=
  trivialCofibrations C ≤ (trivialCofibrations D).inverseImage F

@[simp]
lemma preservesTrivialCofibrations_iff (F : C ⥤ D) :
    PreservesTrivialCofibrations F ↔
      ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
        trivialCofibrations C f → trivialCofibrations D (F.map f) :=
  Iff.rfl

lemma PreservesTrivialCofibrations.map_trivialCofibration {F : C ⥤ D}
    (hF : PreservesTrivialCofibrations F) {X Y : C} {f : X ⟶ Y}
    (hf : trivialCofibrations C f) : trivialCofibrations D (F.map f) :=
  hF _ hf

end PreservesTrivialCofibrations

section PreservesFibrations

variable [CategoryWithFibrations C] [CategoryWithFibrations D]

/-- A functor preserves fibrations. -/
def PreservesFibrations (F : C ⥤ D) : Prop :=
  fibrations C ≤ (fibrations D).inverseImage F

@[simp]
lemma preservesFibrations_iff (F : C ⥤ D) :
    PreservesFibrations F ↔
      ∀ ⦃X Y : C⦄ (f : X ⟶ Y), fibrations C f → fibrations D (F.map f) :=
  Iff.rfl

lemma PreservesFibrations.map_fibration {F : C ⥤ D} (hF : PreservesFibrations F)
    {X Y : C} {f : X ⟶ Y} (hf : fibrations C f) : fibrations D (F.map f) :=
  hF _ hf

end PreservesFibrations

section PreservesTrivialFibrations

variable [CategoryWithFibrations C] [CategoryWithFibrations D]
  [CategoryWithWeakEquivalences C] [CategoryWithWeakEquivalences D]

/-- A functor preserves trivial fibrations. -/
def PreservesTrivialFibrations (F : C ⥤ D) : Prop :=
  trivialFibrations C ≤ (trivialFibrations D).inverseImage F

@[simp]
lemma preservesTrivialFibrations_iff (F : C ⥤ D) :
    PreservesTrivialFibrations F ↔
      ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
        trivialFibrations C f → trivialFibrations D (F.map f) :=
  Iff.rfl

lemma PreservesTrivialFibrations.map_trivialFibration {F : C ⥤ D}
    (hF : PreservesTrivialFibrations F) {X Y : C} {f : X ⟶ Y}
    (hf : trivialFibrations C f) : trivialFibrations D (F.map f) :=
  hF _ hf

end PreservesTrivialFibrations

section PreservesCofibrantObjects

variable [CategoryWithCofibrations C] [HasInitial C]
  [CategoryWithCofibrations D] [HasInitial D]

/-- A functor `F : C ⥤ D` preserves cofibrant objects if the image of every
cofibrant object is cofibrant. -/
def PreservesCofibrantObjects (F : C ⥤ D) : Prop :=
  ∀ ⦃X : C⦄ (_ : IsCofibrant X), IsCofibrant (F.obj X)

@[simp]
lemma preservesCofibrantObjects_iff (F : C ⥤ D) :
    PreservesCofibrantObjects F ↔ ∀ ⦃X : C⦄ (_ : IsCofibrant X), IsCofibrant (F.obj X) :=
  Iff.rfl

lemma PreservesCofibrantObjects.isCofibrant {F : C ⥤ D}
    (hF : PreservesCofibrantObjects (C := C) (D := D) F) {X : C}
    (hx : IsCofibrant X) : IsCofibrant (F.obj X) :=
  hF hx

end PreservesCofibrantObjects

section PreservesFibrantObjects

variable [CategoryWithFibrations C] [HasTerminal C]
  [CategoryWithFibrations D] [HasTerminal D]

/-- A functor `F : C ⥤ D` preserves fibrant objects if the image of every
fibrant object is fibrant. -/
def PreservesFibrantObjects (F : C ⥤ D) : Prop :=
  ∀ ⦃X : C⦄ (_ : IsFibrant X), IsFibrant (F.obj X)

@[simp]
lemma preservesFibrantObjects_iff (F : C ⥤ D) :
    PreservesFibrantObjects F ↔ ∀ ⦃X : C⦄ (_ : IsFibrant X), IsFibrant (F.obj X) :=
  Iff.rfl

lemma PreservesFibrantObjects.isFibrant {F : C ⥤ D}
    (hF : PreservesFibrantObjects (C := C) (D := D) F) {X : C}
    (hx : IsFibrant X) : IsFibrant (F.obj X) :=
  hF hx

end PreservesFibrantObjects

end HomotopicalAlgebra

namespace CategoryTheory.Adjunction

open HomotopicalAlgebra

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [ModelCategory C] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C}

/--
A Quillen adjunction `L ⊣ R` between model categories is an adjunction
whose left adjoint preserves cofibrations and trivial cofibrations.
Equivalently, the right adjoint preserves fibrations and trivial fibrations;
see `IsQuillenAdjunction.preservesFibrations` and
`IsQuillenAdjunction.preservesTrivialFibrations` and the constructor
`IsQuillenAdjunction.mkOfPreservesFibrations`.
-/
class IsQuillenAdjunction (adj : L ⊣ R) : Prop where
  preservesCofibrations : PreservesCofibrations (C := C) (D := D) L
  preservesTrivialCofibrations : PreservesTrivialCofibrations (C := C) (D := D) L

namespace IsQuillenAdjunction

variable {adj : L ⊣ R}

/-- The right adjoint of a Quillen adjunction preserves fibrations.
The proof uses `adj.hasLiftingProperty_iff` and the weak factorization systems
`(trivialCofibrations, fibrations)` in both model categories. -/
theorem preservesFibrations [h : IsQuillenAdjunction adj] :
    PreservesFibrations (C := D) (D := C) R := by
  intro X Y p hp
  have h_eq : (trivialCofibrations C).rlp = fibrations C :=
    rlp_eq_of_wfs (trivialCofibrations C) (fibrations C)
  rw [← h_eq]
  intro A B i hi
  have hi' : trivialCofibrations D (L.map i) := h.preservesTrivialCofibrations _ hi
  have hlp : HasLiftingProperty (L.map i) p :=
    hasLiftingProperty_of_wfs (L.map i) p hi' hp
  exact (adj.hasLiftingProperty_iff i p).mp hlp

/-- The right adjoint of a Quillen adjunction preserves trivial fibrations.
The proof uses `adj.hasLiftingProperty_iff` and the weak factorization systems
`(cofibrations, trivialFibrations)`. -/
theorem preservesTrivialFibrations [h : IsQuillenAdjunction adj] :
    PreservesTrivialFibrations (C := D) (D := C) R := by
  intro X Y p hp
  have h_eq : (cofibrations C).rlp = trivialFibrations C :=
    rlp_eq_of_wfs (cofibrations C) (trivialFibrations C)
  rw [← h_eq]
  intro A B i hi
  have hi' : cofibrations D (L.map i) := h.preservesCofibrations _ hi
  have hlp : HasLiftingProperty (L.map i) p :=
    hasLiftingProperty_of_wfs (L.map i) p hi' hp
  exact (adj.hasLiftingProperty_iff i p).mp hlp

/-- Constructor for `IsQuillenAdjunction` from right-adjoint preservation.
This is the converse direction, also via `adj.hasLiftingProperty_iff`. -/
lemma mkOfPreservesFibrations
    (hf : PreservesFibrations (C := D) (D := C) R)
    (ht : PreservesTrivialFibrations (C := D) (D := C) R) :
    IsQuillenAdjunction adj where
  preservesCofibrations := by
    intro A B i hi
    have h_eq : (trivialFibrations D).llp = cofibrations D :=
      llp_eq_of_wfs (cofibrations D) (trivialFibrations D)
    rw [← h_eq]
    intro X Y p hp
    have hp' : trivialFibrations C (R.map p) := ht _ hp
    have hlp : HasLiftingProperty i (R.map p) :=
      hasLiftingProperty_of_wfs i (R.map p) hi hp'
    exact (adj.hasLiftingProperty_iff i p).mpr hlp
  preservesTrivialCofibrations := by
    intro A B i hi
    have h_eq : (fibrations D).llp = trivialCofibrations D :=
      llp_eq_of_wfs (trivialCofibrations D) (fibrations D)
    rw [← h_eq]
    intro X Y p hp
    have hp' : fibrations C (R.map p) := hf _ hp
    have hlp : HasLiftingProperty i (R.map p) :=
      hasLiftingProperty_of_wfs i (R.map p) hi hp'
    exact (adj.hasLiftingProperty_iff i p).mpr hlp

/-- A Quillen adjunction can be characterized by right-adjoint preservation. -/
theorem isQuillenAdjunction_iff :
    IsQuillenAdjunction adj ↔
      PreservesFibrations (C := D) (D := C) R ∧
        PreservesTrivialFibrations (C := D) (D := C) R :=
  ⟨fun h => letI := h; ⟨preservesFibrations (adj := adj), preservesTrivialFibrations (adj := adj)⟩,
    fun ⟨hf, ht⟩ => mkOfPreservesFibrations (adj := adj) hf ht⟩

/-- A Quillen left adjoint preserves cofibrant objects: it preserves both
initial objects and cofibrations out of them. -/
theorem preservesCofibrantObjects [h : IsQuillenAdjunction adj] :
    PreservesCofibrantObjects (C := C) (D := D) L := by
  intro X hX
  have hCof : Cofibration (initial.to X) := hX
  have hCofProp : cofibrations C (initial.to X) := (cofibration_iff (f := initial.to X)).mp hCof
  have hCofLProp : cofibrations D (L.map (initial.to X)) :=
    h.preservesCofibrations _ hCofProp
  have hCofL : Cofibration (L.map (initial.to X)) :=
    (cofibration_iff (f := L.map (initial.to X))).mpr hCofLProp
  let := adj.leftAdjoint_preservesColimits
  have hInit : IsInitial (L.obj (⊥_ C)) := isColimitOfHasInitialOfPreservesColimit L
  have : (cofibrations D).RespectsIso := by
    apply MorphismProperty.respectsIso_of_isStableUnderComposition
    intro _ _ f hf
    have : IsIso f := hf
    exact HomotopicalAlgebra.mem_cofibrations (f := f)
  have hIff := isCofibrant_iff_of_isInitial (C := D) (L.map (initial.to X)) hInit
  exact hIff.mpr hCofL

/-- A Quillen right adjoint preserves fibrant objects.
Dual to `preservesCofibrantObjects`, using `isFibrant_iff_of_isTerminal`
and preservation of terminal objects by a right adjoint. -/
theorem preservesFibrantObjects [h : IsQuillenAdjunction adj] :
    PreservesFibrantObjects (C := D) (D := C) R := by
  intro Y hY
  have hFib : Fibration (terminal.from Y) := hY
  have hFibProp : fibrations D (terminal.from Y) := (fibration_iff (f := terminal.from Y)).mp hFib
  have hFibRProp : fibrations C (R.map (terminal.from Y)) :=
    preservesFibrations (adj := adj) _ hFibProp
  have hFibR : Fibration (R.map (terminal.from Y)) :=
    (fibration_iff (f := R.map (terminal.from Y))).mpr hFibRProp
  let := adj.rightAdjoint_preservesLimits
  have hTerm : IsTerminal (R.obj (⊤_ D)) := isLimitOfHasTerminalOfPreservesLimit R
  have : (fibrations C).RespectsIso := by
    apply MorphismProperty.respectsIso_of_isStableUnderComposition
    intro _ _ f hf
    have : IsIso f := hf
    exact HomotopicalAlgebra.mem_fibrations (f := f)
  have hIff := isFibrant_iff_of_isTerminal (C := C) (R.map (terminal.from Y)) hTerm
  exact hIff.mpr hFibR

/-- Transport of `IsQuillenAdjunction` across a natural isomorphism on the left.
Uses `MorphismProperty.RespectsIso` via `arrow_mk_iso_iff` rather than
reproving lifting arguments. -/
instance ofNatIsoLeft {L' : C ⥤ D} (e : L ≅ L') [IsQuillenAdjunction adj] :
    IsQuillenAdjunction (adj.ofNatIsoLeft e) where
  preservesCofibrations := by
    intro X Y f hf
    have h : cofibrations D (L.map f) :=
      (inferInstance : IsQuillenAdjunction adj).preservesCofibrations _ hf
    have iso : Arrow.mk (L.map f) ≅ Arrow.mk (L'.map f) :=
      Arrow.isoMk (e.app X) (e.app Y) (e.hom.naturality f).symm
    exact ((cofibrations D).arrow_mk_iso_iff iso).mp h
  preservesTrivialCofibrations := by
    intro X Y f hf
    have h : trivialCofibrations D (L.map f) :=
      (inferInstance : IsQuillenAdjunction adj).preservesTrivialCofibrations _ hf
    have iso : Arrow.mk (L.map f) ≅ Arrow.mk (L'.map f) :=
      Arrow.isoMk (e.app X) (e.app Y) (e.hom.naturality f).symm
    exact ((trivialCofibrations D).arrow_mk_iso_iff iso).mp h

/-- Transport of `IsQuillenAdjunction` across a natural isomorphism on the right.
The left adjoint is unchanged, so the Quillen condition is preserved directly. -/
instance ofNatIsoRight {R' : D ⥤ C} (e : R ≅ R') [IsQuillenAdjunction adj] :
    IsQuillenAdjunction (adj.ofNatIsoRight e) where
  preservesCofibrations :=
    (inferInstance : IsQuillenAdjunction adj).preservesCofibrations
  preservesTrivialCofibrations :=
    (inferInstance : IsQuillenAdjunction adj).preservesTrivialCofibrations

/-- Opposite transport: if `L ⊣ R` is Quillen then `R.op ⊣ L.op` is Quillen
for the opposite model structures. Uses `cofibrations_op` / `fibrations_op`
identities and the right-adjoint preservation characterization. -/
instance op [IsQuillenAdjunction adj] : IsQuillenAdjunction adj.op where
  preservesCofibrations := by
    intro X Y f hf
    -- f : X ⟶ Y in Dᵒᵖ, need cofibrations (Cᵒᵖ) (R.op.map f)
    have hf' : fibrations D (f.unop) := by
      have h : cofibrations (Dᵒᵖ) = (fibrations D).op := cofibrations_op (C := D)
      rw [h] at hf
      exact hf
    have hFib : PreservesFibrations (C := D) (D := C) R :=
      preservesFibrations (adj := adj)
    have hMap : fibrations C (R.map f.unop) := hFib _ hf'
    have hEq : (R.op.map f).unop = R.map f.unop := by
      simp [Functor.op_map]
    rw [cofibrations_op (C := C)]
    change fibrations C ((R.op.map f).unop)
    rw [hEq]
    exact hMap
  preservesTrivialCofibrations := by
    intro X Y f hf
    have hf' : trivialFibrations D (f.unop) := by
      have h : trivialCofibrations (Dᵒᵖ) = (trivialFibrations D).op :=
        trivialCofibrations_op (C := D)
      rw [h] at hf
      exact hf
    have hTriv : PreservesTrivialFibrations (C := D) (D := C) R :=
      preservesTrivialFibrations (adj := adj)
    have hMap : trivialFibrations C (R.map f.unop) := hTriv _ hf'
    have hEq : (R.op.map f).unop = R.map f.unop := by
      simp [Functor.op_map]
    rw [trivialCofibrations_op (C := C)]
    change trivialFibrations C ((R.op.map f).unop)
    rw [hEq]
    exact hMap

/-- The identity adjunction is Quillen. -/
instance id (C : Type u₁) [Category.{v₁} C] [ModelCategory C] :
    IsQuillenAdjunction (Adjunction.id (C := C)) where
  preservesCofibrations := fun _ _ _ hf => hf
  preservesTrivialCofibrations := fun _ _ _ hf => hf

/-- Composition of Quillen adjunctions is Quillen. -/
instance comp {E : Type u₃} [Category.{v₃} E] [ModelCategory E]
    {L' : D ⥤ E} {R' : E ⥤ D} (adj' : L' ⊣ R')
    [h : IsQuillenAdjunction adj] [h' : IsQuillenAdjunction adj'] :
    IsQuillenAdjunction (adj.comp adj') where
  preservesCofibrations := by
    intro X Y f hf
    have h₁ : cofibrations D (L.map f) := h.preservesCofibrations _ hf
    have h₂ : cofibrations E (L'.map (L.map f)) := h'.preservesCofibrations _ h₁
    exact h₂
  preservesTrivialCofibrations := by
    intro X Y f hf
    have h₁ : trivialCofibrations D (L.map f) := h.preservesTrivialCofibrations _ hf
    have h₂ : trivialCofibrations E (L'.map (L.map f)) := h'.preservesTrivialCofibrations _ h₁
    exact h₂

end IsQuillenAdjunction

end CategoryTheory.Adjunction
