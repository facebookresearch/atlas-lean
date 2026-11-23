/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.FiberReflection
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Equivalence

/-!
# Actual fixed-target row groupoids and their strict-fiber comparison

For every given object of an exact category, this file constructs the
groupoid of actual admissible exact rows ending at that object. Its arrows
are forward kernel and middle isomorphism pairs preserving the given
quotient. Their inclusion uses actual quotient diagrams with identity
quotient legs.

The reverse functor retains the original kernel and middle objects and
casts only the quotient endpoint. Accepted identity-span reflection gives
its isomorphism pair for every actual fiber arrow and every raw
representative. Both comparison directions, naturality, and the triangle
retain the original row and given-quotient formulas with independent object
and Hom universes. The extension-category summary and Q-plus construction
remain separate source goals.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.ExactCategory Limits Opposite

universe u v

namespace AlgebraicKTheory

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- Actual admissible exact rows ending at the given object. -/
structure FixedTargetExtension (X : C) where
  /-- The given kernel object. -/
  A : C
  /-- The given middle object. -/
  B : C
  /-- The actual admissible mono of the row. -/
  i : A ⟶ B
  /-- The actual quotient map to the given object. -/
  p : B ⟶ X
  /-- The row is a complex. -/
  zero : i ≫ p = 0
  /-- Admissibility of the actual row. -/
  admissible : IsAdmissibleExact (ShortComplex.mk i p zero)

variable {C}

namespace FixedTargetExtension

variable {X : C}

/-- Forward kernel and middle isomorphisms preserving the given quotient. -/
structure Hom (E' E : FixedTargetExtension C X) where
  /-- The forward isomorphism of kernel objects. -/
  a : E'.A ≅ E.A
  /-- The forward isomorphism of middle objects. -/
  b : E'.B ≅ E.B
  /-- The kernel square commutes. -/
  comm_i : E'.i ≫ b.hom = a.hom ≫ E.i
  /-- The given quotient square commutes. -/
  comm_p : b.hom ≫ E.p = E'.p

namespace Hom

/-- Forward iso-pair arrows agree when both isomorphisms agree. -/
@[ext]
theorem ext {E' E : FixedTargetExtension C X} {f g : Hom E' E}
    (ha : f.a = g.a) (hb : f.b = g.b) : f = g := by
  cases f
  cases g
  cases ha
  cases hb
  rfl

/-- Arrow extensionality using the reverse kernel and forward middle maps. -/
theorem ext_inv {E' E : FixedTargetExtension C X} {f g : Hom E' E}
    (ha : f.a.inv = g.a.inv) (hb : f.b.hom = g.b.hom) : f = g := by
  apply ext
  · exact Iso.ext_inv ha
  · exact Iso.ext hb

/-- The identity forward isomorphism pair of a given-X row. -/
def refl (E : FixedTargetExtension C X) : Hom E E where
  a := Iso.refl _
  b := Iso.refl _
  comm_i := by simp
  comm_p := by simp

/-- Compose forward kernel and middle isomorphisms componentwise. -/
def comp {E' E F : FixedTargetExtension C X} (f : Hom E' E) (g : Hom E F) : Hom E' F where
  a := f.a ≪≫ g.a
  b := f.b ≪≫ g.b
  comm_i := by
    simp only [Iso.trans_hom]
    rw [← Category.assoc, f.comm_i, Category.assoc, g.comm_i, ← Category.assoc]
  comm_p := by
    simp only [Iso.trans_hom]
    rw [Category.assoc, g.comm_p, f.comm_p]

/-- Invert a forward pair and its two commuting equations. -/
def symm {E' E : FixedTargetExtension C X} (f : Hom E' E) : Hom E E' where
  a := f.a.symm
  b := f.b.symm
  comm_i := by
    apply (cancel_mono f.b.hom).1
    simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [f.comm_i, Iso.inv_hom_id_assoc]
  comm_p := by
    change f.b.inv ≫ E'.p = E.p
    rw [← f.comm_p, Iso.inv_hom_id_assoc]

end Hom

/-- The actual given-X row groupoid with componentwise forward-pair operations. -/
instance instGroupoid : Groupoid.{v} (FixedTargetExtension C X) where
  Hom E' E := Hom E' E
  id := Hom.refl
  comp := Hom.comp
  id_comp f := by
    apply Hom.ext <;> apply Iso.ext <;> simp [Hom.comp, Hom.refl]
  comp_id f := by
    apply Hom.ext <;> apply Iso.ext <;> simp [Hom.comp, Hom.refl]
  assoc f g h := by
    apply Hom.ext <;> apply Iso.ext <;> simp [Hom.comp]
  inv := Hom.symm
  inv_comp f := by
    apply Hom.ext <;> apply Iso.ext <;> simp [Hom.comp, Hom.symm, Hom.refl]
  comp_inv f := by
    apply Hom.ext <;> apply Iso.ext <;> simp [Hom.comp, Hom.symm, Hom.refl]

/-- The identity arrow has the identity kernel isomorphism. -/
@[simp] theorem id_a (E : FixedTargetExtension C X) : (𝟙 E : E ⟶ E).a = Iso.refl _ := rfl
/-- The identity arrow has the identity middle isomorphism. -/
@[simp] theorem id_b (E : FixedTargetExtension C X) : (𝟙 E : E ⟶ E).b = Iso.refl _ := rfl
/-- Composition retains the forward order of the kernel isomorphisms. -/
@[simp] theorem comp_a {E' E F : FixedTargetExtension C X} (f : E' ⟶ E) (g : E ⟶ F) :
    (f ≫ g).a = f.a ≪≫ g.a := rfl
/-- Composition retains the forward order of the middle isomorphisms. -/
@[simp] theorem comp_b {E' E F : FixedTargetExtension C X} (f : E' ⟶ E) (g : E ⟶ F) :
    (f ≫ g).b = f.b ≪≫ g.b := rfl

/-- The given row, as an object of the actual quotient-diagram category. -/
abbrev toExtension (E : FixedTargetExtension C X) : ExtensionCategory C :=
  ⟨ShortComplex.mk E.i E.p E.zero, E.admissible⟩

private theorem extension_hom_ext {E' E : ExtensionCategory C} {f g : E' ⟶ E}
    (ha : (ExtensionCategory.homNormalization f).hom.1.unop.hom =
      (ExtensionCategory.homNormalization g).hom.1.unop.hom)
    (hb : (ExtensionCategory.homNormalization f).hom.2.hom =
      (ExtensionCategory.homNormalization g).hom.2.hom) : f = g := by
  apply ExtensionCategory.homNormalization.injective
  apply Functor.Elements.hom_ext
  apply Prod.ext
  · apply Quiver.Hom.unop_inj
    exact InducedWideCategory.Hom.ext ha
  · exact InducedWideCategory.Hom.ext hb

/-- The specified given-X raw representative of a forward isomorphism pair. -/
def inclusionDiagram {E' E : FixedTargetExtension C X} (f : E' ⟶ E) :
    ExtensionDiagram E'.toExtension E.toExtension := by
  have hz : (f.a.inv ≫ E'.i) ≫ E'.p = 0 := by
    rw [Category.assoc, E'.zero, comp_zero]
  let e : ShortComplex.mk (f.a.inv ≫ E'.i) E'.p hz ≅ E'.toExtension.row :=
    ShortComplex.isoMk f.a.symm (Iso.refl _) (Iso.refl _) (by simp) (by simp)
  refine {
    alpha := f.a.inv
    alpha_admissible := IsAdmissibleMono.of_isIso _
    beta := f.b.hom
    beta_admissible := IsAdmissibleMono.of_isIso _
    D := X
    j := f.a.inv ≫ E'.i
    q := E'.p
    zero := hz
    admissible := isAdmissibleExact_of_iso e.symm E'.admissible
    lambda := 𝟙 X
    lambda_admissible := IsAdmissibleEpi.of_isIso _
    mu := 𝟙 X
    mu_admissible := IsAdmissibleMono.of_isIso _
    j_eq := rfl
    j_beta := ?_
    q_lambda := by simp
    q_mu := ?_ }
  · change (f.a.inv ≫ E'.i) ≫ f.b.hom = E.i
    rw [Category.assoc, f.comm_i, Iso.inv_hom_id_assoc]
  · change E'.p ≫ 𝟙 X = f.b.hom ≫ E.p
    rw [Category.comp_id, f.comm_p]

/-- All kernel, middle, and given-quotient formulas of the inclusion representative. -/
theorem inclusionDiagram_fields {E' E : FixedTargetExtension C X} (f : E' ⟶ E) :
    (inclusionDiagram f).alpha = f.a.inv ∧
    (inclusionDiagram f).beta = f.b.hom ∧
    (inclusionDiagram f).D = X ∧
    (inclusionDiagram f).q = E'.p ∧
    (inclusionDiagram f).lambda = 𝟙 X ∧
    (inclusionDiagram f).mu = 𝟙 X ∧
    (inclusionDiagram f).j = f.a.inv ≫ E'.i := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The given-X representative maps to the actual Quillen identity-span class. -/
theorem inclusion_target {E' E : FixedTargetExtension C X} (f : E' ⟶ E) :
    (ExtensionCategory.target (C := C)).map (ExtensionCategory.mkHom (inclusionDiagram f)) =
      𝟙 (⟨X⟩ : QuillenQ C) := by
  rw [ExtensionCategory.target_map_mkHom]
  rfl

/-- The inclusion representative lies over the literal target identity. -/
theorem inclusion_lift {E' E : FixedTargetExtension C X} (f : E' ⟶ E) :
    Functor.IsHomLift (ExtensionCategory.target (C := C)) (𝟙 (⟨X⟩ : QuillenQ C))
      (ExtensionCategory.mkHom (inclusionDiagram f)) := by
  apply IsHomLift.of_fac' _ _ _ rfl rfl
  simpa using inclusion_target f

/-- Inclusion by the actual identity-span raw quotient diagrams. -/
def fiberInclusion (X : C) : FixedTargetExtension C X ⥤
    Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C) where
  obj E := ⟨E.toExtension, rfl⟩
  map f := ⟨ExtensionCategory.mkHom (inclusionDiagram f), inclusion_lift f⟩
  map_id E := by
    apply Subtype.ext
    apply extension_hom_ext
    · simp only [ExtensionCategory.homNormalization_mkHom]
      rfl
    · simp only [ExtensionCategory.homNormalization_mkHom]
      rfl
  map_comp f g := by
    apply Subtype.ext
    apply extension_hom_ext
    · simp only [ExtensionCategory.homNormalization_mkHom]
      rfl
    · simp only [ExtensionCategory.homNormalization_mkHom]
      rfl

/-- Normalization of the inclusion retains the inverse kernel isomorphism. -/
@[simp] theorem inclusion_map_alpha {E' E : FixedTargetExtension C X} (f : E' ⟶ E) :
    (ExtensionCategory.homNormalization ((fiberInclusion X).map f).val).hom.1.unop.hom =
      f.a.inv := rfl

/-- Normalization of the inclusion retains the forward middle isomorphism. -/
@[simp] theorem inclusion_map_beta {E' E : FixedTargetExtension C X} (f : E' ⟶ E) :
    (ExtensionCategory.homNormalization ((fiberInclusion X).map f).val).hom.2.hom =
      f.b.hom := rfl

/-- Every actual fiber object retains A/B/i and casts only its given quotient endpoint. -/
def fromFiberObj (s : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)) :
    FixedTargetExtension C X := by
  let h : s.val.row.X₃ = X := congrArg QuillenQ.obj s.property
  have hz : s.val.row.f ≫ (s.val.row.g ≫ eqToHom h) = 0 := by
    rw [← Category.assoc, s.val.row.zero, zero_comp]
  let e : s.val.row ≅ ShortComplex.mk s.val.row.f (s.val.row.g ≫ eqToHom h) hz :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (eqToIso h) (by simp) (by simp)
  exact ⟨s.val.row.X₁, s.val.row.X₂, s.val.row.f, s.val.row.g ≫ eqToHom h, hz,
    isAdmissibleExact_of_iso e s.val.admissible⟩

/-- The reverse object retains the original kernel object. -/
@[simp] theorem fromFiberObj_A
    (s : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)) :
    (fromFiberObj s).A = s.val.row.X₁ := rfl

/-- The reverse object retains the original middle object. -/
@[simp] theorem fromFiberObj_B
    (s : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)) :
    (fromFiberObj s).B = s.val.row.X₂ := rfl

/-- The reverse object retains the original admissible mono. -/
@[simp] theorem fromFiberObj_i
    (s : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)) :
    (fromFiberObj s).i = s.val.row.f := rfl

/-- Only the quotient endpoint is cast in the reverse object. -/
@[simp] theorem fromFiberObj_p
    (s : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)) :
    (fromFiberObj s).p = s.val.row.g ≫ eqToHom (congrArg QuillenQ.obj s.property) := rfl

private def representative
    {s t : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)}
    (f : s ⟶ t) : ExtensionDiagram s.val t.val :=
  ExtensionDiagram.ofNormalization (ExtensionCategory.homNormalization f.val)

private theorem representative_eq
    {s t : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)}
    (f : s ⟶ t) : ExtensionCategory.mkHom (representative f) = f.val := by
  apply ExtensionCategory.homNormalization.injective
  rw [ExtensionCategory.homNormalization_mkHom]
  exact ExtensionDiagram.normalize_ofNormalization _

/-- Reverse every fiber arrow from its canonical quotient normalization and full C8. -/
def fromFiberMap
    {s t : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)}
    (f : s ⟶ t) : fromFiberObj s ⟶ fromFiberObj t := by
  let d := ExtensionDiagram.ofNormalization (ExtensionCategory.homNormalization f.val)
  have hd : ExtensionCategory.mkHom d = f.val := by
    apply ExtensionCategory.homNormalization.injective
    rw [ExtensionCategory.homNormalization_mkHom]
    exact ExtensionDiagram.normalize_ofNormalization _
  have h := ExtensionCategory.fiber_identity_span_reflection X f d hd
  letI : IsIso d.alpha := h.2.2.2.1
  letI : IsIso d.beta := h.2.2.2.2.1
  refine {
    a := (asIso d.alpha).symm
    b := asIso d.beta
    comm_i := ?_
    comm_p := ?_ }
  · change s.val.row.f ≫ d.beta = inv d.alpha ≫ t.val.row.f
    rw [← d.j_beta, d.j_eq]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  · change d.beta ≫ (t.val.row.g ≫ eqToHom (congrArg QuillenQ.obj t.property)) =
      s.val.row.g ≫ eqToHom (congrArg QuillenQ.obj s.property)
    rw [← Category.assoc, ← d.q_mu, Category.assoc, ← h.1, ← Category.assoc, d.q_lambda]

/-- The reverse kernel component is the canonical quotient-normalization component. -/
@[simp] theorem fromFiberMap_a_inv
    {s t : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)}
    (f : s ⟶ t) : (fromFiberMap f).a.inv =
      (ExtensionCategory.homNormalization f.val).hom.1.unop.hom := rfl

/-- The forward middle component is the canonical quotient-normalization component. -/
@[simp] theorem fromFiberMap_b_hom
    {s t : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)}
    (f : s ⟶ t) : (fromFiberMap f).b.hom =
      (ExtensionCategory.homNormalization f.val).hom.2.hom := rfl

/-- The reverse functor on every actual fiber object and quotient-diagram arrow. -/
def fromFiber (X : C) :
    Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C) ⥤
      FixedTargetExtension C X where
  obj := fromFiberObj
  map := fromFiberMap
  map_id s := by
    apply Hom.ext_inv
    · change (ExtensionCategory.homNormalization (𝟙 s.val)).hom.1.unop.hom = 𝟙 _
      rw [ExtensionCategory.homNormalization_id]
      rfl
    · change (ExtensionCategory.homNormalization (𝟙 s.val)).hom.2.hom = 𝟙 _
      rw [ExtensionCategory.homNormalization_id]
      rfl
  map_comp f g := by
    apply Hom.ext_inv
    · change (ExtensionCategory.homNormalization (f.val ≫ g.val)).hom.1.unop.hom =
        (ExtensionCategory.homNormalization g.val).hom.1.unop.hom ≫
          (ExtensionCategory.homNormalization f.val).hom.1.unop.hom
      rw [ExtensionCategory.homNormalization_comp]
      rfl
    · change (ExtensionCategory.homNormalization (f.val ≫ g.val)).hom.2.hom =
        (ExtensionCategory.homNormalization f.val).hom.2.hom ≫
          (ExtensionCategory.homNormalization g.val).hom.2.hom
      rw [ExtensionCategory.homNormalization_comp]
      rfl

/-- Every raw representative determines the same derived reverse isomorphism pair. -/
theorem fromFiber_map_components
    {s t : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)}
    (f : s ⟶ t) (d : ExtensionDiagram s.val t.val)
    (hd : ExtensionCategory.mkHom d = f.val) :
    ((fromFiber X).map f).a.inv = d.alpha ∧ ((fromFiber X).map f).b.hom = d.beta := by
  change (ExtensionCategory.homNormalization f.val).hom.1.unop.hom = d.alpha ∧
    (ExtensionCategory.homNormalization f.val).hom.2.hom = d.beta
  rw [← hd, ExtensionCategory.homNormalization_mkHom]
  exact ⟨rfl, rfl⟩

/-- The inverse hom-set correspondence at literal given-X rows. -/
def homFromFiber {E' E : FixedTargetExtension C X}
    (f : (fiberInclusion X).obj E' ⟶ (fiberInclusion X).obj E) : E' ⟶ E where
  a := (fromFiberMap f).a
  b := (fromFiberMap f).b
  comm_i := (fromFiberMap f).comm_i
  comm_p := by
    have h := (fromFiberMap f).comm_p
    change (fromFiberMap f).b.hom ≫ (E.p ≫ 𝟙 X) = E'.p ≫ 𝟙 X at h
    simpa using h

/-- The inverse hom-set correspondence retains every representative component. -/
theorem homFromFiber_components {E' E : FixedTargetExtension C X}
    (f : (fiberInclusion X).obj E' ⟶ (fiberInclusion X).obj E)
    (d : ExtensionDiagram E'.toExtension E.toExtension)
    (hd : ExtensionCategory.mkHom d = f.val) :
    (homFromFiber f).a.inv = d.alpha ∧ (homFromFiber f).b.hom = d.beta :=
  fromFiber_map_components f d hd

/-- The actual middle-lambda isomorphism identifies every raw class with the displayed one. -/
theorem representative_relation {E' E : FixedTargetExtension C X}
    (f : (fiberInclusion X).obj E' ⟶ (fiberInclusion X).obj E)
    (d : ExtensionDiagram E'.toExtension E.toExtension)
    (hd : ExtensionCategory.mkHom d = f.val) :
    ExtensionDiagram.Rel d (inclusionDiagram (homFromFiber f)) := by
  obtain ⟨ha, hb⟩ := homFromFiber_components f d hd
  obtain ⟨heq, hLambda, hMu, hAlpha, hBeta, rest⟩ :=
    ExtensionCategory.fiber_identity_span_reflection X f d hd
  let _ : IsIso d.lambda := hLambda
  have hlegs : d.lambda = d.mu := by simpa using heq
  refine ⟨ha.symm, hb.symm, asIso d.lambda, ?_, ?_, ?_⟩
  · exact d.q_lambda
  · change d.lambda ≫ 𝟙 X = d.lambda
    exact Category.comp_id _
  · change d.lambda ≫ 𝟙 X = d.mu
    exact (Category.comp_id _).trans hlegs

/-- The displayed representative recovers every actual fiber arrow at fixed endpoints. -/
theorem inclusion_homFromFiber {E' E : FixedTargetExtension C X}
    (f : (fiberInclusion X).obj E' ⟶ (fiberInclusion X).obj E) :
    (fiberInclusion X).map (homFromFiber f) = f := by
  let d := representative f
  have hd : ExtensionCategory.mkHom d = f.val := representative_eq f
  apply Subtype.ext
  exact ((ExtensionCategory.mkHom_eq_iff d (inclusionDiagram (homFromFiber f))).2
    (representative_relation f d hd)).symm.trans hd

/-- Reverse correspondence recovers every forward pair exactly. -/
theorem homFromFiber_inclusion {E' E : FixedTargetExtension C X} (f : E' ⟶ E) :
    homFromFiber ((fiberInclusion X).map f) = f := by
  apply Hom.ext_inv
  · change (fromFiberMap ((fiberInclusion X).map f)).a.inv = f.a.inv
    rw [fromFiberMap_a_inv, inclusion_map_alpha]
  · change (fromFiberMap ((fiberInclusion X).map f)).b.hom = f.b.hom
    rw [fromFiberMap_b_hom, inclusion_map_beta]

/-- The complete hom-set correspondence with its actual raw formulas. -/
def homEquiv (E' E : FixedTargetExtension C X) : (E' ⟶ E) ≃
    ((fiberInclusion X).obj E' ⟶ (fiberInclusion X).obj E) where
  toFun := (fiberInclusion X).map
  invFun := homFromFiber
  left_inv := homFromFiber_inclusion
  right_inv := inclusion_homFromFiber

/-- The all-row unit has identity A/B components. -/
def unitApp (E : FixedTargetExtension C X) :
    E ≅ (fromFiber X).obj ((fiberInclusion X).obj E) where
  hom := {
    a := Iso.refl _
    b := Iso.refl _
    comm_i := by change E.i ≫ 𝟙 _ = 𝟙 _ ≫ E.i; simp
    comm_p := by change 𝟙 _ ≫ (E.p ≫ 𝟙 X) = E.p; simp }
  inv := {
    a := Iso.refl _
    b := Iso.refl _
    comm_i := by change E.i ≫ 𝟙 _ = 𝟙 _ ≫ E.i; simp
    comm_p := by change 𝟙 _ ≫ E.p = E.p ≫ 𝟙 X; simp }
  hom_inv_id := by
    apply Hom.ext <;> apply Iso.ext <;> simp
  inv_hom_id := by
    apply Hom.ext <;> apply Iso.ext <;> simp

/-- The unit forward arrow has the identity kernel component. -/
@[simp] theorem unitApp_hom_a (E : FixedTargetExtension C X) :
    (unitApp E).hom.a = Iso.refl _ := rfl
/-- The unit forward arrow has the identity middle component. -/
@[simp] theorem unitApp_hom_b (E : FixedTargetExtension C X) :
    (unitApp E).hom.b = Iso.refl _ := rfl
/-- The unit inverse has the identity kernel component. -/
@[simp] theorem unitApp_inv_a (E : FixedTargetExtension C X) :
    (unitApp E).inv.a = Iso.refl _ := rfl
/-- The unit inverse has the identity middle component. -/
@[simp] theorem unitApp_inv_b (E : FixedTargetExtension C X) :
    (unitApp E).inv.b = Iso.refl _ := rfl

/-- The natural unit comparison for every actual given-X row. -/
def fiberUnit (X : C) : 𝟭 (FixedTargetExtension C X) ≅ fiberInclusion X ⋙ fromFiber X :=
  NatIso.ofComponents unitApp (by
    intro E' E f
    apply Hom.ext_inv
    · change ((unitApp E).hom.a.inv ≫ f.a.inv) =
        (fromFiberMap ((fiberInclusion X).map f)).a.inv ≫ (unitApp E').hom.a.inv
      simp only [unitApp_hom_a, Iso.refl_inv, fromFiberMap_a_inv, inclusion_map_alpha]
      exact (Category.id_comp f.a.inv).trans (Category.comp_id f.a.inv).symm
    · change f.b.hom ≫ (unitApp E).hom.b.hom =
        (unitApp E').hom.b.hom ≫ (fromFiberMap ((fiberInclusion X).map f)).b.hom
      simp only [unitApp_hom_b, Iso.refl_hom, fromFiberMap_b_hom, inclusion_map_beta,
        Category.id_comp, Category.comp_id])

/-- The all-object counit uses the original middle row and only the quotient endpoint cast. -/
def counitDiagram
    (s : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)) :
    ExtensionDiagram ((fiberInclusion X).obj ((fromFiber X).obj s)).val s.val where
  alpha := 𝟙 s.val.row.X₁
  alpha_admissible := by
    change IsAdmissibleMono (𝟙 s.val.row.X₁)
    exact IsAdmissibleMono.of_isIso _
  beta := 𝟙 s.val.row.X₂
  beta_admissible := by
    change IsAdmissibleMono (𝟙 s.val.row.X₂)
    exact IsAdmissibleMono.of_isIso _
  D := s.val.row.X₃
  j := s.val.row.f
  q := s.val.row.g
  zero := s.val.row.zero
  admissible := s.val.admissible
  lambda := eqToHom (congrArg QuillenQ.obj s.property)
  lambda_admissible := IsAdmissibleEpi.of_isIso _
  mu := 𝟙 s.val.row.X₃
  mu_admissible := IsAdmissibleMono.of_isIso _
  j_eq := by
    change s.val.row.f = 𝟙 _ ≫ s.val.row.f
    exact (Category.id_comp _).symm
  j_beta := by
    change s.val.row.f ≫ 𝟙 _ = s.val.row.f
    exact Category.comp_id _
  q_lambda := rfl
  q_mu := by
    change s.val.row.g ≫ 𝟙 _ = 𝟙 _ ≫ s.val.row.g
    rw [Category.comp_id, Category.id_comp]

/-- The raw inverse comparison retains the original quotient and middle row as well. -/
def counitInverseDiagram
    (s : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)) :
    ExtensionDiagram s.val ((fiberInclusion X).obj ((fromFiber X).obj s)).val where
  alpha := 𝟙 s.val.row.X₁
  alpha_admissible := by
    change IsAdmissibleMono (𝟙 s.val.row.X₁)
    exact IsAdmissibleMono.of_isIso _
  beta := 𝟙 s.val.row.X₂
  beta_admissible := by
    change IsAdmissibleMono (𝟙 s.val.row.X₂)
    exact IsAdmissibleMono.of_isIso _
  D := s.val.row.X₃
  j := s.val.row.f
  q := s.val.row.g
  zero := s.val.row.zero
  admissible := s.val.admissible
  lambda := 𝟙 s.val.row.X₃
  lambda_admissible := IsAdmissibleEpi.of_isIso _
  mu := eqToHom (congrArg QuillenQ.obj s.property)
  mu_admissible := IsAdmissibleMono.of_isIso _
  j_eq := by
    change s.val.row.f = 𝟙 _ ≫ s.val.row.f
    exact (Category.id_comp _).symm
  j_beta := by
    change s.val.row.f ≫ 𝟙 _ = s.val.row.f
    exact Category.comp_id _
  q_lambda := by
    exact Category.comp_id _
  q_mu := by
    change s.val.row.g ≫ eqToHom (congrArg QuillenQ.obj s.property) =
      𝟙 _ ≫ (s.val.row.g ≫ eqToHom (congrArg QuillenQ.obj s.property))
    exact (Category.id_comp _).symm

/-- The all-object counit representative lies over the literal given-target identity. -/
theorem counit_lift
    (s : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)) :
    Functor.IsHomLift (ExtensionCategory.target (C := C)) (𝟙 (⟨X⟩ : QuillenQ C))
      (ExtensionCategory.mkHom (counitDiagram s)) := by
  rcases s with ⟨⟨@⟨A, B, Y, i, p, w⟩, hExact⟩, hY⟩
  have hx : Y = X := congrArg QuillenQ.obj hY
  subst Y
  apply IsHomLift.of_fac' _ _ _ rfl hY
  rw [ExtensionCategory.target_map_mkHom]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- The raw inverse counit representative lies over the same literal identity. -/
theorem counitInverse_lift
    (s : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)) :
    Functor.IsHomLift (ExtensionCategory.target (C := C)) (𝟙 (⟨X⟩ : QuillenQ C))
      (ExtensionCategory.mkHom (counitInverseDiagram s)) := by
  rcases s with ⟨⟨@⟨A, B, Y, i, p, w⟩, hExact⟩, hY⟩
  have hx : Y = X := congrArg QuillenQ.obj hY
  subst Y
  apply IsHomLift.of_fac' _ _ _ hY rfl
  rw [ExtensionCategory.target_map_mkHom]
  simp only [eqToHom_refl, Category.comp_id]
  rfl

/-- The counit inverse is the standard inverse derived from accepted full C8. -/
def counitApp
    (s : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)) :
    (fiberInclusion X).obj ((fromFiber X).obj s) ≅ s :=
  asIso (⟨ExtensionCategory.mkHom (counitDiagram s), counit_lift s⟩ :
    (fiberInclusion X).obj ((fromFiber X).obj s) ⟶ s)

/-- The counit forward map is the actual original-row comparison diagram. -/
theorem counitApp_hom_val
    (s : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)) :
    (counitApp s).hom.val = ExtensionCategory.mkHom (counitDiagram s) := rfl

/-- The two explicit counit diagrams satisfy both actual quotient-category inverse laws. -/
theorem counit_raw_inverse_laws
    (s : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)) :
    ExtensionCategory.mkHom (counitDiagram s) ≫
      ExtensionCategory.mkHom (counitInverseDiagram s) =
        𝟙 ((fiberInclusion X).obj ((fromFiber X).obj s)).val ∧
    ExtensionCategory.mkHom (counitInverseDiagram s) ≫
      ExtensionCategory.mkHom (counitDiagram s) = 𝟙 s.val := by
  constructor <;> apply extension_hom_ext
  all_goals simp only [ExtensionCategory.homNormalization_comp,
    ExtensionCategory.homNormalization_mkHom, ExtensionCategory.homNormalization_id]
  all_goals change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
  all_goals exact Category.id_comp _

/-- The standard derived counit inverse equals the explicit raw inverse diagram. -/
theorem counitApp_inv_val
    (s : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)) :
    (counitApp s).inv.val = ExtensionCategory.mkHom (counitInverseDiagram s) := by
  let g : s ⟶ (fiberInclusion X).obj ((fromFiber X).obj s) :=
    ⟨ExtensionCategory.mkHom (counitInverseDiagram s), counitInverse_lift s⟩
  have hg : (counitApp s).hom ≫ g = 𝟙 _ := by
    apply Subtype.ext
    exact (counit_raw_inverse_laws s).1
  have hginv : g = (counitApp s).inv := IsIso.eq_inv_of_hom_inv_id hg
  exact (congrArg Subtype.val hginv).symm

/-- The counit retains the identity kernel component. -/
@[simp] theorem counitApp_alpha
    (s : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)) :
    (ExtensionCategory.homNormalization (counitApp s).hom.val).hom.1.unop.hom = 𝟙 _ := rfl

/-- The counit retains the identity middle component. -/
@[simp] theorem counitApp_beta
    (s : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)) :
    (ExtensionCategory.homNormalization (counitApp s).hom.val).hom.2.hom = 𝟙 _ := rfl

/-- The natural counit comparison on every object of the actual strict fiber. -/
def fiberCounit (X : C) : fromFiber X ⋙ fiberInclusion X ≅
    𝟭 (Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)) :=
  NatIso.ofComponents counitApp (by
    intro s t f
    apply Subtype.ext
    change ((fiberInclusion X).map ((fromFiber X).map f)).val ≫ (counitApp t).hom.val =
      (counitApp s).hom.val ≫ f.val
    apply extension_hom_ext
    · change 𝟙 _ ≫ (fromFiberMap f).a.inv =
        (ExtensionCategory.homNormalization f.val).hom.1.unop.hom ≫ 𝟙 _
      simp only [fromFiberMap_a_inv, Category.id_comp, Category.comp_id]
    · change (fromFiberMap f).b.hom ≫ 𝟙 _ =
        𝟙 _ ≫ (ExtensionCategory.homNormalization f.val).hom.2.hom
      simp only [fromFiberMap_b_hom, Category.id_comp, Category.comp_id])

/-- The full constructed equivalence, with both actual comparison functors and formulas. -/
def fiberEquivalence (X : C) : FixedTargetExtension C X ≌
    Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C) where
  functor := fiberInclusion X
  inverse := fromFiber X
  unitIso := fiberUnit X
  counitIso := fiberCounit X
  functor_unitIso_comp E := by
    apply Subtype.ext
    apply extension_hom_ext
    · change 𝟙 E.A ≫ 𝟙 E.A = 𝟙 E.A
      exact Category.id_comp _
    · change 𝟙 E.B ≫ 𝟙 E.B = 𝟙 E.B
      exact Category.id_comp _

/-- The strict-fiber groupoid keeps the actual quotient-diagram category and C8 inverses. -/
@[instance_reducible] def actualFiberGroupoid (X : C) :
    Groupoid (Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)) :=
  Groupoid.ofIsIso (fun f => ExtensionCategory.fiber_morphism_isIso X f)

end FixedTargetExtension

end AlgebraicKTheory

end
