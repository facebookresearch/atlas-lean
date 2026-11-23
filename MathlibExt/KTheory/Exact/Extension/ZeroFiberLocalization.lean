/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.Fibered
public import MathlibExt.KTheory.Exact.Extension.Fiber
public import MathlibExt.CategoryTheory.ExactCategory.Zero
public import Mathlib.CategoryTheory.Core
public import MathlibExt.KTheory.Exact.Extension.LocalizedFiber
public import MathlibExt.CategoryTheory.Limits.Shapes.CoreBiproductMonoidal
public import MathlibExt.CategoryTheory.Monoidal.ActionLocalization

/-!
# The actual fixed-zero extension groupoid and the original core

Weibel IV.7.4.1, printed329/PDF337, compares the original zero fiber with
S = iso C by A ↦ (A --id→ A --0→ 0). The kernel and middle projections are
related through the actual row map i, whose invertibility is derived from
admissible exactness and the original zero target. This is the categorical
prerequisite for the two zero-span base changes in Exercise IV.7.5.

All object and Hom universes remain independent. No splitting, Balanced
category, equivalence, or invertibility witness is supplied as a premise.
-/

@[expose] public section

universe u v

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject

namespace AlgebraicKTheory.FixedTargetExtension

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The literal original identity row with the given chosen zero quotient. -/
def zeroRow (A : Core C) : FixedTargetExtension C (0 : C) where
  A := A.of
  B := A.of
  i := 𝟙 A.of
  p := 0
  zero := by simp
  admissible := by exact isAdmissibleExact_id_zero (isZero_zero C)

/-- The identity row retains the original kernel object. -/
theorem zeroRow_A (A : Core C) : (zeroRow A).A = A.of := rfl

/-- It retains the original middle object. -/
theorem zeroRow_B (A : Core C) : (zeroRow A).B = A.of := rfl

/-- Its first map is the literal identity. -/
theorem zeroRow_i (A : Core C) : (zeroRow A).i = 𝟙 A.of := rfl

/-- Its quotient map has the given zero target. -/
theorem zeroRow_p (A : Core C) : (zeroRow A).p = (0 : A.of ⟶ (0 : C)) := rfl

/-- The original core isomorphism acts forwards on both row objects. -/
def zeroRowMap {A B : Core C} (f : A ⟶ B) : zeroRow A ⟶ zeroRow B where
  a := f.iso
  b := f.iso
  comm_i := by
    change (𝟙 A.of) ≫ f.iso.hom = f.iso.hom ≫ (𝟙 B.of)
    exact (Category.id_comp f.iso.hom).trans (Category.comp_id f.iso.hom).symm
  comm_p := by
    change f.iso.hom ≫ (0 : B.of ⟶ (0 : C)) = (0 : A.of ⟶ (0 : C))
    exact comp_zero (f := f.iso.hom)

/-- The kernel component is the actual core isomorphism. -/
theorem zeroRowMap_a {A B : Core C} (f : A ⟶ B) : (zeroRowMap f).a = f.iso := rfl

/-- The middle component is that same original isomorphism. -/
theorem zeroRowMap_b {A B : Core C} (f : A ⟶ B) : (zeroRowMap f).b = f.iso := rfl

/-- The actual core-to-zero-fiber functor. -/
def zeroRowFunctor : Core C ⥤ FixedTargetExtension C (0 : C) where
  obj := zeroRow
  map := zeroRowMap
  map_id A := by
    apply Hom.ext <;> rfl
  map_comp f g := by
    apply Hom.ext <;> rfl

/-- Extract the original kernel object and the forward kernel isomorphism. -/
def zeroKernelFunctor : FixedTargetExtension C (0 : C) ⥤ Core C where
  obj E := ⟨E.A⟩
  map f := ⟨f.a⟩
  map_id _E := rfl
  map_comp _f _g := rfl

/-- Exact object formula for the kernel projection. -/
theorem zeroKernelFunctor_obj (E : FixedTargetExtension C (0 : C)) :
    (zeroKernelFunctor (C := C)).obj E = (⟨E.A⟩ : Core C) := rfl

/-- Exact arrow formula for that projection. -/
theorem zeroKernelFunctor_map_iso {E F : FixedTargetExtension C (0 : C)} (f : E ⟶ F) :
    ((zeroKernelFunctor (C := C)).map f).iso = f.a := rfl

/-- Extract the original middle object and the forward middle isomorphism. -/
def zeroMiddleFunctor : FixedTargetExtension C (0 : C) ⥤ Core C where
  obj E := ⟨E.B⟩
  map f := ⟨f.b⟩
  map_id _E := rfl
  map_comp _f _g := rfl

/-- Exact object formula for the middle projection. -/
theorem zeroMiddleFunctor_obj (E : FixedTargetExtension C (0 : C)) :
    (zeroMiddleFunctor (C := C)).obj E = (⟨E.B⟩ : Core C) := rfl

/-- Exact arrow formula for that projection. -/
theorem zeroMiddleFunctor_map_iso {E F : FixedTargetExtension C (0 : C)} (f : E ⟶ F) :
    ((zeroMiddleFunctor (C := C)).map f).iso = f.b := rfl

/-- Invertibility follows from the actual admissible exact row with zero target. -/
theorem zero_i_isIso (E : FixedTargetExtension C (0 : C)) : IsIso E.i :=
  isIso_f_of_isAdmissibleExact_of_isZero
    (S := E.toExtension.row) E.admissible (isZero_zero C)

/-- The actual row map compares the kernel and middle projections in the core. -/
def zeroKernelMiddleIso : zeroKernelFunctor (C := C) ≅ zeroMiddleFunctor :=
  NatIso.ofComponents
    (fun E => Core.isoMk
      (@CategoryTheory.asIso C _ E.A E.B E.i (zero_i_isIso E)))
    (by
      intro E F f
      apply Core.hom_ext
      change f.a.hom ≫ F.i = E.i ≫ f.b.hom
      exact f.comm_i.symm)

/-- The natural comparison is the original row map, not a chosen replacement. -/
theorem zeroKernelMiddleIso_hom_app_iso_hom (E : FixedTargetExtension C (0 : C)) :
    ((zeroKernelMiddleIso (C := C)).hom.app E).iso.hom = E.i := rfl

/-- The core-to-row-to-kernel composite is compared with the literal original core. -/
def zeroCoreUnit : 𝟭 (Core C) ≅ zeroRowFunctor (C := C) ⋙ zeroKernelFunctor :=
  NatIso.ofComponents (fun A => Iso.refl A) (by
    intro A B f
    apply Core.hom_ext
    change f.iso.hom ≫ 𝟙 B.of = 𝟙 A.of ≫ f.iso.hom
    exact (Category.comp_id f.iso.hom).trans (Category.id_comp f.iso.hom).symm)

/-- The core unit preserves the original identity arrow. -/
theorem zeroCoreUnit_hom_app_iso_hom (A : Core C) :
    ((zeroCoreUnit (C := C)).hom.app A).iso.hom = 𝟙 A.of := rfl

/-- The original forward identity/kernel-map pair gives the counit row isomorphism. -/
def zeroFiberCounitComponent (E : FixedTargetExtension C (0 : C)) :
    zeroRow (⟨E.A⟩ : Core C) ≅ E := by
  let h : zeroRow (⟨E.A⟩ : Core C) ⟶ E :=
    { a := Iso.refl E.A
      b := @CategoryTheory.asIso C _ E.A E.B E.i (zero_i_isIso E)
      comm_i := by
        change 𝟙 E.A ≫ E.i = 𝟙 E.A ≫ E.i
        rfl
      comm_p := by
        change E.i ≫ E.p = 0
        exact E.zero }
  exact
    { hom := h
      inv := Hom.symm h
      hom_inv_id := Groupoid.comp_inv h
      inv_hom_id := Groupoid.inv_comp h }

/-- The actual counit kernel is the identity on the given kernel. -/
theorem zeroFiberCounitComponent_hom_a (E : FixedTargetExtension C (0 : C)) :
    (zeroFiberCounitComponent E).hom.a = Iso.refl E.A := rfl

/-- The actual counit middle arrow is the given row map. -/
theorem zeroFiberCounitComponent_hom_b_hom (E : FixedTargetExtension C (0 : C)) :
    (zeroFiberCounitComponent E).hom.b.hom = E.i := rfl

/-- The inverse middle component is characterized by the actual inverse law. -/
theorem zeroFiberCounitComponent_inv_b_hom_comp_i (E : FixedTargetExtension C (0 : C)) :
    (zeroFiberCounitComponent E).inv.b.hom ≫ E.i = 𝟙 E.B := by
  let e := zeroFiberCounitComponent E
  have hPair := congrArg (fun f : E ⟶ E => f.b.hom) e.inv_hom_id
  have h : e.inv.b.hom ≫ e.hom.b.hom = 𝟙 E.B := by
    simpa only [comp_b, Iso.trans_hom, id_b, Iso.refl_hom] using hPair
  have hi : e.hom.b.hom = E.i := zeroFiberCounitComponent_hom_b_hom E
  exact (congrArg (fun k : E.A ⟶ E.B => e.inv.b.hom ≫ k) hi).symm.trans h

/-- The row comparison is natural for the original forward a/b isomorphism pairs. -/
def zeroFiberCounit : zeroKernelFunctor (C := C) ⋙ zeroRowFunctor ≅
    𝟭 (FixedTargetExtension C (0 : C)) :=
  NatIso.ofComponents zeroFiberCounitComponent (by
    intro E F f
    apply Hom.ext
    · apply Iso.ext
      change f.a.hom ≫ 𝟙 F.A = 𝟙 E.A ≫ f.a.hom
      exact (Category.comp_id f.a.hom).trans (Category.id_comp f.a.hom).symm
    · apply Iso.ext
      change f.a.hom ≫ F.i = E.i ≫ f.b.hom
      exact f.comm_i.symm)

/-- The triangle retains the actual identity row and original core arrow. -/
theorem zeroCore_triangle (A : Core C) :
    (zeroRowFunctor (C := C)).map ((zeroCoreUnit (C := C)).hom.app A) ≫
        (zeroFiberCounit (C := C)).hom.app ((zeroRowFunctor (C := C)).obj A) =
      𝟙 ((zeroRowFunctor (C := C)).obj A) := by
  apply Hom.ext <;> apply Iso.ext
  · change 𝟙 A.of ≫ 𝟙 A.of = 𝟙 A.of
    exact Category.id_comp _
  · change 𝟙 A.of ≫ 𝟙 A.of = 𝟙 A.of
    exact Category.id_comp _

/-- The actual core and the original fixed-zero fiber are equivalent by the constructed maps. -/
def coreZeroFiberEquivalence : Core C ≌ FixedTargetExtension C (0 : C) where
  functor := zeroRowFunctor
  inverse := zeroKernelFunctor
  unitIso := zeroCoreUnit
  counitIso := zeroFiberCounit
  functor_unitIso_comp A := zeroCore_triangle A

/-- The forward equivalence keeps the actual literal identity row. -/
theorem coreZeroFiberEquivalence_functor_obj (A : Core C) :
    (coreZeroFiberEquivalence (C := C)).functor.obj A = zeroRow A := rfl

/-- The inverse retains the original given kernel object. -/
theorem coreZeroFiberEquivalence_inverse_obj (E : FixedTargetExtension C (0 : C)) :
    (coreZeroFiberEquivalence (C := C)).inverse.obj E = (⟨E.A⟩ : Core C) := rfl

/-- The inverse arrow is the original forward kernel isomorphism. -/
theorem coreZeroFiberEquivalence_inverse_map_iso
    {E F : FixedTargetExtension C (0 : C)} (f : E ⟶ F) :
    ((coreZeroFiberEquivalence (C := C)).inverse.map f).iso = f.a := rfl

end AlgebraicKTheory.FixedTargetExtension

end

/-!
# The two actual zero-span row lifts

Weibel IV.7.7–7.8 and Exercise IV.7.5 identify the contravariant base changes
along 0 ← 0 → X and 0 ← X → X with the original kernel and middle rows.
The diagrams below retain each given quotient. Their cartesian property comes
from the proved original extension target. An arbitrary chosen pullback is
compared by an isomorphism with the canonical row, rather than identified by
an equality of chosen objects. No homotopy-fibration or based comparison is claimed.
-/

noncomputable section

namespace AlgebraicKTheory.ExtensionCategory

set_option autoImplicit false

open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] target_isPreFibered

/-- The literal admissible mono span from the original zero object to X. -/
def zeroMonoSpan (X : C) : QuillenSpan (0 : C) X where
  apex := (0 : C)
  l := 𝟙 (0 : C)
  r := (0 : (0 : C) ⟶ X)
  wl := by exact IsAdmissibleEpi.id (0 : C)
  wr := by exact IsAdmissibleMono.fromZero (0 : (0 : C) ⟶ X)

/-- The literal admissible epi span from the original zero object to X. -/
def zeroEpiSpan (X : C) : QuillenSpan (0 : C) X where
  apex := X
  l := (0 : X ⟶ (0 : C))
  r := 𝟙 X
  wl := by exact isAdmissibleEpi_g (isAdmissibleExact_id_zero (A := X) (isZero_zero C))
  wr := by exact IsAdmissibleMono.id X

/-- The actual Q arrow represented by the zero-apex span. -/
def zeroMonoHom (X : C) : (⟨0⟩ : QuillenQ C) ⟶ (⟨X⟩ : QuillenQ C) :=
  QuillenQ.mkHom (X := ⟨0⟩) (Y := ⟨X⟩) (zeroMonoSpan X)

/-- The actual Q arrow represented by the X-apex span. -/
def zeroEpiHom (X : C) : (⟨0⟩ : QuillenQ C) ⟶ (⟨X⟩ : QuillenQ C) :=
  QuillenQ.mkHom (X := ⟨0⟩) (Y := ⟨X⟩) (zeroEpiSpan X)

/-- Pulling the original row along the zero mono has canonical kernel row. -/
def zeroMonoDiagram {X : C} (E : FixedTargetExtension C X) :
    ExtensionDiagram (FixedTargetExtension.zeroRow (⟨E.A⟩ : Core C)).toExtension
      E.toExtension where
  alpha := 𝟙 E.A
  alpha_admissible := by exact IsAdmissibleMono.id E.A
  beta := E.i
  beta_admissible := by exact isAdmissibleMono_f E.admissible
  D := (0 : C)
  j := 𝟙 E.A
  q := (0 : E.A ⟶ (0 : C))
  zero := by
    change (𝟙 E.A) ≫ (0 : E.A ⟶ (0 : C)) = (0 : E.A ⟶ (0 : C))
    exact Category.id_comp _
  admissible := by exact isAdmissibleExact_id_zero (isZero_zero C)
  lambda := 𝟙 (0 : C)
  lambda_admissible := by exact IsAdmissibleEpi.id (0 : C)
  mu := (0 : (0 : C) ⟶ X)
  mu_admissible := by exact IsAdmissibleMono.fromZero (0 : (0 : C) ⟶ X)
  j_eq := by exact (Category.id_comp (𝟙 E.A)).symm
  j_beta := by exact Category.id_comp E.i
  q_lambda := by exact Category.comp_id (0 : E.A ⟶ (0 : C))
  q_mu := by
    change (0 : E.A ⟶ (0 : C)) ≫ (0 : (0 : C) ⟶ X) = E.i ≫ E.p
    exact (zero_comp (f := (0 : (0 : C) ⟶ X))).trans E.zero.symm

/-- Pulling the original row along the zero epi has canonical middle row. -/
def zeroEpiDiagram {X : C} (E : FixedTargetExtension C X) :
    ExtensionDiagram (FixedTargetExtension.zeroRow (⟨E.B⟩ : Core C)).toExtension
      E.toExtension where
  alpha := E.i
  alpha_admissible := by exact isAdmissibleMono_f E.admissible
  beta := 𝟙 E.B
  beta_admissible := by exact IsAdmissibleMono.id E.B
  D := X
  j := E.i
  q := E.p
  zero := E.zero
  admissible := by exact E.admissible
  lambda := (0 : X ⟶ (0 : C))
  lambda_admissible := by
    exact isAdmissibleEpi_g (isAdmissibleExact_id_zero (A := X) (isZero_zero C))
  mu := 𝟙 X
  mu_admissible := by exact IsAdmissibleMono.id X
  j_eq := by exact (Category.comp_id E.i).symm
  j_beta := by exact Category.comp_id E.i
  q_lambda := by
    change E.p ≫ (0 : X ⟶ (0 : C)) = (0 : E.B ⟶ (0 : C))
    exact comp_zero (f := E.p)
  q_mu := by exact (Category.comp_id E.p).trans (Category.id_comp E.p).symm

/-- The zero-mono diagram retains the literal reverse kernel and forward middle maps. -/
theorem zeroMonoDiagram_fields {X : C} (E : FixedTargetExtension C X) :
    (zeroMonoDiagram E).alpha = 𝟙 E.A ∧ (zeroMonoDiagram E).beta = E.i ∧
      (zeroMonoDiagram E).D = (0 : C) := ⟨rfl, rfl, rfl⟩

/-- The zero-epi diagram retains the literal reverse kernel and forward middle maps. -/
theorem zeroEpiDiagram_fields {X : C} (E : FixedTargetExtension C X) :
    (zeroEpiDiagram E).alpha = E.i ∧ (zeroEpiDiagram E).beta = 𝟙 E.B ∧
      (zeroEpiDiagram E).D = X := ⟨rfl, rfl, rfl⟩

/-- Its right column is exactly the original zero-apex span. -/
theorem zeroMonoDiagram_span {X : C} (E : FixedTargetExtension C X) :
    (zeroMonoDiagram E).toQuillenSpan = zeroMonoSpan X := rfl

/-- Its right column is exactly the original X-apex span. -/
theorem zeroEpiDiagram_span {X : C} (E : FixedTargetExtension C X) :
    (zeroEpiDiagram E).toQuillenSpan = zeroEpiSpan X := rfl

/-- The actual quotient-diagram morphism from the canonical kernel row. -/
def zeroMonoLift {X : C} (E : FixedTargetExtension C X) :
    (FixedTargetExtension.zeroRow (⟨E.A⟩ : Core C)).toExtension ⟶ E.toExtension :=
  mkHom (zeroMonoDiagram E)

/-- The actual quotient-diagram morphism from the canonical middle row. -/
def zeroEpiLift {X : C} (E : FixedTargetExtension C X) :
    (FixedTargetExtension.zeroRow (⟨E.B⟩ : Core C)).toExtension ⟶ E.toExtension :=
  mkHom (zeroEpiDiagram E)

/-- The canonical kernel-row lift lies over the actual zero mono, with the given X. -/
theorem zeroMonoLift_target {X : C} (E : FixedTargetExtension C X) :
    (target (C := C)).map
      (X := (FixedTargetExtension.zeroRow (⟨E.A⟩ : Core C)).toExtension)
      (Y := E.toExtension) (zeroMonoLift E) = zeroMonoHom X := by
  have hMap : (target (C := C)).map
      (X := (FixedTargetExtension.zeroRow (⟨E.A⟩ : Core C)).toExtension)
      (Y := E.toExtension) (zeroMonoLift E) =
      QuillenQ.mkHom (X := ⟨0⟩) (Y := ⟨X⟩) (zeroMonoDiagram E).toQuillenSpan :=
    target_map_mkHom (zeroMonoDiagram E)
  have hSpan : QuillenQ.mkHom (X := ⟨0⟩) (Y := ⟨X⟩)
      (zeroMonoDiagram E).toQuillenSpan = zeroMonoHom X :=
    congrArg (fun d : QuillenSpan (0 : C) X =>
      QuillenQ.mkHom (X := ⟨0⟩) (Y := ⟨X⟩) d) (zeroMonoDiagram_span E)
  exact hMap.trans hSpan

/-- The canonical middle-row lift lies over the actual zero epi, with the given X. -/
theorem zeroEpiLift_target {X : C} (E : FixedTargetExtension C X) :
    (target (C := C)).map
      (X := (FixedTargetExtension.zeroRow (⟨E.B⟩ : Core C)).toExtension)
      (Y := E.toExtension) (zeroEpiLift E) = zeroEpiHom X := by
  have hMap : (target (C := C)).map
      (X := (FixedTargetExtension.zeroRow (⟨E.B⟩ : Core C)).toExtension)
      (Y := E.toExtension) (zeroEpiLift E) =
      QuillenQ.mkHom (X := ⟨0⟩) (Y := ⟨X⟩) (zeroEpiDiagram E).toQuillenSpan :=
    target_map_mkHom (zeroEpiDiagram E)
  have hSpan : QuillenQ.mkHom (X := ⟨0⟩) (Y := ⟨X⟩)
      (zeroEpiDiagram E).toQuillenSpan = zeroEpiHom X :=
    congrArg (fun d : QuillenSpan (0 : C) X =>
      QuillenQ.mkHom (X := ⟨0⟩) (Y := ⟨X⟩) d) (zeroEpiDiagram_span E)
  exact hMap.trans hSpan

/-- The lift property is derived from the actual target map equality. -/
theorem zeroMonoLift_isHomLift {X : C} (E : FixedTargetExtension C X) :
    Functor.IsHomLift (target (C := C)) (zeroMonoHom X) (zeroMonoLift E) := by
  have h : Functor.IsHomLift (target (C := C))
      ((target (C := C)).map
        (X := (FixedTargetExtension.zeroRow (⟨E.A⟩ : Core C)).toExtension)
        (Y := E.toExtension) (zeroMonoLift E)) (zeroMonoLift E) := .map (zeroMonoLift E)
  exact (zeroMonoLift_target E) ▸ h

/-- The lift property is derived from the actual target map equality. -/
theorem zeroEpiLift_isHomLift {X : C} (E : FixedTargetExtension C X) :
    Functor.IsHomLift (target (C := C)) (zeroEpiHom X) (zeroEpiLift E) := by
  have h : Functor.IsHomLift (target (C := C))
      ((target (C := C)).map
        (X := (FixedTargetExtension.zeroRow (⟨E.B⟩ : Core C)).toExtension)
        (Y := E.toExtension) (zeroEpiLift E)) (zeroEpiLift E) := .map (zeroEpiLift E)
  exact (zeroEpiLift_target E) ▸ h

/-- The canonical kernel-row lift is cartesian by the proved original target theorem. -/
theorem zeroMonoLift_isCartesian {X : C} (E : FixedTargetExtension C X) :
    Functor.IsCartesian (target (C := C)) (zeroMonoHom X) (zeroMonoLift E) := by
  let _ : Functor.IsHomLift (target (C := C)) (zeroMonoHom X) (zeroMonoLift E) :=
    zeroMonoLift_isHomLift E
  exact target_isCartesian (zeroMonoHom X) (zeroMonoLift E)

/-- The canonical middle-row lift is cartesian by the proved original target theorem. -/
theorem zeroEpiLift_isCartesian {X : C} (E : FixedTargetExtension C X) :
    Functor.IsCartesian (target (C := C)) (zeroEpiHom X) (zeroEpiLift E) := by
  let _ : Functor.IsHomLift (target (C := C)) (zeroEpiHom X) (zeroEpiLift E) :=
    zeroEpiLift_isHomLift E
  exact target_isCartesian (zeroEpiHom X) (zeroEpiLift E)

/-- A chosen pullback along the zero mono is isomorphic to the actual canonical kernel row. -/
def zeroMonoPullbackComparison {X : C} (E : FixedTargetExtension C X) :
    Functor.IsPreFibered.pullbackObj (p := target (C := C)) (a := E.toExtension)
      (show (target (C := C)).obj E.toExtension = (⟨X⟩ : QuillenQ C) from rfl)
      (zeroMonoHom X) ≅ (FixedTargetExtension.zeroRow (⟨E.A⟩ : Core C)).toExtension := by
  let _ : Functor.IsCartesian (target (C := C)) (zeroMonoHom X) (zeroMonoLift E) :=
    zeroMonoLift_isCartesian E
  exact Functor.IsCartesian.domainUniqueUpToIso (target (C := C)) (zeroMonoHom X)
    (zeroMonoLift E)
    (Functor.IsPreFibered.pullbackMap (p := target (C := C)) (a := E.toExtension)
      (show (target (C := C)).obj E.toExtension = (⟨X⟩ : QuillenQ C) from rfl)
      (zeroMonoHom X))

/-- A chosen pullback along the zero epi is isomorphic to the actual canonical middle row. -/
def zeroEpiPullbackComparison {X : C} (E : FixedTargetExtension C X) :
    Functor.IsPreFibered.pullbackObj (p := target (C := C)) (a := E.toExtension)
      (show (target (C := C)).obj E.toExtension = (⟨X⟩ : QuillenQ C) from rfl)
      (zeroEpiHom X) ≅ (FixedTargetExtension.zeroRow (⟨E.B⟩ : Core C)).toExtension := by
  let _ : Functor.IsCartesian (target (C := C)) (zeroEpiHom X) (zeroEpiLift E) :=
    zeroEpiLift_isCartesian E
  exact Functor.IsCartesian.domainUniqueUpToIso (target (C := C)) (zeroEpiHom X)
    (zeroEpiLift E)
    (Functor.IsPreFibered.pullbackMap (p := target (C := C)) (a := E.toExtension)
      (show (target (C := C)).obj E.toExtension = (⟨X⟩ : QuillenQ C) from rfl)
      (zeroEpiHom X))

/-- The chosen-to-canonical comparison factors the actual chosen mono-span lift. -/
theorem zeroMonoPullbackComparison_hom_fac {X : C} (E : FixedTargetExtension C X) :
    (zeroMonoPullbackComparison E).hom ≫ zeroMonoLift E =
      Functor.IsPreFibered.pullbackMap (p := target (C := C)) (a := E.toExtension)
        (show (target (C := C)).obj E.toExtension = (⟨X⟩ : QuillenQ C) from rfl)
        (zeroMonoHom X) := by
  let _ : Functor.IsCartesian (target (C := C)) (zeroMonoHom X) (zeroMonoLift E) :=
    zeroMonoLift_isCartesian E
  exact Functor.IsCartesian.fac (target (C := C)) (zeroMonoHom X) (zeroMonoLift E)
    (Functor.IsPreFibered.pullbackMap (p := target (C := C)) (a := E.toExtension)
      (show (target (C := C)).obj E.toExtension = (⟨X⟩ : QuillenQ C) from rfl)
      (zeroMonoHom X))

/-- The chosen-to-canonical comparison factors the actual chosen epi-span lift. -/
theorem zeroEpiPullbackComparison_hom_fac {X : C} (E : FixedTargetExtension C X) :
    (zeroEpiPullbackComparison E).hom ≫ zeroEpiLift E =
      Functor.IsPreFibered.pullbackMap (p := target (C := C)) (a := E.toExtension)
        (show (target (C := C)).obj E.toExtension = (⟨X⟩ : QuillenQ C) from rfl)
        (zeroEpiHom X) := by
  let _ : Functor.IsCartesian (target (C := C)) (zeroEpiHom X) (zeroEpiLift E) :=
    zeroEpiLift_isCartesian E
  exact Functor.IsCartesian.fac (target (C := C)) (zeroEpiHom X) (zeroEpiLift E)
    (Functor.IsPreFibered.pullbackMap (p := target (C := C)) (a := E.toExtension)
      (show (target (C := C)).obj E.toExtension = (⟨X⟩ : QuillenQ C) from rfl)
      (zeroEpiHom X))

/-- The canonical source of the mono pullback has the original kernel as middle object. -/
theorem zeroMonoCanonical_middle {X : C} (E : FixedTargetExtension C X) :
    (FixedTargetExtension.zeroRow (⟨E.A⟩ : Core C)).toExtension.row.X₂ = E.A := rfl

/-- The canonical source of the epi pullback has the original middle object. -/
theorem zeroEpiCanonical_middle {X : C} (E : FixedTargetExtension C X) :
    (FixedTargetExtension.zeroRow (⟨E.B⟩ : Core C)).toExtension.row.X₂ = E.B := rfl

end AlgebraicKTheory.ExtensionCategory

end

/-!
# Naturality of the canonical zero-span lifts

The actual fixed-X row inclusion and its kernel/middle projections give the
canonical contravariant zero-span functors. The two transformations below
are made from the original quotient diagrams, and their naturality follows
from the original row square and actual middle-component composition.
No selected cartesian pullback is identified with a projection by definition.
-/

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject

namespace AlgebraicKTheory.FixedTargetExtension

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- Forget only the literal categorical-fiber membership of the given fixed-X row. -/
def givenRowFunctor (X : C) : FixedTargetExtension C X ⥤ ExtensionCategory C :=
  AlgebraicKTheory.FixedTargetExtension.fiberInclusion X ⋙
    Functor.Fiber.fiberInclusion (p := ExtensionCategory.target (C := C))
      (S := (⟨X⟩ : QuillenQ C))

/-- This is the original row with its given quotient. -/
theorem givenRowFunctor_obj {X : C} (E : FixedTargetExtension C X) :
    (givenRowFunctor X).obj E = E.toExtension := rfl

/-- Its arrow is the actual identity-span quotient diagram for the forward a/b pair. -/
theorem givenRowFunctor_map {X : C} {E F : FixedTargetExtension C X} (f : E ⟶ F) :
    (givenRowFunctor X).map (X := E) (Y := F) f =
      ExtensionCategory.mkHom (inclusionDiagram f) := rfl

/-- The original kernel projection for every given X. -/
def kernelProjectionFunctor (X : C) : FixedTargetExtension C X ⥤ Core C where
  obj E := ⟨E.A⟩
  map {_E _F} f := ⟨f.a⟩
  map_id _E := rfl
  map_comp _f _g := rfl

/-- Its object is the original given kernel. -/
theorem kernelProjectionFunctor_obj {X : C} (E : FixedTargetExtension C X) :
    (kernelProjectionFunctor X).obj E = (⟨E.A⟩ : Core C) := rfl

/-- Its arrow is the original forward kernel isomorphism. -/
theorem kernelProjectionFunctor_map_iso {X : C} {E F : FixedTargetExtension C X}
    (f : E ⟶ F) : ((kernelProjectionFunctor X).map f).iso = f.a := rfl

/-- The original middle projection for every given X. -/
def middleProjectionFunctor (X : C) : FixedTargetExtension C X ⥤ Core C where
  obj E := ⟨E.B⟩
  map {_E _F} f := ⟨f.b⟩
  map_id _E := rfl
  map_comp _f _g := rfl

/-- Its object is the original given middle object. -/
theorem middleProjectionFunctor_obj {X : C} (E : FixedTargetExtension C X) :
    (middleProjectionFunctor X).obj E = (⟨E.B⟩ : Core C) := rfl

/-- Its arrow is the original forward middle isomorphism. -/
theorem middleProjectionFunctor_map_iso {X : C} {E F : FixedTargetExtension C X}
    (f : E ⟶ F) : ((middleProjectionFunctor X).map f).iso = f.b := rfl

/-- The actual canonical zero-mono source functor. -/
def kernelZeroRowFunctor (X : C) : FixedTargetExtension C X ⥤ ExtensionCategory C :=
  kernelProjectionFunctor X ⋙ zeroRowFunctor ⋙ givenRowFunctor (0 : C)

/-- The actual canonical zero-epi source functor. -/
def middleZeroRowFunctor (X : C) : FixedTargetExtension C X ⥤ ExtensionCategory C :=
  middleProjectionFunctor X ⋙ zeroRowFunctor ⋙ givenRowFunctor (0 : C)

private theorem kernel_zero_span_naturality {X : C}
    {E F : FixedTargetExtension C X} (f : E ⟶ F) :
    ExtensionCategory.mkHom
        (inclusionDiagram (zeroRowMap (show (⟨E.A⟩ : Core C) ⟶ ⟨F.A⟩ from ⟨f.a⟩))) ≫
      ExtensionCategory.zeroMonoLift F =
      ExtensionCategory.zeroMonoLift E ≫ ExtensionCategory.mkHom (inclusionDiagram f) := by
  let k : (⟨E.A⟩ : Core C) ⟶ ⟨F.A⟩ := ⟨f.a⟩
  let dK : ExtensionDiagram (zeroRow (⟨E.A⟩ : Core C)).toExtension
      (zeroRow (⟨F.A⟩ : Core C)).toExtension := inclusionDiagram (zeroRowMap k)
  let dE := ExtensionCategory.zeroMonoDiagram E
  let dF := ExtensionCategory.zeroMonoDiagram F
  let dG := inclusionDiagram f
  apply ExtensionCategory.hom_ext_of_middle
  have hK : dK.beta = f.a.hom := (inclusionDiagram_fields (zeroRowMap k)).2.1
  have hE : dE.beta = E.i := (ExtensionCategory.zeroMonoDiagram_fields E).2.1
  have hF : dF.beta = F.i := (ExtensionCategory.zeroMonoDiagram_fields F).2.1
  have hG : dG.beta = f.b.hom := (inclusionDiagram_fields f).2.1
  have hL : (ExtensionCategory.homNormalization
      ((ExtensionCategory.mkHom dK) ≫ ExtensionCategory.zeroMonoLift F)).hom.2.hom =
      f.a.hom ≫ F.i :=
    (ExtensionCategory.comp_beta dK dF).trans
      (congrArg₂ (fun (a : E.A ⟶ F.A) (b : F.A ⟶ F.B) => a ≫ b) hK hF)
  have hR : (ExtensionCategory.homNormalization
      (ExtensionCategory.zeroMonoLift E ≫ (ExtensionCategory.mkHom dG))).hom.2.hom =
      E.i ≫ f.b.hom :=
    (ExtensionCategory.comp_beta dE dG).trans
      (congrArg₂ (fun (a : E.A ⟶ E.B) (b : E.B ⟶ F.B) => a ≫ b) hE hG)
  exact hL.trans (f.comm_i.symm.trans hR.symm)

private theorem middle_zero_span_naturality {X : C}
    {E F : FixedTargetExtension C X} (f : E ⟶ F) :
    ExtensionCategory.mkHom
        (inclusionDiagram (zeroRowMap (show (⟨E.B⟩ : Core C) ⟶ ⟨F.B⟩ from ⟨f.b⟩))) ≫
      ExtensionCategory.zeroEpiLift F =
      ExtensionCategory.zeroEpiLift E ≫ ExtensionCategory.mkHom (inclusionDiagram f) := by
  let k : (⟨E.B⟩ : Core C) ⟶ ⟨F.B⟩ := ⟨f.b⟩
  let dK : ExtensionDiagram (zeroRow (⟨E.B⟩ : Core C)).toExtension
      (zeroRow (⟨F.B⟩ : Core C)).toExtension := inclusionDiagram (zeroRowMap k)
  let dE := ExtensionCategory.zeroEpiDiagram E
  let dF := ExtensionCategory.zeroEpiDiagram F
  let dG := inclusionDiagram f
  apply ExtensionCategory.hom_ext_of_middle
  have hK : dK.beta = f.b.hom := (inclusionDiagram_fields (zeroRowMap k)).2.1
  have hE : dE.beta = 𝟙 E.B := (ExtensionCategory.zeroEpiDiagram_fields E).2.1
  have hF : dF.beta = 𝟙 F.B := (ExtensionCategory.zeroEpiDiagram_fields F).2.1
  have hG : dG.beta = f.b.hom := (inclusionDiagram_fields f).2.1
  have hL : (ExtensionCategory.homNormalization
      ((ExtensionCategory.mkHom dK) ≫ ExtensionCategory.zeroEpiLift F)).hom.2.hom =
      f.b.hom :=
    (ExtensionCategory.comp_beta dK dF).trans
      ((congrArg₂ (fun (a : E.B ⟶ F.B) (b : F.B ⟶ F.B) => a ≫ b) hK hF).trans
        (Category.comp_id f.b.hom))
  have hR : (ExtensionCategory.homNormalization
      (ExtensionCategory.zeroEpiLift E ≫ (ExtensionCategory.mkHom dG))).hom.2.hom =
      f.b.hom :=
    (ExtensionCategory.comp_beta dE dG).trans
      ((congrArg₂ (fun (a : E.B ⟶ E.B) (b : E.B ⟶ F.B) => a ≫ b) hE hG).trans
        (Category.id_comp f.b.hom))
  exact hL.trans hR.symm

/-- The actual canonical kernel-row lift is natural for the original fixed-X arrows. -/
def kernelZeroSpanTransformation (X : C) : kernelZeroRowFunctor X ⟶ givenRowFunctor X where
  app E := ExtensionCategory.zeroMonoLift E
  naturality {E F} f := by
    change ExtensionCategory.mkHom
        (inclusionDiagram (zeroRowMap (show (⟨E.A⟩ : Core C) ⟶ ⟨F.A⟩ from ⟨f.a⟩))) ≫
      ExtensionCategory.zeroMonoLift F =
      ExtensionCategory.zeroMonoLift E ≫ ExtensionCategory.mkHom (inclusionDiagram f)
    exact kernel_zero_span_naturality f

/-- The actual canonical middle-row lift is natural for the original fixed-X arrows. -/
def middleZeroSpanTransformation (X : C) : middleZeroRowFunctor X ⟶ givenRowFunctor X where
  app E := ExtensionCategory.zeroEpiLift E
  naturality {E F} f := by
    change ExtensionCategory.mkHom
        (inclusionDiagram (zeroRowMap (show (⟨E.B⟩ : Core C) ⟶ ⟨F.B⟩ from ⟨f.b⟩))) ≫
      ExtensionCategory.zeroEpiLift F =
      ExtensionCategory.zeroEpiLift E ≫ ExtensionCategory.mkHom (inclusionDiagram f)
    exact middle_zero_span_naturality f

/-- The component is exactly the original canonical zero-mono diagram class. -/
theorem kernelZeroSpanTransformation_app {X : C} (E : FixedTargetExtension C X) :
    (kernelZeroSpanTransformation X).app E = ExtensionCategory.zeroMonoLift E := rfl

/-- The component is exactly the original canonical zero-epi diagram class. -/
theorem middleZeroSpanTransformation_app {X : C} (E : FixedTargetExtension C X) :
    (middleZeroSpanTransformation X).app E = ExtensionCategory.zeroEpiLift E := rfl

end AlgebraicKTheory.FixedTargetExtension

end

/-!
# Actual kernel and middle maps on the original localized fixed-X rows

Weibel IV.7.7–7.8 and Exercise IV.7.5 use the original kernel and middle
projections after the two zero-span base changes. The maps below apply those
projections to the actual positive-first SInverse rows. Every raw stabilizer
and denominator morphism is retained. No equivariance or equivalence result
is supplied as a premise, and no alternative group-completion model is used.

The epi-zero composite with eta_X has positive object A ⊞ X and the original
denominator. Its component shift by [X] is retained; no based identity or
homotopy-equivalence assertion is made here.
-/

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace AlgebraicKTheory.FixedTargetExtension

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] leftSumAction MonoidalActionCategory.diagonalAction

/-- The original kernel object paired with the original denominator. -/
def kernelLocalizedObject (a : localizedRows (C := C) X) : SInverse (Core C) (Core C) :=
  ⟨((⟨a.of.1.A⟩ : Core C), a.of.2)⟩

/-- The original middle object paired with the original denominator. -/
def middleLocalizedObject (a : localizedRows (C := C) X) : SInverse (Core C) (Core C) :=
  ⟨((⟨a.of.1.B⟩ : Core C), a.of.2)⟩

/-- The positive kernel object is literal. -/
theorem kernelLocalizedObject_positive (a : localizedRows (C := C) X) :
    (kernelLocalizedObject a).of.1 = (⟨a.of.1.A⟩ : Core C) := rfl

/-- The kernel projection preserves the actual denominator object. -/
theorem kernelLocalizedObject_denominator (a : localizedRows (C := C) X) :
    (kernelLocalizedObject a).of.2 = a.of.2 := rfl

/-- The positive middle object is literal. -/
theorem middleLocalizedObject_positive (a : localizedRows (C := C) X) :
    (middleLocalizedObject a).of.1 = (⟨a.of.1.B⟩ : Core C) := rfl

/-- The middle projection preserves the actual denominator object. -/
theorem middleLocalizedObject_denominator (a : localizedRows (C := C) X) :
    (middleLocalizedObject a).of.2 = a.of.2 := rfl

/-- Apply the actual forward kernel isomorphism to the numerator; retain T and delta. -/
def kernelLocalizedRawMap {a b : localizedRows (C := C) X}
    (r : MonoidalActionCategory.RawHom a b) :
    MonoidalActionCategory.RawHom (kernelLocalizedObject a) (kernelLocalizedObject b) where
  stabilizer := r.stabilizer
  hom := (⟨r.hom.1.a⟩, r.hom.2)

/-- Apply the actual forward middle isomorphism to the numerator; retain T and delta. -/
def middleLocalizedRawMap {a b : localizedRows (C := C) X}
    (r : MonoidalActionCategory.RawHom a b) :
    MonoidalActionCategory.RawHom (middleLocalizedObject a) (middleLocalizedObject b) where
  stabilizer := r.stabilizer
  hom := (⟨r.hom.1.b⟩, r.hom.2)

/-- The raw kernel map has the original numerator isomorphism. -/
theorem kernelLocalizedRawMap_iso {a b : localizedRows (C := C) X}
    (r : MonoidalActionCategory.RawHom a b) :
    (kernelLocalizedRawMap r).hom.1.iso = r.hom.1.a := rfl

/-- The raw middle map has the original numerator isomorphism. -/
theorem middleLocalizedRawMap_iso {a b : localizedRows (C := C) X}
    (r : MonoidalActionCategory.RawHom a b) :
    (middleLocalizedRawMap r).hom.1.iso = r.hom.1.b := rfl

/-- The kernel map retains the actual denominator morphism. -/
theorem kernelLocalizedRawMap_denominator {a b : localizedRows (C := C) X}
    (r : MonoidalActionCategory.RawHom a b) :
    (kernelLocalizedRawMap r).hom.2 = r.hom.2 := rfl

/-- The middle map retains the actual denominator morphism. -/
theorem middleLocalizedRawMap_denominator {a b : localizedRows (C := C) X}
    (r : MonoidalActionCategory.RawHom a b) :
    (middleLocalizedRawMap r).hom.2 = r.hom.2 := rfl

/-- The kernel map retains the actual stabilizer. -/
theorem kernelLocalizedRawMap_stabilizer {a b : localizedRows (C := C) X}
    (r : MonoidalActionCategory.RawHom a b) :
    (kernelLocalizedRawMap r).stabilizer = r.stabilizer := rfl

/-- The middle map retains the actual stabilizer. -/
theorem middleLocalizedRawMap_stabilizer {a b : localizedRows (C := C) X}
    (r : MonoidalActionCategory.RawHom a b) :
    (middleLocalizedRawMap r).stabilizer = r.stabilizer := rfl

omit [ExactCategory C] in
private theorem core_whisker_right_hom {T U : Core C} (e : T ⟶ U) (A : Core C) :
    (e ▷ A).iso.hom = biprod.map e.iso.hom (𝟙 A.of) := by
  rewrite [← tensorHom_id, coreBiprodTensorHom_iso_hom]
  rfl

omit [ExactCategory C] in
private theorem core_whisker_left_hom (T : Core C) {A B : Core C} (e : A ⟶ B) :
    (T ◁ e).iso.hom = biprod.map (𝟙 T.of) e.iso.hom :=
  (coreBiprodTensorLeft_map_iso_hom T e).trans
    (coreLeftBiprodFunctor_map_iso_hom T.of e)

/-- A raw relation maps to the same stabilizer isomorphism under the kernel projection. -/
theorem kernelLocalizedRawMap_rel {a b : localizedRows (C := C) X}
    {r s : MonoidalActionCategory.RawHom a b} (h : r.Rel s) :
    (kernelLocalizedRawMap r).Rel (kernelLocalizedRawMap s) := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, ?_⟩
  apply Prod.ext
  · apply Core.hom_ext
    have hA := congrArg
      (fun q : (r.stabilizer ⊙ₗ a.of) ⟶ b.of => q.1.a.hom) he
    change biprod.map e.hom.iso.hom (𝟙 a.of.1.A) ≫ s.hom.1.a.hom =
      r.hom.1.a.hom at hA
    change (e.hom ▷ (⟨a.of.1.A⟩ : Core C)).iso.hom ≫ s.hom.1.a.hom =
      r.hom.1.a.hom
    exact (congrArg
      (fun k : r.stabilizer.of ⊞ a.of.1.A ⟶ s.stabilizer.of ⊞ a.of.1.A =>
        k ≫ s.hom.1.a.hom) (core_whisker_right_hom e.hom ⟨a.of.1.A⟩)).trans hA
  · exact congrArg (fun q : (r.stabilizer ⊙ₗ a.of) ⟶ b.of => q.2) he

/-- A raw relation maps to the same stabilizer isomorphism under the middle projection. -/
theorem middleLocalizedRawMap_rel {a b : localizedRows (C := C) X}
    {r s : MonoidalActionCategory.RawHom a b} (h : r.Rel s) :
    (middleLocalizedRawMap r).Rel (middleLocalizedRawMap s) := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, ?_⟩
  apply Prod.ext
  · apply Core.hom_ext
    have hB := congrArg
      (fun q : (r.stabilizer ⊙ₗ a.of) ⟶ b.of => q.1.b.hom) he
    change biprod.map e.hom.iso.hom (𝟙 a.of.1.B) ≫ s.hom.1.b.hom =
      r.hom.1.b.hom at hB
    change (e.hom ▷ (⟨a.of.1.B⟩ : Core C)).iso.hom ≫ s.hom.1.b.hom =
      r.hom.1.b.hom
    exact (congrArg
      (fun k : r.stabilizer.of ⊞ a.of.1.B ⟶ s.stabilizer.of ⊞ a.of.1.B =>
        k ≫ s.hom.1.b.hom) (core_whisker_right_hom e.hom ⟨a.of.1.B⟩)).trans hB
  · exact congrArg (fun q : (r.stabilizer ⊙ₗ a.of) ⟶ b.of => q.2) he

private theorem fixed_unit_kernel_core (E : FixedTargetExtension C X) :
    (⟨(leftSumUnitIso E).hom.a⟩ : (𝟙_ (Core C)) ⊗ (⟨E.A⟩ : Core C) ⟶ ⟨E.A⟩) =
      (λ_ (⟨E.A⟩ : Core C)).hom := by
  apply Core.hom_ext
  change (isoZeroBiprod (X := (0 : C)) (Y := E.A) (isZero_zero C)).symm.hom =
    ((λ_ (⟨E.A⟩ : Core C)).hom).iso.hom
  exact (congrArg Iso.hom (coreBiprodLeftUnitor_iso (⟨E.A⟩ : Core C))).symm

private theorem fixed_unit_middle_core (E : FixedTargetExtension C X) :
    (⟨(leftSumUnitIso E).hom.b⟩ : (𝟙_ (Core C)) ⊗ (⟨E.B⟩ : Core C) ⟶ ⟨E.B⟩) =
      (λ_ (⟨E.B⟩ : Core C)).hom := by
  apply Core.hom_ext
  change (isoZeroBiprod (X := (0 : C)) (Y := E.B) (isZero_zero C)).symm.hom =
    ((λ_ (⟨E.B⟩ : Core C)).hom).iso.hom
  exact (congrArg Iso.hom (coreBiprodLeftUnitor_iso (⟨E.B⟩ : Core C))).symm

/-- The kernel raw map preserves the literal unitor representative of the identity. -/
theorem kernelLocalizedRawMap_id (a : localizedRows (C := C) X) :
    kernelLocalizedRawMap (MonoidalActionCategory.RawHom.id a) =
      MonoidalActionCategory.RawHom.id (kernelLocalizedObject a) := by
  let z := kernelLocalizedObject a
  have hHom :
      ((kernelLocalizedRawMap (MonoidalActionCategory.RawHom.id a)).hom :
        (𝟙_ (Core C)) ⊙ₗ z.of ⟶ z.of) =
      (MonoidalActionCategory.RawHom.id z).hom := by
    apply Prod.ext
    · exact fixed_unit_kernel_core a.of.1
    · rfl
  exact congrArg
    (fun q : (𝟙_ (Core C)) ⊙ₗ z.of ⟶ z.of =>
      (⟨𝟙_ (Core C), q⟩ : MonoidalActionCategory.RawHom z z)) hHom

/-- The middle raw map preserves the literal unitor representative of the identity. -/
theorem middleLocalizedRawMap_id (a : localizedRows (C := C) X) :
    middleLocalizedRawMap (MonoidalActionCategory.RawHom.id a) =
      MonoidalActionCategory.RawHom.id (middleLocalizedObject a) := by
  let z := middleLocalizedObject a
  have hHom :
      ((middleLocalizedRawMap (MonoidalActionCategory.RawHom.id a)).hom :
        (𝟙_ (Core C)) ⊙ₗ z.of ⟶ z.of) =
      (MonoidalActionCategory.RawHom.id z).hom := by
    apply Prod.ext
    · exact fixed_unit_middle_core a.of.1
    · rfl
  exact congrArg
    (fun q : (𝟙_ (Core C)) ⊙ₗ z.of ⟶ z.of =>
      (⟨𝟙_ (Core C), q⟩ : MonoidalActionCategory.RawHom z z)) hHom

/-- Actual raw composition keeps later tensor earlier under the kernel map. -/
theorem kernelLocalizedRawMap_comp {a b c : localizedRows (C := C) X}
    (r : MonoidalActionCategory.RawHom a b) (s : MonoidalActionCategory.RawHom b c) :
    kernelLocalizedRawMap (r.comp s) = (kernelLocalizedRawMap r).comp
      (kernelLocalizedRawMap s) := by
  let T := s.stabilizer ⊗ r.stabilizer
  let z := kernelLocalizedObject a
  let w := kernelLocalizedObject c
  have hHom : ((kernelLocalizedRawMap (r.comp s)).hom : T ⊙ₗ z.of ⟶ w.of) =
      ((kernelLocalizedRawMap r).comp (kernelLocalizedRawMap s)).hom := by
    apply Prod.ext
    · apply Core.hom_ext
      let A : C := (s.stabilizer.of ⊞ r.stabilizer.of) ⊞ a.of.1.A
      let B : C := s.stabilizer.of ⊞ (r.stabilizer.of ⊞ a.of.1.A)
      let D : C := s.stabilizer.of ⊞ b.of.1.A
      have hAssoc : ((α_ s.stabilizer r.stabilizer (⟨a.of.1.A⟩ : Core C)).hom).iso.hom =
          (biprod.associator s.stabilizer.of r.stabilizer.of a.of.1.A).hom :=
        congrArg Iso.hom (coreBiprodAssociator_iso _ _ _)
      have hWhisker :
          (s.stabilizer ◁ (⟨r.hom.1.a⟩ :
            r.stabilizer ⊗ (⟨a.of.1.A⟩ : Core C) ⟶ ⟨b.of.1.A⟩)).iso.hom =
          biprod.map (𝟙 s.stabilizer.of) r.hom.1.a.hom :=
        core_whisker_left_hom (A := r.stabilizer ⊗ (⟨a.of.1.A⟩ : Core C))
          (B := (⟨b.of.1.A⟩ : Core C)) s.stabilizer
          (show r.stabilizer ⊗ (⟨a.of.1.A⟩ : Core C) ⟶ (⟨b.of.1.A⟩ : Core C) from
            ⟨r.hom.1.a⟩)
      change (biprod.associator s.stabilizer.of r.stabilizer.of a.of.1.A).hom ≫
          biprod.map (𝟙 s.stabilizer.of) r.hom.1.a.hom ≫ s.hom.1.a.hom =
        ((α_ s.stabilizer r.stabilizer (⟨a.of.1.A⟩ : Core C)).hom).iso.hom ≫
          (s.stabilizer ◁ (⟨r.hom.1.a⟩ :
            r.stabilizer ⊗ (⟨a.of.1.A⟩ : Core C) ⟶ ⟨b.of.1.A⟩)).iso.hom ≫
          s.hom.1.a.hom
      exact (congrArg₂ (fun (h : A ⟶ B) (k : B ⟶ D) => h ≫ k ≫ s.hom.1.a.hom)
        hAssoc hWhisker).symm
    · rfl
  exact congrArg
    (fun q : T ⊙ₗ z.of ⟶ w.of => (⟨T, q⟩ : MonoidalActionCategory.RawHom z w)) hHom

/-- Actual raw composition keeps later tensor earlier under the middle map. -/
theorem middleLocalizedRawMap_comp {a b c : localizedRows (C := C) X}
    (r : MonoidalActionCategory.RawHom a b) (s : MonoidalActionCategory.RawHom b c) :
    middleLocalizedRawMap (r.comp s) = (middleLocalizedRawMap r).comp
      (middleLocalizedRawMap s) := by
  let T := s.stabilizer ⊗ r.stabilizer
  let z := middleLocalizedObject a
  let w := middleLocalizedObject c
  have hHom : ((middleLocalizedRawMap (r.comp s)).hom : T ⊙ₗ z.of ⟶ w.of) =
      ((middleLocalizedRawMap r).comp (middleLocalizedRawMap s)).hom := by
    apply Prod.ext
    · apply Core.hom_ext
      let A : C := (s.stabilizer.of ⊞ r.stabilizer.of) ⊞ a.of.1.B
      let B : C := s.stabilizer.of ⊞ (r.stabilizer.of ⊞ a.of.1.B)
      let D : C := s.stabilizer.of ⊞ b.of.1.B
      have hAssoc : ((α_ s.stabilizer r.stabilizer (⟨a.of.1.B⟩ : Core C)).hom).iso.hom =
          (biprod.associator s.stabilizer.of r.stabilizer.of a.of.1.B).hom :=
        congrArg Iso.hom (coreBiprodAssociator_iso _ _ _)
      have hWhisker :
          (s.stabilizer ◁ (⟨r.hom.1.b⟩ :
            r.stabilizer ⊗ (⟨a.of.1.B⟩ : Core C) ⟶ ⟨b.of.1.B⟩)).iso.hom =
          biprod.map (𝟙 s.stabilizer.of) r.hom.1.b.hom :=
        core_whisker_left_hom (A := r.stabilizer ⊗ (⟨a.of.1.B⟩ : Core C))
          (B := (⟨b.of.1.B⟩ : Core C)) s.stabilizer
          (show r.stabilizer ⊗ (⟨a.of.1.B⟩ : Core C) ⟶ (⟨b.of.1.B⟩ : Core C) from
            ⟨r.hom.1.b⟩)
      change (biprod.associator s.stabilizer.of r.stabilizer.of a.of.1.B).hom ≫
          biprod.map (𝟙 s.stabilizer.of) r.hom.1.b.hom ≫ s.hom.1.b.hom =
        ((α_ s.stabilizer r.stabilizer (⟨a.of.1.B⟩ : Core C)).hom).iso.hom ≫
          (s.stabilizer ◁ (⟨r.hom.1.b⟩ :
            r.stabilizer ⊗ (⟨a.of.1.B⟩ : Core C) ⟶ ⟨b.of.1.B⟩)).iso.hom ≫
          s.hom.1.b.hom
      exact (congrArg₂ (fun (h : A ⟶ B) (k : B ⟶ D) => h ≫ k ≫ s.hom.1.b.hom)
        hAssoc hWhisker).symm
    · rfl
  exact congrArg
    (fun q : T ⊙ₗ z.of ⟶ w.of => (⟨T, q⟩ : MonoidalActionCategory.RawHom z w)) hHom

/-- The quotient map induced by the actual kernel raw map. -/
def localizedKernelHomMap {a b : localizedRows (C := C) X} (f : a ⟶ b) :
    kernelLocalizedObject a ⟶ kernelLocalizedObject b :=
  Quotient.map kernelLocalizedRawMap (by
    intro r s h
    exact kernelLocalizedRawMap_rel h) f

/-- The quotient map induced by the actual middle raw map. -/
def localizedMiddleHomMap {a b : localizedRows (C := C) X} (f : a ⟶ b) :
    middleLocalizedObject a ⟶ middleLocalizedObject b :=
  Quotient.map middleLocalizedRawMap (by
    intro r s h
    exact middleLocalizedRawMap_rel h) f

/-- The quotient kernel map has the actual raw representative. -/
theorem localizedKernelHomMap_mk {a b : localizedRows (C := C) X}
    (r : MonoidalActionCategory.RawHom a b) :
    localizedKernelHomMap (MonoidalActionCategory.Hom.mk r) =
      MonoidalActionCategory.Hom.mk (kernelLocalizedRawMap r) := rfl

/-- The quotient middle map has the actual raw representative. -/
theorem localizedMiddleHomMap_mk {a b : localizedRows (C := C) X}
    (r : MonoidalActionCategory.RawHom a b) :
    localizedMiddleHomMap (MonoidalActionCategory.Hom.mk r) =
      MonoidalActionCategory.Hom.mk (middleLocalizedRawMap r) := rfl

/-- The actual denominator-preserving kernel functor on the original localized rows. -/
def localizedKernelFunctor (X : C) : localizedRows (C := C) X ⥤ SInverse (Core C) (Core C) where
  obj := kernelLocalizedObject
  map {a b} f := localizedKernelHomMap f
  map_id a := by
    change MonoidalActionCategory.Hom.mk
        (kernelLocalizedRawMap (MonoidalActionCategory.RawHom.id a)) =
      MonoidalActionCategory.Hom.mk
        (MonoidalActionCategory.RawHom.id (kernelLocalizedObject a))
    exact congrArg MonoidalActionCategory.Hom.mk (kernelLocalizedRawMap_id a)
  map_comp {a b c} f g := by
    refine Quotient.inductionOn₂ f g ?_
    intro r s
    change MonoidalActionCategory.Hom.mk (kernelLocalizedRawMap (r.comp s)) =
      MonoidalActionCategory.Hom.mk ((kernelLocalizedRawMap r).comp (kernelLocalizedRawMap s))
    exact congrArg MonoidalActionCategory.Hom.mk (kernelLocalizedRawMap_comp r s)

/-- The actual denominator-preserving middle functor on the original localized rows. -/
def localizedMiddleFunctor (X : C) : localizedRows (C := C) X ⥤ SInverse (Core C) (Core C) where
  obj := middleLocalizedObject
  map {a b} f := localizedMiddleHomMap f
  map_id a := by
    change MonoidalActionCategory.Hom.mk
        (middleLocalizedRawMap (MonoidalActionCategory.RawHom.id a)) =
      MonoidalActionCategory.Hom.mk
        (MonoidalActionCategory.RawHom.id (middleLocalizedObject a))
    exact congrArg MonoidalActionCategory.Hom.mk (middleLocalizedRawMap_id a)
  map_comp {a b c} f g := by
    refine Quotient.inductionOn₂ f g ?_
    intro r s
    change MonoidalActionCategory.Hom.mk (middleLocalizedRawMap (r.comp s)) =
      MonoidalActionCategory.Hom.mk ((middleLocalizedRawMap r).comp (middleLocalizedRawMap s))
    exact congrArg MonoidalActionCategory.Hom.mk (middleLocalizedRawMap_comp r s)

/-- The functor keeps the actual original kernel and denominator pair. -/
theorem localizedKernelFunctor_obj (a : localizedRows (C := C) X) :
    (localizedKernelFunctor X).obj a = kernelLocalizedObject a := rfl

/-- The functor keeps the actual original middle and denominator pair. -/
theorem localizedMiddleFunctor_obj (a : localizedRows (C := C) X) :
    (localizedMiddleFunctor X).obj a = middleLocalizedObject a := rfl

/-- The kernel functor maps every actual raw representative by its original a isomorphism. -/
theorem localizedKernelFunctor_map_mk {a b : localizedRows (C := C) X}
    (r : MonoidalActionCategory.RawHom a b) :
    (localizedKernelFunctor X).map (MonoidalActionCategory.Hom.mk r) =
      MonoidalActionCategory.Hom.mk (kernelLocalizedRawMap r) := rfl

/-- The middle functor maps every actual raw representative by its original b isomorphism. -/
theorem localizedMiddleFunctor_map_mk {a b : localizedRows (C := C) X}
    (r : MonoidalActionCategory.RawHom a b) :
    (localizedMiddleFunctor X).map (MonoidalActionCategory.Hom.mk r) =
      MonoidalActionCategory.Hom.mk (middleLocalizedRawMap r) := rfl

end AlgebraicKTheory.FixedTargetExtension

end

/-!
# The actual localized fixed-zero rows and the original core localization

The zero-row map below retains both the actual stabilizer and denominator.
Its inverse is the actual kernel functor at the given zero object. The counit
uses ordinary pair inclusion of the original zero-row counit at the SAME
denominator. Its numerator invertibility is derived from admissible exactness,
not supplied as an extra witness. This is a categorical comparison only.
-/

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace AlgebraicKTheory.FixedTargetExtension

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] leftSumAction MonoidalActionCategory.diagonalAction

/-- The actual zero row paired with the same original denominator. -/
def zeroLocalizedObject (a : SInverse (Core C) (Core C)) : localizedRows (C := C) (0 : C) :=
  ⟨(zeroRow a.of.1, a.of.2)⟩

/-- The actual forward isomorphism acts on both zero-row objects after stabilization. -/
def zeroLocalizedSumArrow {T A B : Core C} (γ : T ⊗ A ⟶ B) :
    leftSumObj T (zeroRow A) ⟶ zeroRow B where
  a := γ.iso
  b := γ.iso
  comm_i := by
    change biprod.map (𝟙 T.of) (𝟙 A.of) ≫ γ.iso.hom = γ.iso.hom ≫ 𝟙 B.of
    have hi : biprod.map (𝟙 T.of) (𝟙 A.of) = 𝟙 (T.of ⊞ A.of) := by
      apply biprod.hom_ext <;> simp
    exact (congrArg (fun k : T.of ⊞ A.of ⟶ T.of ⊞ A.of => k ≫ γ.iso.hom) hi).trans
      ((Category.id_comp γ.iso.hom).trans (Category.comp_id γ.iso.hom).symm)
  comm_p := by
    change γ.iso.hom ≫ (0 : B.of ⟶ (0 : C)) =
      (biprod.snd : T.of ⊞ A.of ⟶ A.of) ≫ (0 : A.of ⟶ (0 : C))
    exact (comp_zero (f := γ.iso.hom)).trans
      (comp_zero (f := (biprod.snd : T.of ⊞ A.of ⟶ A.of))).symm

/-- The zero-row raw map retains the actual stabilizer and denominator arrow. -/
def zeroLocalizedRawMap {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) :
    MonoidalActionCategory.RawHom (zeroLocalizedObject a) (zeroLocalizedObject b) where
  stabilizer := r.stabilizer
  hom := (zeroLocalizedSumArrow r.hom.1, r.hom.2)

/-- Applying the actual kernel to the actual zero row gives back the original pair. -/
theorem kernel_zeroLocalizedObject (a : SInverse (Core C) (Core C)) :
    kernelLocalizedObject (zeroLocalizedObject a) = a := rfl

/-- The actual kernel of the zero-row raw map gives back the original representative. -/
theorem kernel_zeroLocalizedRawMap {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) :
    kernelLocalizedRawMap (zeroLocalizedRawMap r) = r := rfl

private theorem zero_hom_ext_kernel {E F : FixedTargetExtension C (0 : C)}
    (f g : E ⟶ F) (ha : f.a.hom = g.a.hom) : f = g := by
  apply Hom.ext
  · exact Iso.ext ha
  · apply Iso.ext
    let e : E.A ≅ E.B := @CategoryTheory.asIso C _ E.A E.B E.i (zero_i_isIso E)
    apply (cancel_epi e.hom).mp
    change E.i ≫ f.b.hom = E.i ≫ g.b.hom
    exact f.comm_i.trans
      ((congrArg (fun k : E.A ⟶ F.A => k ≫ F.i) ha).trans g.comm_i.symm)

/-- At the original zero quotient, the kernel reflects raw stabilizer relations. -/
theorem kernelLocalizedRawMap_rel_reflect_zero
    {a b : localizedRows (C := C) (0 : C)}
    {r s : MonoidalActionCategory.RawHom a b}
    (h : (kernelLocalizedRawMap r).Rel (kernelLocalizedRawMap s)) : r.Rel s := by
  obtain ⟨e, he⟩ := h
  have hCore := congrArg
    (fun q : (r.stabilizer ⊙ₗ (kernelLocalizedObject a).of) ⟶
      (kernelLocalizedObject b).of => q.1.iso.hom) he
  change (e.hom ▷ (⟨a.of.1.A⟩ : Core C)).iso.hom ≫ s.hom.1.a.hom =
    r.hom.1.a.hom at hCore
  have hKernel : biprod.map e.hom.iso.hom (𝟙 a.of.1.A) ≫ s.hom.1.a.hom =
      r.hom.1.a.hom :=
    (congrArg
      (fun k : r.stabilizer.of ⊞ a.of.1.A ⟶ s.stabilizer.of ⊞ a.of.1.A =>
        k ≫ s.hom.1.a.hom) (core_whisker_right_hom e.hom ⟨a.of.1.A⟩).symm).trans hCore
  refine ⟨e, ?_⟩
  apply Prod.ext
  · apply zero_hom_ext_kernel
    change biprod.map e.hom.iso.hom (𝟙 a.of.1.A) ≫ s.hom.1.a.hom = r.hom.1.a.hom
    exact hKernel
  · exact congrArg
      (fun q : (r.stabilizer ⊙ₗ (kernelLocalizedObject a).of) ⟶
        (kernelLocalizedObject b).of => q.2) he

omit [ExactCategory C] in
private theorem core_raw_rel_of_eq {a b : SInverse (Core C) (Core C)}
    {r s : MonoidalActionCategory.RawHom a b} (h : r = s) : r.Rel s := by
  cases h
  refine ⟨Iso.refl r.stabilizer, ?_⟩
  have hi : (𝟙 r.stabilizer) ⊵ₗ a.of = 𝟙 (r.stabilizer ⊙ₗ a.of) :=
    MonoidalLeftAction.id_actionHomLeft r.stabilizer a.of
  exact (congrArg
    (fun k : r.stabilizer ⊙ₗ a.of ⟶ r.stabilizer ⊙ₗ a.of => k ≫ r.hom) hi).trans
      (Category.id_comp r.hom)

/-- The zero-row map preserves the relation with the original stabilizer Iso. -/
theorem zeroLocalizedRawMap_rel {a b : SInverse (Core C) (Core C)}
    {r s : MonoidalActionCategory.RawHom a b} (h : r.Rel s) :
    (zeroLocalizedRawMap r).Rel (zeroLocalizedRawMap s) := by
  apply kernelLocalizedRawMap_rel_reflect_zero
  simpa only [kernel_zeroLocalizedObject, kernel_zeroLocalizedRawMap] using h

/-- The zero-row map preserves the unit raw class, through proved kernel reflection. -/
theorem zeroLocalizedRawMap_id (a : SInverse (Core C) (Core C)) :
    (zeroLocalizedRawMap (MonoidalActionCategory.RawHom.id a)).Rel
      (MonoidalActionCategory.RawHom.id (zeroLocalizedObject a)) := by
  have hLeft := kernel_zeroLocalizedRawMap (MonoidalActionCategory.RawHom.id a)
  have hRight := kernelLocalizedRawMap_id (zeroLocalizedObject a)
  apply kernelLocalizedRawMap_rel_reflect_zero
  exact core_raw_rel_of_eq (hLeft.trans hRight.symm)

/-- The zero-row map preserves composition with the original later-times-earlier stabilizer. -/
theorem zeroLocalizedRawMap_comp {a b c : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) (s : MonoidalActionCategory.RawHom b c) :
    (zeroLocalizedRawMap (r.comp s)).Rel
      ((zeroLocalizedRawMap r).comp (zeroLocalizedRawMap s)) := by
  have hLeft := kernel_zeroLocalizedRawMap (r.comp s)
  have hRight : kernelLocalizedRawMap
      ((zeroLocalizedRawMap r).comp (zeroLocalizedRawMap s)) = r.comp s :=
    (kernelLocalizedRawMap_comp (zeroLocalizedRawMap r) (zeroLocalizedRawMap s)).trans
      (congrArg₂ MonoidalActionCategory.RawHom.comp
        (kernel_zeroLocalizedRawMap r) (kernel_zeroLocalizedRawMap s))
  apply kernelLocalizedRawMap_rel_reflect_zero
  exact core_raw_rel_of_eq (hLeft.trans hRight.symm)

/-- The actual quotient map, with no supplied equivariance proof or result witness. -/
def zeroLocalizedHomMap {a b : SInverse (Core C) (Core C)} (f : a ⟶ b) :
    zeroLocalizedObject a ⟶ zeroLocalizedObject b :=
  Quotient.map zeroLocalizedRawMap (by
    intro r s h
    exact zeroLocalizedRawMap_rel h) f

/-- Its actual stabilized representative retains both given coordinates. -/
theorem zeroLocalizedHomMap_mk {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) :
    zeroLocalizedHomMap (MonoidalActionCategory.Hom.mk r) =
      MonoidalActionCategory.Hom.mk (zeroLocalizedRawMap r) := rfl

/-- The actual zero-row functor on the original core localization. -/
def zeroLocalizedFunctor : SInverse (Core C) (Core C) ⥤ localizedRows (C := C) (0 : C) where
  obj := zeroLocalizedObject
  map {a b} f := zeroLocalizedHomMap f
  map_id a := by
    change MonoidalActionCategory.Hom.mk
        (zeroLocalizedRawMap (MonoidalActionCategory.RawHom.id a)) =
      MonoidalActionCategory.Hom.mk (MonoidalActionCategory.RawHom.id (zeroLocalizedObject a))
    exact Quotient.sound (zeroLocalizedRawMap_id a)
  map_comp {a b c} f g := by
    refine Quotient.inductionOn₂ f g ?_
    intro r s
    change MonoidalActionCategory.Hom.mk (zeroLocalizedRawMap (r.comp s)) =
      MonoidalActionCategory.Hom.mk ((zeroLocalizedRawMap r).comp (zeroLocalizedRawMap s))
    exact Quotient.sound (zeroLocalizedRawMap_comp r s)

/-- The zero-row functor retains the given denominator object. -/
theorem zeroLocalizedFunctor_denominator (a : SInverse (Core C) (Core C)) :
    ((zeroLocalizedFunctor (C := C)).obj a).of.2 = a.of.2 := rfl

/-- The zero-row representative retains the given denominator morphism. -/
theorem zeroLocalizedRawMap_denominator {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) : (zeroLocalizedRawMap r).hom.2 = r.hom.2 := rfl

/-- The zero-row representative retains the given stabilizer. -/
theorem zeroLocalizedRawMap_stabilizer {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) :
    (zeroLocalizedRawMap r).stabilizer = r.stabilizer := rfl

/-- The actual kernel is a left inverse on every morphism class. -/
theorem kernel_zeroLocalizedFunctor_map {a b : SInverse (Core C) (Core C)} (f : a ⟶ b) :
    (localizedKernelFunctor (0 : C)).map ((zeroLocalizedFunctor (C := C)).map f) = f := by
  obtain ⟨r, rfl⟩ := MonoidalActionCategory.Hom.exists_rep f
  change MonoidalActionCategory.Hom.mk (kernelLocalizedRawMap (zeroLocalizedRawMap r)) =
    MonoidalActionCategory.Hom.mk r
  exact congrArg MonoidalActionCategory.Hom.mk (kernel_zeroLocalizedRawMap r)

private theorem kernel_zero_map_injective
    {a b : localizedRows (C := C) (0 : C)} (f g : a ⟶ b)
    (h : (localizedKernelFunctor (0 : C)).map f = (localizedKernelFunctor (0 : C)).map g) :
    f = g := by
  obtain ⟨r, rfl⟩ := MonoidalActionCategory.Hom.exists_rep f
  obtain ⟨s, rfl⟩ := MonoidalActionCategory.Hom.exists_rep g
  change MonoidalActionCategory.Hom.mk (kernelLocalizedRawMap r) =
    MonoidalActionCategory.Hom.mk (kernelLocalizedRawMap s) at h
  exact Quotient.sound (kernelLocalizedRawMap_rel_reflect_zero
    ((MonoidalActionCategory.Hom.mk_eq_mk_iff _ _).mp h))

/-- The counit uses ordinary pair inclusion at the SAME arbitrary denominator. -/
def zeroLocalizedCounitComponent (a : localizedRows (C := C) (0 : C)) :
    zeroLocalizedObject (kernelLocalizedObject a) ≅ a :=
  (MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C (0 : C) × Core C)).mapIso
    ((zeroFiberCounitComponent a.of.1).prod (Iso.refl a.of.2))

/-- The original forward counit row pair, with the unit stabilizer and given denominator. -/
def zeroLocalizedCounitRaw (a : localizedRows (C := C) (0 : C)) :
    MonoidalActionCategory.RawHom (zeroLocalizedObject (kernelLocalizedObject a)) a :=
  MonoidalActionCategory.RawHom.ofMap (S := Core C)
    (show (zeroRow (⟨a.of.1.A⟩ : Core C), a.of.2) ⟶ (a.of.1, a.of.2) from
      ((zeroFiberCounitComponent a.of.1).hom, 𝟙 a.of.2))

/-- The actual ordinary-inclusion representative of the counit. -/
theorem zeroLocalizedCounitComponent_hom_rep (a : localizedRows (C := C) (0 : C)) :
    (zeroLocalizedCounitComponent a).hom =
      MonoidalActionCategory.Hom.mk (zeroLocalizedCounitRaw a) := rfl

/-- Its stabilizer is the actual tensor unit, with no denominator reset. -/
theorem zeroLocalizedCounitRaw_stabilizer (a : localizedRows (C := C) (0 : C)) :
    (zeroLocalizedCounitRaw a).stabilizer = 𝟙_ (Core C) := rfl

/-- Its denominator map is the actual left unitor of the original denominator. -/
theorem zeroLocalizedCounitRaw_denominator (a : localizedRows (C := C) (0 : C)) :
    (zeroLocalizedCounitRaw a).hom.2 = (λ_ a.of.2).hom := by
  change (λ_ a.of.2).hom ≫ 𝟙 a.of.2 = (λ_ a.of.2).hom
  exact Category.comp_id _

private theorem kernel_zero_counit_raw (a : localizedRows (C := C) (0 : C)) :
    kernelLocalizedRawMap (zeroLocalizedCounitRaw a) =
      MonoidalActionCategory.RawHom.id (kernelLocalizedObject a) := by
  let k := kernelLocalizedObject a
  have hHom : ((kernelLocalizedRawMap (zeroLocalizedCounitRaw a)).hom :
      (𝟙_ (Core C)) ⊙ₗ k.of ⟶ k.of) =
      (MonoidalActionCategory.RawHom.id k).hom := by
    apply Prod.ext
    · apply Core.hom_ext
      let E := a.of.1
      let A : Core C := ⟨E.A⟩
      have hA : (zeroFiberCounitComponent E).hom.a.hom = 𝟙 E.A :=
        congrArg Iso.hom (zeroFiberCounitComponent_hom_a E)
      have hU : (leftSumUnitIso (zeroRow A)).hom.a.hom = ((λ_ A).hom).iso.hom :=
        congrArg (fun f : (𝟙_ (Core C)) ⊗ A ⟶ A => f.iso.hom)
          (fixed_unit_kernel_core (zeroRow A))
      change (leftSumUnitIso (zeroRow A)).hom.a.hom ≫
          (zeroFiberCounitComponent E).hom.a.hom = ((λ_ A).hom).iso.hom
      exact (congrArg
        (fun f : E.A ⟶ E.A => (leftSumUnitIso (zeroRow A)).hom.a.hom ≫ f) hA).trans
          ((Category.comp_id (leftSumUnitIso (zeroRow A)).hom.a.hom).trans hU)
    · exact zeroLocalizedCounitRaw_denominator a
  exact congrArg
    (fun q : (𝟙_ (Core C)) ⊙ₗ k.of ⟶ k.of =>
      (⟨𝟙_ (Core C), q⟩ : MonoidalActionCategory.RawHom k k)) hHom

/-- The original kernel of the ordinary-inclusion counit is the actual identity class. -/
theorem zeroLocalizedCounit_kernel_map (a : localizedRows (C := C) (0 : C)) :
    (localizedKernelFunctor (0 : C)).map (zeroLocalizedCounitComponent a).hom =
      𝟙 (kernelLocalizedObject a) := by
  let r := zeroLocalizedCounitRaw a
  have hRep : (localizedKernelFunctor (0 : C)).map (zeroLocalizedCounitComponent a).hom =
      (localizedKernelFunctor (0 : C)).map (MonoidalActionCategory.Hom.mk r) :=
    congrArg
      (fun f : zeroLocalizedObject (kernelLocalizedObject a) ⟶ a =>
        (localizedKernelFunctor (0 : C)).map f) (zeroLocalizedCounitComponent_hom_rep a)
  have hMap : (localizedKernelFunctor (0 : C)).map (MonoidalActionCategory.Hom.mk r) =
      MonoidalActionCategory.Hom.mk (kernelLocalizedRawMap r) :=
    localizedKernelFunctor_map_mk r
  have hRaw : MonoidalActionCategory.Hom.mk (kernelLocalizedRawMap r) =
      MonoidalActionCategory.Hom.mk
        (MonoidalActionCategory.RawHom.id (kernelLocalizedObject a)) :=
    congrArg MonoidalActionCategory.Hom.mk (kernel_zero_counit_raw a)
  exact hRep.trans (hMap.trans (hRaw.trans
    (MonoidalActionCategory.Hom.mk_id (kernelLocalizedObject a))))

/-- The unit retains the actual core pair and denominator on every component. -/
def zeroLocalizedUnit : 𝟭 (SInverse (Core C) (Core C)) ≅
    zeroLocalizedFunctor (C := C) ⋙ localizedKernelFunctor (0 : C) :=
  NatIso.ofComponents (fun a => Iso.refl a) (by
    intro a b f
    change f ≫ 𝟙 b = 𝟙 a ≫
      (localizedKernelFunctor (0 : C)).map ((zeroLocalizedFunctor (C := C)).map f)
    have hK : (localizedKernelFunctor (0 : C)).map
        ((zeroLocalizedFunctor (C := C)).map f) = f := kernel_zeroLocalizedFunctor_map f
    exact (Category.comp_id f).trans
      (((congrArg (fun q : a ⟶ b => 𝟙 a ≫ q) hK).trans (Category.id_comp f)).symm))

/-- The unit's actual component is the identity of the original pair. -/
theorem zeroLocalizedUnit_hom_app (a : SInverse (Core C) (Core C)) :
    (zeroLocalizedUnit (C := C)).hom.app a = 𝟙 a := rfl

/-- The counit is natural by the proved kernel reflection, not an equivariance witness. -/
def zeroLocalizedCounit : localizedKernelFunctor (0 : C) ⋙ zeroLocalizedFunctor (C := C) ≅
    𝟭 (localizedRows (C := C) (0 : C)) :=
  NatIso.ofComponents zeroLocalizedCounitComponent (by
    intro a b f
    let K := localizedKernelFunctor (0 : C)
    let Z := zeroLocalizedFunctor (C := C)
    let A : SInverse (Core C) (Core C) := kernelLocalizedObject a
    let B : SInverse (Core C) (Core C) := kernelLocalizedObject b
    let q : A ⟶ B := K.map f
    let ca := (zeroLocalizedCounitComponent a).hom
    let cb := (zeroLocalizedCounitComponent b).hom
    change Z.map (K.map f) ≫ cb = ca ≫ f
    apply kernel_zero_map_injective
    have hZ : K.map (Z.map q) = q := kernel_zeroLocalizedFunctor_map q
    have hCA : K.map ca = 𝟙 A := zeroLocalizedCounit_kernel_map a
    have hCB : K.map cb = 𝟙 B := zeroLocalizedCounit_kernel_map b
    have hL : K.map (Z.map q ≫ cb) = q :=
      (K.map_comp (Z.map q) cb).trans
        ((congrArg₂ (fun (x : A ⟶ B) (y : B ⟶ B) => x ≫ y) hZ hCB).trans
          (Category.comp_id q))
    have hR : K.map (ca ≫ f) = q :=
      (K.map_comp ca f).trans
        ((congrArg₂ (fun (x : A ⟶ A) (y : A ⟶ B) => x ≫ y) hCA
          (show K.map f = q from rfl)).trans (Category.id_comp q))
    exact hL.trans hR.symm)

/-- The counit retains its original ordinary-inclusion component. -/
theorem zeroLocalizedCounit_hom_app (a : localizedRows (C := C) (0 : C)) :
    (zeroLocalizedCounit (C := C)).hom.app a = (zeroLocalizedCounitComponent a).hom := rfl

/-- The actual zero row has the counit identity, established by proved kernel reflection. -/
theorem zeroLocalizedCounit_zeroRow (a : SInverse (Core C) (Core C)) :
    (zeroLocalizedCounitComponent ((zeroLocalizedFunctor (C := C)).obj a)).hom =
      𝟙 ((zeroLocalizedFunctor (C := C)).obj a) := by
  let b := (zeroLocalizedFunctor (C := C)).obj a
  apply kernel_zero_map_injective
  exact (zeroLocalizedCounit_kernel_map b).trans
    ((localizedKernelFunctor (0 : C)).map_id b).symm

/-- The actual unit/counit triangle follows from the literal zero-row identity. -/
theorem zeroLocalized_triangle (a : SInverse (Core C) (Core C)) :
    (zeroLocalizedFunctor (C := C)).map ((zeroLocalizedUnit (C := C)).hom.app a) ≫
        (zeroLocalizedCounit (C := C)).hom.app ((zeroLocalizedFunctor (C := C)).obj a) =
      𝟙 ((zeroLocalizedFunctor (C := C)).obj a) := by
  let Z := zeroLocalizedFunctor (C := C)
  let b := Z.obj a
  change Z.map (𝟙 a) ≫ (zeroLocalizedCounitComponent b).hom = 𝟙 b
  exact (congrArg (fun q : b ⟶ b => q ≫ (zeroLocalizedCounitComponent b).hom)
      (Z.map_id a)).trans
    ((Category.id_comp (zeroLocalizedCounitComponent b).hom).trans
      (zeroLocalizedCounit_zeroRow a))

/-- The constructed equivalence of the ACTUAL core localization and given-zero localized rows. -/
def coreZeroLocalizedEquivalence : SInverse (Core C) (Core C) ≌
    localizedRows (C := C) (0 : C) where
  functor := zeroLocalizedFunctor
  inverse := localizedKernelFunctor (0 : C)
  unitIso := zeroLocalizedUnit
  counitIso := zeroLocalizedCounit
  functor_unitIso_comp a := zeroLocalized_triangle a

/-- The forward equivalence keeps the actual zero row and denominator. -/
theorem coreZeroLocalizedEquivalence_functor_obj (a : SInverse (Core C) (Core C)) :
    (coreZeroLocalizedEquivalence (C := C)).functor.obj a = zeroLocalizedObject a := rfl

/-- The inverse keeps the original kernel and the same denominator. -/
theorem coreZeroLocalizedEquivalence_inverse_obj (a : localizedRows (C := C) (0 : C)) :
    (coreZeroLocalizedEquivalence (C := C)).inverse.obj a = kernelLocalizedObject a := rfl

/-- The actual inverse on representatives is the original kernel isomorphism and delta. -/
theorem coreZeroLocalizedEquivalence_inverse_map_mk
    {a b : localizedRows (C := C) (0 : C)} (r : MonoidalActionCategory.RawHom a b) :
    (coreZeroLocalizedEquivalence (C := C)).inverse.map (MonoidalActionCategory.Hom.mk r) =
      MonoidalActionCategory.Hom.mk (kernelLocalizedRawMap r) := rfl

end AlgebraicKTheory.FixedTargetExtension

end
