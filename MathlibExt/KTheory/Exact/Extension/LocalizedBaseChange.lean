/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.ZeroFiberLocalization
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.FiberedCategory.Fiber

/-!
# Actual localized zero-span pullbacks and natural kernel/middle comparisons

The actual chosen-fiber pullback functor, canonical strongly Cartesian
zero-span lifts and domain-comparison components are carried once below.
The new section proves the full localized kernel and middle squares with
the original stabilizer T and denominator map delta. Cartesian factor
uniqueness then proves the components natural in the literal zero fiber,
and constructs both actual functor NatIsos to the kernel/middle zero-row
models. The original localizedTarget, Q arrows and denominators are retained.

All constructions hold in the given exact category with independent u/v.
No split-exactness, generic base-change HE, kappa/beta HE or Theorem-B
hypothesis is supplied or concluded by these categorical comparison data.
-/

universe u v

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject
open CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal

namespace AlgebraicKTheory.LocalizedBaseChange

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] ExtensionCategory.leftSumAction
attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction
attribute [local instance] ExtensionCategory.localizedTarget_isFibered

/-- The independently defined original localized target. -/
abbrev projection := ExtensionCategory.localizedTarget (C := C)

/-- The actual chosen Cartesian pullback object, packaged in its literal target fiber. -/
def baseChangeObject {R S : QuillenQ C} (f : R ⟶ S)
    (a : Functor.Fiber (projection (C := C)) S) :
    Functor.Fiber (projection (C := C)) R :=
  ⟨Functor.IsPreFibered.pullbackObj (p := projection) a.property f,
    Functor.IsPreFibered.pullbackObj_proj a.property f⟩

/-- The original stock chosen lift, without replacing its domain by a model object. -/
abbrev baseChangeLift {R S : QuillenQ C} (f : R ⟶ S)
    (a : Functor.Fiber (projection (C := C)) S) :
    (baseChangeObject f a).val ⟶ a.val :=
  Functor.IsPreFibered.pullbackMap (p := projection) a.property f

private theorem baseChangeLift_cartesian {R S : QuillenQ C} (f : R ⟶ S)
    (a : Functor.Fiber (projection (C := C)) S) :
    Functor.IsCartesian (projection (C := C)) f (baseChangeLift f a) := by
  change Functor.IsCartesian (projection (C := C)) f
    (Functor.IsPreFibered.pullbackMap (p := projection (C := C)) a.property f)
  infer_instance

private theorem incoming_lift {R S : QuillenQ C} (f : R ⟶ S)
    {a b : Functor.Fiber (projection (C := C)) S} (phi : a ⟶ b) :
    Functor.IsHomLift (projection (C := C)) f
      (baseChangeLift f a ≫ Functor.Fiber.fiberInclusion.map phi) := by
  have hLift : Functor.IsHomLift (projection (C := C)) f (baseChangeLift f a) :=
    (baseChangeLift_cartesian f a).toIsHomLift
  exact @IsHomLift.comp_lift_id_right _ _ _ _ (projection (C := C))
    _ _ _ _ _ f (baseChangeLift f a) hLift
    (Functor.Fiber.fiberInclusion.map phi) phi.property

/-- Map the actual fiber arrow by the Cartesian universal-property factor. -/
def baseChangeMap {R S : QuillenQ C} (f : R ⟶ S)
    {a b : Functor.Fiber (projection (C := C)) S} (phi : a ⟶ b) :
    baseChangeObject f a ⟶ baseChangeObject f b := by
  let hCart : Functor.IsCartesian (projection (C := C)) f (baseChangeLift f b) := by
    exact baseChangeLift_cartesian f b
  let incoming := baseChangeLift f a ≫ Functor.Fiber.fiberInclusion.map phi
  let hIncoming : Functor.IsHomLift (projection (C := C)) f incoming := by
    exact incoming_lift f phi
  let m : (baseChangeObject f a).val ⟶ (baseChangeObject f b).val :=
    @Functor.IsCartesian.map _ _ _ _ (projection (C := C)) _ _ _ _ f
      (baseChangeLift f b) hCart _ incoming hIncoming
  let hm : Functor.IsHomLift (projection (C := C)) (𝟙 R) m := by
    exact @Functor.IsCartesian.map_isHomLift _ _ _ _ (projection (C := C)) _ _ _ _ f
      (baseChangeLift f b) hCart _ incoming hIncoming
  exact ⟨m, hm⟩

/-- The mapped arrow satisfies the actual original lift-factor equation. -/
theorem baseChangeMap_fac {R S : QuillenQ C} (f : R ⟶ S)
    {a b : Functor.Fiber (projection (C := C)) S} (phi : a ⟶ b) :
    (baseChangeMap f phi).val ≫ baseChangeLift f b =
      baseChangeLift f a ≫ Functor.Fiber.fiberInclusion.map phi := by
  have hCart : Functor.IsCartesian (projection (C := C)) f (baseChangeLift f b) :=
    baseChangeLift_cartesian f b
  let incoming := baseChangeLift f a ≫ Functor.Fiber.fiberInclusion.map phi
  have hIncoming : Functor.IsHomLift (projection (C := C)) f incoming := incoming_lift f phi
  exact @Functor.IsCartesian.fac _ _ _ _ (projection (C := C)) _ _ _ _ f
    (baseChangeLift f b) hCart _ incoming hIncoming

/-- The actual chosen-object pullback functor on the literal localized target fibers. -/
def baseChangeFunctor {R S : QuillenQ C} (f : R ⟶ S) :
    Functor.Fiber (projection (C := C)) S ⥤ Functor.Fiber (projection (C := C)) R where
  obj := baseChangeObject f
  map {a b} phi := baseChangeMap f phi
  map_id a := by
    apply Functor.Fiber.hom_ext
    have hCart : Functor.IsCartesian (projection (C := C)) f (baseChangeLift f a) :=
      baseChangeLift_cartesian f a
    let incoming := baseChangeLift f a ≫ Functor.Fiber.fiberInclusion.map (𝟙 a)
    have hIncoming : Functor.IsHomLift (projection (C := C)) f incoming :=
      incoming_lift f (𝟙 a)
    have hIdentity : Functor.IsHomLift (projection (C := C)) (𝟙 R)
        (𝟙 (baseChangeObject f a).val) := IsHomLift.id (baseChangeObject f a).property
    have h : 𝟙 (baseChangeObject f a).val ≫ baseChangeLift f a = incoming :=
      (Category.id_comp _).trans (Category.comp_id _).symm
    exact (@Functor.IsCartesian.map_uniq _ _ _ _ (projection (C := C)) _ _ _ _ f
      (baseChangeLift f a) hCart _ incoming hIncoming
      (𝟙 (baseChangeObject f a).val) hIdentity h).symm
  map_comp {a b c} phi psi := by
    apply Functor.Fiber.hom_ext
    have hCart : Functor.IsCartesian (projection (C := C)) f (baseChangeLift f c) :=
      baseChangeLift_cartesian f c
    let incoming := baseChangeLift f a ≫ Functor.Fiber.fiberInclusion.map (phi ≫ psi)
    have hIncoming : Functor.IsHomLift (projection (C := C)) f incoming :=
      incoming_lift f (phi ≫ psi)
    let k := baseChangeMap f phi ≫ baseChangeMap f psi
    have hK : Functor.IsHomLift (projection (C := C)) (𝟙 R) k.val := k.property
    have h : k.val ≫ baseChangeLift f c = incoming := by
      change ((baseChangeMap f phi).val ≫ (baseChangeMap f psi).val) ≫
        baseChangeLift f c = baseChangeLift f a ≫
          (Functor.Fiber.fiberInclusion.map phi ≫ Functor.Fiber.fiberInclusion.map psi)
      exact (Category.assoc _ _ _).trans
        ((congrArg ((baseChangeMap f phi).val ≫ ·) (baseChangeMap_fac f psi)).trans
          (((Category.assoc _ _ _).symm).trans
            ((congrArg (· ≫ Functor.Fiber.fiberInclusion.map psi)
              (baseChangeMap_fac f phi)).trans (Category.assoc _ _ _))))
    exact (@Functor.IsCartesian.map_uniq _ _ _ _ (projection (C := C)) _ _ _ _ f
      (baseChangeLift f c) hCart _ incoming hIncoming k.val hK h).symm

/-- Pullback along the original mono zero span, without changing that Q arrow. -/
def zeroMonoBaseChange (X : C) :
    FixedTargetExtension.localizedFiber (C := C) X ⥤
      FixedTargetExtension.localizedFiber (C := C) (0 : C) :=
  baseChangeFunctor (ExtensionCategory.zeroMonoHom X)

/-- Pullback along the original epi zero span. -/
def zeroEpiBaseChange (X : C) :
    FixedTargetExtension.localizedFiber (C := C) X ⥤
      FixedTargetExtension.localizedFiber (C := C) (0 : C) :=
  baseChangeFunctor (ExtensionCategory.zeroEpiHom X)

/-- The original kernel zero row paired with the very same denominator. -/
def kernelSource {X : C} (a : FixedTargetExtension.localizedRows (C := C) X) :
    ExtensionCategory.localizedExtensions (C := C) :=
  ExtensionCategory.localizedPairInclusion.obj
    ((FixedTargetExtension.zeroRow (⟨a.of.1.A⟩ : Core C)).toExtension, a.of.2)

/-- The original middle zero row at the same denominator. -/
def middleSource {X : C} (a : FixedTargetExtension.localizedRows (C := C) X) :
    ExtensionCategory.localizedExtensions (C := C) :=
  ExtensionCategory.localizedPairInclusion.obj
    ((FixedTargetExtension.zeroRow (⟨a.of.1.B⟩ : Core C)).toExtension, a.of.2)

/-- The canonical kernel object is the actual zero-fiber inclusion after kappa, not a new model. -/
theorem kernelSource_eq_model {X : C} (a : FixedTargetExtension.localizedRows (C := C) X) :
    kernelSource a = (FixedTargetExtension.localizedFiberForget (0 : C)).obj
      ((FixedTargetExtension.localizedFiberFunctor (0 : C)).obj
        ((FixedTargetExtension.zeroLocalizedFunctor (C := C)).obj
          ((FixedTargetExtension.localizedKernelFunctor X).obj a))) := rfl

/-- The canonical middle object is the actual zero-fiber inclusion after beta. -/
theorem middleSource_eq_model {X : C} (a : FixedTargetExtension.localizedRows (C := C) X) :
    middleSource a = (FixedTargetExtension.localizedFiberForget (0 : C)).obj
      ((FixedTargetExtension.localizedFiberFunctor (0 : C)).obj
        ((FixedTargetExtension.zeroLocalizedFunctor (C := C)).obj
          ((FixedTargetExtension.localizedMiddleFunctor X).obj a))) := rfl

/-- The actual kernel zero-span arrow uses ordinary inclusion and identity on the denominator. -/
def kernelArrow {X : C} (a : FixedTargetExtension.localizedRows (C := C) X) :
    kernelSource a ⟶ ((FixedTargetExtension.localizedFiberFunctor X).obj a).val :=
  ExtensionCategory.localizedPairInclusion.map
    (X := ((FixedTargetExtension.zeroRow (⟨a.of.1.A⟩ : Core C)).toExtension, a.of.2))
    (Y := (a.of.1.toExtension, a.of.2)) (ExtensionCategory.zeroMonoLift a.of.1, 𝟙 a.of.2)

/-- The actual middle zero-span arrow has the original forward denominator identity. -/
def middleArrow {X : C} (a : FixedTargetExtension.localizedRows (C := C) X) :
    middleSource a ⟶ ((FixedTargetExtension.localizedFiberFunctor X).obj a).val :=
  ExtensionCategory.localizedPairInclusion.map
    (X := ((FixedTargetExtension.zeroRow (⟨a.of.1.B⟩ : Core C)).toExtension, a.of.2))
    (Y := (a.of.1.toExtension, a.of.2)) (ExtensionCategory.zeroEpiLift a.of.1, 𝟙 a.of.2)

/-- Strong cartesianness is derived from the actual original lift and verified pair theorem. -/
theorem kernelArrow_strong {X : C} (a : FixedTargetExtension.localizedRows (C := C) X) :
    Functor.IsStronglyCartesian (projection (C := C)) (ExtensionCategory.zeroMonoHom X)
      (kernelArrow a) := by
  let _ : Functor.IsHomLift (ExtensionCategory.target (C := C))
      (ExtensionCategory.zeroMonoHom X) (ExtensionCategory.zeroMonoLift a.of.1) :=
    ExtensionCategory.zeroMonoLift_isHomLift a.of.1
  exact ExtensionCategory.localizedPairInclusion_isStronglyCartesian
    (ExtensionCategory.zeroMonoHom X) (ExtensionCategory.zeroMonoLift a.of.1) a.of.2

/-- The corresponding actual epi-zero lift is also derived strongly Cartesian. -/
theorem middleArrow_strong {X : C} (a : FixedTargetExtension.localizedRows (C := C) X) :
    Functor.IsStronglyCartesian (projection (C := C)) (ExtensionCategory.zeroEpiHom X)
      (middleArrow a) := by
  let _ : Functor.IsHomLift (ExtensionCategory.target (C := C))
      (ExtensionCategory.zeroEpiHom X) (ExtensionCategory.zeroEpiLift a.of.1) :=
    ExtensionCategory.zeroEpiLift_isHomLift a.of.1
  exact ExtensionCategory.localizedPairInclusion_isStronglyCartesian
    (ExtensionCategory.zeroEpiHom X) (ExtensionCategory.zeroEpiLift a.of.1) a.of.2

/-- The chosen kernel pullback compares with the canonical object at the original denominator. -/
def kernelPullbackComparison {X : C} (a : FixedTargetExtension.localizedRows (C := C) X) :
    (baseChangeObject (ExtensionCategory.zeroMonoHom X)
      ((FixedTargetExtension.localizedFiberFunctor X).obj a)).val ≅ kernelSource a := by
  let _ : Functor.IsCartesian (projection (C := C))
      (ExtensionCategory.zeroMonoHom X)
      (baseChangeLift (ExtensionCategory.zeroMonoHom X)
        ((FixedTargetExtension.localizedFiberFunctor X).obj a)) := by
    exact baseChangeLift_cartesian (ExtensionCategory.zeroMonoHom X)
      ((FixedTargetExtension.localizedFiberFunctor X).obj a)
  let _ : Functor.IsStronglyCartesian (projection (C := C))
      (ExtensionCategory.zeroMonoHom X) (kernelArrow a) := kernelArrow_strong a
  exact Functor.IsCartesian.domainUniqueUpToIso (projection (C := C))
    (ExtensionCategory.zeroMonoHom X) (kernelArrow a)
    (baseChangeLift (ExtensionCategory.zeroMonoHom X)
      ((FixedTargetExtension.localizedFiberFunctor X).obj a))

/-- The chosen middle pullback compares with the original middle zero row and denominator. -/
def middlePullbackComparison {X : C} (a : FixedTargetExtension.localizedRows (C := C) X) :
    (baseChangeObject (ExtensionCategory.zeroEpiHom X)
      ((FixedTargetExtension.localizedFiberFunctor X).obj a)).val ≅ middleSource a := by
  let _ : Functor.IsCartesian (projection (C := C))
      (ExtensionCategory.zeroEpiHom X)
      (baseChangeLift (ExtensionCategory.zeroEpiHom X)
        ((FixedTargetExtension.localizedFiberFunctor X).obj a)) := by
    exact baseChangeLift_cartesian (ExtensionCategory.zeroEpiHom X)
      ((FixedTargetExtension.localizedFiberFunctor X).obj a)
  let _ : Functor.IsStronglyCartesian (projection (C := C))
      (ExtensionCategory.zeroEpiHom X) (middleArrow a) := middleArrow_strong a
  exact Functor.IsCartesian.domainUniqueUpToIso (projection (C := C))
    (ExtensionCategory.zeroEpiHom X) (middleArrow a)
    (baseChangeLift (ExtensionCategory.zeroEpiHom X)
      ((FixedTargetExtension.localizedFiberFunctor X).obj a))

/-- The comparison factors the exact actual chosen kernel lift. -/
theorem kernelPullbackComparison_fac {X : C}
    (a : FixedTargetExtension.localizedRows (C := C) X) :
    (kernelPullbackComparison a).hom ≫ kernelArrow a =
      baseChangeLift (ExtensionCategory.zeroMonoHom X)
        ((FixedTargetExtension.localizedFiberFunctor X).obj a) := by
  let _ : Functor.IsCartesian (projection (C := C))
      (ExtensionCategory.zeroMonoHom X)
      (baseChangeLift (ExtensionCategory.zeroMonoHom X)
        ((FixedTargetExtension.localizedFiberFunctor X).obj a)) := by
    exact baseChangeLift_cartesian (ExtensionCategory.zeroMonoHom X)
      ((FixedTargetExtension.localizedFiberFunctor X).obj a)
  let _ : Functor.IsStronglyCartesian (projection (C := C))
      (ExtensionCategory.zeroMonoHom X) (kernelArrow a) := kernelArrow_strong a
  exact Functor.IsCartesian.fac (projection (C := C)) (ExtensionCategory.zeroMonoHom X)
    (kernelArrow a) (baseChangeLift (ExtensionCategory.zeroMonoHom X)
      ((FixedTargetExtension.localizedFiberFunctor X).obj a))

/-- The same factor law retains the actual chosen epi-zero lift. -/
theorem middlePullbackComparison_fac {X : C}
    (a : FixedTargetExtension.localizedRows (C := C) X) :
    (middlePullbackComparison a).hom ≫ middleArrow a =
      baseChangeLift (ExtensionCategory.zeroEpiHom X)
        ((FixedTargetExtension.localizedFiberFunctor X).obj a) := by
  let _ : Functor.IsCartesian (projection (C := C))
      (ExtensionCategory.zeroEpiHom X)
      (baseChangeLift (ExtensionCategory.zeroEpiHom X)
        ((FixedTargetExtension.localizedFiberFunctor X).obj a)) := by
    exact baseChangeLift_cartesian (ExtensionCategory.zeroEpiHom X)
      ((FixedTargetExtension.localizedFiberFunctor X).obj a)
  let _ : Functor.IsStronglyCartesian (projection (C := C))
      (ExtensionCategory.zeroEpiHom X) (middleArrow a) := middleArrow_strong a
  exact Functor.IsCartesian.fac (projection (C := C)) (ExtensionCategory.zeroEpiHom X)
    (middleArrow a) (baseChangeLift (ExtensionCategory.zeroEpiHom X)
      ((FixedTargetExtension.localizedFiberFunctor X).obj a))

end AlgebraicKTheory.LocalizedBaseChange

end

/-! ## Actual localized zero-span squares and natural pullback comparisons -/

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace AlgebraicKTheory.LocalizedBaseChange

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] ExtensionCategory.leftSumAction
attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction
attribute [local instance] ExtensionCategory.localizedTarget_isFibered

/-- The actual kernel/zero-row functors land in the literal target fiber at zero. -/
def kernelFiberFunctor (X : C) : FixedTargetExtension.localizedRows (C := C) X ⥤
    FixedTargetExtension.localizedFiber (C := C) (0 : C) :=
  FixedTargetExtension.localizedKernelFunctor X ⋙ FixedTargetExtension.zeroLocalizedFunctor ⋙
    FixedTargetExtension.localizedFiberFunctor (0 : C)

/-- The actual middle/zero-row functors land in that same independently defined fiber. -/
def middleFiberFunctor (X : C) : FixedTargetExtension.localizedRows (C := C) X ⥤
    FixedTargetExtension.localizedFiber (C := C) (0 : C) :=
  FixedTargetExtension.localizedMiddleFunctor X ⋙ FixedTargetExtension.zeroLocalizedFunctor ⋙
    FixedTargetExtension.localizedFiberFunctor (0 : C)

private def beta {E F : ExtensionCategory C} (f : E ⟶ F) : E.row.X₂ ⟶ F.row.X₂ :=
  (ExtensionCategory.homNormalization f).hom.2.hom

private theorem beta_comp {E F G : ExtensionCategory C} (f : E ⟶ F) (g : F ⟶ G) :
    beta (f ≫ g) = beta f ≫ beta g := by
  refine Quotient.inductionOn₂ f g ?_
  intro d e
  exact ExtensionCategory.comp_beta d e

private theorem beta_zeroMono {X : C} (E : FixedTargetExtension C X) :
    beta (ExtensionCategory.zeroMonoLift E) = E.i :=
  congrArg (fun h => h.hom.2.hom)
    (ExtensionCategory.homNormalization_mkHom (ExtensionCategory.zeroMonoDiagram E))

private theorem beta_zeroEpi {X : C} (E : FixedTargetExtension C X) :
    beta (ExtensionCategory.zeroEpiLift E) = 𝟙 E.B :=
  congrArg (fun h => h.hom.2.hom)
    (ExtensionCategory.homNormalization_mkHom (ExtensionCategory.zeroEpiDiagram E))

private theorem beta_leftSum {T : Core C} {E F : ExtensionCategory C} (f : E ⟶ F) :
    beta (ExtensionCategory.leftSumMap (𝟙 T) f) = biprod.map (𝟙 T.of) (beta f) :=
  ExtensionCategory.leftSumMap_beta (𝟙 T) f

private theorem kernel_raw_square {X : C}
    {a b : FixedTargetExtension.localizedRows (C := C) X}
    (r : MonoidalActionCategory.RawHom a b) :
    let k := FixedTargetExtension.localizedRawMap
      (FixedTargetExtension.zeroLocalizedRawMap (FixedTargetExtension.kernelLocalizedRawMap r))
    let g := FixedTargetExtension.localizedRawMap r
    let fa : (kernelSource a).of ⟶ ((FixedTargetExtension.localizedFiberFunctor X).obj a).val.of :=
      (ExtensionCategory.zeroMonoLift a.of.1, 𝟙 a.of.2)
    let fb : (kernelSource b).of ⟶ ((FixedTargetExtension.localizedFiberFunctor X).obj b).val.of :=
      (ExtensionCategory.zeroMonoLift b.of.1, 𝟙 b.of.2)
    k.hom ≫ fb = r.stabilizer ⊴ₗ fa ≫ g.hom := by
  dsimp only
  apply Prod.ext
  · apply ExtensionCategory.hom_ext_of_middle
    let kr := FixedTargetExtension.zeroLocalizedRawMap
      (FixedTargetExtension.kernelLocalizedRawMap r)
    let gr := FixedTargetExtension.localizedRawMap r
    let f := FixedTargetExtension.localizedRawMap kr
    have hk : beta f.hom.1 = r.hom.1.a.hom :=
      FixedTargetExtension.localizedRawMap_beta kr
    have hg : beta gr.hom.1 = r.hom.1.b.hom := FixedTargetExtension.localizedRawMap_beta r
    have hl : beta (f.hom.1 ≫ ExtensionCategory.zeroMonoLift b.of.1) =
        r.hom.1.a.hom ≫ b.of.1.i :=
      (beta_comp f.hom.1 (ExtensionCategory.zeroMonoLift b.of.1)).trans
        (congrArg₂ (fun p q => p ≫ q) hk (beta_zeroMono b.of.1))
    have hs : beta (ExtensionCategory.leftSumMap (𝟙 r.stabilizer)
        (ExtensionCategory.zeroMonoLift a.of.1)) =
        biprod.map (𝟙 r.stabilizer.of) a.of.1.i :=
      (beta_leftSum (ExtensionCategory.zeroMonoLift a.of.1)).trans
        (congrArg (biprod.map (𝟙 r.stabilizer.of)) (beta_zeroMono a.of.1))
    have hr : beta (ExtensionCategory.leftSumMap (𝟙 r.stabilizer)
        (ExtensionCategory.zeroMonoLift a.of.1) ≫ gr.hom.1) =
        biprod.map (𝟙 r.stabilizer.of) a.of.1.i ≫ r.hom.1.b.hom :=
      (beta_comp _ gr.hom.1).trans (congrArg₂ (fun p q => p ≫ q) hs hg)
    exact hl.trans (r.hom.1.comm_i.symm.trans hr.symm)
  · change r.hom.2 ≫ 𝟙 b.of.2 = (r.stabilizer ◁ 𝟙 a.of.2) ≫ r.hom.2
    simp only [whiskerLeft_id, Category.comp_id, Category.id_comp]

private theorem middle_raw_square {X : C}
    {a b : FixedTargetExtension.localizedRows (C := C) X}
    (r : MonoidalActionCategory.RawHom a b) :
    let k := FixedTargetExtension.localizedRawMap
      (FixedTargetExtension.zeroLocalizedRawMap (FixedTargetExtension.middleLocalizedRawMap r))
    let g := FixedTargetExtension.localizedRawMap r
    let fa : (middleSource a).of ⟶ ((FixedTargetExtension.localizedFiberFunctor X).obj a).val.of :=
      (ExtensionCategory.zeroEpiLift a.of.1, 𝟙 a.of.2)
    let fb : (middleSource b).of ⟶ ((FixedTargetExtension.localizedFiberFunctor X).obj b).val.of :=
      (ExtensionCategory.zeroEpiLift b.of.1, 𝟙 b.of.2)
    k.hom ≫ fb = r.stabilizer ⊴ₗ fa ≫ g.hom := by
  dsimp only
  apply Prod.ext
  · apply ExtensionCategory.hom_ext_of_middle
    let kr := FixedTargetExtension.zeroLocalizedRawMap
      (FixedTargetExtension.middleLocalizedRawMap r)
    let gr := FixedTargetExtension.localizedRawMap r
    let f := FixedTargetExtension.localizedRawMap kr
    have hk : beta f.hom.1 = r.hom.1.b.hom := FixedTargetExtension.localizedRawMap_beta kr
    have hg : beta gr.hom.1 = r.hom.1.b.hom := FixedTargetExtension.localizedRawMap_beta r
    have hl : beta (f.hom.1 ≫ ExtensionCategory.zeroEpiLift b.of.1) = r.hom.1.b.hom :=
      (beta_comp f.hom.1 (ExtensionCategory.zeroEpiLift b.of.1)).trans
        ((congrArg₂ (fun p q => p ≫ q) hk (beta_zeroEpi b.of.1)).trans
          (Category.comp_id r.hom.1.b.hom))
    have hs : beta (ExtensionCategory.leftSumMap (𝟙 r.stabilizer)
        (ExtensionCategory.zeroEpiLift a.of.1)) = 𝟙 (r.stabilizer.of ⊞ a.of.1.B) := by
      have h := (beta_leftSum (ExtensionCategory.zeroEpiLift a.of.1)).trans
        (congrArg (biprod.map (𝟙 r.stabilizer.of)) (beta_zeroEpi a.of.1))
      have hId : biprod.map (𝟙 r.stabilizer.of) (𝟙 a.of.1.B) =
          𝟙 (r.stabilizer.of ⊞ a.of.1.B) := by
        apply biprod.hom_ext
        · exact (biprod.map_fst (𝟙 r.stabilizer.of) (𝟙 a.of.1.B)).trans
            ((Category.comp_id
              (biprod.fst : r.stabilizer.of ⊞ a.of.1.B ⟶ r.stabilizer.of)).trans
              (Category.id_comp
                (biprod.fst : r.stabilizer.of ⊞ a.of.1.B ⟶ r.stabilizer.of)).symm)
        · exact (biprod.map_snd (𝟙 r.stabilizer.of) (𝟙 a.of.1.B)).trans
            ((Category.comp_id
              (biprod.snd : r.stabilizer.of ⊞ a.of.1.B ⟶ a.of.1.B)).trans
              (Category.id_comp
                (biprod.snd : r.stabilizer.of ⊞ a.of.1.B ⟶ a.of.1.B)).symm)
      exact h.trans hId
    have hr : beta (ExtensionCategory.leftSumMap (𝟙 r.stabilizer)
        (ExtensionCategory.zeroEpiLift a.of.1) ≫ gr.hom.1) = r.hom.1.b.hom :=
      (beta_comp _ gr.hom.1).trans
        ((congrArg₂ (fun p q => p ≫ q) hs hg).trans (Category.id_comp r.hom.1.b.hom))
    exact hl.trans hr.symm
  · change r.hom.2 ≫ 𝟙 b.of.2 = (r.stabilizer ◁ 𝟙 a.of.2) ≫ r.hom.2
    simp only [whiskerLeft_id, Category.comp_id, Category.id_comp]

private theorem raw_comp_pair_rel {a b c : ExtensionCategory.localizedExtensions (C := C)}
    (r : MonoidalActionCategory.RawHom a b) (f : b.of ⟶ c.of) :
    (r.comp (MonoidalActionCategory.RawHom.ofMap (S := Core C) f)).Rel
      (⟨r.stabilizer, r.hom ≫ f⟩ : MonoidalActionCategory.RawHom a c) := by
  refine ⟨λ_ r.stabilizer, ?_⟩
  dsimp only [MonoidalActionCategory.RawHom.comp, MonoidalActionCategory.RawHom.ofMap]
  rw [MonoidalLeftAction.leftUnitor_actionHom]
  simp only [Category.assoc]
  rw [MonoidalLeftAction.actionUnitIso_hom_naturality_assoc]

private theorem raw_pair_comp_rel {a b c : ExtensionCategory.localizedExtensions (C := C)}
    (f : a.of ⟶ b.of) (r : MonoidalActionCategory.RawHom b c) :
    ((MonoidalActionCategory.RawHom.ofMap (S := Core C) f).comp r).Rel
      (⟨r.stabilizer, r.stabilizer ⊴ₗ f ≫ r.hom⟩ : MonoidalActionCategory.RawHom a c) := by
  refine ⟨ρ_ r.stabilizer, ?_⟩
  dsimp only [MonoidalActionCategory.RawHom.comp, MonoidalActionCategory.RawHom.ofMap]
  rw [MonoidalLeftAction.rightUnitor_actionHom]
  simp only [Category.assoc, MonoidalLeftAction.actionHomRight_comp]

/-- The localized kernel zero-span square retains the actual raw stabilizer and denominator. -/
theorem kernelArrow_naturality {X : C}
    {a b : FixedTargetExtension.localizedRows (C := C) X} (f : a ⟶ b) :
    ((kernelFiberFunctor X).map f).val ≫ kernelArrow b =
      kernelArrow a ≫ ((FixedTargetExtension.localizedFiberFunctor X).map f).val := by
  obtain ⟨r, rfl⟩ := MonoidalActionCategory.Hom.exists_rep f
  let k := FixedTargetExtension.localizedRawMap
    (FixedTargetExtension.zeroLocalizedRawMap (FixedTargetExtension.kernelLocalizedRawMap r))
  let g := FixedTargetExtension.localizedRawMap r
  let t := ((FixedTargetExtension.localizedFiberFunctor X).obj b).val
  let fa : (kernelSource a).of ⟶ ((FixedTargetExtension.localizedFiberFunctor X).obj a).val.of :=
    (ExtensionCategory.zeroMonoLift a.of.1, 𝟙 a.of.2)
  let fb : (kernelSource b).of ⟶ t.of := (ExtensionCategory.zeroMonoLift b.of.1, 𝟙 b.of.2)
  let l : MonoidalActionCategory.RawHom (kernelSource a) t := ⟨r.stabilizer, k.hom ≫ fb⟩
  let m : MonoidalActionCategory.RawHom (kernelSource a) t :=
    ⟨r.stabilizer, r.stabilizer ⊴ₗ fa ≫ g.hom⟩
  have he : l = m := congrArg
    (fun h : r.stabilizer ⊙ₗ (kernelSource a).of ⟶ t.of =>
      (⟨r.stabilizer, h⟩ : MonoidalActionCategory.RawHom (kernelSource a) t))
    (kernel_raw_square r)
  change MonoidalActionCategory.Hom.mk
      (k.comp (MonoidalActionCategory.RawHom.ofMap (S := Core C) fb)) =
    MonoidalActionCategory.Hom.mk
      ((MonoidalActionCategory.RawHom.ofMap (S := Core C) fa).comp g)
  exact (Quotient.sound (raw_comp_pair_rel
    (a := kernelSource a) (b := kernelSource b) (c := t) k fb)).trans
    ((congrArg MonoidalActionCategory.Hom.mk he).trans
      (Quotient.sound (raw_pair_comp_rel (a := kernelSource a)
        (b := ((FixedTargetExtension.localizedFiberFunctor X).obj a).val) (c := t) fa g)).symm)

/-- The localized middle zero-span square retains the same original denominator map. -/
theorem middleArrow_naturality {X : C}
    {a b : FixedTargetExtension.localizedRows (C := C) X} (f : a ⟶ b) :
    ((middleFiberFunctor X).map f).val ≫ middleArrow b =
      middleArrow a ≫ ((FixedTargetExtension.localizedFiberFunctor X).map f).val := by
  obtain ⟨r, rfl⟩ := MonoidalActionCategory.Hom.exists_rep f
  let k := FixedTargetExtension.localizedRawMap
    (FixedTargetExtension.zeroLocalizedRawMap (FixedTargetExtension.middleLocalizedRawMap r))
  let g := FixedTargetExtension.localizedRawMap r
  let t := ((FixedTargetExtension.localizedFiberFunctor X).obj b).val
  let fa : (middleSource a).of ⟶ ((FixedTargetExtension.localizedFiberFunctor X).obj a).val.of :=
    (ExtensionCategory.zeroEpiLift a.of.1, 𝟙 a.of.2)
  let fb : (middleSource b).of ⟶ t.of := (ExtensionCategory.zeroEpiLift b.of.1, 𝟙 b.of.2)
  let l : MonoidalActionCategory.RawHom (middleSource a) t := ⟨r.stabilizer, k.hom ≫ fb⟩
  let m : MonoidalActionCategory.RawHom (middleSource a) t :=
    ⟨r.stabilizer, r.stabilizer ⊴ₗ fa ≫ g.hom⟩
  have he : l = m := congrArg
    (fun h : r.stabilizer ⊙ₗ (middleSource a).of ⟶ t.of =>
      (⟨r.stabilizer, h⟩ : MonoidalActionCategory.RawHom (middleSource a) t))
    (middle_raw_square r)
  change MonoidalActionCategory.Hom.mk
      (k.comp (MonoidalActionCategory.RawHom.ofMap (S := Core C) fb)) =
    MonoidalActionCategory.Hom.mk
      ((MonoidalActionCategory.RawHom.ofMap (S := Core C) fa).comp g)
  exact (Quotient.sound (raw_comp_pair_rel
    (a := middleSource a) (b := middleSource b) (c := t) k fb)).trans
    ((congrArg MonoidalActionCategory.Hom.mk he).trans
      (Quotient.sound (raw_pair_comp_rel (a := middleSource a)
        (b := ((FixedTargetExtension.localizedFiberFunctor X).obj a).val) (c := t) fa g)).symm)

/-- The actual kernel comparison is an isomorphism in the literal zero fiber. -/
def kernelFiberComparison {X : C} (a : FixedTargetExtension.localizedRows (C := C) X) :
    (zeroMonoBaseChange X).obj ((FixedTargetExtension.localizedFiberFunctor X).obj a) ≅
      (kernelFiberFunctor X).obj a := by
  let e := kernelPullbackComparison a
  refine
    { hom := ⟨e.hom, ?_⟩
      inv := ⟨e.inv, ?_⟩
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · let _ : Functor.IsCartesian (projection (C := C))
        (ExtensionCategory.zeroMonoHom X)
        (baseChangeLift (ExtensionCategory.zeroMonoHom X)
          ((FixedTargetExtension.localizedFiberFunctor X).obj a)) := by
      exact baseChangeLift_cartesian (ExtensionCategory.zeroMonoHom X)
        ((FixedTargetExtension.localizedFiberFunctor X).obj a)
    let _ : Functor.IsStronglyCartesian (projection (C := C))
        (ExtensionCategory.zeroMonoHom X) (kernelArrow a) := kernelArrow_strong a
    exact Functor.IsCartesian.domainUniqueUpToIso_inv_isHomLift (projection (C := C))
      (ExtensionCategory.zeroMonoHom X) (kernelArrow a)
      (baseChangeLift (ExtensionCategory.zeroMonoHom X)
        ((FixedTargetExtension.localizedFiberFunctor X).obj a))
  · let _ : Functor.IsCartesian (projection (C := C))
        (ExtensionCategory.zeroMonoHom X)
        (baseChangeLift (ExtensionCategory.zeroMonoHom X)
          ((FixedTargetExtension.localizedFiberFunctor X).obj a)) := by
      exact baseChangeLift_cartesian (ExtensionCategory.zeroMonoHom X)
        ((FixedTargetExtension.localizedFiberFunctor X).obj a)
    let _ : Functor.IsStronglyCartesian (projection (C := C))
        (ExtensionCategory.zeroMonoHom X) (kernelArrow a) := kernelArrow_strong a
    exact Functor.IsCartesian.domainUniqueUpToIso_hom_isHomLift (projection (C := C))
      (ExtensionCategory.zeroMonoHom X) (kernelArrow a)
      (baseChangeLift (ExtensionCategory.zeroMonoHom X)
        ((FixedTargetExtension.localizedFiberFunctor X).obj a))
  · apply Functor.Fiber.hom_ext
    exact e.hom_inv_id
  · apply Functor.Fiber.hom_ext
    exact e.inv_hom_id

/-- The actual middle comparison also belongs to that literal zero fiber. -/
def middleFiberComparison {X : C} (a : FixedTargetExtension.localizedRows (C := C) X) :
    (zeroEpiBaseChange X).obj ((FixedTargetExtension.localizedFiberFunctor X).obj a) ≅
      (middleFiberFunctor X).obj a := by
  let e := middlePullbackComparison a
  refine
    { hom := ⟨e.hom, ?_⟩
      inv := ⟨e.inv, ?_⟩
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · let _ : Functor.IsCartesian (projection (C := C))
        (ExtensionCategory.zeroEpiHom X)
        (baseChangeLift (ExtensionCategory.zeroEpiHom X)
          ((FixedTargetExtension.localizedFiberFunctor X).obj a)) := by
      exact baseChangeLift_cartesian (ExtensionCategory.zeroEpiHom X)
        ((FixedTargetExtension.localizedFiberFunctor X).obj a)
    let _ : Functor.IsStronglyCartesian (projection (C := C))
        (ExtensionCategory.zeroEpiHom X) (middleArrow a) := middleArrow_strong a
    exact Functor.IsCartesian.domainUniqueUpToIso_inv_isHomLift (projection (C := C))
      (ExtensionCategory.zeroEpiHom X) (middleArrow a)
      (baseChangeLift (ExtensionCategory.zeroEpiHom X)
        ((FixedTargetExtension.localizedFiberFunctor X).obj a))
  · let _ : Functor.IsCartesian (projection (C := C))
        (ExtensionCategory.zeroEpiHom X)
        (baseChangeLift (ExtensionCategory.zeroEpiHom X)
          ((FixedTargetExtension.localizedFiberFunctor X).obj a)) := by
      exact baseChangeLift_cartesian (ExtensionCategory.zeroEpiHom X)
        ((FixedTargetExtension.localizedFiberFunctor X).obj a)
    let _ : Functor.IsStronglyCartesian (projection (C := C))
        (ExtensionCategory.zeroEpiHom X) (middleArrow a) := middleArrow_strong a
    exact Functor.IsCartesian.domainUniqueUpToIso_hom_isHomLift (projection (C := C))
      (ExtensionCategory.zeroEpiHom X) (middleArrow a)
      (baseChangeLift (ExtensionCategory.zeroEpiHom X)
        ((FixedTargetExtension.localizedFiberFunctor X).obj a))
  · apply Functor.Fiber.hom_ext
    exact e.hom_inv_id
  · apply Functor.Fiber.hom_ext
    exact e.inv_hom_id

/-- Cartesian factor uniqueness proves naturality of the chosen kernel comparison. -/
theorem kernelFiberComparison_naturality {X : C}
    {a b : FixedTargetExtension.localizedRows (C := C) X} (f : a ⟶ b) :
    (zeroMonoBaseChange X).map ((FixedTargetExtension.localizedFiberFunctor X).map f) ≫
        (kernelFiberComparison b).hom =
      (kernelFiberComparison a).hom ≫ (kernelFiberFunctor X).map f := by
  let l := (zeroMonoBaseChange X).map ((FixedTargetExtension.localizedFiberFunctor X).map f) ≫
    (kernelFiberComparison b).hom
  let r := (kernelFiberComparison a).hom ≫ (kernelFiberFunctor X).map f
  apply Functor.Fiber.hom_ext
  have hCart : Functor.IsCartesian (projection (C := C))
      (ExtensionCategory.zeroMonoHom X) (kernelArrow b) := by
    let _ : Functor.IsStronglyCartesian (projection (C := C))
        (ExtensionCategory.zeroMonoHom X) (kernelArrow b) := kernelArrow_strong b
    infer_instance
  let g := (FixedTargetExtension.localizedFiberFunctor X).map f
  have hl : l.val ≫ kernelArrow b = baseChangeLift (ExtensionCategory.zeroMonoHom X)
      ((FixedTargetExtension.localizedFiberFunctor X).obj a) ≫ g.val :=
    (Category.assoc _ _ _).trans
      ((congrArg ((baseChangeMap (ExtensionCategory.zeroMonoHom X) g).val ≫ ·)
        (kernelPullbackComparison_fac b)).trans
        (baseChangeMap_fac (ExtensionCategory.zeroMonoHom X) g))
  have hr : r.val ≫ kernelArrow b = baseChangeLift (ExtensionCategory.zeroMonoHom X)
      ((FixedTargetExtension.localizedFiberFunctor X).obj a) ≫ g.val :=
    (Category.assoc _ _ _).trans
      ((congrArg ((kernelPullbackComparison a).hom ≫ ·) (kernelArrow_naturality f)).trans
        (((Category.assoc _ _ _).symm).trans
          (congrArg (· ≫ g.val) (kernelPullbackComparison_fac a))))
  exact @Functor.IsCartesian.ext _ _ _ _ (projection (C := C)) _ _ _ _
    (ExtensionCategory.zeroMonoHom X) (kernelArrow b) hCart _
    l.val r.val l.property r.property (hl.trans hr.symm)

/-- The middle comparison is natural by the independently derived middle square. -/
theorem middleFiberComparison_naturality {X : C}
    {a b : FixedTargetExtension.localizedRows (C := C) X} (f : a ⟶ b) :
    (zeroEpiBaseChange X).map ((FixedTargetExtension.localizedFiberFunctor X).map f) ≫
        (middleFiberComparison b).hom =
      (middleFiberComparison a).hom ≫ (middleFiberFunctor X).map f := by
  let l := (zeroEpiBaseChange X).map ((FixedTargetExtension.localizedFiberFunctor X).map f) ≫
    (middleFiberComparison b).hom
  let r := (middleFiberComparison a).hom ≫ (middleFiberFunctor X).map f
  apply Functor.Fiber.hom_ext
  have hCart : Functor.IsCartesian (projection (C := C))
      (ExtensionCategory.zeroEpiHom X) (middleArrow b) := by
    let _ : Functor.IsStronglyCartesian (projection (C := C))
        (ExtensionCategory.zeroEpiHom X) (middleArrow b) := middleArrow_strong b
    infer_instance
  let g := (FixedTargetExtension.localizedFiberFunctor X).map f
  have hl : l.val ≫ middleArrow b = baseChangeLift (ExtensionCategory.zeroEpiHom X)
      ((FixedTargetExtension.localizedFiberFunctor X).obj a) ≫ g.val :=
    (Category.assoc _ _ _).trans
      ((congrArg ((baseChangeMap (ExtensionCategory.zeroEpiHom X) g).val ≫ ·)
        (middlePullbackComparison_fac b)).trans
        (baseChangeMap_fac (ExtensionCategory.zeroEpiHom X) g))
  have hr : r.val ≫ middleArrow b = baseChangeLift (ExtensionCategory.zeroEpiHom X)
      ((FixedTargetExtension.localizedFiberFunctor X).obj a) ≫ g.val :=
    (Category.assoc _ _ _).trans
      ((congrArg ((middlePullbackComparison a).hom ≫ ·) (middleArrow_naturality f)).trans
        (((Category.assoc _ _ _).symm).trans
          (congrArg (· ≫ g.val) (middlePullbackComparison_fac a))))
  exact @Functor.IsCartesian.ext _ _ _ _ (projection (C := C)) _ _ _ _
    (ExtensionCategory.zeroEpiHom X) (middleArrow b) hCart _
    l.val r.val l.property r.property (hl.trans hr.symm)

/-- The actual chosen mono-zero pullback is naturally the kernel/zero-row functor comparison. -/
def zeroMonoKernelNatIso (X : C) :
    FixedTargetExtension.localizedFiberFunctor X ⋙ zeroMonoBaseChange X ≅ kernelFiberFunctor X :=
  NatIso.ofComponents kernelFiberComparison (by
    intro a b f
    exact kernelFiberComparison_naturality f)

/-- The actual chosen epi-zero pullback is naturally the middle/zero-row functor comparison. -/
def zeroEpiMiddleNatIso (X : C) :
    FixedTargetExtension.localizedFiberFunctor X ⋙ zeroEpiBaseChange X ≅ middleFiberFunctor X :=
  NatIso.ofComponents middleFiberComparison (by
    intro a b f
    exact middleFiberComparison_naturality f)

end AlgebraicKTheory.LocalizedBaseChange

end
