/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.KTheory.Exact.Quillen.SpanFlag
public import Mathlib.CategoryTheory.IsConnected

/-!
# The groupoid of explicit flags over a Quillen span

Explicit flag choices over a fixed raw Quillen span form a contractible
groupoid.  A morphism carries the material comparison maps on the kernel,
pushout, and quotient objects.  Compatibility with the induced
pushout-to-quotient map follows by source-pushout extensionality from the
stored leg equations.

Universal properties construct a morphism between any two flags, and
admissible mono/epi cancellation together with pushout extensionality makes
that morphism unique.  Consequently every fixed-span fiber is equivalent to
`Discrete PUnit`.

This file exposes no standalone chosen-flag constructor or selection instance,
and constructs no span-iso transport functor, Grothendieck category,
all-degree grid, realization, Q/S equivalence, additivity, or comparison.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- A material comparison between two explicit flags over the same raw
Quillen span. -/
@[ext]
structure QuillenSpanFlagHom {X Y : C} {S : QuillenSpan X Y}
    (A B : QuillenSpanFlagData S) where
  /-- Comparison of the two kernel objects. -/
  kernelHom : A.kernelObj ⟶ B.kernelObj
  /-- Comparison of the two pushout objects. -/
  pushoutHom : A.pushoutObj ⟶ B.pushoutObj
  /-- Comparison of the two quotient objects. -/
  quotientHom : A.quotientObj ⟶ B.quotientObj
  /-- Compatibility with the kernel inclusion. -/
  kernelHom_kernelι : kernelHom ≫ B.kernelι = A.kernelι
  /-- Compatibility with the pushout leg from the source. -/
  sourceToPushout_naturality :
    A.sourceToPushout ≫ pushoutHom = B.sourceToPushout
  /-- Compatibility with the pushout leg from the target. -/
  targetToPushout_naturality :
    A.targetToPushout ≫ pushoutHom = B.targetToPushout
  /-- Compatibility with the quotient projection. -/
  quotientπ_quotientHom : A.quotientπ ≫ quotientHom = B.quotientπ

attribute [reassoc (attr := simp)]
  QuillenSpanFlagHom.kernelHom_kernelι
  QuillenSpanFlagHom.sourceToPushout_naturality
  QuillenSpanFlagHom.targetToPushout_naturality
  QuillenSpanFlagHom.quotientπ_quotientHom

/-- The induced pushout-to-quotient map is natural under a material flag
comparison. -/
theorem QuillenSpanFlagHom.pushoutToQuotient_naturality
    {X Y : C} {S : QuillenSpan X Y} {A B : QuillenSpanFlagData S}
    (f : QuillenSpanFlagHom A B) :
    A.pushoutToQuotient ≫ f.quotientHom =
      f.pushoutHom ≫ B.pushoutToQuotient := by
  apply A.pushoutSquare.hom_ext
  · simp only [← Category.assoc, A.source_pushoutToQuotient_zero,
      zero_comp, f.sourceToPushout_naturality,
      B.source_pushoutToQuotient_zero]
  · simp only [← Category.assoc, A.target_pushoutToQuotient,
      f.quotientπ_quotientHom, f.targetToPushout_naturality,
      B.target_pushoutToQuotient]

/-- The universal kernel, pushout, and quotient comparisons between two
explicit flags over the same raw span. -/
noncomputable def QuillenSpanFlagHom.canonical
    {X Y : C} {S : QuillenSpan X Y} (A B : QuillenSpanFlagData S) :
    QuillenSpanFlagHom A B := by
  let hKernelB :=
    isLimit_kernelFork_of_isAdmissibleExact B.kernel_apex_source_exact
  let hQuotientA :=
    isColimit_cokernelCofork_of_isAdmissibleExact
      A.apex_target_quotient_exact
  exact
    { kernelHom :=
        hKernelB.lift (KernelFork.ofι A.kernelι A.kernel_left_zero)
      pushoutHom := A.pushoutSquare.desc B.sourceToPushout
        B.targetToPushout B.pushoutSquare.w
      quotientHom := hQuotientA.desc
        (CokernelCofork.ofπ B.quotientπ B.right_quotient_zero)
      kernelHom_kernelι := Fork.IsLimit.lift_ι hKernelB
      sourceToPushout_naturality :=
        A.pushoutSquare.inl_desc _ _ _
      targetToPushout_naturality :=
        A.pushoutSquare.inr_desc _ _ _
      quotientπ_quotientHom := Cofork.IsColimit.π_desc hQuotientA }

noncomputable instance instCategoryQuillenSpanFlagData
    {X Y : C} (S : QuillenSpan X Y) : Category (QuillenSpanFlagData S) where
  Hom := QuillenSpanFlagHom
  id A :=
    { kernelHom := 𝟙 A.kernelObj
      pushoutHom := 𝟙 A.pushoutObj
      quotientHom := 𝟙 A.quotientObj
      kernelHom_kernelι := by simp
      sourceToPushout_naturality := by simp
      targetToPushout_naturality := by simp
      quotientπ_quotientHom := by simp }
  comp f g :=
    { kernelHom := f.kernelHom ≫ g.kernelHom
      pushoutHom := f.pushoutHom ≫ g.pushoutHom
      quotientHom := f.quotientHom ≫ g.quotientHom
      kernelHom_kernelι := by simp
      sourceToPushout_naturality := by simp
      targetToPushout_naturality := by simp
      quotientπ_quotientHom := by simp }
  id_comp f := by ext <;> simp
  comp_id f := by ext <;> simp
  assoc f g h := by ext <;> simp

instance instSubsingletonQuillenSpanFlagHom
    {X Y : C} {S : QuillenSpan X Y} (A B : QuillenSpanFlagData S) :
    Subsingleton (A ⟶ B) where
  allEq f g := by
    apply QuillenSpanFlagHom.ext
    · let _ : Mono B.kernelι :=
        (isAdmissibleMono_f B.kernel_apex_source_exact).mono
      rw [← cancel_mono B.kernelι, f.kernelHom_kernelι,
        g.kernelHom_kernelι]
    · apply A.pushoutSquare.hom_ext
      · rw [f.sourceToPushout_naturality,
          g.sourceToPushout_naturality]
      · rw [f.targetToPushout_naturality,
          g.targetToPushout_naturality]
    · let _ : Epi A.quotientπ :=
        (isAdmissibleEpi_g A.apex_target_quotient_exact).epi
      rw [← cancel_epi A.quotientπ, f.quotientπ_quotientHom,
        g.quotientπ_quotientHom]

noncomputable instance instUniqueQuillenSpanFlagHom
    {X Y : C} {S : QuillenSpan X Y} (A B : QuillenSpanFlagData S) :
    Unique (A ⟶ B) :=
  uniqueOfSubsingleton (QuillenSpanFlagHom.canonical A B)

noncomputable instance instGroupoidQuillenSpanFlagData
    {X Y : C} (S : QuillenSpan X Y) : Groupoid (QuillenSpanFlagData S) :=
  Groupoid.ofHomUnique fun {_ _} => inferInstance

/-- Evaluation of a flag at its kernel object. -/
def quillenSpanFlagKernelFunctor {X Y : C} (S : QuillenSpan X Y) :
    QuillenSpanFlagData S ⥤ C where
  obj A := A.kernelObj
  map f := f.kernelHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Evaluation of a flag at its pushout object. -/
def quillenSpanFlagPushoutFunctor {X Y : C} (S : QuillenSpan X Y) :
    QuillenSpanFlagData S ⥤ C where
  obj A := A.pushoutObj
  map f := f.pushoutHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Evaluation of a flag at its quotient object. -/
def quillenSpanFlagQuotientFunctor {X Y : C} (S : QuillenSpan X Y) :
    QuillenSpanFlagData S ⥤ C where
  obj A := A.quotientObj
  map f := f.quotientHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The groupoid of explicit flags over a fixed raw span is categorically
contractible. -/
noncomputable def quillenSpanFlagFiberEquivalencePUnit
    {X Y : C} (S : QuillenSpan X Y) :
    QuillenSpanFlagData S ≌ Discrete PUnit.{1} :=
  ((equiv_punit_iff_unique (C := QuillenSpanFlagData S)).2
    ⟨QuillenSpanFlagData.nonempty S, fun _ _ => ⟨inferInstance⟩⟩).some

/-- In particular, the groupoid of explicit flags over a fixed raw span is
connected. -/
noncomputable instance quillenSpanFlagFiber_isConnected
    {X Y : C} (S : QuillenSpan X Y) :
    IsConnected (QuillenSpanFlagData S) :=
  isConnected_of_equivalent (quillenSpanFlagFiberEquivalencePUnit S).symm

end AlgebraicKTheory
