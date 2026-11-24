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

public import MathlibExt.CategoryTheory.ExactCategory.PushoutFlag

/-!
# Actual admissible cokernel rows and their composite

The pushout of the first cokernel map and the second admissible mono
retains both original admissible rows. The composite cokernel row and the
extension of the two original cokernels follow from the exact pushout flag.
No abelian ambient, projectivity or caller composite-row outcome is used.
-/

public section

noncomputable section

open CategoryTheory Limits

universe uH vH

namespace CategoryTheory.ExactCategory

variable {H : Type uH} [Category.{vH} H] [Preadditive H]
  [HasZeroObject H] [HasBinaryBiproducts H] [ExactCategory H]

/-- The original admissible mono together with its actual cokernel row. -/
structure AdmissibleMonoCokernelPresentation {A B : H} (i : A ⟶ B) where
  /-- The original quotient object in this admissible cokernel row. -/
  cokernel : H
  /-- The original admissible quotient projection from B. -/
  π : B ⟶ cokernel
  zero : i ≫ π = 0
  exact : ExactCategory.IsAdmissibleExact (ShortComplex.mk i π zero)

namespace AdmissibleMonoCokernelPresentation

variable {A B : H} {i : A ⟶ B}

/-- Any original admissible mono supplies some actual cokernel presentation. -/
theorem nonempty (hi : ExactCategory.IsAdmissibleMono i) :
    Nonempty (AdmissibleMonoCokernelPresentation i) := by
  obtain ⟨C, π, zero, exact⟩ := hi
  exact ⟨{ cokernel := C, π := π, zero := zero, exact := exact }⟩

/-- Admissibility of the original first map comes from its stored row. -/
theorem mono_admissible (K : AdmissibleMonoCokernelPresentation i) :
    ExactCategory.IsAdmissibleMono i :=
  ExactCategory.isAdmissibleMono_f K.exact

/-- The original projection is an admissible epimorphism. -/
theorem π_admissible (K : AdmissibleMonoCokernelPresentation i) :
    ExactCategory.IsAdmissibleEpi K.π :=
  ExactCategory.isAdmissibleEpi_g K.exact

/-- The original cokernel projection has its actual universal property. -/
def cokernelIsColimit (K : AdmissibleMonoCokernelPresentation i) :
    IsColimit (CokernelCofork.ofπ K.π K.zero) :=
  ExactCategory.isColimit_cokernelCofork_of_isAdmissibleExact K.exact

/-- The actual cobase change retains the original cokernel object. -/
structure CobaseChange (K : AdmissibleMonoCokernelPresentation i)
    {A' : H} (f : A ⟶ A') where
  /-- The actual original pushout object of the cobase change. -/
  obj : H
  /-- The original pushed-out admissible mono from A'. -/
  inl : A' ⟶ obj
  /-- The original pushout map from B. -/
  inr : B ⟶ obj
  square : IsPushout f i inl inr
  inl_admissible : ExactCategory.IsAdmissibleMono inl

/-- Original exact-category pushout data for an admissible mono exists. -/
theorem cobaseChange_nonempty (K : AdmissibleMonoCokernelPresentation i)
    {A' : H} (f : A ⟶ A') : Nonempty (K.CobaseChange f) := by
  obtain ⟨P, inl, inr, square, hinl⟩ :=
    ExactCategory.admissibleMono_pushout
      (X := A) (Y := B) (i := i) K.mono_admissible (X' := A') (f := f)
  exact ⟨{
    obj := P
    inl := inl
    inr := inr
    square := square
    inl_admissible := hinl }⟩

/-- The original quotient row after cobase change is admissible exact,
with the same quotient and the actual pushout quotient map. -/
def cobaseChangePresentation (K : AdmissibleMonoCokernelPresentation i)
    {A' : H} {f : A ⟶ A'} (P : K.CobaseChange f) :
    AdmissibleMonoCokernelPresentation P.inl := {
  cokernel := K.cokernel
  π := ExactCategory.pushoutQuotientMap f i K.π P.inl P.inr K.zero P.square
  zero := ExactCategory.pushoutQuotientMap_x f i K.π P.inl P.inr K.zero P.square
  exact := ExactCategory.isAdmissibleExact_pushoutQuotientMap
    f i K.π P.inl P.inr K.zero K.exact P.square }

private theorem originalCobaseCokernelValueComputed (K : AdmissibleMonoCokernelPresentation i)
    {A' : H} {f : A ⟶ A'} (P : K.CobaseChange f) :
    (K.cobaseChangePresentation P).cokernel = K.cokernel := rfl

/-- The actual cobase-changed row keeps the original quotient object. -/
theorem cobaseChangePresentation_cokernel (K : AdmissibleMonoCokernelPresentation i)
    {A' : H} {f : A ⟶ A'} (P : K.CobaseChange f) :
    (K.cobaseChangePresentation P).cokernel = K.cokernel :=
  originalCobaseCokernelValueComputed K P

/-- Actual pushout data of the first cokernel map and the next mono. -/
structure CompositePushout (K : AdmissibleMonoCokernelPresentation i)
    {C : H} (j : B ⟶ C) where
  /-- The actual pushout object that is the composite cokernel. -/
  obj : H
  /-- The original inclusion of the first cokernel into the pushout. -/
  inl : K.cokernel ⟶ obj
  /-- The actual composite-cokernel projection from C. -/
  inr : C ⟶ obj
  square : IsPushout K.π j inl inr
  inl_admissible : ExactCategory.IsAdmissibleMono inl

/-- This composite pushout exists by the original exact-category axiom. -/
theorem compositePushout_nonempty (K : AdmissibleMonoCokernelPresentation i)
    {C : H} {j : B ⟶ C} (L : AdmissibleMonoCokernelPresentation j) :
    Nonempty (K.CompositePushout j) := by
  obtain ⟨P, inl, inr, square, hinl⟩ :=
    ExactCategory.admissibleMono_pushout
      (X := B) (Y := C) (i := j) L.mono_admissible (X' := K.cokernel) (f := K.π)
  exact ⟨{
    obj := P
    inl := inl
    inr := inr
    square := square
    inl_admissible := hinl }⟩

/-- One actual internally selected pushout, preserving the original input rows. -/
def compositePushout (K : AdmissibleMonoCokernelPresentation i)
    {C : H} {j : B ⟶ C} (L : AdmissibleMonoCokernelPresentation j) :
    K.CompositePushout j :=
  (K.compositePushout_nonempty L).some

/-- The actual composite-mono cokernel presentation uses the original
pushout right leg and the exact pushout-flag theorem. -/
def composite (K : AdmissibleMonoCokernelPresentation i)
    {C : H} {j : B ⟶ C} (L : AdmissibleMonoCokernelPresentation j) :
    AdmissibleMonoCokernelPresentation (i ≫ j) :=
  let P := K.compositePushout L
  { cokernel := P.obj
    π := P.inr
    zero := by rw [Category.assoc, ← P.square.w, ← Category.assoc, K.zero, zero_comp]
    exact := ExactCategory.isAdmissibleExact_comp_pushout
      i K.π j L.π P.inl P.inr K.zero L.zero K.exact L.exact P.square }

/-- The first cokernel maps into the actual composite cokernel, which
maps onto the second original cokernel, by the same actual pushout flag. -/
def compositeCokernelSequence (K : AdmissibleMonoCokernelPresentation i)
    {C : H} {j : B ⟶ C} (L : AdmissibleMonoCokernelPresentation j) : ShortComplex H :=
  let P := K.compositePushout L
  ShortComplex.mk P.inl
    (ExactCategory.pushoutQuotientMap K.π j L.π P.inl P.inr L.zero P.square)
    (ExactCategory.pushoutQuotientMap_x K.π j L.π P.inl P.inr L.zero P.square)

/-- The actual cokernel sequence of the composite is admissible exact. -/
theorem compositeCokernelSequence_exact (K : AdmissibleMonoCokernelPresentation i)
    {C : H} {j : B ⟶ C} (L : AdmissibleMonoCokernelPresentation j) :
    ExactCategory.IsAdmissibleExact (K.compositeCokernelSequence L) :=
  let P := K.compositePushout L
  ExactCategory.isAdmissibleExact_pushoutQuotientMap
    K.π j L.π P.inl P.inr L.zero L.exact P.square

private theorem originalCompositeCokernelFirstComputed (K : AdmissibleMonoCokernelPresentation i)
    {C : H} {j : B ⟶ C} (L : AdmissibleMonoCokernelPresentation j) :
    (K.compositeCokernelSequence L).X₁ = K.cokernel := rfl

/-- The left object is the original first cokernel. -/
theorem compositeCokernelSequence_X₁ (K : AdmissibleMonoCokernelPresentation i)
    {C : H} {j : B ⟶ C} (L : AdmissibleMonoCokernelPresentation j) :
    (K.compositeCokernelSequence L).X₁ = K.cokernel :=
  originalCompositeCokernelFirstComputed K L

private theorem originalCompositeCokernelMiddleComputed (K : AdmissibleMonoCokernelPresentation i)
    {C : H} {j : B ⟶ C} (L : AdmissibleMonoCokernelPresentation j) :
    (K.compositeCokernelSequence L).X₂ = (K.composite L).cokernel := rfl

/-- The middle object is the actual composite cokernel from the same pushout. -/
theorem compositeCokernelSequence_X₂ (K : AdmissibleMonoCokernelPresentation i)
    {C : H} {j : B ⟶ C} (L : AdmissibleMonoCokernelPresentation j) :
    (K.compositeCokernelSequence L).X₂ = (K.composite L).cokernel :=
  originalCompositeCokernelMiddleComputed K L

private theorem originalCompositeCokernelThirdComputed (K : AdmissibleMonoCokernelPresentation i)
    {C : H} {j : B ⟶ C} (L : AdmissibleMonoCokernelPresentation j) :
    (K.compositeCokernelSequence L).X₃ = L.cokernel := rfl

/-- The right object is the original second cokernel. -/
theorem compositeCokernelSequence_X₃ (K : AdmissibleMonoCokernelPresentation i)
    {C : H} {j : B ⟶ C} (L : AdmissibleMonoCokernelPresentation j) :
    (K.compositeCokernelSequence L).X₃ = L.cokernel :=
  originalCompositeCokernelThirdComputed K L

end AdmissibleMonoCokernelPresentation

end CategoryTheory.ExactCategory

end
