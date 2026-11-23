/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.ExactCategory.Equivalence
public import MathlibExt.CategoryTheory.ExactCategory.Functor
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Preadditive.Transfer
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# The original exact structure in a canonical larger category world

The existing `AsSmall` equivalence retains every original object and arrow
as its literal universe lift. Its fully faithful down functor transports
the original additive and exact structures as explicit DATA. No replacement
global instances or split exact structure are installed.

The entire structural split-row condition is transported in both directions.
Chosen zero and biproduct objects are retained through their genuine
comparison isomorphisms.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Preadditive
open scoped ZeroObject

universe u v l

namespace CategoryTheory.ExactCategory

variable (C : Type u) [Category.{v} C]

/-- Fully faithful DATA for the actual down functor, whose preimage is
the literal original-arrow lift. -/
def asSmallDownFullyFaithful :
    (AsSmall.down : AsSmall.{l} C ⥤ C).FullyFaithful where
  preimage f := ULift.up f
  map_preimage _ := rfl
  preimage_map f := by cases f; rfl

section Additive

variable [Preadditive C]

/-- Pull the original additive structure back along the actual canonical
down functor. This is explicit DATA. -/
@[instance_reducible]
def asSmallPreadditive : Preadditive (AsSmall.{l} C) :=
  Preadditive.ofFullyFaithful (asSmallDownFullyFaithful.{u, v, l} C)

/-- The actual down functor is additive for the transported DATA. -/
theorem asSmallDown_additive :
    letI := asSmallPreadditive.{u, v, l} C
    (AsSmall.down : AsSmall.{l} C ⥤ C).Additive := by
  let _ := asSmallPreadditive.{u, v, l} C
  exact (asSmallDownFullyFaithful.{u, v, l} C).additive_ofFullyFaithful

/-- The actual original object-and-arrow lift is additive for the same DATA. -/
theorem asSmallUp_additive :
    letI := asSmallPreadditive.{u, v, l} C
    (AsSmall.up : C ⥤ AsSmall.{l} C).Additive := by
  let _ := asSmallPreadditive.{u, v, l} C
  let e : AsSmall.{l} C ≌ C := AsSmall.equiv.symm
  let _ : e.functor.Additive := asSmallDown_additive.{u, v, l} C
  exact e.inverse_additive

variable [HasZeroObject C]

/-- Zero existence is supplied by the image of the original chosen zero;
the resulting structure remains explicit DATA. -/
theorem asSmallHasZeroObject :
    letI := asSmallPreadditive.{u, v, l} C
    HasZeroObject (AsSmall.{l} C) := by
  let _ := asSmallPreadditive.{u, v, l} C
  let _ := asSmallUp_additive.{u, v, l} C
  exact ((AsSmall.up : C ⥤ AsSmall.{l} C).map_isZero (isZero_zero C)).hasZeroObject

/-- The actual lifted source zero and the chosen target zero have their
genuine canonical isomorphism; they are not identified as objects. -/
def asSmallUpZeroIso :
    letI := asSmallPreadditive.{u, v, l} C
    letI := asSmallHasZeroObject.{u, v, l} C
    (AsSmall.up : C ⥤ AsSmall.{l} C).obj (0 : C) ≅ (0 : AsSmall.{l} C) := by
  letI := asSmallPreadditive.{u, v, l} C
  letI := asSmallHasZeroObject.{u, v, l} C
  letI := asSmallUp_additive.{u, v, l} C
  exact (AsSmall.up : C ⥤ AsSmall.{l} C).mapZeroObject

/-- The canonical zero comparison lowers to the original unique arrow
out of the original chosen source zero. -/
theorem asSmallUpZeroIso_hom_down :
    letI := asSmallPreadditive.{u, v, l} C
    letI := asSmallHasZeroObject.{u, v, l} C
    ULift.down (asSmallUpZeroIso.{u, v, l} C).hom =
      (isZero_zero C).to_ (ULift.down (0 : AsSmall.{l} C)) := by
  let _ := asSmallPreadditive.{u, v, l} C
  let _ := asSmallHasZeroObject.{u, v, l} C
  exact (isZero_zero C).eq_of_src _ _

/-- Its inverse lowers to the original unique arrow into the same source zero. -/
theorem asSmallUpZeroIso_inv_down :
    letI := asSmallPreadditive.{u, v, l} C
    letI := asSmallHasZeroObject.{u, v, l} C
    ULift.down (asSmallUpZeroIso.{u, v, l} C).inv =
      (isZero_zero C).from_ (ULift.down (0 : AsSmall.{l} C)) := by
  let _ := asSmallPreadditive.{u, v, l} C
  let _ := asSmallHasZeroObject.{u, v, l} C
  exact (isZero_zero C).eq_of_tgt _ _

variable [HasBinaryBiproducts C]

omit [HasZeroObject C] in
/-- Binary biproduct existence comes from the actual mapped original
bilimit bicones and the actual equivalence, as explicit DATA. -/
theorem asSmallHasBinaryBiproducts :
    letI := asSmallPreadditive.{u, v, l} C
    HasBinaryBiproducts (AsSmall.{l} C) := by
  let _ := asSmallPreadditive.{u, v, l} C
  let _ := asSmallUp_additive.{u, v, l} C
  let F : C ⥤ AsSmall.{l} C := AsSmall.up
  let e : C ≌ AsSmall.{l} C := AsSmall.equiv
  let _ : F.IsEquivalence := by change e.functor.IsEquivalence; infer_instance
  refine ⟨fun X Y => ?_⟩
  let _ : PreservesBinaryBiproduct (ULift.down X) (ULift.down Y) F :=
    preservesBinaryBiproduct_of_preservesBinaryProduct F
  change HasBinaryBiproduct (F.obj (ULift.down X)) (F.obj (ULift.down Y))
  exact Functor.hasBinaryBiproduct_of_preserves F (ULift.down X) (ULift.down Y)

end Additive

section Exact

variable [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The original exact structure pulled back through the literal canonical
down equivalence. This is explicit DATA, with every admissible row preserved. -/
@[instance_reducible]
def asSmallExactCategory :
    letI := asSmallPreadditive.{u, v, l} C
    letI := asSmallHasZeroObject.{u, v, l} C
    letI := asSmallHasBinaryBiproducts.{u, v, l} C
    ExactCategory (AsSmall.{l} C) := by
  letI := asSmallPreadditive.{u, v, l} C
  letI := asSmallHasZeroObject.{u, v, l} C
  letI := asSmallHasBinaryBiproducts.{u, v, l} C
  let e : AsSmall.{l} C ≌ C := AsSmall.equiv.symm
  letI : e.functor.Additive := asSmallDown_additive.{u, v, l} C
  exact ExactCategory.ofEquivalence e

local instance : Preadditive (AsSmall.{l} C) := asSmallPreadditive.{u, v, l} C
local instance : HasZeroObject (AsSmall.{l} C) := asSmallHasZeroObject.{u, v, l} C
local instance : HasBinaryBiproducts (AsSmall.{l} C) := asSmallHasBinaryBiproducts.{u, v, l} C
local instance : ExactCategory (AsSmall.{l} C) := asSmallExactCategory.{u, v, l} C
local instance : (AsSmall.down : AsSmall.{l} C ⥤ C).Additive := asSmallDown_additive.{u, v, l} C
local instance : (AsSmall.up : C ⥤ AsSmall.{l} C).Additive := asSmallUp_additive.{u, v, l} C

/-- Every lifted row is admissible exactly when its original down image is. -/
theorem asSmall_isAdmissibleExact_iff (S : ShortComplex (AsSmall.{l} C)) :
    IsAdmissibleExact S ↔ IsAdmissibleExact (S.map (AsSmall.down : AsSmall.{l} C ⥤ C)) := by
  let e : AsSmall.{l} C ≌ C := AsSmall.equiv.symm
  let _ : e.functor.Additive := asSmallDown_additive.{u, v, l} C
  exact ExactCategory.ofEquivalence_isAdmissibleExact_iff e S

omit [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] in
/-- The actual up/down composite returns every entire original short complex. -/
theorem asSmallUp_down_mapShortComplex (S : ShortComplex C) :
    (S.map (AsSmall.up : C ⥤ AsSmall.{l} C)).map
        (AsSmall.down : AsSmall.{l} C ⥤ C) = S := rfl

/-- The actual up functor preserves and reflects the original admissible rows. -/
theorem asSmallUp_isAdmissibleExact_iff (S : ShortComplex C) :
    IsAdmissibleExact (S.map (AsSmall.up : C ⥤ AsSmall.{l} C)) ↔ IsAdmissibleExact S := by
  rw [asSmall_isAdmissibleExact_iff, asSmallUp_down_mapShortComplex]

/-- The literal down functor is Quillen exact for the original transported structure. -/
theorem asSmallDown_isExact : (AsSmall.down : AsSmall.{l} C ⥤ C).IsExact where
  map_admissibleExact S hS := (asSmall_isAdmissibleExact_iff.{u, v, l} C S).mp hS

/-- The literal original object-and-arrow lift is Quillen exact. -/
theorem asSmallUp_isExact : (AsSmall.up : C ⥤ AsSmall.{l} C).IsExact where
  map_admissibleExact S hS := (asSmallUp_isAdmissibleExact_iff.{u, v, l} C S).mpr hS

/-- The actual equivalence counit compares every entire lifted row with its
down/up image, retaining all three original component isomorphisms. -/
def asSmallDown_up_shortComplexIso (S : ShortComplex (AsSmall.{l} C)) :
    (S.map (AsSmall.down : AsSmall.{l} C ⥤ C)).map (AsSmall.up : C ⥤ AsSmall.{l} C) ≅ S := by
  let e : C ≌ AsSmall.{l} C := AsSmall.equiv
  exact ShortComplex.isoMk (e.counitIso.app S.X₁) (e.counitIso.app S.X₂) (e.counitIso.app S.X₃)
    (e.counitIso.hom.naturality S.f).symm (e.counitIso.hom.naturality S.g).symm

/-- A splitting of the original down row gives the actual splitting of the
lifted row through the same whole counit; this does not assume that row split. -/
def asSmallSplittingOfDown (S : ShortComplex (AsSmall.{l} C))
    (s : (S.map (AsSmall.down : AsSmall.{l} C ⥤ C)).Splitting) : S.Splitting :=
  (s.map (AsSmall.up : C ⥤ AsSmall.{l} C)).ofIso
    (asSmallDown_up_shortComplexIso.{u, v, l} C S)

omit [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] in
/-- The reconstructed splitting retains the entire original retraction
after the actual down map. -/
theorem asSmallSplittingOfDown_r_down (S : ShortComplex (AsSmall.{l} C))
    (s : (S.map (AsSmall.down : AsSmall.{l} C ⥤ C)).Splitting) :
    ULift.down (asSmallSplittingOfDown.{u, v, l} C S s).r = s.r := by
  rcases S with @⟨⟨X₁⟩, ⟨X₂⟩, ⟨X₃⟩, f, g, w⟩
  rcases f with ⟨f⟩
  rcases g with ⟨g⟩
  change (𝟙 X₂ ≫ s.r ≫ 𝟙 X₁) = s.r
  exact (Category.id_comp (s.r ≫ 𝟙 X₁)).trans (Category.comp_id s.r)

omit [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] in
/-- The reconstructed splitting retains the entire original section
after the same actual down map. -/
theorem asSmallSplittingOfDown_s_down (S : ShortComplex (AsSmall.{l} C))
    (s : (S.map (AsSmall.down : AsSmall.{l} C ⥤ C)).Splitting) :
    ULift.down (asSmallSplittingOfDown.{u, v, l} C S s).s = s.s := by
  rcases S with @⟨⟨X₁⟩, ⟨X₂⟩, ⟨X₃⟩, f, g, w⟩
  rcases f with ⟨f⟩
  rcases g with ⟨g⟩
  change (𝟙 X₃ ≫ s.s ≫ 𝟙 X₂) = s.s
  exact (Category.id_comp (s.s ≫ 𝟙 X₂)).trans (Category.comp_id s.s)

omit [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] in
/-- Splitting of every lifted row is equivalent to splitting of its exact
original down image. -/
theorem asSmall_splitting_iff (S : ShortComplex (AsSmall.{l} C)) :
    Nonempty S.Splitting ↔
      Nonempty (S.map (AsSmall.down : AsSmall.{l} C ⥤ C)).Splitting := by
  constructor
  · rintro ⟨s⟩
    exact ⟨s.map (AsSmall.down : AsSmall.{l} C ⥤ C)⟩
  · rintro ⟨s⟩
    exact ⟨asSmallSplittingOfDown.{u, v, l} C S s⟩

/-- The complete structural splitting hypothesis is preserved in both
directions, with every original admissible row retained. -/
theorem asSmall_all_admissible_split_iff :
    (∀ S : ShortComplex (AsSmall.{l} C), IsAdmissibleExact S → Nonempty S.Splitting) ↔
      (∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting) := by
  constructor
  · intro h S hS
    obtain ⟨s⟩ := h (S.map (AsSmall.up : C ⥤ AsSmall.{l} C))
      ((asSmallUp_isAdmissibleExact_iff.{u, v, l} C S).mpr hS)
    have t := s.map (AsSmall.down : AsSmall.{l} C ⥤ C)
    exact ⟨t.ofIso (eqToIso (asSmallUp_down_mapShortComplex.{u, v, l} C S))⟩
  · intro h S hS
    exact (asSmall_splitting_iff.{u, v, l} C S).mpr
      (h _ ((asSmall_isAdmissibleExact_iff.{u, v, l} C S).mp hS))

end Exact

end CategoryTheory.ExactCategory
