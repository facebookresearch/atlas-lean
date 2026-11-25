/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.NonUnitalSubalgebra.TwoSided
public import MathlibExt.Algebra.NonUnitalSubalgebra.Quotient
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Actual ideals and quotients of nonunital ground algebras

The datum is the native nonunital subalgebra with the established `IsTwoSided`
absorption class. Its ideal algebra is the native subtype and its quotient is
the original native module quotient. Quotient multiplication and scalar
compatibility come from the neutral quotient provider's scoped instances.
The original maps and ground-linear splitting are retained.
-/

@[expose] public section

noncomputable section

universe u v w

open scoped NonUnitalSubalgebra.Quotient

namespace NonUnitalSubalgebra

variable {k : Type u} [CommRing k] {A : Type v} [NonUnitalRing A] [Module k A]
  (I : NonUnitalSubalgebra k A) [I.IsTwoSided]

/-- The actual original ideal algebra. -/
abbrev Algebra : Type v := I

/-- The original ideal inclusion is the native subtype homomorphism. -/
def subtypeHom : I.Algebra →ₙₐ[k] A := NonUnitalSubalgebraClass.subtype I

omit [I.IsTwoSided] in
@[simp]
theorem subtypeHom_apply (x : I.Algebra) : I.subtypeHom x = x.val := rfl

/-- The actual original quotient linear map. -/
abbrev quotientLinearMap : A →ₗ[k] I.Quotient := Quotient.mkL I

/-- Original multiplication survives the native quotient map. -/
theorem quotientLinearMap_mul (a b : A) :
    I.quotientLinearMap (a * b) = I.quotientLinearMap a * I.quotientLinearMap b := rfl

/-- The actual original quotient map is a nonunital ground-algebra homomorphism. -/
abbrev quotientMap : A →ₙₐ[k] I.Quotient := Quotient.mk I

@[simp]
theorem quotientMap_toLinearMap : (I.quotientMap : A →ₗ[k] I.Quotient) = I.quotientLinearMap := rfl

/-- The actual quotient kills exactly the original ideal. -/
theorem quotientMap_eq_zero (a : A) : I.quotientMap a = 0 ↔ a ∈ I.toSubmodule :=
  Quotient.mk_eq_zero I a

/-- The actual original ideal inclusion and quotient have zero composite. -/
theorem quotientMap_inclusion (x : I.Algebra) : I.quotientMap (I.subtypeHom x) = 0 :=
  (I.quotientMap_eq_zero x.val).mpr x.property

/-- The entire original nonunital ideal/quotient composite is zero. -/
theorem quotientMap_comp_inclusion : I.quotientMap.comp I.subtypeHom = 0 := by
  ext x
  exact I.quotientMap_inclusion x

/-- The actual quotient is surjective in the original carrier world. -/
theorem quotientMap_surjective : Function.Surjective I.quotientMap := Quotient.mk_surjective I

/-- The source k-splitting is an actual linear section of the actual quotient. -/
structure KSplit where
  /-- The original ground-linear section; no multiplicativity is assumed. -/
  sectionMap : I.Quotient →ₗ[k] A
  /-- The actual original quotient is retracted by this section. -/
  section_spec : I.quotientLinearMap.comp sectionMap = LinearMap.id

namespace KSplit

variable {I} (s : I.KSplit)

omit [I.IsTwoSided] in
theorem quotient_section (x : I.Quotient) : I.quotientLinearMap (s.sectionMap x) = x :=
  DFunLike.congr_fun s.section_spec x

end KSplit

section Maps

variable {I} {B : Type w} [NonUnitalRing B] [Module k B]
  (J : NonUnitalSubalgebra k B) [J.IsTwoSided] (f : A →ₙₐ[k] B)
  (hf : ∀ a ∈ I.toSubmodule, f a ∈ J.toSubmodule)

/-- The original nonunital map descends through the actual ideal quotient maps. -/
def mapQuotient : I.Quotient →ₙₐ[k] J.Quotient := by
  let F : I.Quotient →ₗ[k] J.Quotient := I.toSubmodule.liftQ
    (J.quotientLinearMap.comp (f : A →ₗ[k] B)) (fun a ha => by
      change J.quotientMap (f a) = 0
      exact (J.quotientMap_eq_zero (f a)).mpr (hf a ha))
  exact
    { toFun := F
      map_zero' := map_zero _
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => map_smul _ r x
      map_mul' := fun x y => by
        refine _root_.Quotient.inductionOn₂ x y ?_
        intro a b
        change J.quotientLinearMap (f (a * b)) =
          J.quotientLinearMap (f a) * J.quotientLinearMap (f b)
        rw [map_mul f, J.quotientLinearMap_mul] }

/-- Every actual descended value is the original nonunital map on the original representative. -/
theorem mapQuotient_quotientMap (a : A) :
    mapQuotient J f hf (I.quotientMap a) = J.quotientMap (f a) := rfl

/-- The original ideal map preserves the original element value in its independent target carrier. -/
def mapIdeal : I.Algebra →ₙₐ[k] J.Algebra where
  toFun x := ⟨f x.val, hf x.val x.property⟩
  map_zero' := Subtype.ext (map_zero f)
  map_add' x y := Subtype.ext (map_add f x.val y.val)
  map_mul' x y := Subtype.ext (map_mul f x.val y.val)
  map_smul' r x := Subtype.ext (map_smul f r x.val)

omit [I.IsTwoSided] [J.IsTwoSided] in
theorem inclusion_mapIdeal (x : I.Algebra) :
    J.subtypeHom (mapIdeal J f hf x) = f (I.subtypeHom x) := rfl

end Maps

end NonUnitalSubalgebra
