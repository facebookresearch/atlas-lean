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
# Nonunital ideals and quotient homomorphisms

Let `k` be a commutative ring, let `A` be a nonunital ring with a `k`-module structure, and
let `I` be a two-sided nonunital `k`-subalgebra. The inclusion `I → A` and quotient map `q : A
→ A/I` are nonunital algebra homomorphisms. The kernel of `q` is `I`, and `q` is surjective.

A `KSplit` is a `k`-linear section `s : A/I → A` with `q ∘ s = id`. The section is required to
preserve addition and scalars; its multiplication is unrestricted. A homomorphism carrying `I`
into another two-sided subalgebra induces maps on ideals and quotients.
-/

@[expose] public section

noncomputable section

universe u v w

open scoped NonUnitalSubalgebra.Quotient

namespace NonUnitalSubalgebra

variable {k : Type u} [CommRing k] {A : Type v} [NonUnitalRing A] [Module k A]
  (I : NonUnitalSubalgebra k A) [I.IsTwoSided]

/-- The nonunital algebra of a two-sided subalgebra.

For a two-sided nonunital `k`-subalgebra `I ⊆ A`, this is its subtype, equipped with the
induced addition, multiplication, and scalar action. -/
abbrev Algebra : Type v := I

/-- The nonunital ideal inclusion.

For `I ⊆ A`, the inclusion `I →ₙₐ[k] A` sends an element of the subalgebra to its value in
`A`. -/
def subtypeHom : I.Algebra →ₙₐ[k] A := NonUnitalSubalgebraClass.subtype I

omit [I.IsTwoSided] in
/-- The value of the nonunital ideal inclusion.

For `x : I`, the inclusion sends `x` to `x.val`. This formula does not require two-sidedness. -/
@[simp]
theorem subtypeHom_apply (x : I.Algebra) : I.subtypeHom x = x.val := rfl

/-- The linear quotient map of a nonunital ideal.

For a two-sided nonunital `k`-subalgebra `I ⊆ A`, this is the `k`-linear map `q : A → A/I`
sending `a` to its residue class. -/
abbrev quotientLinearMap : A →ₗ[k] I.Quotient := Quotient.mkL I

/-- Multiplication of quotient residue classes.

For `a, b ∈ A`, the linear quotient map satisfies `q(a * b) = q(a) * q(b)`. -/
theorem quotientLinearMap_mul (a b : A) :
    I.quotientLinearMap (a * b) = I.quotientLinearMap a * I.quotientLinearMap b := rfl

/-- The nonunital algebra quotient map.

For a two-sided nonunital `k`-subalgebra `I ⊆ A`, the map `q : A →ₙₐ[k] A/I` preserves
addition, multiplication, and the `k`-action. -/
abbrev quotientMap : A →ₙₐ[k] I.Quotient := Quotient.mk I

/-- The underlying linear map of the nonunital quotient.

The nonunital algebra quotient homomorphism and the linear quotient map send every `a ∈ A` to
the same residue class. -/
@[simp]
theorem quotientMap_toLinearMap : (I.quotientMap : A →ₗ[k] I.Quotient) = I.quotientLinearMap := rfl

/-- The kernel criterion for a nonunital quotient.

For `a ∈ A`, its image in `A/I` is zero if and only if `a` belongs to the underlying submodule
of `I`. -/
theorem quotientMap_eq_zero (a : A) : I.quotientMap a = 0 ↔ a ∈ I.toSubmodule :=
  Quotient.mk_eq_zero I a

/-- The quotient vanishes on an ideal element.

For `x : I`, the residue class of its inclusion in `A` is zero. -/
theorem quotientMap_inclusion (x : I.Algebra) : I.quotientMap (I.subtypeHom x) = 0 :=
  (I.quotientMap_eq_zero x.val).mpr x.property

/-- The zero composite of ideal inclusion and quotient.

The composite `I →ₙₐ[k] A →ₙₐ[k] A/I` is the zero nonunital algebra homomorphism. -/
theorem quotientMap_comp_inclusion : I.quotientMap.comp I.subtypeHom = 0 := by
  ext x
  exact I.quotientMap_inclusion x

/-- Surjectivity of the nonunital quotient homomorphism.

Every class in `A/I` is represented by an element of `A`. -/
theorem quotientMap_surjective : Function.Surjective I.quotientMap := Quotient.mk_surjective I

/-- A linear splitting of a nonunital ideal quotient.

For `q : A → A/I`, this consists of a `k`-linear section `s : A/I → A` satisfying `q ∘ s =
id`. The datum imposes no multiplicative equation on `s`. -/
structure KSplit where
  /-- The section in a linear ideal splitting.

This `k`-linear map sends each residue class in `A/I` to a chosen representative in `A`. -/
  sectionMap : I.Quotient →ₗ[k] A
  /-- The retraction equation for a linear ideal splitting.

The chosen section `s` satisfies `q ∘ s = id` as a `k`-linear map on `A/I`. -/
  section_spec : I.quotientLinearMap.comp sectionMap = LinearMap.id

namespace KSplit

variable {I} (s : I.KSplit)

omit [I.IsTwoSided] in
/-- The quotient of a section value.

For a linear splitting `s` and a class `x ∈ A/I`, one has `q(s(x)) = x`. -/
theorem quotient_section (x : I.Quotient) : I.quotientLinearMap (s.sectionMap x) = x :=
  DFunLike.congr_fun s.section_spec x

end KSplit

section Maps

variable {I} {B : Type w} [NonUnitalRing B] [Module k B]
  (J : NonUnitalSubalgebra k B) [J.IsTwoSided] (f : A →ₙₐ[k] B)
  (hf : ∀ a ∈ I.toSubmodule, f a ∈ J.toSubmodule)

/-- The quotient homomorphism induced by an ideal-preserving map.

Let `f : A →ₙₐ[k] B` send `I` into a two-sided subalgebra `J`. The induced map `A/I →ₙₐ[k]
B/J` sends the class of `a` to the class of `f(a)`. -/
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

/-- The residue-class formula for an induced quotient map.

If `f(I) ⊆ J`, then the induced quotient homomorphism satisfies `f̄(q_I(a)) = q_J(f(a))` for
every `a ∈ A`. -/
theorem mapQuotient_quotientMap (a : A) :
    mapQuotient J f hf (I.quotientMap a) = J.quotientMap (f a) := rfl

/-- The ideal homomorphism induced by a preserving map.

For `f : A →ₙₐ[k] B` with `f(I) ⊆ J`, the induced map `I →ₙₐ[k] J` sends `x` to the element
with value `f(x.val)`. The two carrier universes may be independent. -/
def mapIdeal : I.Algebra →ₙₐ[k] J.Algebra where
  toFun x := ⟨f x.val, hf x.val x.property⟩
  map_zero' := Subtype.ext (map_zero f)
  map_add' x y := Subtype.ext (map_add f x.val y.val)
  map_mul' x y := Subtype.ext (map_mul f x.val y.val)
  map_smul' r x := Subtype.ext (map_smul f r x.val)

omit [I.IsTwoSided] [J.IsTwoSided] in
/-- Compatibility of an induced ideal map with inclusion.

For `x ∈ I`, including its image in `J` gives `f` applied to its inclusion in `A`. The formula
requires ideal preservation and does not require two-sidedness. -/
theorem inclusion_mapIdeal (x : I.Algebra) :
    J.subtypeHom (mapIdeal J f hf x) = f (I.subtypeHom x) := rfl

end Maps

end NonUnitalSubalgebra
