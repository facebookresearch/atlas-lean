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

public import Mathlib.LinearAlgebra.LinearPMap

/-!
# Partial semilinear maps over genuine semirings and additive monoids

Pinned Mathlib LinearPMap requires rings and additive groups at its carrier
boundary. This minimal carrier keeps the same mathematical domain/value
presentation for semirings and additive commutative monoids. It introduces
only what is needed for exact natural-domain composition and stock
LinearPMap compatibility; there is no invented ring/group dictionary.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe uR uS uE uF

/-- A semilinear map on an actual submodule, with no subtraction or total-domain convention. -/
structure SemilinearPMap {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]
    (sigma : R →+* S) (E : Type uE) [AddCommMonoid E] [Module R E]
    (F : Type uF) [AddCommMonoid F] [Module S F] where
  /-- The actual source submodule on which the partial map is defined. -/
  domain : Submodule R E
  /-- The original semilinear value map on that exact domain subtype. -/
  toFun : domain →ₛₗ[sigma] F

namespace SemilinearPMap
variable {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]
variable {sigma : R →+* S} {E : Type uE} [AddCommMonoid E] [Module R E]
variable {F : Type uF} [AddCommMonoid F] [Module S F]

/-- The underlying function on the partial semilinear map's actual domain. -/
@[coe]
def toFun' (f : SemilinearPMap sigma E F) : f.domain → F := f.toFun

/-- Evaluating a partial semilinear map requires a vector of its actual domain subtype. -/
instance : CoeFun (SemilinearPMap sigma E F) (fun f => f.domain → F) :=
  ⟨toFun'⟩

/-- The actual semilinear value is the underlying domain-map value. -/
theorem apply_toFun (f : SemilinearPMap sigma E F) :
    (f.toFun : f.domain → F) = f := rfl

/-- Domain and actual semilinear map determine a partial map completely. -/
@[ext (iff := false)]
theorem ext {f g : SemilinearPMap sigma E F} (hdom : f.domain = g.domain)
    (hvalue : ∀ x : f.domain, ∀ y : g.domain, (x : E) = y → f x = g y) : f = g := by
  cases f with
  | mk D f =>
    cases g with
    | mk C g =>
      cases hdom
      have hfg : f = g := by
        apply LinearMap.ext
        intro x
        exact hvalue x x rfl
      cases hfg
      rfl

/-- Equality retains exactly domain equality and equality of the actual values after subtype transport. -/
theorem ext_iff {f g : SemilinearPMap sigma E F} :
    f = g ↔ f.domain = g.domain ∧
      (∀ x : f.domain, ∀ y : g.domain, (x : E) = y → f x = g y) := by
  constructor
  · intro h
    cases h
    refine ⟨rfl, ?_⟩
    intro x y hxy
    exact congrArg f.toFun (Subtype.ext hxy)
  · rintro ⟨hdom, hvalue⟩
    exact ext hdom hvalue

/-- Restrict only the actual domain; no vector outside the original domain is assigned a value. -/
def domRestrict (f : SemilinearPMap sigma E F) (D : Submodule R E) :
    SemilinearPMap sigma E F where
  domain := D ⊓ f.domain
  toFun := f.toFun.comp (Submodule.inclusion inf_le_right)

/-- The restricted domain retains exactly the intersection with the original domain. -/
theorem domRestrict_domain (f : SemilinearPMap sigma E F) (D : Submodule R E) :
    (f.domRestrict D).domain = D ⊓ f.domain := rfl

/-- Restriction preserves the actual original value on its original domain. -/
theorem domRestrict_apply (f : SemilinearPMap sigma E F) (D : Submodule R E)
    (x : (f.domRestrict D).domain) (y : f.domain) (hxy : (x : E) = y) :
    f.domRestrict D x = f y := by
  apply congrArg f.toFun
  exact Subtype.ext hxy

end SemilinearPMap

namespace SemilinearPMap
section RingCompatibility
variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
variable {sigma : R →+* S} {E : Type uE} [AddCommGroup E] [Module R E]
variable {F : Type uF} [AddCommGroup F] [Module S F]

/-- Stock ring/group partial maps enter the semiring carrier by their exact domain and actual value map. -/
def ofLinearPMap (f : E →ₛₗ.[sigma] F) : SemilinearPMap sigma E F :=
  ⟨f.domain, f.toFun⟩

/-- On genuine rings and additive groups the semiring carrier has the exact stock partial-map presentation. -/
def toLinearPMap (f : SemilinearPMap sigma E F) : E →ₛₗ.[sigma] F :=
  ⟨f.domain, f.toFun⟩

/-- Entering and leaving the generic carrier retains the entire original stock partial map. -/
theorem toLinearPMap_ofLinearPMap (f : E →ₛₗ.[sigma] F) :
    (ofLinearPMap f).toLinearPMap = f := by cases f; rfl

/-- Leaving and entering the generic carrier retains the entire original generic partial map. -/
theorem ofLinearPMap_toLinearPMap (f : SemilinearPMap sigma E F) :
    ofLinearPMap f.toLinearPMap = f := by cases f; rfl

/-- The stock adapter preserves the exact original domain. -/
theorem domain_ofLinearPMap (f : E →ₛₗ.[sigma] F) : (ofLinearPMap f).domain = f.domain := rfl

/-- The generic adapter preserves the exact original domain. -/
theorem domain_toLinearPMap (f : SemilinearPMap sigma E F) : f.toLinearPMap.domain = f.domain := rfl

/-- The stock adapter preserves the actual original domain-subtype value. -/
theorem ofLinearPMap_apply (f : E →ₛₗ.[sigma] F) (x : f.domain) : ofLinearPMap f x = f x := rfl

/-- The generic adapter preserves the actual original domain-subtype value. -/
theorem toLinearPMap_apply (f : SemilinearPMap sigma E F) (x : f.domain) : f.toLinearPMap x = f x := rfl

end RingCompatibility
end SemilinearPMap
