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
# Partial semilinear maps over semirings

Let R,S be semirings, σ:R→S a semiring homomorphism, E an R-semimodule and F an S-semimodule.
A partial σ-semilinear map f consists of a submodule D_f⊆E and a σ-semilinear value map D_f→F,
with f(x+y)=f(x)+f(y) and f(r•x)=σ(r)•f(x). Restriction replaces the domain by its
intersection with a chosen submodule, retaining the values. For rings and additive groups this
is equivalent to the LinearPMap presentation.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe uR uS uE uF

/-- **Semilinear value map on a submodule.**

Let R,S be semirings, σ:R→S a semiring homomorphism, E an R-semimodule and F an S-semimodule.
A partial σ-semilinear map f consists of a submodule D_f⊆E and a σ-semilinear value map D_f→F,
with f(x+y)=f(x)+f(y) and f(r•x)=σ(r)•f(x). This domain and value map are the structure
SemilinearPMap σ E F.
-/
structure SemilinearPMap {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]
    (sigma : R →+* S) (E : Type uE) [AddCommMonoid E] [Module R E]
    (F : Type uF) [AddCommMonoid F] [Module S F] where
  /-- **Domain submodule of a partial semilinear map.**

Let R,S be semirings, σ:R→S a semiring homomorphism, E an R-semimodule and F an S-semimodule.
A partial σ-semilinear map f consists of a submodule D_f⊆E and a σ-semilinear value map D_f→F,
with f(x+y)=f(x)+f(y) and f(r•x)=σ(r)•f(x). The field domain is D_f⊆E, the R-submodule on
which f is defined.
-/
  domain : Submodule R E
  /-- **Semilinear map on the partial domain.**

Let R,S be semirings, σ:R→S a semiring homomorphism, E an R-semimodule and F an S-semimodule.
A partial σ-semilinear map f consists of a submodule D_f⊆E and a σ-semilinear value map D_f→F,
with f(x+y)=f(x)+f(y) and f(r•x)=σ(r)•f(x). The field toFun:D_f→ₛₗ[σ]F gives the values on the
domain.
-/
  toFun : domain →ₛₗ[sigma] F

namespace SemilinearPMap
variable {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]
variable {sigma : R →+* S} {E : Type uE} [AddCommMonoid E] [Module R E]
variable {F : Type uF} [AddCommMonoid F] [Module S F]

/-- **Function on the partial semilinear domain.**

Let R,S be semirings, σ:R→S a semiring homomorphism, E an R-semimodule and F an S-semimodule.
A partial σ-semilinear map f consists of a submodule D_f⊆E and a σ-semilinear value map D_f→F,
with f(x+y)=f(x)+f(y) and f(r•x)=σ(r)•f(x). The map toFun′ f:D_f→F is the underlying function
x↦f(x).
-/
@[coe]
def toFun' (f : SemilinearPMap sigma E F) : f.domain → F := f.toFun

/-- **Evaluation on a partial semilinear domain.**

Let R,S be semirings, σ:R→S a semiring homomorphism, E an R-semimodule and F an S-semimodule.
A partial σ-semilinear map f consists of a submodule D_f⊆E and a σ-semilinear value map D_f→F,
with f(x+y)=f(x)+f(y) and f(r•x)=σ(r)•f(x). A value f(x) is defined for x∈D_f, by its domain
value map.
-/
instance : CoeFun (SemilinearPMap sigma E F) (fun f => f.domain → F) :=
  ⟨toFun'⟩

/-- **Semilinear and function views of a partial map agree.**

Let R,S be semirings, σ:R→S a semiring homomorphism, E an R-semimodule and F an S-semimodule.
A partial σ-semilinear map f consists of a submodule D_f⊆E and a σ-semilinear value map D_f→F,
with f(x+y)=f(x)+f(y) and f(r•x)=σ(r)•f(x). The function obtained from f.toFun:D_f→F equals
the evaluation function of f.
-/
theorem apply_toFun (f : SemilinearPMap sigma E F) :
    (f.toFun : f.domain → F) = f := rfl

/-- **Domain and values determine a partial semilinear map.**

Let R,S be semirings, σ:R→S a semiring homomorphism, E an R-semimodule and F an S-semimodule.
A partial σ-semilinear map f consists of a submodule D_f⊆E and a σ-semilinear value map D_f→F,
with f(x+y)=f(x)+f(y) and f(r•x)=σ(r)•f(x). If f,g have equal domains and agree whenever
domain vectors represent the same x∈E, then f=g.
-/
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

/-- **Equality criterion for partial semilinear maps.**

Let R,S be semirings, σ:R→S a semiring homomorphism, E an R-semimodule and F an S-semimodule.
A partial σ-semilinear map f consists of a submodule D_f⊆E and a σ-semilinear value map D_f→F,
with f(x+y)=f(x)+f(y) and f(r•x)=σ(r)•f(x). The equality f=g holds exactly when D_f=D_g and
f(x)=g(y) whenever x∈D_f,y∈D_g have the same underlying vector in E.
-/
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

/-- **Restriction of a partial semilinear domain.**

Let R,S be semirings, σ:R→S a semiring homomorphism, E an R-semimodule and F an S-semimodule.
A partial σ-semilinear map f consists of a submodule D_f⊆E and a σ-semilinear value map D_f→F,
with f(x+y)=f(x)+f(y) and f(r•x)=σ(r)•f(x). For a submodule D⊆E, domRestrict f D has domain
D∩D_f and retains f on that intersection.
-/
def domRestrict (f : SemilinearPMap sigma E F) (D : Submodule R E) :
    SemilinearPMap sigma E F where
  domain := D ⊓ f.domain
  toFun := f.toFun.comp (Submodule.inclusion inf_le_right)

/-- **Domain of a restricted partial map.**

Let R,S be semirings, σ:R→S a semiring homomorphism, E an R-semimodule and F an S-semimodule.
A partial σ-semilinear map f consists of a submodule D_f⊆E and a σ-semilinear value map D_f→F,
with f(x+y)=f(x)+f(y) and f(r•x)=σ(r)•f(x). For D⊆E, (domRestrict f D).domain=D∩D_f.
-/
theorem domRestrict_domain (f : SemilinearPMap sigma E F) (D : Submodule R E) :
    (f.domRestrict D).domain = D ⊓ f.domain := rfl

/-- **Value preserved by partial-domain restriction.**

Let R,S be semirings, σ:R→S a semiring homomorphism, E an R-semimodule and F an S-semimodule.
A partial σ-semilinear map f consists of a submodule D_f⊆E and a σ-semilinear value map D_f→F,
with f(x+y)=f(x)+f(y) and f(r•x)=σ(r)•f(x). If x belongs to D∩D_f, domRestrict f D x=f(x),
with domain inclusions understood.
-/
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

/-- **Partial ring map in the semilinear presentation.**

Let R,S be semirings, σ:R→S a semiring homomorphism, E an R-semimodule and F an S-semimodule.
A partial σ-semilinear map f consists of a submodule D_f⊆E and a σ-semilinear value map D_f→F,
with f(x+y)=f(x)+f(y) and f(r•x)=σ(r)•f(x). Assume additionally R,S are rings and E,F additive
groups. The same domain and σ-semilinear value map give the ring partial-map presentation
LinearPMap. The map ofLinearPMap takes a ring partial map to the same domain and value map as
a SemilinearPMap.
-/
def ofLinearPMap (f : E →ₛₗ.[sigma] F) : SemilinearPMap sigma E F :=
  ⟨f.domain, f.toFun⟩

/-- **Semilinear partial map in the ring presentation.**

Let R,S be semirings, σ:R→S a semiring homomorphism, E an R-semimodule and F an S-semimodule.
A partial σ-semilinear map f consists of a submodule D_f⊆E and a σ-semilinear value map D_f→F,
with f(x+y)=f(x)+f(y) and f(r•x)=σ(r)•f(x). Assume additionally R,S are rings and E,F additive
groups. The same domain and σ-semilinear value map give the ring partial-map presentation
LinearPMap. The map toLinearPMap takes f to the ring partial map with domain D_f and values
f(x).
-/
def toLinearPMap (f : SemilinearPMap sigma E F) : E →ₛₗ.[sigma] F :=
  ⟨f.domain, f.toFun⟩

/-- **Ring partial map recovered after both presentations.**

Let R,S be semirings, σ:R→S a semiring homomorphism, E an R-semimodule and F an S-semimodule.
A partial σ-semilinear map f consists of a submodule D_f⊆E and a σ-semilinear value map D_f→F,
with f(x+y)=f(x)+f(y) and f(r•x)=σ(r)•f(x). Assume additionally R,S are rings and E,F additive
groups. The same domain and σ-semilinear value map give the ring partial-map presentation
LinearPMap. For a LinearPMap f, toLinearPMap(ofLinearPMap f)=f.
-/
theorem toLinearPMap_ofLinearPMap (f : E →ₛₗ.[sigma] F) :
    (ofLinearPMap f).toLinearPMap = f := by cases f; rfl

/-- **Semilinear partial map recovered after both presentations.**

Let R,S be semirings, σ:R→S a semiring homomorphism, E an R-semimodule and F an S-semimodule.
A partial σ-semilinear map f consists of a submodule D_f⊆E and a σ-semilinear value map D_f→F,
with f(x+y)=f(x)+f(y) and f(r•x)=σ(r)•f(x). Assume additionally R,S are rings and E,F additive
groups. The same domain and σ-semilinear value map give the ring partial-map presentation
LinearPMap. For f a SemilinearPMap, ofLinearPMap(toLinearPMap f)=f.
-/
theorem ofLinearPMap_toLinearPMap (f : SemilinearPMap sigma E F) :
    ofLinearPMap f.toLinearPMap = f := by cases f; rfl

/-- **Domain preserved on entry to the semilinear presentation.**

Let R,S be semirings, σ:R→S a semiring homomorphism, E an R-semimodule and F an S-semimodule.
A partial σ-semilinear map f consists of a submodule D_f⊆E and a σ-semilinear value map D_f→F,
with f(x+y)=f(x)+f(y) and f(r•x)=σ(r)•f(x). Assume additionally R,S are rings and E,F additive
groups. The same domain and σ-semilinear value map give the ring partial-map presentation
LinearPMap. The domain of ofLinearPMap f equals the domain of the ring partial map f.
-/
theorem domain_ofLinearPMap (f : E →ₛₗ.[sigma] F) : (ofLinearPMap f).domain = f.domain := rfl

/-- **Domain preserved on entry to the ring presentation.**

Let R,S be semirings, σ:R→S a semiring homomorphism, E an R-semimodule and F an S-semimodule.
A partial σ-semilinear map f consists of a submodule D_f⊆E and a σ-semilinear value map D_f→F,
with f(x+y)=f(x)+f(y) and f(r•x)=σ(r)•f(x). Assume additionally R,S are rings and E,F additive
groups. The same domain and σ-semilinear value map give the ring partial-map presentation
LinearPMap. The domain of toLinearPMap f equals D_f.
-/
theorem domain_toLinearPMap (f : SemilinearPMap sigma E F) : f.toLinearPMap.domain = f.domain := rfl

/-- **Values preserved on entry to the semilinear presentation.**

Let R,S be semirings, σ:R→S a semiring homomorphism, E an R-semimodule and F an S-semimodule.
A partial σ-semilinear map f consists of a submodule D_f⊆E and a σ-semilinear value map D_f→F,
with f(x+y)=f(x)+f(y) and f(r•x)=σ(r)•f(x). Assume additionally R,S are rings and E,F additive
groups. The same domain and σ-semilinear value map give the ring partial-map presentation
LinearPMap. For x in the domain of a ring partial map f, ofLinearPMap f x=f(x).
-/
theorem ofLinearPMap_apply (f : E →ₛₗ.[sigma] F) (x : f.domain) : ofLinearPMap f x = f x := rfl

/-- **Values preserved on entry to the ring presentation.**

Let R,S be semirings, σ:R→S a semiring homomorphism, E an R-semimodule and F an S-semimodule.
A partial σ-semilinear map f consists of a submodule D_f⊆E and a σ-semilinear value map D_f→F,
with f(x+y)=f(x)+f(y) and f(r•x)=σ(r)•f(x). Assume additionally R,S are rings and E,F additive
groups. The same domain and σ-semilinear value map give the ring partial-map presentation
LinearPMap. For x∈D_f, toLinearPMap f x=f(x).
-/
theorem toLinearPMap_apply (f : SemilinearPMap sigma E F) (x : f.domain) : f.toLinearPMap x = f x := rfl

end RingCompatibility
end SemilinearPMap
