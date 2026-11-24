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

public import MathlibExt.LinearAlgebra.SemilinearPMap.NaturalComposition

/-!
# Stock ring partial maps as the exact semiring natural-composition specialization

Mathlib56a005 requires Ring/AddCommGroup in LinearPMap itself. The shared
SemilinearPMap carrier owns natural composition over genuine semirings and
additive commutative monoids. These original ring-facing public APIs retain
their full TYPEs, domains, value orientation and callers as exact adapters.
No scalar pin or ring/group dictionary is manufactured.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LinearPMap
universe uR uE uF uG
variable {R : Type uR} [Ring R]
variable {E : Type uE} [AddCommGroup E] [Module R E]
variable {F : Type uF} [AddCommGroup F] [Module R F]
variable {G : Type uG} [AddCommGroup G] [Module R G]

/-- Original stock partial composition, now the canonical generic semiring construction specialized to rings. -/
noncomputable def naturalComp (A : F →ₗ.[R] G) (B : E →ₗ.[R] F) : E →ₗ.[R] G :=
  ((SemilinearPMap.ofLinearPMap A).naturalComp (SemilinearPMap.ofLinearPMap B)).toLinearPMap

/-- The original ring-facing domain remains exactly the inverse image inside the original B-domain. -/
theorem domain_naturalComp (A : F →ₗ.[R] G) (B : E →ₗ.[R] F) :
    (A.naturalComp B).domain = (Submodule.comap B.toFun A.domain).map B.domain.subtype := rfl

/-- The original domain memberships are unchanged by specialization to the generic carrier. -/
theorem mem_domain_naturalComp (A : F →ₗ.[R] G) (B : E →ₗ.[R] F) (x : E) :
    x ∈ (A.naturalComp B).domain ↔ ∃ hx : x ∈ B.domain, B ⟨x, hx⟩ ∈ A.domain :=
  SemilinearPMap.mem_domain_naturalComp (SemilinearPMap.ofLinearPMap A) (SemilinearPMap.ofLinearPMap B) x

/-- On its original natural domain the stock ring-facing product is still exactly A(Bx). -/
theorem naturalComp_apply (A : F →ₗ.[R] G) (B : E →ₗ.[R] F)
    (x : E) (hx : x ∈ (A.naturalComp B).domain)
    (hxB : x ∈ B.domain) (hBx : B ⟨x, hxB⟩ ∈ A.domain) :
    A.naturalComp B ⟨x, hx⟩ = A ⟨B ⟨x, hxB⟩, hBx⟩ :=
  SemilinearPMap.naturalComp_apply (SemilinearPMap.ofLinearPMap A) (SemilinearPMap.ofLinearPMap B)
    x hx hxB hBx

/-- Ring specialization preserves the exact original generic composition as well as its full domain. -/
theorem ofLinearPMap_naturalComp (A : F →ₗ.[R] G) (B : E →ₗ.[R] F) :
    SemilinearPMap.ofLinearPMap (A.naturalComp B) =
      (SemilinearPMap.ofLinearPMap A).naturalComp (SemilinearPMap.ofLinearPMap B) :=
  SemilinearPMap.ofLinearPMap_toLinearPMap _

end LinearPMap
