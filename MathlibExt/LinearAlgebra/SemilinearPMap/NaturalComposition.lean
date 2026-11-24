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

public import MathlibExt.LinearAlgebra.SemilinearPMap.Basic

/-!
# Actual natural-domain partial composition over semirings

The domain of A after B is exactly the original B-domain vectors whose
actual B-value lies in the original A-domain. All values are A(Bx) on that
subtype. Semiring coefficients and additive commutative monoids suffice.
No full-range inclusion, topology, norm, subtraction or model input is used.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace SemilinearPMap
universe uR uS uT uE uF uG
variable {R : Type uR} {S : Type uS} {T : Type uT}
variable [Semiring R] [Semiring S] [Semiring T]
variable {sigma : R →+* S} {tau : S →+* T}
variable {E : Type uE} [AddCommMonoid E] [Module R E]
variable {F : Type uF} [AddCommMonoid F] [Module S F]
variable {G : Type uG} [AddCommMonoid G] [Module T G]

/-- Compose the actual partial semilinear maps on their exact natural domain. -/
def naturalComp (A : SemilinearPMap tau F G) (B : SemilinearPMap sigma E F) :
    SemilinearPMap (tau.comp sigma) E G := by
  let D : Submodule R E := (Submodule.comap B.toFun A.domain).map B.domain.subtype
  have hDB : D ≤ B.domain := by
    intro x hx
    rcases hx with ⟨y, _hy, hxy⟩
    exact hxy ▸ y.property
  let b : D →ₛₗ[sigma] F := B.toFun.comp (Submodule.inclusion hDB)
  have hb : ∀ x : D, b x ∈ A.domain := by
    intro x
    obtain ⟨y, hy, hxy⟩ := x.property
    have he : (Submodule.inclusion hDB x : B.domain) = y := Subtype.ext hxy.symm
    change B.toFun (Submodule.inclusion hDB x) ∈ A.domain
    rw [he]
    exact hy
  letI : RingHomCompTriple sigma tau (tau.comp sigma) := ⟨rfl⟩
  exact ⟨D, A.toFun.comp (b.codRestrict A.domain hb)⟩

/-- The exact natural domain is the original inverse image inside B's domain, mapped back into E. -/
theorem domain_naturalComp (A : SemilinearPMap tau F G) (B : SemilinearPMap sigma E F) :
    (A.naturalComp B).domain = (Submodule.comap B.toFun A.domain).map B.domain.subtype := rfl

/-- Both original domain memberships are retained by the natural product. -/
theorem mem_domain_naturalComp (A : SemilinearPMap tau F G) (B : SemilinearPMap sigma E F) (x : E) :
    x ∈ (A.naturalComp B).domain ↔ ∃ hx : x ∈ B.domain, B ⟨x, hx⟩ ∈ A.domain := by
  rw [domain_naturalComp]
  constructor
  · rintro ⟨y, hy, hxy⟩
    subst x
    exact ⟨y.property, hy⟩
  · rintro ⟨hx, hBx⟩
    exact ⟨⟨x, hx⟩, hBx, rfl⟩

/-- On the actual natural domain, composition has exactly the original value A(Bx). -/
theorem naturalComp_apply (A : SemilinearPMap tau F G) (B : SemilinearPMap sigma E F)
    (x : E) (hx : x ∈ (A.naturalComp B).domain)
    (hxB : x ∈ B.domain) (hBx : B ⟨x, hxB⟩ ∈ A.domain) :
    A.naturalComp B ⟨x, hx⟩ = A ⟨B ⟨x, hxB⟩, hBx⟩ := by
  change A.toFun _ = A.toFun _
  apply congrArg A.toFun
  apply Subtype.ext
  apply congrArg B.toFun
  exact Subtype.ext rfl

end SemilinearPMap
