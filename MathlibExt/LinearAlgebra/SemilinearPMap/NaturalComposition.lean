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
# Natural-domain composition of partial semilinear maps

Let R,S,T be semirings with σ:R→S and τ:S→T, E,F,G semimodules over them, B:D_B⊆E→F a partial
σ-semilinear map and A:D_A⊆F→G a partial τ-semilinear map. Their natural composite has domain
D={x∈D_B:B(x)∈D_A} and value x↦A(B(x)), semilinear for τ∘σ. No full-domain range inclusion is
imposed; membership is tested within D_B.
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

/-- **Partial semilinear map on the natural composition domain.**

Let R,S,T be semirings with σ:R→S and τ:S→T, E,F,G semimodules over them, B:D_B⊆E→F a partial
σ-semilinear map and A:D_A⊆F→G a partial τ-semilinear map. Their natural composite has domain
D={x∈D_B:B(x)∈D_A} and value x↦A(B(x)), semilinear for τ∘σ. The map naturalComp A B is the
partial τ∘σ-semilinear composite.
-/
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

/-- **Submodule formula for natural semilinear composition.**

Let R,S,T be semirings with σ:R→S and τ:S→T, E,F,G semimodules over them, B:D_B⊆E→F a partial
σ-semilinear map and A:D_A⊆F→G a partial τ-semilinear map. Their natural composite has domain
D={x∈D_B:B(x)∈D_A} and value x↦A(B(x)), semilinear for τ∘σ. Its domain is B⁻¹(D_A) as a
submodule of D_B, included into E by the domain inclusion.
-/
theorem domain_naturalComp (A : SemilinearPMap tau F G) (B : SemilinearPMap sigma E F) :
    (A.naturalComp B).domain = (Submodule.comap B.toFun A.domain).map B.domain.subtype := rfl

/-- **Membership in a natural semilinear composition domain.**

Let R,S,T be semirings with σ:R→S and τ:S→T, E,F,G semimodules over them, B:D_B⊆E→F a partial
σ-semilinear map and A:D_A⊆F→G a partial τ-semilinear map. Their natural composite has domain
D={x∈D_B:B(x)∈D_A} and value x↦A(B(x)), semilinear for τ∘σ. For x∈E, x belongs to the
composite domain exactly when x∈D_B and B(x)∈D_A.
-/
theorem mem_domain_naturalComp (A : SemilinearPMap tau F G) (B : SemilinearPMap sigma E F) (x : E) :
    x ∈ (A.naturalComp B).domain ↔ ∃ hx : x ∈ B.domain, B ⟨x, hx⟩ ∈ A.domain := by
  rw [domain_naturalComp]
  constructor
  · rintro ⟨y, hy, hxy⟩
    subst x
    exact ⟨y.property, hy⟩
  · rintro ⟨hx, hBx⟩
    exact ⟨⟨x, hx⟩, hBx, rfl⟩

/-- **Value of natural semilinear composition.**

Let R,S,T be semirings with σ:R→S and τ:S→T, E,F,G semimodules over them, B:D_B⊆E→F a partial
σ-semilinear map and A:D_A⊆F→G a partial τ-semilinear map. Their natural composite has domain
D={x∈D_B:B(x)∈D_A} and value x↦A(B(x)), semilinear for τ∘σ. For x∈D, naturalComp A B
x=A(B(x)).
-/
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
