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
# Natural-domain composition of partial linear maps

Let R be a ring, E,F,G left R-modules and B:D_B⊆E→F, A:D_A⊆F→G partial linear maps. The
natural composite A∘B has domain D={x∈D_B:B(x)∈D_A} and value A(B(x)). These maps can also be
regarded as partial semilinear maps for id_R, with the same domains and values.
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

/-- **Composite on its natural partial domain.**

Let R be a ring, E,F,G left R-modules and B:D_B⊆E→F, A:D_A⊆F→G partial linear maps. The
natural composite A∘B has domain D={x∈D_B:B(x)∈D_A} and value A(B(x)). The partial linear map
naturalComp A B is this composite.
-/
noncomputable def naturalComp (A : F →ₗ.[R] G) (B : E →ₗ.[R] F) : E →ₗ.[R] G :=
  ((SemilinearPMap.ofLinearPMap A).naturalComp (SemilinearPMap.ofLinearPMap B)).toLinearPMap

/-- **Submodule formula for a natural composition domain.**

Let R be a ring, E,F,G left R-modules and B:D_B⊆E→F, A:D_A⊆F→G partial linear maps. The
natural composite A∘B has domain D={x∈D_B:B(x)∈D_A} and value A(B(x)). The domain is the
inverse image B⁻¹(D_A) inside D_B, included back into E.
-/
theorem domain_naturalComp (A : F →ₗ.[R] G) (B : E →ₗ.[R] F) :
    (A.naturalComp B).domain = (Submodule.comap B.toFun A.domain).map B.domain.subtype := rfl

/-- **Membership in the natural composition domain.**

Let R be a ring, E,F,G left R-modules and B:D_B⊆E→F, A:D_A⊆F→G partial linear maps. The
natural composite A∘B has domain D={x∈D_B:B(x)∈D_A} and value A(B(x)). For x∈E, x lies in the
composite domain exactly when x∈D_B and B(x)∈D_A.
-/
theorem mem_domain_naturalComp (A : F →ₗ.[R] G) (B : E →ₗ.[R] F) (x : E) :
    x ∈ (A.naturalComp B).domain ↔ ∃ hx : x ∈ B.domain, B ⟨x, hx⟩ ∈ A.domain :=
  SemilinearPMap.mem_domain_naturalComp (SemilinearPMap.ofLinearPMap A) (SemilinearPMap.ofLinearPMap B) x

/-- **Value of natural partial composition.**

Let R be a ring, E,F,G left R-modules and B:D_B⊆E→F, A:D_A⊆F→G partial linear maps. The
natural composite A∘B has domain D={x∈D_B:B(x)∈D_A} and value A(B(x)). For x in the composite
domain, naturalComp A B x=A(B(x)).
-/
theorem naturalComp_apply (A : F →ₗ.[R] G) (B : E →ₗ.[R] F)
    (x : E) (hx : x ∈ (A.naturalComp B).domain)
    (hxB : x ∈ B.domain) (hBx : B ⟨x, hxB⟩ ∈ A.domain) :
    A.naturalComp B ⟨x, hx⟩ = A ⟨B ⟨x, hxB⟩, hBx⟩ :=
  SemilinearPMap.naturalComp_apply (SemilinearPMap.ofLinearPMap A) (SemilinearPMap.ofLinearPMap B)
    x hx hxB hBx

/-- **Semilinear presentation preserves natural partial composition.**

Let R be a ring, E,F,G left R-modules and B:D_B⊆E→F, A:D_A⊆F→G partial linear maps. The
natural composite A∘B has domain D={x∈D_B:B(x)∈D_A} and value A(B(x)). Regarding A,B and their
composite as SemilinearPMap id_R preserves naturalComp and the complete domain/value data.
-/
theorem ofLinearPMap_naturalComp (A : F →ₗ.[R] G) (B : E →ₗ.[R] F) :
    SemilinearPMap.ofLinearPMap (A.naturalComp B) =
      (SemilinearPMap.ofLinearPMap A).naturalComp (SemilinearPMap.ofLinearPMap B) :=
  SemilinearPMap.ofLinearPMap_toLinearPMap _

end LinearPMap
