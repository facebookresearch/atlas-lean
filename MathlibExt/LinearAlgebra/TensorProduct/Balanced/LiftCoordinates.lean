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

public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.RightActions
public import MathlibExt.Algebra.Module.ULiftActions

/-!
# Lifted coordinates on balanced tensor products

Let k be a commutative ring and R, S semirings. Let M be a right R-module
and N a left R-module and right S-module, both additive commutative groups
with k-module structures. The right S-action on N commutes with k and
the left R-action. The balanced quotient M ⊗_R N therefore has the induced
right S-action [m ⊗ n] s = [m ⊗ n s].

Equivariant k-linear equivalences on M and N induce a right S-linear
equivalence of the balanced quotients, retaining ground k-linearity.
For any common lift height z, lowering the two lifted carriers gives
ULift M ⊗_R ULift N ≅ M ⊗_R N. Composing with the lift of the whole
quotient gives ULift M ⊗_R ULift N ≅ ULift(M ⊗_R N).
Both comparisons have the corresponding up/down values on pure classes
and commute with equivariant coefficient maps. All ring, carrier and lift
universes are independent.
-/

@[expose] public section
noncomputable section

open MulOpposite

universe u r s a b a' b' z l

namespace TensorProduct.Balanced

variable (k : Type u) (R : Type r) (S : Type s)
  [CommRing k] [Semiring R] [Semiring S]
  (M : Type a) (N : Type b) [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N] [Module Rᵐᵒᵖ M] [Module R N] [Module Sᵐᵒᵖ N]
  [SMulCommClass Sᵐᵒᵖ k N] [SMulCommClass R Sᵐᵒᵖ N]

section Coordinates

variable {M' : Type a'} {N' : Type b'} [AddCommGroup M'] [AddCommGroup N']
  [Module k M'] [Module k N'] [Module Rᵐᵒᵖ M'] [Module R N'] [Module Sᵐᵒᵖ N']
  [SMulCommClass Sᵐᵒᵖ k N'] [SMulCommClass R Sᵐᵒᵖ N']
  (f : M ≃ₗ[k] M') (g : N ≃ₗ[k] N')
  (hf : ∀ (r : R) (m : M), f (op r • m) = op r • f m)
  (hg : ∀ (r : R) (n : N), g (r • n) = r • g n)
  (hgS : ∀ (s : Sᵐᵒᵖ) (n : N), g (s • n) = s • g n)

/-- Let k be a commutative ring and R, S semirings. Let M be a right
R-module and N a left R-module and right S-module, both additive commutative
groups with k-module structures. The right S-action on N commutes with
its k-action and left R-action.
Let f : M ≃ₗ[k] M′ preserve the right R-action and
g : N ≃ₗ[k] N′ preserve both the left R- and right S-actions, with
the same structures on M′, N′. The induced balanced quotient
equivalence is right S-linear and sends [m ⊗ n] to [f(m) ⊗ g(n)]. -/
def rightCongr :
    letI := rightModule k R S M N
    letI := rightModule k R S M' N'
    Balanced k R M N ≃ₗ[Sᵐᵒᵖ] Balanced k R M' N' := by
  letI := rightModule k R S M N
  letI := rightModule k R S M' N'
  let e := congr (k := k) (R := R) f g hf hg
  refine { e.toAddEquiv with map_smul' := ?_ }
  intro s x
  change e (rightAction k R S M N s x) = rightAction k R S M' N' s (e x)
  have h : e.toLinearMap.comp (rightAction k R S M N s) =
      (rightAction k R S M' N' s).comp e.toLinearMap :=
    map_rightAction f.toLinearMap g.toLinearMap hf hg hgS s
  exact LinearMap.congr_fun h x

/-- Let k be a commutative ring and R, S semirings. Let M be a right
R-module and N a left R-module and right S-module, both additive commutative
groups with k-module structures. The right S-action on N commutes with
its k-action and left R-action.
For equivariant k-linear equivalences f : M ≅ M′ and g : N ≅ N′,
where f preserves right R and g preserves left R and right S,
the quotient coordinate equivalence satisfies
rightCongr([m ⊗ n]) = [f(m) ⊗ g(n)]. -/
theorem rightCongr_mk (m : M) (n : N) :
    letI := rightModule k R S M N
    letI := rightModule k R S M' N'
    rightCongr k R S M N f g hf hg hgS (mk k R M N m n) =
      mk k R M' N' (f m) (g n) :=
  congr_mk f g hf hg m n

/-- Let k be a commutative ring and R, S semirings. Let M be a right
R-module and N a left R-module and right S-module, both additive commutative
groups with k-module structures. The right S-action on N commutes with
its k-action and left R-action.
For equivariant k-linear equivalences f : M ≅ M′ and g : N ≅ N′,
preserving right R and left R/right S respectively, the inverse quotient
coordinate map sends [m′ ⊗ n′] to [f⁻¹(m′) ⊗ g⁻¹(n′)]. -/
theorem rightCongr_symm_mk (m : M') (n : N') :
    letI := rightModule k R S M N
    letI := rightModule k R S M' N'
    (rightCongr k R S M N f g hf hg hgS).symm (mk k R M' N' m n) =
      mk k R M N (f.symm m) (g.symm n) := by
  let := rightModule k R S M N
  let := rightModule k R S M' N'
  apply (rightCongr k R S M N f g hf hg hgS).injective
  rw [LinearEquiv.apply_symm_apply, rightCongr_mk,
    f.apply_symm_apply, g.apply_symm_apply]

/-- Let k be a commutative ring and R, S semirings. Let M be a right
R-module and N a left R-module and right S-module, both additive commutative
groups with k-module structures. The right S-action on N commutes with
its k-action and left R-action.
The right S-linear coordinate equivalence determined by equivariant
k-linear f : M ≅ M′ and g : N ≅ N′ also preserves the ground action:
rightCongr(c • x) = c • rightCongr(x) for c ∈ k. -/
theorem rightCongr_ground_smul (c : k) (x : Balanced k R M N) :
    letI := rightModule k R S M N
    letI := rightModule k R S M' N'
    rightCongr k R S M N f g hf hg hgS (c • x) =
      c • rightCongr k R S M N f g hf hg hgS x :=
  (congr (k := k) (R := R) f g hf hg).map_smul c x

end Coordinates

/-- Let k be a commutative ring and R, S semirings. Let M be a right
R-module and N a left R-module and right S-module, both additive commutative
groups with k-module structures. The right S-action on N commutes with
its k-action and left R-action.
At any common lift height z, this right S-linear equivalence
ULift M ⊗_R ULift N ≅ M ⊗_R N lowers both factors.
Its pure value is [m ⊗ n] ↦ [m.down ⊗ n.down], with inverse
[m ⊗ n] ↦ [ULift.up(m) ⊗ ULift.up(n)]. -/
def uliftRightCarrierEquiv :
    letI : SMulCommClass Sᵐᵒᵖ k (ULift.{z} N) := ULift.smulCommClassOfBase Sᵐᵒᵖ k N
    letI : SMulCommClass R Sᵐᵒᵖ (ULift.{z} N) := ULift.smulCommClassOfBase R Sᵐᵒᵖ N
    letI := rightModule k R S (ULift.{z} M) (ULift.{z} N)
    letI := rightModule k R S M N
    Balanced k R (ULift.{z} M) (ULift.{z} N) ≃ₗ[Sᵐᵒᵖ] Balanced k R M N := by
  letI : SMulCommClass Sᵐᵒᵖ k (ULift.{z} N) := ULift.smulCommClassOfBase Sᵐᵒᵖ k N
  letI : SMulCommClass R Sᵐᵒᵖ (ULift.{z} N) := ULift.smulCommClassOfBase R Sᵐᵒᵖ N
  letI := rightModule k R S (ULift.{z} M) (ULift.{z} N)
  letI := rightModule k R S M N
  exact rightCongr k R S (ULift.{z} M) (ULift.{z} N)
    (ULift.moduleEquiv : ULift.{z} M ≃ₗ[k] M)
    (ULift.moduleEquiv : ULift.{z} N ≃ₗ[k] N)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- Let k be a commutative ring and R, S semirings. Let M be a right
R-module and N a left R-module and right S-module, both additive commutative
groups with k-module structures. The right S-action on N commutes with
its k-action and left R-action.
For m ∈ ULift M and n ∈ ULift N at a common height z, the
carrier-lowering equivalence has value
[m ⊗ n] ↦ [m.down ⊗ n.down]. -/
theorem uliftRightCarrierEquiv_mk (m : ULift.{z} M) (n : ULift.{z} N) :
    letI : SMulCommClass Sᵐᵒᵖ k (ULift.{z} N) := ULift.smulCommClassOfBase Sᵐᵒᵖ k N
    letI : SMulCommClass R Sᵐᵒᵖ (ULift.{z} N) := ULift.smulCommClassOfBase R Sᵐᵒᵖ N
    letI := rightModule k R S (ULift.{z} M) (ULift.{z} N)
    letI := rightModule k R S M N
    uliftRightCarrierEquiv k R S M N (mk k R (ULift.{z} M) (ULift.{z} N) m n) =
      mk k R M N m.down n.down :=
  rightCongr_mk k R S (ULift.{z} M) (ULift.{z} N)
    (ULift.moduleEquiv : ULift.{z} M ≃ₗ[k] M)
    (ULift.moduleEquiv : ULift.{z} N ≃ₗ[k] N)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) m n

/-- Let k be a commutative ring and R, S semirings. Let M be a right
R-module and N a left R-module and right S-module, both additive commutative
groups with k-module structures. The right S-action on N commutes with
its k-action and left R-action.
At a common lift height z, the inverse carrier-lowering equivalence
sends a pure class [m ⊗ n] to [ULift.up(m) ⊗ ULift.up(n)]. -/
theorem uliftRightCarrierEquiv_symm_mk (m : M) (n : N) :
    letI : SMulCommClass Sᵐᵒᵖ k (ULift.{z} N) := ULift.smulCommClassOfBase Sᵐᵒᵖ k N
    letI : SMulCommClass R Sᵐᵒᵖ (ULift.{z} N) := ULift.smulCommClassOfBase R Sᵐᵒᵖ N
    letI := rightModule k R S (ULift.{z} M) (ULift.{z} N)
    letI := rightModule k R S M N
    (uliftRightCarrierEquiv k R S M N).symm (mk k R M N m n) =
      mk k R (ULift.{z} M) (ULift.{z} N) (ULift.up m) (ULift.up n) :=
  rightCongr_symm_mk k R S (ULift.{z} M) (ULift.{z} N)
    (ULift.moduleEquiv : ULift.{z} M ≃ₗ[k] M)
    (ULift.moduleEquiv : ULift.{z} N ≃ₗ[k] N)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) m n

/-- Let k be a commutative ring and R, S semirings. Let M be a right
R-module and N a left R-module and right S-module, both additive commutative
groups with k-module structures. The right S-action on N commutes with
its k-action and left R-action.
For any common lift height z, this right S-linear equivalence
ULift M ⊗_R ULift N ≅ ULift(M ⊗_R N) lowers the two factors
and then lifts their balanced class in the whole output carrier. -/
def uliftRightEquiv :
    letI : SMulCommClass Sᵐᵒᵖ k (ULift.{z} N) := ULift.smulCommClassOfBase Sᵐᵒᵖ k N
    letI : SMulCommClass R Sᵐᵒᵖ (ULift.{z} N) := ULift.smulCommClassOfBase R Sᵐᵒᵖ N
    letI := rightModule k R S (ULift.{z} M) (ULift.{z} N)
    letI := rightModule k R S M N
    Balanced k R (ULift.{z} M) (ULift.{z} N) ≃ₗ[Sᵐᵒᵖ] ULift.{z} (Balanced k R M N) := by
  letI : SMulCommClass Sᵐᵒᵖ k (ULift.{z} N) := ULift.smulCommClassOfBase Sᵐᵒᵖ k N
  letI : SMulCommClass R Sᵐᵒᵖ (ULift.{z} N) := ULift.smulCommClassOfBase R Sᵐᵒᵖ N
  letI := rightModule k R S (ULift.{z} M) (ULift.{z} N)
  letI := rightModule k R S M N
  exact (uliftRightCarrierEquiv k R S M N).trans
    (ULift.moduleEquiv : ULift.{z} (Balanced k R M N) ≃ₗ[Sᵐᵒᵖ] Balanced k R M N).symm

/-- Let k be a commutative ring and R, S semirings. Let M be a right
R-module and N a left R-module and right S-module, both additive commutative
groups with k-module structures. The right S-action on N commutes with
its k-action and left R-action.
For m ∈ ULift M and n ∈ ULift N at a common height z, the
comparison to the lifted output has value
[m ⊗ n] ↦ ULift.up([m.down ⊗ n.down]). -/
theorem uliftRightEquiv_mk (m : ULift.{z} M) (n : ULift.{z} N) :
    letI : SMulCommClass Sᵐᵒᵖ k (ULift.{z} N) := ULift.smulCommClassOfBase Sᵐᵒᵖ k N
    letI : SMulCommClass R Sᵐᵒᵖ (ULift.{z} N) := ULift.smulCommClassOfBase R Sᵐᵒᵖ N
    letI := rightModule k R S (ULift.{z} M) (ULift.{z} N)
    letI := rightModule k R S M N
    uliftRightEquiv k R S M N (mk k R (ULift.{z} M) (ULift.{z} N) m n) =
      ULift.up (mk k R M N m.down n.down) := by
  let : SMulCommClass Sᵐᵒᵖ k (ULift.{z} N) := ULift.smulCommClassOfBase Sᵐᵒᵖ k N
  let : SMulCommClass R Sᵐᵒᵖ (ULift.{z} N) := ULift.smulCommClassOfBase R Sᵐᵒᵖ N
  let := rightModule k R S (ULift.{z} M) (ULift.{z} N)
  let := rightModule k R S M N
  change ULift.up (uliftRightCarrierEquiv k R S M N _ ) = _
  rw [uliftRightCarrierEquiv_mk]

/-- Let k be a commutative ring and R, S semirings. Let M be a right
R-module and N a left R-module and right S-module, both additive commutative
groups with k-module structures. The right S-action on N commutes with
its k-action and left R-action.
At a common lift height z, the inverse comparison from the lifted
output sends ULift.up([m ⊗ n]) to
[ULift.up(m) ⊗ ULift.up(n)]. -/
theorem uliftRightEquiv_symm_mk (m : M) (n : N) :
    letI := rightModule k R S (ULift.{z} M) (ULift.{z} N)
    letI := rightModule k R S M N
    (uliftRightEquiv k R S M N).symm (ULift.up (mk k R M N m n)) =
      mk k R (ULift.{z} M) (ULift.{z} N) (ULift.up m) (ULift.up n) := by
  let := rightModule k R S (ULift.{z} M) (ULift.{z} N)
  let := rightModule k R S M N
  apply (uliftRightEquiv k R S M N).injective
  rw [LinearEquiv.apply_symm_apply, uliftRightEquiv_mk]

section Naturality

variable {M' : Type a'} {N' : Type b'} [AddCommGroup M'] [AddCommGroup N']
  [Module k M'] [Module k N'] [Module Rᵐᵒᵖ M'] [Module R N'] [Module Sᵐᵒᵖ N']
  [SMulCommClass Sᵐᵒᵖ k N'] [SMulCommClass R Sᵐᵒᵖ N']
  (f : M →ₗ[k] M') (g : N →ₗ[k] N')
  (hf : ∀ (r : R) (m : M), f (op r • m) = op r • f m)
  (hg : ∀ (r : R) (n : N), g (r • n) = r • g n)
  (hgS : ∀ (s : Sᵐᵒᵖ) (n : N), g (s • n) = s • g n)

/-- Let k be a commutative ring and R, S semirings. Let M be a right
R-module and N a left R-module and right S-module, both additive commutative
groups with k-module structures. The right S-action on N commutes with
its k-action and left R-action.
Let k-linear maps f : M → M′ and g : N → N′ preserve right R and
left R/right S respectively, with the same action structures on the targets.
At a common lift height z, lowering lifted factors commutes with the
induced quotient maps: lower′ ∘ tensor(ULift f, ULift g) =
tensor(f, g) ∘ lower. -/
theorem uliftRightCarrierEquiv_naturality :
    letI := rightModule k R S (ULift.{z} M) (ULift.{z} N)
    letI := rightModule k R S (ULift.{z} M') (ULift.{z} N')
    letI := rightModule k R S M N
    letI := rightModule k R S M' N'
    (uliftRightCarrierEquiv k R S M' N').toLinearMap.comp
        (mapRight (ULift.mapLinear k f : ULift.{z} M →ₗ[k] ULift.{z} M')
          (ULift.mapLinear k g : ULift.{z} N →ₗ[k] ULift.{z} N')
          (fun r m => congrArg ULift.up (hf r m.down))
          (fun r n => congrArg ULift.up (hg r n.down))
          (fun s n => congrArg ULift.up (hgS s n.down))) =
      (mapRight f g hf hg hgS).comp (uliftRightCarrierEquiv k R S M N).toLinearMap := by
  let := rightModule k R S (ULift.{z} M) (ULift.{z} N)
  let := rightModule k R S (ULift.{z} M') (ULift.{z} N')
  let := rightModule k R S M N
  let := rightModule k R S M' N'
  apply LinearMap.toAddMonoidHom_injective
  apply addHom_ext k R (ULift.{z} M) (ULift.{z} N)
  intro m n
  change uliftRightCarrierEquiv k R S M' N'
      (mapRight (ULift.mapLinear k f) (ULift.mapLinear k g)
        (fun r m => congrArg ULift.up (hf r m.down))
        (fun r n => congrArg ULift.up (hg r n.down))
        (fun s n => congrArg ULift.up (hgS s n.down))
        (mk k R (ULift.{z} M) (ULift.{z} N) m n)) =
    mapRight f g hf hg hgS
      (uliftRightCarrierEquiv k R S M N (mk k R (ULift.{z} M) (ULift.{z} N) m n))
  have hLift := mapRight_mk (k := k) (R := R) (S := S)
    (ULift.mapLinear k f : ULift.{z} M →ₗ[k] ULift.{z} M')
    (ULift.mapLinear k g : ULift.{z} N →ₗ[k] ULift.{z} N')
    (fun r m => congrArg ULift.up (hf r m.down))
    (fun r n => congrArg ULift.up (hg r n.down))
    (fun s n => congrArg ULift.up (hgS s n.down)) m n
  have hBase := mapRight_mk (k := k) (R := R) (S := S) f g hf hg hgS m.down n.down
  rw [hLift, uliftRightCarrierEquiv_mk, uliftRightCarrierEquiv_mk, hBase]
  rfl

/-- Let k be a commutative ring and R, S semirings. Let M be a right
R-module and N a left R-module and right S-module, both additive commutative
groups with k-module structures. The right S-action on N commutes with
its k-action and left R-action.
Let k-linear maps f : M → M′ and g : N → N′ preserve right R and
left R/right S respectively, with the same action structures on the targets.
At a common lift height z, the whole-output comparison χ satisfies
χ′ ∘ tensor(ULift f, ULift g) = ULift(tensor(f, g)) ∘ χ. -/
theorem uliftRightEquiv_naturality :
    letI := rightModule k R S (ULift.{z} M) (ULift.{z} N)
    letI := rightModule k R S (ULift.{z} M') (ULift.{z} N')
    letI := rightModule k R S M N
    letI := rightModule k R S M' N'
    (uliftRightEquiv k R S M' N').toLinearMap.comp
        (mapRight (ULift.mapLinear k f : ULift.{z} M →ₗ[k] ULift.{z} M')
          (ULift.mapLinear k g : ULift.{z} N →ₗ[k] ULift.{z} N')
          (fun r m => congrArg ULift.up (hf r m.down))
          (fun r n => congrArg ULift.up (hg r n.down))
          (fun s n => congrArg ULift.up (hgS s n.down))) =
      (ULift.mapLinear Sᵐᵒᵖ (mapRight f g hf hg hgS) :
        ULift.{z} (Balanced k R M N) →ₗ[Sᵐᵒᵖ] ULift.{z} (Balanced k R M' N')).comp
          (uliftRightEquiv k R S M N).toLinearMap := by
  let := rightModule k R S (ULift.{z} M) (ULift.{z} N)
  let := rightModule k R S (ULift.{z} M') (ULift.{z} N')
  let := rightModule k R S M N
  let := rightModule k R S M' N'
  apply LinearMap.toAddMonoidHom_injective
  apply addHom_ext k R (ULift.{z} M) (ULift.{z} N)
  intro m n
  change uliftRightEquiv k R S M' N'
      (mapRight (ULift.mapLinear k f) (ULift.mapLinear k g)
        (fun r m => congrArg ULift.up (hf r m.down))
        (fun r n => congrArg ULift.up (hg r n.down))
        (fun s n => congrArg ULift.up (hgS s n.down))
        (mk k R (ULift.{z} M) (ULift.{z} N) m n)) =
    ULift.mapLinear Sᵐᵒᵖ (mapRight f g hf hg hgS)
      (uliftRightEquiv k R S M N (mk k R (ULift.{z} M) (ULift.{z} N) m n))
  have hLift := mapRight_mk (k := k) (R := R) (S := S)
    (ULift.mapLinear k f : ULift.{z} M →ₗ[k] ULift.{z} M')
    (ULift.mapLinear k g : ULift.{z} N →ₗ[k] ULift.{z} N')
    (fun r m => congrArg ULift.up (hf r m.down))
    (fun r n => congrArg ULift.up (hg r n.down))
    (fun s n => congrArg ULift.up (hgS s n.down)) m n
  rw [hLift, uliftRightEquiv_mk, uliftRightEquiv_mk]
  change ULift.up (mk k R M' N' (f m.down) (g n.down)) =
    ULift.up (mapRight f g hf hg hgS (mk k R M N m.down n.down))
  exact congrArg ULift.up
    (mapRight_mk (k := k) (R := R) (S := S) f g hf hg hgS m.down n.down).symm

end Naturality

end TensorProduct.Balanced
