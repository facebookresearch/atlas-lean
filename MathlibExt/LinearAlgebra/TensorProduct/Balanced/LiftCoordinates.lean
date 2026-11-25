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
# Actual lifted coordinates on the balanced quotient

The coordinate maps are the existing balanced congruence maps. Their right
outer linearity is earned from the existing action naturality equation.
Native coefficient/input lifts and native up/down are retained, as are the
original ground scalars and ordered balancing and outer actions. No action
is installed globally and no flatness, freeness or carrier smallness is used.
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

/-- The existing quotient congruence is outer-linear for its actual computed right actions. -/
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

/-- The actual right-coordinate map preserves the two original pure factors. -/
theorem rightCongr_mk (m : M) (n : N) :
    letI := rightModule k R S M N
    letI := rightModule k R S M' N'
    rightCongr k R S M N f g hf hg hgS (mk k R M N m n) =
      mk k R M' N' (f m) (g n) :=
  congr_mk f g hf hg m n

/-- Inverse coordinates preserve the same original ordered factors. -/
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

/-- Outer-linear coordinates also retain the original ground scalar action. -/
theorem rightCongr_ground_smul (c : k) (x : Balanced k R M N) :
    letI := rightModule k R S M N
    letI := rightModule k R S M' N'
    rightCongr k R S M N f g hf hg hgS (c • x) =
      c • rightCongr k R S M N f g hf hg hgS x :=
  (congr (k := k) (R := R) f g hf hg).map_smul c x

end Coordinates

/-- Lower both native lifted factors through the original balanced quotient. -/
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

/-- The lifted quotient coordinate is exactly down on both original factors. -/
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

/-- Inverse lifted coordinates are exactly native up on the two original factors. -/
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

/-- Compare lifted factors with a native lift of the whole original quotient. -/
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

/-- The whole-output comparison has the literal original representative value. -/
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

/-- The inverse whole-output comparison inserts the actual two native input lifts. -/
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

/-- Actual input and coefficient maps commute with lowering native lifted coordinates. -/
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

/-- Whole-output lift comparison is natural in the same actual ordered coefficient maps. -/
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
