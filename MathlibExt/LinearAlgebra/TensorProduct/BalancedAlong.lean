/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.LinearAlgebra.TensorProduct.Balanced

/-!
# Balanced tensor maps under change of acting rings

Ground-linear maps equivariant along a homomorphism of acting rings induce maps of balanced tensor
quotients. Their pure-tensor values preserve both carrier maps, and they satisfy identity and
composition laws. The acting rings and carrier universes are independent.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct
open MulOpposite

universe uk uR uS uM uN uM' uN'

namespace TensorProduct.Balanced

variable {k : Type uk} [CommRing k]
  {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]
  {M : Type uM} {N : Type uN} {M' : Type uM'} {N' : Type uN'}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
  [Module k M] [Module k N] [Module k M'] [Module k N']
  [Module Rᵐᵒᵖ M] [Module R N] [Module Sᵐᵒᵖ M'] [Module S N']

/-- The balanced tensor map along a scalar homomorphism. -/
def mapAlong (φ : R →+* S) (f : M →ₗ[k] M') (g : N →ₗ[k] N')
    (hf : ∀ r m, f (op r • m) = op (φ r) • f m)
    (hg : ∀ r n, g (r • n) = φ r • g n) :
    Balanced k R M N →ₗ[k] Balanced k S M' N' :=
  lift (((mk k S M' N').compl₂ g).comp f) (by
    intro r m n
    change mk k S M' N' (f (op r • m)) (g n) =
      mk k S M' N' (f m) (g (r • n))
    rw [hf, hg, balance])

/-- Both carrier maps are retained on a balanced pure representative. -/
theorem mapAlong_mk (φ : R →+* S) (f : M →ₗ[k] M') (g : N →ₗ[k] N')
    (hf : ∀ r m, f (op r • m) = op (φ r) • f m)
    (hg : ∀ r n, g (r • n) = φ r • g n) (m : M) (n : N) :
    mapAlong φ f g hf hg (mk k R M N m n) = mk k S M' N' (f m) (g n) := rfl

/-- The identity scalar/carrier maps give the balanced identity. -/
theorem mapAlong_id :
    mapAlong (RingHom.id R) (LinearMap.id : M →ₗ[k] M)
      (LinearMap.id : N →ₗ[k] N) (by intros; rfl) (by intros; rfl) = LinearMap.id := by
  apply hom_ext
  intro m n
  rfl

/-- Balanced maps compose along the composite scalar homomorphism. -/
theorem mapAlong_comp
    {T : Type*} [Semiring T] {M'' N'' : Type*}
    [AddCommGroup M''] [AddCommGroup N''] [Module k M''] [Module k N'']
    [Module Tᵐᵒᵖ M''] [Module T N'']
    (φ : R →+* S) (ψ : S →+* T)
    (f : M →ₗ[k] M') (g : N →ₗ[k] N')
    (f' : M' →ₗ[k] M'') (g' : N' →ₗ[k] N'')
    (hf : ∀ r m, f (op r • m) = op (φ r) • f m)
    (hg : ∀ r n, g (r • n) = φ r • g n)
    (hf' : ∀ s m, f' (op s • m) = op (ψ s) • f' m)
    (hg' : ∀ s n, g' (s • n) = ψ s • g' n) :
    (mapAlong ψ f' g' hf' hg').comp (mapAlong φ f g hf hg) =
      mapAlong (ψ.comp φ) (f'.comp f) (g'.comp g)
        (fun r m => (congrArg f' (hf r m)).trans (hf' (φ r) (f m)))
        (fun r n => (congrArg g' (hg r n)).trans (hg' (φ r) (g n))) := by
  apply hom_ext
  intro m n
  rw [LinearMap.comp_apply, mapAlong_mk, mapAlong_mk, mapAlong_mk]
  rfl

end TensorProduct.Balanced
