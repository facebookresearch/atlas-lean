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

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.Alternating.DomCoprod

/-!
# General exterior unshuffle components

The `(p,q)` unshuffle is the alternating descent of the native exterior
product of alternating maps. Native shuffle cosets avoid multiplying by
`p! q!`; all degrees, including either empty block, work over an arbitrary
commutative ring. The summand formula and naturality use the actual maps.
-/

@[expose] public section

noncomputable section

open Function
open scoped TensorProduct

universe u v w

namespace exteriorPower

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The native `(p,q)` shuffle sum is an alternating map on the entire word. -/
def unshuffleAlternating (p q : ℕ) :
    M [⋀^Fin (p + q)]→ₗ[R] ((⋀[R]^p M) ⊗[R] (⋀[R]^q M)) :=
  ((ιMulti R p).domCoprod (ιMulti R q)).domDomCongr
    (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q))

/-- The general unshuffle component, constructed by the alternating universal property. -/
def unshuffle (p q : ℕ) :
    (⋀[R]^(p + q) M) →ₗ[R] ((⋀[R]^p M) ⊗[R] (⋀[R]^q M)) :=
  alternatingMapLinearEquiv (R := R) (n := p + q) (M := M)
    (N := (⋀[R]^p M) ⊗[R] (⋀[R]^q M)) (unshuffleAlternating R M p q)

/-- Each shuffle coset contributes once; no factorial denominator is used. -/
theorem unshuffle_apply_ιMulti (p q : ℕ) (v : Fin (p + q) → M) :
    unshuffle R M p q (ιMulti R (p + q) v) =
      ∑ σ : Equiv.Perm.ModSumCongr (Fin p) (Fin q),
        AlternatingMap.domCoprod.summand (ιMulti R p) (ιMulti R q) σ
          (v ∘ (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q))) := by
  rw [unshuffle, alternatingMapLinearEquiv_apply_ιMulti]
  change ((ιMulti R p).domCoprod (ιMulti R q))
    (v ∘ (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q))) = _
  rw [AlternatingMap.domCoprod_apply, _root_.sum_apply]

/-- A representative gives the expected signed ordered two-block tensor. -/
theorem unshuffle_summand_representative (p q : ℕ)
    (σ : Equiv.Perm (Fin p ⊕ Fin q)) (v : Fin (p + q) → M) :
    AlternatingMap.domCoprod.summand (ιMulti R p) (ιMulti R q) (Quotient.mk'' σ)
        (v ∘ (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q))) =
      Equiv.Perm.sign σ •
        (ιMulti R p (fun i => v (finSumFinEquiv (σ (Sum.inl i)))) ⊗ₜ[R]
          ιMulti R q (fun j => v (finSumFinEquiv (σ (Sum.inr j))))) := by
  rw [AlternatingMap.domCoprod.summand_mk'', _root_.smul_apply]
  simp only [MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
    Function.comp_apply]
  exact (TensorProduct.smul_tmul' (Equiv.Perm.sign σ) _ _).symm

section Naturality

variable {N : Type w} [AddCommGroup N] [Module R N]

private theorem unshuffle_summand_naturality (p q : ℕ) (f : M →ₗ[R] N)
    (σ : Equiv.Perm.ModSumCongr (Fin p) (Fin q)) (v : Fin p ⊕ Fin q → M) :
    TensorProduct.map (map p f) (map q f)
        (AlternatingMap.domCoprod.summand (ιMulti R p) (ιMulti R q) σ v) =
      AlternatingMap.domCoprod.summand (ιMulti R p) (ιMulti R q) σ (f ∘ v) := by
  induction σ using Quotient.inductionOn' with
  | _ σ =>
      rw [AlternatingMap.domCoprod.summand_mk'',
        AlternatingMap.domCoprod.summand_mk'', _root_.smul_apply, _root_.smul_apply]
      simp only [Units.smul_def, map_zsmul, MultilinearMap.domDomCongr_apply,
        MultilinearMap.domCoprod_apply, TensorProduct.map_tmul, map_apply_ιMulti]
      change (TensorProduct.map (map p f) (map q f))
        ((Equiv.Perm.sign σ : ℤ) •
          (ιMulti R p (fun i => v (σ (Sum.inl i))) ⊗ₜ[R]
            ιMulti R q (fun i => v (σ (Sum.inr i))))) = _
      rw [map_zsmul, TensorProduct.map_tmul, map_apply_ιMulti, map_apply_ιMulti]
      rfl

/-- Exterior unshuffle is natural in arbitrary linear maps and independent module universes. -/
theorem unshuffle_naturality (p q : ℕ) (f : M →ₗ[R] N) :
    (TensorProduct.map (map p f) (map q f)).comp (unshuffle R M p q) =
      (unshuffle R N p q).comp (map (p + q) f) := by
  apply exteriorPower.linearMap_ext (R := R) (n := p + q) (M := M)
    (N := (⋀[R]^p N) ⊗[R] (⋀[R]^q N))
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    unshuffle_apply_ιMulti, map_apply_ιMulti, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  exact unshuffle_summand_naturality R M p q f σ
    (v ∘ (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q)))

end Naturality

end exteriorPower
