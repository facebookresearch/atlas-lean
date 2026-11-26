/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/- Signed antisymmetrization of the original tensor coordinates. -/
module

public import MathlibExt.LinearAlgebra.TensorPower.Cons
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Antisymmetrization and the factorial identity

Let k be a commutative ring and V a k-module. Write Aₙ : ⋀ⁿV → V⊗n for the signed lift of an
exterior word, and Qₙ : V⊗n → ⋀ⁿV for the exterior projection. Then Aₙ(v₁ ∧ ⋯ ∧ vₙ) = ∑σ sign(σ)
· ⊗ᵢvσ(i), and Qₙ ∘ Aₙ = n! · id. These formulas use integer signs and hold in every
characteristic. Both maps commute with k-linear maps of V.

For the alternating universal property and these signed sums, see N. Bourbaki, Algebra I,
Chapter III (multilinear algebra).
-/

@[expose] public section
noncomputable section

open scoped TensorProduct

universe u v w z

namespace TensorPower

variable (k : Type u) [CommRing k] (V : Type v) [AddCommGroup V] [Module k V]

private theorem linearMap_sign_smul {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module k M] [Module k N] (f : M →ₗ[k] N) (n : ℕ) (π : Equiv.Perm (Fin n)) (m : M) :
    f (Equiv.Perm.sign π • m) = Equiv.Perm.sign π • f m := by
  change f ((Equiv.Perm.sign π : ℤ) • m) = (Equiv.Perm.sign π : ℤ) • f m
  exact map_zsmul f _ _

/-- The signed lift from exterior powers to tensor powers.

For a commutative ring k, a k-module V and n ≥ 0, this k-linear map Aₙ : ⋀ⁿV → V⊗n sends v₁
∧ ⋯ ∧ vₙ to ∑σ∈Sₙ sign(σ) · ⊗ᵢvσ(i). The signs act through ℤ → k. -/
def exteriorAntisymmetrization (n : ℕ) : (⋀[k]^n V) →ₗ[k] TensorPower k n V :=
  exteriorPower.alternatingMapLinearEquiv
    (MultilinearMap.alternatization (PiTensorProduct.tprod k))

/-- The exterior projection of a tensor power.

For a commutative ring k and a k-module V, Qₙ : V⊗n → ⋀ⁿV is the k-linear map taking ⊗ᵢvᵢ to
v₁ ∧ ⋯ ∧ vₙ. -/
def exteriorProjection (n : ℕ) : TensorPower k n V →ₗ[k] (⋀[k]^n V) :=
  PiTensorProduct.lift (exteriorPower.ιMulti k n).toMultilinearMap

/-- The signed tensor formula for an exterior word.

For a commutative ring k, a k-module V and a : Fin n → V, Aₙ(ιₙ(a)) = ∑σ∈Sₙ sign(σ) ·
tprod(a ∘ σ), where ιₙ is the exterior word map. This sum is integral. -/
theorem exteriorAntisymmetrization_ιMulti (n : ℕ) (a : Fin n → V) :
    exteriorAntisymmetrization k V n (exteriorPower.ιMulti k n a) =
      ∑ π : Equiv.Perm (Fin n), Equiv.Perm.sign π • PiTensorProduct.tprod k (a ∘ π) := by
  rw [exteriorAntisymmetrization, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    MultilinearMap.alternatization_apply]
  rfl

/-- Projection of a pure tensor to its exterior word.

For a commutative ring k, a k-module V and a : Fin n → V, Qₙ(tprod(a)) = ιₙ(a) in ⋀ⁿV. -/
@[simp]
theorem exteriorProjection_tprod (n : ℕ) (a : Fin n → V) :
    exteriorProjection k V n (PiTensorProduct.tprod k a) = exteriorPower.ιMulti k n a :=
  PiTensorProduct.lift.tprod _

/-- Vanishing when two exterior entries agree.

For a commutative ring k, a k-module V and a : Fin n → V, if a i = a j with i ≠ j, then
Aₙ(ιₙ(a)) = 0. This follows from alternation and also holds in characteristic two. -/
theorem exteriorAntisymmetrization_ιMulti_eq_zero
    (n : ℕ) (a : Fin n → V) (i j : Fin n) (h : a i = a j) (hij : i ≠ j) :
    exteriorAntisymmetrization k V n (exteriorPower.ιMulti k n a) = 0 := by
  rw [(exteriorPower.ιMulti k n).map_eq_zero_of_eq a h hij, map_zero]

/-- The permutation sign of an antisymmetrized exterior word.

For a commutative ring k, a k-module V, a : Fin n → V and σ ∈ Sₙ, Aₙ(ιₙ(a ∘ σ)) = sign(σ) ·
Aₙ(ιₙ(a)). The sign is an integer scalar. -/
theorem exteriorAntisymmetrization_ιMulti_perm
    (n : ℕ) (a : Fin n → V) (π : Equiv.Perm (Fin n)) :
    exteriorAntisymmetrization k V n (exteriorPower.ιMulti k n (a ∘ π)) =
      Equiv.Perm.sign π • exteriorAntisymmetrization k V n (exteriorPower.ιMulti k n a) := by
  rw [(exteriorPower.ιMulti k n).map_perm a π]
  exact linearMap_sign_smul k (exteriorAntisymmetrization k V n) n π
    (exteriorPower.ιMulti k n a)

section UniversalAlternatingMap

variable {N : Type w} [AddCommGroup N] [Module k N]

/-- The factorial identity for an alternating functional.

Let k be a commutative ring, V and N k-modules, and f : Vⁿ → N an alternating k-multilinear
map. The tensor lift of f composed with Aₙ equals n! times the induced map ⋀ⁿV → N. -/
theorem lift_alternating_comp_exteriorAntisymmetrization
    (n : ℕ) (a : V [⋀^Fin n]→ₗ[k] N) :
    (PiTensorProduct.lift a.toMultilinearMap).comp (exteriorAntisymmetrization k V n) =
      n.factorial • exteriorPower.alternatingMapLinearEquiv a := by
  let p : TensorPower k n V →ₗ[k] N := PiTensorProduct.lift a.toMultilinearMap
  have hp : p.compMultilinearMap (PiTensorProduct.tprod k) = a.toMultilinearMap := by
    ext v
    exact PiTensorProduct.lift.tprod v
  have h := LinearMap.compMultilinearMap_alternatization p (PiTensorProduct.tprod k)
  rw [hp, AlternatingMap.coe_alternatization] at h
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  have hv := DFunLike.congr_fun h v
  simpa only [LinearMap.comp_apply, exteriorAntisymmetrization,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    LinearMap.compAlternatingMap_apply, Fintype.card_fin, AlternatingMap.smul_apply,
    LinearMap.smul_apply, p] using hv.symm

end UniversalAlternatingMap

/-- The exterior projection of antisymmetrization is multiplication by n!.

For a commutative ring k and any k-module V, Qₙ ∘ Aₙ = n! · id on ⋀ⁿV. The formula requires
no invertibility of n! in k. -/
theorem exteriorProjection_comp_exteriorAntisymmetrization (n : ℕ) :
    (exteriorProjection k V n).comp (exteriorAntisymmetrization k V n) =
      n.factorial • (LinearMap.id : (⋀[k]^n V) →ₗ[k] (⋀[k]^n V)) := by
  simpa only [exteriorProjection, exteriorPower.alternatingMapLinearEquiv_ιMulti] using
    lift_alternating_comp_exteriorAntisymmetrization k V n (exteriorPower.ιMulti k n)

/-- The factorial identity on an exterior element.

For a commutative ring k, a k-module V and x ∈ ⋀ⁿV, Qₙ(Aₙ(x)) = n! · x. -/
theorem exteriorProjection_exteriorAntisymmetrization (n : ℕ) (x : ⋀[k]^n V) :
    exteriorProjection k V n (exteriorAntisymmetrization k V n x) = n.factorial • x :=
  DFunLike.congr_fun (exteriorProjection_comp_exteriorAntisymmetrization k V n) x

section Naturality

variable {W : Type w} [AddCommGroup W] [Module k W]

/-- Naturality of the signed exterior lift.

For a commutative ring k and a k-linear map f : V → W, the factorwise map f⊗n satisfies f⊗n
∘ Aₙ,V = Aₙ,W ∘ ⋀ⁿf. The modules V and W may lie in different universes. -/
theorem exteriorAntisymmetrization_naturality (f : V →ₗ[k] W) (n : ℕ) :
    (PiTensorProduct.map (fun _ : Fin n => f)).comp (exteriorAntisymmetrization k V n) =
      (exteriorAntisymmetrization k W n).comp (exteriorPower.map n f) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro a
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, exteriorAntisymmetrization_ιMulti,
    exteriorPower.map_apply_ιMulti, map_sum, linearMap_sign_smul,
    PiTensorProduct.map_tprod]
  rfl

/-- Naturality of the exterior projection.

For a commutative ring k and a k-linear map f : V → W, Qₙ,W ∘ f⊗n = ⋀ⁿf ∘ Qₙ,V. Here f⊗n
applies f to each tensor factor. -/
theorem exteriorProjection_naturality (f : V →ₗ[k] W) (n : ℕ) :
    (exteriorProjection k W n).comp (PiTensorProduct.map (fun _ : Fin n => f)) =
      (exteriorPower.map n f).comp (exteriorProjection k V n) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro a
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod,
    exteriorProjection_tprod, exteriorPower.map_apply_ιMulti]
  rfl

end Naturality

/-- Antisymmetrization of an empty exterior word.

For a commutative ring k and a k-module V, the degree-zero map sends ι₀(a) to tprod(a), for
the unique empty family a : Fin 0 → V. -/
theorem exteriorAntisymmetrization_zero_ιMulti (a : Fin 0 → V) :
    exteriorAntisymmetrization k V 0 (exteriorPower.ιMulti k 0 a) =
      PiTensorProduct.tprod k a := by
  rw [exteriorAntisymmetrization_ιMulti]
  simp only [Finset.univ_unique, Finset.sum_singleton, Equiv.Perm.sign_one, one_smul]
  have hid : (default : Equiv.Perm (Fin 0)) = 1 := by
    apply Equiv.ext
    intro i
    exact Fin.elim0 i
  rw [hid, Equiv.Perm.sign_one, one_smul]
  exact congrArg (PiTensorProduct.tprod k) (by funext i; exact Fin.elim0 i)

/-- The degree-zero scalar coordinate of antisymmetrization.

For a commutative ring k and a k-module V, identifying both ⋀⁰V and V⊗0 with k identifies A₀
with the identity map of k. -/
theorem exteriorAntisymmetrization_zero_coordinate :
    (zeroEquiv k V).toLinearMap.comp (exteriorAntisymmetrization k V 0) =
      (exteriorPower.zeroEquiv k V).toLinearMap := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro a
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply]
  erw [exteriorAntisymmetrization_zero_ιMulti,
    exteriorPower.zeroEquiv_ιMulti]
  exact PiTensorProduct.isEmptyEquiv_apply_tprod (R := k) (s := fun _ : Fin 0 => V) (Fin 0) a

end TensorPower
