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
# Actual antisymmetrization between exterior and tensor powers

The forward map sends an exterior word to the sum of all tensor-place
permutations with their integer signs. The tensor-to-exterior map uses the
native alternating universal property. Their composite is multiplication
by `n!`, over every commutative ring and for every module.

No factorial is inverted in this owner. In particular the factorial law
does not assert an isomorphism in positive characteristic. All maps and
their naturality laws use the original tensor and exterior objects.
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

/-- Native signed alternatization, descended through the actual exterior power. -/
def exteriorAntisymmetrization (n : ℕ) : (⋀[k]^n V) →ₗ[k] TensorPower k n V :=
  exteriorPower.alternatingMapLinearEquiv
    (MultilinearMap.alternatization (PiTensorProduct.tprod k))

/-- The actual exterior word map on the native tensor power. -/
def exteriorProjection (n : ℕ) : TensorPower k n V →ₗ[k] (⋀[k]^n V) :=
  PiTensorProduct.lift (exteriorPower.ιMulti k n).toMultilinearMap

/-- Every original exterior word maps to its complete signed permutation sum. -/
theorem exteriorAntisymmetrization_ιMulti (n : ℕ) (a : Fin n → V) :
    exteriorAntisymmetrization k V n (exteriorPower.ιMulti k n a) =
      ∑ π : Equiv.Perm (Fin n), Equiv.Perm.sign π • PiTensorProduct.tprod k (a ∘ π) := by
  rw [exteriorAntisymmetrization, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    MultilinearMap.alternatization_apply]
  rfl

/-- The projection takes an original pure tensor to its original exterior word. -/
@[simp]
theorem exteriorProjection_tprod (n : ℕ) (a : Fin n → V) :
    exteriorProjection k V n (PiTensorProduct.tprod k a) = exteriorPower.ιMulti k n a :=
  PiTensorProduct.lift.tprod _

/-- Antisymmetrization annihilates repeated input vectors, including in characteristic two. -/
theorem exteriorAntisymmetrization_ιMulti_eq_zero
    (n : ℕ) (a : Fin n → V) (i j : Fin n) (h : a i = a j) (hij : i ≠ j) :
    exteriorAntisymmetrization k V n (exteriorPower.ιMulti k n a) = 0 := by
  rw [(exteriorPower.ιMulti k n).map_eq_zero_of_eq a h hij, map_zero]

/-- Permuting an original exterior input retains its actual integer permutation sign. -/
theorem exteriorAntisymmetrization_ιMulti_perm
    (n : ℕ) (a : Fin n → V) (π : Equiv.Perm (Fin n)) :
    exteriorAntisymmetrization k V n (exteriorPower.ιMulti k n (a ∘ π)) =
      Equiv.Perm.sign π • exteriorAntisymmetrization k V n (exteriorPower.ιMulti k n a) := by
  rw [(exteriorPower.ιMulti k n).map_perm a π]
  exact linearMap_sign_smul k (exteriorAntisymmetrization k V n) n π
    (exteriorPower.ιMulti k n a)

section UniversalAlternatingMap

variable {N : Type w} [AddCommGroup N] [Module k N]

/-- Evaluating an actual alternating tensor functional after antisymmetrization yields
exactly the factorial multiple of its exterior universal map. -/
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

/-- The actual tensor projection composed with antisymmetrization is `n!`, with no
characteristic, freeness, flatness or finiteness hypothesis on the coefficient module. -/
theorem exteriorProjection_comp_exteriorAntisymmetrization (n : ℕ) :
    (exteriorProjection k V n).comp (exteriorAntisymmetrization k V n) =
      n.factorial • (LinearMap.id : (⋀[k]^n V) →ₗ[k] (⋀[k]^n V)) := by
  simpa only [exteriorProjection, exteriorPower.alternatingMapLinearEquiv_ιMulti] using
    lift_alternating_comp_exteriorAntisymmetrization k V n (exteriorPower.ιMulti k n)

/-- The factorial law holds on every original exterior element. -/
theorem exteriorProjection_exteriorAntisymmetrization (n : ℕ) (x : ⋀[k]^n V) :
    exteriorProjection k V n (exteriorAntisymmetrization k V n x) = n.factorial • x :=
  DFunLike.congr_fun (exteriorProjection_comp_exteriorAntisymmetrization k V n) x

section Naturality

variable {W : Type w} [AddCommGroup W] [Module k W]

/-- Applying the original linear map to every tensor coordinate commutes with
the complete signed antisymmetrization. -/
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

/-- The original tensor-to-exterior projection is natural for arbitrary original
linear maps across independent carrier universes. -/
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

/-- In degree zero the original antisymmetric word is the original empty tensor unit. -/
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

/-- The actual degree-zero tensor and exterior units are identified. -/
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
