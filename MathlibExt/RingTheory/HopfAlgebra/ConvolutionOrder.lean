/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from:

`Theorems/Thm_HopfAlgebra_convPow_finrank_eq_one_of_isCocomm.lean`
and
`P2M/Sol/S_HopfAlgebra_convPow_finrank_eq_one_of_isCocomm.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.TensorProduct.Basic
import MathlibExt.Algebra.AlgebraicGroup.FunctorOfPoints
import MathlibExt.Algebra.Coalgebra.Convolution

open TensorProduct WithConv Coalgebra

universe u v w

namespace DeligneOrderKills

noncomputable section

section postComp

variable {R : Type*} [CommSemiring R] {C : Type*} [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {A A' : Type*} [Semiring A] [Algebra R A] [Semiring A'] [Algebra R A']

def postCompEquiv (g : A ≃ₐ[R] A') :
    WithConv (C →ₗ[R] A) ≃+* WithConv (C →ₗ[R] A') :=
  { (g : A →ₐ[R] A').convPostcomp with
    invFun := (g.symm : A' →ₐ[R] A).convPostcomp
    left_inv := fun F => by
      apply WithConv.ext; ext c; simp
    right_inv := fun F => by
      apply WithConv.ext; ext c; simp }

end postComp

section antipode

variable {R : Type*} [CommSemiring R] {H : Type*} [Semiring H] [HopfAlgebra R H]
variable {A : Type*} [Semiring A] [Algebra R A]

private lemma isUnit_toConv_toLinearMap (g : H →ₐ[R] A) : IsUnit (toConv g.toLinearMap) :=
  (isUnit_iff_exists.mpr ⟨_, LinearMap.id_mul_antipode, LinearMap.antipode_mul_id⟩ :
    IsUnit (toConv (LinearMap.id : H →ₗ[R] H))).map g.convPostcomp

end antipode

section Setup

variable {R : Type u} [CommRing R]
variable {H : Type v} [CommRing H] [HopfAlgebra R H]
variable {T : Type w} [CommRing T] [Algebra R T]

abbrev D (R : Type u) [CommRing R] (H : Type v) [CommRing H] [HopfAlgebra R H]
    (T : Type w) [CommRing T] [Algebra R T] : Type _ := WithConv (H →ₗ[R] T)

abbrev E (R : Type u) [CommRing R] (H : Type v) [CommRing H] [HopfAlgebra R H]
    (T : Type w) [CommRing T] [Algebra R T] : Type _ := WithConv (H →ₗ[R] T ⊗[R] H)

abbrev P (R : Type u) [CommRing R] (H : Type v) [CommRing H] [HopfAlgebra R H]
    (T : Type w) [CommRing T] [Algebra R T] : Type _ := WithConv (H →ₐ[R] T)

def ι : D R H T →+* E R H T :=
  (Algebra.TensorProduct.includeLeft : T →ₐ[R] T ⊗[R] H).convPostcomp.toRingHom

private def xE : E R H T :=
  toConv (Algebra.TensorProduct.includeRight : H →ₐ[R] T ⊗[R] H).toLinearMap

private lemma isUnit_xE : IsUnit (xE : E R H T) := isUnit_toConv_toLinearMap _

private def toD (u : P R H T) : D R H T := toConv u.ofConv.toLinearMap

private lemma toD_mul (u v : P R H T) :
    toD (u * v) = toD u * toD v := AlgHom.toLinearMap_convMul u v

private lemma toD_one : toD (1 : P R H T) = 1 := AlgHom.toLinearMap_convOne

private lemma toD_pow (u : P R H T) (n : ℕ) :
    toD (u ^ n) = toD u ^ n := AlgHom.toLinearMap_convPow u n

private lemma toD_injective : Function.Injective (toD : P R H T → D R H T) :=
  toConv_injective.comp (AlgHom.toLinearMap_injective.comp ofConv_injective)

private def uB (u : P R H T) : WithConv (H →ₐ[R] T ⊗[R] H) :=
  toConv ((Algebra.TensorProduct.includeLeft : T →ₐ[R] T ⊗[R] H).comp u.ofConv)

private def xB : WithConv (H →ₐ[R] T ⊗[R] H) :=
  toConv (Algebra.TensorProduct.includeRight : H →ₐ[R] T ⊗[R] H)

private def τ (u : P R H T) : H →ₐ[R] T ⊗[R] H := (xB * uB u).ofConv

private lemma toConv_τ_toLinearMap (u : P R H T) :
    toConv (τ u).toLinearMap = (xE : E R H T) * ι (toD u) := by
  rw [τ, toConv_ofConv, AlgHom.toLinearMap_convMul]
  rfl

private def tT (u : P R H T) : T ⊗[R] H →ₐ[T] T ⊗[R] H :=
  AlgHom.liftEquiv R T H (T ⊗[R] H) (τ u)

private lemma tT_tmul (u : P R H T) (s : T) (h : H) : tT u (s ⊗ₜ h) = s • τ u h := rfl

private lemma tT_comp_includeRight (u : P R H T) :
    ((tT u).restrictScalars R).comp Algebra.TensorProduct.includeRight = τ u := by
  ext h
  simp [tT_tmul]

private lemma tT_comp_includeLeft (u : P R H T) :
    ((tT u).restrictScalars R).comp
      (Algebra.TensorProduct.includeLeft : T →ₐ[R] T ⊗[R] H) =
      Algebra.TensorProduct.includeLeft := by
  ext s
  change tT u (algebraMap T (T ⊗[R] H) s) = algebraMap T (T ⊗[R] H) s
  exact (tT u).commutes s

private def Φ (u : P R H T) : E R H T →+* E R H T :=
  ((tT u).restrictScalars R).convPostcomp.toRingHom

private lemma Φ_ι (u : P R H T) (φ : D R H T) : Φ u (ι φ) = ι φ := by
  change ((tT u).restrictScalars R).convPostcomp
    ((Algebra.TensorProduct.includeLeft : T →ₐ[R] T ⊗[R] H).convPostcomp φ) = _
  rw [← AlgHom.comp_apply, ← AlgHom.convPostcomp_comp, tT_comp_includeLeft]
  rfl

private lemma Φ_xE (u : P R H T) : Φ u xE = (xE : E R H T) * ι (toD u) := by
  rw [← toConv_τ_toLinearMap, ← tT_comp_includeRight u]
  rfl

private lemma tT_comp_τ (u v : P R H T) : ((tT v).restrictScalars R).comp (τ u) = τ (v * u) := by
  apply AlgHom.toLinearMap_injective
  apply toConv_injective
  change Φ v (toConv (τ u).toLinearMap) = toConv (τ (v * u)).toLinearMap
  rw [toConv_τ_toLinearMap, toConv_τ_toLinearMap, map_mul, Φ_xE, Φ_ι, toD_mul, map_mul, mul_assoc]

private lemma tT_comp_tT (u v : P R H T) : (tT v).comp (tT u) = tT (v * u) := by
  apply Algebra.TensorProduct.ext_ring
  rw [tT_comp_includeRight (v * u), ← tT_comp_τ u v, ← tT_comp_includeRight u]
  ext h
  rfl

private lemma τ_one : τ (1 : P R H T) = Algebra.TensorProduct.includeRight := by
  apply AlgHom.toLinearMap_injective
  apply toConv_injective
  rw [toConv_τ_toLinearMap, toD_one, map_one, mul_one]
  rfl

private lemma tT_one : tT (1 : P R H T) = AlgHom.id T (T ⊗[R] H) := by
  apply Algebra.TensorProduct.ext_ring
  rw [tT_comp_includeRight, τ_one]
  rfl

private def tTEquiv (u : P R H T) : T ⊗[R] H ≃ₐ[T] T ⊗[R] H :=
  AlgEquiv.ofAlgHom (tT u) (tT u⁻¹)
    (by rw [tT_comp_tT, mul_inv_cancel, tT_one])
    (by rw [tT_comp_tT, inv_mul_cancel, tT_one])

end Setup

section Norm

variable {R : Type u} [CommRing R]
variable {H : Type v} [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
variable {T : Type w} [CommRing T] [Algebra R T]

@[reducible] def algebraDE : Algebra (D R H T) (E R H T) :=
  (ι : D R H T →+* E R H T).toAlgebra' fun c F => by exact mul_comm (ι c) F

attribute [local instance] algebraDE

private lemma algebraMap_eq : algebraMap (D R H T) (E R H T) = ι := rfl

private def ΦEquiv (u : P R H T) : E R H T ≃ₐ[D R H T] E R H T :=
  { postCompEquiv ((tTEquiv u).restrictScalars R) with
    commutes' := fun φ => Φ_ι u φ }

private lemma ΦEquiv_apply (u : P R H T) (F : E R H T) : ΦEquiv u F = Φ u F := rfl

section basis

variable {ι₀ : Type*} [Fintype ι₀] (b : Module.Basis ι₀ R H)

private abbrev bT : Module.Basis ι₀ T (T ⊗[R] H) := b.baseChange T

private def coordEquiv : E R H T ≃ₗ[D R H T] (ι₀ → D R H T) :=
  { (bT (T := T) b).convCoordEquiv R H with
    map_smul' := fun φ F => funext fun i =>
      (bT (T := T) b).convCoordEquiv_convPostcomp_mul φ F i }

private def basisDE : Module.Basis ι₀ (D R H T) (E R H T) :=
  Module.Basis.ofEquivFun (coordEquiv b)

end basis

variable [Module.Finite R H] [Module.Free R H]

private theorem toD_pow_card_eq_one (u : P R H T) :
    toD u ^ Fintype.card (Module.Free.ChooseBasisIndex R H) = 1 := by
  classical
  set b := Module.Free.chooseBasis R H
  have hN : Algebra.norm (D R H T) (ΦEquiv u (xE : E R H T)) =
      Algebra.norm (D R H T) (xE : E R H T) :=
    Algebra.norm_eq_of_algEquiv (ΦEquiv u) xE
  rw [ΦEquiv_apply, Φ_xE, map_mul, ← algebraMap_eq,
    Algebra.norm_algebraMap_of_basis (basisDE (T := T) b)] at hN
  have hu : IsUnit (Algebra.norm (D R H T) (xE : E R H T)) := (isUnit_xE).map _
  exact hu.mul_right_injective (hN.trans (mul_one _).symm)

private theorem convPow_finrank_eq_one (u : P R H T) : u ^ Module.finrank R H = 1 := by
  cases subsingleton_or_nontrivial R with
  | inl h =>
    have : Subsingleton T := (algebraMap R T).codomain_trivial
    have : Subsingleton (H →ₐ[R] T) := ⟨fun f g => AlgHom.ext fun _ => Subsingleton.elim _ _⟩
    have : Subsingleton (P R H T) := ⟨fun f g => WithConv.ext (Subsingleton.elim _ _)⟩
    exact Subsingleton.elim _ _
  | inr h =>
    apply toD_injective
    rw [toD_pow, toD_one, Module.finrank_eq_card_chooseBasisIndex]
    exact toD_pow_card_eq_one u

end Norm

end

end DeligneOrderKills

namespace HopfAlgebra

/-- **Points of a finite free commutative and cocommutative Hopf algebra are killed by its rank.**
Let `R` be a commutative ring, `H` a commutative and cocommutative Hopf algebra over `R` that is
finite and free of rank `n` as an `R`-module, and `T` a commutative `R`-algebra. Every
`R`-algebra homomorphism `f : H →ₐ[R] T`, viewed in the convolution monoid, satisfies
`f ^ n = 1`, where `1` is the convolution unit: the counit of `H` followed by `algebraMap R T`. -/
public theorem convPow_finrank_eq_one_of_isCocomm
    (R : Type u) [CommRing R]
    (H : Type v) [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
    [Module.Finite R H] [Module.Free R H]
    (T : Type w) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)) :
    f ^ Module.finrank R H = 1 :=
  DeligneOrderKills.convPow_finrank_eq_one f

end HopfAlgebra
