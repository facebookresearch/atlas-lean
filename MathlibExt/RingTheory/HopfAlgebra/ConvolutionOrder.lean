/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_HopfAlgebra_convPow_finrank_eq_one_of_isCocomm.lean`
and
`P2M/Sol/S_HopfAlgebra_convPow_finrank_eq_one_of_isCocomm.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.Coalgebra.Convolution
public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.Algebra.Operations
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.RingTheory.Norm.Defs

@[expose] public section

open TensorProduct WithConv Coalgebra

universe u v w

namespace DeligneOrderKills

noncomputable section

section postComp

variable {R : Type*} [CommSemiring R] {C : Type*} [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {A A' A'' : Type*} [Semiring A] [Algebra R A] [Semiring A'] [Algebra R A']
  [Semiring A''] [Algebra R A'']

def postComp (g : A →ₐ[R] A') : WithConv (C →ₗ[R] A) →+* WithConv (C →ₗ[R] A') where
  toFun F := toConv (g.toLinearMap ∘ₗ F.ofConv)
  map_one' := by
    apply WithConv.ext
    ext c
    simp [LinearMap.convOne_def]
  map_mul' F G := by
    apply WithConv.ext
    simpa using LinearMap.algHom_comp_convMul_distrib g F G
  map_zero' := by
    apply WithConv.ext
    simp
  map_add' F G := by
    apply WithConv.ext
    simp [LinearMap.comp_add]

@[scoped simp] lemma postComp_apply (g : A →ₐ[R] A') (F : WithConv (C →ₗ[R] A)) :
    postComp g F = toConv (g.toLinearMap ∘ₗ F.ofConv) := rfl

private lemma postComp_comp (g : A →ₐ[R] A') (g' : A' →ₐ[R] A'') (F : WithConv (C →ₗ[R] A)) :
    postComp g' (postComp g F) = postComp (g'.comp g) F := rfl

def postCompEquiv (g : A ≃ₐ[R] A') :
    WithConv (C →ₗ[R] A) ≃+* WithConv (C →ₗ[R] A') :=
  { postComp (g : A →ₐ[R] A') with
    invFun := postComp (g.symm : A' →ₐ[R] A)
    left_inv := fun F => by
      apply WithConv.ext; ext c; simp
    right_inv := fun F => by
      apply WithConv.ext; ext c; simp }

end postComp

section antipode

variable {R : Type*} [CommSemiring R] {H : Type*} [Semiring H] [HopfAlgebra R H]

private lemma id_convMul_antipode :
    toConv (LinearMap.id : H →ₗ[R] H) * toConv (HopfAlgebra.antipode R) = 1 := by
  apply WithConv.ext
  change LinearMap.mul' R H ∘ₗ TensorProduct.map LinearMap.id (HopfAlgebra.antipode R) ∘ₗ comul = _
  exact HopfAlgebra.mul_antipode_lTensor_comul

private lemma antipode_convMul_id :
    toConv (HopfAlgebra.antipode R) * toConv (LinearMap.id : H →ₗ[R] H) = 1 := by
  apply WithConv.ext
  change LinearMap.mul' R H ∘ₗ TensorProduct.map (HopfAlgebra.antipode R) LinearMap.id ∘ₗ comul = _
  exact HopfAlgebra.mul_antipode_rTensor_comul

variable {A : Type*} [Semiring A] [Algebra R A]

private lemma toLinearMap_convMul_comp_antipode (g : H →ₐ[R] A) :
    toConv g.toLinearMap * toConv (g.toLinearMap ∘ₗ HopfAlgebra.antipode R) = 1 := by
  have h1 : postComp g (toConv (LinearMap.id : H →ₗ[R] H)) = toConv g.toLinearMap := rfl
  have h2 : postComp g (toConv (HopfAlgebra.antipode R)) =
      toConv (g.toLinearMap ∘ₗ HopfAlgebra.antipode R) := rfl
  rw [← h1, ← h2, ← map_mul, id_convMul_antipode, map_one]

private lemma comp_antipode_convMul_toLinearMap (g : H →ₐ[R] A) :
    toConv (g.toLinearMap ∘ₗ HopfAlgebra.antipode R) * toConv g.toLinearMap = 1 := by
  have h1 : postComp g (toConv (LinearMap.id : H →ₗ[R] H)) = toConv g.toLinearMap := rfl
  have h2 : postComp g (toConv (HopfAlgebra.antipode R)) =
      toConv (g.toLinearMap ∘ₗ HopfAlgebra.antipode R) := rfl
  rw [← h1, ← h2, ← map_mul, antipode_convMul_id, map_one]

private lemma isUnit_toConv_toLinearMap (g : H →ₐ[R] A) : IsUnit (toConv g.toLinearMap) :=
  isUnit_iff_exists.mpr
    ⟨_, toLinearMap_convMul_comp_antipode g, comp_antipode_convMul_toLinearMap g⟩

end antipode

section commAntipode

variable {R : Type*} [CommSemiring R] {H : Type*} [CommSemiring H] [HopfAlgebra R H]

private def antipodeAlgHom : H →ₐ[R] H :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode R) HopfAlgebra.antipode_one fun a b => by
    rw [HopfAlgebra.antipode_mul, mul_comm]

variable {A : Type*} [CommSemiring A] [Algebra R A]

private lemma point_mul_comp_antipode (g : WithConv (H →ₐ[R] A)) :
    g * toConv (g.ofConv.comp antipodeAlgHom) = 1 := by
  apply toConv_injective.comp (AlgHom.toLinearMap_injective.comp ofConv_injective)
  change toConv (g * toConv (g.ofConv.comp antipodeAlgHom)).ofConv.toLinearMap =
    toConv (1 : WithConv (H →ₐ[R] A)).ofConv.toLinearMap
  rw [AlgHom.toLinearMap_convMul, AlgHom.toLinearMap_convOne]
  exact toLinearMap_convMul_comp_antipode g.ofConv

private lemma comp_antipode_mul_point (g : WithConv (H →ₐ[R] A)) :
    toConv (g.ofConv.comp antipodeAlgHom) * g = 1 := by
  apply toConv_injective.comp (AlgHom.toLinearMap_injective.comp ofConv_injective)
  change toConv (toConv (g.ofConv.comp antipodeAlgHom) * g).ofConv.toLinearMap =
    toConv (1 : WithConv (H →ₐ[R] A)).ofConv.toLinearMap
  rw [AlgHom.toLinearMap_convMul, AlgHom.toLinearMap_convOne]
  exact comp_antipode_convMul_toLinearMap g.ofConv

end commAntipode

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
  postComp (Algebra.TensorProduct.includeLeft : T →ₐ[R] T ⊗[R] H)

private lemma ι_apply_apply (φ : D R H T) (h : H) : (ι φ) h = φ h ⊗ₜ (1 : H) := rfl

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

private def Φ (u : P R H T) : E R H T →+* E R H T := postComp ((tT u).restrictScalars R)

private lemma Φ_ι (u : P R H T) (φ : D R H T) : Φ u (ι φ) = ι φ := by
  change postComp _ (postComp _ φ) = _
  rw [postComp_comp, tT_comp_includeLeft]
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

private def inv (u : P R H T) : P R H T := toConv (u.ofConv.comp antipodeAlgHom)

private lemma mul_inv (u : P R H T) : u * inv u = 1 := point_mul_comp_antipode u

private lemma inv_mul (u : P R H T) : inv u * u = 1 := comp_antipode_mul_point u

private def tTEquiv (u : P R H T) : T ⊗[R] H ≃ₐ[T] T ⊗[R] H :=
  AlgEquiv.ofAlgHom (tT u) (tT (inv u))
    (by rw [tT_comp_tT, mul_inv, tT_one])
    (by rw [tT_comp_tT, inv_mul, tT_one])

end Setup

section Norm

variable {R : Type u} [CommRing R]
variable {H : Type v} [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
variable {T : Type w} [CommRing T] [Algebra R T]

@[reducible] def algebraDE : Algebra (D R H T) (E R H T) :=
  (ι : D R H T →+* E R H T).toAlgebra' fun c F => by exact mul_comm (ι c) F

attribute [local instance] algebraDE

private lemma algebraMap_eq : algebraMap (D R H T) (E R H T) = ι := rfl

private lemma smul_def' (φ : D R H T) (F : E R H T) : φ • F = ι φ * F := rfl

private lemma smul_apply (φ : D R H T) (F : E R H T) (h : H) :
    (φ • F) h = ∑ i ∈ (ℛ R h).index, φ ((ℛ R h).left i) • F ((ℛ R h).right i) := by
  rw [smul_def', Coalgebra.Repr.convMul_apply (ℛ R h)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ι_apply_apply, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply]


private def ΦEquiv (u : P R H T) : E R H T ≃ₐ[D R H T] E R H T :=
  { postCompEquiv ((tTEquiv u).restrictScalars R) with
    commutes' := fun φ => Φ_ι u φ }

private lemma ΦEquiv_apply (u : P R H T) (F : E R H T) : ΦEquiv u F = Φ u F := rfl

section basis

variable {ι₀ : Type*} [Fintype ι₀] (b : Module.Basis ι₀ R H)

private abbrev bT : Module.Basis ι₀ T (T ⊗[R] H) := b.baseChange T

private def coordFun (F : E R H T) (i : ι₀) : D R H T :=
  toConv (((bT (T := T) b).coord i).restrictScalars R ∘ₗ F.ofConv)

omit [IsCocomm R H] [Fintype ι₀] in
private lemma coordFun_apply (F : E R H T) (i : ι₀) (h : H) :
    coordFun b F i h = (bT (T := T) b).coord i (F h) := rfl

private def ofCoordFun (g : ι₀ → D R H T) : E R H T :=
  toConv (∑ i, (LinearMap.toSpanSingleton T (T ⊗[R] H) (bT (T := T) b i)).restrictScalars R ∘ₗ
    (g i).ofConv)

omit [IsCocomm R H] in
private lemma ofCoordFun_apply (g : ι₀ → D R H T) (h : H) :
    ofCoordFun b g h = ∑ i, (g i) h • bT (T := T) b i := by
  simp [ofCoordFun, LinearMap.sum_apply]

private def coordEquiv : E R H T ≃ₗ[D R H T] (ι₀ → D R H T) where
  toFun := coordFun b
  invFun := ofCoordFun b
  map_add' F G := by
    ext i : 1
    apply WithConv.ext; ext h
    simp [coordFun_apply]
  map_smul' φ F := by
    ext i : 1
    apply WithConv.ext; ext h
    rw [coordFun_apply, smul_apply, map_sum, RingHom.id_apply, Pi.smul_apply, smul_eq_mul,
      Coalgebra.Repr.convMul_apply (ℛ R h)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_smul, coordFun_apply, smul_eq_mul]
  left_inv F := by
    apply WithConv.ext; ext h
    rw [ofCoordFun_apply]
    simp only [coordFun_apply, Module.Basis.coord_apply]
    exact (bT (T := T) b).sum_repr (F h)
  right_inv g := by
    ext i : 1
    apply WithConv.ext; ext h
    rw [coordFun_apply, ofCoordFun_apply, Module.Basis.coord_apply]
    rw [(bT (T := T) b).repr_sum_self]

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
    haveI : Subsingleton (H →ₐ[R] T) := ⟨fun f g => AlgHom.ext fun _ => Subsingleton.elim _ _⟩
    haveI : Subsingleton (P R H T) := ⟨fun f g => WithConv.ext (Subsingleton.elim _ _)⟩
    exact Subsingleton.elim _ _
  | inr h =>
    apply toD_injective
    rw [toD_pow, toD_one, Module.finrank_eq_card_chooseBasisIndex]
    exact toD_pow_card_eq_one u

end Norm

end

end DeligneOrderKills

namespace HopfAlgebra

/-- For a finite free cocommutative Hopf algebra `H` of rank `n` over a
commutative ring `R`, every `R`-algebra point of `H`, viewed in the
convolution algebra, satisfies `f ^ n = 1`. -/
public theorem convPow_finrank_eq_one_of_isCocomm
    (R : Type u) [CommRing R]
    (H : Type v) [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
    [Module.Finite R H] [Module.Free R H]
    (T : Type w) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)) :
    f ^ Module.finrank R H = 1 :=
  DeligneOrderKills.convPow_finrank_eq_one f

end HopfAlgebra
