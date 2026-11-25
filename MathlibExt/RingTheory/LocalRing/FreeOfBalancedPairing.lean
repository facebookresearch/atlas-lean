/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Module_free_of_torsionBySet_eq_annihilator_smul.lean` and
`P2M/Sol/S_Module_free_of_torsionBySet_eq_annihilator_smul.lean`
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

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Freeness from a balanced perfect pairing and a saturated torsion submodule

Let `𝒪` be a principal ideal domain and `T` a local `𝒪`-algebra that is finite
free over `𝒪`, with an augmentation `πT : T →ₐ[𝒪] 𝒪` whose congruence ideal
`πT (Ann (ker πT))` is nonzero, and with a perfect `T`-balanced `𝒪`-pairing on `T`.
Let `M` be a finite free `𝒪`-module with a compatible `T`-action and a perfect
`T`-balanced `𝒪`-pairing. If the `ker πT`-torsion submodule `M[ker πT]` equals
`Ann (ker πT) • M` and `rank M = rank M[ker πT] * rank T`, then `M` is free over `T`.

This is the freeness step of the numerical criterion for a surjection of
complete local `𝒪`-algebras.
-/

@[expose] public section

namespace Module.FreeOfBalancedPairing

open Module Submodule Pointwise

section Ring

variable {𝒪 : Type*} {T : Type*} [CommRing 𝒪] [CommRing T] [Algebra 𝒪 T] (πT : T →ₐ[𝒪] 𝒪)

private theorem πT_surjective : Function.Surjective πT :=
  fun c => ⟨algebraMap 𝒪 T c, πT.commutes c⟩

private theorem sub_algebraMap_mem_ker (t : T) : t - algebraMap 𝒪 T (πT t) ∈ RingHom.ker πT := by
  simp [RingHom.mem_ker]

private theorem mul_eq_zero_of_mem_annihilator {i a : T} (hi : i ∈ (RingHom.ker πT).annihilator)
    (ha : a ∈ RingHom.ker πT) : i * a = 0 := by
  rw [Submodule.mem_annihilator] at hi
  simpa [smul_eq_mul] using hi a ha

private theorem mul_eq_smul_of_mem_annihilator {x₀ : T} (hx₀ : x₀ ∈ (RingHom.ker πT).annihilator)
    (t : T) : t * x₀ = πT t • x₀ :=
  calc t * x₀ = (t - algebraMap 𝒪 T (πT t)) * x₀ + algebraMap 𝒪 T (πT t) * x₀ := by ring
    _ = πT t • x₀ := by
        rw [mul_comm, mul_eq_zero_of_mem_annihilator πT hx₀ (sub_algebraMap_mem_ker πT t),
          zero_add, Algebra.smul_def]

private theorem pairing_apply_x₀ (C : T →ₗ[𝒪] T →ₗ[𝒪] 𝒪)
    (hC : ∀ s t u : T, C (s * t) u = C t (s * u))
    {x₀ : T} (hx₀ : x₀ ∈ (RingHom.ker πT).annihilator) (t : T) : C t x₀ = πT t * C 1 x₀ := by
  have h := hC t 1 x₀
  rw [mul_one] at h
  rw [h, mul_eq_smul_of_mem_annihilator πT hx₀ t, map_smul, smul_eq_mul]

section F1

variable [IsDomain 𝒪] [Module.Free 𝒪 T]

private theorem exists_eq_smul_of_mem_annihilator {e₀ : 𝒪} (he₀ : e₀ ≠ 0)
    (hη : (RingHom.ker πT).annihilator.map πT = Ideal.span ({e₀} : Set 𝒪))
    {x₀ : T} (hx₀ : x₀ ∈ (RingHom.ker πT).annihilator) (hπx₀ : πT x₀ = e₀)
    {i : T} (hi : i ∈ (RingHom.ker πT).annihilator) : ∃ c : 𝒪, i = c • x₀ := by
  have hπi : πT i ∈ Ideal.span ({e₀} : Set 𝒪) := hη ▸ Ideal.mem_map_of_mem πT hi
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hπi
  refine ⟨c, ?_⟩
  set y := i - c • x₀ with hy
  have hyI : y ∈ (RingHom.ker πT).annihilator :=
    Submodule.sub_mem _ hi (Submodule.smul_of_tower_mem _ c hx₀)
  have hy℘ : y ∈ RingHom.ker πT := by
    rw [RingHom.mem_ker, hy, map_sub, map_smul, hπx₀, ← hc, smul_eq_mul, sub_self]
  have hey : e₀ • y = 0 := by
    have h1 : (algebraMap 𝒪 T e₀ - x₀) * y = 0 := by
      rw [mul_comm]
      refine mul_eq_zero_of_mem_annihilator πT hyI ?_
      have := Submodule.neg_mem _ (sub_algebraMap_mem_ker πT x₀)
      rwa [hπx₀, neg_sub] at this
    have h2 : x₀ * y = 0 := mul_eq_zero_of_mem_annihilator πT hx₀ hy℘
    calc e₀ • y = (algebraMap 𝒪 T e₀ - x₀) * y + x₀ * y := by rw [Algebra.smul_def]; ring
      _ = 0 := by rw [h1, h2, add_zero]
  have : y = 0 := (smul_eq_zero_iff_right he₀).mp hey
  rwa [hy, sub_eq_zero] at this

private theorem isUnit_pairing_one_x₀
    (C : T →ₗ[𝒪] T →ₗ[𝒪] 𝒪) (hC : ∀ s t u : T, C (s * t) u = C t (s * u))
    (hCb : Function.Bijective C) {e₀ : 𝒪} (he₀ : e₀ ≠ 0)
    (hη : (RingHom.ker πT).annihilator.map πT = Ideal.span ({e₀} : Set 𝒪))
    {x₀ : T} (hx₀ : x₀ ∈ (RingHom.ker πT).annihilator) (hπx₀ : πT x₀ = e₀) :
    IsUnit (C 1 x₀) := by
  obtain ⟨t₁, ht₁⟩ := hCb.2 πT.toLinearMap
  have ht₁I : t₁ ∈ (RingHom.ker πT).annihilator := by
    rw [Submodule.mem_annihilator]
    intro p hp
    apply hCb.1
    rw [map_zero]
    ext u
    rw [smul_eq_mul, mul_comm, hC, ht₁, LinearMap.zero_apply, AlgHom.toLinearMap_apply, map_mul,
      RingHom.mem_ker.mp hp, zero_mul]
  obtain ⟨c, hc⟩ := exists_eq_smul_of_mem_annihilator πT he₀ hη hx₀ hπx₀ ht₁I
  have h1 : C t₁ 1 = 1 := by rw [ht₁, AlgHom.toLinearMap_apply, map_one]
  have h2 : C x₀ 1 = C 1 x₀ := by
    have := hC x₀ 1 1
    rwa [mul_one] at this
  rw [hc, map_smul, LinearMap.smul_apply, smul_eq_mul, h2] at h1
  exact IsUnit.of_mul_eq_one c (by rw [mul_comm]; exact h1)

end F1

end Ring

section ModuleFacts

variable {𝒪 : Type*} {T : Type*} [CommRing 𝒪] [CommRing T] [Algebra 𝒪 T] (πT : T →ₐ[𝒪] 𝒪)
  {M : Type*} [AddCommGroup M] [Module T M]

private theorem x₀_smul_mem {x₀ : T} (hx₀ : x₀ ∈ (RingHom.ker πT).annihilator) (m : M) :
    x₀ • m ∈ Submodule.torsionBySet T M ↑(RingHom.ker πT) := by
  rw [Submodule.mem_torsionBySet_iff]
  rintro ⟨a, ha⟩
  change a • x₀ • m = 0
  rw [smul_smul, mul_comm, mul_eq_zero_of_mem_annihilator πT hx₀ ha, zero_smul]

private theorem x₀_smul_smul_eq_zero {x₀ : T} (hx₀ : x₀ ∈ (RingHom.ker πT).annihilator) {a : T}
    (ha : a ∈ RingHom.ker πT) (m : M) : x₀ • a • m = 0 := by
  rw [smul_smul, mul_eq_zero_of_mem_annihilator πT hx₀ ha, zero_smul]

variable [Module 𝒪 M] [IsScalarTower 𝒪 T M]

private theorem x₀_smul_eq {e₀ : 𝒪} {x₀ : T} (hπx₀ : πT x₀ = e₀) {n : M}
    (hn : n ∈ Submodule.torsionBySet T M ↑(RingHom.ker πT)) : x₀ • n = e₀ • n := by
  rw [Submodule.mem_torsionBySet_iff] at hn
  have h : (x₀ - algebraMap 𝒪 T (πT x₀)) • n = 0 := hn ⟨_, sub_algebraMap_mem_ker πT x₀⟩
  rw [hπx₀, sub_smul, sub_eq_zero, algebraMap_smul] at h
  exact h

private theorem pairing_eq_zero [IsDomain 𝒪] (B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪)
    (hB : ∀ (t : T) (m n : M), B (t • m) n = B m (t • n))
    {e₀ : 𝒪} (he₀ : e₀ ≠ 0) {x₀ : T} (hπx₀ : πT x₀ = e₀)
    {n : M} (hn : n ∈ Submodule.torsionBySet T M ↑(RingHom.ker πT)) {m : M} (hm : x₀ • m = 0) :
    B n m = 0 := by
  have h : e₀ * B n m = 0 := by
    rw [← smul_eq_mul, ← LinearMap.smul_apply, ← LinearMap.map_smul, ← x₀_smul_eq πT hπx₀ hn,
      hB, hm, map_zero]
  exact (mul_eq_zero.mp h).resolve_left he₀

end ModuleFacts

section Main

variable {𝒪 : Type*} {T : Type*} [CommRing 𝒪] [CommRing T] [Algebra 𝒪 T] (πT : T →ₐ[𝒪] 𝒪)
  {M : Type*} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]

local notation "P℘" =>
  Submodule.restrictScalars 𝒪 (Submodule.torsionBySet T M (RingHom.ker πT : Set T))

private theorem core [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪] [IsLocalRing T] [Module.Finite 𝒪 T]
    [Module.Free 𝒪 T] [Module.Finite 𝒪 M] [Module.Free 𝒪 M]
    (C : T →ₗ[𝒪] T →ₗ[𝒪] 𝒪) (hC : ∀ s t u : T, C (s * t) u = C t (s * u))
    (hCb : Function.Bijective C)
    (B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪) (hB : ∀ (t : T) (m n : M), B (t • m) n = B m (t • n))
    (hBb : Function.Bijective B)
    {e₀ : 𝒪} (he₀ : e₀ ≠ 0)
    (hη : (RingHom.ker πT).annihilator.map πT = Ideal.span ({e₀} : Set 𝒪))
    {x₀ : T} (hx₀ : x₀ ∈ (RingHom.ker πT).annihilator) (hπx₀ : πT x₀ = e₀)
    {d : ℕ} (m : Fin d → M)
    (bP : Basis (Fin d) 𝒪 P℘)
    (hbP : ∀ j, (bP j : M) = x₀ • m j)
    (hrank : Module.finrank 𝒪 M = d * Module.finrank 𝒪 T) :
    Module.Free T M := by
  classical
  have c₀unit : IsUnit (C 1 x₀) := isUnit_pairing_one_x₀ πT C hC hCb he₀ hη hx₀ hπx₀
  obtain ⟨cinv, hcinv⟩ := c₀unit.exists_right_inv
  have hcinv' : IsUnit cinv := IsUnit.of_mul_eq_one (C 1 x₀) (by rw [mul_comm]; exact hcinv)
  have hCx₀ : ∀ t, C t x₀ = πT t * C 1 x₀ := pairing_apply_x₀ πT C hC hx₀
  let τ : Fin d → (T →ₗ[𝒪] M) := fun i =>
    { toFun := fun u => u • m i
      map_add' := fun a b => add_smul a b (m i)
      map_smul' := fun c a => by simp [smul_assoc] }
  have hτ : ∀ i u, τ i u = u • m i := fun _ _ => rfl
  let Ce : T ≃ₗ[𝒪] (T →ₗ[𝒪] 𝒪) := LinearEquiv.ofBijective C hCb
  have hCe : ∀ t, Ce t = C t := fun _ => rfl
  let Bτ : Fin d → (M →ₗ[𝒪] (T →ₗ[𝒪] 𝒪)) := fun i =>
    { toFun := fun m' => (B m').comp (τ i)
      map_add' := fun a b => by simp only [map_add, LinearMap.add_comp]
      map_smul' := fun c a => by simp only [map_smul, LinearMap.smul_comp, RingHom.id_apply] }
  let A𝒪 : M →ₗ[𝒪] (Fin d → T) := LinearMap.pi fun i => Ce.symm.toLinearMap.comp (Bτ i)
  have hA : ∀ m' i u, C (A𝒪 m' i) u = B m' (u • m i) := by
    intro m' i u
    have h1 : A𝒪 m' i = Ce.symm ((B m').comp (τ i)) := rfl
    rw [h1, ← hCe, LinearEquiv.apply_symm_apply, LinearMap.comp_apply, hτ]
  have hAT : ∀ (s : T) (m' : M), A𝒪 (s • m') = s • A𝒪 m' := by
    intro s m'
    funext i
    apply hCb.1
    ext u
    rw [hA, hB, smul_smul, Pi.smul_apply, smul_eq_mul, hC, hA]
  let A : M →ₗ[T] (Fin d → T) :=
    { toFun := A𝒪
      map_add' := A𝒪.map_add
      map_smul' := hAT }
  let e : (Fin d → T) →ₗ[T] M := Fintype.linearCombination T m
  have he_single : ∀ j, e (Pi.single j 1) = m j := by
    intro j
    change Fintype.linearCombination T m (Pi.single j 1) = m j
    rw [Fintype.linearCombination_apply_single, one_smul]
  let G : (Fin d → T) →ₗ[T] (Fin d → T) := A.comp e
  set Gm : Matrix (Fin d) (Fin d) T := LinearMap.toMatrix' G with hGmdef
  have hGm : ∀ i j, Gm i j = A𝒪 (m j) i := by
    intro i j
    rw [hGmdef, LinearMap.toMatrix'_apply, LinearMap.comp_apply, he_single]
    rfl
  have hred : ∀ i j, πT (Gm i j) * C 1 x₀ = B (x₀ • m j) (m i) := by
    intro i j
    rw [hGm, ← hCx₀ (A𝒪 (m j) i), hA, ← hB]
  let Φ : P℘ →ₗ[𝒪] (Fin d → 𝒪) :=
    { toFun := fun n i => B (n : M) (m i)
      map_add' := fun a b => by
        funext i
        simp only [Submodule.coe_add, map_add, LinearMap.add_apply, Pi.add_apply]
      map_smul' := fun c a => by
        funext i
        simp only [Submodule.coe_smul, map_smul, LinearMap.smul_apply, Pi.smul_apply,
          RingHom.id_apply] }
  have hΦ : ∀ (n : P℘) i, Φ n i = B (n : M) (m i) := fun _ _ => rfl
  have hdecomp : ∀ m' : M, ∃ c : Fin d → 𝒪, x₀ • (m' - ∑ j, c j • m j) = 0 := by
    intro m'
    have hmem : x₀ • m' ∈ P℘ := x₀_smul_mem πT hx₀ m'
    refine ⟨bP.repr ⟨x₀ • m', hmem⟩, ?_⟩
    have hsum := congrArg Subtype.val (bP.sum_repr ⟨x₀ • m', hmem⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, hbP] at hsum
    rw [smul_sub, Finset.smul_sum, sub_eq_zero]
    conv_lhs => rw [← hsum]
    exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
  have hΦinj : Function.Injective Φ := by
    intro n n' h
    have hsub : Φ (n - n') = 0 := by rw [map_sub, h, sub_self]
    have hBn : B ((n - n' : P℘) : M) = 0 := by
      ext m'
      obtain ⟨c, hc⟩ := hdecomp m'
      have h0 := pairing_eq_zero πT B hB he₀ hπx₀ (n - n').2 hc
      rw [map_sub, sub_eq_zero] at h0
      rw [LinearMap.zero_apply, h0, map_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hj : Φ (n - n') j = 0 := by rw [hsub]; rfl
      rw [hΦ] at hj
      rw [map_smul, smul_eq_mul, hj, mul_zero]
    have : ((n - n' : P℘) : M) = 0 := hBb.1 (by rw [hBn, map_zero])
    rwa [Submodule.coe_eq_zero, sub_eq_zero] at this
  let μ : M →ₗ[𝒪] M :=
    { toFun := fun m' => x₀ • m'
      map_add' := fun a b => smul_add x₀ a b
      map_smul' := fun c a => by simp [smul_comm x₀ c a] }
  have hμP : ∀ m', μ m' ∈ P℘ := fun m' => x₀_smul_mem πT hx₀ m'
  let μ' : M →ₗ[𝒪] P℘ := LinearMap.codRestrict P℘ μ hμP
  have hμ' : ∀ m', (μ' m' : M) = x₀ • m' := fun _ => rfl
  have hΦsurj : Function.Surjective Φ := by
    intro c
    let F : M →ₗ[𝒪] 𝒪 :=
      (Fintype.linearCombination 𝒪 c).comp (bP.equivFun.toLinearMap.comp μ')
    have hF : ∀ m', F m' = ∑ i, bP.equivFun (μ' m') i • c i := fun _ => rfl
    obtain ⟨n, hn⟩ := hBb.2 F
    have hnP : n ∈ P℘ := by
      rw [Submodule.restrictScalars_mem, Submodule.mem_torsionBySet_iff]
      rintro ⟨a, ha⟩
      apply hBb.1
      rw [map_zero]
      ext m'
      change B (a • n) m' = 0
      have hμa : μ' (a • m') = 0 := Subtype.ext (x₀_smul_smul_eq_zero πT hx₀ ha m')
      rw [hB, hn, hF]
      simp [hμa]
    refine ⟨⟨n, hnP⟩, ?_⟩
    funext i
    rw [hΦ]
    change B n (m i) = c i
    have hμi : μ' (m i) = bP i := Subtype.ext (by rw [hμ', hbP])
    rw [hn, hF, hμi]
    simp [Basis.equivFun_self, Finset.sum_ite_eq]
  let ΦE : P℘ ≃ₗ[𝒪] (Fin d → 𝒪) := LinearEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩
  have hΓunit : IsUnit (LinearMap.toMatrix bP (Pi.basisFun 𝒪 (Fin d))
      (ΦE : P℘ →ₗ[𝒪] (Fin d → 𝒪))).det :=
    LinearEquiv.isUnit_det ΦE bP (Pi.basisFun 𝒪 (Fin d))
  have hΓij : ∀ i j, LinearMap.toMatrix bP (Pi.basisFun 𝒪 (Fin d))
      (ΦE : P℘ →ₗ[𝒪] (Fin d → 𝒪)) i j = B (x₀ • m j) (m i) := by
    intro i j
    rw [LinearMap.toMatrix_apply, Pi.basisFun_repr, ← hbP]
    rfl
  have hGbar : (πT : T →+* 𝒪).mapMatrix Gm =
      cinv • LinearMap.toMatrix bP (Pi.basisFun 𝒪 (Fin d)) (ΦE : P℘ →ₗ[𝒪] (Fin d → 𝒪)) := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hΓij,
      ← hred i j, RingHom.coe_coe, mul_comm cinv, mul_assoc, hcinv, mul_one]
  have hdetbar : IsUnit ((πT : T →+* 𝒪).mapMatrix Gm).det := by
    rw [hGbar, Matrix.det_smul]
    exact (hcinv'.pow _).mul hΓunit
  have hdetG : IsUnit Gm.det := by
    have := IsLocalHom.of_surjective (πT : T →+* 𝒪) (πT_surjective πT)
    refine IsUnit.of_map (πT : T →+* 𝒪) _ ?_
    rw [RingHom.map_det]
    exact hdetbar
  let Gequiv : (Fin d → T) ≃ₗ[T] (Fin d → T) :=
    LinearEquiv.ofIsUnitDet (f := G) (v := Pi.basisFun T (Fin d)) (v' := Pi.basisFun T (Fin d))
      (by rw [LinearMap.toMatrix_eq_toMatrix']; exact hdetG)
  have hGe : ∀ t, Gequiv t = G t := fun t => LinearEquiv.ofIsUnitDet_apply _ t
  let s : M →ₗ[T] (Fin d → T) := Gequiv.symm.toLinearMap.comp A
  have hse : ∀ t, s (e t) = t := by
    intro t
    have h1 : A (e t) = Gequiv t := by rw [hGe]; rfl
    change Gequiv.symm (A (e t)) = t
    rw [h1, LinearEquiv.symm_apply_apply]
  set K : Submodule 𝒪 M := (LinearMap.ker s).restrictScalars 𝒪 with hK
  have hKmem : ∀ m', m' - e (s m') ∈ K := by
    intro m'
    rw [hK, Submodule.restrictScalars_mem, LinearMap.mem_ker, map_sub, hse, sub_self]
  let Ξ : M ≃ₗ[𝒪] (Fin d → T) × K :=
    { toFun := fun m' => (s m', ⟨m' - e (s m'), hKmem m'⟩)
      invFun := fun p => e p.1 + (p.2 : M)
      map_add' := fun a b => by
        ext
        · simp only [map_add, Prod.fst_add, Pi.add_apply]
        · simp only [map_add, Prod.snd_add, Submodule.coe_add]
          abel
      map_smul' := fun c a => by
        ext
        · simp only [LinearMap.map_smul_of_tower, Prod.smul_fst, Pi.smul_apply, RingHom.id_apply]
        · simp only [LinearMap.map_smul_of_tower, Prod.smul_snd, Submodule.coe_smul,
            RingHom.id_apply, smul_sub]
      left_inv := fun m' => by simp
      right_inv := fun p => by
        obtain ⟨f, k⟩ := p
        have hk : s (k : M) = 0 := k.2
        ext
        · simp only [map_add, hse, hk, add_zero]
        · simp only [map_add, hse, hk, add_zero, add_sub_cancel_left] }
  have h1 : Module.finrank 𝒪 M = Module.finrank 𝒪 (Fin d → T) + Module.finrank 𝒪 K := by
    rw [Ξ.finrank_eq, Module.finrank_prod]
  have h2 : Module.finrank 𝒪 (Fin d → T) = d * Module.finrank 𝒪 T := by
    rw [Module.finrank_pi_fintype 𝒪]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hK0 : Module.finrank 𝒪 K = 0 := by omega
  have hKs : Subsingleton K := Module.finrank_zero_iff.mp hK0
  have hesurj : Function.Surjective e := by
    intro m'
    refine ⟨s m', ?_⟩
    have hk : (⟨m' - e (s m'), hKmem m'⟩ : K) = 0 := Subsingleton.elim _ _
    have hk' : m' - e (s m') = 0 := congrArg Subtype.val hk
    rw [sub_eq_zero] at hk'
    exact hk'.symm
  have heinj : Function.Injective e := Function.LeftInverse.injective hse
  exact Module.Free.of_equiv (LinearEquiv.ofBijective e ⟨heinj, hesurj⟩)

end Main

end Module.FreeOfBalancedPairing

/-- **Freeness from a balanced perfect pairing.** Over a principal ideal domain `𝒪`,
let `T` be a local, finite free `𝒪`-algebra with augmentation `πT` whose congruence
ideal is nonzero and with a perfect `T`-balanced `𝒪`-pairing `C`. A finite free
`𝒪`-module `M` with a compatible `T`-action and a perfect `T`-balanced `𝒪`-pairing `B`
is free over `T` as soon as its `ker πT`-torsion submodule equals `Ann (ker πT) • M`
and has the rank forced by `rank M = rank M[ker πT] * rank T`. -/
public theorem Module.free_of_torsionBySet_eq_annihilator_smul
    {𝒪 : Type*} {T : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    [CommRing T] [IsLocalRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (πT : T →ₐ[𝒪] 𝒪) (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (C : T →ₗ[𝒪] T →ₗ[𝒪] 𝒪) (hC : ∀ s t u : T, C (s * t) u = C t (s * u))
    (hCb : Function.Bijective C)
    (M : Type*) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M]
    (B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪) (hB : ∀ (t : T) (m n : M), B (t • m) n = B m (t • n))
    (hBb : Function.Bijective B)
    (hrank : Module.finrank 𝒪 M =
      Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) * Module.finrank 𝒪 T)
    (hsat : Submodule.torsionBySet T M ↑(RingHom.ker πT) = (RingHom.ker πT).annihilator • ⊤) :
    Module.Free T M := by
  classical
  obtain ⟨e₀, he⟩ :=
    (IsPrincipalIdealRing.principal ((RingHom.ker πT).annihilator.map πT)).principal
  have he' : (RingHom.ker πT).annihilator.map πT = Ideal.span ({e₀} : Set 𝒪) := he
  have he₀ : e₀ ≠ 0 := by
    rintro rfl
    apply hη
    rw [he', Ideal.span_singleton_eq_bot]
  obtain ⟨x₀, hx₀, hπx₀⟩ : ∃ x₀, x₀ ∈ (RingHom.ker πT).annihilator ∧ πT x₀ = e₀ := by
    have : e₀ ∈ ((RingHom.ker πT).annihilator).map πT := by
      rw [he']
      exact Ideal.mem_span_singleton_self e₀
    exact (Ideal.mem_map_iff_of_surjective πT
      (Module.FreeOfBalancedPairing.πT_surjective πT)).mp this
  have hIspan : (RingHom.ker πT).annihilator = Ideal.span ({x₀} : Set T) := by
    refine le_antisymm (fun i hi => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr hx₀)
    obtain ⟨c, rfl⟩ :=
      Module.FreeOfBalancedPairing.exists_eq_smul_of_mem_annihilator πT he₀ he' hx₀ hπx₀ hi
    exact Submodule.smul_of_tower_mem _ c (Ideal.subset_span rfl)
  have hPx : ∀ p : M, p ∈ Submodule.torsionBySet T M ↑(RingHom.ker πT) →
      ∃ m' : M, x₀ • m' = p := by
    intro p hp
    rw [hsat, hIspan, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at hp
    obtain ⟨m', -, rfl⟩ := hp
    exact ⟨m', rfl⟩
  let P : Submodule 𝒪 M := (Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪
  let bP := Module.finBasis 𝒪 P
  choose mf hmf using fun j => hPx (bP j) (bP j).2
  let eqv : (Submodule.torsionBySet T M ↑(RingHom.ker πT)) ≃ₗ[𝒪] P :=
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun p => ⟨p.1, p.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [eqv.finrank_eq] at hrank
  exact Module.FreeOfBalancedPairing.core πT C hC hCb B hB hBb he₀ he' hx₀ hπx₀ mf bP
    (fun j => (hmf j).symm) hrank
