/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Ideal_span_algebraNorm_eq_of_ker_eq_span_of_isDiscreteValuationRing.lean`,
`Theorems/Thm_exteriorPower_map_mulLeft_apply_eq_norm_smul.lean`,
`Theorems/Thm_exteriorPower_map_apply_eq_det_smul.lean`,
`Theorems/Thm_exteriorPower_iotaMulti_comp_eq_det_smul.lean`,
`Theorems/Thm_exteriorPower_range_map_subtype_eq_maximalIdeal_smul_top.lean`
and
`P2M/Sol/S_Ideal_span_algebraNorm_eq_of_ker_eq_span_of_isDiscreteValuationRing.lean`,
`P2M/Sol/S_exteriorPower_map_mulLeft_apply_eq_norm_smul.lean`,
`P2M/Sol/S_exteriorPower_map_apply_eq_det_smul.lean`,
`P2M/Sol/S_exteriorPower_iotaMulti_comp_eq_det_smul.lean`,
`P2M/Sol/S_exteriorPower_range_map_subtype_eq_maximalIdeal_smul_top.lean`
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

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Norm.Defs

import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Free

@[expose] public section

open scoped TensorProduct Pointwise

universe u

private theorem alternatingMap_apply_matrix_smul {A : Type*} [CommRing A] {M N : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] {n : ℕ}
    (g : M [⋀^Fin n]→ₗ[A] N) (f : Fin n → M) (a : Matrix (Fin n) (Fin n) A) :
    g (fun j => ∑ i, a i j • f i) = a.det • g f := by
  classical
  let L : (Fin n → A) →ₗ[A] M := Fintype.linearCombination A f
  let b : Module.Basis (Fin n) A (Fin n → A) := Pi.basisFun A (Fin n)
  have hL : ∀ i, L (b i) = f i := fun i => by
    simp [L, b, Fintype.linearCombination_apply_single]
  have key : g.compLinearMap L = b.det.smulRight (g f) := by
    refine Module.Basis.ext_alternating b fun v hv => ?_
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective v (Finite.injective_iff_bijective.1 hv)
    have h1 : (fun i => L (b (v i))) = f ∘ σ := funext fun i => hL (v i)
    have h2 : (fun i => b (v i)) = b ∘ σ := rfl
    rw [AlternatingMap.compLinearMap_apply, h1, AlternatingMap.map_perm,
      AlternatingMap.smulRight_apply, h2, AlternatingMap.map_perm, Module.Basis.det_self]
    simp [Units.smul_def, Int.cast_smul_eq_zsmul]
  have h3 : (fun j => ∑ i, a i j • f i) = fun j => L (a.transpose j) := by
    funext j
    simp [L, Fintype.linearCombination_apply, Matrix.transpose_apply]
  have h4 := congrArg (fun G : (Fin n → A) [⋀^Fin n]→ₗ[A] N => G (fun j => a.transpose j)) key
  simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smulRight_apply] at h4
  rw [h3, h4, show (fun j => a.transpose j) = a.transpose from rfl]
  congr 1

private theorem iotaMulti_matrix_smul {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M]
    [Module A M] {n : ℕ} (f : Fin n → M) (a : Matrix (Fin n) (Fin n) A) :
    exteriorPower.ιMulti A n (fun j => ∑ i, a i j • f i) = a.det • exteriorPower.ιMulti A n f :=
  alternatingMap_apply_matrix_smul (exteriorPower.ιMulti A n) f a

private theorem iotaMulti_comp_eq_det_smul {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M]
    [Module A M] {n : ℕ} (b : Module.Basis (Fin n) A M) (f : M →ₗ[A] M) (m : Fin n → M) :
    exteriorPower.ιMulti A n (f ∘ m) = LinearMap.det f • exteriorPower.ιMulti A n m := by
  classical
  let c : Matrix (Fin n) (Fin n) A := fun i j => b.repr (m j) i
  let T : Matrix (Fin n) (Fin n) A := LinearMap.toMatrix b b f
  have hm : (fun j => ∑ i, c i j • b i) = m := by
    funext j
    exact b.sum_repr (m j)
  have hfb : ∀ i, f (b i) = ∑ k, T k i • b k := by
    intro i
    have h := b.sum_repr (f (b i))
    simp only [T, LinearMap.toMatrix_apply]
    exact h.symm
  have hfm : (fun j => ∑ k, (T * c) k j • b k) = f ∘ m := by
    funext j
    have h1 : f (m j) = ∑ i, c i j • f (b i) := by
      have hcongr := congrArg f (congrFun hm j)
      rw [map_sum] at hcongr
      simpa only [map_smul] using hcongr.symm
    rw [Function.comp_apply, h1]
    simp only [Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfb i, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, mul_comm]
  rw [← hfm, iotaMulti_matrix_smul, Matrix.det_mul, ← hm, iotaMulti_matrix_smul, smul_smul]
  simp only [T, LinearMap.det_toMatrix]

private theorem map_apply_eq_det_smul {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M]
    [Module A M] {ι : Type*} [Fintype ι] (b : Module.Basis ι A M) {n : ℕ}
    (hn : Fintype.card ι = n) (f : M →ₗ[A] M) (x : ⋀[A]^n M) :
    exteriorPower.map n f x = LinearMap.det f • x := by
  classical
  let b' : Module.Basis (Fin n) A M := b.reindex (Fintype.equivFinOfCardEq hn)
  have hgen : ∀ m : Fin n → M,
      exteriorPower.map n f (exteriorPower.ιMulti A n m) =
        LinearMap.det f • exteriorPower.ιMulti A n m := by
    intro m
    rw [exteriorPower.map_apply_ιMulti]
    exact iotaMulti_comp_eq_det_smul b' f m
  have hx : x ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A n (M := M))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨m, rfl⟩ := hy; exact hgen m
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, hy, hz, smul_add]
  | smul r y _ hy => rw [map_smul, hy, smul_comm]

private theorem map_mulLeft_apply_eq_norm_smul {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] {ι : Type*} [Fintype ι] (b : Module.Basis ι A B) {n : ℕ}
    (hn : Fintype.card ι = n) (x : B) (w : ⋀[A]^n B) :
    exteriorPower.map n (LinearMap.mulLeft A x) w = Algebra.norm A x • w := by
  rw [map_apply_eq_det_smul b hn, Algebra.norm_apply]
  rfl

private theorem iotaMulti_family_smul_basis {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] {d : ℕ} (b : Module.Basis (Fin d) R M) (a : Fin d → R)
    (s : Set.powersetCard (Fin d) d) :
    exteriorPower.ιMulti_family R d (fun i => a i • b i) s =
      (∏ i, a i) • exteriorPower.ιMulti_family R d b s := by
  apply Subtype.ext
  simp only [exteriorPower.ιMulti_family_apply_coe, ExteriorAlgebra.ιMulti_family]
  set e := ⇑(Set.powersetCard.ofFinEmbEquiv.symm s) with he_def
  change ExteriorAlgebra.ιMulti R d (fun i => a (e i) • b (e i)) = _
  rw [AlternatingMap.map_smul_univ, Submodule.coe_smul]
  have he : Function.Bijective e :=
    Finite.injective_iff_bijective.mp (Set.powersetCard.ofFinEmbEquiv.symm s).injective
  have hprod : (∏ i, a (e i)) = ∏ i, a i := Fintype.prod_bijective e he _ _ (fun _ => rfl)
  rw [hprod]
  rfl

private theorem range_map_subtype_span_smul_basis {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] {d : ℕ} (b : Module.Basis (Fin d) R M) (a : Fin d → R) :
    LinearMap.range (exteriorPower.map d
      (Submodule.span R (Set.range fun i => a i • b i)).subtype) =
      Ideal.span {∏ i, a i} • (⊤ : Submodule R (⋀[R]^d M)) := by
  rw [Submodule.ideal_span_singleton_smul, exteriorPower.ιMulti_family_span]
  have hrange : Set.range (exteriorPower.ιMulti_family R d fun i => a i • b i) =
      (∏ i, a i) • Set.range (exteriorPower.ιMulti_family R d b) := by
    ext x
    simp only [Set.mem_range, Set.mem_smul_set, iotaMulti_family_smul_basis]
    constructor
    · rintro ⟨s, rfl⟩; exact ⟨_, ⟨s, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩; exact ⟨s, rfl⟩
  rw [hrange, Submodule.span_smul, exteriorPower.ιMulti_family_span_of_span R b.span_eq]

private theorem exists_basis_eq_span_cons_uniformizer_smul {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M]
    [Module.Finite R M] (N : Submodule R M)
    (e : (M ⧸ N) ≃ₗ[R] (R ⧸ IsLocalRing.maximalIdeal R)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin (n + 1)) R M) (ϖ : R), Irreducible ϖ ∧
      N = Submodule.span R (Set.range fun i : Fin (n + 1) => (if i = 0 then ϖ else 1) • b i) := by
  classical
  let ψ : M →ₗ[R] R ⧸ IsLocalRing.maximalIdeal R := e.toLinearMap ∘ₗ N.mkQ
  have hψker : LinearMap.ker ψ = N := by
    rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot, Submodule.ker_mkQ]
  have hψsurj : Function.Surjective ψ := e.surjective.comp N.mkQ_surjective
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property
    ((Ideal.Quotient.mkₐ R (IsLocalRing.maximalIdeal R)).toLinearMap) ψ
    Ideal.Quotient.mk_surjective
  have hψφ : ∀ x, ψ x = Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (φ x) :=
    fun x => by rw [← hφ]; rfl
  have hmemN : ∀ x, x ∈ N ↔ φ x ∈ IsLocalRing.maximalIdeal R := fun x => by
    rw [← hψker, LinearMap.mem_ker, hψφ, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨m₀, hm₀⟩ := hψsurj 1
  have hunit : IsUnit (φ m₀) := by
    by_contra h
    have h1 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (φ m₀) = 1 := by
      rw [← hψφ, hm₀]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr
      ((IsLocalRing.mem_maximalIdeal _).mpr h)] at h1
    exact zero_ne_one h1
  let m : M := hunit.unit⁻¹.val • m₀
  have hφm : φ m = 1 := by
    simp only [m, map_smul, smul_eq_mul, IsUnit.val_inv_mul]
  let K : Submodule R M := LinearMap.ker φ
  obtain ⟨n, bK⟩ := Submodule.basisOfPid (Module.Free.chooseBasis R M) K
  have hKspan : K ≤ Submodule.span R (Set.range fun i => (bK i : M)) := by
    intro y hy
    have h1 : (⟨y, hy⟩ : K) ∈ Submodule.span R (Set.range bK) := by
      rw [bK.span_eq]; trivial
    have h2 := Submodule.mem_map_of_mem (f := K.subtype) h1
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact h2
  let v : Fin (n + 1) → M := Fin.cons m (fun i => (bK i : M))
  have hvK : LinearIndependent R (fun i => (bK i : M)) :=
    bK.linearIndependent.map' K.subtype K.ker_subtype
  have hspanK : Submodule.span R (Set.range fun i => (bK i : M)) ≤ K := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact (bK i).2
  have hli : LinearIndependent R v := by
    refine LinearIndependent.finCons' m (fun i => (bK i : M)) hvK fun c y hy hc => ?_
    have hyK : y ∈ K := hspanK hy
    have hcongr := congrArg φ hc
    rw [map_add, map_smul, hφm, smul_eq_mul, mul_one, map_zero,
      LinearMap.mem_ker.mp hyK, add_zero] at hcongr
    exact hcongr
  have hdecomp : ∀ x : M, x - φ x • m ∈ K := fun x => by
    change φ (x - φ x • m) = 0
    rw [map_sub, map_smul, hφm, smul_eq_mul, mul_one, sub_self]
  have hsp : ⊤ ≤ Submodule.span R (Set.range v) := by
    intro x _
    have hx : x = φ x • m + (x - φ x • m) := by abel
    rw [hx]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)) ?_
    refine Submodule.span_mono ?_ (hKspan (hdecomp x))
    rintro _ ⟨i, rfl⟩
    exact ⟨i.succ, by simp [v]⟩
  let b : Module.Basis (Fin (n + 1)) R M := Module.Basis.mk hli hsp
  have hb : ∀ i, b i = v i := fun i => Module.Basis.mk_apply hli hsp i
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have h𝔪 : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  refine ⟨n, b, ϖ, hϖ, le_antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (h𝔪 ▸ (hmemN x).mp hx)
    have hx' : x = r • (ϖ • m) + (x - φ x • m) := by rw [smul_smul, hr]; abel
    rw [hx']
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, ?_⟩)) ?_
    · simp [hb, v]
    · refine Submodule.span_mono ?_ (hKspan (hdecomp x))
      rintro _ ⟨i, rfl⟩
      exact ⟨i.succ, by simp [hb, v]⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · show (if (0 : Fin (n + 1)) = 0 then ϖ else 1) • b 0 ∈ N
      rw [if_pos rfl, hb, show v 0 = m from rfl, hmemN, map_smul, hφm, smul_eq_mul, mul_one, h𝔪]
      exact Ideal.mem_span_singleton_self ϖ
    · show (if j.succ = 0 then ϖ else 1) • b j.succ ∈ N
      rw [if_neg (Fin.succ_ne_zero j), one_smul, hb, show v j.succ = (bK j : M) from rfl, hmemN,
        LinearMap.mem_ker.mp (bK j).2]
      exact Ideal.zero_mem _

private theorem range_map_subtype_eq_maximalIdeal_smul_top {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M]
    [Module.Finite R M] {d : ℕ} (hd : Module.finrank R M = d)
    (N : Submodule R M) (e : (M ⧸ N) ≃ₗ[R] (R ⧸ IsLocalRing.maximalIdeal R)) :
    LinearMap.range (exteriorPower.map d N.subtype) =
      IsLocalRing.maximalIdeal R • ⊤ := by
  obtain ⟨n, b, ϖ, hϖ, rfl⟩ := exists_basis_eq_span_cons_uniformizer_smul N e
  have hdn : d = n + 1 := by rw [← hd, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hdn
  rw [range_map_subtype_span_smul_basis,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Finset.prod_ite_eq']
  simp

private theorem range_smul_id_eq {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V]
    [Module R V] (r : R) :
    LinearMap.range (r • (LinearMap.id : V →ₗ[R] V)) = Ideal.span {r} • (⊤ : Submodule R V) := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self r) (Submodule.mem_top : w ∈ ⊤)
  · refine Submodule.smul_le.mpr fun a ha v _ => ?_
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    refine ⟨c • v, ?_⟩
    change r • (c • v) = (c * r) • v
    rw [mul_comm, mul_smul]

private theorem ideal_eq_of_smul_top_eq {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V]
    [Module R V] {ι : Type*} [Unique ι] (b : Module.Basis ι R V) {I J : Ideal R}
    (h : I • (⊤ : Submodule R V) = J • ⊤) : I = J := by
  let e : V ≃ₗ[R] R := b.repr ≪≫ₗ Finsupp.LinearEquiv.finsuppUnique R R ι
  have key : ∀ K : Ideal R, (K • (⊤ : Submodule R V)).map e.toLinearMap = K := fun K => by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range, Ideal.smul_top_eq_map,
      Algebra.algebraMap_self, Ideal.map_id, Submodule.restrictScalars_self]
  rw [← key I, ← key J, h]

private theorem norm_one_tmul_eq {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι A B) (L : Type*) [CommRing L]
    [Algebra A L] (x : B) :
    Algebra.norm L ((1 : L) ⊗ₜ[A] x) = algebraMap A L (Algebra.norm A x) := by
  let bL := Algebra.TensorProduct.basis L b
  rw [Algebra.norm_eq_matrix_det bL, Algebra.norm_eq_matrix_det b, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, bL,
    Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]

private theorem span_norm_tmul_eq_maximalIdeal {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Free A B] [Module.Finite A B] {K : Type*} [Field K] (χ : B →+* K)
    (hχ : Function.Surjective (χ.comp (algebraMap A B))) (g : B)
    (hg : RingHom.ker χ = Ideal.span {g}) (𝔪 : Ideal A)
    (h𝔪 : RingHom.ker (χ.comp (algebraMap A B)) = 𝔪) [𝔪.IsMaximal] (L : Type*) [CommRing L]
    [Algebra A L] [IsLocalization.AtPrime L 𝔪] [IsDomain L] [IsDiscreteValuationRing L] :
    Ideal.span {Algebra.norm L ((1 : L) ⊗ₜ[A] g)} = IsLocalRing.maximalIdeal L := by
  classical
  have hunit : ∀ s : 𝔪.primeCompl, IsUnit ((χ.comp (algebraMap A B)) s) := fun s => by
    rw [isUnit_iff_ne_zero, ne_eq, ← RingHom.mem_ker, h𝔪]
    exact s.2
  obtain ⟨θ, hθ⟩ : ∃ θ : L →+* K, ∀ a : A, θ (algebraMap A L a) = χ (algebraMap A B a) :=
    ⟨IsLocalization.lift (M := 𝔪.primeCompl) hunit, IsLocalization.lift_eq hunit⟩
  letI : Algebra L K := θ.toAlgebra
  letI : Algebra A K := (θ.comp (algebraMap A L)).toAlgebra
  haveI : IsScalarTower A L K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hθsurj : Function.Surjective θ := fun k => by
    obtain ⟨a, ha⟩ := hχ k
    exact ⟨algebraMap A L a, (hθ a).trans ha⟩
  have hkerθ : RingHom.ker θ = IsLocalRing.maximalIdeal L :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective θ hθsurj)
  let χₐ : B →ₐ[A] K := { toRingHom := χ, commutes' := fun a => (hθ a).symm }
  let Φ : L ⊗[A] B →ₐ[L] K :=
    Algebra.TensorProduct.lift (Algebra.ofId L K) χₐ fun _ _ => mul_comm _ _
  have hΦ : ∀ (l : L) (b : B), Φ (l ⊗ₜ b) = θ l * χ b := fun l b => by
    simp only [Φ, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]
    rfl
  have hΦsurj : Function.Surjective Φ.toLinearMap := fun k => by
    obtain ⟨l, hl⟩ := hθsurj k
    exact ⟨l ⊗ₜ 1, by rw [AlgHom.toLinearMap_apply, hΦ, map_one, mul_one, hl]⟩
  let θₗ : L →ₗ[L] K := Algebra.linearMap L K
  have hθₗsurj : Function.Surjective θₗ := hθsurj
  have hkerθₗ : LinearMap.ker θₗ = IsLocalRing.maximalIdeal L := by
    rw [← hkerθ]; ext x; rfl
  let eK : K ≃ₗ[L] (L ⧸ IsLocalRing.maximalIdeal L) :=
    (LinearMap.quotKerEquivOfSurjective θₗ hθₗsurj).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ hkerθₗ
  let ψ : L ⊗[A] B →ₗ[L] L ⧸ IsLocalRing.maximalIdeal L := eK.toLinearMap ∘ₗ Φ.toLinearMap
  have hψsurj : Function.Surjective ψ := eK.surjective.comp hΦsurj
  have hkerψ : LinearMap.ker ψ = LinearMap.ker Φ.toLinearMap := by
    rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot]
  let ι := Module.Free.ChooseBasisIndex A B
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Equiv.injective _)
  let bB : Module.Basis ι A B := Module.Free.chooseBasis A B
  let bL : Module.Basis ι L (L ⊗[A] B) := Algebra.TensorProduct.basis L bB
  haveI : Module.Free L (L ⊗[A] B) := Module.Free.of_basis bL
  haveI : Module.Finite L (L ⊗[A] B) := Module.Finite.of_basis bL
  have hd : Module.finrank L (L ⊗[A] B) = Fintype.card ι := Module.finrank_eq_card_basis bL
  let N : Submodule L (L ⊗[A] B) := LinearMap.ker Φ.toLinearMap
  have hED : LinearMap.range (exteriorPower.map (Fintype.card ι) N.subtype) =
      IsLocalRing.maximalIdeal L • ⊤ :=
    range_map_subtype_eq_maximalIdeal_smul_top hd N
      ((Submodule.quotEquivOfEq _ _ hkerψ).symm ≪≫ₗ
        LinearMap.quotKerEquivOfSurjective ψ hψsurj)
  let μ : L ⊗[A] B →ₗ[L] L ⊗[A] B := LinearMap.mulLeft L ((1 : L) ⊗ₜ[A] g)
  have hχg : χ g = 0 := by
    rw [← RingHom.mem_ker, hg]; exact Ideal.mem_span_singleton_self g
  have hμN : ∀ z, μ z ∈ N := fun z => by
    change Φ ((1 ⊗ₜ g) * z) = 0
    rw [map_mul, hΦ, map_one, one_mul, hχg, zero_mul]
  haveI : IsLocalizedModule 𝔪.primeCompl (TensorProduct.mk A L B 1) :=
    (isLocalizedModule_iff_isBaseChange 𝔪.primeCompl L _).mpr (TensorProduct.isBaseChange A B L)
  have hμsurj : ∀ z ∈ N, ∃ w, μ w = z := by
    intro z hz
    obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalizedModule.surj 𝔪.primeCompl (TensorProduct.mk A L B 1) z
    have hb : χ b = 0 := by
      have h1 : Φ ((1 : L) ⊗ₜ b) = 0 := by
        change Φ (TensorProduct.mk A L B 1 b) = 0
        rw [← hbs, Submonoid.smul_def, ← algebraMap_smul L (s : A) z, map_smul,
          show Φ z = 0 from hz, smul_zero]
      rwa [hΦ, map_one, one_mul] at h1
    obtain ⟨c, rfl⟩ : ∃ c, c * g = b :=
      Ideal.mem_span_singleton'.mp (hg ▸ (RingHom.mem_ker).mpr hb)
    obtain ⟨u, hu⟩ := IsLocalization.map_units L s
    refine ⟨((u⁻¹ : Lˣ) : L) • ((1 : L) ⊗ₜ[A] c), ?_⟩
    rw [LinearMap.map_smul]
    change ((u⁻¹ : Lˣ) : L) • ((1 ⊗ₜ g) * (1 ⊗ₜ c)) = z
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm g c]
    have hz' : (u : L) • z = (1 : L) ⊗ₜ[A] (c * g) := by
      rw [hu, algebraMap_smul]; simpa [Submonoid.smul_def] using hbs
    rw [← hz', smul_smul, Units.inv_mul, one_smul]
  have hrange : LinearMap.range (exteriorPower.map (Fintype.card ι) μ) =
      IsLocalRing.maximalIdeal L • ⊤ := by
    have hfac : μ = N.subtype ∘ₗ LinearMap.codRestrict N μ hμN := LinearMap.ext fun _ => rfl
    have hsurj : Function.Surjective (LinearMap.codRestrict N μ hμN) := fun z => by
      obtain ⟨w, hw⟩ := hμsurj z z.2
      exact ⟨w, Subtype.ext hw⟩
    rw [hfac, exteriorPower.map_comp, LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr (exteriorPower.map_surjective hsurj)), hED]
  have hμnorm : exteriorPower.map (Fintype.card ι) μ =
      Algebra.norm L ((1 : L) ⊗ₜ[A] g) •
        (LinearMap.id : ⋀[L]^(Fintype.card ι) (L ⊗[A] B) →ₗ[L] _) := by
    refine LinearMap.ext fun w => ?_
    exact map_mulLeft_apply_eq_norm_smul bL rfl _ w
  rw [hμnorm, range_smul_id_eq] at hrange
  haveI : Unique (Set.powersetCard ι (Fintype.card ι)) :=
    { default := ⟨Finset.univ, Finset.card_univ⟩
      uniq := fun s => Subtype.ext (Finset.eq_univ_of_card _ s.2) }
  exact ideal_eq_of_smul_top_eq (bL.exteriorPower (Fintype.card ι)) hrange

/-- The algebra norm of a generator of the kernel of a residue map `χ : B →+* K`
generates the contracted ideal in `A`, provided `B` is finite free over `A`,
`χ` is surjective on constants, and the localization of `A` at the contracted
ideal is a discrete valuation ring. -/
public theorem Ideal.span_algebraNorm_eq_of_ker_eq_span_of_isDiscreteValuationRing
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B]
    {K : Type u} [Field K] (χ : B →+* K) (hχ : Function.Surjective (χ.comp (algebraMap A B)))
    (g : B) (hg : RingHom.ker χ = Ideal.span {g})
    (𝔪 : Ideal A) (h𝔪 : RingHom.ker (χ.comp (algebraMap A B)) = 𝔪) [𝔪.IsMaximal]
    (Aₘ : Type u) [CommRing Aₘ] [Algebra A Aₘ] [IsLocalization.AtPrime Aₘ 𝔪]
    [IsDomain Aₘ] [IsDiscreteValuationRing Aₘ] :
    Ideal.span {Algebra.norm A g} = 𝔪 := by
  classical
  have hmap : ∀ {S : Type u} [CommRing S] [Algebra A S] (x : A),
      (Ideal.span {x}).map (algebraMap A S) = Ideal.span {algebraMap A S x} := fun x => by
    rw [Ideal.map_span, Set.image_singleton]
  apply Ideal.eq_of_localization_maximal
  intro P hP
  by_cases hP𝔪 : P = 𝔪
  · subst hP𝔪
    have key := span_norm_tmul_eq_maximalIdeal χ hχ g hg P h𝔪 Aₘ
    rw [norm_one_tmul_eq (Module.Free.chooseBasis A B) Aₘ g, ← hmap,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal P Aₘ] at key
    let e : Localization.AtPrime P ≃ₐ[A] Aₘ := IsLocalization.algEquiv P.primeCompl _ _
    have he : (algebraMap A Aₘ) =
        (e : Localization.AtPrime P →+* Aₘ).comp (algebraMap A (Localization.AtPrime P)) := by
      ext a; exact (e.commutes a).symm
    have tr : ∀ I : Ideal A, I.map (algebraMap A (Localization.AtPrime P)) =
        (I.map (algebraMap A Aₘ)).map (e.symm : Aₘ →+* Localization.AtPrime P) := fun I => by
      rw [he, ← Ideal.map_map, Ideal.map_map (e : Localization.AtPrime P →+* Aₘ)]
      have hcomp : (e.symm : Aₘ →+* Localization.AtPrime P).comp
          (e : Localization.AtPrime P →+* Aₘ) = RingHom.id _ := by
        ext x; exact e.symm_apply_apply x
      rw [hcomp, Ideal.map_id]
    rw [tr, tr, key]
  · have hle : ¬ 𝔪 ≤ P :=
      fun h => hP𝔪 ((Ideal.IsMaximal.eq_of_le inferInstance hP.ne_top h).symm)
    have htop : ∀ I : Ideal A, ¬ I ≤ P →
        I.map (algebraMap A (Localization.AtPrime P)) = ⊤ := fun I hI => by
      by_contra h
      refine hI fun x hx => ?_
      by_contra hxP
      exact Set.disjoint_left.mp
        ((IsLocalization.map_algebraMap_ne_top_iff_disjoint P.primeCompl _ I).mp h) hxP hx
    rw [htop 𝔪 hle, htop]
    intro hNP
    obtain ⟨s, hs𝔪, hsP⟩ := Set.not_subset.mp hle
    have hs : algebraMap A B s ∈ RingHom.ker χ := by
      rw [RingHom.mem_ker]
      have hmem : s ∈ RingHom.ker (χ.comp (algebraMap A B)) := h𝔪 ▸ hs𝔪
      exact hmem
    rw [hg] at hs
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hs
    have hnorm := congrArg (Algebra.norm A) hc
    rw [map_mul, Algebra.norm_algebraMap] at hnorm
    have hmem : s ^ Module.finrank A B ∈ P := by
      rw [← hnorm]
      exact hNP (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    exact hsP (hP.isPrime.mem_of_pow_mem _ hmem)
