/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_MvPowerSeries_exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem.lean`
and
`P2M/Sol/S_MvPowerSeries_exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem.lean`
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

public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import MathlibExt.RingTheory.MvPowerSeries.VariableIdealPower

@[expose] public section


set_option autoImplicit false

universe u v w t

open TensorProduct

namespace TruncBCEngine

open MvPowerSeries

section L0

variable {σ : Type w} [Finite σ] {R : Type u} [CommRing R]

omit [Finite σ] in

private theorem exists_le_degree_eq (N : ℕ) (x : σ →₀ ℕ) (hx : N ≤ x.degree) :
    ∃ y : σ →₀ ℕ, y ≤ x ∧ y.degree = N := by
  classical
  induction N with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨y, hyx, hyn⟩ := ih ((Nat.le_succ n).trans hx)
    have hne : x - y ≠ 0 := by
      intro h
      have hle : x ≤ y := tsub_eq_zero_iff_le.mp h
      have : x = y := le_antisymm hle hyx
      subst this
      omega
    obtain ⟨i, hi⟩ : ∃ i, (x - y) i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hne (Finsupp.ext hcon)
    refine ⟨y + Finsupp.single i 1, ?_, by simp [hyn]⟩
    intro j
    simp only [Finsupp.coe_add, Pi.add_apply]
    have hyj : y j ≤ x j := hyx j
    have hij : (x - y) i = x i - y i := Finsupp.tsub_apply x y i
    by_cases h : i = j
    · subst h
      rw [Finsupp.single_eq_same]
      omega
    · rw [Finsupp.single_apply, ite_eq_right h]
      omega

omit [Finite σ] in

private theorem monomial_one_mem_pow_span_X (y : σ →₀ ℕ) :
    (monomial y (1 : R) : MvPowerSeries σ R) ∈
      Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ y.degree := by
  classical
  rw [MvPowerSeries.monomial_one_eq, Finsupp.prod, Finsupp.degree_apply,
    ← Finset.prod_pow_eq_pow_sum]
  refine Ideal.prod_mem_prod fun i _ => ?_
  exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) _

private theorem mem_of_forall_coeff_eq_zero_of_forall_monomial_mem (N : ℕ) (I : Ideal
  (MvPowerSeries σ R))
    (hI : ∀ y : σ →₀ ℕ, y.degree = N → (monomial y (1 : R) : MvPowerSeries σ R) ∈ I)
    (q : MvPowerSeries σ R) (hq : ∀ x : σ →₀ ℕ, x.degree < N → coeff x q = 0) : q ∈ I := by
  classical

  have hY : ∀ x : σ →₀ ℕ, ∃ y : σ →₀ ℕ, N ≤ x.degree → y ≤ x ∧ y.degree = N := by
    intro x
    by_cases hx : N ≤ x.degree
    · obtain ⟨y, hy⟩ := exists_le_degree_eq N x hx
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose Y hY using hY
  set D : Finset (σ →₀ ℕ) := (Finsupp.finite_of_degree_le N).toFinset.filter fun y => y.degree = N
    with hD
  have hmemD : ∀ y, y ∈ D ↔ y.degree = N := by
    intro y
    simp only [hD, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
      and_iff_right_iff_imp]
    intro h; exact h.le

  let r : (σ →₀ ℕ) → MvPowerSeries σ R := fun y z =>
    if N ≤ (z + y).degree ∧ Y (z + y) = y then coeff (z + y) q else 0
  have hr : ∀ y z, coeff z (r y) = if N ≤ (z + y).degree ∧ Y (z + y) = y then coeff (z + y) q else
    0 :=
    fun y z => rfl
  have hdecomp : q = ∑ y ∈ D, monomial y (1 : R) * r y := by
    ext x
    rw [map_sum]
    simp_rw [coeff_monomial_mul, one_mul]
    by_cases hx : N ≤ x.degree
    · obtain ⟨hYx, hYdeg⟩ := hY x hx
      rw [Finset.sum_eq_single (Y x)]
      · rw [ite_eq_left hYx, hr, tsub_add_cancel_of_le hYx, ite_eq_left ⟨hx, rfl⟩]
      · intro y _ hne
        split_ifs with hyx
        · rw [hr, tsub_add_cancel_of_le hyx]
          rw [ite_eq_right]
          rintro ⟨_, h⟩
          exact hne h.symm
        · rfl
      · intro h
        exact absurd ((hmemD _).mpr hYdeg) h
    · rw [hq x (not_le.mp hx)]
      symm
      refine Finset.sum_eq_zero fun y hy => ?_
      split_ifs with hyx
      · exfalso
        have := Finsupp.degree_mono hyx
        rw [(hmemD y).mp hy] at this
        exact hx this
      · rfl
  rw [hdecomp]
  refine Ideal.sum_mem _ fun y hy => ?_
  exact Ideal.mul_mem_right _ _ (hI y ((hmemD y).mp hy))

end L0

section Coe

variable {σ : Type w} {R : Type u} [CommRing R]

private noncomputable def coeAlgHom (R : Type u) [CommRing R] (σ : Type w) :
    MvPolynomial σ R →ₐ[R] MvPowerSeries σ R :=
  { MvPolynomial.coeToMvPowerSeries.ringHom with
    commutes' := fun r => by
      show ((algebraMap R (MvPolynomial σ R) r : MvPolynomial σ R) : MvPowerSeries σ R) = _
      rw [MvPolynomial.algebraMap_eq, MvPolynomial.coe_C]
      rfl }

@[scoped simp] private theorem coeAlgHom_apply (t : MvPolynomial σ R) : coeAlgHom R σ t = (t :
  MvPowerSeries σ R) :=
  rfl

private theorem map_coeAlgHom_idealOfVars :
    Ideal.map (coeAlgHom R σ) (MvPolynomial.idealOfVars σ R) =
      Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) := by
  rw [MvPolynomial.idealOfVars, Ideal.map_span, ← Set.range_comp]
  congr 1
  ext q
  simp only [Set.mem_range, Function.comp_apply, coeAlgHom_apply, MvPolynomial.coe_X]

private theorem coe_mem_pow_span_X_of_mem {N : ℕ} {t : MvPolynomial σ R}
    (ht : t ∈ MvPolynomial.idealOfVars σ R ^ N) :
    (t : MvPowerSeries σ R) ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N := by
  have := Ideal.mem_map_of_mem (coeAlgHom R σ) ht
  rwa [Ideal.map_pow, map_coeAlgHom_idealOfVars] at this

end Coe

section Trunc

variable {σ : Type w} [Finite σ] {R : Type u} [CommRing R]

private theorem truncTotal_map {S : Type v} [CommRing S] (f : R →+* S) (N : ℕ) (q : MvPowerSeries σ
  R) :
    truncTotal N (MvPowerSeries.map f q) = MvPolynomial.map f (truncTotal N q) :=
  truncFinset_map f q

private theorem sub_coe_truncTotal_mem_pow_span_X (N : ℕ) (q : MvPowerSeries σ R) :
    q - ((truncTotal N q : MvPolynomial σ R) : MvPowerSeries σ R) ∈
      Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N := by
  refine MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero N _ fun x hx => ?_
  rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hx, sub_self]

private theorem mk_coe_truncTotal (N : ℕ) (I : Ideal (MvPowerSeries σ R))
    (hI : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ I) (q : MvPowerSeries σ R) :
    Ideal.Quotient.mk I ((truncTotal N q : MvPolynomial σ R) : MvPowerSeries σ R) =
      Ideal.Quotient.mk I q := by
  rw [Ideal.Quotient.eq]
  have := hI (sub_coe_truncTotal_mem_pow_span_X N q)
  rwa [← neg_sub, Ideal.neg_mem_iff] at this

end Trunc

section BaseChangeIdeals

variable {σ : Type w} {R : Type u} [CommRing R] {S : Type v} [CommRing S]

private theorem map_map_span_X (f : R →+* S) :
    Ideal.map (MvPowerSeries.map (σ := σ) f) (Ideal.span (Set.range (X : σ → MvPowerSeries σ R))) =
      Ideal.span (Set.range (X : σ → MvPowerSeries σ S)) := by
  rw [Ideal.map_span, ← Set.range_comp]
  congr 1
  ext q
  simp only [Set.mem_range, Function.comp_apply, MvPowerSeries.map_X]

private theorem map_map_span_range {ι : Type*} (f : R →+* S) (φ : ι → MvPowerSeries σ R) :
    Ideal.map (MvPowerSeries.map (σ := σ) f) (Ideal.span (Set.range φ)) =
      Ideal.span (Set.range fun i => MvPowerSeries.map f (φ i)) := by
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

private theorem pow_span_X_le_span_map {ι : Type*} (f : R →+* S) (φ : ι → MvPowerSeries σ R) (N : ℕ)
    (hN : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ Ideal.span (Set.range φ)) :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ S)) ^ N ≤
      Ideal.span (Set.range fun i => MvPowerSeries.map f (φ i)) := by
  rw [← map_map_span_X f, ← Ideal.map_pow, ← map_map_span_range f φ]
  exact Ideal.map_mono hN

end BaseChangeIdeals

section Main

variable {σ : Type w} [Finite σ] {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
variable {ι : Type*}

private noncomputable def theta (φ : ι → MvPowerSeries σ R) (N : ℕ)
    (hN : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ Ideal.span (Set.range φ)) :
    (MvPolynomial σ R ⧸ MvPolynomial.idealOfVars σ R ^ N) →ₐ[R]
      (MvPowerSeries σ R ⧸ Ideal.span (Set.range φ)) :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ R _).comp (coeAlgHom R σ)) fun t ht => by
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, coeAlgHom_apply,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hN (coe_mem_pow_span_X_of_mem ht)

omit [Finite σ] in
private theorem theta_mk (φ : ι → MvPowerSeries σ R) (N : ℕ)
    (hN : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ Ideal.span (Set.range φ))
    (t : MvPolynomial σ R) :
    theta φ N hN (Ideal.Quotient.mk _ t) = Ideal.Quotient.mk _ (t : MvPowerSeries σ R) :=
  rfl

scoped instance instIsScalarTowerTensorQuot (N : ℕ) :
    IsScalarTower R S (S ⊗[R] (MvPolynomial σ R ⧸ MvPolynomial.idealOfVars σ R ^ N)) :=
  TensorProduct.isScalarTower_left

private noncomputable def xfam (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (σ : Type w) (N : ℕ) : σ → S ⊗[R] (MvPolynomial σ R ⧸ MvPolynomial.idealOfVars σ R ^ N) :=
  fun i => (1 : S) ⊗ₜ[R] Ideal.Quotient.mk _ (MvPolynomial.X i)

omit [Finite σ] in
private theorem aeval_xfam (N : ℕ) (t : MvPolynomial σ R) :
    MvPolynomial.aeval (xfam R S σ N) t = (1 : S) ⊗ₜ[R] Ideal.Quotient.mk _ t := by
  have h : MvPolynomial.aeval (R := R) (xfam R S σ N) =
      (Algebra.TensorProduct.includeRight (R := R) (A := S)).comp
        (Ideal.Quotient.mkₐ R (MvPolynomial.idealOfVars σ R ^ N)) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [MvPolynomial.aeval_X]
    rfl
  exact congrArg (fun F => F t) h

private noncomputable def beta0 (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (σ : Type w) (N : ℕ) :
    MvPolynomial σ S →ₐ[S] S ⊗[R] (MvPolynomial σ R ⧸ MvPolynomial.idealOfVars σ R ^ N) :=
  MvPolynomial.aeval (xfam R S σ N)

omit [Finite σ] in
private theorem beta0_map (N : ℕ) (t : MvPolynomial σ R) :
    beta0 R S σ N (MvPolynomial.map (algebraMap R S) t) = (1 : S) ⊗ₜ[R] Ideal.Quotient.mk _ t := by
  have key : ∀ t : MvPolynomial σ R,
      MvPolynomial.aeval (xfam R S σ N) (MvPolynomial.map (algebraMap R S) t)
        = MvPolynomial.aeval (R := R) (xfam R S σ N) t := by
    intro t
    induction t using MvPolynomial.induction_on with
    | C a => simp [IsScalarTower.algebraMap_apply R S
        (S ⊗[R] (MvPolynomial σ R ⧸ MvPolynomial.idealOfVars σ R ^ N)) a]
    | add p q hp hq => simp [hp, hq]
    | mul_X p n hp => simp [hp]
  rw [beta0, key]
  exact aeval_xfam N t

omit [Finite σ] in
private theorem beta0_ker (N : ℕ) (a : MvPolynomial σ S) (ha : a ∈ MvPolynomial.idealOfVars σ S ^
  N) :
    beta0 R S σ N a = 0 := by
  rw [MvPolynomial.pow_idealOfVars_eq_span] at ha
  suffices h : Ideal.span ((fun y => MvPolynomial.monomial y (1 : S)) '' (Finsupp.degree ⁻¹' {N})) ≤
      RingHom.ker (beta0 R S σ N) from RingHom.mem_ker.mp (h ha)
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨y, hy, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker]
  have h1 : (MvPolynomial.monomial y (1 : S)) =
      MvPolynomial.map (algebraMap R S) (MvPolynomial.monomial y (1 : R)) := by
    rw [MvPolynomial.map_monomial, (algebraMap R S).map_one]
  have h2 : MvPolynomial.monomial y (1 : R) ∈ MvPolynomial.idealOfVars σ R ^ N := by
    rw [MvPolynomial.pow_idealOfVars_eq_span]
    exact Ideal.subset_span ⟨y, hy, rfl⟩
  show beta0 R S σ N (MvPolynomial.monomial y (1 : S)) = 0
  rw [h1, beta0_map, Ideal.Quotient.eq_zero_iff_mem.mpr h2, TensorProduct.tmul_zero]

private noncomputable def beta (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (σ : Type w) (N : ℕ) :
    (MvPolynomial σ S ⧸ MvPolynomial.idealOfVars σ S ^ N) →ₐ[S]
      S ⊗[R] (MvPolynomial σ R ⧸ MvPolynomial.idealOfVars σ R ^ N) :=
  Ideal.Quotient.liftₐ _ (beta0 R S σ N) (beta0_ker N)

omit [Finite σ] in
private theorem beta_mk (N : ℕ) (a : MvPolynomial σ S) :
    beta R S σ N (Ideal.Quotient.mk _ a) = beta0 R S σ N a :=
  rfl

private noncomputable def tau (S : Type v) [CommRing S] (σ : Type w) [Finite σ] (N : ℕ) :
    MvPowerSeries σ S →ₐ[S] (MvPolynomial σ S ⧸ MvPolynomial.idealOfVars σ S ^ N) :=
  { (truncTotalAlgHom σ S N).toRingHom with
    commutes' := fun s => by
      show truncTotalAlgHom σ S N (algebraMap S (MvPowerSeries σ S) s) = algebraMap S _ s
      have h := (truncTotalAlgHom σ S N).commutes (MvPolynomial.C s)
      rw [MvPowerSeries.algebraMap_apply', MvPolynomial.coe_C, Algebra.algebraMap_self,
        MvPowerSeries.map_id, RingHom.id_apply] at h
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, h]
      rfl }

private theorem tau_apply (N : ℕ) (q : MvPowerSeries σ S) :
    tau S σ N q = Ideal.Quotient.mk _ (truncTotal N q) :=
  rfl

private noncomputable def G0 (S : Type v) [CommRing S] [Algebra R S] (φ : ι → MvPowerSeries σ R) (N
  : ℕ)
    (hN : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ Ideal.span (Set.range φ)) :
    MvPowerSeries σ S →ₐ[S] S ⊗[R] (MvPowerSeries σ R ⧸ Ideal.span (Set.range φ)) :=
  (Algebra.TensorProduct.map (AlgHom.id S S) (theta φ N hN)).comp ((beta R S σ N).comp (tau S σ N))

private theorem G0_apply (φ : ι → MvPowerSeries σ R) (N : ℕ)
    (hN : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ Ideal.span (Set.range φ))
    (q : MvPowerSeries σ S) :
    G0 S φ N hN q =
      Algebra.TensorProduct.map (AlgHom.id S S) (theta φ N hN) (beta0 R S σ N (truncTotal N q)) :=
  rfl

private theorem G0_map (φ : ι → MvPowerSeries σ R) (N : ℕ)
    (hN : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ Ideal.span (Set.range φ))
    (q : MvPowerSeries σ R) :
    G0 S φ N hN (MvPowerSeries.map (algebraMap R S) q) = (1 : S) ⊗ₜ[R] Ideal.Quotient.mk _ q := by
  rw [G0_apply, truncTotal_map, beta0_map, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    theta_mk, mk_coe_truncTotal N _ hN]

private noncomputable def G (S : Type v) [CommRing S] [Algebra R S] (φ : ι → MvPowerSeries σ R) (N
  : ℕ)
    (hN : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ Ideal.span (Set.range φ)) :
    (MvPowerSeries σ S ⧸ Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap R S) (φ i)))
      →ₐ[S] S ⊗[R] (MvPowerSeries σ R ⧸ Ideal.span (Set.range φ)) :=
  Ideal.Quotient.liftₐ _ (G0 S φ N hN) fun a ha => by
    suffices h : Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap R S) (φ i)) ≤
        RingHom.ker (G0 S φ N hN) from RingHom.mem_ker.mp (h ha)
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    show G0 S φ N hN (MvPowerSeries.map (algebraMap R S) (φ i)) = 0
    rw [G0_map, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i)),
      TensorProduct.tmul_zero]

private theorem G_mk (φ : ι → MvPowerSeries σ R) (N : ℕ)
    (hN : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ Ideal.span (Set.range φ))
    (q : MvPowerSeries σ S) :
    G S φ N hN (Ideal.Quotient.mk _ q) = G0 S φ N hN q :=
  rfl

private noncomputable def mapAH (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (σ : Type w) : MvPowerSeries σ R →ₐ[R] MvPowerSeries σ S :=
  { MvPowerSeries.map (σ := σ) (algebraMap R S) with
    commutes' := fun r => by
      show MvPowerSeries.map (algebraMap R S) (algebraMap R (MvPowerSeries σ R) r) = _
      rw [MvPowerSeries.algebraMap_apply, MvPowerSeries.algebraMap_apply, MvPowerSeries.map_C,
        Algebra.algebraMap_self, RingHom.id_apply] }

omit [Finite σ] in
@[scoped simp] private theorem mapAH_apply (q : MvPowerSeries σ R) :
    mapAH R S σ q = MvPowerSeries.map (algebraMap R S) q :=
  rfl

private noncomputable def chi (S : Type v) [CommRing S] [Algebra R S] (φ : ι → MvPowerSeries σ R) :
    (MvPowerSeries σ R ⧸ Ideal.span (Set.range φ)) →ₐ[R]
      (MvPowerSeries σ S ⧸ Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap R S) (φ
        i))) :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ R _).comp (mapAH R S σ)) fun a ha => by
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, mapAH_apply, Ideal.Quotient.eq_zero_iff_mem,
      ← map_map_span_range]
    exact Ideal.mem_map_of_mem _ ha

omit [Finite σ] in
private theorem chi_mk (φ : ι → MvPowerSeries σ R) (q : MvPowerSeries σ R) :
    chi S φ (Ideal.Quotient.mk _ q) = Ideal.Quotient.mk _ (MvPowerSeries.map (algebraMap R S) q) :=
  rfl

private noncomputable def F (S : Type v) [CommRing S] [Algebra R S] (φ : ι → MvPowerSeries σ R) :
    S ⊗[R] (MvPowerSeries σ R ⧸ Ideal.span (Set.range φ)) →ₐ[S]
      (MvPowerSeries σ S ⧸ Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap R S) (φ
        i))) :=
  Algebra.TensorProduct.lift (Algebra.ofId S _) (chi S φ) fun _ _ => Commute.all _ _

omit [Finite σ] in
private theorem F_tmul (φ : ι → MvPowerSeries σ R) (s : S) (q : MvPowerSeries σ R) :
    F S φ (s ⊗ₜ[R] Ideal.Quotient.mk _ q) =
      s • Ideal.Quotient.mk _ (MvPowerSeries.map (algebraMap R S) q) := by
  rw [F, Algebra.TensorProduct.lift_tmul, chi_mk, Algebra.ofId_apply]
  exact (Algebra.smul_def s _).symm

private theorem G_comp_F (φ : ι → MvPowerSeries σ R) (N : ℕ)
    (hN : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ Ideal.span (Set.range φ)) :
    (G S φ N hN).comp (F S φ) = AlgHom.id S _ := by
  refine Algebra.TensorProduct.ext' fun s b => ?_
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [AlgHom.comp_apply, F_tmul, map_smul, G_mk, G0_map, AlgHom.id_apply, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one]

private theorem F_comp_G (φ : ι → MvPowerSeries σ R) (N : ℕ)
    (hN : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ Ideal.span (Set.range φ)) :
    (F S φ).comp (G S φ N hN) = AlgHom.id S _ := by
  have hΨ : (F S φ).comp ((Algebra.TensorProduct.map (AlgHom.id S S) (theta φ N hN)).comp
      (beta0 R S σ N)) = (Ideal.Quotient.mkₐ S _).comp (coeAlgHom S σ) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, beta0, MvPolynomial.aeval_X, xfam,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, theta_mk, F_tmul, one_smul,
      MvPolynomial.coe_X, MvPowerSeries.map_X, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      coeAlgHom_apply, MvPolynomial.coe_X]
  refine AlgHom.ext fun z => ?_
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
  have := congrArg (fun Ψ => Ψ (truncTotal N q)) hΨ
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, coeAlgHom_apply] at this
  rw [AlgHom.comp_apply, G_mk, G0_apply, this, AlgHom.id_apply]
  exact mk_coe_truncTotal N _ (pow_span_X_le_span_map (algebraMap R S) φ N hN) q

private noncomputable def baseChangeEquiv (S : Type v) [CommRing S] [Algebra R S]
    (φ : ι → MvPowerSeries σ R) (N : ℕ)
    (hN : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ Ideal.span (Set.range φ)) :
    S ⊗[R] (MvPowerSeries σ R ⧸ Ideal.span (Set.range φ)) ≃ₐ[S]
      (MvPowerSeries σ S ⧸ Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap R S) (φ
        i))) :=
  AlgEquiv.ofAlgHom (F S φ) (G S φ N hN) (F_comp_G φ N hN) (G_comp_F φ N hN)

private theorem baseChangeEquiv_tmul (φ : ι → MvPowerSeries σ R) (N : ℕ)
    (hN : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ Ideal.span (Set.range φ))
    (s : S) (q : MvPowerSeries σ R) :
    baseChangeEquiv S φ N hN (s ⊗ₜ[R] Ideal.Quotient.mk _ q) =
      s • Ideal.Quotient.mk _ (MvPowerSeries.map (algebraMap R S) q) :=
  F_tmul φ s q

end Main

section Bridges

variable {σ : Type w} {R : Type u} [CommRing R]

private def lowVanishing (σ : Type w) (R : Type u) [CommRing R] (N : ℕ) : Ideal (MvPowerSeries σ R)
  where
  carrier := {q | ∀ x : σ →₀ ℕ, x.degree < N → coeff x q = 0}
  add_mem' {a b} ha hb x hx := by rw [map_add, ha x hx, hb x hx, add_zero]
  zero_mem' x _ := by rw [map_zero]
  smul_mem' a q hq x hx := by
    classical
    rw [smul_eq_mul, coeff_mul]
    refine Finset.sum_eq_zero fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    have hj : ij.2 ≤ x := hij ▸ le_add_self
    rw [hq ij.2 ((Finsupp.degree_mono hj).trans_lt hx), mul_zero]

private theorem mem_lowVanishing_iff (N : ℕ) (q : MvPowerSeries σ R) :
    q ∈ lowVanishing σ R N ↔ ∀ x : σ →₀ ℕ, x.degree < N → coeff x q = 0 :=
  Iff.rfl

private theorem span_X_le_lowVanishing_one :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ≤ lowVanishing σ R 1 := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩ x hx
  have hx0 : x = 0 := (Finsupp.degree_eq_zero_iff x).mp (Nat.lt_one_iff.mp hx)
  subst hx0
  exact coeff_zero_X i

private theorem lowVanishing_mul_le (a b : ℕ) :
    lowVanishing σ R a * lowVanishing σ R b ≤ lowVanishing σ R (a + b) := by
  classical
  rw [Ideal.mul_le]
  intro r hr s hs x hx
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  by_cases hi : ij.1.degree < a
  · rw [hr ij.1 hi, zero_mul]
  · have hdeg : x.degree = ij.1.degree + ij.2.degree := by rw [← hij, map_add]
    have hj : ij.2.degree < b := by omega
    rw [hs ij.2 hj, mul_zero]

private theorem pow_span_X_le_lowVanishing (N : ℕ) :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ lowVanishing σ R N := by
  induction N with
  | zero =>
    intro q _ x hx
    exact absurd hx (Nat.not_lt_zero _)
  | succ n ih =>
    rw [pow_succ]
    exact (Ideal.mul_mono ih span_X_le_lowVanishing_one).trans (lowVanishing_mul_le n 1)

private theorem pow_span_X_le_of_forall_monomial_mem [Finite σ] (N : ℕ) (I : Ideal (MvPowerSeries σ
  R))
    (hI : ∀ y : σ →₀ ℕ, y.degree = N → (monomial y (1 : R) : MvPowerSeries σ R) ∈ I) :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ I := fun q hq =>
  mem_of_forall_coeff_eq_zero_of_forall_monomial_mem N I hI q (pow_span_X_le_lowVanishing N hq)

private theorem pow_span_X_le_of_forall_coeff_eq_zero_imp_mem (N : ℕ) (I : Ideal (MvPowerSeries σ
  R))
    (hI : ∀ q : MvPowerSeries σ R, (∀ x : σ →₀ ℕ, x.degree < N → coeff x q = 0) → q ∈ I) :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ I := fun q hq =>
  hI q (pow_span_X_le_lowVanishing N hq)

private theorem mem_of_pow_span_X_le [Finite σ] (N : ℕ) (I : Ideal (MvPowerSeries σ R))
    (hN : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ I)
    (q : MvPowerSeries σ R) (hq : ∀ x : σ →₀ ℕ, x.degree < N → coeff x q = 0) : q ∈ I :=
  hN (MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero N q hq)

private theorem pow_span_X_le_of_forall_X_pow_mem [Fintype σ] (N : ℕ) (I : Ideal (MvPowerSeries σ
  R))
    (hI : ∀ i : σ, (X i : MvPowerSeries σ R) ^ N ∈ I) :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ (Fintype.card σ * (N - 1) + 1) ≤ I := by
  classical
  refine pow_span_X_le_of_forall_monomial_mem _ I fun y hy => ?_

  obtain ⟨i, hi⟩ : ∃ i, N ≤ y i := by
    by_contra hcon
    push Not at hcon
    have hle : y.degree ≤ Fintype.card σ * (N - 1) := by
      rw [Finsupp.degree_eq_sum]
      calc ∑ i, y i ≤ ∑ _i : σ, (N - 1) := Finset.sum_le_sum fun i _ => by have := hcon i; omega
        _ = Fintype.card σ * (N - 1) := by rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
    omega
  have hsplit : y = Finsupp.single i N + (y - Finsupp.single i N) := by
    rw [add_tsub_cancel_of_le]
    intro j
    by_cases hij : i = j
    · subst hij; rwa [Finsupp.single_eq_same]
    · rw [Finsupp.single_apply, ite_eq_right hij]; exact Nat.zero_le _
  rw [hsplit, ← one_mul (1 : R), ← monomial_mul_monomial, ← X_pow_eq]
  exact Ideal.mul_mem_right _ _ (hI i)

end Bridges

end TruncBCEngine

open scoped TensorProduct

open scoped TensorProduct

namespace MvPowerSeries

/-- Base change of a finite power-series quotient: if every `X s ^ N` lies in
the span of the `φ i` for some `N`, then tensoring the quotient with `S`
gives the corresponding quotient of power series over `S`, compatibly with
the canonical maps. -/
public theorem exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    {σ : Type*} [Fintype σ] {ι : Type*} (φ : ι → MvPowerSeries σ R)
    (hN : ∃ N : ℕ, ∀ s : σ, (MvPowerSeries.X s : MvPowerSeries σ R) ^ N ∈
      Ideal.span (Set.range φ)) :
    ∃ e : S ⊗[R] (MvPowerSeries σ R ⧸ Ideal.span (Set.range φ)) ≃ₐ[S]
        (MvPowerSeries σ S ⧸ Ideal.span
          (Set.range fun i => MvPowerSeries.map (algebraMap R S) (φ i))),
      ∀ (s : S) (q : MvPowerSeries σ R),
        e (s ⊗ₜ[R] Ideal.Quotient.mk (Ideal.span (Set.range φ)) q) =
          s • Ideal.Quotient.mk
            (Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap R S) (φ i)))
            (MvPowerSeries.map (algebraMap R S) q) := by
  classical
  obtain ⟨N, hN⟩ := hN
  have hM := TruncBCEngine.pow_span_X_le_of_forall_X_pow_mem N (Ideal.span (Set.range φ)) hN
  exact ⟨TruncBCEngine.baseChangeEquiv S φ _ hM,
    fun s q => TruncBCEngine.baseChangeEquiv_tmul φ _ hM s q⟩

end MvPowerSeries
