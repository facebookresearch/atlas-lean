/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.lean`
and
`P2M/Sol/S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.lean`
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

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Generic flatness

Let `A` be a Noetherian domain, `B` a finite type `A`-algebra and `M` a finite `B`-module. Then
there is a nonzero `a : A` such that the localization of `M` at the powers of `a` is flat over `A`.

## Main results

* `Module.Flat.exists_ne_zero_flat_localization_tensorProduct`

## References

* [Stacks Project, Lemma 10.118.1 (Tag 051R)](https://stacks.math.columbia.edu/tag/051R), which
  proves that the localization is free over the localization of `A`
-/

@[expose] public section

open TensorProduct

namespace Module.Flat.GenericFlatness

variable {A : Type*} [CommRing A]

/-- `KT a M`: every element of the kernel of `M ⊗ I → M ⊗ A` is killed by a power of `a`. -/
private def KT (a : A) (M : Type*) [AddCommGroup M] [Module A M] : Prop :=
  ∀ (I : Ideal A) (k : M ⊗[A] I), LinearMap.lTensor M I.subtype k = 0 → ∃ n : ℕ, a ^ n • k = 0

section Basic

variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

private lemma KT.mul_right {a : A} (c : A) (h : KT a M) : KT (a * c) M := fun I k hk => by
  obtain ⟨n, hn⟩ := h I k hk
  exact ⟨n, by rw [mul_pow, mul_comm, mul_smul, hn, smul_zero]⟩

private lemma KT.of_pow {a : A} {m : ℕ} (h : KT (a ^ m) M) : KT a M := fun I k hk => by
  obtain ⟨n, hn⟩ := h I k hk
  exact ⟨m * n, by rw [pow_mul, hn]⟩

private lemma KT.of_linearEquiv {a : A} (e : M ≃ₗ[A] N) (h : KT a M) : KT a N :=
  fun I k hk => by
  have hk' : LinearMap.lTensor M I.subtype (LinearMap.rTensor I e.symm.toLinearMap k) = 0 := by
    rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
      ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply, hk, map_zero]
  obtain ⟨n, hn⟩ := h I _ hk'
  refine ⟨n, ?_⟩
  have : k = LinearMap.rTensor I e.toLinearMap (LinearMap.rTensor I e.symm.toLinearMap k) := by
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    simp
  rw [this, ← map_smul, hn, map_zero]

private lemma KT.of_flat (a : A) [Module.Flat A M] : KT a M := fun I k hk =>
  ⟨0, by
    have := Module.Flat.lTensor_preserves_injective_linearMap (M := M) I.subtype
      I.injective_subtype
    rw [pow_zero, one_smul]
    exact this (by rw [hk, map_zero])⟩

private lemma smul_tensor_eq_zero {a : A} (h : ∀ m : M, a • m = 0) {P : Type*}
    [AddCommGroup P] [Module A P] (k : M ⊗[A] P) : a • k = 0 := by
  induction k using TensorProduct.inductionOn with
  | tmul m x => rw [TensorProduct.smul_tmul', h, TensorProduct.zero_tmul]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

private lemma KT.of_smul_eq_zero {a : A} (h : ∀ m : M, a • m = 0) : KT a M := fun _ k _ =>
  ⟨1, by rw [pow_one]; exact smul_tensor_eq_zero h k⟩

end Basic

section Extension

variable {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
  [AddCommGroup M₃] [Module A M₃]

private lemma rid_rTensor (ι : M₁ →ₗ[A] M₂) (z : M₁ ⊗[A] A) :
    TensorProduct.rid A M₂ (LinearMap.rTensor A ι z) = ι (TensorProduct.rid A M₁ z) := by
  induction z using TensorProduct.inductionOn with
  | tmul m r => simp
  | add u v hu hv => simp only [map_add, hu, hv]

private lemma rTensor_injective_of_injective (ι : M₁ →ₗ[A] M₂) (hι : Function.Injective ι) :
    Function.Injective (LinearMap.rTensor A ι) := by
  intro x y hxy
  have h := congrArg (TensorProduct.rid A M₂) hxy
  rw [rid_rTensor, rid_rTensor] at h
  exact (TensorProduct.rid A M₁).injective (hι h)

private theorem KT.extension {a₁ a₃ : A} (ι : M₁ →ₗ[A] M₂) (π : M₂ →ₗ[A] M₃)
    (hι : Function.Injective ι) (hex : Function.Exact ι π) (hπ : Function.Surjective π)
    (h₁ : KT a₁ M₁) (h₃ : KT a₃ M₃) : KT (a₁ * a₃) M₂ := by
  intro I k hk
  have hk3 : LinearMap.lTensor M₃ I.subtype (LinearMap.rTensor I π k) = 0 := by
    rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
      ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply, hk, map_zero]
  obtain ⟨n, hn⟩ := h₃ I _ hk3
  have hmem : a₃ ^ n • k ∈ Set.range (LinearMap.rTensor I ι) := by
    refine (_root_.rTensor_exact (↥I) hex hπ _).mp ?_
    rw [map_smul, hn]
  obtain ⟨y, hy⟩ := hmem
  have hy0 : LinearMap.lTensor M₁ I.subtype y = 0 := by
    apply rTensor_injective_of_injective ι hι
    rw [map_zero, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
      ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, hy, map_smul, hk, smul_zero]
  obtain ⟨m, hm⟩ := h₁ I y hy0
  refine ⟨m + n, ?_⟩
  have e1 : (a₁ * a₃) ^ (m + n) = (a₁ ^ n * a₃ ^ m) * (a₁ ^ m * a₃ ^ n) := by ring
  rw [e1, mul_smul, mul_smul (a₁ ^ m), ← hy, ← map_smul, hm, map_zero, smul_zero]

end Extension

section Union

variable {M : Type*} [AddCommGroup M] [Module A M]

private theorem KT.of_directed_cover {ι' : Type*} (N : ι' → Submodule A M)
    (hdir : Directed (· ≤ ·) N) (hcov : ∀ m : M, ∃ i, m ∈ N i) {a : A}
    (h : ∀ i, KT a (N i)) : KT a M := by
  classical
  intro I k hk
  have hlift : ∀ k : M ⊗[A] I, ∃ i, k ∈ Set.range (LinearMap.rTensor I (N i).subtype) := by
    intro k
    induction k using TensorProduct.inductionOn with
    | tmul m x =>
      obtain ⟨i, hi⟩ := hcov m
      exact ⟨i, ⟨m, hi⟩ ⊗ₜ x, rfl⟩
    | add x y hx hy =>
      obtain ⟨i, x', hx'⟩ := hx
      obtain ⟨j, y', hy'⟩ := hy
      obtain ⟨l, hil, hjl⟩ := hdir i j
      refine ⟨l, LinearMap.rTensor I (Submodule.inclusion hil) x' +
        LinearMap.rTensor I (Submodule.inclusion hjl) y', ?_⟩
      rw [map_add, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, ← LinearMap.comp_apply,
        ← LinearMap.rTensor_comp, Submodule.subtype_comp_inclusion,
        Submodule.subtype_comp_inclusion, hx', hy']
  obtain ⟨i, k', rfl⟩ := hlift k
  have hk' : LinearMap.lTensor (N i) I.subtype k' = 0 := by
    apply rTensor_injective_of_injective (N i).subtype (N i).injective_subtype
    rw [map_zero, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
      ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, hk]
  obtain ⟨n, hn⟩ := h i I k' hk'
  exact ⟨n, by rw [← map_smul, hn, map_zero]⟩

end Union

section Base

variable [IsDomain A] {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]

private theorem base_case : ∃ a : A, a ≠ 0 ∧ KT a M := by
  classical
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := A) (M := M)
  let v : ↥G → M := fun g => (g : M)
  obtain ⟨T, hTind, hTmax⟩ := exists_maximal_linearIndepOn A v
  set F : Submodule A M := Submodule.span A (Set.range fun x : T => v x) with hFdef
  have hFeq : Submodule.span A (v '' T) = F := by rw [hFdef, Set.image_eq_range]
  have hli : LinearIndependent A (fun x : T => v x) := hTind
  have : Module.Free A F := Module.Free.of_basis (Module.Basis.span hli)
  choose! c hc0 hc using hTmax
  let a : A := ∏ g ∈ Finset.univ.filter (fun g : ↥G => g ∉ T), c g
  have ha : a ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun g hg => hc0 g (Finset.mem_filter.mp hg).2
  have hgen : ∀ g : ↥G, a • v g ∈ F := by
    intro g
    by_cases hgT : g ∈ T
    · exact F.smul_mem a (Submodule.subset_span ⟨⟨g, hgT⟩, rfl⟩)
    · have hmem : g ∈ Finset.univ.filter (fun g : ↥G => g ∉ T) :=
        Finset.mem_filter.mpr ⟨by simp, hgT⟩
      obtain ⟨d, hd⟩ : c g ∣ a := Finset.dvd_prod_of_mem c hmem
      rw [hd, mul_comm, mul_smul, ← hFeq]
      exact Submodule.smul_mem _ d (hc g hgT)
  have haF : ∀ m : M, a • m ∈ F := by
    intro m
    have hm : m ∈ Submodule.span A (G : Set M) := by rw [hG]; trivial
    induction hm using Submodule.span_induction with
    | mem x hx => exact hgen ⟨x, hx⟩
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact F.add_mem hx hy
    | smul r x _ hx => rw [smul_comm]; exact F.smul_mem r hx
  refine ⟨a, ha, ?_⟩
  have h := KT.extension (a₁ := 1) (a₃ := a) F.subtype F.mkQ F.injective_subtype
    (LinearMap.exact_subtype_mkQ F) (Submodule.mkQ_surjective F) (KT.of_flat 1)
    (KT.of_smul_eq_zero fun q => by
      obtain ⟨m, rfl⟩ := F.mkQ_surjective q
      rw [← map_smul, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero F).mpr (haF m)])
  rwa [one_mul] at h

end Base

section Filt

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  (f : M →ₗ[R] M) (M' : Submodule R M)

/-- The filtration `M' ⊔ f M' ⊔ ... ⊔ f^i M'`. -/
private def filt : ℕ → Submodule R M
  | 0 => M'
  | i + 1 => filt i ⊔ M'.map (f ^ (i + 1))

private lemma filt_zero : filt f M' 0 = M' := rfl

private lemma filt_succ (i : ℕ) : filt f M' (i + 1) = filt f M' i ⊔ M'.map (f ^ (i + 1)) := rfl

private lemma filt_le_succ (i : ℕ) : filt f M' i ≤ filt f M' (i + 1) := by
  rw [filt_succ]; exact le_sup_left

private lemma filt_mono : Monotone (filt f M') := monotone_nat_of_le_succ (filt_le_succ f M')

private lemma map_filt_le (i : ℕ) : (filt f M' i).map f ≤ filt f M' (i + 1) := by
  induction i with
  | zero =>
    rw [filt_succ, filt_zero, pow_one]
    exact le_sup_right
  | succ i ih =>
    rw [filt_succ, Submodule.map_sup, filt_succ f M' (i + 1)]
    refine sup_le (ih.trans (filt_le_succ f M' _)) ?_
    rw [← Submodule.map_comp]
    have : f ∘ₗ f ^ (i + 1) = f ^ (i + 1 + 1) := by rw [pow_succ' f (i + 1)]; rfl
    rw [this]
    exact le_sup_right

private lemma pow_apply_mem_filt {i : ℕ} {x : M} (hx : x ∈ filt f M' i) (j : ℕ) :
    (f ^ j) x ∈ filt f M' (i + j) := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    rw [pow_succ', mul_apply_eq_comp, ← add_assoc]
    exact map_filt_le f M' _ (Submodule.mem_map_of_mem ih)

private lemma pow_apply_mem_filt' (m : M') (j : ℕ) : (f ^ j) (m : M) ∈ filt f M' j := by
  simpa using pow_apply_mem_filt f M' (i := 0) m.2 j

private def K (i : ℕ) : Submodule R M' := ((filt f M' i).comap (f ^ (i + 1))).comap M'.subtype

private lemma mem_K (i : ℕ) (m : M') : m ∈ K f M' i ↔ (f ^ (i + 1)) (m : M) ∈ filt f M' i :=
  Iff.rfl

private lemma K_mono : Monotone (K f M') := by
  refine monotone_nat_of_le_succ fun i m hm => ?_
  rw [mem_K] at hm ⊢
  rw [pow_succ', mul_apply_eq_comp]
  exact map_filt_le f M' i (Submodule.mem_map_of_mem hm)

private abbrev Gr (i : ℕ) :=
  ↥(filt f M' (i + 1)) ⧸ (filt f M' i).comap (filt f M' (i + 1)).subtype

private def toGr (i : ℕ) : M' →ₗ[R] Gr f M' i :=
  ((filt f M' i).comap (filt f M' (i + 1)).subtype).mkQ ∘ₗ
    (LinearMap.codRestrict (filt f M' (i + 1)) ((f ^ (i + 1)) ∘ₗ M'.subtype)
      (fun m => pow_apply_mem_filt' f M' m (i + 1)))

private lemma toGr_apply (i : ℕ) (m : M') :
    toGr f M' i m =
      Submodule.Quotient.mk ⟨(f ^ (i + 1)) (m : M), pow_apply_mem_filt' f M' m (i + 1)⟩ :=
  rfl

private lemma ker_toGr (i : ℕ) : LinearMap.ker (toGr f M' i) = K f M' i := by
  ext m
  rw [LinearMap.mem_ker, toGr_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, mem_K]
  rfl

private lemma toGr_surjective (i : ℕ) : Function.Surjective (toGr f M' i) := by
  intro q
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.mkQ_surjective _ q
  rw [filt_succ] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.mp hz
  refine ⟨⟨m, hm⟩, ?_⟩
  rw [toGr_apply, Submodule.mkQ_apply, eq_comm, Submodule.Quotient.eq, Submodule.mem_comap]
  simpa using hy

private noncomputable def grEquiv (i : ℕ) : (M' ⧸ K f M' i) ≃ₗ[R] Gr f M' i :=
  (Submodule.quotEquivOfEq _ _ (ker_toGr f M' i).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (toGr_surjective f M' i))

section WithBase

variable [Algebra A R] [Module A M] [IsScalarTower A R M]

private theorem KT_filt_succ {a : A} (i : ℕ) (ih : KT a (filt f M' i))
    (hGr : KT a (Gr f M' i)) : KT a (filt f M' (i + 1)) := by
  let ι : ↥(filt f M' i) →ₗ[A] ↥(filt f M' (i + 1)) :=
    (Submodule.inclusion (filt_le_succ f M' i)).restrictScalars A
  let π : ↥(filt f M' (i + 1)) →ₗ[A] Gr f M' i :=
    ((filt f M' i).comap (filt f M' (i + 1)).subtype).mkQ.restrictScalars A
  have hι : Function.Injective ι := Submodule.inclusion_injective (filt_le_succ f M' i)
  have hπ : Function.Surjective π := by
    intro q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact ⟨x, rfl⟩
  have hex : Function.Exact ι π := by
    intro x
    change Submodule.Quotient.mk x = 0 ↔
      x ∈ Set.range (Submodule.inclusion (filt_le_succ f M' i))
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
      Set.mem_range]
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.2
  have h := KT.extension ι π hι hex hπ ih hGr
  rw [← pow_two] at h
  exact h.of_pow

end WithBase

end Filt

section Step

universe uM

variable {B' : Type*} [CommRing B'] [Algebra A B'] [IsNoetherianRing B'] [IsDomain A]

open Polynomial in
private theorem poly_step
    (IH : ∀ (N : Type uM) [AddCommGroup N] [Module A N] [Module B' N] [IsScalarTower A B' N]
      [Module.Finite B' N], ∃ a : A, a ≠ 0 ∧ KT a N)
    (M : Type uM) [AddCommGroup M] [Module A M] [Module B' M] [Module B'[X] M]
    [IsScalarTower A B' M] [IsScalarTower B' B'[X] M] [Module.Finite B'[X] M] :
    ∃ a : A, a ≠ 0 ∧ KT a M := by
  classical
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := B'[X]) (M := M)
  let M' : Submodule B' M := Submodule.span B' (G : Set M)
  have : Module.Finite B' M' := Module.Finite.iff_fg.mpr (Submodule.fg_span G.finite_toSet)
  have : IsNoetherian B' M' := isNoetherian_of_isNoetherianRing_of_finite B' M'
  let f : M →ₗ[B'] M :=
    { toFun := fun m => (X : B'[X]) • m
      map_add' := fun x y => smul_add _ _ _
      map_smul' := fun b m => by
        rw [RingHom.id_apply, ← algebraMap_smul (A := B'[X]) b,
          ← algebraMap_smul (A := B'[X]) b, smul_smul, smul_smul, mul_comm] }
  have hf : ∀ (j : ℕ) (m : M), (f ^ j) m = (X ^ j : B'[X]) • m := by
    intro j m
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', mul_apply_eq_comp, ih, pow_succ', mul_smul]; rfl
  obtain ⟨i₀, hi₀⟩ :=
    (monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian B' M'))
      ⟨K f M', K_mono f M'⟩
  simp only [OrderHom.coe_mk] at hi₀
  have hpieces : ∀ i, ∃ a : A, a ≠ 0 ∧ KT a (M' ⧸ K f M' i) := fun i => IH (↥M' ⧸ K f M' i)
  choose aa haa hKT using hpieces
  obtain ⟨a₀, ha₀, hKT₀⟩ := IH M'
  let a : A := a₀ * ∏ i ∈ Finset.range (i₀ + 1), aa i
  have ha : a ≠ 0 := mul_ne_zero ha₀ (Finset.prod_ne_zero_iff.mpr fun i _ => haa i)
  have hdvd : ∀ i ≤ i₀, aa i ∣ a := fun i hi =>
    (Finset.dvd_prod_of_mem aa (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))).mul_left a₀
  have hall : ∀ i, KT a (M' ⧸ K f M' i) := by
    intro i
    by_cases hi : i ≤ i₀
    · obtain ⟨d, hd⟩ := hdvd i hi
      rw [hd]
      exact (hKT i).mul_right d
    · have hle : i₀ ≤ i := le_of_not_ge hi
      have heq : K f M' i₀ = K f M' i := hi₀ i hle
      obtain ⟨d, hd⟩ := hdvd i₀ le_rfl
      rw [hd]
      exact ((hKT i₀).mul_right d).of_linearEquiv
        ((Submodule.quotEquivOfEq _ _ heq).restrictScalars A)
  have hfilt : ∀ i, KT a (filt f M' i) := by
    intro i
    induction i with
    | zero => exact hKT₀.mul_right _
    | succ i ih =>
      have hGr : KT a (Gr f M' i) :=
        (hall i).of_linearEquiv ((grEquiv f M' i).restrictScalars A)
      exact KT_filt_succ f M' i ih hGr
  have hcov : ∀ m : M, ∃ i, m ∈ filt f M' i := by
    intro m
    have hm : m ∈ Submodule.span B'[X] (G : Set M) := by rw [hG]; trivial
    induction hm using Submodule.span_induction with
    | mem x hx => exact ⟨0, Submodule.subset_span hx⟩
    | zero => exact ⟨0, Submodule.zero_mem _⟩
    | add x y _ _ hx hy =>
      obtain ⟨i, hi⟩ := hx
      obtain ⟨j, hj⟩ := hy
      exact ⟨max i j, Submodule.add_mem _ (filt_mono f M' (le_max_left i j) hi)
        (filt_mono f M' (le_max_right i j) hj)⟩
    | smul q x _ hx =>
      obtain ⟨i, hi⟩ := hx
      induction q using Polynomial.induction_on' with
      | add q₁ q₂ h₁ h₂ =>
        obtain ⟨i₁, hi₁⟩ := h₁
        obtain ⟨i₂, hi₂⟩ := h₂
        refine ⟨max i₁ i₂, ?_⟩
        rw [add_smul]
        exact Submodule.add_mem _ (filt_mono f M' (le_max_left _ _) hi₁)
          (filt_mono f M' (le_max_right _ _) hi₂)
      | monomial n b =>
        refine ⟨i + n, ?_⟩
        rw [← Polynomial.C_mul_X_pow_eq_monomial, mul_smul, ← hf, Polynomial.C_eq_algebraMap,
          algebraMap_smul]
        exact Submodule.smul_mem _ b (pow_apply_mem_filt f M' hi n)
  refine ⟨a, ha, ?_⟩
  refine KT.of_directed_cover (ι' := ℕ) (fun i => (filt f M' i).restrictScalars A) ?_ hcov hfilt
  exact (Monotone.directed_le fun i j hij => (filt_mono f M' hij : _))

end Step

section Induction

universe uM

variable [IsDomain A] [IsNoetherianRing A]

private lemma finite_of_surjective_ringHom {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ) (M : Type*) [AddCommGroup M] [Module S M]
    [Module R M] (hsmul : ∀ (r : R) (m : M), r • m = φ r • m) [Module.Finite S M] :
    Module.Finite R M := by
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := S) (M := M)
  refine ⟨G, ?_⟩
  rw [eq_top_iff]
  rintro m -
  have hm : m ∈ Submodule.span S (G : Set M) := by rw [hG]; trivial
  induction hm using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul s x _ hx =>
    obtain ⟨r, rfl⟩ := hφ s
    rw [← hsmul]
    exact Submodule.smul_mem _ r hx

private theorem mvPolynomial_case (n : ℕ) :
    ∀ (M : Type uM) [AddCommGroup M] [Module A M] [Module (MvPolynomial (Fin n) A) M]
      [IsScalarTower A (MvPolynomial (Fin n) A) M] [Module.Finite (MvPolynomial (Fin n) A) M],
      ∃ a : A, a ≠ 0 ∧ KT a M := by
  induction n with
  | zero =>
    intro M _ _ _ _ _
    have : Module.Finite A (MvPolynomial (Fin 0) A) :=
      Module.Finite.equiv (MvPolynomial.isEmptyAlgEquiv A (Fin 0)).toLinearEquiv.symm
    have : Module.Finite A M := Module.Finite.trans (MvPolynomial (Fin 0) A) M
    exact base_case
  | succ n ih =>
    intro M _ _ _ _ _
    let P := MvPolynomial (Fin n) A
    let e : MvPolynomial (Fin (n + 1)) A ≃ₐ[A] Polynomial P := MvPolynomial.finSuccEquiv A n
    let mPX : Module (Polynomial P) M := Module.compHom M e.symm.toRingEquiv.toRingHom
    let mP : Module P M := Module.compHom M (e.symm.toRingEquiv.toRingHom.comp Polynomial.C)
    have hPX : ∀ (q : Polynomial P) (m : M), q • m = e.symm q • m := fun _ _ => rfl
    have hP : ∀ (p : P) (m : M), p • m = e.symm (Polynomial.C p) • m := fun _ _ => rfl
    have : IsScalarTower A P M := IsScalarTower.of_algebraMap_smul fun r m => by
      rw [hP, ← Polynomial.algebraMap_apply, AlgEquiv.commutes, algebraMap_smul]
    have : IsScalarTower P (Polynomial P) M := IsScalarTower.of_algebraMap_smul fun p m => by
      rw [hPX, hP, Polynomial.algebraMap_eq]
    have : Module.Finite (Polynomial P) M :=
      finite_of_surjective_ringHom e.symm.toRingEquiv.toRingHom e.symm.surjective M
        (fun q m => hPX q m)
    exact poly_step (B' := P) (fun N _ _ _ _ _ => ih N) M

private theorem finiteType_case {B : Type*} [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (M : Type uM) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Module.Finite B M] : ∃ a : A, a ≠ 0 ∧ KT a M := by
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType A B)
  let P := MvPolynomial (Fin n) A
  let mP : Module P M := Module.compHom M φ.toRingHom
  have hP : ∀ (p : P) (m : M), p • m = φ p • m := fun _ _ => rfl
  have : IsScalarTower A P M := IsScalarTower.of_algebraMap_smul fun r m => by
    rw [hP, AlgHom.commutes, algebraMap_smul]
  have : Module.Finite P M := finite_of_surjective_ringHom φ.toRingHom hφ M hP
  exact mvPolynomial_case n M

end Induction

section Convert

variable {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']

private theorem flat_of_isLocalizedModule (S : Submonoid A) (g : M →ₗ[A] M')
    [IsLocalizedModule S g]
    (h : ∀ (I : Ideal A) (k : M ⊗[A] I), LinearMap.lTensor M I.subtype k = 0 →
      ∃ s ∈ S, s • k = 0) :
    Module.Flat A M' := by
  rw [Module.Flat.iff_lTensor_injective']
  intro I
  let GX := TensorProduct.AlgebraTensorModule.rTensor A (↥I) g
  let GY := TensorProduct.AlgebraTensorModule.rTensor A A g
  have : IsLocalizedModule S GX := inferInstance
  have : IsLocalizedModule S GY := inferInstance
  have hmap : IsLocalizedModule.map S GX GY
      (TensorProduct.AlgebraTensorModule.lTensor A M I.subtype) =
      TensorProduct.AlgebraTensorModule.lTensor A M' I.subtype :=
    IsLocalizedModule.map_lTensor A S I.subtype g
  refine (injective_iff_map_eq_zero _).mpr fun z hz => ?_
  obtain ⟨⟨k, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S GX z
  simp only [Function.uncurry_apply_pair] at hz ⊢
  have h1 : IsLocalizedModule.mk' GY
      (TensorProduct.AlgebraTensorModule.lTensor A M I.subtype k) s = 0 := by
    rw [← IsLocalizedModule.map_mk' S GX GY, hmap,
      TensorProduct.AlgebraTensorModule.coe_lTensor, hz]
  obtain ⟨s', hs'⟩ := (IsLocalizedModule.mk'_eq_zero' GY s).mp h1
  have h2 : LinearMap.lTensor M I.subtype (s'.1 • k) = 0 := by
    rw [map_smul, ← TensorProduct.AlgebraTensorModule.coe_lTensor (A := A)]
    exact hs'
  obtain ⟨s'', hs''S, hs''⟩ := h I _ h2
  rw [IsLocalizedModule.mk'_eq_zero' GX s]
  refine ⟨⟨s'', hs''S⟩ * s', ?_⟩
  rw [Submonoid.smul_def, Submonoid.coe_mul, mul_smul]
  exact hs''

variable {B : Type*} [CommRing B] [Algebra A B] [Module B M] [IsScalarTower A B M]

private theorem isLocalizedModule_powers (a : A) :
    IsLocalizedModule (Submonoid.powers a)
      ((TensorProduct.mk B (Localization (Submonoid.powers (algebraMap A B a))) M
        1).restrictScalars A) := by
  set T : Submonoid B := Submonoid.powers (algebraMap A B a)
  set Ba := Localization T
  have hT : IsLocalizedModule T (TensorProduct.mk B Ba M 1) := inferInstance
  have hmemT : ∀ t ∈ T, ∃ n : ℕ, algebraMap A B (a ^ n) = t := fun t ht => by
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp ht
    exact ⟨n, map_pow _ _ _⟩
  refine (isLocalizedModule_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨s, n, rfl⟩
    have hu := hT.map_units ⟨algebraMap A B a ^ n, n, rfl⟩
    rw [Module.End.isUnit_iff] at hu ⊢
    have heq : ⇑((algebraMap A (Module.End A (Ba ⊗[B] M))) (a ^ n)) =
        ⇑((algebraMap B (Module.End B (Ba ⊗[B] M))) (algebraMap A B a ^ n)) := by
      funext y
      change (a ^ n) • y = (algebraMap A B a ^ n) • y
      rw [← map_pow, algebraMap_smul]
    rw [heq]
    exact hu
  · intro y
    obtain ⟨⟨m, t, ht⟩, hmt⟩ := hT.surj y
    obtain ⟨n, hn⟩ := hmemT t ht
    refine ⟨⟨m, ⟨a ^ n, n, rfl⟩⟩, ?_⟩
    change (a ^ n) • y = _
    rw [← algebraMap_smul B (a ^ n) y, hn]
    exact hmt
  · intro x₁ x₂ hx
    obtain ⟨⟨t, ht⟩, htx⟩ := hT.exists_of_eq hx
    obtain ⟨n, hn⟩ := hmemT t ht
    refine ⟨⟨a ^ n, n, rfl⟩, ?_⟩
    change (a ^ n) • x₁ = (a ^ n) • x₂
    rw [← algebraMap_smul B (a ^ n) x₁, ← algebraMap_smul B (a ^ n) x₂, hn]
    exact htx

end Convert

end Module.Flat.GenericFlatness

open Module.Flat.GenericFlatness in
/-- **Generic flatness.** A finite module over a finite type algebra `B` over a Noetherian domain
`A` becomes flat over `A` after inverting the image of some nonzero `a : A`.

Source: [Stacks Project, Lemma 10.118.1 (Tag 051R)](https://stacks.math.columbia.edu/tag/051R),
which proves the stronger statement that the localized module is free over the localization of
`A`. -/
public theorem Module.Flat.exists_ne_zero_flat_localization_tensorProduct
    {A B M : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Module.Finite B M] :
    ∃ a : A, a ≠ 0 ∧
      Module.Flat A (Localization (Submonoid.powers (algebraMap A B a)) ⊗[B] M) := by
  obtain ⟨a, ha, hKT⟩ := finiteType_case (A := A) (B := B) M
  refine ⟨a, ha, ?_⟩
  have := isLocalizedModule_powers (M := M) (B := B) a
  refine flat_of_isLocalizedModule (Submonoid.powers a)
    ((TensorProduct.mk B (Localization (Submonoid.powers (algebraMap A B a))) M
      1).restrictScalars A) fun I k hk => ?_
  obtain ⟨n, hn⟩ := hKT I k hk
  exact ⟨a ^ n, ⟨n, rfl⟩, hn⟩
