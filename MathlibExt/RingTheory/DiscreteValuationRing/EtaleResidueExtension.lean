/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsDiscreteValuationRing_exists_etale_dvr_residueField_equiv_
card_algEquiv_eq_of_isAdicComplete.lean`,
`P2M/Sol/S_IsDiscreteValuationRing_exists_etale_dvr_residueField_equiv_
card_algEquiv_eq_of_isAdicComplete.lean`,
`Theorems/Thm_AdjoinRoot_exists_isLocalRing_etale_residueField_algEquiv_of_isAdicComplete.lean`,
`P2M/Sol/S_AdjoinRoot_exists_isLocalRing_etale_residueField_algEquiv_of_isAdicComplete.lean`,
`Theorems/Thm_IsAdicComplete_of_module_finite_free_map.lean`, and
`P2M/Sol/S_IsAdicComplete_of_module_finite_free_map.lean`
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

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Unramified.LocalRing
import MathlibExt.RingTheory.LocalRing.Henselian

universe u


private theorem isAdicComplete_of_linearEquiv {A : Type*} [CommRing A] (I : Ideal A)
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) [IsAdicComplete I M] : IsAdicComplete I N := by
  rw [← AdicCompletion.of_bijective_iff]
  have h : (AdicCompletion.of I N : N → AdicCompletion I N) =
      AdicCompletion.congr I e ∘ AdicCompletion.of I M ∘ e.symm := by
    funext x
    simp only [Function.comp_apply, AdicCompletion.congr_apply, AdicCompletion.map_of,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [h]
  exact (LinearEquiv.bijective (AdicCompletion.congr I e)).comp
    ((AdicCompletion.of_bijective I M).comp (LinearEquiv.bijective e.symm))

private theorem isAdicComplete_pi_of_fintype {A : Type*} [CommRing A] (I : Ideal A)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)] [∀ i, IsAdicComplete I (M i)] :
    IsAdicComplete I (∀ i, M i) := by
  rw [← AdicCompletion.of_bijective_iff]
  have h : (AdicCompletion.piEquivOfFintype I M : _ → _) ∘
      AdicCompletion.of I (∀ i, M i) = Pi.map fun i => AdicCompletion.of I (M i) := by
    funext x j
    simp [AdicCompletion.pi, AdicCompletion.map_of]
  have hb : Function.Bijective ((AdicCompletion.piEquivOfFintype I M : _ → _) ∘
      AdicCompletion.of I (∀ i, M i)) := by
    rw [h]
    exact Function.Bijective.piMap fun i => AdicCompletion.of_bijective I (M i)
  exact (Function.Bijective.of_comp_iff'
    (LinearEquiv.bijective (AdicCompletion.piEquivOfFintype I M)) _).1 hb

private theorem isAdicComplete_map_algebraMap_of_finite_free {A : Type*} [CommRing A]
    (I : Ideal A) [IsAdicComplete I A] (R : Type*) [CommRing R] [Algebra A R]
    [Module.Finite A R] [Module.Free A R] :
    IsAdicComplete (I.map (algebraMap A R)) R := by
  classical
  rw [IsAdicComplete.map_algebraMap_iff]
  haveI : IsAdicComplete I (Module.Free.ChooseBasisIndex A R → A) :=
    isAdicComplete_pi_of_fintype I _
  exact isAdicComplete_of_linearEquiv I (Module.Free.chooseBasis A R).equivFun.symm

open Polynomial IsLocalRing in
private theorem adjoinRoot_exists_isLocalRing_etale_residueField_algEquiv_of_isAdicComplete
    (R : Type*) [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (f : R[X]) (hfm : f.Monic) [Fact (Irreducible (f.map (residue R)))]
    [Algebra.IsSeparable (ResidueField R) (AdjoinRoot (f.map (residue R)))] :
    ∃ (_ : IsLocalRing (AdjoinRoot f)) (_ : IsLocalHom (algebraMap R (AdjoinRoot f))),
      Module.Finite R (AdjoinRoot f) ∧ Module.Free R (AdjoinRoot f) ∧
      Algebra.Etale R (AdjoinRoot f) ∧
      IsAdicComplete (maximalIdeal (AdjoinRoot f)) (AdjoinRoot f) ∧
      Ideal.map (algebraMap R (AdjoinRoot f)) (maximalIdeal R) =
        maximalIdeal (AdjoinRoot f) ∧
      Nonempty (ResidueField (AdjoinRoot f) ≃ₐ[ResidueField R]
        AdjoinRoot (f.map (residue R))) := by
  classical
  set g : (ResidueField R)[X] := f.map (residue R) with hg
  have hfg : Polynomial.map (residue R) f = g := rfl
  set 𝔪 : Ideal R := maximalIdeal R with h𝔪
  let W := AdjoinRoot f
  let pb : PowerBasis R W := AdjoinRoot.powerBasis' hfm
  haveI : Module.Free R W := Module.Free.of_basis pb.basis
  haveI : Module.Finite R W := Module.Finite.of_basis pb.basis
  have hσ : algebraMap R W = AdjoinRoot.of f := AdjoinRoot.algebraMap_eq f
  set J : Ideal W := 𝔪.map (AdjoinRoot.of f) with hJ
  let e1 : (W ⧸ J) ≃+* AdjoinRoot (Polynomial.map (residue R) f) :=
    (AdjoinRoot.quotEquivQuotMap f 𝔪).toRingEquiv
  let e2 : AdjoinRoot (Polynomial.map (residue R) f) ≃ₐ[ResidueField R] AdjoinRoot g :=
    AdjoinRoot.algEquivOfEq (ResidueField R) _ _ hfg
  let eJ : (W ⧸ J) ≃+* AdjoinRoot g := e1.trans e2.toRingEquiv
  haveI hJmax : J.IsMaximal :=
    Ideal.Quotient.maximal_of_isField _
      (MulEquiv.isField (Field.toIsField (AdjoinRoot g)) eJ.toMulEquiv)
  have hc : IsAdicComplete J W := by
    have h := isAdicComplete_map_algebraMap_of_finite_free 𝔪 W
    rwa [hσ] at h
  haveI := hc
  haveI : IsLocalRing W := isLocalRing_of_isAdicComplete_maximal J
  have hmaxJ : maximalIdeal W = J := (IsLocalRing.eq_maximalIdeal hJmax).symm
  have hlocal : IsLocalHom (algebraMap R W) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have haI : a ∈ 𝔪 := (mem_maximalIdeal a).mpr hna
    have : algebraMap R W a ∈ maximalIdeal W := by
      rw [hmaxJ, hσ]
      exact Ideal.mem_map_of_mem _ haI
    exact (mem_maximalIdeal _).mp this ha
  haveI := hlocal
  let ιr : ResidueField W ≃+* AdjoinRoot g := (Ideal.quotEquivOfEq hmaxJ).trans eJ
  have hι : ∀ c : ResidueField R, ιr (algebraMap (ResidueField R) (ResidueField W) c) =
      algebraMap (ResidueField R) (AdjoinRoot g) c := by
    intro c
    obtain ⟨r, rfl⟩ := residue_surjective c
    show eJ (Ideal.quotEquivOfEq hmaxJ
      (Ideal.Quotient.mk (maximalIdeal W) (algebraMap R W r))) = _
    rw [Ideal.quotEquivOfEq_mk]
    have h1 : (Ideal.Quotient.mk J) (algebraMap R W r) = algebraMap R (W ⧸ J) r := rfl
    have h2 : eJ (algebraMap R (W ⧸ J) r) =
        algebraMap (ResidueField R) (AdjoinRoot g) (residue R r) := by
      show e2 (AdjoinRoot.quotEquivQuotMap f 𝔪 (algebraMap R (W ⧸ J) r)) = _
      rw [AlgEquiv.commutes]
      have h3 : algebraMap R (AdjoinRoot (Polynomial.map (residue R) f)) r =
          algebraMap (ResidueField R) (AdjoinRoot (Polynomial.map (residue R) f))
            (residue R r) :=
        IsScalarTower.algebraMap_apply R (ResidueField R) _ r
      show e2 (algebraMap R (AdjoinRoot (Polynomial.map (residue R) f)) r) = _
      rw [h3, AlgEquiv.commutes]
    rw [h1, h2]
  let ι : ResidueField W ≃ₐ[ResidueField R] AdjoinRoot g := AlgEquiv.ofRingEquiv hι
  haveI : Algebra.IsSeparable (ResidueField R) (ResidueField W) :=
    AlgEquiv.Algebra.isSeparable ι.symm
  have hmapσ : Ideal.map (algebraMap R W) 𝔪 = maximalIdeal W := by rw [hmaxJ, hσ]
  haveI : Algebra.FormallyUnramified R W :=
    Algebra.FormallyUnramified.of_map_maximalIdeal hmapσ
  haveI : Algebra.Etale R W := Algebra.Etale.of_formallyUnramified_of_flat
  refine ⟨inferInstance, hlocal, inferInstance, inferInstance, inferInstance, ?_,
    hmapσ, ⟨ι⟩⟩
  rw [hmaxJ]; exact hc


namespace EtaleDvrAux
open Polynomial IsLocalRing

section Generic

theorem root_eq_of_sub_mem_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R]
    (g : R[X]) {a b : R}
    (ha : g.IsRoot a) (hb : g.IsRoot b) (hda : IsUnit (g.derivative.eval a))
    (hab : b - a ∈ maximalIdeal R) : a = b := by
  obtain ⟨c, hc⟩ := g.binomExpansion a (b - a)
  rw [add_sub_cancel, hb.eq_zero, ha.eq_zero, zero_add] at hc
  have h1 : (b - a) * (g.derivative.eval a + c * (b - a)) = 0 := by
    have : g.derivative.eval a * (b - a) + c * (b - a) ^ 2 =
        (b - a) * (g.derivative.eval a + c * (b - a)) := by ring
    rw [← this]
    exact hc.symm
  have hu : IsUnit (g.derivative.eval a + c * (b - a)) := by
    obtain ⟨u, hu⟩ := hda
    have hm : c * (b - a) ∈ maximalIdeal R := Ideal.mul_mem_left _ _ hab
    have hj : ((u⁻¹ : Rˣ) : R) * (c * (b - a)) ∈ (⊥ : Ideal R).jacobson :=
      maximalIdeal_le_jacobson _ (Ideal.mul_mem_left _ _ hm)
    have h2 := (Ideal.mem_jacobson_bot.mp hj) 1
    rw [mul_one] at h2
    have h3 : g.derivative.eval a + c * (b - a) = u * (((u⁻¹ : Rˣ) : R) * (c * (b - a)) + 1) := by
      rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul, add_comm, hu]
    rw [h3]
    exact (Units.isUnit u).mul h2
  obtain ⟨v, hv⟩ := hu
  rw [← hv] at h1
  have hba : b - a = 0 := by
    have := congrArg (· * ((v⁻¹ : Rˣ) : R)) h1
    simpa [mul_assoc] using this
  exact (sub_eq_zero.mp hba).symm

theorem exists_root_residue_eq {R : Type*} [CommRing R] [HenselianLocalRing R]
    (g : R[X]) (hg : g.Monic)
    (β : ResidueField R) (hβ : (g.map (residue R)).IsRoot β)
    (hβ' : ¬ ((g.map (residue R)).derivative).IsRoot β) :
    ∃ a : R, g.IsRoot a ∧ residue R a = β := by
  obtain ⟨a₀, rfl⟩ := residue_surjective β
  have h0 : g.eval a₀ ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, ← eval_map_apply]
    exact hβ.eq_zero
  have h1 : IsUnit (g.derivative.eval a₀) := by
    rw [← residue_ne_zero_iff_isUnit, ← eval_map_apply, ← derivative_map]
    exact hβ'
  obtain ⟨a, ha, hsub⟩ := HenselianLocalRing.is_henselian g hg a₀ h0 h1
  refine ⟨a, ha, ?_⟩
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  exact hsub

theorem not_isRoot_derivative_of_separable {K : Type*} [Field K] {p : K[X]}
    (hp : p.Separable) {β : K}
    (hβ : p.IsRoot β) : ¬ p.derivative.IsRoot β := by
  intro h
  have := hp.aeval_derivative_ne_zero (x := β) (by rw [coe_aeval_eq_eval]; exact hβ)
  apply this
  rw [coe_aeval_eq_eval]
  exact h

theorem algHom_bijective {R : Type*} [CommRing R] [IsDomain R] {f : R[X]} (hf : f.Monic)
    (hf1 : f.degree ≠ 0) [IsDomain (AdjoinRoot f)] (φ : AdjoinRoot f →ₐ[R] AdjoinRoot f) :
    Function.Bijective φ := by
  haveI : Module.Finite R (AdjoinRoot f) := hf.finite_adjoinRoot
  haveI : Algebra.IsIntegral R (AdjoinRoot f) := Algebra.IsIntegral.of_finite R _
  have hinjR : Function.Injective (algebraMap R (AdjoinRoot f)) := by
    rw [AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.of.injective_of_degree_ne_zero hf1
  have hinj : Function.Injective φ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_under_eq_bot (R := R)
    rw [Ideal.under_def, eq_bot_iff]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes] at hr
    rw [Ideal.mem_bot]
    exact (map_eq_zero_iff _ hinjR).mp hr
  refine ⟨hinj, ?_⟩

  set S : Set (AdjoinRoot f) := {x | aeval x f = 0} with hS
  have hSfin : S.Finite := by
    apply (((f.map (algebraMap R (AdjoinRoot f))).roots.toFinset).finite_toSet).subset
    intro x hx
    simp only [hS, Set.mem_setOf_eq] at hx
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [mem_roots ((hf.map _).ne_zero), IsRoot, eval_map, ← aeval_def]
    exact hx
  have hmaps : Set.MapsTo φ S S := fun x hx => by
    simp only [hS, Set.mem_setOf_eq] at hx ⊢
    rw [aeval_algHom_apply, hx, map_zero]
  have hbij := (hSfin.injOn_iff_bijOn_of_mapsTo hmaps).mp hinj.injOn
  have hroot : AdjoinRoot.root f ∈ S := by
    simp only [hS, Set.mem_setOf_eq, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  obtain ⟨a, -, ha⟩ := hbij.surjOn hroot
  have hrange : φ.range = ⊤ := by
    rw [eq_top_iff, ← AdjoinRoot.adjoinRoot_eq_top, Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    exact ⟨a, ha⟩
  exact (AlgHom.range_eq_top φ).mp hrange

end Generic

section Construction

variable (W : Type u) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
  [IsAdicComplete (maximalIdeal W) W]
  (k : Type u) [Field k] [Algebra (ResidueField W) k] [FiniteDimensional (ResidueField W) k]
  [Algebra.IsSeparable (ResidueField W) k]

noncomputable def α : k := (Field.exists_primitive_element (ResidueField W) k).choose

theorem adjoin_α_eq_top : IntermediateField.adjoin (ResidueField W) {α W k} = ⊤ :=
  (Field.exists_primitive_element (ResidueField W) k).choose_spec

theorem isIntegral_α : IsIntegral (ResidueField W) (α W k) := .of_finite _ _

noncomputable def fbar : (ResidueField W)[X] := minpoly (ResidueField W) (α W k)

theorem fbar_monic : (fbar W k).Monic := minpoly.monic (isIntegral_α W k)

theorem fbar_irreducible : Irreducible (fbar W k) := minpoly.irreducible (isIntegral_α W k)

theorem fbar_separable : (fbar W k).Separable := Algebra.IsSeparable.isSeparable _ (α W k)

theorem natDegree_fbar : (fbar W k).natDegree = Module.finrank (ResidueField W) k := by
  rw [fbar, ← IntermediateField.adjoin.finrank (isIntegral_α W k), adjoin_α_eq_top]
  exact IntermediateField.finrank_top'

noncomputable def adjoinRootFbarEquiv : AdjoinRoot (fbar W k) ≃ₐ[ResidueField W] k :=
  (IntermediateField.adjoinRootEquivAdjoin (ResidueField W) (isIntegral_α W k)).trans
    ((IntermediateField.equivOfEq (adjoin_α_eq_top W k)).trans IntermediateField.topEquiv)

theorem exists_lift : ∃ q : W[X], q.map (residue W) = fbar W k ∧ q.Monic := by
  obtain ⟨q, hq, -, hmonic⟩ := lifts_and_natDegree_eq_and_monic
    ((mem_lifts _).mpr (map_surjective _ residue_surjective _)) (fbar_monic W k)
  exact ⟨q, hq, hmonic⟩

noncomputable def f : W[X] := (exists_lift W k).choose

theorem map_f : (f W k).map (residue W) = fbar W k := (exists_lift W k).choose_spec.1

theorem monic_f : (f W k).Monic := (exists_lift W k).choose_spec.2

theorem natDegree_f : (f W k).natDegree = Module.finrank (ResidueField W) k := by
  rw [← natDegree_fbar, ← map_f, (monic_f W k).natDegree_map]

theorem natDegree_f_pos : 0 < (f W k).natDegree := by
  rw [natDegree_f]
  exact Module.finrank_pos

theorem degree_f_ne_zero : (f W k).degree ≠ 0 := by
  rw [Polynomial.degree_eq_natDegree (monic_f W k).ne_zero]
  exact_mod_cast (natDegree_f_pos W k).ne'

noncomputable abbrev W' : Type u := AdjoinRoot (f W k)

scoped instance fact_irreducible_map_f : Fact (Irreducible ((f W k).map (residue W))) :=
  ⟨by rw [map_f]; exact fbar_irreducible W k⟩

noncomputable def adjoinRootMapEquiv :
    AdjoinRoot ((f W k).map (residue W)) ≃ₐ[ResidueField W] k :=
  (AdjoinRoot.algEquivOfEq (ResidueField W) _ _ (map_f W k)).trans (adjoinRootFbarEquiv W k)

scoped instance isSeparable_adjoinRoot_map_f :
    Algebra.IsSeparable (ResidueField W) (AdjoinRoot ((f W k).map (residue W))) :=
  AlgEquiv.Algebra.isSeparable (adjoinRootMapEquiv W k).symm

theorem irreducible_f : Irreducible (f W k) :=
  Monic.irreducible_of_irreducible_map (residue W) (f W k) (monic_f W k)
    (by rw [map_f]; exact fbar_irreducible W k)

scoped instance isDomain_W' : IsDomain (W' W k) :=
  AdjoinRoot.isDomain_of_prime (irreducible_f W k).prime

scoped instance moduleFinite_W' : Module.Finite W (W' W k) := (monic_f W k).finite_adjoinRoot

scoped instance isNoetherianRing_W' : IsNoetherianRing (W' W k) := IsNoetherianRing.of_finite W _

theorem algebraMap_W'_injective : Function.Injective (algebraMap W (W' W k)) := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.of.injective_of_degree_ne_zero (degree_f_ne_zero W k)

theorem finrank_W' : Module.finrank W (W' W k) = Module.finrank (ResidueField W) k := by
  rw [(AdjoinRoot.powerBasis' (monic_f W k)).finrank, AdjoinRoot.powerBasis'_dim, natDegree_f]

theorem isDiscreteValuationRing_W' [IsLocalRing (W' W k)]
    (hmap : Ideal.map (algebraMap W (W' W k)) (maximalIdeal W) = maximalIdeal (W' W k)) :
    IsDiscreteValuationRing (W' W k) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hspan : maximalIdeal (W' W k) = Ideal.span {algebraMap W (W' W k) ϖ} := by
    rw [← hmap, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hprinc : (maximalIdeal (W' W k)).IsPrincipal := ⟨algebraMap W (W' W k) ϖ, hspan⟩
  have hnf : ¬ IsField (W' W k) := by
    rw [isField_iff_maximalIdeal_eq, hspan, Ideal.span_singleton_eq_bot,
      map_eq_zero_iff _ (algebraMap_W'_injective W k)]
    exact hϖ.ne_zero
  exact ((IsDiscreteValuationRing.TFAE (W' W k) hnf).out 5 1).mp hprinc

theorem finite_algEquiv : Finite (W' W k ≃ₐ[W] W' W k) := by
  set S : Set (W' W k) := {x | aeval x (f W k) = 0} with hS
  have hSfin : S.Finite := by
    apply ((((f W k).map (algebraMap W (W' W k))).roots.toFinset).finite_toSet).subset
    intro x hx
    simp only [hS, Set.mem_setOf_eq] at hx
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [mem_roots (((monic_f W k).map _).ne_zero), IsRoot, eval_map, ← aeval_def]
    exact hx
  haveI : Finite S := hSfin.to_subtype
  refine Finite.of_injective (fun γ : W' W k ≃ₐ[W] W' W k =>
    (⟨γ (AdjoinRoot.root (f W k)), ?_⟩ : S)) ?_
  · simp only [hS, Set.mem_setOf_eq]
    rw [aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  · intro γ₁ γ₂ h
    simp only [Subtype.mk.injEq] at h
    exact AlgEquiv.coe_algHom_injective (AdjoinRoot.algHom_ext h)

end Construction

section GaloisClause

variable (W : Type u) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
  [IsAdicComplete (maximalIdeal W) W]
  (k : Type u) [Field k] [Algebra (ResidueField W) k] [FiniteDimensional (ResidueField W) k]
  [Algebra.IsSeparable (ResidueField W) k]

noncomputable def rootsW' : Set (W' W k) := {x | aeval x (f W k) = 0}

theorem mem_rootsW'_iff (x : W' W k) :
    x ∈ rootsW' W k ↔ ((f W k).map (algebraMap W (W' W k))).IsRoot x := by
  rw [rootsW', Set.mem_setOf_eq, IsRoot, eval_map, ← aeval_def]

theorem root_mem_rootsW' : AdjoinRoot.root (f W k) ∈ rootsW' W k := by
  simp only [rootsW', Set.mem_setOf_eq, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

theorem rootsW'_finite : (rootsW' W k).Finite := by
  apply ((((f W k).map (algebraMap W (W' W k))).roots.toFinset).finite_toSet).subset
  intro x hx
  rw [mem_rootsW'_iff] at hx
  simp only [Finset.mem_coe, Multiset.mem_toFinset]
  rwa [mem_roots (((monic_f W k).map _).ne_zero)]

scoped instance : Finite (rootsW' W k) := (rootsW'_finite W k).to_subtype

noncomputable def autOfRoot (a : rootsW' W k) : W' W k ≃ₐ[W] W' W k :=
  AlgEquiv.ofBijective
    (AdjoinRoot.liftAlgHom (f W k) (Algebra.ofId W (W' W k)) (a : W' W k)
      (by have h := (mem_rootsW'_iff W k a).mp a.2; rw [IsRoot, eval_map] at h; simpa using h))
    (algHom_bijective (monic_f W k) (degree_f_ne_zero W k) _)

theorem autOfRoot_root (a : rootsW' W k) :
    autOfRoot W k a (AdjoinRoot.root (f W k)) = a := by
  rw [autOfRoot, AlgEquiv.ofBijective_apply, AdjoinRoot.liftAlgHom_root]

noncomputable def autEquivRoots : (W' W k ≃ₐ[W] W' W k) ≃ rootsW' W k where
  toFun γ := ⟨γ (AdjoinRoot.root (f W k)), by
    simp only [rootsW', Set.mem_setOf_eq]
    rw [aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]⟩
  invFun a := autOfRoot W k a
  left_inv γ := by
    apply AlgEquiv.coe_algHom_injective
    apply AdjoinRoot.algHom_ext
    exact autOfRoot_root W k _
  right_inv a := Subtype.ext (autOfRoot_root W k a)

variable [IsLocalRing (W' W k)] [IsLocalHom (algebraMap W (W' W k))]

theorem map_map_f :
    ((f W k).map (algebraMap W (W' W k))).map (residue (W' W k)) =
      (fbar W k).map (algebraMap (ResidueField W) (ResidueField (W' W k))) := by
  rw [← map_f, Polynomial.map_map, Polynomial.map_map]
  rfl

theorem separable_map_map_f :
    (((f W k).map (algebraMap W (W' W k))).map (residue (W' W k))).Separable := by
  rw [map_map_f]
  exact (fbar_separable W k).map

theorem rootsW'_residue_injective :
    Set.InjOn (residue (W' W k)) (rootsW' W k) := by
  intro a ha b hb hab
  rw [mem_rootsW'_iff] at ha hb
  apply root_eq_of_sub_mem_maximalIdeal _ ha hb
  · rw [← residue_ne_zero_iff_isUnit, ← eval_map_apply, ← derivative_map]
    exact not_isRoot_derivative_of_separable (separable_map_map_f W k) (by
      rw [IsRoot, eval_map_apply, ha.eq_zero, map_zero])
  · rw [← residue_eq_zero_iff, map_sub, hab, sub_self]

theorem rootsW'_residue_surjOn [IsAdicComplete (maximalIdeal (W' W k)) (W' W k)] :
    Set.SurjOn (residue (W' W k)) (rootsW' W k)
      {β | (((f W k).map (algebraMap W (W' W k))).map (residue (W' W k))).IsRoot β} := by
  haveI : HenselianLocalRing (W' W k) := HenselianLocalRing.of_isAdicComplete_maximalIdeal (W' W k)
  intro β hβ
  obtain ⟨a, ha, hres⟩ := exists_root_residue_eq _ ((monic_f W k).map _) β hβ
    (not_isRoot_derivative_of_separable (separable_map_map_f W k) hβ)
  exact ⟨a, (mem_rootsW'_iff W k a).mpr ha, hres⟩

theorem natCard_rootsW'_eq [IsAdicComplete (maximalIdeal (W' W k)) (W' W k)] :
    Nat.card (rootsW' W k) =
      Nat.card {β : ResidueField (W' W k) |
        (((f W k).map (algebraMap W (W' W k))).map (residue (W' W k))).IsRoot β} := by
  have hbij : Set.BijOn (residue (W' W k)) (rootsW' W k)
      {β | (((f W k).map (algebraMap W (W' W k))).map (residue (W' W k))).IsRoot β} :=
    ⟨fun a ha => by
      simp only [Set.mem_setOf_eq]
      rw [IsRoot, eval_map_apply, ((mem_rootsW'_iff W k a).mp ha).eq_zero, map_zero],
     rootsW'_residue_injective W k, rootsW'_residue_surjOn W k⟩
  exact Nat.card_congr hbij.equiv

theorem natCard_roots_residue_eq [IsGalois (ResidueField W) k]
    (e : ResidueField (W' W k) ≃ₐ[ResidueField W] k) :
    Nat.card {β : ResidueField (W' W k) |
        (((f W k).map (algebraMap W (W' W k))).map (residue (W' W k))).IsRoot β} =
      Module.finrank (ResidueField W) k := by

  have h1 : {β : ResidueField (W' W k) |
      (((f W k).map (algebraMap W (W' W k))).map (residue (W' W k))).IsRoot β} =
      (fbar W k).rootSet (ResidueField (W' W k)) := by
    ext β
    rw [map_map_f, Set.mem_setOf_eq, mem_rootSet, IsRoot, eval_map, ← aeval_def]
    exact ⟨fun h => ⟨(fbar_monic W k).ne_zero, h⟩, fun h => h.2⟩
  rw [h1]
  have h2 : Nat.card ((fbar W k).rootSet (ResidueField (W' W k))) =
      Nat.card ((fbar W k).rootSet k) := by
    apply Nat.card_congr
    refine Equiv.ofBijective (fun β => ⟨e β, ?_⟩) ⟨?_, ?_⟩
    · have hβ := β.2
      rw [mem_rootSet] at hβ ⊢
      refine ⟨hβ.1, ?_⟩
      rw [aeval_algHom_apply, hβ.2, map_zero]
    · intro β₁ β₂ h
      exact Subtype.ext (e.injective (congrArg Subtype.val h))
    · intro γ
      have hγ := γ.2
      rw [mem_rootSet] at hγ
      refine ⟨⟨e.symm γ, ?_⟩, Subtype.ext (e.apply_symm_apply γ)⟩
      rw [mem_rootSet]
      refine ⟨hγ.1, ?_⟩
      rw [aeval_algHom_apply, hγ.2, map_zero]
  rw [h2, Nat.card_eq_fintype_card, card_rootSet_eq_natDegree (fbar_separable W k), natDegree_fbar]
  exact Normal.splits (IsGalois.to_normal) (α W k)

theorem natCard_algEquiv [IsAdicComplete (maximalIdeal (W' W k)) (W' W k)]
    [IsGalois (ResidueField W) k]
    (e : ResidueField (W' W k) ≃ₐ[ResidueField W] k) :
    Nat.card (W' W k ≃ₐ[W] W' W k) = Module.finrank W (W' W k) := by
  rw [Nat.card_congr (autEquivRoots W k), natCard_rootsW'_eq,
    natCard_roots_residue_eq W k e, finrank_W']

theorem mem_range_of_forall_smul_eq [IsAdicComplete (maximalIdeal (W' W k)) (W' W k)]
    [IsGalois (ResidueField W) k] (e : ResidueField (W' W k) ≃ₐ[ResidueField W] k)
    (v : W' W k) (hv : ∀ γ : W' W k ≃ₐ[W] W' W k, γ • v = v) :
    v ∈ Set.range (algebraMap W (W' W k)) := by
  classical
  haveI : Fintype (rootsW' W k) := Fintype.ofFinite _
  set d := (f W k).natDegree with hd
  let pb := AdjoinRoot.powerBasis' (monic_f W k)
  have hdim : pb.dim = d := AdjoinRoot.powerBasis'_dim (monic_f W k)

  let c : Fin pb.dim → W := fun i => pb.basis.repr v i
  have hv_sum : (∑ i : Fin pb.dim, algebraMap W (W' W k) (c i) *
      AdjoinRoot.root (f W k) ^ (i : ℕ)) = v := by
    conv_rhs => rw [← pb.basis.sum_repr v]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PowerBasis.coe_basis, Algebra.smul_def, AdjoinRoot.powerBasis'_gen]

  let P : (W' W k)[X] :=
    (∑ i : Fin pb.dim, C (algebraMap W (W' W k) (c i)) * X ^ (i : ℕ)) - C v
  have hPeval : ∀ a : rootsW' W k, P.eval (a : W' W k) = 0 := by
    intro a
    have hγ := hv (autOfRoot W k a)
    rw [AlgEquiv.smul_def] at hγ
    simp only [P, eval_sub, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    rw [sub_eq_zero]
    conv_rhs => rw [← hγ, ← hv_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, AlgEquiv.commutes, autOfRoot_root]
  have hPdeg : P.natDegree < Fintype.card (rootsW' W k) := by
    have hcard : Fintype.card (rootsW' W k) = d := by
      rw [← Nat.card_eq_fintype_card, natCard_rootsW'_eq,
        natCard_roots_residue_eq W k e, ← natDegree_f]
    rw [hcard]
    have hdpos : 0 < d := natDegree_f_pos W k
    refine lt_of_le_of_lt (natDegree_sub_le _ _) ?_
    rw [natDegree_C, max_eq_left (Nat.zero_le _)]
    have hsum : (∑ i : Fin pb.dim, C (algebraMap W (W' W k) (c i)) *
        X ^ (i : ℕ)).natDegree ≤ d - 1 :=
      natDegree_sum_le_of_forall_le _ _ fun i _ =>
        (natDegree_C_mul_X_pow_le _ _).trans (by have := i.2; omega)
    omega
  have hP0 : P = 0 :=
    eq_zero_of_natDegree_lt_card_of_eval_eq_zero P Subtype.val_injective hPeval hPdeg

  have hdpos : 0 < pb.dim := by rw [hdim]; exact natDegree_f_pos W k
  have hcoeff := congrArg (fun Q : (W' W k)[X] => Q.coeff 0) hP0
  simp only [P, coeff_sub, coeff_zero, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_C_zero,
    mul_ite, mul_one, mul_zero] at hcoeff
  rw [Finset.sum_eq_single (⟨0, hdpos⟩ : Fin pb.dim)] at hcoeff
  · simp only [ite_true, sub_eq_zero] at hcoeff
    exact ⟨c ⟨0, hdpos⟩, hcoeff⟩
  · intro i _ hi
    rw [ite_eq_right]
    intro h0
    apply hi
    exact Fin.ext (by simpa using h0.symm)
  · intro h
    exact absurd (Finset.mem_univ _) h

end GaloisClause

end EtaleDvrAux

@[expose] public section

open Polynomial IsLocalRing
open scoped EtaleDvrAux

/-- Existence of a finite étale faithfully flat local DVR extension
realizing a finite separable residue extension.

Let `W` be a discrete valuation ring complete for its maximal-ideal adic
topology, and let `k` be a finite separable extension of its residue
field. Then there is a discrete valuation ring `W'` in the same universe,
complete for its maximal-ideal adic topology, with a finite free (hence
flat) and finite étale `W`-algebra structure, faithfully flat, whose
maximal ideal is the extension of the maximal ideal of `W` and whose
residue field is isomorphic to `k` compatibly with the residue maps.
The ranks agree, there are only finitely many `W`-algebra
automorphisms of `W'`, and when `k` is Galois over the residue field
of `W` the automorphism count equals the rank and the fixed elements
are exactly the image of `W`. -/
public theorem
    IsDiscreteValuationRing.exists_etale_dvr_residueField_equiv_card_algEquiv_eq_of_isAdicComplete
    (W : Type u) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (k : Type u) [Field k] [Algebra (IsLocalRing.ResidueField W) k]
    [FiniteDimensional (IsLocalRing.ResidueField W) k]
    [Algebra.IsSeparable (IsLocalRing.ResidueField W) k] :
    ∃ (W' : Type u) (_ : CommRing W') (_ : IsDomain W') (_ : IsDiscreteValuationRing W')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal W') W') (_ : Algebra W W')
      (_ : IsLocalHom (algebraMap W W'))
      (_ : Module.Finite W W') (_ : Module.Free W W') (_ : Module.Flat W W') (_ : FaithfulSMul W W')
      (_ : Algebra.Etale W W')
      (ι : IsLocalRing.ResidueField W' ≃ₐ[IsLocalRing.ResidueField W] k),
      Ideal.map (algebraMap W W') (IsLocalRing.maximalIdeal W) = IsLocalRing.maximalIdeal W' ∧
      Module.finrank W W' = Module.finrank (IsLocalRing.ResidueField W) k ∧
      Finite (W' ≃ₐ[W] W') ∧
      (IsGalois (IsLocalRing.ResidueField W) k →
        Nat.card (W' ≃ₐ[W] W') = Module.finrank W W' ∧
        ∀ w' : W', (∀ γ : W' ≃ₐ[W] W', γ • w' = w') ↔ w' ∈ Set.range (algebraMap W W')) := by
  obtain ⟨hloc, hlh, hfin, hfree, het, hcompl, hmap, ⟨eres⟩⟩ :=
    adjoinRoot_exists_isLocalRing_etale_residueField_algEquiv_of_isAdicComplete W
      (EtaleDvrAux.f W k) (EtaleDvrAux.monic_f W k)
  haveI := hloc
  haveI := hlh
  haveI := hfree
  haveI := het
  haveI : IsDiscreteValuationRing (EtaleDvrAux.W' W k) :=
    EtaleDvrAux.isDiscreteValuationRing_W' W k hmap
  haveI : IsDomain (EtaleDvrAux.W' W k) := EtaleDvrAux.isDomain_W' W k
  let ι : ResidueField (EtaleDvrAux.W' W k) ≃ₐ[ResidueField W] k :=
    eres.trans (EtaleDvrAux.adjoinRootMapEquiv W k)
  refine ⟨EtaleDvrAux.W' W k, inferInstance, inferInstance, inferInstance, hcompl,
    inferInstance, hlh, inferInstance, hfree,
    inferInstance, inferInstance, het, ι, hmap, EtaleDvrAux.finrank_W' W k,
    EtaleDvrAux.finite_algEquiv W k, ?_⟩
  · intro hgal
    haveI := hgal
    haveI := hcompl
    exact ⟨EtaleDvrAux.natCard_algEquiv W k (eres.trans (EtaleDvrAux.adjoinRootMapEquiv W k)),
      fun w' => ⟨EtaleDvrAux.mem_range_of_forall_smul_eq W k
        (eres.trans (EtaleDvrAux.adjoinRootMapEquiv W k)) w',
      fun ⟨w, hw⟩ γ => by rw [← hw, AlgEquiv.smul_def, AlgEquiv.commutes]⟩⟩
