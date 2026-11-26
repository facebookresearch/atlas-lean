/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of the local denominator argument are adapted from:

`Mathlib/RingTheory/DiscreteValuationRing/TFAE.lean` (Mathlib):
Copyright (c) 2022 Andrew Yang. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import MathlibExt.AlgebraicGeometry.LogPairs

import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

/-!
# Discrepancy independence of the adjoint Cartier representation

The theorem states that replacing a log pair's adjoint Cartier combination by another
representation of the same divisor preserves log discrepancy.

References: Hartshorne, *Algebraic Geometry*, II.6; Kollár--Mori,
*Birational Geometry of Algebraic Varieties*, §2.3. Native function fields,
local orders and stalk scalar maps are covered Mathlib support. General
canonical/Cartier gluing and birational normalization are shared dependencies
for these minimal log-pair interfaces, not claims of a completed MMP theory.
The earlier principalization and affine hypersurface requests remain in
their original scope.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.LogPairDiscrepancyWanted

open MathlibExt.AlgebraicGeometry.LogPairs
open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace IsLocalRing
open scoped BigOperators

universe u

private theorem specializes_eqToHom (X : Scheme.{u}) (x y : X) (h : x = y) :
    X.presheaf.stalkSpecializes (Inseparable.of_eq h).specializes =
      eqToHom (congrArg (fun z => X.presheaf.stalk z) h.symm) := by
  subst y
  simp

private theorem fieldIso_algebraMap (k : Type u) [Field k] (n : ℕ) (P : LogPair k n)
    (M : BirationalModel P) (p : PrimePoint M.variety)
    (a : LocalRing P.variety (M.map.left p.val)) :
    M.data.fieldIso (algebraMap (LocalRing P.variety (M.map.left p.val))
      (FunctionField P.variety) a) =
      algebraMap (LocalRing M.variety p.val) (FunctionField M.variety)
        ((M.map.left.stalkMap p.val).hom a) := by
  change M.data.fieldIso.toRingHom _ = _
  rw [M.data.fieldNormalized]
  unfold genericMap
  rw [← specializes_eqToHom P.variety.X.left _ _ M.data.generic]
  change (M.map.left.stalkMap (genericPoint M.variety.X.left))
    ((P.variety.X.left.presheaf.stalkSpecializes (Inseparable.of_eq M.data.generic).specializes)
      ((P.variety.X.left.presheaf.stalkSpecializes
        ((genericPoint_spec P.variety.X.left).specializes trivial)) a)) = _
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply]
  exact M.map.left.stalkSpecializes_stalkMap_apply
    (genericPoint M.variety.X.left) p.val
    ((genericPoint_spec M.variety.X.left).specializes trivial) a

private theorem ord_fieldIso_localUnit (k : Type u) [Field k] (n : ℕ) (P : LogPair k n)
    (M : BirationalModel P) (p : PrimePoint M.variety)
    (a : LocalRing P.variety (M.map.left p.val)) (ha : IsUnit a) :
    M.variety.X.left.ord
      (M.data.fieldIso (algebraMap (LocalRing P.variety (M.map.left p.val))
        (FunctionField P.variety) a)) p.val = 0 := by
  rw [fieldIso_algebraMap]
  exact M.variety.X.left.ord_algebraMap_eq_zero_of_isUnit
    (ha.map (M.map.left.stalkMap p.val).hom)

private theorem maximalIdeal_principal (R K : Type*) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsLocalRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (x : K) (hx : ¬∃ a : R, algebraMap R K a = x)
    (h : ∀ a ∈ maximalIdeal R, ∃ b : R, x * algebraMap R K a = algebraMap R K b) :
    (maximalIdeal R).IsPrincipal := by
  classical
  let M := Submodule.map (Algebra.linearMap R K) (maximalIdeal R)
  have hMfg : M.FG := (IsNoetherian.noetherian (maximalIdeal R)).map _
  have hMne : M ≠ ⊥ := by
    by_contra hzero
    have hm : maximalIdeal R = ⊥ := by
      apply Submodule.map_injective_of_injective (f := Algebra.linearMap R K)
        (IsFractionRing.injective R K)
      simpa only [M, Submodule.map_bot] using hzero
    have hfield : IsField R := isField_iff_maximalIdeal_eq.mpr hm
    exact hx (((IsFractionRing.surjective_iff_isField (R := R) (K := K)).mpr hfield) x)
  by_cases hs : ∀ y ∈ M, x * y ∈ M
  · have hi : IsIntegral R x := isIntegral_of_smul_mem_submodule M hMne hMfg x hs
    exact (hx (IsIntegrallyClosed.algebraMap_eq_of_integral hi)).elim
  obtain ⟨y, hy⟩ := not_forall.mp hs
  obtain ⟨hyM, hxy⟩ := not_imp.mp hy
  obtain ⟨a, ha, rfl⟩ := hyM
  obtain ⟨b, hb⟩ := h a ha
  have hbunit : IsUnit b := by
    by_contra hbu
    apply hxy
    change x * algebraMap R K a ∈ M
    rw [hb]
    exact ⟨b, (mem_nonunits_iff.mp hbu), rfl⟩
  obtain ⟨u, hu⟩ := hbunit
  have heq : maximalIdeal R = Ideal.span {a} := by
    apply le_antisymm
    · intro r hr
      obtain ⟨s, hs⟩ := h r hr
      refine Ideal.mem_span_singleton.mpr ⟨s * ↑u⁻¹, ?_⟩
      have hcancel : x * algebraMap R K r * algebraMap R K a =
          x * algebraMap R K a * algebraMap R K r := by ring
      rw [hb, hs] at hcancel
      have hsr : s * a = b * r := IsFractionRing.injective R K (by
        simpa only [map_mul] using hcancel)
      calc
        r = (↑u * r) * ↑u⁻¹ := by
          rw [mul_comm (↑u : R) r, mul_assoc]
          simp
        _ = (s * a) * ↑u⁻¹ := by rw [hu, hsr]
        _ = a * (s * ↑u⁻¹) := by ring
    · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha)
  exact ⟨a, heq⟩

private theorem not_mem_localization (R S K : Type*) [CommRing R] [CommRing S]
    [Field K] [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    (P : Ideal R) [P.IsPrime] [IsLocalization.AtPrime S P] (x : K)
    (h : ∀ r : R, (∃ a : R, x * algebraMap R K r = algebraMap R K a) → r ∈ P) :
    ¬∃ a : S, algebraMap S K a = x := by
  rintro ⟨a, ha⟩
  obtain ⟨r, s, hs⟩ := IsLocalization.exists_mk'_eq P.primeCompl a
  have heq := congrArg (algebraMap S K) (IsLocalization.mk'_spec S r s)
  rw [map_mul, hs, ha, ← IsScalarTower.algebraMap_apply R S K,
    ← IsScalarTower.algebraMap_apply R S K] at heq
  exact s.property (h s ⟨r, heq⟩)

private theorem denominator_principal (R S K : Type*) [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsLocalRing S] [IsIntegrallyClosed S]
    [Field K] [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    [IsFractionRing R K] [IsFractionRing S K] (P : Ideal R) [P.IsPrime] [IsLocalization.AtPrime S P]
    (x : K) (h : ∀ r : R, r ∈ P ↔
      ∃ a : R, x * algebraMap R K r = algebraMap R K a) :
    (maximalIdeal S).IsPrincipal := by
  have hx := not_mem_localization R S K P x (fun r => (h r).mpr)
  apply maximalIdeal_principal S K x hx
  intro a ha
  obtain ⟨r, s, hs⟩ := IsLocalization.exists_mk'_eq P.primeCompl a
  have hr : r ∈ P := by
    have hnu : ¬IsUnit a := mem_nonunits_iff.mp ha
    rw [← hs, IsLocalization.AtPrime.isUnit_mk'_iff] at hnu
    exact not_not.mp hnu
  obtain ⟨b, hb⟩ := (h r).mp hr
  refine ⟨IsLocalization.mk' S b s, ?_⟩
  have hsne : algebraMap R K s ≠ 0 :=
    (IsFractionRing.to_map_eq_zero_iff (R := R) (K := K)).not.mpr
      (fun hz => s.property (hz.symm ▸ P.zero_mem))
  apply mul_right_cancel₀ hsne
  have haeq := congrArg (algebraMap S K) (IsLocalization.mk'_spec S r s)
  have hbeq := congrArg (algebraMap S K) (IsLocalization.mk'_spec S b s)
  simp only [map_mul, ← IsScalarTower.algebraMap_apply R S K, hs] at haeq hbeq
  calc
    (x * algebraMap S K a) * algebraMap R K s =
        x * (algebraMap S K a * algebraMap R K s) := mul_assoc _ _ _
    _ = algebraMap R K b := by rw [haeq, hb]
    _ = algebraMap S K (IsLocalization.mk' S b s) * algebraMap R K s := hbeq.symm

private theorem exists_denominator_prime (R K : Type*) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (f : K) (hf : ¬∃ a : R, algebraMap R K a = f) :
    ∃ P : Ideal R, P.IsPrime ∧ ∃ z : K,
      (∀ r : R, r ∈ P ↔ ∃ a : R, z * algebraMap R K r = algebraMap R K a) ∧
      (∀ r : R, (∃ a : R, f * algebraMap R K r = algebraMap R K a) → r ∈ P) := by
  let N := LinearMap.range (Algebra.linearMap R K)
  have hq : N.mkQ f ≠ 0 := by
    intro he
    exact hf ((Submodule.Quotient.mk_eq_zero N).mp he)
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R (N.mkQ f) hq
  obtain ⟨hp, w, hw⟩ := isAssociatedPrime_iff.mp hP
  obtain ⟨z, rfl⟩ := N.mkQ_surjective w
  refine ⟨P, hp, z, ?_, ?_⟩
  · intro r
    rw [hw, Submodule.mem_colon_singleton, Submodule.mem_bot, ← N.mkQ.map_smul,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change (∃ a, algebraMap R K a = r • z) ↔ _
    simp only [Algebra.smul_def, mul_comm (algebraMap R K r) z, eq_comm]
  · intro r ⟨a, ha⟩
    apply hle
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← N.mkQ.map_smul,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine ⟨a, ?_⟩
    change algebraMap R K a = r • f
    simpa only [Algebra.smul_def, mul_comm] using ha.symm

private theorem affine_lift (k : Type u) [Field k] (n : ℕ) (V : NormalVariety k n)
    (U : V.X.left.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (f : FunctionField V)
    (h : ∀ q : PrimePoint V, q.val ∈ U → V.X.left.ord f q.val = 0) :
    ∃ a : Γ(V.X.left, U), V.X.left.germToFunctionField U a = f := by
  have : IsNoetherianRing Γ(V.X.left, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : IsFractionRing Γ(V.X.left, U) (FunctionField V) :=
    functionField_isFractionRing_of_isAffineOpen V.X.left U hU
  by_contra hf
  obtain ⟨P, hp, z, hz, hPf⟩ := exists_denominator_prime Γ(V.X.left, U) (FunctionField V) f hf
  have : P.IsPrime := hp
  let t : Spec Γ(V.X.left, U) := ⟨P, hp⟩
  let y : U := hU.isoSpec.inv t
  have hy : hU.primeIdealOf y = t := by
    change hU.isoSpec.hom (hU.isoSpec.inv t) = t
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  let S := LocalRing V y.val
  let : Algebra Γ(V.X.left, U) S := V.X.left.presheaf.algebra_section_stalk y
  have : IsLocalization.AtPrime S P := by
    convert hU.isLocalization_stalk y using 1
    rw [hy]
  have : IsScalarTower Γ(V.X.left, U) S (FunctionField V) :=
    functionField_isScalarTower V.X.left U y
  have : IsIntegrallyClosed S := V.normal y.val
  have hzS := not_mem_localization Γ(V.X.left, U) S (FunctionField V) P z
    (fun r => (hz r).mpr)
  have hnot : ¬IsField S := fun H =>
    hzS ((IsFractionRing.surjective_iff_isField (R := S) (K := FunctionField V)).mpr H z)
  have hprincipal := denominator_principal Γ(V.X.left, U) S (FunctionField V) P z hz
  have : IsDiscreteValuationRing S := ((IsDiscreteValuationRing.TFAE S hnot).out 5 1).mp hprincipal
  have hcodim : Order.coheight y.val = 1 := Scheme.coheight_eq_one_of_isDiscreteValuationRing
  have hq := h ⟨y.val, hcodim⟩ y.property
  have hflocal : ∃ a : S, algebraMap S (FunctionField V) a = f :=
    (Scheme.exists_algebraMap_eq_iff_ord_nonneg f).mpr (by rw [hq])
  exact (not_mem_localization Γ(V.X.left, U) S (FunctionField V) P f hPf) hflocal

private theorem affine_unit (k : Type u) [Field k] (n : ℕ) (V : NormalVariety k n)
    (U : V.X.left.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (f : FunctionField V) (hf : f ≠ 0)
    (h : ∀ q : PrimePoint V, q.val ∈ U → V.X.left.ord f q.val = 0) :
    ∃ a : Γ(V.X.left, U), IsUnit a ∧ V.X.left.germToFunctionField U a = f := by
  obtain ⟨a, ha⟩ := affine_lift k n V U hU f h
  obtain ⟨b, hb⟩ := affine_lift k n V U hU f⁻¹ (fun q hq => by
    rw [V.X.left.ord_inv, h q hq, neg_zero])
  have hab : a * b = 1 := V.X.left.germToFunctionField_injective U (by
    change (V.X.left.germToFunctionField U).hom (a * b) =
      (V.X.left.germToFunctionField U).hom 1
    rw [map_mul, map_one, ha, hb, mul_inv_cancel₀ hf])
  exact ⟨a, isUnit_iff_exists_inv.mpr ⟨b, hab⟩, ha⟩

private theorem local_unit_of_ord_eq_zero (k : Type u) [Field k] (n : ℕ)
    (V : NormalVariety k n) (U : V.X.left.Opens) (x : V.X.left) (hx : x ∈ U)
    (f : FunctionField V) (hf : f ≠ 0)
    (h : ∀ q : PrimePoint V, q.val ∈ U → V.X.left.ord f q.val = 0) :
    ∃ a : LocalRing V x, IsUnit a ∧ algebraMap (LocalRing V x) (FunctionField V) a = f := by
  obtain ⟨A, hA, hxA, hAU⟩ := exists_isAffineOpen_mem_and_subset (U := U) (x := x) hx
  let : Nonempty A := ⟨⟨x, hxA⟩⟩
  obtain ⟨a, ha, haf⟩ := affine_unit k n V A hA f hf (fun q hq => h q (hAU hq))
  refine ⟨(V.X.left.presheaf.germ A x hxA).hom a,
    ha.map (V.X.left.presheaf.germ A x hxA).hom, ?_⟩
  exact (V.X.left.algebraMap_germ_eq_germToFunctionField hxA a).trans haf

private theorem integer_relations (k : Type u) [Field k] (n : ℕ) (P : LogPair k n)
    (M : BirationalModel P) (p : PrimePoint M.variety)
    (ι : Type) [Finite ι] (L : ι → CartierLine P.variety) (z : ι →₀ ℤ)
    (hz : Finsupp.linearCombination ℤ (fun i => (L i).divisor) z = 0) :
    Finsupp.linearCombination ℤ (fun i => pulledCartierCoefficient M (L i) p) z = 0 := by
  classical
  let := Fintype.ofFinite ι
  let x := M.map.left p.val
  let c (i : ι) := Classical.choose ((L i).covers x)
  let U : P.variety.X.left.Opens := ⨅ i, (L i).opens (c i)
  have hx : x ∈ U := by
    change x ∈ ((⨅ i, (L i).opens (c i) : P.variety.X.left.Opens) : Set P.variety.X.left)
    rw [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    exact fun i => Classical.choose_spec ((L i).covers x)
  let f : FunctionField P.variety := ∏ i, (L i).functions (c i) ^ z i
  have hf : f ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (Units.ne_zero _)
  have hord (q : PrimePoint P.variety) (hq : q.val ∈ U) :
      P.variety.X.left.ord f q.val = 0 := by
    have hzq := congrArg (fun d : IntegerWeil P.variety => d q) hz
    have hqi (i : ι) : q.val ∈ (L i).opens (c i) :=
      (iInf_le (fun i => (L i).opens (c i)) i) hq
    have hcq (i : ι) : (L i).divisor q =
        P.variety.X.left.ord ((L i).functions (c i)) q.val :=
      (L i).toCartierAtlas.coefficient_eq q (c i) (hqi i)
    simp only [f, P.variety.X.left.ord_prod q.val Finset.univ _
      (fun i _ => zpow_ne_zero _ (Units.ne_zero _)), P.variety.X.left.ord_zpow]
    simpa [Finsupp.linearCombination_apply, Finsupp.sum_fintype, hcq] using hzq
  obtain ⟨a, ha, haf⟩ := local_unit_of_ord_eq_zero k n P.variety U x hx f hf hord
  have hzero : M.variety.X.left.ord (M.data.fieldIso f) p.val = 0 := by
    rw [← haf]
    exact ord_fieldIso_localUnit k n P M p a ha
  have htransport : M.data.fieldIso f =
      ∏ i, M.data.fieldIso ((L i).functions (c i)) ^ z i := by simp [f]
  rw [htransport, M.variety.X.left.ord_prod p.val Finset.univ _
    (fun i _ => zpow_ne_zero _
      ((map_ne_zero M.data.fieldIso).mpr (Units.ne_zero _)))] at hzero
  simpa [M.variety.X.left.ord_zpow, pulledCartierCoefficient,
    Finsupp.linearCombination_apply, Finsupp.sum_fintype, c, x] using hzero

private theorem real_relations (k : Type u) [Field k] (n : ℕ) (V : NormalVariety k n)
    (ι : Type) [Fintype ι] (a : ι → IntegerWeil V) (b : ι → ℤ)
    (h : ∀ z : ι →₀ ℤ, Finsupp.linearCombination ℤ a z = 0 →
      Finsupp.linearCombination ℤ b z = 0)
    (c : ι → ℝ) (hc : ∑ i, c i • realCast (a i) = 0) :
    ∑ i, c i * (b i : ℝ) = 0 := by
  classical
  let f := Finsupp.linearCombination ℤ a
  let g : (ι →₀ ℤ) →ₗ[ℤ] ℝ :=
    (Int.castAddHom ℝ).toIntLinearMap.comp (Finsupp.linearCombination ℤ b)
  have hker : LinearMap.ker f.rangeRestrict ≤ LinearMap.ker g := by
    intro z hz
    have hfz : f z = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hz)
    have hgz := h z hfz
    change (Finsupp.linearCombination ℤ b z : ℝ) = 0
    rw [hgz, Int.cast_zero]
  have hsur : Function.Surjective f.rangeRestrict := by
    rintro ⟨_, z, rfl⟩
    exact ⟨z, rfl⟩
  let g' := f.rangeRestrict.liftOfSurjective hsur ⟨g, hker⟩
  obtain ⟨φ, hφ⟩ := (Module.Baer.of_divisible ℝ).extension_property
    (LinearMap.range f).subtype (LinearMap.range f).subtype_injective g'
  have hφa (i : ι) : φ (a i) = (b i : ℝ) := by
    have hext := congrArg (fun l => l (f.rangeRestrict (Finsupp.single i 1))) hφ
    change φ (f (Finsupp.single i 1)) =
      (f.rangeRestrict.liftOfSurjective _ ⟨g, hker⟩) (f.rangeRestrict _) at hext
    rw [LinearMap.equivOfSurjective_apply] at hext
    simpa [f, g] using hext
  let φR : RealWeil V →ₗ[ℝ] ℝ :=
    Finsupp.linearCombination ℝ (fun p => φ (Finsupp.single p 1))
  have hcast (z : IntegerWeil V) : φR (realCast z) = φ z := by
    induction z using Finsupp.induction with
    | zero => simp [realCast]
    | @single_add p r z hp hr ih =>
      have hsum : realCast (Finsupp.single p r + z) =
          realCast (Finsupp.single p r) + realCast z := by
        ext q
        by_cases hq : p = q <;> simp [realCast, hq]
      rw [hsum]
      rw [φR.map_add, φ.map_add, ih]
      congr 1
      have hsingle : realCast (Finsupp.single p r) = Finsupp.single p (r : ℝ) := by
        ext q
        by_cases hq : p = q <;> simp [realCast, hq]
      rw [hsingle]
      rw [Finsupp.linearCombination_single]
      change (r : ℝ) * φ (Finsupp.single p 1) = φ (Finsupp.single p r)
      have hsmul : Finsupp.single p r = r • Finsupp.single p (1 : ℤ) := by simp
      rw [hsmul, φ.map_smul]
      simp only [zsmul_eq_mul]
  have H := congrArg φR hc
  simpa only [map_sum, map_smul, hcast, hφa, map_zero, smul_eq_mul] using H

private theorem pulled_eq (k : Type u) [Field k] (n : ℕ) (P : LogPair k n)
    (M : BirationalModel P) (p : PrimePoint M.variety)
    (E F : CartierCombination P.variety) (hdiv : E.divisor = F.divisor) :
    pulledCombinationCoefficient M E p = pulledCombinationCoefficient M F p := by
  let L : Fin E.size ⊕ Fin F.size → CartierLine P.variety :=
    Sum.elim E.components F.components
  let c : Fin E.size ⊕ Fin F.size → ℝ :=
    Sum.elim E.coefficients (fun i => -F.coefficients i)
  have hc : ∑ i, c i • realCast (L i).divisor = 0 := by
    simp only [Fintype.sum_sum_type, c, L, Sum.elim_inl, Sum.elim_inr, neg_smul,
      Finset.sum_neg_distrib]
    change E.divisor + -F.divisor = 0
    rw [hdiv, add_neg_cancel]
  have H := real_relations k n P.variety _ (fun i => (L i).divisor)
    (fun i => pulledCartierCoefficient M (L i) p)
    (integer_relations k n P M p _ L) c hc
  simp only [Fintype.sum_sum_type, c, L, Sum.elim_inl, Sum.elim_inr, neg_mul,
    Finset.sum_neg_distrib] at H
  exact sub_eq_zero.mp H

/-- The log discrepancy does not depend on the Cartier representation of $K + \Delta$: for a field
$k$ of characteristic zero, a log pair $P$ over $k$, a proper birational model `M` of $P$ and a real
Cartier combination $D$ on the variety of $P$ whose divisor is $K + \Delta$ (the canonical divisor
of $P$ plus its boundary), every prime divisor of `M` has the same log discrepancy when computed
with $D$ in place of the adjoint combination of $P$. -/
public theorem discrepancy_adjoint_independence (k : Type u) [Field k] [CharZero k]
    (n : ℕ) (P : LogPair k n) (M : BirationalModel P)
    (D : CartierCombination P.variety)
    (h : D.divisor = realCast (canonicalDivisor P.canonical) + P.boundary)
    (p : PrimePoint M.variety) :
    logDiscrepancy M p = logDiscrepancy (M.withAdjoint D h) p := by
  have hdiv : P.adjoint.divisor = D.divisor := P.normalized.trans h.symm
  change 1 + (canonicalDivisor M.data.canonical p : ℝ) -
      pulledCombinationCoefficient M P.adjoint p =
    1 + (canonicalDivisor M.data.canonical p : ℝ) -
      pulledCombinationCoefficient M D p
  congr 1
  exact pulled_eq k n P M p P.adjoint D hdiv

end WantedExt.AlgebraicGeometry.LogPairDiscrepancyWanted
