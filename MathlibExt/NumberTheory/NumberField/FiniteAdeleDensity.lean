/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_NumberField_denseRange_algebraMap_finiteAdeleRing_and_ringHom_ext.lean`
and
`P2M/Sol/S_NumberField_denseRange_algebraMap_finiteAdeleRing_and_ringHom_ext.lean`
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

public import Mathlib.NumberTheory.NumberField.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.Topology.Algebra.Ring.Basic

@[expose] public section

open IsDedekindDomain NumberField

open scoped RestrictedProduct nonZeroDivisors

noncomputable section

namespace NumberField



noncomputable section

namespace P2MDensity

open IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K]

private theorem exists_radius_of_mem_nhds (i : HeightOneSpectrum (𝓞 K)) (x : i.adicCompletion K)
    (s : Set (i.adicCompletion K)) (hs : s ∈ nhds x) :
    ∃ γ : WithZero (Multiplicative ℤ), γ ≠ 0 ∧
      ∀ y : i.adicCompletion K, Valued.v (y - x) < γ → y ∈ s := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hs
  refine ⟨MonoidWithZeroHom.ValueGroup₀.embedding γ.1, (map_ne_zero _).mpr γ.ne_zero,
    fun y hy => hγ ?_⟩
  show Valued.v.restrict (y - x) < γ.1
  exact (Valuation.restrict_lt_iff_lt_embedding _).mpr hy

private theorem val_algebraMap (v : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) :
    v.valuation K (algebraMap (𝓞 K) K r) = v.intValuation r :=
  valuation_of_algebraMap v r

private theorem valued_algebraMap (v : HeightOneSpectrum (𝓞 K)) (k : K) :
    Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k :=
  valuedAdicCompletion_eq_valuation' v k

private theorem finite_setOf_intValuation_lt_one (d : 𝓞 K) (hd : d ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | v.intValuation d < 1}.Finite := by
  have h : {v : HeightOneSpectrum (𝓞 K) | v.intValuation d < 1} =
      {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ Ideal.span {d}} := by
    ext v
    simp only [Set.mem_setOf_eq, intValuation_lt_one_iff_dvd]
  rw [h]
  exact Ideal.finite_factors (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hd)

private theorem exists_forall_intValuation_sub_lt (T : Finset (HeightOneSpectrum (𝓞 K)))
    (t : HeightOneSpectrum (𝓞 K) → 𝓞 K) (δ : HeightOneSpectrum (𝓞 K) → WithZero (Multiplicative ℤ))
    (hδ : ∀ v, δ v ≠ 0) :
    ∃ c : 𝓞 K, ∀ v ∈ T, v.intValuation (c - t v) < δ v := by
  choose n hn using fun v => WithZero.exists_exp_neg_natCast_lt (hδ v)
  have hcop : ∀ v ∈ T, ∀ w ∈ T, v ≠ w → v.asIdeal ≠ w.asIdeal :=
    fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)
  obtain ⟨c, hc⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T) (fun v => v.asIdeal) n
    (fun v _ => v.prime) hcop (fun v => t v.1)
  exact ⟨c, fun v hv => lt_of_le_of_lt ((v.intValuation_le_pow_iff_mem _ _).mpr (hc v hv)) (hn v)⟩

private theorem exists_forall_valuation_sub_lt (T : Finset (HeightOneSpectrum (𝓞 K)))
    (b : HeightOneSpectrum (𝓞 K) → K) (γ : HeightOneSpectrum (𝓞 K) → WithZero (Multiplicative ℤ))
    (hγ : ∀ v, γ v ≠ 0) :
    ∃ a : K, (∀ v ∈ T, v.valuation K (a - b v) < γ v) ∧ (∀ v ∉ T, v.valuation K a ≤ 1) := by
  classical

  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finset (𝓞 K)⁰ (T.image b)
  have hs0 : (s : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hsK : algebraMap (𝓞 K) K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hs' : ∀ v ∈ T, ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = (s : 𝓞 K) • b v :=
    fun v hv => hs (b v) (Finset.mem_image_of_mem b hv)
  choose! r hr using hs'

  let T' : Finset (HeightOneSpectrum (𝓞 K)) :=
    T ∪ (finite_setOf_intValuation_lt_one (s : 𝓞 K) hs0).toFinset
  let t : HeightOneSpectrum (𝓞 K) → 𝓞 K := fun v => if v ∈ T then r v else 0
  let δ : HeightOneSpectrum (𝓞 K) → WithZero (Multiplicative ℤ) :=
    fun v => (if v ∈ T then γ v else 1) * v.intValuation s
  have hvs : ∀ v : HeightOneSpectrum (𝓞 K), 0 < v.intValuation s :=
    fun v => zero_lt_iff.mpr (v.intValuation_ne_zero _ hs0)
  have hδ : ∀ v, δ v ≠ 0 := fun v =>
    mul_ne_zero (by split_ifs; exacts [hγ v, one_ne_zero]) (hvs v).ne'
  obtain ⟨c, hc⟩ := exists_forall_intValuation_sub_lt T' t δ hδ
  refine ⟨algebraMap (𝓞 K) K c / algebraMap (𝓞 K) K s, fun v hv => ?_, fun v hv => ?_⟩
  · have h1 := hc v (Finset.mem_union_left _ hv)
    simp only [t, δ, if_pos hv] at h1
    have h2 : algebraMap (𝓞 K) K c / algebraMap (𝓞 K) K s - b v =
        algebraMap (𝓞 K) K (c - r v) / algebraMap (𝓞 K) K s := by
      rw [map_sub, sub_div, hr v hv, Algebra.smul_def, mul_div_cancel_left₀ _ hsK]
    rw [h2, map_div₀, val_algebraMap, val_algebraMap, div_lt_iff₀ (hvs v)]
    exact h1
  · rw [map_div₀, val_algebraMap, val_algebraMap]
    by_cases hv' : v ∈ T'
    · have h1 := hc v hv'
      simp only [t, δ, if_neg hv, sub_zero, one_mul] at h1
      exact (div_le_one₀ (hvs v)).mpr h1.le
    · have h3 : v.intValuation s = 1 := by
        refine le_antisymm (v.intValuation_le_one _) (not_lt.mp fun h => hv' ?_)
        exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr h)
      rw [h3, div_one]
      exact v.intValuation_le_one c

/-- A number field is dense in its finite adele ring (strong approximation
for the finite adeles). -/
private theorem denseRange_algebraMap_finiteAdeleRing (K : Type*) [Field K] [NumberField K] :
    DenseRange (algebraMap K (FiniteAdeleRing (𝓞 K) K)) := by
  classical
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨x, hxU⟩

  let S : Set (HeightOneSpectrum (𝓞 K)) := {v | x v ∈ v.adicCompletionIntegers K}
  have hS : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 K))) ≤ Filter.principal S :=
    Filter.le_principal_iff.mpr x.2
  let x' : Πʳ v : HeightOneSpectrum (𝓞 K),
      [v.adicCompletion K, v.adicCompletionIntegers K]_[Filter.principal S] :=
    ⟨fun v => x v, Filter.eventually_principal.mpr fun v hv => hv⟩
  have hx' : RestrictedProduct.inclusion _ _ hS x' = x := rfl

  have hU' : IsOpen (RestrictedProduct.inclusion _ _ hS ⁻¹' U) :=
    hU.preimage (RestrictedProduct.continuous_inclusion hS)
  obtain ⟨V, hV, hVU⟩ := RestrictedProduct.isEmbedding_coe_of_principal.isInducing.isOpen_iff.mp hU'
  have hxV : (⇑x' : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K) ∈ V := by
    have h : x' ∈ RestrictedProduct.inclusion _ _ hS ⁻¹' U := by
      show (RestrictedProduct.inclusion _ _ hS x') ∈ U
      rw [hx']; exact hxU
    rwa [← hVU] at h

  obtain ⟨T, u, hu, hTV⟩ := isOpen_pi_iff.mp hV _ hxV

  let W : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K) :=
    fun v => u v ∩ {y | v ∈ S → y ∈ v.adicCompletionIntegers K}
  have hWopen : ∀ v ∈ T, IsOpen (W v) := by
    intro v hv
    refine (hu v hv).1.inter ?_
    by_cases hvS : v ∈ S
    · have : {y : v.adicCompletion K | v ∈ S → y ∈ v.adicCompletionIntegers K} =
          (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
        ext y; simp [hvS]
      rw [this]
      exact Valued.isOpen_valuationSubring _
    · have : {y : v.adicCompletion K | v ∈ S → y ∈ v.adicCompletionIntegers K} = Set.univ := by
        ext y; simp [hvS]
      rw [this]
      exact isOpen_univ
  have hxW : ∀ v ∈ T, (x' v) ∈ W v := fun v hv => ⟨(hu v hv).2, fun hvS => hvS⟩

  have hb : ∀ v, ∃ b : K, v ∈ T → algebraMap K (v.adicCompletion K) b ∈ W v := by
    intro v
    by_cases hv : v ∈ T
    · obtain ⟨b, hb⟩ :=
        (denseRange_algebraMap (K := K) v).exists_mem_open (hWopen v hv) ⟨_, hxW v hv⟩
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose b hb using hb
  have hrad : ∀ v, ∃ γ : WithZero (Multiplicative ℤ), γ ≠ 0 ∧ (v ∈ T → ∀ y : v.adicCompletion K,
      Valued.v (y - algebraMap K (v.adicCompletion K) (b v)) < γ → y ∈ W v) := by
    intro v
    by_cases hv : v ∈ T
    · obtain ⟨γ, hγ0, hγ⟩ := exists_radius_of_mem_nhds v _ (W v) ((hWopen v hv).mem_nhds (hb v hv))
      exact ⟨γ, hγ0, fun _ => hγ⟩
    · exact ⟨1, one_ne_zero, fun h => absurd h hv⟩
  choose γ hγ0 hγ using hrad

  obtain ⟨a, haT, haT'⟩ := exists_forall_valuation_sub_lt T b γ hγ0
  have haW : ∀ v ∈ T, algebraMap K (v.adicCompletion K) a ∈ W v := by
    intro v hv
    refine hγ v hv _ ?_
    rw [← map_sub, valued_algebraMap]
    exact haT v hv
  have ha_int : ∀ v ∈ S, algebraMap K (v.adicCompletion K) a ∈ v.adicCompletionIntegers K := by
    intro v hvS
    by_cases hvT : v ∈ T
    · exact (haW v hvT).2 hvS
    · rw [mem_adicCompletionIntegers, valued_algebraMap]
      exact haT' v hvT
  let a' : Πʳ v : HeightOneSpectrum (𝓞 K),
      [v.adicCompletion K, v.adicCompletionIntegers K]_[Filter.principal S] :=
    ⟨fun v => algebraMap K (v.adicCompletion K) a, Filter.eventually_principal.mpr ha_int⟩
  have ha' : RestrictedProduct.inclusion _ _ hS a' = algebraMap K (FiniteAdeleRing (𝓞 K) K) a := rfl
  have haU : a' ∈ RestrictedProduct.inclusion _ _ hS ⁻¹' U := by
    rw [← hVU, Set.mem_preimage]
    exact hTV fun v hv => (haW v hv).1
  refine ⟨algebraMap K (FiniteAdeleRing (𝓞 K) K) a, ?_, a, rfl⟩
  have hfin : (RestrictedProduct.inclusion _ _ hS a') ∈ U := haU
  rw [ha'] at hfin
  exact hfin

end P2MDensity

/-- A number field is dense in its finite adele ring (strong approximation
for the finite adeles). -/
theorem denseRange_algebraMap_finiteAdeleRing (K : Type*) [Field K] [NumberField K] :
    DenseRange (algebraMap K (FiniteAdeleRing (𝓞 K) K)) :=
  P2MDensity.denseRange_algebraMap_finiteAdeleRing K

/-- Continuous ring homomorphisms out of the finite adele ring of a number
field are determined by their values on the diagonally embedded field. -/
theorem ringHom_ext_of_agreeOn_algebraMap_finiteAdeleRing
    (K : Type*) [Field K] [NumberField K] (R : Type*) [Ring R] [TopologicalSpace R] [T2Space R]
    (Ψ Ψ' : FiniteAdeleRing (𝓞 K) K →+* R) (hΨ : Continuous Ψ) (hΨ' : Continuous Ψ')
    (h : ∀ a : K, Ψ (algebraMap K (FiniteAdeleRing (𝓞 K) K) a) =
      Ψ' (algebraMap K (FiniteAdeleRing (𝓞 K) K) a)) : Ψ = Ψ' :=
  DFunLike.coe_injective
    ((denseRange_algebraMap_finiteAdeleRing K).equalizer hΨ hΨ' (funext h))

end

/-- A number field is dense in its finite adele ring, and continuous ring
homomorphisms out of the finite adele ring are determined by their values
on the diagonally embedded field. -/
theorem denseRange_algebraMap_finiteAdeleRing_and_ringHom_ext
    (K : Type*) [Field K] [NumberField K] :
    DenseRange (algebraMap K (FiniteAdeleRing (𝓞 K) K)) ∧
    (∀ (R : Type*) [Ring R] [TopologicalSpace R] [T2Space R]
        (Ψ Ψ' : FiniteAdeleRing (𝓞 K) K →+* R), Continuous Ψ → Continuous Ψ' →
        (∀ a : K, Ψ (algebraMap K (FiniteAdeleRing (𝓞 K) K) a) =
          Ψ' (algebraMap K (FiniteAdeleRing (𝓞 K) K) a)) → Ψ = Ψ') := by
  refine ⟨denseRange_algebraMap_finiteAdeleRing K, ?_⟩
  intro R _ _ _ Ψ Ψ' hΨ hΨ' h
  exact ringHom_ext_of_agreeOn_algebraMap_finiteAdeleRing K R Ψ Ψ' hΨ hΨ' h

end NumberField
