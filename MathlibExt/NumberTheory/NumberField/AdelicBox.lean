/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_NumberField_AdelicBox.lean`,
`Definitions/Def_NumberField_AdelicCentre.lean`
and
`Definitions/Def_NumberField_AdelicHaar.lean`
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

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import MathlibExt.NumberTheory.NumberField.AdelicHaar

/-!
# A fundamental domain for `K` in the adeles, and adelic `PGL(2)`

For a number field `K` with adele ring `AdeleRing (𝓞 K) K`, the first part of this file builds a
fundamental domain for the principal adeles `K`, acting on the adele ring by translation. The
second part, for a Dedekind domain `R` with fraction field `K`, defines adelic `PGL(2)` as the
quotient of adelic `GL(2)` by its centre and equips it with a Haar measure.

## Main definitions

* `NumberField.AdelicBox.integralFiniteAdeles R K`: the finite adeles that are integral at every
  finite place.
* `NumberField.AdelicBox.infiniteBox K`: the preimage, under the isomorphism of the infinite
  adeles with the mixed space, of the half-open parallelepiped (`ZSpan.fundamentalDomain`)
  spanned by `mixedEmbedding.latticeBasis K`, a `ℤ`-basis of the image of `𝓞 K`.
* `NumberField.AdelicBox.adelicBox K`: the adeles whose infinite component lies in
  `infiniteBox K` and whose finite component is integral.
* `NumberField.AdelicCentre.AdelicPGL2 R K`: adelic `PGL(2)`, the quotient of
  `GL (Fin 2) (AdeleRing R K)` by its centre.
* `NumberField.AdelicCentre.pglBorel R K`: the Borel measurable space on adelic `PGL(2)`. Like
  `NumberField.AdelicHaar.adeleBorel`, it is a reducible definition rather than an instance.
* `NumberField.AdelicCentre.adelicPGLHaar R K`: a Haar measure on adelic `PGL(2)` for
  `pglBorel R K`, when adelic `PGL(2)` is a locally compact topological group.

## Main results

* `NumberField.AdelicBox.existsUnique_algebraMap_add_mem_adelicBox`: every adele has exactly one
  translate by an element of `K` in the adelic box.
* `NumberField.AdelicBox.isAddFundamentalDomain_adelicBox`: the adelic box is a fundamental
  domain for the principal adeles, for every measure.
* `NumberField.AdelicBox.adelicAddHaar_adelicBox_pos` and
  `NumberField.AdelicBox.adelicAddHaar_adelicBox_lt_top`: the adelic box has positive, finite
  additive Haar measure.
* `NumberField.AdelicCentre.scalar_injective`: the scalar map from the units of the adele ring to
  adelic `GL(2)` is injective; by `Matrix.GeneralLinearGroup.center_eq_range_scalar` its range is
  the centre.
* `NumberField.AdelicCentre.adelicPGLHaar_image_pos` and
  `NumberField.AdelicCentre.adelicPGLHaar_image_lt_top_of_subset`: for a number field `K` and `R`
  a free `ℤ`-module of finite rank, the image in adelic `PGL(2)` of a set containing a nonempty
  open set has positive Haar measure, and the image of a set contained in a compact set times the
  centre has finite Haar measure.
-/

@[expose] public section

open IsDedekindDomain NumberField MeasureTheory
open scoped RestrictedProduct

noncomputable section

namespace NumberField.AdelicBox

section Finite

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

def integralFiniteAdeles : Set (FiniteAdeleRing R K) :=
  {x | ∀ v : HeightOneSpectrum R, x v ∈ v.adicCompletionIntegers K}

variable (v : HeightOneSpectrum R)

theorem algebraMap_mem_adicCompletionIntegers (r : R) :
    algebraMap K (v.adicCompletion K) (algebraMap R K r) ∈ v.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers,
    show algebraMap K (v.adicCompletion K) (algebraMap R K r) =
      ((algebraMap R K r : K) : v.adicCompletion K) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact v.valuation_le_one r

theorem valued_algebraMap (r : R) :
    Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) = v.intValuation r := by
  rw [show algebraMap K (v.adicCompletion K) (algebraMap R K r) =
      ((algebraMap R K r : K) : v.adicCompletion K) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]

theorem ball_mem_nhds (x t : v.adicCompletion K) (ht : t ≠ 0) :
    {z : v.adicCompletion K | Valued.v (z - x) < Valued.v t} ∈ nhds x := by
  have ht' : Valued.v.restrict t ≠ 0 := by
    rwa [Ne, Valuation.restrict_eq_zero_iff, Valuation.zero_iff]
  refine Valued.mem_nhds.mpr ⟨Units.mk0 _ ht', fun z hz => ?_⟩
  rw [Units.val_mk0] at hz
  exact Valued.v.restrict_lt_iff.mp hz

theorem exists_valued_sub_algebraMap_lt (x t : v.adicCompletion K) (ht : t ≠ 0) :
    ∃ c : K, Valued.v (x - algebraMap K (v.adicCompletion K) c) < Valued.v t := by
  obtain ⟨_, hz, c, rfl⟩ := mem_closure_iff_nhds.mp
    (HeightOneSpectrum.denseRange_algebraMap (K := K) (v := v) x) _ (ball_mem_nhds R K v x t ht)
  exact ⟨c, by rwa [Set.mem_setOf_eq, Valuation.map_sub_swap] at hz⟩

theorem exists_valued_algebraMap_sub_lt (x : v.adicCompletionIntegers K)
    (t : v.adicCompletion K) (ht : t ≠ 0) :
    ∃ a : R, Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K a) -
      (x : v.adicCompletion K)) < Valued.v t := by
  set γ : (WithZero (Multiplicative ℤ))ˣ :=
    Units.mk0 (Valued.v t) ((Valuation.ne_zero_iff _).mpr ht)
    with hγ

  have hn : {z : v.adicCompletion K | Valued.v (z - x) < Valued.v t} ∩
      {z : v.adicCompletion K | Valued.v (z - x) < Valued.v (1 : v.adicCompletion K)} ∈
        nhds (x : v.adicCompletion K) :=
    Filter.inter_mem (ball_mem_nhds R K v _ t ht) (ball_mem_nhds R K v _ 1 one_ne_zero)
  obtain ⟨_, ⟨hzγ, hz1⟩, y, rfl⟩ := mem_closure_iff_nhds.mp
    (HeightOneSpectrum.denseRange_algebraMap (K := K) (v := v) (x : v.adicCompletion K)) _ hn
  have hyγ : Valued.v (algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K)) < γ := by
    rw [hγ, Units.val_mk0]; exact hzγ
  have hz1 : Valued.v (algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K)) < 1 := by
    have := hz1; rwa [Set.mem_setOf_eq, Valuation.map_one] at this
  have hy1 : Valued.v (algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K)) < 1 := hz1

  have hyint : v.valuation K y ≤ 1 := by
    have hx1 : Valued.v (x : v.adicCompletion K) ≤ 1 := x.2
    have h : Valued.v (algebraMap K (v.adicCompletion K) y) ≤ 1 := by
      have := Valuation.map_add (Valued.v : Valuation (v.adicCompletion K) _)
        (algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K)) (x : v.adicCompletion K)
      rw [sub_add_cancel] at this
      exact this.trans (max_le hy1.le hx1)
    rwa [show algebraMap K (v.adicCompletion K) y = (y : v.adicCompletion K) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hyint γ
  refine ⟨a, ?_⟩
  have ha' : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K a) -
      algebraMap K (v.adicCompletion K) y) < γ := by
    rw [← map_sub, show algebraMap K (v.adicCompletion K) (algebraMap R K a - y) =
        ((algebraMap R K a - y : K) : v.adicCompletion K) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact ha
  have := Valuation.map_add (Valued.v : Valuation (v.adicCompletion K) _)
    (algebraMap K (v.adicCompletion K) (algebraMap R K a) - algebraMap K (v.adicCompletion K) y)
    (algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K))
  rw [sub_add_sub_cancel] at this
  rw [hγ, Units.val_mk0] at ha' hyγ
  exact lt_of_le_of_lt this (max_lt ha' hyγ)

theorem exists_mul_mem_adicCompletionIntegers (x : v.adicCompletion K) :
    ∃ s : R, s ≠ 0 ∧
      algebraMap K (v.adicCompletion K) (algebraMap R K s) * x ∈ v.adicCompletionIntegers K := by
  obtain ⟨c, hc⟩ := exists_valued_sub_algebraMap_lt R K v x 1 one_ne_zero
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) c
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hsK : algebraMap R K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  refine ⟨s, hs0, ?_⟩
  have hid : algebraMap K (v.adicCompletion K) (algebraMap R K s) * x =
      algebraMap K (v.adicCompletion K) (algebraMap R K s) *
        (x - algebraMap K (v.adicCompletion K) (algebraMap R K a / algebraMap R K s)) +
      algebraMap K (v.adicCompletion K) (algebraMap R K a) := by
    have : algebraMap R K s * (algebraMap R K a / algebraMap R K s) = algebraMap R K a := by
      field_simp
    rw [mul_sub, ← map_mul, this]
    ring
  rw [hid, HeightOneSpectrum.mem_adicCompletionIntegers]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
  · rw [Valuation.map_mul]
    have h1 : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K s)) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers R K v).mp
        (algebraMap_mem_adicCompletionIntegers R K v s)
    have h2 : Valued.v (x - algebraMap K (v.adicCompletion K) (algebraMap R K a / algebraMap R K s))
        ≤ 1 := by
      have := hc.le; rwa [Valuation.map_one] at this
    exact mul_le_one' h1 h2
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers R K v).mp
      (algebraMap_mem_adicCompletionIntegers R K v a)

omit v in
theorem algebraMap_mul_apply (r : R) (y : FiniteAdeleRing R K) (v : HeightOneSpectrum R) :
    (algebraMap R (FiniteAdeleRing R K) r * y) v =
      algebraMap K (v.adicCompletion K) (algebraMap R K r) * y v := rfl

omit v in
theorem algebraMap_add_apply (k : K) (y : FiniteAdeleRing R K) (v : HeightOneSpectrum R) :
    (algebraMap K (FiniteAdeleRing R K) k + y) v = algebraMap K (v.adicCompletion K) k + y v := rfl

omit v in
theorem exists_mul_mem_integralFiniteAdeles (y : FiniteAdeleRing R K) :
    ∃ s : R, s ≠ 0 ∧ algebraMap R (FiniteAdeleRing R K) s * y ∈ integralFiniteAdeles R K := by
  classical
  have hS : {v : HeightOneSpectrum R | y v ∉ v.adicCompletionIntegers K}.Finite :=
    Filter.eventually_cofinite.mp
      (show Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]
        from y).eventually
  choose s hs0 hs using fun v => exists_mul_mem_adicCompletionIntegers R K v (y v)
  refine ⟨∏ w ∈ hS.toFinset, s w, Finset.prod_ne_zero_iff.mpr fun w _ => hs0 w, fun v => ?_⟩
  rw [algebraMap_mul_apply]
  by_cases hv : v ∈ hS.toFinset
  · rw [← Finset.prod_erase_mul _ _ hv, map_mul, map_mul, mul_assoc]
    exact mul_mem (algebraMap_mem_adicCompletionIntegers R K v _) (hs v)
  · have hyv : y v ∈ v.adicCompletionIntegers K := by
      simpa [Set.Finite.mem_toFinset] using hv
    exact mul_mem (algebraMap_mem_adicCompletionIntegers R K v _) hyv

omit v in
theorem exists_forall_valued_sub_le {z : FiniteAdeleRing R K} (hz : z ∈ integralFiniteAdeles R K)
    {s : R} (hs : s ≠ 0) :
    ∃ a : R, ∀ v : HeightOneSpectrum R,
      Valued.v (z v - algebraMap K (v.adicCompletion K) (algebraMap R K a)) ≤
        Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K s)) := by
  classical
  have hI : (Ideal.span {s} : Ideal R) ≠ 0 := by
    simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hs
  set T := (Ideal.finite_factors hI).toFinset with hT
  let e : HeightOneSpectrum R → ℕ := fun v =>
    (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {s} : Ideal R)).factors
  have hvs : ∀ v : HeightOneSpectrum R,
      Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K s)) ≠ 0 := fun v => by
    rw [valued_algebraMap]; exact v.intValuation_ne_zero s hs
  have hS : ∀ v : HeightOneSpectrum R,
      algebraMap K (v.adicCompletion K) (algebraMap R K s) ≠ 0 := fun v =>
    (Valuation.ne_zero_iff _).mp (hvs v)
  choose a ha using fun v : HeightOneSpectrum R =>
    exists_valued_algebraMap_sub_lt R K v ⟨z v, hz v⟩ _ (hS v)
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun v : HeightOneSpectrum R => v.asIdeal) e (fun v _ => v.prime)
    (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => a v.1)
  refine ⟨b, fun v => ?_⟩
  have hzb : z v - algebraMap K (v.adicCompletion K) (algebraMap R K b) =
      (z v - algebraMap K (v.adicCompletion K) (algebraMap R K (a v))) +
      (algebraMap K (v.adicCompletion K) (algebraMap R K (a v)) -
        algebraMap K (v.adicCompletion K) (algebraMap R K b)) := by ring
  rw [hzb]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
  · have := ha v
    rw [Valuation.map_sub_swap] at this
    exact this.le
  · rw [← map_sub, ← map_sub, valued_algebraMap, valued_algebraMap]
    by_cases hv : v ∈ T
    ·
      rw [v.intValuation_if_neg hs, Valuation.map_sub_swap]
      exact (v.intValuation_le_pow_iff_mem _ _).mpr (hb v hv)
    ·
      have hsv : s ∉ v.asIdeal := by
        intro h
        apply hv
        rw [hT, Set.Finite.mem_toFinset]
        exact Ideal.dvd_span_singleton.mpr h
      rw [(HeightOneSpectrum.intValuation_eq_one_iff).mpr hsv]
      exact v.intValuation_le_one _

omit v in
theorem exists_algebraMap_add_mem_integralFiniteAdeles (y : FiniteAdeleRing R K) :
    ∃ k : K, algebraMap K (FiniteAdeleRing R K) k + y ∈ integralFiniteAdeles R K := by
  obtain ⟨s, hs, hsy⟩ := exists_mul_mem_integralFiniteAdeles R K y
  obtain ⟨a, ha⟩ := exists_forall_valued_sub_le R K hsy hs
  refine ⟨-(algebraMap R K a / algebraMap R K s), fun v => ?_⟩
  have hsK : algebraMap R K s ≠ 0 := fun h => hs ((injective_iff_map_eq_zero _).mp
    (IsFractionRing.injective R K) s h)
  set S := algebraMap K (v.adicCompletion K) (algebraMap R K s) with hSdef
  set A := algebraMap K (v.adicCompletion K) (algebraMap R K a) with hAdef
  have hS : S ≠ 0 := by rw [hSdef]; exact (map_ne_zero _).mpr hsK
  have hvS : Valued.v S ≠ 0 := (Valuation.ne_zero_iff _).mpr hS
  rw [algebraMap_add_apply, HeightOneSpectrum.mem_adicCompletionIntegers]
  have hid : algebraMap K (v.adicCompletion K) (-(algebraMap R K a / algebraMap R K s)) + y v =
      S⁻¹ * (S * y v - A) := by
    rw [map_neg, map_div₀, ← hSdef, ← hAdef]
    field_simp
    ring
  rw [hid, Valuation.map_mul, map_inv₀]
  have h := ha v
  rw [algebraMap_mul_apply, ← hSdef, ← hAdef] at h
  calc (Valued.v S)⁻¹ * Valued.v (S * y v - A)
      ≤ (Valued.v S)⁻¹ * Valued.v S := by gcongr
    _ = 1 := inv_mul_cancel₀ hvS

end Finite

section Infinite

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in
def infiniteBox : Set (InfiniteAdeleRing K) :=
  InfiniteAdeleRing.ringEquiv_mixedSpace K ⁻¹'
    ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis K)

omit [NumberField K] in
theorem continuous_ringEquiv_mixedSpace :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K) := by
  have h : (InfiniteAdeleRing.ringEquiv_mixedSpace K :
      InfiniteAdeleRing K → mixedEmbedding.mixedSpace K)
      = fun x => (fun (w : {w : InfinitePlace K // w.IsReal}) =>
          InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (x w.1),
        fun (w : {w : InfinitePlace K // w.IsComplex}) =>
          InfinitePlace.Completion.extensionEmbedding w.1 (x w.1)) := by
    funext x; exact InfiniteAdeleRing.ringEquiv_mixedSpace_apply K x
  rw [h]
  refine Continuous.prodMk (continuous_pi fun w => ?_) (continuous_pi fun w => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).continuous.comp
      (continuous_apply w.1)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding w.1).continuous.comp
      (continuous_apply w.1)

open scoped Classical in

theorem existsUnique_int_add_mem_infiniteBox (x : InfiniteAdeleRing K) :
    ∃! o : 𝓞 K, algebraMap K (InfiniteAdeleRing K) (o : K) + x ∈ infiniteBox K := by
  set e := InfiniteAdeleRing.ringEquiv_mixedSpace K with he
  obtain ⟨ℓ, hℓ, huniq⟩ :=
    ZSpan.exist_unique_vadd_mem_fundamentalDomain (mixedEmbedding.latticeBasis K) (e x)

  have hℓ' : (ℓ : mixedEmbedding.mixedSpace K) ∈ mixedEmbedding.integerLattice K :=
    (mixedEmbedding.mem_span_latticeBasis K).mp ℓ.2
  obtain ⟨o, ho⟩ := LinearMap.mem_range.mp hℓ'
  have ho' : mixedEmbedding K (o : K) = ℓ := ho
  have key : ∀ o' : 𝓞 K, e (algebraMap K (InfiniteAdeleRing K) (o' : K) + x) =
      mixedEmbedding K (o' : K) + e x := fun o' => by
    rw [map_add, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  refine ⟨o, ?_, fun o' ho'mem => ?_⟩
  · show e (algebraMap K (InfiniteAdeleRing K) (o : K) + x) ∈
      ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis K)
    rw [key, ho']
    exact hℓ
  · have hmem : mixedEmbedding K (o' : K) ∈
        Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis K)) :=
      (mixedEmbedding.mem_span_latticeBasis K).mpr (LinearMap.mem_range.mpr ⟨o', rfl⟩)
    have h2 : (⟨mixedEmbedding K (o' : K), hmem⟩ :
        Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis K)))
        +ᵥ e x ∈ ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis K) := by
      have : e (algebraMap K (InfiniteAdeleRing K) (o' : K) + x) ∈
          ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis K) := ho'mem
      rw [key] at this
      exact this
    have h3 := huniq _ h2
    have h4 : mixedEmbedding K (o' : K) = mixedEmbedding K (o : K) := by
      rw [ho']; exact congrArg Subtype.val h3
    exact_mod_cast (mixedEmbedding_injective K) h4

end Infinite

section Box

variable (K : Type*) [Field K] [NumberField K]

def adelicBox : Set (AdeleRing (𝓞 K) K) :=
  {x | x.1 ∈ infiniteBox K ∧ x.2 ∈ integralFiniteAdeles (𝓞 K) K}

theorem existsUnique_algebraMap_add_mem_adelicBox (x : AdeleRing (𝓞 K) K) :
    ∃! k : K, algebraMap K (AdeleRing (𝓞 K) K) k + x ∈ adelicBox K := by
  obtain ⟨k₁, hk₁⟩ := exists_algebraMap_add_mem_integralFiniteAdeles (𝓞 K) K x.2
  obtain ⟨o, ho, _⟩ := existsUnique_int_add_mem_infiniteBox K
    (algebraMap K (InfiniteAdeleRing K) k₁ + x.1)
  have hfst : ∀ k : K, (algebraMap K (AdeleRing (𝓞 K) K) k + x).1 =
      algebraMap K (InfiniteAdeleRing K) k + x.1 := fun _ => rfl
  have hsnd : ∀ k : K, (algebraMap K (AdeleRing (𝓞 K) K) k + x).2 =
      algebraMap K (FiniteAdeleRing (𝓞 K) K) k + x.2 := fun _ => rfl
  refine ⟨(o : K) + k₁, ⟨?_, ?_⟩, fun k' hk' => ?_⟩
  · rw [hfst, map_add, add_assoc]
    exact ho
  · rw [hsnd]
    intro v
    rw [map_add, add_assoc, algebraMap_add_apply]
    exact add_mem (algebraMap_mem_adicCompletionIntegers (𝓞 K) K v o) (hk₁ v)
  ·
    obtain ⟨hk'1, hk'2⟩ := hk'
    rw [hsnd] at hk'2
    have hdiff : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K (k' - k₁) ≤ 1 := fun v => by
      have h1 := hk'2 v
      have h2 := hk₁ v
      rw [algebraMap_add_apply] at h1 h2
      have := sub_mem h1 h2
      rw [add_sub_add_right_eq_sub, ← map_sub] at this
      rwa [HeightOneSpectrum.mem_adicCompletionIntegers,
        show algebraMap K (v.adicCompletion K) (k' - k₁) = ((k' - k₁ : K) : v.adicCompletion K)
          from rfl, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
    obtain ⟨o', ho'⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K (k' - k₁) hdiff
    have hk'o : k' = (o' : K) + k₁ := by
      rw [show ((o' : 𝓞 K) : K) = algebraMap (𝓞 K) K o' from rfl, ho']; ring
    rw [hfst, hk'o, map_add, add_assoc] at hk'1
    obtain ⟨_, _, huniq⟩ := existsUnique_int_add_mem_infiniteBox K
      (algebraMap K (InfiniteAdeleRing K) k₁ + x.1)
    rw [hk'o, huniq o' hk'1, huniq o ho]

attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel

theorem isClosed_integralFiniteAdeles :
    IsClosed (integralFiniteAdeles (𝓞 K) K) := by
  have : integralFiniteAdeles (𝓞 K) K = ⋂ v : HeightOneSpectrum (𝓞 K),
      (fun x : FiniteAdeleRing (𝓞 K) K => x v) ⁻¹'
        (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    ext x; simp [integralFiniteAdeles]
  rw [this]
  refine isClosed_iInter fun v => IsClosed.preimage ?_ (Valued.isClosed_valuationSubring _)
  exact (RestrictedProduct.continuous_eval v :
    Continuous fun x : Πʳ w : HeightOneSpectrum (𝓞 K),
      [w.adicCompletion K, w.adicCompletionIntegers K] => x v)

open scoped Classical in

theorem measurableSet_infiniteBox :
    MeasurableSet[borel (InfiniteAdeleRing K)] (infiniteBox K) := by
  letI : MeasurableSpace (InfiniteAdeleRing K) := borel _
  haveI : BorelSpace (InfiniteAdeleRing K) := ⟨rfl⟩
  exact (ZSpan.fundamentalDomain_measurableSet _).preimage
    (continuous_ringEquiv_mixedSpace K).measurable

theorem measurableSet_adelicBox : MeasurableSet (adelicBox K) := by
  letI : MeasurableSpace (InfiniteAdeleRing K) := borel _
  haveI : BorelSpace (InfiniteAdeleRing K) := ⟨rfl⟩
  letI : MeasurableSpace (FiniteAdeleRing (𝓞 K) K) := borel _
  haveI : BorelSpace (FiniteAdeleRing (𝓞 K) K) := ⟨rfl⟩
  have hc1 : Continuous fun x : AdeleRing (𝓞 K) K => x.1 := continuous_fst
  have hc2 : Continuous fun x : AdeleRing (𝓞 K) K => x.2 := continuous_snd
  have h1 : Measurable fun x : AdeleRing (𝓞 K) K => x.1 := hc1.measurable
  have h2 : Measurable fun x : AdeleRing (𝓞 K) K => x.2 := hc2.measurable
  exact ((measurableSet_infiniteBox K).preimage h1).inter
    ((isClosed_integralFiniteAdeles K).measurableSet.preimage h2)

theorem isAddFundamentalDomain_adelicBox (μ : Measure (AdeleRing (𝓞 K) K)) :
    IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 K) K) (adelicBox K) μ := by
  refine IsAddFundamentalDomain.mk' (measurableSet_adelicBox K).nullMeasurableSet fun x => ?_
  obtain ⟨k, hk, huniq⟩ := existsUnique_algebraMap_add_mem_adelicBox K x
  refine ⟨⟨algebraMap K _ k, k, rfl⟩, ?_, ?_⟩
  · show (algebraMap K (AdeleRing (𝓞 K) K) k) + x ∈ adelicBox K
    exact hk
  · rintro ⟨_, k', rfl⟩ hk'
    have : k' = k := huniq k' hk'
    subst this
    rfl

theorem isAddFundamentalDomain_adelicBox_adelicAddHaar :
    IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 K) K) (adelicBox K)
      (NumberField.AdelicHaar.adelicAddHaar (𝓞 K) K) :=
  isAddFundamentalDomain_adelicBox K _

omit [NumberField K] in

theorem properSpace_completion (v : InfinitePlace K) : ProperSpace v.Completion := by
  by_cases hv : v.IsReal
  · have h := (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.isometry
      |>.antilipschitz.properSpace
    exact h (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous
      (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.surjective
  · have hc : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hv
    have h := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.isometry
      |>.antilipschitz.properSpace
    exact h (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.continuous
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.surjective

open scoped Classical in
theorem norm_apply_le_of_isReal (x : InfiniteAdeleRing K) {v : InfinitePlace K} (hv : v.IsReal) :
    ‖x v‖ ≤ ‖InfiniteAdeleRing.ringEquiv_mixedSpace K x‖ := by
  have h1 : ‖InfinitePlace.Completion.extensionEmbeddingOfIsReal hv (x v)‖ = ‖x v‖ :=
    (AddMonoidHomClass.isometry_iff_norm _).mp
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv) (x v)
  have h2 : (InfiniteAdeleRing.ringEquiv_mixedSpace K x).1 ⟨v, hv⟩ =
      InfinitePlace.Completion.extensionEmbeddingOfIsReal hv (x v) := rfl
  rw [← h1, ← h2]
  exact (norm_le_pi_norm (InfiniteAdeleRing.ringEquiv_mixedSpace K x).1 ⟨v, hv⟩).trans
    (norm_fst_le (InfiniteAdeleRing.ringEquiv_mixedSpace K x))

open scoped Classical in
theorem norm_apply_le_of_isComplex (x : InfiniteAdeleRing K) {v : InfinitePlace K}
    (hv : v.IsComplex) : ‖x v‖ ≤ ‖InfiniteAdeleRing.ringEquiv_mixedSpace K x‖ := by
  have h1 : ‖InfinitePlace.Completion.extensionEmbedding v (x v)‖ = ‖x v‖ :=
    (AddMonoidHomClass.isometry_iff_norm _).mp
      (InfinitePlace.Completion.isometry_extensionEmbedding v) (x v)
  have h2 : (InfiniteAdeleRing.ringEquiv_mixedSpace K x).2 ⟨v, hv⟩ =
      InfinitePlace.Completion.extensionEmbedding v (x v) := rfl
  rw [← h1, ← h2]
  exact (norm_le_pi_norm (InfiniteAdeleRing.ringEquiv_mixedSpace K x).2 ⟨v, hv⟩).trans
    (norm_snd_le (InfiniteAdeleRing.ringEquiv_mixedSpace K x))

open scoped Classical in
theorem exists_forall_norm_apply_le_of_mem_infiniteBox :
    ∃ r : ℝ, ∀ x ∈ infiniteBox K, ∀ v : InfinitePlace K, ‖x v‖ ≤ r := by
  obtain ⟨r, hr⟩ := isBounded_iff_forall_norm_le.mp
    (ZSpan.fundamentalDomain_isBounded (mixedEmbedding.latticeBasis K))
  refine ⟨r, fun x hx v => ?_⟩
  have hx' : ‖InfiniteAdeleRing.ringEquiv_mixedSpace K x‖ ≤ r := hr _ hx
  by_cases hv : v.IsReal
  · exact (norm_apply_le_of_isReal K x hv).trans hx'
  · exact (norm_apply_le_of_isComplex K x (InfinitePlace.not_isReal_iff_isComplex.mp hv)).trans hx'

theorem exists_isCompact_infiniteBox_subset :
    ∃ S : Set (InfiniteAdeleRing K), IsCompact S ∧ infiniteBox K ⊆ S := by
  obtain ⟨r, hr⟩ := exists_forall_norm_apply_le_of_mem_infiniteBox K
  haveI : ∀ v : InfinitePlace K, ProperSpace v.Completion := fun v => properSpace_completion K v
  refine ⟨{x | ∀ v, ‖x v‖ ≤ r}, ?_, fun x hx v => hr x hx v⟩
  have : {x : InfiniteAdeleRing K | ∀ v, ‖x v‖ ≤ r} =
      Set.pi Set.univ fun v : InfinitePlace K => Metric.closedBall (0 : v.Completion) r := by
    ext x
    exact ⟨fun h v _ => mem_closedBall_zero_iff.mpr (h v),
      fun h v => mem_closedBall_zero_iff.mp (h v (Set.mem_univ v))⟩
  rw [this]
  exact isCompact_univ_pi fun v => isCompact_closedBall (0 : v.Completion) r

theorem isCompact_integralFiniteAdeles : IsCompact (integralFiniteAdeles (𝓞 K) K) := by
  haveI : ∀ v : HeightOneSpectrum (𝓞 K),
      CompactSpace ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) := fun v =>
    IsDedekindDomain.HeightOneSpectrum.compactSpace K v
  haveI : Fact (∀ v : HeightOneSpectrum (𝓞 K),
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    ⟨fun v => Valued.isOpen_valuationSubring _⟩
  have h := isCompact_range (RestrictedProduct.isOpenEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (A := fun v : HeightOneSpectrum (𝓞 K) =>
      (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    Fact.out).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

theorem isOpen_integralFiniteAdeles : IsOpen (integralFiniteAdeles (𝓞 K) K) := by
  haveI : Fact (∀ v : HeightOneSpectrum (𝓞 K),
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    ⟨fun v => Valued.isOpen_valuationSubring _⟩
  exact RestrictedProduct.isOpen_forall_mem
    (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (A := fun v : HeightOneSpectrum (𝓞 K) =>
      (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    Fact.out

theorem exists_isCompact_adelicBox_subset :
    ∃ C : Set (AdeleRing (𝓞 K) K), IsCompact C ∧ adelicBox K ⊆ C := by
  obtain ⟨S, hS, hsub⟩ := exists_isCompact_infiniteBox_subset K
  refine ⟨{x | x.1 ∈ S ∧ x.2 ∈ integralFiniteAdeles (𝓞 K) K}, ?_, fun x hx => ⟨hsub hx.1, hx.2⟩⟩
  have : IsCompact (S ×ˢ integralFiniteAdeles (𝓞 K) K) := hS.prod (isCompact_integralFiniteAdeles K)
  exact this

theorem measure_adelicBox_lt_top (μ : Measure (AdeleRing (𝓞 K) K)) [IsFiniteMeasureOnCompacts μ] :
    μ (adelicBox K) < ⊤ := by
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset K
  exact (measure_mono hsub).trans_lt hC.measure_lt_top

open scoped Classical in

theorem exists_isOpen_subset_adelicBox :
    ∃ U : Set (AdeleRing (𝓞 K) K), IsOpen U ∧ U.Nonempty ∧ U ⊆ adelicBox K := by
  set b := mixedEmbedding.latticeBasis K with hb
  set e := InfiniteAdeleRing.ringEquiv_mixedSpace K with he

  let V : Set (mixedEmbedding.mixedSpace K) := {m | ∀ i, b.repr m i ∈ Set.Ioo (0 : ℝ) 1}
  have hVopen : IsOpen V := by
    have : V = ⋂ i, (fun m => b.repr m i) ⁻¹' Set.Ioo (0 : ℝ) 1 := by ext m; simp [V]
    rw [this]
    refine isOpen_iInter_of_finite fun i => IsOpen.preimage ?_ isOpen_Ioo
    exact (b.coord i).continuous_of_finiteDimensional
  have hVsub : V ⊆ ZSpan.fundamentalDomain b := fun m hm i => Set.Ioo_subset_Ico_self (hm i)
  have hVne : (e.symm (b.equivFun.symm fun _ => 1 / 2)) ∈ e ⁻¹' V := by
    show e (e.symm _) ∈ V
    rw [RingEquiv.apply_symm_apply]
    intro i
    rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
    norm_num
  have hc1 : Continuous fun x : AdeleRing (𝓞 K) K => x.1 := continuous_fst
  have hc2 : Continuous fun x : AdeleRing (𝓞 K) K => x.2 := continuous_snd
  refine ⟨{x | x.1 ∈ e ⁻¹' V ∧ x.2 ∈ integralFiniteAdeles (𝓞 K) K}, ?_, ?_, ?_⟩
  · exact ((hVopen.preimage (continuous_ringEquiv_mixedSpace K)).preimage hc1).inter
      ((isOpen_integralFiniteAdeles K).preimage hc2)
  · refine ⟨((e.symm (b.equivFun.symm fun _ => 1 / 2), 0) :
      InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K), hVne, ?_⟩
    intro v
    exact zero_mem _
  · rintro x ⟨hx1, hx2⟩
    exact ⟨hVsub hx1, hx2⟩

theorem measure_adelicBox_pos (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsOpenPosMeasure] :
    0 < μ (adelicBox K) := by
  obtain ⟨U, hU, hne, hsub⟩ := exists_isOpen_subset_adelicBox K
  exact (hU.measure_pos μ hne).trans_le (measure_mono hsub)

attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

theorem adelicAddHaar_adelicBox_lt_top :
    NumberField.AdelicHaar.adelicAddHaar (𝓞 K) K (adelicBox K) < ⊤ :=
  measure_adelicBox_lt_top K _

theorem adelicAddHaar_adelicBox_pos :
    0 < NumberField.AdelicHaar.adelicAddHaar (𝓞 K) K (adelicBox K) :=
  measure_adelicBox_pos K _

open scoped ProbabilityTheory in
theorem isProbabilityMeasure_cond_adelicBox :
    IsProbabilityMeasure ((NumberField.AdelicHaar.adelicAddHaar (𝓞 K) K)[|adelicBox K]) :=
  ProbabilityTheory.cond_isProbabilityMeasure_of_finite (adelicAddHaar_adelicBox_pos K).ne'
    (adelicAddHaar_adelicBox_lt_top K).ne

end Box

end NumberField.AdelicBox

open scoped Pointwise

/-! ### Adelic `PGL(2)`

For a Dedekind domain `R` with fraction field `K`, adelic `PGL(2)` is the quotient of
`GL (Fin 2) (AdeleRing R K)` by its centre, with the quotient group structure and the quotient
topology. The centre is the range of the scalar map from the units of the adele ring
(`Matrix.GeneralLinearGroup.center_eq_range_scalar`), and that map is injective
(`scalar_injective`). Since `AdelicPGL2` is an abbreviation, it inherits Mathlib's quotient-group
instances: it is a topological group (`QuotientGroup.instIsTopologicalGroup`), regular and
Hausdorff because the centre is closed (`isClosed_center`, `QuotientGroup.instT3Space`), and
locally compact when `AdeleRing R K` is (`QuotientGroup.instLocallyCompactSpace`), as for
`R = 𝓞 K` over a number field `K` (`NumberField.AdeleRing.locallyCompactSpace`). Given those two
instances, `adelicPGLHaar` is a Haar measure on it; the results about it in the section
`NumberFieldCase` also assume that `K` is a number field and that `R` is a free `ℤ`-module of
finite rank. The generic measure bounds before that section need neither.
-/

namespace NumberField.AdelicCentre

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- **Injectivity of the adelic scalar map.** For a Dedekind domain `R` with fraction field `K`,
the scalar map from the units of `AdeleRing R K` to adelic `GL(2)`, sending `a` to the scalar
matrix with diagonal entries `a`, is injective. With
`Matrix.GeneralLinearGroup.center_eq_range_scalar`, it identifies these units with the centre
of adelic `GL(2)`. -/
theorem scalar_injective :
    Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 2) : (AdeleRing R K)ˣ →* _) :=
  fun a b h => by
    have := congrArg (fun g : GL (Fin 2) (AdeleRing R K) => (g : Matrix (Fin 2) (Fin 2) (AdeleRing
      R K)) 0 0) h
    exact Units.ext (by simpa using this)

/-- **Adelic `PGL(2)`.** For a Dedekind domain `R` with fraction field `K`, the quotient of
`GL (Fin 2) (AdeleRing R K)` by its centre, the scalar matrices. As an abbreviation, it carries
the quotient group structure, the quotient topology and Mathlib's instances for quotient groups.
Mathlib's `Matrix.ProjGenLinGroup (Fin 2) (AdeleRing R K)` is the same group, but it is a `def`
with no topology. -/
abbrev AdelicPGL2 : Type _ :=
  GL (Fin 2) (AdeleRing R K) ⧸ Subgroup.center (GL (Fin 2) (AdeleRing R K))

/-- **Open images in adelic `PGL(2)` have positive measure.** Let `R` be a Dedekind domain with
fraction field `K`, and let `μ` be an open-positive measure on adelic `PGL(2)`, for any measurable
space `m`; no number-field hypothesis is needed. The image of a set `D` of adelic `GL(2)` that
contains a nonempty open set has positive `μ`-measure, since the quotient map is open. -/
theorem measure_image_mk_pos {m : MeasurableSpace (AdelicPGL2 R K)} (μ : Measure (AdelicPGL2 R K))
    [μ.IsOpenPosMeasure] {D : Set (GL (Fin 2) (AdeleRing R K))}
    (h : ∃ U : Set (GL (Fin 2) (AdeleRing R K)), IsOpen U ∧ U.Nonempty ∧ U ⊆ D) :
    0 < μ ((QuotientGroup.mk : GL (Fin 2) (AdeleRing R K) → AdelicPGL2 R K) '' D) := by
  obtain ⟨U, hU, hne, hsub⟩ := h
  exact ((QuotientGroup.isOpenMap_coe U hU).measure_pos μ (hne.image _)).trans_le
    (measure_mono (Set.image_mono hsub))

/-- **Compact images in adelic `PGL(2)` have finite measure.** Let `R` be a Dedekind domain with
fraction field `K`, and let `μ` be a measure on adelic `PGL(2)`, for any measurable space `m`,
that is finite on compact sets; no number-field hypothesis is needed. The image of a compact set
of adelic `GL(2)` has finite `μ`-measure. -/
theorem measure_image_mk_lt_top {m : MeasurableSpace (AdelicPGL2 R K)} (μ : Measure (AdelicPGL2 R
  K))
    [IsFiniteMeasureOnCompacts μ] {C : Set (GL (Fin 2) (AdeleRing R K))} (hC : IsCompact C) :
    μ ((QuotientGroup.mk : GL (Fin 2) (AdeleRing R K) → AdelicPGL2 R K) '' C) < ⊤ :=
  (hC.image QuotientGroup.continuous_mk).measure_lt_top

/-- **Images modulo the centre.** Let `R` be a Dedekind domain with fraction field `K`. If
`D ⊆ C * Z`, where `Z` is the centre of adelic `GL(2)`, then the image of `D` in adelic `PGL(2)`
lies in the image of `C`. -/
theorem image_mk_subset_of_subset_mul_center {D C : Set (GL (Fin 2) (AdeleRing R K))}
    (h : D ⊆ C * ((Subgroup.center (GL (Fin 2) (AdeleRing R K)) : Set (GL (Fin 2) (AdeleRing R
      K))))) :
    (QuotientGroup.mk : _ → AdelicPGL2 R K) '' D ⊆ (QuotientGroup.mk : _ → AdelicPGL2 R K) '' C :=
      by
  rintro _ ⟨d, hd, rfl⟩
  obtain ⟨c, hc, z, hz, rfl⟩ := h hd
  refine ⟨c, hc, ?_⟩
  rw [QuotientGroup.eq]
  simpa using hz

/-- **Borel measurable space on adelic `PGL(2)`.** For a Dedekind domain `R` with fraction field
`K`, the Borel σ-algebra of the quotient topology on adelic `PGL(2)`. Like
`NumberField.AdelicHaar.adeleBorel` and `NumberField.AdelicHaar.glBorel`, it is a reducible
definition rather than an instance: statements about `adelicPGLHaar` name it, and proofs install
it with `letI` together with `borelSpace_pglBorel`. -/
@[reducible] def pglBorel : MeasurableSpace (AdelicPGL2 R K) := borel _

/-- **`pglBorel` is Borel.** For a Dedekind domain `R` with fraction field `K`, `pglBorel R K`
is the Borel σ-algebra of the quotient topology on adelic `PGL(2)`. -/
theorem borelSpace_pglBorel : @BorelSpace (AdelicPGL2 R K) _ (pglBorel R K) :=
  @BorelSpace.mk _ _ (pglBorel R K) rfl

section NumberFieldCase

variable [Module.Free ℤ R] [Module.Finite ℤ R] [NumberField K]

/-- **The centre of adelic `GL(2)` is closed.** For a Dedekind domain `R` with fraction field `K`
(this instance takes no number-field hypothesis), the centre is the intersection, over all `g`,
of the closed sets `{z | g * z = z * g}`. With Mathlib's `QuotientGroup.instT3Space`, this makes
adelic `PGL(2)` regular and Hausdorff. -/
instance isClosed_center :
    IsClosed ((Subgroup.center (GL (Fin 2) (AdeleRing R K)) : Set (GL (Fin 2) (AdeleRing R K)))) :=
      by
  have : ((Subgroup.center (GL (Fin 2) (AdeleRing R K)) : Set (GL (Fin 2) (AdeleRing R K))))
      = ⋂ g : GL (Fin 2) (AdeleRing R K), {z | g * z = z * g} := by
    ext z
    simp only [SetLike.mem_coe, Subgroup.mem_center_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [this]
  exact isClosed_iInter fun g =>
    isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)

/-- **Haar measure on adelic `PGL(2)`.** Let `R` be a Dedekind domain with fraction field `K`, and
assume that adelic `PGL(2)` is a topological group and locally compact (the instance arguments
`IsTopologicalGroup (AdelicPGL2 R K)` and `LocallyCompactSpace (AdelicPGL2 R K)`). Then
`adelicPGLHaar R K` is a Haar measure for the Borel measurable space `pglBorel R K`: Mathlib's
`MeasureTheory.Measure.haar`, which gives measure `1` to an arbitrarily chosen positive compact
set. Mathlib's quotient-group instances supply the first assumption for every such `R`, and the
second when `AdeleRing R K` is locally compact, as for `R = 𝓞 K` over a number field `K`. The
results about `adelicPGLHaar` (`isHaarMeasure_adelicPGLHaar`, `adelicPGLHaar_image_pos`,
`adelicPGLHaar_image_lt_top_of_subset`) also assume that `K` is a number field and that `R` is a
free `ℤ`-module of finite rank. -/
def adelicPGLHaar [IsTopologicalGroup (AdelicPGL2 R K)]
    [LocallyCompactSpace (AdelicPGL2 R K)] :
    @Measure (AdelicPGL2 R K) (pglBorel R K) := by
  letI := pglBorel R K
  haveI := borelSpace_pglBorel R K
  exact Measure.haar

/-- **`adelicPGLHaar` is a Haar measure.** In the setting of `adelicPGLHaar` (`R` a Dedekind domain
with fraction field `K`, and adelic `PGL(2)` a locally compact topological group), with `K` a
number field and `R` a free `ℤ`-module of finite rank, `adelicPGLHaar R K` is a Haar measure on
adelic `PGL(2)`. -/
theorem isHaarMeasure_adelicPGLHaar [IsTopologicalGroup (AdelicPGL2 R K)]
    [LocallyCompactSpace (AdelicPGL2 R K)] :
    @Measure.IsHaarMeasure (AdelicPGL2 R K) _ _ (pglBorel R K) (adelicPGLHaar R K) := by
  letI := pglBorel R K
  haveI := borelSpace_pglBorel R K
  exact Measure.isHaarMeasure_haarMeasure _

/-- **Positivity of `adelicPGLHaar` on open images.** In the setting of `adelicPGLHaar` (`R` a
Dedekind domain with fraction field `K`, and adelic `PGL(2)` a locally compact topological group),
with `K` a number field and `R` a free `ℤ`-module of finite rank, the image in adelic `PGL(2)` of a
set of adelic `GL(2)` that contains a nonempty open set has positive `adelicPGLHaar` measure. -/
theorem adelicPGLHaar_image_pos [IsTopologicalGroup (AdelicPGL2 R K)]
    [LocallyCompactSpace (AdelicPGL2 R K)] {D : Set (GL (Fin 2) (AdeleRing R K))}
    (h : ∃ U : Set (GL (Fin 2) (AdeleRing R K)), IsOpen U ∧ U.Nonempty ∧ U ⊆ D) :
    0 < adelicPGLHaar R K ((QuotientGroup.mk : _ → AdelicPGL2 R K) '' D) := by
  letI := pglBorel R K
  haveI := borelSpace_pglBorel R K
  haveI := isHaarMeasure_adelicPGLHaar R K
  exact measure_image_mk_pos R K _ h

/-- **Finite `adelicPGLHaar` measure modulo the centre.** In the setting of `adelicPGLHaar` (`R` a
Dedekind domain with fraction field `K`, and adelic `PGL(2)` a locally compact topological group),
with `K` a number field and `R` a free `ℤ`-module of finite rank: if `D ⊆ C * Z` for a compact set
`C` and the centre `Z` of adelic `GL(2)`, then the image of `D` in adelic `PGL(2)` has finite
`adelicPGLHaar` measure. -/
theorem adelicPGLHaar_image_lt_top_of_subset [IsTopologicalGroup (AdelicPGL2 R K)]
    [LocallyCompactSpace (AdelicPGL2 R K)] {D C : Set (GL (Fin 2) (AdeleRing R K))} (hC :
  IsCompact C)
    (h : D ⊆ C * ((Subgroup.center (GL (Fin 2) (AdeleRing R K)) : Set (GL (Fin 2) (AdeleRing R
      K))))) :
    adelicPGLHaar R K ((QuotientGroup.mk : _ → AdelicPGL2 R K) '' D) < ⊤ := by
  letI := pglBorel R K
  haveI := borelSpace_pglBorel R K
  haveI := isHaarMeasure_adelicPGLHaar R K
  exact lt_of_le_of_lt (measure_mono (image_mk_subset_of_subset_mul_center R K h))
    (measure_image_mk_lt_top R K _ hC)

end NumberFieldCase

end NumberField.AdelicCentre

end
