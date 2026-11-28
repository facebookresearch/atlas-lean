/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.Valuation.DVRFinite
public import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Discrete valuation rings dominating a one-dimensional local domain

Let `R` be a Noetherian local domain of Krull dimension at most one which is not a field, with
fraction field `K`, and let `L` be a finite extension of `K`. Then some discrete valuation ring
with fraction field `L` dominates `R`: there is a valuation subring `V` of `L` that is a discrete
valuation ring, contains the image of `R`, and contains the image of the maximal ideal of `R` in
its maximal ideal (`IsLocalRing.exists_isDiscreteValuationRing_dominating`).

This is the case `dim R ≤ 1`, `L/K` finite of the Stacks project, Lemma 10.119.13
(Tag 00PH), https://stacks.math.columbia.edu/tag/00PH, which is the last step of its proof; the
general statement (any Noetherian local domain, `L/K` finitely generated) reduces to it there by a
transcendence basis and Lemma 10.119.1, and that reduction is formalized in
`MathlibExt.RingTheory.Valuation.DVRDominationNoetherian`. The proof takes a
valuation subring of `L` dominating the image of `R` and applies the Krull–Akizuki theorem in the
form `ValuationSubring.isDiscreteValuationRing_of_algebraMap_mem_of_finite`.
-/

@[expose] public section

open IsLocalRing

namespace IsLocalRing

/-- **Discrete valuation rings dominating a one-dimensional local domain.** Let `R` be a
Noetherian local domain of Krull dimension at most one which is not a field, `K` its fraction
field and `L` a finite extension of `K`. Then there is a valuation subring `V` of `L` (whose
fraction field is `L`) which is a discrete valuation ring and dominates `R`: it contains the image
of `R`, and the image of the maximal ideal of `R` consists of nonunits of `V`.

This is the Stacks project, Lemma 10.119.13 (Tag 00PH), in the case `dim R ≤ 1` and `L/K`
finite. -/
theorem exists_isDiscreteValuationRing_dominating
    {R K L : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    [Ring.KrullDimLE 1 R] (hR : ¬ IsField R)
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L] [Module.Finite K L] :
    ∃ V : ValuationSubring L, IsDiscreteValuationRing V ∧ (∀ r : R, algebraMap R L r ∈ V) ∧
      ∀ r ∈ maximalIdeal R, algebraMap R L r ∈ V.nonunits := by
  have hinj : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  let f := (algebraMap R L).rangeRestrict
  have hf : Function.Surjective f := RingHom.rangeRestrict_surjective _
  have hker : RingHom.ker f ≤ maximalIdeal R := by
    intro x hx
    have : algebraMap R L x = 0 := congrArg Subtype.val ((RingHom.mem_ker).1 hx)
    rw [hinj (this.trans (map_zero _).symm)]
    exact zero_mem _
  have hmax := Ideal.IsMaximal.map_of_surjective_of_ker_le hf hker
  obtain ⟨V, hAV, hI⟩ := Ideal.image_subset_nonunits_valuationSubring _ hmax.ne_top
  have hmem : ∀ r : R, algebraMap R L r ∈ V := fun r ↦ hAV ⟨r, rfl⟩
  have hnon : ∀ r ∈ maximalIdeal R, algebraMap R L r ∈ V.nonunits := fun r hr ↦
    hI ⟨f r, Ideal.mem_map_of_mem _ hr, rfl⟩
  have hne : V ≠ ⊤ := by
    intro hV
    have hm : maximalIdeal R ≠ ⊥ := fun h ↦ hR ((isField_iff_maximalIdeal_eq).2 h)
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
    have hx0 : algebraMap R L r ≠ 0 := fun h ↦ hr0 (hinj (h.trans (map_zero _).symm))
    have h1 := (V.mem_nonunits_iff).1 (hnon r hr)
    have h2 : V.valuation (algebraMap R L r)⁻¹ ≤ 1 :=
      (V.valuation_le_one_iff _).2 (by rw [hV]; trivial)
    rw [map_inv₀] at h2
    have h3 : V.valuation (algebraMap R L r) ≠ 0 := by simpa using hx0
    exact absurd ((inv_le_one₀ (zero_lt_iff.2 h3)).1 h2) (not_le.2 h1)
  exact ⟨V,
    ValuationSubring.isDiscreteValuationRing_of_algebraMap_mem_of_finite (K := K) V hmem hne,
    hmem, hnon⟩

end IsLocalRing
