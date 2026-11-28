/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DedekindDomain.AdicCompletionIntegers
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Residue field of the adic completion integers

For a Dedekind domain `A` with fraction field `K` and
`𝔭 : IsDedekindDomain.HeightOneSpectrum A`, the composite map starting at `A`,
through the `𝔭`-adic completion integers and onto the residue field of the
completion, is surjective with kernel `𝔭.asIdeal`, inducing a residue-field
ring equivalence.
-/

@[expose] public section

noncomputable section

open IsDedekindDomain
open scoped Valued

namespace IsDedekindDomain.HeightOneSpectrum

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
variable (𝔭 : HeightOneSpectrum A)

/-- **Residue map to the completed residue field.** Let $A$ be a Dedekind domain with fraction
field $K$, let $\mathfrak{p}$ be a height-one prime of $A$, and let $\mathcal{O}_\mathfrak{p}$ be
the valuation ring of the $\mathfrak{p}$-adic completion of $K$, with maximal ideal
$\mathfrak{m}_\mathfrak{p}$. The residue map is the ring homomorphism
$A \to \mathcal{O}_\mathfrak{p}/\mathfrak{m}_\mathfrak{p}$ obtained by composing the canonical map
$A \to \mathcal{O}_\mathfrak{p}$ with the quotient map
$\mathcal{O}_\mathfrak{p} \to \mathcal{O}_\mathfrak{p}/\mathfrak{m}_\mathfrak{p}$. -/
noncomputable def completionResidueMap :
    A →+* (𝔭.adicCompletionIntegers K ⧸
      IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K)) :=
  (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K))).comp
    (algebraMap A (𝔭.adicCompletionIntegers K))

/-- **Kernel of the completed residue map.** Let $A$ be a Dedekind domain with fraction field $K$,
let $\mathfrak{p}$ be a height-one prime of $A$, and let $\mathcal{O}_\mathfrak{p}$ be the
valuation ring of the $\mathfrak{p}$-adic completion of $K$, with maximal ideal
$\mathfrak{m}_\mathfrak{p}$. The kernel of the residue map
$A \to \mathcal{O}_\mathfrak{p}/\mathfrak{m}_\mathfrak{p}$, the canonical map
$A \to \mathcal{O}_\mathfrak{p}$ followed by the quotient map, is $\mathfrak{p}$. -/
theorem ker_completionResidueMap :
    RingHom.ker (𝔭.completionResidueMap (K := K)) = 𝔭.asIdeal := by
  ext a
  simp only [RingHom.mem_ker, completionResidueMap, RingHom.comp_apply,
    Ideal.Quotient.eq_zero_iff_mem]
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have hval : Valued.v (↑(algebraMap A (𝔭.adicCompletionIntegers K) a) :
      𝔭.adicCompletion K) = 𝔭.valuation K (algebraMap A K a) := by
    simp only [algebraMap_adicCompletionIntegers_apply]
    exact valuedAdicCompletion_eq_valuation' 𝔭 (algebraMap A K a)
  have hle : Valued.v (↑(algebraMap A (𝔭.adicCompletionIntegers K) a) :
      𝔭.adicCompletion K) ≤ 1 :=
    (algebraMap A (𝔭.adicCompletionIntegers K) a).2
  rw [hval] at hle ⊢
  rw [← valuation_lt_one_iff_mem (K := K)]
  exact ⟨fun h => lt_of_le_of_ne hle h, fun h => ne_of_lt h⟩

private lemma exists_mul_sub_mem_of_not_mem (b : A) (hb : b ∉ 𝔭.asIdeal) :
    ∃ e : A, b * e - 1 ∈ 𝔭.asIdeal := by
  have hmax : 𝔭.asIdeal.IsMaximal := 𝔭.isPrime.isMaximal 𝔭.ne_bot
  have hfield :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient 𝔭.asIdeal).mp hmax
  have hne : Ideal.Quotient.mk 𝔭.asIdeal b ≠ 0 := by
    rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨inv, hinv⟩ := hfield.mul_inv_cancel hne
  obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective inv
  exact ⟨e, by rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_mul,
    sub_eq_zero]; exact hinv⟩

/-- **Surjectivity of the completed residue map.** Let $A$ be a Dedekind domain with fraction
field $K$, let $\mathfrak{p}$ be a height-one prime of $A$, and let $\mathcal{O}_\mathfrak{p}$ be
the valuation ring of the $\mathfrak{p}$-adic completion of $K$, with maximal ideal
$\mathfrak{m}_\mathfrak{p}$. The residue map
$A \to \mathcal{O}_\mathfrak{p}/\mathfrak{m}_\mathfrak{p}$, the canonical map
$A \to \mathcal{O}_\mathfrak{p}$ followed by the quotient map, is surjective. -/
theorem surjective_completionResidueMap :
    Function.Surjective (𝔭.completionResidueMap (K := K)) := by
  intro q
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hd := 𝔭.denseRange_algebraMap K
  have hxcl := hd (x : 𝔭.adicCompletion K)
  rw [mem_closure_iff_nhds] at hxcl
  have hball : {y : 𝔭.adicCompletion K | Valued.v (y - ↑x) < 1} ∈ nhds (↑x) := by
    rw [Valued.mem_nhds]
    refine ⟨1, fun y hy => ?_⟩
    simp only [Set.mem_ofPred_eq] at hy ⊢
    rw [Valued.v.restrict_lt_iff_lt_embedding] at hy
    simp only [Units.val_one, map_one] at hy
    exact hy
  obtain ⟨y, hy, ⟨k, rfl⟩⟩ := hxcl _ hball
  simp only [Set.mem_ofPred_eq] at hy
  have hxle : Valued.v (x : 𝔭.adicCompletion K) ≤ 1 := x.2
  have hkle : Valued.v (algebraMap K (𝔭.adicCompletion K) k) ≤ 1 := by
    have : algebraMap K (𝔭.adicCompletion K) k =
        (x : 𝔭.adicCompletion K) -
          ((x : 𝔭.adicCompletion K) - algebraMap K (𝔭.adicCompletion K) k) := by
      ring
    rw [this]
    exact le_trans (Valued.v.map_sub _ _)
      (max_le hxle (le_of_lt (by rwa [Valuation.map_sub_swap] at hy)))
  have hkval : 𝔭.valuation K k ≤ 1 := by
    rw [show Valued.v (algebraMap K (𝔭.adicCompletion K) k) = 𝔭.valuation K k
      from by
      simpa only [algebraMap_adicCompletion, Function.comp_apply,
        Algebra.algebraMap_self_apply] using 𝔭.valuedAdicCompletion_eq_valuation' k] at hkle
    exact hkle
  obtain ⟨a, ⟨b, hb⟩, hkab⟩ := 𝔭.exists_primeCompl_mul_eq_of_integer k hkval
  obtain ⟨t, hbt⟩ := 𝔭.exists_mul_sub_mem_of_not_mem b hb
  use a * t
  show completionResidueMap 𝔭 (a * t) = Ideal.Quotient.mk _ x
  simp only [completionResidueMap, RingHom.comp_apply]
  rw [Ideal.Quotient.eq, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    adicCompletionIntegers.isUnit_iff_valued_eq_one]
  suffices h : Valued.v (↑(algebraMap A (𝔭.adicCompletionIntegers K) (a * t) - x) :
      𝔭.adicCompletion K) < 1 from ne_of_lt h
  change Valued.v ((↑(algebraMap A (𝔭.adicCompletionIntegers K) (a * t)) :
    𝔭.adicCompletion K) - (↑x : 𝔭.adicCompletion K)) < 1
  have hcoe_alg : (↑(algebraMap A (𝔭.adicCompletionIntegers K) (a * t)) :
      𝔭.adicCompletion K) =
      algebraMap K (𝔭.adicCompletion K) (algebraMap A K (a * t)) := by
    simp only [algebraMap_adicCompletionIntegers_apply, algebraMap_adicCompletion,
      Function.comp_apply]
    congr 1
  rw [hcoe_alg]
  have hterm1 :
      Valued.v (algebraMap K (𝔭.adicCompletion K) (algebraMap A K (a * t)) -
        algebraMap K (𝔭.adicCompletion K) k) < 1 := by
    have halg_eq : algebraMap A K (a * t) - k =
        k * algebraMap A K (b * t - 1) := by
      simp only [map_mul, map_sub, map_one]
      rw [show algebraMap A K a = k * algebraMap A K b from hkab.symm]; ring
    have hval_bound : 𝔭.valuation K (algebraMap A K (a * t) - k) < 1 := by
      rw [halg_eq, map_mul]
      calc 𝔭.valuation K k * 𝔭.valuation K (algebraMap A K (b * t - 1))
          ≤ 1 * 𝔭.valuation K (algebraMap A K (b * t - 1)) := by gcongr
        _ = 𝔭.valuation K (algebraMap A K (b * t - 1)) := one_mul _
        _ < 1 := (𝔭.valuation_lt_one_iff_mem (K := K) _).mpr hbt
    rw [show algebraMap K (𝔭.adicCompletion K) (algebraMap A K (a * t)) -
        algebraMap K (𝔭.adicCompletion K) k =
        algebraMap K (𝔭.adicCompletion K) (algebraMap A K (a * t) - k) from by
      rw [map_sub]]
    rw [show Valued.v
        (algebraMap K (𝔭.adicCompletion K) (algebraMap A K (a * t) - k)) =
        𝔭.valuation K (algebraMap A K (a * t) - k) from by
      simpa only [algebraMap_adicCompletion, Function.comp_apply,
        Algebra.algebraMap_self_apply] using
          𝔭.valuedAdicCompletion_eq_valuation' (algebraMap A K (a * t) - k)]
    exact hval_bound
  have hsplit : algebraMap K (𝔭.adicCompletion K) (algebraMap A K (a * t)) - ↑x =
    (algebraMap K (𝔭.adicCompletion K) (algebraMap A K (a * t)) -
      algebraMap K (𝔭.adicCompletion K) k) +
    (algebraMap K (𝔭.adicCompletion K) k - ↑x) := by ring
  rw [hsplit]
  exact lt_of_le_of_lt (Valued.v.map_add_le_max' _ _) (max_lt hterm1 hy)

/-- **Residue field of the completion.** Let $A$ be a Dedekind domain with fraction field $K$, let
$\mathfrak{p}$ be a height-one prime of $A$, and let $\mathcal{O}_\mathfrak{p}$ be the valuation
ring of the $\mathfrak{p}$-adic completion of $K$, with maximal ideal $\mathfrak{m}_\mathfrak{p}$.
This is the ring isomorphism
$\mathcal{O}_\mathfrak{p}/\mathfrak{m}_\mathfrak{p} \cong A/\mathfrak{p}$ that sends the residue
class of the image of each $a \in A$ to the class of $a$ modulo $\mathfrak{p}$. It is induced by
the residue map $A \to \mathcal{O}_\mathfrak{p}/\mathfrak{m}_\mathfrak{p}$ (the canonical map
$A \to \mathcal{O}_\mathfrak{p}$ followed by the quotient map), which is surjective with kernel
$\mathfrak{p}$. -/
noncomputable def completionResidueFieldEquiv :
    (↥(𝔭.adicCompletionIntegers K) ⧸
      IsLocalRing.maximalIdeal ↥(𝔭.adicCompletionIntegers K)) ≃+* (A ⧸ 𝔭.asIdeal) :=
  (RingHom.quotientKerEquivOfSurjective
    (𝔭.surjective_completionResidueMap (K := K))).symm.trans
    (Ideal.quotEquivOfEq (𝔭.ker_completionResidueMap (K := K)))

end IsDedekindDomain.HeightOneSpectrum
