/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Möbius inversion and the Möbius function of products and Boolean algebras

Mathlib's `IncidenceAlgebra` provides the incidence algebra of a locally finite order, its zeta
function `IncidenceAlgebra.zeta` and Möbius function `IncidenceAlgebra.mu`, one direction of
Möbius inversion under an `OrderBot` (`IncidenceAlgebra.moebius_inversion_bot`) or `OrderTop`
hypothesis, and the product theorem in algebra form (`IncidenceAlgebra.mu_prod_mu`).

This file states these results in the form of Stanley, *Enumerative Combinatorics*, vol. 1,
2nd ed. (author's draft of 15 July 2011, https://math.mit.edu/~rstan/ec/ec1.pdf), Section 3.7
and 3.8:

* `moebius_inversion_iff`: Proposition 3.7.1, both directions, for a poset whose principal order
  ideals are finite; no least element is assumed.
* `moebius_inversion_dual_iff`: Proposition 3.7.2, the dual form.
* `mu_prod_apply`: Proposition 3.8.2, the product theorem, pointwise.
* `mu_finset_of_subset`: Example 3.8.3, the Möbius function of a Boolean algebra.
-/

@[expose] public section

open Finset IncidenceAlgebra

namespace MathlibExt.Order.IncidenceAlgebra.MoebiusInversion

section Inversion

variable {𝕜 α : Type*} [Ring 𝕜] [PartialOrder α] [LocallyFiniteOrder α]

/-- Exchange of summation over the pairs `u ≤ s ≤ t`. -/
private lemma sum_Iic_sum_Iic [LocallyFiniteOrderBot α] (t : α) (F : α → α → 𝕜) :
    ∑ s ∈ Iic t, ∑ u ∈ Iic s, F u s = ∑ u ∈ Iic t, ∑ s ∈ Icc u t, F u s :=
  Finset.sum_comm' fun s u => by
    simp only [mem_Iic, mem_Icc]
    exact ⟨fun ⟨hs, hu⟩ => ⟨⟨hu, hs⟩, hu.trans hs⟩, fun ⟨⟨hu, hs⟩, _⟩ => ⟨hs, hu⟩⟩

/-- Exchange of summation over the pairs `t ≤ s ≤ u`. -/
private lemma sum_Ici_sum_Ici [LocallyFiniteOrderTop α] (t : α) (F : α → α → 𝕜) :
    ∑ s ∈ Ici t, ∑ u ∈ Ici s, F u s = ∑ u ∈ Ici t, ∑ s ∈ Icc t u, F u s :=
  Finset.sum_comm' fun s u => by
    simp only [mem_Ici, mem_Icc]
    exact ⟨fun ⟨hs, hu⟩ => ⟨⟨hs, hu⟩, hs.trans hu⟩, fun ⟨⟨hs, hu⟩, _⟩ => ⟨hs, hu⟩⟩

/-- **Möbius inversion formula.** Let `P` be a poset in which every principal order ideal
`Λ_t = {s : s ≤ t}` is finite, and let `f g : P → 𝕜` take values in a ring. Then
`g(t) = ∑_{s ≤ t} f(s)` for all `t` if and only if `f(t) = ∑_{s ≤ t} g(s) μ(s, t)` for all `t`,
where `μ` is the Möbius function of `P` (Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed.,
author's draft of 15 July 2011, Proposition 3.7.1, stated there over a field).

No least element is assumed: Mathlib's `IncidenceAlgebra.moebius_inversion_bot` proves the
direction `→` under `OrderBot`. -/
theorem moebius_inversion_iff [DecidableEq α] [LocallyFiniteOrderBot α] (f g : α → 𝕜) :
    (∀ t, g t = ∑ s ∈ Iic t, f s) ↔ ∀ t, f t = ∑ s ∈ Iic t, g s * mu 𝕜 s t := by
  constructor
  · intro h t
    simp_rw [h, Finset.sum_mul]
    rw [sum_Iic_sum_Iic t (fun u s => f u * mu 𝕜 s t)]
    simp_rw [← Finset.mul_sum, sum_Icc_mu_left]
    rw [Finset.sum_eq_single t (fun u _ hu => by simp [hu]) (by simp)]
    simp
  · intro h t
    simp_rw [h]
    rw [sum_Iic_sum_Iic t (fun u s => g u * mu 𝕜 u s)]
    simp_rw [← Finset.mul_sum, sum_Icc_mu_right]
    rw [Finset.sum_eq_single t (fun u _ hu => by simp [hu]) (by simp)]
    simp

/-- **Möbius inversion formula, dual form.** Let `P` be a poset in which every principal dual
order ideal `V_s = {t : t ≥ s}` is finite, and let `f g : P → 𝕜`. Then
`g(s) = ∑_{t ≥ s} f(t)` for all `s` if and only if `f(s) = ∑_{t ≥ s} μ(s, t) g(t)` for all `s`
(Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed., author's draft of 15 July 2011,
Proposition 3.7.2). -/
theorem moebius_inversion_dual_iff [DecidableEq α] [LocallyFiniteOrderTop α] (f g : α → 𝕜) :
    (∀ s, g s = ∑ t ∈ Ici s, f t) ↔ ∀ s, f s = ∑ t ∈ Ici s, mu 𝕜 s t * g t := by
  constructor
  · intro h s
    simp_rw [h, Finset.mul_sum]
    rw [sum_Ici_sum_Ici s (fun u t => mu 𝕜 s t * f u)]
    simp_rw [← Finset.sum_mul, sum_Icc_mu_right]
    rw [Finset.sum_eq_single s (fun u _ hu => by simp [Ne.symm hu]) (by simp)]
    simp
  · intro h s
    simp_rw [h]
    rw [sum_Ici_sum_Ici s (fun u t => mu 𝕜 t u * g u)]
    simp_rw [← Finset.sum_mul, sum_Icc_mu_left]
    rw [Finset.sum_eq_single s (fun u _ hu => by simp [Ne.symm hu]) (by simp)]
    simp

end Inversion

/-- **Product theorem for the Möbius function.** For locally finite posets `P` and `Q` and
elements of `P × Q`, `μ_{P × Q}((s, t), (s', t')) = μ_P(s, s') μ_Q(t, t')` (Stanley,
*Enumerative Combinatorics*, vol. 1, 2nd ed., author's draft of 15 July 2011,
Proposition 3.8.2). This is the pointwise form of Mathlib's `IncidenceAlgebra.mu_prod_mu`; it
holds for all pairs, both sides vanishing unless `(s, t) ≤ (s', t')`. -/
theorem mu_prod_apply {𝕜 α β : Type*} [Ring 𝕜] [PartialOrder α] [PartialOrder β]
    [LocallyFiniteOrder α] [LocallyFiniteOrder β] [DecidableEq α] [DecidableEq β]
    [DecidableLE α] [DecidableLE β] (s s' : α) (t t' : β) :
    mu 𝕜 (s, t) (s', t') = mu 𝕜 s s' * mu 𝕜 t t' := by
  rw [← mu_prod_mu 𝕜 (α := α) (β := β), IncidenceAlgebra.prod_mk]

/-- **Möbius function of a Boolean algebra.** In the Boolean algebra of finite subsets of a type,
ordered by inclusion, `μ(S, T) = (-1)^{|T - S|}` whenever `S ⊆ T` (Stanley, *Enumerative
Combinatorics*, vol. 1, 2nd ed., author's draft of 15 July 2011, Example 3.8.3, there for the
Boolean algebra `B_n` of subsets of an `n`-element set). -/
theorem mu_finset_of_subset {𝕜 ι : Type*} [Ring 𝕜] [DecidableEq ι] {S T : Finset ι}
    (h : S ⊆ T) : mu 𝕜 S T = (-1) ^ (T \ S).card := by
  induction T using Finset.strongInduction with
  | H T ih =>
    rcases eq_or_ne S T with rfl | hne
    · simp
    rw [mu_eq_neg_sum_Ico_of_ne hne]
    have hsum : ∑ U ∈ Ico S T, mu 𝕜 S U = ∑ U ∈ Ico S T, ((-1 : 𝕜) ^ (U \ S).card) :=
      Finset.sum_congr rfl fun U hU => by
        rw [mem_Ico] at hU
        exact ih U hU.2 hU.1
    rw [hsum]
    -- `∑_{S ⊆ U ⊆ T} (-1)^{|U - S|} = 0` because `S ≠ T`.
    have hfull : ∑ U ∈ Icc S T, ((-1 : 𝕜) ^ (U \ S).card) = 0 := by
      have himage : Icc S T = (T \ S).powerset.image (· ∪ S) := by
        ext U
        simp only [mem_Icc, mem_image, mem_powerset]
        constructor
        · rintro ⟨hSU, hUT⟩
          exact ⟨U \ S, sdiff_subset_sdiff hUT le_rfl, sdiff_union_of_subset hSU⟩
        · rintro ⟨V, hV, rfl⟩
          exact ⟨subset_union_right, union_subset (hV.trans sdiff_subset) h⟩
      rw [himage, sum_image]
      · have : ∀ V ∈ (T \ S).powerset, ((-1 : 𝕜) ^ ((V ∪ S) \ S).card) = (-1) ^ V.card := by
          intro V hV
          rw [mem_powerset] at hV
          rw [union_sdiff_right, sdiff_eq_self_of_disjoint]
          exact disjoint_of_subset_left hV disjoint_sdiff_self_left
        rw [sum_congr rfl this]
        have hne' : (T \ S).Nonempty := by
          rw [nonempty_iff_ne_empty]
          intro he
          exact hne (le_antisymm h (sdiff_eq_empty_iff_subset.mp he))
        have hcast : ∑ V ∈ (T \ S).powerset, ((-1 : 𝕜) ^ V.card) =
            ((∑ V ∈ (T \ S).powerset, (-1 : ℤ) ^ V.card : ℤ) : 𝕜) := by
          push_cast; rfl
        rw [hcast, sum_powerset_neg_one_pow_card_of_nonempty hne', Int.cast_zero]
      · intro V hV W hW hVW
        simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset] at hV hW
        have hV' : Disjoint V S := disjoint_of_subset_left hV disjoint_sdiff_self_left
        have hW' : Disjoint W S := disjoint_of_subset_left hW disjoint_sdiff_self_left
        have := congrArg (· \ S) hVW
        simpa [union_sdiff_right, sdiff_eq_self_of_disjoint hV',
          sdiff_eq_self_of_disjoint hW'] using this
    rw [← sum_Ico_add_eq_sum_Icc h] at hfull
    exact neg_eq_of_add_eq_zero_right hfull

end MathlibExt.Order.IncidenceAlgebra.MoebiusInversion
