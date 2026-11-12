/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Algebra.BigOperators.Field
import MathlibExt.Analysis.Convex.BrouwerFixedPoint

/-!
# Existence of competitive equilibrium in an exchange economy

An exchange economy in demand form has finitely many consumers and goods, endowments, and
demand functions of normalized prices. If every demand is continuous on the closed price simplex
and exhausts the consumer's budget there, a normalized competitive equilibrium with free disposal
exists: no good is in excess demand, and every good in excess supply has price zero
(Gale–Nikaido–Debreu). If moreover every good is in strict excess demand when its price is zero,
some strictly positive price vector clears every market exactly.

The theorems hold for any such demand-form data: endowments and demands are real vectors, and
nonnegativity of bundles is neither assumed nor needed. A pure exchange economy with nonnegative
endowments and demands is the special case.

Demand is taken as given. Deriving it from preferences, production, and the open-simplex
boundary condition of Mas-Colell–Whinston–Green, Proposition 17.C.1, are out of scope.
The `_of_brouwer` theorems take Brouwer's theorem on the price simplex as a hypothesis; the
unconditional versions discharge it with `BrouwerFixedPoint.exists_fixedPoint`.

`priceSimplex_eq_range_weights` identifies the price simplex with the weight vectors of Mathlib's
`Convexity.StdSimplex ℝ L`.

## Main results

* `ExchangeEconomy.exists_isFreeDisposalEquilibrium`: free-disposal equilibrium exists.
* `ExchangeEconomy.exists_excessDemand_eq_zero`: market clearing at strictly positive prices
  under boundary desirability.

## References

* D. Gale, *The law of supply and demand*, Math. Scand. 3 (1955), 155–169.
* H. Nikaido, *On the classical multilateral exchange problem*, Metroeconomica 8 (1956), 135–145.
* G. Debreu, *Market equilibrium*, Proc. Natl. Acad. Sci. USA 42 (1956), 876–878.
* A. Mas-Colell, M. D. Whinston, J. R. Green, *Microeconomic Theory*, Oxford University Press
  (1995), Sections 17.B–17.C.
-/

@[expose] public section

namespace MathlibExt.Economics.ExchangeEquilibriumExistence

/-- Normalized prices: the price simplex `{p | p ≥ 0, ∑ l, p l = 1}`, on which demands and
equilibria are considered. -/
def priceSimplex (L : Type*) [Fintype L] : Set (L → ℝ) :=
  {p | (∀ l, 0 ≤ p l) ∧ ∑ l, p l = 1}

/-- An exchange economy in demand form: consumers `I`, goods `L`, consumer `i` owns the
endowment `endowment i` and demands the bundle `demand i p` at prices `p`. Bundles are arbitrary
real vectors: nonnegativity is not imposed, and the existence theorems below do not need it. A
pure exchange economy with nonnegative endowments and demands is the special case. -/
structure ExchangeEconomy (I L : Type*) where
  /-- `endowment i` is consumer `i`'s initial bundle. -/
  endowment : I → L → ℝ
  /-- `demand i p` is consumer `i`'s demanded bundle at prices `p`. -/
  demand : I → (L → ℝ) → L → ℝ

namespace ExchangeEconomy

/-- Aggregate excess demand `z(p) = ∑ i, (demand i p - endowment i)`. -/
def excessDemand {I L : Type*} [Fintype I] (E : ExchangeEconomy I L) (p : L → ℝ) : L → ℝ :=
  ∑ i, (E.demand i p - E.endowment i)

/-- A normalized competitive equilibrium with free disposal: normalized prices at which no good
is in excess demand, and every good in excess supply is free. -/
def IsFreeDisposalEquilibrium {I L : Type*} [Fintype I] [Fintype L] (E : ExchangeEconomy I L)
    (p : L → ℝ) : Prop :=
  p ∈ priceSimplex L ∧ (∀ l, E.excessDemand p l ≤ 0) ∧ ∀ l, E.excessDemand p l < 0 → p l = 0

/-- Existence of a normalized competitive equilibrium with free disposal (Gale–Nikaido–Debreu),
derived from Brouwer's theorem on the price simplex: if every consumer's demand is continuous on
the price simplex and exhausts the consumer's budget there (`p · demand i p = p · endowment i`),
an equilibrium exists. -/
theorem exists_isFreeDisposalEquilibrium_of_brouwer {I L : Type*} [Fintype I] [Fintype L]
    [Nonempty L]
    (hB : ∀ g : (L → ℝ) → (L → ℝ), ContinuousOn g (priceSimplex L) →
      Set.MapsTo g (priceSimplex L) (priceSimplex L) → ∃ p ∈ priceSimplex L, g p = p)
    (E : ExchangeEconomy I L) (hcont : ∀ i, ContinuousOn (E.demand i) (priceSimplex L))
    (hbudget : ∀ i, ∀ p ∈ priceSimplex L,
      ∑ l, p l * E.demand i p l = ∑ l, p l * E.endowment i l) :
    ∃ p, E.IsFreeDisposalEquilibrium p := by
  -- Aggregate excess demand is continuous on the simplex.
  have hz_cont : ContinuousOn E.excessDemand (priceSimplex L) := by
    unfold ExchangeEconomy.excessDemand
    apply continuousOn_finsetSum Finset.univ
    intro i _
    exact (hcont i).sub continuousOn_const
  -- Total positive excess demand.
  set S : (L → ℝ) → ℝ := fun p => ∑ k, max 0 (E.excessDemand p k) with hS_def
  have hS_nonneg : ∀ p, 0 ≤ S p := by
    intro p
    simp only [hS_def]
    apply Finset.sum_nonneg
    intro k _
    exact le_max_left _ _
  have hS_cont : ContinuousOn S (priceSimplex L) := by
    simp only [hS_def]
    apply continuousOn_finsetSum Finset.univ
    intro k _
    have hz_k : ContinuousOn (fun p : L → ℝ => E.excessDemand p k) (priceSimplex L) :=
      (continuous_apply k).comp_continuousOn hz_cont
    have hprod : ContinuousOn (fun p : L → ℝ => ((0 : ℝ), E.excessDemand p k))
        (priceSimplex L) :=
      continuousOn_const.prodMk hz_k
    exact continuous_max.comp_continuousOn hprod
  -- Gale–Nikaido–Debreu map.
  set g : (L → ℝ) → (L → ℝ) :=
    fun p l => (p l + max 0 (E.excessDemand p l)) / (1 + S p) with hg_def
  have hg_cont : ContinuousOn g (priceSimplex L) := by
    rw [continuousOn_pi]
    intro l
    simp only [hg_def]
    apply ContinuousOn.div₀
    · have hz_k : ContinuousOn (fun p : L → ℝ => E.excessDemand p l)
          (priceSimplex L) :=
        (continuous_apply l).comp_continuousOn hz_cont
      have hprod : ContinuousOn (fun p : L → ℝ => ((0 : ℝ), E.excessDemand p l))
          (priceSimplex L) :=
        continuousOn_const.prodMk hz_k
      have hmax : ContinuousOn (fun p : L → ℝ => max 0 (E.excessDemand p l))
          (priceSimplex L) :=
        continuous_max.comp_continuousOn hprod
      exact (continuousOn_apply l _).add hmax
    · exact continuousOn_const.add hS_cont
    · intro p hp
      have hpos : (0 : ℝ) < 1 + S p := by
        have h0 := hS_nonneg p
        linarith
      exact ne_of_gt hpos
  have hg_maps : Set.MapsTo g (priceSimplex L) (priceSimplex L) := by
    intro p hp
    obtain ⟨h0, h1⟩ := hp
    have hD_pos : (0 : ℝ) < 1 + S p := by
      have hS := hS_nonneg p
      linarith
    have hD_ne : 1 + S p ≠ 0 := ne_of_gt hD_pos
    constructor
    · intro l
      simp only [hg_def]
      apply div_nonneg
      · exact add_nonneg (h0 l) (le_max_left _ _)
      · linarith [hS_nonneg p]
    · simp only [hg_def]
      calc ∑ l, (p l + max 0 (E.excessDemand p l)) / (1 + S p)
          = (∑ l, (p l + max 0 (E.excessDemand p l))) / (1 + S p) := by
            exact (Finset.sum_div Finset.univ _ _).symm
        _ = (1 + S p) / (1 + S p) := by
            congr 1
            rw [Finset.sum_add_distrib, h1]
        _ = 1 := div_self hD_ne
  obtain ⟨p, hp_mem, hfixed⟩ := hB g hg_cont hg_maps
  have hwalras : ∑ l, p l * E.excessDemand p l = 0 := by
    have hexpand : ∀ l, E.excessDemand p l
        = ∑ i, (E.demand i p l - E.endowment i l) := by
      intro l
      simp [ExchangeEconomy.excessDemand]
    have hexpand2 : ∀ l, p l * E.excessDemand p l
        = ∑ i, p l * (E.demand i p l - E.endowment i l) := by
      intro l
      rw [hexpand l, Finset.mul_sum]
    have hsplit : ∀ i, (∑ l, p l * (E.demand i p l - E.endowment i l))
        = (∑ l, p l * E.demand i p l) - (∑ l, p l * E.endowment i l) := by
      intro i
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro l _
      rw [mul_sub]
    calc ∑ l, p l * E.excessDemand p l
        = ∑ l, ∑ i, p l * (E.demand i p l - E.endowment i l) :=
          Finset.sum_congr rfl (fun l _ => hexpand2 l)
      _ = ∑ i, ∑ l, p l * (E.demand i p l - E.endowment i l) := Finset.sum_comm
      _ = ∑ i, ((∑ l, p l * E.demand i p l)
          - (∑ l, p l * E.endowment i l)) :=
          Finset.sum_congr rfl (fun i _ => hsplit i)
      _ = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          exact sub_eq_zero_of_eq (hbudget i p hp_mem)
  have hz_le : ∀ l, E.excessDemand p l ≤ 0 := by
    have hfix : ∀ l, (p l + max 0 (E.excessDemand p l)) / (1 + S p) = p l := by
      intro l
      have h := congrFun hfixed l
      simpa [hg_def] using h
    have hD_pos : (0 : ℝ) < 1 + S p := by
      have hS := hS_nonneg p
      linarith
    have hD_ne : 1 + S p ≠ 0 := ne_of_gt hD_pos
    have hkey : ∀ l, p l * S p = max 0 (E.excessDemand p l) := by
      intro l
      have h := hfix l
      have hmul : p l + max 0 (E.excessDemand p l) = p l * (1 + S p) :=
        (div_eq_iff hD_ne).mp h
      have hring : p l * (1 + S p) = p l + p l * S p := by ring
      rw [hring] at hmul
      exact (add_left_cancel_iff.mp hmul).symm
    have hmax_mul : ∀ l, max 0 (E.excessDemand p l) * E.excessDemand p l
        = (max 0 (E.excessDemand p l)) ^ 2 := by
      intro l
      by_cases h : E.excessDemand p l ≤ 0
      · rw [max_eq_left h]
        simp
      · push Not at h
        rw [max_eq_right (le_of_lt h)]
        ring
    have hsum_sq : ∑ l, (max 0 (E.excessDemand p l)) ^ 2 = 0 := by
      calc ∑ l, (max 0 (E.excessDemand p l)) ^ 2
          = ∑ l, max 0 (E.excessDemand p l) * E.excessDemand p l :=
            Finset.sum_congr rfl (fun l _ => (hmax_mul l).symm)
        _ = ∑ l, S p * (p l * E.excessDemand p l) := by
            apply Finset.sum_congr rfl
            intro l _
            have hk := hkey l
            rw [← hk]
            ring
        _ = S p * ∑ l, p l * E.excessDemand p l := by
            rw [Finset.mul_sum]
        _ = S p * 0 := by rw [hwalras]
        _ = 0 := mul_zero _
    have hmax_zero : ∀ l, max 0 (E.excessDemand p l) = 0 := by
      have hnonneg : ∀ l ∈ Finset.univ,
          (0 : ℝ) ≤ (max 0 (E.excessDemand p l)) ^ 2 := by
        intro l _
        exact sq_nonneg _
      have hall_zero : ∀ l ∈ Finset.univ,
          (max 0 (E.excessDemand p l)) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum_sq
      intro l
      have h0 := hall_zero l (Finset.mem_univ l)
      exact sq_eq_zero_iff.mp h0
    intro l
    have h0 := hmax_zero l
    have hle : E.excessDemand p l ≤ max 0 (E.excessDemand p l) :=
      le_max_right _ _
    rw [h0] at hle
    exact hle
  have hslack : ∀ l, E.excessDemand p l < 0 → p l = 0 := by
    intro l hlt
    have hnonpos : ∀ k ∈ Finset.univ, p k * E.excessDemand p k ≤ 0 := by
      intro k _
      apply mul_nonpos_of_nonneg_of_nonpos
      · exact hp_mem.1 k
      · exact hz_le k
    have hall_zero : ∀ k ∈ Finset.univ, p k * E.excessDemand p k = 0 :=
      (Finset.sum_eq_zero_iff_of_nonpos hnonpos).mp hwalras
    have h0 := hall_zero l (Finset.mem_univ l)
    have hzne : E.excessDemand p l ≠ 0 := ne_of_lt hlt
    rcases mul_eq_zero.mp h0 with h | h
    · exact h
    · contradiction
  exact ⟨p, hp_mem, hz_le, hslack⟩

/-- Existence of a market-clearing equilibrium at strictly positive prices: under the hypotheses
of `exists_isFreeDisposalEquilibrium_of_brouwer`, if moreover every good is in strict excess
demand whenever its normalized price is zero, some strictly positive normalized price vector
clears all markets exactly. -/
theorem exists_excessDemand_eq_zero_of_brouwer {I L : Type*} [Fintype I] [Fintype L]
    [Nonempty L]
    (hB : ∀ g : (L → ℝ) → (L → ℝ), ContinuousOn g (priceSimplex L) →
      Set.MapsTo g (priceSimplex L) (priceSimplex L) → ∃ p ∈ priceSimplex L, g p = p)
    (E : ExchangeEconomy I L) (hcont : ∀ i, ContinuousOn (E.demand i) (priceSimplex L))
    (hbudget : ∀ i, ∀ p ∈ priceSimplex L,
      ∑ l, p l * E.demand i p l = ∑ l, p l * E.endowment i l)
    (hdes : ∀ p ∈ priceSimplex L, ∀ l, p l = 0 → 0 < E.excessDemand p l) :
    ∃ p ∈ priceSimplex L, (∀ l, 0 < p l) ∧ E.excessDemand p = 0 := by
  obtain ⟨p, hp_mem, hz_le, hslack⟩ :=
    exists_isFreeDisposalEquilibrium_of_brouwer hB E hcont hbudget
  have hpos : ∀ l, 0 < p l := by
    intro l
    have h0 : 0 ≤ p l := hp_mem.1 l
    by_contra h
    push Not at h
    have heq : p l = 0 := le_antisymm h h0
    have hlt := hdes p hp_mem l heq
    have hle := hz_le l
    linarith
  have hz_eq : E.excessDemand p = 0 := by
    funext l
    simp only [Pi.zero_apply]
    have h_not_lt : ¬ E.excessDemand p l < 0 := by
      intro hlt
      have h0eq := hslack l hlt
      have hplt := hpos l
      linarith
    have h_ge : 0 ≤ E.excessDemand p l := le_of_not_gt h_not_lt
    exact le_antisymm (hz_le l) h_ge
  exact ⟨p, hp_mem, hpos, hz_eq⟩

end ExchangeEconomy

/-- The price simplex is exactly the set of weight vectors of Mathlib's standard simplex
`Convexity.StdSimplex ℝ L`. -/
theorem priceSimplex_eq_range_weights (L : Type*) [Fintype L] :
    priceSimplex L = Set.range (fun t : Convexity.StdSimplex ℝ L => (t.weights : L → ℝ)) := by
  rw [Convexity.StdSimplex.range_toFun_comp_weights]
  ext s
  simp [priceSimplex]

/-- The price simplex is compact. -/
theorem isCompact_priceSimplex (L : Type*) [Fintype L] : IsCompact (priceSimplex L) := by
  rw [priceSimplex_eq_range_weights]
  exact isCompact_range (continuous_pi fun l => Convexity.StdSimplex.continuous_weights_apply ℝ l)

/-- The price simplex is convex. -/
theorem convex_priceSimplex (L : Type*) [Fintype L] : Convex ℝ (priceSimplex L) := by
  rw [priceSimplex_eq_range_weights]
  exact Convexity.ConvexSpace.AffineMap.convex_range
    (Convexity.ConvexSpace.AffineMap.mk _
      ((Convexity.IsAffineMap.linearMap (Finsupp.lcoeFun (R := ℝ) (M := ℝ) (α := L))).comp
        (Convexity.StdSimplex.isAffineMap_weights ℝ L)))

/-- The price simplex is nonempty when there is at least one good. -/
theorem priceSimplex_nonempty (L : Type*) [Fintype L] [Nonempty L] :
    (priceSimplex L).Nonempty := by
  rw [priceSimplex_eq_range_weights]
  exact Set.range_nonempty _

end MathlibExt.Economics.ExchangeEquilibriumExistence

namespace MathlibExt.Economics.ExchangeEquilibriumExistence.ExchangeEconomy

/-- Existence of a normalized competitive equilibrium with free disposal (Gale–Nikaido–Debreu):
if every consumer's demand is continuous on the price simplex and exhausts the consumer's
budget there, an equilibrium exists. -/
theorem exists_isFreeDisposalEquilibrium {I L : Type*} [Fintype I] [Fintype L]
    [Nonempty L]
    (E : ExchangeEconomy I L) (hcont : ∀ i, ContinuousOn (E.demand i) (priceSimplex L))
    (hbudget : ∀ i, ∀ p ∈ priceSimplex L,
      ∑ l, p l * E.demand i p l = ∑ l, p l * E.endowment i l) :
    ∃ p, E.IsFreeDisposalEquilibrium p := by
  have hB : ∀ g : (L → ℝ) → (L → ℝ), ContinuousOn g (priceSimplex L) →
      Set.MapsTo g (priceSimplex L) (priceSimplex L) → ∃ p ∈ priceSimplex L, g p = p := by
    intro g hg_cont hg_maps
    exact MathlibExt.Analysis.Convex.BrouwerFixedPoint.exists_fixedPoint
      (isCompact_priceSimplex L) (convex_priceSimplex L) (priceSimplex_nonempty L)
      hg_cont hg_maps
  exact exists_isFreeDisposalEquilibrium_of_brouwer hB E hcont hbudget

/-- Existence of a market-clearing equilibrium at strictly positive prices: under the hypotheses
of `exists_isFreeDisposalEquilibrium`, if moreover every good is in strict excess demand
whenever its normalized price is zero, some strictly positive normalized price vector clears
all markets exactly. -/
theorem exists_excessDemand_eq_zero {I L : Type*} [Fintype I] [Fintype L]
    [Nonempty L]
    (E : ExchangeEconomy I L) (hcont : ∀ i, ContinuousOn (E.demand i) (priceSimplex L))
    (hbudget : ∀ i, ∀ p ∈ priceSimplex L,
      ∑ l, p l * E.demand i p l = ∑ l, p l * E.endowment i l)
    (hdes : ∀ p ∈ priceSimplex L, ∀ l, p l = 0 → 0 < E.excessDemand p l) :
    ∃ p ∈ priceSimplex L, (∀ l, 0 < p l) ∧ E.excessDemand p = 0 := by
  have hB : ∀ g : (L → ℝ) → (L → ℝ), ContinuousOn g (priceSimplex L) →
      Set.MapsTo g (priceSimplex L) (priceSimplex L) → ∃ p ∈ priceSimplex L, g p = p := by
    intro g hg_cont hg_maps
    exact MathlibExt.Analysis.Convex.BrouwerFixedPoint.exists_fixedPoint
      (isCompact_priceSimplex L) (convex_priceSimplex L) (priceSimplex_nonempty L)
      hg_cont hg_maps
  exact exists_excessDemand_eq_zero_of_brouwer hB E hcont hbudget hdes

end MathlibExt.Economics.ExchangeEquilibriumExistence.ExchangeEconomy
