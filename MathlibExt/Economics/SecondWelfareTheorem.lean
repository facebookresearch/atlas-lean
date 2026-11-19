/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Quasiconvex
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Topology.Order.Basic
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import MathlibExt.Economics.Consumer.LocalNonsatiation

/-!
# Second fundamental welfare theorem: supporting prices

Pure exchange economy with finitely many consumers `I` and goods `L`, consumption set `ℝ^L_+`
and utilities `u i`. A Pareto optimal allocation `x` with `∑ i, x i = ω` is supported by a
nonzero price vector `p` as a price quasi-equilibrium with transfers (wealth `p · x i`): any
nonnegative bundle strictly preferred to `x i` costs at least `p · x i`. This holds when every
`u i` is continuous, quasiconcave and locally nonsatiated on `ℝ^L_+`. A quasi-equilibrium is a
price equilibrium with transfers (each `x i` maximizes `u i` on its budget set) once every
consumer has a strictly cheaper nonnegative bundle; at zero wealth it need not be.

Continuity is assumed (stronger than Mas-Colell–Whinston–Green, Prop. 16.D.1) so that the
aggregate strictly-preferred set has nonempty interior and Mathlib's
`geometric_hahn_banach_of_nonempty_interior` applies. Nonnegativity of `p` is not claimed.

## Main results

* `exists_isQuasiEquilibriumWithTransfers`: second welfare theorem; a Pareto optimum is a price
  quasi-equilibrium with transfers (`p ≠ 0`, feasible, strictly preferred bundles cost at least
  as much).
* `isEquilibriumWithTransfers_of_cheaper`: a quasi-equilibrium in which every consumer has a
  strictly cheaper bundle is a price equilibrium with transfers (`p ≠ 0` is kept).
* `exists_isQuasiSupportingPrice`, `isBudgetOptimal_of_cheaper`: the same results stated with the
  consumer conditions `IsQuasiSupportingPrice` and `IsBudgetOptimal` alone.

## References

* A. Mas-Colell, M. D. Whinston, J. R. Green, *Microeconomic Theory*, Oxford University Press
  (1995), Section 16.D, Propositions 16.D.1 and 16.D.2.
* K. J. Arrow, *An extension of the basic theorems of classical welfare economics*, Proc. Second
  Berkeley Symposium (1951), 507–532.
-/

@[expose] public section

namespace MathlibExt.Economics.SecondWelfareTheorem

/-- The consumption set `ℝ^L_+` of nonnegative bundles (Mas-Colell–Whinston–Green §16.B). -/
def consumptionSet (L : Type*) : Set (L → ℝ) :=
  {z | ∀ l, 0 ≤ z l}

/-- The value `p · z = ∑ l, p l * z l` of the bundle `z` at prices `p`. -/
def value {L : Type*} [Fintype L] (p z : L → ℝ) : ℝ :=
  ∑ l, p l * z l

/-- An allocation `x` (consumer `i` receives `x i`) is feasible for the aggregate endowment `ω`
in a pure exchange economy: every bundle is nonnegative and the bundles add up to `ω`. -/
def IsFeasible {I L : Type*} [Fintype I] (ω : L → ℝ) (x : I → L → ℝ) : Prop :=
  (∀ i, x i ∈ consumptionSet L) ∧ ∑ i, x i = ω

/-- A feasible allocation is Pareto optimal (MWG Def. 16.B.3) if no feasible allocation makes
every consumer weakly better off and some consumer strictly better off, utilities `u i`. -/
def IsParetoOptimal {I L : Type*} [Fintype I] (u : I → (L → ℝ) → ℝ) (ω : L → ℝ)
    (x : I → L → ℝ) : Prop :=
  IsFeasible ω x ∧
    ¬ ∃ y : I → L → ℝ, IsFeasible ω y ∧ (∀ i, u i (x i) ≤ u i (y i)) ∧
      ∃ i, u i (x i) < u i (y i)

/-- Local nonsatiation on the consumption set (MWG Def. 3.B.3): arbitrarily close to every
nonnegative bundle there is a nonnegative bundle with strictly higher utility. This is
`MathlibExt.Economics.Consumer.LocallyNonsatiated` specialized to `X = consumptionSet L`. -/
abbrev LocallyNonsatiated {L : Type*} [Fintype L] (v : (L → ℝ) → ℝ) : Prop :=
  MathlibExt.Economics.Consumer.LocallyNonsatiated v (consumptionSet L)

/-- Consumer condition of a price quasi-equilibrium with transfers (MWG Def. 16.D.1 (ii)), the
wealth of consumer `i` being `value p (x i)`: every nonnegative bundle strictly preferred to `x i`
costs at least `value p (x i)`. It says nothing about `p ≠ 0` or feasibility; see
`IsQuasiEquilibriumWithTransfers`. -/
def IsQuasiSupportingPrice {I L : Type*} [Fintype L] (u : I → (L → ℝ) → ℝ)
    (p : L → ℝ) (x : I → L → ℝ) : Prop :=
  ∀ i, ∀ z ∈ consumptionSet L, u i (x i) < u i z → value p (x i) ≤ value p z

/-- Consumer condition of a price equilibrium with transfers (MWG Def. 16.B.4 (ii)), the wealth
of consumer `i` being `value p (x i)`: `x i` maximizes `u i` on its budget set. It says nothing
about feasibility; see `IsEquilibriumWithTransfers`. -/
def IsBudgetOptimal {I L : Type*} [Fintype L] (u : I → (L → ℝ) → ℝ)
    (p : L → ℝ) (x : I → L → ℝ) : Prop :=
  ∀ i, ∀ z ∈ consumptionSet L, value p z ≤ value p (x i) → u i z ≤ u i (x i)

private theorem consumptionSet_convex (L : Type*) :
    Convex ℝ (consumptionSet L) := by
  intro x hx y hy a b ha hb hab
  simp only [consumptionSet, Set.mem_ofPred] at hx hy ⊢
  intro l
  have h1 : ((a • x + b • y : L → ℝ)) l = a * x l + b * y l := by
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [h1]
  exact add_nonneg (mul_nonneg ha (hx l)) (mul_nonneg hb (hy l))

private theorem value_add {L : Type*} [Fintype L] (p a b : L → ℝ) :
    value p (a + b) = value p a + value p b := by
  unfold value
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [Pi.add_apply, mul_add]

private theorem value_smul {L : Type*} [Fintype L] (p : L → ℝ) (t : ℝ) (z : L → ℝ) :
    value p (t • z) = t * value p z := by
  unfold value
  have h : ∀ l : L, p l * (t • z) l = t * (p l * z l) := by
    intro l
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  simp only [h]
  rw [Finset.mul_sum]

private theorem value_sum {I L : Type*} [Fintype I] [Fintype L] (p : L → ℝ) (z : I → L → ℝ) :
    value p (∑ i, z i) = ∑ i, value p (z i) := by
  unfold value
  have h1 : ∀ l : L, p l * (∑ i, z i) l = ∑ i, p l * z i l := by
    intro l
    rw [Finset.sum_apply]
    rw [Finset.mul_sum]
  simp only [h1]
  rw [Finset.sum_comm]

private theorem value_continuous {L : Type*} [Fintype L] (p : L → ℝ) :
    Continuous (fun z : L → ℝ => value p z) := by
  unfold value
  exact continuous_finsetSum _ (fun l _ => continuous_const.mul (continuous_apply l))

-- Strictly positive bundles are open and inside the consumption set
private theorem posBundles_open (L : Type*) [Finite L] :
    IsOpen {z : L → ℝ | ∀ l, 0 < z l} := by
  have heq : {z : L → ℝ | ∀ l, 0 < z l} = ⋂ l, {z : L → ℝ | 0 < z l} := by
    ext z
    simp
  rw [heq]
  apply isOpen_iInter_of_finite
  intro l
  have : {z : L → ℝ | 0 < z l} = (fun z : L → ℝ => z l) ⁻¹' Set.Ioi 0 := by
    ext z
    simp
  rw [this]
  exact isOpen_Ioi.preimage (continuous_apply l)

private theorem posBundles_subset (L : Type*) :
    {z : L → ℝ | ∀ l, 0 < z l} ⊆ consumptionSet L := by
  intro z hz l
  exact le_of_lt (hz l)

private theorem mem_interior_consumptionSet_of_pos {L : Type*} [Finite L] {z : L → ℝ}
    (h : ∀ l, 0 < z l) : z ∈ interior (consumptionSet L) := by
  have hopen := posBundles_open L
  have hsub := posBundles_subset L
  have hmem : z ∈ {z : L → ℝ | ∀ l, 0 < z l} := h
  have hsub2 := interior_maximal hsub hopen
  exact hsub2 hmem

/-- Supporting prices for a Pareto optimum (MWG Prop. 16.D.1, exchange economy, with continuous
utilities): a Pareto optimal allocation of an exchange economy with continuous, quasiconcave,
locally nonsatiated utilities on `ℝ^L_+` has a nonzero price vector satisfying the
quasi-equilibrium consumer condition. -/
theorem exists_isQuasiSupportingPrice {I L : Type*} [Fintype I] [Fintype L]
    [Nonempty L] {u : I → (L → ℝ) → ℝ} {ω : L → ℝ} {x : I → L → ℝ}
    (hcont : ∀ i, ContinuousOn (u i) (consumptionSet L))
    (hqc : ∀ i, QuasiconcaveOn ℝ (consumptionSet L) (u i))
    (hlns : ∀ i, LocallyNonsatiated (u i))
    (hx : IsParetoOptimal u ω x) :
    ∃ p : L → ℝ, p ≠ 0 ∧ IsQuasiSupportingPrice u p x := by
  -- Unpack Pareto
  obtain ⟨hfeas, hpareto⟩ := hx
  obtain ⟨hxX, hsum⟩ := hfeas
  by_cases hI : Nonempty I
  · -- Nonempty case: main proof
    -- Preferred sets V i
    set V : I → Set (L → ℝ) := fun i => {z | z ∈ consumptionSet L ∧ u i (x i) < u i z} with hV_def
    have hVconv : ∀ i, Convex ℝ (V i) := fun i => (hqc i).convex_gt (u i (x i))
    have hVne : ∀ i, (V i).Nonempty := by
      intro i
      obtain ⟨z', hz'X, _, hutil⟩ := hlns i (x i) (hxX i) 1 one_pos
      exact ⟨z', hz'X, hutil⟩
    -- Aggregate set W (Minkowski sum)
    set W : Set (L → ℝ) :=
      {w | ∃ z : I → L → ℝ, (∀ i, z i ∈ V i) ∧ ∑ i, z i = w} with hW_def
    have hWconv : Convex ℝ W := by
      intro w₁ hw₁ w₂ hw₂ a b ha hb hab
      obtain ⟨z₁, hz₁V, hw₁eq⟩ := hw₁
      obtain ⟨z₂, hz₂V, hw₂eq⟩ := hw₂
      refine ⟨fun i => a • z₁ i + b • z₂ i, fun i => hVconv i (hz₁V i) (hz₂V i) ha hb hab, ?_⟩
      have hsum : (∑ i, (a • z₁ i + b • z₂ i)) = a • w₁ + b • w₂ := by
        rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, ← hw₁eq, ← hw₂eq]
      exact hsum
    have hωnW : ω ∉ W := by
      rintro ⟨z, hzV, hsumz⟩
      apply hpareto
      refine ⟨z, ⟨fun i => (hzV i).1, hsumz⟩, fun i => le_of_lt (hzV i).2, ?_⟩
      obtain ⟨i₀⟩ := hI
      exact ⟨i₀, (hzV i₀).2⟩
    -- Each V i has nonempty interior
    have hVint : ∀ i, (interior (V i)).Nonempty := by
      intro i
      obtain ⟨z₀, hz₀X, hutil₀⟩ := hVne i
      -- continuity at z₀ gives δ₀ keeping utility above u i (x i)
      have hwithin₀ : ContinuousWithinAt (u i) (consumptionSet L) z₀ :=
        (hcont i).continuousWithinAt hz₀X
      have hgap₀ : (0 : ℝ) < u i z₀ - u i (x i) := sub_pos.mpr hutil₀
      obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := (Metric.continuousWithinAt_iff.mp hwithin₀)
        ((u i z₀ - u i (x i)) / 2) (by linarith)
      have hutil_close₀ : ∀ w ∈ consumptionSet L, dist w z₀ < δ₀ → u i (x i) < u i w := by
        intro w hwX hdist
        have hclose := hδ₀ hwX hdist
        rw [Real.dist_eq] at hclose
        have habs := abs_lt.mp hclose
        linarith
      -- path y δ = z₀ + δ • 1, continuous, y 0 = z₀
      set y : ℝ → (L → ℝ) := fun δ => z₀ + δ • 1 with hy_def
      have hy_cont : Continuous y := by
        unfold y
        exact continuous_const.add (continuous_id.smul continuous_const)
      have hy0 : y 0 = z₀ := by simp [y]
      obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := (Metric.continuousAt_iff.mp hy_cont.continuousAt) δ₀ hδ₀pos
      set δstar : ℝ := min (δ₁ / 2) (1 / 2) with hδstar_def
      have hδstar_pos : (0 : ℝ) < δstar := lt_min_iff.mpr ⟨by linarith, by norm_num⟩
      have hδstar_lt : dist δstar (0 : ℝ) < δ₁ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hδstar_pos]
        have : δstar ≤ δ₁ / 2 := by rw [hδstar_def]; exact min_le_left _ _
        linarith
      have hdist_star : dist (y δstar) z₀ < δ₀ := by
        have := hδ₁ hδstar_lt
        rwa [hy0] at this
      -- y* has all coordinates strictly positive
      have hy_pos : ∀ l, 0 < (y δstar) l := by
        intro l
        have hyl : (y δstar) l = z₀ l + δstar := by
          simp [y, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
        rw [hyl]
        have hz0 := hz₀X l
        linarith
      have hyX : y δstar ∈ consumptionSet L := fun l => le_of_lt (hy_pos l)
      have hutil_star : u i (x i) < u i (y δstar) := hutil_close₀ _ hyX hdist_star
      have hy_interior_X : y δstar ∈ interior (consumptionSet L) :=
        mem_interior_consumptionSet_of_pos hy_pos
      -- ball inside X
      have hX_nhds : consumptionSet L ∈ nhds (y δstar) :=
        mem_interior_iff_mem_nhds.mp hy_interior_X
      obtain ⟨r₁, hr₁pos, hr₁sub⟩ := Metric.mem_nhds_iff.mp hX_nhds
      -- continuity at y* gives r₂ keeping utility above
      have hwithin_star : ContinuousWithinAt (u i) (consumptionSet L) (y δstar) :=
        (hcont i).continuousWithinAt hyX
      have hgap_star : (0 : ℝ) < u i (y δstar) - u i (x i) := sub_pos.mpr hutil_star
      obtain ⟨r₂, hr₂pos, hr₂⟩ := (Metric.continuousWithinAt_iff.mp hwithin_star)
        ((u i (y δstar) - u i (x i)) / 2) (by linarith)
      have hutil_close_star :
          ∀ w ∈ consumptionSet L, dist w (y δstar) < r₂ → u i (x i) < u i w := by
        intro w hwX hdist
        have hclose := hr₂ hwX hdist
        rw [Real.dist_eq] at hclose
        have habs := abs_lt.mp hclose
        linarith
      set r : ℝ := min r₁ r₂ with hr_def
      have hr_pos : (0 : ℝ) < r := lt_min_iff.mpr ⟨hr₁pos, hr₂pos⟩
      have hball_sub : Metric.ball (y δstar) r ⊆ V i := by
        intro w hw
        rw [Metric.mem_ball] at hw
        have hr_le1 : r ≤ r₁ := min_le_left _ _
        have hr_le2 : r ≤ r₂ := min_le_right _ _
        have hw1 : dist w (y δstar) < r₁ := lt_of_lt_of_le hw hr_le1
        have hw2 : dist w (y δstar) < r₂ := lt_of_lt_of_le hw hr_le2
        have hw_ball1 : w ∈ Metric.ball (y δstar) r₁ := Metric.mem_ball.mpr hw1
        have hwX : w ∈ consumptionSet L := hr₁sub hw_ball1
        exact ⟨hwX, hutil_close_star w hwX hw2⟩
      have hball_open : IsOpen (Metric.ball (y δstar) r) := Metric.isOpen_ball
      have hball_interior := interior_maximal hball_sub hball_open
      have hmem : y δstar ∈ Metric.ball (y δstar) r := Metric.mem_ball_self hr_pos
      exact ⟨y δstar, hball_interior hmem⟩
    -- Lift to interior W nonempty via translation
    have hWint : (interior W).Nonempty := by
      classical
      obtain ⟨i₀⟩ := hI
      choose c hc using hVne
      set C : L → ℝ := ∑ j ∈ Finset.univ.erase i₀, c j with hC_def
      obtain ⟨y₀, hy₀mem⟩ := hVint i₀
      have hnhds := mem_interior_iff_mem_nhds.mp hy₀mem
      obtain ⟨r, hrpos, hrsub⟩ := Metric.mem_nhds_iff.mp hnhds
      have hballW : Metric.ball (y₀ + C) r ⊆ W := by
        intro w hw
        rw [Metric.mem_ball] at hw
        -- y = w - C is in ball y₀ r
        have hdist_eq : dist (w - C) y₀ = dist w (y₀ + C) := by
          rw [dist_eq_norm, dist_eq_norm]
          congr 1
          abel
        have hy_mem : w - C ∈ Metric.ball y₀ r := by
          rw [Metric.mem_ball, hdist_eq]
          exact hw
        have hyV : w - C ∈ V i₀ := hrsub hy_mem
        -- allocation: update c at i₀ with w - C
        set z : I → L → ℝ := Function.update c i₀ (w - C) with hz_def
        have hzV : ∀ j, z j ∈ V j := by
          intro j
          by_cases hj : j = i₀
          · subst hj
            rw [hz_def]
            rw [Function.update_self]
            exact hyV
          · rw [hz_def]
            rw [Function.update_of_ne hj]
            exact hc j
        have hsumz : ∑ j, z j = w := by
          have hadd := Finset.add_sum_erase Finset.univ z (Finset.mem_univ i₀)
          have hz_i0 : z i₀ = w - C := by
            rw [hz_def, Function.update_self]
          have hrest : ∑ x ∈ Finset.univ.erase i₀, z x = C := by
            apply Finset.sum_congr rfl
            intro j hj
            have hjne : j ≠ i₀ := Finset.ne_of_mem_erase hj
            rw [hz_def, Function.update_of_ne hjne]
          rw [hz_i0, hrest] at hadd
          have hsub : (w - C) + C = w := sub_add_cancel w C
          -- hadd : (w - C) + C = ∑ j, z j? Actually hadd : z i₀ + ∑ erase = ∑ univ
          -- So ∑ univ = w via hsub
          have : ∑ x ∈ Finset.univ, z x = w := by
            rw [← hadd, hsub]
          simpa using this
        exact ⟨z, hzV, hsumz⟩
      have hopen : IsOpen (Metric.ball (y₀ + C) r) := Metric.isOpen_ball
      have hsub := interior_maximal hballW hopen
      have hmem : y₀ + C ∈ Metric.ball (y₀ + C) r := Metric.mem_ball_self hrpos
      exact ⟨y₀ + C, hsub hmem⟩
    -- Separation
    have hSingle : Convex ℝ ({ω} : Set (L → ℝ)) := convex_singleton ω
    have hDisj : Disjoint (interior W) ({ω} : Set (L → ℝ)) := by
      rw [Set.disjoint_left]
      rintro x hx hmem
      have hxW : x ∈ W := interior_subset hx
      have hxeq : x = ω := Set.mem_singleton_iff.mp hmem
      rw [hxeq] at hxW
      exact hωnW hxW
    have hSingNe : ({ω} : Set (L → ℝ)).Nonempty := ⟨ω, rfl⟩
    obtain ⟨f, ub, hfne, hfle, hge⟩ :=
      geometric_hahn_banach_of_nonempty_interior hWconv hSingle hDisj hWint hSingNe
    have hub_le : ub ≤ f ω := hge ω rfl
    -- Price vector from f
    classical
    set p : L → ℝ := fun l => -(f (Pi.single l 1)) with hp_def
    -- Representation of any bundle as sum of singles
    have hrepr : ∀ z : L → ℝ, z = ∑ l, z l • Pi.single l (1 : ℝ) := by
      intro z
      ext l'
      have hsum_apply : (∑ l, z l • Pi.single l (1 : ℝ)) l' =
          ∑ l ∈ Finset.univ, (z l • Pi.single l (1 : ℝ)) l' := by
        rw [Finset.sum_apply]
      rw [hsum_apply]
      have hterm : ∀ l : L, (z l • Pi.single l (1 : ℝ)) l' = (if l' = l then z l else 0) := by
        intro l
        rw [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
        by_cases h : l' = l
        · simp [h]
        · simp [h]
      simp only [hterm]
      rw [Finset.sum_ite_eq]
      simp
    have hfz : ∀ z : L → ℝ, f z = ∑ l, z l * f (Pi.single l (1 : ℝ)) := by
      intro z
      conv_lhs => rw [hrepr z]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [map_smul, smul_eq_mul]
    have hval_eq : ∀ z : L → ℝ, value p z = -(f z) := by
      intro z
      unfold value
      rw [hfz z]
      have hterm : ∀ l : L, p l * z l = -(z l * f (Pi.single l (1 : ℝ))) := by
        intro l
        rw [hp_def]
        simp only
        ring
      simp only [hterm]
      rw [Finset.sum_neg_distrib]
    have hpne : p ≠ 0 := by
      intro h0
      apply hfne
      apply ContinuousLinearMap.ext
      intro z
      have hall0 : ∀ l : L, f (Pi.single l (1 : ℝ)) = 0 := by
        intro l
        have : p l = (0 : L → ℝ) l := by rw [h0]
        simpa [hp_def] using this
      rw [hfz z]
      simp [hall0]
    -- Aggregate inequality
    have hagg : ∀ w ∈ W, value p ω ≤ value p w := by
      intro w hw
      have h1 := hfle w hw
      have h2 : f w ≤ f ω := le_trans h1 hub_le
      rw [hval_eq w, hval_eq ω]
      exact neg_le_neg h2
    have hωeq : value p ω = ∑ i, value p (x i) := by
      rw [← hsum, value_sum]
    have hsum_ineq : ∀ z : I → L → ℝ, (∀ i, z i ∈ V i) →
        ∑ i, value p (x i) ≤ ∑ i, value p (z i) := by
      intro z hzV
      have hwW : (∑ i, z i) ∈ W := ⟨z, hzV, rfl⟩
      have hle := hagg _ hwW
      rw [hωeq, value_sum] at hle
      exact hle
    -- Individual support from aggregate inequality
    refine ⟨p, hpne, ?_⟩
    intro i z hzX hutil
    by_contra hnge
    have hlt : value p z < value p (x i) := lt_of_not_ge hnge
    set gap : ℝ := value p (x i) - value p z with hgap_def
    have hgap_pos : (0 : ℝ) < gap := sub_pos.mpr hlt
    have hnpos : 0 < Fintype.card I := Fintype.card_pos_iff.mpr hI
    have hnR_pos : (0 : ℝ) < (Fintype.card I : ℝ) := Nat.cast_pos.mpr hnpos
    set eps : ℝ := gap / (Fintype.card I : ℝ) with heps_def
    have heps_pos : (0 : ℝ) < eps := div_pos hgap_pos hnR_pos
    have hcont_val : Continuous (fun w : L → ℝ => value p w) := value_continuous p
    have hδ_ex : ∀ j : I, ∃ δ > 0, ∀ y, dist y (x j) < δ →
        dist (value p y) (value p (x j)) < eps := by
      intro j
      exact Metric.continuousAt_iff.mp hcont_val.continuousAt eps heps_pos
    have hEx : ∀ j : I, ∃ wj, wj ∈ V j ∧ (j = i → wj = z) ∧
        (j ≠ i → dist (value p wj) (value p (x j)) < eps) := by
      intro j
      by_cases hj : j = i
      · subst hj
        refine ⟨z, ⟨hzX, hutil⟩, fun _ => rfl, ?_⟩
        intro hne
        exact (hne rfl).elim
      · obtain ⟨δ, hδpos, hδ⟩ := hδ_ex j
        obtain ⟨wj, hwjX, hdist, hutilj⟩ := hlns j (x j) (hxX j) δ hδpos
        refine ⟨wj, ⟨hwjX, hutilj⟩, ?_, ?_⟩
        · intro heq
          exact (hj heq).elim
        · intro _
          exact hδ wj hdist
    choose w hw using hEx
    have hwV : ∀ j, w j ∈ V j := fun j => (hw j).1
    have hw_eq : ∀ j, j = i → w j = z := fun j => (hw j).2.1
    have hw_dist : ∀ j, j ≠ i → dist (value p (w j)) (value p (x j)) < eps := fun j => (hw j).2.2
    have hle_sum := hsum_ineq w hwV
    -- Show ∑ w < ∑ x for contradiction
    have hw_i : w i = z := hw_eq i rfl
    have hbound : ∀ j ∈ Finset.univ.erase i, value p (w j) < value p (x j) + eps := by
      intro j hj
      have hjne : j ≠ i := Finset.ne_of_mem_erase hj
      have hdist := hw_dist j hjne
      rw [Real.dist_eq] at hdist
      have habs := abs_lt.mp hdist
      linarith
    have hbound_le : ∀ j ∈ Finset.univ.erase i, value p (w j) ≤ value p (x j) + eps := by
      intro j hj
      exact le_of_lt (hbound j hj)
    have hsum_le : ∑ j ∈ Finset.univ.erase i, value p (w j) ≤
        ∑ j ∈ Finset.univ.erase i, (value p (x j) + eps) :=
      Finset.sum_le_sum hbound_le
    have hsum_rhs : ∑ j ∈ Finset.univ.erase i, (value p (x j) + eps)
        = (∑ j ∈ Finset.univ.erase i, value p (x j)) + (Finset.univ.erase i).card * eps := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_const, nsmul_eq_mul]
    have hcard_lt : ((Finset.univ.erase i).card : ℝ) < (Fintype.card I : ℝ) := by
      have hlt : (Finset.univ.erase i).card < Finset.univ.card :=
        Finset.card_erase_lt_of_mem (Finset.mem_univ i)
      rw [Finset.card_univ] at hlt
      exact Nat.cast_lt.mpr hlt
    have hcard_eps : ((Finset.univ.erase i).card : ℝ) * eps < gap := by
      have h1 : ((Finset.univ.erase i).card : ℝ) * eps < (Fintype.card I : ℝ) * eps :=
        mul_lt_mul_of_pos_right hcard_lt heps_pos
      have h2 : (Fintype.card I : ℝ) * eps = gap := by
        rw [heps_def]
        field_simp
      linarith
    have hadd_w := Finset.add_sum_erase Finset.univ (fun j => value p (w j)) (Finset.mem_univ i)
    have hadd_x := Finset.add_sum_erase Finset.univ (fun j => value p (x j)) (Finset.mem_univ i)
    have hw_i_val : value p (w i) = value p (x i) - gap := by
      rw [hw_i, hgap_def]
      ring
    -- Combine
    have hlt_sum : ∑ j, value p (w j) < ∑ j, value p (x j) := by
      have h1 : (∑ j, value p (w j))
          = value p (w i) + ∑ j ∈ Finset.univ.erase i, value p (w j) := hadd_w.symm
      have h2 : (∑ j, value p (x j))
          = value p (x i) + ∑ j ∈ Finset.univ.erase i, value p (x j) := hadd_x.symm
      have h3 : ∑ j ∈ Finset.univ.erase i, value p (w j)
          ≤ (∑ j ∈ Finset.univ.erase i, value p (x j)) + (Finset.univ.erase i).card * eps := by
        rw [← hsum_rhs]
        exact hsum_le
      rw [h1, h2, hw_i_val]
      linarith
    linarith
  · -- Empty case: any nonzero p works
    obtain ⟨l0⟩ := ‹Nonempty L›
    use fun _ => 1
    constructor
    · intro h0
      have : (fun _ : L => (1 : ℝ)) l0 = (0 : L → ℝ) l0 := by rw [h0]
      simp at this
    · intro i
      exact (hI ⟨i⟩).elim

/-- From the quasi-equilibrium consumer condition to budget optimality (MWG Prop. 16.D.2): with
continuous utilities and nonnegative bundles `x i`, if every consumer has a strictly cheaper
nonnegative bundle, the quasi-equilibrium consumer condition implies budget optimality. -/
theorem isBudgetOptimal_of_cheaper {I L : Type*} [Fintype L]
    {u : I → (L → ℝ) → ℝ} {p : L → ℝ} {x : I → L → ℝ}
    (hcont : ∀ i, ContinuousOn (u i) (consumptionSet L))
    (hxX : ∀ i, x i ∈ consumptionSet L)
    (hq : IsQuasiSupportingPrice u p x)
    (hcheap : ∀ i, ∃ z ∈ consumptionSet L, value p z < value p (x i)) :
    IsBudgetOptimal u p x := by
  intro i z hzX hle
  have _ := hxX i
  by_contra hnge
  have hnge : u i (x i) < u i z := lt_of_not_ge hnge
  obtain ⟨c, hcX, hc_lt⟩ := hcheap i
  set h : ℝ → (L → ℝ) := fun t => (1 - t) • z + t • c with hh_def
  have hcont_path : Continuous h := by
    unfold h
    apply Continuous.add
    · exact (continuous_const.sub continuous_id).smul continuous_const
    · exact continuous_id.smul continuous_const
  have h0 : h 0 = z := by
    simp [h]
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, h t ∈ consumptionSet L := by
    intro t ht
    have hX := consumptionSet_convex L
    have ha : (0 : ℝ) ≤ 1 - t := sub_nonneg.mpr ht.2
    have hb : (0 : ℝ) ≤ t := ht.1
    have hab : (1 - t) + t = 1 := by ring
    have := hX hzX hcX ha hb hab
    simpa [h] using this
  have hval : ∀ t : ℝ, value p (h t) = (1 - t) * value p z + t * value p c := by
    intro t
    simp only [h]
    rw [value_add, value_smul, value_smul]
  have hcheap_path : ∀ t ∈ Set.Ioc (0 : ℝ) 1, value p (h t) < value p (x i) := by
    intro t ht
    rw [hval t]
    have h1t : (0 : ℝ) ≤ 1 - t := sub_nonneg.mpr ht.2
    have hlt1 : (1 - t) * value p z ≤ (1 - t) * value p (x i) :=
      mul_le_mul_of_nonneg_left hle h1t
    have hlt2 : t * value p c < t * value p (x i) :=
      mul_lt_mul_of_pos_left hc_lt ht.1
    have heq : (1 - t) * value p (x i) + t * value p (x i) = value p (x i) := by ring
    linarith
  have hwithin : ContinuousWithinAt (u i) (consumptionSet L) z :=
    (hcont i).continuousWithinAt hzX
  have hgap : (0 : ℝ) < u i z - u i (x i) := sub_pos.mpr hnge
  obtain ⟨δ, hδpos, hδ⟩ :=
    (Metric.continuousWithinAt_iff.mp hwithin) ((u i z - u i (x i)) / 2) (by linarith)
  have hpath_at : ContinuousAt h 0 := hcont_path.continuousAt
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := (Metric.continuousAt_iff.mp hpath_at) δ hδpos
  set t₀ : ℝ := min (δ₁ / 2) (1 / 2) with ht0_def
  have ht0_pos : (0 : ℝ) < t₀ := lt_min_iff.mpr ⟨by linarith, by norm_num⟩
  have ht0_le_half : t₀ ≤ 1 / 2 := by
    rw [ht0_def]
    exact min_le_right _ _
  have ht0_le1 : t₀ ≤ 1 := by linarith
  have ht0_lt_δ₁ : dist t₀ (0 : ℝ) < δ₁ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht0_pos]
    have : t₀ ≤ δ₁ / 2 := by rw [ht0_def]; exact min_le_left _ _
    linarith
  have hdist : dist (h t₀) (h 0) < δ := hδ₁ ht0_lt_δ₁
  rw [h0] at hdist
  have ht0_mem : h t₀ ∈ consumptionSet L := hmem t₀ ⟨le_of_lt ht0_pos, ht0_le1⟩
  have hclose := hδ ht0_mem hdist
  rw [Real.dist_eq] at hclose
  have hutil : u i (x i) < u i (h t₀) := by
    have habs := abs_lt.mp hclose
    linarith
  have ht0_ioc : t₀ ∈ Set.Ioc (0 : ℝ) 1 := ⟨ht0_pos, ht0_le1⟩
  have hval_lt : value p (h t₀) < value p (x i) := hcheap_path t₀ ht0_ioc
  have hval_le : value p (x i) ≤ value p (h t₀) := hq i (h t₀) ht0_mem hutil
  linarith

/-- `(x, p)` is a price quasi-equilibrium with transfers for the aggregate endowment `ω`
(MWG Def. 16.D.1, exchange economy): `p ≠ 0`, the allocation is feasible, and every nonnegative
bundle strictly preferred to `x i` costs at least the wealth `value p (x i)`; these wealth levels
add up to `value p ω`. -/
def IsQuasiEquilibriumWithTransfers {I L : Type*} [Fintype I] [Fintype L]
    (u : I → (L → ℝ) → ℝ) (ω p : L → ℝ) (x : I → L → ℝ) : Prop :=
  p ≠ 0 ∧ IsFeasible ω x ∧ IsQuasiSupportingPrice u p x

/-- `(x, p)` is a price equilibrium with transfers for the aggregate endowment `ω` (MWG Def. 16.B.4,
exchange economy): `p ≠ 0`, the allocation is feasible, and each `x i` maximizes `u i` on its budget
set at wealth `value p (x i)`. -/
def IsEquilibriumWithTransfers {I L : Type*} [Fintype I] [Fintype L]
    (u : I → (L → ℝ) → ℝ) (ω p : L → ℝ) (x : I → L → ℝ) : Prop :=
  p ≠ 0 ∧ IsFeasible ω x ∧ IsBudgetOptimal u p x

/-- Second fundamental welfare theorem (MWG Prop. 16.D.1, exchange economy, with continuous
utilities): a Pareto optimal allocation of an exchange economy with continuous, quasiconcave,
locally nonsatiated utilities on `ℝ^L_+` is a price quasi-equilibrium with transfers for some
price vector. -/
theorem exists_isQuasiEquilibriumWithTransfers {I L : Type*} [Fintype I] [Fintype L]
    [Nonempty L] {u : I → (L → ℝ) → ℝ} {ω : L → ℝ} {x : I → L → ℝ}
    (hcont : ∀ i, ContinuousOn (u i) (consumptionSet L))
    (hqc : ∀ i, QuasiconcaveOn ℝ (consumptionSet L) (u i))
    (hlns : ∀ i, LocallyNonsatiated (u i))
    (hx : IsParetoOptimal u ω x) :
    ∃ p : L → ℝ, IsQuasiEquilibriumWithTransfers u ω p x := by
  obtain ⟨p, hpne, hsupp⟩ := exists_isQuasiSupportingPrice hcont hqc hlns hx
  exact ⟨p, hpne, hx.1, hsupp⟩

/-- From quasi-equilibrium to equilibrium (MWG Prop. 16.D.2): with continuous utilities, a price
quasi-equilibrium with transfers in which every consumer has a strictly cheaper nonnegative
bundle is a price equilibrium with transfers. -/
theorem isEquilibriumWithTransfers_of_cheaper {I L : Type*} [Fintype I] [Fintype L]
    {u : I → (L → ℝ) → ℝ} {ω p : L → ℝ} {x : I → L → ℝ}
    (hcont : ∀ i, ContinuousOn (u i) (consumptionSet L))
    (hq : IsQuasiEquilibriumWithTransfers u ω p x)
    (hcheap : ∀ i, ∃ z ∈ consumptionSet L, value p z < value p (x i)) :
    IsEquilibriumWithTransfers u ω p x := by
  obtain ⟨hpne, hfeas, hsupp⟩ := hq
  exact ⟨hpne, hfeas, isBudgetOptimal_of_cheaper hcont hfeas.1 hsupp hcheap⟩

end MathlibExt.Economics.SecondWelfareTheorem
