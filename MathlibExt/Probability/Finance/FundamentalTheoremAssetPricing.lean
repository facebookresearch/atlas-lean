/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# One-period fundamental theorem of asset pricing

In a finite one-period market where asset `a` gains `g a ω` in state `ω`, there is no arbitrage
(no portfolio whose gain is nonnegative in every state and positive in some state) iff some
strictly positive probability `q` on the states gives every asset zero expected gain. The proof
separates the range of the gains map from the probability simplex by Hahn-Banach.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.FundamentalTheoremAssetPricing

/-- **Fundamental theorem of asset pricing for a finite one-period market.** Let $\Omega$ be a
nonempty finite set of states and $A$ a finite set of assets, and let $g(a, \omega) \in \mathbb{R}$
be the gain of asset $a$ in state $\omega$. Call a portfolio $h \colon A \to \mathbb{R}$ an
arbitrage if its gain $\sum_{a \in A} h(a)\, g(a, \omega)$ is nonnegative in every state
$\omega$ and positive in some state. There is no arbitrage if and only if there is a function
$q \colon \Omega \to \mathbb{R}$ with $q(\omega) > 0$ for every $\omega \in \Omega$ and
$\sum_{\omega \in \Omega} q(\omega) = 1$ such that
$\sum_{\omega \in \Omega} q(\omega)\, g(a, \omega) = 0$ for every asset $a \in A$. -/
theorem one_period_fundamental_theorem_asset_pricing_general
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {A : Type*} [Fintype A]
    (g : A → Ω → ℝ) :
    (¬ ∃ h : A → ℝ, (∀ ω : Ω, 0 ≤ ∑ a : A, h a * g a ω) ∧
      (∃ ω : Ω, 0 < ∑ a : A, h a * g a ω)) ↔
    ∃ q : Ω → ℝ, (∀ ω : Ω, 0 < q ω) ∧ (∑ ω : Ω, q ω = 1) ∧
      (∀ a : A, ∑ ω : Ω, q ω * g a ω = 0) := by
  classical
  -- The marketed-gains operator: portfolio ↦ state-contingent payoff.
  let T : (A → ℝ) →ₗ[ℝ] (Ω → ℝ) :=
    { toFun := fun h ω => ∑ a, h a * g a ω
      map_add' := by
        intro h₁ h₂
        funext ω
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c h
        funext ω
        change (∑ a, (c • h) a * g a ω) = c • (∑ a, h a * g a ω)
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum] }
  have hTapp : ∀ (h : A → ℝ) (ω : Ω), T h ω = ∑ a, h a * g a ω := fun h ω => rfl
  have hfin : FiniteDimensional ℝ ↥(LinearMap.range T) := LinearMap.finiteDimensional_range T
  -- The price simplex: nonnegative state vectors summing to one.
  set Δ : Set (Ω → ℝ) := {x | (∀ ω, 0 ≤ x ω) ∧ ∑ ω, x ω = 1} with hΔdef
  have hSconv : Convex ℝ (↑(LinearMap.range T) : Set (Ω → ℝ)) :=
    (LinearMap.range T).convex
  have hSclosed : IsClosed (↑(LinearMap.range T) : Set (Ω → ℝ)) :=
    @Submodule.closed_of_finiteDimensional _ _ _ _ _ _ _ _ _ _ (LinearMap.range T) hfin
  have hΔconv : Convex ℝ Δ := by
    intro x hx y hy a b ha hb hab
    obtain ⟨hx0, hx1⟩ := hx
    obtain ⟨hy0, hy1⟩ := hy
    refine ⟨fun ω => ?_, ?_⟩
    · rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha (hx0 ω)) (mul_nonneg hb (hy0 ω))
    · rw [show (∑ ω, (a • x + b • y) ω) = a * (∑ ω, x ω) + b * (∑ ω, y ω) from by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum],
        hx1, hy1]
      linear_combination hab
  have hΔeq : Δ = (⋂ ω, {x : Ω → ℝ | 0 ≤ x ω}) ∩ {x : Ω → ℝ | ∑ ω, x ω = 1} := by
    apply Set.ext
    intro x
    simp only [hΔdef, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  have hcont : Continuous (fun x : Ω → ℝ => ∑ ω, x ω) :=
    continuous_finsetSum Finset.univ fun ω _ => continuous_apply ω
  have hΔclosed : IsClosed Δ := by
    rw [hΔeq]
    exact ((isClosed_iInter fun ω => isClosed_Ici.preimage (continuous_apply ω)).inter
      (isClosed_singleton.preimage hcont))
  have hΔcompact : IsCompact Δ := by
    apply IsCompact.of_isClosed_subset (s := Set.Icc (0 : Ω → ℝ) 1) isCompact_Icc hΔclosed
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    refine ⟨Pi.le_def.mpr hx0, Pi.le_def.mpr fun ω => ?_⟩
    change x ω ≤ 1
    rw [← hx1]
    exact Finset.single_le_sum (fun ω' _ => hx0 ω') (Finset.mem_univ ω)
  have hsingle_mem : ∀ ω : Ω, Pi.single ω (1 : ℝ) ∈ Δ := by
    intro ω
    refine ⟨fun ω' => ?_, ?_⟩
    · by_cases h : ω' = ω
      · subst h
        rw [Pi.single_eq_same]
        exact zero_le_one
      · simp only [Pi.single_eq_of_ne h 1, le_refl]
    · rw [Finset.sum_eq_single ω]
      · rw [Pi.single_eq_same]
      · intro b _ hb
        exact Pi.single_eq_of_ne hb 1
      · simp
  constructor
  · -- No arbitrage: separate the marketed subspace from the simplex.
    intro hnoarb
    have hdisj : Disjoint (↑(LinearMap.range T) : Set (Ω → ℝ)) Δ := by
      rw [Set.disjoint_left]
      intro x hxmem hx
      rw [SetLike.mem_coe, LinearMap.mem_range] at hxmem
      obtain ⟨h, rfl⟩ := hxmem
      obtain ⟨hx0, hx1⟩ := hx
      exact hnoarb ⟨h, fun ω => by rw [← hTapp]; exact hx0 ω, by
        by_contra hall
        push Not at hall
        have hzero : ∀ ω, T h ω = 0 := fun ω =>
          le_antisymm (by rw [hTapp]; exact hall ω) (hx0 ω)
        have hsum : (∑ ω, T h ω) = 0 := Finset.sum_eq_zero fun ω _ => hzero ω
        rw [hx1] at hsum
        exact one_ne_zero hsum⟩
    obtain ⟨f, u, v, hfu, huv, hfv⟩ :=
      geometric_hahn_banach_closed_compact hSconv hSclosed hΔconv hΔcompact hdisj
    -- The separator vanishes on the marketed subspace.
    have hle_of_bound : ∀ (y : Ω → ℝ), y ∈ LinearMap.range T → f y ≤ 0 := by
      intro y hy
      by_contra hlt
      push Not at hlt
      obtain ⟨n, hn⟩ := exists_nat_gt (u / f y)
      have hlt' : u < (n : ℝ) * f y := (div_lt_iff₀ hlt).mp hn
      have hmem : (n : ℝ) • y ∈ (↑(LinearMap.range T) : Set (Ω → ℝ)) :=
        Submodule.smul_mem _ _ (SetLike.mem_coe.mpr hy)
      have h2 := hfu _ hmem
      rw [map_smul, smul_eq_mul] at h2
      linarith
    have hvanish : ∀ y ∈ LinearMap.range T, f y = 0 := by
      intro y hy
      refine le_antisymm (hle_of_bound y hy) ?_
      have h := hle_of_bound (-y) (neg_mem hy)
      rwa [map_neg, neg_nonpos] at h
    have h0lt : (0 : ℝ) < u := by
      have h0 := hfu 0 (zero_mem _)
      rwa [map_zero] at h0
    have hqpos : ∀ ω : Ω, 0 < f (Pi.single ω (1 : ℝ)) := fun ω =>
      lt_trans (lt_trans h0lt huv) (hfv _ (hsingle_mem ω))
    -- Normalize the strictly positive separator to a pmf.
    set S : ℝ := ∑ ω, f (Pi.single ω (1 : ℝ)) with hSdef
    have hSpos : 0 < S := by
      rw [hSdef]
      exact Finset.sum_pos (fun ω _ => hqpos ω)
        (Finset.univ_nonempty_iff.mpr inferInstance)
    have hxa : ∀ a : A, (fun ω => g a ω) = T (Pi.single a 1) := by
      intro a
      funext ω
      show g a ω = T (Pi.single a 1) ω
      rw [hTapp]
      rw [Finset.sum_eq_single a]
      · rw [Pi.single_eq_same, one_mul]
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb, zero_mul]
      · simp
    have hprice : ∀ a : A, ∑ ω, f (Pi.single ω (1 : ℝ)) / S * g a ω = 0 := by
      intro a
      have hfa : f (fun ω => g a ω) = 0 :=
        hvanish _ (LinearMap.mem_range.mpr ⟨Pi.single a 1, (hxa a).symm⟩)
      have hexpand : f (fun ω => g a ω) = ∑ ω, g a ω * f (Pi.single ω (1 : ℝ)) := by
        conv_lhs => rw [pi_eq_sum_univ' (fun ω => g a ω)]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro ω _
        rw [map_smul, smul_eq_mul]
      have h2 : (∑ ω, f (Pi.single ω (1 : ℝ)) / S * g a ω)
          = (∑ ω, g a ω * f (Pi.single ω (1 : ℝ))) / S := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro ω _
        rw [div_mul_eq_mul_div, mul_comm]
      rw [hexpand] at hfa
      rw [h2, hfa, zero_div]
    exact ⟨fun ω => f (Pi.single ω (1 : ℝ)) / S, fun ω => div_pos (hqpos ω) hSpos,
      by rw [← Finset.sum_div, ← hSdef, div_self (ne_of_gt hSpos)], fun a => hprice a⟩
  · -- A martingale pmf rules out arbitrage by double counting.
    rintro ⟨q, hqpos, hqsum, hqmart⟩ ⟨h, hnn, ω₀, hpos⟩
    have hswap : (∑ ω, q ω * (∑ a, h a * g a ω))
        = ∑ a, h a * (∑ ω, q ω * g a ω) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro ω _
      ring
    have hRHS : (∑ a, h a * (∑ ω, q ω * g a ω)) = 0 :=
      Finset.sum_eq_zero fun a _ => by rw [hqmart a, mul_zero]
    have hLHSpos : 0 < ∑ ω, q ω * (∑ a, h a * g a ω) := by
      apply Finset.sum_pos'
      · intro ω _
        exact mul_nonneg (le_of_lt (hqpos ω)) (hnn ω)
      · exact ⟨ω₀, Finset.mem_univ ω₀, mul_pos (hqpos ω₀) hpos⟩
    rw [hswap, hRHS] at hLHSpos
    exact lt_irrefl _ hLHSpos

set_option linter.unusedDecidableInType false in
/--
**One-period fundamental theorem of asset pricing.** Let $\Omega$ be a nonempty finite set of
states and $A$ a finite set of assets, and let $g(a, \omega) \in \mathbb{R}$ be the gain of
asset $a$ in state $\omega$. Call a portfolio $h \colon A \to \mathbb{R}$ an arbitrage if its
gain $\sum_{a \in A} h(a)\, g(a, \omega)$ is nonnegative in every state $\omega$ and positive
in some state. There is no arbitrage if and only if there is a function
$q \colon \Omega \to \mathbb{R}$ with $q(\omega) > 0$ for every $\omega \in \Omega$ and
$\sum_{\omega \in \Omega} q(\omega) = 1$ such that
$\sum_{\omega \in \Omega} q(\omega)\, g(a, \omega) = 0$ for every asset $a \in A$, that is, a
strictly positive probability on the states under which every asset has zero expected gain.

Source: J. M. Harrison and D. M. Kreps, J. Econom. Theory 20 (1979), DOI
10.1016/0022-0531(79)90043-7.
Proves `Wanted` entry `one_period_fundamental_theorem_asset_pricing`.
It follows from `one_period_fundamental_theorem_asset_pricing_general`; the unused
`[DecidableEq Ω]` and `[DecidableEq A]` keep the source's shape.
-/
theorem one_period_fundamental_theorem_asset_pricing
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    {A : Type*} [Fintype A] [DecidableEq A]
    (g : A → Ω → ℝ) :
    (¬ ∃ h : A → ℝ, (∀ ω : Ω, 0 ≤ ∑ a : A, h a * g a ω) ∧
      (∃ ω : Ω, 0 < ∑ a : A, h a * g a ω)) ↔
    ∃ q : Ω → ℝ, (∀ ω : Ω, 0 < q ω) ∧ (∑ ω : Ω, q ω = 1) ∧
      (∀ a : A, ∑ ω : Ω, q ω * g a ω = 0) :=
  one_period_fundamental_theorem_asset_pricing_general g

end MathlibExt.Probability.Finance.FundamentalTheoremAssetPricing
