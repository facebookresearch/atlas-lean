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
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# One-period fundamental theorem of asset pricing

In a finite one-period market where asset `a` gains `g a ω` in state `ω`, there is no arbitrage
(no portfolio whose gain is nonnegative in every state and positive in some state) iff some
strictly positive probability `q` on the states gives every asset zero expected gain. The proof
separates the range of the gains map from the probability simplex by Hahn-Banach.
The second fundamental theorem, `one_period_second_fundamental_theorem_asset_pricing`, adds that
an arbitrage-free market is complete (every state payoff is a riskless amount plus a portfolio's
gain) iff that strictly positive normalized `q` is unique. The converse direction uses the
perturbation lemma `exists_ne_statePrice_of_ne_zero`: a small move of a strictly positive state
price along a nonzero direction that keeps the linear constraints is another state price.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.FundamentalTheoremAssetPricing

/-- Finite one-period FTAP without `DecidableEq` instances on the states `Ω` or the assets `A`;
`one_period_fundamental_theorem_asset_pricing` is the source-shaped form. -/
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
Finite one-period FTAP: no arbitrage iff strictly positive state-price / martingale pmf with zero
expected gain exists.
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

set_option linter.unusedFintypeInType false in
/-- **Perturbation lemma.** In a finite one-period market with gains `g`, if `q` is a strictly
positive normalized state-price vector (`∑ ω, q ω = 1` and `∑ ω, q ω * g a ω = 0` for every
asset `a`) and `d` is a nonzero direction preserving these linear constraints (`∑ ω, d ω = 0`
and `∑ ω, d ω * g a ω = 0`), then a sufficiently small perturbation of `q` along `d` is a
different strictly positive normalized state-price vector. -/
theorem exists_ne_statePrice_of_ne_zero
    {Ω : Type*} [Fintype Ω] {A : Type*} [Fintype A] (g : A → Ω → ℝ)
    {q d : Ω → ℝ} (hq : ∀ ω : Ω, 0 < q ω) (hq1 : ∑ ω : Ω, q ω = 1)
    (hqg : ∀ a : A, ∑ ω : Ω, q ω * g a ω = 0)
    (hd : d ≠ 0) (hd1 : ∑ ω : Ω, d ω = 0) (hdg : ∀ a : A, ∑ ω : Ω, d ω * g a ω = 0) :
    ∃ q' : Ω → ℝ, q' ≠ q ∧ (∀ ω : Ω, 0 < q' ω) ∧ (∑ ω : Ω, q' ω = 1) ∧
      (∀ a : A, ∑ ω : Ω, q' ω * g a ω = 0) := by
  have hne2 : Nonempty Ω := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact hd (funext fun ω => hne.elim ω)
  have huniv : Finset.univ.Nonempty := @Finset.univ_nonempty Ω _ hne2
  obtain ⟨ω₀, -, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun ω => q ω / (1 + |d ω|)) huniv
  have hmpos : 0 < q ω₀ / (1 + |d ω₀|) := div_pos (hq ω₀) (by positivity)
  set ε : ℝ := (q ω₀ / (1 + |d ω₀|)) / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hεne : ε ≠ 0 := ne_of_gt hεpos
  have key : ∀ ω : Ω, ε * |d ω| < q ω := by
    intro ω
    have hden : (0 : ℝ) < 1 + |d ω| := by positivity
    have h := hmin ω (Finset.mem_univ ω)
    rw [le_div_iff₀ hden] at h
    rw [hεdef]
    generalize hE : q ω₀ / (1 + |d ω₀|) = E0 at h hmpos ⊢
    nlinarith [h, hmpos, hq ω, abs_nonneg (d ω)]
  refine ⟨fun ω => q ω + ε * d ω, ?_, ?_, ?_, ?_⟩
  · intro hcon
    apply hd
    funext ω
    have hω : q ω + ε * d ω = q ω := congr_fun hcon ω
    have h0 : ε * d ω = 0 := add_eq_left.mp hω
    rcases mul_eq_zero.mp h0 with hε0 | hd0
    · exact absurd hε0 hεne
    · exact hd0
  · intro ω
    have habs : |ε * d ω| = ε * |d ω| := by rw [abs_mul, abs_of_pos hεpos]
    have hlt : |ε * d ω| < q ω := by rw [habs]; exact key ω
    have hlb : -(q ω) < ε * d ω := neg_lt_of_abs_lt hlt
    change (0 : ℝ) < q ω + ε * d ω
    linarith
  · change (∑ ω, (q ω + ε * d ω)) = 1
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hq1, hd1, mul_zero, add_zero]
  · intro a
    have hpt : ∀ ω : Ω, (q ω + ε * d ω) * g a ω
        = q ω * g a ω + ε * (d ω * g a ω) := fun ω => by ring
    change (∑ ω, (q ω + ε * d ω) * g a ω) = 0
    simp only [hpt, Finset.sum_add_distrib, ← Finset.mul_sum, hqg, hdg, mul_zero, add_zero]

/-- **Second fundamental theorem of asset pricing (finite one-period, gains form).** In an
arbitrage-free finite market with a riskless numeraire, where `g a ω` is the discounted gain of
asset `a` in state `ω`, the market is complete (every state-contingent payoff `x` is replicated
by a riskless position `c` plus a portfolio `h` of the risky assets) iff the strictly positive
normalized state-price vector is unique. -/
theorem one_period_second_fundamental_theorem_asset_pricing
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {A : Type*} [Fintype A]
    (g : A → Ω → ℝ)
    (hNA : ¬ ∃ h : A → ℝ, (∀ ω : Ω, 0 ≤ ∑ a : A, h a * g a ω) ∧
      (∃ ω : Ω, 0 < ∑ a : A, h a * g a ω)) :
    (∀ x : Ω → ℝ, ∃ c : ℝ, ∃ h : A → ℝ, ∀ ω : Ω, x ω = c + ∑ a : A, h a * g a ω) ↔
    ∃! q : Ω → ℝ, (∀ ω : Ω, 0 < q ω) ∧ (∑ ω : Ω, q ω = 1) ∧
      (∀ a : A, ∑ ω : Ω, q ω * g a ω = 0) := by
  classical
  constructor
  · -- (⇒) completeness forces every state-price vector to agree on indicators.
    intro hcompl
    obtain ⟨q₀, hq₀pos, hq₀1, hq₀g⟩ :=
      (one_period_fundamental_theorem_asset_pricing_general g).mp hNA
    refine ⟨q₀, ⟨hq₀pos, hq₀1, hq₀g⟩, fun q' hq' => ?_⟩
    obtain ⟨-, hq'1, hq'g⟩ := hq'
    funext ω
    obtain ⟨c, h, hrep⟩ := hcompl (Pi.single ω (1 : ℝ))
    have hval : ∀ q : Ω → ℝ, (∑ ω', q ω' = 1) →
        (∀ a, ∑ ω', q ω' * g a ω' = 0) → q ω = c := by
      intro q hq1 hqg
      have hsingle : (∑ ω', q ω' * (Pi.single ω (1 : ℝ) : Ω → ℝ) ω') = q ω := by
        rw [Finset.sum_eq_single ω]
        · rw [Pi.single_eq_same, mul_one]
        · intro ω' _ hne
          rw [Pi.single_eq_of_ne hne, mul_zero]
        · simp
      have hexpand : (∑ ω', q ω' * (Pi.single ω (1 : ℝ) : Ω → ℝ) ω') = c := by
        have hpt : ∀ ω' : Ω, q ω' * (Pi.single ω (1 : ℝ) : Ω → ℝ) ω'
            = q ω' * c + q ω' * (∑ a, h a * g a ω') := by
          intro ω'
          rw [hrep ω', mul_add]
        have hB : (∑ ω', q ω' * (∑ a, h a * g a ω')) = 0 := by
          have hswap : (∑ ω', q ω' * (∑ a, h a * g a ω'))
              = ∑ a, h a * (∑ ω', q ω' * g a ω') := by
            simp only [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro ω' _
            ring
          rw [hswap]
          exact Finset.sum_eq_zero fun a _ => by rw [hqg a, mul_zero]
        simp only [hpt, Finset.sum_add_distrib, ← Finset.sum_mul, hq1, one_mul, hB,
          add_zero]
      rw [hsingle] at hexpand
      exact hexpand
    rw [hval q₀ hq₀1 hq₀g, hval q' hq'1 hq'g]
  · -- (⇐) if some payoff is not replicated, a dual vector gives a second pmf.
    intro huniq
    by_contra hnc
    push Not at hnc
    obtain ⟨x₀, hnc⟩ := hnc
    let L : ℝ × (A → ℝ) →ₗ[ℝ] (Ω → ℝ) :=
      { toFun := fun p ω => p.1 + ∑ a, p.2 a * g a ω
        map_add' := by
          intro p₁ p₂
          funext ω
          simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul,
            Finset.sum_add_distrib]
          ring
        map_smul' := by
          intro c p
          funext ω
          change (c • p).1 + ∑ a, (c • p).2 a * g a ω
            = c • (p.1 + ∑ a, p.2 a * g a ω)
          simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
          rw [mul_add, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro a _
          ring }
    have hLapp : ∀ (p : ℝ × (A → ℝ)) (ω : Ω),
        L p ω = p.1 + ∑ a, p.2 a * g a ω := fun p ω => rfl
    have hx₀ : x₀ ∉ LinearMap.range L := by
      rintro ⟨⟨c, h⟩, rfl⟩
      obtain ⟨ω, hω⟩ := hnc c h
      exact hω rfl
    have hlt : LinearMap.range L < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      apply hx₀
      rw [htop]
      exact Submodule.mem_top
    obtain ⟨f, hf0, hmap⟩ :=
      Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
    have hvan : ∀ x ∈ LinearMap.range L, f x = 0 := by
      intro x hx
      have hmem : f x ∈ Submodule.map f (LinearMap.range L) :=
        Submodule.mem_map_of_mem hx
      rw [hmap] at hmem
      exact (Submodule.mem_bot ℝ).mp hmem
    have hone : (fun _ : Ω => (1 : ℝ)) ∈ LinearMap.range L := by
      have h : L (1, 0) = fun _ : Ω => (1 : ℝ) := by
        funext ω
        rw [hLapp]
        change (1 : ℝ) + ∑ b, (0 : A → ℝ) b * g b ω = 1
        simp
      rw [← h]
      exact LinearMap.mem_range_self L (1, 0)
    have hgmem : ∀ a : A, (fun ω => g a ω) ∈ LinearMap.range L := by
      intro a
      have hsum : ∀ ω : Ω, (∑ b, (Pi.single a (1 : ℝ) : A → ℝ) b * g b ω) = g a ω := by
        intro ω
        rw [Finset.sum_eq_single a]
        · rw [Pi.single_eq_same, one_mul]
        · intro b _ hb
          rw [Pi.single_eq_of_ne hb, zero_mul]
        · simp
      have h : L (0, Pi.single a 1) = fun ω => g a ω := by
        funext ω
        rw [hLapp]
        change (0 : ℝ) + ∑ b, (Pi.single a (1 : ℝ) : A → ℝ) b * g b ω = g a ω
        rw [hsum ω, zero_add]
      rw [← h]
      exact LinearMap.mem_range_self L (0, Pi.single a 1)
    set d : Ω → ℝ := fun ω => f (Pi.single ω 1) with hddef
    have hrepr : ∀ x : Ω → ℝ, f x = ∑ ω, d ω * x ω := by
      intro x
      have hexpand : f x = ∑ ω, x ω * f (Pi.single ω (1 : ℝ)) := by
        conv_lhs => rw [pi_eq_sum_univ' x]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro ω _
        rw [map_smul, smul_eq_mul]
      rw [hexpand]
      apply Finset.sum_congr rfl
      intro ω _
      simp only [hddef]
      ring
    have hd0 : d ≠ 0 := by
      intro hcon
      apply hf0
      apply LinearMap.ext
      intro x
      simp only [hrepr, hcon, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
        LinearMap.zero_apply]
    have hd1 : ∑ ω, d ω = 0 := by
      have h1 : f (fun _ : Ω => (1 : ℝ)) = 0 := hvan _ hone
      rw [hrepr] at h1
      simpa only [mul_one] using h1
    have hdg : ∀ a : A, ∑ ω, d ω * g a ω = 0 := by
      intro a
      have ha : f (fun ω => g a ω) = 0 := hvan _ (hgmem a)
      rw [hrepr] at ha
      simpa only using ha
    obtain ⟨q₀, hq₀pos, hq₀1, hq₀g⟩ :=
      (one_period_fundamental_theorem_asset_pricing_general g).mp hNA
    obtain ⟨q', hq'ne, hq'pos, hq'1, hq'g⟩ :=
      exists_ne_statePrice_of_ne_zero g hq₀pos hq₀1 hq₀g hd0 hd1 hdg
    obtain ⟨qstar, hstar, huniq'⟩ := huniq
    have e1 : q₀ = qstar := huniq' q₀ ⟨hq₀pos, hq₀1, hq₀g⟩
    have e2 : q' = qstar := huniq' q' ⟨hq'pos, hq'1, hq'g⟩
    exact hq'ne (e2.trans e1.symm)

end MathlibExt.Probability.Finance.FundamentalTheoremAssetPricing
