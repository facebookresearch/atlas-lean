/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.HardyWeinberg
public import Mathlib.Analysis.SpecificLimits.Basic
import Domains.Biology.PopulationGenetics.Classical.Dioecy
import Mathlib.Dynamics.FixedPoints.Topology
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Allele frequency under meiotic drive without viability differences

One diploid locus with alleles `A` and `a`, in an infinite randomly mating population with
nonoverlapping generations and no viability differences. Alleles are `Bool`, `true` being `A`,
and a genotype is an ordered pair (maternal allele, paternal allele), as in
`MathlibExt.Biology.PopulationGenetics.HardyWeinberg`. Meiotic drive acts in both sexes: a
heterozygote transmits `A` with probability `k ∈ [0, 1]` instead of Mendel's `1/2`, and a
homozygote transmits its own allele.

If the newborns are in Hardy–Weinberg proportions and `p` is the frequency of `A` among them,
the newborns of the next generation are again in Hardy–Weinberg proportions and the frequency
of `A` among them is `p' = p² + 2pqk`, `q = 1 - p`; so `p' - p = pq(2k - 1)` and `p' ∈ [0, 1]`.
From `p₀ ∈ (0, 1)` the frequency increases strictly to `1` if `k > 1/2`, decreases strictly
to `0` if `k < 1/2`, and stays at `p₀` if `k = 1/2`.

## Main definitions

* `driveTransmit c`: transmission under meiotic drive, where a heterozygote transmits an allele
  drawn from `c : PMF Bool`, so `A` with probability `k = c true`.
* `driveOffspring c G`: the genotype law of the next generation's newborns.
* `driveStep k p = p ^ 2 + 2 * p * (1 - p) * k`: the allele-frequency map.

## Main result

* `allele_frequency_under_meiotic_drive`: the recursion from the genotype model, the change
  `p' - p = pq(2k - 1)`, `p' ∈ [0, 1]`, and the three regimes `k > 1/2`, `k < 1/2`, `k = 1/2`.

## References

* J. Felsenstein, *Theoretical Evolutionary Genetics* (version of December 2019), Chapter II,
  Complements/Problems, Problem 19, p. 135: meiotic drive in both sexes, heterozygotes producing
  a fraction `(1 + α)/2` of `A` gametes, that is `k = (1 + α)/2`. The convergence statements are
  derived from the change in gene frequency.
-/

@[expose] public section

open Filter Set Topology
open scoped ENNReal

namespace MathlibExt.Biology.PopulationGenetics.Classical.MeioticDrive

open MathlibExt.Biology.PopulationGenetics.HardyWeinberg

/-- Transmission at a two-allele locus under meiotic drive acting in both sexes. Alleles are
`Bool`, `true` being `A` and `false` being `a`, and a genotype is an ordered pair. A homozygote
`(b, b)` transmits `b`; a heterozygote, `(A, a)` or `(a, A)`, transmits an allele drawn from `c`,
so `A` with probability `k = c true` and `a` with probability `1 - k`. For the fair coin
`c = PMF.uniformFintype Bool` this is Mendel's law `HardyWeinberg.transmit`. -/
noncomputable def driveTransmit (c : PMF Bool) (g : Bool × Bool) : PMF Bool :=
  if g.1 = g.2 then PMF.pure g.1 else c

/-- The genotype law of the next generation's newborns under meiotic drive `driveTransmit c`,
when the current newborns have genotype law `G`. With no viability differences the adults have
the newborns' law `G`; each parent transmits an allele by `driveTransmit c`, and gametes unite at
random, so the two alleles of a newborn are independent draws from the gamete law
`G.bind (driveTransmit c)`. -/
noncomputable def driveOffspring (c : PMF Bool) (G : PMF (Bool × Bool)) : PMF (Bool × Bool) :=
  (G.bind (driveTransmit c)).bind fun a => (G.bind (driveTransmit c)).map (Prod.mk a)

/-- The allele-frequency map `p ↦ p' = p² + 2pqk`, with `q = 1 - p`, of meiotic drive in which
heterozygotes transmit `A` with probability `k`: `p'` is the frequency of `A` among the next
generation's newborns when `p` is its frequency among the current newborns, in Hardy–Weinberg
proportions (`allele_frequency_under_meiotic_drive`). -/
noncomputable def driveStep (k p : ℝ) : ℝ := p ^ 2 + 2 * p * (1 - p) * k

/-! ### The genotype model -/

/-- The gamete law of adults with genotype law `G` puts mass `G (A, A) + G (A, a) k + G (a, A) k`
on `A`, where `k = c true`. -/
private theorem bind_driveTransmit_true (c : PMF Bool) (G : PMF (Bool × Bool)) :
    G.bind (driveTransmit c) true =
      G (true, true) + G (true, false) * c true + G (false, true) * c true := by
  simp [PMF.bind_apply, tsum_fintype, Fintype.sum_prod_type, driveTransmit, add_assoc]

/-- Under random union of gametes with law `g`, the frequency of each allele among the
newborns is its mass under `g`. -/
private theorem gamete_bind_map_prodMk (g : PMF Bool) :
    gamete (g.bind fun a => g.map (Prod.mk a)) = g := by
  have hsum : ∑ b, g b = 1 := by simpa [tsum_fintype] using g.tsum_coe
  ext a
  rw [gamete_apply]
  simp only [Dioecy.bind_map_prodMk_apply]
  rw [← Finset.mul_sum, ← Finset.sum_mul, hsum, mul_one, one_mul, ← add_mul,
    ENNReal.inv_two_add_inv_two, one_mul]

/-- The newborns of the next generation are in Hardy–Weinberg proportions, and their allele
law is the gamete law of the current adults. -/
private theorem driveOffspring_hw (c : PMF Bool) (G : PMF (Bool × Bool)) :
    gamete (driveOffspring c G) = G.bind (driveTransmit c) ∧
      offspring (driveOffspring c G) = driveOffspring c G := by
  have h := gamete_bind_map_prodMk (G.bind (driveTransmit c))
  refine ⟨h, ?_⟩
  change (gamete (driveOffspring c G)).bind (fun a => (gamete (driveOffspring c G)).map
    (Prod.mk a)) = driveOffspring c G
  rw [show gamete (driveOffspring c G) = G.bind (driveTransmit c) from h]
  rfl

/-- One generation from newborns in Hardy–Weinberg proportions with `A`-frequency `p`: the
next newborns have `A`-frequency `driveStep k p`. -/
private theorem freq_driveOffspring {c : PMF Bool} {G : PMF (Bool × Bool)}
    (hG : offspring G = G) :
    (gamete (driveOffspring c G) true).toReal =
      driveStep (c true).toReal (gamete G true).toReal := by
  have hGab : ∀ a b, G (a, b) = gamete G a * gamete G b := fun a b => by
    rw [← offspring_apply, hG]
  have hq : (gamete G false).toReal = 1 - (gamete G true).toReal := by
    linarith [freq_true_add_freq_false G]
  have hfin : ∀ a b : Bool, gamete G a * gamete G b * c true ≠ ∞ := fun a b =>
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))
      (PMF.apply_ne_top _ _)
  rw [(driveOffspring_hw c G).1, bind_driveTransmit_true, hGab, hGab, hGab,
    ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
      (PMF.apply_ne_top _ _), hfin _ _⟩) (hfin _ _),
    ENNReal.toReal_add (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))
      (hfin _ _)]
  simp only [ENNReal.toReal_mul, hq, driveStep]
  ring

/-! ### The allele-frequency map -/

private theorem driveStep_sub_self (k p : ℝ) : driveStep k p - p = p * (1 - p) * (2 * k - 1) := by
  unfold driveStep
  ring

private theorem one_sub_driveStep (k p : ℝ) :
    1 - driveStep k p = (1 - p) ^ 2 + 2 * (p * (1 - p)) * (1 - k) := by
  unfold driveStep
  ring

private theorem driveStep_mem_Icc {k p : ℝ} (hk : k ∈ Icc (0 : ℝ) 1) (hp : p ∈ Icc (0 : ℝ) 1) :
    driveStep k p ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨hk0, hk1⟩ := hk
  obtain ⟨hp0, hp1⟩ := hp
  have hpq : 0 ≤ p * (1 - p) := mul_nonneg hp0 (by linarith)
  have h1 := one_sub_driveStep k p
  constructor
  · unfold driveStep
    nlinarith [mul_nonneg hpq hk0, sq_nonneg p]
  · nlinarith [mul_nonneg hpq (sub_nonneg.2 hk1), sq_nonneg (1 - p)]

private theorem driveStep_mem_Ioo {k p : ℝ} (hk : k ∈ Icc (0 : ℝ) 1) (hp : p ∈ Ioo (0 : ℝ) 1) :
    driveStep k p ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨hk0, hk1⟩ := hk
  obtain ⟨hp0, hp1⟩ := hp
  have hpq : 0 ≤ p * (1 - p) := mul_nonneg hp0.le (by linarith)
  have hq : 0 < (1 - p) ^ 2 := pow_pos (by linarith) 2
  have h1 := one_sub_driveStep k p
  constructor
  · unfold driveStep
    nlinarith [mul_nonneg hpq hk0, mul_pos hp0 hp0]
  · nlinarith [mul_nonneg hpq (sub_nonneg.2 hk1)]

private theorem continuous_driveStep (k : ℝ) : Continuous (driveStep k) := by
  unfold driveStep
  fun_prop

/-- The orbit from `p₀ ∈ (0, 1)` stays in `(0, 1)`. -/
private theorem iterate_driveStep_mem_Ioo {k p₀ : ℝ} (hk : k ∈ Icc (0 : ℝ) 1)
    (hp₀ : p₀ ∈ Ioo (0 : ℝ) 1) (t : ℕ) : (driveStep k)^[t] p₀ ∈ Ioo (0 : ℝ) 1 := by
  induction t with
  | zero => exact hp₀
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact driveStep_mem_Ioo hk ih

/-- A limit of an orbit is a fixed point, hence `0` or `1` when `k ≠ 1/2`. -/
private theorem limit_eq_zero_or_one {k p₀ L : ℝ} (hk : k ≠ 1 / 2)
    (hL : Tendsto (fun t => (driveStep k)^[t] p₀) atTop (𝓝 L)) : L = 0 ∨ L = 1 := by
  have hfix : driveStep k L = L :=
    isFixedPt_of_tendsto_iterate hL (continuous_driveStep k).continuousAt
  have h0 : L * (1 - L) * (2 * k - 1) = 0 := by rw [← driveStep_sub_self, hfix, sub_self]
  have hk' : 2 * k - 1 ≠ 0 := fun h => hk (by linarith)
  rcases mul_eq_zero.1 ((mul_eq_zero.1 h0).resolve_right hk') with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-- **Allele frequency under meiotic drive without viability differences.** Consider one diploid
locus with alleles `A` (`true`) and `a` (`false`) in an infinite randomly mating population with
nonoverlapping generations and no viability differences, in which heterozygotes of both sexes
transmit `A` with probability `k ∈ [0, 1]` (`k = 1/2` is Mendelian segregation).

* **Recursion.** Let heterozygotes transmit an allele drawn from `c : PMF Bool` with
  `c true = k` (`driveTransmit`), and let the newborns have genotype law `G` in Hardy–Weinberg
  proportions (`offspring G = G`), with `p` the frequency of `A` among them. Then the newborns of
  the next generation (`driveOffspring c G`) are again in Hardy–Weinberg proportions, the
  frequency of `A` among them is `p' = driveStep k p = p² + 2pqk` with `q = 1 - p`, and after
  `t` generations it is `(driveStep k)^[t] p`.
* **Change in frequency.** `p' - p = pq(2k - 1)` for every `p`.
* **Range.** `p ∈ [0, 1]` implies `p' ∈ [0, 1]`.
* **Regimes.** Let `p_t = (driveStep k)^[t] p₀` with `p₀ ∈ (0, 1)`. If `k > 1/2`, then `p_t`
  increases strictly and `p_t → 1`; if `k < 1/2`, then `p_t` decreases strictly and `p_t → 0`;
  if `k = 1/2`, then `p_t = p₀` for all `t`. -/
theorem allele_frequency_under_meiotic_drive {k : ℝ} (hk : k ∈ Icc (0 : ℝ) 1) :
    (∀ (c : PMF Bool) (G : PMF (Bool × Bool)), (c true).toReal = k → offspring G = G →
      offspring (driveOffspring c G) = driveOffspring c G ∧
        (gamete (driveOffspring c G) true).toReal = driveStep k (gamete G true).toReal ∧
        ∀ t : ℕ, (gamete ((driveOffspring c)^[t] G) true).toReal =
          (driveStep k)^[t] (gamete G true).toReal) ∧
    (∀ p : ℝ, driveStep k p - p = p * (1 - p) * (2 * k - 1)) ∧
    (∀ p ∈ Icc (0 : ℝ) 1, driveStep k p ∈ Icc (0 : ℝ) 1) ∧
    ∀ p₀ ∈ Ioo (0 : ℝ) 1,
      (1 / 2 < k → StrictMono (fun t => (driveStep k)^[t] p₀) ∧
        Tendsto (fun t => (driveStep k)^[t] p₀) atTop (𝓝 1)) ∧
      (k < 1 / 2 → StrictAnti (fun t => (driveStep k)^[t] p₀) ∧
        Tendsto (fun t => (driveStep k)^[t] p₀) atTop (𝓝 0)) ∧
      (k = 1 / 2 → ∀ t : ℕ, (driveStep k)^[t] p₀ = p₀) := by
  refine ⟨?_, driveStep_sub_self k, fun p hp => driveStep_mem_Icc hk hp, ?_⟩
  · rintro c G rfl hG
    refine ⟨(driveOffspring_hw c G).2, freq_driveOffspring hG, fun t => ?_⟩
    induction t generalizing G with
    | zero => rfl
    | succ t ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        ih _ (driveOffspring_hw c G).2, freq_driveOffspring hG]
  intro p₀ hp₀
  set s : ℕ → ℝ := fun t => (driveStep k)^[t] p₀ with hs_def
  have hs_mem : ∀ t, s t ∈ Ioo (0 : ℝ) 1 := iterate_driveStep_mem_Ioo hk hp₀
  have hs_succ : ∀ t, s (t + 1) - s t = s t * (1 - s t) * (2 * k - 1) := fun t => by
    simp only [hs_def, Function.iterate_succ_apply']
    exact driveStep_sub_self k _
  have hs_pq : ∀ t, 0 < s t * (1 - s t) := fun t =>
    mul_pos (hs_mem t).1 (by linarith [(hs_mem t).2])
  refine ⟨fun hk2 => ?_, fun hk2 => ?_, fun hk2 t => Function.iterate_fixed ?_ t⟩
  · have hmono : StrictMono s := strictMono_nat_of_lt_succ fun t => by
      have := mul_pos (hs_pq t) (by linarith : (0 : ℝ) < 2 * k - 1)
      linarith [hs_succ t]
    have hbdd : BddAbove (range s) := ⟨1, by rintro _ ⟨t, rfl⟩; exact (hs_mem t).2.le⟩
    have hlim := tendsto_atTop_ciSup hmono.monotone hbdd
    have hpos : 0 < ⨆ t, s t := lt_of_lt_of_le (hs_mem 0).1 (le_ciSup hbdd 0)
    rcases limit_eq_zero_or_one (by linarith) hlim with h | h
    · exact absurd h hpos.ne'
    · exact ⟨hmono, h ▸ hlim⟩
  · have hanti : StrictAnti s := strictAnti_nat_of_succ_lt fun t => by
      have := mul_neg_of_pos_of_neg (hs_pq t) (by linarith : 2 * k - 1 < (0 : ℝ))
      linarith [hs_succ t]
    have hbdd : BddBelow (range s) := ⟨0, by rintro _ ⟨t, rfl⟩; exact (hs_mem t).1.le⟩
    have hlim := tendsto_atTop_ciInf hanti.antitone hbdd
    have hlt : ⨅ t, s t < 1 := lt_of_le_of_lt (ciInf_le hbdd 0) (hs_mem 0).2
    rcases limit_eq_zero_or_one (by linarith) hlim with h | h
    · exact ⟨hanti, h ▸ hlim⟩
    · exact absurd h hlt.ne
  · rw [hk2]
    unfold driveStep
    ring

end MathlibExt.Biology.PopulationGenetics.Classical.MeioticDrive
