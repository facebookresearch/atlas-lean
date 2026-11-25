/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ChineseRestaurant
public import Domains.Biology.PopulationGenetics.Ewens

/-!
# The allelic partition of the Chinese restaurant process

The Chinese restaurant process with parameter `θ > 0` builds a random set partition of the
customers `Fin n` one customer at a time (Aldous 1985, §11; Pitman 2006, ch. 3). Customer `0`
sits alone; when customers `0, …, m - 1` are seated, customer `m` joins an occupied table `B`
with probability `|B| / (m + θ)` and opens a new table with probability `θ / (m + θ)`. The
tables after `n` customers form a partition of `Fin n`; in Hoppe's urn (Hoppe 1984) the
customers are genes and the tables are allelic classes under the neutral infinite-alleles
model with scaled mutation rate `θ = 4Nu`.

The process and its exchangeability and consistency laws are developed in
`MathlibExt.Probability.ChineseRestaurant`. Here its block sizes are identified with the Hoppe urn
and the Ewens sampling formula.

## Main results

* `ChineseRestaurant.crp_map_blockSizes_eq_hoppeLaw`,
  `ChineseRestaurant.crp_map_blockSizes`: the block sizes follow Hoppe's urn and the Ewens
  sampling formula.
* `ChineseRestaurant.sum_crp_toReal_mul_card_parts`: the expected number of tables is
  `∑_{i < n} θ / (θ + i)`.

## References

* D. J. Aldous, *Exchangeability and related topics*, École d'Été de Probabilités de
  Saint-Flour XIII (1983), Lecture Notes in Math. 1117 (1985), §11.
* J. Pitman, *Combinatorial Stochastic Processes*, Lecture Notes in Math. 1875 (2006), ch. 3.
* W. J. Ewens, *The sampling theory of selectively neutral alleles*, Theor. Popul. Biol. 3
  (1972), 87–112.
* F. M. Hoppe, *Pólya-like urns and the Ewens sampling formula*, J. Math. Biol. 20 (1984),
  91–94.
-/

@[expose] public section

noncomputable section

open Finset

namespace MathlibExt.Biology.PopulationGenetics.ChineseRestaurant

open Ewens

/-- Lumpability: the seating step, read through `blockSizes`, is Hoppe's urn. -/
private lemma sum_seatWeight_blockSizes (θ : ℝ) {n : ℕ}
    (π : Finpartition (univ : Finset (Fin n))) (q : (n + 1).Partition) :
    ∑ c, (if q = blockSizes (seat π c) then seatWeight θ π c else 0) =
      hoppeStep θ (blockSizes π) q := by
  classical
  rw [Fintype.sum_option, hoppeStep]
  congr 1
  · simp only [seat, seatWeight, Nat.Partition.ext_iff, blockSizes_newTable, add_comm]
  · let g : ℕ → ℝ := fun j ↦
      if q.parts = (j + 1) ::ₘ (blockSizes π).parts.erase j then j / (n + θ) else 0
    have hterm : ∀ B : π.parts,
        (if q = blockSizes (seat π (some B)) then seatWeight θ π (some B) else 0) =
          g #B.1 := by
      rintro ⟨B, hB⟩
      simp only [seat, seatWeight, Nat.Partition.ext_iff, blockSizes_joinTable, g]
    rw [Fintype.sum_congr _ _ hterm, sum_coe_sort π.parts (fun B ↦ g #B), ← sum_map_val,
      show (π.parts.val.map fun B ↦ g #B) = (π.parts.val.map card).map g by
        rw [Multiset.map_map]; rfl]
    change ((blockSizes π).parts.map g).sum = _
    rw [sum_multiset_map_count]
    refine sum_congr rfl fun j _ ↦ ?_
    simp only [g, nsmul_eq_mul]
    split_ifs
    · rw [add_comm (n : ℝ) θ]
      ring
    · simp

/-- **The block sizes follow Hoppe's urn**: the law of the multiset of block sizes after `n`
customers is the law `Ewens.hoppeLaw` of Hoppe's urn on allelic partitions after `n` draws. -/
theorem crp_map_blockSizes_eq_hoppeLaw {θ : ℝ} (hθ : 0 < θ) {n : ℕ} (p : n.Partition) :
    (crp θ hθ n).map blockSizes p = ENNReal.ofReal (hoppeLaw θ n p) := by
  induction n with
  | zero =>
    change (PMF.pure ⊥).map blockSizes p = _
    rw [PMF.pure_map, Subsingleton.elim p (blockSizes ⊥), PMF.pure_apply_self]
    simp [hoppeLaw]
  | succ n ih =>
    have hstep : ∀ π : Finpartition (univ : Finset (Fin n)),
        (crpStep θ hθ π).map blockSizes p =
          ENNReal.ofReal (hoppeStep θ (blockSizes π) p) := by
      intro π
      rw [crpStep, PMF.map_comp, PMF.map_apply, tsum_fintype,
        ← sum_seatWeight_blockSizes θ π p, ENNReal.ofReal_sum_of_nonneg]
      · refine sum_congr rfl fun c _ ↦ ?_
        simp only [Function.comp_apply, seatChoice, PMF.ofFintype_apply]
        split_ifs <;> simp
      · intro c _
        split_ifs
        · exact seatWeight_nonneg hθ π c
        · exact le_rfl
    change ((crp θ hθ n).bind (crpStep θ hθ)).map blockSizes p = _
    rw [PMF.map_bind, PMF.bind_apply, tsum_fintype]
    simp_rw [hstep]
    have hlaw : hoppeLaw θ (n + 1) p = ∑ l : n.Partition, hoppeLaw θ n l * hoppeStep θ l p := rfl
    rw [hlaw, ENNReal.ofReal_sum_of_nonneg fun l _ ↦
      mul_nonneg (hoppeLaw_nonneg hθ l) (hoppeStep_nonneg hθ l p)]
    simp_rw [ENNReal.ofReal_mul (hoppeLaw_nonneg hθ _), ← ih, PMF.map_apply, tsum_fintype,
      sum_mul, ite_mul, zero_mul]
    rw [sum_comm]
    refine sum_congr rfl fun π _ ↦ ?_
    rw [sum_ite_eq']
    simp

/-- **The allelic partition of the Chinese restaurant process follows the Ewens sampling
formula** (Ewens 1972; Hoppe 1984): the multiset of block sizes after `n` customers has law
`Ewens.ewensProb θ`. -/
theorem crp_map_blockSizes {θ : ℝ} (hθ : 0 < θ) {n : ℕ} (p : n.Partition) :
    (crp θ hθ n).map blockSizes p = ENNReal.ofReal (ewensProb θ p) := by
  rw [crp_map_blockSizes_eq_hoppeLaw hθ, hoppeLaw_eq_ewensProb hθ]

/-- **Expected number of tables** (expected number of alleles in a sample of `n` genes,
Ewens 1972): `E[|π|] = ∑_{i < n} θ / (θ + i)`. -/
theorem sum_crp_toReal_mul_card_parts {θ : ℝ} (hθ : 0 < θ) (n : ℕ) :
    ∑ π : Finpartition (univ : Finset (Fin n)), (crp θ hθ n π).toReal * #π.parts =
      ∑ i ∈ range n, θ / (θ + i) := by
  have hcard : ∀ π : Finpartition (univ : Finset (Fin n)),
      ((blockSizes π).parts.card : ℝ) = #π.parts := fun π ↦ by
    simp [blockSizes]
  calc
    _ = ∑ π : Finpartition (univ : Finset (Fin n)), ∑ p : n.Partition,
        if p = blockSizes π then (crp θ hθ n π).toReal * (p.parts.card : ℝ) else 0 := by
      refine sum_congr rfl fun π _ ↦ ?_
      rw [sum_ite_eq']
      simp [hcard]
    _ = ∑ p : n.Partition, (∑ π : Finpartition (univ : Finset (Fin n)),
        if p = blockSizes π then (crp θ hθ n π).toReal else 0) * (p.parts.card : ℝ) := by
      rw [sum_comm]
      refine sum_congr rfl fun p _ ↦ ?_
      rw [sum_mul]
      refine sum_congr rfl fun π _ ↦ ?_
      split_ifs <;> simp
    _ = ∑ p : n.Partition, ewensProb θ p * (p.parts.card : ℝ) := by
      refine sum_congr rfl fun p _ ↦ ?_
      rw [← ENNReal.toReal_ofReal (ewensProb_nonneg hθ p), ← crp_map_blockSizes hθ,
        PMF.map_apply, tsum_fintype, ENNReal.toReal_sum fun π _ ↦ ?_]
      · congr 1
        refine sum_congr rfl fun π _ ↦ ?_
        split_ifs <;> simp
      · split_ifs
        · exact PMF.apply_ne_top _ _
        · exact ENNReal.zero_ne_top
    _ = _ := sum_ewensProb_mul_card_parts θ hθ n

end MathlibExt.Biology.PopulationGenetics.ChineseRestaurant
