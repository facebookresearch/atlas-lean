/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.CanningsKingman
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Tests for Cannings genealogies and Kingman's coalescent

The test models are instances of the shared `Cannings.CanningsModel`, built from real masses by
`ofReal` (a `PMF.ofFintype` law).

* **Wright–Fisher** (every child picks its parent uniformly and independently, `wf N`): the
  coalescence probabilities are computed by counting parent maps, giving `c_N = 1 / N` (the
  `1 - noCoalProb N 2` of `Kingman.lean`) and `E[(ν₁)_3] = (N)_3 / N³`; the Möhle–Sagitov
  conditions hold, so the main theorem applies, including its finite-dimensional form
  (`MohleSagitov.tendsto_chainFDD`). A chain that never moves shows that `chainFDD` contains the
  law at the first observation time, and with one observation time `kingmanFDD` is `timeLaw`.
* **Moran** (exactly one parent has two offspring and every other parent at most one, children
  labeled uniformly, `moran N`): `c_N = 2 / (N (N - 1))` and `E[(ν₁)_3] = 0`, computed from the
  support of the law; the conditions hold.
* **A violating model** (`sweepMix N`): with probability `1 / N` the whole generation descends
  from a single parent, otherwise Wright–Fisher. Here `c_N → 0` still holds, but three lineages
  merge at once with probability at least `c_N / 2`, the triple-merger condition fails and the
  Möhle–Sagitov conditions do not hold (`not_mohleSagitov_sweepMix`); Kingman convergence is not
  claimed for this model (its genealogy has multiple mergers).
-/

@[expose] public section

open Finset Filter Topology

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.CanningsKingman

open MathlibExt.Biology.PopulationGenetics.Coalescent
open MathlibExt.Biology.PopulationGenetics.Coalescent.Cannings
open MathlibExt.Biology.PopulationGenetics.Coalescent.Cannings.CanningsModel
open MathlibExt.Biology.PopulationGenetics.Coalescent.CanningsKingman
open MathlibExt.Biology.PopulationGenetics.Coalescent.PartitionCoalescent

variable {N : ℕ}

/-- A Cannings model from real masses: nonnegative, summing to `1`, and unchanged by relabeling
the children and the parents. Its law is `PMF.ofFintype` of the masses. -/
noncomputable def ofReal (w : (Fin N → Fin N) → ℝ) (hw0 : ∀ f, 0 ≤ w f) (hw1 : ∑ f, w f = 1)
    (hc : ∀ (σ : Equiv.Perm (Fin N)) f, w (f ∘ σ) = w f)
    (hp : ∀ (σ : Equiv.Perm (Fin N)) f, w (σ ∘ f) = w f) : CanningsModel N where
  law := PMF.ofFintype (fun f => ENNReal.ofReal (w f)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun f _ => hw0 f, hw1, ENNReal.ofReal_one])
  law_comp_perm σ f := by simp only [PMF.ofFintype_apply, hc]
  law_perm_comp σ f := by simp only [PMF.ofFintype_apply, hp]

/-- The real masses of `ofReal w` are `w`. -/
@[simp]
theorem toReal_law_ofReal (w : (Fin N → Fin N) → ℝ) (hw0 : ∀ f, 0 ≤ w f) (hw1 : ∑ f, w f = 1)
    (hc : ∀ (σ : Equiv.Perm (Fin N)) f, w (f ∘ σ) = w f)
    (hp : ∀ (σ : Equiv.Perm (Fin N)) f, w (σ ∘ f) = w f) (f : Fin N → Fin N) :
    ((ofReal w hw0 hw1 hc hp).law f).toReal = w f :=
  ENNReal.toReal_ofReal (hw0 f)

/-- Expectations only see the support of the law. -/
theorem expect_congr_support (W : CanningsModel N) {F G : (Fin N → Fin N) → ℝ}
    (h : ∀ f, (W.law f).toReal ≠ 0 → F f = G f) : W.expect F = W.expect G := by
  unfold CanningsModel.expect
  refine sum_congr rfl fun f _ => ?_
  by_cases hf : (W.law f).toReal = 0
  · simp [hf]
  · rw [h f hf]

/-! ### Wright–Fisher -/

/-- The Wright–Fisher model: every child picks its parent uniformly and independently, so every
parent map has probability `N ^ (-N)`. -/
noncomputable def wf (N : ℕ) : CanningsModel N :=
  ofReal (fun _ => ((N : ℝ) ^ N)⁻¹) (fun _ => by positivity) (by
    rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · exact mul_inv_cancel₀ (by positivity)) (fun _ _ => rfl) (fun _ _ => rfl)

/-- Counting parent maps: `N ^ (N - m)` maps give `m + 1` given distinct children a common
parent. -/
theorem sum_allEq_wf {m : ℕ} {g : Fin (m + 1) → Fin N} (hg : Function.Injective g) :
    (∑ f : Fin N → Fin N, if ∀ i, f (g i) = f (g 0) then (1 : ℝ) else 0) = (N : ℝ) ^ (N - m) := by
  set R := univ.image g with hR_def
  have hR : #R = m + 1 := by rw [card_image_of_injective _ hg, card_univ, Fintype.card_fin]
  have hmN : m + 1 ≤ N := by simpa using Fintype.card_le_of_injective g hg
  have key : ∀ f : Fin N → Fin N, (if ∀ i, f (g i) = f (g 0) then (1 : ℝ) else 0) =
      ∑ y, ∏ c, (if c ∈ R then (if f c = y then (1 : ℝ) else 0) else 1) := by
    intro f
    have hprod : ∀ y, ∏ c, (if c ∈ R then (if f c = y then (1 : ℝ) else 0) else 1) =
        if f (g 0) = y ∧ ∀ i, f (g i) = f (g 0) then 1 else 0 := by
      intro y
      rw [← prod_filter, prod_boole]
      congr 1
      apply propext
      simp only [mem_filter, mem_univ, true_and, hR_def, mem_image, forall_exists_index,
        forall_apply_eq_imp_iff]
      constructor
      · intro hy
        exact ⟨hy 0, fun i => (hy i).trans (hy 0).symm⟩
      · rintro ⟨h0, hall⟩ i
        rw [hall i, h0]
    simp_rw [hprod]
    by_cases hA : ∀ i, f (g i) = f (g 0)
    · simp [hA]
    · simp [hA]
  rw [sum_congr rfl fun f _ => key f, sum_comm]
  have hpi : ∀ y, (∑ f : Fin N → Fin N, ∏ c, (if c ∈ R then (if f c = y then (1 : ℝ) else 0)
      else 1)) = ∏ c, ∑ z, (if c ∈ R then (if z = y then (1 : ℝ) else 0) else 1) := by
    intro y
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp_rw [hpi]
  have hin : ∀ y c, (∑ z : Fin N, (if c ∈ R then (if z = y then (1 : ℝ) else 0) else 1)) =
      if c ∈ R then 1 else (N : ℝ) := by
    intro y c
    split_ifs <;> simp
  simp_rw [hin]
  rw [prod_ite, prod_const_one, one_mul, prod_const, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hc : #(univ.filter fun c => c ∉ R) = N - (m + 1) := by
    have : (univ.filter fun c => c ∉ R) = univ \ R := by
      ext c
      simp
    rw [this, card_univ_sdiff, hR, Fintype.card_fin]
  rw [hc, ← pow_succ']
  congr 1
  omega

/-- Under Wright–Fisher, `m + 1` distinct children have a common parent with probability
`N ^ (-m)`. -/
theorem wf_expect_allEq {m : ℕ} {g : Fin (m + 1) → Fin N} (hg : Function.Injective g) :
    (wf N).expect (fun f => if ∀ i, f (g i) = f (g 0) then 1 else 0) = ((N : ℝ) ^ m)⁻¹ := by
  have hmN : m + 1 ≤ N := by simpa using Fintype.card_le_of_injective g hg
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  simp only [CanningsModel.expect, wf, toReal_law_ofReal]
  rw [← mul_sum, sum_allEq_wf hg]
  have hpow : (N : ℝ) ^ N = (N : ℝ) ^ (N - m) * (N : ℝ) ^ m := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]
  rw [hpow, mul_inv, mul_comm ((N : ℝ) ^ (N - m))⁻¹, mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero _ hN), mul_one]

/-- Wright–Fisher: `c_N = 1 / N`. -/
theorem wf_pairCoalescence (hN : 2 ≤ N) : (wf N).pairCoalescence = (N : ℝ)⁻¹ := by
  set a : Fin N := ⟨0, by omega⟩
  set b : Fin N := ⟨1, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hg : Function.Injective ![a, b] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  rw [← (wf N).expect_pair hab]
  have := wf_expect_allEq (m := 1) hg
  rw [pow_one] at this
  rw [← this]
  congr 1
  funext f
  by_cases hf : f a = f b <;> simp [Fin.forall_fin_two, hf, eq_comm]

/-- The Wright–Fisher time scale is the one of `Kingman.lean`: `c_N = 1 - noCoalProb N 2`. -/
example (hN : 2 ≤ N) : (wf N).pairCoalescence = 1 - noCoalProb N 2 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  rw [wf_pairCoalescence hN]
  simp [noCoalProb, prod_range_succ]

/-- The coalescence probability `coalProb` of the shared model, as used by `CanningsLambda`, is
the same `1 / N`. -/
example (hN : 2 ≤ N) : (wf N).coalProb = (N : ℝ)⁻¹ := by
  rw [coalProb_eq_pairCoalescence _ hN, wf_pairCoalescence hN]

/-- Wright–Fisher: three distinct children have a common parent with probability `1 / N²`. -/
theorem wf_tripleCoalescence (hN : 3 ≤ N) : (wf N).tripleCoalescence = ((N : ℝ) ^ 2)⁻¹ := by
  have hg : Function.Injective ![(⟨0, by omega⟩ : Fin N), ⟨1, by omega⟩, ⟨2, by omega⟩] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]
  rw [← (wf N).expect_triple hg]
  exact wf_expect_allEq hg

/-- Wright–Fisher: `E[(ν₁)_3] = (N)_3 / N³`. -/
theorem wf_factorialMoment_three (hN : 3 ≤ N) :
    (wf N).factorialMoment 3 = (N.descFactorial 3 : ℝ) / (N : ℝ) ^ 3 := by
  have h := wf_tripleCoalescence hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hD : (N.descFactorial 3 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.2 hN).ne'
  rw [CanningsModel.tripleCoalescence, div_eq_iff hD] at h
  have h' : (N : ℝ) ^ 2 * (N * (wf N).factorialMoment 3) = N.descFactorial 3 := by
    rw [h]
    field_simp
  rw [eq_div_iff (pow_ne_zero 3 hN0)]
  linear_combination h'

/-- **The Möhle–Sagitov conditions hold for Wright–Fisher**, verified from the definitions. -/
theorem wf_mohleSagitov : MohleSagitov wf where
  pairCoalescence_pos := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [wf_pairCoalescence hN]
    have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    positivity
  tendsto_pairCoalescence := by
    refine (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [wf_pairCoalescence hN]
    rfl
  tendsto_triple := by
    have hinv : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    refine squeeze_zero' ?_ ?_ hinv
    · filter_upwards [eventually_ge_atTop 3] with N hN
      rw [wf_factorialMoment_three hN, wf_pairCoalescence (by omega)]
      positivity
    · filter_upwards [eventually_ge_atTop 3] with N hN
      rw [wf_factorialMoment_three hN, wf_pairCoalescence (by omega)]
      have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      have hD : (N.descFactorial 3 : ℝ) ≤ (N : ℝ) ^ 3 := by
        exact_mod_cast Nat.descFactorial_le_pow N 3
      rw [show (N.descFactorial 3 : ℝ) / (N : ℝ) ^ 3 / ((N : ℝ) ^ 2 * (N : ℝ)⁻¹) =
          (N.descFactorial 3 : ℝ) / (N : ℝ) ^ 4 by field_simp]
      rw [div_le_iff₀ (by positivity)]
      calc (N.descFactorial 3 : ℝ) ≤ (N : ℝ) ^ 3 := hD
        _ = (N : ℝ)⁻¹ * (N : ℝ) ^ 4 := by field_simp

/-- Kingman's limit for Wright–Fisher, as an instance of the main theorem: after `⌊t N⌋`
generations (`⌊t / c_N⌋` with `c_N = 1 / N`), the ancestral partition of `n` genes started
from singletons has Kingman's time-`t` law in the limit. -/
example (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (π : SamplePartition n) :
    Tendsto (fun N => (ancestralMatrix (wf N) n ^ ⌊t / (wf N).pairCoalescence⌋₊) ⊥ π) atTop
      (𝓝 (timeLaw n t π)) :=
  wf_mohleSagitov.tendsto_ancestralMatrix_pow_bot n ht π

/-- Kingman's limit for Wright–Fisher in finite-dimensional distributions, as an instance of
the main theorem: started from singletons and observed at the generations `⌊t i / c_N⌋`, the
ancestral partition process has Kingman's finite-dimensional distributions in the limit. -/
example (n : ℕ) {k : ℕ} (t : Fin (k + 1) → ℝ) (ht0 : 0 ≤ t 0) (ht : Monotone t)
    (x : Fin (k + 1) → SamplePartition n) :
    Tendsto (fun N => chainFDD (ancestralMatrix (wf N) n) ⊥
        (fun i => ⌊t i / (wf N).pairCoalescence⌋₊) x) atTop (𝓝 (kingmanFDD n t x)) :=
  wf_mohleSagitov.tendsto_chainFDD n t ht0 ht x

/-! ### Finite-dimensional distributions include the initial law -/

/-- A chain that never moves, started from `0` and observed once (at time `3`) in state `1`, has
finite-dimensional distribution `0`: the law at the first observation, reached from the initial
state, is part of `chainFDD` (the transition product alone is the empty product `1`). -/
example : chainFDD (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 (k := 0) (fun _ => 3) (fun _ => 1) = 0 := by
  simp [chainFDD]

/-- With one observation time, Kingman's finite-dimensional distribution is the time-`t 0` law
from singletons. -/
example (n : ℕ) (t : Fin 1 → ℝ) (x : Fin 1 → SamplePartition n) :
    kingmanFDD n t x = timeLaw n (t 0) (x 0) := by
  simp [kingmanFDD]

/-! ### Moran -/

/-- The number of ordered pairs of distinct children with a common parent, as a natural
number. -/
def natPairCount (f : Fin N → Fin N) : ℕ := ∑ j, (offspring f j).descFactorial 2

theorem natPairCount_comp_perm (σ : Equiv.Perm (Fin N)) (f : Fin N → Fin N) :
    natPairCount (f ∘ σ) = natPairCount f := by
  simp [natPairCount, offspring_comp_perm]

theorem natPairCount_perm_comp (σ : Equiv.Perm (Fin N)) (f : Fin N → Fin N) :
    natPairCount (σ ∘ f) = natPairCount f := by
  simp only [natPairCount, offspring_perm_comp]
  exact Equiv.sum_comp σ.symm (fun j => (offspring f j).descFactorial 2)

/-- A Moran parent map for `N ≥ 2`: child `1` descends from parent `0`, every other child `c`
from parent `c`. -/
def moranMap (hN : 2 ≤ N) (c : Fin N) : Fin N := if c = ⟨1, by omega⟩ then ⟨0, by omega⟩ else c

theorem natPairCount_moranMap (hN : 2 ≤ N) : natPairCount (moranMap hN) = 2 := by
  set z : Fin N := ⟨0, by omega⟩
  set o : Fin N := ⟨1, by omega⟩
  have hzo : z ≠ o := by simp [z, o, Fin.ext_iff]
  have h0 : offspring (moranMap hN) z = 2 := by
    have : univ.filter (fun c => moranMap hN c = z) = {z, o} := by
      ext c
      rw [mem_filter, mem_insert, mem_singleton]
      simp only [mem_univ, true_and, moranMap, z, o]
      by_cases hc : c = ⟨1, by omega⟩
      · simp [hc]
      · simp [hc]
    rw [offspring, this, card_pair hzo]
  have hj : ∀ j, j ≠ z → offspring (moranMap hN) j ≤ 1 := by
    intro j hj
    rw [offspring]
    calc _ ≤ #({j} : Finset (Fin N)) := by
          refine card_le_card fun c hc => ?_
          have hc' := (mem_filter.1 hc).2
          rw [mem_singleton]
          unfold moranMap at hc'
          split_ifs at hc' with h
          · exact absurd hc'.symm hj
          · exact hc'
      _ = 1 := card_singleton j
  rw [natPairCount, sum_eq_single z]
  · rw [h0]
    rfl
  · intro j _ hjz
    exact Nat.descFactorial_eq_zero_iff_lt.2 (by have := hj j hjz; omega)
  · simp

/-- The Moran model (`N ≥ 2`): uniform over the parent maps in which exactly one ordered pair
of children, i.e. one unordered pair, shares a parent; equivalently one parent has two offspring,
one parent none, and all others one, with the children labeled uniformly at random. -/
noncomputable def moran (N : ℕ) (hN : 2 ≤ N) : CanningsModel N :=
  ofReal (fun f => if natPairCount f = 2 then (#{f : Fin N → Fin N | natPairCount f = 2} : ℝ)⁻¹
      else 0)
    (fun f => by split_ifs <;> positivity)
    (by
      rw [← sum_filter, sum_const, nsmul_eq_mul]
      refine mul_inv_cancel₀ ?_
      exact_mod_cast (card_pos.2 ⟨moranMap hN, by simp [natPairCount_moranMap hN]⟩).ne')
    (fun σ f => by simp only [natPairCount_comp_perm])
    (fun σ f => by simp only [natPairCount_perm_comp])

theorem moran_pairCount (hN : 2 ≤ N) :
    (moran N hN).expect CanningsModel.pairCount = 2 := by
  rw [expect_congr_support (moran N hN) (G := fun _ => 2), CanningsModel.expect_const]
  intro f hf
  have : natPairCount f = 2 := by
    by_contra h
    exact hf (by simp [moran, h])
  simp only [CanningsModel.pairCount]
  have h2 : ((natPairCount f : ℕ) : ℝ) = 2 := by rw [this]; rfl
  simpa [natPairCount] using h2

theorem moran_tripleCount (hN : 2 ≤ N) :
    (moran N hN).expect CanningsModel.tripleCount = 0 := by
  rw [expect_congr_support (moran N hN) (G := fun _ => 0), CanningsModel.expect_const]
  intro f hf
  have hpc : natPairCount f = 2 := by
    by_contra h
    exact hf (by simp [moran, h])
  simp only [CanningsModel.tripleCount]
  refine sum_eq_zero fun j _ => ?_
  have hle : (offspring f j).descFactorial 2 ≤ 2 := by
    calc (offspring f j).descFactorial 2 ≤ natPairCount f :=
          single_le_sum (f := fun j => (offspring f j).descFactorial 2)
            (fun _ _ => Nat.zero_le _) (mem_univ j)
      _ = 2 := hpc
  have h3 : offspring f j < 3 := by
    by_contra h
    obtain ⟨k, hk⟩ : ∃ k, offspring f j = k + 3 := ⟨offspring f j - 3, by omega⟩
    have e : (k + 3).descFactorial 2 = (k + 2) * (k + 3) := by simp [Nat.descFactorial_succ]
    rw [hk, e] at hle
    nlinarith
  exact_mod_cast Nat.descFactorial_eq_zero_iff_lt.2 h3

/-- Moran: `c_N = 2 / (N (N - 1))`. -/
theorem moran_pairCoalescence (hN : 2 ≤ N) :
    (moran N hN).pairCoalescence = 2 / ((N : ℝ) * (N - 1)) := by
  have h := (moran N hN).natCast_mul_factorialMoment 2
  rw [show (fun f => ∑ j, ((offspring f j).descFactorial 2 : ℝ)) = CanningsModel.pairCount
    from rfl, moran_pairCount hN] at h
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hN1 : (N : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  rw [CanningsModel.pairCoalescence, eq_div_iff (mul_ne_zero hN0 hN1)]
  field_simp
  linear_combination h

/-- Moran: no parent has three offspring, `E[(ν₁)_3] = 0`. -/
theorem moran_factorialMoment_three (hN : 2 ≤ N) : (moran N hN).factorialMoment 3 = 0 := by
  have h := (moran N hN).natCast_mul_factorialMoment 3
  rw [show (fun f => ∑ j, ((offspring f j).descFactorial 3 : ℝ)) = CanningsModel.tripleCount
    from rfl, moran_tripleCount hN] at h
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  exact (mul_eq_zero.1 h).resolve_left hN0

/-- The Moran sequence (Wright–Fisher below `N = 2`, where no Moran map exists). -/
noncomputable def moranSeq (N : ℕ) : CanningsModel N :=
  if hN : 2 ≤ N then moran N hN else wf N

theorem moranSeq_eq (hN : 2 ≤ N) : moranSeq N = moran N hN := by
  simp [moranSeq, hN]

/-- **The Möhle–Sagitov conditions hold for the Moran model.** -/
theorem moran_mohleSagitov : MohleSagitov moranSeq where
  pairCoalescence_pos := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [moranSeq_eq hN, moran_pairCoalescence hN]
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have : (0 : ℝ) < N * (N - 1) := by nlinarith
    positivity
  tendsto_pairCoalescence := by
    have hg : Tendsto (fun N : ℕ => (N : ℝ) * ((N : ℝ) - 1)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_atTop₀
        (tendsto_atTop_add_const_right _ (-1) tendsto_natCast_atTop_atTop)
    have h := (tendsto_const_nhds (x := (2 : ℝ))).div_atTop hg
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [moranSeq_eq hN, moran_pairCoalescence hN]
  tendsto_triple := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [moranSeq_eq hN, moran_factorialMoment_three hN, zero_div]

/-! ### A model violating the conditions: total sweeps -/

/-- Total sweep: the whole generation descends from a single parent, chosen uniformly. -/
noncomputable def sweep (N : ℕ) : CanningsModel N :=
  ofReal (fun f => if ∀ a b, f a = f b then (#{f : Fin N → Fin N | ∀ a b, f a = f b} : ℝ)⁻¹
      else 0)
    (fun f => by split_ifs <;> positivity)
    (by
      rw [← sum_filter, sum_const, nsmul_eq_mul]
      refine mul_inv_cancel₀ ?_
      have hex : ∃ f : Fin N → Fin N, ∀ a b, f a = f b := by
        rcases N with _ | N
        · exact ⟨id, fun a => a.elim0⟩
        · exact ⟨fun _ => 0, fun _ _ => rfl⟩
      obtain ⟨f₀, hf₀⟩ := hex
      exact_mod_cast (card_pos.2 ⟨f₀, mem_filter.2 ⟨mem_univ _, hf₀⟩⟩).ne')
    (fun σ f => by
      have : (∀ a b, (f ∘ σ) a = (f ∘ σ) b) ↔ ∀ a b, f a = f b := by
        constructor
        · intro h a b
          simpa using h (σ.symm a) (σ.symm b)
        · intro h a b
          exact h _ _
      simp only [this])
    (fun σ f => by
      have : (∀ a b, (σ ∘ f) a = (σ ∘ f) b) ↔ ∀ a b, f a = f b := by
        simp [σ.injective.eq_iff]
      simp only [this])

/-- Under a total sweep every sample of children has a common parent. -/
theorem sweep_expect_allEq {m : ℕ} (g : Fin (m + 1) → Fin N) :
    (sweep N).expect (fun f => if ∀ i, f (g i) = f (g 0) then 1 else 0) = 1 := by
  rw [expect_congr_support (sweep N) (G := fun _ => 1), CanningsModel.expect_const]
  intro f hf
  have hc : ∀ a b, f a = f b := by
    by_contra h
    exact hf (by simp [sweep, h])
  simp [hc _ (g 0)]

/-- Mixing two Cannings models with weights `1 - p` and `p`. -/
noncomputable def mix (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (W₁ W₂ : CanningsModel N) :
    CanningsModel N :=
  ofReal (fun f => (1 - p) * (W₁.law f).toReal + p * (W₂.law f).toReal)
    (fun f => add_nonneg (mul_nonneg (by linarith) ENNReal.toReal_nonneg)
      (mul_nonneg hp0 ENNReal.toReal_nonneg))
    (by rw [sum_add_distrib, ← mul_sum, ← mul_sum, W₁.sum_toReal_law, W₂.sum_toReal_law]; ring)
    (fun σ f => by simp only [W₁.law_comp_perm, W₂.law_comp_perm])
    (fun σ f => by simp only [W₁.law_perm_comp, W₂.law_perm_comp])

theorem expect_mix (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (W₁ W₂ : CanningsModel N)
    (F : (Fin N → Fin N) → ℝ) :
    (mix p hp0 hp1 W₁ W₂).expect F = (1 - p) * W₁.expect F + p * W₂.expect F := by
  simp only [CanningsModel.expect, mix, toReal_law_ofReal, add_mul, sum_add_distrib, mul_sum,
    mul_assoc]

/-- With probability `1 / N` a total sweep, otherwise a Wright–Fisher generation. -/
noncomputable def sweepMix (N : ℕ) : CanningsModel N :=
  mix (N : ℝ)⁻¹ (by positivity) (Nat.cast_inv_le_one N) (wf N) (sweep N)

/-- In the sweep mixture, `m + 1` distinct children have a common parent with probability
`(1 - 1/N) N^(-m) + 1/N`. -/
theorem sweepMix_expect_allEq {m : ℕ} {g : Fin (m + 1) → Fin N} (hg : Function.Injective g) :
    (sweepMix N).expect (fun f => if ∀ i, f (g i) = f (g 0) then 1 else 0) =
      (1 - (N : ℝ)⁻¹) * ((N : ℝ) ^ m)⁻¹ + (N : ℝ)⁻¹ := by
  rw [sweepMix, expect_mix, wf_expect_allEq hg, sweep_expect_allEq, mul_one]

theorem sweepMix_pairCoalescence (hN : 2 ≤ N) :
    (sweepMix N).pairCoalescence = (2 * N - 1) / (N : ℝ) ^ 2 := by
  set a : Fin N := ⟨0, by omega⟩
  set b : Fin N := ⟨1, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hg : Function.Injective ![a, b] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  rw [← (sweepMix N).expect_pair hab]
  have := sweepMix_expect_allEq (m := 1) hg
  rw [show (fun f : Fin N → Fin N => if f a = f b then (1 : ℝ) else 0) =
      fun f => if ∀ i, f (![a, b] i) = f (![a, b] 0) then 1 else 0 by
    funext f
    by_cases hf : f a = f b <;> simp [Fin.forall_fin_two, hf, eq_comm], this]
  field_simp
  ring

theorem sweepMix_tripleCoalescence (hN : 3 ≤ N) :
    (sweepMix N).tripleCoalescence = (N ^ 2 + N - 1) / (N : ℝ) ^ 3 := by
  have hg : Function.Injective ![(⟨0, by omega⟩ : Fin N), ⟨1, by omega⟩, ⟨2, by omega⟩] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  rw [← (sweepMix N).expect_triple hg, sweepMix_expect_allEq hg]
  field_simp
  ring

/-- **Multiple mergers are not negligible**: three lineages merge at once with probability at
least half the pair-coalescence probability. -/
theorem sweepMix_triple_ge (hN : 3 ≤ N) :
    (sweepMix N).pairCoalescence / 2 ≤ (sweepMix N).tripleCoalescence := by
  rw [sweepMix_pairCoalescence (by omega), sweepMix_tripleCoalescence hN]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have : (3 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith [sq_nonneg (N : ℝ)]

/-- The pair-coalescence condition `c_N → 0` holds for the sweep mixture. -/
theorem sweepMix_tendsto_pairCoalescence :
    Tendsto (fun N => (sweepMix N).pairCoalescence) atTop (𝓝 0) := by
  have hinv : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h := (hinv.const_mul 2).sub (hinv.pow 2)
  have h0 : (2 : ℝ) * 0 - 0 ^ 2 = 0 := by norm_num
  rw [h0] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [sweepMix_pairCoalescence hN]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  field_simp

/-- **The sweep mixture violates the Möhle–Sagitov conditions**: the triple-merger ratio
`E[(ν₁)_3] / (N² c_N)` stays above `1/8`. Kingman convergence is not claimed for it. -/
theorem not_mohleSagitov_sweepMix : ¬MohleSagitov sweepMix := by
  intro hW
  have hev : ∀ᶠ N in atTop,
      (1 : ℝ) / 8 ≤
        (sweepMix N).factorialMoment 3 / ((N : ℝ) ^ 2 * (sweepMix N).pairCoalescence) := by
    filter_upwards [eventually_ge_atTop 4] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have h4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
    have hD : (N.descFactorial 3 : ℝ) = N * (N - 1) * (N - 2) := by
      rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_one]
      push_cast [Nat.cast_sub (by omega : 2 ≤ N), Nat.cast_sub (by omega : 1 ≤ N)]
      ring
    have hDpos : (0 : ℝ) < N.descFactorial 3 := by exact_mod_cast Nat.descFactorial_pos.2 (by omega)
    have hμ : (sweepMix N).factorialMoment 3 =
        (N.descFactorial 3 : ℝ) * ((N ^ 2 + N - 1) / (N : ℝ) ^ 3) / N := by
      have h := sweepMix_tripleCoalescence (N := N) (by omega)
      rw [CanningsModel.tripleCoalescence, div_eq_iff hDpos.ne'] at h
      rw [eq_div_iff hN0.ne']
      linear_combination h
    have h2N : (0 : ℝ) < 2 * N - 1 := by linarith
    have hr : (sweepMix N).factorialMoment 3 / ((N : ℝ) ^ 2 * (sweepMix N).pairCoalescence) =
        (N - 1) * (N - 2) * (N ^ 2 + N - 1) / ((N : ℝ) ^ 3 * (2 * N - 1)) := by
      rw [hμ, sweepMix_pairCoalescence (by omega), hD]
      field_simp
    rw [hr, le_div_iff₀ (mul_pos (by positivity) h2N)]
    have h4' : (0 : ℝ) ≤ N - 4 := by linarith
    nlinarith [mul_nonneg h4' (pow_nonneg hN0.le 3), mul_nonneg h4' (pow_nonneg hN0.le 2)]
  have hlt := hW.tendsto_triple.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
  obtain ⟨N, hN1, hN2⟩ := (hev.and hlt).exists
  linarith

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.CanningsKingman
