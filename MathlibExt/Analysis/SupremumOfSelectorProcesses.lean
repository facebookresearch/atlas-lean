/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Analysis/SupremumOfSelectorProcesses.lean` (leanprover/lean-eval, revision
38361be884302c7edce1908c4aef8296eb2cb27e), based on
`AnnalsChallenge/AnnalsOfMathematics/2024-199-3-SupremumOfSelectorProcesses.lean` (v1.0.0).
Copyright (c) 2025 David Ledvinka. All rights reserved.
Copyright 2026 Lean FRO, LLC.
Authors: David Ledvinka (lean-eval submission).
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).

The adapted portions are the binomial subset measure, the definition of a small family, and
the statement of the selector-process theorem. ATLAS moved these declarations here from
`WantedExt/Analysis/SupremumOfSelectorProcessesWanted.lean` with the same names and statements.

Unless required by applicable law or agreed to in writing, software distributed under the
License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
either express or implied. See the License for the specific language governing permissions
and limitations under the License. lean-eval ships no `NOTICE` file.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Distributions.SetBernoulli

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Sigma
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Topology.Order.Compact

/-!
# The Park–Pham theorem on selector processes

A tail at a universal multiple of the expected supremum of a selector process is a small
family. The proof constructs a cover using minimal fragments of weight witnesses,
counts the fragments under an enlarged Bernoulli sample, and applies Markov's inequality.
-/

open Finset MeasureTheory ProbabilityTheory unitInterval
open scoped BigOperators NNReal ENNReal

namespace MathlibExt.Analysis.SupremumOfSelectorProcessesWanted
namespace SupremumOfSelectorProcesses

@[expose] public section

/-- **Binomial random subset.** For a type $X$ and $p \in [0, 1]$, the binomial random subset
distribution on $X$ with parameter $p$ is the probability measure on the subsets of $X$ under
which each element of $X$ belongs to the random subset independently with probability $p$. A
random subset with this law is denoted $X_p$. -/
noncomputable def binomialSetDistribution (X : Type*) (p : I) : Measure (Set X) :=
  setBernoulli Set.univ p

open Classical in
/-- **$p$-small families of sets.** Let $X$ be a finite type and $p \in [0, 1]$. A family
$\mathcal{F}$ of subsets of $X$ is $p$-small when there is a family $\mathcal{G}$ of subsets of
$X$ such that every member of $\mathcal{F}$ contains some member of $\mathcal{G}$ and
$\sum_{S \in \mathcal{G}} p^{|S|} \le 1/2$. -/
def IsSmall {X : Type*} [Fintype X] (p : I) (𝓕 : Set (Set X)) : Prop :=
  ∃ 𝓖 : Set (Set X), 𝓕 ⊆ ⋃ s ∈ 𝓖, {t | s ⊆ t} ∧
    (∑ s ∈ 𝓖, (p : ℝ) ^ s.ncard ≤ 2⁻¹)

end

namespace theorem_1_2

variable {X : Type*} [Fintype X] [DecidableEq X]

private def capSum (w : X → ℝ) (a : ℝ) (A : Finset X) : ℝ :=
  ∑ i ∈ A, min (w i) a

private noncomputable def heavy (w : X → ℝ) (a : ℝ) : Finset X :=
  univ.filter fun i ↦ a < w i

omit [Fintype X] in
private lemma capSum_add_of_disjoint (w : X → ℝ) (a : ℝ) {A B : Finset X}
    (hd : Disjoint A B) : capSum w a (A ∪ B) = capSum w a A + capSum w a B :=
  sum_union hd

omit [Fintype X] [DecidableEq X] in
private lemma capSum_le (w : X → ℝ) (a : ℝ) (A : Finset X) :
    capSum w a A ≤ A.card * a := by
  simpa [capSum] using sum_le_sum (s := A) (fun i _ ↦ min_le_right (w i) a)

omit [DecidableEq X] in
private lemma capSum_eq (w : X → ℝ) (a : ℝ) {A : Finset X} (hA : A ⊆ heavy w a) :
    capSum w a A = A.card * a := by
  unfold capSum
  rw [sum_eq_card_nsmul (b := a), nsmul_eq_mul]
  intro i hi
  exact min_eq_right (le_of_lt (by simpa [heavy] using hA hi))

private lemma capSum_step (w : X → ℝ) (A : Finset X) {a b : ℝ} (hab : a ≤ b)
    (hb : ∀ i ∈ heavy w a, b ≤ w i) :
    capSum w b A = capSum w a A + (A ∩ heavy w a).card * (b - a) := by
  classical
  have h i : min (w i) b = min (w i) a + if i ∈ heavy w a then b - a else 0 := by
    by_cases hi : i ∈ heavy w a
    · have hia : a ≤ w i := hab.trans (hb i hi)
      rw [ite_eq_left hi, min_eq_right (hb i hi), min_eq_right hia]
      ring
    · have hia : w i ≤ a := le_of_not_gt (by simpa [heavy] using hi)
      simp [hi, min_eq_left hia, min_eq_left (hia.trans hab)]
  simp_rw [capSum, h, sum_add_distrib]
  have hfilter : A.filter (· ∈ heavy w a) = A ∩ heavy w a := by
    ext i
    simp
  rw [← sum_filter, hfilter, sum_const, nsmul_eq_mul]

-- At the greatest feasible cutoff, increasing the cutoff makes the inequality fail.
-- Up to the next weight this change is linear, with slope given by the two cardinalities.
private lemma improve_cutoff (w : X → ℝ) (W : Finset X) (hw : ∀ i, 0 ≤ w i)
    (hbad : 2 * (∑ i ∈ W, w i) < ∑ i, w i)
    {a₀ : ℝ} (h₀ : capSum w a₀ univ ≤ 2 * capSum w a₀ W) :
    ∃ a ≥ a₀, capSum w a univ ≤ 2 * capSum w a W ∧
      (heavy w a).card ≤ 2 * ((heavy w a) \ W).card ∧
      ((heavy w a) \ W).Nonempty := by
  classical
  let M := ∑ i, w i
  have hM i : w i ≤ M := single_le_sum (fun j _ ↦ hw j) (mem_univ i)
  have hn a (ha : M ≤ a) : ¬ capSum w a univ ≤ 2 * capSum w a W := by
    simpa only [capSum, min_eq_left ((hM _).trans ha)] using not_le_of_gt hbad
  have haM : a₀ < M := lt_of_not_ge fun ha ↦ hn a₀ ha h₀
  let K := {a | capSum w a univ ≤ 2 * capSum w a W} ∩ Set.Icc a₀ M
  have hcont (A : Finset X) : Continuous fun a ↦ capSum w a A := by
    unfold capSum
    exact continuous_finsetSum _ fun i _ ↦ continuous_const.min continuous_id
  have hK : IsCompact K :=
    isCompact_Icc.inter_left (isClosed_le (hcont univ) (continuous_const.mul (hcont W)))
  obtain ⟨a, ha, hamax⟩ := hK.exists_isGreatest ⟨a₀, h₀, le_rfl, haM.le⟩
  have haM' : a < M := lt_of_not_ge fun hh ↦ hn a hh ha.1
  let B := insert M ((heavy w a).image w)
  have hB : B.Nonempty := ⟨M, mem_insert_self _ _⟩
  let b := B.min' hB
  have hb : a < b := by
    have hm : b ∈ B := min'_mem B hB
    simp only [B, mem_insert, mem_image, heavy, mem_filter, mem_univ, true_and] at hm
    rcases hm with h | ⟨i, hi, h⟩
    · exact h.symm ▸ haM'
    · exact h ▸ hi
  have hbM : b ≤ M := min'_le B _ (mem_insert_self _ _)
  have hbw i (hi : i ∈ heavy w a) : b ≤ w i :=
    min'_le B _ (mem_insert_of_mem (mem_image_of_mem _ hi))
  have hb' : ¬ capSum w b univ ≤ 2 * capSum w b W :=
    fun h ↦ (not_le_of_gt hb) (hamax ⟨h, ha.2.1.trans hb.le, hbM⟩)
  rw [capSum_step w univ hb.le hbw, capSum_step w W hb.le hbw, univ_inter] at hb'
  have hcard : 2 * (W ∩ heavy w a).card < (heavy w a).card := by
    by_contra! h
    have h' : ((heavy w a).card : ℝ) ≤ 2 * (W ∩ heavy w a).card := by exact_mod_cast h
    have hmul := mul_le_mul_of_nonneg_right h' (sub_nonneg.mpr hb.le)
    have hcapA : capSum w a univ ≤ 2 * capSum w a W := ha.1
    exact hb' (by linarith only [add_le_add hcapA hmul])
  have hparts : ((heavy w a) \ W).card + (W ∩ heavy w a).card = (heavy w a).card := by
    rw [inter_comm, card_sdiff_add_card_inter]
  refine ⟨a, ha.2.1, ha.1, by omega, ?_⟩
  exact card_pos.mp (by omega)

variable (F : Finset (Finset X)) (w : Finset X → X → ℝ)

private def completion (W S T : Finset X) : Prop :=
  T ⊆ S \ W ∧ ∃ U ∈ F, ∃ a ≥ 0,
    heavy (w U) a \ W = T ∧ capSum (w U) a univ ≤ 2 * capSum (w U) a W

private noncomputable def fragments (W : Finset X) : Finset (Finset X) := by
  classical
  exact univ.filter fun T ↦
    ∃ S ∈ F, completion F w W S T ∧ ∀ T', completion F w W S T' → T.card ≤ T'.card

private lemma fragments_cover (hw : ∀ S i, 0 ≤ w S i) (hsupp : ∀ S i, i ∉ S → w S i = 0)
    (W : Finset X) {S : Finset X} (hS : S ∈ F) :
    ∃ T ∈ fragments F w W, T ⊆ S := by
  classical
  have h₀ : completion F w W S (heavy (w S) 0 \ W) := by
    refine ⟨sdiff_subset_sdiff ?_ (Subset.refl _), S, hS, 0, le_rfl, rfl, ?_⟩
    · intro i hi
      by_contra hn
      simp [heavy, hsupp S i hn] at hi
    · simp [capSum, min_eq_right (hw S _)]
  let candidates := univ.filter (completion F w W S)
  have hc : candidates.Nonempty := ⟨_, mem_filter.mpr ⟨mem_univ _, h₀⟩⟩
  obtain ⟨T, hT, hmin⟩ := candidates.exists_min_image card hc
  refine ⟨T, mem_filter.mpr ⟨mem_univ _, S, hS, (mem_filter.mp hT).2, ?_⟩,
    (mem_filter.mp hT).2.1.trans sdiff_subset⟩
  exact fun T' ht' ↦ hmin T' (mem_filter.mpr ⟨mem_univ _, ht'⟩)

private def encodes (Z : Finset X) (k : ℕ) (P : Finset X) : Prop :=
  P ⊆ Z ∧ P.card ≤ 2 * k ∧ ∃ U ∈ F, ∃ a ≥ 0,
    heavy (w U) a = P ∧
    capSum (w U) a univ + 2 * k * a ≤ 2 * capSum (w U) a Z

private noncomputable def canonical (Z : Finset X) (k : ℕ) : Finset X := by
  classical
  exact if h : ∃ P, encodes F w Z k P then h.choose else ∅

omit [DecidableEq X] in
private lemma canonical_card (Z : Finset X) (k : ℕ) :
    (canonical F w Z k).card ≤ 2 * k := by
  classical
  by_cases h : ∃ P, encodes F w Z k P
  · simpa [canonical, h] using h.choose_spec.2.1
  · simp [canonical, h]

private lemma fragment_encoding (hw : ∀ S i, 0 ≤ w S i) {W T : Finset X}
    (hbad : ∀ S ∈ F, 2 * (∑ i ∈ W, w S i) < ∑ i, w S i)
    (hT : T ∈ fragments F w W) :
    Disjoint W T ∧ T.Nonempty ∧ T ⊆ canonical F w (W ∪ T) T.card := by
  classical
  obtain ⟨S, _, ⟨hsub, U, hU, a₀, ha₀, hr, h₀⟩, hmin⟩ := (mem_filter.mp hT).2
  have hd : Disjoint W T :=
    disjoint_sdiff_self_right.mono_right hsub
  obtain ⟨a, haa, hac, hap, hne⟩ := improve_cutoff (w U) W (hw U) (hbad U hU) h₀
  have hsm : heavy (w U) a \ W ⊆ T := by
    rw [← hr]
    apply sdiff_subset_sdiff _ (Subset.refl _)
    intro i hi
    have hi' : a < w U i := by simpa [heavy] using hi
    simp [heavy, haa.trans_lt hi']
  have heq : heavy (w U) a \ W = T :=
    eq_of_subset_of_card_le hsm (hmin _ ⟨hsm.trans hsub, U, hU, a, ha₀.trans haa, rfl, hac⟩)
  -- Moving from W to W ∪ T adds exactly |T| a to the capped weight.
  have hc : ∃ P, encodes F w (W ∪ T) T.card P := by
    refine ⟨heavy (w U) a, ?_, heq ▸ hap, U, hU, a, ha₀.trans haa, rfl, ?_⟩
    · intro i hi
      by_cases hw' : i ∈ W
      · exact mem_union_left _ hw'
      · exact mem_union_right _ (heq ▸ mem_sdiff.mpr ⟨hi, hw'⟩)
    · have ht : T ⊆ heavy (w U) a := by rw [← heq]; exact sdiff_subset
      rw [capSum_add_of_disjoint _ _ hd, capSum_eq _ _ ht]
      linarith
  have hcs : encodes F w (W ∪ T) T.card (canonical F w (W ∪ T) T.card) := by
    simpa only [canonical, dite_eq_left hc] using hc.choose_spec
  obtain ⟨hP, _, V, hV, b, hb, hPb, hcap⟩ := hcs
  have ht' : heavy (w V) b \ W ⊆ T := by
    intro i hi
    have hi' := hP (hPb ▸ (mem_sdiff.mp hi).1)
    exact (mem_union.mp hi').resolve_left (mem_sdiff.mp hi).2
  -- For a canonical certificate, removing T costs at most |T| b in capped weight.
  -- The resulting fragment is contained in T and hence equals T by minimality.
  have hcap' : capSum (w V) b univ ≤ 2 * capSum (w V) b W := by
    rw [capSum_add_of_disjoint _ _ hd] at hcap
    linarith [capSum_le (w V) b T]
  have heq' := eq_of_subset_of_card_le ht'
    (hmin _ ⟨ht'.trans hsub, V, hV, b, hb, rfl, hcap'⟩)
  refine ⟨hd, heq ▸ hne, ?_⟩
  exact heq'.symm.subset.trans (sdiff_subset.trans hPb.subset)

private def mass (q : ℝ) (W : Finset X) : ℝ :=
  q ^ W.card * (1 - q) ^ (Fintype.card X - W.card)

omit [DecidableEq X] in
private lemma mass_nonneg {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (W : Finset X) :
    0 ≤ mass q W :=
  mul_nonneg (pow_nonneg hq₀ _) (pow_nonneg (sub_nonneg.mpr hq₁) _)

private lemma mass_weight (p : ℝ) {q : ℝ} (hq : 0 < q) {W T : Finset X}
    (h : Disjoint W T) :
    mass q W * p ^ T.card = mass q (W ∪ T) * (p * (1 - q) / q) ^ T.card := by
  have hu := card_union_of_disjoint h
  have hcard : (Fintype.card X - (W ∪ T).card) + T.card =
      Fintype.card X - W.card := by
    have := card_le_univ (s := W ∪ T)
    omega
  unfold mass
  rw [← hcard, pow_add (1 - q), hu, pow_add q, div_pow, mul_pow]
  field_simp

-- Replacing W by W ∪ T in the Bernoulli mass pays for the p-cost of each fragment.
-- For fixed W ∪ T and |T|, there are at most 4 ^ |T| possible fragments.
omit [DecidableEq X] in
private lemma weighted_cover {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) (hq₁ : q ≤ 1)
    (hr : 4 * (p * (1 - q) / q) ≤ 1 / 8) (bad : Finset (Finset X))
    (hMass : ∑ W ∈ bad, mass q W ≥ 1 / 2) (hTotal : ∑ W : Finset X, mass q W = 1)
    (hw : ∀ S i, 0 ≤ w S i) (hsupp : ∀ S i, i ∉ S → w S i = 0)
    (hbad : ∀ W ∈ bad, ∀ S ∈ F, 2 * (∑ i ∈ W, w S i) < ∑ i, w S i) :
    ∃ G : Finset (Finset X), (∀ S ∈ F, ∃ T ∈ G, T ⊆ S) ∧
      ∑ T ∈ G, p ^ T.card ≤ 1 / 2 := by
  classical
  let r := p * (1 - q) / q
  have hr₀ : 0 ≤ r := div_nonneg (mul_nonneg hp (sub_nonneg.mpr hq₁)) hq.le
  let domain := bad.sigma (fragments F w)
  let choices (Z : Finset X) :=
    (range (Fintype.card X)).sigma fun k ↦ (canonical F w Z (k + 1)).powerset
  let imageSet := (univ : Finset (Finset X)).sigma choices
  let encode : (Σ _ : Finset X, Finset X) → (Σ _ : Finset X, Σ _ : ℕ, Finset X) :=
    fun ⟨W, T⟩ ↦ ⟨W ∪ T, T.card - 1, T⟩
  have henc (W T : Finset X) (hW : W ∈ bad) (hT : T ∈ fragments F w W) :=
    fragment_encoding F w hw (hbad W hW) hT
  have hkey (W T : Finset X) (hW : W ∈ bad) (hT : T ∈ fragments F w W) :
      T.card - 1 + 1 = T.card := by
    have := card_pos.mpr (henc W T hW hT).2.1
    omega
  have hin (x) (hx : x ∈ domain) : encode x ∈ imageSet := by
    obtain ⟨W, T⟩ := x
    obtain ⟨hW, hT⟩ := mem_sigma.mp hx
    have hk := hkey W T hW hT
    refine mem_sigma.mpr ⟨mem_univ _, mem_sigma.mpr ⟨mem_range.mpr ?_, mem_powerset.mpr ?_⟩⟩
    · change T.card - 1 < Fintype.card X
      have := card_le_univ (s := T)
      omega
    · change T ⊆ canonical F w (W ∪ T) (T.card - 1 + 1)
      rw [hk]
      exact (henc W T hW hT).2.2
  have hinj : Set.InjOn encode (↑domain : Set (Σ _ : Finset X, Finset X)) := by
    intro ⟨W, T⟩ hWT ⟨V, U⟩ hVU h
    have hZ : W ∪ T = V ∪ U := congrArg Sigma.fst h
    have hT : T = U := congrArg (fun a : Σ _ : Finset X, Σ _ : ℕ, Finset X ↦ a.2.2) h
    subst U
    have hW := (henc W T (mem_sigma.mp hWT).1 (mem_sigma.mp hWT).2).1
    have hV := (henc V T (mem_sigma.mp hVU).1 (mem_sigma.mp hVU).2).1
    have hWV : W = V := by
      have recW : (W ∪ T) \ T = W := by simp [sdiff_eq_left.mpr hW]
      have recV : (V ∪ T) \ T = V := by simp [sdiff_eq_left.mpr hV]
      rw [← recW, hZ, recV]
    cases hWV
    rfl
  have hgeom : ∑ k ∈ range (Fintype.card X), (1 / (8 : ℝ)) ^ (k + 1) ≤ 1 / 4 := by
    calc
      _ = (1 / 8) * ∑ k ∈ range (Fintype.card X), (1 / (8 : ℝ)) ^ k := by
        rw [mul_sum]
        simp_rw [pow_succ']
      _ ≤ (1 / 8) * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine (sum_le_sum fun i _ ↦ ?_).trans (sum_geometric_two_le _)
        exact pow_le_pow_left₀ (by norm_num) (by norm_num) i
      _ = _ := by norm_num
  have hbound (Z : Finset X) : (∑ a ∈ choices Z, r ^ (a.1 + 1)) ≤ 1 / 4 := by
    dsimp only [choices]
    rw [sum_sigma]
    refine (sum_le_sum fun k _ ↦ ?_).trans hgeom
    have hpow := pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ))
      (canonical_card F w Z (k + 1))
    calc
      (∑ _T ∈ (canonical F w Z (k + 1)).powerset, r ^ (k + 1)) =
          (2 : ℝ) ^ (canonical F w Z (k + 1)).card * r ^ (k + 1) := by
        rw [sum_const, nsmul_eq_mul, card_powerset, Nat.cast_pow, Nat.cast_ofNat]
      _ ≤ (2 : ℝ) ^ (2 * (k + 1)) * r ^ (k + 1) := by gcongr
      _ = (4 * r) ^ (k + 1) := by rw [pow_mul, mul_pow]; norm_num
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hr _
  have hsum : (∑ W ∈ bad, mass q W * ∑ T ∈ fragments F w W, p ^ T.card) ≤ 1 / 4 := by
    calc
      _ = ∑ x ∈ domain, mass q x.1 * p ^ x.2.card := by
        dsimp only [domain]
        rw [sum_sigma]
        simp_rw [mul_sum]
      _ ≤ ∑ y ∈ imageSet, mass q y.1 * r ^ (y.2.1 + 1) := by
        refine sum_le_sum_of_injOn encode hinj ?_ (fun x hx ↦ ?_) (fun y _ _ ↦ ?_)
        · exact image_subset_iff.mpr hin
        · obtain ⟨W, T⟩ := x
          obtain ⟨hW, hT⟩ := mem_sigma.mp hx
          simpa only [encode, hkey W T hW hT] using
            (mass_weight p hq (henc W T hW hT).1).le
        · exact mul_nonneg (mass_nonneg hq.le hq₁ _) (pow_nonneg hr₀ _)
      _ = ∑ Z : Finset X, mass q Z * (∑ a ∈ choices Z, r ^ (a.1 + 1)) := by
        dsimp only [imageSet]
        rw [sum_sigma]
        simp_rw [mul_sum]
      _ ≤ ∑ Z : Finset X, mass q Z * (1 / 4) := by
        exact sum_le_sum fun Z _ ↦ mul_le_mul_of_nonneg_left (hbound Z) (mass_nonneg hq.le hq₁ _)
      _ = _ := by rw [← sum_mul, hTotal, one_mul]
  obtain ⟨W, hW, hcost⟩ : ∃ W ∈ bad, ∑ T ∈ fragments F w W, p ^ T.card ≤ 1 / 2 := by
    by_contra! hh
    have hp' : ∃ W ∈ bad, 0 < mass q W := by
      by_contra! hn
      have hsum' : ∑ W ∈ bad, mass q W ≤ 0 := sum_nonpos hn
      linarith
    obtain ⟨W, hm, hpos⟩ := hp'
    have hlt : (∑ W ∈ bad, mass q W * (1 / 2)) <
        (∑ W ∈ bad, mass q W * ∑ T ∈ fragments F w W, p ^ T.card) := by
      exact sum_lt_sum (fun V hV ↦ mul_le_mul_of_nonneg_left (hh V hV).le (mass_nonneg hq.le hq₁ _))
        ⟨W, hm, mul_lt_mul_of_pos_left (hh W hm) hpos⟩
    rw [← sum_mul] at hlt
    linarith
  exact ⟨fragments F w W, fun S hS ↦ fragments_cover F w hw hsupp W hS, hcost⟩

section Probability

open MeasureTheory _root_.ProbabilityTheory Measure unitInterval
open scoped NNReal ENNReal

omit [DecidableEq X] in
private lemma sum_mass (p : I) (B : Finset (Finset X)) :
    ∑ W ∈ B, mass (p : ℝ) W =
      (binomialSetDistribution X p).real (⋃ W ∈ B, {(W : Set X)}) := by
  classical
  let : IsProbabilityMeasure (binomialSetDistribution X p) :=
    inferInstanceAs (IsProbabilityMeasure (setBernoulli Set.univ p))
  rw [measureReal_biUnion_finset (fun a _ b _ hab ↦ ?_) fun W _ ↦ measurableSet_singleton _]
  · refine sum_congr rfl fun W _ ↦ ?_
    rw [binomialSetDistribution, setBernoulli_real_singleton p (Set.subset_univ _) Set.finite_univ]
    simp [mass, Set.sdiff_eq_compl_inter, Set.ncard_compl, Nat.card_eq_fintype_card]
  · simpa using fun h : (a : Set X) = (b : Set X) ↦ hab (coe_injective h)

private def failure (p : I) (m : ℕ) : I :=
  ⟨(1 - (p : ℝ)) ^ m, pow_nonneg (one_sub_nonneg p) _, pow_le_one₀ (one_sub_nonneg p)
    (one_sub_le_one p)⟩

private def boosted (p : I) (m : ℕ) : I := σ (failure p m)

private lemma boosted_pos (p : I) (hp : 0 < (p : ℝ)) :
    0 < (boosted p 32 : ℝ) := by
  change 0 < 1 - (1 - (p : ℝ)) ^ 32
  exact sub_pos.mpr (pow_lt_one₀ (one_sub_nonneg p) (by linarith) (by decide))

private lemma boosted_odds (p : I) (hp : 0 < (p : ℝ)) :
    4 * ((p : ℝ) * (1 - (boosted p 32 : ℝ)) / (boosted p 32 : ℝ)) ≤ 1 / 8 := by
  rw [mul_div_assoc', div_le_iff₀ (boosted_pos p hp)]
  have hsum : 32 * (1 - (p : ℝ)) ^ 32 ≤
      ∑ i ∈ range 32, (1 - (p : ℝ)) ^ i := by
    simpa only [sum_const, card_range, nsmul_eq_mul, Nat.cast_ofNat] using
      (sum_le_sum (s := range 32) fun i hi ↦
        pow_le_pow_of_le_one (one_sub_nonneg p) (one_sub_le_one p)
          (Nat.le_of_lt (mem_range.mp hi)))
  have hmul := mul_le_mul_of_nonneg_right hsum hp.le
  have hg := geom_sum_mul_neg (1 - (p : ℝ)) 32
  rw [sub_sub_cancel] at hg
  rw [hg] at hmul
  change 4 * ((p : ℝ) * (1 - (1 - (1 - (p : ℝ)) ^ 32))) ≤
    1 / 8 * (1 - (1 - (p : ℝ)) ^ 32)
  rw [sub_sub_cancel]
  linarith only [hmul]

private lemma map_membership (p : I) (j : Fin 32) :
    (binomialSetDistribution (Fin 32) p).map (fun s ↦ j ∈ s) =
      bernoulliMeasure True False p := by
  rw [binomialSetDistribution, setBernoulli_eq_map, map_map (measurable_set_mem j)
    measurable_setOfPred]
  simpa [Function.comp_def] using
    (infinitePi_map_eval (fun _ : Fin 32 ↦ bernoulliMeasure True False p) j)

private lemma map_nonempty (p : I) :
    (binomialSetDistribution (Fin 32) p).map (fun s ↦ s.Nonempty) =
      bernoulliMeasure True False (boosted p 32) := by
  classical
  let μ := binomialSetDistribution (Fin 32) p
  let : IsProbabilityMeasure μ :=
    inferInstanceAs (IsProbabilityMeasure (setBernoulli Set.univ p))
  let ν := μ.map (fun s ↦ s.Nonempty)
  have hm : Measurable (fun s : Set (Fin 32) ↦ s.Nonempty) := measurable_of_finite _
  let : IsProbabilityMeasure ν := inferInstanceAs (IsProbabilityMeasure (μ.map _))
  have hpre : (fun s : Set (Fin 32) ↦ s.Nonempty) ⁻¹' ({False} : Set Prop) = {∅} := by
    ext s
    simp [Set.not_nonempty_iff_eq_empty]
  have hf : ν {False} = toNNReal (failure p 32) := by
    change μ.map (fun s ↦ s.Nonempty) {False} = _
    rw [map_apply hm (measurableSet_singleton _), hpre]
    have hpow : toNNReal (failure p 32) = (toNNReal (σ p)) ^ 32 := NNReal.eq rfl
    rw [hpow, ENNReal.coe_pow]
    simp [μ, binomialSetDistribution, setBernoulli_singleton, Nat.card_eq_fintype_card]
  have hf' : bernoulliMeasure True False (boosted p 32) {False} = ν {False} := by
    rw [hf]
    simp [bernoulliMeasure_def, boosted]
  apply Measure.ext_of_singleton
  intro b
  by_cases hb : b
  · rw [eq_true hb]
    change ν {True} = _
    have hc : ({False} : Set Prop)ᶜ = {True} := by
      ext a
      by_cases ha : a <;> simp [ha]
    rw [← hc, prob_compl_eq_one_sub (measurableSet_singleton False),
      prob_compl_eq_one_sub (measurableSet_singleton False), hf']
  · rw [eq_false hb]
    exact hf'.symm

private noncomputable def value (f : X → ℝ≥0) (S : Set X) : ℝ≥0∞ := by
  classical
  exact ∑ i ∈ S, (f i : ℝ≥0∞)

private noncomputable def score (Λ : Set (X → ℝ≥0)) (S : Set X) : ℝ≥0∞ :=
  ⨆ f ∈ Λ, value f S

omit [DecidableEq X] in
open Classical in
private lemma value_eq_sum_ite (f : X → ℝ≥0) (S : Set X) :
    value f S = ∑ i : X, if i ∈ S then (f i : ℝ≥0∞) else 0 := by
  classical
  unfold value
  rw [← sum_filter]
  congr 1
  ext i
  simp

omit [DecidableEq X] in
private lemma score_union_le (Λ : Set (X → ℝ≥0)) (A : Fin 32 → Set X) :
    score Λ (⋃ j, A j) ≤ ∑ j, score Λ (A j) := by
  classical
  refine iSup_le fun f ↦ iSup_le fun hf ↦ ?_
  refine le_trans ?_ (sum_le_sum fun j _ ↦ le_iSup_of_le f (le_iSup _ hf))
  rw [value_eq_sum_ite, show (∑ j, value f (A j)) =
    ∑ i : X, ∑ j : Fin 32, if i ∈ A j then (f i : ℝ≥0∞) else 0 by
      simpa only [value_eq_sum_ite] using
        (sum_comm (s := (univ : Finset (Fin 32))) (t := (univ : Finset X))
          (f := fun j i ↦ if i ∈ A j then (f i : ℝ≥0∞) else 0))]
  refine sum_le_sum fun i _ ↦ ?_
  by_cases hi : i ∈ ⋃ j, A j
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hi
    rw [ite_eq_left hi]
    simpa [hj] using
      (single_le_sum (f := fun j ↦ if i ∈ A j then (f i : ℝ≥0∞) else 0)
        (fun _ _ ↦ zero_le) (mem_univ j))
  · simp [hi]

-- Each coordinate independently records the draws in which it is selected.
-- The union has the boosted law while each individual draw has the original law.
omit [DecidableEq X] in
private lemma boosted_expectation (p : I) (Λ : Set (X → ℝ≥0)) :
    ∫⁻ S, score Λ S ∂binomialSetDistribution X (boosted p 32) ≤
      32 * ∫⁻ S, score Λ S ∂binomialSetDistribution X p := by
  classical
  let μ := binomialSetDistribution (Fin 32) p
  let : IsProbabilityMeasure μ :=
    inferInstanceAs (IsProbabilityMeasure (setBernoulli Set.univ p))
  let P : Measure (X → Set (Fin 32)) := infinitePi fun _ ↦ μ
  let A (j : Fin 32) (ω : X → Set (Fin 32)) : Set X := {i | j ∈ ω i}
  have hlaw (j : Fin 32) : P.map (A j) = binomialSetDistribution X p := by
    change P.map ((fun t : X → Prop ↦ {i | t i}) ∘ fun ω i ↦ j ∈ ω i) = _
    dsimp only [P]
    rw [← map_map measurable_setOfPred (measurable_of_finite _),
      infinitePi_map_pi _ (fun _ ↦ measurable_set_mem j), binomialSetDistribution,
      setBernoulli_eq_map]
    simp only [μ, map_membership, Set.mem_univ]
  let B (ω : X → Set (Fin 32)) : Set X := {i | (ω i).Nonempty}
  have hB : P.map B = binomialSetDistribution X (boosted p 32) := by
    change P.map ((fun t : X → Prop ↦ {i | t i}) ∘ fun ω i ↦ (ω i).Nonempty) = _
    dsimp only [P]
    rw [← map_map measurable_setOfPred (measurable_of_finite _),
      infinitePi_map_pi _ (fun _ ↦ measurable_of_finite _), binomialSetDistribution,
      setBernoulli_eq_map]
    simp only [μ, map_nonempty, Set.mem_univ]
  have hBA ω : B ω = ⋃ j, A j ω := by ext i; simp [A, B, Set.Nonempty]
  calc
    _ = ∫⁻ ω, score Λ (B ω) ∂P := by
      rw [← hB, lintegral_map (measurable_of_finite _) (measurable_of_finite _)]
    _ ≤ ∫⁻ ω, ∑ j, score Λ (A j ω) ∂P :=
      lintegral_mono fun ω ↦ hBA ω ▸ score_union_le Λ (A · ω)
    _ = ∑ j : Fin 32, ∫⁻ ω, score Λ (A j ω) ∂P :=
      lintegral_finsetSum _ (fun _ _ ↦ measurable_of_finite _)
    _ = _ := by
      simp_rw [← lintegral_map (measurable_of_finite (score Λ))
        (measurable_of_finite (A _)), hlaw]
      simp [nsmul_eq_mul]

end Probability


end theorem_1_2

open Measure theorem_1_2

local notation "𝔼⁻[" t "; " X " ∼ " μ "]" => MeasureTheory.lintegral μ (fun X ↦ ↑t)

open Classical in
/--
**Park–Pham theorem on selector processes (Talagrand's selector process conjecture).** There is
a real number $L > 0$ with the following property. Let $0 < p < 1$, let $X$ be a finite type,
let $\Lambda$ be a set of functions from $X$ to $[0, \infty)$, and let $X_p$ be a binomial random
subset of $X$ with parameter $p$. Write
$E = \mathbb{E}\bigl[\sup_{f \in \Lambda} \sum_{i \in X_p} f(i)\bigr]$, computed in
$[0, \infty]$. If $0 < E < \infty$, then the family of subsets $s \subseteq X$ with
$\sup_{f \in \Lambda} \sum_{i \in s} f(i) \ge L E$ is $p$-small.

The hypothesis $0 < E < \infty$ is not stated explicitly in the paper's theorem, but it is used
in the last step of the proof, which derives a contradiction from an inequality $E \ge c E$
with a constant $c > 1$.

Source: J. Park and H. T. Pham, `On a conjecture of Talagrand on selector processes and a
consequence on positive empirical processes`, Annals of Math, 199 (3) 2024. Statement taken from
https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14),
AnnalsChallenge/AnnalsOfMathematics/2024-199-3-SupremumOfSelectorProcesses.lean Via
leanprover/lean-eval@38361be, problem `annals_supremum_of_selector_processes`.
-/
public theorem theorem_1_2 : ∃ L : ℝ≥0, 0 < L ∧ ∀ (p : I), 0 < p → p < 1 →
    ∀ (X : Type*) [Fintype X] (Λ : Set (X → ℝ≥0)),
    0 < 𝔼⁻[⨆ f ∈ Λ, ∑ i ∈ Xp, (f i : ℝ≥0∞); Xp ∼ binomialSetDistribution X p] →
    𝔼⁻[⨆ f ∈ Λ, ∑ i ∈ Xp, (f i : ℝ≥0∞); Xp ∼ binomialSetDistribution X p] < ∞ →
    IsSmall p {s : Set X | ⨆ f ∈ Λ, ∑ i ∈ s, (f i : ℝ≥0∞) ≥
        L * 𝔼⁻[⨆ f ∈ Λ, ∑ i ∈ Xp, (f i : ℝ≥0∞); Xp ∼ binomialSetDistribution X p]} := by
  classical
  refine ⟨256, by norm_num, ?_⟩
  intro p hp _ X _ Λ
  let E := ∫⁻ s, score Λ s ∂binomialSetDistribution X p
  change 0 < E → E < ∞ → IsSmall p {s | 256 * E ≤ score Λ s}
  intro hE hEtop
  let q := boosted p 32
  let μ := binomialSetDistribution X q
  let : IsProbabilityMeasure μ :=
    inferInstanceAs (IsProbabilityMeasure (_root_.ProbabilityTheory.setBernoulli Set.univ q))
  let tail : Set (Set X) := {s | 64 * E ≤ score Λ s}
  have htail : μ.real tail ≤ 1 / 2 := by
    have hmul : (64 * E) * μ tail ≤ 32 * E :=
      (mul_meas_ge_le_lintegral (μ := μ) (measurable_of_finite (score Λ)) (64 * E)).trans
        (boosted_expectation p Λ)
    have hfin : (32 : ℝ≥0∞) * E ≠ ∞ := ENNReal.mul_ne_top (by norm_num) hEtop.ne
    have hreal := ENNReal.toReal_mono hfin hmul
    simp only [ENNReal.toReal_mul] at hreal
    change 64 * E.toReal * μ.real tail ≤ 32 * E.toReal at hreal
    apply (mul_le_mul_iff_left₀ (ENNReal.toReal_pos hE.ne' hEtop.ne)).mp
    linarith only [hreal]
  let bad : Finset (Finset X) := univ.filter fun W ↦ score Λ (W : Set X) < 64 * E
  have hbadset : (⋃ W ∈ bad, {(W : Set X)}) = tailᶜ := by
    ext s
    simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_compl_iff, tail, Set.mem_ofPred_eq,
      not_le]
    constructor
    · rintro ⟨W, hW, rfl⟩
      exact (mem_filter.mp hW).2
    · intro hs
      exact ⟨s.toFinset, mem_filter.mpr ⟨mem_univ _, by simpa using hs⟩, (Set.coe_toFinset _).symm⟩
  have hMass : (1 : ℝ) / 2 ≤ ∑ W ∈ bad, mass (q : ℝ) W := by
    rw [sum_mass q, hbadset, measureReal_compl MeasurableSet.of_discrete, probReal_univ]
    linarith only [htail]
  have hTotal : ∑ W : Finset X, mass (q : ℝ) W = 1 := by
    rw [sum_mass q]
    have hu : (⋃ W ∈ (univ : Finset (Finset X)), {(W : Set X)}) = Set.univ := by
      ext s
      simp only [Set.mem_iUnion, mem_univ, Set.mem_singleton_iff, exists_const, Set.mem_univ,
        iff_true]
      exact ⟨s.toFinset, (Set.coe_toFinset _).symm⟩
    rw [hu]
    exact probReal_univ (μ := μ)
  let F : Finset (Finset X) := univ.filter fun S ↦ 256 * E ≤ score Λ (S : Set X)
  have hexists (S : Finset X) (hS : S ∈ F) : ∃ f ∈ Λ, 128 * E < value f (S : Set X) := by
    have hlt : (128 : ℝ≥0∞) * E < 256 * E :=
      ENNReal.mul_lt_mul_left hE.ne' hEtop.ne (show (128 : ℝ≥0∞) < 256 by norm_num)
    have hlarge : 256 * E ≤ score Λ (S : Set X) := (mem_filter.mp hS).2
    have h := hlt.trans_le hlarge
    simpa only [score, lt_iSup_iff, exists_prop] using h
  let witness (S : Finset X) : X → ℝ≥0 := if h : S ∈ F then (hexists S h).choose else 0
  let weights (S : Finset X) (i : X) : ℝ≥0 := if i ∈ S then witness S i else 0
  let w (S : Finset X) (i : X) : ℝ := weights S i
  have hvalue (S W : Finset X) :
      ∑ i ∈ W, (weights S i : ℝ≥0∞) = value (witness S) ((W ∩ S : Finset X) : Set X) := by
    simp only [value, Finset.toFinset_coe]
    have hfilter : W.filter (· ∈ S) = W ∩ S := by ext i; simp
    simp_rw [weights, apply_ite (fun x : ℝ≥0 ↦ (x : ℝ≥0∞)), ENNReal.coe_zero,
      ← sum_filter, hfilter]
  have hbad (W : Finset X) (hW : W ∈ bad) (S : Finset X) (hS : S ∈ F) :
      2 * (∑ i ∈ W, w S i) < ∑ i, w S i := by
    have hf : witness S ∈ Λ ∧ 128 * E < value (witness S) (S : Set X) := by
      simpa only [witness, dite_eq_left hS] using (hexists S hS).choose_spec
    have hsmall : (∑ i ∈ W, (weights S i : ℝ≥0∞)) < 64 * E := by
      rw [hvalue]
      have hle : value (witness S) ((W ∩ S : Finset X) : Set X) ≤
          value (witness S) (W : Set X) := by
        simpa [value] using
          (sum_le_sum_of_subset inter_subset_left :
            ∑ i ∈ W ∩ S, (witness S i : ℝ≥0∞) ≤ ∑ i ∈ W, (witness S i : ℝ≥0∞))
      have hs : value (witness S) (W : Set X) ≤ score Λ (W : Set X) :=
        le_iSup_of_le (witness S) (le_iSup (fun _ : witness S ∈ Λ ↦ value (witness S) ↑W) hf.1)
      exact (hle.trans hs).trans_lt (mem_filter.mp hW).2
    have hlarge : 128 * E < (∑ i, (weights S i : ℝ≥0∞)) := by
      rw [hvalue, univ_inter]
      exact hf.2
    have hlt : (2 : ℝ≥0∞) * (∑ i ∈ W, (weights S i : ℝ≥0∞)) <
        (∑ i, (weights S i : ℝ≥0∞)) := by
      have hmul : (2 : ℝ≥0∞) * (∑ i ∈ W, (weights S i : ℝ≥0∞)) < 2 * (64 * E) :=
        ENNReal.mul_lt_mul_right (show (2 : ℝ≥0∞) ≠ 0 by norm_num)
          (show (2 : ℝ≥0∞) ≠ ∞ by norm_num) hsmall
      exact hmul.trans (by simpa only [← mul_assoc, show (2 : ℝ≥0∞) * 64 = 128 by norm_num]
        using hlarge)
    have hfinite (A : Finset X) : (∑ i ∈ A, (weights S i : ℝ≥0∞)) ≠ ∞ := by
      rw [← ENNReal.ofNNReal_finsetSum]
      exact ENNReal.coe_ne_top
    have hr := (ENNReal.toReal_lt_toReal (ENNReal.mul_ne_top (by norm_num) (hfinite W))
      (hfinite univ)).mpr hlt
    simpa [ENNReal.toReal_mul, ENNReal.toReal_sum, w] using hr
  obtain ⟨G, hG, hcost⟩ := weighted_cover F w (unitInterval.nonneg p)
    (boosted_pos p hp) (unitInterval.le_one q) (boosted_odds p hp) bad hMass hTotal
    (fun S i ↦ (weights S i).2) (fun S i hi ↦ by simp [w, weights, hi]) hbad
  refine ⟨{t | t.toFinset ∈ G}, ?_, ?_⟩
  · intro s hs
    have hsF : s.toFinset ∈ F := mem_filter.mpr ⟨mem_univ _, by simpa using hs⟩
    obtain ⟨T, hT, hTs⟩ := hG _ hsF
    refine Set.mem_iUnion.mpr ⟨(T : Set X), Set.mem_iUnion.mpr ⟨by simpa, ?_⟩⟩
    simpa using coe_subset.mpr hTs
  · calc
      _ = ∑ s ∈ G.image (fun W : Finset X ↦ (W : Set X)), (p : ℝ) ^ s.ncard := by
        apply sum_congr _ (fun _ _ ↦ rfl)
        ext s
        simp only [Set.mem_toFinset, Set.mem_ofPred_eq, mem_image]
        constructor
        · exact fun hs ↦ ⟨s.toFinset, hs, Set.coe_toFinset _⟩
        · rintro ⟨T, hT, rfl⟩
          simpa using hT
      _ ≤ _ := by
        rw [sum_image coe_injective.injOn]
        simpa [one_div] using hcost

end SupremumOfSelectorProcesses
end MathlibExt.Analysis.SupremumOfSelectorProcessesWanted
