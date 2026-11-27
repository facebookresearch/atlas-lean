/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.BinomialTail
public import Mathlib.Data.ZMod.Basic
public import CSLibExt.Coding.Hamming74
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# Bounded-distance decoding over a binary symmetric channel

For a binary code of length `n` with minimum distance at least
`2t + 1`, bounded-distance decoding over a binary symmetric channel
with crossover probability `delta` fails only when more than `t`
symbols are flipped, so the decoding error probability is at most
the binomial tail `ProbabilityTheory.binomTail n (t + 1) delta`.
The Hamming (7,4) case (`t = 1`) is included. The binomial tail is
the canonical `MathlibExt.Probability.Distributions.BinomialTail`
definition, not a local copy.
-/

@[expose] public section

open ProbabilityTheory

namespace Cslib.CodingTheory.BoundedDistanceBSC

/-- Binary symmetric channel law on error words: product
(`Measure.pi`) of IID `Bernoulli(delta)` flips, where flip value `1`
has probability `delta` and `0` has probability `1 - delta`. -/
noncomputable def bscMeasure (n : ℕ) (delta : ℝ) (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta ≤ 1) :
    MeasureTheory.Measure (Fin n → ZMod 2) :=
  MeasureTheory.Measure.pi
    (fun _ : Fin n =>
      ProbabilityTheory.bernoulliMeasure (1 : ZMod 2) 0
        ⟨delta, Set.mem_Icc.mpr ⟨hdelta0, hdelta1⟩⟩)

/-- The BSC law is a probability measure. -/
private instance bsc_isProbabilityMeasure (n : ℕ) (delta : ℝ) (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta ≤ 1) :
    MeasureTheory.IsProbabilityMeasure (bscMeasure n delta hdelta0 hdelta1) := by
  unfold bscMeasure
  infer_instance

/-- Support of an error word: the positions carrying a nonzero value. -/
private def supp (n : ℕ) (e : Fin n → ZMod 2) : Finset (Fin n) :=
  Finset.univ.filter (fun i => e i ≠ 0)

/-- Indicator error word of a set of positions. -/
private def ind (n : ℕ) (S : Finset (Fin n)) : Fin n → ZMod 2 :=
  fun i => if i ∈ S then 1 else 0

/-- Every nonzero element of `ZMod 2` equals `1`. -/
private lemma zmod2_eq_one_of_ne_zero (x : ZMod 2) (hx : x ≠ 0) : x = 1 := by
  have h : ∀ y : ZMod 2, y ≠ 0 → y = 1 := by decide
  exact h x hx

/-- The Hamming norm is bounded by the word length. -/
private lemma hammingNorm_le_n (n : ℕ) (e : Fin n → ZMod 2) :
    hammingNorm e ≤ n := by
  calc hammingNorm e ≤ Fintype.card (Fin n) := hammingNorm_le_card_fintype
    _ = n := Fintype.card_fin n

/-- The `bscMeasure` mass of a singleton error word. -/
private lemma bsc_real_singleton (n : ℕ) (delta : ℝ) (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta ≤ 1) (e : Fin n → ZMod 2) :
    (bscMeasure n delta hdelta0 hdelta1).real {e} =
      delta ^ hammingNorm e * (1 - delta) ^ (n - hammingNorm e) := by
  have hbridge : hammingNorm e = (Finset.univ.filter (fun i => e i ≠ 0)).card := rfl
  rw [hbridge]
  have hfactor : ∀ i : Fin n,
      ((ProbabilityTheory.bernoulliMeasure (1 : ZMod 2) 0
        ⟨delta, Set.mem_Icc.mpr ⟨hdelta0, hdelta1⟩⟩) {e i}).toReal =
        (if e i ≠ 0 then delta else (1 - delta)) := by
    intro i
    by_cases hi : e i ≠ 0
    · rw [ite_eq_left hi]
      have hei : e i = 1 := zmod2_eq_one_of_ne_zero _ hi
      have h1mem : (1 : ZMod 2) ∈ ({e i} : Set (ZMod 2)) := by
        rw [Set.mem_singleton_iff]
        exact hei.symm
      have h0nmem : (0 : ZMod 2) ∉ ({e i} : Set (ZMod 2)) := by
        rw [Set.mem_singleton_iff, hei]
        exact by decide
      exact ProbabilityTheory.bernoulliMeasure_real_apply_of_mem_of_notMem _
        (measurableSet_singleton (e i)) h1mem h0nmem
    · rw [ite_eq_right hi]
      have hei : e i = 0 := of_not_not hi
      have h1nmem : (1 : ZMod 2) ∉ ({e i} : Set (ZMod 2)) := by
        rw [Set.mem_singleton_iff, hei]
        exact by decide
      have h0mem : (0 : ZMod 2) ∈ ({e i} : Set (ZMod 2)) := by
        rw [Set.mem_singleton_iff]
        exact hei.symm
      exact ProbabilityTheory.bernoulliMeasure_real_apply_of_notMem_of_mem _
        (measurableSet_singleton (e i)) h1nmem h0mem
  unfold bscMeasure
  rw [MeasureTheory.measureReal_def, MeasureTheory.Measure.pi_singleton]
  simp only [ENNReal.toReal_prod]
  have hprod1 : (∏ i : Fin n,
        ((ProbabilityTheory.bernoulliMeasure (1 : ZMod 2) 0
          ⟨delta, Set.mem_Icc.mpr ⟨hdelta0, hdelta1⟩⟩) {e i}).toReal) =
      ∏ i : Fin n, (if e i ≠ 0 then delta else (1 - delta)) :=
    Finset.prod_congr rfl (fun i _ => hfactor i)
  rw [hprod1]
  have hsplit : (∏ i ∈ Finset.univ.filter (fun i => e i ≠ 0),
          (if e i ≠ 0 then delta else (1 - delta))) *
        (∏ i ∈ Finset.univ.filter (fun i => ¬ e i ≠ 0),
          (if e i ≠ 0 then delta else (1 - delta))) =
        ∏ i ∈ Finset.univ, (if e i ≠ 0 then delta else (1 - delta)) :=
    Finset.prod_filter_mul_prod_filter_not _ _ _
  rw [← hsplit]
  have hp1 : ∀ i ∈ Finset.univ.filter (fun i => e i ≠ 0),
      (if e i ≠ 0 then delta else (1 - delta)) = delta := by
    intro i hi
    exact ite_eq_left (Finset.mem_filter.mp hi).2
  have hp2 : ∀ i ∈ Finset.univ.filter (fun i => ¬ e i ≠ 0),
      (if e i ≠ 0 then delta else (1 - delta)) = (1 - delta) := by
    intro i hi
    exact ite_eq_right (Finset.mem_filter.mp hi).2
  rw [Finset.prod_congr rfl hp1, Finset.prod_congr rfl hp2, Finset.prod_const,
    Finset.prod_const]
  have hcard2 : (Finset.univ.filter (fun i => ¬ e i ≠ 0)).card =
      n - (Finset.univ.filter (fun i => e i ≠ 0)).card := by
    have h : (Finset.univ.filter (fun i => e i ≠ 0)).card +
        (Finset.univ.filter (fun i => ¬ e i ≠ 0)).card = Finset.univ.card :=
      Finset.card_filter_add_card_filter_not _
    rw [Finset.card_univ, Fintype.card_fin] at h
    omega
  rw [hcard2]

/-- Error words of a given weight biject with `j`-subsets of positions. -/
private lemma card_filter_weight_eq_choose (n j : ℕ) :
    (Finset.univ.filter
      (fun e : Fin n → ZMod 2 => hammingNorm e = j)).card =
      n.choose j := by
  have hi_maps : Set.MapsTo (supp n)
      (↑(Finset.univ.filter
        (fun e : Fin n → ZMod 2 => hammingNorm e = j)))
      (↑(Finset.powersetCard j (Finset.univ : Finset (Fin n)))) := by
    intro e he
    have hew : hammingNorm e = j :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨Finset.filter_subset _ _, ?_⟩
    exact hew
  have hi_inj : Set.InjOn (supp n)
      (↑(Finset.univ.filter
        (fun e : Fin n → ZMod 2 => hammingNorm e = j))) := by
    intro e₁ _ e₂ _ hsup
    funext i
    by_cases h1 : e₁ i ≠ 0
    · have he₁1 : e₁ i = 1 := zmod2_eq_one_of_ne_zero _ h1
      have hi1 : i ∈ supp n e₁ :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, h1⟩
      rw [hsup] at hi1
      have h2 : e₂ i ≠ 0 := (Finset.mem_filter.mp hi1).2
      have he₂1 : e₂ i = 1 := zmod2_eq_one_of_ne_zero _ h2
      rw [he₁1, he₂1]
    · have he₁0 : e₁ i = 0 := of_not_not h1
      have hi1 : i ∉ supp n e₁ := fun h => h1 (Finset.mem_filter.mp h).2
      rw [hsup] at hi1
      have he₂0 : e₂ i = 0 :=
        of_not_not (fun h => hi1 (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩))
      rw [he₁0, he₂0]
  have hi_surj : Set.SurjOn (supp n)
      (↑(Finset.univ.filter
        (fun e : Fin n → ZMod 2 => hammingNorm e = j)))
      (↑(Finset.powersetCard j (Finset.univ : Finset (Fin n)))) := by
    intro S hS
    have hScard : S.card = j :=
      (Finset.mem_powersetCard.mp (Finset.mem_coe.mp hS)).2
    have hsupp : supp n (ind n S) = S := by
      show Finset.univ.filter (fun i => (ind n S) i ≠ 0) = S
      apply le_antisymm
      · intro i hi
        have hi2 : (ind n S) i ≠ 0 := (Finset.mem_filter.mp hi).2
        by_contra hc
        have h0 : (ind n S) i = 0 := by
          show (if i ∈ S then (1 : ZMod 2) else 0) = 0
          rw [ite_eq_right hc]
        exact hi2 h0
      · intro i hiS
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ i, ?_⟩
        have h1 : (ind n S) i = 1 := by
          show (if i ∈ S then (1 : ZMod 2) else 0) = 1
          rw [ite_eq_left hiS]
        rw [h1]
        exact by decide
    have hweight : hammingNorm (ind n S) = j := by
      have hrfl : hammingNorm (ind n S) = (supp n (ind n S)).card := rfl
      rw [hrfl, hsupp]
      exact hScard
    refine ⟨ind n S, ?_, hsupp⟩
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hweight⟩
  have hbij := Finset.card_nbij (supp n) hi_maps hi_inj hi_surj
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at hbij
  exact hbij

/-- A block error forces error weight at least `t + 1`, given that
every error of weight at most `t` is corrected. -/
theorem weight_gt_t_of_decode_ne (n k t : ℕ)
    (encode : (Fin k → ZMod 2) → (Fin n → ZMod 2))
    (decode : (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (hcorrect : ∀ (msg : Fin k → ZMod 2) (e : Fin n → ZMod 2),
      hammingNorm e ≤ t → decode (encode msg + e) = encode msg)
    (m : Fin k → ZMod 2) (e : Fin n → ZMod 2)
    (hbad : decode (encode m + e) ≠ encode m) :
    t + 1 ≤ hammingNorm e := by
  by_contra h
  have hle : hammingNorm e ≤ t := by omega
  exact hbad (hcorrect m e hle)

/-- For `0 ≤ δ ≤ 1`, the BSC law on `𝔽₂^n` gives the error words of weight at least `k`
probability `∑_{i=k}^{n} C(n, i) δ^i (1 - δ)^(n - i)`. -/
theorem bsc_real_weight_ge_eq_binomTail (n k : ℕ) (delta : ℝ)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    (bscMeasure n delta hdelta0 hdelta1).real
        {e : Fin n → ZMod 2 | k ≤ hammingNorm e} =
      binomTail n k delta := by
  have hFS : ((Finset.univ.filter
        (fun e : Fin n → ZMod 2 => k ≤ hammingNorm e)) :
        Set (Fin n → ZMod 2)) =
      {e : Fin n → ZMod 2 | k ≤ hammingNorm e} := by
    apply le_antisymm
    · intro e he
      rw [Finset.mem_coe, Finset.mem_filter] at he
      show k ≤ hammingNorm e
      exact he.2
    · intro e he
      have he' : k ≤ hammingNorm e := he
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨Finset.mem_univ e, he'⟩
  have hdisj : Set.PairwiseDisjoint
      (↑(Finset.univ.filter
        (fun e : Fin n → ZMod 2 => k ≤ hammingNorm e)))
      (fun e => ({e} : Set (Fin n → ZMod 2))) := by
    intro e _ e' _ hne
    show Disjoint ({e} : Set (Fin n → ZMod 2)) ({e'} : Set (Fin n → ZMod 2))
    exact Set.disjoint_singleton.mpr hne
  have hbiU : (⋃ e ∈ ((Finset.univ.filter
          (fun e : Fin n → ZMod 2 => k ≤ hammingNorm e)) :
          Set (Fin n → ZMod 2)),
        ({e} : Set (Fin n → ZMod 2))) =
      ((Finset.univ.filter
        (fun e : Fin n → ZMod 2 => k ≤ hammingNorm e)) :
        Set (Fin n → ZMod 2)) := by
    apply le_antisymm
    · intro e he
      simp only [Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at he
      obtain ⟨e', he', rfl⟩ := he
      exact he'
    · intro e he
      simp only [Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]
      exact ⟨e, he, rfl⟩
  have hsum : (bscMeasure n delta hdelta0 hdelta1)
        {e : Fin n → ZMod 2 | k ≤ hammingNorm e} =
      ∑ e ∈ Finset.univ.filter (fun e : Fin n → ZMod 2 => k ≤ hammingNorm e),
        (bscMeasure n delta hdelta0 hdelta1) {e} := by
    have hbiUmeas : (bscMeasure n delta hdelta0 hdelta1)
          (⋃ e ∈ ((Finset.univ.filter
            (fun e : Fin n → ZMod 2 => k ≤ hammingNorm e)) :
            Set (Fin n → ZMod 2)),
            ({e} : Set (Fin n → ZMod 2))) =
        ∑ e ∈ Finset.univ.filter (fun e : Fin n → ZMod 2 => k ≤ hammingNorm e),
          (bscMeasure n delta hdelta0 hdelta1) {e} :=
      MeasureTheory.measure_biUnion_finset hdisj
        (fun e _ => measurableSet_singleton e)
    rw [← hFS, ← hbiU]
    exact hbiUmeas
  have hreal_sum : (bscMeasure n delta hdelta0 hdelta1).real
        {e : Fin n → ZMod 2 | k ≤ hammingNorm e} =
      ∑ e ∈ Finset.univ.filter (fun e : Fin n → ZMod 2 => k ≤ hammingNorm e),
        (bscMeasure n delta hdelta0 hdelta1).real {e} := by
    rw [MeasureTheory.measureReal_def, hsum,
      ENNReal.toReal_sum (fun e (_ : e ∈ Finset.univ.filter
        (fun e : Fin n → ZMod 2 => k ≤ hammingNorm e)) =>
        (MeasureTheory.measure_lt_top (bscMeasure n delta hdelta0 hdelta1)
          {e}).ne)]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [MeasureTheory.measureReal_def]
  have h_mem : ∀ e ∈ Finset.univ.filter
      (fun e : Fin n → ZMod 2 => k ≤ hammingNorm e),
      hammingNorm e ∈ Finset.Icc k n := by
    intro e he
    have hek : k ≤ hammingNorm e := (Finset.mem_filter.mp he).2
    have hle : hammingNorm e ≤ n := hammingNorm_le_n n e
    rw [Finset.mem_Icc]
    exact ⟨hek, hle⟩
  have hsplit : (∑ e ∈ Finset.univ.filter
        (fun e : Fin n → ZMod 2 => k ≤ hammingNorm e),
        (bscMeasure n delta hdelta0 hdelta1).real {e}) =
      ∑ j ∈ Finset.Icc k n,
        ∑ e ∈ (Finset.univ.filter
          (fun e : Fin n → ZMod 2 => k ≤ hammingNorm e)).filter
          (fun e => hammingNorm e = j),
        (bscMeasure n delta hdelta0 hdelta1).real {e} :=
    (Finset.sum_fiberwise_of_maps_to h_mem _).symm
  have hfib : ∀ j ∈ Finset.Icc k n,
      (Finset.univ.filter
        (fun e : Fin n → ZMod 2 => k ≤ hammingNorm e)).filter
        (fun e => hammingNorm e = j) =
        Finset.univ.filter (fun e : Fin n → ZMod 2 => hammingNorm e = j) := by
    intro j hj
    have hkj : k ≤ j := (Finset.mem_Icc.mp hj).1
    apply le_antisymm
    · intro e he
      have he2 := (Finset.mem_filter.mp he).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, he2⟩
    · intro e he
      have he2 : hammingNorm e = j := (Finset.mem_filter.mp he).2
      have hek : k ≤ hammingNorm e := by omega
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ e, hek⟩, he2⟩
  have hinner : ∀ j ∈ Finset.Icc k n,
      (∑ e ∈ (Finset.univ.filter
        (fun e : Fin n → ZMod 2 => k ≤ hammingNorm e)).filter
        (fun e => hammingNorm e = j),
        (bscMeasure n delta hdelta0 hdelta1).real {e}) =
        ((n.choose j : ℝ) * delta ^ j * (1 - delta) ^ (n - j)) := by
    intro j hj
    have hconst : ∀ e ∈ Finset.univ.filter
        (fun e : Fin n → ZMod 2 => hammingNorm e = j),
        (bscMeasure n delta hdelta0 hdelta1).real {e} =
          delta ^ j * (1 - delta) ^ (n - j) := by
      intro e he
      have hew : hammingNorm e = j := (Finset.mem_filter.mp he).2
      rw [bsc_real_singleton n delta hdelta0 hdelta1 e, hew]
    rw [hfib j hj, Finset.sum_congr rfl hconst, Finset.sum_const,
      card_filter_weight_eq_choose n j, nsmul_eq_mul, mul_assoc]
  rw [hreal_sum, hsplit]
  unfold binomTail
  exact Finset.sum_congr rfl hinner

/-- **Bounded-distance BSC block-error bound.** A decoder correcting
every error of weight at most `t` has block-error probability under
IID `Bernoulli(delta)` flips at most `binomTail n (t + 1) delta`. -/
theorem boundedDistance_bsc_error_le_binomTail (n k t : ℕ)
    (encode : (Fin k → ZMod 2) → (Fin n → ZMod 2))
    (decode : (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (hcorrect : ∀ (msg : Fin k → ZMod 2) (e : Fin n → ZMod 2),
      hammingNorm e ≤ t → decode (encode msg + e) = encode msg)
    (m : Fin k → ZMod 2) (delta : ℝ) (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta ≤ 1) :
    (bscMeasure n delta hdelta0 hdelta1).real
        {e : Fin n → ZMod 2 | decode (encode m + e) ≠ encode m} ≤
      binomTail n (t + 1) delta := by
  have hsub : {e : Fin n → ZMod 2 | decode (encode m + e) ≠ encode m} ⊆
      {e : Fin n → ZMod 2 | t + 1 ≤ hammingNorm e} := by
    intro e he
    exact weight_gt_t_of_decode_ne n k t encode decode hcorrect m e he
  have hle := MeasureTheory.measureReal_mono hsub
    (MeasureTheory.measure_lt_top (bscMeasure n delta hdelta0 hdelta1)
      {e : Fin n → ZMod 2 | t + 1 ≤ hammingNorm e}).ne
  rw [bsc_real_weight_ge_eq_binomTail n (t + 1) delta hdelta0 hdelta1] at hle
  exact hle

/-- If `t >= n`, every error is corrected and block-error
probability is `0`. -/
theorem boundedDistance_bsc_error_eq_zero_of_le (n k t : ℕ)
    (encode : (Fin k → ZMod 2) → (Fin n → ZMod 2))
    (decode : (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (hcorrect : ∀ (msg : Fin k → ZMod 2) (e : Fin n → ZMod 2),
      hammingNorm e ≤ t → decode (encode msg + e) = encode msg)
    (hnt : n ≤ t) (m : Fin k → ZMod 2) (delta : ℝ)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    (bscMeasure n delta hdelta0 hdelta1).real
        {e : Fin n → ZMod 2 | decode (encode m + e) ≠ encode m} = 0 := by
  have hsub : {e : Fin n → ZMod 2 | decode (encode m + e) ≠ encode m} ⊆ ∅ := by
    intro e he
    exact absurd (hcorrect m e (le_trans (hammingNorm_le_n n e) hnt)) he
  have hle := MeasureTheory.measureReal_mono hsub
    (MeasureTheory.measure_lt_top (bscMeasure n delta hdelta0 hdelta1) ∅).ne
  rw [MeasureTheory.measureReal_empty] at hle
  exact le_antisymm hle MeasureTheory.measureReal_nonneg


/-- The concrete Hamming (7,4) code of `Cslib.CodingTheory.Hamming74`
over the BSC: since its decoder corrects every error of weight at
most `1` (`Hamming74.decode_add`), the block-error probability is at
most `ProbabilityTheory.binomTail 7 2 delta`. -/
theorem hamming74_bsc_error_le (m : Fin 4 → ZMod 2) (delta : ℝ)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    (bscMeasure 7 delta hdelta0 hdelta1).real
        {e : Fin 7 → ZMod 2 | Cslib.CodingTheory.Hamming74.decode
          (Cslib.CodingTheory.Hamming74.encode m + e)
          ≠ Cslib.CodingTheory.Hamming74.encode m}
      ≤ ProbabilityTheory.binomTail 7 2 delta :=
  boundedDistance_bsc_error_le_binomTail 7 4 1
    Cslib.CodingTheory.Hamming74.encode Cslib.CodingTheory.Hamming74.decode
    (fun msg e he => Cslib.CodingTheory.Hamming74.decode_add
      (Cslib.CodingTheory.Hamming74.encode_mem_code msg) he)
    m delta hdelta0 hdelta1

end Cslib.CodingTheory.BoundedDistanceBSC
