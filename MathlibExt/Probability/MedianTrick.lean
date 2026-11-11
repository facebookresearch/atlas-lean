/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.GetD
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.SubGaussian

@[expose] public section

/-! # The median trick (confidence amplification)

If each of an odd number `r` of independent estimates is within `ε` of `μ`
with probability at least `3/4`, then their median is within `ε` of `μ`
except with probability at most `exp (-r / 8)`: repeating an estimate and
taking the median amplifies confidence exponentially in the number of
repetitions. This is the first half of roadmap package ML-36 of the Atlas
TCS canon roadmap; the median-of-means corollary is a follow-up.

The proof counts bad estimates on each outcome (a bad median forces at
least `(r + 1) / 2` bad estimates) and applies Hoeffding's inequality to
the independent bad-event indicators, each of mean at most `1 / 4`.

For `ε < 0` the hypothesis `hbd` is unsatisfiable, so the statement is
vacuous there; the intended range is `0 ≤ ε`.

Source: Jerrum, Valiant and Vazirani (1986); Alon, Matias and Szegedy
(1996); see also the median-trick chapter of any randomized-algorithms
text (e.g. Motwani and Raghavan, Randomized Algorithms, 1995).
-/

open MeasureTheory ProbabilityTheory

/-- The median of finitely many reals: the middle element of the sorted
list of values (index `r / 2`), or `0` for the empty family. -/
noncomputable def medianOf {r : ℕ} (X : Fin r → ℝ) : ℝ :=
  ((Finset.univ.val.map X).sort (· ≤ ·)).getD (r / 2) 0

-- Helper: sorted list length
private lemma sorted_length (r : ℕ) (f : Fin r → ℝ) :
    (((Finset.univ.val.map f).sort (· ≤ ·)).length = r) := by
  rw [Multiset.length_sort]
  rw [Multiset.card_map]
  rw [Finset.card_val]
  simp

-- Helper: median equals get
private lemma median_eq_get (r : ℕ) (f : Fin r → ℝ)
    (hlt : r / 2 < (((Finset.univ.val.map f).sort (· ≤ ·)).length)) :
    medianOf f = (((Finset.univ.val.map f).sort (· ≤ ·)).get ⟨r / 2, hlt⟩) := by
  unfold medianOf
  have h1 : ((((Finset.univ.val.map f).sort (· ≤ ·))).getD (r / 2) 0)
      = ((((Finset.univ.val.map f).sort (· ≤ ·)))[r / 2]'hlt) :=
    List.getD_eq_getElem _ _ hlt
  have h2 : ((((Finset.univ.val.map f).sort (· ≤ ·)).get ⟨r / 2, hlt⟩))
      = ((((Finset.univ.val.map f).sort (· ≤ ·)))[r / 2]'hlt) := by
    rw [List.get_eq_getElem]
  rw [h1, h2]

-- Helper: filter card equals multiset countP
private lemma filter_card_eq_countP (r : ℕ) (f : Fin r → ℝ) (μ ε : ℝ) :
    (Finset.univ.filter (fun i => ε < |f i - μ|)).card
      = (Finset.univ.val.map f).countP (fun x => ε < |x - μ|) := by
  rw [Multiset.countP_map]
  rw [← Finset.filter_val]
  rfl

-- Upper-tail element helper: everything in drop k is bad
private lemma drop_mem_bad (L : List ℝ) (hpair : L.Pairwise (· ≤ ·)) (k : ℕ)
    (hk : k < L.length) (μ ε : ℝ) (hε : 0 ≤ ε)
    (hup : μ + ε < L.get ⟨k, hk⟩) :
    ∀ a ∈ L.drop k, ε < |a - μ| := by
  intro a ha
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp ha
  have hkj : k + j.val < L.length := by
    have h1 := j.isLt
    have hlen : (L.drop k).length = L.length - k := List.length_drop
    omega
  have hjval : (L.drop k).get j = L.get ⟨k + j.val, hkj⟩ := by
    have e1 : (L.drop k).get j = (L.drop k)[j.val]'j.isLt := by rw [List.get_eq_getElem]
    have e2 : (L.drop k)[j.val]'j.isLt = L[k + j.val]'hkj :=
      List.getElem_drop (h := j.isLt)
    have e3 : L.get ⟨k + j.val, hkj⟩ = L[k + j.val]'hkj := by
      rw [List.get_eq_getElem]
    rw [e1, e2, ← e3]
  have hle : (⟨k, hk⟩ : Fin L.length) ≤ ⟨k + j.val, hkj⟩ := by
    simp
  have hmono : L.get ⟨k, hk⟩ ≤ L.get ⟨k + j.val, hkj⟩ :=
    hpair.rel_get_of_le hle
  have ham : a = L.get ⟨k + j.val, hkj⟩ := by
    rw [← hj, hjval]
  have hnonneg : 0 ≤ a - μ := by
    have : μ + ε < a := by rw [ham]; linarith [hup, hmono]
    linarith
  rw [abs_of_nonneg hnonneg]
  rw [ham]
  linarith [hup, hmono]

-- Lower-tail element helper: everything in take (k+1) is bad
private lemma take_mem_bad (L : List ℝ) (hpair : L.Pairwise (· ≤ ·)) (k : ℕ)
    (hk : k < L.length) (μ ε : ℝ) (hε : 0 ≤ ε)
    (hlo : L.get ⟨k, hk⟩ < μ - ε) :
    ∀ a ∈ L.take (k + 1), ε < |a - μ| := by
  intro a ha
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp ha
  have h1 := j.isLt
  have hlen : (L.take (k + 1)).length = min (k + 1) L.length := List.length_take
  have hjL : j.val < L.length := by omega
  have hjle : j.val ≤ k := by omega
  have hjval : (L.take (k + 1)).get j = L.get ⟨j.val, hjL⟩ := by
    have e1 : (L.take (k + 1)).get j = (L.take (k + 1))[j.val]'j.isLt := by
      rw [List.get_eq_getElem]
    have e2 : (L.take (k + 1))[j.val]'j.isLt = L[j.val]'hjL :=
      List.getElem_take (h := j.isLt)
    have e3 : L.get ⟨j.val, hjL⟩ = L[j.val]'hjL := by rw [List.get_eq_getElem]
    rw [e1, e2, ← e3]
  have hle : (⟨j.val, hjL⟩ : Fin L.length) ≤ ⟨k, hk⟩ := by
    simp only [Fin.mk_le_mk]
    omega
  have hmono : L.get ⟨j.val, hjL⟩ ≤ L.get ⟨k, hk⟩ := hpair.rel_get_of_le hle
  have ham : a = L.get ⟨j.val, hjL⟩ := by rw [← hj, hjval]
  have hneg : a - μ < 0 := by
    have : a < μ - ε := by rw [ham]; linarith [hlo, hmono]
    linarith
  rw [abs_of_neg hneg]
  rw [ham]
  linarith [hlo, hmono]

-- Measurability of the bad set in ℝ
private lemma measSet_bad_real (μ ε : ℝ) : MeasurableSet {x : ℝ | ε < |x - μ|} :=
  measurableSet_lt measurable_const (by fun_prop)

-- Measurability of the bad indicator in ℝ
private lemma meas_indicator_bad (μ ε : ℝ) :
    Measurable ({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) :=
  measurable_const.indicator (measSet_bad_real μ ε)

-- Indicator over Ω equals indicator over ℝ composed with X
private lemma indicator_comp_eq (Ω : Type*) (μ ε : ℝ) (X : Ω → ℝ) (ω : Ω) :
    (({ω : Ω | ε < |X ω - μ|}.indicator (1 : Ω → ℝ)) ω)
      = (({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) (X ω)) := by
  by_cases h : ω ∈ {ω : Ω | ε < |X ω - μ|}
  · have hx : X ω ∈ {x : ℝ | ε < |x - μ|} := h
    simp [Set.indicator_of_mem h, Set.indicator_of_mem hx]
  · have hx : X ω ∉ {x : ℝ | ε < |x - μ|} := h
    rw [Set.indicator_of_notMem h, Set.indicator_of_notMem hx]

-- Counting lemma (deterministic)
private lemma count_bad_of_median_bad (r : ℕ) (hr : Odd r) (f : Fin r → ℝ) (μ ε : ℝ)
    (h : ε < |medianOf f - μ|) :
    (r + 1) / 2 ≤ (Finset.univ.filter (fun i => ε < |f i - μ|)).card := by
  obtain ⟨kk, hk⟩ := hr
  by_cases hε : ε < 0
  · have hall : ∀ i : Fin r, ε < |f i - μ| := fun i => lt_of_lt_of_le hε (abs_nonneg _)
    have hfilter : Finset.univ.filter (fun i => ε < |f i - μ|) = Finset.univ :=
      Finset.filter_true_of_mem (fun i _ => hall i)
    rw [hfilter, Finset.card_univ, Fintype.card_fin]
    omega
  · push Not at hε
    have hlen : (((Finset.univ.val.map f).sort (· ≤ ·)).length) = r := sorted_length r f
    have hpair : (((Finset.univ.val.map f).sort (· ≤ ·)).Pairwise (· ≤ ·)) :=
      Multiset.pairwise_sort _ _
    have hkr : r / 2 < r := by omega
    have hlt : r / 2 < (((Finset.univ.val.map f).sort (· ≤ ·)).length) := by omega
    have hmed : medianOf f = (((Finset.univ.val.map f).sort (· ≤ ·)).get ⟨r / 2, hlt⟩) :=
      median_eq_get r f hlt
    have hsplit : μ + ε < medianOf f ∨ medianOf f < μ - ε := by
      by_cases hle : μ ≤ medianOf f
      · left
        have habs : |medianOf f - μ| = medianOf f - μ := abs_of_nonneg (by linarith)
        rw [habs] at h
        linarith
      · right
        push Not at hle
        have habs : |medianOf f - μ| = -(medianOf f - μ) :=
          abs_of_neg (by linarith)
        rw [habs] at h
        linarith
    have hsort : (↑(((Finset.univ.val.map f).sort (· ≤ ·))) : Multiset ℝ)
        = Finset.univ.val.map f := Multiset.sort_eq _ _
    rcases hsplit with hup | hlo
    · -- Upper tail: use drop
      have hup' : μ + ε < (((Finset.univ.val.map f).sort (· ≤ ·)).get ⟨r / 2, hlt⟩) := by
        rw [← hmed]; exact hup
      have hall : ∀ a ∈ (((Finset.univ.val.map f).sort (· ≤ ·)).drop (r / 2)),
          ε < |a - μ| :=
        drop_mem_bad _ hpair _ hlt _ _ hε hup'
      have h_all : ∀ a ∈ (↑((((Finset.univ.val.map f).sort (· ≤ ·)).drop (r / 2)))
          : Multiset ℝ), ε < |a - μ| :=
        fun a ha => hall a (Multiset.mem_coe.mp ha)
      have h_eq := Multiset.countP_eq_card.mpr h_all
      have h_card := Multiset.coe_card ((((Finset.univ.val.map f).sort (· ≤ ·)).drop (r / 2)))
      have hle_sub : (↑((((Finset.univ.val.map f).sort (· ≤ ·)).drop (r / 2))) : Multiset ℝ)
          ≤ ↑(((Finset.univ.val.map f).sort (· ≤ ·))) :=
        Multiset.coe_le.mpr (List.drop_sublist _ _).subperm
      have hle_count := Multiset.countP_le_of_le (fun x => ε < |x - μ|) hle_sub
      rw [hsort] at hle_count
      have hlen_drop : ((((Finset.univ.val.map f).sort (· ≤ ·)).drop (r / 2)).length)
          = r - r / 2 := by rw [List.length_drop, hlen]
      have hhalf : r - r / 2 = (r + 1) / 2 := by omega
      rw [filter_card_eq_countP]
      omega
    · -- Lower tail: use take
      have hlo' : (((Finset.univ.val.map f).sort (· ≤ ·)).get ⟨r / 2, hlt⟩) < μ - ε := by
        rw [← hmed]; exact hlo
      have hall : ∀ a ∈ (((Finset.univ.val.map f).sort (· ≤ ·)).take (r / 2 + 1)),
          ε < |a - μ| :=
        take_mem_bad _ hpair _ hlt _ _ hε hlo'
      have h_all : ∀ a ∈ (↑((((Finset.univ.val.map f).sort (· ≤ ·)).take (r / 2 + 1)))
          : Multiset ℝ), ε < |a - μ| :=
        fun a ha => hall a (Multiset.mem_coe.mp ha)
      have h_eq := Multiset.countP_eq_card.mpr h_all
      have h_card := Multiset.coe_card ((((Finset.univ.val.map f).sort (· ≤ ·)).take (r / 2 + 1)))
      have hle_sub : (↑((((Finset.univ.val.map f).sort (· ≤ ·)).take (r / 2 + 1))) : Multiset ℝ)
          ≤ ↑(((Finset.univ.val.map f).sort (· ≤ ·))) :=
        Multiset.coe_le.mpr (List.take_sublist _ _).subperm
      have hle_count := Multiset.countP_le_of_le (fun x => ε < |x - μ|) hle_sub
      rw [hsort] at hle_count
      have hlen_take : ((((Finset.univ.val.map f).sort (· ≤ ·)).take (r / 2 + 1)).length)
          = r / 2 + 1 := by
        rw [List.length_take, hlen, Nat.min_eq_left (by omega)]
      have hhalf : r / 2 + 1 = (r + 1) / 2 := by omega
      rw [filter_card_eq_countP]
      omega

theorem median_trick {r : ℕ} (hr : Odd r) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ ε : ℝ}
    {X : Fin r → Ω → ℝ} (hX : iIndepFun X P) (hXm : ∀ i, Measurable (X i))
    (hbd : ∀ i, P {ω | ε < |X i ω - μ|} ≤ 1 / 4) :
    P {ω | ε < |medianOf (fun i => X i ω) - μ|} ≤
      ENNReal.ofReal (Real.exp (-(r / 8 : ℝ))) := by
  obtain ⟨kk, hk⟩ := hr
  have hrOdd : Odd r := ⟨kk, hk⟩
  have hr0 : (r : ℝ) ≠ 0 := by
    have hne : r ≠ 0 := by omega
    exact_mod_cast hne
  have measB : ∀ i, MeasurableSet {ω : Ω | ε < |X i ω - μ|} := fun i =>
    measurableSet_lt measurable_const (((hXm i).sub_const _).abs)
  have h0meas : Measurable ({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) :=
    meas_indicator_bad μ ε
  have hY : iIndepFun
      (fun i ω => ({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) (X i ω)) P :=
    hX.comp (fun _ => ({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ))) (fun _ => h0meas)
  have hYmeas : ∀ i, Measurable
      (fun ω => ({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) (X i ω)) :=
    fun i => h0meas.comp (hXm i)
  have hYIcc : ∀ i, ∀ᵐ ω ∂P,
      (fun ω => ({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) (X i ω)) ω
        ∈ Set.Icc (0:ℝ) 1 :=
    fun i => ae_of_all P (fun ω => by
      show ({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) (X i ω) ∈ Set.Icc (0:ℝ) 1
      by_cases hx : X i ω ∈ {x : ℝ | ε < |x - μ|}
      · simp only [Set.indicator_of_mem hx, Pi.one_apply]
        norm_num
      · simp only [Set.indicator_of_notMem hx]
        norm_num)
  have hYint : ∀ i, (∫ ω, ({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) (X i ω) ∂P)
      = P.real {ω | ε < |X i ω - μ|} := fun i => by
    have h_eq : ∀ ω, ((({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) (X i ω))
        = ((({ω : Ω | ε < |X i ω - μ|}.indicator (1 : Ω → ℝ)) ω))) :=
      fun ω => (indicator_comp_eq Ω μ ε (X i) ω).symm
    simp only [h_eq]
    exact integral_indicator_one (measB i)
  have hbdr : ∀ i, P.real {ω | ε < |X i ω - μ|} ≤ 1 / 4 := fun i => by
    have h4 : (1 / 4 : ENNReal) ≠ ⊤ := by simp
    have h := ENNReal.toReal_mono h4 (hbd i)
    simpa [measureReal_def] using h
  have hZ : iIndepFun
      (fun i ω => ({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) (X i ω)
        - ∫ a, ({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) (X i a) ∂P) P :=
    hY.comp
      (fun i x => x - ∫ a, ({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) (X i a) ∂P)
      (fun i => by fun_prop)
  have h_subG : ∀ i ∈ Finset.univ,
      HasSubgaussianMGF
        (fun ω => ({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) (X i ω)
          - ∫ a, ({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) (X i a) ∂P)
        (1/4 : NNReal) P := fun i _ => by
    have hm : AEMeasurable
        (fun ω => ({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) (X i ω)) P :=
      (hYmeas i).aemeasurable
    have hb : ∀ᵐ ω ∂P, (fun ω => ({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) (X i ω)) ω
        ∈ Set.Icc (0:ℝ) 1 := hYIcc i
    have h := hasSubgaussianMGF_of_mem_Icc (a := (0:ℝ)) (b := (1:ℝ)) hm hb
    have hparam : ((nnnorm ((1:ℝ) - 0) / 2)^2 : NNReal) = 1/4 := by simp; norm_num
    rw [hparam] at h
    exact h
  have hε4 : (0:ℝ) ≤ (r:ℝ)/4 := by
    have hnn : (0:ℝ) ≤ (r:ℝ) := Nat.cast_nonneg _
    linarith
  have htail := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    (s := Finset.univ) (c := fun _ => (1/4 : NNReal)) (ε := (r:ℝ)/4) hZ h_subG hε4
  have hsub : {ω : Ω | ε < |medianOf (fun i => X i ω) - μ|}
      ⊆ {ω : Ω | (r:ℝ)/4 ≤ ∑ i ∈ Finset.univ,
        ((({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) (X i ω))
          - ∫ a, ({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) (X i a) ∂P)} := by
    intro ω hω
    show (r:ℝ)/4 ≤ ∑ i ∈ Finset.univ,
        ((({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) (X i ω))
          - ∫ a, ({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) (X i a) ∂P)
    have hcount := count_bad_of_median_bad r hrOdd (fun i => X i ω) μ ε hω
    have hterm : ∀ i : Fin r, ((({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) (X i ω))
        = (if ε < |X i ω - μ| then (1:ℝ) else 0)) := fun i => by
      by_cases hi : ε < |X i ω - μ|
      · simp [hi]
      · simp [hi]
    have hsumY : (∑ i ∈ Finset.univ,
          ((({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) (X i ω))))
        = ((Finset.univ.filter (fun i => ε < |X i ω - μ|)).card : ℝ) := by
      simp only [hterm]
      simp
    have hE : (∑ i ∈ Finset.univ,
          (∫ a, ({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) (X i a) ∂P))
        ≤ (r:ℝ)/4 := by
      have h1 : (∑ i ∈ Finset.univ,
            (∫ a, ({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) (X i a) ∂P))
          ≤ ∑ _i ∈ (Finset.univ : Finset (Fin r)), (1/4 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        rw [hYint i]
        exact hbdr i
      have h2 : (∑ _i ∈ (Finset.univ : Finset (Fin r)), (1/4:ℝ)) = (r:ℝ)/4 := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
      linarith
    have hZeq : (∑ i ∈ Finset.univ,
          (((({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) (X i ω))
            - ∫ a, ({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) (X i a) ∂P)))
        = (∑ i ∈ Finset.univ,
            ((({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) (X i ω))))
          - (∑ i ∈ Finset.univ,
            (∫ a, ({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) (X i a) ∂P)) :=
      Finset.sum_sub_distrib _ _
    have hhalf : (r:ℝ)/2 ≤ ((((r+1)/2 : ℕ)) : ℝ) := by
      have h_eq_nat : (r+1)/2 = kk+1 := by omega
      have hr_real : (r:ℝ) = 2*(kk:ℝ)+1 := by exact_mod_cast hk
      rw [h_eq_nat]
      push_cast
      linarith
    have hcard_real : ((((r+1)/2 : ℕ)) : ℝ)
        ≤ ((Finset.univ.filter (fun i => ε < |X i ω - μ|)).card : ℝ) :=
      by exact_mod_cast hcount
    rw [hZeq]
    linarith [hsumY, hE, hhalf, hcard_real]
  have hfin_tail : P {ω : Ω | (r:ℝ)/4 ≤ ∑ i ∈ Finset.univ,
      ((({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) (X i ω))
        - ∫ a, ({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) (X i a) ∂P)} ≠ ⊤ := by
    finiteness
  have hreal_le : P.real {ω | ε < |medianOf (fun i => X i ω) - μ|}
      ≤ P.real {ω : Ω | (r:ℝ)/4 ≤ ∑ i ∈ Finset.univ,
        ((({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) (X i ω))
          - ∫ a, ({x : ℝ | ε < |x - μ|}.indicator (1 : ℝ → ℝ)) (X i a) ∂P)} :=
    measureReal_mono hsub hfin_tail
  have hsum_nn : (↑(∑ _i ∈ (Finset.univ : Finset (Fin r)), (1/4 : NNReal)) : ℝ)
      = (r:ℝ)/4 := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring
  rw [hsum_nn] at htail
  have hexp : -((r:ℝ)/4)^2 / (2 * ((r:ℝ)/4)) = -((r:ℝ)/8) := by
    field_simp
    ring
  rw [hexp] at htail
  have hreal : P.real {ω | ε < |medianOf (fun i => X i ω) - μ|}
      ≤ Real.exp (-((r:ℝ)/8)) := le_trans hreal_le htail
  have hfin_bad : P {ω | ε < |medianOf (fun i => X i ω) - μ|} ≠ ⊤ := by finiteness
  rw [← ofReal_measureReal hfin_bad]
  exact ENNReal.ofReal_le_ofReal hreal

