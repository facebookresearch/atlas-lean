/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Nonparametric.RankFreeness

/-!
# Tests for distribution-freeness of ranks under continuity

* Positive case: two independent coordinates with a common law without atoms satisfy
  `P(X 0 < X 1) = 1 / 2`.
* Boundary case: the no-atom hypothesis is a real restriction; a Dirac law has an atom.
* Degenerate case: a one-point sample has rank vector `fun _ => 1`.
* Convention case: tied entries share the smallest rank of their tie group:
  `sampleRank ![2, 1, 2] = ![2, 1, 2]`.
* Rank-law API case: `rankLaw n` is a probability measure, and its masses `(n!)⁻¹` at the `n!`
  permutation vectors add up to `1`.
* Rank-law case: by `sampleRank_uniform_of_nonatomic` each rank vector `permVec σ` has
  probability `(n!)⁻¹`; for `n = 2` the rank law alone gives `P(X 0 < X 1) = 1 / 2`.
* Independence case: by `rank_indep_of_sorted` a rank event and an order-statistics event factor,
  `P(sampleRank = permVec σ, orderStatistic ∈ T) = (n!)⁻¹ * P(orderStatistic ∈ T)`.
* No-ties case: by `ae_injective_of_nonatomic` two distinct coordinates tie with probability `0`.
* Ties case: under the atomic law `dirac 0` all entries tie for the minimum rank, so the rank
  vector is a.s. the all-`1` vector, which has `rankLaw n`-mass `0` for `n ≥ 2`, so the rank law
  fails.
-/

@[expose] public section

open Filter Topology MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.Measurement
open scoped ENNReal

/-- Positive case: for `n = 2` this gives `P(X 0 < X 1) = 1 / 2`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin 2 → Ω → ℝ}
    (hIndep : iIndepFun X μ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hlaw : ∀ i, HasLaw (X i) ν μ)
    (hAtom : ∀ x, ν {x} = 0) :
    μ {ω | X ⟨0, by omega⟩ ω < X ⟨1, by omega⟩ ω} = (1 / 2 : ℝ≥0∞) := by
  set i0 : Fin 2 := ⟨0, by omega⟩ with hi0
  set i1 : Fin 2 := ⟨1, by omega⟩ with hi1
  have hne : i0 ≠ i1 := by decide
  have hindep : (X i0) ⟂ᵢ[μ] (X i1) := hIndep.indepFun hne
  have hpair_law : HasLaw (fun ω => (X i0 ω, X i1 ω)) (ν.prod ν) μ :=
    IndepFun.hasLaw_prod (hlaw i0) (hlaw i1) hindep
  have hae : AEMeasurable (fun ω => (X i0 ω, X i1 ω)) μ := hpair_law.aemeasurable
  set A : Set (ℝ × ℝ) := {p | p.1 < p.2} with hA
  set B : Set (ℝ × ℝ) := {p | p.2 < p.1} with hB
  set D : Set (ℝ × ℝ) := Set.diagonal ℝ with hD
  have hAmeas : MeasurableSet A := (isOpen_lt continuous_fst continuous_snd).measurableSet
  have hBmeas : MeasurableSet B := (isOpen_lt continuous_snd continuous_fst).measurableSet
  have hDmeas : MeasurableSet D := isClosed_diagonal.measurableSet
  have htrans : μ {ω | X i0 ω < X i1 ω} = (ν.prod ν) A := by
    have hset : {ω | X i0 ω < X i1 ω} = (fun ω => (X i0 ω, X i1 ω)) ⁻¹' A := rfl
    rw [hset, ← Measure.map_apply_of_aemeasurable hae hAmeas, hpair_law.map_eq]
  have hswap : Measure.map Prod.swap (ν.prod ν) = ν.prod ν := Measure.prod_swap
  have hsymm : (ν.prod ν) A = (ν.prod ν) B := by
    have h : Measure.map Prod.swap (ν.prod ν) A = (ν.prod ν) (Prod.swap ⁻¹' A) :=
      Measure.map_apply measurable_swap hAmeas
    rw [hswap] at h
    have hpre : Prod.swap ⁻¹' A = B := by
      ext p
      simp [hA, hB]
    rw [hpre] at h
    exact h
  have hdiag_null : (ν.prod ν) (Set.diagonal ℝ) = 0 := by
    rw [Measure.prod_apply isClosed_diagonal.measurableSet]
    have hsec : ∀ x : ℝ, ν (Prod.mk x ⁻¹' Set.diagonal ℝ) = 0 := by
      intro x
      have hsub : Prod.mk x ⁻¹' Set.diagonal ℝ = {x} := by
        ext y
        simp [Set.diagonal, eq_comm]
      rw [hsub, hAtom x]
    simp [hsec]
  have hDnull : (ν.prod ν) D = 0 := by
    rw [hD]
    exact hdiag_null
  have hunion : A ∪ B ∪ D = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    simp only [hA, hB, hD, Set.mem_union]
    rcases lt_trichotomy p.1 p.2 with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (by simpa [Set.diagonal] using h)
    · exact Or.inl (Or.inr h)
  have hdisjAB : Disjoint A B := by
    rw [Set.disjoint_left]
    intro p hpA hpB
    rw [hA] at hpA
    rw [hB] at hpB
    change p.1 < p.2 at hpA
    change p.2 < p.1 at hpB
    exact absurd hpA (not_lt_of_gt hpB)
  have hdisjABD : Disjoint (A ∪ B) D := by
    rw [Set.disjoint_left]
    intro p hpAB hpD
    rw [hD] at hpD
    simp only [hA, hB, Set.mem_union] at hpAB
    have hpD' : p.1 = p.2 := hpD
    rcases hpAB with h | h
    · change p.1 < p.2 at h
      rw [hpD'] at h
      exact absurd h (lt_irrefl _)
    · change p.2 < p.1 at h
      rw [hpD'] at h
      exact absurd h (lt_irrefl _)
  have hun : (ν.prod ν) A + (ν.prod ν) A = 1 := by
    have h1 : (ν.prod ν) Set.univ = 1 := measure_univ
    rw [← hunion, measure_union hdisjABD hDmeas, measure_union hdisjAB hBmeas, ← hsymm, hDnull] at h1
    simpa [add_zero] using h1
  have hx_top : (ν.prod ν) A ≠ ⊤ := by
    intro h
    rw [h] at hun
    simp at hun
  have hreal : ((ν.prod ν) A).toReal = 1 / 2 := by
    have h2 := congrArg ENNReal.toReal hun
    rw [ENNReal.toReal_add hx_top hx_top, ENNReal.toReal_one] at h2
    linarith
  have h2real : (1/2 : ℝ≥0∞).toReal = 1 / 2 := by
    rw [ENNReal.toReal_div, ENNReal.toReal_one]
    have h2 : (2 : ℝ≥0∞).toReal = 2 := by
      conv_lhs => rw [← ENNReal.ofReal_ofNat 2]
      exact ENNReal.toReal_ofReal (by norm_num)
    rw [h2]
  have h2top : (1/2 : ℝ≥0∞) ≠ ⊤ := by simp
  have hfin : (ν.prod ν) A = 1 / 2 := by
    calc (ν.prod ν) A = ENNReal.ofReal (((ν.prod ν) A).toReal) :=
            (ENNReal.ofReal_toReal hx_top).symm
      _ = ENNReal.ofReal (1/2) := by rw [hreal]
      _ = ENNReal.ofReal ((1/2 : ℝ≥0∞).toReal) := by rw [h2real]
      _ = 1/2 := ENNReal.ofReal_toReal h2top
  rw [htrans, hfin]

/-- Boundary case: atoms are genuinely excluded; a Dirac law has an atom. -/
example : ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ∃ x, ν {x} ≠ 0 :=
  ⟨Measure.dirac 0, inferInstance, 0, by simp⟩

/-- Degenerate case: a one-point sample always has rank one. -/
example (x : Fin 1 → ℝ) : sampleRank x = fun _ => 1 := by
  funext i
  simp only [sampleRank]
  have hempty : Finset.univ.filter (fun j => x j < x i) = ∅ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hji : j = i := Subsingleton.elim j i
    subst hji
    simp
  rw [hempty]
  simp

/-- Convention case: `sampleRank` gives competition (minimum) ranks; the two tied entries share
rank `2`, where the maximum-rank convention would give `3`. -/
example : sampleRank ![(2 : ℝ), 1, 2] = ![2, 1, 2] := by
  funext i
  simp only [sampleRank, Finset.card_filter, Fin.sum_univ_three]
  fin_cases i <;> norm_num

namespace RankFreenessTest

/-- Rank-law API case: `rankLaw n` is a probability measure (for `n = 0` too), and its masses
`(n!)⁻¹` at the `n!` permutation vectors add up to `1`. -/
example (n : ℕ) :
    rankLaw n Set.univ = 1 ∧ ∑ σ : Equiv.Perm (Fin n), rankLaw n {permVec σ} = 1 := by
  refine ⟨measure_univ, ?_⟩
  simp only [rankLaw_singleton_permVec, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel (by exact_mod_cast n.factorial_ne_zero) (ENNReal.natCast_ne_top _)

/-- Rank-law case: by `sampleRank_uniform_of_nonatomic`, each of the `n!` rank vectors `permVec σ`
has probability `(n!)⁻¹`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    {X : Fin n → Ω → ℝ} (hIndep : iIndepFun X μ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hlaw : ∀ i, HasLaw (X i) ν μ)
    (hAtom : ∀ x, ν {x} = 0) (σ : Equiv.Perm (Fin n)) :
    μ {ω | sampleRank (fun j => X j ω) = permVec σ} = (n.factorial : ℝ≥0∞)⁻¹ := by
  have hrank := sampleRank_uniform_of_nonatomic hIndep ν hlaw hAtom
  have h : μ {ω | sampleRank (fun j => X j ω) = permVec σ} = rankLaw n {permVec σ} :=
    hrank.measure_eq (p := fun r => r = permVec σ) (measurableSet_singleton _)
  rw [h, rankLaw_singleton_permVec]

/-- Positive case through the rank law: for `n = 2`, `X 0 < X 1` holds exactly when the rank
vector is `permVec 1 = (1, 2)`, so `sampleRank_uniform_of_nonatomic` gives
`P(X 0 < X 1) = (2!)⁻¹ = 1 / 2` without the symmetry argument of the first example. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin 2 → Ω → ℝ} (hIndep : iIndepFun X μ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hlaw : ∀ i, HasLaw (X i) ν μ)
    (hAtom : ∀ x, ν {x} = 0) :
    μ {ω | X 0 ω < X 1 ω} = (1 / 2 : ℝ≥0∞) := by
  have hrank := sampleRank_uniform_of_nonatomic hIndep ν hlaw hAtom
  have hevent : ∀ x : Fin 2 → ℝ, sampleRank x = permVec 1 ↔ x 0 < x 1 := by
    intro x
    simp only [funext_iff, Fin.forall_fin_two, sampleRank, permVec, Finset.card_filter,
      Fin.sum_univ_two, Equiv.Perm.one_apply]
    by_cases h : x 0 < x 1
    · simp [h, h.le]
    · simp [h]
  have hset : {ω | X 0 ω < X 1 ω} = {ω | sampleRank (fun j => X j ω) = permVec 1} := by
    ext ω
    exact (hevent fun j => X j ω).symm
  have h : μ {ω | sampleRank (fun j => X j ω) = permVec 1} = rankLaw 2 {permVec 1} :=
    hrank.measure_eq (p := fun r => r = permVec 1) (measurableSet_singleton _)
  rw [hset, h, rankLaw_singleton_permVec]
  simp [Nat.factorial_two, one_div]

/-- Independence case: by `rank_indep_of_sorted` a rank event and an order-statistics event
factor, and by `sampleRank_uniform_of_nonatomic` the rank factor is `(n!)⁻¹`:
`P(sampleRank = permVec σ, orderStatistic ∈ T) = (n!)⁻¹ * P(orderStatistic ∈ T)`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    {X : Fin n → Ω → ℝ} (hIndep : iIndepFun X μ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hlaw : ∀ i, HasLaw (X i) ν μ)
    (hAtom : ∀ x, ν {x} = 0) (σ : Equiv.Perm (Fin n)) {T : Set (Fin n → ℝ)}
    (hT : MeasurableSet T) :
    μ {ω | sampleRank (fun j => X j ω) = permVec σ ∧ orderStatistic (fun j => X j ω) ∈ T}
      = (n.factorial : ℝ≥0∞)⁻¹ * μ {ω | orderStatistic (fun j => X j ω) ∈ T} := by
  have hind := rank_indep_of_sorted hIndep ν hlaw hAtom
  have hrank := sampleRank_uniform_of_nonatomic hIndep ν hlaw hAtom
  have hprod : μ {ω | sampleRank (fun j => X j ω) = permVec σ ∧ orderStatistic (fun j => X j ω) ∈ T}
      = μ {ω | sampleRank (fun j => X j ω) = permVec σ}
        * μ {ω | orderStatistic (fun j => X j ω) ∈ T} :=
    indepFun_iff_measure_inter_preimage_eq_mul.mp hind {permVec σ} T
      (measurableSet_singleton _) hT
  have hR : μ {ω | sampleRank (fun j => X j ω) = permVec σ} = rankLaw n {permVec σ} :=
    hrank.measure_eq (p := fun r => r = permVec σ) (measurableSet_singleton _)
  rw [hprod, hR, rankLaw_singleton_permVec]

/-- No-ties case: by `ae_injective_of_nonatomic`, two distinct coordinates of a sample from a
law without atoms are equal with probability `0`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    {X : Fin n → Ω → ℝ} (hIndep : iIndepFun X μ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hlaw : ∀ i, HasLaw (X i) ν μ)
    (hAtom : ∀ x, ν {x} = 0) {i j : Fin n} (hij : i ≠ j) :
    μ {ω | X i ω = X j ω} = 0 := by
  have hinj := ae_injective_of_nonatomic hIndep ν hlaw hAtom
  have hne : ∀ᵐ ω ∂μ, X i ω ≠ X j ω := hinj.mono fun ω hω heq => hij (hω heq)
  simpa [ae_iff] using hne

/-- Ties case: atoms break the rank law. Under the atomic law `dirac 0`, realized by the
coordinates of `Measure.pi` (measurable, independent and identically distributed), the sample is
a.s. constant, so every entry ties for the minimum rank and the rank vector is a.s. the all-`1`
vector. For `n ≥ 2` that vector is not a permutation vector and has `rankLaw n`-mass `0`, so the
conclusion of `sampleRank_uniform_of_nonatomic` fails; applied to this model, the theorem then
forces an atom. -/
example {n : ℕ} (hn : 2 ≤ n) :
    (Measure.pi fun _ : Fin n => Measure.dirac (0 : ℝ))
        {ω | sampleRank (fun j => ω j) = fun _ => 1} = 1 ∧
      rankLaw n {fun _ => 1} = 0 ∧
      ¬ HasLaw (fun ω : Fin n → ℝ => sampleRank (fun j => ω j)) (rankLaw n)
        (Measure.pi fun _ : Fin n => Measure.dirac (0 : ℝ)) ∧
      ¬ ∀ x, Measure.dirac (0 : ℝ) {x} = 0 := by
  have hconst : sampleRank (fun _ : Fin n => (0 : ℝ)) = fun _ => 1 := by
    funext i
    simp [sampleRank]
  have hone : (Measure.pi fun _ : Fin n => Measure.dirac (0 : ℝ))
      {ω | sampleRank (fun j => ω j) = fun _ => 1} = 1 := by
    refine le_antisymm prob_le_one ?_
    calc (1 : ℝ≥0∞)
        = (Measure.pi fun _ : Fin n => Measure.dirac (0 : ℝ)) (Set.univ.pi fun _ => {0}) := by
          rw [Measure.pi_pi]
          simp
      _ ≤ (Measure.pi fun _ : Fin n => Measure.dirac (0 : ℝ))
          {ω | sampleRank (fun j => ω j) = fun _ => 1} := by
          refine measure_mono fun ω hω => ?_
          have hω0 : ω = fun _ => 0 := funext fun i => hω i (Set.mem_univ i)
          subst hω0
          exact hconst
  have hzero : rankLaw n {fun _ => 1} = 0 := by
    refine rankLaw_singleton_of_notMem ?_
    rintro ⟨σ, h⟩
    have h1 := congrFun h (σ.symm ⟨1, by omega⟩)
    simp [permVec] at h1
  have hfail : ¬ HasLaw (fun ω : Fin n → ℝ => sampleRank (fun j => ω j)) (rankLaw n)
      (Measure.pi fun _ : Fin n => Measure.dirac (0 : ℝ)) := by
    intro hHas
    have h : (Measure.pi fun _ : Fin n => Measure.dirac (0 : ℝ))
        {ω | sampleRank (fun j => ω j) = fun _ => 1} = rankLaw n {fun _ => 1} :=
      hHas.measure_eq (p := fun r => r = fun _ => 1) (measurableSet_singleton _)
    rw [hone, hzero] at h
    exact one_ne_zero h
  have hIndep : iIndepFun (fun (i : Fin n) (ω : Fin n → ℝ) => ω i)
      (Measure.pi fun _ : Fin n => Measure.dirac (0 : ℝ)) :=
    iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id
  have hlaw : ∀ i, HasLaw (fun ω : Fin n → ℝ => ω i) (Measure.dirac (0 : ℝ))
      (Measure.pi fun _ : Fin n => Measure.dirac (0 : ℝ)) :=
    fun i => (measurePreserving_eval (fun _ : Fin n => Measure.dirac (0 : ℝ)) i).hasLaw
  exact ⟨hone, hzero, hfail, fun hAtom =>
    hfail (sampleRank_uniform_of_nonatomic hIndep (Measure.dirac 0) hlaw hAtom)⟩

end RankFreenessTest
