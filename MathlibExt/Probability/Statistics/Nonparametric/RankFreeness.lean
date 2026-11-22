/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.Scales
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.HasLaw

/-!
# Distribution-freeness of ranks under continuity

Let `X : Fin n → Ω → ℝ` have independent coordinates with a common law `ν` that has no atoms,
`∀ x, ν {x} = 0`. Ranks are the competition (minimum) ranks
`MathlibExt.Probability.Statistics.Measurement.sampleRank x i = 1 + #{j | x j < x i}`; tied
entries share the smallest rank of their tie group.

* `ProbabilityTheory.ae_injective_of_nonatomic`: almost surely the sample has no ties.
* `ProbabilityTheory.sampleRank_uniform_of_nonatomic`: the rank vector has law `rankLaw n`, the
  uniform law on the `n!` vectors `permVec σ = (i ↦ σ i + 1)` for permutations `σ` of `Fin n`.
* `ProbabilityTheory.rank_indep_of_sorted`: the rank vector is independent of the order
  statistics `MathlibExt.Probability.Statistics.Measurement.orderStatistic`, the sample sorted
  by `Tuple.sort`.

`rankLaw n` is `MeasureTheory.Measure.uniformOfFinset` on the permutation vectors; it is a
probability measure, with point masses `rankLaw_singleton_permVec` and
`rankLaw_singleton_of_notMem`.

Without ties the ranks form a permutation of `1, …, n`, and the exchangeability of the sample
makes every permutation equally likely. Ties, which need a mid-rank or randomized convention, are
not covered.

## References

* J. Hájek, Z. Šidák, P. K. Sen, *Theory of Rank Tests*, 2nd ed., Academic Press, 1999.
-/

@[expose] public section

open Filter Topology MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.Measurement
open scoped ENNReal

namespace ProbabilityTheory

/-- The rank vector of a permutation, `permVec σ i = σ i + 1`, with entries `1, …, n`. -/
noncomputable def permVec {n : ℕ} (σ : Equiv.Perm (Fin n)) : Fin n → ℕ :=
  fun i => (σ i).val + 1

private theorem permVec_injective {n : ℕ} : Function.Injective (@permVec n) := by
  intro σ τ h
  ext i
  have h2 := congrFun h i
  simp only [permVec] at h2
  omega

private theorem card_image_permVec (n : ℕ) :
    (Finset.univ.image (@permVec n)).card = n.factorial := by
  rw [Finset.card_image_of_injective _ permVec_injective, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin]

/-- Uniform law on rank vectors: `Measure.uniformOfFinset` on the `n!` permutation vectors
`permVec σ`. -/
noncomputable def rankLaw (n : ℕ) : Measure (Fin n → ℕ) :=
  Measure.uniformOfFinset (Finset.univ.image (@permVec n))

/-- `rankLaw n` is a probability measure for every `n`, including `n = 0`. -/
instance isProbabilityMeasure_rankLaw (n : ℕ) : IsProbabilityMeasure (rankLaw n) := by
  constructor
  rw [rankLaw, Measure.uniformOfFinset_apply]
  simp only [Set.mem_univ, Finset.filter_true, card_image_permVec]
  exact ENNReal.div_self (by exact_mod_cast n.factorial_ne_zero) (ENNReal.natCast_ne_top _)

/-- Each of the `n!` permutation vectors has `rankLaw n`-mass `(n!)⁻¹`. -/
theorem rankLaw_singleton_permVec {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    rankLaw n {permVec σ} = (n.factorial : ℝ≥0∞)⁻¹ := by
  rw [rankLaw, Measure.uniformOfFinset_apply_singleton_of_mem
    (Finset.mem_image_of_mem _ (Finset.mem_univ σ)), card_image_permVec]

/-- `rankLaw n` gives no mass to a vector that is not a permutation vector. -/
theorem rankLaw_singleton_of_notMem {n : ℕ} {r : Fin n → ℕ}
    (hr : r ∉ Set.range (@permVec n)) : rankLaw n {r} = 0 :=
  Measure.uniformOfFinset_apply_singleton_of_notMem (by simpa using hr)

private theorem sampleRank_equivariant {n : ℕ} (x : Fin n → ℝ) (τ : Equiv.Perm (Fin n)) :
    sampleRank (x ∘ τ) = sampleRank x ∘ τ := by
  funext i
  change 1 + (Finset.univ.filter (fun j => (x ∘ τ) j < (x ∘ τ) i)).card
      = 1 + (Finset.univ.filter (fun j => x j < x (τ i))).card
  rw [Finset.card_filter, Finset.card_filter]
  simp only [Function.comp_apply]
  congr 1
  exact Equiv.Perm.sum_comp τ Finset.univ (fun j => if x j < x (τ i) then (1:ℕ) else 0)
    (by simp)

private theorem measurable_sampleRank {n : ℕ} :
    Measurable (fun x : Fin n → ℝ => sampleRank x) := by
  rw [measurable_pi_iff]
  intro i
  have hcard : ∀ x : Fin n → ℝ, (Finset.univ.filter (fun j => x j < x i)).card
      = ∑ j ∈ Finset.univ, (if x j < x i then 1 else 0) :=
    fun x => Finset.card_filter _ _
  change Measurable (fun x : Fin n → ℝ => 1 + (Finset.univ.filter (fun j => x j < x i)).card)
  simp only [hcard]
  refine (measurable_from_nat (f := fun k : ℕ => 1 + k)).comp ?_
  apply Finset.measurable_sum
  intro j _
  apply Measurable.ite _ measurable_const measurable_const
  have hset : {x : Fin n → ℝ | x j < x i}
      = (fun x => (x j, x i)) ⁻¹' {p : ℝ × ℝ | p.1 < p.2} := rfl
  rw [hset]
  exact ((measurable_pi_apply j).prodMk (measurable_pi_apply i))
    ((isOpen_lt continuous_fst continuous_snd).measurableSet)

private theorem sampleRank_injective_of_injective {n : ℕ} {x : Fin n → ℝ}
    (hx : Function.Injective x) : Function.Injective (sampleRank x) := by
  intro i k hik
  by_contra hne
  rcases lt_or_gt_of_ne (hx.ne hne) with hlt | hlt
  · exact ((sampleRank_lt_sampleRank_iff x i k).mpr hlt).ne hik
  · exact ((sampleRank_lt_sampleRank_iff x k i).mpr hlt).ne hik.symm

private theorem sampleRank_mem_range_of_injective {n : ℕ} {x : Fin n → ℝ}
    (hx : Function.Injective x) : sampleRank x ∈ Set.range (@permVec n) := by
  have hrinj := sampleRank_injective_of_injective hx
  have hlo : ∀ i, 1 ≤ sampleRank x i := fun i => Nat.le_add_right _ _
  have hhi : ∀ i, sampleRank x i ≤ n := by
    intro i
    have hlt : (Finset.univ.filter (fun j => x j < x i)).card < n :=
      calc (Finset.univ.filter (fun j => x j < x i)).card
          < Finset.univ.card :=
            Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨i, Finset.mem_univ i, lt_irrefl _⟩)
        _ = n := by simp [Finset.card_univ, Fintype.card_fin]
    change 1 + (Finset.univ.filter (fun j => x j < x i)).card ≤ n
    omega
  have hb : ∀ i, sampleRank x i - 1 < n := fun i => by
    have h1 := hlo i
    have h2 := hhi i
    omega
  set s : Fin n → Fin n := fun i => ⟨sampleRank x i - 1, hb i⟩ with hs
  have hsinj : Function.Injective s := by
    intro i k hik
    have h2 : sampleRank x i - 1 = sampleRank x k - 1 := congrArg Fin.val hik
    have h1i := hlo i
    have h1k := hlo k
    have h3 : sampleRank x i = sampleRank x k := by omega
    exact hrinj h3
  have hsbij : Function.Bijective s := Finite.injective_iff_bijective.mp hsinj
  refine ⟨Equiv.ofBijective s hsbij, ?_⟩
  funext i
  simp only [permVec, Equiv.ofBijective_apply, hs]
  exact Nat.sub_add_cancel (hlo i)

private theorem measurable_orderStatistic {n : ℕ} :
    Measurable (fun x : Fin n → ℝ => orderStatistic x) := by
  have hE : ∀ σ : Equiv.Perm (Fin n),
      MeasurableSet {x : Fin n → ℝ | Tuple.sort x = σ} := by
    intro σ
    have hC : ∀ p : Fin n × Fin n, MeasurableSet
        ({x : Fin n → ℝ | p.1 ≤ p.2 → x (σ p.1) ≤ x (σ p.2)}
          ∩ {x : Fin n → ℝ | p.1 < p.2 → x (σ p.1) = x (σ p.2) → σ p.1 < σ p.2}) := by
      intro p
      apply MeasurableSet.inter
      · by_cases hle : p.1 ≤ p.2
        · have heq : {x : Fin n → ℝ | p.1 ≤ p.2 → x (σ p.1) ≤ x (σ p.2)}
              = {x : Fin n → ℝ | x (σ p.1) ≤ x (σ p.2)} := by
            ext x
            change (p.1 ≤ p.2 → x (σ p.1) ≤ x (σ p.2)) ↔ x (σ p.1) ≤ x (σ p.2)
            constructor
            · intro h
              exact h hle
            · intro h _
              exact h
          rw [heq]
          have hset : {x : Fin n → ℝ | x (σ p.1) ≤ x (σ p.2)}
              = (fun x => (x (σ p.1), x (σ p.2))) ⁻¹' {q : ℝ × ℝ | q.1 ≤ q.2} := rfl
          rw [hset]
          exact ((measurable_pi_apply _).prodMk (measurable_pi_apply _))
            ((isClosed_le continuous_fst continuous_snd).measurableSet)
        · have heq : {x : Fin n → ℝ | p.1 ≤ p.2 → x (σ p.1) ≤ x (σ p.2)} = Set.univ := by
            rw [Set.eq_univ_iff_forall]
            intro x h
            exact absurd h hle
          rw [heq]
          exact MeasurableSet.univ
      · by_cases hlt : p.1 < p.2
        · by_cases hsig : σ p.1 < σ p.2
          · have heq : {x : Fin n → ℝ | p.1 < p.2 → x (σ p.1) = x (σ p.2) → σ p.1 < σ p.2}
                = Set.univ := by
              rw [Set.eq_univ_iff_forall]
              intro x _ _
              exact hsig
            rw [heq]
            exact MeasurableSet.univ
          · have heq : {x : Fin n → ℝ | p.1 < p.2 → x (σ p.1) = x (σ p.2) → σ p.1 < σ p.2}
                = {x : Fin n → ℝ | x (σ p.1) ≠ x (σ p.2)} := by
              ext x
              constructor
              · intro h heq2
                exact hsig (h hlt heq2)
              · intro h _ heq2
                exact absurd heq2 h
            rw [heq]
            have hbase : MeasurableSet {x : Fin n → ℝ | x (σ p.1) = x (σ p.2)} := by
              have hset2 : {x : Fin n → ℝ | x (σ p.1) = x (σ p.2)}
                  = (fun x => (x (σ p.1), x (σ p.2))) ⁻¹' Set.diagonal ℝ := rfl
              rw [hset2]
              exact ((measurable_pi_apply _).prodMk (measurable_pi_apply _))
                (isClosed_diagonal.measurableSet)
            have hset : {x : Fin n → ℝ | x (σ p.1) ≠ x (σ p.2)}
                = {x : Fin n → ℝ | x (σ p.1) = x (σ p.2)}ᶜ := by
              ext x
              simp
            rw [hset]
            exact hbase.compl
        · have heq : {x : Fin n → ℝ | p.1 < p.2 → x (σ p.1) = x (σ p.2) → σ p.1 < σ p.2}
              = Set.univ := by
            rw [Set.eq_univ_iff_forall]
            intro x h
            exact absurd h hlt
          rw [heq]
          exact MeasurableSet.univ
    have hEq : {x : Fin n → ℝ | Tuple.sort x = σ}
        = ⋂ p : Fin n × Fin n, ({x : Fin n → ℝ | p.1 ≤ p.2 → x (σ p.1) ≤ x (σ p.2)}
          ∩ {x : Fin n → ℝ | p.1 < p.2 → x (σ p.1) = x (σ p.2) → σ p.1 < σ p.2}) := by
      ext x
      simp only [Set.mem_iInter, Set.mem_inter_iff]
      change Tuple.sort x = σ ↔ ∀ p : Fin n × Fin n,
        (p.1 ≤ p.2 → x (σ p.1) ≤ x (σ p.2)) ∧
        (p.1 < p.2 → x (σ p.1) = x (σ p.2) → σ p.1 < σ p.2)
      constructor
      · intro hsort p
        have h := (Tuple.eq_sort_iff (f := x) (σ := σ)).mp hsort.symm
        constructor
        · intro hle
          exact h.1 hle
        · intro hlt heq
          exact h.2 p.1 p.2 hlt heq
      · intro h
        have hmon : Monotone (x ∘ ⇑σ) := by
          intro a b hab
          exact (h (a, b)).1 hab
        have hstab : ∀ i j : Fin n, i < j → x (σ i) = x (σ j) → σ i < σ j :=
          fun i j hlt heq => (h (i, j)).2 hlt heq
        exact ((Tuple.eq_sort_iff (f := x) (σ := σ)).mpr ⟨hmon, hstab⟩).symm
    rw [hEq]
    exact MeasurableSet.iInter hC
  intro T hT
  have hpsi : ∀ σ : Equiv.Perm (Fin n),
      Measurable (fun x : Fin n → ℝ => x ∘ ⇑σ) := by
    intro σ
    rw [measurable_pi_iff]
    intro i
    exact measurable_pi_apply (σ i)
  have hunion : (fun x : Fin n → ℝ => orderStatistic x) ⁻¹' T
      = ⋃ σ : Equiv.Perm (Fin n), ({x : Fin n → ℝ | Tuple.sort x = σ}
        ∩ (fun x : Fin n → ℝ => x ∘ ⇑σ) ⁻¹' T) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff]
    change orderStatistic x ∈ T ↔ ∃ σ, Tuple.sort x = σ ∧ (x ∘ ⇑σ) ∈ T
    constructor
    · intro hx
      exact ⟨Tuple.sort x, rfl, hx⟩
    · intro h
      obtain ⟨σ, hσ, hx⟩ := h
      subst hσ
      exact hx
  rw [hunion]
  apply MeasurableSet.iUnion
  intro σ
  exact (hE σ).inter (hpsi σ hT)

/-- No ties: an i.i.d. sample from a nonatomic law is a.s. injective. -/
theorem ae_injective_of_nonatomic {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ}
    (hIndep : iIndepFun X μ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hlaw : ∀ i, HasLaw (X i) ν μ)
    (hAtom : ∀ x, ν {x} = 0) :
    ∀ᵐ ω ∂μ, Function.Injective (fun i => X i ω) := by
  have hdiag_meas : MeasurableSet (Set.diagonal ℝ) :=
    isClosed_diagonal.measurableSet
  have hdiag_null : (ν.prod ν) (Set.diagonal ℝ) = 0 := by
    rw [Measure.prod_apply hdiag_meas]
    have hsec : ∀ x : ℝ, ν (Prod.mk x ⁻¹' Set.diagonal ℝ) = 0 := by
      intro x
      have hsub : Prod.mk x ⁻¹' Set.diagonal ℝ = {x} := by
        ext y
        simp [Set.diagonal, eq_comm]
      rw [hsub, hAtom x]
    simp [hsec]
  have hpair : ∀ i j : Fin n, i ≠ j → ∀ᵐ ω ∂μ, X i ω ≠ X j ω := by
    intro i j hij
    have hindep : (X i) ⟂ᵢ[μ] (X j) := hIndep.indepFun hij
    have hpair_law : HasLaw (fun ω => (X i ω, X j ω)) (ν.prod ν) μ :=
      IndepFun.hasLaw_prod (hlaw i) (hlaw j) hindep
    have hae : AEMeasurable (fun ω => (X i ω, X j ω)) μ := hpair_law.aemeasurable
    have hpre : μ ((fun ω => (X i ω, X j ω)) ⁻¹' Set.diagonal ℝ) = 0 := by
      have h := Measure.map_apply_of_aemeasurable hae hdiag_meas
      rw [hpair_law.map_eq, hdiag_null] at h
      exact h.symm
    have hmem : ∀ᵐ ω ∂μ, ω ∉ (fun ω => (X i ω, X j ω)) ⁻¹' Set.diagonal ℝ := by
      have h2 : {ω | ω ∉ (fun ω => (X i ω, X j ω)) ⁻¹' Set.diagonal ℝ} ∈ ae μ := by
        rw [mem_ae_iff]
        have hcomp : {ω | ω ∉ (fun ω => (X i ω, X j ω)) ⁻¹' Set.diagonal ℝ}ᶜ
            = (fun ω => (X i ω, X j ω)) ⁻¹' Set.diagonal ℝ := by
          ext ω
          simp
        rw [hcomp]
        exact hpre
      exact h2
    refine hmem.mono (fun ω hω hEq => hω ?_)
    simp [Set.diagonal, hEq]
  have hall : ∀ᵐ ω ∂μ, ∀ i j : Fin n, i ≠ j → X i ω ≠ X j ω := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    by_cases hij : i = j
    · subst hij
      exact Filter.Eventually.of_forall (fun ω h => absurd rfl h)
    · exact (hpair i j hij).mono (fun ω h _ => h)
  exact hall.mono (fun ω h => fun i j hij => by
    by_contra hne
    exact h i j hne hij)

/-- Rank uniformity: the rank vector has the uniform permutation law. -/
theorem sampleRank_uniform_of_nonatomic {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ}
    (hIndep : iIndepFun X μ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hlaw : ∀ i, HasLaw (X i) ν μ)
    (hAtom : ∀ x, ν {x} = 0) :
    HasLaw (fun ω => sampleRank (fun j => X j ω)) (rankLaw n) μ := by
  have hlawX : HasLaw (fun ω i => X i ω) (Measure.pi (fun _ : Fin n => ν)) μ :=
    hIndep.hasLaw_pi hlaw
  have haeX : AEMeasurable (fun ω i => X i ω) μ := hlawX.aemeasurable
  have hjointX : μ.map (fun ω i => X i ω) = Measure.pi (fun _ : Fin n => ν) := hlawX.map_eq
  have hlawY : ∀ τ : Equiv.Perm (Fin n),
      HasLaw (fun ω i => X (τ i) ω) (Measure.pi (fun _ : Fin n => ν)) μ := fun τ =>
    ((iIndepFun_precomp_of_bijective τ.bijective).mpr hIndep).hasLaw_pi fun i => hlaw (τ i)
  have hjointY : ∀ τ : Equiv.Perm (Fin n),
      μ.map (fun ω i => X (τ i) ω) = Measure.pi (fun _ : Fin n => ν) :=
    fun τ => (hlawY τ).map_eq
  have haeY : ∀ τ : Equiv.Perm (Fin n), AEMeasurable (fun ω i => X (τ i) ω) μ :=
    fun τ => (hlawY τ).aemeasurable
  have hae_rank : AEMeasurable (fun ω => sampleRank (fun j => X j ω)) μ :=
    measurable_sampleRank.comp_aemeasurable haeX
  have hS : ∀ s : Fin n → ℕ, MeasurableSet {x : Fin n → ℝ | sampleRank x = s} := by
    intro s
    have hset : {x : Fin n → ℝ | sampleRank x = s}
        = (fun x => sampleRank x) ⁻¹' {s} := rfl
    rw [hset]
    exact measurable_sampleRank (measurableSet_singleton s)
  have htrans : ∀ s : Fin n → ℕ,
      (Measure.pi (fun _ : Fin n => ν)) {x | sampleRank x = s}
        = μ {ω | sampleRank (fun j => X j ω) = s} := by
    intro s
    have hset : {ω | sampleRank (fun j => X j ω) = s}
        = (fun ω i => X i ω) ⁻¹' {x | sampleRank x = s} := rfl
    rw [hset, ← Measure.map_apply_of_aemeasurable haeX (hS s), hjointX]
  have hatom_eq : ∀ (r : Fin n → ℕ) (τ : Equiv.Perm (Fin n)),
      μ {ω | sampleRank (fun j => X j ω) = r}
        = μ {ω | sampleRank (fun j => X j ω) = r ∘ τ} := by
    intro r τ
    have heq1 : {ω | sampleRank (fun j => X (τ j) ω) = r ∘ τ}
        = {ω | sampleRank (fun j => X j ω) = r} := by
      ext ω
      change sampleRank (fun j => X (τ j) ω) = r ∘ τ ↔ sampleRank (fun j => X j ω) = r
      have hev := sampleRank_equivariant (fun j => X j ω) τ
      have hYeq : (fun j => X (τ j) ω) = (fun j => X j ω) ∘ τ := rfl
      rw [hYeq, hev]
      constructor
      · intro h2
        funext i
        have h2i := congrFun h2 (τ.symm i)
        simpa [Function.comp_apply] using h2i
      · intro h2
        rw [h2]
    have eY : μ {ω | sampleRank (fun j => X (τ j) ω) = r ∘ τ}
        = (Measure.pi (fun _ : Fin n => ν)) {x | sampleRank x = r ∘ τ} := by
      have hsetY : {ω | sampleRank (fun j => X (τ j) ω) = r ∘ τ}
          = (fun ω i => X (τ i) ω) ⁻¹' {x | sampleRank x = r ∘ τ} := rfl
      rw [hsetY, ← Measure.map_apply_of_aemeasurable (haeY τ) (hS (r ∘ τ)), hjointY τ]
    have eX : μ {ω | sampleRank (fun j => X j ω) = r ∘ τ}
        = (Measure.pi (fun _ : Fin n => ν)) {x | sampleRank x = r ∘ τ} :=
      (htrans (r ∘ τ)).symm
    rw [← heq1, eY, ← eX]
  have hequal : ∀ σ₁ σ₂ : Equiv.Perm (Fin n),
      μ {ω | sampleRank (fun j => X j ω) = permVec σ₁}
        = μ {ω | sampleRank (fun j => X j ω) = permVec σ₂} := by
    intro σ₁ σ₂
    have hcomp : permVec σ₁ ∘ (σ₂.trans σ₁.symm) = permVec σ₂ := by
      funext i
      change (σ₁ ((σ₂.trans σ₁.symm) i)).val + 1 = (σ₂ i).val + 1
      have hxy : σ₁ ((σ₂.trans σ₁.symm) i) = σ₂ i := by
        change σ₁ (σ₁.symm (σ₂ i)) = σ₂ i
        exact Equiv.apply_symm_apply σ₁ (σ₂ i)
      rw [hxy]
    have h := hatom_eq (permVec σ₁) (σ₂.trans σ₁.symm)
    rw [hcomp] at h
    exact h
  have hnull_of_mem : ∀ᵐ ω ∂μ, Function.Injective (fun i => X i ω) :=
    ae_injective_of_nonatomic hIndep ν hlaw hAtom
  have hnullset : μ {ω | ¬ Function.Injective (fun i => X i ω)} = 0 := by
    have hmem : {ω | Function.Injective (fun i => X i ω)} ∈ ae μ := hnull_of_mem
    rw [mem_ae_iff] at hmem
    have hcomp : {ω | ¬ Function.Injective (fun i => X i ω)}
        = {ω | Function.Injective (fun i => X i ω)}ᶜ := by
      ext ω
      simp
    rw [hcomp]
    exact hmem
  have hnonrange : ∀ r : Fin n → ℕ, r ∉ Set.range (@permVec n) →
      μ {ω | sampleRank (fun j => X j ω) = r} = 0 := by
    intro r hr
    apply measure_mono_null _ hnullset
    intro ω hω
    change ¬ Function.Injective (fun i => X i ω)
    intro hinj
    have hmem := sampleRank_mem_range_of_injective hinj
    have hω' : sampleRank (fun j => X j ω) = r := hω
    have hrw : r ∈ Set.range (@permVec n) := by
      rw [← hω']
      exact hmem
    exact hr hrw
  have hunion : (⋃ r : Fin n → ℕ, {x : Fin n → ℝ | sampleRank x = r}) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    simp only [Set.mem_iUnion]
    exact ⟨sampleRank x, rfl⟩
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun r : Fin n → ℕ => {x : Fin n → ℝ | sampleRank x = r})) := by
    intro r₁ r₂ hne
    change Disjoint _ _
    rw [Set.disjoint_left]
    intro x hx1 hx2
    have e1 : sampleRank x = r₁ := hx1
    have e2 : sampleRank x = r₂ := hx2
    exact hne (e1.symm.trans e2)
  have htsum : (Measure.pi (fun _ : Fin n => ν)) Set.univ
      = ∑' r : Fin n → ℕ, (Measure.pi (fun _ : Fin n => ν)) {x | sampleRank x = r} := by
    rw [← hunion, measure_iUnion hdisj (fun r => hS r)]
  have hone : (∑' r : Fin n → ℕ, (Measure.pi (fun _ : Fin n => ν)) {x | sampleRank x = r}) = 1 := by
    rw [← htsum]
    exact measure_univ
  set p : ℝ≥0∞ := μ {ω | sampleRank (fun j => X j ω) = permVec 1} with hp
  have hterm : ∀ r : Fin n → ℕ,
      (Measure.pi (fun _ : Fin n => ν)) {x | sampleRank x = r}
        = (if r ∈ Set.range (@permVec n) then p else 0) := by
    intro r
    rw [htrans r]
    by_cases hr : r ∈ Set.range (@permVec n)
    · rw [ite_eq_left hr]
      obtain ⟨σ₀, hσ₀⟩ := hr
      have hrr : r = permVec σ₀ := hσ₀.symm
      rw [hrr]
      exact hequal σ₀ 1
    · rw [ite_eq_right hr]
      exact hnonrange r hr
  have htsum_val : (∑' r : Fin n → ℕ, (Measure.pi (fun _ : Fin n => ν)) {x | sampleRank x = r})
      = (n.factorial : ℝ≥0∞) * p := by
    rw [tsum_congr hterm]
    have hsupp : ∀ r ∉ Finset.univ.image (@permVec n),
        ((if r ∈ Set.range (@permVec n) then p else 0) : ℝ≥0∞) = 0 := by
      intro r hr
      apply ite_eq_right
      intro hmem
      apply hr
      obtain ⟨σ₀, hσ₀⟩ := hmem
      exact Finset.mem_image.mpr ⟨σ₀, Finset.mem_univ σ₀, hσ₀⟩
    rw [tsum_eq_sum hsupp]
    have hif : ∀ r ∈ Finset.univ.image (@permVec n),
        ((if r ∈ Set.range (@permVec n) then p else 0) : ℝ≥0∞) = p := by
      intro r hr
      apply ite_eq_left
      obtain ⟨σ₀, _, hσ₀⟩ := Finset.mem_image.mp hr
      exact ⟨σ₀, hσ₀⟩
    rw [Finset.sum_congr rfl hif]
    rw [Finset.sum_const, card_image_permVec, nsmul_eq_mul]
  have hfact0 : (n.factorial : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hfacttop : (n.factorial : ℝ≥0∞) ≠ ⊤ := by simp
  have hbase : p = (n.factorial : ℝ≥0∞)⁻¹ := by
    have h1 : (n.factorial : ℝ≥0∞) * p = 1 := by
      rw [← htsum_val, hone]
    calc p = (n.factorial : ℝ≥0∞)⁻¹ * ((n.factorial : ℝ≥0∞) * p) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hfact0 hfacttop, one_mul]
      _ = (n.factorial : ℝ≥0∞)⁻¹ * 1 := by rw [h1]
      _ = (n.factorial : ℝ≥0∞)⁻¹ := mul_one _
  have hmap_eq : μ.map (fun ω => sampleRank (fun j => X j ω)) = rankLaw n := by
    rw [Measure.ext_iff_singleton]
    intro r
    have hmap_single : μ.map (fun ω => sampleRank (fun j => X j ω)) {r}
        = μ {ω | sampleRank (fun j => X j ω) = r} := by
      have hset : {ω | sampleRank (fun j => X j ω) = r}
          = (fun ω => sampleRank (fun j => X j ω)) ⁻¹' {r} := rfl
      rw [hset]
      exact Measure.map_apply_of_aemeasurable hae_rank (measurableSet_singleton r)
    rw [hmap_single]
    by_cases hr : r ∈ Set.range (@permVec n)
    · obtain ⟨σ₀, hσ₀⟩ := hr
      have hrr : r = permVec σ₀ := hσ₀.symm
      rw [hrr, rankLaw_singleton_permVec, hequal σ₀ 1, ← hp, hbase]
    · rw [rankLaw_singleton_of_notMem hr]
      exact hnonrange r hr
  exact HasLaw.mk hae_rank hmap_eq

/-- The rank vector is independent of the order statistics `orderStatistic`, the sorted sample. -/
theorem rank_indep_of_sorted {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ}
    (hIndep : iIndepFun X μ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hlaw : ∀ i, HasLaw (X i) ν μ)
    (hAtom : ∀ x, ν {x} = 0) :
    IndepFun (fun ω => sampleRank (fun j => X j ω))
      (fun ω => orderStatistic (fun j => X j ω)) μ := by
  have hlawX : HasLaw (fun ω i => X i ω) (Measure.pi (fun _ : Fin n => ν)) μ :=
    hIndep.hasLaw_pi hlaw
  have haeX : AEMeasurable (fun ω i => X i ω) μ := hlawX.aemeasurable
  have hjointX : μ.map (fun ω i => X i ω) = Measure.pi (fun _ : Fin n => ν) := hlawX.map_eq
  have hae_rank : AEMeasurable (fun ω => sampleRank (fun j => X j ω)) μ :=
    measurable_sampleRank.comp_aemeasurable haeX
  have hS : ∀ s : Fin n → ℕ, MeasurableSet {x : Fin n → ℝ | sampleRank x = s} := by
    intro s
    have hset : {x : Fin n → ℝ | sampleRank x = s}
        = (fun x => sampleRank x) ⁻¹' {s} := rfl
    rw [hset]
    exact measurable_sampleRank (measurableSet_singleton s)
  have htrans : ∀ s : Fin n → ℕ,
      (Measure.pi (fun _ : Fin n => ν)) {x | sampleRank x = s}
        = μ {ω | sampleRank (fun j => X j ω) = s} := by
    intro s
    have hset : {ω | sampleRank (fun j => X j ω) = s}
        = (fun ω i => X i ω) ⁻¹' {x | sampleRank x = s} := rfl
    rw [hset, ← Measure.map_apply_of_aemeasurable haeX (hS s), hjointX]
  have hUnif : HasLaw (fun ω => sampleRank (fun j => X j ω)) (rankLaw n) μ :=
    sampleRank_uniform_of_nonatomic hIndep ν hlaw hAtom
  have hR_atom : ∀ r : Fin n → ℕ,
      μ {ω | sampleRank (fun j => X j ω) = r} = rankLaw n {r} := by
    intro r
    have hset : {ω | sampleRank (fun j => X j ω) = r}
        = (fun ω => sampleRank (fun j => X j ω)) ⁻¹' {r} := rfl
    rw [hset, ← Measure.map_apply_of_aemeasurable hae_rank (measurableSet_singleton r),
      hUnif.map_eq]
  have hST : ∀ T : Set (Fin n → ℝ), MeasurableSet T →
      MeasurableSet {x : Fin n → ℝ | orderStatistic x ∈ T} := by
    intro T hT
    have hSt : {x : Fin n → ℝ | orderStatistic x ∈ T}
        = (fun x : Fin n → ℝ => orderStatistic x) ⁻¹' T := rfl
    rw [hSt]
    exact measurable_orderStatistic hT
  have hmeasA : ∀ (r : Fin n → ℕ) (T : Set (Fin n → ℝ)), MeasurableSet T →
      MeasurableSet {x : Fin n → ℝ | sampleRank x = r ∧ orderStatistic x ∈ T} := by
    intro r T hT
    have hsplit : {x : Fin n → ℝ | sampleRank x = r ∧ orderStatistic x ∈ T}
        = {x : Fin n → ℝ | sampleRank x = r} ∩ {x : Fin n → ℝ | orderStatistic x ∈ T} := rfl
    rw [hsplit]
    apply MeasurableSet.inter (hS r)
    exact hST T hT
  have hlawY : ∀ τ : Equiv.Perm (Fin n),
      HasLaw (fun ω i => X (τ i) ω) (Measure.pi (fun _ : Fin n => ν)) μ := fun τ =>
    ((iIndepFun_precomp_of_bijective τ.bijective).mpr hIndep).hasLaw_pi fun i => hlaw (τ i)
  have hjointY : ∀ τ : Equiv.Perm (Fin n),
      μ.map (fun ω i => X (τ i) ω) = Measure.pi (fun _ : Fin n => ν) :=
    fun τ => (hlawY τ).map_eq
  have haeY : ∀ τ : Equiv.Perm (Fin n), AEMeasurable (fun ω i => X (τ i) ω) μ :=
    fun τ => (hlawY τ).aemeasurable
  have hsymm : ∀ (T : Set (Fin n → ℝ)) (_ : MeasurableSet T) (r : Fin n → ℕ)
      (τ : Equiv.Perm (Fin n)),
      (Measure.pi (fun _ : Fin n => ν)) {x | sampleRank x = r ∧ orderStatistic x ∈ T}
        = (Measure.pi (fun _ : Fin n => ν)) {x | sampleRank x = r ∘ τ ∧ orderStatistic x ∈ T} := by
    intro T hT r τ
    have heq1 : {ω | sampleRank (fun j => X (τ j) ω) = r ∘ τ
          ∧ orderStatistic (fun j => X (τ j) ω) ∈ T}
        = {ω | sampleRank (fun j => X j ω) = r ∧ orderStatistic (fun j => X j ω) ∈ T} := by
      ext ω
      change (sampleRank (fun j => X (τ j) ω) = r ∘ τ ∧ orderStatistic (fun j => X (τ j) ω) ∈ T)
        ↔ (sampleRank (fun j => X j ω) = r ∧ orderStatistic (fun j => X j ω) ∈ T)
      have hev := sampleRank_equivariant (fun j => X j ω) τ
      have hinv : orderStatistic ((fun j => X j ω) ∘ ⇑τ) = orderStatistic (fun j => X j ω) :=
        Tuple.comp_perm_comp_sort_eq_comp_sort
      have hYeq : (fun j => X (τ j) ω) = (fun j => X j ω) ∘ ⇑τ := rfl
      rw [hYeq, hev, hinv]
      constructor
      · intro h
        refine ⟨?_, h.2⟩
        funext i
        have h2i := congrFun h.1 (τ.symm i)
        simpa [Function.comp_apply] using h2i
      · intro h
        refine ⟨?_, h.2⟩
        rw [h.1]
    have eY : μ {ω | sampleRank (fun j => X (τ j) ω) = r ∘ τ
          ∧ orderStatistic (fun j => X (τ j) ω) ∈ T}
        = (Measure.pi (fun _ : Fin n => ν)) {x | sampleRank x = r ∘ τ ∧ orderStatistic x ∈ T} := by
      have hsetY : {ω | sampleRank (fun j => X (τ j) ω) = r ∘ τ
            ∧ orderStatistic (fun j => X (τ j) ω) ∈ T}
          = (fun ω i => X (τ i) ω) ⁻¹' {x | sampleRank x = r ∘ τ ∧ orderStatistic x ∈ T} := rfl
      rw [hsetY, ← Measure.map_apply_of_aemeasurable (haeY τ) (hmeasA (r ∘ τ) T hT), hjointY τ]
    have eXr : μ {ω | sampleRank (fun j => X j ω) = r ∧ orderStatistic (fun j => X j ω) ∈ T}
        = (Measure.pi (fun _ : Fin n => ν)) {x | sampleRank x = r ∧ orderStatistic x ∈ T} := by
      have hsetXr : {ω | sampleRank (fun j => X j ω) = r ∧ orderStatistic (fun j => X j ω) ∈ T}
          = (fun ω i => X i ω) ⁻¹' {x | sampleRank x = r ∧ orderStatistic x ∈ T} := rfl
      rw [hsetXr, ← Measure.map_apply_of_aemeasurable haeX (hmeasA r T hT), hjointX]
    rw [← eXr, ← heq1, eY]
  have hequalT : ∀ (T : Set (Fin n → ℝ)) (_ : MeasurableSet T)
      (σ₁ σ₂ : Equiv.Perm (Fin n)),
      (Measure.pi (fun _ : Fin n => ν)) {x | sampleRank x = permVec σ₁ ∧ orderStatistic x ∈ T}
        = (Measure.pi (fun _ : Fin n => ν))
          {x | sampleRank x = permVec σ₂ ∧ orderStatistic x ∈ T} := by
    intro T hT σ₁ σ₂
    have hcomp : permVec σ₁ ∘ ⇑(σ₂.trans σ₁.symm) = permVec σ₂ := by
      funext i
      change (σ₁ ((σ₂.trans σ₁.symm) i)).val + 1 = (σ₂ i).val + 1
      have hxy : σ₁ ((σ₂.trans σ₁.symm) i) = σ₂ i := by
        change σ₁ (σ₁.symm (σ₂ i)) = σ₂ i
        exact Equiv.apply_symm_apply σ₁ (σ₂ i)
      rw [hxy]
    have h := hsymm T hT (permVec σ₁) (σ₂.trans σ₁.symm)
    rw [hcomp] at h
    exact h
  have hnull_of_mem : ∀ᵐ ω ∂μ, Function.Injective (fun i => X i ω) :=
    ae_injective_of_nonatomic hIndep ν hlaw hAtom
  have hnullset : μ {ω | ¬ Function.Injective (fun i => X i ω)} = 0 := by
    have hmem : {ω | Function.Injective (fun i => X i ω)} ∈ ae μ := hnull_of_mem
    rw [mem_ae_iff] at hmem
    have hcomp : {ω | ¬ Function.Injective (fun i => X i ω)}
        = {ω | Function.Injective (fun i => X i ω)}ᶜ := by
      ext ω
      simp
    rw [hcomp]
    exact hmem
  have hnonrange : ∀ r : Fin n → ℕ, r ∉ Set.range (@permVec n) →
      μ {ω | sampleRank (fun j => X j ω) = r} = 0 := by
    intro r hr
    apply measure_mono_null _ hnullset
    intro ω hω
    change ¬ Function.Injective (fun i => X i ω)
    intro hinj
    have hmem := sampleRank_mem_range_of_injective hinj
    have hω' : sampleRank (fun j => X j ω) = r := hω
    have hrw : r ∈ Set.range (@permVec n) := by
      rw [← hω']
      exact hmem
    exact hr hrw
  have hnullT : ∀ (T : Set (Fin n → ℝ)) (_ : MeasurableSet T) (r : Fin n → ℕ),
      r ∉ Set.range (@permVec n) →
      (Measure.pi (fun _ : Fin n => ν)) {x | sampleRank x = r ∧ orderStatistic x ∈ T} = 0 := by
    intro T hT r hr
    have hsub : {x : Fin n → ℝ | sampleRank x = r ∧ orderStatistic x ∈ T}
        ⊆ {x : Fin n → ℝ | sampleRank x = r} := by
      intro x hx
      have hx' : sampleRank x = r ∧ orderStatistic x ∈ T := hx
      exact hx'.1
    apply measure_mono_null hsub
    rw [htrans r]
    exact hnonrange r hr
  have hunionT : ∀ T : Set (Fin n → ℝ),
      (⋃ r : Fin n → ℕ, {x : Fin n → ℝ | sampleRank x = r ∧ orderStatistic x ∈ T})
        = {x : Fin n → ℝ | orderStatistic x ∈ T} := by
    intro T
    ext x
    simp only [Set.mem_iUnion]
    change (∃ r, sampleRank x = r ∧ orderStatistic x ∈ T) ↔ orderStatistic x ∈ T
    constructor
    · intro h
      obtain ⟨r, hr, hT⟩ := h
      exact hT
    · intro h
      exact ⟨sampleRank x, rfl, h⟩
  have hdisjT : ∀ T : Set (Fin n → ℝ), Pairwise (Function.onFun Disjoint
      (fun r : Fin n → ℕ => {x : Fin n → ℝ | sampleRank x = r ∧ orderStatistic x ∈ T})) := by
    intro T r₁ r₂ hne
    change Disjoint _ _
    rw [Set.disjoint_left]
    intro x hx1 hx2
    have e1 : sampleRank x = r₁ ∧ orderStatistic x ∈ T := hx1
    have e2 : sampleRank x = r₂ ∧ orderStatistic x ∈ T := hx2
    exact hne (e1.1.symm.trans e2.1)
  have htsumT : ∀ (T : Set (Fin n → ℝ)) (_ : MeasurableSet T),
      (∑' r : Fin n → ℕ, (Measure.pi (fun _ : Fin n => ν))
        {x | sampleRank x = r ∧ orderStatistic x ∈ T})
        = (Measure.pi (fun _ : Fin n => ν)) {x | orderStatistic x ∈ T} := by
    intro T hT
    rw [← hunionT T, measure_iUnion (hdisjT T) (fun r => hmeasA r T hT)]
  have htsumT_val : ∀ (T : Set (Fin n → ℝ)) (_ : MeasurableSet T),
      (∑' r : Fin n → ℕ, (Measure.pi (fun _ : Fin n => ν))
        {x | sampleRank x = r ∧ orderStatistic x ∈ T})
        = (n.factorial : ℝ≥0∞)
          * (Measure.pi (fun _ : Fin n => ν))
            {x | sampleRank x = permVec 1 ∧ orderStatistic x ∈ T} := by
    intro T hT
    set q : ℝ≥0∞ := (Measure.pi (fun _ : Fin n => ν))
      {x | sampleRank x = permVec 1 ∧ orderStatistic x ∈ T}
    have hterm : ∀ r : Fin n → ℕ,
        (Measure.pi (fun _ : Fin n => ν)) {x | sampleRank x = r ∧ orderStatistic x ∈ T}
          = (if r ∈ Set.range (@permVec n) then q else 0) := by
      intro r
      by_cases hr : r ∈ Set.range (@permVec n)
      · rw [ite_eq_left hr]
        obtain ⟨σ₀, hσ₀⟩ := hr
        have hrr : r = permVec σ₀ := hσ₀.symm
        rw [hrr]
        exact hequalT T hT σ₀ 1
      · rw [ite_eq_right hr]
        exact hnullT T hT r hr
    rw [tsum_congr hterm]
    have hsupp : ∀ r ∉ Finset.univ.image (@permVec n),
        ((if r ∈ Set.range (@permVec n) then q else 0) : ℝ≥0∞) = 0 := by
      intro r hr
      apply ite_eq_right
      intro hmem
      apply hr
      obtain ⟨σ₀, hσ₀⟩ := hmem
      exact Finset.mem_image.mpr ⟨σ₀, Finset.mem_univ σ₀, hσ₀⟩
    rw [tsum_eq_sum hsupp]
    have hif : ∀ r ∈ Finset.univ.image (@permVec n),
        ((if r ∈ Set.range (@permVec n) then q else 0) : ℝ≥0∞) = q := by
      intro r hr
      apply ite_eq_left
      obtain ⟨σ₀, _, hσ₀⟩ := Finset.mem_image.mp hr
      exact ⟨σ₀, hσ₀⟩
    rw [Finset.sum_congr rfl hif]
    rw [Finset.sum_const, card_image_permVec, nsmul_eq_mul]
  have hq_val : ∀ (T : Set (Fin n → ℝ)) (hT : MeasurableSet T),
      (Measure.pi (fun _ : Fin n => ν)) {x | sampleRank x = permVec 1 ∧ orderStatistic x ∈ T}
        = (n.factorial : ℝ≥0∞)⁻¹
          * (Measure.pi (fun _ : Fin n => ν)) {x | orderStatistic x ∈ T} := by
    intro T hT
    have hfact0 : (n.factorial : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    have hfacttop : (n.factorial : ℝ≥0∞) ≠ ⊤ := by simp
    have h1 : (n.factorial : ℝ≥0∞)
        * (Measure.pi (fun _ : Fin n => ν)) {x | sampleRank x = permVec 1 ∧ orderStatistic x ∈ T}
        = (Measure.pi (fun _ : Fin n => ν)) {x | orderStatistic x ∈ T} := by
      rw [← htsumT_val T hT, htsumT T hT]
    calc (Measure.pi (fun _ : Fin n => ν)) {x | sampleRank x = permVec 1 ∧ orderStatistic x ∈ T}
        = (n.factorial : ℝ≥0∞)⁻¹ * ((n.factorial : ℝ≥0∞)
          * (Measure.pi (fun _ : Fin n => ν))
            {x | sampleRank x = permVec 1 ∧ orderStatistic x ∈ T}) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hfact0 hfacttop, one_mul]
      _ = (n.factorial : ℝ≥0∞)⁻¹
          * (Measure.pi (fun _ : Fin n => ν)) {x | orderStatistic x ∈ T} := by rw [h1]
  have hsingle : ∀ (T : Set (Fin n → ℝ)) (hT : MeasurableSet T) (r : Fin n → ℕ),
      (Measure.pi (fun _ : Fin n => ν)) {x | sampleRank x = r ∧ orderStatistic x ∈ T}
        = (Measure.pi (fun _ : Fin n => ν)) {x | sampleRank x = r}
          * (Measure.pi (fun _ : Fin n => ν)) {x | orderStatistic x ∈ T} := by
    intro T hT r
    by_cases hr : r ∈ Set.range (@permVec n)
    · obtain ⟨σ₀, hσ₀⟩ := hr
      have hrr : r = permVec σ₀ := hσ₀.symm
      have hLHS : (Measure.pi (fun _ : Fin n => ν)) {x | sampleRank x = r ∧ orderStatistic x ∈ T}
          = (n.factorial : ℝ≥0∞)⁻¹
            * (Measure.pi (fun _ : Fin n => ν)) {x | orderStatistic x ∈ T} := by
        rw [hrr]
        rw [hequalT T hT σ₀ 1]
        exact hq_val T hT
      have hRHS : (Measure.pi (fun _ : Fin n => ν)) {x | sampleRank x = r}
          = (n.factorial : ℝ≥0∞)⁻¹ := by
        rw [htrans r, hR_atom r, hrr, rankLaw_singleton_permVec]
      rw [hLHS, hRHS]
    · have hLHS : (Measure.pi (fun _ : Fin n => ν))
          {x | sampleRank x = r ∧ orderStatistic x ∈ T} = 0 :=
        hnullT T hT r hr
      have hRHS : (Measure.pi (fun _ : Fin n => ν)) {x | sampleRank x = r} = 0 := by
        rw [htrans r, hR_atom r, rankLaw_singleton_of_notMem hr]
      rw [hLHS, hRHS, zero_mul]
  have hmain : ∀ (s : Set (Fin n → ℕ)) (_ : MeasurableSet s) (T : Set (Fin n → ℝ))
      (_ : MeasurableSet T),
      (Measure.pi (fun _ : Fin n => ν))
          {x | sampleRank x ∈ s ∧ orderStatistic x ∈ T}
        = (Measure.pi (fun _ : Fin n => ν)) {x | sampleRank x ∈ s}
          * (Measure.pi (fun _ : Fin n => ν)) {x | orderStatistic x ∈ T} := by
    intro s hs T hT
    classical
    have hPeq : {x : Fin n → ℝ | sampleRank x ∈ s ∧ orderStatistic x ∈ T}
        = ⋃ r : Fin n → ℕ, ({x : Fin n → ℝ | sampleRank x = r ∧ orderStatistic x ∈ T}
          ∩ {x : Fin n → ℝ | sampleRank x ∈ s}) := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_inter_iff]
      change (sampleRank x ∈ s ∧ orderStatistic x ∈ T)
        ↔ ∃ r, (sampleRank x = r ∧ orderStatistic x ∈ T) ∧ sampleRank x ∈ s
      constructor
      · intro h
        exact ⟨sampleRank x, ⟨rfl, h.2⟩, h.1⟩
      · intro h
        obtain ⟨r, hr, hmem⟩ := h
        exact ⟨hmem, hr.2⟩
    have hPmeas : ∀ r : Fin n → ℕ, MeasurableSet
        ({x : Fin n → ℝ | sampleRank x = r ∧ orderStatistic x ∈ T}
          ∩ {x : Fin n → ℝ | sampleRank x ∈ s}) := by
      intro r
      apply MeasurableSet.inter (hmeasA r T hT)
      have hRs : {x : Fin n → ℝ | sampleRank x ∈ s} = (fun x => sampleRank x) ⁻¹' s := rfl
      rw [hRs]
      exact measurable_sampleRank hs
    have hPdisj : Pairwise (Function.onFun Disjoint
        (fun r : Fin n → ℕ => ({x : Fin n → ℝ | sampleRank x = r ∧ orderStatistic x ∈ T}
          ∩ {x : Fin n → ℝ | sampleRank x ∈ s}))) := by
      intro r₁ r₂ hne
      change Disjoint _ _
      rw [Set.disjoint_left]
      intro x hx1 hx2
      have e1 : (sampleRank x = r₁ ∧ orderStatistic x ∈ T) ∧ sampleRank x ∈ s := hx1
      have e2 : (sampleRank x = r₂ ∧ orderStatistic x ∈ T) ∧ sampleRank x ∈ s := hx2
      exact hne (e1.1.1.symm.trans e2.1.1)
    have hPval : ∀ r : Fin n → ℕ,
        (Measure.pi (fun _ : Fin n => ν))
          ({x | sampleRank x = r ∧ orderStatistic x ∈ T} ∩ {x | sampleRank x ∈ s})
          = (if r ∈ s then (Measure.pi (fun _ : Fin n => ν)) {x | sampleRank x = r}
            else 0)
            * (Measure.pi (fun _ : Fin n => ν)) {x | orderStatistic x ∈ T} := by
      intro r
      by_cases hr : r ∈ s
      · have hset : ({x : Fin n → ℝ | sampleRank x = r ∧ orderStatistic x ∈ T}
            ∩ {x : Fin n → ℝ | sampleRank x ∈ s})
            = {x : Fin n → ℝ | sampleRank x = r ∧ orderStatistic x ∈ T} := by
          ext x
          change ((sampleRank x = r ∧ orderStatistic x ∈ T) ∧ sampleRank x ∈ s)
            ↔ (sampleRank x = r ∧ orderStatistic x ∈ T)
          constructor
          · intro h
            exact h.1
          · intro h
            refine ⟨h, ?_⟩
            rw [h.1]
            exact hr
        rw [hset, hsingle T hT r, ite_eq_left hr]
      · have hset : ({x : Fin n → ℝ | sampleRank x = r ∧ orderStatistic x ∈ T}
            ∩ {x : Fin n → ℝ | sampleRank x ∈ s})
            = (∅ : Set (Fin n → ℝ)) := by
          ext x
          change ((sampleRank x = r ∧ orderStatistic x ∈ T) ∧ sampleRank x ∈ s)
            ↔ x ∈ (∅ : Set (Fin n → ℝ))
          constructor
          · intro h
            have h2 := h.2
            rw [h.1.1] at h2
            exact absurd h2 hr
          · intro h
            exact absurd h (Set.notMem_empty x)
        rw [hset, ite_eq_right hr, measure_empty, zero_mul]
    have hLHS : (Measure.pi (fun _ : Fin n => ν)) {x | sampleRank x ∈ s ∧ orderStatistic x ∈ T}
        = ∑' r : Fin n → ℕ, ((if r ∈ s then (Measure.pi (fun _ : Fin n => ν)) {x | sampleRank x = r}
          else 0) * (Measure.pi (fun _ : Fin n => ν)) {x | orderStatistic x ∈ T}) := by
      rw [hPeq, measure_iUnion hPdisj hPmeas]
      exact tsum_congr hPval
    have hQeq : {x : Fin n → ℝ | sampleRank x ∈ s}
        = ⋃ r : Fin n → ℕ, ({x : Fin n → ℝ | sampleRank x = r}
          ∩ {x : Fin n → ℝ | sampleRank x ∈ s}) := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_inter_iff]
      change sampleRank x ∈ s ↔ ∃ r, sampleRank x = r ∧ sampleRank x ∈ s
      constructor
      · intro h
        exact ⟨sampleRank x, rfl, h⟩
      · intro h
        obtain ⟨r, hr, hmem⟩ := h
        exact hmem
    have hQmeas : ∀ r : Fin n → ℕ, MeasurableSet
        ({x : Fin n → ℝ | sampleRank x = r} ∩ {x : Fin n → ℝ | sampleRank x ∈ s}) := by
      intro r
      apply MeasurableSet.inter (hS r)
      have hRs : {x : Fin n → ℝ | sampleRank x ∈ s} = (fun x => sampleRank x) ⁻¹' s := rfl
      rw [hRs]
      exact measurable_sampleRank hs
    have hQdisj : Pairwise (Function.onFun Disjoint
        (fun r : Fin n → ℕ => ({x : Fin n → ℝ | sampleRank x = r}
          ∩ {x : Fin n → ℝ | sampleRank x ∈ s}))) := by
      intro r₁ r₂ hne
      change Disjoint _ _
      rw [Set.disjoint_left]
      intro x hx1 hx2
      have e1 : (sampleRank x = r₁) ∧ sampleRank x ∈ s := hx1
      have e2 : (sampleRank x = r₂) ∧ sampleRank x ∈ s := hx2
      exact hne (e1.1.symm.trans e2.1)
    have hQval : ∀ r : Fin n → ℕ,
        (Measure.pi (fun _ : Fin n => ν))
          ({x | sampleRank x = r} ∩ {x | sampleRank x ∈ s})
          = (if r ∈ s then (Measure.pi (fun _ : Fin n => ν)) {x | sampleRank x = r} else 0) := by
      intro r
      by_cases hr : r ∈ s
      · have hset : ({x : Fin n → ℝ | sampleRank x = r} ∩ {x : Fin n → ℝ | sampleRank x ∈ s})
            = {x : Fin n → ℝ | sampleRank x = r} := by
          ext x
          change ((sampleRank x = r) ∧ sampleRank x ∈ s) ↔ sampleRank x = r
          constructor
          · intro h
            exact h.1
          · intro h
            refine ⟨h, ?_⟩
            rw [h]
            exact hr
        rw [hset, ite_eq_left hr]
      · have hset : ({x : Fin n → ℝ | sampleRank x = r} ∩ {x : Fin n → ℝ | sampleRank x ∈ s})
            = (∅ : Set (Fin n → ℝ)) := by
          ext x
          change ((sampleRank x = r) ∧ sampleRank x ∈ s) ↔ x ∈ (∅ : Set (Fin n → ℝ))
          constructor
          · intro h
            have h2 := h.2
            rw [h.1] at h2
            exact absurd h2 hr
          · intro h
            exact absurd h (Set.notMem_empty x)
        rw [hset, ite_eq_right hr, measure_empty]
    have hRHS : (Measure.pi (fun _ : Fin n => ν)) {x | sampleRank x ∈ s}
        = ∑' r : Fin n → ℕ, (if r ∈ s then (Measure.pi (fun _ : Fin n => ν)) {x | sampleRank x = r}
          else 0) := by
      rw [hQeq, measure_iUnion hQdisj hQmeas]
      exact tsum_congr hQval
    rw [hLHS, hRHS, ENNReal.tsum_mul_right]
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro s t hs ht
  have hinter : (fun ω => sampleRank (fun j => X j ω)) ⁻¹' s
        ∩ (fun ω => orderStatistic (fun j => X j ω)) ⁻¹' t
      = (fun ω i => X i ω) ⁻¹'
        ({x : Fin n → ℝ | sampleRank x ∈ s} ∩ {x : Fin n → ℝ | orderStatistic x ∈ t}) := by
    ext ω
    change (sampleRank (fun j => X j ω) ∈ s ∧ orderStatistic (fun j => X j ω) ∈ t)
      ↔ (sampleRank (fun i => X i ω) ∈ s ∧ orderStatistic (fun i => X i ω) ∈ t)
    constructor
    · intro h
      exact h
    · intro h
      exact h
  have hRω : (fun ω => sampleRank (fun j => X j ω)) ⁻¹' s
      = (fun ω i => X i ω) ⁻¹' {x : Fin n → ℝ | sampleRank x ∈ s} := rfl
  have hSω : (fun ω => orderStatistic (fun j => X j ω)) ⁻¹' t
      = (fun ω i => X i ω) ⁻¹' {x : Fin n → ℝ | orderStatistic x ∈ t} := rfl
  have hAmeas : MeasurableSet ({x : Fin n → ℝ | sampleRank x ∈ s}
      ∩ {x : Fin n → ℝ | orderStatistic x ∈ t}) := by
    apply MeasurableSet.inter
    · have hRs : {x : Fin n → ℝ | sampleRank x ∈ s} = (fun x => sampleRank x) ⁻¹' s := rfl
      rw [hRs]
      exact measurable_sampleRank hs
    · exact hST t ht
  have hRmeas : MeasurableSet {x : Fin n → ℝ | sampleRank x ∈ s} := by
    have hRs : {x : Fin n → ℝ | sampleRank x ∈ s} = (fun x => sampleRank x) ⁻¹' s := rfl
    rw [hRs]
    exact measurable_sampleRank hs
  have hSmeas : MeasurableSet {x : Fin n → ℝ | orderStatistic x ∈ t} := hST t ht
  have eInter : μ ((fun ω => sampleRank (fun j => X j ω)) ⁻¹' s
        ∩ (fun ω => orderStatistic (fun j => X j ω)) ⁻¹' t)
      = (Measure.pi (fun _ : Fin n => ν))
        ({x : Fin n → ℝ | sampleRank x ∈ s} ∩ {x : Fin n → ℝ | orderStatistic x ∈ t}) := by
    rw [hinter, ← Measure.map_apply_of_aemeasurable haeX hAmeas, hjointX]
  have eR : μ ((fun ω => sampleRank (fun j => X j ω)) ⁻¹' s)
      = (Measure.pi (fun _ : Fin n => ν)) {x : Fin n → ℝ | sampleRank x ∈ s} := by
    rw [hRω, ← Measure.map_apply_of_aemeasurable haeX hRmeas, hjointX]
  have eS : μ ((fun ω => orderStatistic (fun j => X j ω)) ⁻¹' t)
      = (Measure.pi (fun _ : Fin n => ν)) {x : Fin n → ℝ | orderStatistic x ∈ t} := by
    rw [hSω, ← Measure.map_apply_of_aemeasurable haeX hSmeas, hjointX]
  have hpi := hmain s hs t ht
  have hsplit : {x : Fin n → ℝ | sampleRank x ∈ s ∧ orderStatistic x ∈ t}
      = ({x : Fin n → ℝ | sampleRank x ∈ s} ∩ {x : Fin n → ℝ | orderStatistic x ∈ t}) := rfl
  rw [hsplit] at hpi
  rw [eInter, eR, eS]
  exact hpi

end ProbabilityTheory
