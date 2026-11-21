/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BranchingProcess.GaltonWatson
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Distributions.Uniform

/-!
# Early epidemic and its branching-process approximation

A generation-based SIR epidemic in a population `α` (finite, `N` individuals) is started by one
*index case*: an infective who is not an individual of `α` (an external ancestor, such as an
imported case). The individuals of `S₀ ⊆ α` are initially susceptible; the others are immune and
are never infected. The `i`-th infective of generation `n` (generation `0` is the index case)
makes `ξ n i` contacts; the contacts of the epidemic are numbered `0, 1, 2, …` in the order they
are made (generation by generation, and within a generation infective by infective), and contact
number `j` goes to the individual `U j`. A contact infects its target iff the target is initially
susceptible (`U j ∈ S₀`) and has not been contacted before (`epiHit`); the infected targets form
the next generation.

An index case who is an individual `i₀` of the population is the special case `i₀ ∉ S₀`:
contacts to `i₀` never infect, and the infectives of all generations, index case included, never
outnumber the population (`sum_epiSize_le_card`). The statements below hold for every `S₀`, so
they apply to both readings; in the large-population results such an `i₀` is one of the `o(N)`
individuals outside `S₀`.

The branching process on the same randomness ignores depletion: every contact produces a new
individual, so generation sizes are `Z 0 = 1`, `Z (n + 1) = ∑_{i < Z n} ξ n i` (`bpSize`). With
the `ξ n i` i.i.d. with law `ν` this is the Bienaymé–Galton–Watson process with offspring law `ν`
(`hasLaw_bpSize`), and the epidemic sizes `I n` (`epiSize`) are a deterministic thinning of it
(the Ball–Donnelly coupling).

## Main results

Deterministic coupling (any offspring numbers and contact targets):
* `epiSize_le_bpSize`: the epidemic is dominated by the branching process, `I n ≤ Z n`.
* `epi_eq_of_forall_hit`: the two agree, `I n = Z n`, as long as every one of the first
  `bpContacts n` contacts hits a fresh susceptible (no susceptible has yet been depleted).
* `epiSize_card_add_one_eq_zero`: in a finite population the epidemic is extinct by
  generation `#S₀ + 1`; minor versus major outbreak is therefore a large-population notion
  (see "Minor and major outbreaks" below).
* `sum_epiSize_le_card`: if the index case is an individual `i₀ ∉ S₀` of a finite population, the
  infectives of generations `0, …, n` number at most `Fintype.card α`.

Probabilistic statements (`IsEarlyEpidemic`: `ξ n i` i.i.d. `∼ ν`, targets i.i.d. uniform on
`Fin N`; no assumption on the joint law of `ξ` and `U`):
* `hasLaw_bpSize`, `measureReal_exists_bpSize_eq_zero`: `Z n` has the Galton–Watson law
  `law ν n`, and the branching process dies out with probability `extinctionProb ν`.
* `measure_exists_not_epiHit_le`: the birthday bound
  `P(some of the first M contacts is wasted) ≤ (M (N - #S₀) + C(M, 2)) / N`.
* `measureReal_epiSize_eq_zero_le`: the approximation bound
  `P(Z n = 0) ≤ P(I n = 0) ≤ P(Z n = 0) + ∑_{m<n} P(Z_{m+1} > L) + (nL (N - #S₀) + C(nL, 2))/N`.
* `tendsto_measureReal_epiSize_eq_zero`: as the population size `N → ∞` with `N - #S₀ = o(N)`,
  the probability that the epidemic is extinct by generation `n` converges to
  `P(Z n = 0) = f^[n](0)`.
* `isEarlyEpidemic_canonical`: the hypotheses are satisfiable (product-space model).

Threshold (`R₀ = mean ν`, `q = extinctionProb ν`):
* `exists_forall_measureReal_epiSize_eq_zero_gt`: if `R₀ ≤ 1` (and `ν {1} ≠ 1`), for every
  `ε > 0` there is a number of generations `n₀`, independent of the population size and of the
  law of the contact targets, by which the epidemic is extinct with probability `> 1 - ε`: only
  minor outbreaks occur. (Almost sure eventual extinction alone says nothing about `R₀`: in a
  finite population it always holds, `measureReal_exists_epiSize_eq_zero`.)
* `tendsto_measureReal_epiSize_ne_zero`, `one_sub_extinctionProb_le`,
  `one_sub_extinctionProb_pos`: if `R₀ > 1`, the large-population probability that the epidemic
  survives `n` generations is `1 - P(Z n = 0) ≥ 1 - q > 0`; it is non-increasing in `n`
  (`antitone_one_sub_law_real_zero`) and tends to the branching-process survival probability
  `1 - q` (`tendsto_one_sub_law_real_zero`): a major outbreak has probability `1 - q > 0`.

## Minor and major outbreaks

Since a finite population always becomes extinct, the outbreak notions are defined through the
large-population limit. The epidemic has a *major outbreak* if it survives `n` generations in the
limit `N → ∞`, for every `n`; its probability is the iterated limit
`lim_n lim_N P(I n ≠ 0) = lim_n (1 - P(Z n = 0)) = 1 - q`. A *minor outbreak* is the complement,
with probability `lim_n lim_N P(I n = 0) = q`. No statement about the final size of the epidemic
is proved.

## Measurability

Measurability of the epidemic events `{ω | epiSize … n = 0}` is not proved, and the targets `U j`
are not assumed measurable; `P.real` of such an event is therefore its outer measure. Every bound
on these events uses only monotonicity and subadditivity of outer measure (`measureReal_mono`,
`measureReal_union_le`, `measureReal_biUnion_finset_le`), so all statements hold as written. The
lower bounds also hold for the inner measure, because `{I n = 0} ⊇ {Z n = 0}` and the
branching-process events are measurable (`measurable_bpSize`).

## References

* F. Ball, P. Donnelly, *Strong approximations for epidemic models*, Stochastic Process. Appl.
  55 (1995), 1–21.
* F. Ball, *The threshold behaviour of epidemic models*, J. Appl. Probab. 20 (1983), 227–241.
* K. B. Athreya, P. E. Ney, *Branching Processes*, Springer (1972), ch. I.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

namespace MathlibExt.Biology.Epidemiology.EarlyEpidemicBranching

open MathlibExt.Probability MathlibExt.Probability.GaltonWatson

/-! ### The coupled processes -/

section Deterministic

variable (ξ : ℕ → ℕ → ℕ)

/-- Generation sizes of the branching process: `Z 0 = 1` and `Z (n + 1) = ∑_{i < Z n} ξ n i`,
where `ξ n i` is the number of offspring (contacts) of the `i`-th individual of generation
`n`. -/
def bpSize : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ i ∈ range (bpSize n), ξ n i

/-- The number of contacts made by generations `0, …, n - 1` of the branching process,
`∑_{m < n} Z (m + 1)`. -/
def bpContacts (n : ℕ) : ℕ :=
  ∑ m ∈ range n, bpSize ξ (m + 1)

variable {α : Type*} [DecidableEq α] (U : ℕ → α) (S₀ : Finset α)

/-- Contact number `j` (to the individual `U j`) infects its target: the target is initially
susceptible and no earlier contact went to it. -/
def epiHit (j : ℕ) : Prop :=
  U j ∈ S₀ ∧ ∀ j' < j, U j' ≠ U j

instance (j : ℕ) : Decidable (epiHit U S₀ j) := by
  unfold epiHit; infer_instance

/-- The state of the epidemic at generation `n`: the number of infectives of generation `n`
and the number of contacts made by the earlier generations. Generation `0` is the index case
alone, with no earlier contacts. Generation `n` makes the contacts numbered `D, …, D + c - 1`
with `c = ∑_{i < I} ξ n i`, and the next generation consists of the targets of those contacts
that hit (`epiHit`). -/
def epi : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | n + 1 =>
    ((Ico (epi n).2 ((epi n).2 + ∑ i ∈ range (epi n).1, ξ n i)).filter (epiHit U S₀) |>.card,
      (epi n).2 + ∑ i ∈ range (epi n).1, ξ n i)

/-- The number `I n` of infectives in generation `n` of the epidemic; `I 0 = 1` is the index
case. -/
def epiSize (n : ℕ) : ℕ :=
  (epi ξ U S₀ n).1

theorem bpContacts_succ (n : ℕ) : bpContacts ξ (n + 1) = bpContacts ξ n + bpSize ξ (n + 1) :=
  sum_range_succ _ _

theorem bpSize_succ (n : ℕ) : bpSize ξ (n + 1) = ∑ i ∈ range (bpSize ξ n), ξ n i :=
  rfl

/-- `0` is absorbing for the branching process. -/
theorem bpSize_succ_eq_zero {n : ℕ} (h : bpSize ξ n = 0) : bpSize ξ (n + 1) = 0 := by
  simp [bpSize_succ, h]

theorem epiSize_succ (n : ℕ) : epiSize ξ U S₀ (n + 1) =
    ((Ico (epi ξ U S₀ n).2 ((epi ξ U S₀ n).2 + ∑ i ∈ range (epiSize ξ U S₀ n), ξ n i)).filter
      (epiHit U S₀)).card :=
  rfl

/-- `0` is absorbing for the epidemic. -/
theorem epiSize_succ_eq_zero {n : ℕ} (h : epiSize ξ U S₀ n = 0) :
    epiSize ξ U S₀ (n + 1) = 0 := by
  simp [epiSize_succ, h]

theorem epiSize_eq_zero_of_le {n m : ℕ} (hnm : n ≤ m) (h : epiSize ξ U S₀ n = 0) :
    epiSize ξ U S₀ m = 0 := by
  induction m, hnm using Nat.le_induction with
  | base => exact h
  | succ m _ ih => exact epiSize_succ_eq_zero ξ U S₀ ih

/-- **Domination.** The epidemic never exceeds the branching process: `I n ≤ Z n`. -/
theorem epiSize_le_bpSize (n : ℕ) : epiSize ξ U S₀ n ≤ bpSize ξ n := by
  induction n with
  | zero => simp [epiSize, epi, bpSize]
  | succ n ih =>
    rw [epiSize_succ, bpSize_succ]
    refine (card_filter_le _ _).trans ?_
    rw [Nat.card_Ico, Nat.add_sub_cancel_left]
    exact sum_le_sum_of_subset (range_subset_range.2 ih)

/-- **The coupling.** If each of the first `M` contacts hits a fresh initially susceptible
individual and the branching process makes at most `M` contacts in its first `n` generations,
then the epidemic and the branching process agree up to generation `n`: same generation sizes
and same contact counts. -/
theorem epi_eq_of_forall_hit {M n : ℕ} (hhit : ∀ j < M, epiHit U S₀ j)
    (hn : bpContacts ξ n ≤ M) : epi ξ U S₀ n = (bpSize ξ n, bpContacts ξ n) := by
  induction n with
  | zero => simp [epi, bpSize, bpContacts]
  | succ n ih =>
    rw [bpContacts_succ] at hn
    have h := ih (le_trans (Nat.le_add_right _ _) hn)
    simp only [epi, h]
    rw [bpContacts_succ, ← bpSize_succ]
    refine Prod.ext ?_ rfl
    dsimp only
    rw [filter_true_of_mem, Nat.card_Ico, Nat.add_sub_cancel_left]
    intro j hj
    exact hhit j (lt_of_lt_of_le (mem_Ico.1 hj).2 hn)

/-- Under the hypotheses of `epi_eq_of_forall_hit`, `I n = Z n`. -/
theorem epiSize_eq_bpSize_of_forall_hit {M n : ℕ} (hhit : ∀ j < M, epiHit U S₀ j)
    (hn : bpContacts ξ n ≤ M) : epiSize ξ U S₀ n = bpSize ξ n := by
  rw [epiSize, epi_eq_of_forall_hit ξ U S₀ hhit hn]

/-- The total number of infections in generations `1, …, n` is the number of hits among the
contacts made before generation `n`. -/
theorem sum_epiSize_eq_card (n : ℕ) :
    ∑ m ∈ range n, epiSize ξ U S₀ (m + 1) =
      ((range (epi ξ U S₀ n).2).filter (epiHit U S₀)).card := by
  induction n with
  | zero => simp [epi]
  | succ n ih =>
    rw [sum_range_succ, ih, epiSize_succ, ← card_union_of_disjoint]
    · congr 1
      rw [← filter_union, range_eq_Ico, Ico_union_Ico_eq_Ico (Nat.zero_le _)
        (Nat.le_add_right _ _), ← range_eq_Ico]
      rfl
    · exact disjoint_filter_filter (by
        rw [range_eq_Ico]; exact Ico_disjoint_Ico_consecutive _ _ _)

/-- Hits go to distinct initially susceptible individuals, so there are at most `#S₀` of
them. -/
theorem card_filter_epiHit_le (D : ℕ) : ((range D).filter (epiHit U S₀)).card ≤ S₀.card := by
  refine card_le_card_of_injOn U (fun j hj => (mem_filter.1 hj).2.1) ?_
  intro j hj j' hj' hU
  rcases lt_trichotomy j j' with h | h | h
  · exact absurd hU ((mem_filter.1 hj').2.2 j h)
  · exact h
  · exact absurd hU.symm ((mem_filter.1 hj).2.2 j' h)

/-- In a finite population the epidemic is extinct by generation `#S₀ + 1`: every infective
of generations `1, …, n` is a distinct initially susceptible individual. -/
theorem epiSize_card_add_one_eq_zero : epiSize ξ U S₀ (S₀.card + 1) = 0 := by
  by_contra h
  have hpos : ∀ m ≤ S₀.card, 0 < epiSize ξ U S₀ (m + 1) := fun m hm =>
    Nat.pos_of_ne_zero fun h0 => h (epiSize_eq_zero_of_le ξ U S₀ (by omega) h0)
  have hle := (sum_epiSize_eq_card ξ U S₀ (S₀.card + 1)).trans_le
    (card_filter_epiHit_le U S₀ _)
  have hge : S₀.card + 1 ≤ ∑ m ∈ range (S₀.card + 1), epiSize ξ U S₀ (m + 1) := by
    simpa using card_nsmul_le_sum (range (S₀.card + 1)) (fun m => epiSize ξ U S₀ (m + 1)) 1
      (fun m hm => hpos m (Nat.lt_succ_iff.1 (mem_range.1 hm)))
  omega

/-- **An index case inside the population.** If the index case is an individual `i₀` of a finite
population who is not initially susceptible (`i₀ ∉ S₀`), the infectives of generations
`0, …, n` number at most `Fintype.card α`: the infections of generations `1, …, n` go to distinct
individuals of `S₀` (`card_filter_epiHit_le`), and `#S₀ < Fintype.card α`. -/
theorem sum_epiSize_le_card [Fintype α] {i₀ : α} (h₀ : i₀ ∉ S₀) (n : ℕ) :
    ∑ m ∈ range (n + 1), epiSize ξ U S₀ m ≤ Fintype.card α := by
  rw [sum_range_succ', sum_epiSize_eq_card]
  have h1 := card_filter_epiHit_le U S₀ (epi ξ U S₀ n).2
  have h2 := card_lt_univ_of_notMem h₀
  have h3 : epiSize ξ U S₀ 0 = 1 := rfl
  omega

end Deterministic

/-! ### The branching process on a path space -/

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ν : Measure ℕ}

/-- The offspring numbers `ξ n i` (`i`-th individual of generation `n`) are measurable,
independent, and identically distributed with law `ν`. -/
structure IsOffspringFamily (P : Measure Ω) (ν : Measure ℕ) (ξ : ℕ → ℕ → Ω → ℕ) : Prop where
  measurable : ∀ n i, Measurable (ξ n i)
  indep : ProbabilityTheory.iIndepFun (fun p : ℕ × ℕ => ξ p.1 p.2) P
  map_eq : ∀ n i, P.map (ξ n i) = ν

namespace IsOffspringFamily

variable {ξ : ℕ → ℕ → Ω → ℕ}

/-- A family with a probability law lives on a probability space. -/
theorem isProbabilityMeasure (hξ : IsOffspringFamily P ν ξ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure P := by
  have h1 : P.map (ξ 0 0) Set.univ = 1 := by rw [hξ.map_eq 0 0]; exact measure_univ
  rw [Measure.map_apply (hξ.measurable 0 0) MeasurableSet.univ] at h1
  exact ⟨by simpa using h1⟩

/-- The σ-algebra generated by the offspring numbers indexed by `s`. -/
private abbrev genOn (ξ : ℕ → ℕ → Ω → ℕ) (s : Set (ℕ × ℕ)) : MeasurableSpace Ω :=
  ⨆ p ∈ s, MeasurableSpace.comap (ξ p.1 p.2) inferInstance

omit [MeasurableSpace Ω] in
private lemma le_genOn {s : Set (ℕ × ℕ)} {n i : ℕ} (h : (n, i) ∈ s) :
    MeasurableSpace.comap (ξ n i) inferInstance ≤ genOn ξ s :=
  le_iSup₂ (f := fun (p : ℕ × ℕ) (_ : p ∈ s) =>
    MeasurableSpace.comap (ξ p.1 p.2) inferInstance) (n, i) h

private lemma genOn_le (hξ : IsOffspringFamily P ν ξ) (s : Set (ℕ × ℕ)) :
    genOn ξ s ≤ ‹MeasurableSpace Ω› :=
  iSup₂_le fun p _ => measurable_iff_comap_le.1 (hξ.measurable p.1 p.2)

omit [MeasurableSpace Ω] in
/-- `Z n` is measurable with respect to the offspring numbers of generations `< n`. -/
private lemma measurable_bpSize_genOn (n : ℕ) :
    Measurable[genOn ξ {p | p.1 < n}] fun ω => bpSize (ξ · · ω) n := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hZ : Measurable[genOn ξ {p | p.1 < n + 1}] fun ω => bpSize (ξ · · ω) n :=
      ih.mono (biSup_mono fun p (hp : p.1 < n) => Nat.lt_succ_of_lt hp) le_rfl
    have hsum (z : ℕ) : Measurable[genOn ξ {p | p.1 < n + 1}] fun ω => ∑ i ∈ range z, ξ n i ω :=
      Finset.measurable_sum _ fun i _ =>
        measurable_iff_comap_le.2 (le_genOn (s := {p | p.1 < n + 1}) (Nat.lt_succ_self n))
    refine @measurable_to_countable' ℕ Ω _ _ (genOn ξ {p | p.1 < n + 1}) _ fun k => ?_
    have : (fun ω => bpSize (ξ · · ω) (n + 1)) ⁻¹' {k} = ⋃ z : ℕ,
        ((fun ω => bpSize (ξ · · ω) n) ⁻¹' {z} ∩
          (fun ω => ∑ i ∈ range z, ξ n i ω) ⁻¹' {k}) := by
      ext ω; simp [bpSize_succ]
    rw [this]
    exact MeasurableSet.iUnion fun z =>
      (hZ (measurableSet_singleton z)).inter (hsum z (measurableSet_singleton k))

/-- The total offspring of `z` individuals of generation `n` has law `ν^{∗z}`. -/
private lemma hasLaw_sum (hξ : IsOffspringFamily P ν ξ) [IsProbabilityMeasure ν] (n z : ℕ) :
    HasLaw (∑ i ∈ range z, ξ n i) (Measure.convPow ν z) P := by
  have hind : ProbabilityTheory.iIndepFun (fun i => ξ n i) P :=
    hξ.indep.precomp (g := fun i => (n, i)) fun _ _ h => (Prod.mk.inj h).2
  induction z with
  | zero =>
    have := hξ.isProbabilityMeasure
    exact ⟨measurable_const.aemeasurable,
      by simp [Measure.convPow_zero, Pi.zero_def, Measure.map_const]⟩
  | succ z ih =>
    have := Measure.isProbabilityMeasure_convPow (ν := ν) z
    rw [sum_range_succ, Measure.convPow_succ]
    exact (hind.indepFun_finsetSum_of_notMem (fun i => hξ.measurable n i)
      (by simp : z ∉ range z)).hasLaw_add ih ⟨(hξ.measurable n z).aemeasurable, hξ.map_eq n z⟩

theorem measurable_bpSize (hξ : IsOffspringFamily P ν ξ) (n : ℕ) :
    Measurable fun ω => bpSize (ξ · · ω) n :=
  (measurable_bpSize_genOn n).mono (genOn_le hξ _) le_rfl

/-- **The path-space Galton–Watson process.** `Z n` has the Galton–Watson law `law ν n`: given
`Z n = z`, the next generation is the total offspring of `z` fresh individuals, which is
independent of `Z n` and has law `ν^{∗z}`. -/
theorem hasLaw_bpSize (hξ : IsOffspringFamily P ν ξ) [IsProbabilityMeasure ν] (n : ℕ) :
    HasLaw (fun ω => bpSize (ξ · · ω) n) (law ν n) P := by
  have := hξ.isProbabilityMeasure
  induction n with
  | zero => exact ⟨measurable_const.aemeasurable, by simp [law, bpSize, Measure.map_const]⟩
  | succ n ih =>
    refine ⟨(hξ.measurable_bpSize _).aemeasurable, ?_⟩
    have hind : Indep (genOn ξ {p | p.1 < n}) (genOn ξ {p | p.1 = n}) P :=
      indep_iSup_of_disjoint
        (m := fun p : ℕ × ℕ => MeasurableSpace.comap (ξ p.1 p.2) inferInstance)
        (S := {p | p.1 < n}) (T := {p | p.1 = n})
        (fun p => measurable_iff_comap_le.1 (hξ.measurable p.1 p.2))
        ((iIndepFun_iff_iIndep (fun _ => inferInstance) (fun p : ℕ × ℕ => ξ p.1 p.2) P).1
          hξ.indep)
        (Set.disjoint_left.2 fun p (h1 : p.1 < n) (h2 : p.1 = n) => by omega)
    have hsumG (z : ℕ) : Measurable[genOn ξ {p | p.1 = n}] (∑ i ∈ range z, ξ n i) := by
      rw [Finset.sum_fn]
      exact Finset.measurable_fun_sum _ fun i _ =>
        measurable_iff_comap_le.2 (le_genOn (s := {p | p.1 = n}) rfl)
    have hsum (z : ℕ) : Measurable (∑ i ∈ range z, ξ n i) :=
      (hsumG z).mono (genOn_le hξ _) le_rfl
    have hset (k : ℕ) : (fun ω => bpSize (ξ · · ω) (n + 1)) ⁻¹' {k} = ⋃ z : ℕ,
        ((fun ω => bpSize (ξ · · ω) n) ⁻¹' {z} ∩ (∑ i ∈ range z, ξ n i) ⁻¹' {k}) := by
      ext ω; simp [bpSize_succ, Finset.sum_apply]
    rw [Measure.ext_iff_singleton]
    intro k
    rw [Measure.map_apply (hξ.measurable_bpSize _) (measurableSet_singleton k), law,
      Measure.bind_apply (measurableSet_singleton k) measurable_from_nat.aemeasurable,
      lintegral_countable', ← ih.map_eq, hset, measure_iUnion]
    · congr 1; ext z
      rw [(Indep_iff _ _ _).1 hind _ _ (measurable_bpSize_genOn n (measurableSet_singleton z))
          (hsumG z (measurableSet_singleton k)),
        Measure.map_apply (hξ.measurable_bpSize n) (measurableSet_singleton z), mul_comm,
        ← (hasLaw_sum hξ n z).map_eq, Measure.map_apply (hsum z) (measurableSet_singleton k)]
    · intro z z' hzz'
      refine Set.disjoint_left.2 fun ω h1 h2 => hzz' ?_
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
      rw [← h1.1, ← h2.1]
    · exact fun z => (hξ.measurable_bpSize n (measurableSet_singleton z)).inter
        (hsum z (measurableSet_singleton k))

/-- `P(Z n = 0) = (law ν n){0} = f^[n](0)`. -/
theorem measureReal_bpSize_eq_zero (hξ : IsOffspringFamily P ν ξ) [IsProbabilityMeasure ν]
    (n : ℕ) : P.real {ω | bpSize (ξ · · ω) n = 0} = (law ν n).real {0} := by
  rw [← (hasLaw_bpSize hξ n).map_eq, map_measureReal_apply (hξ.measurable_bpSize n)
    (measurableSet_singleton 0)]
  rfl

/-- **Extinction of the path-space process.** The branching process dies out with probability
`extinctionProb ν`, the least fixed point of the offspring generating function in `[0, 1]`. -/
theorem measureReal_exists_bpSize_eq_zero (hξ : IsOffspringFamily P ν ξ)
    [IsProbabilityMeasure ν] :
    P.real {ω | ∃ n, bpSize (ξ · · ω) n = 0} = extinctionProb ν := by
  have := hξ.isProbabilityMeasure
  have hmono : Monotone fun n => {ω | bpSize (ξ · · ω) n = 0} := by
    refine monotone_nat_of_le_succ fun n ω (h : bpSize _ n = 0) => ?_
    exact bpSize_succ_eq_zero _ h
  have ht := tendsto_measure_iUnion_atTop (μ := P) hmono
  have ht' : Tendsto (fun n => P.real {ω | bpSize (ξ · · ω) n = 0}) atTop
      (𝓝 (P.real (⋃ n, {ω | bpSize (ξ · · ω) n = 0}))) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht
  simp_rw [measureReal_bpSize_eq_zero hξ] at ht'
  rw [Set.ofPred_exists, tendsto_nhds_unique ht' (tendsto_law_real_zero ν)]

/-- By domination, the epidemic is extinct by generation `n` at least as often as the branching
process: `P(Z n = 0) ≤ P(I n = 0)`, whatever the contact targets. -/
theorem law_real_zero_le_measureReal_epiSize_eq_zero (hξ : IsOffspringFamily P ν ξ)
    [IsProbabilityMeasure ν] {α : Type*} [DecidableEq α] (U : ℕ → Ω → α) (S₀ : Finset α)
    (n : ℕ) : (law ν n).real {0} ≤ P.real {ω | epiSize (ξ · · ω) (U · ω) S₀ n = 0} := by
  have := hξ.isProbabilityMeasure
  rw [← measureReal_bpSize_eq_zero hξ n]
  exact measureReal_mono fun ω (hω : bpSize _ n = 0) =>
    Nat.eq_zero_of_le_zero (hω ▸ epiSize_le_bpSize _ _ S₀ n)

end IsOffspringFamily

/-! ### Wasted contacts: the birthday bound -/

/-- The hypotheses of the coupled model in a population `Fin N`, started by an index case outside
`Fin N` or by an individual left out of `S₀` (see the module docstring): offspring numbers i.i.d.
with law `ν`, and contact targets i.i.d. uniform on `Fin N`. Nothing is assumed about the joint
law of the offspring numbers and the targets (in the epidemic model they are independent). -/
structure IsEarlyEpidemic (P : Measure Ω) (ν : Measure ℕ) (N : ℕ) (ξ : ℕ → ℕ → Ω → ℕ)
    (U : ℕ → Ω → Fin N) : Prop extends IsOffspringFamily P ν ξ where
  indep_target : ProbabilityTheory.iIndepFun U P
  measure_target : ∀ j a, P (U j ⁻¹' {a}) = (N : ℝ≥0∞)⁻¹

namespace IsEarlyEpidemic

variable {N : ℕ} {ξ : ℕ → ℕ → Ω → ℕ} {U : ℕ → Ω → Fin N}

/-- Two distinct contacts go to the same individual with probability at most `1 / N`. -/
theorem measure_target_eq_le (h : IsEarlyEpidemic P ν N ξ U) {j j' : ℕ} (hjj' : j' ≠ j) :
    P {ω | U j' ω = U j ω} ≤ (N : ℝ≥0∞)⁻¹ := by
  have hind := h.indep_target.indepFun hjj'
  have hsub : {ω | U j' ω = U j ω} ⊆ ⋃ a ∈ (univ : Finset (Fin N)), U j' ⁻¹' {a} ∩ U j ⁻¹' {a} :=
    fun ω hω => Set.mem_biUnion (mem_univ (U j ω)) ⟨hω, rfl⟩
  calc P {ω | U j' ω = U j ω}
      ≤ ∑ a : Fin N, P (U j' ⁻¹' {a} ∩ U j ⁻¹' {a}) :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ = ∑ _a : Fin N, (N : ℝ≥0∞)⁻¹ * (N : ℝ≥0∞)⁻¹ := by
        refine sum_congr rfl fun a _ => ?_
        rw [hind.measure_inter_preimage_eq_mul _ _ (measurableSet_singleton a)
          (measurableSet_singleton a), h.measure_target, h.measure_target]
    _ ≤ (N : ℝ≥0∞)⁻¹ := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
        rcases eq_or_ne N 0 with rfl | hN
        · simp
        · rw [ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 hN) (ENNReal.natCast_ne_top N), one_mul]

/-- Contact number `j` is wasted (its target is not initially susceptible, or was contacted
before) with probability at most `(N - #S₀ + j) / N`. -/
theorem measure_not_epiHit_le (h : IsEarlyEpidemic P ν N ξ U) (S₀ : Finset (Fin N)) (j : ℕ) :
    P {ω | ¬ epiHit (U · ω) S₀ j} ≤ ((N - S₀.card + j : ℕ) : ℝ≥0∞) * (N : ℝ≥0∞)⁻¹ := by
  have hsub : {ω | ¬ epiHit (U · ω) S₀ j} ⊆
      (⋃ a ∈ (univ \ S₀ : Finset (Fin N)), U j ⁻¹' {a}) ∪
        ⋃ j' ∈ range j, {ω | U j' ω = U j ω} := by
    intro ω hω
    simp only [epiHit, not_and_or, not_forall, not_not, Set.mem_ofPred_eq] at hω
    rcases hω with hω | ⟨j', hj', hU⟩
    · exact Or.inl (Set.mem_biUnion (by simpa using hω) rfl)
    · exact Or.inr (Set.mem_biUnion (mem_range.2 hj') hU)
  calc P {ω | ¬ epiHit (U · ω) S₀ j}
      ≤ ∑ a ∈ univ \ S₀, P (U j ⁻¹' {a}) + ∑ j' ∈ range j, P {ω | U j' ω = U j ω} :=
        (measure_mono hsub).trans ((measure_union_le _ _).trans
          (add_le_add (measure_biUnion_finset_le _ _) (measure_biUnion_finset_le _ _)))
    _ ≤ ∑ _a ∈ univ \ S₀, (N : ℝ≥0∞)⁻¹ + ∑ _j' ∈ range j, (N : ℝ≥0∞)⁻¹ := by
        gcongr with a _ j' hj'
        · exact (h.measure_target j a).le
        · exact h.measure_target_eq_le (mem_range.1 hj').ne
    _ = ((N - S₀.card + j : ℕ) : ℝ≥0∞) * (N : ℝ≥0∞)⁻¹ := by
        rw [sum_const, sum_const, card_univ_sdiff, Fintype.card_fin, card_range, nsmul_eq_mul,
          nsmul_eq_mul, ← add_mul, Nat.cast_add]

/-- **Birthday bound.** Some of the first `M` contacts is wasted with probability at most
`(M (N - #S₀) + C(M, 2)) / N`. -/
theorem measure_exists_not_epiHit_le (h : IsEarlyEpidemic P ν N ξ U) (S₀ : Finset (Fin N))
    (M : ℕ) : P {ω | ∃ j < M, ¬ epiHit (U · ω) S₀ j} ≤
      ((M * (N - S₀.card) + M.choose 2 : ℕ) : ℝ≥0∞) * (N : ℝ≥0∞)⁻¹ := by
  have hsub : {ω | ∃ j < M, ¬ epiHit (U · ω) S₀ j} ⊆
      ⋃ j ∈ range M, {ω | ¬ epiHit (U · ω) S₀ j} := fun ω ⟨j, hj, hω⟩ =>
    Set.mem_biUnion (mem_range.2 hj) hω
  calc P {ω | ∃ j < M, ¬ epiHit (U · ω) S₀ j}
      ≤ ∑ j ∈ range M, ((N - S₀.card + j : ℕ) : ℝ≥0∞) * (N : ℝ≥0∞)⁻¹ :=
        (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans
          (sum_le_sum fun j _ => h.measure_not_epiHit_le S₀ j))
    _ = ((M * (N - S₀.card) + M.choose 2 : ℕ) : ℝ≥0∞) * (N : ℝ≥0∞)⁻¹ := by
        rw [← sum_mul, ← Nat.cast_sum, sum_add_distrib, sum_const, card_range, smul_eq_mul,
          sum_range_id, ← Nat.choose_two_right]

/-- A model of the epidemic lives in a nonempty population. -/
theorem ne_zero (h : IsEarlyEpidemic P ν N ξ U) [IsProbabilityMeasure ν] : N ≠ 0 := by
  rintro rfl
  have := h.isProbabilityMeasure
  have hΩ : IsEmpty Ω := ⟨fun ω => (U 0 ω).elim0⟩
  have h1 : P Set.univ = 1 := measure_univ
  rw [Set.univ_eq_empty_iff.2 hΩ, measure_empty] at h1
  exact zero_ne_one h1

/-- **The approximation bound.** For every `L`, the probability that the epidemic is extinct by
generation `n` exceeds the branching-process value `P(Z n = 0)` by at most the probability that
some generation `≤ n` of the branching process exceeds `L`, plus the probability that one of the
first `n L` contacts is wasted. -/
theorem measureReal_epiSize_eq_zero_le (h : IsEarlyEpidemic P ν N ξ U) [IsProbabilityMeasure ν]
    (S₀ : Finset (Fin N)) (n L : ℕ) :
    P.real {ω | epiSize (ξ · · ω) (U · ω) S₀ n = 0} ≤ (law ν n).real {0} +
      ∑ m ∈ range n, (law ν (m + 1)).real (Set.Ioi L) +
      ((n * L * (N - S₀.card) + (n * L).choose 2 : ℕ) : ℝ) / N := by
  have := h.isProbabilityMeasure
  have hsub : {ω | epiSize (ξ · · ω) (U · ω) S₀ n = 0} ⊆
      ({ω | bpSize (ξ · · ω) n = 0} ∪ ⋃ m ∈ range n, {ω | L < bpSize (ξ · · ω) (m + 1)}) ∪
        {ω | ∃ j < n * L, ¬ epiHit (U · ω) S₀ j} := by
    intro ω hω
    by_contra hc
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists, not_lt,
      not_and, not_not, mem_range] at hc
    obtain ⟨⟨hZ, hL⟩, hhit⟩ := hc
    have hC : bpContacts (ξ · · ω) n ≤ n * L :=
      calc bpContacts (ξ · · ω) n ≤ ∑ _m ∈ range n, L :=
            sum_le_sum fun m hm => hL m (mem_range.1 hm)
        _ = n * L := by rw [sum_const, card_range, smul_eq_mul]
    exact hZ (epiSize_eq_bpSize_of_forall_hit _ _ S₀ hhit hC ▸ hω)
  have hB : P.real (⋃ m ∈ range n, {ω | L < bpSize (ξ · · ω) (m + 1)}) ≤
      ∑ m ∈ range n, (law ν (m + 1)).real (Set.Ioi L) := by
    refine (measureReal_biUnion_finset_le _ _).trans (sum_le_sum fun m _ => le_of_eq ?_)
    rw [← (IsOffspringFamily.hasLaw_bpSize h.toIsOffspringFamily (m + 1)).map_eq,
      map_measureReal_apply (h.measurable_bpSize _) measurableSet_Ioi]
    rfl
  have hC : P.real {ω | ∃ j < n * L, ¬ epiHit (U · ω) S₀ j} ≤
      ((n * L * (N - S₀.card) + (n * L).choose 2 : ℕ) : ℝ) / N := by
    have hN : (N : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 h.ne_zero)
    refine (ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hN)
      (h.measure_exists_not_epiHit_le S₀ (n * L))).trans (le_of_eq ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
      div_eq_mul_inv]
  calc P.real {ω | epiSize (ξ · · ω) (U · ω) S₀ n = 0}
      ≤ P.real {ω | bpSize (ξ · · ω) n = 0} +
          P.real (⋃ m ∈ range n, {ω | L < bpSize (ξ · · ω) (m + 1)}) +
          P.real {ω | ∃ j < n * L, ¬ epiHit (U · ω) S₀ j} :=
        (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans
          (add_le_add_left (measureReal_union_le _ _) _))
    _ ≤ _ := by
        rw [IsOffspringFamily.measureReal_bpSize_eq_zero h.toIsOffspringFamily]
        gcongr

end IsEarlyEpidemic

end Probability

/-! ### A canonical model -/

section Canonical

variable (ν : Measure ℕ) [IsProbabilityMeasure ν] (N : ℕ) [NeZero N]

/-- The uniform law on the population `Fin N` is a probability measure. -/
theorem isProbabilityMeasure_uniformOfFinset_univ :
    IsProbabilityMeasure (Measure.uniformOfFinset (univ : Finset (Fin N))) := by
  refine ⟨?_⟩
  rw [Measure.uniformOfFinset, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 (NeZero.ne N)) (ENNReal.natCast_ne_top N)

/-- The canonical probability space of the coupled model: i.i.d. `ν` offspring numbers indexed by
`(generation, individual)`, independent of i.i.d. uniform contact targets. -/
noncomputable def canonicalMeasure : Measure ((ℕ × ℕ → ℕ) × (ℕ → Fin N)) :=
  have := isProbabilityMeasure_uniformOfFinset_univ N
  (Measure.infinitePi fun _ : ℕ × ℕ => ν).prod
    (Measure.infinitePi fun _ : ℕ => Measure.uniformOfFinset (univ : Finset (Fin N)))

/-- The hypotheses `IsEarlyEpidemic` are satisfiable: the coordinate maps of the canonical space
form a model of the coupled epidemic. -/
theorem isEarlyEpidemic_canonical :
    IsEarlyEpidemic (canonicalMeasure ν N) ν N (fun n i ω => ω.1 (n, i)) (fun j ω => ω.2 j) := by
  have := isProbabilityMeasure_uniformOfFinset_univ N
  set P := canonicalMeasure ν N
  have hP : P = (Measure.infinitePi fun _ : ℕ × ℕ => ν).prod
      (Measure.infinitePi fun _ : ℕ => Measure.uniformOfFinset (univ : Finset (Fin N))) := rfl
  have : IsProbabilityMeasure P := by rw [hP]; infer_instance
  have hfst : P.map Prod.fst = Measure.infinitePi fun _ : ℕ × ℕ => ν := by
    rw [hP, Measure.map_fst_prod, measure_univ, one_smul]
  have hsnd : P.map Prod.snd =
      Measure.infinitePi fun _ : ℕ => Measure.uniformOfFinset (univ : Finset (Fin N)) := by
    rw [hP, Measure.map_snd_prod, measure_univ, one_smul]
  have hξ (p : ℕ × ℕ) : P.map (fun ω => ω.1 p) = ν := by
    rw [show (fun ω : (ℕ × ℕ → ℕ) × (ℕ → Fin N) => ω.1 p) = (fun x => x p) ∘ Prod.fst from rfl,
      ← Measure.map_map (measurable_pi_apply p) measurable_fst, hfst, Measure.infinitePi_map_eval]
  have hU (j : ℕ) : P.map (fun ω => ω.2 j) = Measure.uniformOfFinset (univ : Finset (Fin N)) := by
    rw [show (fun ω : (ℕ × ℕ → ℕ) × (ℕ → Fin N) => ω.2 j) = (fun x => x j) ∘ Prod.snd from rfl,
      ← Measure.map_map (measurable_pi_apply j) measurable_snd, hsnd, Measure.infinitePi_map_eval]
  refine
    { measurable := fun n i => (measurable_pi_apply (n, i)).comp measurable_fst
      indep := ?_
      map_eq := fun n i => hξ (n, i)
      indep_target := ?_
      measure_target := fun j a => ?_ }
  · refine (iIndepFun_iff_map_fun_eq_infinitePi_map (P := P)
      (X := fun (p : ℕ × ℕ) (ω : (ℕ × ℕ → ℕ) × (ℕ → Fin N)) => ω.1 (p.1, p.2))
      fun p => (measurable_pi_apply (p.1, p.2)).comp measurable_fst).2 ?_
    simp only [Prod.mk.eta, hξ]
    exact hfst
  · refine (iIndepFun_iff_map_fun_eq_infinitePi_map (P := P)
      (X := fun (j : ℕ) (ω : (ℕ × ℕ → ℕ) × (ℕ → Fin N)) => ω.2 j)
      fun j => (measurable_pi_apply j).comp measurable_snd).2 ?_
    simp only [hU]
    exact hsnd
  · have h : P.map (fun ω => ω.2 j) {a} =
        Measure.uniformOfFinset (univ : Finset (Fin N)) {a} := by
      rw [hU j]
    rw [Measure.map_apply (show Measurable fun ω : (ℕ × ℕ → ℕ) × (ℕ → Fin N) => ω.2 j from
      (measurable_pi_apply j).comp measurable_snd) (measurableSet_singleton a),
      Measure.uniformOfFinset_apply_singleton_of_mem (mem_univ a), card_univ,
      Fintype.card_fin] at h
    exact h

end Canonical

/-! ### Threshold behavior -/

section Threshold

variable {ν : Measure ℕ} [IsProbabilityMeasure ν]

/-- `P(Z n = 0) ≤ q`. -/
theorem law_real_zero_le_extinctionProb (n : ℕ) : (law ν n).real {0} ≤ extinctionProb ν :=
  le_ciSup (f := fun n => (law ν n).real {0}) ⟨1, by rintro _ ⟨k, rfl⟩; exact measureReal_le_one⟩ n

/-- An offspring law with mean `> 1` is not the Dirac mass at `1`. -/
theorem measure_one_ne_one_of_one_lt_mean (hm : 1 < mean ν) : ν {1} ≠ 1 := by
  intro h1
  have hae : ∀ᵐ k : ℕ ∂ν, (k : ℝ≥0∞) = 1 := by
    rw [ae_iff]
    refine measure_mono_null (fun k (hk : ¬ (k : ℝ≥0∞) = 1) (hk' : k ∈ ({1} : Set ℕ)) => hk ?_)
      ((prob_compl_eq_zero_iff (measurableSet_singleton 1)).2 h1)
    rw [Set.mem_singleton_iff.1 hk']
    simp
  rw [mean, lintegral_congr_ae hae, lintegral_one, measure_univ] at hm
  exact lt_irrefl 1 hm

/-- **Major outbreaks have positive probability.** If `R₀ = mean ν > 1`, the branching process
survives with probability `1 - q > 0`; by `tendsto_measureReal_epiSize_ne_zero` and
`tendsto_one_sub_law_real_zero` this is the probability of a major outbreak in the sense of the
module docstring. -/
theorem one_sub_extinctionProb_pos (hm : 1 < mean ν) : 0 < 1 - extinctionProb ν := by
  have hle := (isLeast_extinctionProb ν).1.1.2
  have hne : extinctionProb ν ≠ 1 := fun h =>
    not_le_of_gt hm ((extinctionProb_eq_one_iff ν (measure_one_ne_one_of_one_lt_mean hm)).1 h)
  exact sub_pos.2 (lt_of_le_of_ne hle hne)

/-- The survival probabilities `1 - P(Z n = 0)` are non-increasing in `n`. -/
theorem antitone_one_sub_law_real_zero : Antitone fun n => 1 - (law ν n).real {0} :=
  fun _ _ hnm => sub_le_sub_left (monotone_law_real_zero ν hnm) 1

/-- The survival probabilities `1 - P(Z n = 0)` converge to `1 - q`. -/
theorem tendsto_one_sub_law_real_zero :
    Tendsto (fun n => 1 - (law ν n).real {0}) atTop (𝓝 (1 - extinctionProb ν)) :=
  (tendsto_law_real_zero ν).const_sub 1

/-- In a finite population the epidemic dies out almost surely, whatever the offspring law and
the contact targets (`epiSize_card_add_one_eq_zero`). This is why eventual extinction cannot
distinguish minor from major outbreaks; see the module docstring. -/
theorem measureReal_exists_epiSize_eq_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ξ : ℕ → ℕ → Ω → ℕ) {α : Type*} [DecidableEq α]
    (U : ℕ → Ω → α) (S₀ : Finset α) :
    P.real {ω | ∃ n, epiSize (ξ · · ω) (U · ω) S₀ n = 0} = 1 := by
  have h : {ω | ∃ n, epiSize (ξ · · ω) (U · ω) S₀ n = 0} = Set.univ :=
    Set.eq_univ_of_forall fun ω => ⟨_, epiSize_card_add_one_eq_zero (ξ · · ω) (U · ω) S₀⟩
  rw [h, probReal_univ]

universe u v in
/-- **Minor outbreaks only when `R₀ ≤ 1`, uniformly in the population.** For every `ε > 0` there
is a number of generations `n₀` such that, in every population, with every law of the contact
targets, the epidemic is extinct by generation `n` (any `n ≥ n₀`) with probability `> 1 - ε`. -/
theorem exists_forall_measureReal_epiSize_eq_zero_gt (h1 : ν {1} ≠ 1) (hm : mean ν ≤ 1)
    {ε : ℝ} (hε : 0 < ε) : ∃ n₀, ∀ n ≥ n₀, ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {ξ : ℕ → ℕ → Ω → ℕ} {α : Type v} [DecidableEq α] (U : ℕ → Ω → α) (S₀ : Finset α),
      IsOffspringFamily P ν ξ → 1 - ε < P.real {ω | epiSize (ξ · · ω) (U · ω) S₀ n = 0} := by
  have ht := tendsto_law_real_zero ν
  rw [(extinctionProb_eq_one_iff ν h1).2 hm] at ht
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (ht.eventually (lt_mem_nhds (by linarith : 1 - ε < 1)))
  exact ⟨n₀, fun n hn Ω _ P ξ α _ U S₀ hξ =>
    (hn₀ n hn).trans_le (hξ.law_real_zero_le_measureReal_epiSize_eq_zero U S₀ n)⟩

private lemma tendsto_measureReal_Ioi (μ : Measure ℕ) [IsFiniteMeasure μ] :
    Tendsto (fun L : ℕ => μ.real (Set.Ioi L)) atTop (𝓝 0) := by
  have h := tendsto_measure_iInter_atTop (μ := μ) (s := fun L : ℕ => Set.Ioi L)
    (fun _ => measurableSet_Ioi.nullMeasurableSet) (fun _ _ hab => Set.Ioi_subset_Ioi hab)
    ⟨0, measure_ne_top _ _⟩
  have he : (⋂ L : ℕ, Set.Ioi L) = ∅ :=
    Set.eq_empty_of_forall_notMem fun k hk => lt_irrefl k (Set.mem_iInter.1 hk k)
  rw [he, measure_empty] at h
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h

variable {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)] {P : ∀ k, Measure (Ω k)} {N : ℕ → ℕ}
  {ξ : ∀ k, ℕ → ℕ → Ω k → ℕ} {U : ∀ k, ℕ → Ω k → Fin (N k)} {S₀ : ∀ k, Finset (Fin (N k))}

/-- **Large-population limit.** Along a sequence of models `k` with population sizes
`N k → ∞` in which all but `o(N k)` individuals are initially susceptible (an index case inside
the population is one of these `o(N k)` individuals), the probability that the epidemic is
extinct by generation `n` converges to the branching-process value
`P(Z n = 0) = f^[n](0)`. As `n → ∞` these values increase to the extinction probability `q`
(`tendsto_law_real_zero`): `q` is the probability of a minor outbreak in the sense of the
module docstring. -/
theorem tendsto_measureReal_epiSize_eq_zero (h : ∀ k, IsEarlyEpidemic (P k) ν (N k) (ξ k) (U k))
    (hN : Tendsto N atTop atTop)
    (hS : Tendsto (fun k => ((N k - (S₀ k).card : ℕ) : ℝ) / N k) atTop (𝓝 0)) (n : ℕ) :
    Tendsto (fun k => (P k).real {ω | epiSize (ξ k · · ω) (U k · ω) (S₀ k) n = 0}) atTop
      (𝓝 ((law ν n).real {0})) := by
  rw [tendsto_order]
  refine ⟨fun b hb => Eventually.of_forall fun k => hb.trans_le
    ((h k).toIsOffspringFamily.law_real_zero_le_measureReal_epiSize_eq_zero _ _ n), fun b hb => ?_⟩
  have hδ : 0 < (b - (law ν n).real {0}) / 2 := half_pos (sub_pos.2 hb)
  have htail : Tendsto (fun L : ℕ => ∑ m ∈ range n, (law ν (m + 1)).real (Set.Ioi L)) atTop
      (𝓝 0) := by
    simpa using tendsto_finsetSum (range n) fun m _ => tendsto_measureReal_Ioi (law ν (m + 1))
  obtain ⟨L, hL⟩ := (htail.eventually (gt_mem_nhds hδ)).exists
  have hc : Tendsto (fun k =>
      ((n * L * (N k - (S₀ k).card) + (n * L).choose 2 : ℕ) : ℝ) / N k) atTop (𝓝 0) := by
    have heq : (fun k => ((n * L * (N k - (S₀ k).card) + (n * L).choose 2 : ℕ) : ℝ) / N k) =
        fun k => ((n : ℝ) * L) * (((N k - (S₀ k).card : ℕ) : ℝ) / N k) +
          ((n * L).choose 2 : ℝ) / N k := by
      ext k; simp only [Nat.cast_add, Nat.cast_mul]; ring
    rw [heq]
    simpa using (hS.const_mul ((n : ℝ) * L)).add
      (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hN))
  filter_upwards [hc.eventually (gt_mem_nhds hδ)] with k hk
  calc _ ≤ _ := (h k).measureReal_epiSize_eq_zero_le (S₀ k) n L
    _ < b := by linarith

/-- **Survival in the large-population limit.** The probability that the epidemic is still
alive at generation `n` converges to `1 - P(Z n = 0) ≥ 1 - q`; when `R₀ > 1` this limit is
positive for every `n` (`one_sub_extinctionProb_pos`, `one_sub_extinctionProb_le`). -/
theorem tendsto_measureReal_epiSize_ne_zero (h : ∀ k, IsEarlyEpidemic (P k) ν (N k) (ξ k) (U k))
    (hN : Tendsto N atTop atTop)
    (hS : Tendsto (fun k => ((N k - (S₀ k).card : ℕ) : ℝ) / N k) atTop (𝓝 0)) (n : ℕ) :
    Tendsto (fun k => (P k).real {ω | epiSize (ξ k · · ω) (U k · ω) (S₀ k) n ≠ 0}) atTop
      (𝓝 (1 - (law ν n).real {0})) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    ((tendsto_measureReal_epiSize_eq_zero h hN hS n).const_sub 1) tendsto_const_nhds
    (fun k => ?_) (fun k => ?_)
  · have := (h k).isProbabilityMeasure
    have h1 := measureReal_union_le (μ := P k)
      {ω | epiSize (ξ k · · ω) (U k · ω) (S₀ k) n = 0}
      {ω | epiSize (ξ k · · ω) (U k · ω) (S₀ k) n ≠ 0}
    rw [show {ω | epiSize (ξ k · · ω) (U k · ω) (S₀ k) n = 0} ∪
        {ω | epiSize (ξ k · · ω) (U k · ω) (S₀ k) n ≠ 0} = Set.univ from
      Set.eq_univ_of_forall fun ω => em _, probReal_univ] at h1
    dsimp only
    linarith
  · have := (h k).isProbabilityMeasure
    have hZ := (h k).toIsOffspringFamily
    calc (P k).real {ω | epiSize (ξ k · · ω) (U k · ω) (S₀ k) n ≠ 0}
        ≤ (P k).real {ω | bpSize (ξ k · · ω) n = 0}ᶜ :=
          measureReal_mono fun ω hω hZ0 =>
            hω (Nat.eq_zero_of_le_zero ((hZ0 : bpSize _ n = 0) ▸ epiSize_le_bpSize _ _ _ n))
      _ = 1 - (law ν n).real {0} := by
          change (P k).real ((fun ω => bpSize (ξ k · · ω) n) ⁻¹' {0})ᶜ = _
          rw [probReal_compl_eq_one_sub (hZ.measurable_bpSize n (measurableSet_singleton 0)),
            ← hZ.measureReal_bpSize_eq_zero]
          rfl

/-- The large-population survival probability at generation `n` is at least `1 - q`. -/
theorem one_sub_extinctionProb_le (n : ℕ) :
    1 - extinctionProb ν ≤ 1 - (law ν n).real {0} :=
  sub_le_sub_left (law_real_zero_le_extinctionProb n) 1

end Threshold

end MathlibExt.Biology.Epidemiology.EarlyEpidemicBranching
