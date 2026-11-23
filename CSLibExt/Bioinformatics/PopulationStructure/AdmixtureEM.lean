/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.LatentVariable.BernoulliMixture
public import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The admixture-model likelihood and the FRAPPE EM algorithm

The admixture model of population structure (Pritchard, Stephens and Donnelly 2000, the
"admixture model" of STRUCTURE; Tang, Peng, Wang and Risch 2005, FRAPPE; Alexander, Novembre and
Lange 2009, ADMIXTURE). There are `I` individuals, `J` biallelic SNPs and `K` ancestral
populations (finite types). The parameters `θ = (Q, F)` are the ancestry proportions
`Q i k > 0` with `∑ k, Q i k = 1` and the reference-allele frequencies `0 < F k j < 1` of SNP `j`
in population `k` (`Params`; strict positivity keeps every log-likelihood term finite). The
genotype `g i j ∈ {0, 1, 2}` is the number of reference alleles of individual `i` at SNP `j`.

Each of the two allele copies `c : Fin 2` of `(i, j)` is an observation `(i, j, a)`, where
`a = decide (c < g i j)` records whether the copy carries the reference allele (`copyAllele`),
with latent variable `z : K`, the ancestral population of that copy, and joint weight
`p θ (i, j, a) z = Q i z * (if a then F z j else 1 - F z j)` (`joint`). This is an instance of
the generic EM of `CSLibExt/MachineLearning/LatentVariable/ExpectationMaximization.lean`; the
`2 |I| |J|` copies are indexed through `Fintype.equivFin` (`data`).

The closed-form EM step proved optimal here is FRAPPE's (Tang et al. 2005). ADMIXTURE
(Alexander, Novembre and Lange 2009) maximizes the same likelihood with a different optimizer
(block relaxation with quasi-Newton acceleration), so the names `admixtureLogLik` refer to the
shared likelihood, not to ADMIXTURE's update rule.

## Main results

* `marginal_eq`: the marginal probability of a copy is `qf θ i j = ∑ k, Q i k * F k j` (reference)
  or `1 - qf θ i j` (alternative).
* `logLik_eq_admixtureLogLik`: the EM log-likelihood of the allele copies is the admixture
  log-likelihood `∑ i, ∑ j, (g i j * log (qf θ i j) + (2 - g i j) * log (1 - qf θ i j))`.
* `admixtureLogLik_le_of_emQ_le`, `admixtureLogLik_iterate_monotone`: the EM theorem for this
  model.
* `emStep` (`mStepQ`, `mStepF`; `mStep_Q_pos`, `mStep_F_pos`, `mStep_F_lt_one`): the closed-form
  FRAPPE EM update `Q' i k = (∑ j, ∑ c, r) / (2 J)`,
  `F' k j = (∑ i, ∑ c reference, r) / (∑ i, ∑ c, r)` with responsibilities `r = posterior`; it
  is strictly inside the parameter set when `J` is nonempty and every SNP is polymorphic in the
  sample (`Polymorphic`).
* `emQ_le_emStep`: **the update maximizes `Q(· | θ)`** over the parameter set (Gibbs'
  inequality, separately for the `Q`-part and for each `(k, j)` in the `F`-part).
* `admixtureLogLik_le_emStep`, `admixtureLogLik_iterate_emStep_monotone`: the admixture
  log-likelihood never decreases along the FRAPPE EM iterates.

## References

* J. K. Pritchard, M. Stephens, P. Donnelly, *Inference of population structure using multilocus
  genotype data*, Genetics 155 (2000) 945–959.
* H. Tang, J. Peng, P. Wang, N. J. Risch, *Estimation of individual admixture: analytical and
  study design considerations*, Genet. Epidemiol. 28 (2005) 289–301.
* D. H. Alexander, J. Novembre, K. Lange, *Fast model-based estimation of ancestry in unrelated
  individuals*, Genome Res. 19 (2009) 1655–1664.

## Cost model

None: the subject is the likelihood, over the reals.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.PopulationStructure.AdmixtureEM

open Real
open Cslib.MachineLearning.LatentVariable.ExpectationMaximization
open Cslib.MachineLearning.LatentVariable.BernoulliMixture (sum_mul_log_le_sum_mul_log_div)

variable {I J K : Type*} [Fintype K]

/-! ## The model -/

variable (I J K) in
/-- Parameters `θ = (Q, F)` of the admixture model: positive ancestry proportions `Q i k` summing
to one over `k`, and reference-allele frequencies `F k j` strictly between `0` and `1`. -/
structure Params where
  /-- The ancestry proportion of population `k` in individual `i`. -/
  Q : I → K → ℝ
  /-- The reference-allele frequency of SNP `j` in population `k`. -/
  F : K → J → ℝ
  /-- Ancestry proportions are positive. -/
  Q_pos : ∀ i k, 0 < Q i k
  /-- Ancestry proportions of each individual sum to one. -/
  Q_sum : ∀ i, ∑ k, Q i k = 1
  /-- Allele frequencies are positive. -/
  F_pos : ∀ k j, 0 < F k j
  /-- Allele frequencies are below one. -/
  F_lt_one : ∀ k j, F k j < 1

/-- The reference-allele probability `qf θ i j = ∑ k, Q i k * F k j` of a copy of SNP `j` in
individual `i`. -/
noncomputable def qf (θ : Params I J K) (i : I) (j : J) : ℝ := ∑ k, θ.Q i k * θ.F k j

/-- The joint weight of an allele copy `(i, j, a)` and its ancestral population `k`:
`Q i k * (if a then F k j else 1 - F k j)`. -/
noncomputable def joint (θ : Params I J K) (x : I × J × Bool) (k : K) : ℝ :=
  θ.Q x.1 k * if x.2.2 then θ.F k x.2.1 else 1 - θ.F k x.2.1

/-- The joint weight is positive (the standing hypothesis of the generic EM). -/
theorem joint_pos (θ : Params I J K) (x : I × J × Bool) (k : K) : 0 < joint θ x k := by
  refine mul_pos (θ.Q_pos _ k) ?_
  split_ifs
  · exact θ.F_pos k _
  · linarith [θ.F_lt_one k x.2.1]

/-- **The marginal of an allele copy**: reference with probability `qf θ i j`, alternative with
probability `1 - qf θ i j`. -/
theorem marginal_eq (θ : Params I J K) (i : I) (j : J) (a : Bool) :
    marginal joint θ (i, j, a) = if a then qf θ i j else 1 - qf θ i j := by
  cases a
  · simp only [marginal, joint, Bool.false_eq_true, ↓reduceIte, qf, mul_sub, mul_one,
      Finset.sum_sub_distrib, θ.Q_sum]
  · simp [marginal, joint, qf]

/-- The reference-allele probability is positive. -/
theorem qf_pos [Nonempty K] (θ : Params I J K) (i : I) (j : J) : 0 < qf θ i j :=
  Finset.sum_pos (fun k _ => mul_pos (θ.Q_pos i k) (θ.F_pos k j)) Finset.univ_nonempty

/-- The reference-allele probability is below one. -/
theorem qf_lt_one [Nonempty K] (θ : Params I J K) (i : I) (j : J) : qf θ i j < 1 := by
  have h : 0 < marginal joint θ (i, j, false) :=
    Finset.sum_pos (fun k _ => joint_pos θ _ k) Finset.univ_nonempty
  rw [marginal_eq] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  linarith

/-! ## The data: two allele copies per genotype -/

/-- Whether copy `c` of the genotype `g i j` (with `g i j` reference copies) carries the
reference allele: copies `c < g i j` do. -/
def isRef (g : I → J → Fin 3) (i : I) (j : J) (c : Fin 2) : Bool := decide (c.val < (g i j).val)

/-- The observation `(i, j, a)` of copy `c` of genotype `g i j`. -/
def copyAllele (g : I → J → Fin 3) (x : I × J × Fin 2) : I × J × Bool :=
  (x.1, x.2.1, isRef g x.1 x.2.1 x.2.2)

/-- Every SNP is polymorphic in the sample: some individual carries a reference allele and some
individual carries an alternative allele. Without it the M-step frequency is `0` or `1`. -/
def Polymorphic (g : I → J → Fin 3) : Prop := ∀ j, (∃ i, g i j ≠ 0) ∧ ∃ i, g i j ≠ 2

section Data

variable [Fintype I] [Fintype J]

/-- The `2 |I| |J|` allele-copy observations of the genotype matrix `g`, indexed by `Fin`. -/
noncomputable def data (g : I → J → Fin 3) :
    Fin (Fintype.card (I × J × Fin 2)) → I × J × Bool :=
  fun n => copyAllele g ((Fintype.equivFin _).symm n)

/-- A sum over the indexed data is a sum over individuals, SNPs and copies. -/
theorem sum_data (g : I → J → Fin 3) (f : I × J × Bool → ℝ) :
    ∑ n, f (data g n) = ∑ i, ∑ j, ∑ c : Fin 2, f (copyAllele g (i, j, c)) := by
  simp only [data]
  rw [Equiv.sum_comp (Fintype.equivFin _).symm (fun x => f (copyAllele g x)),
    Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => Fintype.sum_prod_type _

/-- The admixture log-likelihood
`ℓ(Q, F) = ∑ i, ∑ j, (g i j * log (qf θ i j) + (2 - g i j) * log (1 - qf θ i j))`. -/
noncomputable def admixtureLogLik (g : I → J → Fin 3) (θ : Params I J K) : ℝ :=
  ∑ i, ∑ j, (((g i j).val : ℝ) * log (qf θ i j) + (2 - ((g i j).val : ℝ)) * log (1 - qf θ i j))

/-- **The EM log-likelihood of the allele copies is the admixture log-likelihood.** -/
theorem logLik_eq_admixtureLogLik (g : I → J → Fin 3) (θ : Params I J K) :
    logLik joint (data g) θ = admixtureLogLik g θ := by
  rw [logLik, sum_data g (fun x => log (marginal joint θ x)), admixtureLogLik]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [copyAllele, marginal_eq, Fin.sum_univ_two, isRef]
  generalize g i j = v
  fin_cases v <;> simp <;> ring

/-! ## The EM theorem -/

/-- **The EM theorem for the admixture model**: a step that does not decrease `Q(· | θ)` does
not decrease the admixture log-likelihood. -/
theorem admixtureLogLik_le_of_emQ_le [Nonempty K] (g : I → J → Fin 3) {θ θ' : Params I J K}
    (h : emQ joint (data g) θ θ ≤ emQ joint (data g) θ' θ) :
    admixtureLogLik g θ ≤ admixtureLogLik g θ' := by
  rw [← logLik_eq_admixtureLogLik, ← logLik_eq_admixtureLogLik]
  exact logLik_le_of_emQ_le (fun θ x k => joint_pos θ x k) (data g) h

/-- **The admixture log-likelihood is monotone along the iterates** of any M-step `M` with
`Q(M θ | θ) ≥ Q(θ | θ)`. -/
theorem admixtureLogLik_iterate_monotone [Nonempty K] (g : I → J → Fin 3)
    {M : Params I J K → Params I J K}
    (hM : ∀ θ, emQ joint (data g) θ θ ≤ emQ joint (data g) (M θ) θ)
    (θ₀ : Params I J K) : Monotone fun t => admixtureLogLik g (M^[t] θ₀) := by
  simp only [← logLik_eq_admixtureLogLik]
  exact logLik_iterate_monotone (fun θ x k => joint_pos θ x k) (data g) hM θ₀

end Data

/-! ## The closed-form M-step -/

variable (g : I → J → Fin 3)

/-- The responsibility `r = P(z = k | copy c of (i, j))` (the E-step). -/
noncomputable def resp (θ : Params I J K) (i : I) (j : J) (c : Fin 2) (k : K) : ℝ :=
  posterior joint θ (copyAllele g (i, j, c)) k

variable {g}

/-- The responsibilities are positive. -/
theorem resp_pos (θ : Params I J K) (i : I) (j : J) (c : Fin 2) (k : K) :
    0 < resp g θ i j c k :=
  div_pos (joint_pos θ _ k) (Finset.sum_pos (fun k _ => joint_pos θ _ k) ⟨k, Finset.mem_univ k⟩)

/-- The responsibilities of a copy sum to one over the populations. -/
theorem sum_resp [Nonempty K] (θ : Params I J K) (i : I) (j : J) (c : Fin 2) :
    ∑ k, resp g θ i j c k = 1 :=
  (isDist_posterior (fun θ x k => joint_pos θ x k) θ _).2

section AncestryUpdate

variable [Fintype J]

variable (g) in
/-- The expected number of allele copies of individual `i` from population `k`. -/
noncomputable def ancCount (θ : Params I J K) (i : I) (k : K) : ℝ :=
  ∑ j, ∑ c, resp g θ i j c k

variable (g) in
/-- The FRAPPE update of the ancestry proportions,
`Q' i k = (∑ j, ∑ c, r) / (2 J)`. -/
noncomputable def mStepQ (θ : Params I J K) (i : I) (k : K) : ℝ :=
  ancCount g θ i k / (2 * Fintype.card J)

/-- The expected ancestry counts of an individual sum to its `2 J` allele copies. -/
theorem sum_ancCount [Nonempty K] (θ : Params I J K) (i : I) :
    ∑ k, ancCount g θ i k = 2 * Fintype.card J := by
  simp only [ancCount]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (γ := K) (s := Finset.univ) (t := Finset.univ), sum_resp]
  simp [mul_comm]

/-- The expected ancestry counts are positive when there is at least one SNP. -/
theorem ancCount_pos [Nonempty J] (θ : Params I J K) (i : I) (k : K) : 0 < ancCount g θ i k :=
  Finset.sum_pos (fun j _ => Finset.sum_pos (fun c _ => resp_pos θ i j c k)
    Finset.univ_nonempty) Finset.univ_nonempty

/-- The updated ancestry proportions are positive. -/
theorem mStep_Q_pos [Nonempty J] (θ : Params I J K) (i : I) (k : K) : 0 < mStepQ g θ i k := by
  have := Fintype.card_pos (α := J)
  exact div_pos (ancCount_pos θ i k) (by positivity)

/-- The updated ancestry proportions of each individual sum to one. -/
theorem mStep_Q_sum [Nonempty J] [Nonempty K] (θ : Params I J K) (i : I) :
    ∑ k, mStepQ g θ i k = 1 := by
  simp only [mStepQ]
  have := Fintype.card_pos (α := J)
  rw [← Finset.sum_div, sum_ancCount, div_self (by positivity)]

end AncestryUpdate

section FrequencyUpdate

variable [Fintype I]

variable (g) in
/-- The expected number of allele copies of SNP `j` from population `k`. -/
noncomputable def popCount (θ : Params I J K) (k : K) (j : J) : ℝ :=
  ∑ i, ∑ c, resp g θ i j c k

variable (g) in
/-- The expected number of reference copies of SNP `j` from population `k`. -/
noncomputable def refCount (θ : Params I J K) (k : K) (j : J) : ℝ :=
  ∑ i, ∑ c, if isRef g i j c then resp g θ i j c k else 0

variable (g) in
/-- The expected number of alternative copies of SNP `j` from population `k`. -/
noncomputable def altCount (θ : Params I J K) (k : K) (j : J) : ℝ :=
  ∑ i, ∑ c, if isRef g i j c then 0 else resp g θ i j c k

variable (g) in
/-- The FRAPPE update of the allele frequencies,
`F' k j = (∑ i, ∑ c reference, r) / (∑ i, ∑ c, r)`. -/
noncomputable def mStepF (θ : Params I J K) (k : K) (j : J) : ℝ :=
  refCount g θ k j / popCount g θ k j

/-- Reference plus alternative expected counts give the population's expected count. -/
theorem refCount_add_altCount (θ : Params I J K) (k : K) (j : J) :
    refCount g θ k j + altCount g θ k j = popCount g θ k j := by
  rw [refCount, altCount, popCount, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun c _ => by split_ifs <;> simp

/-- On polymorphic data the expected reference counts are positive. -/
theorem refCount_pos (hg : Polymorphic g) (θ : Params I J K) (k : K) (j : J) :
    0 < refCount g θ k j := by
  obtain ⟨i, hi⟩ := (hg j).1
  have hc : isRef g i j 0 = true := by
    simp only [isRef, Fin.val_zero, decide_eq_true_eq]
    exact Fin.pos_iff_ne_zero.2 hi
  have hnn : ∀ i' c, 0 ≤ if isRef g i' j c then resp g θ i' j c k else 0 := fun i' c => by
    split_ifs
    exacts [(resp_pos θ i' j c k).le, le_rfl]
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun i' _ => Finset.sum_nonneg
    fun c _ => hnn i' c) (Finset.mem_univ i))
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun c _ => hnn i c) (Finset.mem_univ 0))
  simp only [hc, ↓reduceIte]
  exact resp_pos θ i j 0 k

/-- On polymorphic data the expected alternative counts are positive. -/
theorem altCount_pos (hg : Polymorphic g) (θ : Params I J K) (k : K) (j : J) :
    0 < altCount g θ k j := by
  obtain ⟨i, hi⟩ := (hg j).2
  have hc : isRef g i j 1 = false := by
    simp only [isRef, Fin.val_one, decide_eq_false_iff_not, not_lt]
    have := (g i j).isLt
    have : (g i j).val ≠ 2 := fun h => hi (Fin.ext h)
    omega
  have hnn : ∀ i' c, 0 ≤ if isRef g i' j c then 0 else resp g θ i' j c k := fun i' c => by
    split_ifs
    exacts [le_rfl, (resp_pos θ i' j c k).le]
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun i' _ => Finset.sum_nonneg
    fun c _ => hnn i' c) (Finset.mem_univ i))
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun c _ => hnn i c) (Finset.mem_univ 1))
  simp only [hc, Bool.false_eq_true, ↓reduceIte]
  exact resp_pos θ i j 1 k

/-- On polymorphic data the expected population counts are positive. -/
theorem popCount_pos (hg : Polymorphic g) (θ : Params I J K) (k : K) (j : J) :
    0 < popCount g θ k j := by
  rw [← refCount_add_altCount]
  linarith [refCount_pos hg θ k j, altCount_pos hg θ k j]

/-- On polymorphic data the updated allele frequencies are positive. -/
theorem mStep_F_pos (hg : Polymorphic g) (θ : Params I J K) (k : K) (j : J) :
    0 < mStepF g θ k j :=
  div_pos (refCount_pos hg θ k j) (popCount_pos hg θ k j)

/-- On polymorphic data the updated allele frequencies are below one. -/
theorem mStep_F_lt_one (hg : Polymorphic g) (θ : Params I J K) (k : K) (j : J) :
    mStepF g θ k j < 1 := by
  rw [mStepF, div_lt_one (popCount_pos hg θ k j), ← refCount_add_altCount]
  linarith [altCount_pos hg θ k j]

end FrequencyUpdate

variable [Fintype I] [Fintype J]

variable (g) in
/-- **The FRAPPE EM step** `θ ↦ (Q', F')`, with `Q' = mStepQ` and `F' = mStepF`; it
lies in the strictly positive parameter set when `J` is nonempty and every SNP is
polymorphic. -/
noncomputable def emStep [Nonempty J] [Nonempty K] (hg : Polymorphic g) (θ : Params I J K) :
    Params I J K where
  Q := mStepQ g θ
  F := mStepF g θ
  Q_pos := mStep_Q_pos θ
  Q_sum := mStep_Q_sum θ
  F_pos := mStep_F_pos hg θ
  F_lt_one := mStep_F_lt_one hg θ

/-! ## The M-step maximizes `Q` -/

omit [Fintype I] in
private theorem sum_comm_three (f : J → Fin 2 → K → ℝ) :
    ∑ j, ∑ c, ∑ k, f j c k = ∑ k, ∑ j, ∑ c, f j c k := by
  rw [Finset.sum_comm (f := fun k j => ∑ c, f j c k)]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

private theorem sum_comm_four (f : I → J → Fin 2 → K → ℝ) :
    ∑ i, ∑ j, ∑ c, ∑ k, f i j c k = ∑ k, ∑ j, ∑ i, ∑ c, f i j c k :=
  calc ∑ i, ∑ j, ∑ c, ∑ k, f i j c k = ∑ i, ∑ j, ∑ k, ∑ c, f i j c k :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ j, ∑ c, f i j c k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, ∑ c, f i j c k := Finset.sum_comm
    _ = ∑ k, ∑ j, ∑ i, ∑ c, f i j c k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

variable (g) in
/-- `Q(θ' | θ)` splits into an ancestry term per individual and a two-point term per population
and SNP. -/
theorem emQ_eq (θ' θ : Params I J K) :
    emQ joint (data g) θ' θ = ∑ i, ∑ k, ancCount g θ i k * log (θ'.Q i k) +
      ∑ k, ∑ j, (refCount g θ k j * log (θ'.F k j) +
        altCount g θ k j * log (1 - θ'.F k j)) := by
  have hlog : ∀ i j c k, log (joint θ' (copyAllele g (i, j, c)) k) = log (θ'.Q i k) +
      (if isRef g i j c then log (θ'.F k j) else log (1 - θ'.F k j)) := by
    intro i j c k
    have hc : copyAllele g (i, j, c) = (i, j, isRef g i j c) := rfl
    rw [hc]
    cases isRef g i j c
    · simp only [joint, Bool.false_eq_true, ↓reduceIte]
      rw [log_mul (θ'.Q_pos i k).ne' (by linarith [θ'.F_lt_one k j])]
    · simp only [joint, ↓reduceIte]
      rw [log_mul (θ'.Q_pos i k).ne' (θ'.F_pos k j).ne']
  rw [emQ, sum_data g (fun x => ∑ k, posterior joint θ x k * log (joint θ' x k))]
  simp only [hlog, mul_add, Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ancCount, Finset.sum_mul, resp]
    exact sum_comm_three _
  · have hterm : ∀ i j c k, posterior joint θ (copyAllele g (i, j, c)) k *
        (if isRef g i j c then log (θ'.F k j) else log (1 - θ'.F k j)) =
        (if isRef g i j c then resp g θ i j c k else 0) * log (θ'.F k j) +
        (if isRef g i j c then 0 else resp g θ i j c k) * log (1 - θ'.F k j) := by
      intro i j c k
      simp only [resp]
      split_ifs <;> ring
    simp only [hterm]
    rw [sum_comm_four]
    simp only [Finset.sum_add_distrib, refCount, altCount, Finset.sum_mul]

variable (g) in
/-- **The FRAPPE update maximizes `Q(· | θ)`**: no parameter `θ'` in the strictly
positive parameter set has a larger `Q(θ' | θ)` than the closed-form update `emStep g hg θ`. -/
theorem emQ_le_emStep [Nonempty J] [Nonempty K] (hg : Polymorphic g) (θ' θ : Params I J K) :
    emQ joint (data g) θ' θ ≤ emQ joint (data g) (emStep g hg θ) θ := by
  rw [emQ_eq, emQ_eq]
  have hJ : (0 : ℝ) < 2 * Fintype.card J := by
    have := Fintype.card_pos (α := J)
    positivity
  refine add_le_add (Finset.sum_le_sum fun i _ => ?_)
    (Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun j _ => ?_)
  · -- the ancestry term of individual `i`: Gibbs' inequality over `K`
    have h := sum_mul_log_le_sum_mul_log_div (fun k => (ancCount_pos (g := g) θ i k).le)
      (by rw [sum_ancCount]; exact hJ) (θ'.Q_pos i) (θ'.Q_sum i)
    rw [sum_ancCount] at h
    exact h
  · -- one population and SNP: the two-point case over `Bool`
    have hm := popCount_pos hg θ k j
    have h := sum_mul_log_le_sum_mul_log_div (Z := Bool)
      (c := fun b => if b then refCount g θ k j else altCount g θ k j)
      (w := fun b => if b then θ'.F k j else 1 - θ'.F k j)
      (fun b => by cases b <;> simp [(refCount_pos hg θ k j).le, (altCount_pos hg θ k j).le])
      (by simp [refCount_add_altCount, hm])
      (fun b => by cases b <;> simp [θ'.F_pos k j, θ'.F_lt_one k j])
      (by simp)
    simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true] at h
    rw [refCount_add_altCount] at h
    have e1 : (emStep g hg θ).F k j = refCount g θ k j / popCount g θ k j := rfl
    have e2 : 1 - (emStep g hg θ).F k j = altCount g θ k j / popCount g θ k j := by
      rw [e1, eq_div_iff hm.ne', sub_mul, one_mul, div_mul_cancel₀ _ hm.ne',
        ← refCount_add_altCount]
      ring
    rw [e2, e1]
    linarith

variable (g) in
/-- **Each FRAPPE EM step does not decrease the admixture log-likelihood.** -/
theorem admixtureLogLik_le_emStep [Nonempty J] [Nonempty K] (hg : Polymorphic g)
    (θ : Params I J K) : admixtureLogLik g θ ≤ admixtureLogLik g (emStep g hg θ) :=
  admixtureLogLik_le_of_emQ_le g (emQ_le_emStep g hg θ θ)

variable (g) in
/-- **The admixture log-likelihood is monotone along the FRAPPE EM iterates.** -/
theorem admixtureLogLik_iterate_emStep_monotone [Nonempty J] [Nonempty K] (hg : Polymorphic g)
    (θ₀ : Params I J K) : Monotone fun t => admixtureLogLik g ((emStep g hg)^[t] θ₀) :=
  admixtureLogLik_iterate_monotone g (fun θ => emQ_le_emStep g hg θ θ) θ₀

end Cslib.Bioinformatics.PopulationStructure.AdmixtureEM
