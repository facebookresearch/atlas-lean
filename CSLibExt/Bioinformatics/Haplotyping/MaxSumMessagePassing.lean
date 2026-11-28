/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sequence.HiddenMarkov
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Ring

/-!
# Probabilistic haplotyping by max-sum message passing

Kuleshov's probabilistic model of single-individual haplotyping (V. Kuleshov, *Probabilistic
single-individual haplotyping*, Bioinformatics 30 (2014) i379–i385, Sections 4.1–4.3 and 5.1).
`n` reads cover `m` heterozygous sites. A phasing matrix `M ∈ {0, 1, -}^{n × m}` gives the
allele each read shows at each site it covers, and an error matrix `Q ∈ [0, 1)^{n × m}` the
probability of a sequencing error there. The hidden variables are a haplotype `h ∈ {0, 1}^m`,
the other haplotype being its complement, and the origins `r ∈ {0, 1}^n` of the reads. The
likelihood `P(o = M | r, h)` has one factor for each covered entry; the clusters of the reads
spanning each site form a junction tree along the sites, and max-sum message passing along it
computes the maximum log-likelihood exactly.

Sites are numbered from `0` here, so site `j` is the source's site `j + 1`, and alleles and
origins `0`, `1` are `false`, `true`. An assignment of origins to a set of reads is the subset
of those reads with origin `1`. Log-likelihoods are extended reals with `log 0 = ⊥`, so error
probabilities `0` are allowed.

Main results:

* `ReadData.exists_scope_subset_cluster`, `ReadData.mem_cluster_of_le`: the clusters form a
  junction tree (Lemma 1 of the source).
* `ReadData.sup_logLikelihood_eq_message`: the max-sum messages (Equation (1)) compute the
  maximum log-likelihood. The proof runs Viterbi
  (`Cslib.MachineLearning.Sequence.HiddenMarkov.sup'_viterbi_eq`) on the chain whose state at
  site `j` is `h_j` together with the origins of the reads spanning `j`.
* `ReadData.logLikelihood_backtrack`: backtracking through stored argmaxes recovers a maximum
  likelihood haplotype and read origins.
* `ReadData.maxSumTimed_ret`, `ReadData.maxSumTimed_time_le`: the tabulated algorithm returns
  that maximum after `∑_j |R_j| 2^(|R_j| + 1) ≤ m κ 2^(κ + 1)` steps, `κ` the coverage.
* `ReadData.likelihood_not`, `ReadData.sup_log_jointProb`: the likelihood is invariant under
  complementing the haplotype and the origins, and with the priors the maximum of the joint law is
  the maximum likelihood times the prior mass `2^(-(n + m - 1))`.
* `ReadData.logLikelihood_eq_of_err_eq`, `ReadData.isMaxOn_iff_isMEC`: with a constant error
  probability `q ∈ (0, 1/2)`, the log-likelihood is a constant minus `log ((1 - q) / q)` times the
  number of allele flips, so maximum likelihood is minimum error correction (Section 5.1).
* `ReadData.maxSum_haplotyping`: all of these together.

## Cost model

`maxSumTimed` charges one unit for each term `log P(o_ij | r_i, h_j)` that a site score adds.
Maxima, the addition of the previous message, and the construction and lookup of message tables
are free: each term is followed by a constant amount of such work. Message `j + 1` takes a value
for each of the `2^|R_j ∩ R_{j+1}|` assignments of the reads spanning `j` and `j + 1`,
maximising over the `2` alleles `h_j` and the `2^|R_j \ R_{j+1}|` assignments of the other reads
spanning `j`, each a sum of `|R_j|` terms: `|R_j| 2^(|R_j| + 1)` units in all.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.Haplotyping

open Finset
open scoped ENNReal

variable {n m : ℕ}

/-- **Error model of an observed allele.** For a per-base error probability $q$, the
probability $P(o = a \mid r, b)$ that a read with origin $r \in \{0, 1\}$ shows the allele
$a \in \{0, 1\}$ at a site where the haplotype $h$ carries $b$. The read comes from $h$ if
$r = 0$ and from its complement $\bar h$ if $r = 1$, so it carries $b(r) = b \oplus r$
($b$ if $r = 0$, $1 - b$ if $r = 1$); it shows that allele with probability $1 - q$ and the other
one with probability $q$. Alleles and origins $0$ and $1$ are `false` and `true`. -/
def alleleProb (q : ℝ) (a r b : Bool) : ℝ := if a = xor b r then 1 - q else q

theorem alleleProb_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (a r b : Bool) :
    0 ≤ alleleProb q a r b := by
  unfold alleleProb
  split_ifs <;> linarith

theorem alleleProb_false_add_true (q : ℝ) (r b : Bool) :
    alleleProb q false r b + alleleProb q true r b = 1 := by
  cases r <;> cases b <;> simp [alleleProb]

/-- **Variables of the haplotyping model.** For $n$ reads and $m$ sites: the haplotype
alleles $h_j$, the read origins $r_i$ and the observed alleles $o_{ij}$. -/
inductive Var (n m : ℕ) where
  /-- The haplotype allele `h_j` at site `j`. -/
  | hap (j : Fin m)
  /-- The origin `r_i` of read `i`. -/
  | origin (i : Fin n)
  /-- The observed allele `o_ij` of read `i` at site `j`. -/
  | obs (i : Fin n) (j : Fin m)
  deriving DecidableEq

/-- **Factors of the haplotyping model.** For $n$ reads and $m$ sites: an observation factor
$P(o_{ij} \mid r_i, h_j)$ for each read $i$ and site $j$ (a factor of the joint law exactly when
read $i$ covers site $j$, `ReadData.IsFactor`), the prior $P(r_i)$ of each read origin and the
prior $P(h_j)$ of each haplotype allele. -/
inductive Factor (n m : ℕ) where
  /-- The observation factor `P(o_ij | r_i, h_j)`. -/
  | obs (i : Fin n) (j : Fin m)
  /-- The prior `P(r_i)` of a read origin. -/
  | originPrior (i : Fin n)
  /-- The prior `P(h_j)` of a haplotype allele. -/
  | hapPrior (j : Fin m)

/-- **Scope of a factor.** The variables a factor of the haplotyping model depends on:
$\{o_{ij}, r_i, h_j\}$ for $P(o_{ij} \mid r_i, h_j)$, $\{r_i\}$ for $P(r_i)$ and $\{h_j\}$ for
$P(h_j)$. -/
def Factor.scope : Factor n m → Set (Var n m)
  | .obs i j => {.obs i j, .origin i, .hap j}
  | .originPrior i => {.origin i}
  | .hapPrior j => {.hap j}

/-- **Prior of a haplotype allele.** The prior $P(h_j = b)$ at a site $j$, with sites
numbered from $0$: $P(h_0 = 0) = 1$ at the first site, which removes the symmetry between a
haplotype and its complement, and the uniform prior $1/2$ at every other site. -/
noncomputable def hapPrior (j : Fin m) (b : Bool) : ℝ :=
  if (j : ℕ) = 0 then (if b then 0 else 1) else 1 / 2

/-- **Prior of a read origin.** The uniform prior $P(r_i = b) = 1/2$ of the origin of a
read. -/
noncomputable def originPrior : Bool → ℝ := fun _ => 1 / 2

theorem hapPrior_false_add_true (j : Fin m) : hapPrior j false + hapPrior j true = 1 := by
  by_cases hj : (j : ℕ) = 0 <;> norm_num [hapPrior, hj]

theorem originPrior_false_add_true : originPrior false + originPrior true = 1 := by
  norm_num [originPrior]

/-- **Read data for single-individual haplotyping.** An instance with $n$ reads and $m$
heterozygous sites, numbered from $0$: a phasing matrix $M \in \{0, 1, -\}^{n \times m}$, where
$M_{ij}$ is the allele that read $i$ shows at site $j$, or $-$ if read $i$ does not cover $j$,
and an error matrix $Q \in [0, 1)^{n \times m}$ of per-base error probabilities. Every read
covers at least one site, so that its first and last covered sites exist. -/
structure ReadData (n m : ℕ) where
  /-- The phasing matrix: `allele i j = some a` when read `i` shows the allele `a` at site `j`,
  and `none` (`-`) when it does not cover `j`. -/
  allele : Fin n → Fin m → Option Bool
  /-- The error matrix: the probability `err i j` of a sequencing error of read `i` at
  site `j`. -/
  err : Fin n → Fin m → ℝ
  /-- Error probabilities are nonnegative. -/
  err_nonneg : ∀ i j, 0 ≤ err i j
  /-- Error probabilities are below one. -/
  err_lt_one : ∀ i j, err i j < 1
  /-- Every read covers a site. -/
  covers : ∀ i, ∃ j, allele i j ≠ none

namespace ReadData

variable (D : ReadData n m)

/-- **Sites covered by a read.** $\mathrm{Po}(i) = \{j : M_{ij} \ne -\}$, the sites at which
read $i$ shows an allele. -/
def covered (i : Fin n) : Finset (Fin m) := {j | D.allele i j ≠ none}

theorem mem_covered {i : Fin n} {j : Fin m} : j ∈ D.covered i ↔ D.allele i j ≠ none := by
  simp [covered]

theorem covered_nonempty (i : Fin n) : (D.covered i).Nonempty := by
  obtain ⟨j, hj⟩ := D.covers i
  exact ⟨j, D.mem_covered.2 hj⟩

/-- **Reads spanning a site.** $R_j = \{i : \min \mathrm{Po}(i) \le j \le \max \mathrm{Po}(i)\}$,
the reads whose span, from the first to the last site they cover, contains the site
$j \in \mathbb{N}$. It is empty for $j \ge m$. -/
def spanning (j : ℕ) : Finset (Fin n) :=
  {i | ((D.covered i).min' (D.covered_nonempty i) : ℕ) ≤ j ∧
    j ≤ (D.covered i).max' (D.covered_nonempty i)}

/-- **Observation factor.** $P(o_{ij} = M_{ij} \mid r_i = r, h_j = b)$, the probability
that read $i$ shows its observed allele at site $j$: $1 - Q_{ij}$ if $M_{ij} = b \oplus r$ and
$Q_{ij}$ otherwise (`alleleProb`), and $1$, no factor, where $M_{ij} = -$. -/
def obsProb (i : Fin n) (j : Fin m) (r b : Bool) : ℝ :=
  match D.allele i j with
  | none => 1
  | some a => alleleProb (D.err i j) a r b

/-- **Likelihood.** For a haplotype $h \in \{0, 1\}^m$ and read origins $r \in \{0, 1\}^n$,
$P(o = M \mid r, h) = \prod_{i} \prod_{j \in \mathrm{Po}(i)} P(o_{ij} = M_{ij} \mid r_i, h_j)$. -/
def likelihood (h : Fin m → Bool) (r : Fin n → Bool) : ℝ :=
  ∏ i, ∏ j ∈ D.covered i, D.obsProb i j (r i) (h j)

/-- **Log-likelihood.** $\log P(o = M \mid r, h)$, as an extended real with $\log 0 = \bot$. -/
noncomputable def logLikelihood (h : Fin m → Bool) (r : Fin n → Bool) : EReal :=
  ENNReal.log (ENNReal.ofReal (D.likelihood h r))

/-- **Logarithm of an observation factor.** $\log P(o_{ij} = M_{ij} \mid r_i = r, h_j = b)$
for a site $j \in \mathbb{N}$, as an extended real with $\log 0 = \bot$; it is $0$, no factor,
where read $i$ shows no allele at $j$, for $j \ge m$ in particular. -/
noncomputable def logObs (i : Fin n) (j : ℕ) (r b : Bool) : EReal :=
  if hj : j < m then ENNReal.log (ENNReal.ofReal (D.obsProb i ⟨j, hj⟩ r b)) else 0

/-- **Site score.** $\sum_{i \in R_j} \log P(o_{ij} \mid r_i, h_j = b)$ for the origins
$r_i = 1$ for $i \in T$ and $r_i = 0$ otherwise, a read that spans $j$ without covering it
contributing $0$. -/
noncomputable def siteScore (j : ℕ) (T : Finset (Fin n)) (b : Bool) : EReal :=
  ∑ i ∈ D.spanning j, D.logObs i j (decide (i ∈ T)) b

/-- **Max-sum messages.** $M_0 \equiv 0$ and, for each site $j$,

$$M_{j+1}(\sigma) = \max_{b \in \{0, 1\}} \max_{U \subseteq R_j \setminus R_{j+1}}
\Bigl(\sum_{i \in R_j} \log P(o_{ij} \mid r_i, h_j = b)
+ M_j\bigl((\sigma \cup U) \cap R_{j-1}\bigr)\Bigr),$$

the origins being $r_i = 1$ for $i \in \sigma \cup U$ and $r_i = 0$ for the other reads of
$R_j$. Here an assignment of origins to a set of reads is the subset of those with origin $1$:
$\sigma \subseteq R_j \cap R_{j+1}$ assigns the reads spanning $j$ and $j + 1$, $U$ the reads
spanning $j$ but not $j + 1$, and $(\sigma \cup U) \cap R_{j-1}$ is the restriction of
$\sigma \cup U$ to the reads spanning $j - 1$ and $j$, the argument of $M_j$ (for $j = 0$ it
is not used). With the sites numbered from $1$, as in the source, $M_j$ is the message from
cluster $j$ to cluster $j + 1$. Since no read spans site $m$, $M_m(\emptyset)$ maximizes over
$h_{m-1}$ and all origins of $R_{m-1}$, the source's final expression. -/
noncomputable def message : ℕ → Finset (Fin n) → EReal
  | 0, _ => 0
  | j + 1, σ => ((univ : Finset Bool) ×ˢ (D.spanning j \ D.spanning (j + 1)).powerset).sup
      fun p => D.siteScore j (σ ∪ p.2) p.1 + message j ((σ ∪ p.2) ∩ D.spanning (j - 1))

/-! ### Basic facts -/

theorem mem_spanning {i : Fin n} {j : ℕ} :
    i ∈ D.spanning j ↔ ((D.covered i).min' (D.covered_nonempty i) : ℕ) ≤ j ∧
      j ≤ (D.covered i).max' (D.covered_nonempty i) := by
  simp [spanning]

theorem mem_spanning_of_mem_covered {i : Fin n} {j : Fin m} (hj : j ∈ D.covered i) :
    i ∈ D.spanning j :=
  D.mem_spanning.2 ⟨Fin.le_iff_val_le_val.1 (min'_le _ _ hj),
    Fin.le_iff_val_le_val.1 (le_max' _ _ hj)⟩

theorem spanning_eq_empty {j : ℕ} (hj : m ≤ j) : D.spanning j = ∅ := by
  ext i
  simp only [mem_spanning, Finset.notMem_empty, iff_false, not_and, not_le]
  intro _
  exact lt_of_lt_of_le ((D.covered i).max' (D.covered_nonempty i)).isLt hj

theorem mem_spanning_of_le {i : Fin n} {x y z : ℕ} (hx : i ∈ D.spanning x)
    (hy : i ∈ D.spanning y) (hxz : x ≤ z) (hzy : z ≤ y) : i ∈ D.spanning z :=
  D.mem_spanning.2 ⟨(D.mem_spanning.1 hx).1.trans hxz, hzy.trans (D.mem_spanning.1 hy).2⟩

theorem obsProb_of_notMem {i : Fin n} {j : Fin m} (hj : j ∉ D.covered i) (r b : Bool) :
    D.obsProb i j r b = 1 := by
  rw [mem_covered, not_not] at hj
  simp [obsProb, hj]

theorem obsProb_nonneg (i : Fin n) (j : Fin m) (r b : Bool) : 0 ≤ D.obsProb i j r b := by
  unfold obsProb
  split
  · exact zero_le_one
  · exact alleleProb_nonneg (D.err_nonneg i j) (D.err_lt_one i j).le _ _ _

theorem likelihood_nonneg (h : Fin m → Bool) (r : Fin n → Bool) : 0 ≤ D.likelihood h r :=
  prod_nonneg fun i _ => prod_nonneg fun j _ => D.obsProb_nonneg i j _ _

/-! ### Max-sum as Viterbi on the chain of spanning-read origins -/

open Cslib.MachineLearning.Sequence.HiddenMarkov

private theorem log_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    ENNReal.log (∏ i ∈ s, f i) = ∑ i ∈ s, ENNReal.log (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [prod_insert ha, sum_insert ha, ENNReal.log_mul_add, ih]

-- The weight of an observation, at a site given as a natural number.
private noncomputable def obsWeight (i : Fin n) (j : ℕ) (r b : Bool) : ℝ≥0∞ :=
  if hj : j < m then ENNReal.ofReal (D.obsProb i ⟨j, hj⟩ r b) else 1

-- The weight of the observations of the spanning reads at a site.
private noncomputable def siteProb (j : ℕ) (T : Finset (Fin n)) (b : Bool) : ℝ≥0∞ :=
  ∏ i ∈ D.spanning j, D.obsWeight i j (decide (i ∈ T)) b

private theorem log_siteProb (j : ℕ) (T : Finset (Fin n)) (b : Bool) :
    ENNReal.log (D.siteProb j T b) = D.siteScore j T b := by
  rw [siteProb, log_prod, siteScore]
  refine sum_congr rfl fun i _ => ?_
  unfold obsWeight logObs
  split_ifs <;> simp

-- The site weights of origins that agree with `r` multiply to the likelihood.
private theorem prod_siteProb (h : Fin m → Bool) (r : Fin n → Bool) (ρ : Fin m → Finset (Fin n))
    (hρ : ∀ (t : Fin m) (i : Fin n), i ∈ D.spanning t → (i ∈ ρ t ↔ r i = true)) :
    ∏ t : Fin m, D.siteProb t (ρ t) (h t) = ENNReal.ofReal (D.likelihood h r) := by
  have step : ∀ t : Fin m, D.siteProb t (ρ t) (h t) =
      ∏ i, ENNReal.ofReal (D.obsProb i t (r i) (h t)) := by
    intro t
    rw [siteProb, ← prod_subset (subset_univ (D.spanning t))
      (f := fun i => ENNReal.ofReal (D.obsProb i t (r i) (h t))) (fun i _ hi => ?_)]
    · refine prod_congr rfl fun i hi => ?_
      have hd : decide (i ∈ ρ t) = r i := by
        rw [Bool.eq_iff_iff, decide_eq_true_iff]
        exact hρ t i hi
      simp [obsWeight, hd]
    · rw [D.obsProb_of_notMem (fun hc => hi (D.mem_spanning_of_mem_covered hc)),
        ENNReal.ofReal_one]
  rw [Fintype.prod_congr _ _ step, prod_comm, likelihood,
    ENNReal.ofReal_prod_of_nonneg fun i _ => prod_nonneg fun j _ => D.obsProb_nonneg i j _ _]
  refine prod_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_prod_of_nonneg fun j _ => D.obsProb_nonneg i j _ _]
  refine (prod_subset (subset_univ _) fun j _ hj => ?_).symm
  rw [D.obsProb_of_notMem hj, ENNReal.ofReal_one]

-- Origins at consecutive sites that agree on the reads spanning both agree along every read.
private theorem mem_iff_mem_min' (ρ : ℕ → Finset (Fin n))
    (hcons : ∀ t, t + 1 < m → ρ t ∩ D.spanning (t + 1) = ρ (t + 1) ∩ D.spanning t)
    {i : Fin n} {t : ℕ} (hi : i ∈ D.spanning t) :
    i ∈ ρ t ↔ i ∈ ρ ((D.covered i).min' (D.covered_nonempty i)).val := by
  set a : ℕ := ((D.covered i).min' (D.covered_nonempty i)).val
  set b : ℕ := ((D.covered i).max' (D.covered_nonempty i)).val
  have hb : b < m := ((D.covered i).max' (D.covered_nonempty i)).isLt
  obtain ⟨hat, htb⟩ := D.mem_spanning.1 hi
  induction t, hat using Nat.le_induction with
  | base => exact Iff.rfl
  | succ u hau ih =>
      have hu : i ∈ D.spanning u := D.mem_spanning.2 ⟨hau, by omega⟩
      have h := congrArg (i ∈ ·) (hcons u (by omega))
      simp only [mem_inter, hi, hu, and_true] at h
      rw [← h]
      exact ih hu (by omega)

-- The chain whose state at site `t` is `t`, the allele `h_t` and the origins of the reads
-- spanning `t` (the subset of them with origin `1`).
private noncomputable def chain : HMM (Fin m × Bool × Finset (Fin n)) ℕ ℝ≥0∞ where
  init s := if (s.1 : ℕ) = 0 then 1 else 0
  trans s s' :=
    if (s'.1 : ℕ) = s.1 + 1 ∧ s.2.2 ∩ D.spanning s'.1 = s'.2.2 ∩ D.spanning s.1 then 1 else 0
  emit s t := if (s.1 : ℕ) = t ∧ s.2.2 ⊆ D.spanning s.1 then D.siteProb s.1 s.2.2 s.2.1 else 0

private theorem chain_nonneg : D.chain.Nonneg :=
  ⟨fun _ => zero_le, fun _ _ => zero_le, fun _ _ => zero_le⟩

private theorem viterbi_eq_zero [NeZero m] (t : ℕ) (s : Fin m × Bool × Finset (Fin n))
    (hs : ¬((s.1 : ℕ) = t ∧ s.2.2 ⊆ D.spanning s.1)) : viterbi D.chain id t s = 0 := by
  cases t with
  | zero =>
      simp only [viterbi, chain, id]
      rw [ite_eq_right hs, mul_zero]
  | succ t =>
      simp only [viterbi, chain, id]
      rw [ite_eq_right hs, mul_zero]

private theorem log_sup'_viterbi_of [NeZero m] {t : ℕ} (ht : t < m)
    (IH : ∀ (b : Bool) (ρ : Finset (Fin n)), ρ ⊆ D.spanning t →
      ENNReal.log (viterbi D.chain id t (⟨t, ht⟩, b, ρ)) =
        D.siteScore t ρ b + D.message t (ρ ∩ D.spanning (t - 1)))
    (σ : Finset (Fin n)) (hσ : σ ⊆ D.spanning t ∩ D.spanning (t + 1)) :
    ENNReal.log (univ.sup' univ_nonempty fun s =>
      if s.2.2 ∩ D.spanning (t + 1) = σ then viterbi D.chain id t s else 0) =
        D.message (t + 1) σ := by
  rw [apply_sup'_eq_sup'_comp _ _ ENNReal.log_monotone.map_sup, message]
  apply le_antisymm
  · refine sup'_le _ _ fun s _ => ?_
    obtain ⟨u, b, ρ⟩ := s
    simp only [Function.comp_apply]
    split_ifs with hρ
    · by_cases hs : (u : ℕ) = t ∧ ρ ⊆ D.spanning u
      · obtain ⟨hu, hsub⟩ := hs
        obtain rfl : u = ⟨t, ht⟩ := Fin.ext hu
        rw [IH b ρ hsub]
        refine le_trans (le_of_eq ?_) (le_sup (f := fun p : Bool × Finset (Fin n) =>
          D.siteScore t (σ ∪ p.2) p.1 + D.message t ((σ ∪ p.2) ∩ D.spanning (t - 1)))
          (b := (b, ρ \ D.spanning (t + 1))) ?_)
        · have : σ ∪ (ρ \ D.spanning (t + 1)) = ρ := by
            rw [← hρ, union_comm, sdiff_union_inter]
          simp only [this]
        · simp only [mem_product, mem_univ, mem_powerset, true_and]
          exact sdiff_subset_sdiff hsub le_rfl
      · rw [D.viterbi_eq_zero t _ hs]
        simp
    · simp
  · refine Finset.sup_le fun p hp => ?_
    obtain ⟨b, U⟩ := p
    simp only [mem_product, mem_univ, mem_powerset, true_and] at hp
    have hsub : σ ∪ U ⊆ D.spanning t :=
      union_subset (hσ.trans inter_subset_left) (hp.trans sdiff_subset)
    have hcap : (σ ∪ U) ∩ D.spanning (t + 1) = σ := by
      rw [union_inter_distrib_right, inter_eq_left.2 (hσ.trans inter_subset_right)]
      have : U ∩ D.spanning (t + 1) = ∅ := by
        rw [← disjoint_iff_inter_eq_empty]
        exact disjoint_of_subset_left hp disjoint_sdiff_self_left
      rw [this, union_empty]
    refine le_trans ?_ (le_sup' _ (mem_univ (⟨t, ht⟩, b, σ ∪ U)))
    simp only [Function.comp_apply, ite_eq_left hcap, IH b (σ ∪ U) hsub, le_refl]

private theorem log_viterbi [NeZero m] : ∀ (t : ℕ) (ht : t < m) (b : Bool) (ρ : Finset (Fin n)),
    ρ ⊆ D.spanning t → ENNReal.log (viterbi D.chain id t (⟨t, ht⟩, b, ρ)) =
      D.siteScore t ρ b + D.message t (ρ ∩ D.spanning (t - 1))
  | 0, ht, b, ρ, hρ => by
      simp [viterbi, chain, hρ, message, log_siteProb]
  | t + 1, ht, b, ρ, hρ => by
      have key : (fun s => viterbi D.chain id t s * D.chain.trans s (⟨t + 1, ht⟩, b, ρ)) =
          fun s => if s.2.2 ∩ D.spanning (t + 1) = ρ ∩ D.spanning t then
            viterbi D.chain id t s else 0 := by
        funext s
        obtain ⟨u, b', ρ'⟩ := s
        by_cases hu : (u : ℕ) = t
        · simp [chain, hu]
        · rw [D.viterbi_eq_zero t _ (fun h => hu h.1)]
          simp
      rw [viterbi, key, ENNReal.log_mul_add,
        D.log_sup'_viterbi_of (by omega) (log_viterbi t (by omega)) _
          (subset_inter inter_subset_right (inter_subset_left.trans hρ))]
      simp [chain, hρ, log_siteProb, add_comm]

private theorem sup'_pathProb (k : ℕ) (D : ReadData n (k + 1)) :
    (univ : Finset (Fin (k + 1) → Fin (k + 1) × Bool × Finset (Fin n))).sup' univ_nonempty
        (pathProb D.chain id k) =
      (univ : Finset ((Fin (k + 1) → Bool) × (Fin n → Bool))).sup' univ_nonempty
        (fun p => ENNReal.ofReal (D.likelihood p.1 p.2)) := by
  apply le_antisymm
  · refine sup'_le _ _ fun z _ => ?_
    rw [pathProb_eq_prod]
    by_cases hC : ∀ t : Fin (k + 1), (z t).1 = t ∧ (z t).2.2 ⊆ D.spanning (z t).1
    · by_cases hC' : ∀ t : Fin k,
          (z t.castSucc).2.2 ∩ D.spanning (t + 1) = (z t.succ).2.2 ∩ D.spanning t
      · set ρ : ℕ → Finset (Fin n) := fun t => if ht : t < k + 1 then (z ⟨t, ht⟩).2.2 else ∅
        have hcons : ∀ t, t + 1 < k + 1 →
            ρ t ∩ D.spanning (t + 1) = ρ (t + 1) ∩ D.spanning t := by
          intro t ht
          have := hC' ⟨t, by omega⟩
          simp only [ρ, dite_eq_left (show t < k + 1 by omega), dite_eq_left ht]
          simpa [Fin.castSucc, Fin.succ] using this
        let r : Fin n → Bool :=
          fun i => decide (i ∈ ρ ((D.covered i).min' (D.covered_nonempty i)).val)
        have hinit : D.chain.init (z 0) = 1 := by
          simp [chain, (hC 0).1]
        have htrans : ∀ t : Fin k, D.chain.trans (z t.castSucc) (z t.succ) = 1 := by
          intro t
          have h1 := (hC t.castSucc).1
          have h2 := (hC t.succ).1
          simp only [chain, h1, h2, Fin.val_succ, Fin.val_castSucc, true_and]
          rw [ite_eq_left (hC' t)]
        have hemit : ∀ t : Fin (k + 1), D.chain.emit (z t) (id t) =
            D.siteProb t (z t).2.2 (z t).2.1 := by
          intro t
          have h2 := (hC t).2
          rw [(hC t).1] at h2
          simp only [chain, (hC t).1, id, true_and]
          exact ite_eq_left h2
        rw [hinit, Fintype.prod_congr _ _ htrans, Fintype.prod_congr _ _ hemit, prod_const_one,
          one_mul, one_mul]
        refine le_trans (le_of_eq ?_) (le_sup' _ (mem_univ (fun t => (z t).2.1, r)))
        refine D.prod_siteProb _ r (fun t => (z t).2.2) fun t i hi => ?_
        have := D.mem_iff_mem_min' ρ hcons hi
        simp only [ρ, dite_eq_left t.isLt] at this
        simp only [r, decide_eq_true_iff]
        exact this
      · obtain ⟨t, ht⟩ := not_forall.1 hC'
        rw [prod_eq_zero (mem_univ t), mul_zero, zero_mul]
        · exact zero_le
        · simp only [chain]
          rw [ite_eq_right]
          rintro ⟨-, h⟩
          rw [(hC t.castSucc).1, (hC t.succ).1] at h
          exact ht (by simpa [Fin.castSucc, Fin.succ] using h)
    · obtain ⟨t, ht⟩ := not_forall.1 hC
      rw [prod_eq_zero (mem_univ t), mul_zero]
      · exact zero_le
      · simp only [chain, id]
        rw [ite_eq_right]
        rintro ⟨h1, h2⟩
        exact ht ⟨Fin.ext h1, h2⟩
  · refine sup'_le _ _ fun p _ => ?_
    obtain ⟨h, r⟩ := p
    let z : Fin (k + 1) → Fin (k + 1) × Bool × Finset (Fin n) :=
      fun t => (t, h t, (D.spanning t).filter fun i => r i = true)
    refine le_trans (le_of_eq ?_) (le_sup' _ (mem_univ z))
    rw [pathProb_eq_prod]
    have hinit : D.chain.init (z 0) = 1 := by simp [chain, z]
    have htrans : ∀ t : Fin k, D.chain.trans (z t.castSucc) (z t.succ) = 1 := by
      intro t
      simp only [chain, z, Fin.val_succ, Fin.val_castSucc, true_and]
      rw [ite_eq_left]
      ext i
      simp only [mem_inter, mem_filter]
      tauto
    have hemit : ∀ t : Fin (k + 1), D.chain.emit (z t) (id t) =
        D.siteProb t ((D.spanning t).filter fun i => r i = true) (h t) := by
      intro t
      simp [chain, z]
    rw [hinit, Fintype.prod_congr _ _ htrans, Fintype.prod_congr _ _ hemit, prod_const_one,
      one_mul, one_mul]
    exact (D.prod_siteProb h r _ fun t i hi => by simp [hi]).symm

theorem sup_logLikelihood_eq_message :
    (univ : Finset ((Fin m → Bool) × (Fin n → Bool))).sup
      (fun p => D.logLikelihood p.1 p.2) = D.message m ∅ := by
  obtain _ | k := m
  · have : ∀ p : (Fin 0 → Bool) × (Fin n → Bool), D.logLikelihood p.1 p.2 = 0 := by
      intro p
      simp [logLikelihood, likelihood, covered]
    simp only [this, message]
    exact sup_const univ_nonempty 0
  · rw [← sup'_eq_sup univ_nonempty]
    have hlog : (fun p : (Fin (k + 1) → Bool) × (Fin n → Bool) => D.logLikelihood p.1 p.2) =
        ENNReal.log ∘ fun p => ENNReal.ofReal (D.likelihood p.1 p.2) := rfl
    rw [hlog, ← apply_sup'_eq_sup'_comp _ _ ENNReal.log_monotone.map_sup, ← sup'_pathProb,
      ← sup'_viterbi_eq id D.chain_nonneg]
    have hfun : viterbi D.chain id k = fun s =>
        if s.2.2 ∩ D.spanning (k + 1) = ∅ then viterbi D.chain id k s else 0 := by
      funext s
      rw [D.spanning_eq_empty le_rfl, inter_empty, ite_eq_left rfl]
    rw [hfun]
    exact D.log_sup'_viterbi_of (lt_add_one k) (D.log_viterbi k (lt_add_one k)) ∅
      (empty_subset _)

/-! ### Backtracking through stored argmaxes -/

/-- **Stored argmaxes of the max-sum messages.** For each site $j < m$ and each assignment
$\sigma \subseteq R_j \cap R_{j+1}$, an argument of the message $M_{j+1}$, an allele $b$ for
$h_j$ and origins $U \subseteq R_j \setminus R_{j+1}$ of the reads spanning $j$ but not $j + 1$
at which the maximum defining $M_{j+1}(\sigma)$ is attained. Entries outside these arguments
are not constrained. -/
structure ArgmaxTable (D : ReadData n m) where
  /-- The stored allele `h_j` and origins `U` for the argument `σ` of `M_{j+1}`. -/
  pick : ℕ → Finset (Fin n) → Bool × Finset (Fin n)
  /-- The stored origins are those of reads spanning `j` but not `j + 1`. -/
  pick_subset : ∀ j < m, ∀ σ ⊆ D.spanning j ∩ D.spanning (j + 1),
    (pick j σ).2 ⊆ D.spanning j \ D.spanning (j + 1)
  /-- The stored choice attains the maximum defining `M_{j+1}(σ)`. -/
  pick_eq : ∀ j < m, ∀ σ ⊆ D.spanning j ∩ D.spanning (j + 1),
    D.siteScore j (σ ∪ (pick j σ).2) (pick j σ).1 +
      D.message j ((σ ∪ (pick j σ).2) ∩ D.spanning (j - 1)) = D.message (j + 1) σ

theorem nonempty_argmaxTable : Nonempty D.ArgmaxTable := by
  have hex : ∀ j (σ : Finset (Fin n)), ∃ p ∈ (univ : Finset Bool) ×ˢ
      (D.spanning j \ D.spanning (j + 1)).powerset,
      D.message (j + 1) σ = D.siteScore j (σ ∪ p.2) p.1 +
        D.message j ((σ ∪ p.2) ∩ D.spanning (j - 1)) := fun j σ =>
    exists_mem_eq_sup _ ⟨(false, ∅), by simp⟩ _
  refine ⟨⟨fun j σ => Classical.choose (hex j σ), fun j _ σ _ => ?_, fun j _ σ _ => ?_⟩⟩
  · exact mem_powerset.1 (mem_product.1 (Classical.choose_spec (hex j σ)).1).2
  · exact (Classical.choose_spec (hex j σ)).2.symm

namespace ArgmaxTable

variable {D} (A : D.ArgmaxTable)

/-- **Arguments read by backtracking.** Backtracking from the root reads $M_m$ at
$\sigma_m = \emptyset$ (for $j \ge m$ the argument is $\emptyset$), and, at each site
$j < m$, takes the stored choice $(b, U)$ for $\sigma_{j+1}$ and reads $M_j$ at
$\sigma_j = (\sigma_{j+1} \cup U) \cap R_{j-1}$. -/
noncomputable def arg (j : ℕ) : Finset (Fin n) :=
  if hj : m ≤ j then ∅ else
    (arg (j + 1) ∪ (A.pick j (arg (j + 1))).2) ∩ D.spanning (j - 1)
termination_by m - j
decreasing_by omega

/-- **Backtracked origins at a site.** The origins $\sigma_{j+1} \cup U$ of the reads
spanning site $j$ that backtracking chooses, $(b, U)$ being the stored choice for
$\sigma_{j+1}$ (as a subset: the reads with origin $1$). -/
noncomputable def origins (j : ℕ) : Finset (Fin n) := A.arg (j + 1) ∪ (A.pick j (A.arg (j + 1))).2

/-- **Backtracked haplotype.** The stored allele $h_j$ for the argument $\sigma_{j+1}$ that
backtracking reads. -/
noncomputable def hap (j : Fin m) : Bool := (A.pick j (A.arg (j + 1))).1

/-- **Backtracked read origins.** The origin of each read chosen at the first site it
covers. -/
noncomputable def origin (i : Fin n) : Bool :=
  decide (i ∈ A.origins ((D.covered i).min' (D.covered_nonempty i)).val)

theorem arg_of_le {j : ℕ} (hj : m ≤ j) : A.arg j = ∅ := by
  rw [arg, dite_eq_left hj]

theorem arg_of_lt {j : ℕ} (hj : j < m) : A.arg j = A.origins j ∩ D.spanning (j - 1) := by
  rw [arg, dite_eq_right (by omega), origins]

theorem arg_subset (j : ℕ) : A.arg (j + 1) ⊆ D.spanning j ∩ D.spanning (j + 1) := by
  by_cases hj : m ≤ j + 1
  · rw [A.arg_of_le hj]
    exact empty_subset _
  · have ih := arg_subset (j + 1)
    rw [A.arg_of_lt (by omega), origins, Nat.add_sub_cancel, inter_comm _ (D.spanning j)]
    refine inter_subset_inter_left (union_subset (ih.trans inter_subset_left) ?_)
    exact (A.pick_subset (j + 1) (by omega) _ ih).trans sdiff_subset
termination_by m - j
decreasing_by omega

theorem origins_subset {j : ℕ} (hj : j < m) : A.origins j ⊆ D.spanning j :=
  union_subset ((A.arg_subset j).trans inter_subset_left)
    ((A.pick_subset j hj _ (A.arg_subset j)).trans sdiff_subset)

theorem origins_inter {j : ℕ} (hj : j + 1 < m) :
    A.origins j ∩ D.spanning (j + 1) = A.origins (j + 1) ∩ D.spanning j := by
  have hU : (A.pick j (A.arg (j + 1))).2 ∩ D.spanning (j + 1) = ∅ := by
    rw [← disjoint_iff_inter_eq_empty]
    exact disjoint_of_subset_left (A.pick_subset j (by omega) _ (A.arg_subset j))
      disjoint_sdiff_self_left
  rw [origins, union_inter_distrib_right, hU, union_empty, A.arg_of_lt hj,
    Nat.add_sub_cancel, inter_assoc, inter_comm (D.spanning j), ← inter_assoc,
    inter_eq_left.2 (A.origins_subset hj)]

theorem message_arg : ∀ j, j ≤ m →
    D.message j (A.arg j) = ∑ t ∈ range j, D.siteScore t (A.origins t) (A.pick t (A.arg (t + 1))).1
  | 0, _ => by simp [message]
  | j + 1, hj => by
      rw [sum_range_succ, ← message_arg j (by omega),
        ← A.pick_eq j (by omega) (A.arg (j + 1)) (A.arg_subset j),
        A.arg_of_lt (j := j) (by omega), add_comm]
      rfl

end ArgmaxTable

theorem logLikelihood_backtrack (A : D.ArgmaxTable) :
    D.logLikelihood A.hap A.origin = D.message m ∅ := by
  rw [← A.arg_of_le le_rfl, A.message_arg m le_rfl, ← Fin.sum_univ_eq_sum_range
    (fun t => D.siteScore t (A.origins t) (A.pick t (A.arg (t + 1))).1)]
  have hρ : ∀ (t : Fin m) (i : Fin n), i ∈ D.spanning t →
      (i ∈ A.origins t ↔ A.origin i = true) := by
    intro t i hi
    rw [ArgmaxTable.origin, decide_eq_true_iff]
    exact D.mem_iff_mem_min' A.origins (fun t ht => A.origins_inter ht) hi
  rw [logLikelihood, ← D.prod_siteProb A.hap A.origin (fun t => A.origins t) hρ, log_prod]
  exact sum_congr rfl fun t _ => D.log_siteProb _ _ _

/-! ### The tabulated algorithm and its running time -/

open Cslib.Algorithms.Lean

/-- **A site score, with its cost.** The site score
$\sum_{i \in R_j} \log P(o_{ij} \mid r_i, h_j = b)$, added up term by term over the reads
spanning $j$ at a cost of one unit per term. -/
noncomputable def siteScoreTimed (j : ℕ) (T : Finset (Fin n)) (b : Bool) : TimeM ℕ EReal :=
  (D.spanning j).toList.foldlM
    (fun acc i => do
      TimeM.tick 1
      pure (acc + D.logObs i j (decide (i ∈ T)) b)) 0

/-- **One max-sum message value, with its cost.** Given the table `prev` of the previous
message $M_j$, the value $M_{j+1}(\sigma)$: the maximum over the alleles $b$ and the
$U \subseteq R_j \setminus R_{j+1}$ of the site score (`siteScoreTimed`) plus
$M_j((\sigma \cup U) \cap R_{j-1})$, looked up in `prev`. -/
noncomputable def messageTimed (j : ℕ) (prev : Finset (Fin n) → EReal) (σ : Finset (Fin n)) :
    TimeM ℕ EReal :=
  ((univ : Finset Bool) ×ˢ (D.spanning j \ D.spanning (j + 1)).powerset).toList.foldlM
    (fun best p => do
      let s ← D.siteScoreTimed j (σ ∪ p.2) p.1
      pure (max best (s + prev ((σ ∪ p.2) ∩ D.spanning (j - 1))))) ⊥

/-- **Max-sum message tables, with their cost.** The table of $M_0 \equiv 0$, and, from
the table of $M_j$, the table of $M_{j+1}$, which stores `messageTimed` for each assignment
$\sigma \subseteq R_j \cap R_{j+1}$ (and $\bot$ elsewhere). -/
noncomputable def tableTimed : ℕ → TimeM ℕ (Finset (Fin n) → EReal)
  | 0 => pure fun _ => 0
  | j + 1 => do
      let prev ← tableTimed j
      (D.spanning j ∩ D.spanning (j + 1)).powerset.toList.foldlM
        (fun tbl σ => do
          let v ← D.messageTimed j prev σ
          pure (Function.update tbl σ v)) fun _ => ⊥

/-- **Max-sum message passing, with its cost.** Compute the message tables up to $M_m$ and
return $M_m(\emptyset)$. -/
noncomputable def maxSumTimed : TimeM ℕ EReal := do
  let tbl ← D.tableTimed m
  pure (tbl ∅)

/-- **Coverage.** $\kappa = \max_j |R_j|$, the largest number of reads spanning a site
($0$ when there are no sites). -/
def coverage : ℕ := univ.sup fun j : Fin m => #(D.spanning j)

private theorem foldlM_add {α : Type*} (G : EReal → α → TimeM ℕ EReal) (g : α → EReal)
    (c : α → ℕ) (hG : ∀ acc a, (G acc a).ret = acc + g a) (hc : ∀ acc a, (G acc a).time = c a) :
    ∀ (l : List α) (acc : EReal),
      (l.foldlM G acc).ret = acc + (l.map g).sum ∧ (l.foldlM G acc).time = (l.map c).sum
  | [], acc => by simp
  | a :: l, acc => by
      obtain ⟨h1, h2⟩ := foldlM_add G g c hG hc l (G acc a).ret
      rw [List.foldlM_cons, TimeM.ret_bind, TimeM.time_bind, h1, h2, hG, hc]
      simp [add_assoc]

private theorem foldlM_max {α : Type*} [DecidableEq α] (G : EReal → α → TimeM ℕ EReal)
    (g : α → EReal) (c : α → ℕ) (hG : ∀ best a, (G best a).ret = max best (g a))
    (hc : ∀ best a, (G best a).time = c a) :
    ∀ (l : List α) (best : EReal),
      (l.foldlM G best).ret = max best (l.toFinset.sup g) ∧ (l.foldlM G best).time = (l.map c).sum
  | [], best => by simp
  | a :: l, best => by
      obtain ⟨h1, h2⟩ := foldlM_max G g c hG hc l (G best a).ret
      rw [List.foldlM_cons, TimeM.ret_bind, TimeM.time_bind, h1, h2, hG, hc]
      simp [max_assoc]

private theorem foldlM_update {α β : Type} [DecidableEq α] (G : (α → β) → α → TimeM ℕ (α → β))
    (K : α → TimeM ℕ β) (hG : ∀ tbl a, (G tbl a).ret = Function.update tbl a (K a).ret)
    (hc : ∀ tbl a, (G tbl a).time = (K a).time) :
    ∀ (l : List α) (tbl : α → β),
      (∀ x, (l.foldlM G tbl).ret x = if x ∈ l then (K x).ret else tbl x) ∧
      (l.foldlM G tbl).time = (l.map fun a => (K a).time).sum
  | [], tbl => by simp
  | a :: l, tbl => by
      obtain ⟨h1, h2⟩ := foldlM_update G K hG hc l (G tbl a).ret
      rw [List.foldlM_cons, TimeM.ret_bind, TimeM.time_bind, h2, hc]
      refine ⟨fun x => ?_, by simp⟩
      rw [h1, hG]
      by_cases hx : x = a
      · subst hx
        simp
      · simp [hx]

theorem siteScoreTimed_ret_time (j : ℕ) (T : Finset (Fin n)) (b : Bool) :
    (D.siteScoreTimed j T b).ret = D.siteScore j T b ∧
      (D.siteScoreTimed j T b).time = #(D.spanning j) := by
  rw [siteScoreTimed, (foldlM_add _ (fun i => D.logObs i j (decide (i ∈ T)) b) (fun _ => 1)
    (fun _ _ => ?_) (fun _ _ => ?_) _ 0).1, (foldlM_add _ (fun i => D.logObs i j (decide (i ∈ T)) b)
    (fun _ => 1) (fun _ _ => ?_) (fun _ _ => ?_) _ 0).2, zero_add, sum_map_toList, siteScore]
  · simp
  all_goals rfl

theorem messageTimed_ret_time (j : ℕ) (prev : Finset (Fin n) → EReal) (σ : Finset (Fin n)) :
    (D.messageTimed j prev σ).ret = ((univ : Finset Bool) ×ˢ
      (D.spanning j \ D.spanning (j + 1)).powerset).sup (fun p =>
        D.siteScore j (σ ∪ p.2) p.1 + prev ((σ ∪ p.2) ∩ D.spanning (j - 1))) ∧
    (D.messageTimed j prev σ).time =
      2 * 2 ^ #(D.spanning j \ D.spanning (j + 1)) * #(D.spanning j) := by
  have H := foldlM_max (fun best p => do
      let s ← D.siteScoreTimed j (σ ∪ p.2) p.1
      pure (max best (s + prev ((σ ∪ p.2) ∩ D.spanning (j - 1)))))
    (fun p => D.siteScore j (σ ∪ p.2) p.1 + prev ((σ ∪ p.2) ∩ D.spanning (j - 1)))
    (fun _ => #(D.spanning j))
    (fun best p => by rw [TimeM.ret_bind, TimeM.ret_pure, (D.siteScoreTimed_ret_time _ _ _).1])
    (fun best p => by
      rw [TimeM.time_bind, TimeM.time_pure, add_zero, (D.siteScoreTimed_ret_time _ _ _).2])
    ((univ : Finset Bool) ×ˢ (D.spanning j \ D.spanning (j + 1)).powerset).toList ⊥
  refine ⟨?_, ?_⟩
  · rw [messageTimed, H.1, toList_toFinset, bot_sup_eq]
  · rw [messageTimed, H.2]
    simp [card_product, card_powerset, mul_comm]

theorem tableTimed_ret : ∀ (j : ℕ) (σ : Finset (Fin n)),
    (j = 0 ∨ σ ⊆ D.spanning (j - 1) ∩ D.spanning j) → (D.tableTimed j).ret σ = D.message j σ
  | 0, σ, _ => by simp [tableTimed, message]
  | j + 1, σ, hσ => by
      have hσ' : σ ⊆ D.spanning j ∩ D.spanning (j + 1) := by simpa using hσ
      rw [tableTimed, TimeM.ret_bind, ((foldlM_update _ (D.messageTimed j (D.tableTimed j).ret)
        (fun _ _ => rfl) (fun _ _ => add_zero _) _ _).1 σ), ite_eq_left (by simpa using hσ'),
        (D.messageTimed_ret_time _ _ _).1, message]
      refine sup_congr rfl fun p hp => ?_
      simp only [mem_product, mem_univ, mem_powerset, true_and] at hp
      rw [tableTimed_ret j _ ?_]
      rcases Nat.eq_zero_or_pos j with hj | hj
      · exact Or.inl hj
      · refine Or.inr (subset_inter inter_subset_right (inter_subset_left.trans ?_))
        exact union_subset (hσ'.trans inter_subset_left) (hp.trans sdiff_subset)

theorem tableTimed_time : ∀ j : ℕ,
    (D.tableTimed j).time = ∑ t ∈ range j, #(D.spanning t) * 2 ^ (#(D.spanning t) + 1)
  | 0 => by simp [tableTimed]
  | j + 1 => by
      rw [tableTimed, TimeM.time_bind, (foldlM_update _ (D.messageTimed j (D.tableTimed j).ret)
        (fun _ _ => rfl) (fun _ _ => add_zero _) _ _).2, tableTimed_time j, sum_range_succ]
      congr 1
      simp only [(D.messageTimed_ret_time _ _ _).2, List.map_const', List.sum_replicate,
        length_toList, card_powerset, smul_eq_mul]
      rw [← card_inter_add_card_sdiff (D.spanning j) (D.spanning (j + 1))]
      ring

theorem maxSumTimed_ret : D.maxSumTimed.ret = D.message m ∅ := by
  rw [maxSumTimed, TimeM.ret_bind, TimeM.ret_pure]
  exact D.tableTimed_ret m ∅ (by rcases Nat.eq_zero_or_pos m with h | h <;> simp [h])

theorem maxSumTimed_time :
    D.maxSumTimed.time = ∑ t ∈ range m, #(D.spanning t) * 2 ^ (#(D.spanning t) + 1) := by
  rw [maxSumTimed, TimeM.time_bind, TimeM.time_pure, add_zero, tableTimed_time]

theorem maxSumTimed_time_le : D.maxSumTimed.time ≤ m * D.coverage * 2 ^ (D.coverage + 1) := by
  rw [maxSumTimed_time, mul_assoc]
  refine le_trans (sum_le_sum fun t ht => ?_) (by rw [sum_const, card_range, smul_eq_mul])
  have hc : #(D.spanning t) ≤ D.coverage :=
    le_sup (f := fun j : Fin m => #(D.spanning j)) (mem_univ ⟨t, mem_range.1 ht⟩)
  exact Nat.mul_le_mul hc (Nat.pow_le_pow_right two_pos (by omega))

/-! ### The junction tree -/

/-- **Factors of the joint law.** The factors of $P(r, h, o)$: $P(o_{ij} \mid r_i, h_j)$
for $j \in \mathrm{Po}(i)$, and the priors $P(r_i)$ and $P(h_j)$ of every read and site. -/
def IsFactor : Factor n m → Prop
  | .obs i j => j ∈ D.covered i
  | .originPrior _ => True
  | .hapPrior _ => True

/-- **Clusters of the junction tree.** $C_j = \{h_j\} \cup \{r_i, o_{ij} : i \in R_j\}$:
the haplotype allele at site $j$ and the origins and observed alleles at $j$ of the reads
spanning $j$. -/
def cluster (j : Fin m) : Set (Var n m) :=
  {v | v = .hap j ∨ ∃ i ∈ D.spanning j, v = .origin i ∨ v = .obs i j}

theorem exists_scope_subset_cluster {f : Factor n m} (hf : D.IsFactor f) :
    ∃ j, f.scope ⊆ D.cluster j := by
  cases f with
  | obs i j =>
      have hi : i ∈ D.spanning j := D.mem_spanning_of_mem_covered hf
      refine ⟨j, fun v hv => ?_⟩
      simp only [Factor.scope, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl
      · exact Or.inr ⟨i, hi, Or.inr rfl⟩
      · exact Or.inr ⟨i, hi, Or.inl rfl⟩
      · exact Or.inl rfl
  | originPrior i =>
      refine ⟨(D.covered i).min' (D.covered_nonempty i), fun v hv => ?_⟩
      simp only [Factor.scope, Set.mem_singleton_iff] at hv
      subst hv
      exact Or.inr ⟨i, D.mem_spanning_of_mem_covered (min'_mem _ _), Or.inl rfl⟩
  | hapPrior j =>
      refine ⟨j, fun v hv => ?_⟩
      simp only [Factor.scope, Set.mem_singleton_iff] at hv
      exact Or.inl hv

theorem hap_mem_cluster {j x : Fin m} : Var.hap j ∈ D.cluster x ↔ j = x := by
  simp [cluster]

theorem origin_mem_cluster {i : Fin n} {x : Fin m} :
    Var.origin i ∈ D.cluster x ↔ i ∈ D.spanning x := by
  simp [cluster]

theorem obs_mem_cluster {i : Fin n} {j x : Fin m} :
    Var.obs i j ∈ D.cluster x ↔ i ∈ D.spanning x ∧ j = x := by
  simp [cluster]

theorem mem_cluster_of_le {v : Var n m} {x y z : Fin m} (hx : v ∈ D.cluster x)
    (hy : v ∈ D.cluster y) (hxz : x ≤ z) (hzy : z ≤ y) : v ∈ D.cluster z := by
  cases v with
  | hap j =>
      rw [hap_mem_cluster] at hx hy ⊢
      subst hx
      subst hy
      exact le_antisymm hxz hzy
  | origin i =>
      rw [origin_mem_cluster] at hx hy ⊢
      exact D.mem_spanning_of_le hx hy hxz hzy
  | obs i j =>
      rw [obs_mem_cluster] at hx hy ⊢
      obtain ⟨hi, rfl⟩ := hx
      obtain ⟨-, rfl⟩ := hy
      obtain rfl := le_antisymm hxz hzy
      exact ⟨hi, rfl⟩

/-! ### Minimum error correction -/

/-- **Number of allele flips.**
$\#\{(i, j) : j \in \mathrm{Po}(i),\ M_{ij} \ne h_j(r_i)\}$, the number of entries of the
phasing matrix to correct so that each read agrees with the haplotype it comes from, $h$ for
$r_i = 0$ and $\bar h$ for $r_i = 1$. -/
def flips (h : Fin m → Bool) (r : Fin n → Bool) : ℕ :=
  ∑ i, #{j ∈ D.covered i | D.allele i j ≠ some (xor (h j) (r i))}

/-- **Minimum error correction solution.** A haplotype $h$ and read origins $r$, that is a
bipartition of the reads and a haplotype pair $(h, \bar h)$, that require the fewest allele
flips. -/
def IsMEC (h : Fin m → Bool) (r : Fin n → Bool) : Prop :=
  ∀ h' r', D.flips h r ≤ D.flips h' r'

theorem logLikelihood_eq_of_err_eq {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hQ : ∀ i j, D.err i j = q) (h : Fin m → Bool) (r : Fin n → Bool) :
    D.logLikelihood h r = ((∑ i, #(D.covered i) : ℕ) * Real.log (1 - q) -
      Real.log ((1 - q) / q) * D.flips h r : ℝ) := by
  have hpos : ∀ i (j : Fin m), j ∈ D.covered i → 0 < D.obsProb i j (r i) (h j) := by
    intro i j hj
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 (D.mem_covered.1 hj)
    simp only [obsProb, ha, alleleProb, hQ]
    split_ifs <;> linarith
  have hlog : ∀ i (j : Fin m), j ∈ D.covered i → Real.log (D.obsProb i j (r i) (h j)) =
      Real.log (1 - q) - if D.allele i j ≠ some (xor (h j) (r i))
        then Real.log ((1 - q) / q) else 0 := by
    intro i j hj
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 (D.mem_covered.1 hj)
    simp only [obsProb, ha, alleleProb, hQ, ne_eq, Option.some.injEq]
    split_ifs with h1
    · simp
    · rw [Real.log_div (by linarith) hq0.ne']
      ring
  have hL : 0 < D.likelihood h r :=
    prod_pos fun i _ => prod_pos fun j hj => hpos i j hj
  rw [logLikelihood, ENNReal.log_ofReal_of_pos hL, likelihood,
    Real.log_prod fun i _ => (prod_pos fun j hj => hpos i j hj).ne']
  congr 1
  rw [flips, Nat.cast_sum, Nat.cast_sum, sum_mul, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [Real.log_prod fun j hj => (hpos i j hj).ne', sum_congr rfl (hlog i), sum_sub_distrib,
    sum_const, nsmul_eq_mul, sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
  ring

theorem isMaxOn_iff_isMEC {q : ℝ} (hq0 : 0 < q) (hq : q < 1 / 2)
    (hQ : ∀ i j, D.err i j = q) (h : Fin m → Bool) (r : Fin n → Bool) :
    (∀ h' r', D.logLikelihood h' r' ≤ D.logLikelihood h r) ↔ D.IsMEC h r := by
  have hK : 0 < Real.log ((1 - q) / q) :=
    Real.log_pos ((one_lt_div hq0).2 (by linarith))
  simp only [D.logLikelihood_eq_of_err_eq hq0 (by linarith) hQ, EReal.coe_le_coe_iff, IsMEC]
  refine forall₂_congr fun h' r' => ?_
  rw [sub_le_sub_iff_left, mul_le_mul_iff_right₀ hK, Nat.cast_le]

/-! ### The joint law -/

/-- **Joint law.** $P(r, h, o = M) = \prod_i \prod_{j \in \mathrm{Po}(i)}
P(o_{ij} = M_{ij} \mid r_i, h_j) \prod_i P(r_i) \prod_j P(h_j)$, with the uniform priors
`originPrior` and the priors `hapPrior`, $P(h_0 = 0) = 1$ and uniform at the other sites. -/
noncomputable def jointProb (h : Fin m → Bool) (r : Fin n → Bool) : ℝ :=
  D.likelihood h r * (∏ i, originPrior (r i)) * ∏ j, hapPrior j (h j)

theorem likelihood_not (h : Fin m → Bool) (r : Fin n → Bool) :
    D.likelihood (fun j => !h j) (fun i => !r i) = D.likelihood h r := by
  simp [likelihood, obsProb, alleleProb]

theorem jointProb_eq [NeZero m] (h : Fin m → Bool) (r : Fin n → Bool) :
    D.jointProb h r = if h 0 = true then 0 else (1 / 2) ^ (n + m - 1) * D.likelihood h r := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos m)).symm⟩
  rw [jointProb, Fin.prod_univ_succ]
  have hsucc : ∀ j : Fin k, hapPrior j.succ (h j.succ) = 1 / 2 := fun j => by
    simp [hapPrior]
  simp only [hsucc, prod_const, card_univ, Fintype.card_fin, originPrior]
  by_cases h0 : h 0 = true
  · simp [hapPrior, h0]
  · simp only [hapPrior, Fin.val_zero, ↓reduceIte, h0, Bool.false_eq_true]
    rw [show n + (k + 1) - 1 = n + k by omega, pow_add]
    ring

theorem log_jointProb_of_false [NeZero m] {h : Fin m → Bool} (h0 : h 0 = false)
    (r : Fin n → Bool) : ENNReal.log (ENNReal.ofReal (D.jointProb h r)) =
      D.logLikelihood h r + (Real.log ((1 / 2) ^ (n + m - 1)) : EReal) := by
  have hc : (0 : ℝ) < (1 / 2) ^ (n + m - 1) := by positivity
  rw [D.jointProb_eq, ite_eq_right (by simp [h0]), ENNReal.ofReal_mul hc.le,
    ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos hc, logLikelihood, add_comm]

theorem log_jointProb_of_true [NeZero m] {h : Fin m → Bool} (h0 : h 0 = true)
    (r : Fin n → Bool) : ENNReal.log (ENNReal.ofReal (D.jointProb h r)) = ⊥ := by
  rw [D.jointProb_eq, ite_eq_left h0, ENNReal.ofReal_zero, ENNReal.log_zero]

theorem sup_log_jointProb (hm : 0 < m) :
    (univ : Finset ((Fin m → Bool) × (Fin n → Bool))).sup
      (fun p => ENNReal.log (ENNReal.ofReal (D.jointProb p.1 p.2))) =
      D.message m ∅ + (Real.log ((1 / 2) ^ (n + m - 1)) : EReal) := by
  have : NeZero m := ⟨hm.ne'⟩
  set c : EReal := (Real.log ((1 / 2) ^ (n + m - 1)) : EReal)
  set f : (Fin m → Bool) × (Fin n → Bool) → EReal := fun p => D.logLikelihood p.1 p.2 with hf
  set g : (Fin m → Bool) × (Fin n → Bool) → EReal :=
    fun p => ENNReal.log (ENNReal.ofReal (D.jointProb p.1 p.2)) with hg
  rw [← D.sup_logLikelihood_eq_message]
  apply le_antisymm
  · refine Finset.sup_le fun p _ => ?_
    cases h0 : p.1 0
    · have hle : f p ≤ univ.sup f := le_sup (mem_univ p)
      simp only [hg, D.log_jointProb_of_false h0]
      exact add_le_add_left hle c
    · simp only [hg, D.log_jointProb_of_true h0]
      exact bot_le
  · obtain ⟨p, -, hp⟩ := exists_mem_eq_sup univ univ_nonempty f
    rw [hp]
    cases h0 : p.1 0
    · have hle : g p ≤ univ.sup g := le_sup (mem_univ p)
      simp only [hg, D.log_jointProb_of_false h0] at hle
      exact hle
    · let p' : (Fin m → Bool) × (Fin n → Bool) := (fun j => !p.1 j, fun i => !p.2 i)
      have hp' : f p' = f p := by
        simp only [hf, logLikelihood, p', likelihood_not]
      have h0' : p'.1 0 = false := by simp [p', h0]
      have hle : g p' ≤ univ.sup g := le_sup (mem_univ p')
      simp only [hg, D.log_jointProb_of_false h0'] at hle
      rw [← hp']
      exact hle

/-! ### The main result -/

/-- **Probabilistic haplotyping by max-sum message passing** (Kuleshov 2014, Sections 4.1–4.3
and 5.1). Let $n$ reads and $m$ heterozygous sites, numbered from $0$, be given by a phasing
matrix $M \in \{0, 1, -\}^{n \times m}$ and an error matrix $Q \in [0, 1)^{n \times m}$, every
read covering a site. Let $\mathrm{Po}(i) = \{j : M_{ij} \ne -\}$,
$R_j = \{i : \min \mathrm{Po}(i) \le j \le \max \mathrm{Po}(i)\}$, $\kappa = \max_j |R_j|$, and
$P(o_{ij} = M_{ij} \mid r_i, h_j)$ equal to $1 - Q_{ij}$ if $M_{ij} = h_j(r_i)$ and to $Q_{ij}$
otherwise, where $h_j(r_i)$ is $h_j$ if $r_i = 0$ and $1 - h_j$ if $r_i = 1$. Then:

1. **Junction tree.** Every factor of the joint law $P(r, h, o)$ (the factors
   $P(o_{ij} \mid r_i, h_j)$ for $j \in \mathrm{Po}(i)$ and the priors $P(r_i)$, $P(h_j)$) has its
   scope in some cluster $C_j = \{h_j\} \cup \{r_i, o_{ij} : i \in R_j\}$, and the clusters,
   joined in a path in the order of the sites, have the running intersection property: a
   variable in $C_x$ and $C_y$ with $x \le z \le y$ is in $C_z$.
2. **Priors.** The likelihood $P(o = M \mid r, h)$ is unchanged when both $h$ and $r$ are
   complemented, and, with the uniform priors except $P(h_0 = 0) = 1$ and $m \ge 1$, the maximum of
   $\log P(r, h, o = M)$ over $(h, r)$ is $M_m(\emptyset) + \log 2^{-(n + m - 1)}$.
3. **Exactness.** The maximum over $(h, r)$ of $\log P(o = M \mid r, h)$ is $M_m(\emptyset)$, the
   value that the max-sum messages (`ReadData.message`) take at the root.
4. **Backtracking.** Stored argmaxes of the messages exist, and for any of them the backtracked
   haplotype and read origins attain that maximum.
5. **Running time.** The tabulated algorithm returns $M_m(\emptyset)$ after at most
   $m \kappa 2^{\kappa + 1}$ evaluations of terms $\log P(o_{ij} \mid r_i, h_j)$.
6. **Minimum error correction.** If $Q_{ij} = q$ for all $i, j$, with $0 < q < 1/2$, then
   $\log P(o = M \mid r, h) = N \log(1 - q) - \log\frac{1 - q}{q} \cdot
   \#\{(i, j) : j \in \mathrm{Po}(i),\ M_{ij} \ne h_j(r_i)\}$, where
   $N = \sum_i |\mathrm{Po}(i)|$, and $(h, r)$ maximizes the likelihood if and only if it is a
   minimum error correction solution. -/
theorem maxSum_haplotyping :
    ((∀ f : Factor n m, D.IsFactor f → ∃ j, f.scope ⊆ D.cluster j) ∧
      ∀ (v : Var n m) (x y z : Fin m), v ∈ D.cluster x → v ∈ D.cluster y → x ≤ z → z ≤ y →
        v ∈ D.cluster z) ∧
    ((∀ h r, D.likelihood (fun j => !h j) (fun i => !r i) = D.likelihood h r) ∧
      (0 < m → (univ : Finset ((Fin m → Bool) × (Fin n → Bool))).sup
        (fun p => ENNReal.log (ENNReal.ofReal (D.jointProb p.1 p.2))) =
          D.message m ∅ + (Real.log ((1 / 2) ^ (n + m - 1)) : EReal))) ∧
    (univ : Finset ((Fin m → Bool) × (Fin n → Bool))).sup
      (fun p => D.logLikelihood p.1 p.2) = D.message m ∅ ∧
    (Nonempty D.ArgmaxTable ∧
      ∀ A : D.ArgmaxTable, D.logLikelihood A.hap A.origin = D.message m ∅) ∧
    (D.maxSumTimed.ret = D.message m ∅ ∧
      D.maxSumTimed.time ≤ m * D.coverage * 2 ^ (D.coverage + 1)) ∧
    ∀ q : ℝ, 0 < q → q < 1 / 2 → (∀ i j, D.err i j = q) →
      (∀ h r, D.logLikelihood h r = ((∑ i, #(D.covered i) : ℕ) * Real.log (1 - q) -
        Real.log ((1 - q) / q) * D.flips h r : ℝ)) ∧
      ∀ h r, (∀ h' r', D.logLikelihood h' r' ≤ D.logLikelihood h r) ↔ D.IsMEC h r :=
  ⟨⟨fun _ => D.exists_scope_subset_cluster, fun _ _ _ _ => D.mem_cluster_of_le⟩,
    ⟨D.likelihood_not, D.sup_log_jointProb⟩, D.sup_logLikelihood_eq_message,
    ⟨D.nonempty_argmaxTable, D.logLikelihood_backtrack⟩,
    ⟨D.maxSumTimed_ret, D.maxSumTimed_time_le⟩,
    fun _ hq0 hq hQ => ⟨D.logLikelihood_eq_of_err_eq hq0 (by linarith) hQ,
      D.isMaxOn_iff_isMEC hq0 hq hQ⟩⟩

end ReadData

end Cslib.Bioinformatics.Haplotyping
