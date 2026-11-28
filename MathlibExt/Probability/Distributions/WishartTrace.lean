/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Gaussian.Real
public import MathlibExt.LinearAlgebra.Matrix.TraceDispersion
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Probability.Independence.Integration
import MathlibExt.Probability.Distributions.ChiSquare
import MathlibExt.Probability.Distributions.GammaMoments
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite real Wishart trace moments

The sample is a real `m × n` matrix `M`; its law is the finite product of centred normal
laws of entry variance `v`. The Gram matrix `X = M Mᵀ` is neither centred nor divided by
the number of columns. Its diagonal entries are squared row lengths; off the diagonal they
are inner products of independent rows. Expanding their squares gives the first two trace
moments, including in zero variance and in empty dimensions. The two statistics used for
moment fitting are `tr X` and `2 tr(X²) + (tr X)²`, not `tr X` and `tr(X²)`.
When `v > 0`, `m ≥ 2` and `n ≥ 1`, two distinct rows almost surely have different squared
lengths. Thus `m tr(X²) − (tr X)²` is strictly positive without any rank assumption.

See N. Patterson, A. L. Price and D. Reich, “Population Structure and Eigenanalysis”,
PLOS Genetics 2 (2006), e190, Theorem 1 and equations (23)–(24), pp. 2089–2090,
<https://doi.org/10.1371/journal.pgen.0020190>.
-/

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped NNReal ENNReal

namespace ProbabilityTheory.Wishart

variable {m n : ℕ}

/-- Law of an `m × n` real matrix with independent normal entries of mean zero and
variance `v ≥ 0`. This is a measure on the data matrix, not its pushforward to the cone of
positive semidefinite matrices. -/
abbrev matrixLaw (m n : ℕ) (v : ℝ≥0) : Measure (Fin m → Fin n → ℝ) :=
  Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 v

/-- The uncentred, unnormalised Gram matrix of the rows of the sample. -/
def gram (M : Fin m → Fin n → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of M * (Matrix.of M)ᵀ

/-- Every sample Gram matrix is positive semidefinite, even when `n < m`. -/
theorem gram_posSemidef (M : Fin m → Fin n → ℝ) : (gram M).PosSemidef := by
  simpa [gram, conjTranspose_eq_transpose_of_trivial] using
    posSemidef_self_mul_conjTranspose (Matrix.of M)

private abbrev iid {α : Type*} [MeasurableSpace α] (k : ℕ) (μ : Measure α) :
    Measure (Fin k → α) := Measure.pi fun _ => μ

private lemma marginal {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {k : ℕ} (i : Fin k) : HasLaw (fun x : Fin k → α => x i) μ (iid k μ) :=
  (measurePreserving_eval (fun _ => μ) i).hasLaw

private lemma factor {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {k : ℕ} {i j : Fin k} (hij : i ≠ j) {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g) :
    ∫ x, f (x i) * g (x j) ∂iid k μ = (∫ a, f a ∂μ) * ∫ a, g a ∂μ := by
  have hi : iIndepFun (fun i (x : Fin k → α) => x i) (iid k μ) :=
    iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id
  rw [(hi.indepFun hij).integral_fun_comp_mul_comp (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable
    hf.aestronglyMeasurable hg.aestronglyMeasurable]
  exact congrArg₂ (· * ·) ((marginal i).integral_comp hf.aestronglyMeasurable)
    ((marginal j).integral_comp hg.aestronglyMeasurable)

private lemma normal_sq (v : ℝ≥0) : ∫ x, x ^ 2 ∂gaussianReal 0 v = v := by
  simpa [variance_eq_integral measurable_id'.aemeasurable] using
    variance_fun_id_gaussianReal (μ := 0) (v := v)

private lemma normal_fourth (v : ℝ≥0) : ∫ x, x ^ 4 ∂gaussianReal 0 v = 3 * (v : ℝ) ^ 2 := by
  have h₁ : ∫ x, x ^ 4 ∂gaussianReal 0 1 = 3 := by
    have h := integral_sq_gammaMeasure (a := 1 / 2) (r := 1 / 2) (by norm_num) (by norm_num)
    have he : chiSquareMeasure 1 = gammaMeasure (1 / 2) (1 / 2) := by norm_num [chiSquareMeasure]
    rw [← he, ← gaussianReal_map_sq, integral_map (by fun_prop) (by fun_prop)] at h
    norm_num [← pow_mul] at h
    exact h
  let c := Real.sqrt v
  have hc : c ^ 2 = (v : ℝ) := Real.sq_sqrt v.2
  have hh : (gaussianReal 0 1).map (c * ·) = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
    exact NNReal.eq hc
  rw [← hh, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [mul_pow, integral_const_mul, h₁]
  rw [show c ^ 4 = (c ^ 2) ^ 2 by ring, hc, mul_comm]

private lemma count_pairs (k : ℕ) (a b : ℝ) :
    (∑ i : Fin k, ∑ j : Fin k, if i = j then a else b) = k * (a + (k - 1) * b) := by
  simp_rw [show ∀ i j : Fin k, (if i = j then a else b) = b + (if i = j then a - b else 0)
    from fun i j => by split_ifs <;> ring, Finset.sum_add_distrib]
  simp
  ring

private lemma sum_second {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {k : ℕ}
    (Z : Fin k → Ω → ℝ) (hZ : ∀ i, MemLp (Z i) 2 P) (a b : ℝ)
    (h : ∀ i j, ∫ x, Z i x * Z j x ∂P = if i = j then a else b) :
    ∫ x, (∑ i, Z i x) ^ 2 ∂P = k * (a + (k - 1) * b) := by
  simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
  have hp (i j) : Integrable (fun x => Z i x * Z j x) P := (hZ i).integrable_mul (hZ j)
  rw [integral_finsetSum Finset.univ fun i _ => integrable_finsetSum Finset.univ fun j _ => hp i j]
  simp_rw [integral_finsetSum Finset.univ fun j _ => hp _ j, h]
  exact count_pairs k a b

private abbrev rowLaw (n : ℕ) (v : ℝ≥0) := iid n (gaussianReal 0 v)

private lemma holder_four : ENNReal.HolderTriple 4 4 2 := ⟨by
  rw [← two_mul, show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
    ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), ← mul_assoc,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]⟩

attribute [local instance] holder_four

private lemma coord_four (v : ℝ≥0) (a : Fin n) :
    MemLp (fun x : Fin n → ℝ => x a) 4 (rowLaw n v) :=
  (memLp_id_gaussianReal' 4 (by norm_num)).comp_measurePreserving (measurePreserving_eval _ a)

private lemma row_pair (v : ℝ≥0) (a b : Fin n) :
    ∫ x, x a * x b ∂rowLaw n v = if a = b then (v : ℝ) else 0 := by
  split_ifs with h
  · subst b
    simpa [sq] using ((marginal a).integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)).trans
      (normal_sq v)
  · simpa using factor (μ := gaussianReal 0 v) h measurable_id measurable_id

private abbrev lengthSq (x : Fin n → ℝ) := ∑ a, x a ^ 2

private lemma measurable_length : Measurable (lengthSq (n := n)) := by
  unfold lengthSq
  fun_prop

private lemma row_length (v : ℝ≥0) : ∫ x, lengthSq x ∂rowLaw n v = (n : ℝ) * v := by
  unfold lengthSq
  rw [integral_finsetSum Finset.univ fun a _ =>
    ((coord_four v a).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)).integrable_sq]
  simp_rw [sq, row_pair]
  simp

private lemma row_length_sq (v : ℝ≥0) :
    ∫ x, lengthSq x ^ 2 ∂rowLaw n v = (n : ℝ) * (n + 2) * (v : ℝ) ^ 2 := by
  have hl (a : Fin n) : MemLp (fun x : Fin n → ℝ => x a ^ 2) 2 (rowLaw n v) := by
    simpa [sq, Pi.mul_def] using (coord_four v a).mul (r := 2) (coord_four v a)
  rw [sum_second (fun a (x : Fin n → ℝ) => x a ^ 2) hl (3 * v ^ 2) (v ^ 2)]
  · ring
  intro a b
  split_ifs with h
  · subst b
    convert ((marginal a).integral_comp (f := fun x : ℝ => x ^ 4) (by fun_prop)).trans
      (normal_fourth v) using 1
    congr 1; funext x; dsimp; ring
  · rw [factor (μ := gaussianReal 0 v) (f := (· ^ 2)) (g := (· ^ 2)) h
      (by fun_prop) (by fun_prop), normal_sq, sq]

private lemma entry_lp (v : ℝ≥0) (i : Fin m) (a : Fin n) :
    MemLp (fun M : Fin m → Fin n → ℝ => M i a) 4 (matrixLaw m n v) :=
  (coord_four v a).comp_measurePreserving (measurePreserving_eval _ i)

private lemma gram_lp (v : ℝ≥0) (i j : Fin m) :
    MemLp (fun M => gram M i j) 2 (matrixLaw m n v) :=
  memLp_finsetSum Finset.univ (f := fun (a : Fin n) (M : Fin m → Fin n → ℝ) => M i a * M j a)
    fun a _ => (entry_lp v i a).mul (entry_lp v j a)

private lemma gram_diag (M : Fin m → Fin n → ℝ) (i : Fin m) :
    gram M i i = lengthSq (M i) := by simp [gram, Matrix.mul_apply, lengthSq, sq]

/-- With independent `N(0,v)` entries of variance `v ≥ 0`, each diagonal entry of
the unnormalised Gram matrix has expectation `n v`. -/
theorem integral_gram_diag (v : ℝ≥0) (i : Fin m) :
    ∫ M, gram M i i ∂matrixLaw m n v = (n : ℝ) * v := by
  simp_rw [gram_diag]
  exact ((marginal i).integral_comp (f := lengthSq) measurable_length.aestronglyMeasurable).trans
    (row_length v)

/-- For independent centred normal entries of variance `v ≥ 0`, a squared row length has
second moment `n(n+2)v²`; an inner product of two distinct rows has second moment `nv²`. -/
theorem integral_gram_entry_sq (v : ℝ≥0) (i j : Fin m) :
    ∫ M, gram M i j ^ 2 ∂matrixLaw m n v =
      if i = j then (n : ℝ) * (n + 2) * (v : ℝ) ^ 2 else (n : ℝ) * (v : ℝ) ^ 2 := by
  split_ifs with hij
  · subst j
    simp_rw [gram_diag]
    exact ((marginal i).integral_comp (f := fun x => lengthSq x ^ 2)
      (measurable_length.pow_const 2).aestronglyMeasurable).trans (row_length_sq v)
  · let Z := fun a (M : Fin m → Fin n → ℝ) => M i a * M j a
    have hz (a) : MemLp (Z a) 2 (matrixLaw m n v) := (entry_lp v i a).mul (entry_lp v j a)
    change ∫ M, (∑ a, Z a M) ^ 2 ∂_ = _
    rw [sum_second Z hz (v ^ 2) 0]
    · ring
    intro a b
    have he (M) : Z a M * Z b M = (M i a * M i b) * (M j a * M j b) := by dsimp [Z]; ring
    simp_rw [he]
    rw [factor (μ := rowLaw n v) (f := fun x => x a * x b) (g := fun x => x a * x b) hij
      (by fun_prop) (by fun_prop), row_pair]
    split_ifs <;> ring

/-- First eigenvalue power sum of the sample Gram matrix, expressed as its trace. -/
def firstTrace (M : Fin m → Fin n → ℝ) : ℝ := (gram M).trace

/-- Second eigenvalue power sum of the sample Gram matrix, expressed as the trace of its square. -/
def secondTrace (M : Fin m → Fin n → ℝ) : ℝ := (gram M ^ 2).trace

/-- The two sample traces are the first and second power sums over the full spectrum of
`M Mᵀ`, including zero eigenvalues and counting multiplicities. -/
theorem trace_power_sums (M : Fin m → Fin n → ℝ) :
    let eigs := (gram_posSemidef M).isHermitian.eigenvalues
    firstTrace M = ∑ i, eigs i ∧ secondTrace M = ∑ i, eigs i ^ 2 := by
  exact ⟨(gram_posSemidef M).isHermitian.trace_eq_sum_eigenvalues,
    (gram_posSemidef M).isHermitian.trace_sq_eq_sum_sq_eigenvalues⟩

private lemma trace_two_sum (M : Fin m → Fin n → ℝ) :
    secondTrace M = ∑ i, ∑ j, gram M i j ^ 2 := by
  have h (i j) : gram M j i = gram M i j := by
    simp only [gram, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  simp only [secondTrace, sq, Matrix.trace, Matrix.diag, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [h i j]

private lemma first_lp (v : ℝ≥0) : MemLp (firstTrace (m := m) (n := n)) 2 (matrixLaw m n v) :=
  memLp_finsetSum Finset.univ (f := fun i M => gram M i i) fun i _ => gram_lp v i i

/-- Under the Gaussian product law, the trace, trace of the square, squared trace and fitted
second statistic of the unnormalised Gram matrix are integrable, including when `v = 0`. -/
theorem trace_integrability (m n : ℕ) (v : ℝ≥0) :
    Integrable firstTrace (matrixLaw m n v) ∧ Integrable secondTrace (matrixLaw m n v) ∧
    Integrable (fun M => firstTrace M ^ 2) (matrixLaw m n v) ∧
    Integrable (fun M => 2 * secondTrace M + firstTrace M ^ 2) (matrixLaw m n v) := by
  have h : Integrable secondTrace (matrixLaw m n v) := by
    rw [funext (trace_two_sum (m := m) (n := n))]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (gram_lp v i j).integrable_sq
  have h' := (first_lp (m := m) (n := n) v).integrable_sq
  exact ⟨(first_lp v).integrable (by norm_num), h, h', (h.const_mul 2).add h'⟩

/-- The four finite trace moments of `X = M Mᵀ` for independent centred normal entries of
variance `v ≥ 0`. Writing `s = tr X` and `t = tr(X²)`, the means of `s`, `t`, `s²` and
`2t + s²` are `mnv`, `mn(m+n+1)v²`, `mn(mn+2)v²` and `m(m+2)n(n+2)v²`. In particular
the third integral is the expectation of the squared trace, not the square of its mean. -/
theorem trace_moments (m n : ℕ) (v : ℝ≥0) :
    (∫ M, firstTrace M ∂matrixLaw m n v) = (m : ℝ) * n * v ∧
    (∫ M, secondTrace M ∂matrixLaw m n v) = (m : ℝ) * n * (m + n + 1) * (v : ℝ) ^ 2 ∧
    (∫ M, firstTrace M ^ 2 ∂matrixLaw m n v) = (m : ℝ) * n * (m * n + 2) * (v : ℝ) ^ 2 ∧
    (∫ M, 2 * secondTrace M + firstTrace M ^ 2 ∂matrixLaw m n v) =
      (m : ℝ) * (m + 2) * n * (n + 2) * (v : ℝ) ^ 2 := by
  let P := matrixLaw m n v
  have e₁ : ∫ M, firstTrace M ∂P = (m : ℝ) * n * v := by
    change ∫ M, ∑ i, gram M i i ∂matrixLaw m n v = _
    rw [integral_finsetSum Finset.univ fun i _ => (gram_lp v i i).integrable (by norm_num)]
    simp [integral_gram_diag, mul_assoc]
  have e₂ : ∫ M, secondTrace M ∂P = (m : ℝ) * n * (m + n + 1) * (v : ℝ) ^ 2 := by
    simp_rw [trace_two_sum]
    rw [integral_finsetSum Finset.univ fun i _ => integrable_finsetSum Finset.univ fun j _ =>
      (gram_lp v i j).integrable_sq]
    simp_rw [integral_finsetSum Finset.univ fun j _ => (gram_lp v _ j).integrable_sq,
      integral_gram_entry_sq, count_pairs]
    ring
  have e₃ : ∫ M, firstTrace M ^ 2 ∂P = (m : ℝ) * n * (m * n + 2) * (v : ℝ) ^ 2 := by
    change ∫ M, (∑ i, gram M i i) ^ 2 ∂matrixLaw m n v = _
    rw [sum_second (fun i M => gram M i i) (fun i => gram_lp v i i)
      ((n : ℝ) * (n + 2) * (v : ℝ) ^ 2) (((n : ℝ) * v) ^ 2)]
    · ring
    intro i j
    split_ifs with h
    · subst j
      simpa [sq] using integral_gram_entry_sq (n := n) v i i
    · simp_rw [gram_diag]
      rw [factor (μ := rowLaw n v) (f := lengthSq) (g := lengthSq) h
        measurable_length measurable_length, row_length, sq]
  refine ⟨e₁, e₂, e₃, ?_⟩
  obtain ⟨_, h₂, h₃, _⟩ := trace_integrability m n v
  rw [integral_add (h₂.const_mul 2) h₃, integral_const_mul, e₂, e₃]
  ring

private lemma ae_sq_ne (v : ℝ≥0) (hv : 0 < v) (c : ℝ) : ∀ᵐ x ∂gaussianReal 0 v, x ^ 2 ≠ c := by
  let := nullSingletonClass_gaussianReal (μ := 0) hv.ne'
  filter_upwards [(gaussianReal 0 v).ae_ne (Real.sqrt c), (gaussianReal 0 v).ae_ne (-Real.sqrt c)]
    with x hp hn he
  have hc : 0 ≤ c := he ▸ sq_nonneg x
  exact (sq_eq_sq_iff_eq_or_eq_neg.mp (he.trans (Real.sq_sqrt hc).symm)).elim hp hn

private lemma ae_length_ne (v : ℝ≥0) (hv : 0 < v) (hn : 0 < n) (c : ℝ) :
    ∀ᵐ x ∂rowLaw n v, lengthSq x ≠ c := by
  cases n with
  | zero => omega
  | succ n =>
    have hm : MeasurableSet {z : ℝ × (Fin n → ℝ) | z.1 ^ 2 + lengthSq z.2 ≠ c} :=
      (measurableSet_eq_fun (by unfold lengthSq; fun_prop) measurable_const).compl
    have h : ∀ᵐ z ∂(gaussianReal 0 v).prod (rowLaw n v), z.1 ^ 2 + lengthSq z.2 ≠ c := by
      apply (Measure.ae_prod_iff_ae_ae hm).2
      apply (Measure.ae_ae_comm hm).2
      exact Filter.Eventually.of_forall fun y => (ae_sq_ne v hv (c - lengthSq y)).mono
        fun x hx he => hx (by linarith)
    have mp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 v) 0
    have hh := mp.quasiMeasurePreserving.ae h
    filter_upwards [hh] with x hx
    simpa [lengthSq, Fin.sum_univ_succ, MeasurableEquiv.piFinSuccAbove_apply,
      Fin.insertNthEquiv, Fin.tail] using hx

private lemma ae_rows (v : ℝ≥0) (hv : 0 < v) (hn : 0 < n) {i j : Fin m} (hij : i ≠ j) :
    ∀ᵐ M ∂Measure.pi (fun _ : Fin m => rowLaw n v), lengthSq (M i) ≠ lengthSq (M j) := by
  have hi : iIndepFun (fun i (x : Fin m → Fin n → ℝ) => x i) (Measure.pi fun _ => rowLaw n v) :=
    iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id
  have hm : MeasurableSet {p : (Fin n → ℝ) × (Fin n → ℝ) | lengthSq p.1 ≠ lengthSq p.2} :=
    (measurableSet_eq_fun (by unfold lengthSq; fun_prop) (by unfold lengthSq; fun_prop)).compl
  have hh : ∀ᵐ z ∂(rowLaw n v).prod (rowLaw n v), lengthSq z.1 ≠ lengthSq z.2 :=
    (Measure.ae_prod_iff_ae_ae hm).2 (Filter.Eventually.of_forall fun x =>
      (ae_length_ne v hv hn (lengthSq x)).mono fun _ h => h.symm)
  have hj := (hi.indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  have mp (q : Fin m) := (measurePreserving_eval (fun _ : Fin m => rowLaw n v) q).map_eq
  rw [mp i, mp j] at hj
  rw [← hj] at hh
  exact (ae_map_iff ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable hm).1 hh

/-- Eigenvalue dispersion of the sample: `m tr(X²) − (tr X)²` for `X = M Mᵀ`. -/
def dispersion (M : Fin m → Fin n → ℝ) : ℝ := m * secondTrace M - firstTrace M ^ 2

/-- Every sample has nonnegative dispersion, with equality exactly for a scalar Gram matrix. -/
theorem dispersion_spec (M : Fin m → Fin n → ℝ) :
    0 ≤ dispersion M ∧ (dispersion M = 0 ↔ ∃ c : ℝ, gram M = c • 1) :=
  ⟨(gram_posSemidef M).isHermitian.trace_dispersion_nonneg,
   (gram_posSemidef M).isHermitian.trace_dispersion_eq_zero_iff⟩

/-- For independent centred Gaussian entries of positive variance, at least two rows and
at least one column give strictly positive dispersion almost surely, even for singular Gram
matrices when there are fewer columns than rows. -/
theorem ae_dispersion_pos (v : ℝ≥0) (hv : 0 < v) (hm : 2 ≤ m) (hn : 0 < n) :
    ∀ᵐ M ∂matrixLaw m n v, 0 < dispersion M := by
  let i : Fin m := ⟨0, by omega⟩
  let j : Fin m := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j]
  filter_upwards [ae_rows v hv hn hij] with M hM
  refine lt_of_le_of_ne (dispersion_spec M).1 fun he => hM ?_
  obtain ⟨c, hc⟩ := (dispersion_spec M).2.mp he.symm
  rw [← gram_diag M i, ← gram_diag M j, hc]
  simp

/-- A single row always gives zero dispersion, independently of the sample law. -/
theorem dispersion_one_row (M : Fin 1 → Fin n → ℝ) : dispersion M = 0 := by
  simp [dispersion, firstTrace, secondTrace, Matrix.trace, Matrix.diag, sq, Matrix.mul_apply]

/-- With no columns the Gram matrix is zero and so is the sample dispersion. -/
theorem dispersion_no_columns (M : Fin m → Fin 0 → ℝ) : dispersion M = 0 := by
  have h : gram M = 0 := by ext; simp [gram, Matrix.mul_apply]
  simp [dispersion, firstTrace, secondTrace, h]

/-- Under the centred Gaussian product law with variance zero the sample itself is zero
almost surely, hence its dispersion vanishes. -/
theorem ae_zero_of_zero_variance (m n : ℕ) :
    ∀ᵐ M ∂matrixLaw m n 0, M = 0 ∧ dispersion M = 0 := by
  have he (i : Fin m) (a : Fin n) : ∀ᵐ M ∂matrixLaw m n 0, M i a = 0 := by
    have hx : ∀ᵐ x ∂gaussianReal 0 0, x = 0 := by simp
    have hr : ∀ᵐ x ∂rowLaw n 0, x a = 0 :=
      (measurePreserving_eval (fun _ => gaussianReal 0 0) a).quasiMeasurePreserving.ae hx
    exact (measurePreserving_eval (fun _ => rowLaw n 0) i).quasiMeasurePreserving.ae hr
  filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 (he i)] with M hM
  have hz : M = 0 := funext fun i => funext (hM i)
  refine ⟨hz, (dispersion_spec M).2.mpr ⟨0, ?_⟩⟩
  rw [hz]
  ext i j
  simp [gram, Matrix.mul_apply]

end ProbabilityTheory.Wishart
