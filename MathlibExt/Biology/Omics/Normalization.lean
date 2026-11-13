/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# The centered log-ratio (CLR) transform: invariances, information loss, zeros

A composition with `D = card ι` parts (for example the read counts of `D` taxa or genes in one
sample) is recorded as a vector `x : ι → ℝ`. The **centered log-ratio transform** of Aitchison
(1982, 1986) is

  `clr x i = log (x i) - (1 / D) ∑ j, log (x j) = log (x i / g(x))`,

where `g(x)` is the geometric mean of the parts. This file treats CLR as the one normalization of
OMICS-02.1.

## Domain and zero policy

`clr` is defined only on `PosComposition ι`, the strictly positive vectors, so no statement here
evaluates `log 0`. Count data containing zeros enter only through the named pseudocount rule
`withPseudocount c n`, which adds one fixed `c > 0` to every count `n i ≥ 0` before the
transform. Its effects are proved rather than assumed: rescaling the pseudocount with the counts
keeps CLR unchanged; with a fixed pseudocount, rescaling the counts by `t ≠ 1` keeps CLR unchanged
exactly when the counts are all equal, so scale invariance fails in general; and every zero count
gets the smallest CLR coordinate of the sample.

## Main definitions

* `PosComposition ι`: strictly positive vectors indexed by `ι`, the domain of `clr`.
* `PosComposition.smul t ht x`, `PosComposition.perm σ x`: rescaling by `t > 0`, reindexing.
* `clr x`: the centered log-ratio transform.
* `withPseudocount c hc n hn`: the pseudocount zero policy for nonnegative counts.

## Main results

Invariances:
* `clr_smul`: scale invariance, `clr (t • x) = clr x` for `t > 0`.
* `clr_perm`: permutation equivariance, `clr (x ∘ σ) = clr x ∘ σ`.
* `sum_clr`: the image lies in the hyperplane `∑ i, clr x i = 0`.
* `clr_le_clr_iff`: CLR preserves the order of the parts.

Information loss:
* `clr_eq_clr_iff`: the fibre of `clr` through `x` is exactly the ray `{t • x | t > 0}`.
* `exists_clr_eq_sum_eq`: every positive total is attained in every fibre.
* `not_exists_total_of_clr`: no function of `clr x` recovers the total `∑ i, x i`.

Zero policy:
* `clr_withPseudocount_smul`: rescaling counts and pseudocount together leaves CLR unchanged.
* `clr_withPseudocount_smul_eq_iff`: with the pseudocount fixed and `t ≠ 1`, rescaling the counts
  by `t` leaves CLR unchanged if and only if all counts are equal.
* `exists_clr_withPseudocount_smul_ne`: a concrete case where a fixed pseudocount breaks scale
  invariance.
* `clr_withPseudocount_le_of_eq_zero`: a zero count gets the minimal CLR coordinate.

## References

* J. Aitchison, *The statistical analysis of compositional data*, J. R. Stat. Soc. B 44 (1982),
  139–177; and the monograph of the same title (Chapman & Hall, 1986): CLR, scale invariance,
  and the zero problem for log-ratios.
* J. A. Martín-Fernández, C. Barceló-Vidal, V. Pawlowsky-Glahn, *Dealing with zeros and missing
  values in compositional data sets using nonparametric imputation*, Math. Geol. 35 (2003),
  253–278: zero replacement before log-ratio transforms.
* G. B. Gloor et al., *Microbiome datasets are compositional: and this is not optional*,
  Front. Microbiol. 8 (2017), 2224: CLR with a pseudocount for sequencing counts.

## Reuse receipt (API-00)

Searched `MathlibExt`, `CSLibExt`, `WantedExt` and pinned Mathlib for `clr`, `centered log`,
`log-ratio`/`logRatio`, `Aitchison`, `compositional`, `pseudocount`, `CPM`/`TPM`, `size factor`,
and `geometric mean`: no compositional log-ratio transform or zero policy exists. The only hits
are unrelated lemma names (`IsExchangeablePair.measure_le_logRatio` in
`Biology/PopulationGenetics/SelectionScan/CrossPopulationEHH.lean`, a private `logRatio` lemma in
`Probability/Statistics/FisherInformation.lean`, `carlemanGeomMean` for Carleman's inequality).
The file reuses Mathlib's `Real.log`, `Real.exp`, and `Equiv.sum_comp`.
-/

@[expose] public section

open Finset

namespace MathlibExt.Biology.Omics.Normalization

variable {ι : Type*} [Fintype ι]

/-- Strictly positive compositions with parts `ι`: the domain of the CLR transform. -/
abbrev PosComposition (ι : Type*) := {x : ι → ℝ // ∀ i, 0 < x i}

namespace PosComposition

/-- Rescale a positive composition by a positive constant `t` (for example, a different
sequencing depth). -/
def smul (t : ℝ) (ht : 0 < t) (x : PosComposition ι) : PosComposition ι :=
  ⟨t • x.1, fun i => by simpa using mul_pos ht (x.2 i)⟩

/-- Reindex a positive composition by a permutation `σ` of its parts. -/
def perm (σ : Equiv.Perm ι) (x : PosComposition ι) : PosComposition ι :=
  ⟨x.1 ∘ σ, fun i => x.2 (σ i)⟩

end PosComposition

/-- The centered log-ratio transform `clr x i = log (x i) - (1 / D) ∑ j, log (x j)` with
`D = card ι`, defined on strictly positive compositions only. -/
noncomputable def clr (x : PosComposition ι) : ι → ℝ :=
  fun i => Real.log (x.1 i) - (∑ j, Real.log (x.1 j)) / Fintype.card ι

/-! ### Invariances -/

/-- **Scale invariance.** Multiplying every part by the same `t > 0` leaves CLR unchanged. -/
theorem clr_smul (t : ℝ) (ht : 0 < t) (x : PosComposition ι) : clr (x.smul t ht) = clr x := by
  rcases isEmpty_or_nonempty ι with h | h
  · funext i; exact isEmptyElim i
  have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hlog : ∀ j, Real.log (t * x.1 j) = Real.log t + Real.log (x.1 j) :=
    fun j => Real.log_mul ht.ne' (x.2 j).ne'
  funext i
  simp only [clr, PosComposition.smul, Pi.smul_apply, smul_eq_mul, hlog, sum_add_distrib,
    sum_const, card_univ, nsmul_eq_mul]
  field_simp
  ring

/-- **Permutation equivariance.** Reindexing the parts reindexes the CLR coordinates. -/
theorem clr_perm (σ : Equiv.Perm ι) (x : PosComposition ι) : clr (x.perm σ) = clr x ∘ σ := by
  funext i
  simp only [clr, PosComposition.perm, Function.comp_apply]
  rw [Equiv.sum_comp σ (fun j => Real.log (x.1 j))]

/-- The CLR coordinates sum to zero. -/
theorem sum_clr (x : PosComposition ι) : ∑ i, clr x i = 0 := by
  rcases isEmpty_or_nonempty ι with h | h
  · simp
  have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [clr, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
  field_simp
  ring

/-- CLR preserves the order of the parts. -/
theorem clr_le_clr_iff (x : PosComposition ι) (i j : ι) : clr x i ≤ clr x j ↔ x.1 i ≤ x.1 j := by
  simp only [clr, sub_le_sub_iff_right]
  exact Real.log_le_log_iff (x.2 i) (x.2 j)

/-! ### Information loss -/

/-- **Fibres of CLR.** Two positive compositions have the same CLR transform if and only if one
is a positive multiple of the other. -/
theorem clr_eq_clr_iff {x y : PosComposition ι} :
    clr x = clr y ↔ ∃ t, ∃ ht : 0 < t, y = x.smul t ht := by
  constructor
  · intro h
    set c := (∑ j, Real.log (y.1 j)) / Fintype.card ι - (∑ j, Real.log (x.1 j)) / Fintype.card ι
    refine ⟨Real.exp c, Real.exp_pos c, Subtype.ext ?_⟩
    funext i
    have hi := congrFun h i
    simp only [clr] at hi
    simp only [PosComposition.smul, Pi.smul_apply, smul_eq_mul]
    calc y.1 i = Real.exp (Real.log (y.1 i)) := (Real.exp_log (y.2 i)).symm
      _ = Real.exp (c + Real.log (x.1 i)) := by congr 1; simp only [c]; linarith
      _ = Real.exp c * x.1 i := by rw [Real.exp_add, Real.exp_log (x.2 i)]
  · rintro ⟨t, ht, rfl⟩
    exact (clr_smul t ht x).symm

/-- Every positive total is attained in every CLR fibre: for any positive composition `x` and any
`T > 0` there is a composition with the same CLR transform and total `T`. -/
theorem exists_clr_eq_sum_eq [Nonempty ι] (x : PosComposition ι) {T : ℝ} (hT : 0 < T) :
    ∃ y : PosComposition ι, clr y = clr x ∧ ∑ i, y.1 i = T := by
  have hS : 0 < ∑ i, x.1 i := sum_pos (fun i _ => x.2 i) univ_nonempty
  refine ⟨x.smul (T / ∑ i, x.1 i) (div_pos hT hS), clr_smul _ _ x, ?_⟩
  simp only [PosComposition.smul, Pi.smul_apply, smul_eq_mul, ← mul_sum]
  field_simp

/-- **CLR forgets the total.** With at least one part, no function of the CLR transform recovers
the total `∑ i, x i` of a positive composition. -/
theorem not_exists_total_of_clr [Nonempty ι] :
    ¬ ∃ f : (ι → ℝ) → ℝ, ∀ x : PosComposition ι, f (clr x) = ∑ i, x.1 i := by
  rintro ⟨f, hf⟩
  let x : PosComposition ι := ⟨fun _ => 1, fun _ => one_pos⟩
  have h1 := hf x
  have h2 := hf (x.smul 2 two_pos)
  rw [clr_smul, h1] at h2
  -- `h2 : card ι = 2 * card ι`, impossible for a nonempty index type
  simp [x, PosComposition.smul] at h2

/-! ### Zero policy: a fixed pseudocount -/

/-- **Pseudocount zero policy.** Nonnegative counts `n` (zeros allowed) become the strictly
positive composition `n + c` for a fixed pseudocount `c > 0`; CLR is then applied to this. -/
def withPseudocount (c : ℝ) (hc : 0 < c) (n : ι → ℝ) (hn : ∀ i, 0 ≤ n i) : PosComposition ι :=
  ⟨fun i => n i + c, fun i => add_pos_of_nonneg_of_pos (hn i) hc⟩

/-- Rescaling the counts by `t > 0` and the pseudocount by the same `t` leaves CLR unchanged. -/
theorem clr_withPseudocount_smul (c : ℝ) (hc : 0 < c) (t : ℝ) (ht : 0 < t) (n : ι → ℝ)
    (hn : ∀ i, 0 ≤ n i) :
    clr (withPseudocount (t * c) (mul_pos ht hc) (t • n)
        (fun i => by simpa using mul_nonneg ht.le (hn i))) =
      clr (withPseudocount c hc n hn) := by
  have : withPseudocount (t * c) (mul_pos ht hc) (t • n)
      (fun i => by simpa using mul_nonneg ht.le (hn i)) =
      (withPseudocount c hc n hn).smul t ht := by
    apply Subtype.ext
    funext i
    simp only [withPseudocount, PosComposition.smul, Pi.smul_apply, smul_eq_mul]
    ring
  rw [this, clr_smul]

/-- **Scale invariance under a fixed pseudocount.** With the pseudocount `c` fixed and a scale
factor `t ≠ 1`, rescaling the counts by `t` leaves CLR unchanged if and only if all counts are
equal. -/
theorem clr_withPseudocount_smul_eq_iff (c : ℝ) (hc : 0 < c) (t : ℝ) (ht : 0 < t) (ht1 : t ≠ 1)
    (n : ι → ℝ) (hn : ∀ i, 0 ≤ n i) :
    clr (withPseudocount c hc (t • n) (fun i => by simpa using mul_nonneg ht.le (hn i))) =
        clr (withPseudocount c hc n hn) ↔ ∀ i j, n i = n j := by
  constructor
  · intro h i j
    obtain ⟨s, _hs, hy⟩ := clr_eq_clr_iff.1 h.symm
    have hi := congrFun (congrArg Subtype.val hy) i
    have hj := congrFun (congrArg Subtype.val hy) j
    simp only [withPseudocount, PosComposition.smul, Pi.smul_apply, smul_eq_mul] at hi hj
    -- `hi : t * n i + c = s * (n i + c)`, `hj : t * n j + c = s * (n j + c)`
    by_contra hne
    have hts : t = s := by
      have : (t - s) * (n i - n j) = 0 := by linear_combination hi - hj
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne))
    subst hts
    have : (t - 1) * c = 0 := by linear_combination -hi
    exact ht1 (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hc.ne'))
  · intro hconst
    rcases isEmpty_or_nonempty ι with h | ⟨⟨i₀⟩⟩
    · funext i; exact isEmptyElim i
    have hpos : 0 < t * n i₀ + c := add_pos_of_nonneg_of_pos (mul_nonneg ht.le (hn i₀)) hc
    refine clr_eq_clr_iff.2 ⟨(n i₀ + c) / (t * n i₀ + c),
      div_pos (add_pos_of_nonneg_of_pos (hn i₀) hc) hpos, Subtype.ext (funext fun i => ?_)⟩
    simp only [withPseudocount, PosComposition.smul, Pi.smul_apply, smul_eq_mul, hconst i i₀]
    exact (div_mul_cancel₀ _ hpos.ne').symm

/-- **A fixed pseudocount breaks scale invariance.** For the counts `(0, 1)` with pseudocount
`1`, doubling the counts changes the CLR transform. -/
theorem exists_clr_withPseudocount_smul_ne :
    ∃ (n : Fin 2 → ℝ) (hn : ∀ i, 0 ≤ n i) (h2n : ∀ i, 0 ≤ ((2 : ℝ) • n) i),
      clr (withPseudocount 1 one_pos ((2 : ℝ) • n) h2n) ≠ clr (withPseudocount 1 one_pos n hn) := by
  refine ⟨![0, 1], fun i => by fin_cases i <;> norm_num, fun i => by fin_cases i <;> norm_num, ?_⟩
  intro h
  have h0 := congrFun h 0
  simp only [clr, withPseudocount, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fintype.card_fin] at h0
  norm_num at h0
  have : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  linarith

/-- Under the pseudocount policy a zero count receives the smallest CLR coordinate of the
sample. -/
theorem clr_withPseudocount_le_of_eq_zero (c : ℝ) (hc : 0 < c) (n : ι → ℝ) (hn : ∀ i, 0 ≤ n i)
    {i : ι} (hi : n i = 0) (j : ι) :
    clr (withPseudocount c hc n hn) i ≤ clr (withPseudocount c hc n hn) j := by
  rw [clr_le_clr_iff]
  simp only [withPseudocount, hi, zero_add, le_add_iff_nonneg_left]
  exact hn j

end MathlibExt.Biology.Omics.Normalization
