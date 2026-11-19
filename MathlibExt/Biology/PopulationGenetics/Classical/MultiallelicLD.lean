/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Fintype.BigOperators
public import MathlibExt.Biology.PopulationGenetics.Linkage
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Multiallelic two-locus linkage disequilibrium

For finite allele sets at two loci, write `x (i, j)` for the frequency of
haplotype `(i, j)`, `p i = ∑ l, x (i, l)` and `q j = ∑ k, x (k, j)` for the
allele frequencies, and
`D i j = x (i, j) - p i * q j` for the pairwise linkage disequilibrium.

Under random mating with recombination fraction `r`, allele frequencies are
conserved and every disequilibrium decays by the same factor:
`D' i j = (1 - r) * D i j`. Hence `D_t i j = (1 - r)^t * D_0 i j`, and
`D_t i j → 0` in the algebraic range `0 < r ≤ 1`. The biological range for a
two-locus recombination fraction is `0 ≤ r ≤ 1 / 2`; values
`1 / 2 < r ≤ 1` are an algebraic extension of the recurrence, not a
recombination fraction arising from random mating. This matches the
distinction made in the biallelic `Linkage` API. For each fixed allele at
either locus, the disequilibria sum to zero over the alleles at the other
locus. The biallelic case agrees with `Linkage.linkageDiseq`.

The named operators `alleleFreqFst`, `alleleFreqSnd`, `linkageDiseq`, and
`recombine` are defined first. The decay results are proved once for any
operator satisfying the displayed random-mating recursion, then restated
directly for `recombine` and `linkageDiseq` under the canonical theorem names.

## References

* J. Felsenstein, *Theoretical Evolutionary Genetics*, Section I.10.
-/

@[expose] public section

open scoped BigOperators

namespace MathlibExt.Biology.PopulationGenetics.Classical.MultiallelicLD

/-! ### Named multiallelic operators -/

section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The frequency `∑ l, x (i, l)` of allele `i` at the first locus. -/
def alleleFreqFst (x : ι × κ → ℝ) (i : ι) : ℝ := ∑ l, x (i, l)

/-- The frequency `∑ k, x (k, j)` of allele `j` at the second locus. -/
def alleleFreqSnd (x : ι × κ → ℝ) (j : κ) : ℝ := ∑ k, x (k, j)

/-- The pairwise multiallelic linkage disequilibrium
`D i j = x (i, j) - p i * q j`. -/
def linkageDiseq (x : ι × κ → ℝ) (i : ι) (j : κ) : ℝ :=
  x (i, j) - (∑ l, x (i, l)) * (∑ k, x (k, j))

/-- One generation of random mating with recombination fraction `r`:
a fraction `1 - r` of haplotypes is copied, and a fraction `r` is formed by
independent assortment of the two loci. -/
def recombine (r : ℝ) (x : ι × κ → ℝ) (g : ι × κ) : ℝ :=
  (1 - r) * x g + r * ((∑ l, x (g.1, l)) * (∑ k, x (k, g.2)))

end

/-! ### Generic recurrence form

The following theorems are the generic forms for an operator satisfying the
random-mating recurrence. The canonical direct statements for `recombine` and
`linkageDiseq` follow after the biallelic compatibility lemmas. -/


/-- Random mating with recombination fraction `r` conserves the allele frequencies at the first
locus. Haplotypes are pairs `(i, j)` of alleles `i : ι` at the first locus and `j : κ` at the
second; `x` are haplotype frequencies summing to `1`, and `R` is one generation of random mating,
`R y g = (1 - r) * y g + r * ((∑ l, y (g.1, l)) * (∑ k, y (k, g.2)))`. -/
private theorem alleleFreqFst_recombine_of_eq {ι κ : Type*} [Fintype ι] [Fintype κ] (r : ℝ)
    (R : (ι × κ → ℝ) → ι × κ → ℝ)
    (hR : ∀ y g, R y g = (1 - r) * y g + r * ((∑ l, y (g.1, l)) * (∑ k, y (k, g.2))))
    (x : ι × κ → ℝ) (hx : ∑ g, x g = 1) (i : ι) :
    ∑ l, R x (i, l) = ∑ l, x (i, l) := by
  have hsum : (∑ l : κ, ∑ k : ι, x (k, l)) = 1 := by
    rw [Finset.sum_comm]
    have h := hx
    rw [Fintype.sum_prod_type] at h
    exact h
  simp only [hR]
  rw [Finset.sum_add_distrib]
  have h1 : (∑ l : κ, (1 - r) * x (i, l)) = (1 - r) * (∑ l : κ, x (i, l)) := by
    rw [Finset.mul_sum]
  rw [h1]
  have hfactor : ∀ l : κ, r * ((∑ l', x (i, l')) * (∑ k, x (k, l))) =
      (r * (∑ l', x (i, l'))) * (∑ k, x (k, l)) := fun l => by ring
  simp only [hfactor]
  rw [← Finset.mul_sum]
  have h2 : (r * (∑ l', x (i, l'))) * (∑ l : κ, ∑ k : ι, x (k, l)) =
      r * ((∑ l', x (i, l')) * (∑ l : κ, ∑ k : ι, x (k, l))) := by ring
  rw [h2, hsum]
  ring

/-- Random mating with recombination fraction `r` conserves the allele frequencies at the second
locus (same setting as `alleleFreqFst_recombine_of_eq`). -/
private theorem alleleFreqSnd_recombine_of_eq {ι κ : Type*} [Fintype ι] [Fintype κ] (r : ℝ)
    (R : (ι × κ → ℝ) → ι × κ → ℝ)
    (hR : ∀ y g, R y g = (1 - r) * y g + r * ((∑ l, y (g.1, l)) * (∑ k, y (k, g.2))))
    (x : ι × κ → ℝ) (hx : ∑ g, x g = 1) (j : κ) :
    ∑ k, R x (k, j) = ∑ k, x (k, j) := by
  have hsum : (∑ k : ι, ∑ l : κ, x (k, l)) = 1 := by
    have h := hx
    rw [Fintype.sum_prod_type] at h
    exact h
  simp only [hR]
  rw [Finset.sum_add_distrib]
  have h1 : (∑ k : ι, (1 - r) * x (k, j)) = (1 - r) * (∑ k : ι, x (k, j)) := by
    rw [Finset.mul_sum]
  rw [h1]
  have hfactor : ∀ k : ι, r * ((∑ l, x (k, l)) * (∑ k', x (k', j))) =
      (r * (∑ k', x (k', j))) * (∑ l, x (k, l)) := fun k => by ring
  simp only [hfactor]
  rw [← Finset.mul_sum]
  rw [hsum]
  ring

/-- **Multiallelic linkage disequilibrium decays by the factor `1 - r`.** For every pair of
alleles `(i, j)`, the disequilibrium `D i j = x (i, j) - p i * q j`, with allele frequencies
`p i = ∑ l, x (i, l)` and `q j = ∑ k, x (k, j)`, satisfies `D' i j = (1 - r) * D i j` after one
generation of random mating `R` (setting of `alleleFreqFst_recombine_of_eq`; every real `r`). -/
private theorem linkageDiseq_recombine_of_eq {ι κ : Type*} [Fintype ι] [Fintype κ] (r : ℝ)
    (R : (ι × κ → ℝ) → ι × κ → ℝ)
    (hR : ∀ y g, R y g = (1 - r) * y g + r * ((∑ l, y (g.1, l)) * (∑ k, y (k, g.2))))
    (x : ι × κ → ℝ) (hx : ∑ g, x g = 1) (i : ι) (j : κ) :
    R x (i, j) - (∑ l, R x (i, l)) * (∑ k, R x (k, j)) =
      (1 - r) * (x (i, j) - (∑ l, x (i, l)) * (∑ k, x (k, j))) := by
  have h1 := alleleFreqFst_recombine_of_eq r R hR x hx i
  have h2 := alleleFreqSnd_recombine_of_eq r R hR x hx j
  rw [h1, h2, hR]
  ring

/-- For each second-locus allele `j`, the multiallelic disequilibria sum to zero over the
first-locus alleles: `∑ i, (x (i, j) - p i * q j) = 0` when the haplotype frequencies sum
to `1`. -/
private theorem sum_linkageDiseq_fst_unfolded {ι κ : Type*} [Fintype ι] [Fintype κ] (x : ι × κ → ℝ)
    (hx : ∑ g, x g = 1) (j : κ) :
    ∑ i, (x (i, j) - (∑ l, x (i, l)) * (∑ k, x (k, j))) = 0 := by
  have hsum : (∑ i : ι, ∑ l : κ, x (i, l)) = 1 := by
    have h := hx
    rw [Fintype.sum_prod_type] at h
    exact h
  rw [Finset.sum_sub_distrib]
  have hfactor : (∑ i : ι, (∑ l, x (i, l)) * (∑ k, x (k, j))) =
      (∑ i : ι, ∑ l : κ, x (i, l)) * (∑ k, x (k, j)) := by
    rw [Finset.sum_mul]
  rw [hfactor, hsum]
  simp

/-- For each first-locus allele `i`, the multiallelic disequilibria sum to zero over the
second-locus alleles: `∑ j, (x (i, j) - p i * q j) = 0` when the haplotype frequencies sum
to `1`. -/
private theorem sum_linkageDiseq_snd_unfolded {ι κ : Type*} [Fintype ι] [Fintype κ] (x : ι × κ → ℝ)
    (hx : ∑ g, x g = 1) (i : ι) :
    ∑ j, (x (i, j) - (∑ l, x (i, l)) * (∑ k, x (k, j))) = 0 := by
  have hsum : (∑ j : κ, ∑ k : ι, x (k, j)) = 1 := by
    rw [Finset.sum_comm]
    have h := hx
    rw [Fintype.sum_prod_type] at h
    exact h
  rw [Finset.sum_sub_distrib]
  have hfactor : (∑ j : κ, (∑ l, x (i, l)) * (∑ k, x (k, j))) =
      (∑ l, x (i, l)) * (∑ j : κ, ∑ k : ι, x (k, j)) := by
    rw [Finset.mul_sum]
  rw [hfactor, hsum]
  simp

/-- After `t` generations of random mating `R` (setting of `alleleFreqFst_recombine_of_eq`),
the multiallelic disequilibrium is `D_t i j = (1 - r) ^ t * D_0 i j` (every real `r`). -/
private theorem linkageDiseq_iterate_of_eq {ι κ : Type*} [Fintype ι] [Fintype κ] (r : ℝ)
    (R : (ι × κ → ℝ) → ι × κ → ℝ)
    (hR : ∀ y g, R y g = (1 - r) * y g + r * ((∑ l, y (g.1, l)) * (∑ k, y (k, g.2))))
    (x : ι × κ → ℝ) (hx : ∑ g, x g = 1) (t : ℕ) (i : ι) (j : κ) :
    R^[t] x (i, j) - (∑ l, R^[t] x (i, l)) * (∑ k, R^[t] x (k, j)) =
      (1 - r) ^ t * (x (i, j) - (∑ l, x (i, l)) * (∑ k, x (k, j))) := by
  have htotal : ∀ y : ι × κ → ℝ, (∑ g, y g = 1) → ∑ g, R y g = 1 := by
    intro y hy
    rw [Fintype.sum_prod_type]
    have hall : ∀ a : ι, (∑ l, R y (a, l)) = ∑ l, y (a, l) :=
      fun a => alleleFreqFst_recombine_of_eq r R hR y hy a
    simp only [hall]
    have h := hy
    rw [Fintype.sum_prod_type] at h
    exact h
  have htot : ∀ t : ℕ, ∑ g, R^[t] x g = 1 := by
    intro t
    induction t with
    | zero => simpa using hx
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact htotal _ ih
  induction t with
  | zero => simp
  | succ n ih =>
    have hytot := htot n
    have hstep := linkageDiseq_recombine_of_eq r R hR (R^[n] x) hytot i j
    have hrew : R^[n.succ] x = R (R^[n] x) := Function.iterate_succ_apply' R n x
    rw [hrew]
    rw [hstep]
    rw [ih]
    ring

/-- **Multiallelic linkage disequilibrium tends to `0`** under repeated
iteration of the recurrence whenever `0 < r ≤ 1` algebraically (setting of
`alleleFreqFst_recombine_of_eq`). For a biological two-locus recombination
fraction the range is `0 < r ≤ 1 / 2`; the larger values are only the
algebraic extension of the same recurrence. -/
private theorem tendsto_linkageDiseq_iterate_of_eq {ι κ : Type*} [Fintype ι] [Fintype κ] (r : ℝ)
    (R : (ι × κ → ℝ) → ι × κ → ℝ)
    (hR : ∀ y g, R y g = (1 - r) * y g + r * ((∑ l, y (g.1, l)) * (∑ k, y (k, g.2))))
    (x : ι × κ → ℝ) (hx : ∑ g, x g = 1) (hr0 : 0 < r) (hr1 : r ≤ 1) (i : ι) (j : κ) :
    Filter.Tendsto
      (fun t : ℕ => R^[t] x (i, j) - (∑ l, R^[t] x (i, l)) * (∑ k, R^[t] x (k, j)))
      Filter.atTop (nhds 0) := by
  have heq : ∀ t : ℕ, R^[t] x (i, j) - (∑ l, R^[t] x (i, l)) * (∑ k, R^[t] x (k, j)) =
      (1 - r) ^ t * (x (i, j) - (∑ l, x (i, l)) * (∑ k, x (k, j))) :=
    fun t => linkageDiseq_iterate_of_eq r R hR x hx t i j
  have hfun : (fun t : ℕ => R^[t] x (i, j) - (∑ l, R^[t] x (i, l)) * (∑ k, R^[t] x (k, j))) =
      (fun t : ℕ => (1 - r) ^ t * (x (i, j) - (∑ l, x (i, l)) * (∑ k, x (k, j)))) :=
    funext heq
  rw [hfun]
  have hnonneg : 0 ≤ 1 - r := sub_nonneg.mpr hr1
  have hlt : (1 - r) < 1 := sub_lt_self 1 hr0
  have hpow : Filter.Tendsto (fun t : ℕ => (1 - r) ^ t) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hnonneg hlt
  have hlim := hpow.mul_const (x (i, j) - (∑ l, x (i, l)) * (∑ k, x (k, j)))
  simpa using hlim

/-- **Biallelic instance.** For two alleles at each locus (`Bool × Bool`, `true` = `A`, `B`) and
haplotype frequencies summing to `1`, the disequilibrium of the `AB` haplotype,
`x_AB - p_A * p_B`, equals `x_AB * x_ab - x_Ab * x_aB`. -/
private theorem linkageDiseq_true_true_unfolded (x : Bool × Bool → ℝ) (hx : ∑ g, x g = 1) :
    x (true, true) - (∑ l, x (true, l)) * (∑ k, x (k, true)) =
      x (true, true) * x (false, false) - x (true, false) * x (false, true) := by
  have hx' : x (true, true) + x (true, false) + x (false, true) + x (false, false) = 1 := by
    have h := hx
    rw [Fintype.sum_prod_type] at h
    simp only [Fintype.sum_bool] at h
    linear_combination h
  have e1 : (∑ l : Bool, x (true, l)) = x (true, true) + x (true, false) :=
    Fintype.sum_bool _
  have e2 : (∑ k : Bool, x (k, true)) = x (true, true) + x (false, true) :=
    Fintype.sum_bool _
  rw [e1, e2]
  linear_combination -(x (true, true)) * hx'

/-! ### Biallelic compatibility and direct operator API -/

/-- The named multiallelic recombination map agrees definitionally with the
biallelic `Linkage.recombine` on `Bool × Bool`. -/
theorem recombine_bool (r : ℝ) (y : Bool × Bool → ℝ) :
    recombine r y =
      MathlibExt.Biology.PopulationGenetics.Linkage.recombine r y := rfl

/-- In the biallelic case, the pairwise disequilibrium for `(true, true)` is
Atlas's `Linkage.linkageDiseq`. -/
theorem linkageDiseq_bool {x : Bool × Bool → ℝ} (hx : ∑ g, x g = 1) :
    linkageDiseq x true true =
      MathlibExt.Biology.PopulationGenetics.Linkage.linkageDiseq x :=
  linkageDiseq_true_true_unfolded x hx

/-- Random mating conserves allele frequencies at the first locus. -/
theorem alleleFreqFst_recombine {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r : ℝ) (x : ι × κ → ℝ) (hx : ∑ g, x g = 1) (i : ι) :
    alleleFreqFst (recombine r x) i = alleleFreqFst x i :=
  alleleFreqFst_recombine_of_eq r (recombine r) (fun _ _ => rfl) x hx i

/-- Random mating conserves allele frequencies at the second locus. -/
theorem alleleFreqSnd_recombine {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r : ℝ) (x : ι × κ → ℝ) (hx : ∑ g, x g = 1) (j : κ) :
    alleleFreqSnd (recombine r x) j = alleleFreqSnd x j :=
  alleleFreqSnd_recombine_of_eq r (recombine r) (fun _ _ => rfl) x hx j

/-- One generation of random mating multiplies each disequilibrium by
`1 - r`. -/
theorem linkageDiseq_recombine {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r : ℝ) (x : ι × κ → ℝ) (hx : ∑ g, x g = 1) (i : ι) (j : κ) :
    linkageDiseq (recombine r x) i j = (1 - r) * linkageDiseq x i j :=
  linkageDiseq_recombine_of_eq r (recombine r) (fun _ _ => rfl) x hx i j

/-- For each second-locus allele, the disequilibria sum to zero over the
first-locus alleles. -/
theorem sum_linkageDiseq_fst {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι × κ → ℝ) (hx : ∑ g, x g = 1) (j : κ) :
    ∑ i, linkageDiseq x i j = 0 :=
  sum_linkageDiseq_fst_unfolded x hx j

/-- For each first-locus allele, the disequilibria sum to zero over the
second-locus alleles. -/
theorem sum_linkageDiseq_snd {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι × κ → ℝ) (hx : ∑ g, x g = 1) (i : ι) :
    ∑ j, linkageDiseq x i j = 0 :=
  sum_linkageDiseq_snd_unfolded x hx i

/-- After `t` generations, each disequilibrium has decayed by
`(1 - r) ^ t`. -/
theorem linkageDiseq_iterate {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r : ℝ) (x : ι × κ → ℝ) (hx : ∑ g, x g = 1) (t : ℕ) (i : ι) (j : κ) :
    linkageDiseq ((recombine r)^[t] x) i j = (1 - r) ^ t * linkageDiseq x i j :=
  linkageDiseq_iterate_of_eq r (recombine r) (fun _ _ => rfl) x hx t i j

/-- Linkage disequilibrium converges to zero in the algebraic range
`0 < r ≤ 1`; biological recombination fractions have `r ≤ 1 / 2`. -/
theorem tendsto_linkageDiseq_iterate {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r : ℝ) (x : ι × κ → ℝ) (hx : ∑ g, x g = 1) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (i : ι) (j : κ) :
    Filter.Tendsto (fun t : ℕ => linkageDiseq ((recombine r)^[t] x) i j)
      Filter.atTop (nhds 0) :=
  tendsto_linkageDiseq_iterate_of_eq r (recombine r) (fun _ _ => rfl) x hx hr0 hr1 i j


end MathlibExt.Biology.PopulationGenetics.Classical.MultiallelicLD
