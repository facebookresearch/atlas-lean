/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Bond percolation on the rooted `b`-ary tree, via the generating function

In bond percolation with parameter `p` on the rooted tree in which every vertex has `b` children,
the open cluster of the root is a Galton–Watson tree with offspring law `Binomial(b, p)`, whose
generating function is `treeGF b p s = (1 - p + p s)^b`. This file works with that generating
function directly: it defines the extinction probability as the least fixed point of `treeGF b p`
in `[0, 1]`, the survival probability as its complement, and the critical parameter `treePc b` as
the supremum of the parameters with survival probability `0`, and proves `treePc b = 1 / b`.

The identification of `survivalProb b p` with the probability that the root's open cluster is
infinite (the Galton–Watson extinction theorem applied to the percolation cluster) is not
formalized here. For a general offspring law, the Galton–Watson process and its extinction
probability as a least fixed point are in `MathlibExt.Probability.BranchingProcess.GaltonWatson`
(`MathlibExt.Probability.GaltonWatson.isLeast_extinctionProb`,
`MathlibExt.Probability.GaltonWatson.extinctionProb_eq_one_iff`); no bridge between the two is
proved.

## Main definitions

* `StatMech.Percolation.binomialOffspringPMF`, `StatMech.Percolation.treeGF`: the binomial offspring
  law and its generating function.
* `StatMech.Percolation.extinctionProb`, `StatMech.Percolation.survivalProb`: the least fixed point
  of `treeGF b p` in `[0, 1]` and its complement.
* `StatMech.Percolation.treePc`: the critical parameter defined from `survivalProb`.

## Main results

* `StatMech.Percolation.survivalProb_eq_zero_of_subcritical`,
  `StatMech.Percolation.survivalProb_pos_of_supercritical`: the survival probability is `0` when
  the mean `b p` is below `1` and positive when it is above `1`.
* `StatMech.Percolation.treePc_eq`: `treePc b = 1 / b` for `b ≥ 1`.

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer (1999), Section 10.1.
* R. Lyons, Y. Peres, *Probability on Trees and Networks*, Cambridge (2016), Chapter 5.
-/

@[expose] public section

open Set Finset
open scoped NNReal

namespace StatMech

namespace Percolation

/-- The `Binomial(b, p)` probability mass function `k ↦ (b choose k) p^k (1 - p)^(b - k)`. -/
noncomputable def binomialOffspringPMF (b : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (b.choose k : ℝ) * p ^ k * (1 - p) ^ (b - k)

/-- The generating function `s ↦ (1 - p + p s)^b` of the `Binomial(b, p)` offspring law. -/
noncomputable def treeGF (b : ℕ) (p : ℝ) (s : ℝ) : ℝ := (1 - p + p * s) ^ b

@[simp] lemma treeGF_one (b : ℕ) (p : ℝ) : treeGF b p 1 = 1 := by simp [treeGF]

lemma treeGF_continuous (b : ℕ) (p : ℝ) : Continuous (treeGF b p) := by
  unfold treeGF; fun_prop

/-- `treeGF b p` is the generating function `∑ k, P(k) s^k` of `binomialOffspringPMF b p`. -/
lemma treeGF_eq_pgf (b : ℕ) (p s : ℝ) :
    treeGF b p s = ∑ k ∈ range (b + 1), binomialOffspringPMF b p k * s ^ k := by
  unfold treeGF binomialOffspringPMF
  have hcomm : (1 - p + p * s) = (p * s + (1 - p)) := by ring
  rw [hcomm, add_pow]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [mul_pow]; ring

/-- The binomial weights sum to `1`. -/
lemma binomialOffspringPMF_sum (b : ℕ) (p : ℝ) :
    ∑ k ∈ range (b + 1), binomialOffspringPMF b p k = 1 := by
  have h := treeGF_eq_pgf b p 1
  simp only [treeGF_one, one_pow, mul_one] at h
  exact h.symm

/-- Derivative of `treeGF b p`. -/
lemma treeGF_hasDerivAt (b : ℕ) (p s : ℝ) :
    HasDerivAt (treeGF b p) ((b : ℝ) * (1 - p + p * s) ^ (b - 1) * p) s := by
  have hu : HasDerivAt (fun s => 1 - p + p * s) p s := by
    simpa using ((hasDerivAt_id s).const_mul p).const_add (1 - p)
  convert hu.pow b using 1
  funext x; simp [treeGF]

/-- `treeGF b p` has derivative `b p` (the mean offspring number) at `1`. -/
lemma treeGF_hasDerivAt_one (b : ℕ) (p : ℝ) :
    HasDerivAt (treeGF b p) ((b : ℝ) * p) 1 := by
  have h := treeGF_hasDerivAt b p 1
  have heq : (b : ℝ) * (1 - p + p * 1) ^ (b - 1) * p = (b : ℝ) * p := by ring_nf
  rwa [heq] at h

/-- The mean `b p` of the `Binomial(b, p)` offspring law. -/
noncomputable def treeMean (b : ℕ) (p : ℝ) : ℝ := (b : ℝ) * p

/-- The mean is the derivative of the generating function at `1`. -/
lemma treeMean_eq_deriv (b : ℕ) (p : ℝ) :
    treeMean b p = deriv (treeGF b p) 1 :=
  (treeGF_hasDerivAt_one b p).deriv.symm

/-- The fixed points of `treeGF b p` in `[0, 1]`. -/
def fixedSet (b : ℕ) (p : ℝ) : Set ℝ := {s | s ∈ Icc (0 : ℝ) 1 ∧ treeGF b p s = s}

lemma one_mem_fixedSet (b : ℕ) (p : ℝ) : (1 : ℝ) ∈ fixedSet b p :=
  ⟨⟨zero_le_one, le_refl 1⟩, by simp⟩

lemma fixedSet_nonempty (b : ℕ) (p : ℝ) : (fixedSet b p).Nonempty :=
  ⟨1, one_mem_fixedSet b p⟩

lemma fixedSet_bddBelow (b : ℕ) (p : ℝ) : BddBelow (fixedSet b p) :=
  ⟨0, fun _ hs => hs.1.1⟩

lemma fixedSet_isClosed (b : ℕ) (p : ℝ) : IsClosed (fixedSet b p) :=
  isClosed_Icc.inter (isClosed_eq (treeGF_continuous b p) continuous_id)

/-- The extinction probability: the least fixed point of `treeGF b p` in `[0, 1]`. See also
`MathlibExt.Probability.GaltonWatson.extinctionProb` (defined from the process; least fixed point
by `MathlibExt.Probability.GaltonWatson.isLeast_extinctionProb`). -/
noncomputable def extinctionProb (b : ℕ) (p : ℝ) : ℝ := sInf (fixedSet b p)

/-- The extinction probability is a fixed point in `[0, 1]`. -/
lemma extinctionProb_mem (b : ℕ) (p : ℝ) : extinctionProb b p ∈ fixedSet b p :=
  (fixedSet_isClosed b p).csInf_mem (fixedSet_nonempty b p) (fixedSet_bddBelow b p)

lemma extinctionProb_isFixed (b : ℕ) (p : ℝ) :
    treeGF b p (extinctionProb b p) = extinctionProb b p :=
  (extinctionProb_mem b p).2

lemma extinctionProb_mem_Icc (b : ℕ) (p : ℝ) : extinctionProb b p ∈ Icc (0 : ℝ) 1 :=
  (extinctionProb_mem b p).1

lemma extinctionProb_nonneg (b : ℕ) (p : ℝ) : 0 ≤ extinctionProb b p :=
  (extinctionProb_mem_Icc b p).1

lemma extinctionProb_le_one (b : ℕ) (p : ℝ) : extinctionProb b p ≤ 1 :=
  (extinctionProb_mem_Icc b p).2

/-- The survival probability `1 - extinctionProb b p`. -/
noncomputable def survivalProb (b : ℕ) (p : ℝ) : ℝ := 1 - extinctionProb b p

lemma survivalProb_nonneg (b : ℕ) (p : ℝ) : 0 ≤ survivalProb b p := by
  unfold survivalProb; linarith [extinctionProb_le_one b p]

lemma survivalProb_pos_iff (b : ℕ) (p : ℝ) :
    0 < survivalProb b p ↔ extinctionProb b p < 1 := by
  unfold survivalProb; constructor <;> intro h <;> linarith

/-- `treeGF b p 0 = (1 - p)^b ≥ 0` for `p ≤ 1`. -/
lemma treeGF_zero_nonneg (b : ℕ) {p : ℝ} (hp1 : p ≤ 1) : 0 ≤ treeGF b p 0 := by
  unfold treeGF
  have : (0 : ℝ) ≤ 1 - p + p * 0 := by simp; linarith
  positivity

/-- If `b p > 1`, `treeGF b p` has a fixed point in `[0, 1)`. -/
lemma supercritical_fixed (b : ℕ) {p : ℝ} (hp1 : p ≤ 1) (hmean : 1 < (b : ℝ) * p) :
    ∃ q ∈ Ico (0 : ℝ) 1, treeGF b p q = q := by
  set g : ℝ → ℝ := fun s => treeGF b p s - s with hg
  have hg1 : g 1 = 0 := by simp [hg]
  have hgder : HasDerivAt g ((b : ℝ) * p - 1) 1 := by
    have := (treeGF_hasDerivAt_one b p).sub (hasDerivAt_id 1)
    exact this
  have hslope : Filter.Tendsto (slope g 1) (nhdsWithin 1 {1}ᶜ) (nhds ((b : ℝ) * p - 1)) :=
    hasDerivAt_iff_tendsto_slope.mp hgder
  have hpos : (0 : ℝ) < (b : ℝ) * p - 1 := by linarith
  have hev : ∀ᶠ y in nhdsWithin 1 {1}ᶜ, 0 < slope g 1 y := hslope.eventually_const_lt hpos
  have hsub : nhdsWithin 1 (Ioo (0 : ℝ) 1) ≤ nhdsWithin 1 {1}ᶜ := by
    refine nhdsWithin_mono _ (fun x hx => ?_)
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_lt hx.2
  have hev2 : ∀ᶠ y in nhdsWithin 1 (Ioo (0 : ℝ) 1), 0 < slope g 1 y := hev.filter_mono hsub
  have : (nhdsWithin (1 : ℝ) (Ioo 0 1)).NeBot := right_nhdsWithin_Ioo_neBot (by norm_num)
  obtain ⟨y, hyslope, hymem⟩ := (hev2.and self_mem_nhdsWithin).exists
  have hy01 : y ∈ Ioo (0 : ℝ) 1 := hymem
  have hylt1 : y < 1 := hy01.2
  have hy0 : 0 < y := hy01.1
  have hyne : y - 1 ≠ 0 := by intro h; nlinarith
  have hslope_eq : slope g 1 y = (g y - g 1) / (y - 1) := slope_def_field g 1 y
  have hgy_neg : g y < 0 := by
    rw [hslope_eq, hg1, sub_zero] at hyslope
    have hyneg : y - 1 < 0 := by linarith
    by_contra hcon
    have hge : 0 ≤ g y := le_of_not_gt hcon
    have : g y / (y - 1) ≤ 0 := div_nonpos_of_nonneg_of_nonpos hge (le_of_lt hyneg)
    linarith
  have hg0 : 0 ≤ g 0 := by
    have hval : g 0 = treeGF b p 0 - 0 := rfl
    rw [hval, sub_zero]; exact treeGF_zero_nonneg b hp1
  have hgcont : ContinuousOn g (Icc 0 y) :=
    ((treeGF_continuous b p).sub continuous_id).continuousOn
  have hmem0 : (0 : ℝ) ∈ Icc (g y) (g 0) := ⟨le_of_lt hgy_neg, hg0⟩
  obtain ⟨q, hqmem, hqval⟩ := intermediate_value_Icc' (le_of_lt hy0) hgcont hmem0
  refine ⟨q, ⟨hqmem.1, lt_of_le_of_lt hqmem.2 hylt1⟩, ?_⟩
  have hval : g q = treeGF b p q - q := rfl
  rw [hval] at hqval; linarith

/-- If `b p < 1`, `treeGF b p s > s` on `[0, 1)` (Bernoulli's inequality). -/
lemma subcritical_no_fixed (b : ℕ) {p s : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hmean : (b : ℝ) * p < 1) (hs0 : 0 ≤ s) (hs1 : s < 1) : s < treeGF b p s := by
  have hps : 0 ≤ p * (1 - s) := mul_nonneg hp0 (by linarith)
  have hbern : 1 - (b : ℝ) * (p * (1 - s)) ≤ treeGF b p s := by
    have hbase : (-1 : ℝ) ≤ 1 - p * (1 - s) := by
      have hub : p * (1 - s) ≤ 1 := by nlinarith
      linarith
    have hb := one_add_mul_sub_le_pow hbase b
    have heq1 : (1 : ℝ) + (b : ℝ) * ((1 - p * (1 - s)) - 1) = 1 - (b : ℝ) * (p * (1 - s)) := by
      ring
    have hgeq : treeGF b p s = (1 - p * (1 - s)) ^ b := by unfold treeGF; ring_nf
    rw [hgeq]; linarith [heq1 ▸ hb]
  have h1s : (0 : ℝ) < 1 - s := by linarith
  have hkey : (b : ℝ) * (p * (1 - s)) < 1 - s := by
    have hlt : (b : ℝ) * p * (1 - s) < 1 * (1 - s) := mul_lt_mul_of_pos_right hmean h1s
    rw [one_mul] at hlt; nlinarith [hlt]
  linarith

/-- Subcritical case: `b p < 1` implies survival probability `0`. -/
lemma survivalProb_eq_zero_of_subcritical (b : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hmean : (b : ℝ) * p < 1) : survivalProb b p = 0 := by
  have hext : extinctionProb b p = 1 := by
    rcases lt_or_eq_of_le (extinctionProb_le_one b p) with hlt | heq
    · exact absurd (extinctionProb_isFixed b p)
        (ne_of_gt (subcritical_no_fixed b hp0 hp1 hmean (extinctionProb_nonneg b p) hlt))
    · exact heq
  unfold survivalProb; rw [hext]; ring

/-- Supercritical case: `b p > 1` implies positive survival probability. -/
lemma survivalProb_pos_of_supercritical (b : ℕ) {p : ℝ} (hp1 : p ≤ 1)
    (hmean : 1 < (b : ℝ) * p) : 0 < survivalProb b p := by
  rw [survivalProb_pos_iff]
  obtain ⟨q, hq_mem, hq_fix⟩ := supercritical_fixed b hp1 hmean
  have hqmem : q ∈ fixedSet b p := ⟨⟨hq_mem.1, le_of_lt hq_mem.2⟩, hq_fix⟩
  have : extinctionProb b p ≤ q := csInf_le (fixedSet_bddBelow b p) hqmem
  linarith [hq_mem.2]

/-- The parameters `p ∈ [0, 1]` with survival probability `0`. -/
def subcriticalSetTree (b : ℕ) : Set ℝ := {p | p ∈ Icc (0 : ℝ) 1 ∧ survivalProb b p = 0}

/-- The critical parameter: the supremum of `subcriticalSetTree b`. -/
noncomputable def treePc (b : ℕ) : ℝ := sSup (subcriticalSetTree b)

lemma survivalProb_zero_eq_zero (b : ℕ) : survivalProb b 0 = 0 := by
  refine survivalProb_eq_zero_of_subcritical b (le_refl 0) (by norm_num) ?_
  simp

/-- The critical parameter of the `b`-ary tree is `1 / b` (for the generating-function surrogate
`survivalProb`; see the module docstring). Grimmett, *Percolation*, 1999, Section 10.1. -/
theorem treePc_eq (b : ℕ) (hb : 1 ≤ b) : treePc b = 1 / (b : ℝ) := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  have hbinv_le_one : 1 / (b : ℝ) ≤ 1 := by
    rw [div_le_one hbpos]; exact_mod_cast hb
  have hbinv_pos : (0 : ℝ) < 1 / b := by positivity
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt
    ⟨0, ⟨by norm_num, survivalProb_zero_eq_zero b⟩⟩ ?_ ?_
  · intro p hp
    by_contra hcon
    have hcon' : 1 / (b : ℝ) < p := lt_of_not_ge hcon
    have hmean : 1 < (b : ℝ) * p := by
      have hmul : (b : ℝ) * (1 / b) < (b : ℝ) * p := mul_lt_mul_of_pos_left hcon' hbpos
      rwa [mul_one_div, div_self (ne_of_gt hbpos)] at hmul
    have hsurv := survivalProb_pos_of_supercritical b hp.1.2 hmean
    rw [hp.2] at hsurv; exact lt_irrefl 0 hsurv
  · intro w hw
    rcases le_or_gt 0 w with hw0 | hw0
    · refine ⟨(w + 1 / b) / 2, ⟨⟨by linarith, by linarith⟩, ?_⟩, by linarith⟩
      refine survivalProb_eq_zero_of_subcritical b (by linarith) (by linarith) ?_
      have hlt : (w + 1 / b) / 2 < 1 / b := by linarith
      have hmul : (b : ℝ) * ((w + 1 / b) / 2) < (b : ℝ) * (1 / b) :=
        mul_lt_mul_of_pos_left hlt hbpos
      rwa [mul_one_div, div_self (ne_of_gt hbpos)] at hmul
    · exact ⟨0, ⟨⟨le_refl 0, zero_le_one⟩, survivalProb_zero_eq_zero b⟩, hw0⟩

/-- Survival probability is positive for `p > 1 / b`. -/
theorem survivalProb_pos_of_gt_treePc (b : ℕ) {p : ℝ} (hb : 1 ≤ b)
    (hp1 : p ≤ 1) (hlt : 1 / (b : ℝ) < p) : 0 < survivalProb b p := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  have hmean : 1 < (b : ℝ) * p := by
    have hmul : (b : ℝ) * (1 / b) < (b : ℝ) * p := mul_lt_mul_of_pos_left hlt hbpos
    rwa [mul_one_div, div_self (ne_of_gt hbpos)] at hmul
  exact survivalProb_pos_of_supercritical b hp1 hmean

/-- Survival probability is `0` for `p < 1 / b`. -/
theorem survivalProb_eq_zero_of_lt_treePc (b : ℕ) {p : ℝ} (hb : 1 ≤ b)
    (hp0 : 0 ≤ p) (hlt : p < 1 / (b : ℝ)) : survivalProb b p = 0 := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  have hbinv_le_one : 1 / (b : ℝ) ≤ 1 := by rw [div_le_one hbpos]; exact_mod_cast hb
  have hmean : (b : ℝ) * p < 1 := by
    have hmul : (b : ℝ) * p < (b : ℝ) * (1 / b) := mul_lt_mul_of_pos_left hlt hbpos
    rwa [mul_one_div, div_self (ne_of_gt hbpos)] at hmul
  exact survivalProb_eq_zero_of_subcritical b hp0 (le_of_lt (lt_of_lt_of_le hlt hbinv_le_one)) hmean

end Percolation

end StatMech
