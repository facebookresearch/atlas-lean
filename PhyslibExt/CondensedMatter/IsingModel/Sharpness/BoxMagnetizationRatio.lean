/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.MagnetizationFieldDeriv

/-!
# Ratio limits for box magnetizations

Positivity and strict bounds for finite-volume magnetizations, and abstract lemmas showing that
ratios `M(n)/m_n(y)` tend to `1` when `M` converges and is squeezed between boxes of size `n` and
`2n`.

## i. Overview

For `β > 0` and `h ≥ 0` the finite-volume magnetization is strictly positive and strictly below `1`,
and strictly increasing in the field. If `M(n) → L > 0` and every site magnetization `m_n(y)` in the
box of size `n` lies between `M(n)` and `M(2n)` (Griffiths' monotonicity and the inclusion of a
translated box in the doubled box), then `min_y M(n)/m_n(y) → 1`. This controls the dependence of
box magnetizations on the position of the site.

## ii. Key results

- `sct_expectation_spin_pos` : positivity of the finite-volume magnetization
- `sct_c_to_one` : squeeze for ratio sequences
- `sct_cInfDep` : the minimal ratio `min_y M(n)/m_n(y)`
- `sct_cInfDep_to_one_of_monotone` : the minimal ratio tends to `1`

## iii. Table of contents

- A. Translated boxes
- B. Bounds on finite-volume magnetizations
- C. Ratio limits

## iv. References

- R. B. Griffiths, "Correlations in Ising ferromagnets I", J. Math. Phys. 8 (1967) 478–483

-/

@[expose] public section

open scoped BigOperators
open Filter Topology

namespace StatMech

namespace Sharpness

open Ising
open StatMech.Lattice

/-! ## A. Translated boxes -/

lemma sct_translate_box_subset_double {d n : ℕ} {y : Site d} (hy : y ∈ box d n) :
    (fun z : Site d => z - y) '' box d n ⊆ box d (2 * n) := by
  rintro _ ⟨z, hz, rfl⟩ i
  calc
    (z i - y i).natAbs ≤ (z i).natAbs + (y i).natAbs := Int.natAbs_sub_le _ _
    _ ≤ n + n := Nat.add_le_add (hz i) (hy i)
    _ = 2 * n := by omega

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## B. Bounds on finite-volume magnetizations -/

lemma sct_expectation_spin_lt_one (β h : ℝ) (x : V) :
    isingExpectation G β h (fun s => spin s x) < 1 := by
  let sminus : ConfigSpace V := fun _ => false
  have hterm : 0 < isingProb G β h sminus * (1 - spin sminus x) := by
    have hp := isingProb_pos G β h sminus
    simpa [sminus, spin] using mul_pos hp (show (0 : ℝ) < 2 by norm_num)
  have hnonneg : ∀ s : ConfigSpace V, 0 ≤ isingProb G β h s * (1 - spin s x) := by
    intro s
    refine mul_nonneg (isingProb_nonneg G β h s) ?_
    rcases spin_eq_pm s x with hs | hs <;> rw [hs] <;> norm_num
  have hsum : 0 < ∑ s : ConfigSpace V, isingProb G β h s * (1 - spin s x) := by
    exact lt_of_lt_of_le hterm
      (Finset.single_le_sum (fun s _ => hnonneg s) (Finset.mem_univ sminus))
  have hid :
      (∑ s : ConfigSpace V, isingProb G β h s * (1 - spin s x)) =
        1 - isingExpectation G β h (fun s => spin s x) := by
    unfold isingExpectation
    calc
      (∑ s : ConfigSpace V, isingProb G β h s * (1 - spin s x)) =
          (∑ s : ConfigSpace V, isingProb G β h s) -
            ∑ s : ConfigSpace V, isingProb G β h s * spin s x := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro s _
              ring
      _ = 1 - ∑ s : ConfigSpace V, isingProb G β h s * spin s x := by
        rw [isingProb_sum_eq_one]
  rw [hid] at hsum
  linarith

lemma sct_deriv_magnetization_pos (β h : ℝ) (hβ : 0 < β) (hh : 0 ≤ h) (o : V) :
    0 < deriv (fun t => isingExpectation G β t (fun s => spin s o)) h := by
  rw [deriv_magnetization_eq_sum_cov]
  apply mul_pos hβ
  let cov : V → ℝ := fun x =>
    isingExpectation G β h (fun s => spin s o * spin s x) -
      isingExpectation G β h (fun s => spin s o) *
        isingExpectation G β h (fun s => spin s x)
  have hcov : ∀ x, 0 ≤ cov x := by
    intro x
    by_cases hxo : x = o
    · subst x
      have hsq : (fun s => spin s o * spin s o) = (fun _ : ConfigSpace V => (1 : ℝ)) := by
        funext s
        exact spin_sq s o
      simp only [cov, hsq]
      have hone : isingExpectation G β h (fun _ : ConfigSpace V => (1 : ℝ)) = 1 := by
        unfold isingExpectation
        simp [isingProb_sum_eq_one G β h]
      rw [hone]
      have hlo := expectation_spin_nonneg G β h hβ.le hh o
      have hhi := expectation_spin_le_one G β h o
      nlinarith
    · exact sub_nonneg.mpr (cov_nonneg G β h hβ.le hh o x (Ne.symm hxo))
  have hdiag : 0 < cov o := by
    have hsq : (fun s => spin s o * spin s o) = (fun _ : ConfigSpace V => (1 : ℝ)) := by
      funext s
      exact spin_sq s o
    simp only [cov, hsq]
    have hone : isingExpectation G β h (fun _ : ConfigSpace V => (1 : ℝ)) = 1 := by
      unfold isingExpectation
      simp [isingProb_sum_eq_one G β h]
    rw [hone]
    have hlo := expectation_spin_nonneg G β h hβ.le hh o
    have hhi := sct_expectation_spin_lt_one G β h o
    nlinarith
  change 0 < ∑ x, cov x
  exact Finset.sum_pos' (fun x _ => hcov x) ⟨o, Finset.mem_univ o, hdiag⟩

lemma sct_expectation_spin_pos (β h : ℝ) (hβ : 0 < β) (hh : 0 < h) (o : V) :
    0 < isingExpectation G β h (fun s => spin s o) := by
  let f : ℝ → ℝ := fun t => isingExpectation G β t (fun s => spin s o)
  have hcont : ContinuousOn f (Set.Ici 0) := by
    intro t _
    exact (hasDerivAt_magnetization G β t o).continuousAt.continuousWithinAt
  have hstrict : StrictMonoOn f (Set.Ici 0) :=
    strictMonoOn_of_deriv_pos (convex_Ici 0) hcont
      (fun t ht => sct_deriv_magnetization_pos G β t hβ (by
        have ht0 : 0 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
        exact ht0.le) o)
  have hlt := hstrict (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hh.le) hh
  change f 0 < f h at hlt
  rw [show f 0 = 0 from magnetization_zero_field G β o] at hlt
  exact hlt

/-! ## C. Ratio limits -/
omit [DecidableRel G.Adj] in
lemma sct_ratioSeq_tendsto_one (M : ℕ → ℝ) {L : ℝ} (hLpos : 0 < L)
    (hM : Tendsto M atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => M n / M (2 * n)) atTop (𝓝 1) := by
  have htwo : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (g := fun n : ℕ => 2 * n) (f := id) (fun n => by simp only [id]; omega)
      tendsto_id
  have hM2 : Tendsto (fun n : ℕ => M (2 * n)) atTop (𝓝 L) := hM.comp htwo
  have hdiv : Tendsto (fun n : ℕ => M n / M (2 * n)) atTop (𝓝 (L / L)) :=
    hM.div hM2 hLpos.ne'
  rwa [div_self hLpos.ne'] at hdiv

lemma sct_c_to_one (M c : ℕ → ℝ) {L : ℝ} (hLpos : 0 < L)
    (hM : Tendsto M atTop (𝓝 L))
    (hsqueeze : ∀ n, M n / M (2 * n) ≤ c n) (hle_one : ∀ n, c n ≤ 1) :
    Tendsto c atTop (𝓝 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (sct_ratioSeq_tendsto_one M hLpos hM) tendsto_const_nhds hsqueeze hle_one

/-- The minimal ratio `min_{y ∈ sites n} M(n)/m(n, y)` for sites indexed by `ℕ`. -/
noncomputable def sct_cInf (M : ℕ → ℝ) (sites : ℕ → Finset ℕ)
    (m : ℕ → ℕ → ℝ) (hne : ∀ n, (sites n).Nonempty) (n : ℕ) : ℝ :=
  (sites n).inf' (hne n) (fun y => M n / m n y)

lemma sct_cInf_le_one (M : ℕ → ℝ) (sites : ℕ → Finset ℕ) (m : ℕ → ℕ → ℝ)
    (hne : ∀ n, (sites n).Nonempty) (o : ℕ → ℕ) (ho : ∀ n, o n ∈ sites n)
    (hoM : ∀ n, m n (o n) = M n) (hMne : ∀ n, M n ≠ 0) (n : ℕ) :
    sct_cInf M sites m hne n ≤ 1 := by
  unfold sct_cInf
  calc (sites n).inf' (hne n) (fun y => M n / m n y)
      ≤ M n / m n (o n) := Finset.inf'_le _ (ho n)
    _ = 1 := by rw [hoM n]; exact div_self (hMne n)

lemma sct_ratio_le_cInf (M : ℕ → ℝ) (sites : ℕ → Finset ℕ) (m : ℕ → ℕ → ℝ)
    (hne : ∀ n, (sites n).Nonempty)
    (hmpos : ∀ n y, y ∈ sites n → 0 < m n y) (hMnn : ∀ n, 0 ≤ M n)
    (hbox : ∀ n y, y ∈ sites n → m n y ≤ M (2 * n)) (n : ℕ) :
    M n / M (2 * n) ≤ sct_cInf M sites m hne n := by
  unfold sct_cInf
  refine Finset.le_inf' (hne n) _ ?_
  intro y hy
  exact div_le_div_of_nonneg_left (hMnn n) (hmpos n y hy) (hbox n y hy)

lemma sct_cInf_to_one (M : ℕ → ℝ) (sites : ℕ → Finset ℕ) (m : ℕ → ℕ → ℝ)
    (hne : ∀ n, (sites n).Nonempty) {L : ℝ} (hLpos : 0 < L)
    (hM : Tendsto M atTop (𝓝 L))
    (hmpos : ∀ n y, y ∈ sites n → 0 < m n y) (hMnn : ∀ n, 0 ≤ M n)
    (hMne : ∀ n, M n ≠ 0)
    (o : ℕ → ℕ) (ho : ∀ n, o n ∈ sites n) (hoM : ∀ n, m n (o n) = M n)
    (hbox : ∀ n y, y ∈ sites n → m n y ≤ M (2 * n)) :
    Tendsto (sct_cInf M sites m hne) atTop (𝓝 1) :=
  sct_c_to_one M (sct_cInf M sites m hne) hLpos hM
    (sct_ratio_le_cInf M sites m hne hmpos hMnn hbox)
    (sct_cInf_le_one M sites m hne o ho hoM hMne)

/-- The minimal ratio `min_{y ∈ sites n} M(n)/m(n, y)` for site types depending on `n`. -/
noncomputable def sct_cInfDep (ι : ℕ → Type*) [∀ n, DecidableEq (ι n)]
    (M : ℕ → ℝ) (sites : (n : ℕ) → Finset (ι n))
    (m : (n : ℕ) → ι n → ℝ) (hne : ∀ n, (sites n).Nonempty) (n : ℕ) : ℝ :=
  (sites n).inf' (hne n) (fun y => M n / m n y)

lemma sct_cInfDep_le_one (ι : ℕ → Type*) [∀ n, DecidableEq (ι n)]
    (M : ℕ → ℝ) (sites : (n : ℕ) → Finset (ι n))
    (m : (n : ℕ) → ι n → ℝ) (hne : ∀ n, (sites n).Nonempty)
    (o : (n : ℕ) → ι n) (ho : ∀ n, o n ∈ sites n)
    (hoM : ∀ n, m n (o n) = M n) (hMne : ∀ n, M n ≠ 0) (n : ℕ) :
    sct_cInfDep ι M sites m hne n ≤ 1 := by
  unfold sct_cInfDep
  calc
    (sites n).inf' (hne n) (fun y => M n / m n y) ≤ M n / m n (o n) :=
      Finset.inf'_le _ (ho n)
    _ = 1 := by rw [hoM n]; exact div_self (hMne n)

lemma sct_ratio_le_cInfDep (ι : ℕ → Type*) [∀ n, DecidableEq (ι n)]
    (M : ℕ → ℝ) (sites : (n : ℕ) → Finset (ι n))
    (m : (n : ℕ) → ι n → ℝ) (hne : ∀ n, (sites n).Nonempty)
    (hmpos : ∀ n y, y ∈ sites n → 0 < m n y) (hMnn : ∀ n, 0 ≤ M n)
    (hbox : ∀ n y, y ∈ sites n → m n y ≤ M (2 * n)) (n : ℕ) :
    M n / M (2 * n) ≤ sct_cInfDep ι M sites m hne n := by
  unfold sct_cInfDep
  refine Finset.le_inf' (hne n) _ ?_
  intro y hy
  exact div_le_div_of_nonneg_left (hMnn n) (hmpos n y hy) (hbox n y hy)

lemma sct_cInfDep_to_one (ι : ℕ → Type*) [∀ n, DecidableEq (ι n)]
    (M : ℕ → ℝ) (sites : (n : ℕ) → Finset (ι n))
    (m : (n : ℕ) → ι n → ℝ) (hne : ∀ n, (sites n).Nonempty)
    {L : ℝ} (hLpos : 0 < L) (hM : Tendsto M atTop (𝓝 L))
    (hmpos : ∀ n y, y ∈ sites n → 0 < m n y) (hMnn : ∀ n, 0 ≤ M n)
    (hMne : ∀ n, M n ≠ 0) (o : (n : ℕ) → ι n)
    (ho : ∀ n, o n ∈ sites n) (hoM : ∀ n, m n (o n) = M n)
    (hbox : ∀ n y, y ∈ sites n → m n y ≤ M (2 * n)) :
    Tendsto (sct_cInfDep ι M sites m hne) atTop (𝓝 1) :=
  sct_c_to_one M (sct_cInfDep ι M sites m hne) hLpos hM
    (sct_ratio_le_cInfDep ι M sites m hne hmpos hMnn hbox)
    (sct_cInfDep_le_one ι M sites m hne o ho hoM hMne)

lemma sct_cInfDep_to_one_of_monotone (ι : ℕ → Type*) [∀ n, DecidableEq (ι n)]
    (M : ℕ → ℝ) (sites : (n : ℕ) → Finset (ι n))
    (m : (n : ℕ) → ι n → ℝ) (hne : ∀ n, (sites n).Nonempty)
    (hmono : Monotone M) (hub : ∀ n, M n ≤ 1) (hM0 : 0 < M 0)
    (hmpos : ∀ n y, y ∈ sites n → 0 < m n y)
    (o : (n : ℕ) → ι n) (ho : ∀ n, o n ∈ sites n)
    (hoM : ∀ n, m n (o n) = M n)
    (hbox : ∀ n y, y ∈ sites n → m n y ≤ M (2 * n)) :
    Tendsto (sct_cInfDep ι M sites m hne) atTop (𝓝 1) := by
  let L : ℝ := ⨆ n, M n
  have hbdd : BddAbove (Set.range M) := ⟨1, by rintro _ ⟨n, rfl⟩; exact hub n⟩
  have hM : Tendsto M atTop (𝓝 L) := tendsto_atTop_ciSup hmono hbdd
  have h0L : M 0 ≤ L := by
    exact le_ciSup hbdd 0
  have hLpos : 0 < L := lt_of_lt_of_le hM0 h0L
  have hMpos : ∀ n, 0 < M n := by
    intro n
    exact lt_of_lt_of_le hM0 (hmono (Nat.zero_le n))
  exact sct_cInfDep_to_one ι M sites m hne hLpos hM hmpos
    (fun n => (hMpos n).le) (fun n => (hMpos n).ne') o ho hoM hbox

end Sharpness

end StatMech
