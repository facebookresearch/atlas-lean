/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/NumberTheory/DuffinSchaefferConjecture.lean` (leanprover/lean-eval),
problem `annals_duffin_schaeffer_conjecture` at commit 38361be884302c7edce1908c4aef8296eb2cb27e.
Copyright 2026 Lean FRO, LLC.
Authors: Katerina Hristova, Kevin Buzzard
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).

The approximation inequality, the set of approximable points, the weighted supremum and the
theorem statement are adapted from this source. The proof is new.
-/

module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.PNat.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# The convergent case of Catlin's conjecture

Koukoulopoulos–Maynard Theorem 2(a) shows that the set of points admitting infinitely many
unrestricted rational approximations is Borel and null when Catlin's series converges.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.DuffinSchaefferConjectureWanted.DuffinSchaefferConjecture

open NNReal ENNReal MeasureTheory
open scoped Nat

/-- **The approximation inequality (1.7).** For a function $\psi$ from the positive integers to
the nonnegative reals, a real number $\alpha$, a natural number $a$ and a positive integer $q$,
inequality (1.7) is the condition $|\alpha - a/q| \le \psi(q)/q$. -/
def inequality_1_7 (ψ : ℕ+ → ℝ≥0) (α : ℝ) (a : ℕ) (q : ℕ+) : Prop :=
  |α - a / q| ≤ ψ q / q

/-- **The set $\mathcal{K}$ of Catlin's conjecture.** For a function $\psi$ from the positive
integers to the nonnegative reals, $\mathcal{K}(\psi)$ is the set of real numbers
$\alpha \in [0, 1]$ for which inequality (1.7), $|\alpha - a/q| \le \psi(q)/q$, has infinitely
many solutions $(a, q)$ with $a$ a natural number and $q$ a positive integer such that $a \le q$.

The fractions $a/q$ need not be reduced. -/
def 𝒦 (ψ : ℕ+ → ℝ≥0) : Set ℝ :=
  {α ∈ Set.Icc 0 1 | {(a, q) : ℕ × ℕ+ | a ≤ q ∧ inequality_1_7 ψ α a q}.Infinite}

/-- **The function $\psi^*$ of Catlin's conjecture.** For a function $\psi$ from the positive
integers to the nonnegative reals, $\psi^*$ sends each positive integer $q$ to
$\psi^*(q) = \varphi(q) \cdot \sup \{\psi(n)/n : n \text{ a positive integer with } q \mid n\}$,
where $\varphi$ is Euler's totient function and the supremum is taken in $[0, \infty]$. -/
noncomputable def ψ_star (ψ : ℕ+ → ℝ≥0) : ℕ+ → ℝ≥0∞ :=
  fun q ↦ φ q * sSup {r : ℝ≥0∞ | ∃ n : ℕ+, q ∣ n ∧ r = ψ n / n}

open Set Filter

private theorem measurableSet_catlin (ψ : ℕ+ → ℝ≥0) : MeasurableSet (𝒦 ψ) := by
  classical
  let ball (p : ℕ × ℕ+) := Metric.closedBall (p.1 / (p.2 : ℝ)) (ψ p.2 / (p.2 : ℝ))
  have h : 𝒦 ψ = Icc 0 1 ∩ ⋂ F : Finset (ℕ × ℕ+),
      ⋃ p : {p : ℕ × ℕ+ // p ∉ F ∧ p.1 ≤ p.2}, ball p := by
    ext x
    simp only [𝒦, mem_ofPred, mem_inter_iff, mem_iInter, mem_iUnion, and_congr_right_iff]
    intro _
    constructor
    · intro hx F
      obtain ⟨⟨a, q⟩, ⟨ha, hax⟩, hF⟩ := hx.exists_notMem_finset F
      exact ⟨⟨(a, q), hF, ha⟩, hax⟩
    · intro hx hfin
      obtain ⟨p, hp⟩ := hx hfin.toFinset
      exact p.2.1 (hfin.mem_toFinset.mpr ⟨p.2.2, hp⟩)
  rw [h]
  exact measurableSet_Icc.inter <| .iInter fun _ ↦
    .iUnion fun _ ↦ Metric.isClosed_closedBall.measurableSet

private noncomputable def radius (ψ : ℕ+ → ℝ≥0) (d : ℕ+) : ℝ≥0∞ :=
  sSup {r : ℝ≥0∞ | ∃ n : ℕ+, d ∣ n ∧ r = ψ n / n}

private theorem le_radius (ψ : ℕ+ → ℝ≥0) {d q : ℕ+} (hd : d ∣ q) :
    (ψ q : ℝ≥0∞) / q ≤ radius ψ d :=
  le_sSup ⟨q, hd, rfl⟩

private theorem radius_le_star (ψ : ℕ+ → ℝ≥0) (d : ℕ+) : radius ψ d ≤ ψ_star ψ d := by
  apply le_mul_of_one_le_left'
  exact_mod_cast Nat.totient_pos.mpr d.2

-- Include the right endpoint in addition to the totient's usual half-open range.
private def numerators (d : ℕ+) : Finset ℕ :=
  insert (d : ℕ) ((Finset.range d).filter ((d : ℕ).Coprime ·))

private theorem reduce_fraction {a : ℕ} {q : ℕ+} (ha : a ≤ q) :
    ∃ (d : ℕ+) (b : ℕ), b ∈ numerators d ∧ d ∣ q ∧ (a : ℝ) / q = (b : ℝ) / d := by
  obtain ⟨n, hn⟩ := q
  change a ≤ n at ha
  obtain ⟨g, b, d, hg, hcop, hab, hnd⟩ := Nat.exists_coprime' (Nat.gcd_pos_of_pos_right a hn)
  have hd : 0 < d := Nat.pos_of_mul_pos_right (hnd ▸ hn)
  have hbd : b ≤ d := Nat.le_of_mul_le_mul_right (hab ▸ hnd ▸ ha) hg
  refine ⟨⟨d, hd⟩, b, ?_, PNat.dvd_iff.mpr ⟨g, hnd⟩, ?_⟩
  · rcases hbd.lt_or_eq with h | rfl
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h, hcop.symm⟩)
    · exact Finset.mem_insert_self ..
  · change (a : ℝ) / n = (b : ℝ) / d
    rw [hab, hnd, Nat.cast_mul, Nat.cast_mul, mul_div_mul_right _ _ (by positivity)]

private noncomputable def cover (ψ : ℕ+ → ℝ≥0) (d : ℕ+) : Set ℝ :=
  ⋃ b ∈ numerators d, Metric.closedEBall ((b : ℝ) / d) (radius ψ d)

private theorem volume_cover_le (ψ : ℕ+ → ℝ≥0) (d : ℕ+) :
    volume (cover ψ d) ≤ 4 * ψ_star ψ d := by
  have hcard : (numerators d).card ≤ 2 * φ d := by
    have h := Finset.card_insert_le (d : ℕ) ((Finset.range d).filter ((d : ℕ).Coprime ·))
    change (numerators d).card ≤ φ d + 1 at h
    rw [two_mul]
    exact h.trans (Nat.add_le_add_left (Nat.totient_pos.mpr d.2) _)
  calc
    volume (cover ψ d) ≤ _ := measure_biUnion_finset_le _ _
    _ = (numerators d).card * (2 * radius ψ d) := by simp [nsmul_eq_mul]
    _ ≤ (2 * (φ d : ℝ≥0∞)) * (2 * radius ψ d) := by
      gcongr
      exact_mod_cast hcard
    _ = 4 * ψ_star ψ d := by
      change _ = 4 * ((φ d : ℝ≥0∞) * radius ψ d)
      ring

private theorem tsum_volume_ne_top {ψ : ℕ+ → ℝ≥0} (hψ : ∑' q, ψ_star ψ q < ∞)
    {s : ℕ+ → Set ℝ} (C : ℕ) (hs : ∀ q, volume (s q) ≤ C * ψ_star ψ q) :
    ∑' q, volume (s q) ≠ ∞ := by
  apply ne_top_of_le_ne_top _ (tsum_le_tsum hs)
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_ne_top (by simp) hψ.ne

private theorem finite_pairs {Q : Set ℕ+} (hQ : Q.Finite) :
    {p : ℕ × ℕ+ | p.2 ∈ Q ∧ p.1 ≤ p.2}.Finite := by
  refine (hQ.biUnion fun q _ ↦ (finite_Iic (q : ℕ)).prod (finite_singleton q)).subset ?_
  rintro ⟨a, q⟩ ⟨hq, ha⟩
  exact mem_iUnion₂.mpr ⟨q, hq, ha, rfl⟩

/-- **Koukoulopoulos–Maynard Theorem 2(a) (Catlin's conjecture, convergent case).** Let $\psi$
be a function from the positive integers to the nonnegative reals, and for each positive integer
$q$ let $\psi^*(q) = \varphi(q) \cdot \sup \{\psi(n)/n : n \text{ a positive integer with }
q \mid n\}$, where $\varphi$ is Euler's totient function and the supremum is taken in
$[0, \infty]$. Let $\mathcal{K}(\psi)$ be the set of real numbers $\alpha \in [0, 1]$ for which
$|\alpha - a/q| \le \psi(q)/q$ has infinitely many solutions with $a$ a natural number and $q$ a
positive integer such that $a \le q$. If $\sum_{q \ge 1} \psi^*(q) < \infty$, then
$\mathcal{K}(\psi)$ is a Borel set and has Lebesgue measure $0$.

Source: D. Koukoulopoulos and J. Maynard, `On the Duffin-Schaeffer conjecture`, Annals of Math, 192 (1) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-1-DuffinSchaefferConjecture.lean Via leanprover/lean-eval@38361be, problem `annals_duffin_schaeffer_conjecture`.
-/
public theorem theorem_2_a (ψ : ℕ+ → ℝ≥0) (hψ : ∑' q, ψ_star ψ q < ∞) :
    MeasurableSet (𝒦 ψ) ∧ volume (𝒦 ψ) = 0 := by
  refine ⟨measurableSet_catlin ψ, measure_eq_zero_iff_ae_notMem.mpr ?_⟩
  have hcover := ae_finite_setOfPred_mem (tsum_volume_ne_top hψ 4 (volume_cover_le ψ))
  -- At any one rational centre, almost every point meets only finitely many original radii.
  let ball (d : ℕ+) (b : ℕ) (q : ℕ+) :=
    Metric.closedEBall ((b : ℝ) / d) ((ψ q : ℝ≥0∞) / q)
  have hball : ∀ᵐ x : ℝ, ∀ d b, {q | x ∈ ball d b q}.Finite := by
    refine ae_all_iff.mpr fun d ↦ ae_all_iff.mpr fun b ↦ ae_finite_setOfPred_mem ?_
    apply tsum_volume_ne_top hψ 2
    intro q
    simp only [ball, Real.volume_closedEBall]
    change 2 * _ ≤ 2 * ψ_star ψ q
    gcongr
    exact (le_radius ψ (dvd_refl q)).trans (radius_le_star ψ q)
  filter_upwards [hcover, hball] with x hx hcentres
  rintro ⟨_, hinf⟩
  -- Take the union of the finite denominator sets over the finitely many eligible centres.
  have hQ := hx.biUnion fun d _ ↦ (numerators d).finite_toSet.biUnion fun b _ ↦ hcentres d b
  apply hinf ((finite_pairs hQ).subset ?_)
  rintro ⟨a, q⟩ ⟨ha, hax⟩
  obtain ⟨d, b, hb, hd, heq⟩ := reduce_fraction ha
  have hdist : edist x ((b : ℝ) / d) ≤ (ψ q : ℝ≥0∞) / q := by
    rw [← heq, edist_dist, Real.dist_eq]
    have h := ENNReal.ofReal_le_ofReal hax
    rwa [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_natCast] at h
  have hxd : x ∈ cover ψ d := mem_iUnion₂.mpr ⟨b, hb, hdist.trans (le_radius ψ hd)⟩
  exact ⟨mem_iUnion₂.mpr ⟨d, hxd, mem_iUnion₂.mpr ⟨b, hb, hdist⟩⟩, ha⟩

end MathlibExt.NumberTheory.DuffinSchaefferConjectureWanted.DuffinSchaefferConjecture
