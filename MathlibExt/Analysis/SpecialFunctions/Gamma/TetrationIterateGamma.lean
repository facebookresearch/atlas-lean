/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import MathlibExt.Analysis.SpecialFunctions.Gamma.IterateRpow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# Tetrations as iterated Gamma values

Every power tower whose base lies above the nontrivial fixed point of the Gamma
function is an iterate of the Gamma function applied to a convergent, eventually
strictly decreasing sequence of starting points
(`MetaMathlibExt.exists_tetration_eq_iterate_Gamma`).
-/

namespace MetaMathlibExt

open Filter Topology

namespace exists_tetration_eq_iterate_Gamma

/-- The nontrivial fixed point of `Gamma` exceeds `2`: on `[1, 2]` convexity
gives `Gamma z ≤ 1 < z`. -/
private theorem two_lt_of_fixed {z : ℝ} (hz : 1 < z) (hΓz : Real.Gamma z = z) :
    2 < z := by
  by_contra h
  have hzle : z ≤ 2 := not_lt.mp h
  rcases eq_or_lt_of_le hzle with h2 | h2
  · subst h2
    rw [Real.Gamma_two] at hΓz
    norm_num at hΓz
  · have hconv := Real.convexOn_Gamma.2 (show (1 : ℝ) ∈ Set.Ioi 0 by simp)
      (show (2 : ℝ) ∈ Set.Ioi 0 by simp) (show (0 : ℝ) ≤ 2 - z by linarith)
      (show (0 : ℝ) ≤ z - 1 by linarith) (by ring : 2 - z + (z - 1) = 1)
    simp only [smul_eq_mul, Real.Gamma_one, Real.Gamma_two] at hconv
    have hz_eq : (2 - z) * 1 + (z - 1) * 2 = z := by ring
    rw [hz_eq] at hconv
    have hone : (2 - z) * 1 + (z - 1) * 1 = 1 := by ring
    rw [hone] at hconv
    rw [hΓz] at hconv
    linarith

/-- The nontrivial fixed point of `Gamma` exceeds `3`, by strict monotonicity
of `Gamma` on `[2, ∞)` and `Gamma 3 = 2`. -/
private theorem three_lt_of_fixed {z : ℝ} (hz : 1 < z) (hΓz : Real.Gamma z = z) :
    3 < z := by
  have hz2 := two_lt_of_fixed hz hΓz
  by_contra h
  have hle : z ≤ 3 := not_lt.mp h
  have h3 : Real.Gamma 3 = 2 := by
    rw [show (3 : ℝ) = ((2 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num
  have hle2 := Real.Gamma_strictMonoOn_Ici.monotoneOn (show z ∈ Set.Ici (2 : ℝ) from hz2.le)
    (show (3 : ℝ) ∈ Set.Ici (2 : ℝ) by norm_num) hle
  rw [hΓz, h3] at hle2
  linarith

/-- For `x > 4`, `x ≤ Gamma x`, since `Gamma (x - 1) ≥ 2` and
`Gamma x = (x - 1) * Gamma (x - 1)`. -/
private theorem le_Gamma_of_four_lt {x : ℝ} (hx : 4 < x) : x ≤ Real.Gamma x := by
  have h3 : Real.Gamma 3 = 2 := by
    rw [show (3 : ℝ) = ((2 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num
  have hprev : 2 ≤ Real.Gamma (x - 1) := by
    have h := Real.Gamma_strictMonoOn_Ici.monotoneOn (show (3 : ℝ) ∈ Set.Ici (2 : ℝ) by norm_num)
      (show x - 1 ∈ Set.Ici (2 : ℝ) by simp only [Set.mem_Ici]; linarith) (by linarith)
    rwa [h3] at h
  calc
    x ≤ (x - 1) * 2 := by linarith
    _ ≤ (x - 1) * Real.Gamma (x - 1) := mul_le_mul_of_nonneg_left hprev (by linarith)
    _ = Real.Gamma x := by
        rw [← Real.Gamma_add_one (by linarith : x - 1 ≠ 0)]
        ring_nf

/-- Every iterate of `Gamma` maps `(z, ∞)` to itself. -/
private theorem iterate_Gamma_gt {z : ℝ} (hz2 : 2 < z) (hΓz : Real.Gamma z = z)
    (k : ℕ) {x : ℝ} (hx : z < x) : z < Real.Gamma^[k] x := by
  induction k generalizing x with
  | zero => simpa using hx
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hgt : z < Real.Gamma^[k] x := ih hx
    have hlt := Real.Gamma_strictMonoOn_Ici (show z ∈ Set.Ici (2 : ℝ) from hz2.le)
      (show Real.Gamma^[k] x ∈ Set.Ici (2 : ℝ) from hz2.le.trans hgt.le) hgt
    rwa [hΓz] at hlt

/-- Every iterate of `Gamma` is strictly monotone on `(z, ∞)`. -/
private theorem strictMonoOn_iterate_Gamma {z : ℝ} (hz2 : 2 < z)
    (hΓz : Real.Gamma z = z) (k : ℕ) :
    StrictMonoOn (Real.Gamma^[k]) (Set.Ioi z) := by
  induction k with
  | zero => simpa using strictMonoOn_id (s := Set.Ioi z)
  | succ k ih =>
    rw [Function.iterate_succ']
    have hmono : StrictMonoOn Real.Gamma (Set.Ioi z) := by
      intro a ha b hb hab
      exact Real.Gamma_strictMonoOn_Ici (show a ∈ Set.Ici (2 : ℝ) from hz2.le.trans ha.le)
        (show b ∈ Set.Ici (2 : ℝ) from hz2.le.trans hb.le) hab
    have hmaps : Set.MapsTo (Real.Gamma^[k]) (Set.Ioi z) (Set.Ioi z) :=
      fun a ha => iterate_Gamma_gt hz2 hΓz k ha
    exact hmono.comp ih hmaps

/-- The fixed point `z` is fixed by every iterate of `Gamma`. -/
private theorem iterate_Gamma_fixed {z : ℝ} (hΓz : Real.Gamma z = z) (k : ℕ) :
    Real.Gamma^[k] z = z := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, hΓz]

/-- Every iterate of `Gamma` is continuous on `(0, ∞)`. -/
private theorem continuousOn_iterate_Gamma (k : ℕ) :
    ContinuousOn (Real.Gamma^[k]) (Set.Ioi (0 : ℝ)) := by
  apply ContinuousOn.iterate _ _ k
  · exact Real.differentiableOn_Gamma_Ioi.continuousOn
  · intro x hx
    exact Real.Gamma_pos_of_pos hx

/-- Every iterate of `Gamma` dominates the identity above `4`. -/
private theorem le_iterate_Gamma_of_four_lt {x : ℝ} (hx : 4 < x) (k : ℕ) :
    x ≤ Real.Gamma^[k] x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (le_Gamma_of_four_lt (lt_of_lt_of_le hx ih))

/-- A power tower is at least `1`. -/
private theorem one_le_tetration {b : ℝ} (hb : 1 < b) (n : ℕ) :
    1 ≤ (fun y : ℝ => b ^ y)^[n] 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have h1 : b ≤ (fun y : ℝ => b ^ y) ((fun y : ℝ => b ^ y)^[n] 1) := by
      have h := Real.rpow_le_rpow_of_exponent_le hb.le ih
      simpa [Real.rpow_one] using h
    exact hb.le.trans h1

/-- A power tower of height at least `1` is at least its base. -/
private theorem tetration_ge {b : ℝ} (hb : 1 < b) {n : ℕ} (hn : 1 ≤ n) :
    b ≤ (fun y : ℝ => b ^ y)^[n] 1 := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n _ ih =>
    rw [Function.iterate_succ_apply']
    have h1 : (1 : ℝ) ≤ (fun y : ℝ => b ^ y)^[n] 1 := one_le_tetration hb n
    have h := Real.rpow_le_rpow_of_exponent_le hb.le h1
    simpa [Real.rpow_one] using h

/-- For every height `n ≥ 1`, some `x > z` satisfies `Gamma^[n] x` equal to the
power tower of height `n`, by the intermediate value theorem. -/
private theorem exists_iterate_Gamma_eq_tetration {z b : ℝ} (hz : 1 < z)
    (hΓz : Real.Gamma z = z) (hb : z < b) {n : ℕ} (hn : 1 ≤ n) :
    ∃ x : ℝ, z < x ∧ Real.Gamma^[n] x = (fun y : ℝ => b ^ y)^[n] 1 := by
  have hz2 := two_lt_of_fixed hz hΓz
  have hb1 : 1 < b := hz.trans hb
  have hT : b ≤ (fun y : ℝ => b ^ y)^[n] 1 := tetration_ge hb1 hn
  have hzT : z < (fun y : ℝ => b ^ y)^[n] 1 := hb.trans_le hT
  set T : ℝ := (fun y : ℝ => b ^ y)^[n] 1 with hTdef
  set u : ℝ := max T 5 with hudef
  have hu4 : 4 < u := lt_max_of_lt_right (by norm_num)
  have huT : T ≤ u := le_max_left _ _
  have hiter_u : u ≤ Real.Gamma^[n] u := le_iterate_Gamma_of_four_lt hu4 n
  have hcont : ContinuousOn (Real.Gamma^[n]) (Set.Icc z u) :=
    (continuousOn_iterate_Gamma n).mono
      (fun x hx => (zero_lt_one.trans hz).trans_le hx.1)
  have hmem : (fun y : ℝ => b ^ y)^[n] 1 ∈
      Set.Icc (Real.Gamma^[n] z) (Real.Gamma^[n] u) := by
    constructor
    · rw [iterate_Gamma_fixed hΓz]
      exact hzT.le
    · exact huT.trans hiter_u
  have hzu : z ≤ u := le_trans hzT.le huT
  obtain ⟨x, hxIcc, hxeq⟩ := (intermediate_value_Icc hzu hcont) hmem
  have hne : z ≠ x := by
    intro h
    rw [← h, iterate_Gamma_fixed hΓz] at hxeq
    exact (lt_irrefl _ (hxeq ▸ hzT)).elim
  exact ⟨x, lt_of_le_of_ne hxIcc.1 hne, hxeq⟩

/-- The chosen starting points strictly decrease from height `2` on: applying
`Gamma` once more to the tower of height `n` exceeds the tower of height
`n + 1`, by the Gamma bound for iterated exponentials. -/
private theorem step_lt {z b : ℝ} (hz : 1 < z) (hΓz : Real.Gamma z = z) (hb : z < b)
    {x : ℕ → ℝ} (hx_gt : ∀ n : ℕ, 1 ≤ n → z < x n)
    (hx_eq : ∀ n : ℕ, 1 ≤ n → Real.Gamma^[n] (x n) = (fun y : ℝ => b ^ y)^[n] 1)
    {n : ℕ} (hn : 2 ≤ n) : x (n + 1) < x n := by
  have hz2 := two_lt_of_fixed hz hΓz
  have hz3 := three_lt_of_fixed hz hΓz
  have hbexp : Real.exp 1 ≤ b := by
    have h := Real.exp_one_lt_d9
    linarith
  obtain ⟨m, hm, rfl⟩ : ∃ m : ℕ, 1 ≤ m ∧ n = m + 1 := ⟨n - 1, by omega, by omega⟩
  have hT_n : (fun y : ℝ => b ^ y)^[m + 1] 1 = (fun y : ℝ => b ^ y)^[m] b := by
    calc (fun y : ℝ => b ^ y)^[m + 1] 1
        = (fun y : ℝ => b ^ y)^[m] ((fun y : ℝ => b ^ y) 1) :=
          Function.iterate_succ_apply _ _ _
      _ = (fun y : ℝ => b ^ y)^[m] b := by
          congr 1
          change b ^ (1 : ℝ) = b
          exact Real.rpow_one b
  have hT_n1 : (fun y : ℝ => b ^ y)^[m + 1 + 1] 1 = (fun y : ℝ => b ^ y)^[m + 1] b := by
    calc (fun y : ℝ => b ^ y)^[m + 1 + 1] 1
        = (fun y : ℝ => b ^ y)^[m + 1] ((fun y : ℝ => b ^ y) 1) :=
          Function.iterate_succ_apply _ _ _
      _ = (fun y : ℝ => b ^ y)^[m + 1] b := by
          congr 1
          change b ^ (1 : ℝ) = b
          exact Real.rpow_one b
  have hlt : (fun y : ℝ => b ^ y)^[m + 1 + 1] 1 <
      Real.Gamma ((fun y : ℝ => b ^ y)^[m + 1] 1) := by
    rw [hT_n1, hT_n]
    exact MetaMathlibExt.iterate_rpow_succ_lt_Gamma_iterate_rpow hbexp hm
  have hiter_next : Real.Gamma^[m + 1 + 1] (x (m + 1 + 1)) =
      (fun y : ℝ => b ^ y)^[m + 1 + 1] 1 := hx_eq _ (by omega)
  have hiter_cur : Real.Gamma^[m + 1 + 1] (x (m + 1)) =
      Real.Gamma ((fun y : ℝ => b ^ y)^[m + 1] 1) := by
    rw [Function.iterate_succ_apply', hx_eq _ (by omega)]
  have hmono := strictMonoOn_iterate_Gamma hz2 hΓz (m + 1 + 1)
  have hlt2 : Real.Gamma^[m + 1 + 1] (x (m + 1 + 1)) <
      Real.Gamma^[m + 1 + 1] (x (m + 1)) := by rw [hiter_next, hiter_cur]; exact hlt
  exact (hmono.lt_iff_lt (hx_gt _ (by omega)) (hx_gt _ (by omega))).mp hlt2

end exists_tetration_eq_iterate_Gamma

/-- **Tetrations as iterated Gamma values.** Let $z > 1$ be a real number with $\Gamma(z) = z$,
and let $b > z$. Let $b \uparrow\uparrow n$ be the $n$-fold iterate of $y \mapsto b^y$ starting
at $1$, and $\Gamma^n$ the $n$-fold iterate of $\Gamma$. Then there is a convergent sequence
$(x_n)$ of real numbers, strictly decreasing from some index on, such that
$b \uparrow\uparrow n = \Gamma^n(x_n)$ for every $n \ge 1$.

The case $n = 0$ is excluded, as the paper defines power towers only for $n \ge 1$.

Source: Karol Gryszka, *Exponential versus Factorial Revisited*, Journal of Integer
Sequences 28 (2025), Article 25.2.8, Theorem 12 (`jis-2025-25.2.8-thm-12`). -/
public theorem exists_tetration_eq_iterate_Gamma {z b : ℝ} (hz : 1 < z)
    (hΓz : Real.Gamma z = z) (hb : z < b) :
    ∃ x : ℕ → ℝ, (∀ n ≥ 1, (fun y : ℝ => b ^ y)^[n] 1 = Real.Gamma^[n] (x n)) ∧
      (∃ L : ℝ, Tendsto x atTop (𝓝 L)) ∧ ∃ M : ℕ, StrictAntiOn x (Set.Ici M) := by
  have hex : ∀ n : ℕ, ∃ x : ℝ, 1 ≤ n → z < x ∧ Real.Gamma^[n] x = (fun y : ℝ => b ^ y)^[n] 1 := by
    intro n
    by_cases hn : 1 ≤ n
    · obtain ⟨y, hy1, hy2⟩ :=
        exists_tetration_eq_iterate_Gamma.exists_iterate_Gamma_eq_tetration hz hΓz hb hn
      exact ⟨y, fun _ => ⟨hy1, hy2⟩⟩
    · exact ⟨z, fun h => absurd h hn⟩
  choose x hx using hex
  have hx_gt : ∀ n : ℕ, 1 ≤ n → z < x n := fun n hn => (hx n hn).1
  have hx_eq : ∀ n : ℕ, 1 ≤ n → Real.Gamma^[n] (x n) = (fun y : ℝ => b ^ y)^[n] 1 :=
    fun n hn => (hx n hn).2
  have hdec : ∀ a b₁ : ℕ, 2 ≤ a → a < b₁ → x b₁ < x a := by
    intro a b₁ ha hab
    have hchain : ∀ k : ℕ, x (a + k + 1) < x a := by
      intro k
      induction k with
      | zero =>
        have h := exists_tetration_eq_iterate_Gamma.step_lt hz hΓz hb hx_gt hx_eq
          (show 2 ≤ a from ha)
        simpa using h
      | succ k ih =>
        have hstep : x (a + k + 1 + 1) < x (a + k + 1) :=
          exists_tetration_eq_iterate_Gamma.step_lt hz hΓz hb hx_gt hx_eq
            (show 2 ≤ a + k + 1 by omega)
        have heq : a + (k + 1) + 1 = a + k + 1 + 1 := by omega
        rw [heq]
        exact hstep.trans ih
    obtain ⟨k, hk⟩ : ∃ k : ℕ, b₁ = a + k + 1 := ⟨b₁ - a - 1, by omega⟩
    rw [hk]
    exact hchain k
  have hanti : StrictAntiOn x (Set.Ici 2) := by
    intro a ha b₁ hb₁ hab
    exact hdec a b₁ ha hab
  have hconv : ∃ L : ℝ, Tendsto x atTop (𝓝 L) := by
    have hanti_shift : Antitone (fun n : ℕ => x (n + 2)) := by
      intro m n hmn
      rcases eq_or_lt_of_le hmn with h | h
      · rw [h]
      · exact (hdec (m + 2) (n + 2) (by omega) (by omega)).le
    have hbdd : BddBelow (Set.range (fun n : ℕ => x (n + 2))) :=
      ⟨z, by rintro _ ⟨n, rfl⟩; exact (hx_gt (n + 2) (by omega)).le⟩
    have ht := tendsto_atTop_ciInf hanti_shift hbdd
    exact ⟨⨅ i, x (i + 2), (Filter.tendsto_add_atTop_iff_nat 2).mp ht⟩
  refine ⟨x, ?_, hconv, 2, hanti⟩
  intro n hn
  exact (hx_eq n hn).symm

end MetaMathlibExt
