/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import MathlibExt.NumberTheory.GaussKuzminFundamentalIntervals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Reversal symmetry characterizes the Gauss–Kuzmin density

This module proves that a function that is continuous on $[0, 1]$, has integral $1$ there, and
gives the fundamental interval $I(a)$ of every string $a$ whose length lies in an infinite set the
same integral as $I(\overleftarrow{a})$, is the Gauss–Kuzmin density
$\frac{1}{\log 2 \cdot (1 + x)}$ on $[0, 1]$ (Theorem 1 of Singh, Zhang and Hildebrand).

As in the source, if the fundamental intervals of $(a_1, \ldots, a_n, t)$ and
$(t, a_n, \ldots, a_1)$ carry the same integral of $f$ for every digit $t \ge 1$, where the $a_i$
are positive integers, comparing them as $t \to \infty$ gives $f(r) = f(0)/(1 + r)$ at
$r = [0; a_1, \ldots, a_n]$ (`density_cfValue_eq_of_append_symmetric`, the source's Lemma 3.1).
Such points, with
$n + 1$ in the given set, are dense in $[0, 1]$: every rational number in $[0, 1]$ is
$[0; b_1, \ldots, b_m]$ for some string $b$ (Euclid's algorithm), and appending a string whose
first digit is large gives strings of any larger length whose values are as close to it as
wanted. Continuity extends the identity to $[0, 1]$, and the normalization gives
$f(0) = 1/\log 2$. The nonnegativity hypothesis is not needed.
-/

namespace MetaMathlibExt

@[expose] public section

open MeasureTheory Filter Topology Real Set

namespace density_eq_gaussKuzmin_of_reverse_symmetric

/-- The number $[0; a_1, \ldots, a_n] = p/q$ read off the convergent matrix of a string. -/
private noncomputable def val (a : List ℕ) : ℝ :=
  (convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ)

private theorem cm_cons (t : ℕ) (a : List ℕ) :
    convergentMatrix (t :: a) 0 0 = convergentMatrix a 1 0 ∧
      convergentMatrix (t :: a) 0 1 = convergentMatrix a 1 1 ∧
      convergentMatrix (t :: a) 1 0 = convergentMatrix a 0 0 + t * convergentMatrix a 1 0 ∧
      convergentMatrix (t :: a) 1 1 = convergentMatrix a 0 1 + t * convergentMatrix a 1 1 := by
  simp [convergentMatrix_cons, Matrix.mul_apply, Fin.sum_univ_two]

/-- Sign and size of the entries of the convergent matrix of a positive string. -/
private theorem entries (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) :
    0 ≤ convergentMatrix a 0 0 ∧ 0 ≤ convergentMatrix a 0 1 ∧ 0 ≤ convergentMatrix a 1 0 ∧
      1 ≤ convergentMatrix a 1 1 ∧ convergentMatrix a 0 1 ≤ convergentMatrix a 1 1 := by
  induction a with
  | nil => simp [convergentMatrix_nil]
  | cons t a ih =>
    obtain ⟨h00, h01, h10, h11, hle⟩ := ih fun x hx => ha x (List.mem_cons_of_mem _ hx)
    have ht : (1 : ℤ) ≤ t := by exact_mod_cast ha t List.mem_cons_self
    obtain ⟨e00, e01, e10, e11⟩ := cm_cons t a
    rw [e00, e01, e10, e11]
    refine ⟨h10, by omega, by positivity, by nlinarith, by nlinarith⟩

private theorem q_pos (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) :
    (0 : ℝ) < convergentMatrix a 1 1 := by
  obtain ⟨-, -, -, h11, -⟩ := entries a ha
  exact_mod_cast (show (0 : ℤ) < convergentMatrix a 1 1 by omega)

private theorem val_mem_Icc (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) : val a ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨-, h01, -, -, hle⟩ := entries a ha
  have hq := q_pos a ha
  exact ⟨div_nonneg (by exact_mod_cast h01) hq.le, (div_le_one hq).2 (by exact_mod_cast hle)⟩

private theorem val_cons (t : ℕ) (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) :
    val (t :: a) = 1 / (t + val a) := by
  have hq := q_pos a ha
  obtain ⟨-, e01, -, e11⟩ := cm_cons t a
  simp only [val, e01, e11]
  push_cast
  field_simp
  ring

private theorem val_append (b c : List ℕ) (hc : ∀ x ∈ c, 0 < x) :
    val (b ++ c) = ((convergentMatrix b 0 0 : ℝ) * val c + convergentMatrix b 0 1) /
      ((convergentMatrix b 1 0 : ℝ) * val c + convergentMatrix b 1 1) := by
  have hmul : convergentMatrix (b ++ c) = convergentMatrix b * convergentMatrix c := by
    simp [convergentMatrix, List.prod_append]
  have hq := q_pos c hc
  simp only [val, hmul, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  rw [mul_div_assoc', div_add' _ _ _ hq.ne', mul_div_assoc', div_add' _ _ _ hq.ne',
    div_div_div_cancel_right₀ hq.ne']

/-- Every rational number in $[0, 1]$ is the value of a string of positive integers. -/
private theorem exists_val_eq (p : ℕ) :
    ∀ q : ℕ, p ≤ q → 0 < q → ∃ b : List ℕ, (∀ x ∈ b, 0 < x) ∧ val b = p / q := by
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro q hpq hq
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · exact ⟨[], by simp, by simp [val, convergentMatrix_nil]⟩
    · obtain ⟨b, hb, hval⟩ := ih (q % p) (Nat.mod_lt q hp) p (Nat.mod_lt q hp).le hp
      refine ⟨(q / p) :: b, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact Nat.div_pos hpq hp
        · exact hb x hx
      · rw [val_cons _ _ hb, hval]
        have hq' : (q : ℝ) = (q / p : ℕ) * p + (q % p : ℕ) := by
          exact_mod_cast (Nat.div_add_mod' q p).symm
        have hp' : (0 : ℝ) < p := by exact_mod_cast hp
        rw [hq']
        field_simp

/-- The values of strings of positive integers are dense in $[0, 1]$. -/
private theorem mem_closure_vals {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    x ∈ closure {y | ∃ b : List ℕ, (∀ z ∈ b, 0 < z) ∧ val b = y} := by
  have h := (tendsto_nat_floor_mul_div_atTop hx.1).comp tendsto_natCast_atTop_atTop
  refine mem_closure_of_tendsto h ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hle : ⌊x * n⌋₊ ≤ n :=
    Nat.floor_le_of_le (by nlinarith [hx.2, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  obtain ⟨b, hb, hv⟩ := exists_val_eq ⌊x * n⌋₊ n hle hn
  exact ⟨b, hb, hv⟩

/-- Appending a string whose first digit tends to infinity leaves the value unchanged in the
limit. -/
private theorem tendsto_val_append (b : List ℕ) (hb : ∀ x ∈ b, 0 < x) (d : List ℕ)
    (hd : ∀ x ∈ d, 0 < x) :
    Tendsto (fun T : ℕ => val (b ++ (T + 1) :: d)) atTop (𝓝 (val b)) := by
  have hpos : ∀ T : ℕ, ∀ x ∈ (T + 1) :: d, 0 < x := by
    intro T x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · omega
    · exact hd x hx
  have hv : Tendsto (fun T : ℕ => val ((T + 1) :: d)) atTop (𝓝 0) := by
    simp only [fun T => val_cons (T + 1) d hd]
    refine tendsto_const_nhds.div_atTop ?_
    refine tendsto_atTop_add_const_right _ _ ?_
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hq := q_pos b hb
  simp only [fun T => val_append b ((T + 1) :: d) (hpos T)]
  have h := ((tendsto_const_nhds (x := (convergentMatrix b 0 0 : ℝ))).mul hv).add
    (tendsto_const_nhds (x := (convergentMatrix b 0 1 : ℝ))) |>.div
    (((tendsto_const_nhds (x := (convergentMatrix b 1 0 : ℝ))).mul hv).add
    (tendsto_const_nhds (x := (convergentMatrix b 1 1 : ℝ)))) (by simpa using hq.ne')
  simpa [val, Pi.div_def] using h

private theorem measurableSet_fundInterval (α β : ℝ) : MeasurableSet (fundInterval α β) := by
  unfold fundInterval
  split_ifs
  · exact measurableSet_Ico
  · exact measurableSet_Ioc

/-- The integral over $\langle \alpha, \alpha + \delta \rangle$ as a signed interval integral. -/
private theorem setIntegral_fundInterval (F : ℝ → ℝ) (α δ : ℝ) (hδ : δ ≠ 0) :
    ∫ x in fundInterval α (α + δ), F x = |δ| * ((∫ x in α..α + δ, F x) / δ) := by
  rcases hδ.lt_or_gt with h | h
  · have hf : fundInterval α (α + δ) = Ioc (α + δ) α := by
      simp [fundInterval, not_lt.2 (by linarith : α + δ ≤ α)]
    rw [hf, ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_symm,
      abs_of_neg h]
    field_simp
  · rw [fundInterval_of_lt (by linarith), integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith), abs_of_pos h]
    field_simp

/-- Averages of a continuous function over shrinking intervals converge to its value. -/
private theorem tendsto_intervalIntegral_div {F : ℝ → ℝ} (hF : Continuous F) {r : ℝ}
    {u δ : ℕ → ℝ} (hu : Tendsto u atTop (𝓝 r)) (hδ : Tendsto δ atTop (𝓝 0))
    (hδ0 : ∀ᶠ t in atTop, δ t ≠ 0) :
    Tendsto (fun t => (∫ x in u t..u t + δ t, F x) / δ t) atTop (𝓝 (F r)) := by
  have hv : Tendsto (fun t => u t + δ t) atTop (𝓝 r) := by simpa using hu.add hδ
  have h := intervalIntegral.integral_sub_linear_isLittleO_of_tendsto_ae (a := r) (c := F r)
    (l := 𝓝 r) (l' := 𝓝 r) (hF.stronglyMeasurableAtFilter _ _)
    ((hF.tendsto r).mono_left inf_le_left) hu hv
  have h2 := h.tendsto_div_nhds_zero.add_const (F r)
  rw [zero_add] at h2
  refine h2.congr' ?_
  filter_upwards [hδ0] with t ht
  simp only [Pi.sub_apply, add_sub_cancel_left, smul_eq_mul]
  field_simp
  ring

private theorem tendsto_linear_div (α β γ η : ℝ) (hη : η ≠ 0) :
    Tendsto (fun t : ℕ => (α + t * β) / (γ + t * η)) atTop (𝓝 (β / η)) := by
  have h1 : Tendsto (fun t : ℕ => α / t + β) atTop (𝓝 (0 + β)) :=
    (tendsto_const_div_atTop_nhds_zero_nat α).add tendsto_const_nhds
  have h2 : Tendsto (fun t : ℕ => γ / t + η) atTop (𝓝 (0 + η)) :=
    (tendsto_const_div_atTop_nhds_zero_nat γ).add tendsto_const_nhds
  rw [zero_add] at h1 h2
  refine (h1.div h2 hη).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have ht' : (t : ℝ) ≠ 0 := by positivity
  simp only [Pi.div_apply]
  rw [div_add' _ _ _ ht', div_add' _ _ _ ht', div_div_div_cancel_right₀ ht', mul_comm β,
    mul_comm η]

private theorem tendsto_linear_atTop (γ η : ℝ) (hη : 0 < η) :
    Tendsto (fun t : ℕ => γ + t * η) atTop atTop :=
  tendsto_atTop_add_const_left _ _ (tendsto_natCast_atTop_atTop.atTop_mul_const hη)

/-- The analytic core: symmetric masses of the cylinders $(a, t)$ and $(t, \overleftarrow{a})$
force $F(p/q) = \frac{q}{p + q} F(0)$. -/
private theorem core {F : ℝ → ℝ} (hF : Continuous F) {p' p q' q s : ℝ} (hp' : 0 ≤ p')
    (hp : 0 ≤ p) (hq' : 0 ≤ q') (hq : 0 < q) (hs : |s| = 1)
    (hint : ∀ t : ℕ, 1 ≤ t →
      ∫ x in fundInterval ((p' + t * p) / (q' + t * q))
          ((p' + t * p) / (q' + t * q) + s / ((q' + t * q) * (q' + (t + 1) * q))), F x =
        ∫ x in fundInterval (q / (q' + t * q))
          (q / (q' + t * q) + s / ((q' + t * q) * (p' + q' + t * (p + q)))), F x) :
    F (p / q) = q / (p + q) * F 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, abs_zero] at hs
    exact zero_ne_one hs
  have hD1 : ∀ t : ℕ, 1 ≤ t → 0 < (q' + t * q) * (q' + (t + 1) * q) := by
    intro t ht
    have : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have h1 : 0 < q' + t * q := by nlinarith
    have h2 : 0 < q' + (t + 1) * q := by nlinarith
    positivity
  have hD2 : ∀ t : ℕ, 1 ≤ t → 0 < (q' + t * q) * (p' + q' + t * (p + q)) := by
    intro t ht
    have : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have h1 : 0 < q' + t * q := by nlinarith
    have h2 : 0 < p' + q' + t * (p + q) := by nlinarith
    positivity
  set A : ℕ → ℝ := fun t =>
    (∫ x in (p' + t * p) / (q' + t * q)..(p' + t * p) / (q' + t * q) +
      s / ((q' + t * q) * (q' + (t + 1) * q)), F x) /
      (s / ((q' + t * q) * (q' + (t + 1) * q))) with hA
  set B : ℕ → ℝ := fun t =>
    (∫ x in q / (q' + t * q)..q / (q' + t * q) +
      s / ((q' + t * q) * (p' + q' + t * (p + q))), F x) /
      (s / ((q' + t * q) * (p' + q' + t * (p + q)))) with hB
  set ρ : ℕ → ℝ := fun t => (q' + (t + 1) * q) / (p' + q' + t * (p + q)) with hρ
  -- the symmetry, rewritten as an identity between averages
  have hAB : ∀ᶠ t in atTop, A t = ρ t * B t := by
    filter_upwards [eventually_ge_atTop 1] with t ht
    have h1 := hD1 t ht
    have h2 := hD2 t ht
    have h := hint t ht
    rw [setIntegral_fundInterval _ _ _ (div_ne_zero hs0 h1.ne'),
      setIntegral_fundInterval _ _ _ (div_ne_zero hs0 h2.ne'), abs_div, abs_div, hs,
      abs_of_pos h1, abs_of_pos h2] at h
    have h3 : 0 < p' + q' + t * (p + q) := by
      have : (1 : ℝ) ≤ t := by exact_mod_cast ht
      nlinarith
    have h4 : 0 < q' + (t + 1) * q := by
      have : (1 : ℝ) ≤ t := by exact_mod_cast ht
      nlinarith
    simp only [hA, hB, hρ]
    field_simp at h ⊢
    linear_combination h
  -- limits of the endpoints, lengths and length ratio
  have hden : Tendsto (fun t : ℕ => q' + t * q) atTop atTop := tendsto_linear_atTop q' q hq
  have hu : Tendsto (fun t : ℕ => (p' + t * p) / (q' + t * q)) atTop (𝓝 (p / q)) :=
    tendsto_linear_div p' p q' q hq.ne'
  have hδ : Tendsto (fun t : ℕ => s / ((q' + t * q) * (q' + (t + 1) * q))) atTop (𝓝 0) := by
    refine tendsto_const_nhds.div_atTop (hden.atTop_mul_atTop₀ ?_)
    have := tendsto_linear_atTop (q' + q) q hq
    refine this.congr fun t => ?_
    ring
  have hw : Tendsto (fun t : ℕ => q / (q' + t * q)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hε : Tendsto (fun t : ℕ => s / ((q' + t * q) * (p' + q' + t * (p + q)))) atTop
      (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (hden.atTop_mul_atTop₀ (tendsto_linear_atTop (p' + q') (p + q) (by linarith)))
  have hρlim : Tendsto ρ atTop (𝓝 (q / (p + q))) := by
    have := tendsto_linear_div (q' + q) q (p' + q') (p + q) (by linarith)
    refine this.congr fun t => ?_
    simp only [hρ]
    congr 1
    ring
  have hAlim : Tendsto A atTop (𝓝 (F (p / q))) :=
    tendsto_intervalIntegral_div hF hu hδ
      ((eventually_ge_atTop 1).mono fun t ht => div_ne_zero hs0 (hD1 t ht).ne')
  have hBlim : Tendsto B atTop (𝓝 (F 0)) :=
    tendsto_intervalIntegral_div hF hw hε
      ((eventually_ge_atTop 1).mono fun t ht => div_ne_zero hs0 (hD2 t ht).ne')
  exact tendsto_nhds_unique hAlim ((hρlim.mul hBlim).congr' (hAB.mono fun t ht => ht.symm))

/-- The one-digit extension step (the source's Lemma 3.1): if the fundamental intervals of
$(a, t)$ and $(t, \overleftarrow{a})$ carry the same integral of $f$ for every digit $t \ge 1$, then
$f(r) = f(0)/(1 + r)$ at $r = [0; a_1, \ldots, a_n]$. -/
private theorem density_val_eq {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) {a : List ℕ}
    (ha : ∀ x ∈ a, 0 < x)
    (hsym : ∀ t : ℕ, 1 ≤ t →
      ∫ x in cfCylinder (a ++ [t]), f x = ∫ x in cfCylinder (t :: a.reverse), f x) :
    f (val a) = f 0 / (1 + val a) := by
  obtain ⟨h00, h01, h10, -, -⟩ := entries a ha
  have hq := q_pos a ha
  -- a continuous extension of `f` from `[0, 1]` to the real line
  set F : ℝ → ℝ := fun x => f (max 0 (min 1 x))
  have hF : Continuous F :=
    hf.comp_continuous (continuous_const.max (continuous_const.min continuous_id))
      fun x => ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hFf : ∀ x ∈ Icc (0 : ℝ) 1, F x = f x := fun x hx => by
    simp [F, hx.1, hx.2]
  have hcyl : ∀ b : List ℕ, ∀ α β : ℝ, cfCylinder b =ᵐ[volume] fundInterval α β →
      ∫ x in cfCylinder b, f x = ∫ x in fundInterval α β, F x := by
    intro b α β hb
    rw [← setIntegral_congr_set hb]
    refine setIntegral_congr_fun₀
      ((measurableSet_fundInterval α β).nullMeasurableSet.congr hb.symm) fun x hx => ?_
    exact (hFf x ⟨hx.1.1, hx.1.2.le⟩).symm
  have key := core (p' := (convergentMatrix a 0 0 : ℝ)) (p := (convergentMatrix a 0 1 : ℝ))
    (q' := (convergentMatrix a 1 0 : ℝ)) (q := (convergentMatrix a 1 1 : ℝ))
    (s := (-1) ^ (a.length + 1)) hF (by exact_mod_cast h00) (by exact_mod_cast h01)
    (by exact_mod_cast h10) hq (by simp) fun t ht => by
      obtain ⟨-, h2, -, h4⟩ := cfCylinder_reverse_append_cons_ae_eq a ha t ht
      rw [← hcyl _ _ _ h2, ← hcyl _ _ _ h4]
      exact hsym t ht
  have hval := val_mem_Icc a ha
  rw [← hFf _ hval, ← hFf 0 ⟨le_rfl, zero_le_one⟩]
  change F ((convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ)) = _
  rw [key]
  simp only [val]
  field_simp
  ring

end density_eq_gaussKuzmin_of_reverse_symmetric

open density_eq_gaussKuzmin_of_reverse_symmetric in
set_option linter.unusedVariables false in
/-- **Symmetric one-digit extensions fix the density at a rational point.** Let $f$ be a real
function that is continuous and nonnegative on $[0, 1]$ with $\int_0^1 f(x)\,dx = 1$. Let
$a = (a_1, \dots, a_n)$ be a string of positive integers, let $p$ and $q$ be the upper-right and
lower-right entries of its convergent matrix $C(a)$, so that $p/q = [0; a_1, \dots, a_n]$, and let
$\overleftarrow{a}$ be the reverse of $a$. Write $I(b)$ for the fundamental interval of a string
$b$, $(a, t)$ for $a$ followed by $t$, and $(t, \overleftarrow{a})$ for $t$ followed by
$\overleftarrow{a}$. If $\int_{I(a, t)} f(x)\,dx = \int_{I(t, \overleftarrow{a})} f(x)\,dx$ for
every integer $t \ge 1$, then $f(p/q) = f(0)/(1 + p/q)$.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 3.1 (`integers-2025-A89-lem-3-1`). -/
theorem density_cfValue_eq_of_append_symmetric (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 1)) (hf0 : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f x)
    (hf1 : ∫ x in (0 : ℝ)..1, f x = 1) (a : List ℕ) (ha : (∀ x ∈ a, 0 < x))
    (hsym : ∀ t : ℕ, 1 ≤ t →
      ∫ x in cfCylinder (a ++ [t]), f x = ∫ x in cfCylinder (t :: a.reverse), f x) :
    f ((convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ)) = f 0 / (1 +
        (convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ)) :=
  density_val_eq hf ha hsym

open density_eq_gaussKuzmin_of_reverse_symmetric in
set_option linter.unusedVariables false in
/-- **Reversal symmetry forces the Gauss–Kuzmin density.** Let $f$ be a real function that is
continuous and nonnegative on $[0, 1]$ with $\int_0^1 f(x)\,dx = 1$, and let $S$ be an infinite
set of natural numbers. Write $I(a)$ for the fundamental interval of a string $a$ and
$\overleftarrow{a}$ for the reverse of $a$. If
$\int_{I(a)} f(x)\,dx = \int_{I(\overleftarrow{a})} f(x)\,dx$ for every string $a$ of positive
integers whose length lies in $S$, then $f(x) = \frac{1}{\log 2 \cdot (1 + x)}$ for every
$x \in [0, 1]$.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Theorem 1 (`integers-2025-A89-thm-1`). -/
theorem density_eq_gaussKuzmin_of_reverse_symmetric (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 1)) (hf0 : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f x)
    (hf1 : ∫ x in (0 : ℝ)..1, f x = 1) (S : Set ℕ) (hS : S.Infinite)
    (hsym : ∀ a : List ℕ, (∀ x ∈ a, 0 < x) → a.length ∈ S →
      ∫ x in cfCylinder a, f x = ∫ x in cfCylinder a.reverse, f x) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, f x = 1 / (log 2 * (1 + x)) := by
  -- Step 1: the identity at the values of strings whose length plus one lies in `S`.
  have hE : ∀ a : List ℕ, (∀ x ∈ a, 0 < x) → a.length + 1 ∈ S →
      f (val a) = f 0 / (1 + val a) := by
    intro a ha hlen
    refine density_cfValue_eq_of_append_symmetric f hf hf0 hf1 a ha fun t ht => ?_
    have hpos : ∀ x ∈ a ++ [t], 0 < x := by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact ha x hx
      · rw [List.mem_singleton.1 hx]
        exact ht
    simpa using hsym (a ++ [t]) hpos (by simpa using hlen)
  -- Step 2: these values are dense in `[0, 1]`, so the identity holds on `[0, 1]`.
  set E : Set ℝ := {y | ∃ a : List ℕ, (∀ z ∈ a, 0 < z) ∧ a.length + 1 ∈ S ∧ val a = y}
  have hEsub : E ⊆ Icc 0 1 := by
    rintro _ ⟨a, ha, -, rfl⟩
    exact val_mem_Icc a ha
  have hEeq : EqOn f (fun x => f 0 / (1 + x)) E := by
    rintro _ ⟨a, ha, hlen, rfl⟩
    exact hE a ha hlen
  have hvals : ∀ b : List ℕ, (∀ z ∈ b, 0 < z) → val b ∈ closure E := by
    intro b hb
    obtain ⟨k, hkS, hk⟩ := hS.exists_gt (b.length + 1)
    refine mem_closure_of_tendsto
      (tendsto_val_append b hb (List.replicate (k - (b.length + 2)) 1) (by simp))
      (Eventually.of_forall fun T => ⟨_, ?_, ?_, rfl⟩)
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hb x hx
      · rcases List.mem_cons.1 hx with rfl | hx
        · omega
        · rw [List.eq_of_mem_replicate hx]
          exact one_pos
    · simp only [List.length_append, List.length_cons, List.length_replicate]
      convert hkS using 1
      omega
  have hdense : Icc (0 : ℝ) 1 ⊆ closure E := by
    intro x hx
    refine closure_minimal ?_ isClosed_closure (mem_closure_vals hx)
    rintro _ ⟨b, hb, rfl⟩
    exact hvals b hb
  have hg : ContinuousOn (fun x : ℝ => f 0 / (1 + x)) (Icc 0 1) :=
    continuousOn_const.div (continuousOn_const.add continuousOn_id) fun x hx => by
      linarith [hx.1]
  have hEq : EqOn f (fun x => f 0 / (1 + x)) (Icc 0 1) :=
    hEeq.of_subset_closure hf hg hEsub hdense
  -- Step 3: the normalization fixes `f 0 = 1 / log 2`.
  have hint : ∫ x in (0 : ℝ)..1, f x = f 0 * log 2 := by
    rw [intervalIntegral.integral_congr (g := fun x => f 0 / (1 + x)) fun x hx =>
      hEq (by rwa [uIcc_of_le zero_le_one] at hx)]
    simp only [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have h := intervalIntegral.integral_comp_add_left (a := 0) (b := 1) (fun x : ℝ => x⁻¹) 1
    rw [h, integral_inv (by norm_num [mem_uIcc])]
    norm_num
  have hlog : 0 < log 2 := log_pos one_lt_two
  have hf0' : f 0 = 1 / log 2 := by
    rw [eq_div_iff hlog.ne', ← hint, hf1]
  intro x hx
  have hx' := hEq hx
  simp only at hx'
  rw [hx', hf0', div_div]

end

end MetaMathlibExt
