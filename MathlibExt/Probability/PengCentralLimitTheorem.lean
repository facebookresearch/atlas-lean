/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.SublinearExpectationSpace
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Peng's central limit theorem under a sublinear expectation

`PengLimitTheoremsWanted.clt` proves convergence of normalized sums to the G-normal law with the
same upper and lower variances, for every Lipschitz test function on the real line.

## Proof

Independence expresses the law of a sum by iterating the operator
`step S X t f x = S.E (fun ω ↦ f (x + t * X ω))`. G-normal stability evaluates the corresponding
iteration for the limiting law exactly.

Averaging a Lipschitz function twice over intervals of length `d` gives a Lipschitz second
derivative and hence a uniform cubic Taylor remainder. Centering and the two variance identities
make the expectations of its quadratic Taylor polynomial agree for the two laws. Sublinearity
lets us move each spatial average outside the expectation in one direction, by dyadic subdivision.
Thus we can compare the two iterations by smoothing only one side, and then interchange the laws.
For fixed `d`, the accumulated Taylor error is of order `n * (1 / √n)³`. The cost of smoothing
the test function at the two endpoints is at most `4 * K * d`.
-/

open MathlibExt.Probability.SublinearExpectation
open Filter Topology Finset

namespace MathlibExt.Probability.SublinearExpectation.PengLimitTheoremsWanted

section

variable {Ω : Type*} {S : SublinearExpectationSpace Ω} {X : Ω → ℝ}

private theorem mem_comp_lip (hX : X ∈ S.H) {f : ℝ → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) : (fun ω ↦ f (X ω)) ∈ S.H := by
  exact S.comp_mem 1 (fun _ ↦ X) (fun _ ↦ hX) _
    (isLocLip_of_lipschitzWith (hf.comp (LipschitzWith.eval (α := fun _ : Fin 1 ↦ ℝ) 0)))

private theorem mul_mem (hX : X ∈ S.H) (a : ℝ) : (fun ω ↦ a * X ω) ∈ S.H :=
  mem_comp_lip hX (lipschitzWith_smul a)

private theorem sq_mem (hX : X ∈ S.H) : (fun ω ↦ X ω ^ 2) ∈ S.H := by
  refine S.comp_mem 1 (fun _ ↦ X) (fun _ ↦ hX) (fun v ↦ v 0 ^ 2) ⟨1, 1, ?_⟩
  intro x y
  have hx := norm_le_pi_norm x 0
  have hy := norm_le_pi_norm y 0
  have hd := norm_le_pi_norm (x - y) 0
  simp only [Pi.sub_apply, Real.norm_eq_abs] at hx hy hd
  rw [sq_sub_sq, abs_mul]
  simp only [one_mul, pow_one]
  exact mul_le_mul ((abs_add_le _ _).trans (by linarith)) hd (abs_nonneg _) (by positivity)

/-- One increment of size `t * X`, starting from `x`. -/
private noncomputable def step (S : SublinearExpectationSpace Ω) (X : Ω → ℝ) (t : ℝ)
    (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  S.E (fun ω ↦ f (x + t * X ω))

private theorem step_mem (hX : X ∈ S.H) {K : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith K f)
    (x t : ℝ) : (fun ω ↦ f (x + t * X ω)) ∈ S.H :=
  mem_comp_lip (S.add_mem (S.const_mem x) (mul_mem hX t)) hf

private theorem step_le_add (hX : X ∈ S.H) {K L : NNReal} {f g : ℝ → ℝ}
    (hf : LipschitzWith K f) (hg : LipschitzWith L g) {c : ℝ} (h : ∀ x, f x ≤ c + g x)
    (t x : ℝ) : step S X t f x ≤ c + step S X t g x := by
  rw [step, step, ← S.expectation_const_add (step_mem hX hg x t)]
  exact S.mono _ (S.add_mem (S.const_mem c) (step_mem hX hg x t)) _ (step_mem hX hf x t)
    (fun ω ↦ h _)

private theorem step_lip (hX : X ∈ S.H) {K : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith K f)
    (t : ℝ) : LipschitzWith K (step S X t f) := by
  have aux (x y : ℝ) : step S X t f x ≤ (K : ℝ) * |x - y| + step S X t f y := by
    let c := (K : ℝ) * |x - y|
    rw [step, step, ← S.expectation_const_add (step_mem hX hf y t)]
    apply S.mono _ (S.add_mem (S.const_mem c) (step_mem hX hf y t)) _ (step_mem hX hf x t)
    intro ω
    change f (x + t * X ω) ≤ c + f (y + t * X ω)
    have h := hf.dist_le_mul (x + t * X ω) (y + t * X ω)
    simp only [Real.dist_eq, add_sub_add_right_eq_sub] at h
    linarith [le_abs_self (f (x + t * X ω) - f (y + t * X ω))]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, Real.dist_eq, abs_le]
  constructor
  · have h := aux y x
    rw [abs_sub_comm y x] at h
    linarith
  · linarith [aux x y]

private theorem affine_isLocLip {K : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith K f) (x a : ℝ) :
    IsLocLip (fun z ↦ f (x + a * z)) :=
  isLocLip_of_lipschitzWith (hf.comp ((LipschitzWith.const x).add (lipschitzWith_smul a)))

private theorem iid_steps (S : SublinearExpectationSpace Ω) (X : ℕ → Ω → ℝ)
    (hX : ∀ i, X i ∈ S.H)
    (hid : ∀ i, SublinearExpectationSpace.IdentDistrib S S (X (i + 1)) (X i))
    (hind : ∀ i, S.IndepFrom (X (i + 1)) (fun ω (j : Fin (i + 1)) ↦ X j ω))
    (t : ℝ) (n : ℕ) {K : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith K f) :
    S.E (fun ω ↦ f (t * ∑ j ∈ range n, X j ω)) = (step S (X 0) t)^[n] f 0 := by
  have hd (i : ℕ) : SublinearExpectationSpace.IdentDistrib S S (X i) (X 0) := by
    induction i with
    | zero => exact fun _ _ ↦ rfl
    | succ i ih => exact fun g hg ↦ (hid i g hg).trans (ih g hg)
  induction n generalizing f with
  | zero => simpa using S.const (f 0)
  | succ n ih =>
    rw [Function.iterate_succ_apply, ← ih (step_lip (hX 0) hf t)]
    cases n with
    | zero => simp [step, S.const]
    | succ k =>
      let A : (Fin (k + 1) → ℝ) →L[ℝ] ℝ := ∑ j, ContinuousLinearMap.proj j
      let F (p : (Fin (k + 1) → ℝ) × ℝ) := f (t * (A p.1 + p.2))
      have hF : IsLocLip F := isLocLip_of_lipschitzWith (hf.comp
        ((lipschitzWith_smul t).comp ((A.lipschitzWith.comp LipschitzWith.prod_fst).add
          LipschitzWith.prod_snd)))
      have he := hind k F hF
      simp only [F, A, _root_.sum_apply, ContinuousLinearMap.proj_apply] at he
      have heq (ω : Ω) := Fin.sum_univ_eq_sum_range (fun j ↦ X j ω) (k + 1)
      simp_rw [heq] at he
      simp only [sum_range_succ (n := k + 1)]
      rw [he]
      congr 1
      ext ω
      simp only [step, mul_add]
      exact hd (k + 1) _ (affine_isLocLip hf _ t)

private theorem normal_comp {Z : Ω → ℝ} (hZ : S.IsGNormal Z) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) {K : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith K f) (x : ℝ) :
    step S Z a (step S Z b f) x = step S Z (Real.sqrt (a ^ 2 + b ^ 2)) f x := by
  obtain ⟨_, Z', _, hd, hi, hs⟩ := hZ
  let F (p : ℝ × ℝ) := f (x + (a * p.1 + b * p.2))
  have hF : IsLocLip F := isLocLip_of_lipschitzWith (hf.comp ((LipschitzWith.const x).add
    (((lipschitzWith_smul a).comp LipschitzWith.prod_fst).add
      ((lipschitzWith_smul b).comp LipschitzWith.prod_snd))))
  have h := hi F hF
  have hsc := hs a b ha hb (fun z ↦ f (x + z))
    (isLocLip_of_lipschitzWith (hf.comp ((LipschitzWith.const x).add LipschitzWith.id)))
  change _ = S.E (fun ω ↦ f (x + Real.sqrt (a ^ 2 + b ^ 2) * Z ω))
  rw [← hsc]
  change _ = S.E (fun ω ↦ F (Z ω, Z' ω))
  rw [h]
  unfold step
  apply congrArg S.E
  funext ω
  simp only [F, ← add_assoc]
  exact (hd _ (affine_isLocLip hf _ b)).symm

private theorem normal_steps {Z : Ω → ℝ} (hZ : S.IsGNormal Z) {t : ℝ} (ht : 0 ≤ t)
    (n : ℕ) {K : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith K f) :
    (step S Z t)^[n] f = step S Z (Real.sqrt n * t) f := by
  induction n with
  | zero =>
    ext x
    simp [step, S.const]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    ext x
    rw [normal_comp hZ ht (mul_nonneg (Real.sqrt_nonneg _) ht) hf]
    congr 1
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) ht)).mp
    rw [Real.sq_sqrt (by positivity), mul_pow, mul_pow, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
    push_cast
    ring

/-! ### Expectations of quadratic Taylor polynomials -/

private theorem mean_mul_zero (hX : X ∈ S.H) (h : S.E X = 0) (h' : S.E (fun ω ↦ -X ω) = 0)
    (a : ℝ) : S.E (fun ω ↦ a * X ω) = 0 := by
  rcases le_or_gt 0 a with ha | ha
  · simpa [Pi.smul_def, smul_eq_mul, h] using S.pos_hom X hX a ha
  · have hn := mem_comp_lip hX (LipschitzWith.id (α := ℝ)).neg
    have hh := S.pos_hom _ hn (-a) (neg_nonneg.mpr ha.le)
    change S.E (fun ω ↦ (-a) * (-X ω)) = (-a) * S.E (fun ω ↦ -X ω) at hh
    simpa [h'] using hh

private theorem mean_add (hX : X ∈ S.H) {Y : Ω → ℝ} (hY : Y ∈ S.H)
    (h : S.E X = 0) (h' : S.E (fun ω ↦ -X ω) = 0) : S.E (X + Y) = S.E Y := by
  have h₁ := S.subadd X hX Y hY
  have hn := mem_comp_lip hX (LipschitzWith.id (α := ℝ)).neg
  have h₂ := S.subadd (X + Y) (S.add_mem hX hY) (-X) hn
  have he : X + Y + -X = Y := by abel
  change S.E (-X) = 0 at h'
  rw [he, h'] at h₂
  linarith

private theorem quad_expect (hX : X ∈ S.H) (h : S.E X = 0) (h' : S.E (fun ω ↦ -X ω) = 0)
    (c a b : ℝ) : S.E (fun ω ↦ c + (a * X ω + b * X ω ^ 2)) =
      c + if 0 ≤ b then b * S.E (fun ω ↦ X ω ^ 2) else
        (-b) * S.E (fun ω ↦ -X ω ^ 2) := by
  have hL := mul_mem hX a
  have hQ := mul_mem (sq_mem hX) b
  rw [show S.E (fun ω ↦ c + (a * X ω + b * X ω ^ 2)) = _ from
    S.expectation_const_add (S.add_mem hL hQ) c]
  congr 1
  change S.E ((fun ω ↦ a * X ω) + fun ω ↦ b * X ω ^ 2) = _
  rw [mean_add hL hQ (mean_mul_zero hX h h' a) (by
    simpa using mean_mul_zero hX h h' (-a))]
  split_ifs with hb
  · exact S.pos_hom _ (sq_mem hX) _ hb
  · have hn := mem_comp_lip (sq_mem hX) (LipschitzWith.id (α := ℝ)).neg
    have hh := S.pos_hom _ hn (-b) (neg_nonneg.mpr (le_of_not_ge hb))
    change S.E (fun ω ↦ (-b) * (-X ω ^ 2)) = _ at hh
    simpa using hh

/-- A finite bound for the absolute third moment, using only closure under squaring. -/
private noncomputable def momentBound (S : SublinearExpectationSpace Ω) (X : Ω → ℝ) :=
  S.E (fun ω ↦ 1 + (X ω ^ 2) ^ 2)

private theorem le_add_error {A B R : Ω → ℝ} (hA : A ∈ S.H) (hB : B ∈ S.H) (hR : R ∈ S.H)
    (hle : ∀ ω, A ω ≤ B ω + R ω) : S.E A ≤ S.E B + S.E R :=
  (S.mono _ (S.add_mem hB hR) _ hA hle).trans (S.subadd _ hB _ hR)

private theorem step_expansion (hX : X ∈ S.H) (hc : S.E X = 0) (hc' : S.E (fun ω ↦ -X ω) = 0)
    {K : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith K f) (x : ℝ)
    {a b D t : ℝ} (hD : 0 ≤ D) (ht : 0 ≤ t)
    (he : ∀ v, |f (x + v) - (f x + (a * v + b * v ^ 2))| ≤ D * |v| ^ 3) :
    |step S X t f x - (f x + if 0 ≤ b * t ^ 2 then (b * t ^ 2) * S.E (fun ω ↦ X ω ^ 2)
      else (-(b * t ^ 2)) * S.E (fun ω ↦ -X ω ^ 2))| ≤ (D * t ^ 3) * momentBound S X := by
  let P (ω : Ω) := f x + ((a * t) * X ω + (b * t ^ 2) * X ω ^ 2)
  let R (ω : Ω) := (D * t ^ 3) * (1 + (X ω ^ 2) ^ 2)
  have hP : P ∈ S.H := S.add_mem (S.const_mem _) (S.add_mem (mul_mem hX _) (mul_mem (sq_mem hX) _))
  have hm := S.add_mem (S.const_mem 1) (sq_mem (sq_mem hX))
  have hR : R ∈ S.H := mul_mem hm _
  have hER : S.E R = D * t ^ 3 * momentBound S X := S.pos_hom _ hm _ (by positivity)
  have hh (ω) : |f (x + t * X ω) - P ω| ≤ R ω := by
    have h := he (t * X ω)
    rw [abs_mul, abs_of_nonneg ht, mul_pow t |X ω|] at h
    have heq : f x + (a * (t * X ω) + b * (t * X ω) ^ 2) = P ω := by dsimp [P]; ring
    rw [heq] at h
    apply h.trans
    dsimp [R]
    rw [← mul_assoc]
    gcongr
    rcases le_or_gt |X ω| 1 with hx | hx
    · have h₁ : |X ω| ^ 3 ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
      nlinarith [sq_nonneg (X ω ^ 2)]
    · have h₁ : |X ω| ^ 3 ≤ |X ω| ^ 4 := pow_le_pow_right₀ hx.le (by decide)
      rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, sq_abs] at h₁
      linarith
  rw [← quad_expect hX hc hc' (f x) (a * t) (b * t ^ 2), ← hER]
  change |step S X t f x - S.E P| ≤ S.E R
  have H := step_mem hX hf x t
  have hi := le_add_error H hP hR (fun ω ↦ by linarith [(abs_le.mp (hh ω)).2])
  have lo := le_add_error hP H hR (fun ω ↦ by linarith [(abs_le.mp (hh ω)).1])
  rw [abs_le, step]
  exact ⟨by linarith, by linarith⟩

/-! ### Spatial averaging and sublinearity -/

open intervalIntegral

/-- The average over a translated interval of length `d`. -/
private noncomputable def avg (d : ℝ) (f : ℝ → ℝ) (x : ℝ) :=
  (∫ y in x..x + d, f y) / d

private theorem avg_eq (d x : ℝ) (f : ℝ → ℝ) :
    avg d f x = (∫ z in 0..d, f (x + z)) / d := by
  simp [avg, integral_comp_add_left]

private theorem avg_bound {d : ℝ} (hd : 0 < d) {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) {x y c : ℝ} (h : ∀ z ∈ Set.Icc 0 d, f (x + z) ≤ c + g (y + z)) :
    avg d f x ≤ c + avg d g y := by
  rw [avg_eq, avg_eq, div_le_iff₀ hd]
  have hg' : Continuous (fun z ↦ g (y + z)) := hg.comp (continuous_const.add continuous_id)
  have hf' : Continuous (fun z ↦ f (x + z)) := hf.comp (continuous_const.add continuous_id)
  have hh := integral_mono_on (μ := MeasureTheory.volume) hd.le (hf'.intervalIntegrable 0 d)
    ((continuous_const.add hg').intervalIntegrable 0 d) h
  simp only [Pi.add_apply] at hh
  rw [integral_add intervalIntegrable_const (hg'.intervalIntegrable 0 d)] at hh
  simp only [integral_const, sub_zero, smul_eq_mul] at hh
  rw [add_mul, div_mul_cancel₀ _ hd.ne']
  linarith

private theorem avg_lip {d : ℝ} (hd : 0 < d) {K : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith K f) : LipschitzWith K (avg d f) := by
  have hl (x y : ℝ) : avg d f x ≤ (K : ℝ) * |x - y| + avg d f y := by
    apply avg_bound hd hf.continuous hf.continuous
    intro z _
    have h := hf.dist_le_mul (x + z) (y + z)
    simp only [Real.dist_eq, add_sub_add_right_eq_sub] at h
    linarith [le_abs_self (f (x + z) - f (y + z))]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, Real.dist_eq, abs_le]
  have h := hl y x
  rw [abs_sub_comm y x] at h
  exact ⟨by linarith, by linarith [hl x y]⟩

private theorem avg_close {d : ℝ} (hd : 0 < d) {K : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith K f) (x : ℝ) : |avg d f x - f x| ≤ K * d := by
  have h (z : ℝ) (hz : z ∈ Set.Icc 0 d) : |f (x + z) - f x| ≤ K * d := by
    have hh := hf.dist_le_mul (x + z) x
    simp only [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg hz.1] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hz.2 K.2)
  have hconst : avg d (fun _ ↦ f x) x = f x := by simp [avg, hd.ne']
  have hu := avg_bound hd hf.continuous (continuous_const (y := f x)) (x := x) (y := x)
    (c := K * d) (fun z hz ↦ by linarith [(abs_le.mp (h z hz)).2])
  have hl := avg_bound hd (continuous_const (y := f x)) hf.continuous (x := x) (y := x)
    (c := K * d) (fun z hz ↦ by linarith [(abs_le.mp (h z hz)).1])
  rw [hconst] at hu hl
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem avg_split {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    avg d f x = (avg (d / 2) f x + avg (d / 2) f (x + d / 2)) / 2 := by
  unfold avg
  rw [show x + d / 2 + d / 2 = x + d by ring]
  have h := integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hf.intervalIntegrable x (x + d / 2)) (hf.intervalIntegrable (x + d / 2) (x + d))
  generalize (∫ u in x..x + d, f u) = z at h ⊢
  generalize (∫ u in x..x + d / 2, f u) = a at h ⊢
  generalize (∫ u in x + d / 2..x + d, f u) = b at h ⊢
  field_simp
  linarith

private theorem step_avg_split {d : ℝ} (hd : 0 < d) (hX : X ∈ S.H) {f : ℝ → ℝ}
    {K : NNReal} (hf : LipschitzWith K f) (x t : ℝ) :
    step S X t (avg d f) x ≤
      (step S X t (avg (d / 2) f) x + step S X t (avg (d / 2) f) (x + d / 2)) / 2 := by
  have hA := avg_lip (half_pos hd) hf
  let U (ω : Ω) := avg (d / 2) f (x + t * X ω)
  let V (ω : Ω) := avg (d / 2) f (x + d / 2 + t * X ω)
  have hU : U ∈ S.H := step_mem hX hA x t
  have hV : V ∈ S.H := step_mem hX hA (x + d / 2) t
  have hsum := S.subadd _ hU _ hV
  have he : step S X t (avg d f) x = S.E ((1 / 2 : ℝ) • (U + V)) := by
    apply congrArg S.E
    funext ω
    rw [avg_split hd hf.continuous]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, U, V, add_right_comm x (t * X ω) (d / 2)]
    ring
  rw [he, S.pos_hom _ (S.add_mem hU hV) _ (by norm_num)]
  change _ ≤ (S.E U + S.E V) / 2
  linarith

/-- Sublinearity gives the midpoint inequality on each dyadic subinterval.
The approximation error after `m` subdivisions is at most `2 * K * d / 2 ^ m`. -/
private theorem step_avg_le (hX : X ∈ S.H) {f : ℝ → ℝ} {K : NNReal} (hf : LipschitzWith K f)
    (t : ℝ) {d : ℝ} (hd : 0 < d) (x : ℝ) :
    step S X t (avg d f) x ≤ avg d (step S X t f) x := by
  have hg := step_lip hX hf t
  have aux (m : ℕ) (d : ℝ) (hd : 0 < d) (x : ℝ) :
      step S X t (avg d f) x ≤ avg d (step S X t f) x + (2 * (K : ℝ) * d) / 2 ^ m := by
    induction m generalizing d x with
    | zero =>
      have hu := step_le_add hX (avg_lip hd hf) hf
        (c := K * d) (fun y ↦ by linarith [(abs_le.mp (avg_close hd hf y)).2]) t x
      have hl := (abs_le.mp (avg_close hd hg x)).1
      simp only [pow_zero, div_one]
      linarith
    | succ m ih =>
      have h₁ := ih (d / 2) (half_pos hd) x
      have h₂ := ih (d / 2) (half_pos hd) (x + d / 2)
      rw [avg_split hd hg.continuous x]
      apply (step_avg_split hd hX hf x t).trans
      simp only [pow_succ, div_mul_eq_div_div]
      linarith [show (2 * (K : ℝ) * (d / 2)) / 2 ^ m = (2 * K * d) / 2 ^ m / 2 by ring]
  have hp : Tendsto (fun m : ℕ ↦ (2 : ℝ) ^ m) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have he : Tendsto (fun m : ℕ ↦ (2 * (K : ℝ) * d) / 2 ^ m) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hp
  have hh := ge_of_tendsto ((tendsto_const_nhds (x := avg d (step S X t f) x)).add he)
    (Filter.Eventually.of_forall (fun m ↦ aux m d hd x))
  simpa using hh

private theorem double_avg_le (hX : X ∈ S.H) {K : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith K f)
    (t : ℝ) {d : ℝ} (hd : 0 < d) (x : ℝ) :
    step S X t (avg d (avg d f)) x ≤ avg d (avg d (step S X t f)) x := by
  apply (step_avg_le hX (avg_lip hd hf) t hd x).trans
  have h := avg_bound hd (step_lip hX (avg_lip hd hf) t).continuous
    (avg_lip hd (step_lip hX hf t)).continuous (x := x) (y := x) (c := 0)
    (fun z _ ↦ by simpa using step_avg_le hX hf t hd (x + z))
  simpa using h

/-! ### Taylor expansion of the twice-averaged test function -/

private noncomputable def diffQuot (d : ℝ) (f : ℝ → ℝ) (x : ℝ) :=
  (f (x + d) - f x) / d

private theorem avg_hasDeriv (d : ℝ) {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (avg d f) (diffQuot d f x) x := by
  let F (u : ℝ) := ∫ v in 0..u, f v
  have hF (u : ℝ) : HasDerivAt F (f u) u :=
    integral_hasDerivAt_right (hf.intervalIntegrable 0 u)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have he : avg d f = fun u ↦ (F (u + d) - F u) / d := by
    funext u
    dsimp [avg, F]
    rw [integral_interval_sub_left (hf.intervalIntegrable 0 (u + d))
      (hf.intervalIntegrable 0 u)]
  rw [he]
  simpa only [diffQuot, mul_one, Pi.sub_apply, Function.comp_apply, id_eq] using
    (((hF (x + d)).comp x ((hasDerivAt_id x).add_const d)).sub (hF x)).div_const d

private theorem diffQuot_lip {K : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith K f) (d : ℝ) :
    LipschitzWith (‖d⁻¹‖₊ * (K + K)) (diffQuot d f) := by
  have hs : LipschitzWith K (fun x ↦ f (x + d)) := by
    exact LipschitzWith.of_dist_le_mul fun x y ↦ by simpa using hf.dist_le_mul (x + d) (y + d)
  change LipschitzWith _ (fun x ↦ (f (x + d) - f x) / d)
  simpa [Function.comp_def, div_eq_inv_mul] using (lipschitzWith_smul (β := ℝ) d⁻¹).comp (hs.sub hf)

private noncomputable def remainderBound (K : NNReal) (d : ℝ) : NNReal :=
  ‖d⁻¹‖₊ * (‖d⁻¹‖₊ * (K + K) + ‖d⁻¹‖₊ * (K + K))

private theorem avg_expansion {d : ℝ} (hd : 0 < d) {K : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith K f) (x : ℝ) :
    ∃ a b : ℝ, ∀ v, |avg d (avg d f) (x + v) - (avg d (avg d f) x + (a * v + b * v ^ 2))|
      ≤ (remainderBound K d : ℝ) * |v| ^ 3 := by
  let F := avg d (avg d f)
  let F₁ := diffQuot d (avg d f)
  let F₂ := diffQuot d (diffQuot d f)
  have h₀ (u : ℝ) : HasDerivAt F (F₁ u) u := avg_hasDeriv d (avg_lip hd hf).continuous u
  have h₁ (u : ℝ) : HasDerivAt F₁ (F₂ u) u := by
    have h := avg_hasDeriv d hf.continuous
    change HasDerivAt (fun x ↦ (avg d f (x + d) - avg d f x) / d) _ u
    simpa only [F₂, diffQuot, mul_one, Pi.sub_apply, Function.comp_apply, id_eq] using
      (((h (u + d)).comp u ((hasDerivAt_id u).add_const d)).sub (h u)).div_const d
  have h₂ := diffQuot_lip (diffQuot_lip hf d) d
  have e₀ : deriv F = F₁ := funext fun u ↦ (h₀ u).deriv
  have e₁ : deriv F₁ = F₂ := funext fun u ↦ (h₁ u).deriv
  have hcd₁ : ContDiff ℝ 1 F₁ := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num, contDiff_succ_iff_deriv, e₁]
    exact ⟨fun u ↦ (h₁ u).differentiableAt, by simp, contDiff_zero.mpr h₂.continuous⟩
  have hcd : ContDiff ℝ 2 F := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_deriv, e₀]
    exact ⟨fun u ↦ (h₀ u).differentiableAt, by simp, hcd₁⟩
  refine ⟨F₁ x, F₂ x / 2, fun v ↦ ?_⟩
  change |F (x + v) - (F x + (F₁ x * v + F₂ x / 2 * v ^ 2))| ≤ _
  by_cases hv : v = 0
  · simp [hv]
  have hx : x ≠ x + v := by grind
  obtain ⟨y, hy, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 1) hx hcd.contDiffOn
  have hwithin := (h₀ x).differentiableAt.derivWithin (uniqueDiffOn_uIcc hx x Set.left_mem_uIcc)
  rw [show (1 : ℕ) = 0 + 1 by decide, taylorWithinEval_succ, taylor_within_zero_eval] at he
  norm_num [iteratedDerivWithin_one, hwithin, iteratedDeriv_succ, iteratedDeriv_zero, e₀, e₁,
    Nat.factorial] at he
  have hdist := h₂.dist_le_mul y x
  simp only [Real.dist_eq] at hdist
  have hy' : |y - x| ≤ |v| := by
    rcases lt_or_gt_of_ne hv with hv | hv
    · rw [Set.uIoo_of_ge (by linarith : x + v ≤ x)] at hy
      rw [abs_of_nonpos (by linarith [hy.2] : y - x ≤ 0), abs_of_neg hv]
      linarith [hy.1]
    · rw [Set.uIoo_of_le (by linarith : x ≤ x + v)] at hy
      rw [abs_of_nonneg (by linarith [hy.1] : 0 ≤ y - x), abs_of_pos hv]
      linarith [hy.2]
  let L := remainderBound K d
  have hb : |F₂ y - F₂ x| ≤ (L : ℝ) * |v| := hdist.trans (mul_le_mul_of_nonneg_left hy' L.2)
  rw [show F (x + v) - (F x + (F₁ x * v + F₂ x / 2 * v ^ 2)) =
    (F₂ y - F₂ x) * v ^ 2 / 2 by linarith]
  rw [abs_div, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  change _ ≤ (L : ℝ) * |v| ^ 3
  calc
    _ ≤ |F₂ y - F₂ x| * |v| ^ 2 := by
      nlinarith [mul_nonneg (abs_nonneg (F₂ y - F₂ x)) (sq_nonneg |v|)]
    _ ≤ ((L : ℝ) * |v|) * |v| ^ 2 := mul_le_mul_of_nonneg_right hb (sq_nonneg _)
    _ = _ := by ring

private theorem avg_twice_close {d : ℝ} (hd : 0 < d) {K : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith K f) (x : ℝ) : |avg d (avg d f) x - f x| ≤ 2 * (K : ℝ) * d := by
  rw [← Real.dist_eq]
  have h₁ := avg_close hd (avg_lip hd hf) x
  have h₂ := avg_close hd hf x
  rw [← Real.dist_eq] at h₁ h₂
  linarith [dist_triangle (avg d (avg d f) x) (avg d f x) (f x)]

/-! ### Comparing the iterated expectations -/

variable {Ω' : Type*} {T : SublinearExpectationSpace Ω'} {Z : Ω' → ℝ}

private theorem step_comparison (hX : X ∈ S.H) (hx : S.E X = 0) (hx' : S.E (fun ω ↦ -X ω) = 0)
    (hZ : Z ∈ T.H) (hz : T.E Z = 0) (hz' : T.E (fun ω ↦ -Z ω) = 0)
    (hu : T.E (fun ω ↦ Z ω ^ 2) = S.E (fun ω ↦ X ω ^ 2))
    (hl : T.E (fun ω ↦ -Z ω ^ 2) = S.E (fun ω ↦ -X ω ^ 2)) {d t : ℝ} (hd : 0 < d)
    (ht : 0 ≤ t) {K : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith K f) (x : ℝ) :
    step S X t (avg d (avg d f)) x ≤ avg d (avg d (step T Z t f)) x +
      remainderBound K d * t ^ 3 * (momentBound S X + momentBound T Z) := by
  obtain ⟨a, b, he⟩ := avg_expansion hd hf x
  have hF := avg_lip hd (avg_lip hd hf)
  have eX := step_expansion hX hx hx' hF x (a := a) (b := b) (remainderBound K d).2 ht he
  have eZ := step_expansion hZ hz hz' hF x (a := a) (b := b) (remainderBound K d).2 ht he
  rw [hu, hl] at eZ
  rw [mul_add]
  have compare {u v w q r s : ℝ} (hu : |u - q| ≤ r) (hv : |v - q| ≤ s) (hw : v ≤ w) :
      u ≤ w + (r + s) := by linarith [(abs_le.mp hu).2, (abs_le.mp hv).1]
  exact compare eX eZ (double_avg_le hZ hf t hd x)

private theorem iterate_lip (hX : X ∈ S.H) {f : ℝ → ℝ} {K : NNReal} (hf : LipschitzWith K f)
    (t : ℝ) (n : ℕ) : LipschitzWith K ((step S X t)^[n] f) := by
  induction n with
  | zero => exact hf
  | succ n ih => rw [Function.iterate_succ_apply']; exact step_lip hX ih t

private theorem iterate_comparison (hX : X ∈ S.H) (hx : S.E X = 0) (hx' : S.E (fun ω ↦ -X ω) = 0)
    (hZ : Z ∈ T.H) (hz : T.E Z = 0) (hz' : T.E (fun ω ↦ -Z ω) = 0)
    (hu : T.E (fun ω ↦ Z ω ^ 2) = S.E (fun ω ↦ X ω ^ 2))
    (hl : T.E (fun ω ↦ -Z ω ^ 2) = S.E (fun ω ↦ -X ω ^ 2)) {d t : ℝ} (hd : 0 < d)
    (ht : 0 ≤ t) {K : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith K f) (n : ℕ) (x : ℝ) :
    (step S X t)^[n] f x - (step T Z t)^[n] f x ≤ 4 * (K : ℝ) * d +
      n * (remainderBound K d * t ^ 3 * (momentBound S X + momentBound T Z)) := by
  let e := remainderBound K d * t ^ 3 * (momentBound S X + momentBound T Z)
  have aux (m : ℕ) (y : ℝ) : (step S X t)^[m] f y ≤ 2 * (K : ℝ) * d + m * e +
      avg d (avg d ((step T Z t)^[m] f)) y := by
    induction m generalizing y with
    | zero =>
      simp only [Function.iterate_zero_apply, Nat.cast_zero, zero_mul, add_zero]
      linarith [(abs_le.mp (avg_twice_close hd hf y)).1]
    | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have hZf := iterate_lip hZ hf t m
      have hi := step_le_add hX (iterate_lip hX hf t m) (avg_lip hd (avg_lip hd hZf)) ih t y
      have hc := step_comparison hX hx hx' hZ hz hz' hu hl hd ht hZf y
      change _ ≤ _ + e at hc
      push_cast
      linarith
  have h := (abs_le.mp (avg_twice_close hd (iterate_lip hZ hf t n) x)).2
  linarith [aux n x]

end

/-- **Peng's central limit theorem under a sublinear expectation** (one-dimensional, zero mean).
Let `(X_i)` be real random variables in a sublinear expectation space with `X_{i+1} =ᵈ X_i`,
`X_{i+1}` independent from `(X_0, …, X_i)`, and no mean uncertainty: `E[X_0] = E[-X_0] = 0`. Let
`ξ` be a G-normally distributed random variable on any sublinear expectation space with the same
upper and lower variances, `E'[ξ²] = E[X_0²]` and `-E'[-ξ²] = -E[-X_0²]`. Then for every
Lipschitz `φ`, `E[φ((X_0 + ⋯ + X_{n-1}) / √n)] → E'[φ(ξ)]`. S. Peng, arXiv:1002.4546v1,
Chapter II, Theorem 3.3 with `d = 1` (Remark 3.4: the limit is `N({0} × [σ²_, σ̄²])`). -/
public theorem clt {Ω Ω' : Type*} (S : SublinearExpectationSpace Ω) (X : ℕ → Ω → ℝ)
    (hX : ∀ i, X i ∈ S.H)
    (hid : ∀ i, SublinearExpectationSpace.IdentDistrib S S (X (i + 1)) (X i))
    (hind : ∀ i, S.IndepFrom (X (i + 1)) (fun ω (j : Fin (i + 1)) ↦ X j ω))
    (hmean : S.E (X 0) = 0) (hmean' : S.E (fun ω ↦ -X 0 ω) = 0)
    (S' : SublinearExpectationSpace Ω') (ξ : Ω' → ℝ) (hξ : S'.IsGNormal ξ)
    (hup : S'.E (fun ω ↦ ξ ω ^ 2) = S.E (fun ω ↦ X 0 ω ^ 2))
    (hlow : S'.E (fun ω ↦ -ξ ω ^ 2) = S.E (fun ω ↦ -X 0 ω ^ 2))
    {φ : ℝ → ℝ} {K : NNReal} (hφ : LipschitzWith K φ) :
    Tendsto (fun n : ℕ ↦ S.E (fun ω ↦ φ ((∑ i ∈ range n, X i ω) / Real.sqrt n))) atTop
      (𝓝 (S'.E (fun ω ↦ φ (ξ ω)))) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let d := ε / (8 * ((K : ℝ) + 1))
  have hd : 0 < d := by dsimp [d]; positivity
  have hdε : 4 * (K : ℝ) * d < ε / 2 := by
    have h₀ : 8 * ((K : ℝ) + 1) * d = ε := by dsimp [d]; field_simp
    linarith
  let C := (remainderBound K d : ℝ) * (momentBound S (X 0) + momentBound S' ξ)
  have hlim : Tendsto (fun n : ℕ ↦ C / Real.sqrt n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (ε / 2) (half_pos hε)
  refine ⟨max N 1, fun n hn ↦ ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let t := (Real.sqrt n)⁻¹
  have hs := Real.sqrt_pos.mpr hn'
  have ht : 0 ≤ t := inv_nonneg.mpr hs.le
  -- Express both laws after n steps of size 1 / √n.
  have hsum := iid_steps S X hX hid hind t n hφ
  have heq (ω) : (∑ i ∈ range n, X i ω) / Real.sqrt n = t * ∑ i ∈ range n, X i ω := by
    simp [t, div_eq_inv_mul]
  simp only [heq]
  rw [hsum, Real.dist_eq]
  have hz := SublinearExpectationSpace.IsGNormal.expectation_eq_zero _ hξ
  have hz' := SublinearExpectationSpace.IsGNormal.expectation_neg_eq_zero _ hξ
  have hZ : (step S' ξ t)^[n] φ 0 = S'.E (fun ω ↦ φ (ξ ω)) := by
    rw [normal_steps hξ ht n hφ]
    simp [step, t, hs.ne']
  rw [← hZ]
  -- Interchanging the laws gives the reverse inequality with the same error.
  have hi := iterate_comparison (hX 0) hmean hmean' hξ.1 hz hz' hup hlow hd ht hφ n 0
  have lo := iterate_comparison hξ.1 hz hz' (hX 0) hmean hmean' hup.symm hlow.symm hd ht hφ n 0
  rw [add_comm (momentBound S' ξ) (momentBound S (X 0))] at lo
  have he : (n : ℝ) * (remainderBound K d * t ^ 3 * (momentBound S (X 0) + momentBound S' ξ)) =
      C / Real.sqrt n := by
    dsimp [t, C]
    field_simp
    rw [Real.sq_sqrt hn'.le]
    ring
  rw [he] at hi lo
  have hsmall := hN n (by omega)
  simp only [Real.dist_eq, sub_zero] at hsmall
  exact abs_lt.mpr ⟨by linarith [le_abs_self (C / Real.sqrt n)],
    by linarith [le_abs_self (C / Real.sqrt n)]⟩

end MathlibExt.Probability.SublinearExpectation.PengLimitTheoremsWanted
