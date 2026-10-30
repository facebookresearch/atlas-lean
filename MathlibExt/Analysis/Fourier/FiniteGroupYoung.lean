/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.MeanInequalities

@[expose] public section

namespace MathlibExt.Analysis.Fourier

/-!
# Young's convolution inequality on a finite group

For complex-valued functions on a finite abelian additive group `G`, the
convolution
`(f * g) x = ∑ y, f y * g (x - y)`
satisfies Young's inequality: if `1 < p`, `1 < q`, `1 < r` and
`1 / p + 1 / q = 1 + 1 / r`, then
`‖f * g‖_r ≤ ‖f‖_p * ‖g‖_q`, where the norms are the finite-sum
`ℓ^p` norms. This is the finite-group form of Young's inequality
(W. H. Young, "On the multiplication of successions of Fourier constants",
Proc. Roy. Soc. London Ser. A 87 (1912), 331-339). Mathlib has only the
pointwise, conjugate-exponent form `enorm_convolution_le` and the
`L¹` case used inside `WienerTauberian`; the full three-exponent norm
inequality is not in Mathlib.

Proof: a three-function Hölder inequality (iterating Mathlib's
two-function Hölder) bounds each pointwise value, and summing over `x`
and using translation invariance of the finite sums collects the
remaining factors.
-/

/-- Convolution of complex-valued functions on a finite additive group. -/
noncomputable def finGroupConv {G : Type*} [AddCommGroup G] [Fintype G] (f g : G → ℂ) :
    G → ℂ :=
  fun x => ∑ y, f y * g (x - y)

theorem finGroupConv_apply {G : Type*} [AddCommGroup G] [Fintype G] (f g : G → ℂ) (x : G) :
    finGroupConv f g x = ∑ y, f y * g (x - y) :=
  rfl

theorem finGroupConv_zero_left {G : Type*} [AddCommGroup G] [Fintype G] (g : G → ℂ) :
    finGroupConv 0 g = 0 := by
  funext x
  simp [finGroupConv_apply]

theorem finGroupConv_zero_right {G : Type*} [AddCommGroup G] [Fintype G] (f : G → ℂ) :
    finGroupConv f 0 = 0 := by
  funext x
  simp [finGroupConv_apply]

/-- Convolution on a finite group of complex-valued functions is commutative. -/
theorem finGroupConv_comm {G : Type*} [AddCommGroup G] [Fintype G] (f g : G → ℂ) :
    finGroupConv f g = finGroupConv g f := by
  funext x
  rw [finGroupConv_apply, finGroupConv_apply]
  apply Finset.sum_bij (fun y _ => x - y)
  · intro y _
    exact Finset.mem_univ _
  · intro y1 _ y2 _ h
    rw [← sub_sub_cancel x y1, h, sub_sub_cancel]
  · intro z _
    exact ⟨x - z, Finset.mem_univ _, by rw [sub_sub_cancel]⟩
  · intro y _
    rw [sub_sub_cancel]
    exact mul_comm _ _

/-- Convolution on a finite group of complex-valued functions is associative. -/
theorem finGroupConv_assoc {G : Type*} [AddCommGroup G] [Fintype G] (f g h : G → ℂ) :
    finGroupConv (finGroupConv f g) h = finGroupConv f (finGroupConv g h) := by
  funext x
  simp only [finGroupConv_apply, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Equiv.sum_comp (Equiv.addRight y)
    (fun z => f y * g (z - y) * h (x - z))]
  apply Finset.sum_congr rfl
  intro z _
  change f y * g (z + y - y) * h (x - (z + y)) = f y * (g z * h (x - y - z))
  rw [add_sub_cancel_right, ← sub_add_eq_sub_sub, add_comm z y, mul_assoc]

/-- The delta function at `0` is the identity for convolution. -/
theorem finGroupConv_delta_left {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (g : G → ℂ) :
    finGroupConv (fun y => if y = 0 then (1 : ℂ) else 0) g = g := by
  funext x
  rw [finGroupConv_apply]
  rw [Finset.sum_eq_single (0 : G)]
  · simp
  · intro y _ hy
    simp [hy]
  · simp

/-- Hölder's inequality for three nonnegative functions on a finite set. -/
private theorem holder_three_finset {ι : Type*} (s : Finset ι)
    {F G H : ι → ℝ} {a b c : ℝ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (habc : a⁻¹ + b⁻¹ + c⁻¹ = 1)
    (hF : ∀ i ∈ s, 0 ≤ F i) (hG : ∀ i ∈ s, 0 ≤ G i) (hH : ∀ i ∈ s, 0 ≤ H i) :
    ∑ i ∈ s, F i * G i * H i ≤
      (∑ i ∈ s, F i ^ a) ^ (1 / a) * (∑ i ∈ s, G i ^ b) ^ (1 / b) *
        (∑ i ∈ s, H i ^ c) ^ (1 / c) := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hb0 : (0 : ℝ) < b := by linarith
  have hc0 : (0 : ℝ) < c := by linarith
  -- The conjugate exponent of `a`.
  set a' : ℝ := a / (a - 1) with ha'def
  have ha1 : (0 : ℝ) < a - 1 := sub_pos.mpr ha
  have ha'pos : 0 < a' := div_pos ha0 ha1
  have ha'ne : a' ≠ 0 := ne_of_gt ha'pos
  have ha'inv : (a')⁻¹ = 1 - a⁻¹ := by
    rw [ha'def, inv_div]
    field_simp
  have hconj : a.HolderConjugate a' := by
    rw [Real.holderConjugate_iff]
    exact ⟨ha, by rw [ha'inv]; ring⟩
  have htriple : b.HolderTriple c a' := by
    refine ⟨?_, hb0, hc0⟩
    rw [ha'inv]
    linarith
  have step1 : ∑ i ∈ s, F i * G i * H i ≤
      (∑ i ∈ s, F i ^ a) ^ (1 / a) * (∑ i ∈ s, (G i * H i) ^ a') ^ (1 / a') := by
    have h := Real.inner_le_Lp_mul_Lq_of_nonneg s hconj hF
      (fun i hi => mul_nonneg (hG i hi) (hH i hi))
    have hsum : ∑ i ∈ s, F i * G i * H i = ∑ i ∈ s, F i * (G i * H i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_assoc]
    rw [hsum]
    exact h
  have step2 : (∑ i ∈ s, (G i * H i) ^ a') ^ (1 / a') ≤
      (∑ i ∈ s, G i ^ b) ^ (1 / b) * (∑ i ∈ s, H i ^ c) ^ (1 / c) := by
    have h := Real.Lr_rpow_le_Lp_mul_Lq_of_nonneg s htriple hG hH
    have hX0 : 0 ≤ ∑ i ∈ s, (G i * H i) ^ a' :=
      Finset.sum_nonneg fun i hi =>
        Real.rpow_nonneg (mul_nonneg (hG i hi) (hH i hi)) a'
    have hle := Real.rpow_le_rpow hX0 h (by positivity : (0 : ℝ) ≤ 1 / a')
    have e1 : ((∑ i ∈ s, G i ^ b) ^ (a' / b)) ^ (1 / a') =
        (∑ i ∈ s, G i ^ b) ^ (1 / b) := by
      rw [← Real.rpow_mul (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hG i hi) b)]
      congr 1
      field_simp
    have e2 : ((∑ i ∈ s, H i ^ c) ^ (a' / c)) ^ (1 / a') =
        (∑ i ∈ s, H i ^ c) ^ (1 / c) := by
      rw [← Real.rpow_mul (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hH i hi) c)]
      congr 1
      field_simp
    rw [Real.mul_rpow
      (Real.rpow_nonneg (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hG i hi) b) _)
      (Real.rpow_nonneg (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hH i hi) c) _)]
      at hle
    rw [e1, e2] at hle
    exact hle
  refine le_trans step1 ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left step2
    (Real.rpow_nonneg (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hF i hi) a) _)

/-- **Young's convolution inequality** on a finite abelian additive group: for
`1 < p`, `1 < q`, `1 < r` with `1 / p + 1 / q = 1 + 1 / r`,
`‖f * g‖_r ≤ ‖f‖_p * ‖g‖_q` in the finite-sum `ℓ^p` norms. -/
theorem young_convolution_finite_group {G : Type*} [AddCommGroup G] [Fintype G]
    {f g : G → ℂ} {p q r : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hexp : p⁻¹ + q⁻¹ = 1 + r⁻¹) :
    (∑ x, ‖finGroupConv f g x‖ ^ r) ^ (1 / r)
      ≤ (∑ x, ‖f x‖ ^ p) ^ (1 / p) * (∑ x, ‖g x‖ ^ q) ^ (1 / q) := by
  classical
  set A : G → ℝ := fun x => ‖f x‖ with hAdef
  set B : G → ℝ := fun x => ‖g x‖ with hBdef
  have hp0 : (0 : ℝ) < p := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  have hr0 : (0 : ℝ) < r := by linarith
  have hAnonneg : ∀ x : G, 0 ≤ A x := fun x => norm_nonneg _
  have hBnonneg : ∀ x : G, 0 ≤ B x := fun x => norm_nonneg _
  -- Since `1 / q < 1`, we have `1 / r < 1 / p`, hence `p < r`; similarly `q < r`.
  have h1q : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  have h1p : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  have hrp : p < r := by
    have h : r⁻¹ < p⁻¹ := by linarith
    exact (inv_lt_inv₀ hr0 hp0).mp h
  have hrq : q < r := by
    have h : r⁻¹ < q⁻¹ := by linarith
    exact (inv_lt_inv₀ hr0 hq0).mp h
  have hrp0 : (0 : ℝ) < r - p := sub_pos.mpr hrp
  have hrq0 : (0 : ℝ) < r - q := sub_pos.mpr hrq
  -- The remaining Hölder exponents `u = p * r / (r - p)` and `v = q * r / (r - q)`.
  set u : ℝ := p * r / (r - p) with hudef
  set v : ℝ := q * r / (r - q) with hvdef
  have hu0 : (0 : ℝ) < u := div_pos (mul_pos hp0 hr0) hrp0
  have hv0 : (0 : ℝ) < v := div_pos (mul_pos hq0 hr0) hrq0
  have huinv : u⁻¹ = p⁻¹ - r⁻¹ := by
    rw [hudef, inv_div]
    field_simp
  have hvinv : v⁻¹ = q⁻¹ - r⁻¹ := by
    rw [hvdef, inv_div]
    field_simp
  have hu1 : 1 < u := by
    have hlt : u⁻¹ < 1 := by
      rw [huinv]
      have hpos : (0 : ℝ) < r⁻¹ := inv_pos.mpr hr0
      have hpr : r⁻¹ < p⁻¹ := by linarith
      linarith
    exact (inv_lt_inv₀ hu0 zero_lt_one).mp (by simpa using hlt)
  have hv1 : 1 < v := by
    have hlt : v⁻¹ < 1 := by
      rw [hvinv]
      have hpos : (0 : ℝ) < r⁻¹ := inv_pos.mpr hr0
      have hqr : r⁻¹ < q⁻¹ := by linarith
      linarith
    exact (inv_lt_inv₀ hv0 zero_lt_one).mp (by simpa using hlt)
  have habc : r⁻¹ + u⁻¹ + v⁻¹ = 1 := by
    rw [huinv, hvinv]
    linarith
  -- The two `ℓ^p` / `ℓ^q` power sums.
  set Fp : ℝ := ∑ y, A y ^ p with hFpdef
  set Gq : ℝ := ∑ y, B y ^ q with hGqdef
  have hFp0 : 0 ≤ Fp :=
    Finset.sum_nonneg fun y _ => Real.rpow_nonneg (hAnonneg y) p
  have hGq0 : 0 ≤ Gq :=
    Finset.sum_nonneg fun y _ => Real.rpow_nonneg (hBnonneg y) q
  -- Translation invariance of the finite sums.
  have hshiftB : ∀ (x : G), (∑ y, B (x - y) ^ q) = Gq := by
    intro x
    have h := Equiv.sum_comp (Equiv.subLeft x) (fun y => B y ^ q)
    rw [hGqdef]
    exact h
  have hshiftB' : ∀ (y : G), (∑ x, B (x - y) ^ q) = Gq := by
    intro y
    rw [hGqdef]
    apply Finset.sum_bij (fun x _ => x - y)
    · intro x _
      exact Finset.mem_univ _
    · intro x1 _ x2 _ h
      exact sub_left_injective h
    · intro z _
      exact ⟨z + y, Finset.mem_univ _, by rw [add_sub_cancel_right]⟩
    · intro x _
      rfl
  -- Pointwise bound: raise the per-point Hölder estimate to the `r`-th power.
  have hper : ∀ x : G, ‖finGroupConv f g x‖ ^ r ≤
      (∑ y, A y ^ p * B (x - y) ^ q) * Fp ^ (r / p - 1) * Gq ^ (r / q - 1) := by
    intro x
    have hpt : ‖finGroupConv f g x‖ ≤ ∑ y, A y * B (x - y) := by
      rw [finGroupConv_apply]
      calc ‖∑ y, f y * g (x - y)‖ ≤ ∑ y, ‖f y * g (x - y)‖ := norm_sum_le _ _
        _ = ∑ y, A y * B (x - y) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [norm_mul]
    -- The three factors in the pointwise Hölder estimate.
    have h3 := holder_three_finset (Finset.univ : Finset G)
      (F := fun y => (A y ^ p * B (x - y) ^ q) ^ (1 / r))
      (G := fun y => A y ^ (1 - p / r))
      (H := fun y => B (x - y) ^ (1 - q / r))
      hr hu1 hv1 habc
      (fun y _ => Real.rpow_nonneg
        (mul_nonneg (Real.rpow_nonneg (hAnonneg y) p)
          (Real.rpow_nonneg (hBnonneg _) q)) _)
      (fun y _ => Real.rpow_nonneg (hAnonneg y) _)
      (fun y _ => Real.rpow_nonneg (hBnonneg _) _)
    -- The product of the three factors is `A y * B (x - y)`.
    have hprod : ∀ y : G,
        ((A y ^ p * B (x - y) ^ q) ^ (1 / r)) * (A y ^ (1 - p / r)) *
          (B (x - y) ^ (1 - q / r)) = A y * B (x - y) := by
      intro y
      have hsplit : ((A y ^ p * B (x - y) ^ q) ^ (1 / r)) =
          A y ^ (p / r) * B (x - y) ^ (q / r) := by
        rw [Real.mul_rpow (Real.rpow_nonneg (hAnonneg y) p)
          (Real.rpow_nonneg (hBnonneg _) q),
          ← Real.rpow_mul (hAnonneg y), ← Real.rpow_mul (hBnonneg _),
          show p * (1 / r) = p / r by ring, show q * (1 / r) = q / r by ring]
      rw [hsplit]
      have eA : A y ^ (p / r) * A y ^ (1 - p / r) = A y := by
        rw [← Real.rpow_add_of_nonneg (hAnonneg y) (div_nonneg hp0.le hr0.le)
          (by linarith [div_le_one_of_le₀ (le_of_lt hrp) hr0.le] :
            (0:ℝ) ≤ 1 - p / r)]
        rw [show p / r + (1 - p / r) = (1 : ℝ) by ring, Real.rpow_one]
      have eB : B (x - y) ^ (q / r) * B (x - y) ^ (1 - q / r) = B (x - y) := by
        rw [← Real.rpow_add_of_nonneg (hBnonneg _) (div_nonneg hq0.le hr0.le)
          (by linarith [div_le_one_of_le₀ (le_of_lt hrq) hr0.le] :
            (0:ℝ) ≤ 1 - q / r)]
        rw [show q / r + (1 - q / r) = (1 : ℝ) by ring, Real.rpow_one]
      calc (A y ^ (p / r) * B (x - y) ^ (q / r)) * A y ^ (1 - p / r) *
            B (x - y) ^ (1 - q / r)
          = (A y ^ (p / r) * A y ^ (1 - p / r)) *
            (B (x - y) ^ (q / r) * B (x - y) ^ (1 - q / r)) := by ring
        _ = A y * B (x - y) := by rw [eA, eB]
    -- Identify the three Hölder norms.
    have e1 : (∑ y, ((A y ^ p * B (x - y) ^ q) ^ (1 / r)) ^ r) =
        ∑ y, A y ^ p * B (x - y) ^ q := by
      apply Finset.sum_congr rfl
      intro y _
      rw [← Real.rpow_mul (mul_nonneg (Real.rpow_nonneg (hAnonneg y) p)
        (Real.rpow_nonneg (hBnonneg _) q))]
      rw [show (1 / r) * r = (1 : ℝ) by field_simp, Real.rpow_one]
    have e2 : (∑ y, (A y ^ (1 - p / r)) ^ u) = Fp := by
      rw [hFpdef]
      apply Finset.sum_congr rfl
      intro y _
      rw [← Real.rpow_mul (hAnonneg y)]
      congr 1
      rw [hudef]
      field_simp
    have e3 : (∑ y, (B (x - y) ^ (1 - q / r)) ^ v) = Gq := by
      rw [← hshiftB x]
      apply Finset.sum_congr rfl
      intro y _
      rw [← Real.rpow_mul (hBnonneg _)]
      congr 1
      rw [hvdef]
      field_simp
    have hpt2 : ∑ y : G, A y * B (x - y) ≤
        (∑ y, A y ^ p * B (x - y) ^ q) ^ (1 / r) * Fp ^ (1 / u) * Gq ^ (1 / v) := by
      rw [show ∑ y : G, A y * B (x - y) =
          ∑ y : G, ((A y ^ p * B (x - y) ^ q) ^ (1 / r)) * (A y ^ (1 - p / r)) *
            (B (x - y) ^ (1 - q / r)) from
          Finset.sum_congr rfl fun y _ => (hprod y).symm]
      rw [e1, e2, e3] at h3
      exact h3
    -- Raise to the `r`-th power.
    have hrle : (0 : ℝ) ≤ r := hr0.le
    have hbase : (0 : ℝ) ≤ (∑ y, A y ^ p * B (x - y) ^ q) ^ (1 / r) * Fp ^ (1 / u) *
        Gq ^ (1 / v) :=
      mul_nonneg (mul_nonneg
        (Real.rpow_nonneg (Finset.sum_nonneg fun y _ =>
          mul_nonneg (Real.rpow_nonneg (hAnonneg y) p)
            (Real.rpow_nonneg (hBnonneg _) q)) _)
        (Real.rpow_nonneg hFp0 _))
        (Real.rpow_nonneg hGq0 _)
    have hpow := Real.rpow_le_rpow (norm_nonneg _) (le_trans hpt hpt2) hrle
    rw [Real.mul_rpow (mul_nonneg
        (Real.rpow_nonneg (Finset.sum_nonneg fun y _ =>
          mul_nonneg (Real.rpow_nonneg (hAnonneg y) p)
            (Real.rpow_nonneg (hBnonneg _) q)) _)
        (Real.rpow_nonneg hFp0 _))
      (Real.rpow_nonneg hGq0 _),
      Real.mul_rpow
        (Real.rpow_nonneg (Finset.sum_nonneg fun y _ =>
          mul_nonneg (Real.rpow_nonneg (hAnonneg y) p)
            (Real.rpow_nonneg (hBnonneg _) q)) _)
        (Real.rpow_nonneg hFp0 _),
      ← Real.rpow_mul (Finset.sum_nonneg fun y _ =>
        mul_nonneg (Real.rpow_nonneg (hAnonneg y) p)
          (Real.rpow_nonneg (hBnonneg _) q)),
      ← Real.rpow_mul hFp0,
      ← Real.rpow_mul hGq0] at hpow
    rw [show (1 / r) * r = (1 : ℝ) by field_simp, Real.rpow_one] at hpow
    rw [show (1 / u) * r = r / p - 1 from by
      rw [one_div, huinv]; field_simp] at hpow
    rw [show (1 / v) * r = r / q - 1 from by
      rw [one_div, hvinv]; field_simp] at hpow
    exact hpow
  -- Sum over `x` and collect the double sum.
  have hsum : (∑ x, ‖finGroupConv f g x‖ ^ r) ≤
      Fp ^ (r / p) * Gq ^ (r / q) := by
    have hper' : (∑ x, ‖finGroupConv f g x‖ ^ r) ≤
        (∑ x, (∑ y, A y ^ p * B (x - y) ^ q) * Fp ^ (r / p - 1) * Gq ^ (r / q - 1)) :=
      Finset.sum_le_sum fun x _ => hper x
    have hfact : (∑ x, (∑ y, A y ^ p * B (x - y) ^ q) * Fp ^ (r / p - 1) *
        Gq ^ (r / q - 1)) =
        (∑ x, ∑ y, A y ^ p * B (x - y) ^ q) * Fp ^ (r / p - 1) * Gq ^ (r / q - 1) := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
    have hdouble : (∑ x, ∑ y, A y ^ p * B (x - y) ^ q) = Fp * Gq := by
      rw [Finset.sum_comm]
      have hswap : (∑ y, ∑ x, A y ^ p * B (x - y) ^ q) =
          ∑ y, A y ^ p * (∑ x, B (x - y) ^ q) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [Finset.mul_sum]
      rw [hswap]
      have hinner : ∀ y : G, A y ^ p * (∑ x, B (x - y) ^ q) = A y ^ p * Gq := by
        intro y
        rw [hshiftB' y]
      rw [Finset.sum_congr rfl fun y _ => hinner y]
      rw [← Finset.sum_mul, ← hFpdef]
    rw [hfact, hdouble] at hper'
    -- `(Fp * Gq) * Fp ^ (r / p - 1) * Gq ^ (r / q - 1) = Fp ^ (r / p) * Gq ^ (r / q)`.
    have hcombine : Fp * Gq * Fp ^ (r / p - 1) * Gq ^ (r / q - 1) =
        Fp ^ (r / p) * Gq ^ (r / q) := by
      have eFp : Fp ^ (1 : ℝ) * Fp ^ (r / p - 1) = Fp ^ (r / p) := by
        rw [← Real.rpow_add_of_nonneg hFp0 zero_le_one
          (by rw [sub_nonneg, one_le_div hp0]; exact hrp.le :
            (0:ℝ) ≤ r / p - 1)]
        congr 1
        ring
      have eGq : Gq ^ (1 : ℝ) * Gq ^ (r / q - 1) = Gq ^ (r / q) := by
        rw [← Real.rpow_add_of_nonneg hGq0 zero_le_one
          (by rw [sub_nonneg, one_le_div hq0]; exact hrq.le :
            (0:ℝ) ≤ r / q - 1)]
        congr 1
        ring
      calc Fp * Gq * Fp ^ (r / p - 1) * Gq ^ (r / q - 1)
          = (Fp ^ (1 : ℝ) * Fp ^ (r / p - 1)) * (Gq ^ (1 : ℝ) * Gq ^ (r / q - 1)) := by
            rw [Real.rpow_one, Real.rpow_one]
            ring
        _ = Fp ^ (r / p) * Gq ^ (r / q) := by rw [eFp, eGq]
    rw [hcombine] at hper'
    exact hper'
  -- Take the `1 / r`-th power of both sides.
  have hfin := Real.rpow_le_rpow
    (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (norm_nonneg _) r) hsum
    (by positivity : (0 : ℝ) ≤ 1 / r)
  rw [Real.mul_rpow (Real.rpow_nonneg hFp0 _) (Real.rpow_nonneg hGq0 _),
    ← Real.rpow_mul hFp0, ← Real.rpow_mul hGq0] at hfin
  rw [show (r / p) * (1 / r) = 1 / p by field_simp,
    show (r / q) * (1 / r) = 1 / q by field_simp] at hfin
  exact hfin

end MathlibExt.Analysis.Fourier
