/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import MathlibExt.Analysis.Fourier.BooleanCubeInfluence

@[expose] public section

/-!
# Tensorization of two-point hypercontractivity on the uniform cube

On `ι → Bool` with the uniform measure, define `L^q` norms and the noise operator `T_ρ` (each
coordinate kept with probability `(1 + ρ) / 2`, flipped otherwise). If a vector-valued two-point
inequality holds for `ρ`, then by induction on the dimension `‖T_ρ f‖₂ ≤ ‖f‖_(1 + ρ²)` on every
`Fin n → Bool`.

## Main definitions

* `StatMech.Probability.bnt_uexp`: the uniform expectation on `ι → Bool`.
* `StatMech.Probability.bnt_qnormPow`, `StatMech.Probability.bnt_qnorm`: `E|f|^q` and
  `(E|f|^q)^(1/q)`.
* `StatMech.Probability.bnt_noiseKernel`, `StatMech.Probability.bnt_noiseOp`: the noise kernel and
  operator `T_ρ`; `bnt_noiseOp` is `BooleanCube.boolNoiseOp` on `Fin n → Bool`
  (`StatMech.Probability.bnt_noiseOp_eq_boolNoiseOp`).
* `StatMech.Probability.bnt_VectorTwoPoint ρ`: the two-point inequality for functions on a cube,
  `(‖((1+ρ)/2) u + ((1-ρ)/2) v‖₂² + ‖((1-ρ)/2) u + ((1+ρ)/2) v‖₂²) / 2
  ≤ ((‖u‖_q^q + ‖v‖_q^q) / 2)^(2/q)` with `q = 1 + ρ²`.
* `StatMech.Probability.bnt_TensorStep ρ`: the induction step from dimension `n` to `n + 1`.

## Main results

* `StatMech.Probability.bnt_tensorStep_of_vec`: the vector two-point inequality gives the
  induction step.
* `StatMech.Probability.bnt_hypercontractivity`: `‖T_ρ f‖₂ ≤ ‖f‖_(1 + ρ²)` for every `n`,
  assuming `bnt_VectorTwoPoint ρ` (proved for `0 ≤ ρ ≤ 1` in
  `MathlibExt.Probability.Hypercontractivity.VectorTwoPoint`).

## References

* A. Bonami, *Étude des coefficients de Fourier des fonctions de `L^p(G)`*, Ann. Inst. Fourier 20
  (1970).
* W. Beckner, *Inequalities in Fourier analysis*, Ann. of Math. 102 (1975).
* R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press (2014), Chapter 9.
-/

open scoped BigOperators
open Finset

namespace StatMech
namespace Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The expectation of `f` under the uniform measure on `ι → Bool`. This is `𝔼 ω, f ω`
(`Finset.expect`). -/
noncomputable def bnt_uexp (f : (ι → Bool) → ℝ) : ℝ :=
  (∑ ω : ι → Bool, f ω) / (2 ^ (Fintype.card ι))

/-- `E|f|^q` under the uniform measure. -/
noncomputable def bnt_qnormPow (q : ℝ) (f : (ι → Bool) → ℝ) : ℝ :=
  bnt_uexp (fun ω => |f ω| ^ q)

/-- The `L^q` norm `(E|f|^q)^(1/q)` under the uniform measure. -/
noncomputable def bnt_qnorm (q : ℝ) (f : (ι → Bool) → ℝ) : ℝ :=
  (bnt_qnormPow q f) ^ (1 / q)

theorem bnt_qnormPow_nonneg (q : ℝ) (f : (ι → Bool) → ℝ) : 0 ≤ bnt_qnormPow q f := by
  unfold bnt_qnormPow bnt_uexp
  apply div_nonneg
  · exact Finset.sum_nonneg (fun ω _ => Real.rpow_nonneg (abs_nonneg _) q)
  · positivity

theorem bnt_qnorm_nonneg (q : ℝ) (f : (ι → Bool) → ℝ) : 0 ≤ bnt_qnorm q f :=
  Real.rpow_nonneg (bnt_qnormPow_nonneg q f) _

/-- The noise kernel: `∏ i, (1 + ρ)/2` or `(1 - ρ)/2` according as `x i = y i` or not. -/
noncomputable def bnt_noiseKernel (ρ : ℝ) (x y : ι → Bool) : ℝ :=
  ∏ i : ι, (if x i = y i then (1 + ρ) / 2 else (1 - ρ) / 2)

/-- The noise operator `T_ρ f x = ∑ y, bnt_noiseKernel ρ x y * f y`: for `ρ ∈ [-1, 1]`, the
expectation of `f y` where each coordinate of `y` equals that of `x` with probability
`(1 + ρ)/2`. -/
noncomputable def bnt_noiseOp (ρ : ℝ) (f : (ι → Bool) → ℝ) : (ι → Bool) → ℝ :=
  fun x => ∑ y : ι → Bool, bnt_noiseKernel ρ x y * f y

/-- `bnt_uexp` is the uniform average `Finset.expect`. -/
theorem bnt_uexp_eq_expect (f : (ι → Bool) → ℝ) : bnt_uexp f = 𝔼 ω, f ω := by
  rw [Finset.expect_eq_sum_div_card, Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
  simp [bnt_uexp]

/-- On `Fin n → Bool`, `bnt_noiseOp` is the noise operator `BooleanCube.boolNoiseOp`. -/
theorem bnt_noiseOp_eq_boolNoiseOp {n : ℕ} (ρ : ℝ) (f : (Fin n → Bool) → ℝ) :
    bnt_noiseOp ρ f = BooleanCube.boolNoiseOp ρ f := by
  funext x
  unfold bnt_noiseOp bnt_noiseKernel BooleanCube.boolNoiseOp
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  cases x i <;> cases y i <;> simp [BooleanCube.cubeVal] <;> ring

theorem bnt_noiseOp_one (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    bnt_noiseOp 1 f x = f x := by
  unfold bnt_noiseOp bnt_noiseKernel
  have hker : ∀ y : ι → Bool,
      (∏ i : ι, (if x i = y i then (1 + (1 : ℝ)) / 2 else (1 - 1) / 2))
        = (if x = y then 1 else 0) := by
    intro y
    by_cases hxy : x = y
    · subst hxy; simp
    · rw [ite_eq_right hxy, Finset.prod_eq_zero_iff]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
      exact ⟨i, mem_univ i, by simp [hi]⟩
  simp_rw [hker, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq univ x (fun y => f y)]
  simp

theorem bnt_sum_cons_split {n : ℕ} {M : Type*} [AddCommMonoid M]
    (F : (Fin (n + 1) → Bool) → M) :
    (∑ y : Fin (n + 1) → Bool, F y)
      = ∑ c : Bool, ∑ ω' : Fin n → Bool, F (Fin.cons c ω') := by
  rw [← Fintype.sum_prod_type (fun p : Bool × (Fin n → Bool) => F (Fin.cons p.1 p.2))]
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => Bool))
    (fun p => F (Fin.cons p.1 p.2)) F (fun _ => rfl)).symm

theorem bnt_uexp_cons_split {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    bnt_uexp f
      = (∑ c : Bool, bnt_uexp (fun ω' : Fin n → Bool => f (Fin.cons c ω'))) / 2 := by
  unfold bnt_uexp
  rw [bnt_sum_cons_split f, Fintype.card_fin, Fintype.card_fin, pow_succ,
    Finset.sum_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  rw [div_div]

theorem bnt_noiseOp_cons {n : ℕ} (ρ : ℝ) (f : (Fin (n + 1) → Bool) → ℝ)
    (a : Bool) (ω : Fin n → Bool) :
    bnt_noiseOp ρ f (Fin.cons a ω)
      = ∑ c : Bool, (if a = c then (1 + ρ) / 2 else (1 - ρ) / 2)
          * bnt_noiseOp ρ (fun ω' : Fin n → Bool => f (Fin.cons c ω')) ω := by
  unfold bnt_noiseOp bnt_noiseKernel
  set xa : Fin (n + 1) → Bool := Fin.cons a ω with hxa
  refine (bnt_sum_cons_split (fun y : Fin (n + 1) → Bool => (∏ i : Fin (n + 1),
    (if xa i = y i then (1 + ρ) / 2 else (1 - ρ) / 2)) * f y)).trans ?_
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω' _
  rw [Fin.prod_univ_succ, hxa]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

theorem bnt_qnormPow_cons_split {n : ℕ} (q : ℝ) (f : (Fin (n + 1) → Bool) → ℝ) :
    bnt_qnormPow q f
      = (∑ c : Bool, bnt_qnormPow q (fun ω' : Fin n → Bool => f (Fin.cons c ω'))) / 2 := by
  unfold bnt_qnormPow
  rw [bnt_uexp_cons_split (fun ω => |f ω| ^ q)]

theorem bnt_noiseOp_cons_false {n : ℕ} (ρ : ℝ) (f : (Fin (n + 1) → Bool) → ℝ)
    (ω : Fin n → Bool) :
    bnt_noiseOp ρ f (Fin.cons false ω)
      = (1 + ρ) / 2 * bnt_noiseOp ρ (fun ω' => f (Fin.cons false ω')) ω
        + (1 - ρ) / 2 * bnt_noiseOp ρ (fun ω' => f (Fin.cons true ω')) ω := by
  rw [bnt_noiseOp_cons ρ f false ω, Fintype.sum_bool]
  simp only [Bool.false_eq_true, ite_true, ite_false]; ring

theorem bnt_noiseOp_cons_true {n : ℕ} (ρ : ℝ) (f : (Fin (n + 1) → Bool) → ℝ)
    (ω : Fin n → Bool) :
    bnt_noiseOp ρ f (Fin.cons true ω)
      = (1 - ρ) / 2 * bnt_noiseOp ρ (fun ω' => f (Fin.cons false ω')) ω
        + (1 + ρ) / 2 * bnt_noiseOp ρ (fun ω' => f (Fin.cons true ω')) ω := by
  rw [bnt_noiseOp_cons ρ f true ω, Fintype.sum_bool]
  simp only [Bool.true_eq_false, ite_true, ite_false]; ring

theorem bnt_qnorm_rpow_self {n : ℕ} {q : ℝ} (hq : q ≠ 0) (g : (Fin n → Bool) → ℝ) :
    bnt_qnorm q g ^ q = bnt_qnormPow q g := by
  unfold bnt_qnorm
  rw [← Real.rpow_mul (bnt_qnormPow_nonneg q g), one_div, inv_mul_cancel₀ hq, Real.rpow_one]

theorem bnt_qnorm_add_le {n : ℕ} {p : ℝ} (hp : 1 ≤ p) (u v : (Fin n → Bool) → ℝ) :
    bnt_qnorm p (fun ω => u ω + v ω) ≤ bnt_qnorm p u + bnt_qnorm p v := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  unfold bnt_qnorm bnt_qnormPow bnt_uexp
  set N := Fintype.card (Fin n)
  have hc : (0 : ℝ) < 2 ^ N := by positivity
  rw [Real.div_rpow (Finset.sum_nonneg (fun ω _ => Real.rpow_nonneg (abs_nonneg _) p)) hc.le,
      Real.div_rpow (Finset.sum_nonneg (fun ω _ => Real.rpow_nonneg (abs_nonneg _) p)) hc.le,
      Real.div_rpow (Finset.sum_nonneg (fun ω _ => Real.rpow_nonneg (abs_nonneg _) p)) hc.le]
  rw [← add_div, div_le_div_iff_of_pos_right (by positivity)]
  calc (∑ ω : Fin n → Bool, |u ω + v ω| ^ p) ^ (1 / p)
      ≤ (∑ ω : Fin n → Bool, (|u ω| + |v ω|) ^ p) ^ (1 / p) := by
        apply Real.rpow_le_rpow (Finset.sum_nonneg (fun ω _ => Real.rpow_nonneg (abs_nonneg _) p))
        · apply Finset.sum_le_sum; intro ω _
          exact Real.rpow_le_rpow (abs_nonneg _) (abs_add_le _ _) (le_of_lt hp0)
        · positivity
    _ ≤ (∑ ω : Fin n → Bool, |u ω| ^ p) ^ (1 / p) + (∑ ω : Fin n → Bool, |v ω| ^ p) ^ (1 / p) :=
        Real.Lp_add_le_of_nonneg (s := Finset.univ) (f := fun ω => |u ω|) (g := fun ω => |v ω|) hp
          (fun ω _ => abs_nonneg _) (fun ω _ => abs_nonneg _)

theorem bnt_qnorm_const_mul {n : ℕ} {p : ℝ} (hp : 0 < p) (c : ℝ) (f : (Fin n → Bool) → ℝ) :
    bnt_qnorm p (fun ω => c * f ω) = |c| * bnt_qnorm p f := by
  unfold bnt_qnorm bnt_qnormPow bnt_uexp
  have hcabs : ∀ ω : Fin n → Bool, |c * f ω| ^ p = |c| ^ p * |f ω| ^ p := by
    intro ω; rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  simp_rw [hcabs]
  rw [← Finset.mul_sum, mul_div_assoc,
      Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) p)
        (div_nonneg (Finset.sum_nonneg (fun ω _ => Real.rpow_nonneg (abs_nonneg _) p))
          (by positivity))]
  congr 1
  rw [← Real.rpow_mul (abs_nonneg c), mul_one_div, div_self (ne_of_gt hp), Real.rpow_one]

/-- The vector-valued two-point inequality at noise `ρ`, with `q = 1 + ρ²`: for all `n` and
`u v : (Fin n → Bool) → ℝ`, the average of `‖((1+ρ)/2) u + ((1-ρ)/2) v‖₂²` and
`‖((1-ρ)/2) u + ((1+ρ)/2) v‖₂²` is at most `((‖u‖_q^q + ‖v‖_q^q) / 2)^(2/q)`. -/
def bnt_VectorTwoPoint (ρ : ℝ) : Prop :=
  ∀ (n : ℕ) (u v : (Fin n → Bool) → ℝ),
    (bnt_qnormPow 2 (fun ω => (1 + ρ) / 2 * u ω + (1 - ρ) / 2 * v ω)
        + bnt_qnormPow 2 (fun ω => (1 - ρ) / 2 * u ω + (1 + ρ) / 2 * v ω)) / 2
      ≤ ((bnt_qnorm 2 u ^ (1 + ρ ^ 2) + bnt_qnorm 2 v ^ (1 + ρ ^ 2)) / 2) ^ (2 / (1 + ρ ^ 2))

theorem bnt_vectorTwoPoint_zero : bnt_VectorTwoPoint 0 := by
  intro n u v
  have hq : (1 : ℝ) + 0 ^ 2 = 1 := by norm_num
  rw [hq, show (2 : ℝ) / 1 = 2 by norm_num, Real.rpow_two]
  have e1 : (fun ω : Fin n → Bool => (1 + (0 : ℝ)) / 2 * u ω + (1 - 0) / 2 * v ω)
          = (fun ω => (1 / 2) * u ω + (1 / 2) * v ω) := by funext ω; norm_num
  have e2 : (fun ω : Fin n → Bool => (1 - (0 : ℝ)) / 2 * u ω + (1 + 0) / 2 * v ω)
          = (fun ω => (1 / 2) * u ω + (1 / 2) * v ω) := by funext ω; norm_num
  rw [e1, e2]
  set m := (fun ω : Fin n → Bool => (1 / 2 : ℝ) * u ω + (1 / 2) * v ω) with hm
  rw [show (bnt_qnormPow 2 m + bnt_qnormPow 2 m) / 2 = bnt_qnormPow 2 m by ring]
  rw [Real.rpow_one, Real.rpow_one]
  have htri : bnt_qnorm 2 m ≤ (bnt_qnorm 2 u + bnt_qnorm 2 v) / 2 := by
    have hmink := bnt_qnorm_add_le (n := n) (p := 2) (by norm_num)
      (fun ω => (1 / 2 : ℝ) * u ω) (fun ω => (1 / 2 : ℝ) * v ω)
    have hh1 := bnt_qnorm_const_mul (n := n) (p := 2) (by norm_num) (1 / 2 : ℝ) u
    have hh2 := bnt_qnorm_const_mul (n := n) (p := 2) (by norm_num) (1 / 2 : ℝ) v
    rw [hm]
    rw [hh1, hh2] at hmink
    simp only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hmink
    calc bnt_qnorm 2 (fun ω => (1 / 2 : ℝ) * u ω + (1 / 2 : ℝ) * v ω)
        ≤ 1 / 2 * bnt_qnorm 2 u + 1 / 2 * bnt_qnorm 2 v := hmink
      _ = (bnt_qnorm 2 u + bnt_qnorm 2 v) / 2 := by ring
  have hmnn : 0 ≤ bnt_qnorm 2 m := bnt_qnorm_nonneg 2 m
  have hrhs_nn : 0 ≤ (bnt_qnorm 2 u + bnt_qnorm 2 v) / 2 := by
    have := bnt_qnorm_nonneg 2 u; have := bnt_qnorm_nonneg 2 v; linarith
  have hsq : bnt_qnorm 2 m ^ 2 ≤ ((bnt_qnorm 2 u + bnt_qnorm 2 v) / 2) ^ 2 := by
    nlinarith [htri, hmnn, hrhs_nn]
  have hmpow : bnt_qnorm 2 m ^ (2 : ℝ) = bnt_qnormPow 2 m :=
    bnt_qnorm_rpow_self (by norm_num) m
  rw [Real.rpow_two] at hmpow
  rw [← hmpow]; exact hsq

theorem bnt_vectorTwoPoint_one : bnt_VectorTwoPoint 1 := by
  intro n u v
  have hq : (1 : ℝ) + 1 ^ 2 = 2 := by norm_num
  rw [hq, show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one]
  have e1 : (fun ω : Fin n → Bool => (1 + (1 : ℝ)) / 2 * u ω + (1 - 1) / 2 * v ω) = u := by
    funext ω; norm_num
  have e2 : (fun ω : Fin n → Bool => (1 - (1 : ℝ)) / 2 * u ω + (1 + 1) / 2 * v ω) = v := by
    funext ω; norm_num
  rw [e1, e2]
  have hu : bnt_qnorm 2 u ^ (2 : ℝ) = bnt_qnormPow 2 u := bnt_qnorm_rpow_self (by norm_num) u
  have hv : bnt_qnorm 2 v ^ (2 : ℝ) = bnt_qnormPow 2 v := bnt_qnorm_rpow_self (by norm_num) v
  rw [hu, hv]

/-- The induction step of tensorization: `‖T_ρ g‖₂ ≤ ‖g‖_(1+ρ²)` in dimension `n` implies the
same in dimension `n + 1`. -/
def bnt_TensorStep (ρ : ℝ) : Prop :=
  ∀ n : ℕ,
    (∀ g : (Fin n → Bool) → ℝ, bnt_qnorm 2 (bnt_noiseOp ρ g) ≤ bnt_qnorm (1 + ρ ^ 2) g) →
    (∀ f : (Fin (n + 1) → Bool) → ℝ,
      bnt_qnorm 2 (bnt_noiseOp ρ f) ≤ bnt_qnorm (1 + ρ ^ 2) f)

/-- The vector two-point inequality gives the tensorization step. -/
theorem bnt_tensorStep_of_vec {ρ : ℝ} (Hvec : bnt_VectorTwoPoint ρ) (n : ℕ)
    (ih : ∀ g : (Fin n → Bool) → ℝ, bnt_qnorm 2 (bnt_noiseOp ρ g) ≤ bnt_qnorm (1 + ρ ^ 2) g)
    (f : (Fin (n + 1) → Bool) → ℝ) :
    bnt_qnorm 2 (bnt_noiseOp ρ f) ≤ bnt_qnorm (1 + ρ ^ 2) f := by
  set q : ℝ := 1 + ρ ^ 2 with hqdef
  have hq0 : (0 : ℝ) < q := by rw [hqdef]; positivity
  set g₀ : (Fin n → Bool) → ℝ := fun ω' => f (Fin.cons false ω') with hg0
  set g₁ : (Fin n → Bool) → ℝ := fun ω' => f (Fin.cons true ω') with hg1
  set F₀ := bnt_noiseOp ρ g₀ with hF0
  set F₁ := bnt_noiseOp ρ g₁ with hF1
  have hcentral : bnt_qnormPow 2 (bnt_noiseOp ρ f)
      = (bnt_qnormPow 2 (fun ω : Fin n → Bool => (1 + ρ) / 2 * F₀ ω + (1 - ρ) / 2 * F₁ ω)
          + bnt_qnormPow 2 (fun ω : Fin n → Bool => (1 - ρ) / 2 * F₀ ω + (1 + ρ) / 2 * F₁ ω))
          / 2 := by
    unfold bnt_qnormPow
    rw [bnt_uexp_cons_split (fun x => |bnt_noiseOp ρ f x| ^ (2 : ℝ)), Fintype.sum_bool]
    simp only [bnt_noiseOp_cons_false, bnt_noiseOp_cons_true, hF0, hF1, hg0, hg1]
    rw [add_comm]
  have hvec := Hvec n F₀ F₁
  rw [← hqdef] at hvec
  have hstep1 : bnt_qnormPow 2 (bnt_noiseOp ρ f)
      ≤ ((bnt_qnorm 2 F₀ ^ q + bnt_qnorm 2 F₁ ^ q) / 2) ^ (2 / q) := by
    rw [hcentral]; exact hvec
  have hb0 : bnt_qnorm 2 F₀ ≤ bnt_qnorm q g₀ := ih g₀
  have hb1 : bnt_qnorm 2 F₁ ≤ bnt_qnorm q g₁ := ih g₁
  have hpow0 : bnt_qnorm 2 F₀ ^ q ≤ bnt_qnormPow q g₀ := by
    rw [← bnt_qnorm_rpow_self (ne_of_gt hq0) g₀]
    exact Real.rpow_le_rpow (bnt_qnorm_nonneg 2 F₀) hb0 (le_of_lt hq0)
  have hpow1 : bnt_qnorm 2 F₁ ^ q ≤ bnt_qnormPow q g₁ := by
    rw [← bnt_qnorm_rpow_self (ne_of_gt hq0) g₁]
    exact Real.rpow_le_rpow (bnt_qnorm_nonneg 2 F₁) hb1 (le_of_lt hq0)
  have hbase : (bnt_qnorm 2 F₀ ^ q + bnt_qnorm 2 F₁ ^ q) / 2 ≤ bnt_qnormPow q f := by
    have hsplit : bnt_qnormPow q f = (bnt_qnormPow q g₀ + bnt_qnormPow q g₁) / 2 := by
      rw [bnt_qnormPow_cons_split q f, Fintype.sum_bool, ← hg0, ← hg1]; ring
    rw [hsplit]; linarith
  have hB : (0 : ℝ) ≤ (bnt_qnorm 2 F₀ ^ q + bnt_qnorm 2 F₁ ^ q) / 2 := by
    have h0 : (0 : ℝ) ≤ bnt_qnorm 2 F₀ ^ q := Real.rpow_nonneg (bnt_qnorm_nonneg 2 F₀) q
    have h1 : (0 : ℝ) ≤ bnt_qnorm 2 F₁ ^ q := Real.rpow_nonneg (bnt_qnorm_nonneg 2 F₁) q
    linarith
  unfold bnt_qnorm
  calc (bnt_qnormPow 2 (bnt_noiseOp ρ f)) ^ ((1 : ℝ) / 2)
      ≤ (((bnt_qnorm 2 F₀ ^ q + bnt_qnorm 2 F₁ ^ q) / 2) ^ (2 / q)) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow (bnt_qnormPow_nonneg 2 _) hstep1 (by norm_num)
    _ = ((bnt_qnorm 2 F₀ ^ q + bnt_qnorm 2 F₁ ^ q) / 2) ^ (1 / q) := by
        rw [← Real.rpow_mul hB]; congr 1; field_simp
    _ ≤ (bnt_qnormPow q f) ^ (1 / q) := Real.rpow_le_rpow hB hbase (by positivity)

theorem bnt_tensorStep_one : bnt_TensorStep 1 := by
  intro n _ f
  have hid : bnt_noiseOp 1 f = f := by funext x; exact bnt_noiseOp_one f x
  rw [hid, show (1 : ℝ) + 1 ^ 2 = 2 by norm_num]

theorem bnt_qnorm_fin_zero {q : ℝ} (hq : 0 < q) (f : (Fin 0 → Bool) → ℝ) :
    bnt_qnorm q f = |f default| := by
  unfold bnt_qnorm bnt_qnormPow bnt_uexp
  rw [show Fintype.card (Fin 0) = 0 by simp, pow_zero, div_one]
  rw [Finset.sum_eq_single (default : Fin 0 → Bool)]
  · rw [← Real.rpow_mul (abs_nonneg _), mul_one_div, div_self (ne_of_gt hq), Real.rpow_one]
  · intro y _ hy; exact absurd (Subsingleton.elim y default) hy
  · intro h; exact absurd (Finset.mem_univ _) h

theorem bnt_noiseOp_fin_zero (ρ : ℝ) (f : (Fin 0 → Bool) → ℝ) :
    bnt_noiseOp ρ f = f := by
  funext x
  unfold bnt_noiseOp bnt_noiseKernel
  rw [Finset.sum_eq_single x]
  · rw [Finset.prod_eq_one (fun i _ => by exact absurd i.2 (by simp)), one_mul]
  · intro y _ hyx; exact absurd (Subsingleton.elim y x) hyx
  · intro h; exact absurd (Finset.mem_univ x) h

theorem bnt_hypercontractivity_fin_zero (ρ : ℝ) (f : (Fin 0 → Bool) → ℝ) :
    bnt_qnorm 2 (bnt_noiseOp ρ f) ≤ bnt_qnorm (1 + ρ ^ 2) f := by
  rw [bnt_noiseOp_fin_zero ρ f, bnt_qnorm_fin_zero (by norm_num),
    bnt_qnorm_fin_zero (by positivity)]

/-- Hypercontractivity `‖T_ρ f‖₂ ≤ ‖f‖_(1+ρ²)` on `Fin n → Bool`, from the vector two-point
inequality. -/
theorem bnt_hypercontractivity {ρ : ℝ} (Hvec : bnt_VectorTwoPoint ρ) (n : ℕ)
    (f : (Fin n → Bool) → ℝ) :
    bnt_qnorm 2 (bnt_noiseOp ρ f) ≤ bnt_qnorm (1 + ρ ^ 2) f := by
  induction n with
  | zero => exact bnt_hypercontractivity_fin_zero ρ f
  | succ m ih => exact bnt_tensorStep_of_vec Hvec m (fun g => ih g) f

/-- Hypercontractivity `‖T_ρ f‖₂ ≤ ‖f‖_(1+ρ²)` on `Fin n → Bool`, from the tensorization step. -/
theorem bnt_hypercontractivity_of_twoPoint {ρ : ℝ} (Hstep : bnt_TensorStep ρ)
    (n : ℕ) (f : (Fin n → Bool) → ℝ) :
    bnt_qnorm 2 (bnt_noiseOp ρ f) ≤ bnt_qnorm (1 + ρ ^ 2) f := by
  induction n with
  | zero => exact bnt_hypercontractivity_fin_zero ρ f
  | succ m ih => exact Hstep m (fun g => ih g) f

end Probability
end StatMech
