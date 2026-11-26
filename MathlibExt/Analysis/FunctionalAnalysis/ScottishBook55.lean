/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.Module.Multilinear.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Mazur's Problem 55 has a negative answer

The factorisation claim of Scottish Book Problem 55
(`ScottishBookProblem55Claim`) is false (`mazur55_refuted`). Pestov's
inhomogeneous quadratic polynomial on `ℓ²` is bounded on the open
`1`-neighbourhood of an unbounded set `R` but unbounded on `(1 / 2) R`,
so it has no factorisation through a bounded affine image.

Source: S. Mazur, Problem 55 of the Scottish Book; V. Pestov, "Two 1935
questions of Mazur about polynomials in Banach spaces: a
counter-example" (1997), arXiv:funct-an/9705002, Sections 2-3.
-/

@[expose] public section

open scoped BigOperators ENNReal

noncomputable section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook55Wanted

/-- Mazur's Problem 55 from the Scottish Book, in the Banach-space
form: every continuous polynomial `W`, of arbitrary finite degree, that
is bounded on an `ε`-neighbourhood of an unbounded set `R` factors as
`W = V ∘ φ`, where `φ x = L x + a` is a continuous affine map into a
normed space `F` with `φ(R)` bounded, and `V` is a continuous
polynomial on `F`.

Continuous polynomials are encoded here, both for `W` on `E` and for
`V` on `F`, as finite sums of diagonals of continuous multilinear
maps, `W x = ∑ j, P j (fun _ => x)` and `V y = ∑ j, A j (fun _ => y)`,
the `j = 0` terms being the constant terms. Over `ℝ` every continuous
polynomial has this form, by polarization, and every such sum is a
continuous polynomial, so this is the usual notion, covering every
finite degree.

Both features of the factorisation are essential. With a scalar factor
(`F = ℝ`) the claim already fails in finite dimensions: on `ℝ³` with
`R` the first coordinate axis, `W x = x₂² + x₃²` is bounded near `R`
but no `V (L x + c)` equals it, since for `L ≠ 0` the function `W` is
unbounded on every level set of `L`, and for `L = 0` it would be
constant. And the inhomogeneous terms (`j = 0` and `j = 1` above)
matter because Pestov's counterexample is inhomogeneous. In finite
dimensions the answer with a general normed-space factor is positive
(Auerbach). -/
def ScottishBookProblem55Claim : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (R : Set E) (n : ℕ)
    (P : (j : Fin (n + 1)) →
      ContinuousMultilinearMap ℝ (fun _ : Fin (j : ℕ) => E) ℝ),
    (∀ M : ℝ, ∃ r ∈ R, M < ‖r‖) →
    (∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ,
      ∀ x : E, (∃ r ∈ R, dist x r < ε) → |∑ j, P j (fun _ => x)| ≤ C) →
    ∃ (F : Type) (_ : NormedAddCommGroup F) (_ : NormedSpace ℝ F)
      (L : E →L[ℝ] F) (a : F) (d : ℕ)
      (A : (j : Fin (d + 1)) →
        ContinuousMultilinearMap ℝ (fun _ : Fin (j : ℕ) => F) ℝ),
      (∀ x : E, (∑ j, P j (fun _ => x)) = ∑ j, A j (fun _ => L x + a)) ∧
      ∃ M : ℝ, ∀ r ∈ R, ‖L r + a‖ ≤ M

/-! ### The diagonal bilinear form on `ℓ²` -/

/-- The underlying Banach space `ℓ²`. -/
private abbrev E := lp (fun _ : ℕ => ℝ) 2

/-- The diagonal weights: `w 0 = 0` and `w n = -(n⁻¹)` for `n ≠ 0`. -/
private def w : ℕ → ℝ := fun n => if n = 0 then 0 else -(n : ℝ)⁻¹

private theorem w_abs_le_one (n : ℕ) : |w n| ≤ 1 := by
  by_cases hn : n = 0
  · subst hn
    simp [w]
  · simp only [w, hn, ite_false]
    rw [abs_neg, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
    exact inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn))

/-- The squared norm on `ℓ²` is the sum of the squared coordinates. -/
private theorem norm_sq_eq (x : E) : ‖x‖ ^ 2 = ∑' n, ((x : ℕ → ℝ) n) ^ 2 := by
  have ht : (2 : ℝ≥0∞).toReal = 2 := by simp
  have hform :=
    lp.norm_eq_tsum_rpow (by rw [ht]; norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) x
  rw [ht] at hform
  have e : ∀ n : ℕ, ‖(x : ℕ → ℝ) n‖ ^ (2 : ℝ) = ((x : ℕ → ℝ) n) ^ 2 := by
    intro n
    rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
  have hS : 0 ≤ ∑' n, ((x : ℕ → ℝ) n) ^ 2 := tsum_nonneg (fun n => sq_nonneg _)
  calc ‖x‖ ^ 2 = ((∑' n, ((x : ℕ → ℝ) n) ^ 2) ^ ((1 : ℝ) / 2)) ^ 2 := by
        rw [hform, tsum_congr e]
    _ = ∑' n, ((x : ℕ → ℝ) n) ^ 2 := by
        generalize ∑' n, ((x : ℕ → ℝ) n) ^ 2 = S at hS ⊢
        rw [← Real.rpow_natCast, ← Real.rpow_mul hS]
        have hexp : ((1 : ℝ) / 2) * ((2 : ℕ) : ℝ) = 1 := by norm_num
        rw [hexp, Real.rpow_one]

/-- Square-summability of the coordinates of a point of `ℓ²`. -/
private theorem summable_sq (x : E) : Summable (fun n => ((x : ℕ → ℝ) n) ^ 2) := by
  have ht : (2 : ℝ≥0∞).toReal = 2 := by simp
  have h :=
    Memℓp.summable (by rw [ht]; norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) x.2
  rw [ht] at h
  have e : ∀ n : ℕ, ‖(x : ℕ → ℝ) n‖ ^ (2 : ℝ) = ((x : ℕ → ℝ) n) ^ 2 := by
    intro n
    rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
  exact (summable_congr e).mp h

/-- The diagonal bilinear form on `ℓ²`, as a function. -/
private def Bfn : E → E → ℝ := fun x y => ∑' n, w n * ((x : ℕ → ℝ) n * (y : ℕ → ℝ) n)

/-- Summability of the terms of `Bfn`, in norm. -/
private theorem summable_Bfn_norm (x y : E) :
    Summable (fun n => ‖w n * ((x : ℕ → ℝ) n * (y : ℕ → ℝ) n)‖) := by
  have hhalf : Summable (fun n => ((x : ℕ → ℝ) n) ^ 2 + ((y : ℕ → ℝ) n) ^ 2) :=
    (summable_sq x).add (summable_sq y)
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hhalf
  have hw := w_abs_le_one n
  have hcs := two_mul_le_add_sq |(x : ℕ → ℝ) n| |(y : ℕ → ℝ) n|
  rw [sq_abs, sq_abs] at hcs
  simp only [norm_mul, Real.norm_eq_abs]
  calc |w n| * (|(x : ℕ → ℝ) n| * |(y : ℕ → ℝ) n|)
      ≤ |(x : ℕ → ℝ) n| * |(y : ℕ → ℝ) n| := by
        have hle : |w n| * (|(x : ℕ → ℝ) n| * |(y : ℕ → ℝ) n|) ≤
            1 * (|(x : ℕ → ℝ) n| * |(y : ℕ → ℝ) n|) :=
          mul_le_mul_of_nonneg_right hw (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        simpa using hle
    _ ≤ ((x : ℕ → ℝ) n) ^ 2 + ((y : ℕ → ℝ) n) ^ 2 := by
        have hx := sq_nonneg ((x : ℕ → ℝ) n)
        have hy := sq_nonneg ((y : ℕ → ℝ) n)
        linarith

/-- Summability of the terms of `Bfn`. -/
private theorem summable_Bfn (x y : E) :
    Summable (fun n => w n * ((x : ℕ → ℝ) n * (y : ℕ → ℝ) n)) := by
  have h := summable_Bfn_norm x y
  have e : ∀ n : ℕ, ‖w n * ((x : ℕ → ℝ) n * (y : ℕ → ℝ) n)‖ =
      |w n * ((x : ℕ → ℝ) n * (y : ℕ → ℝ) n)| := fun n => Real.norm_eq_abs _
  exact summable_abs_iff.mp ((summable_congr e).mp h)

private theorem Bfn_add_left (x₁ x₂ y : E) : Bfn (x₁ + x₂) y = Bfn x₁ y + Bfn x₂ y := by
  have h := Summable.tsum_add (summable_Bfn x₁ y) (summable_Bfn x₂ y)
  simp only [Bfn]
  rw [← h]
  apply tsum_congr
  intro n
  show w n * (((x₁ + x₂ : E) : ℕ → ℝ) n * (y : ℕ → ℝ) n) =
    w n * ((x₁ : ℕ → ℝ) n * (y : ℕ → ℝ) n) + w n * ((x₂ : ℕ → ℝ) n * (y : ℕ → ℝ) n)
  show w n * ((((x₁ : ℕ → ℝ) n + (x₂ : ℕ → ℝ) n)) * (y : ℕ → ℝ) n) = _
  ring

private theorem Bfn_add_right (x y₁ y₂ : E) : Bfn x (y₁ + y₂) = Bfn x y₁ + Bfn x y₂ := by
  have h := Summable.tsum_add (summable_Bfn x y₁) (summable_Bfn x y₂)
  simp only [Bfn]
  rw [← h]
  apply tsum_congr
  intro n
  show w n * ((x : ℕ → ℝ) n * (((y₁ + y₂ : E) : ℕ → ℝ) n)) =
    w n * ((x : ℕ → ℝ) n * (y₁ : ℕ → ℝ) n) + w n * ((x : ℕ → ℝ) n * (y₂ : ℕ → ℝ) n)
  show w n * ((x : ℕ → ℝ) n * (((y₁ : ℕ → ℝ) n + (y₂ : ℕ → ℝ) n))) = _
  ring

private theorem Bfn_smul_left (c : ℝ) (x y : E) : Bfn (c • x) y = c • Bfn x y := by
  simp only [Bfn, smul_eq_mul]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  show w n * (((c • x : E) : ℕ → ℝ) n * (y : ℕ → ℝ) n) =
    c * (w n * ((x : ℕ → ℝ) n * (y : ℕ → ℝ) n))
  show w n * ((c * (x : ℕ → ℝ) n) * (y : ℕ → ℝ) n) = _
  ring

private theorem Bfn_smul_right (c : ℝ) (x y : E) : Bfn x (c • y) = c • Bfn x y := by
  simp only [Bfn, smul_eq_mul]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  show w n * ((x : ℕ → ℝ) n * (((c • y : E) : ℕ → ℝ) n)) =
    c * (w n * ((x : ℕ → ℝ) n * (y : ℕ → ℝ) n))
  show w n * ((x : ℕ → ℝ) n * (c * (y : ℕ → ℝ) n)) = _
  ring

/-- The operator-norm bound for `Bfn`, by Cauchy–Schwarz. -/
private theorem Bfn_bound (x y : E) : ‖Bfn x y‖ ≤ 1 * ‖x‖ * ‖y‖ := by
  have hS : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, ‖w n * ((x : ℕ → ℝ) n * (y : ℕ → ℝ) n)‖) ≤ ‖x‖ * ‖y‖ := by
    intro N
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N)
      (fun n => |(x : ℕ → ℝ) n|) (fun n => |(y : ℕ → ℝ) n|)
    simp only [sq_abs] at hcs
    have hle : (∑ n ∈ Finset.range N, ‖w n * ((x : ℕ → ℝ) n * (y : ℕ → ℝ) n)‖) ≤
        ∑ n ∈ Finset.range N, |(x : ℕ → ℝ) n| * |(y : ℕ → ℝ) n| := by
      apply Finset.sum_le_sum
      intro n _
      simp only [norm_mul, Real.norm_eq_abs]
      have hw := w_abs_le_one n
      have hle : |w n| * (|(x : ℕ → ℝ) n| * |(y : ℕ → ℝ) n|) ≤
          1 * (|(x : ℕ → ℝ) n| * |(y : ℕ → ℝ) n|) :=
        mul_le_mul_of_nonneg_right hw (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      simpa using hle
    have hxx : (∑ n ∈ Finset.range N, ((x : ℕ → ℝ) n) ^ 2) ≤ ‖x‖ ^ 2 := by
      have h := Summable.sum_le_tsum (Finset.range N) (fun n _ => sq_nonneg _) (summable_sq x)
      rw [norm_sq_eq x]
      exact h
    have hyy : (∑ n ∈ Finset.range N, ((y : ℕ → ℝ) n) ^ 2) ≤ ‖y‖ ^ 2 := by
      have h := Summable.sum_le_tsum (Finset.range N) (fun n _ => sq_nonneg _) (summable_sq y)
      rw [norm_sq_eq y]
      exact h
    have hsq : ((∑ n ∈ Finset.range N, |(x : ℕ → ℝ) n| * |(y : ℕ → ℝ) n|)) ^ 2 ≤
        (‖x‖ * ‖y‖) ^ 2 := by
      calc ((∑ n ∈ Finset.range N, |(x : ℕ → ℝ) n| * |(y : ℕ → ℝ) n|)) ^ 2
          ≤ (∑ n ∈ Finset.range N, ((x : ℕ → ℝ) n) ^ 2) *
            (∑ n ∈ Finset.range N, ((y : ℕ → ℝ) n) ^ 2) := hcs
        _ ≤ (‖x‖ ^ 2) * (‖y‖ ^ 2) :=
            mul_le_mul hxx hyy (Finset.sum_nonneg (fun n _ => sq_nonneg _)) (sq_nonneg _)
        _ = (‖x‖ * ‖y‖) ^ 2 := by ring
    have hnn1 : 0 ≤ (∑ n ∈ Finset.range N, |(x : ℕ → ℝ) n| * |(y : ℕ → ℝ) n|) :=
      Finset.sum_nonneg (fun n _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hnn2 : 0 ≤ ‖x‖ * ‖y‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hfin : (∑ n ∈ Finset.range N, |(x : ℕ → ℝ) n| * |(y : ℕ → ℝ) n|) ≤ ‖x‖ * ‖y‖ := by
      have hab := sq_le_sq.mp hsq
      rwa [abs_of_nonneg hnn1, abs_of_nonneg hnn2] at hab
    exact hle.trans hfin
  have hlim := (summable_Bfn_norm x y).hasSum.tendsto_sum_nat
  have hle : (∑' n, ‖w n * ((x : ℕ → ℝ) n * (y : ℕ → ℝ) n)‖) ≤ ‖x‖ * ‖y‖ :=
    le_of_tendsto hlim (Filter.Eventually.of_forall hS)
  calc ‖Bfn x y‖ = ‖∑' n, w n * ((x : ℕ → ℝ) n * (y : ℕ → ℝ) n)‖ := rfl
    _ ≤ ∑' n, ‖w n * ((x : ℕ → ℝ) n * (y : ℕ → ℝ) n)‖ :=
        norm_tsum_le_tsum_norm (summable_Bfn_norm x y)
    _ ≤ ‖x‖ * ‖y‖ := hle
    _ = 1 * ‖x‖ * ‖y‖ := by ring

/-! ### The linear term, the set `R`, and pointwise values -/

/-- Evaluation at coordinate `0`, as a function. -/
private def Lfn : E → ℝ := fun x => (x : ℕ → ℝ) 0

private theorem Lfn_add (x y : E) : Lfn (x + y) = Lfn x + Lfn y := rfl

private theorem Lfn_smul (c : ℝ) (x : E) : Lfn (c • x) = c • Lfn x := rfl

/-- A coordinate is bounded by the norm. -/
private theorem coord_le_norm (x : E) (i : ℕ) : |(x : ℕ → ℝ) i| ≤ ‖x‖ := by
  have hsum := summable_sq x
  have h0 := Summable.sum_le_tsum ({i} : Finset ℕ) (fun n _ => sq_nonneg _) hsum
  rw [Finset.sum_singleton, ← norm_sq_eq x] at h0
  have hab := sq_le_sq.mp h0
  rwa [abs_of_nonneg (norm_nonneg x)] at hab

/-- The operator-norm bound for `Lfn`. -/
private theorem Lfn_bound (x : E) : ‖Lfn x‖ ≤ 1 * ‖x‖ := by
  have h := coord_le_norm x 0
  simp only [Lfn, Real.norm_eq_abs, one_mul]
  exact h

/-- The standard basis vectors. -/
private def e : ℕ → E := fun i => lp.single 2 i 1

private theorem e_self (i : ℕ) : ((e i : E) : ℕ → ℝ) i = 1 :=
  lp.single_apply_self 2 i 1

private theorem e_ne {i j : ℕ} (h : j ≠ i) : ((e i : E) : ℕ → ℝ) j = 0 :=
  lp.single_apply_ne 2 i 1 h

/-- The points `r n = n • (e 0 + e n)`. -/
private def r : ℕ → E := fun n => (n : ℝ) • (e 0 + e n)

/-- The unbounded set `R`. -/
private def R : Set E := {x | ∃ n : ℕ, n ≠ 0 ∧ x = r n}

private theorem r_zero_coord {n : ℕ} (hn : n ≠ 0) : ((r n : E) : ℕ → ℝ) 0 = n := by
  show (n : ℝ) * (((e 0 : E) : ℕ → ℝ) 0 + ((e n : E) : ℕ → ℝ) 0) = n
  rw [e_self 0, e_ne (Ne.symm hn)]
  simp

private theorem r_coord {n k : ℕ} (hk0 : k ≠ 0) (hkn : k ≠ n) :
    ((r n : E) : ℕ → ℝ) k = 0 := by
  show (n : ℝ) * (((e 0 : E) : ℕ → ℝ) k + ((e n : E) : ℕ → ℝ) k) = 0
  rw [e_ne hk0, e_ne hkn, add_zero, mul_zero]

private theorem r_self_coord {n : ℕ} (hn : n ≠ 0) : ((r n : E) : ℕ → ℝ) n = n := by
  show (n : ℝ) * (((e 0 : E) : ℕ → ℝ) n + ((e n : E) : ℕ → ℝ) n) = n
  rw [e_ne hn, e_self n]
  simp

private theorem w_eq {n : ℕ} (hn : n ≠ 0) : w n = -(n : ℝ)⁻¹ := by simp [w, hn]

/-- `B (r n) (r n) = -n`. -/
private theorem Bfn_r_r {n : ℕ} (hn : n ≠ 0) : Bfn (r n) (r n) = -(n : ℝ) := by
  have hvan : ∀ k : ℕ, k ≠ n →
      w k * (((r n : E) : ℕ → ℝ) k * ((r n : E) : ℕ → ℝ) k) = 0 := by
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      simp [w]
    · simp [r_coord hk0 hk]
  simp only [Bfn]
  rw [tsum_eq_single n hvan, r_self_coord hn, w_eq hn]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  calc (-(n : ℝ)⁻¹) * ((n : ℝ) * (n : ℝ)) = -(((n : ℝ)⁻¹ * (n : ℝ)) * (n : ℝ)) := by ring
    _ = -(n : ℝ) := by rw [inv_mul_cancel₀ hnR, one_mul]

/-- `B (r n) h = -hₙ`. -/
private theorem Bfn_r_h {n : ℕ} (hn : n ≠ 0) (h : E) :
    Bfn (r n) h = -((h : ℕ → ℝ) n) := by
  have hvan : ∀ k : ℕ, k ≠ n →
      w k * (((r n : E) : ℕ → ℝ) k * (h : ℕ → ℝ) k) = 0 := by
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      simp [w]
    · simp [r_coord hk0 hk]
  simp only [Bfn]
  rw [tsum_eq_single n hvan, r_self_coord hn, w_eq hn]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  calc (-(n : ℝ)⁻¹) * ((n : ℝ) * (h : ℕ → ℝ) n)
      = -(((n : ℝ)⁻¹ * (n : ℝ)) * (h : ℕ → ℝ) n) := by ring
    _ = -((h : ℕ → ℝ) n) := by rw [inv_mul_cancel₀ hnR, one_mul]

/-- `B h (r n) = -hₙ`. -/
private theorem Bfn_h_r {n : ℕ} (hn : n ≠ 0) (h : E) :
    Bfn h (r n) = -((h : ℕ → ℝ) n) := by
  have hvan : ∀ k : ℕ, k ≠ n →
      w k * ((h : ℕ → ℝ) k * ((r n : E) : ℕ → ℝ) k) = 0 := by
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      simp [w]
    · simp [r_coord hk0 hk]
  simp only [Bfn]
  rw [tsum_eq_single n hvan, r_self_coord hn, w_eq hn]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  calc (-(n : ℝ)⁻¹) * ((h : ℕ → ℝ) n * (n : ℝ))
      = -(((n : ℝ)⁻¹ * (n : ℝ)) * (h : ℕ → ℝ) n) := by ring
    _ = -((h : ℕ → ℝ) n) := by rw [inv_mul_cancel₀ hnR, one_mul]

private theorem Lfn_r {n : ℕ} (hn : n ≠ 0) : Lfn (r n) = n := r_zero_coord hn

private theorem R_unbounded : ∀ M : ℝ, ∃ r ∈ R, M < ‖r‖ := by
  intro M
  obtain ⟨n, hn⟩ := exists_nat_gt M
  refine ⟨r (n + 1), ⟨n + 1, by omega, rfl⟩, ?_⟩
  have h01 : ((r (n + 1) : E) : ℕ → ℝ) 0 = ((n + 1 : ℕ) : ℝ) := r_zero_coord (by omega)
  have hle : |((r (n + 1) : E) : ℕ → ℝ) 0| ≤ ‖r (n + 1)‖ := coord_le_norm _ _
  rw [h01] at hle
  have hpos : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [abs_of_nonneg hpos] at hle
  have hlt : M < ((n + 1 : ℕ) : ℝ) := by
    have hnn : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by norm_num
    linarith
  linarith

/-! ### The polynomial as multilinear diagonals -/

/-- The constant term, `0`. -/
private def P0 : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ := 0

/-- The linear term, as a multilinear map. -/
private def P1ml : (Π _ : Fin 1, E) →ₘₗ[ℝ] ℝ :=
  MultilinearMap.mk (fun m => Lfn (m 0)) (fun m i x y => by
    fin_cases i
    simp [Lfn_add]) (fun m i c x => by
    fin_cases i
    simp [Lfn_smul])

/-- The linear term, continuously. -/
private def P1 : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ :=
  MultilinearMap.mkContinuous P1ml 1 (by
    intro m
    rw [Fin.prod_univ_one]
    show ‖Lfn (m 0)‖ ≤ 1 * ‖m 0‖
    exact Lfn_bound (m 0))

/-- The quadratic term, as a multilinear map. -/
private def P2ml : (Π _ : Fin 2, E) →ₘₗ[ℝ] ℝ :=
  MultilinearMap.mk (fun m => Bfn (m 0) (m 1)) (fun m i x y => by
    fin_cases i <;> simp [Bfn_add_left, Bfn_add_right]) (fun m i c x => by
    fin_cases i <;> simp [Bfn_smul_left, Bfn_smul_right])

/-- The quadratic term, continuously. -/
private def P2 : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ :=
  MultilinearMap.mkContinuous P2ml 1 (by
    intro m
    rw [Fin.prod_univ_two]
    show ‖Bfn (m 0) (m 1)‖ ≤ 1 * (‖m 0‖ * ‖m 1‖)
    have h := Bfn_bound (m 0) (m 1)
    rwa [mul_assoc] at h)

private abbrev C (j : Fin 3) :=
  ContinuousMultilinearMap ℝ (fun _ : Fin (j : ℕ) => E) ℝ

/-- The polynomial data: constant `0`, linear `Lfn`, quadratic `Bfn`. -/
private def P : (j : Fin 3) → C j
  | ⟨0, _⟩ => P0
  | ⟨1, _⟩ => P1
  | ⟨2, _⟩ => P2
  | ⟨n + 3, h⟩ => absurd h (by omega)

private theorem P_zero : P 0 = P0 := rfl

private theorem P_one : P 1 = P1 := rfl

private theorem P_two : P 2 = P2 := rfl

private theorem P0_apply (m : Fin 0 → E) : P0 m = 0 := rfl

private theorem P1_apply (m : Fin 1 → E) : P1 m = Lfn (m 0) := rfl

private theorem P2_apply (m : Fin 2 → E) : P2 m = Bfn (m 0) (m 1) := rfl

/-- The polynomial is `Lfn + Bfn` on the diagonal. -/
private theorem Wdiag (x : E) : (∑ j, P j (fun _ => x)) = Lfn x + Bfn x x := by
  rw [Fin.sum_univ_three, P_zero, P_one, P_two, P0_apply, P1_apply, P2_apply]
  simp

/-- `W ((1 / 2) • r n) = n / 4`. -/
private theorem W_half {n : ℕ} (hn : n ≠ 0) :
    (∑ j, P j (fun _ => (1 / 2 : ℝ) • r n)) = (n : ℝ) / 4 := by
  rw [Wdiag]
  have hL : Lfn ((1 / 2 : ℝ) • r n) = (1 / 2 : ℝ) * n := by
    rw [Lfn_smul, Lfn_r hn, smul_eq_mul]
  have hB : Bfn ((1 / 2 : ℝ) • r n) ((1 / 2 : ℝ) • r n) =
      (1 / 2 : ℝ) * ((1 / 2 : ℝ) * (-(n : ℝ))) := by
    rw [Bfn_smul_left, Bfn_smul_right, Bfn_r_r hn, smul_eq_mul, smul_eq_mul]
  rw [hL, hB]
  ring

/-- `W` is bounded by `4` on the open `1`-neighbourhood of `R`. -/
private theorem W_nbhd (x : E) (h : ∃ r ∈ R, dist x r < 1) :
    |∑ j, P j (fun _ => x)| ≤ 4 := by
  obtain ⟨r, ⟨n, hn0, rfl⟩, hdr⟩ := h
  rw [dist_eq_norm] at hdr
  have hx : x = r n + (x - r n) := (add_sub_cancel _ _).symm
  have hW : (∑ j, P j (fun _ => x)) = Lfn (x - r n) +
      (-(((x - r n : E) : ℕ → ℝ) n) +
        (-(((x - r n : E) : ℕ → ℝ) n) + Bfn (x - r n) (x - r n))) := by
    conv_lhs => rw [hx]
    rw [Wdiag, Lfn_add, Bfn_add_left, Bfn_add_right, Bfn_add_right,
      Lfn_r hn0, Bfn_r_r hn0, Bfn_r_h hn0, Bfn_h_r hn0]
    ring
  rw [hW]
  have hL0 : |Lfn (x - r n)| ≤ ‖x - r n‖ := by
    have hbb := Lfn_bound (x - r n)
    rwa [Real.norm_eq_abs, one_mul] at hbb
  have hLn : |(((x - r n : E) : ℕ → ℝ) n)| ≤ ‖x - r n‖ := coord_le_norm _ _
  have hB : |Bfn (x - r n) (x - r n)| ≤ ‖x - r n‖ * ‖x - r n‖ := by
    have hbb := Bfn_bound (x - r n) (x - r n)
    rwa [Real.norm_eq_abs, one_mul] at hbb
  have hnn : 0 ≤ ‖x - r n‖ := norm_nonneg _
  calc |Lfn (x - r n) + (-(((x - r n : E) : ℕ → ℝ) n) +
          (-(((x - r n : E) : ℕ → ℝ) n) + Bfn (x - r n) (x - r n)))|
      ≤ |Lfn (x - r n)| + (|-(((x - r n : E) : ℕ → ℝ) n)| +
          (|-(((x - r n : E) : ℕ → ℝ) n)| + |Bfn (x - r n) (x - r n)|)) :=
        (abs_add_le _ _).trans (add_le_add le_rfl
          ((abs_add_le _ _).trans (add_le_add le_rfl (abs_add_le _ _))))
    _ ≤ ‖x - r n‖ + (2 * ‖x - r n‖ + ‖x - r n‖ * ‖x - r n‖) := by
        simp only [abs_neg]
        have h2 : |(((x - r n : E) : ℕ → ℝ) n)| + |(((x - r n : E) : ℕ → ℝ) n)| ≤
            2 * ‖x - r n‖ := by
          linarith [hLn]
        linarith [hL0, h2, hB]
    _ ≤ 4 := by
        have hsq : ‖x - r n‖ * ‖x - r n‖ ≤ ‖x - r n‖ := by
          calc ‖x - r n‖ * ‖x - r n‖ ≤ 1 * ‖x - r n‖ :=
                mul_le_mul_of_nonneg_right hdr.le hnn
            _ = ‖x - r n‖ := one_mul _
        have hlt : ‖x - r n‖ + (2 * ‖x - r n‖ + ‖x - r n‖ * ‖x - r n‖) < 4 := by
          linarith
        exact hlt.le

/-! ### No factorisation exists -/

/-- The scaled set `(1 / 2) R`. -/
private def halfR : Set E := (fun x : E => (1 / 2 : ℝ) • x) '' R

/-- `W` is unbounded on `(1 / 2) R`. -/
private theorem W_half_unbounded :
    ∀ C : ℝ, ∃ y ∈ halfR, C < |∑ j, P j (fun _ => y)| := by
  intro C
  obtain ⟨n, hn⟩ := exists_nat_gt (4 * C)
  refine ⟨(1 / 2 : ℝ) • r (n + 1), ⟨r (n + 1), ⟨n + 1, by omega, rfl⟩, rfl⟩, ?_⟩
  rw [W_half (by omega : n + 1 ≠ 0)]
  have hpos : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) / 4 :=
    div_nonneg (Nat.cast_nonneg _) (by norm_num)
  rw [abs_of_nonneg hpos]
  have hnn : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by norm_num
  linarith

/-- A factorisation would make `W` bounded on `(1 / 2) R`. -/
private theorem W_half_bounded (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (a : F) (d : ℕ)
    (A : (j : Fin (d + 1)) →
      ContinuousMultilinearMap ℝ (fun _ : Fin (j : ℕ) => F) ℝ)
    (hfac : ∀ x : E, (∑ j : Fin 3, P j (fun _ => x)) = ∑ j, A j (fun _ => L x + a))
    (M : ℝ) (hM : ∀ r ∈ R, ‖L r + a‖ ≤ M) :
    ∃ Cb : ℝ, ∀ y ∈ halfR, |∑ j, P j (fun _ => y)| ≤ Cb := by
  set Bnd : ℝ := |M| + ‖a‖ with hBnd
  have hV : ∀ y : F, ‖y‖ ≤ Bnd →
      |∑ j, A j (fun _ => y)| ≤ ∑ j, ‖A j‖ * Bnd ^ (j : ℕ) := by
    intro y hy
    calc |∑ j, A j (fun _ => y)| = ‖∑ j, A j (fun _ => y)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑ j, ‖A j (fun _ => y)‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖A j‖ * Bnd ^ (j : ℕ) := by
          apply Finset.sum_le_sum
          intro j _
          have hj := ContinuousMultilinearMap.le_opNorm (A j) (fun _ => y)
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hj
          calc ‖A j (fun _ => y)‖ ≤ ‖A j‖ * ‖y‖ ^ (j : ℕ) := hj
            _ ≤ ‖A j‖ * Bnd ^ (j : ℕ) :=
                mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hy _)
                  (norm_nonneg _)
  refine ⟨∑ j, ‖A j‖ * Bnd ^ (j : ℕ), fun y hy => ?_⟩
  obtain ⟨r, hrR, rfl⟩ : ∃ r ∈ R, (1 / 2 : ℝ) • r = y := hy
  rw [hfac]
  apply hV
  have h2 : (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • a = a := by
    rw [← add_smul, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, one_smul]
  have haff : L ((1 / 2 : ℝ) • r) + a = (1 / 2 : ℝ) • (L r + a) + (1 / 2 : ℝ) • a := by
    rw [map_smul, smul_add, add_assoc, h2]
  calc ‖L ((1 / 2 : ℝ) • r) + a‖
      = ‖(1 / 2 : ℝ) • (L r + a) + (1 / 2 : ℝ) • a‖ := by rw [haff]
    _ ≤ ‖(1 / 2 : ℝ) • (L r + a)‖ + ‖(1 / 2 : ℝ) • a‖ := norm_add_le _ _
    _ = (1 / 2) * ‖L r + a‖ + (1 / 2) * ‖a‖ := by
        simp only [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
    _ ≤ (1 / 2) * |M| + (1 / 2) * ‖a‖ := by
        apply add_le_add _ le_rfl
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
        exact (hM r hrR).trans (le_abs_self M)
    _ ≤ Bnd := by
        simp only [hBnd]
        linarith [abs_nonneg M, norm_nonneg a]

/--
Mazur's Problem 55 is false in the Banach-space form above. It already
fails for continuous polynomials of degree at most two, which refutes
the claim for arbitrary finite degree. Pestov constructs a
scalar-valued inhomogeneous 2-polynomial `W` on `ℓ²` that is bounded on
an `ε`-neighbourhood of an unbounded set `R` but unbounded on
`(1 / 2) R`. A continuous affine map with bounded image on `R` also has
bounded image on `(1 / 2) R`, and a continuous polynomial is bounded on
bounded sets, so no factorisation `W = V ∘ φ` of the required form can
exist.

Source: S. Mazur, Problem 55 of the Scottish Book; V. Pestov, "Two 1935
questions of Mazur about polynomials in Banach spaces: a
counter-example" (1997), arXiv:funct-an/9705002, Sections 2-3. The same
counterexample refutes Problem 75. In finite dimensions the answer is
positive (Auerbach), with a normed-space-valued affine factor rather
than a single scalar coordinate, so the infinite-dimensional Banach
setting is essential.
-/
theorem mazur55_refuted : ¬ ScottishBookProblem55Claim := by
  intro H
  obtain ⟨F, _, _, L, a, d, A, hfac, M, hM⟩ :=
    H E R 2 P R_unbounded ⟨1, by norm_num, 4, fun x hx => W_nbhd x hx⟩
  have hfac3 : ∀ x : E, (∑ j : Fin 3, P j (fun _ => x)) =
      ∑ j, A j (fun _ => L x + a) := hfac
  obtain ⟨Cb, hCb⟩ := W_half_bounded F L a d A hfac3 M hM
  obtain ⟨y, hyR, hylt⟩ := W_half_unbounded Cb
  have hle := hCb y hyR
  linarith

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook55Wanted
