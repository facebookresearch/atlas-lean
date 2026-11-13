/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.KarushKuhnTucker
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Convex.Mul

/-!
# Tests for the inequality-only KKT conditions

Focused API examples for
`MathlibExt.Analysis.Convex.KarushKuhnTucker.karush_kuhn_tucker_inequality`:
projections onto multiplier nonnegativity, complementarity, and stationarity,
plus a one-dimensional specialization over `ℝ`.

For `isMinOn_of_karush_kuhn_tucker_convex` and `ConvexOn.add_fderiv_sub_le`: a corner solution
(minimize `y` subject to `-y ≤ 0` with multiplier `1`), an unconstrained interior minimum of
`(y - 3) ^ 2`, and the tangent-line inequality for `y ^ 2` at `1` and `4`.
-/

@[expose]
public section

open MathlibExt.Analysis.Convex.KarushKuhnTucker

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {m : ℕ} {f : E → ℝ} {g : Fin m → E → ℝ} {x : E}

/-- The KKT multipliers are nonnegative. -/
example
    (hf_diff : DifferentiableAt ℝ f x)
    (hg_diff : ∀ i, DifferentiableAt ℝ (g i) x)
    (hfeas : ∀ i, g i x ≤ 0)
    (hmin : IsLocalMinOn f {y | ∀ i, g i y ≤ 0} x)
    (hLICQ : LinearIndependent ℝ
      (fun i : {i : Fin m // g i x = 0} => fderiv ℝ (g i.val) x)) :
    ∃ lam : Fin m → ℝ, ∀ i, 0 ≤ lam i := by
  obtain ⟨lam, hnn, -, -⟩ :=
    karush_kuhn_tucker_inequality hf_diff hg_diff hfeas hmin hLICQ
  exact ⟨lam, hnn⟩

/-- The KKT multipliers satisfy complementarity. -/
example
    (hf_diff : DifferentiableAt ℝ f x)
    (hg_diff : ∀ i, DifferentiableAt ℝ (g i) x)
    (hfeas : ∀ i, g i x ≤ 0)
    (hmin : IsLocalMinOn f {y | ∀ i, g i y ≤ 0} x)
    (hLICQ : LinearIndependent ℝ
      (fun i : {i : Fin m // g i x = 0} => fderiv ℝ (g i.val) x)) :
    ∃ lam : Fin m → ℝ, ∀ i, lam i * g i x = 0 := by
  obtain ⟨lam, -, hcomp, -⟩ :=
    karush_kuhn_tucker_inequality hf_diff hg_diff hfeas hmin hLICQ
  exact ⟨lam, hcomp⟩

/-- The KKT stationarity equation holds. -/
example
    (hf_diff : DifferentiableAt ℝ f x)
    (hg_diff : ∀ i, DifferentiableAt ℝ (g i) x)
    (hfeas : ∀ i, g i x ≤ 0)
    (hmin : IsLocalMinOn f {y | ∀ i, g i y ≤ 0} x)
    (hLICQ : LinearIndependent ℝ
      (fun i : {i : Fin m // g i x = 0} => fderiv ℝ (g i.val) x)) :
    ∃ lam : Fin m → ℝ,
      fderiv ℝ f x + ∑ i : Fin m, lam i • fderiv ℝ (g i) x = 0 := by
  obtain ⟨lam, -, -, hstat⟩ :=
    karush_kuhn_tucker_inequality hf_diff hg_diff hfeas hmin hLICQ
  exact ⟨lam, hstat⟩

/-- Multipliers vanish on inactive constraints. -/
example
    (hf_diff : DifferentiableAt ℝ f x)
    (hg_diff : ∀ i, DifferentiableAt ℝ (g i) x)
    (hfeas : ∀ i, g i x ≤ 0)
    (hmin : IsLocalMinOn f {y | ∀ i, g i y ≤ 0} x)
    (hLICQ : LinearIndependent ℝ
      (fun i : {i : Fin m // g i x = 0} => fderiv ℝ (g i.val) x))
    (j : Fin m) (hj : g j x < 0) :
    ∃ lam : Fin m → ℝ, lam j = 0 := by
  obtain ⟨lam, -, hcomp, -⟩ :=
    karush_kuhn_tucker_inequality hf_diff hg_diff hfeas hmin hLICQ
  refine ⟨lam, ?_⟩
  have hj0 := hcomp j
  have hne : g j x ≠ 0 := ne_of_lt hj
  exact (mul_eq_zero.mp hj0).resolve_right hne

/-- One-dimensional specialization over `ℝ`. -/
example
    {φ : ℝ → ℝ} {ψ : Fin m → ℝ → ℝ} {a : ℝ}
    (hφ : DifferentiableAt ℝ φ a)
    (hψ : ∀ i, DifferentiableAt ℝ (ψ i) a)
    (hfeas : ∀ i, ψ i a ≤ 0)
    (hmin : IsLocalMinOn φ {y | ∀ i, ψ i y ≤ 0} a)
    (hLICQ : LinearIndependent ℝ
      (fun i : {i : Fin m // ψ i a = 0} => fderiv ℝ (ψ i.val) a)) :
    ∃ lam : Fin m → ℝ, (∀ i, 0 ≤ lam i) ∧ (∀ i, lam i * ψ i a = 0) ∧
      fderiv ℝ φ a + ∑ i : Fin m, lam i • fderiv ℝ (ψ i) a = 0 :=
  karush_kuhn_tucker_inequality hφ hψ hfeas hmin hLICQ

/-- Test 1 (corner solution on ℝ): minimize `f y = y` subject to `g 0 y = -y ≤ 0`. -/
example : IsMinOn (fun y : ℝ => y)
    {y : ℝ | ∀ i : Fin 1, (fun _ : Fin 1 => fun z : ℝ => -z) i y ≤ 0} (0 : ℝ) := by
  have h1 : ConvexOn ℝ (Set.univ : Set ℝ) (fun y : ℝ => y) := by
    constructor
    · exact convex_univ
    · intro x _ y _ a b _ _ _
      exact le_rfl
  have h2 : ∀ _ : Fin 1, ConvexOn ℝ (Set.univ : Set ℝ) (fun z : ℝ => -z) := by
    intro _
    constructor
    · exact convex_univ
    · intro x _ y _ a b _ _ _
      simp only [smul_eq_mul]
      have heq : -((a * x + b * y : ℝ)) = a * -x + b * -y := by ring
      exact heq.le
  have h3 : DifferentiableAt ℝ (fun y : ℝ => y) (0 : ℝ) := differentiableAt_id
  have h4 : ∀ _ : Fin 1, DifferentiableAt ℝ (fun z : ℝ => -z) (0 : ℝ) :=
    fun _ => differentiableAt_id.neg
  have h5 : ∀ _ : Fin 1, (0 : ℝ) ≤ (1 : ℝ) := fun _ => zero_le_one
  have h6 : ∀ _ : Fin 1, (1 : ℝ) * (-(0 : ℝ)) = 0 := fun _ => by norm_num
  have hfid : fderiv ℝ (fun y : ℝ => y) (0 : ℝ) = ContinuousLinearMap.id ℝ ℝ := fderiv_id
  have hneg : fderiv ℝ (fun z : ℝ => -z) (0 : ℝ) = -ContinuousLinearMap.id ℝ ℝ :=
    ((hasFDerivAt_id (0 : ℝ)).neg).fderiv
  have h7 : fderiv ℝ (fun y : ℝ => y) (0 : ℝ)
      + ∑ i : Fin 1, (fun _ : Fin 1 => (1 : ℝ)) i
        • fderiv ℝ ((fun _ : Fin 1 => fun z : ℝ => -z) i) (0 : ℝ) = 0 := by
    simp only [Fin.sum_univ_one, hfid, hneg, one_smul, add_neg_cancel]
  exact MathlibExt.Analysis.Convex.KarushKuhnTucker.isMinOn_of_karush_kuhn_tucker_convex
    (E := ℝ) (m := 1) (f := fun y : ℝ => y) (g := fun _ : Fin 1 => fun z : ℝ => -z)
    (x := (0 : ℝ)) (lam := fun _ : Fin 1 => (1 : ℝ)) h1 h2 h3 h4 h5 h6 h7

/-- Test 2 (interior, no constraints): minimize `f y = (y - 3)^2` on ℝ. -/
example : IsMinOn (fun y : ℝ => (y - 3) ^ 2)
    {y : ℝ | ∀ i : Fin 0, (Fin.elim0 : Fin 0 → ℝ → ℝ) i y ≤ 0} (3 : ℝ) := by
  have hsq : ConvexOn ℝ (Set.univ : Set ℝ) (fun y : ℝ => y ^ 2) := even_two.convexOn_pow
  have hlin : ConvexOn ℝ (Set.univ : Set ℝ) (fun y : ℝ => -6 * y + 9) := by
    constructor
    · exact convex_univ
    · intro x _ y _ a b _ _ hab
      simp only [smul_eq_mul]
      linear_combination (-9) * hab
  have hcomp : (fun y : ℝ => (y - 3) ^ 2)
      = (fun y : ℝ => y ^ 2) + (fun y : ℝ => -6 * y + 9) := by
    ext y
    simp only [Pi.add_apply]
    ring
  have hf_conv2 : ConvexOn ℝ (Set.univ : Set ℝ) (fun y : ℝ => (y - 3) ^ 2) := by
    rw [hcomp]
    exact hsq.add hlin
  have hu : HasFDerivAt (fun y : ℝ => y - 3) (ContinuousLinearMap.id ℝ ℝ) (3 : ℝ) :=
    HasFDerivAt.sub_const (3 : ℝ) (hasFDerivAt_id (3 : ℝ))
  have hmul := hu.mul hu
  have hdiff2 : DifferentiableAt ℝ (fun y : ℝ => (y - 3) ^ 2) (3 : ℝ) := by
    have h2 : (fun y : ℝ => (y - 3) ^ 2)
        = (fun y : ℝ => y - 3) * (fun y : ℝ => y - 3) := by
      ext y
      simp [pow_two, Pi.mul_apply]
    rw [h2]
    exact hmul.differentiableAt
  have hfd2 : fderiv ℝ (fun y : ℝ => (y - 3) ^ 2) (3 : ℝ) = 0 := by
    have h2 : (fun y : ℝ => (y - 3) ^ 2)
        = (fun y : ℝ => y - 3) * (fun y : ℝ => y - 3) := by
      ext y
      simp [pow_two, Pi.mul_apply]
    rw [h2]
    have h3 := hmul.fderiv
    simpa using h3
  have hstat2 : fderiv ℝ (fun y : ℝ => (y - 3) ^ 2) (3 : ℝ)
      + ∑ i : Fin 0, (Fin.elim0 : Fin 0 → ℝ) i
        • fderiv ℝ ((Fin.elim0 : Fin 0 → ℝ → ℝ) i) (3 : ℝ) = 0 := by
    simp [hfd2]
  exact MathlibExt.Analysis.Convex.KarushKuhnTucker.isMinOn_of_karush_kuhn_tucker_convex
    (E := ℝ) (m := 0) (f := fun y : ℝ => (y - 3) ^ 2)
    (g := Fin.elim0) (x := (3 : ℝ)) (lam := Fin.elim0)
    hf_conv2 (fun i => Fin.elim0 i) hdiff2 (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) hstat2

/-- Test 3: first-order convexity inequality for `f y = y^2` at `x = 1`, `y = 4`. -/
example : (1 : ℝ) + 2 * 3 ≤ 16 := by
  have hsq : ConvexOn ℝ (Set.univ : Set ℝ) (fun y : ℝ => y ^ 2) := even_two.convexOn_pow
  have hid : HasFDerivAt (fun y : ℝ => y) (ContinuousLinearMap.id ℝ ℝ) (1 : ℝ) :=
    hasFDerivAt_id (1 : ℝ)
  have h2 : (fun y : ℝ => y ^ 2) = (fun y : ℝ => y) * (fun y : ℝ => y) := by
    ext y
    simp [pow_two, Pi.mul_apply]
  have hclm : (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ
      = ((fun y : ℝ => y) (1 : ℝ)) • ContinuousLinearMap.id ℝ ℝ
        + ((fun y : ℝ => y) (1 : ℝ)) • ContinuousLinearMap.id ℝ ℝ := by
    rw [← add_smul]
    norm_num
  have hF : HasFDerivAt (fun y : ℝ => y ^ 2)
      ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) (1 : ℝ) := by
    rw [h2, hclm]
    exact hid.mul hid
  have hdiff : DifferentiableAt ℝ (fun y : ℝ => y ^ 2) (1 : ℝ) := hF.differentiableAt
  have hfd : fderiv ℝ (fun y : ℝ => y ^ 2) (1 : ℝ) (3 : ℝ) = 2 * 3 := by
    rw [hF.fderiv]
    simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.id_apply]
  have h := ConvexOn.add_fderiv_sub_le (s := Set.univ) (f := fun y : ℝ => y ^ 2)
    (x := (1 : ℝ)) (y := (4 : ℝ)) hsq (Set.mem_univ _) (Set.mem_univ _) hdiff
  have h4 : ((4 : ℝ) - 1) = 3 := by norm_num
  have h1sq : (1 : ℝ) ^ 2 = 1 := by norm_num
  have h4sq : (4 : ℝ) ^ 2 = 16 := by norm_num
  rw [h4, h1sq, h4sq, hfd] at h
  exact h
