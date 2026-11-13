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
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

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


open scoped Topology

/-! ### Tests for the mixed-constraint KKT conditions -/

-- Test 1: concrete instance on `ℝ` with an inactive inequality.
-- `f y = y^2`, `h 0 y = y - 1`, `g 0 y = -y`, `x = 1`.
example : ∃ (lam : Fin 1 → ℝ) (mu : Fin 1 → ℝ),
    (∀ i, 0 ≤ lam i)
    ∧ (∀ i, lam i * ((fun _ y : ℝ => -y) i) 1 = 0)
    ∧ (fderiv ℝ (fun y : ℝ => y ^ 2) 1
      + ∑ i : Fin 1, lam i • fderiv ℝ ((fun _ y : ℝ => -y) i) 1
      + ∑ j : Fin 1, mu j • fderiv ℝ ((fun _ y : ℝ => y - 1) j) 1 = 0)
    ∧ lam 0 = 0 ∧ mu 0 = -2 := by
  have hf_diff : DifferentiableAt ℝ (fun y : ℝ => y ^ 2) 1 := by fun_prop
  have hg_diff : ∀ i : Fin 1, DifferentiableAt ℝ ((fun _ y : ℝ => -y) i) 1 := by
    intro i
    fun_prop
  have hh_diff : ∀ j : Fin 1, ContDiffAt ℝ 1 ((fun _ y : ℝ => y - 1) j) 1 := by
    intro j
    exact contDiffAt_id.sub contDiffAt_const
  have hfeas : ∀ i : Fin 1, (fun _ y : ℝ => -y) i 1 ≤ 0 := by
    intro i
    change (-1 : ℝ) ≤ 0
    norm_num
  have heq : ∀ j : Fin 1, (fun _ y : ℝ => y - 1) j 1 = 0 := by
    intro j
    change (1 : ℝ) - 1 = 0
    norm_num
  have hmin : IsLocalMinOn (fun y : ℝ => y ^ 2)
      {y | (∀ i : Fin 1, (fun _ y : ℝ => -y) i y ≤ 0)
        ∧ ∀ j : Fin 1, (fun _ y : ℝ => y - 1) j y = 0} 1 := by
    change ∀ᶠ y : ℝ in 𝓝[{y | (∀ i : Fin 1, (fun _ y : ℝ => -y) i y ≤ 0)
        ∧ ∀ j : Fin 1, (fun _ y : ℝ => y - 1) j y = 0}] 1,
      (fun y : ℝ => y ^ 2) 1 ≤ (fun y : ℝ => y ^ 2) y
    filter_upwards [self_mem_nhdsWithin] with y hy
    obtain ⟨hg, hh⟩ := hy
    have h0 := hh 0
    have hy1 : y = 1 := by linarith
    rw [hy1]
  have hLICQ : LinearIndependent ℝ (Sum.elim
      (fun j : Fin 1 => fderiv ℝ ((fun _ y : ℝ => y - 1) j) 1)
      (fun i : {i : Fin 1 // (fun _ y : ℝ => -y) i 1 = 0} =>
        fderiv ℝ ((fun _ y : ℝ => -y) i.val) 1)) := by
    -- The active set is empty.
    have hempty : ∀ a : {i : Fin 1 // (fun _ y : ℝ => -y) i 1 = 0}, False := by
      intro a
      have hprop : (fun _ y : ℝ => -y) a.val (1 : ℝ) = 0 := a.property
      norm_num at hprop
    -- The single equality derivative is `id`, hence nonzero.
    have hderiv : HasFDerivAt (fun y : ℝ => y - 1) (ContinuousLinearMap.id ℝ ℝ) (1 : ℝ) :=
      HasFDerivAt.sub_const 1 (hasFDerivAt_id 1)
    have hfderiv_id : fderiv ℝ ((fun _ y : ℝ => y - 1) 0) 1
        = ContinuousLinearMap.id ℝ ℝ := hderiv.fderiv
    have hne : fderiv ℝ ((fun _ y : ℝ => y - 1) 0) 1 ≠ 0 := by
      rw [hfderiv_id]
      intro hcon
      have hcon1 := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hcon
      simp at hcon1
    -- Independence by direct sum analysis.
    rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [Fintype.sum_sum_type] at hc
    have hA0 : (∑ a : {i : Fin 1 // (fun _ y : ℝ => -y) i 1 = 0},
        c (Sum.inr a) • fderiv ℝ ((fun _ y : ℝ => -y) a.val) 1) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      exact (hempty a).elim
    simp only [Sum.elim_inr] at hc
    rw [hA0, add_zero] at hc
    -- `hc` is now a singleton sum over `Fin 1`.
    rw [Fin.sum_univ_one] at hc
    -- From `c (inl 0) • id = 0`, get `c (inl 0) = 0`.
    have hfd0 : (Sum.elim (fun j : Fin 1 => fderiv ℝ ((fun _ y : ℝ => y - 1) j) 1)
        (fun i : {i : Fin 1 // (fun _ y : ℝ => -y) i 1 = 0} =>
          fderiv ℝ ((fun _ y : ℝ => -y) i.val) 1)) (Sum.inl 0)
        = ContinuousLinearMap.id ℝ ℝ := by
      simp only [Sum.elim_inl]
      exact hfderiv_id
    rw [hfd0] at hc
    have hc0 : c (Sum.inl 0) = 0 := by
      have hc1 := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hc
      simp at hc1
      linarith [hc1]
    intro s
    cases s with
    | inl j =>
      have hj0 : j = 0 := by fin_cases j; rfl
      subst hj0
      simp [hc0]
    | inr a => exact (hempty a).elim
  obtain ⟨lam, mu, hlam, hcompl, hstat⟩ := karush_kuhn_tucker_mixed
    hf_diff hg_diff hh_diff hfeas heq hmin hLICQ
  have hlam0 : lam 0 = 0 := by
    have hc := hcompl 0
    simp only [] at hc
    -- `hc : lam 0 * -1 = 0`
    linarith
  have hmu0 : mu 0 = -2 := by
    have hstat1 := congrArg (fun L : ℝ →L[ℝ] ℝ => L (1 : ℝ)) hstat
    simp only [add_apply, sum_apply, smul_apply, smul_eq_mul,
      ContinuousLinearMap.zero_apply, Fin.sum_univ_one] at hstat1
    have hf1 : (fderiv ℝ (fun y : ℝ => y ^ 2) 1) 1 = 2 := by
      have hfun : (fun y : ℝ => y ^ 2) = (fun y => y * y) := by
        funext y
        exact pow_two y
      rw [hfun]
      have hmul := (hasFDerivAt_id (𝕜 := ℝ) (1 : ℝ)).mul (hasFDerivAt_id (𝕜 := ℝ) (1 : ℝ))
      have hfd : fderiv ℝ (fun y : ℝ => y * y) 1
          = (1 : ℝ) • ContinuousLinearMap.id ℝ ℝ + (1 : ℝ) • ContinuousLinearMap.id ℝ ℝ :=
        hmul.fderiv
      rw [hfd]
      simp [add_apply]
      norm_num
    have hg1 : (fderiv ℝ ((fun _ y : ℝ => -y) 0) 1) 1 = -1 := by
      have hneg : HasFDerivAt (fun y : ℝ => -y) (-ContinuousLinearMap.id ℝ ℝ) (1 : ℝ) :=
        (hasFDerivAt_id (1 : ℝ)).neg
      have hfd : fderiv ℝ ((fun _ y : ℝ => -y) 0) 1 = -ContinuousLinearMap.id ℝ ℝ := hneg.fderiv
      rw [hfd]
      simp
    have hh1 : (fderiv ℝ ((fun _ y : ℝ => y - 1) 0) 1) 1 = 1 := by
      have hsub : HasFDerivAt (fun y : ℝ => y - 1) (ContinuousLinearMap.id ℝ ℝ) (1 : ℝ) :=
        HasFDerivAt.sub_const 1 (hasFDerivAt_id 1)
      have hfd : fderiv ℝ ((fun _ y : ℝ => y - 1) 0) 1 = ContinuousLinearMap.id ℝ ℝ := hsub.fderiv
      rw [hfd]
      simp
    rw [hf1, hg1, hh1, hlam0] at hstat1
    simp at hstat1
    linarith
  exact ⟨lam, mu, hlam, hcompl, hstat, hlam0, hmu0⟩

-- Test 2: without LICQ the KKT conclusion can fail (constraint qualification probe).
-- Minimize `f y = y` subject to `g 0 y = y^2 ≤ 0` (no equalities).
-- `0` is the unique feasible point, hence a local min, but no `lam ≥ 0` gives stationarity.
example : IsLocalMinOn (fun y : ℝ => y)
      {y | (∀ i : Fin 1, (fun _ y : ℝ => y ^ 2) i y ≤ 0)
        ∧ ∀ j : Fin 0, (fun (_ : Fin 0) (_ : ℝ) => (0 : ℝ)) j y = 0} (0 : ℝ)
    ∧ ¬∃ lam : Fin 1 → ℝ, (∀ i, 0 ≤ lam i)
      ∧ (fderiv ℝ (fun y : ℝ => y) 0
        + lam 0 • fderiv ℝ ((fun _ y : ℝ => y ^ 2) 0) 0 = 0) := by
  constructor
  · -- `0` is the only feasible point, hence a (global, so local) minimum.
    change ∀ᶠ y : ℝ in 𝓝[{y | (∀ i : Fin 1, (fun _ y : ℝ => y ^ 2) i y ≤ 0)
        ∧ ∀ j : Fin 0, (fun (_ : Fin 0) (_ : ℝ) => (0 : ℝ)) j y = 0}] 0,
      (fun y : ℝ => y) 0 ≤ (fun y : ℝ => y) y
    filter_upwards [self_mem_nhdsWithin] with y hy
    obtain ⟨hg, -⟩ := hy
    have h0 := hg 0
    have hsq : (0 : ℝ) ≤ y ^ 2 := by positivity
    have heq : y ^ 2 = 0 := le_antisymm h0 hsq
    have hy0 : y = 0 := sq_eq_zero_iff.mp heq
    rw [hy0]
  · -- No multipliers exist: `fderiv` of `y` is `id ≠ 0`, of `y^2` at `0` is `0`.
    rintro ⟨lam, -, hstat⟩
    have hid : fderiv ℝ (fun y : ℝ => y) 0 = ContinuousLinearMap.id ℝ ℝ :=
      (hasFDerivAt_id (0 : ℝ)).fderiv
    have hzero : fderiv ℝ ((fun _ y : ℝ => y ^ 2) 0) 0 = 0 := by
      have hfun : ((fun _ y : ℝ => y ^ 2) 0) = (fun y => y * y) := by
        funext y
        exact pow_two y
      rw [hfun]
      have hmul := (hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).mul (hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ))
      have hfd := hmul.fderiv
      simp at hfd
      exact hfd
    rw [hid, hzero, smul_zero, add_zero] at hstat
    have hcon1 := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hstat
    simp at hcon1
