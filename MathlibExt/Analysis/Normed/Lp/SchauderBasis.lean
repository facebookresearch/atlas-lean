/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.Bases
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-!
# The unit vectors form a Schauder basis of `ℓ^p`

For `1 ≤ p < ∞`, the unit vectors `e i = lp.single p i 1` form a Schauder basis
of `ℓ^p (ι, 𝕜)`, with coordinate functionals given by evaluation at `i`. In
fact they form an *unconditional* Schauder basis: every `x ∈ ℓ^p` is the sum of
`x i • e i` over finite subsets of `ι`, directed by inclusion. When `ι = ℕ`
this gives the classical sequential Schauder basis, whose `n`-th partial-sum
projection is truncation to the first `n` coordinates. The projections are
contractive: their operator norms are at most `1`.

This construction complements the `L^p`-norm material in the archived `v1`
Functional Analysis book (April 6, 2021): the book defines `L^p` spaces and
proves Hölder's and Minkowski's inequalities, but does not state this basis
construction. The proof instantiates Mathlib's abstract `SchauderBasis` and
`UnconditionalSchauderBasis` structures using `lp.hasSum_single`.

## Main declarations

* `lpUnconditionalSchauderBasis` : the unit vectors as an
  `UnconditionalSchauderBasis ι 𝕜 (lp (fun _ : ι => 𝕜) p)`.
* `lpSchauderBasis` : the unit vectors as a classical
  `SchauderBasis 𝕜 (lp (fun _ : ℕ => 𝕜) p)`.
* `norm_lpSchauderBasis_proj_apply_le` : the basis projections are contractive.
* `norm_lpSchauderBasis_proj_le` : every basis projection has operator norm `≤ 1`.
-/

@[expose] public section

namespace MathlibExt.Analysis.Normed.Lp.SchauderBasis

open scoped ENNReal

variable {ι : Type*} {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The unit vectors of `ℓ^p (ι, 𝕜)` form an unconditional Schauder basis, with
coordinate functionals given by evaluation at each index. -/
noncomputable def lpUnconditionalSchauderBasis [DecidableEq ι] (hp : p ≠ ⊤) :
    UnconditionalSchauderBasis ι 𝕜 (lp (fun _ : ι => 𝕜) p) where
  basis i := lp.single p i 1
  coord i := lp.evalCLM 𝕜 (fun _ : ι => 𝕜) p i
  ortho i j := by
    have h1 : (lp.evalCLM 𝕜 (fun _ : ι => 𝕜) p i)
        (lp.single (E := fun _ : ι => 𝕜) p j (1 : 𝕜))
        = (lp.single (E := fun _ : ι => 𝕜) p j (1 : 𝕜)) i := rfl
    rw [h1]
    by_cases hij : i = j
    · subst hij
      simp [Pi.single_eq_same]
    · simp [hij, Pi.single_eq_of_ne]
  expansion x := by
    have h : HasSum (fun i : ι => lp.single (E := fun _ : ι => 𝕜) p i (x i)) x :=
      lp.hasSum_single hp x
    have hfun : (fun i : ι => (lp.evalCLM 𝕜 (fun _ : ι => 𝕜) p i) x • lp.single p i (1 : 𝕜))
        = fun i : ι => lp.single (E := fun _ : ι => 𝕜) p i (x i) := by
      funext i
      show (x i) • lp.single (E := fun _ : ι => 𝕜) p i (1 : 𝕜)
        = lp.single (E := fun _ : ι => 𝕜) p i (x i)
      rw [← lp.single_smul, smul_eq_mul, mul_one]
    rw [hfun]
    exact h

/-- The unit vectors of `ℓ^p (ℕ, 𝕜)` form a classical sequential Schauder basis. -/
noncomputable def lpSchauderBasis (hp : p ≠ ⊤) :
    SchauderBasis 𝕜 (lp (fun _ : ℕ => 𝕜) p) where
  basis i := lp.single p i 1
  coord i := lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) p i
  ortho i j := by
    have h1 : (lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) p i)
        (lp.single (E := fun _ : ℕ => 𝕜) p j (1 : 𝕜))
        = (lp.single (E := fun _ : ℕ => 𝕜) p j (1 : 𝕜)) i := rfl
    rw [h1]
    by_cases hij : i = j
    · subst hij
      simp [Pi.single_eq_same]
    · simp [hij, Pi.single_eq_of_ne]
  expansion x := by
    have h : HasSum (fun i : ℕ => lp.single (E := fun _ : ℕ => 𝕜) p i (x i)) x :=
      lp.hasSum_single hp x
    have hfun : (fun i : ℕ => (lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) p i) x • lp.single p i (1 : 𝕜))
        = fun i : ℕ => lp.single (E := fun _ : ℕ => 𝕜) p i (x i) := by
      funext i
      show (x i) • lp.single (E := fun _ : ℕ => 𝕜) p i (1 : 𝕜)
        = lp.single (E := fun _ : ℕ => 𝕜) p i (x i)
      rw [← lp.single_smul, smul_eq_mul, mul_one]
    rw [hfun]
    exact h.mono_left SummationFilter.LeAtTop.le_atTop

/-- The coordinate functional of the `ℓ^p` Schauder basis is evaluation. -/
@[simp]
theorem lpUnconditionalSchauderBasis_coord_apply [DecidableEq ι] (hp : p ≠ ⊤)
    (i : ι) (x : lp (fun _ : ι => 𝕜) p) :
    (lpUnconditionalSchauderBasis (ι := ι) (𝕜 := 𝕜) (p := p) hp).coord i x = x i := by
  show (lp.evalCLM 𝕜 (fun _ : ι => 𝕜) p i) x = x i
  rfl

/-- The `i`-th basis vector of the `ℓ^p` Schauder basis is the unit vector. -/
@[simp]
theorem lpUnconditionalSchauderBasis_apply [DecidableEq ι] (hp : p ≠ ⊤) (i : ι) :
    (lpUnconditionalSchauderBasis (ι := ι) (𝕜 := 𝕜) (p := p) hp) i
      = lp.single (E := fun _ : ι => 𝕜) p i (1 : 𝕜) := by
  simp [lpUnconditionalSchauderBasis]

/-- The `ℓ^p` basis projection onto a finite set of coordinates is the corresponding
finite partial sum. -/
theorem lpUnconditionalSchauderBasis_proj_apply [DecidableEq ι] (hp : p ≠ ⊤)
    (A : Finset ι) (x : lp (fun _ : ι => 𝕜) p) :
    (lpUnconditionalSchauderBasis (ι := ι) (𝕜 := 𝕜) (p := p) hp).proj A x
      = ∑ i ∈ A, lp.single (E := fun _ : ι => 𝕜) p i (x i) := by
  rw [GeneralSchauderBasis.proj_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lpUnconditionalSchauderBasis_coord_apply, lpUnconditionalSchauderBasis_apply,
    ← lp.single_smul, smul_eq_mul, mul_one]

/-- The basis projections of the `ℓ^p` Schauder basis are contractive on vectors. -/
theorem norm_lpSchauderBasis_proj_apply_le [DecidableEq ι] (hp : p ≠ ⊤)
    (A : Finset ι) (x : lp (fun _ : ι => 𝕜) p) :
    ‖(lpUnconditionalSchauderBasis (ι := ι) (𝕜 := 𝕜) (p := p) hp).proj A x‖ ≤ ‖x‖ := by
  have hp0 : (0 : ℝ) < p.toReal := by
    have h1 : (0 : ℝ≥0∞) < p := zero_lt_one.trans_le Fact.out
    exact ENNReal.toReal_pos h1.ne' hp
  rw [lpUnconditionalSchauderBasis_proj_apply]
  have hnorm : ‖∑ i ∈ A, lp.single p i (x i)‖ ^ p.toReal
      = ∑ i ∈ A, ‖x i‖ ^ p.toReal :=
    lp.norm_sum_single hp0 _ _
  have hsum : ∑ i ∈ A, ‖x i‖ ^ p.toReal ≤ ‖x‖ ^ p.toReal := by
    have hsumm : Summable (fun i => ‖x i‖ ^ p.toReal) :=
      (lp.hasSum_norm hp0 x).summable
    have htsum : ∑' i, ‖x i‖ ^ p.toReal = ‖x‖ ^ p.toReal :=
      (lp.hasSum_norm hp0 x).tsum_eq
    rw [← htsum]
    exact hsumm.sum_le_tsum A (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hle : ‖∑ i ∈ A, lp.single p i (x i)‖ ^ p.toReal ≤ ‖x‖ ^ p.toReal := by
    rw [hnorm]; exact hsum
  exact (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hp0).mp hle

/-- Every basis projection of the `ℓ^p` Schauder basis has operator norm at most `1`:
the operator-norm bound is `1`, including an empty index type. -/
theorem norm_lpSchauderBasis_proj_le [DecidableEq ι] (hp : p ≠ ⊤) (A : Finset ι) :
    ‖(lpUnconditionalSchauderBasis (ι := ι) (𝕜 := 𝕜) (p := p) hp).proj A‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul]
  exact norm_lpSchauderBasis_proj_apply_le hp A x

/-- The coordinate functional of the classical `ℓ^p` Schauder basis is evaluation. -/
@[simp]
theorem lpSchauderBasis_coord_apply (hp : p ≠ ⊤)
    (i : ℕ) (x : lp (fun _ : ℕ => 𝕜) p) :
    (lpSchauderBasis (𝕜 := 𝕜) (p := p) hp).coord i x = x i := by
  show (lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) p i) x = x i
  rfl

/-- The `i`-th basis vector of the classical `ℓ^p` Schauder basis is the unit vector. -/
@[simp]
theorem lpSchauderBasis_apply (hp : p ≠ ⊤) (i : ℕ) :
    (lpSchauderBasis (𝕜 := 𝕜) (p := p) hp) i
      = lp.single (E := fun _ : ℕ => 𝕜) p i (1 : 𝕜) := by
  simp [lpSchauderBasis]

/-- The `n`-th partial-sum projection of the classical `ℓ^p` Schauder basis is
truncation to the first `n` coordinates. -/
theorem lpSchauderBasis_proj_apply (hp : p ≠ ⊤)
    (n : ℕ) (x : lp (fun _ : ℕ => 𝕜) p) :
    (lpSchauderBasis (𝕜 := 𝕜) (p := p) hp).proj n x
      = ∑ i ∈ Finset.range n, lp.single (E := fun _ : ℕ => 𝕜) p i (x i) := by
  rw [SchauderBasis.proj_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lpSchauderBasis_coord_apply, lpSchauderBasis_apply,
    ← lp.single_smul, smul_eq_mul, mul_one]

/-- The classical partial-sum projections are contractive on vectors. -/
theorem norm_lpSchauderBasis_classical_proj_apply_le (hp : p ≠ ⊤)
    (n : ℕ) (x : lp (fun _ : ℕ => 𝕜) p) :
    ‖(lpSchauderBasis (𝕜 := 𝕜) (p := p) hp).proj n x‖ ≤ ‖x‖ := by
  have h := norm_lpSchauderBasis_proj_apply_le (ι := ℕ) (𝕜 := 𝕜) (p := p) hp
    (Finset.range n) x
  have heq : (lpUnconditionalSchauderBasis (ι := ℕ) (𝕜 := 𝕜) (p := p) hp).proj
      (Finset.range n) x
      = (lpSchauderBasis (𝕜 := 𝕜) (p := p) hp).proj n x := rfl
  rw [← heq]
  exact h

/-- The classical partial-sum projections have operator norm at most `1`. -/
theorem norm_lpSchauderBasis_classical_proj_le (hp : p ≠ ⊤) (n : ℕ) :
    ‖(lpSchauderBasis (𝕜 := 𝕜) (p := p) hp).proj n‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul]
  exact norm_lpSchauderBasis_classical_proj_apply_le hp n x

end MathlibExt.Analysis.Normed.Lp.SchauderBasis
