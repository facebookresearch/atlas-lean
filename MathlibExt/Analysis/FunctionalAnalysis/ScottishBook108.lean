/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Krein's theorem on bases in dense sets

Every dense subset of a real Banach space with a Schauder basis contains a Schauder basis.
We move the original basis into the set by a norm-convergent sequence of rank-one corrections.
-/

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook108Wanted

/-- **Schauder basis.** A sequence $(e_n)_{n \ge 0}$ in a real normed space $E$ is a Schauder
basis when for every $x \in E$ there is exactly one sequence of real numbers $(a_n)_{n \ge 0}$
such that the partial sums $\sum_{i < N} a_i e_i$ converge to $x$ as $N \to \infty$. -/
def IsSchauderBasis {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : ℕ → E) : Prop :=
  ∀ x : E, ∃! a : ℕ → ℝ,
    Filter.Tendsto (fun N => ∑ i ∈ Finset.range N, a i • e i)
      Filter.atTop (nhds x)

section

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {e : ℕ → E}

private theorem basis_linearIndependent (he : IsSchauderBasis e) : LinearIndependent ℝ e := by
  apply linearIndependent_iff''.2
  intro s a ha hsum i
  have h : HasSum (fun j => a j • e j) 0 := hsum ▸
    hasSum_sum_of_ne_finset_zero (fun j hj => by simp [ha j hj])
  have hz : Tendsto (fun N => ∑ j ∈ Finset.range N, (0 : ℝ) • e j) atTop (𝓝 0) := by simp
  exact congrFun ((he 0).unique h.tendsto_sum_nat hz) i

private theorem basis_map (he : IsSchauderBasis e) (u : E ≃L[ℝ] E) :
    IsSchauderBasis (fun i => u (e i)) := by
  intro x
  obtain ⟨a, ha, uniq⟩ := he (u.symm x)
  refine ⟨a, ?_, fun b hb => uniq b ?_⟩
  · simpa [Function.comp_def, map_sum] using (u.continuous.tendsto _).comp ha
  · simpa [Function.comp_def, map_sum] using (u.symm.continuous.tendsto _).comp hb

-- A functional on the quotient by the first n vectors separates the next vector from them.
private theorem separating_functional (he : LinearIndependent ℝ e) (n : ℕ) :
    ∃ f : E →L[ℝ] ℝ, f (e n) = 1 ∧ ∀ i < n, f (e i) = 0 := by
  let S := Submodule.span ℝ (e '' (Finset.range n : Set ℕ))
  have : FiniteDimensional ℝ S :=
    FiniteDimensional.span_of_finite ℝ ((Finset.finite_toSet _).image e)
  have : IsClosed (S : Set E) := S.isClosed_of_finiteDimensional
  have hn : e n ∉ S := he.notMem_span_image (by simp)
  have hq : S.mkQL (e n) ≠ 0 := by
    simpa [Submodule.mkQL_apply, Submodule.mkQ_apply] using hn
  obtain ⟨f, hf⟩ := SeparatingDual.exists_eq_one (R := ℝ) hq
  refine ⟨f.comp S.mkQL, hf, fun i hi => ?_⟩
  have hiS : e i ∈ S := Submodule.subset_span ⟨i, Finset.mem_range.mpr hi, rfl⟩
  simp [Submodule.mkQL_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero S).mpr hiS]

-- Change the value at e n while fixing all earlier values, with any prescribed error budget.
private theorem perturb_step (he : LinearIndependent ℝ e) {H : Set E} (hH : Dense H)
    (n : ℕ) (T : E →L[ℝ] E) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : E →L[ℝ] E, dist T U ≤ ε ∧ U (e n) ∈ H ∧ ∀ i < n, U (e i) = T (e i) := by
  obtain ⟨f, hf, hzero⟩ := separating_functional he n
  have hpos : 0 < ‖f‖ + 1 := by positivity
  obtain ⟨y, hy, hd⟩ := hH.exists_dist_lt (T (e n)) (div_pos hε hpos)
  let v := y - T (e n)
  have hv : ‖v‖ * (‖f‖ + 1) < ε := by
    rwa [dist_comm, dist_eq_norm, lt_div_iff₀ hpos] at hd
  refine ⟨T + f.smulRight v, ?_, ?_, fun i hi => ?_⟩
  · rw [dist_self_add_right, f.norm_smulRight_apply, mul_comm]
    exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (norm_nonneg v)).trans
      hv.le
  · simpa [ContinuousLinearMap.smulRight_apply, hf, v] using hy
  · simp [ContinuousLinearMap.smulRight_apply, hzero i hi]

private theorem exists_basis_in_dense_set [CompleteSpace E] (he : IsSchauderBasis e)
    (H : Set E) (hH : Dense H) : ∃ b : ℕ → E, IsSchauderBasis b ∧ ∀ n, b n ∈ H := by
  -- The sum of the step bounds is 1/2, so the limit stays within distance 1 of the identity.
  let ε (n : ℕ) : ℝ := (1 / 2) / 2 / 2 ^ n
  choose step hdist hmem hfix using fun n T =>
    perturb_step (basis_linearIndependent he) hH n T (ε := ε n) (by dsimp [ε]; positivity)
  let T : ℕ → (E →L[ℝ] E) := Nat.rec 1 step
  have hstep (n : ℕ) : dist (T n) (T (n + 1)) ≤ ε n := hdist n (T n)
  obtain ⟨U, hU⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric_two hstep)
  have hnear : dist (1 : E →L[ℝ] E) U ≤ 1 / 2 :=
    dist_le_of_le_geometric_two_of_tendsto₀ hstep hU
  have hunit : IsUnit U := by
    rw [dist_eq_norm] at hnear
    have hsmall : ‖1 - U‖ < 1 := hnear.trans_lt (by norm_num)
    simpa using isUnit_one_sub_of_norm_lt_one hsmall
  obtain ⟨u, rfl⟩ := hunit
  refine ⟨fun n => (u : E →L[ℝ] E) (e n), basis_map he (ContinuousLinearEquiv.ofUnit u), ?_⟩
  intro n
  -- At each basis vector the sequence is eventually constant, even if H is not closed.
  have hstable (m : ℕ) (hm : n + 1 ≤ m) : T m (e n) = T (n + 1) (e n) := by
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih => exact (hfix m (T m) n hm).trans ih
  have hlim : Tendsto (fun m => T m (e n)) atTop (𝓝 ((u : E →L[ℝ] E) (e n))) :=
    ((ContinuousLinearMap.apply ℝ E (e n)).continuous.tendsto _).comp hU
  have hconst : Tendsto (fun m => T m (e n)) atTop (𝓝 (T (n + 1) (e n))) :=
    tendsto_const_nhds.congr' ((eventually_ge_atTop (n + 1)).mono fun m hm => (hstable m hm).symm)
  change (u : E →L[ℝ] E) (e n) ∈ H
  rw [tendsto_nhds_unique hlim hconst]
  exact hmem n (T n)

end

/--
**Krein's theorem on bases in dense sets.** Let $E$ be a real Banach space that has a Schauder
basis. Then for every dense subset $H \subseteq E$ there is a Schauder basis $(e_n)_{n \ge 0}$ of
$E$ with $e_n \in H$ for all $n$, and likewise for every dense linear subspace $S \subseteq E$
there is a Schauder basis $(e_n)_{n \ge 0}$ of $E$ with $e_n \in S$ for all $n$.

Source: S. Banach,
S. Mazur, S. Ulam, Problem 108 of the Scottish Book; affirmative answer
(Krein), typescript addendum Ad 108.
-/
theorem krein_basis_in_dense_set :
    ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
      (∃ e : ℕ → E, IsSchauderBasis e) →
      (∀ H : Set E, Dense H →
        ∃ e : ℕ → E, IsSchauderBasis e ∧ ∀ n, e n ∈ H) ∧
      (∀ S : Submodule ℝ E, Dense (S : Set E) →
        ∃ e : ℕ → E, IsSchauderBasis e ∧ ∀ n, e n ∈ S) := by
  rintro E _ _ _ ⟨e, he⟩
  exact ⟨exists_basis_in_dense_set he, fun S => exists_basis_in_dense_set he (S : Set E)⟩

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook108Wanted
