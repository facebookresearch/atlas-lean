/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.Dynamics.Replicator
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Data.Matrix.Mul
import Domains.Biology.Dynamics.ReplicatorStability
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex

/-!
# An interior ESS attracts every interior orbit

This module defines the simplex, matrix replicator field, forward solutions and evolutionarily
stable states, and proves global attraction of an interior evolutionarily stable state.

## References

* Josef Hofbauer and Karl Sigmund, *Evolutionary game dynamics*, Bull. Amer. Math. Soc. (N.S.)
  40 (2003), no. 4, 479–519, §2.6, Theorem 7; see also §2.2, eq. (3), for the replicator field
  and its simplex and §2.3(d) for the Lyapunov stability criterion using this field.
-/

@[expose] public section

namespace WantedExt.Biology.Ecology.BoundaryESSStabilityWanted

open Matrix Filter Topology

variable {ι : Type*} [Fintype ι]

/-- The simplex of mixed strategies `Δ = {x | ∀ i, 0 ≤ x i, ∑ i, x i = 1}`. -/
def simplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

/-- The **replicator vector field** of the matrix game `A`:
`F(x)_i = x_i ((A x)_i - x · A x)`. -/
def replicatorField (A : Matrix ι ι ℝ) (x : ι → ℝ) : ι → ℝ :=
  fun i => x i * ((A *ᵥ x) i - x ⬝ᵥ A *ᵥ x)

/-- `x` solves the replicator equation `ẋ = F(x)` of `A` for all times `t ≥ 0`. -/
def IsReplicatorSolution (A : Matrix ι ι ℝ) (x : ℝ → ι → ℝ) : Prop :=
  ∀ i t, 0 ≤ t → HasDerivAt (fun s => x s i) (replicatorField A (x t) i) t

/-- `p` is an **evolutionarily stable state** of `A` (Maynard Smith and Price): `p ∈ Δ` and for
every `q ∈ Δ` with `q ≠ p`, either `q · A p < p · A p`, or `q · A p = p · A p` and
`q · A q < p · A q`. -/
def IsESS (A : Matrix ι ι ℝ) (p : ι → ℝ) : Prop :=
  p ∈ simplex ι ∧ ∀ q ∈ simplex ι, q ≠ p →
    q ⬝ᵥ A *ᵥ p < p ⬝ᵥ A *ᵥ p ∨ (q ⬝ᵥ A *ᵥ p = p ⬝ᵥ A *ᵥ p ∧ q ⬝ᵥ A *ᵥ q < p ⬝ᵥ A *ᵥ q)

/-- **Membership in the strategy simplex.** Frequencies are nonnegative and sum to one. -/
public theorem mem_simplex_iff {x : ι → ℝ} :
    x ∈ simplex ι ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 :=
  Iff.rfl

/-- **Coordinates of the matrix replicator field.** The rate of change of each frequency is
its product with the difference between its payoff and the mean payoff. -/
public theorem replicatorField_apply (A : Matrix ι ι ℝ) (x : ι → ℝ) (i : ι) :
    replicatorField A x i = x i * ((A *ᵥ x) i - x ⬝ᵥ A *ᵥ x) :=
  rfl

open MathlibExt.Biology.Dynamics.Replicator (IsSolution relEntropy relEntropy_self relEntropy_pos
  continuous_mulVec_fitness)

/-- **Matrix game solutions as fitness-driven solutions.** The two forward-solution predicates
agree when fitness at state `y` is `A *ᵥ y`. -/
public theorem isReplicatorSolution_iff_isSolution_mulVec {A : Matrix ι ι ℝ} {x : ℝ → ι → ℝ} :
    IsReplicatorSolution A x ↔ IsSolution (fun y => A *ᵥ y) x := by
  constructor
  · intro h
    exact ⟨fun i t ht => by
      simpa only [replicatorField_apply, MathlibExt.Biology.Dynamics.Replicator.meanFitness_mulVec]
        using h i t ht⟩
  · intro h i t ht
    simpa only [replicatorField_apply, MathlibExt.Biology.Dynamics.Replicator.meanFitness_mulVec]
      using h.hasDerivAt i t ht

private theorem antitoneOn_entropy_add {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} {p : ι → ℝ} {x : ℝ → ι → ℝ}
    (hx : IsSolution (fun z => A *ᵥ z) x)
    (hp1 : ∑ i, p i = 1) (hpos : ∀ t, 0 ≤ t → ∀ i, 0 < x t i) (c : ℝ)
    (hc : ∀ t, 0 ≤ t → c ≤ p ⬝ᵥ A *ᵥ x t - x t ⬝ᵥ A *ᵥ x t) :
    AntitoneOn (fun t => relEntropy p (x t) + c * t)
      (Set.Ici 0) := by
  have hd : ∀ t, 0 ≤ t → HasDerivAt
      (fun s => relEntropy p (x s) + c * s)
      (-(p ⬝ᵥ A *ᵥ x t - x t ⬝ᵥ A *ᵥ x t) + c) t := fun t ht => by
    simpa using (hx.hasDerivAt_relEntropy hp1 ht fun i => (hpos t ht i).ne').fun_add
      ((hasDerivAt_id' t).const_mul c)
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt) fun t ht => ?_
  linarith [hc t (interior_subset ht)]

/-- **An interior ESS attracts every interior orbit** (Hofbauer and Sigmund 2003, Theorem 7).
For every payoff matrix `A` and every ESS `p` of `A` with `p i > 0` for all `i`, every solution
`x` of the replicator equation with `x 0 ∈ Δ` and `x 0 i > 0` for all `i` converges to `p`.

Source: Hofbauer and Sigmund (2003), §2.6, Theorem 7. -/
public theorem IsESS.tendsto_of_pos {A : Matrix ι ι ℝ} {p : ι → ℝ} (h : IsESS A p)
    (hp : ∀ i, 0 < p i) {x : ℝ → ι → ℝ} (hx : IsReplicatorSolution A x)
    (hx₀ : x 0 ∈ simplex ι) (hx₀pos : ∀ i, 0 < x 0 i) : Tendsto x atTop (𝓝 p) := by
  have hess : MathlibExt.Biology.Dynamics.Replicator.IsESS A p := h
  have hsol := isReplicatorSolution_iff_isSolution_mulVec.mp hx
  have hf := continuous_mulVec_fitness A
  have hmem : ∀ t, 0 ≤ t → x t ∈ simplex ι := fun t ht =>
    hsol.mem_simplex hf hx₀.1 hx₀.2 ht
  have hpos : ∀ t, 0 ≤ t → ∀ i, 0 < x t i := fun t ht i =>
    hsol.pos_of_pos hf (hx₀pos i) ht
  have hV : ∀ t, 0 ≤ t → 0 ≤ relEntropy p (x t) :=
    fun t ht => by
      by_cases heq : x t = p
      · rw [heq, relEntropy_self]
      · exact (relEntropy_pos hp h.1.2
          (hpos t ht) (hmem t ht).2 heq).le
  obtain ⟨δ, hδ, hatt⟩ := hess.tendsto_nhds hp
  have henter : ∃ T, 0 ≤ T ∧ ‖x T - p‖ < δ := by
    by_contra hno
    push Not at hno
    let K := simplex ι ∩ {y : ι → ℝ | δ ≤ ‖y - p‖}
    have hcompact : IsCompact (simplex ι) := by
      have hc := isCompact_range (continuous_pi fun i : ι =>
        Convexity.StdSimplex.continuous_weights_apply ℝ i)
      convert hc using 1
      ext y
      simp [simplex, Convexity.StdSimplex.range_toFun_comp_weights]
    have hK : IsCompact K := hcompact.inter_right
      (isClosed_le continuous_const (continuous_id.sub continuous_const).norm)
    have hg : Continuous fun y : ι → ℝ => p ⬝ᵥ A *ᵥ y - y ⬝ᵥ A *ᵥ y := by
      simp only [dotProduct]
      fun_prop
    obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn ⟨x 0, hx₀, hno 0 le_rfl⟩ hg.continuousOn
    have hyne : y ≠ p := by
      intro heq
      have hyfar : δ ≤ ‖y - p‖ := hy.2
      exact (not_le.2 hδ) (by simpa only [heq, sub_self, norm_zero] using hyfar)
    let c := p ⬝ᵥ A *ᵥ y - y ⬝ᵥ A *ᵥ y
    have hc : 0 < c := sub_pos.2 (hess.dotProduct_mulVec_lt_of_pos hp hy.1 hyne)
    have hanti := antitoneOn_entropy_add hsol h.1.2 hpos c fun t ht =>
      hmin ⟨hmem t ht, hno t ht⟩
    let T := relEntropy p (x 0) / c + 1
    have hT : 0 ≤ T := add_nonneg (div_nonneg (hV 0 le_rfl) hc.le) zero_le_one
    have hbound := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hT) hT
    have hcT : c * T = relEntropy p (x 0) + c := by
      dsimp [T]
      field_simp
    simp only [mul_zero, add_zero] at hbound
    linarith [hV T hT]
  obtain ⟨T, hT, hnear⟩ := henter
  have hshift : IsSolution (fun z => A *ᵥ z)
      (fun t => x (t + T)) := ⟨fun i t ht => by
    simpa only [Function.comp_def, one_smul] using
      (hsol.hasDerivAt i (t + T) (add_nonneg ht hT)).scomp t
      ((hasDerivAt_id' t).add_const T)⟩
  have hlimit := hatt (fun t => x (t + T)) hshift (by simpa [simplex] using hmem T hT)
    (by simpa using hnear)
  rw [Metric.tendsto_atTop] at hlimit ⊢
  intro ε hε
  obtain ⟨S, hS⟩ := hlimit ε hε
  refine ⟨S + T, fun t ht => ?_⟩
  simpa using hS (t - T) (by linarith)

end WantedExt.Biology.Ecology.BoundaryESSStabilityWanted
