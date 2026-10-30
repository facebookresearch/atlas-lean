/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Algebra.Order.Floor.Defs

/-!
# Markov-chain mixing vocabulary

Total variation distance on a finite set, mixing at a time (the `1/4` convention), cutoff for a
family of distance profiles, discrete tori with their coordinate steps, the `±1` sign of a Boolean
spin, and the number of monochromatic edges of a colouring (Potts energy). Shared by the AimPL
"Markov chain mixing times" conjecture entries.
-/

@[expose] public section


namespace MathlibExt.Probability.MarkovMixing

/-- Vertices of the discrete torus `ℤ_n^d`. -/
abbrev Torus (d n : ℕ) := Fin d → Fin n

/-- The neighbour `x + e_k` of `x` in `ℤ_n^d`. -/
def stepUp {d n : ℕ} (k : Fin d) (x : Torus d n) : Torus d n :=
  Function.update x k ⟨((x k).val + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt (x k).2)⟩

/-- The sign `±1` of a Boolean spin (`true ↦ +1`). -/
noncomputable def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- Total variation distance `(1/2) ∑_y |μ y - ν y|` of two functions on a finite set. -/
noncomputable def tvDist {S : Type*} [Fintype S] (μ ν : S → ℝ) : ℝ :=
  (1 / 2) * ∑ y, |μ y - ν y|

/-- The total variation distance `(1/2) ∑_y |Q(x, y) - π(y)|` of the row `x` of `Q` from `π`. -/
noncomputable def tvRow {S : Type*} [Fintype S] (Q : Matrix S S ℝ) (π : S → ℝ) (x : S) : ℝ :=
  (1 / 2) * ∑ y, |Q x y - π y|

/-- `P` is `1/4`-mixed at time `t` w.r.t. `π`: `d_TV(P^t(x, ·), π) ≤ 1/4` for every start `x`
(`t_mix = min {t | IsMixedAt P π t}`). -/
def IsMixedAt {S : Type*} [Fintype S] [DecidableEq S] (P : Matrix S S ℝ) (π : S → ℝ)
    (t : ℕ) : Prop :=
  ∀ x, tvDist (fun y => (P ^ t) x y) π ≤ 1 / 4

open Classical in
/-- Number of monochromatic edges `∑_{uv ∈ E} 1{σ_u = σ_v}` of `σ` in `G` (each edge counted
once). -/
noncomputable def monoEdges {n q : ℕ} (G : SimpleGraph (Fin n)) (σ : Fin n → Fin q) : ℝ :=
  (1 / 2) * ∑ u, ∑ v, if G.Adj u v ∧ σ u = σ v then 1 else 0

/-- Distance profiles `d n t` exhibit cutoff: some `tₙ → ∞` has `d n ⌈(1+η)tₙ⌉ → 0` and
`d n ⌊(1-η)tₙ⌋ → 1` for every `η ∈ (0,1)`. -/
def HasCutoff (d : ℕ → ℕ → ℝ) : Prop :=
  ∃ t : ℕ → ℝ, Filter.Tendsto t Filter.atTop Filter.atTop ∧ ∀ η : ℝ, 0 < η → η < 1 →
    Filter.Tendsto (fun n => d n ⌈(1 + η) * t n⌉₊) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n => d n ⌊(1 - η) * t n⌋₊) Filter.atTop (nhds 1)

@[simp] theorem sgn_true : sgn true = 1 := by simp [sgn]

@[simp] theorem sgn_false : sgn false = -1 := by simp [sgn]

@[simp] theorem tvDist_self {S : Type*} [Fintype S] (μ : S → ℝ) : tvDist μ μ = 0 := by
  simp [tvDist]

theorem tvDist_comm {S : Type*} [Fintype S] (μ ν : S → ℝ) : tvDist μ ν = tvDist ν μ := by
  simp only [tvDist, abs_sub_comm]

theorem tvRow_eq_tvDist {S : Type*} [Fintype S] (Q : Matrix S S ℝ) (π : S → ℝ) (x : S) :
    tvRow Q π x = tvDist (Q x) π :=
  rfl

end MathlibExt.Probability.MarkovMixing
