/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A degree-theory criterion for unique versus multiple equilibria

Conradi, Feliu, Mincheva and Wiuf (2017, Theorem 1 (A′)/(B′); Supporting Information, Theorem 4):
consider a reaction network with `n` species and `ℓ` reactions `∑_i α_{ij} X_i → ∑_i β_{ij} X_i`,
stoichiometric matrix `N = β - α` of rank `s`, and `C¹` rate functions `v`, nonnegative on
`ℝ^n_{≥0}`, with `v_j(x) = 0` whenever `x_i = 0` for some `i` with `α_{ij} > 0` (main text Eq. (2);
Supporting Information, condition (22); mass action satisfies both). The ODE is `ẋ = f(x) = N v(x)`
on `ℝ^n_{≥0}`. Let `W ∈ ℝ^{d × n}`, `d = n - s`, be a row-reduced matrix whose rows form a basis of
`im(N)^⊥`, with pivot columns `i_1 < … < i_d`, and `P_c = {x ≥ 0 : W x = c}`, `P_c^+` its positive
part. Let `φ_c(x)_i = f_i(x)` for `i` not a pivot and `φ_c(x)_{i_k} = (W x - c)_k`, and `M(x)` its
Jacobian matrix. Assume `P_c^+ ≠ ∅`, (i) the semiflow is dissipative (all trajectories in each class
with positive points eventually enter a fixed compact subset of the class), and (ii) there are no
boundary equilibria in `P_c`. Then:

* (A′) if `sign det M(x) = (-1)^s` at every positive equilibrium in `P_c`, there is exactly one
  positive equilibrium in `P_c`, and it is nondegenerate;
* (B′) if `sign det M(x) = (-1)^{s+1}` at some positive equilibrium in `P_c`, there are at least
  two positive equilibria in `P_c`, at least one of them nondegenerate; if all positive
  equilibria in `P_c` are nondegenerate, there are finitely many, at least three, and an odd
  number.

Here an equilibrium `x` is nondegenerate when the Jacobian of `f` at `x` has no nonzero kernel
vector in `im(N)` (the standard definition; the source shows this is equivalent to `det M(x) ≠ 0`).
The rate functions are assumed continuously differentiable on all of `ℝ^n`, a trajectory is a
function with derivative `f(x(t))` at every `t ≥ 0`, and dissipativity includes that every point of
each class with positive points starts at least one trajectory. Not recorded here: the degree
statement (Supporting Information, Theorem 3) and the Brouwer-degree facts used in the proof.

Sources: C. Conradi, E. Feliu, M. Mincheva and C. Wiuf, "Identifying parameter regions for
multistationarity", PLoS Computational Biology 13 (2017) e1005751, arXiv:1608.03993, Supporting
Information, condition (22), Definition 2 and Theorem 4 (main text: Theorem 1 and Eq. (2));
numbers are those of the arXiv version.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace WantedExt.Biology.Biophysics.MultistationarityDegreeCriterionWanted

open Filter

variable {n ℓ d : ℕ}

/-- A **reaction system**: reactant and product coefficient matrices `α β` and rate functions
`v : ℝ^n → ℝ^ℓ`. -/
structure ReactionSystem (n ℓ : ℕ) where
  /-- Reactant coefficients `α_{ij}`. -/
  α : Matrix (Fin n) (Fin ℓ) ℕ
  /-- Product coefficients `β_{ij}`. -/
  β : Matrix (Fin n) (Fin ℓ) ℕ
  /-- Rate functions. -/
  v : (Fin n → ℝ) → Fin ℓ → ℝ

/-- The stoichiometric matrix `N = β - α`. -/
def ReactionSystem.N (G : ReactionSystem n ℓ) : Matrix (Fin n) (Fin ℓ) ℝ :=
  fun i j => (G.β i j : ℝ) - G.α i j

/-- The species-formation rate `f(x) = N v(x)`. -/
noncomputable def ReactionSystem.f (G : ReactionSystem n ℓ) (x : Fin n → ℝ) : Fin n → ℝ :=
  G.N.mulVec (G.v x)

/-- The rate functions are `C¹`, nonnegative on the nonnegative orthant, and satisfy assumption
(Supporting Information, condition (22)) on the nonnegative orthant: for every `x` with `x_k ≥ 0`
for all `k`, `v_j(x) = 0` whenever `x_i = 0` for some `i` with `α_{ij} > 0`. -/
def ReactionSystem.Admissible (G : ReactionSystem n ℓ) : Prop :=
  ContDiff ℝ 1 G.v ∧ (∀ x, (∀ i, 0 ≤ x i) → ∀ j, 0 ≤ G.v x j) ∧
    ∀ x, (∀ k, 0 ≤ x k) → ∀ j i, x i = 0 → 0 < G.α i j → G.v x j = 0

/-- `W` is a **row-reduced conservation matrix** with pivots `piv`: its rows form a basis of
`im(N)^⊥` (they are linearly independent, annihilate every column of `N`, and every vector
orthogonal to all columns of `N` is a combination of them), `piv` is strictly increasing,
`W k (piv k) = 1`, `W k j = 0` for `j < piv k`, and `W k' (piv k) = 0` for `k' ≠ k`. -/
def IsRowReducedConservation (N : Matrix (Fin n) (Fin ℓ) ℝ) (W : Matrix (Fin d) (Fin n) ℝ)
    (piv : Fin d → Fin n) : Prop :=
  LinearIndependent ℝ (fun k => W k) ∧ W * N = 0 ∧
    (∀ w : Fin n → ℝ, (∀ j, ∑ i, w i * N i j = 0) → w ∈ Submodule.span ℝ (Set.range W)) ∧
    StrictMono piv ∧ (∀ k, W k (piv k) = 1) ∧ (∀ k j, j < piv k → W k j = 0) ∧
    ∀ k k', k' ≠ k → W k' (piv k) = 0

/-- The class `P_c = {x ≥ 0 : W x = c}`. -/
def classSet (W : Matrix (Fin d) (Fin n) ℝ) (c : Fin d → ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ W.mulVec x = c}

/-- The positive class `P_c^+ = {x > 0 : W x = c}`. -/
def posClassSet (W : Matrix (Fin d) (Fin n) ℝ) (c : Fin d → ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 < x i) ∧ W.mulVec x = c}

/-- `y` is a **trajectory** of `ẋ = f(x)` from `x₀`: `y 0 = x₀` and `y` has derivative
`f(y t)` at every `t ≥ 0`. -/
def ReactionSystem.IsTrajectory (G : ReactionSystem n ℓ) (x₀ : Fin n → ℝ) (y : ℝ → Fin n → ℝ) :
    Prop :=
  y 0 = x₀ ∧ ∀ t, 0 ≤ t → HasDerivAt y (G.f (y t)) t

/-- The semiflow is **dissipative** (Supporting Information, Definition 2): for every `c` with
`P_c^+ ≠ ∅` there is a compact `K ⊆ P_c` such that every point of `P_c` starts a trajectory, and
every trajectory from a point of `P_c` lies in `K` from some time on. -/
def ReactionSystem.Dissipative (G : ReactionSystem n ℓ) (W : Matrix (Fin d) (Fin n) ℝ) : Prop :=
  ∀ c, (posClassSet W c).Nonempty → ∃ K ⊆ classSet W c, IsCompact K ∧
    ∀ x₀ ∈ classSet W c, (∃ y, G.IsTrajectory x₀ y) ∧
      ∀ y, G.IsTrajectory x₀ y → ∀ᶠ t in atTop, y t ∈ K

open Classical in
/-- The matrix `M(x)`: the Jacobian of `φ_c`, i.e. row `i` is the derivative of `f_i` at `x` for
`i` not a pivot, and row `piv k` is row `k` of `W`. -/
noncomputable def ReactionSystem.M (G : ReactionSystem n ℓ) (W : Matrix (Fin d) (Fin n) ℝ)
    (piv : Fin d → Fin n) (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if h : ∃ k, piv k = i then W h.choose j
    else fderiv ℝ G.f x (Pi.single j 1) i

/-- The equilibrium `x` is **nondegenerate**: no nonzero vector in `im(N)` is in the kernel of the
Jacobian of `f` at `x`. -/
def ReactionSystem.Nondegenerate (G : ReactionSystem n ℓ) (x : Fin n → ℝ) : Prop :=
  ∀ u : Fin ℓ → ℝ, fderiv ℝ G.f x (G.N.mulVec u) = 0 → G.N.mulVec u = 0

/-- **Uniqueness criterion** (Conradi, Feliu, Mincheva and Wiuf 2017, Theorem 1 (A′); Supporting
Information, Theorem 4): for
an admissible reaction system (`C¹` rates, nonnegative on the nonnegative orthant, satisfying
condition (22)) with stoichiometric matrix of rank `s`, a row-reduced conservation matrix `W`
with pivots `piv`, and `c` with `P_c^+ ≠ ∅`, if the semiflow is dissipative, there are no boundary
equilibria in `P_c`, and `sign det M(x) = (-1)^s` at every positive equilibrium `x ∈ P_c^+`, then
there is exactly one positive equilibrium in `P_c`, and it is nondegenerate.

Source: Conradi, Feliu, Mincheva and Wiuf (2017), arXiv:1608.03993, Theorem 1 (A′)
(Supporting Information, Theorem 4). -/
public theorem_wanted existsUnique_equilibrium (G : ReactionSystem n ℓ) (hG : G.Admissible)
    (W : Matrix (Fin d) (Fin n) ℝ) (piv : Fin d → Fin n)
    (hW : IsRowReducedConservation G.N W piv) (c : Fin d → ℝ)
    (hne : (posClassSet W c).Nonempty) (hdiss : G.Dissipative W)
    (hbd : ∀ x ∈ classSet W c, (∃ i, x i = 0) → G.f x ≠ 0)
    (hsign : ∀ x ∈ posClassSet W c, G.f x = 0 →
      SignType.sign (G.M W piv x).det = (-1) ^ G.N.rank) :
    (∃! x, x ∈ posClassSet W c ∧ G.f x = 0) ∧
      ∀ x ∈ posClassSet W c, G.f x = 0 → G.Nondegenerate x

/-- **Multistationarity criterion** (Conradi, Feliu, Mincheva and Wiuf 2017, Theorem 1 (B′);
Supporting Information, Theorem 4): for an admissible reaction system (`C¹` rates, nonnegative on
the nonnegative orthant, satisfying condition (22)) with stoichiometric matrix of rank `s`, a
row-reduced conservation matrix `W` with pivots `piv`, and `c` with `P_c^+ ≠ ∅`, if the semiflow is
dissipative, there are no boundary equilibria in `P_c`, and `sign det M(x₁) = (-1)^{s+1}` at some
positive equilibrium `x₁ ∈ P_c^+`, then there are two distinct positive equilibria in `P_c`, at
least one positive equilibrium in `P_c` is nondegenerate, and if every positive equilibrium in `P_c`
is nondegenerate then the set of positive equilibria in `P_c` is finite with an odd number `≥ 3` of
elements.

Source: Conradi, Feliu, Mincheva and Wiuf (2017), arXiv:1608.03993, Theorem 1 (B′)
(Supporting Information, Theorem 4). -/
public theorem_wanted multiple_equilibria (G : ReactionSystem n ℓ) (hG : G.Admissible)
    (W : Matrix (Fin d) (Fin n) ℝ) (piv : Fin d → Fin n)
    (hW : IsRowReducedConservation G.N W piv) (c : Fin d → ℝ)
    (hne : (posClassSet W c).Nonempty) (hdiss : G.Dissipative W)
    (hbd : ∀ x ∈ classSet W c, (∃ i, x i = 0) → G.f x ≠ 0)
    (x₁ : Fin n → ℝ) (hx₁ : x₁ ∈ posClassSet W c) (hf₁ : G.f x₁ = 0)
    (hsign : SignType.sign (G.M W piv x₁).det = (-1) ^ (G.N.rank + 1)) :
    (∃ x ∈ posClassSet W c, ∃ y ∈ posClassSet W c, x ≠ y ∧ G.f x = 0 ∧ G.f y = 0) ∧
      (∃ x ∈ posClassSet W c, G.f x = 0 ∧ G.Nondegenerate x) ∧
      ((∀ x ∈ posClassSet W c, G.f x = 0 → G.Nondegenerate x) →
        ∃ E : Finset (Fin n → ℝ), (∀ x, x ∈ E ↔ x ∈ posClassSet W c ∧ G.f x = 0) ∧
          3 ≤ E.card ∧ Odd E.card)

end WantedExt.Biology.Biophysics.MultistationarityDegreeCriterionWanted
