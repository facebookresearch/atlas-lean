/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Leonard Dinh
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Analysis 386, Analysis 387, Analysis 388

/-!
# Solution of a Delayed Difference Equation; Lyapunov Stability of a Delayed Difference Solution;
  Asymptotic Stability of a Delayed Difference Solution

## References

* This is the standard notion of a solution of a finite-delay difference equation. For the
  particular recurrence considered here, see: G. L. Karakostas, On a Conjecture for the Difference
  Equation $x_{n+1}=1+p x_{n-m}/x_n^2$, AIMS Mathematics 8 (2023), 22714--22729. DOI:
  10.3934/math.20231156. (for `IsDelayedDifferenceSolution`)
* This is the usual Lyapunov stability condition for solutions of finite-dimensional discrete
  dynamical systems, expressed in terms of the complete initial history required by a delay
  equation. For its use in the present problem, see: G. L. Karakostas, On a Conjecture for the
  Difference Equation $x_{n+1}=1+p x_{n-m}/x_n^2$, AIMS Mathematics 8 (2023), 22714--22729. (for
  `IsStableDelayedSolution`)
* This is the standard notion of local asymptotic stability for discrete dynamical systems,
  adapted to the finite initial history of a delay equation. For the present recurrence, see: G.
  L. Karakostas, On a Conjecture for the Difference Equation $x_{n+1}=1+p x_{n-m}/x_n^2$, AIMS
  Mathematics 8 (2023), 22714--22729. (for `IsAsymptoticallyStableDelayedSolution`)
-/

namespace MetaMathlibExt

-- Analysis 386: Solution of a Delayed Difference Equation

/-- Let X be a type, let m∈ℕ, and let

F:Xᵐ⁺¹→ X.

A bi-infinite sequence

x:ℤ→ X

is a solution of the delayed difference equation determined by F if

xₙ₊₁=F(xₙ,xₙ₋₁,…,xₙ₋ₘ)

for every n≥0.

The use of integer indices allows the prescribed initial history

x₋ₘ,…,x₀

to appear directly as values of the same sequence.
-/
def IsDelayedDifferenceSolution
    {X : Type*}
    (m : ℕ)
    (F : (Fin (m + 1) → X) → X)
    (x : ℤ → X) : Prop :=
  ∀ n : ℕ,
    x (Int.ofNat (n + 1)) =
      F
        (fun j =>
          x
            (Int.ofNat n -
              Int.ofNat (j : ℕ)))

-- Analysis 387: Lyapunov Stability of a Delayed Difference Solution

/-- Let X be a metric space and let r be a solution of a delayed difference equation with delay m.
Relative to a specified class of admissible trajectories, r is stable if for every ε>0 there exists
δ>0 such that every admissible solution whose initial history

x₋ₘ,…,x₀

is within δ of

r₋ₘ,…,r₀

remains within ε of rₙ for every n≥0.
-/
def IsStableDelayedSolution
    {X : Type*}
    [PseudoMetricSpace X]
    (m : ℕ)
    (F : (Fin (m + 1) → X) → X)
    (admissible : (ℤ → X) → Prop)
    (r : ℤ → X) : Prop :=
  IsDelayedDifferenceSolution m F r ∧
  admissible r ∧
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x : ℤ → X,
        IsDelayedDifferenceSolution m F x →
        admissible x →
        (∀ j : Fin (m + 1),
          dist
              (x (-Int.ofNat (j : ℕ)))
              (r (-Int.ofNat (j : ℕ))) < δ) →
        ∀ n : ℕ,
          dist
              (x (Int.ofNat n))
              (r (Int.ofNat n)) < ε

-- Analysis 388: Asymptotic Stability of a Delayed Difference Solution

/-- A solution r of a delayed difference equation is asymptotically stable if it is Lyapunov stable
and there exists δ>0 such that every admissible solution whose initial history is within δ of that
of r satisfies

d(xₙ,rₙ)⟶0  as n→∞.

Thus asymptotic stability combines stability under small perturbations with local attraction.
-/
def IsAsymptoticallyStableDelayedSolution
    {X : Type*}
    [PseudoMetricSpace X]
    (m : ℕ)
    (F : (Fin (m + 1) → X) → X)
    (admissible : (ℤ → X) → Prop)
    (r : ℤ → X) : Prop :=
  IsStableDelayedSolution m F admissible r ∧
  ∃ δ : ℝ, 0 < δ ∧
    ∀ x : ℤ → X,
      IsDelayedDifferenceSolution m F x →
      admissible x →
      (∀ j : Fin (m + 1),
        dist
            (x (-Int.ofNat (j : ℕ)))
            (r (-Int.ofNat (j : ℕ))) < δ) →
      Filter.Tendsto
        (fun n : ℕ =>
          dist
            (x (Int.ofNat n))
            (r (Int.ofNat n)))
        Filter.atTop
        (nhds 0)

end MetaMathlibExt

end
