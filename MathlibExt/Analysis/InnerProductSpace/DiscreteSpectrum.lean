/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

open scoped BigOperators

/-- **Nonnegative discrete spectrum.** A nonnegative discrete spectrum is a sequence of real
numbers $E_0, E_1, E_2, \ldots$, the eigenvalues listed with multiplicity, such that
$E_j \ge 0$ for every $j$, $E_i \le E_j$ whenever $i \le j$, and $E_j \to +\infty$ as
$j \to \infty$.

The sequence is not required to be the spectrum of any particular operator, such as a
Dirichlet or Neumann Laplacian. -/
structure NonnegativeDiscreteSpectrum where
  eigenvalue : ℕ → ℝ
  nonnegative_eigenvalue : ∀ j, 0 ≤ eigenvalue j
  monotone_eigenvalue : Monotone eigenvalue
  tendsto_eigenvalue_atTop :
    Filter.Tendsto eigenvalue Filter.atTop Filter.atTop

namespace NonnegativeDiscreteSpectrum

instance : CoeFun NonnegativeDiscreteSpectrum (fun _ => ℕ → ℝ) :=
  ⟨NonnegativeDiscreteSpectrum.eigenvalue⟩

/-- **A nonnegative discrete spectrum is determined by its eigenvalues.** If two nonnegative
discrete spectra $S$ and $T$ have the same $j$-th eigenvalue for every index $j \in \mathbb{N}$,
then $S = T$. -/
@[ext] theorem ext {S T : NonnegativeDiscreteSpectrum} (h : ∀ j, S j = T j) :
    S = T := by
  obtain ⟨eS, h1S, h2S, h3S⟩ := S
  obtain ⟨eT, h1T, h2T, h3T⟩ := T
  have he : eS = eT := funext h
  subst he
  rfl

/-- **Strict sublevel set.** For a nonnegative discrete spectrum with eigenvalues
$E_0 \le E_1 \le \cdots$ and a real number $\Lambda$, the strict sublevel set at $\Lambda$ is the
set of indices $\{j \in \mathbb{N} : E_j < \Lambda\}$.

The strict inequality matches the convention that $(\Lambda - E_j)_+^0$ equals $1$ only when
$E_j < \Lambda$, avoiding $0^0 = 1$ at the cutoff. -/
def sublevelSet (S : NonnegativeDiscreteSpectrum) (Λ : ℝ) : Set ℕ :=
  {j | S j < Λ}

/-- **Strict sublevel sets are finite.** For a nonnegative discrete spectrum with eigenvalues
$E_0 \le E_1 \le \cdots$ and every real number $\Lambda$, the strict sublevel set
$\{j \in \mathbb{N} : E_j < \Lambda\}$ is finite.

Since $E_j \to +\infty$, there is $N$ with $E_j \ge \Lambda$ for all $j \ge N$, so the set is
contained in $\{0, 1, \ldots, N - 1\}$. -/
theorem sublevelSet_finite
    (S : NonnegativeDiscreteSpectrum) (Λ : ℝ) :
    (S.sublevelSet Λ).Finite := by
  obtain ⟨N, hN⟩ := Filter.tendsto_atTop_atTop.mp S.tendsto_eigenvalue_atTop Λ
  refine Set.Finite.subset (Finset.finite_toSet (Finset.range N)) fun j hj => ?_
  simp only [sublevelSet, Set.mem_ofPred_eq] at hj
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  have hle : N ≤ j := not_lt.mp h
  exact (not_le.mpr hj) (hN j hle)

/-- **Finite strict sublevel set.** For a nonnegative discrete spectrum with eigenvalues
$E_0 \le E_1 \le \cdots$ and a real number $\Lambda$, the finite strict sublevel set at $\Lambda$ is
the strict sublevel set $\{j \in \mathbb{N} : E_j < \Lambda\}$, regarded as a finite set of
indices; it is finite because $E_j \to +\infty$. -/
noncomputable def sublevelFinset
    (S : NonnegativeDiscreteSpectrum) (Λ : ℝ) : Finset ℕ :=
  (S.sublevelSet_finite Λ).toFinset

/-- **Membership in the finite strict sublevel set.** For a nonnegative discrete spectrum with
eigenvalues $E_0 \le E_1 \le \cdots$, a real number $\Lambda$ and an index $j \in \mathbb{N}$, the
index $j$ lies in the finite strict sublevel set at $\Lambda$ if and only if $E_j < \Lambda$. -/
@[simp] theorem mem_sublevelFinset
    (S : NonnegativeDiscreteSpectrum) (Λ : ℝ) (j : ℕ) :
    j ∈ S.sublevelFinset Λ ↔ S j < Λ := by
  rw [sublevelFinset, Set.Finite.mem_toFinset]
  rfl

/-- **Eigenvalue counting function.** For a nonnegative discrete spectrum with eigenvalues
$E_0 \le E_1 \le \cdots$ and a real number $\Lambda$, the counting function $N(\Lambda)$ is the
number of indices $j \in \mathbb{N}$ with $E_j < \Lambda$, so eigenvalues are counted with
multiplicity. -/
noncomputable def countingFunction
    (S : NonnegativeDiscreteSpectrum) (Λ : ℝ) : ℕ :=
  (S.sublevelFinset Λ).card

/-- **Riesz mean.** For a nonnegative discrete spectrum with eigenvalues $E_0 \le E_1 \le \cdots$
and real numbers $\sigma$ and $\Lambda$, the Riesz mean of order $\sigma$ at $\Lambda$ is the
finite sum $R_\sigma(\Lambda) = \sum_{j \in \mathbb{N},\, E_j < \Lambda} (\Lambda - E_j)^\sigma$
over indices, where $x^\sigma$ is the real power. -/
noncomputable def rieszMean
    (S : NonnegativeDiscreteSpectrum) (σ Λ : ℝ) : ℝ :=
  ∑ j ∈ S.sublevelFinset Λ, Real.rpow (Λ - S j) σ

/-- **The Riesz mean of order zero is the counting function.** For a nonnegative discrete
spectrum with eigenvalues $E_0 \le E_1 \le \cdots$ and every real number $\Lambda$, the Riesz
mean of order $0$ at $\Lambda$ equals the counting function at $\Lambda$, viewed as a real
number: $R_0(\Lambda) = N(\Lambda)$.

Every summand $(\Lambda - E_j)^0$ has strictly positive base $\Lambda - E_j$, so it equals $1$. -/
@[simp] theorem rieszMean_zero
    (S : NonnegativeDiscreteSpectrum) (Λ : ℝ) :
    S.rieszMean 0 Λ = S.countingFunction Λ := by
  simp [rieszMean, countingFunction]

end NonnegativeDiscreteSpectrum
