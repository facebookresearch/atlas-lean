/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Lajmanovich–Yorke threshold for the multigroup SIS model

A population is divided into `n` groups of sizes `N_i > 0`. With `I_i ∈ [0, 1]` the fraction of
group `i` that is infective, `λ_ij ≥ 0` the rate of adequate contacts of an infective of group
`j` with members of group `i`, and `d_i > 0` the mean duration of infection, the multigroup SIS
model of Lajmanovich and Yorke (1976) is

  `d/dt (N_i I_i) = (∑_j λ_ij N_j I_j) (1 - I_i) - N_i I_i / d_i`.

Let `A = L - D` with `L = (λ_ij N_j)` and `D = diag (N_i / d_i)`, and let `s(A)` be its stability
modulus, the largest real part of an eigenvalue. If the contact matrix `(λ_ij)` is irreducible,
then every solution with initial data in `[0, 1]ⁿ` tends to `0` when `s(A) ≤ 0`; when
`s(A) > 0` there is a unique equilibrium in `(0, 1)ⁿ`, and it attracts every solution with
some group initially infected.

The single-group SIS model and its Lyapunov stability are in
`Domains.Biology.Epidemiology.SIS` and `Domains.Biology.Epidemiology.SISGlobalStability`; the
multigroup threshold theorem is not proved yet.

Sources: A. Lajmanovich and J. A. Yorke, "A deterministic model for gonorrhea in a
nonhomogeneous population", Math. Biosci. 28 (1976) 221–236; statement as restated in
H. W. Hethcote and J. A. Yorke, *Gonorrhea Transmission Dynamics and Control*, Lecture Notes
in Biomathematics 56, Springer (1984), Section 3.1, model [3.1] and Theorem 3.1.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

namespace WantedExt.Biology.Epidemiology.MultigroupSISThresholdWanted

open Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The vector field of the multigroup SIS model in the prevalence variables:
`I_i' = ((∑_j λ_ij N_j I_j) (1 - I_i) - N_i I_i / d_i) / N_i`. -/
noncomputable def field (Nsz d : ι → ℝ) (lam : Matrix ι ι ℝ) (I : ι → ℝ) : ι → ℝ :=
  fun i => ((∑ j, lam i j * Nsz j * I j) * (1 - I i) - Nsz i * I i / d i) / Nsz i

/-- A forward solution: `I` has right derivative `field (I t)` at every `t ≥ 0`. -/
def IsSolution (Nsz d : ι → ℝ) (lam : Matrix ι ι ℝ) (I : ℝ → ι → ℝ) : Prop :=
  ∀ t, 0 ≤ t → HasDerivWithinAt I (field Nsz d lam (I t)) (Set.Ici 0) t

/-- The matrix `A = L - D` with `L_ij = λ_ij N_j` and `D = diag (N_i / d_i)`. -/
noncomputable def thresholdMatrix (Nsz d : ι → ℝ) (lam : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => lam i j * Nsz j - if i = j then Nsz i / d i else 0

/-- The stability modulus `s(M)`: the largest real part of a (complex) eigenvalue of `M`. -/
noncomputable def stabilityModulus (M : Matrix ι ι ℝ) : ℝ :=
  sSup ((fun z : ℂ => z.re) '' spectrum ℂ (M.map (algebraMap ℝ ℂ)))

/-- **Well-posedness** (Lajmanovich and Yorke 1976, as restated by Hethcote and Yorke 1984,
p. 27): for initial data in `[0, 1]ⁿ` there is a forward solution, it stays in `[0, 1]ⁿ`, and
any two forward solutions with the same initial data agree for all `t ≥ 0`. -/
theorem_wanted exists_unique_solution (Nsz d : ι → ℝ) (lam : Matrix ι ι ℝ)
    (hN : ∀ i, 0 < Nsz i) (hd : ∀ i, 0 < d i) (hlam : ∀ i j, 0 ≤ lam i j)
    (I₀ : ι → ℝ) (hI₀ : ∀ i, I₀ i ∈ Set.Icc (0 : ℝ) 1) :
    ∃ I : ℝ → ι → ℝ, I 0 = I₀ ∧ IsSolution Nsz d lam I ∧
      (∀ t, 0 ≤ t → ∀ i, I t i ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ J : ℝ → ι → ℝ, J 0 = I₀ → IsSolution Nsz d lam J → ∀ t, 0 ≤ t → J t = I t

/-- **Lajmanovich–Yorke theorem, die-out** (Theorem 3.1 of Hethcote and Yorke 1984, after
Lajmanovich and Yorke 1976): if the contact matrix `(λ_ij)` is irreducible and the stability
modulus of `A = L - D` satisfies `s(A) ≤ 0` (the critical case `s(A) = 0` included), then
every forward solution with initial data in `[0, 1]ⁿ` tends to `0`. -/
theorem_wanted tendsto_zero_of_stabilityModulus_nonpos [Nonempty ι] (Nsz d : ι → ℝ)
    (lam : Matrix ι ι ℝ) (hN : ∀ i, 0 < Nsz i) (hd : ∀ i, 0 < d i) (hirr : lam.IsIrreducible)
    (hs : stabilityModulus (thresholdMatrix Nsz d lam) ≤ 0) (I : ℝ → ι → ℝ)
    (hI : IsSolution Nsz d lam I) (hI₀ : ∀ i, I 0 i ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto I atTop (𝓝 0)

/-- **Lajmanovich–Yorke theorem, endemic case** (Theorem 3.1 of Hethcote and Yorke 1984,
after Lajmanovich and Yorke 1976): if the contact matrix `(λ_ij)` is irreducible and
`s(A) > 0`, there is a unique equilibrium `E` with every coordinate in `(0, 1)`, and every
forward solution with initial data in `[0, 1]ⁿ` other than `0` tends to `E`. -/
theorem_wanted exists_endemic_of_stabilityModulus_pos [Nonempty ι] (Nsz d : ι → ℝ)
    (lam : Matrix ι ι ℝ) (hN : ∀ i, 0 < Nsz i) (hd : ∀ i, 0 < d i) (hirr : lam.IsIrreducible)
    (hs : 0 < stabilityModulus (thresholdMatrix Nsz d lam)) :
    ∃ E : ι → ℝ, (∀ i, E i ∈ Set.Ioo (0 : ℝ) 1) ∧ field Nsz d lam E = 0 ∧
      (∀ E' : ι → ℝ, (∀ i, E' i ∈ Set.Ioo (0 : ℝ) 1) → field Nsz d lam E' = 0 → E' = E) ∧
      ∀ I : ℝ → ι → ℝ, IsSolution Nsz d lam I → (∀ i, I 0 i ∈ Set.Icc (0 : ℝ) 1) →
        I 0 ≠ 0 → Tendsto I atTop (𝓝 E)

end WantedExt.Biology.Epidemiology.MultigroupSISThresholdWanted
