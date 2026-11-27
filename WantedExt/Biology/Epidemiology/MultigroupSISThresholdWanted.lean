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

Dividing by `N_i`, it is the network Levins system `I' = LevinsNetwork.field C e I`,
`I_i' = (1 - I_i) (C I)_i - e_i I_i`, with contact matrix `C_ij = λ_ij N_j / N_i ≥ 0` and
recovery rates `e_i = 1 / d_i > 0`; `C` is irreducible exactly when `(λ_ij)` is. Lajmanovich and
Yorke state the threshold through the stability modulus `s(A)` (the largest real part of an
eigenvalue) of `A = (λ_ij N_j) - diag (N_i / d_i) = diag (N) (C - diag e)`. Since `A` is a
Metzler matrix and `diag (N)` is a positive diagonal scaling, `s(A)` has the sign of
`s(C - diag e)`, and for `C ≥ 0`, `e > 0` the latter is `≤ 0` exactly when the persistence
number `R₀ = ρ(C diag(e)⁻¹)` (`LevinsNetwork.persistenceNumber C e`) satisfies `R₀ ≤ 1`, and
`> 0` exactly when `R₀ > 1` (`LevinsNetwork.isHurwitz_iff`, `LevinsNetwork.exists_re_pos_iff`).
So the theorem reads: if the population cannot be split into two parts that do not contact each
other, every solution with initial data in `[0, 1]ⁿ` tends to `0` when `R₀ ≤ 1`; when `R₀ > 1`
there is a unique equilibrium in `(0, 1)ⁿ`, and it attracts every solution with some group
initially infected. For two or more groups that condition is the irreducibility of `C`. A single
group cannot be split even when `C = 0`, but `Matrix.IsIrreducible` asks for a path of positive
length from each group to itself, so the die-out statement also allows a single group; in the
endemic statement `C = 0` cannot occur, since then `R₀ = 0`.

The model, `IsSolution` and `R₀` are those of `Domains.Biology.Ecology.LevinsNetwork`, which
proves invariance of the box
`[0, 1]ⁿ` (`IsSolution.mem_Icc`), extinction for `R₀ < 1` (`tendsto_zero_of_lt_one`) and
non-extinction for `R₀ > 1` with `C` irreducible (`not_tendsto_zero_of_one_lt`). The statements
below add the critical case `R₀ = 1`, the existence and uniqueness of the endemic equilibrium,
its global attraction, and the global existence and uniqueness of solutions. Continuous
dependence on the initial data, the remaining part of the well-posedness that Lajmanovich and
Yorke prove (Hethcote and Yorke 1984, p. 27), is not stated.

Sources: A. Lajmanovich and J. A. Yorke, "A deterministic model for gonorrhea in a
nonhomogeneous population", Math. Biosci. 28 (1976) 221–236; statement as restated in
H. W. Hethcote and J. A. Yorke, *Gonorrhea Transmission Dynamics and Control*, Lecture Notes
in Biomathematics 56, Springer (1984), Section 3.1, model [3.1] and Theorem 3.1.
-/
module

public import Batteries.Util.ProofWanted
public import Domains.Biology.Ecology.LevinsNetwork
public import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

namespace WantedExt.Biology.Epidemiology.MultigroupSISThresholdWanted

open Filter Topology MathlibExt.Biology.Ecology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Global existence and uniqueness.** Lajmanovich and Yorke (1976), as restated by Hethcote
and Yorke (1984, p. 27): on a finite index set `ι` of groups, let `C` be a contact matrix with
every `C_ij ≥ 0` and `e` recovery rates with every `e_i > 0` (for the multigroup SIS model,
`C_ij = λ_ij N_j / N_i` and `e_i = 1 / d_i`). For every initial state `I₀ ∈ [0, 1]ⁿ` there is a
solution `I` of `I' = LevinsNetwork.field C e I` on `[0, ∞)` (`LevinsNetwork.IsSolution C e I`)
with `I 0 = I₀`; it stays in `[0, 1]ⁿ`, and every solution `J` with `J 0 = I₀` agrees with `I`
for all `t ≥ 0`. This is the source's well-posedness without its continuous dependence on the
initial data, which is not stated here. -/
theorem_wanted exists_unique_solution (C : Matrix ι ι ℝ) (e : ι → ℝ)
    (hC : ∀ i j, 0 ≤ C i j) (he : ∀ i, 0 < e i)
    (I₀ : ι → ℝ) (hI₀ : ∀ i, I₀ i ∈ Set.Icc (0 : ℝ) 1) :
    ∃ I : ℝ → ι → ℝ, I 0 = I₀ ∧ LevinsNetwork.IsSolution C e I ∧
      (∀ t, 0 ≤ t → ∀ i, I t i ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ J : ℝ → ι → ℝ, J 0 = I₀ → LevinsNetwork.IsSolution C e J → ∀ t, 0 ≤ t → J t = I t

/-- **Lajmanovich–Yorke theorem, die-out.** Theorem 3.1 of Hethcote and Yorke (1984), after
Lajmanovich and Yorke (1976): let the index set `ι` of groups be finite and nonempty, let `C` be a
contact matrix with every `C_ij ≥ 0` that is irreducible or has a single group, and let `e` be
recovery rates with every `e_i > 0`. If the persistence number satisfies
`R₀ = LevinsNetwork.persistenceNumber C e ≤ 1` (the critical case `R₀ = 1` included; equivalently
`s(A) ≤ 0` in Lajmanovich and Yorke's notation), then every solution `I` of
`LevinsNetwork.IsSolution C e I` with `I 0 ∈ [0, 1]ⁿ` tends to `0`. The source asks only that the
population cannot be split into two parts that do not contact each other. A single group cannot
be split even when `C = 0`, which `Matrix.IsIrreducible` excludes, since it asks for a path of
positive length from each group to itself. -/
theorem_wanted tendsto_zero_of_persistenceNumber_le_one [Nonempty ι] (C : Matrix ι ι ℝ)
    (e : ι → ℝ) (hC : ∀ i j, 0 ≤ C i j) (hirr : C.IsIrreducible ∨ Subsingleton ι)
    (he : ∀ i, 0 < e i)
    (hR : LevinsNetwork.persistenceNumber C e ≤ 1) (I : ℝ → ι → ℝ)
    (hI : LevinsNetwork.IsSolution C e I) (hI₀ : ∀ i, I 0 i ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto I atTop (𝓝 0)

/-- **Lajmanovich–Yorke theorem, endemic case** (Theorem 3.1 of Hethcote and Yorke 1984, after
Lajmanovich and Yorke 1976): let the index set `ι` of groups be finite and nonempty, let `C` be an
irreducible contact matrix, and let `e` be recovery rates with every `e_i > 0`. If
`1 < LevinsNetwork.persistenceNumber C e` (equivalently `s(A) > 0`), there is a unique equilibrium
`E` (`LevinsNetwork.field C e E = 0`) with every coordinate in `(0, 1)`, and every solution `I` of
`LevinsNetwork.IsSolution C e I` with `I 0 ∈ [0, 1]ⁿ` and `I 0 ≠ 0` tends to `E`. -/
theorem_wanted exists_endemic_of_one_lt_persistenceNumber [Nonempty ι] (C : Matrix ι ι ℝ)
    (e : ι → ℝ) (hirr : C.IsIrreducible) (he : ∀ i, 0 < e i)
    (hR : 1 < LevinsNetwork.persistenceNumber C e) :
    ∃ E : ι → ℝ, (∀ i, E i ∈ Set.Ioo (0 : ℝ) 1) ∧ LevinsNetwork.field C e E = 0 ∧
      (∀ E' : ι → ℝ, (∀ i, E' i ∈ Set.Ioo (0 : ℝ) 1) → LevinsNetwork.field C e E' = 0 →
        E' = E) ∧
      ∀ I : ℝ → ι → ℝ, LevinsNetwork.IsSolution C e I → (∀ i, I 0 i ∈ Set.Icc (0 : ℝ) 1) →
        I 0 ≠ 0 → Tendsto I atTop (𝓝 E)

end WantedExt.Biology.Epidemiology.MultigroupSISThresholdWanted
