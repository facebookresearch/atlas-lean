/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Double commutators with transvections (Kourovka Notebook Problem 10.46)

Kourovka Notebook, Problem 10.46 (V. M. Petechuk), marked solved: let `R` be an associative ring
with identity. Prove that for every `σ ∈ GLₙ(R)`, `n ≥ 3`, there exist transvections `τ₁, τ₂` such
that `[[σ, τ₁], τ₂]` is a unipotent element.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.TransvectionCommutatorUnipotentKourovka10Problem46Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 10.46 (V. M. Petechuk). UnsolvedMath record
UM-00700661 (`KOU-10.46`), dataset ulamai/UnsolvedMath v1.8.0.

Transvections are read as the elementary transvections `1 + r eᵢⱼ` (`i ≠ j`, `r ≠ 0`); every notion
of transvection over a ring contains them, and the resolving counterexample excludes all nonidentity
unipotent matrices. Unipotent means that `g - 1` is nilpotent. `R` is nontrivial: over the zero ring
there are no transvections. The commutator is `[x, y] = x y x⁻¹ y⁻¹`; the convention `x⁻¹ y⁻¹ x y`
gives an equivalent statement, since unipotence is invariant under conjugation and inversion and
inverses of elementary transvections are elementary transvections.
-/

/-- `τ` is an elementary transvection `1 + r eᵢⱼ` with `i ≠ j` and `r ≠ 0`. -/
def IsElementaryTransvection {R : Type*} [Ring R] {n : ℕ} (τ : GL (Fin n) R) : Prop :=
  ∃ (i j : Fin n) (r : R), i ≠ j ∧ r ≠ 0 ∧ (τ : Matrix (Fin n) (Fin n) R) = 1 + Matrix.single i j r

/-- Kourovka 10.46 (V. M. Petechuk): for every nontrivial associative ring `R` with identity, every
`n ≥ 3` and every `σ ∈ GLₙ(R)` there are transvections `τ₁, τ₂` such that `[[σ, τ₁], τ₂]` is
unipotent (`[[σ, τ₁], τ₂] - 1` is nilpotent), with `[x, y] = x y x⁻¹ y⁻¹`. Transvections are read as
elementary transvections. -/
def doubleCommutatorWithTransvectionsUnipotent : Prop :=
  ∀ (R : Type) [Ring R] [Nontrivial R] (n : ℕ), 3 ≤ n → ∀ σ : GL (Fin n) R,
    ∃ τ₁ τ₂ : GL (Fin n) R, IsElementaryTransvection τ₁ ∧ IsElementaryTransvection τ₂ ∧
      IsNilpotent (((σ * τ₁ * σ⁻¹ * τ₁⁻¹) * τ₂ * (σ * τ₁ * σ⁻¹ * τ₁⁻¹)⁻¹ * τ₂⁻¹ : GL (Fin n) R) -
        1 : Matrix (Fin n) (Fin n) R)

/--
Resolved false: Muliarchyk (2026 preprint, Theorem 1.1) shows that for every field `k` and `n ≥ 2`,
over the nonzero algebra `R = k⟨xᵢⱼ, yᵢⱼ⟩ / (XY = YX = I)` the matrix `X = (xᵢⱼ) ∈ GLₙ(R)` has every
nonempty iterated commutator with nonidentity unipotent matrices nonunipotent, which excludes
elementary transvections and their conjugates. The Kourovka Notebook (21st issue) marks 10.46
solved, "This is not always true". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems
in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 10.46 (V. M.
Petechuk); resolution: K. Muliarchyk, A counterexample to Kourovka Notebook Problem 10.46: unipotent
commutators over noncommutative algebras, preprint (2026), Theorem 1.1 (over R = k⟨x_ij, y_ij⟩ / (XY
= YX = I) every nonempty iterated commutator of X with nonidentity unipotent matrices is
nonunipotent); the Kourovka Notebook (21st issue) marks 10.46 solved,
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka_10.46_solution.pdf.
-/
public theorem_wanted doubleCommutatorWithTransvectionsUnipotent_refuted :
    ¬ doubleCommutatorWithTransvectionsUnipotent

end MathlibExt.GroupTheory.TransvectionCommutatorUnipotentKourovka10Problem46Wanted
