/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Spoke graphs with cyclotomic norm squared (AimPL Classifying fusion categories, Problem 4.2)

AimPL, Classifying fusion categories, Problem 4.2 (N. Snyder): look at all spoke graphs with `N > 0`
arms. Are there finitely many `N`-tuples `(ℓ₁, …, ℓ_N)` such that the spoke graph with `N` arms of
lengths `ℓ₁, …, ℓ_N` has cyclotomic norm squared?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.FieldTheory.Galois.Abelian

@[expose] public section

namespace MathlibExt.GraphTheory.AbelianSpokeGraphFinitenessAIMOtherProblem50Wanted

/-!
Source: AimPL: Classifying fusion categories, Problem 4.2 (N. Snyder),
http://aimpl.org/fusioncat/4/. UnsolvedMath record UM-20003243 (`AIM-OTHER-0050`), dataset
ulamai/UnsolvedMath v1.8.0.

A spoke graph is a centre with `N` paths (arms) of positive lengths attached; its norm `λ` is the
largest eigenvalue of its adjacency matrix (the Perron-Frobenius eigenvalue). `λ²` is cyclotomic
when it lies in a cyclotomic field, equivalently (Kronecker-Weber) when `ℚ(λ²)` is an abelian
extension of `ℚ`, Calegari and Guo's 'abelian' graphs; the statement uses the latter
(`IsAbelianGalois`). The answer depends on `N`; only `N ≥ 4` is formalized (finitely many tuples).
The cases `N ≤ 3`, where the Dynkin diagrams `A_m` and `D_m` give infinitely many tuples, are not
formalized: no source states that answer (`partial_scope`). The adjacency matrix was checked
numerically on `A_m`, `D_m`, `E₆`, `E₈`, `D̃₄` and stars.
-/

/-- The vertices of the spoke graph with arms of lengths `ℓ₀, …, ℓ_{N-1}`: the centre `none` and,
for `j < ℓᵢ`, the vertex `some ⟨i, j⟩` at distance `j + 1` from the centre on arm `i`. -/
abbrev SpokeVertex {N : ℕ} (ℓ : Fin N → ℕ) := Option (Σ i : Fin N, Fin (ℓ i))

/-- The adjacency matrix of the spoke graph: the centre is adjacent to the first vertex of every
arm, and consecutive vertices of an arm are adjacent. -/
def spokeAdjMatrix {N : ℕ} (ℓ : Fin N → ℕ) : Matrix (SpokeVertex ℓ) (SpokeVertex ℓ) ℝ :=
  Matrix.of fun u v =>
    match u, v with
    | none, none => 0
    | none, some w => if w.2.val = 0 then 1 else 0
    | some w, none => if w.2.val = 0 then 1 else 0
    | some w, some w' =>
      if w.1 = w'.1 ∧ (w.2.val + 1 = w'.2.val ∨ w'.2.val + 1 = w.2.val) then 1 else 0

/-- The norm `λ` of the spoke graph: the largest real eigenvalue of its adjacency matrix (its
Perron-Frobenius eigenvalue). -/
noncomputable def spokeNorm {N : ℕ} (ℓ : Fin N → ℕ) : ℝ :=
  sSup {μ : ℝ | ∃ v : SpokeVertex ℓ → ℝ, v ≠ 0 ∧ (spokeAdjMatrix ℓ).mulVec v = μ • v}

/-- The `N`-tuples of positive arm lengths whose spoke graph has abelian norm squared: `ℚ(λ²)` is an
abelian Galois extension of `ℚ` (equivalently, by Kronecker-Weber, `λ²` is cyclotomic). -/
def abelianSpokeTuples (N : ℕ) : Set (Fin N → ℕ) :=
  {ℓ | (∀ i, 1 ≤ ℓ i) ∧
    IsAbelianGalois ℚ (IntermediateField.adjoin ℚ ({spokeNorm ℓ ^ 2} : Set ℝ))}

/-- AimPL Classifying fusion categories, Problem 4.2, for `N ≥ 4` arms, as a claim: only finitely
many `N`-tuples of arm lengths give a spoke graph with cyclotomic (abelian) norm squared. -/
def abelianSpokeTuplesFiniteManyArms : Prop :=
  ∀ N : ℕ, 4 ≤ N → (abelianSpokeTuples N).Finite

/--
Resolved true for `N ≥ 4`: Calegari and Guo proved that for a fixed graph and number of attachment
points only finitely many abelian spiders are not Dynkin diagrams; a spoke graph with `N ≥ 4` arms
of positive length has a vertex of degree `N ≥ 4`, so none of them is a Dynkin diagram (`A_m`,
`D_m`, `E₆`, `E₇`, `E₈` have maximum degree at most `3`). Source: AimPL: Classifying fusion
categories, Problem 4.2 (N. Snyder), http://aimpl.org/fusioncat/4/; resolution: F. Calegari and Z.
Guo, Abelian spiders and real cyclotomic integers, Trans. Amer. Math. Soc. 370 (2018), no. 9,
6515-6533, arXiv:1502.00035, Theorem 1.1: for a fixed graph Γ and k there are only finitely many
abelian k-spiders Γ_k (paths of lengths r_i ≥ 0 attached at k not necessarily distinct vertices of
Γ; abelian: ℚ(λ²) abelian, λ the Perron-Frobenius eigenvalue) which are not Dynkin diagrams; here Γ
is a single vertex and k = N, https://doi.org/10.1090/tran/7237.
-/
public theorem_wanted abelianSpokeTuplesFiniteManyArms_holds : abelianSpokeTuplesFiniteManyArms

end MathlibExt.GraphTheory.AbelianSpokeGraphFinitenessAIMOtherProblem50Wanted
