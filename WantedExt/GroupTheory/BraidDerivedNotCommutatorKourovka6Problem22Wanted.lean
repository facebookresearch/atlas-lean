/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A braid in the derived subgroup that is not a commutator (Kourovka Notebook Problem 6.22)

Kourovka Notebook, Archive of Solved Problems, Problem 6.22 (G. S. Makanin): construct a braid that
belongs to the derived subgroup of the braid group but is not a commutator.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Commutator.Basic
public import MathlibExt.GroupTheory.ArtinGroup

@[expose] public section

namespace MathlibExt.GroupTheory.BraidDerivedNotCommutatorKourovka6Problem22Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.22 (G. S.
Makanin). UnsolvedMath record UM-00700369 (`KOU-6.22`), dataset ulamai/UnsolvedMath v1.8.0.

The braid group `B₃` is the Artin group of type `A₂` from `MathlibExt.GroupTheory.ArtinGroup`, with
standard generators `x = σ₁ = of 0` and `y = σ₂ = of 1` and relation `x y x = y x y`. The derived
subgroup is Mathlib's `commutator`, and a commutator is an element `a b a⁻¹ b⁻¹`. The target is the
Archive's explicit braid.
-/

/-- Kourovka 6.22 (G. S. Makanin), answer of the Archive: in the braid group
`B₃ = ⟨x, y | x y x = y x y⟩` (the Artin group of type `A₂`, `x = σ₁`, `y = σ₂`), the braid
`(x y x y x)¹² (x y)⁻¹² (x y x)⁻¹²` lies in the derived subgroup but is not a commutator. -/
def braidDerivedNotCommutator : Prop :=
  ∀ x y : (CoxeterMatrix.A 2).ArtinGroup, x = CoxeterMatrix.ArtinGroup.of (CoxeterMatrix.A 2) 0 →
    y = CoxeterMatrix.ArtinGroup.of (CoxeterMatrix.A 2) 1 →
    (x * y * x * y * x) ^ (12 : ℤ) * (x * y) ^ (-12 : ℤ) * (x * y * x) ^ (-12 : ℤ) ∈
        commutator (CoxeterMatrix.A 2).ArtinGroup ∧
      ¬ ∃ a b : (CoxeterMatrix.A 2).ArtinGroup,
        (x * y * x * y * x) ^ (12 : ℤ) * (x * y) ^ (-12 : ℤ) * (x * y * x) ^ (-12 : ℤ) =
          a * b * a⁻¹ * b⁻¹

/--
Resolved true: the Kourovka Archive answers 6.22 with Semënov's example (1986): in `B₃` with
standard generators `x = σ₁`, `y = σ₂`, the braid `(x y x y x)¹² (x y)⁻¹² (x y x)⁻¹²` belongs to the
derived subgroup but is not a commutator. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 6.22 (G. S. Makanin); resolution: Yu. S. Semënov, Abstracts of the 10th
All-Union Symposium on Group Theory, Minsk, 1986, p. 207 (Russian), Kourovka Archive, Problem 6.22:
the braid (xyxyx)¹²(xy)⁻¹²(xyx)⁻¹² of B₃ belongs to the derived subgroup but is not a commutator
(Semënov), https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted braidDerivedNotCommutator_holds : braidDerivedNotCommutator

end MathlibExt.GroupTheory.BraidDerivedNotCommutatorKourovka6Problem22Wanted
