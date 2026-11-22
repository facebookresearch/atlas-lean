/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.ShuffleFilling
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.PrismSkeletal

/-!
# Two-horn prisms in a quasicategory

For a monomorphism `i : A ⟶ B` and a quasicategory `C`, prescribed maps
on `A ⊗ Δ[2]` and `B ⊗ Λ[2, k]`, agreeing on their intersection, extend
to `B ⊗ Δ[2]` when the critical edges are equivalences. The critical
edge is `0 → 1` for `k = 0` and `1 → 2` for `k = 2`; the condition is
imposed at every vertex of `B`. Both complete prescribed maps are retained.

The four results below assemble the shuffle-cell and relative skeletal
proofs, including the boundary case in dimension zero. Their special
outer-horn input is the absolute criterion of HTT Proposition 1.2.4.3,
with the opposite criterion on the right. Cisinski, *Higher Categories
and Homotopical Algebra*, July 30, 2026, Theorem 3.4.18 (printed p.103 /
PDF p.119) gives the relative special outer-horn context. The product-prism
statements follow by the shuffle attachments and skeletal extension.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial

universe u

namespace SSet

variable {A B C : SSet.{u}} {i : A ⟶ B}

/-- **Horn-zero `Δ[2]`-prism extension along `∂Δ[n].ι`,
unconditionally**: `SSet.`
`prismTwoHornZeroExtension_boundary_of_shuffleCell` at
`SSet.shuffleHornZeroCellExtension_of_quasicategory`. -/
theorem prismTwoHornZeroExtension_boundary (n : ℕ) (C : SSet.{u})
    [Quasicategory C] :
    PrismTwoHornZeroExtension ∂Δ[n].ι C :=
  prismTwoHornZeroExtension_boundary_of_shuffleCell
    (shuffleHornZeroCellExtension_of_quasicategory n C)

/-- **Horn-two `Δ[2]`-prism extension along `∂Δ[n].ι`,
unconditionally**: `SSet.`
`prismTwoHornTwoExtension_boundary_of_shuffleCell` at
`SSet.shuffleHornTwoCellExtension_of_quasicategory`. -/
theorem prismTwoHornTwoExtension_boundary (n : ℕ) (C : SSet.{u})
    [Quasicategory C] :
    PrismTwoHornTwoExtension ∂Δ[n].ι C :=
  prismTwoHornTwoExtension_boundary_of_shuffleCell
    (shuffleHornTwoCellExtension_of_quasicategory n C)

/-- **Horn-zero `Δ[2]`-prism extension along every
monomorphism, unconditionally**: `SSet.`
`prismTwoHornZeroExtension_of_mono_of_shuffleCell` at
`SSet.shuffleHornZeroCellExtension_of_quasicategory`. -/
theorem prismTwoHornZeroExtension_of_mono (i : A ⟶ B) [Mono i]
    [Quasicategory C] :
    PrismTwoHornZeroExtension i C :=
  prismTwoHornZeroExtension_of_mono_of_shuffleCell i
    (fun n ↦ shuffleHornZeroCellExtension_of_quasicategory n C)

/-- **Horn-two `Δ[2]`-prism extension along every
monomorphism, unconditionally**: `SSet.`
`prismTwoHornTwoExtension_of_mono_of_shuffleCell` at
`SSet.shuffleHornTwoCellExtension_of_quasicategory`. -/
theorem prismTwoHornTwoExtension_of_mono (i : A ⟶ B) [Mono i]
    [Quasicategory C] :
    PrismTwoHornTwoExtension i C :=
  prismTwoHornTwoExtension_of_mono_of_shuffleCell i
    (fun n ↦ shuffleHornTwoCellExtension_of_quasicategory n C)

end SSet
