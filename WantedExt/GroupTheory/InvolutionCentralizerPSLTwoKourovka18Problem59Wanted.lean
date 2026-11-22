/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Involution centralizers isomorphic to ⟨i⟩ × L₂(P) (Kourovka Notebook Problem 18.59)

Kourovka Notebook, Problem 18.59 (D. V. Lytkina), marked solved in the 21st issue: does there exist
a periodic group `G` such that `G` contains an involution, all involutions in `G` are conjugate, and
the centralizer of every involution `i` is isomorphic to `⟨i⟩ × L₂(P)`, where `P` is some infinite
locally finite field of characteristic `2`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

@[expose] public section

namespace MathlibExt.GroupTheory.InvolutionCentralizerPSLTwoKourovka18Problem59Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 18.59 (D. V. Lytkina). UnsolvedMath record
UM-00701488 (`KOU-18.59`), dataset ulamai/UnsolvedMath v1.8.0.

`L₂(P) = PSL₂(P)` is Mathlib's `Matrix.ProjectiveSpecialLinearGroup (Fin 2) P`, the quotient of
`SL₂(P)` by its centre; a locally finite field is one whose finitely generated subfields are finite;
periodic means every element has finite order. The field `P` is chosen once for all involutions
(they are conjugate, so this loses nothing).
-/

/-- `P` is a locally finite field: every finitely generated subfield is finite. -/
def IsLocallyFiniteField (P : Type) [Field P] : Prop :=
  ∀ s : Finset P, Finite (Subfield.closure (s : Set P))

/-- Kourovka 18.59 (D. V. Lytkina): there is a periodic group `G` that contains an involution, in
which all involutions are conjugate and the centralizer of every involution `i` is isomorphic to
`⟨i⟩ × L₂(P)` for some infinite locally finite field `P` of characteristic `2`. -/
def periodicGroupWithPSLInvolutionCentralizers : Prop :=
  ∃ (G : Type) (_ : Group G), (∀ g : G, IsOfFinOrder g) ∧ (∃ i : G, orderOf i = 2) ∧
    (∀ i j : G, orderOf i = 2 → orderOf j = 2 → IsConj i j) ∧
    ∃ (P : Type) (_ : Field P), CharP P 2 ∧ Infinite P ∧ IsLocallyFiniteField P ∧
      ∀ i : G, orderOf i = 2 →
        Nonempty (Subgroup.centralizer {i} ≃*
          (Subgroup.zpowers i × Matrix.ProjectiveSpecialLinearGroup (Fin 2) P))

/--
Resolved false: the Kourovka Notebook (21st issue) answers 18.59 "No, there are no such groups" (K.
Muliarchyk, 2026). Muliarchyk's Theorem 3 shows that no group, periodic or not, has one nonempty
conjugacy class of involutions whose centralizers are isomorphic to `C₂ × PSL₂(P)` for an infinite
locally finite field `P` of characteristic `2`. Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Problem 18.59 (D. V. Lytkina); resolution: K. Muliarchyk, Involution centralizers and a linear
obstruction: Kourovka Problems 18.59 and 18.60, preprint, 2026, Theorem 3: no group has a single
nonempty conjugacy class of involutions with involution centralizers isomorphic to C_2 × PSL_2(P), P
an infinite locally finite field of characteristic two (periodicity not needed); the Kourovka
Notebook (21st issue) marks 18.59 solved,
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka_18_59-18_60_solution.pdf.
-/
public theorem_wanted periodicGroupWithPSLInvolutionCentralizers_refuted :
    ¬ periodicGroupWithPSLInvolutionCentralizers

end MathlibExt.GroupTheory.InvolutionCentralizerPSLTwoKourovka18Problem59Wanted
