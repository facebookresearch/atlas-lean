/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatBoundaryWFS
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHornWFS
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGeneratorRLPComparison
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyEquivalence

/-!
# Conditional model compatibility equalities for the two `TopCat` WFSs

This file is part of the KQ3 layer. Let `W` be
`TopCat.weakHomotopyEquivalences` with its staged two-out-of-three and
retract stability, and let the boundary/horn weak factorization systems be
the staged small-object instances. From the hard inclusions
`realizedHornInclusions.rlp.llp ≤ W` and
`realizedBoundaryInclusions.rlp ≤ W`, the easy halves of the two model
compatibility equalities hold directly: every boundary-RLP map is a
horn-RLP weak equivalence, and every horn left-class map is a
boundary left-class weak equivalence.

Each hard direction is proved as a reusable retract/factorization lemma,
conditional on the opposite cross inclusion: the fibration hard direction
assumes
`realizedBoundaryInclusions.rlp.llp ⊓ W ≤ realizedHornInclusions.rlp.llp`,
and the cofibration hard direction assumes
`realizedHornInclusions.rlp ⊓ W ≤ realizedBoundaryInclusions.rlp`.
Combining each hard direction with its easy half gives the corresponding
equality. The cross inclusions are genuine further inputs, since the two
hard directions are interdependent by the standard retract argument, so
no unconditional model claim is made here.
-/

@[expose] public section

open CategoryTheory MorphismProperty

universe u

namespace TopCat

/-- Retract step for fibrations: a horn-RLP weak equivalence is a
boundary-RLP map, once the cofibration cross inclusion is assumed. -/
theorem hornRLP_inf_W_le_boundaryRLP
    (hBdry : realizedBoundaryInclusions.{u}.rlp ≤ weakHomotopyEquivalences)
    (hCross : realizedBoundaryInclusions.{u}.rlp.llp ⊓ weakHomotopyEquivalences ≤
      realizedHornInclusions.{u}.rlp.llp) :
    realizedHornInclusions.{u}.rlp ⊓ weakHomotopyEquivalences ≤
      realizedBoundaryInclusions.{u}.rlp := by
  intro X Y f hf
  obtain ⟨hfR, hfW⟩ := hf
  obtain ⟨Z, i, p, fac, hi, hp⟩ :=
    factorizationData realizedBoundaryInclusions.{u}.rlp.llp
      realizedBoundaryInclusions.{u}.rlp f
  have hpW : weakHomotopyEquivalences p := hBdry _ hp
  have hcomp : weakHomotopyEquivalences (i ≫ p) := by
    rw [fac]
    exact hfW
  have hiW : weakHomotopyEquivalences i :=
    MorphismProperty.of_postcomp weakHomotopyEquivalences i p hpW hcomp
  have hiH : realizedHornInclusions.{u}.rlp.llp i := hCross _ ⟨hi, hiW⟩
  have : HasLiftingProperty i f := hiH _ hfR
  exact MorphismProperty.of_retract
    (RetractArrow.ofRightLiftingProperty fac) hp

/-- Retract step for cofibrations: a boundary left-class weak equivalence
is a horn left-class map, once the fibration cross inclusion is assumed. -/
theorem boundaryLLP_inf_W_le_hornLLP
    (hHorn : realizedHornInclusions.{u}.rlp.llp ≤ weakHomotopyEquivalences)
    (hCross : realizedHornInclusions.{u}.rlp ⊓ weakHomotopyEquivalences ≤
      realizedBoundaryInclusions.{u}.rlp) :
    realizedBoundaryInclusions.{u}.rlp.llp ⊓ weakHomotopyEquivalences ≤
      realizedHornInclusions.{u}.rlp.llp := by
  intro X Y g hg
  obtain ⟨hgL, hgW⟩ := hg
  obtain ⟨Z, j, q, fac, hj, hq⟩ :=
    factorizationData realizedHornInclusions.{u}.rlp.llp
      realizedHornInclusions.{u}.rlp g
  have hjW : weakHomotopyEquivalences j := hHorn _ hj
  have hcomp : weakHomotopyEquivalences (j ≫ q) := by
    rw [fac]
    exact hgW
  have hqW : weakHomotopyEquivalences q :=
    MorphismProperty.of_precomp weakHomotopyEquivalences j q hjW hcomp
  have hqB : realizedBoundaryInclusions.{u}.rlp q := hCross _ ⟨hq, hqW⟩
  have : HasLiftingProperty g q := hgL _ hqB
  exact MorphismProperty.of_retract
    (RetractArrow.ofLeftLiftingProperty fac) hj

/-- Conditional fibration equality: horn-RLP weak equivalences are exactly
the boundary-RLP maps. -/
theorem hornRLP_inf_W_eq_boundaryRLP
    (hBdry : realizedBoundaryInclusions.{u}.rlp ≤ weakHomotopyEquivalences)
    (hCross : realizedBoundaryInclusions.{u}.rlp.llp ⊓ weakHomotopyEquivalences ≤
      realizedHornInclusions.{u}.rlp.llp) :
    realizedHornInclusions.{u}.rlp ⊓ weakHomotopyEquivalences =
      realizedBoundaryInclusions.{u}.rlp :=
  le_antisymm (hornRLP_inf_W_le_boundaryRLP hBdry hCross)
    (le_inf realizedBoundaryRLP_le_realizedHornRLP hBdry)

/-- Conditional cofibration equality: boundary left-class weak equivalences
are exactly the horn left-class maps. -/
theorem boundaryLLP_inf_W_eq_hornLLP
    (hHorn : realizedHornInclusions.{u}.rlp.llp ≤ weakHomotopyEquivalences)
    (hCross : realizedHornInclusions.{u}.rlp ⊓ weakHomotopyEquivalences ≤
      realizedBoundaryInclusions.{u}.rlp) :
    realizedBoundaryInclusions.{u}.rlp.llp ⊓ weakHomotopyEquivalences =
      realizedHornInclusions.{u}.rlp.llp :=
  le_antisymm (boundaryLLP_inf_W_le_hornLLP hHorn hCross)
    (le_inf (antitone_llp realizedBoundaryRLP_le_realizedHornRLP) hHorn)

end TopCat
