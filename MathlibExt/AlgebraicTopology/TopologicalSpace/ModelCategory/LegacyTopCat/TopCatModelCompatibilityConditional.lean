/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatBoundaryWFS
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHornWFS
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGeneratorRLPComparison
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyEquivalence

/-!
# Compatibility of topological lifting classes

On `TopCat.{u}`, write `B=realizedBoundaryInclusions`, `H=realizedHornInclusions`, and
`W=weakHomotopyEquivalences`. If `B.rlp≤W` and `B.rlp.llp ⊓ W≤H.rlp.llp`, the retract argument
gives `H.rlp ⊓ W=B.rlp`. If `H.rlp.llp≤W` and `H.rlp ⊓ W≤B.rlp`, the analogous argument gives
`B.rlp.llp ⊓ W=H.rlp.llp`.

The two inclusions and the resulting equalities are stated separately with their respective
cross-compatibility hypotheses.
-/

@[expose] public section

open CategoryTheory MorphismProperty

universe u

namespace TopCat

/-- On `TopCat.{u}`, let `B=realizedBoundaryInclusions`, `H=realizedHornInclusions`, and
`W=weakHomotopyEquivalences`. Assume `B.rlp≤W` and `B.rlp.llp ⊓ W≤H.rlp.llp`. Then `H.rlp ⊓
W≤B.rlp`: every horn-right-lifting weak homotopy equivalence lifts against realized
boundaries. -/
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

/-- On `TopCat.{u}`, let `B=realizedBoundaryInclusions`, `H=realizedHornInclusions`, and
`W=weakHomotopyEquivalences`. Assume `H.rlp.llp≤W` and `H.rlp ⊓ W≤B.rlp`. Then `B.rlp.llp ⊓
W≤H.rlp.llp`: a boundary-left-lifting weak homotopy equivalence belongs to the horn-generated
left class. -/
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

/-- On `TopCat.{u}`, let `B=realizedBoundaryInclusions`, `H=realizedHornInclusions`, and `W=weakHomotopyEquivalences`.
If `B.rlp≤W` and `B.rlp.llp ⊓ W≤H.rlp.llp`, then
`H.rlp ⊓ W=B.rlp`.
The horn-right-lifting weak equivalences are exactly the boundary-right-lifting maps. -/
theorem hornRLP_inf_W_eq_boundaryRLP
    (hBdry : realizedBoundaryInclusions.{u}.rlp ≤ weakHomotopyEquivalences)
    (hCross : realizedBoundaryInclusions.{u}.rlp.llp ⊓ weakHomotopyEquivalences ≤
      realizedHornInclusions.{u}.rlp.llp) :
    realizedHornInclusions.{u}.rlp ⊓ weakHomotopyEquivalences =
      realizedBoundaryInclusions.{u}.rlp :=
  le_antisymm (hornRLP_inf_W_le_boundaryRLP hBdry hCross)
    (le_inf realizedBoundaryRLP_le_realizedHornRLP hBdry)

/-- On `TopCat.{u}`, let `B=realizedBoundaryInclusions`, `H=realizedHornInclusions`, and `W=weakHomotopyEquivalences`.
If `H.rlp.llp≤W` and `H.rlp ⊓ W≤B.rlp`, then
`B.rlp.llp ⊓ W=H.rlp.llp`.
The weak equivalences in the boundary-generated left class are exactly the horn-generated left maps. -/
theorem boundaryLLP_inf_W_eq_hornLLP
    (hHorn : realizedHornInclusions.{u}.rlp.llp ≤ weakHomotopyEquivalences)
    (hCross : realizedHornInclusions.{u}.rlp ⊓ weakHomotopyEquivalences ≤
      realizedBoundaryInclusions.{u}.rlp) :
    realizedBoundaryInclusions.{u}.rlp.llp ⊓ weakHomotopyEquivalences =
      realizedHornInclusions.{u}.rlp.llp :=
  le_antisymm (boundaryLLP_inf_W_le_hornLLP hHorn hCross)
    (le_inf (antitone_llp realizedBoundaryRLP_le_realizedHornRLP) hHorn)

end TopCat
