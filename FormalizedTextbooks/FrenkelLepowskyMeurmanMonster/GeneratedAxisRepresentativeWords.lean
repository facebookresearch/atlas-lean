/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal actual generated-group words for the BSD mmgroup sample representatives.
The class labels are descriptive; this module makes no classification or coverage claim.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555NortonActualCandidates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Actual fiber-product lift of compact permutation node 0. -/
noncomputable def representativeNodeFiber0 : localFiberSubgroup :=
  (monsterSourcePermutationFiber 0)⁻¹

/-- Actual fiber-product lift of compact permutation node 1. -/
noncomputable def representativeNodeFiber1 : localFiberSubgroup :=
  (monsterSourcePermutationFiber 1)⁻¹

/-- Actual fiber-product lift of compact permutation node 2. -/
noncomputable def representativeNodeFiber2 : localFiberSubgroup :=
  representativeNodeFiber0 *
    representativeNodeFiber1 *
    representativeNodeFiber0⁻¹

/-- Actual fiber-product lift of compact permutation node 3. -/
noncomputable def representativeNodeFiber3 : localFiberSubgroup :=
  representativeNodeFiber0 *
    representativeNodeFiber0 *
    representativeNodeFiber1 *
    representativeNodeFiber0⁻¹ *
    representativeNodeFiber0⁻¹

/-- Actual fiber-product lift of compact permutation node 4. -/
noncomputable def representativeNodeFiber4 : localFiberSubgroup :=
  representativeNodeFiber1 *
    representativeNodeFiber3 *
    representativeNodeFiber1

/-- Actual fiber-product lift of compact permutation node 5. -/
noncomputable def representativeNodeFiber5 : localFiberSubgroup :=
  representativeNodeFiber3 *
    representativeNodeFiber1 *
    representativeNodeFiber3

/-- Actual fiber-product lift of compact permutation node 6. -/
noncomputable def representativeNodeFiber6 : localFiberSubgroup :=
  representativeNodeFiber1 *
    representativeNodeFiber2 *
    representativeNodeFiber3 *
    representativeNodeFiber2 *
    representativeNodeFiber1

/-- Actual fiber-product lift of compact permutation node 7. -/
noncomputable def representativeNodeFiber7 : localFiberSubgroup :=
  representativeNodeFiber2 *
    representativeNodeFiber3 *
    representativeNodeFiber2 *
    representativeNodeFiber3 *
    representativeNodeFiber1 *
    representativeNodeFiber2

/-- Actual fiber-product lift of compact permutation node 8. -/
noncomputable def representativeNodeFiber8 : localFiberSubgroup :=
  representativeNodeFiber4 *
    representativeNodeFiber7 *
    representativeNodeFiber4

/-- Actual fiber-product lift of compact permutation node 9. -/
noncomputable def representativeNodeFiber9 : localFiberSubgroup :=
  representativeNodeFiber5 *
    representativeNodeFiber8 *
    representativeNodeFiber5 *
    representativeNodeFiber8⁻¹ *
    representativeNodeFiber5

/-- Actual fiber-product lift of compact permutation node 10. -/
noncomputable def representativeNodeFiber10 : localFiberSubgroup :=
  representativeNodeFiber7 *
    representativeNodeFiber4 *
    representativeNodeFiber7⁻¹ *
    representativeNodeFiber8⁻¹ *
    representativeNodeFiber8⁻¹ *
    representativeNodeFiber9

/-- Actual fiber-product lift of compact permutation node 11. -/
noncomputable def representativeNodeFiber11 : localFiberSubgroup :=
  representativeNodeFiber0 *
    representativeNodeFiber0 *
    representativeNodeFiber0 *
    representativeNodeFiber1 *
    representativeNodeFiber0⁻¹ *
    representativeNodeFiber0⁻¹ *
    representativeNodeFiber0⁻¹ *
    representativeNodeFiber3 *
    representativeNodeFiber2 *
    representativeNodeFiber1 *
    representativeNodeFiber3 *
    representativeNodeFiber2 *
    representativeNodeFiber6 *
    representativeNodeFiber7⁻¹ *
    representativeNodeFiber5 *
    representativeNodeFiber6 *
    representativeNodeFiber4 *
    representativeNodeFiber8⁻¹ *
    representativeNodeFiber8⁻¹ *
    representativeNodeFiber5 *
    representativeNodeFiber8⁻¹ *
    representativeNodeFiber9 *
    representativeNodeFiber10⁻¹

/-- Actual fiber-product lift of compact permutation node 12. -/
noncomputable def representativeNodeFiber12 : localFiberSubgroup :=
  representativeNodeFiber10 *
    representativeNodeFiber11 *
    representativeNodeFiber10⁻¹

/-- Actual fiber-product lift of compact permutation node 13. -/
noncomputable def representativeNodeFiber13 : localFiberSubgroup :=
  representativeNodeFiber9 *
    representativeNodeFiber11 *
    representativeNodeFiber9

/-- Actual fiber-product lift of compact permutation node 14. -/
noncomputable def representativeNodeFiber14 : localFiberSubgroup :=
  representativeNodeFiber10 *
    representativeNodeFiber13 *
    representativeNodeFiber10⁻¹

/-- The fifteen actual compact permutation lifts, retaining both spin and Leech components. -/
noncomputable def representativeNodeFiber : Fin 15 → localFiberSubgroup :=
  ![representativeNodeFiber0,
    representativeNodeFiber1,
    representativeNodeFiber2,
    representativeNodeFiber3,
    representativeNodeFiber4,
    representativeNodeFiber5,
    representativeNodeFiber6,
    representativeNodeFiber7,
    representativeNodeFiber8,
    representativeNodeFiber9,
    representativeNodeFiber10,
    representativeNodeFiber11,
    representativeNodeFiber12,
    representativeNodeFiber13,
    representativeNodeFiber14]

/-- Evaluation of a signed compact-node reference in the actual fiber product. -/
noncomputable def representativeNodeLetterFiber (a : RepresentativeNodeLetter) :
    localFiberSubgroup :=
  if a.2 then (representativeNodeFiber a.1)⁻¹ else representativeNodeFiber a.1

/-- The actual compact target word, with its explicit source cocode correction on the left. -/
noncomputable def representativePermutationFiber (n : Fin 83) : localFiberSubgroup :=
  localFiberIncl (sourceQCocode (golayLabelCoefficients (representativePermutationCorrection n))) *
    ((representativePermutationWord n).map representativeNodeLetterFiber).prod

/-- The compact target word projected to the actual simultaneous-sign quotient H. -/
noncomputable def representativePermutationLocal (n : Fin 83) : H :=
  QuotientGroup.mk' localDiagonalSubgroup (representativePermutationFiber n)

/-- The literal compact target permutation word in the named generated group G. -/
noncomputable def representativePermutationGenerated (n : Fin 83) : ↥G :=
  localIntoGenerated (representativePermutationLocal n)

/-- The source central-code sign converted without losing its high bit. -/
def representativeSourceSign (negative : Bool) : ZMod 2 := if negative then 1 else 0

/-- Every literal source tag is interpreted using the frozen actual generator convention.
In particular source p lifts are inverse fiber lifts and source y uses source triality. -/
noncomputable def representativeSourceLetterGenerated : RepresentativeSourceLetter → ↥G
  | .x d negative => sourceGeneratedCode d (representativeSourceSign negative)
  | .y d negative => y555NortonActualY d (representativeSourceSign negative)
  | .d δ => sourceGeneratedCocode (golayLabelCoefficients δ)
  | .p n => representativePermutationGenerated n
  | .l power => if power = 0 then 1 else if power = 1 then xiSpinGenerated⁻¹
      else xiSpinGenerated
  | .t power => monsterSourceTriality ^ power.val

/-- The twelve literal source sample words, as actual elements of G.
No assertion that their descriptive source labels classify all axes is made. -/
noncomputable def representativeAxisWord (k : Fin 12) : ↥G :=
  ((representativeAxisLetters k).map representativeSourceLetterGenerated).prod

/-- The ten literal source feasible sample words, as actual elements of G.
No assertion of feasibility, class membership, or orbit coverage is made here. -/
noncomputable def representativeFeasibleWord (k : Fin 10) : ↥G :=
  ((representativeFeasibleLetters k).map representativeSourceLetterGenerated).prod

/-- The identity sample word for the source positive-axis label is literally the identity. -/
theorem representativeAxisWord_zero : representativeAxisWord 0 = 1 := rfl

/-- The first feasible sample word is literally the identity. -/
theorem representativeFeasibleWord_zero : representativeFeasibleWord 0 = 1 := rfl

/-- The second feasible sample word is the frozen source triality generator. -/
theorem representativeFeasibleWord_one : representativeFeasibleWord 1 = monsterSourceTriality := by
  simp [representativeFeasibleWord, representativeFeasibleLetters,
    representativeSourceLetterGenerated]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
