/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanSpectralSequence
public import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKanChains
public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationLift

/-!
# The group-completion Bousfield--Kan spectral sequence

For a small additive category, the cofibered projection from additive
`S⁻¹S` to the one-coordinate translation category gives a convergent
Bousfield--Kan homology spectral sequence.  Its second page is category
homology of the translation category with strict-fiber homology
coefficients, and its abutment is the homology of the nerve of `S⁻¹S`.

Objects and morphisms of the input category lie in one common universe.
The quotient arrows contain stabilizer objects and still lie in that universe.
The construction retains the original translation projection and all of its
strict-fiber coefficient maps at every common universe level.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe u

namespace CategoryTheory
namespace SInverseS

/-- Canonical common-universe additive colimits for the group-completion BK construction. -/
noncomputable local instance groupCompletionBKAdditiveColimits :
    HasColimitsOfSize.{u, u} AddCommGrpCat.{u} :=
  { has_colimits_of_shape := fun (J : Type u) (hJ : Category.{u} J) => by
      letI : Category.{u} J := hJ
      letI : Small.{u} J := small_self J
      exact AddCommGrpCat.hasColimitsOfShape.{u, u, u} (J := J) }

/-- Canonical common-universe additive coproducts for the group-completion BK construction. -/
noncomputable local instance groupCompletionBKAdditiveCoproducts :
    HasCoproducts.{u} AddCommGrpCat.{u} :=
  fun (J : Type u) => by
    let _ : HasColimitsOfSize.{u, u} AddCommGrpCat.{u} := groupCompletionBKAdditiveColimits
    exact HasColimitsOfSize.has_colimits_of_shape (C := AddCommGrpCat.{u}) (J := Discrete J)

variable (C : Type u) [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- The Bousfield--Kan spectral sequence associated to the cofibered
translation projection `S⁻¹S(C) ⟶ ⟨S,S⟩`. -/
noncomputable abbrev translationBKHomologySpectralSequence
    (R : AddCommGrpCat.{u}) :=
  SSet.bkHomologySpectralSequence R
    (SSet.rightCommaNerveDiagram
      (translationProjection (C := C)))

/-- The second page of the translation-projection spectral sequence is
category homology with coefficients in the homology of its strict fibers. -/
noncomputable def translationBKSecondPageIso
    (R : AddCommGrpCat.{u}) (p q : ℕ) :
    ((translationBKHomologySpectralSequence C R).page 2).X (p, q) ≅
      Functor.IsCofibered.fiberHomologyCategoryHomology
        (p := translationProjection (C := C)) AddCommGrpCat.{u} R p q :=
  Functor.IsCofibered.cofiberedBKSecondPageIso
    (f := translationProjection (C := C)) R p q

/-- Finite filtration on the total homology to which the translation BK
spectral sequence converges. -/
noncomputable abbrev translationBKTotalHomologyFiltration
    (R : AddCommGrpCat.{u}) (n : ℕ) :=
  SSet.bkTotalHomologyFiltration R
    (SSet.rightCommaNerveDiagram
      (translationProjection (C := C))) n

/-- Associated graded pieces of the total homology filtration. -/
noncomputable abbrev translationBKTotalHomologyGradedPiece
    (R : AddCommGrpCat.{u}) (p q : ℕ) :=
  SSet.bkTotalHomologyGradedPiece R
    (SSet.rightCommaNerveDiagram
      (translationProjection (C := C))) p q

/-- Every sufficiently late page of the translation BK spectral sequence
is the corresponding associated graded piece of total homology. -/
noncomputable def translationBKStablePageGradedIso
    (R : AddCommGrpCat.{u}) (r : ℤ) (hr : 1 ≤ r) (p q : ℕ)
    (hlower : (p : ℤ) + 1 ≤ r) (hupper : (q : ℤ) + 2 ≤ r) :
    ((translationBKHomologySpectralSequence C R).page r).X (p, q) ≅
      translationBKTotalHomologyGradedPiece C R p q :=
  SSet.bkStablePageGradedIso R
    (SSet.rightCommaNerveDiagram
      (translationProjection (C := C)))
    r hr p q hlower hupper

/-- The abutment total homology is canonically the simplicial homology of
the additive `S⁻¹S` nerve. -/
noncomputable def translationBKAbutmentHomologyIso
    (R : AddCommGrpCat.{u}) (n : ℕ) :
    (SSet.bkAlternatingTotalComplex AddCommGrpCat.{u} R
      (SSet.rightCommaNerveDiagram
        (translationProjection (C := C)))).homology n ≅
      ((nerve (Pair C)).chainComplex R).homology n :=
  SSet.rightCommaBKTotalSourceHomologyIso_addCommGrp R
    (translationProjection (C := C)) n

end SInverseS
end CategoryTheory

end
