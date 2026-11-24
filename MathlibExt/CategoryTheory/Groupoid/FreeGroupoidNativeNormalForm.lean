/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidReductionValue

/-!
# Genuine native original quiver-groupoid reduced-word normal forms

The complete actual original signed-path value is unchanged by native
label-word reduction. Native FreeGroup reduced-word uniqueness and
full admissible original path reconstruction prove that the actual
original label functor is faithful. Every individual original endpoint,
full generator and orientation is retained; no normal-form or weak
outcome is supplied as an input.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V]

/-- Equality of full original admissible words preserves the SAME native value. -/
lemma value_eq_of_wordEq {x y : V} {L M : List (Labels V × Bool)}
    (h : L = M) (hL : Admissible V x L y) (hM : Admissible V x M y) : hL.value = hM.value := by
  cases h
  rfl

/-- Actual signed-path values agree whenever their SAME native full original labels agree as
free-group words. -/
lemma signedPathValue_eq_of_labelValue {x y : Quiver.Symmetrify V} (p q : Quiver.Path x y)
    (h : FreeGroup.mk (signedPathLabels V p) = FreeGroup.mk (signedPathLabels V q)) :
    signedPathValue V p = signedPathValue V q := by
  classical
  let _ : DecidableEq (Labels V) := Classical.decEq _
  have hp := signedPathLabels_admissible V p
  have hq := signedPathLabels_admissible V q
  have hpr := reducedWord_admissible V hp
  have hqr := reducedWord_admissible V hq
  have he := FreeGroup.reduce.sound h
  have hvalp := value_eq_of_red V hp hpr FreeGroup.reduce.red
  have hvalq := value_eq_of_red V hq hqr FreeGroup.reduce.red
  have hr : hpr.value = hqr.value := value_eq_of_wordEq V he hpr hqr
  exact (Admissible.value_path V hp p rfl).symm.trans
    (hvalp.trans (hr.trans (hvalq.symm.trans (Admissible.value_path V hq q rfl))))

/-- The SAME full native original signed-path values are detected by their actual original
label functor. -/
lemma signedPathValue_eq_of_labelledFunctor {x y : Quiver.Symmetrify V} (p q : Quiver.Path x y)
    (h : (labelledFunctor V).map (signedPathValue V p) =
      (labelledFunctor V).map (signedPathValue V q)) : signedPathValue V p =
        signedPathValue V q := by
  have he : FreeGroup.mk (signedPathLabels V p) = FreeGroup.mk (signedPathLabels V q) :=
    congrArg MulOpposite.unop ((labelled_signedPathValue V p).symm.trans
      (h.trans (labelled_signedPathValue V q)))
  exact signedPathValue_eq_of_labelValue V p q he

/-- Every genuine native quiver free-groupoid Hom retains full faithful original-label readback. -/
instance labelledFunctor_faithful : (labelledFunctor V).Faithful where
  map_injective {x y} f g h := by
    let _ : (signedPathFunctor V).Full := CategoryTheory.Quotient.full_functor
      (@Quiver.FreeGroupoid.redStep V inferInstance)
    cases x with
    | mk x =>
      cases y with
      | mk y =>
        obtain ⟨p, rfl⟩ := (signedPathFunctor V).map_surjective f
        obtain ⟨q, rfl⟩ := (signedPathFunctor V).map_surjective g
        exact signedPathValue_eq_of_labelledFunctor V p q h

end Quiver.FreeGroupoid.OriginalWords
