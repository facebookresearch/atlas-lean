/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MeromorphicCompletionRefinements
import MathlibExt.AlgebraicGeometry.MeromorphicTorsorCompletionPositiveRefinementComp
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Composition of generic refinement maps

The positive and generic refinement maps of a composite pole-chart refinement, whose chart map
is the composite of the factors, are the composites of the factors' maps. Source:
Fargues--Scholze, arXiv:2102.13459v4, Sections III.3 and VI.1; Beauville--Laszlo descent.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MeromorphicTorsorCompletion

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open MathlibExt.AlgebraicGeometry
open AnalyticGroupTorsorSites AnalyticBundlePrestackModels AnalyticBundleModifications
open AnalyticMeromorphicCoordinates MeromorphicHeckeModels AffinoidTorsorAlgebraizationModels
open CompletedTorsorSourceFrames MeromorphicCompletionRefinements
open MeromorphicCoefficientCompletion

/-- Refinement maps of localized completed rings compose: for a prime $p$, a field $E$, a map
$d : D \to X$ of $E$-spaces with a puncture `U` and refinements $r$ of a pole chart `Q` by `Q'`, $s$
of `Q'` by `Q''` and $t$ of `Q` by `Q''` whose maps of chart spaces satisfy $t = r \circ s$, and
coefficient refinements `R`, `S`, `T` for them, the induced map of completed chart rings localized
at the formal parameters (`genericMap`) for $t$ is the one for $r$ followed by the one for $s$. -/
public theorem genericRefinement_comp (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] {X D : ESpace p E}
    (d : D ⟶ X) (U : Puncture p E d) (Q Q' Q'' : PoleChart p E d U)
    (r : PoleRefinement p E d U Q Q') (s : PoleRefinement p E d U Q' Q'')
    (t : PoleRefinement p E d U Q Q'') (ht : t.map = s.map ≫ r.map)
    (R : CoefficientRefinement p E d U Q Q' r)
    (S : CoefficientRefinement p E d U Q' Q'' s)
    (T : CoefficientRefinement p E d U Q Q'' t) :
    genericMap p E d U Q Q'' t T =
      (genericMap p E d U Q' Q'' s S).comp (genericMap p E d U Q Q' r R) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (formalParameter p E d U Q))
  apply RingHom.ext
  intro a
  simp only [RingHom.comp_apply, genericMap_coefficients]
  have hPos : positiveMap p E d U Q Q'' t T.powers T.finite a =
      positiveMap p E d U Q' Q'' s S.powers S.finite
        (positiveMap p E d U Q Q' r R.powers R.finite a) := by
    rw [positiveRefinement_comp p E d U Q Q' Q'' r s t ht R S T]
    rfl
  rw [hPos]

end WantedExt.AlgebraicGeometry.MeromorphicTorsorCompletion
