/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MeromorphicCompletionRefinements

/-!
# Identity of generic meromorphic completion refinement

An identity map of pole-chart spaces induces the identity on the localized completed ring.

Source: Fargues--Scholze, arXiv:2102.13459v4, Sections III.3 and VI.1;
Beauville--Laszlo descent.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MeromorphicTorsorCompletion

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry
open AnalyticGroupTorsorSites AnalyticBundleModifications
open AnalyticMeromorphicCoordinates MeromorphicHeckeModels MeromorphicCompletionRefinements

/-- The identity refinement induces the identity of localized completed rings: for a prime $p$, a
field $E$, a map $d : D \to X$ of $E$-spaces with a puncture `U` and a pole chart `Q` at `U`, a
refinement $r$ of `Q` by itself whose map of chart spaces is the identity, and a coefficient
refinement `R` for $r$, the induced map of the completed chart ring localized at the formal
parameter (`genericMap`) is the identity. -/
public theorem genericRefinement_identity (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] {X D : ESpace p E}
    (d : D ⟶ X) (U : Puncture p E d) (Q : PoleChart p E d U)
    (r : PoleRefinement p E d U Q Q) (hr : r.map = 𝟙 Q.space)
    (R : CoefficientRefinement p E d U Q Q r) :
    genericMap p E d U Q Q r R = RingHom.id _
    := by
  have hs : sectionMap p E r.map = RingHom.id _ := by
    rw [hr]
    change ((globalRings p).map (𝟙 (Opposite.op Q.space.left))).hom = _
    rw [_root_.CategoryTheory.Functor.map_id]
    rfl
  have hp : positiveMap p E d U Q Q r R.powers R.finite = RingHom.id _ := by
    apply RingHom.ext
    intro a
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [positiveMap_finite]
    change (Ideal.quotientMap _ (sectionMap p E r.map) (R.powers n))
      (AdicCompletion.evalₐ (chartIdeal p E d U Q) n a) =
      AdicCompletion.evalₐ (chartIdeal p E d U Q) n a
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ (chartIdeal p E d U Q) n a)
    rw [← hb, Ideal.quotientMap_mk, hs]
    rfl
  apply IsLocalization.ringHom_ext (Submonoid.powers (formalParameter p E d U Q))
  apply RingHom.ext
  intro a
  change genericMap p E d U Q Q r R (algebraMap _ (GenericRing p E d U Q) a) =
    algebraMap _ (GenericRing p E d U Q) a
  rw [genericMap_coefficients, hp, RingHom.id_apply]

end WantedExt.AlgebraicGeometry.MeromorphicTorsorCompletion
