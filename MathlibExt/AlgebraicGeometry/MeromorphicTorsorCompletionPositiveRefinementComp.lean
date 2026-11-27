/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MeromorphicCompletionRefinements

/-!
# Composition of positive refinement maps

The completed coefficient maps of pole-chart refinements respect composition.
Source: Fargues--Scholze,
arXiv:2102.13459v4, Sections III.3 and VI.1; Beauville--Laszlo descent.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MeromorphicTorsorCompletion

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry
open AnalyticGroupTorsorSites AnalyticBundleModifications
open AnalyticMeromorphicCoordinates MeromorphicCompletionRefinements

/-- Refinement maps of completed rings compose: for a prime $p$, a field $E$, a map $d : D \to X$ of
$E$-spaces with a puncture `U` and refinements $r$ of a pole chart `Q` by `Q'`, $s$ of `Q'` by `Q''`
and $t$ of `Q` by `Q''` whose maps of chart spaces satisfy $t = r \circ s$, and coefficient
refinements `R`, `S`, `T` for them, the induced map of completed chart rings (`positiveMap`) for $t$
is the one for $r$ followed by the one for $s$. -/
public theorem positiveRefinement_comp (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] {X D : ESpace p E}
    (d : D ⟶ X) (U : Puncture p E d) (Q Q' Q'' : PoleChart p E d U)
    (r : PoleRefinement p E d U Q Q') (s : PoleRefinement p E d U Q' Q'')
    (t : PoleRefinement p E d U Q Q'') (ht : t.map = s.map ≫ r.map)
    (R : CoefficientRefinement p E d U Q Q' r)
    (S : CoefficientRefinement p E d U Q' Q'' s)
    (T : CoefficientRefinement p E d U Q Q'' t) :
    positiveMap p E d U Q Q'' t T.powers T.finite =
      (positiveMap p E d U Q' Q'' s S.powers S.finite).comp
        (positiveMap p E d U Q Q' r R.powers R.finite)
    := by
  apply RingHom.ext
  intro a
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [RingHom.comp_apply, positiveMap_finite, positiveMap_finite]
  simp only [finiteMap, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [positiveMap_finite]
  simp only [finiteMap, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (chartIdeal p E d U Q) n a)
  rw [← hb]
  simp only [Ideal.quotientMap_mk]
  congr 1
  rw [ht]
  change ((globalRings p).map (s.map.left ≫ r.map.left).op).hom b =
    ((globalRings p).map s.map.left.op).hom
      (((globalRings p).map r.map.left.op).hom b)
  rw [op_comp, Functor.map_comp]
  rfl

end WantedExt.AlgebraicGeometry.MeromorphicTorsorCompletion
