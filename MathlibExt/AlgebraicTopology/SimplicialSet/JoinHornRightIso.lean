/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinHornRightZeroIso

/-!
# The right boundary--horn pushout is a standard horn
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace SSet
namespace JoinHorn.Internal

/-- The canonical right-oriented boundary--horn pushout isomorphism, including
its zero-dimensional boundary case. -/
@[no_expose]
noncomputable def joinBoundaryHornRightPointIso (p q : ℕ)
    (j : Fin (q + 2)) :
    (joinBoundaryHornRightPushoutObjObj.{u} p q j).pt ≅
      (horn (p + (q + 1) + 1) (rightJoinHornIndex p q j) : SSet.{u}) :=
  match p with
  | 0 => joinBoundaryHornRightPointIsoZero q j
  | p + 1 => joinBoundaryHornRightPointIsoSucc p q j

/-- The point isomorphism retains the first pushout coprojection strictly. -/
@[reassoc]
lemma joinBoundaryHornRightPointIso_hom_inl (p q : ℕ)
    (j : Fin (q + 2)) :
    (joinBoundaryHornRightPushoutObjObj.{u} p q j).inl ≫
        (joinBoundaryHornRightPointIso p q j).hom =
      joinBoundaryHornRightFactorMap p q j := by
  obtain _ | p := p
  · exact joinBoundaryHornRightPointIsoZero_hom_inl q j
  · exact joinBoundaryHornRightPushout_inl_toHorn (p + 1) q j

/-- The point isomorphism retains the second pushout coprojection strictly. -/
@[reassoc]
lemma joinBoundaryHornRightPointIso_hom_inr (p q : ℕ)
    (j : Fin (q + 2)) :
    (joinBoundaryHornRightPushoutObjObj.{u} p q j).inr ≫
        (joinBoundaryHornRightPointIso p q j).hom =
      joinBoundaryHornRightBoundaryFactorMap p q j := by
  obtain _ | p := p
  · exact joinBoundaryHornRightPointIsoZero_hom_inr q j
  · exact joinBoundaryHornRightPushout_inr_toHorn (p + 1) q j

/-- The point isomorphism retains the final inclusion in the joined simplex. -/
@[reassoc]
lemma joinBoundaryHornRightPointIso_hom_ι (p q : ℕ)
    (j : Fin (q + 2)) :
    (joinBoundaryHornRightPointIso.{u} p q j).hom ≫
        (horn (p + (q + 1) + 1) (rightJoinHornIndex p q j)).ι =
      (joinBoundaryHornRightPushoutObjObj p q j).ι ≫
        (joinStdSimplexIso p (q + 1)).hom := by
  obtain _ | p := p
  · exact joinBoundaryHornRightPointIsoZero_hom_ι q j
  · exact joinBoundaryHornRightToHorn_ι (p + 1) q j

end JoinHorn.Internal
end SSet
