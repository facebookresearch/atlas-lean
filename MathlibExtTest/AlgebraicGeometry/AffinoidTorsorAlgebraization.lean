/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AffinoidTorsorAlgebraization

/-!
# Fpqc restriction probes

Pulling a torsor back along the identity, and along two consecutive scheme
maps, preserves the torsor condition.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.AffinoidTorsorAlgebraization

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open MathlibExt.CategoryTheory.SheafTorsorGroupoids
open WittDiscTorsorModels
open WantedExt.AlgebraicGeometry.AffinoidTorsorAlgebraization

-- Pullback along the identity preserves the torsor condition.
theorem isTorsor_actionPullback_id (E : Type) [Field E]
    (G : Over (Spec (.of E))) [GrpObj G] (B : Over (Spec (.of E)))
    (N : Action (topology E B) (groupSheaf E G B))
    (hN : IsTorsor (topology E B) (groupSheaf E G B) N) :
    IsTorsor (topology E B) (groupSheaf E G B)
      ((actionPullback G (𝟙 B)).obj N) :=
  fpqcRestrictionPreservesTorsors E G (𝟙 B) N hN

-- Pullback along two consecutive scheme maps preserves the torsor condition.
theorem isTorsor_actionPullback_comp (E : Type) [Field E]
    (G : Over (Spec (.of E))) [GrpObj G]
    {B C D : Over (Spec (.of E))} (f : B ⟶ C) (g : C ⟶ D)
    (N : Action (topology E D) (groupSheaf E G D))
    (hN : IsTorsor (topology E D) (groupSheaf E G D) N) :
    IsTorsor (topology E B) (groupSheaf E G B)
      ((actionPullback G f).obj ((actionPullback G g).obj N)) :=
  fpqcRestrictionPreservesTorsors E G f _
    (fpqcRestrictionPreservesTorsors E G g N hN)

end MathlibExtTest.AlgebraicGeometry.AffinoidTorsorAlgebraization
