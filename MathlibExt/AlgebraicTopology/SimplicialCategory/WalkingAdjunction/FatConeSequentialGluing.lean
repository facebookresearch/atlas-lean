/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.CategoricalSequentialColimits
import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.JoinPointMonomorphisms
import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.FatConeConnectedColimits
import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.FatConeMonomorphisms

/-!
# Whole fat-cone comparison on monic sequential colimits

Both actual cone functors preserve the original connected colimit.
Their transition maps are monic by the proved fat-cone and point-join
preservation theorems. The named Joyal sequence theorem applies to
the identical whole comparison natural transformation.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace SSet.WalkingAdjunction.FatCone

/-- Comparison on all original finite stages induces the actual comparison on their supplied monic sequential colimit, retaining every original colimit leg. -/
theorem toJoin_of_sequence_isColimit
    (F : ℕ ⥤ SSet.{u})
    (hstep : ∀ n : ℕ, Mono (F.map (homOfLE (n.le_add_right 1))))
    (hF : ∀ n, categoricalEquivalences (toJoin (F.obj n)))
    {c : Cocone F} (hc : IsColimit c) : categoricalEquivalences (toJoin c.pt) := by
  have hf : ∀ n : ℕ, Mono ((F ⋙ underlyingFunctor).map (homOfLE (n.le_add_right 1))) := by
    intro n
    let _ : Mono (F.map (homOfLE (n.le_add_right 1))) := hstep n
    change Mono (map (F.map (homOfLE (n.le_add_right 1))))
    exact inferInstance
  have hg : ∀ n : ℕ, Mono ((F ⋙ joinFunctor).map (homOfLE (n.le_add_right 1))) := by
    intro n
    let _ : Mono (F.map (homOfLE (n.le_add_right 1))) := hstep n
    change Mono ((join.map (F.map (homOfLE (n.le_add_right 1)))).app (Δ[0] : SSet.{u}))
    exact mono_join_point _
  exact categoricalEquivalences_of_sequence_isColimits
    (Functor.whiskerLeft F underlyingComparison) hf hg hF (mapIsColimit hc) (joinMapIsColimit hc)
    (toJoin c.pt) (fun n => toJoin_naturality (c.ι.app n))

end SSet.WalkingAdjunction.FatCone
