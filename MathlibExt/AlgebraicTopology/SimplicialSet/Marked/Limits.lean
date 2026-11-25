/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Basic
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Limits of the original marked simplicial-set carriers

The underlying limit cone is marked by the intersection of the inverse
images of every original projection marking. This constructs a genuine
marked limit for any shape for which the underlying limit exists.
Forgetting preserves limits by the actual minimal-marking adjunction;
it is not asserted to reflect arbitrary markings or create limits.
-/

noncomputable section
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet.Marked

variable {J : Type w} [Category.{v} J] (F : J ⥤ Marked.{u})

/-- Mark the original cone point by exactly the edges marked by every projection. -/
def limitCone (c : Cone (F ⋙ forget)) : Cone F where
  pt :=
    { toSSet := c.pt
      marking := {a | ∀ j : J, (c.π.app j).app (op ⦋1⦌) a ∈ (F.obj j).marking}
      degenerate_mem x := by
        intro j
        let π : c.pt ⟶ (F.obj j).toSSet := c.π.app j
        change π.app (op ⦋1⦌) (c.pt.σ 0 x) ∈ (F.obj j).marking
        exact (σ_naturality_apply π 0 x).symm ▸ (F.obj j).degenerate_mem (π.app _ x) }
  π :=
    { app j := ⟨c.π.app j, fun ha => ha j⟩
      naturality _ _ f := Hom.ext (c.π.naturality f) }

/-- Every original projection retains exactly its original simplicial map. -/
@[simp] theorem limitCone_π_hom (c : Cone (F ⋙ forget)) (j : J) :
    ((limitCone F c).π.app j).hom = c.π.app j := rfl

/-- The canonical projection marking makes an actual underlying limit a genuine marked limit. -/
def limitConeIsLimit {c : Cone (F ⋙ forget)} (hc : IsLimit c) : IsLimit (limitCone F c) where
  lift s :=
    { hom := hc.lift (forget.mapCone s)
      preserve {a} ha := by
        intro j
        have he := congrArg (fun f => f.app (op ⦋1⦌) a) (hc.fac (forget.mapCone s) j)
        change (c.π.app j).app _ ((hc.lift (forget.mapCone s)).app _ a) =
          (s.π.app j).hom.app _ a at he
        exact he.symm ▸ (s.π.app j).preserve ha }
  fac s j := Hom.ext (hc.fac (forget.mapCone s) j)
  uniq s m hm := by
    apply Hom.ext
    apply hc.uniq (forget.mapCone s) m.hom
    intro j
    exact congrArg Hom.hom (hm j)

/-- Underlying limits give actual marked limits, without changing the shape universes. -/
instance hasLimit [HasLimit (F ⋙ forget)] : HasLimit F :=
  ⟨⟨{ cone := limitCone F (limit.cone (F ⋙ forget)),
       isLimit := limitConeIsLimit F (limit.isLimit (F ⋙ forget)) }⟩⟩

/-- The original forgetful functor preserves limits by its genuine right-adjoint structure. -/
theorem forgetPreservesLimits : PreservesLimitsOfSize.{v, w} forget.{u} :=
  minimalAdjunction.rightAdjoint_preservesLimits

end SSet.Marked
