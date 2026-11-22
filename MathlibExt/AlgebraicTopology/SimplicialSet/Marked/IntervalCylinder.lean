/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.InternalHomAdjunction
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SmallLimits
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ParameterMapMonomorphisms
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorialCylinder

/-!
# The native fully marked interval cylinder on original marked carriers

Multiply the original marked object by the original fully marked interval.
Both endpoint maps and the source projection retain their literal original
simplices. The existing marked internal-Hom adjunction proves preservation
of original-universe colimits, and native component injection proves
preservation of monomorphisms. No marked-model structure is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite HomotopicalAlgebra
open scoped Simplicial

namespace SSet.Marked

/-- The actual original interval endpoint is the marked constant original vertex map. -/
def intervalCylinderEndpoint (X : Marked.{u}) (ε : Fin 2) : X ⟶ prod X (max (Δ[1] : SSet.{u})) :=
  prodLift (𝟙 X) (toMax (SSet.const (SSet.stdSimplex.obj₀Equiv.symm ε)))

/-- The same original endpoint is natural in every original marked map. -/
theorem intervalCylinderEndpoint_natural {X Y : Marked.{u}} (f : X ⟶ Y) (ε : Fin 2) :
    f ≫ intervalCylinderEndpoint Y ε = intervalCylinderEndpoint X ε ≫ prodMap f (𝟙 (max (Δ[1] : SSet.{u}))) := by
  apply Hom.ext
  rfl

/-- Projection retains the original source exactly at either endpoint. -/
theorem intervalCylinderEndpoint_projection (X : Marked.{u}) (ε : Fin 2) :
    intervalCylinderEndpoint X ε ≫ prodFst X (max (Δ[1] : SSet.{u})) = 𝟙 X := Hom.ext rfl

/-- The original full marked interval product gives a genuine native functorial precylinder. -/
def intervalCylinder : Precylinder (𝟭 Marked.{u}) where
  I := prodRight (max (Δ[1] : SSet.{u}))
  i₀ :=
    { app X := intervalCylinderEndpoint X 0
      naturality X Y f := intervalCylinderEndpoint_natural f 0 }
  i₁ :=
    { app X := intervalCylinderEndpoint X 1
      naturality X Y f := intervalCylinderEndpoint_natural f 1 }
  π :=
    { app X := prodFst X (max (Δ[1] : SSet.{u}))
      naturality X Y f := Hom.ext rfl }
  i₀_π := by
    apply NatTrans.ext
    funext X
    exact intervalCylinderEndpoint_projection X 0
  i₁_π := by
    apply NatTrans.ext
    funext X
    exact intervalCylinderEndpoint_projection X 1

/-- Its actual native product endofunctor preserves all original-universe colimits through the existing adjunction. -/
theorem intervalCylinder_preservesColimits : PreservesColimitsOfSize.{u, u} intervalCylinder.{u}.I :=
  (internalHomAdjunction (max (Δ[1] : SSet.{u}))).leftAdjoint_preservesColimits

/-- The original cylinder's whole component map remains monic whenever the original marked map is monic. -/
theorem intervalCylinder_map_mono {X Y : Marked.{u}} (f : X ⟶ Y) [Mono f] :
    Mono (intervalCylinder.{u}.I.map f) := by
  let g : prod X (max (Δ[1] : SSet.{u})) ⟶ prod Y (max (Δ[1] : SSet.{u})) :=
    prodMap f (𝟙 (max (Δ[1] : SSet.{u})))
  let _ : ∀ n : SimplexCategoryᵒᵖ, Mono (g.hom.app n) := fun n =>
    (CategoryTheory.mono_iff_injective _).mpr (by
      intro a b h
      change (f.hom.app n a.1, a.2) = (f.hom.app n b.1, b.2) at h
      have h₁ : a.1 = b.1 := (f.injective_app n.unop)
        (congrArg (fun (q : Y.toSSet.obj n × (Δ[1] : SSet.{u}).obj n) => q.1) h)
      have h₂ : a.2 = b.2 :=
        congrArg (fun (q : Y.toSSet.obj n × (Δ[1] : SSet.{u}).obj n) => q.2) h
      exact Prod.ext h₁ h₂)
  let _ : Mono g.hom := NatTrans.mono_of_mono_app _
  exact Hom.mono_of_underlying g

end SSet.Marked
