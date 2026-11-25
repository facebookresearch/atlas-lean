/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
See NOTICE in the repository root for the original Mathlib attribution.
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic

/-!
# Fundamental-groupoid functor comparisons

The identity and composition comparisons use Mathlib's constructor for
natural isomorphisms on the fundamental groupoid. A map whose two-truncation
is an isomorphism also induces an isomorphism of groupoids.

The comparison statements originate in Mathlib PR #42587.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial SimplicialObject.Truncated

namespace SSet

variable {X Y Z : SSet.{u}}

namespace FundamentalGroupoid

variable {D : Type*} [Category* D] {F G : FundamentalGroupoid X ⥤ D}

@[ext]
lemma natTrans_ext {f g : F ⟶ G}
    (h : ∀ (x : X _⦋0⦌), f.app (mk x) = g.app (mk x)) : f = g := by
  ext
  apply h

end FundamentalGroupoid

open FundamentalGroupoid

/-- The isomorphism of fundamental groupoids that is induced
by a morphism of simplicial sets which induces an isomorphism
on the `2`-truncations. -/
noncomputable def isoCatMapFundamentalGroupoid (f : X ⟶ Y)
    (hf : IsIso ((truncation 2).map f) := by infer_instance) :
    IsoCat (FundamentalGroupoid X) (FundamentalGroupoid Y) :=
  Truncated.mapIsoFundamentalGroupoid (asIso ((truncation 2).map f))


variable (X) in
/-- The identity morphism of a simplicial set acts by the
identity functor on the fundamental groupoid. -/
@[simps! hom_app inv_app]
def mapFundamentalGroupoidId :
    mapFundamentalGroupoid (𝟙 X) ≅ 𝟭 _ :=
  FundamentalGroupoid.natIsoMk (fun x ↦ Iso.refl _)

/-- The composition of two morphisms of simplicial sets acts
on the fundamental groupoid by the composition of the
corresponding functors. -/
@[simps! hom_app inv_app]
def mapFundamentalGroupoidComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    mapFundamentalGroupoid f ⋙ mapFundamentalGroupoid g ≅
      mapFundamentalGroupoid (f ≫ g) :=
  FundamentalGroupoid.natIsoMk (fun x ↦ Iso.refl _)

/-- Two identical morphisms induce isomorphic functors
on the fundamental groupoid. -/
@[simps!]
def congrMapFundamentalGroupoidOfEq {f g : X ⟶ Y} (h : f = g) :
    mapFundamentalGroupoid f ≅ mapFundamentalGroupoid g :=
  congrArg SSet.mapFundamentalGroupoid h |> eqToIso

end SSet
