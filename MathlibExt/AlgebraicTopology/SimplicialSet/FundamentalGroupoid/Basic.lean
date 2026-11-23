/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
See NOTICE in the repository root for the original Mathlib attribution.
-/

module

-- BACKPORT: Seven comparison helpers from Mathlib PR #42587,
-- head `d7757b4d8106b7e199293d833742c1b82dd38a4d`,
-- `Mathlib/AlgebraicTopology/SimplicialSet/FundamentalGroupoid/Basic.lean`,
-- blob `ee7aba11d4733c337034ee3d5ad5406ee9bd2ade`.
-- The upstream fundamental-groupoid core is reused; see `BACKPORTS.md`.

public import Mathlib.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic

/-!
# Fundamental-groupoid functor and transformation comparisons

Vertex components and naturality on original edges construct natural transformations and natural
isomorphisms from fundamental groupoids into an arbitrary category. The comparison helpers also
retain an explicit isomorphism from a two-truncation isomorphism and natural isomorphisms for
identity, composition and equal simplicial maps. The fundamental groupoids and their basic
functors are imported from pinned Mathlib.

The compatibility scope against Mathlib 4.35.0 (`56a005855ea17e0b0958f73ec801ae140b0a1679`) and
its removal conditions are recorded in `BACKPORTS.md`.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial SimplicialObject.Truncated

namespace SSet

variable {X Y Z : SSet.{u}}

namespace FundamentalGroupoid

section

variable {D : Type*} [Category* D] {F G : FundamentalGroupoid X ⥤ D}

@[ext]
lemma natTrans_ext {f g : F ⟶ G}
    (h : ∀ (x : X _⦋0⦌), f.app (mk x) = g.app (mk x)) : f = g := by
  ext
  apply h

open MorphismProperty in
/-- Constructor for natural transformations for functors from the
fundamental groupoid of a simplicial set. -/
@[simps!]
def natTransMk (app : ∀ (x : X _⦋0⦌), F.obj (mk x) ⟶ G.obj (mk x))
    (naturality : ∀ {x y : X _⦋0⦌} (e : Edge x y),
      F.map (homMk e) ≫ app y = app x ≫ G.map (homMk e) := by cat_disch) : F ⟶ G where
  app x := app x.pt
  naturality := by
    let φ (x : FundamentalGroupoid X) := app x.pt
    intro _ _ f
    change naturalityProperty φ f
    induction f with
    | homMk e => exact naturality e
    | inv f hf => exact (naturalityProperty.stableUnderInverse φ) (asIso f) hf
    | comp f g hf hg => exact comp_mem _ _ _ hf hg

/-- Constructor for natural isomorphisms for functors from the
fundamental groupoid of a simplicial set. -/
@[simps!]
def natIsoMk (app : ∀ (x : X _⦋0⦌), F.obj (mk x) ≅ G.obj (mk x))
    (naturality : ∀ {x y : X _⦋0⦌} (e : Edge x y),
      F.map (homMk e) ≫ (app y).hom =
        (app x).hom ≫ G.map (homMk e) := by cat_disch) : F ≅ G :=
  NatIso.ofComponents (fun x ↦ app x.pt)
    (fun f ↦ (natTransMk _ naturality).naturality f)

end


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
  eqToIso (by rw[h])


end SSet
