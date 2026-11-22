/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
See NOTICE in the repository root for the original Mathlib attribution.
-/
module

-- BACKPORT: Seven remaining comparison helpers extracted from
-- `Mathlib/AlgebraicTopology/SimplicialSet/FundamentalGroupoid/Basic.lean`
-- in PR `leanprover-community/mathlib4#42587` at commit
-- `d7757b4d8106b7e199293d833742c1b82dd38a4d`,
-- blob `ee7aba11d4733c337034ee3d5ad5406ee9bd2ade`.
-- The fundamental-groupoid core is imported from pinned Mathlib.
-- See `BACKPORTS.md` for provenance and upgrade-removal steps.

public import Mathlib.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic

/-!
# Remaining fundamental-groupoid comparison API

Mathlib 4.35 provides the fundamental groupoids and their basic functors.
The declarations below retain the natural-transformation constructors and
functor comparison isomorphisms from Mathlib PR #42587 at commit
`d7757b4d8106b7e199293d833742c1b82dd38a4d`, blob
`ee7aba11d4733c337034ee3d5ad5406ee9bd2ade`, which remain absent from the pin.
The original copied helper statements and proofs are preserved over the
canonical upstream types. See `BACKPORTS.md` for provenance and removal rules.
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
