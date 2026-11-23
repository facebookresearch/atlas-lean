/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import Mathlib.Topology.Category.TopPair
public import Mathlib.Topology.Homotopy.Equiv

/-! # Homotopy equivalences of topological pairs -/

@[expose] public section

open CategoryTheory

universe u

namespace TopPair

namespace Homotopy

/-- A homotopy of topological-space maps induces a homotopy between their
images under the absolute-to-relative inclusion functor. -/
def ofTopCat {X Y : TopCat.{u}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g) :
    Homotopy (TopPair.incl.map f) (TopPair.incl.map g) where
  fst := H
  snd := TopCat.Homotopy.refl (𝟙 _)
  w := by
    ext x
    exact PEmpty.elim x.1

end Homotopy

/-- A homotopy equivalence of topological pairs: maps each way with homotopies
to the identities. Stores the chosen homotopies, not mere existence. -/
structure HomotopyEquiv (X Y : TopPair.{u}) where
  /-- Forward map of pairs. -/
  hom : X ⟶ Y
  /-- Backward map of pairs. -/
  inv : Y ⟶ X
  /-- Homotopy `hom ≫ inv ≃ 𝟙 X`. -/
  homotopyHomInvId : Homotopy (hom ≫ inv) (𝟙 X)
  /-- Homotopy `inv ≫ hom ≃ 𝟙 Y`. -/
  homotopyInvHomId : Homotopy (inv ≫ hom) (𝟙 Y)

namespace HomotopyEquiv

variable {X Y Z : TopPair.{u}}

/-- Reflexivity: identity is a homotopy equivalence. -/
@[refl]
def refl (X : TopPair.{u}) : HomotopyEquiv X X where
  hom := 𝟙 X
  inv := 𝟙 X
  homotopyHomInvId := Homotopy.refl (𝟙 X)
  homotopyInvHomId := Homotopy.refl (𝟙 X)

/-- Symmetry of homotopy equivalences. -/
@[symm]
def symm (e : HomotopyEquiv X Y) : HomotopyEquiv Y X where
  hom := e.inv
  inv := e.hom
  homotopyHomInvId := e.homotopyInvHomId
  homotopyInvHomId := e.homotopyHomInvId

/-- Transitivity by whiskering the chosen pair homotopies. -/
@[trans]
noncomputable def trans (e : HomotopyEquiv X Y) (f : HomotopyEquiv Y Z) :
    HomotopyEquiv X Z where
  hom := e.hom ≫ f.hom
  inv := f.inv ≫ e.inv
  homotopyHomInvId := by
    let Hf := f.homotopyHomInvId
    let He := e.homotopyHomInvId
    let H1 : Homotopy (e.hom ≫ (f.hom ≫ f.inv)) (e.hom ≫ 𝟙 Y) :=
      Hf.comp (Homotopy.refl e.hom)
    let H2 : Homotopy ((e.hom ≫ (f.hom ≫ f.inv)) ≫ e.inv)
        ((e.hom ≫ 𝟙 Y) ≫ e.inv) :=
      (Homotopy.refl e.inv).comp H1
    exact H2.trans He
  homotopyInvHomId := by
    let He := e.homotopyInvHomId
    let Hf := f.homotopyInvHomId
    let H1 : Homotopy (f.inv ≫ (e.inv ≫ e.hom)) (f.inv ≫ 𝟙 Y) :=
      He.comp (Homotopy.refl f.inv)
    let H2 : Homotopy ((f.inv ≫ (e.inv ≫ e.hom)) ≫ f.hom)
        ((f.inv ≫ 𝟙 Y) ≫ f.hom) :=
      (Homotopy.refl f.hom).comp H1
    exact H2.trans Hf

/-- From a categorical iso of pairs to a homotopy equivalence. -/
def ofIso (e : X ≅ Y) : HomotopyEquiv X Y where
  hom := e.hom
  inv := e.inv
  homotopyHomInvId := e.hom_inv_id ▸ Homotopy.refl (e.hom ≫ e.inv)
  homotopyInvHomId := e.inv_hom_id ▸ Homotopy.refl (e.inv ≫ e.hom)

/-- A homotopy equivalence of spaces induces one between their empty-subspace
pairs. -/
noncomputable def ofTopCat {X Y : TopCat.{u}}
    (e : ContinuousMap.HomotopyEquiv X Y) :
    HomotopyEquiv (TopPair.ofTopCat X) (TopPair.ofTopCat Y) where
  hom := TopPair.incl.map (TopCat.ofHom e.toFun)
  inv := TopPair.incl.map (TopCat.ofHom e.invFun)
  homotopyHomInvId := Homotopy.ofTopCat e.left_inv.some
  homotopyInvHomId := Homotopy.ofTopCat e.right_inv.some

@[simp]
lemma ofTopCat_hom {X Y : TopCat.{u}} (e : ContinuousMap.HomotopyEquiv X Y) :
    (ofTopCat e).hom = TopPair.incl.map (TopCat.ofHom e.toFun) := rfl

@[simp]
lemma ofTopCat_inv {X Y : TopCat.{u}} (e : ContinuousMap.HomotopyEquiv X Y) :
    (ofTopCat e).inv = TopPair.incl.map (TopCat.ofHom e.invFun) := rfl

end HomotopyEquiv

end TopPair
