/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyFiberLoopsRealizedConull
public import MathlibExt.Topology.Category.TopPair.HomotopyEquiv

/-!
# Actual full homotopy fiber and loop singleton point pairs

A based contraction gives maps of the actual selected singleton point pairs
and both pair inverse homotopies. The subspace maps restrict the same ambient
return and selected-loop inclusion. Realized total conullity specializes this
construction through its derived actual based contraction.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Topology
open scoped unitInterval Topology.Homotopy Simplicial

universe u

namespace TopCat

/-- The actual full fiber and loop singleton pairs from a based total contraction. -/
def homotopyFiberLoopPointPairEquivOfBasedContraction
    {E B : TopCat.{u}} (p : E ⟶ B) (e : E) (b : B)
    (he : p e = b) (C : BasedContraction E e) :
    TopPair.HomotopyEquiv
      (TopPair.ofSubset (X := homotopyFiber p b)
        {homotopyFiberSelectedPointMap p e b he PUnit.unit})
      (TopPair.ofSubset (X := TopCat.of (LoopSpace B b)) {Path.refl b}) := by
  let eHE := homotopyFiberLoopEquivOfBasedContraction p e b he C
  let z0 : homotopyFiber p b :=
    homotopyFiberSelectedPointMap p e b he PUnit.unit
  let c0 : LoopSpace B b := Path.refl b
  let F : TopPair.{u} := TopPair.ofSubset (X := homotopyFiber p b)
    ({z0} : Set (homotopyFiber p b))
  let L : TopPair.{u} := TopPair.ofSubset (X := TopCat.of (LoopSpace B b))
    ({c0} : Set (LoopSpace B b))
  have hf0 : eHE.toFun z0 = c0 := by
    change (homotopyFiberLoopEquivOfBasedContraction p e b he C).toFun z0 = c0
    rw [homotopyFiberLoopEquivOfBasedContraction_toFun]
    exact ConcreteCategory.congr_hom
      (homotopyFiberToLoopsOfBasedContraction_selectedPoint p e b he C) PUnit.unit
  have hg0 : eHE.invFun c0 = z0 := by
    change (homotopyFiberLoopEquivOfBasedContraction p e b he C).invFun c0 = z0
    rw [homotopyFiberLoopEquivOfBasedContraction_invFun]
    exact ConcreteCategory.congr_hom
      (loopToHomotopyFiber_constant_point p e b he) PUnit.unit
  let f : F.fst ⟶ L.fst := TopCat.ofHom eHE.toFun
  let g : L.fst ⟶ F.fst := TopCat.ofHom eHE.invFun
  let fSub : F.snd ⟶ L.snd := TopCat.ofHom
    { toFun := fun a =>
        ⟨eHE.toFun a.1, Set.mem_singleton_iff.mpr
          ((congrArg eHE.toFun (Set.mem_singleton_iff.mp a.2)).trans hf0)⟩
      continuous_toFun :=
        (eHE.toFun.continuous.comp continuous_subtype_val).subtype_mk _ }
  let gSub : L.snd ⟶ F.snd := TopCat.ofHom
    { toFun := fun a =>
        ⟨eHE.invFun a.1, Set.mem_singleton_iff.mpr
          ((congrArg eHE.invFun (Set.mem_singleton_iff.mp a.2)).trans hg0)⟩
      continuous_toFun :=
        (eHE.invFun.continuous.comp continuous_subtype_val).subtype_mk _ }
  let hom : F ⟶ L := TopPair.ofHom f fSub (by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro a
    rfl)
  let inv : L ⟶ F := TopPair.ofHom g gSub (by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro a
    rfl)
  have hleftSub : TopPair.Hom.snd (hom ≫ inv) = 𝟙 F.snd := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro a
    apply Subtype.ext
    change (gSub (fSub a)).1 = a.1
    exact (Set.mem_singleton_iff.mp (gSub (fSub a)).2).trans
      (Set.mem_singleton_iff.mp a.2).symm
  have hrightSub : TopPair.Hom.snd (inv ≫ hom) = 𝟙 L.snd := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro a
    apply Subtype.ext
    change (fSub (gSub a)).1 = a.1
    exact (Set.mem_singleton_iff.mp (fSub (gSub a)).2).trans
      (Set.mem_singleton_iff.mp a.2).symm
  let leftRel := homotopyFiberLoopEquivOfBasedContraction_leftHomotopyRel p e b he C
  let rightRel := homotopyFiberLoopEquivOfBasedContraction_rightHomotopyRel p e b he C
  let leftFst : TopCat.Homotopy (TopPair.Hom.fst (hom ≫ inv))
      (TopPair.Hom.fst (𝟙 F)) := by
    change ContinuousMap.Homotopy (eHE.invFun.comp eHE.toFun)
      (ContinuousMap.id (homotopyFiber p b))
    exact leftRel.toHomotopy
  let rightFst : TopCat.Homotopy (TopPair.Hom.fst (inv ≫ hom))
      (TopPair.Hom.fst (𝟙 L)) := by
    change ContinuousMap.Homotopy (eHE.toFun.comp eHE.invFun)
      (ContinuousMap.id (LoopSpace B b))
    exact rightRel.toHomotopy
  let leftSnd : TopCat.Homotopy (TopPair.Hom.snd (hom ≫ inv))
      (TopPair.Hom.snd (𝟙 F)) :=
    (TopCat.Homotopy.refl (𝟙 F.snd)).cast
      (congrArg TopCat.Hom.hom hleftSub.symm) rfl
  let rightSnd : TopCat.Homotopy (TopPair.Hom.snd (inv ≫ hom))
      (TopPair.Hom.snd (𝟙 L)) :=
    (TopCat.Homotopy.refl (𝟙 L.snd)).cast
      (congrArg TopCat.Hom.hom hrightSub.symm) rfl
  refine
    { hom := hom
      inv := inv
      homotopyHomInvId := { fst := leftFst, snd := leftSnd, w := ?_ }
      homotopyInvHomId := { fst := rightFst, snd := rightSnd, w := ?_ } }
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    rintro ⟨a, t⟩
    change leftRel.toHomotopy ((TopCat.I.homeomorph.{u}) t, a.1) = a.1
    exact leftRel.eq_snd ((TopCat.I.homeomorph.{u}) t) a.2
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    rintro ⟨a, t⟩
    change rightRel.toHomotopy ((TopCat.I.homeomorph.{u}) t, a.1) = a.1
    exact rightRel.eq_snd ((TopCat.I.homeomorph.{u}) t) a.2

/-- The ambient forward map is the same full homotopy-fiber return. -/
theorem homotopyFiberLoopPointPairEquivOfBasedContraction_hom_fst
    {E B : TopCat.{u}} (p : E ⟶ B) (e : E) (b : B)
    (he : p e = b) (C : BasedContraction E e) :
    (TopPair.Hom.fst (homotopyFiberLoopPointPairEquivOfBasedContraction p e b he C).hom).hom =
      (homotopyFiberLoopEquivOfBasedContraction p e b he C).toFun := (rfl)

/-- The ambient inverse is the original full selected-loop inclusion. -/
theorem homotopyFiberLoopPointPairEquivOfBasedContraction_inv_fst
    {E B : TopCat.{u}} (p : E ⟶ B) (e : E) (b : B)
    (he : p e = b) (C : BasedContraction E e) :
    (TopPair.Hom.fst (homotopyFiberLoopPointPairEquivOfBasedContraction p e b he C).inv).hom =
      (loopToHomotopyFiber p e b he).hom := by
  change (homotopyFiberLoopEquivOfBasedContraction p e b he C).invFun = _
  exact homotopyFiberLoopEquivOfBasedContraction_invFun p e b he C

/-- The actual full HF and raw loop spaces are equivalent as their genuine
selected singleton point pairs, with both constructed relative inverse homotopies. -/
@[expose]
def realizedConullHomotopyFiberLoopPointPairEquiv
    (K : SSet.{u}) (x : K _⦋0⦌)
    {B : TopCat.{u}} (p : SSet.toTop.obj K ⟶ B) (b : B)
    (he : p (SSet.realizedVertex x) = b)
    (hK : weakHomotopyEquivalences (terminal.from (SSet.toTop.obj K))) :
    TopPair.HomotopyEquiv
      (TopPair.ofSubset (X := homotopyFiber p b)
        {homotopyFiberSelectedPointMap p (SSet.realizedVertex x) b he PUnit.unit})
      (TopPair.ofSubset (X := TopCat.of (LoopSpace B b)) {Path.refl b}) :=
  homotopyFiberLoopPointPairEquivOfBasedContraction p (SSet.realizedVertex x) b he
    (SSet.basedContractionAtRealizedVertex K x hK)

end TopCat

end
