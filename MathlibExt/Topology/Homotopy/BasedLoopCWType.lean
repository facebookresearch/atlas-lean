/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopPair.LoopNDR
public import MathlibExt.Topology.Category.TopPair.HomotopyEquiv
public import MathlibExt.Topology.Homotopy.StrictLoopMap

/-!
# Actual based loop maps and relative homotopies

Strict pointed postcomposition acts on the raw compact-open loop space.
Homotopies relative to the original point give continuous loop-space homotopies
relative to the literal constant loop. These provide the based data needed to
transport a constructed CW loop model; CW reconstruction is a separate step.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Topology
open scoped unitInterval

universe u

namespace PointedTopCat

variable {X Y Z : PointedTopCat.{u}}

/-- Strict based postcomposition on the actual raw compact-open loop objects. -/
@[expose]
def loopSpaceMap (f : X ⟶ Y) : loopSpace X ⟶ loopSpace Y := by
  let h0 : f.right (X.hom PUnit.unit) = Y.hom PUnit.unit := map_basepoint f
  let m : C(LoopSpace X.right (X.hom PUnit.unit), LoopSpace Y.right (Y.hom PUnit.unit)) :=
    { toFun gamma :=
        (ContinuousMap.strictLoopMap f.right.hom (X.hom PUnit.unit) gamma).cast
          h0.symm h0.symm
      continuous_toFun := Path.continuous_uncurry_iff.mp
        (f.right.hom.continuous.comp (continuous_fst.eval continuous_snd)) }
  exact Under.homMk (TopCat.ofHom m) (by
    apply TopCat.ext
    intro p
    apply Path.ext
    funext t
    exact h0)

/-- The actual loop map applies the given pointed map at every path parameter. -/
@[simp]
theorem loopSpaceMap_apply (f : X ⟶ Y)
    (gamma : LoopSpace X.right (X.hom PUnit.unit)) (t : unitInterval) :
    ((loopSpaceMap f).right gamma : LoopSpace Y.right (Y.hom PUnit.unit)) t =
      f.right (gamma t) := rfl

/-- Strict loop postcomposition sends the identity pointed map to the identity. -/
@[simp]
theorem loopSpaceMap_id (X : PointedTopCat.{u}) :
    loopSpaceMap (𝟙 X) = 𝟙 (loopSpace X) := by
  apply (Under.forget (TopCat.of PUnit)).map_injective
  apply TopCat.ext
  intro gamma
  apply Path.ext
  funext t
  rfl

/-- Strict loop postcomposition retains composition of the actual pointed maps. -/
@[simp]
theorem loopSpaceMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    loopSpaceMap (f ≫ g) = loopSpaceMap f ≫ loopSpaceMap g := by
  apply (Under.forget (TopCat.of PUnit)).map_injective
  apply TopCat.ext
  intro gamma
  apply Path.ext
  funext t
  rfl

/-- The actual pointed compact-open loop construction as a strict functor. -/
@[expose]
def loopSpaceFunctor : PointedTopCat.{u} ⥤ PointedTopCat.{u} where
  obj := loopSpace
  map := loopSpaceMap
  map_id := loopSpaceMap_id
  map_comp := loopSpaceMap_comp

variable {f₀ f₁ : X ⟶ Y}

private def loopHomotopyPath
    (H : ContinuousMap.HomotopyRel f₀.right.hom f₁.right.hom {X.hom PUnit.unit})
    (s : unitInterval) (gamma : LoopSpace X.right (X.hom PUnit.unit)) :
    LoopSpace Y.right (Y.hom PUnit.unit) where
  toContinuousMap :=
    { toFun t := H (s, gamma t)
      continuous_toFun := H.continuous.comp (continuous_const.prodMk gamma.continuous) }
  source' := by
    change H (s, gamma 0) = Y.hom PUnit.unit
    rw [gamma.source, H.eq_fst s (Set.mem_singleton_iff.mpr rfl)]
    exact map_basepoint f₀
  target' := by
    change H (s, gamma 1) = Y.hom PUnit.unit
    rw [gamma.target, H.eq_fst s (Set.mem_singleton_iff.mpr rfl)]
    exact map_basepoint f₀

/-- A homotopy relative to the original point induces a continuous loop-space
homotopy relative to the literal constant loop. -/
def loopSpaceMapHomotopyRel
    (H : ContinuousMap.HomotopyRel f₀.right.hom f₁.right.hom {X.hom PUnit.unit}) :
    ContinuousMap.HomotopyRel (loopSpaceMap f₀).right.hom (loopSpaceMap f₁).right.hom
      {Path.refl (X.hom PUnit.unit)} where
  toFun z := loopHomotopyPath H z.1 z.2
  continuous_toFun := Path.continuous_uncurry_iff.mp
    (H.continuous.comp
      ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).eval continuous_snd)))
  map_zero_left gamma := by
    apply Path.ext
    funext t
    exact H.apply_zero (gamma t)
  map_one_left gamma := by
    apply Path.ext
    funext t
    exact H.apply_one (gamma t)
  prop' s gamma hgamma := by
    obtain rfl := Set.mem_singleton_iff.mp hgamma
    apply Path.ext
    funext t
    exact H.eq_fst s (Set.mem_singleton_iff.mpr rfl)

private theorem loopSpaceMapHomotopyRel_apply_private
    (H : ContinuousMap.HomotopyRel f₀.right.hom f₁.right.hom {X.hom PUnit.unit})
    (s : unitInterval) (gamma : LoopSpace X.right (X.hom PUnit.unit)) (t : unitInterval) :
    (loopSpaceMapHomotopyRel H (s, gamma) : LoopSpace Y.right (Y.hom PUnit.unit)) t =
      H (s, gamma t) := by rfl

/-- The induced relative loop homotopy applies the original homotopy pointwise. -/
@[simp]
theorem loopSpaceMapHomotopyRel_apply
    (H : ContinuousMap.HomotopyRel f₀.right.hom f₁.right.hom {X.hom PUnit.unit})
    (s : unitInterval) (gamma : LoopSpace X.right (X.hom PUnit.unit)) (t : unitInterval) :
    (loopSpaceMapHomotopyRel H (s, gamma) : LoopSpace Y.right (Y.hom PUnit.unit)) t =
      H (s, gamma t) := loopSpaceMapHomotopyRel_apply_private H s gamma t

end PointedTopCat

namespace TopPair.HomotopyEquiv

variable {X Y : PointedTopCat.{u}}

private def pointedHomOfPair
    (f : PointedTopCat.pointedPair.obj X ⟶ PointedTopCat.pointedPair.obj Y) : X ⟶ Y :=
  Under.homMk (TopPair.Hom.fst f) (by
    apply TopCat.ext
    intro p
    have h := TopPair.Hom.w_apply f p
    change Y.hom ((TopPair.Hom.snd f) p) = (TopPair.Hom.fst f) (X.hom p) at h
    have hp : (TopPair.Hom.snd f) p = p :=
      Subsingleton.elim (α := PUnit.{u + 1}) _ _
    rw [hp] at h
    exact h.symm)

private def pointRelOfPairHomotopy
    {f g : PointedTopCat.pointedPair.obj X ⟶ PointedTopCat.pointedPair.obj Y}
    (H : TopPair.Homotopy f g) :
    ContinuousMap.HomotopyRel (TopPair.Hom.fst f).hom (TopPair.Hom.fst g).hom
      {X.hom PUnit.unit} where
  toHomotopy := H.fst
  prop' s x hx := by
    obtain rfl := Set.mem_singleton_iff.mp hx
    have h := H.w_apply' PUnit.unit s
    change H.fst (s, X.hom PUnit.unit) = Y.hom (H.snd (s, PUnit.unit)) at h
    have hp : H.snd (s, PUnit.unit) = PUnit.unit :=
      Subsingleton.elim (α := PUnit.{u + 1}) _ _
    rw [hp] at h
    have hf := PointedTopCat.map_basepoint (pointedHomOfPair (X := X) (Y := Y) f)
    exact h.trans hf.symm

private def pairHomotopyOfPointedRel {f g : X ⟶ Y}
    (H : ContinuousMap.HomotopyRel f.right.hom g.right.hom {X.hom PUnit.unit}) :
    TopPair.Homotopy (PointedTopCat.pointedPair.map f) (PointedTopCat.pointedPair.map g) where
  fst := H.toHomotopy
  snd := TopCat.Homotopy.refl (𝟙 (TopCat.of PUnit))
  w := by
    apply TopCat.ext
    intro ⟨p, t⟩
    change H (TopCat.I.homeomorph t, X.hom p) = Y.hom p
    cases p
    exact (H.eq_fst (TopCat.I.homeomorph t) (Set.mem_singleton_iff.mpr rfl)).trans
      (PointedTopCat.map_basepoint f)

/-- A specified homotopy equivalence of literal point pairs induces a
homotopy equivalence of their actual loop point pairs, with both homotopies
relative to the constant loops. -/
def loopSpace
    (e : TopPair.HomotopyEquiv
      (PointedTopCat.pointedPair.obj X) (PointedTopCat.pointedPair.obj Y)) :
    TopPair.HomotopyEquiv
      (PointedTopCat.pointedPair.obj (PointedTopCat.loopSpace X))
      (PointedTopCat.pointedPair.obj (PointedTopCat.loopSpace Y)) := by
  let f := pointedHomOfPair (X := X) (Y := Y) e.hom
  let g := pointedHomOfPair (X := Y) (Y := X) e.inv
  let hX : ContinuousMap.HomotopyRel (f ≫ g).right.hom (𝟙 X : X ⟶ X).right.hom
      {X.hom PUnit.unit} :=
    pointRelOfPairHomotopy (X := X) (Y := X) e.homotopyHomInvId
  let hY : ContinuousMap.HomotopyRel (g ≫ f).right.hom (𝟙 Y : Y ⟶ Y).right.hom
      {Y.hom PUnit.unit} :=
    pointRelOfPairHomotopy (X := Y) (Y := Y) e.homotopyInvHomId
  have hIdX : PointedTopCat.pointedPair.map (𝟙 (PointedTopCat.loopSpace X)) =
      𝟙 (PointedTopCat.pointedPair.obj (PointedTopCat.loopSpace X)) := by
    exact PointedTopCat.pointedPair.map_id _
  have hIdY : PointedTopCat.pointedPair.map (𝟙 (PointedTopCat.loopSpace Y)) =
      𝟙 (PointedTopCat.pointedPair.obj (PointedTopCat.loopSpace Y)) := by
    exact PointedTopCat.pointedPair.map_id _
  refine
    { hom := PointedTopCat.pointedPair.map (PointedTopCat.loopSpaceMap f)
      inv := PointedTopCat.pointedPair.map (PointedTopCat.loopSpaceMap g)
      homotopyHomInvId := ?_
      homotopyInvHomId := ?_ }
  · simpa only [PointedTopCat.loopSpaceMap_comp, Functor.map_comp,
      PointedTopCat.loopSpaceMap_id, hIdX] using
      (pairHomotopyOfPointedRel
        (X := PointedTopCat.loopSpace X) (Y := PointedTopCat.loopSpace X)
        (PointedTopCat.loopSpaceMapHomotopyRel hX))
  · simpa only [PointedTopCat.loopSpaceMap_comp, Functor.map_comp,
      PointedTopCat.loopSpaceMap_id, hIdY] using
      (pairHomotopyOfPointedRel
        (X := PointedTopCat.loopSpace Y) (Y := PointedTopCat.loopSpace Y)
        (PointedTopCat.loopSpaceMapHomotopyRel hY))

variable (e : TopPair.HomotopyEquiv
  (PointedTopCat.pointedPair.obj X) (PointedTopCat.pointedPair.obj Y))

/-- The actual forward loop map of the constructed based equivalence. -/
@[expose]
def loopSpaceHom : C(LoopSpace X.right (X.hom PUnit.unit),
    LoopSpace Y.right (Y.hom PUnit.unit)) :=
  (TopPair.Hom.fst (e.loopSpace (X := X) (Y := Y)).hom).hom

/-- The actual backward loop map of the constructed based equivalence. -/
@[expose]
def loopSpaceInv : C(LoopSpace Y.right (Y.hom PUnit.unit),
    LoopSpace X.right (X.hom PUnit.unit)) :=
  (TopPair.Hom.fst (e.loopSpace (X := X) (Y := Y)).inv).hom

private theorem loopSpaceHom_apply_private
    (gamma : LoopSpace X.right (X.hom PUnit.unit)) (t : unitInterval) :
    e.loopSpaceHom gamma t = (TopPair.Hom.fst e.hom) (gamma t) := by rfl

/-- The forward map applies the original equivalence map at every loop parameter. -/
@[simp]
theorem loopSpaceHom_apply (gamma : LoopSpace X.right (X.hom PUnit.unit))
    (t : unitInterval) :
    e.loopSpaceHom gamma t = (TopPair.Hom.fst e.hom) (gamma t) :=
  loopSpaceHom_apply_private e gamma t

private theorem loopSpaceInv_apply_private
    (gamma : LoopSpace Y.right (Y.hom PUnit.unit)) (t : unitInterval) :
    e.loopSpaceInv gamma t = (TopPair.Hom.fst e.inv) (gamma t) := by rfl

/-- The backward map applies the original inverse map at every loop parameter. -/
@[simp]
theorem loopSpaceInv_apply (gamma : LoopSpace Y.right (Y.hom PUnit.unit))
    (t : unitInterval) :
    e.loopSpaceInv gamma t = (TopPair.Hom.fst e.inv) (gamma t) :=
  loopSpaceInv_apply_private e gamma t

end TopPair.HomotopyEquiv

end
