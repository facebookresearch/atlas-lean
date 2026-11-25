/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Continuous maps preserving a point up to a chosen path

A `ContinuousMap.WeaklyPointed x y` consists of a continuous map `f : X ⟶ Y`
together with a path from `f x` to `y`.  It induces a continuous map of loop
spaces by mapping a loop and conjugating it with the chosen root path.

Identity and composition are recorded only up to path homotopy: path
concatenation is not strictly unital or associative.  The file also provides
the canonical homeomorphism between loops in a product and pairs of loops,
with its projection, inverse, basepoint, and naturality laws.

No weak-equivalence, group-completion, classifying-space, topological-monoid,
or global pointed-instance claim is made here.
-/

@[expose] public section

noncomputable section

open unitInterval

universe u v w u' v'

namespace ContinuousMap

/-- A continuous map equipped with a path from the image of the source point
to the target point. -/
structure WeaklyPointed
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) where
  /-- The underlying continuous map. -/
  hom : C(X, Y)
  /-- The chosen path from the mapped source point to the target point. -/
  rootPath : Path (hom x) y

namespace WeaklyPointed

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {x : X} {y : Y} {z : Z}

/-- A weakly pointed map induces a continuous map of loop spaces by
conjugating the mapped loop with the chosen root path. -/
noncomputable def loopMap (f : WeaklyPointed x y) :
    C(LoopSpace X x, LoopSpace Y y) where
  toFun gamma :=
    f.rootPath.symm.trans
      ((gamma.map f.hom.continuous).trans f.rootPath)
  continuous_toFun := by
    apply Continuous.path_trans continuous_const
    apply Continuous.path_trans _ continuous_const
    apply Path.continuous_uncurry_iff.mp
    exact f.hom.continuous.comp
      (continuous_eval.comp (continuous_fst.prodMk continuous_snd))

/-- The induced loop map has the literal conjugation formula. -/
@[simp]
theorem loopMap_apply (f : WeaklyPointed x y) (gamma : LoopSpace X x) :
    f.loopMap gamma =
      f.rootPath.symm.trans
        ((gamma.map f.hom.continuous).trans f.rootPath) :=
  rfl

/-- The identity continuous map with the reflexive root path. -/
def id (x : X) : WeaklyPointed x x where
  hom := ContinuousMap.id X
  rootPath := Path.refl x

/-- Composite weakly pointed map.  Its root path first maps the first root
path through the second map and then follows the second root path. -/
def comp (f : WeaklyPointed x y) (g : WeaklyPointed y z) :
    WeaklyPointed x z where
  hom := g.hom.comp f.hom
  rootPath := (f.rootPath.map g.hom.continuous).trans g.rootPath

/-- The underlying map of the weakly pointed identity is the identity. -/
@[simp]
theorem id_hom (x : X) : (id x).hom = ContinuousMap.id X :=
  rfl

/-- The root path of the weakly pointed identity is reflexive. -/
@[simp]
theorem id_rootPath (x : X) : (id x).rootPath = Path.refl x :=
  rfl

/-- The underlying map of a weakly pointed composite is the composite of the
underlying continuous maps. -/
@[simp]
theorem comp_hom (f : WeaklyPointed x y) (g : WeaklyPointed y z) :
    (comp f g).hom = g.hom.comp f.hom :=
  rfl

/-- Root-path formula for a weakly pointed composite. -/
@[simp]
theorem comp_rootPath (f : WeaklyPointed x y) (g : WeaklyPointed y z) :
    (comp f g).rootPath =
      (f.rootPath.map g.hom.continuous).trans g.rootPath :=
  rfl

/-- The induced loop map of the weakly pointed identity is homotopic, but not
claimed equal, to the identity on loops. -/
theorem loopMap_id_homotopic (x : X) (gamma : LoopSpace X x) :
    ((id x).loopMap gamma).Homotopic gamma := by
  rw [loopMap_apply]
  have hmap : gamma.map (id x).hom.continuous = gamma := by
    apply Path.ext
    rfl
  rw [hmap]
  exact (Path.Homotopic.refl_trans _).trans
    (Path.Homotopic.trans_refl _)

/-- Induced loop maps respect composition up to path homotopy. -/
theorem loopMap_comp_homotopic
    (f : WeaklyPointed x y) (g : WeaklyPointed y z)
    (gamma : LoopSpace X x) :
    ((comp f g).loopMap gamma).Homotopic
      (g.loopMap (f.loopMap gamma)) := by
  change
    (((f.rootPath.map g.hom.continuous).trans g.rootPath).symm.trans
      ((gamma.map (g.hom.comp f.hom).continuous).trans
        ((f.rootPath.map g.hom.continuous).trans g.rootPath))).Homotopic
      (g.rootPath.symm.trans
        (((f.rootPath.symm.trans
          ((gamma.map f.hom.continuous).trans f.rootPath)).map
            g.hom.continuous).trans g.rootPath))
  have hmapGamma :
      gamma.map (g.hom.comp f.hom).continuous =
        (gamma.map f.hom.continuous).map g.hom.continuous := by
    apply Path.ext
    rfl
  rw [Path.map_trans, Path.map_trans, ← Path.map_symm, hmapGamma]
  rw [Path.trans_symm]
  apply Path.Homotopic.Quotient.eq.mp
  simp only [Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.mk_map]
  simp only [Path.Homotopic.Quotient.trans_assoc]

end WeaklyPointed

end ContinuousMap

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (x : X) (y : Y)

/-- Loops in a product are canonically homeomorphic to pairs of loops. -/
noncomputable def loopSpaceProdHomeomorph :
    LoopSpace (X × Y) (x, y) ≃ₜ
      LoopSpace X x × LoopSpace Y y where
  toFun gamma :=
    (gamma.map continuous_fst, gamma.map continuous_snd)
  invFun gamma := gamma.1.prod gamma.2
  left_inv gamma := by
    apply Path.ext
    rfl
  right_inv gamma := by
    apply Prod.ext
    · apply Path.ext
      rfl
    · apply Path.ext
      rfl
  continuous_toFun := by
    apply Continuous.prodMk
    · apply Path.continuous_uncurry_iff.mp
      exact continuous_fst.comp
        (continuous_eval.comp (continuous_fst.prodMk continuous_snd))
    · apply Path.continuous_uncurry_iff.mp
      exact continuous_snd.comp
        (continuous_eval.comp (continuous_fst.prodMk continuous_snd))
  continuous_invFun := by
    apply Path.continuous_uncurry_iff.mp
    exact
      (continuous_eval.comp
        ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).prodMk
      (continuous_eval.comp
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd))

/-- First projection formula for the product-loop homeomorphism. -/
@[simp]
theorem loopSpaceProdHomeomorph_apply_fst (gamma : LoopSpace (X × Y) (x, y)) :
    (loopSpaceProdHomeomorph x y gamma).1 = gamma.map continuous_fst :=
  by
    unfold loopSpaceProdHomeomorph
    rfl

/-- Second projection formula for the product-loop homeomorphism. -/
@[simp]
theorem loopSpaceProdHomeomorph_apply_snd (gamma : LoopSpace (X × Y) (x, y)) :
    (loopSpaceProdHomeomorph x y gamma).2 = gamma.map continuous_snd :=
  by
    unfold loopSpaceProdHomeomorph
    rfl

/-- Inverse formula for the product-loop homeomorphism. -/
@[simp]
theorem loopSpaceProdHomeomorph_symm_apply
    (gamma : LoopSpace X x × LoopSpace Y y) :
    (loopSpaceProdHomeomorph x y).symm gamma = gamma.1.prod gamma.2 :=
  by
    unfold loopSpaceProdHomeomorph
    rfl

/-- The reflexive loop at a product point corresponds to the pair of
reflexive loops. -/
@[simp]
theorem loopSpaceProdHomeomorph_refl :
    loopSpaceProdHomeomorph x y (Path.refl (x, y)) =
      (Path.refl x, Path.refl y) :=
  by
    unfold loopSpaceProdHomeomorph
    apply Prod.ext
    · apply Path.ext
      rfl
    · apply Path.ext
      rfl

variable {X' : Type u'} {Y' : Type v'}
  [TopologicalSpace X'] [TopologicalSpace Y']

/-- The product-loop homeomorphism is natural under continuous maps. -/
@[simp]
theorem loopSpaceProdHomeomorph_naturality
    (f : C(X, X')) (g : C(Y, Y'))
    (gamma : LoopSpace (X × Y) (x, y)) :
    loopSpaceProdHomeomorph (f x) (g y)
        (gamma.map (f.prodMap g).continuous) =
      ((loopSpaceProdHomeomorph x y gamma).1.map f.continuous,
        (loopSpaceProdHomeomorph x y gamma).2.map g.continuous) := by
  simp only [loopSpaceProdHomeomorph]
  apply Prod.ext
  · apply Path.ext
    rfl
  · apply Path.ext
    rfl

/-- Naturality of the inverse product-loop construction. -/
@[simp]
theorem loopSpaceProdHomeomorph_symm_naturality
    (f : C(X, X')) (g : C(Y, Y'))
    (gamma : LoopSpace X x × LoopSpace Y y) :
    ((loopSpaceProdHomeomorph x y).symm gamma).map
        (f.prodMap g).continuous =
      (loopSpaceProdHomeomorph (f x) (g y)).symm
        (gamma.1.map f.continuous, gamma.2.map g.continuous) := by
  simp only [loopSpaceProdHomeomorph]
  apply Path.ext
  rfl

end
