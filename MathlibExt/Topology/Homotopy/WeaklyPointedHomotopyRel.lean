/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.Topology.Homotopy.WeaklyPointedMap
public import Mathlib.Topology.Homotopy.Product

/-!
# Weakly pointed products and relative-homotopy transport

This file packages products of weakly pointed continuous maps, their exact
root-path projections, and their induced loop maps.  A continuous homotopy
relative to the source basepoint transports mapped loops, and a compatible
homotopy of chosen root paths then gives pointwise homotopy of the induced
loop maps.

The results are universe-polymorphic and pointwise.  They install no global
instances and assert no equality or bundled homotopy of continuous loop
maps, weak equivalence, spectrum, or K-theory consequence.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Path.Homotopic

universe u v

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]

/-- Paths in a product are homotopic when both projected paths are
homotopic, with the first factor followed by the second factor. -/
theorem of_prod_projections
    {a b : X × Y} {p q : Path a b}
    (hfst : (p.map continuous_fst).Homotopic
      (q.map continuous_fst))
    (hsnd : (p.map continuous_snd).Homotopic
      (q.map continuous_snd)) :
    p.Homotopic q := by
  rcases hfst with ⟨hfst⟩
  rcases hsnd with ⟨hsnd⟩
  let hprod := Path.Homotopic.prodHomotopy hfst hsnd
  have hp : (p.map continuous_fst).prod (p.map continuous_snd) = p := by
    apply Path.ext
    rfl
  have hq : (q.map continuous_fst).prod (q.map continuous_snd) = q := by
    apply Path.ext
    rfl
  rw [hp, hq] at hprod
  exact ⟨hprod⟩

end Path.Homotopic

namespace Path

universe u v

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]

/-- Mapping commutes with endpoint transport, and maps both endpoint
equalities covariantly. -/
theorem map_cast
    {a a' b b' : X} (p : Path a b) (f : C(X, Y))
    (ha : a' = a) (hb : b' = b) :
    (p.cast ha hb).map f.continuous =
      (p.map f.continuous).cast (congrArg f ha) (congrArg f hb) := by
  subst ha
  subst hb
  rfl

end Path

namespace ContinuousMap.HomotopyRel

universe u v

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {f g : C(X, Y)}

/-- A homotopy relative to the source basepoint gives an endpoint-fixed
homotopy from the loop mapped through its first endpoint to the loop mapped
through its second endpoint and cast along the fixed-basepoint equality. -/
noncomputable def mappedLoopHomotopy
    (H : ContinuousMap.HomotopyRel f g {x})
    (gamma : LoopSpace X x) :
    Path.Homotopy (gamma.map f.continuous)
      ((gamma.map g.continuous).cast
        (H.fst_eq_snd (by simp)) (H.fst_eq_snd (by simp))) where
  toFun p := H (p.1, gamma p.2)
  continuous_toFun := H.continuous.comp
    (continuous_fst.prodMk (gamma.continuous.comp continuous_snd))
  map_zero_left t := H.map_zero_left (gamma t)
  map_one_left t := H.map_one_left (gamma t)
  prop' t s hs := by
    rcases hs with rfl | hs
    · change H (t, gamma 0) = f (gamma 0)
      rw [gamma.source]
      exact H.eq_fst t (by simp)
    · rw [Set.mem_singleton_iff] at hs
      subst s
      change H (t, gamma 1) = f (gamma 1)
      rw [gamma.target]
      exact H.eq_fst t (by simp)

private theorem conjugation_homotopic
    {a b : Y} {p q : Path a b} {gamma delta : Path a a}
    (hp : p.Homotopic q) (hgamma : gamma.Homotopic delta) :
    (p.symm.trans (gamma.trans p)).Homotopic
      (q.symm.trans (delta.trans q)) :=
  hp.symm₂.hcomp (hgamma.hcomp hp)

end ContinuousMap.HomotopyRel

namespace ContinuousMap.WeaklyPointed

universe u₁ u₂ v₁ v₂ w₁ w₂

variable {X : Type u₁} {X' : Type u₂}
  {Y : Type v₁} {Y' : Type v₂}
  [TopologicalSpace X] [TopologicalSpace X']
  [TopologicalSpace Y] [TopologicalSpace Y']
  {x : X} {x' : X'} {y : Y} {y' : Y'}

/-- Product of weakly pointed maps, with componentwise root path. -/
def prod
    (f : ContinuousMap.WeaklyPointed x y)
    (g : ContinuousMap.WeaklyPointed x' y') :
    ContinuousMap.WeaklyPointed (x, x') (y, y') where
  hom := f.hom.prodMap g.hom
  rootPath := f.rootPath.prod g.rootPath

/-- The underlying map of a product is the ordinary product map. -/
@[simp]
theorem prod_hom
    (f : ContinuousMap.WeaklyPointed x y)
    (g : ContinuousMap.WeaklyPointed x' y') :
    (f.prod g).hom = f.hom.prodMap g.hom :=
  rfl

/-- The root path of a product is the product of the two root paths. -/
@[simp]
theorem prod_rootPath
    (f : ContinuousMap.WeaklyPointed x y)
    (g : ContinuousMap.WeaklyPointed x' y') :
    (f.prod g).rootPath = f.rootPath.prod g.rootPath :=
  rfl

/-- First projection of the product root path. -/
@[simp]
theorem prod_rootPath_fst
    (f : ContinuousMap.WeaklyPointed x y)
    (g : ContinuousMap.WeaklyPointed x' y') :
    (f.prod g).rootPath.map continuous_fst = f.rootPath := by
  apply Path.ext
  rfl

/-- Second projection of the product root path. -/
@[simp]
theorem prod_rootPath_snd
    (f : ContinuousMap.WeaklyPointed x y)
    (g : ContinuousMap.WeaklyPointed x' y') :
    (f.prod g).rootPath.map continuous_snd = g.rootPath := by
  apply Path.ext
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Projecting a composite weakly-pointed root distributes over its two
concatenated legs, in image-of-source-root then target-root order. -/
theorem comp_rootPath_map
    {Z : Type w₁} {W : Type w₂} [TopologicalSpace Z] [TopologicalSpace W]
    {z : Z} (f : ContinuousMap.WeaklyPointed x y)
    (g : ContinuousMap.WeaklyPointed y z) (k : C(Z, W)) :
    ((f.comp g).rootPath.map k.continuous) =
      (((f.rootPath.map g.hom.continuous).map k.continuous).trans
        (g.rootPath.map k.continuous)) := by
  rw [ContinuousMap.WeaklyPointed.comp_rootPath, Path.map_trans]

/-- The loop map of a product is componentwise after the canonical product-
loop homeomorphism. -/
theorem loopMap_prod
    (f : ContinuousMap.WeaklyPointed x y)
    (g : ContinuousMap.WeaklyPointed x' y')
    (gamma : LoopSpace (X × X') (x, x')) :
    loopSpaceProdHomeomorph y y' ((f.prod g).loopMap gamma) =
      (f.loopMap (loopSpaceProdHomeomorph x x' gamma).1,
        g.loopMap (loopSpaceProdHomeomorph x x' gamma).2) := by
  apply Prod.ext
  · rw [loopSpaceProdHomeomorph_apply_fst,
      ContinuousMap.WeaklyPointed.loopMap_apply,
      Path.map_trans, Path.map_trans, ← Path.map_symm]
    apply Path.ext
    rfl
  · rw [loopSpaceProdHomeomorph_apply_snd,
      ContinuousMap.WeaklyPointed.loopMap_apply,
      Path.map_trans, Path.map_trans, ← Path.map_symm]
    apply Path.ext
    rfl

/-- A homotopy relative to the source basepoint, together with a compatible
homotopy of chosen root paths, gives pointwise homotopy of the induced loop
maps. -/
theorem loopMap_homotopic_of_homotopyRel
    (f g : ContinuousMap.WeaklyPointed x y)
    (H : ContinuousMap.HomotopyRel f.hom g.hom {x})
    (hp : f.rootPath.Homotopic
      (g.rootPath.cast (H.fst_eq_snd (by simp)) rfl))
    (gamma : LoopSpace X x) :
    (f.loopMap gamma).Homotopic (g.loopMap gamma) := by
  have hgamma : (gamma.map f.hom.continuous).Homotopic
      ((gamma.map g.hom.continuous).cast
        (H.fst_eq_snd (by simp)) (H.fst_eq_snd (by simp))) :=
    ⟨ContinuousMap.HomotopyRel.mappedLoopHomotopy H gamma⟩
  have hc := ContinuousMap.HomotopyRel.conjugation_homotopic hp hgamma
  convert hc using 1 <;> apply Path.ext <;> rfl

end ContinuousMap.WeaklyPointed
