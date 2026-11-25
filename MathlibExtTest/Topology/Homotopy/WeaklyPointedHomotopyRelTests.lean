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

public import Mathlib.CategoryTheory.Category.Basic
public import MathlibExt.Topology.Homotopy.WeaklyPointedHomotopyRel

/-!
# Tests for weakly pointed relative-homotopy transport

These clients pin mixed universes, product root projections, composite-root
order, endpoint casts, product loop maps, and relative-homotopy transport.
They make no equality or bundled homotopy of loop maps and no weak-
equivalence claim.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open scoped Topology

universe u₁ u₂ v₁ v₂ w

namespace MathlibExtTest.Topology.Homotopy
namespace WeaklyPointedHomotopyRelTests

variable {X : Type u₁} {X' : Type u₂}
  {Y : Type v₁} {Y' : Type v₂} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace X']
  [TopologicalSpace Y] [TopologicalSpace Y'] [TopologicalSpace Z]
  {x : X} {x' : X'} {y : Y} {y' : Y'} {z : Z}

variable (f : ContinuousMap.WeaklyPointed x y)
  (g : ContinuousMap.WeaklyPointed x' y')

/-- Product weakly-pointed map in independent universes. -/
example : ContinuousMap.WeaklyPointed (x, x') (y, y') :=
  f.prod g

/-- Underlying product map computation. -/
example : (f.prod g).hom = f.hom.prodMap g.hom :=
  ContinuousMap.WeaklyPointed.prod_hom f g

/-- Product root is componentwise. -/
example : (f.prod g).rootPath = f.rootPath.prod g.rootPath :=
  ContinuousMap.WeaklyPointed.prod_rootPath f g

/-- Source factor is projected first. -/
example : (f.prod g).rootPath.map continuous_fst = f.rootPath :=
  ContinuousMap.WeaklyPointed.prod_rootPath_fst f g

/-- Target factor is projected second. -/
example : (f.prod g).rootPath.map continuous_snd = g.rootPath :=
  ContinuousMap.WeaklyPointed.prod_rootPath_snd f g

/-- Product-path homotopy is reconstructed from ordered projections. -/
example {a b : X × X'} {p q : Path a b}
    (hfst : (p.map continuous_fst).Homotopic
      (q.map continuous_fst))
    (hsnd : (p.map continuous_snd).Homotopic
      (q.map continuous_snd)) :
    p.Homotopic q :=
  Path.Homotopic.of_prod_projections hfst hsnd

/-- Endpoint transport is mapped covariantly at both ends. -/
example {a a' b b' : X} (p : Path a b) (k : C(X, Y))
    (ha : a' = a) (hb : b' = b) :
    (p.cast ha hb).map k.continuous =
      (p.map k.continuous).cast (congrArg k ha) (congrArg k hb) :=
  Path.map_cast p k ha hb

/-- Composite root order is mapped source root, then target root. -/
example (h : ContinuousMap.WeaklyPointed y z) (k : C(Z, Y')) :
    ((f.comp h).rootPath.map k.continuous) =
      (((f.rootPath.map h.hom.continuous).map k.continuous).trans
        (h.rootPath.map k.continuous)) :=
  ContinuousMap.WeaklyPointed.comp_rootPath_map f h k

/-- Product loop map is componentwise through the canonical homeomorphism. -/
example (gamma : LoopSpace (X × X') (x, x')) :
    loopSpaceProdHomeomorph y y' ((f.prod g).loopMap gamma) =
      (f.loopMap (loopSpaceProdHomeomorph x x' gamma).1,
        g.loopMap (loopSpaceProdHomeomorph x x' gamma).2) :=
  ContinuousMap.WeaklyPointed.loopMap_prod f g gamma

section Relative

variable (f₀ f₁ : ContinuousMap.WeaklyPointed x y)
  (H : ContinuousMap.HomotopyRel f₀.hom f₁.hom {x})

/-- Relative homotopy gives the exact casted mapped-loop homotopy. -/
example (gamma : LoopSpace X x) :
    Path.Homotopy (gamma.map f₀.hom.continuous)
      ((gamma.map f₁.hom.continuous).cast
        (H.fst_eq_snd (by simp)) (H.fst_eq_snd (by simp))) :=
  ContinuousMap.HomotopyRel.mappedLoopHomotopy H gamma

/-- Root-compatible relative homotopy transports the induced loop maps
pointwise. -/
example (hp : f₀.rootPath.Homotopic
      (f₁.rootPath.cast (H.fst_eq_snd (by simp)) rfl))
    (gamma : LoopSpace X x) :
    (f₀.loopMap gamma).Homotopic (f₁.loopMap gamma) :=
  ContinuousMap.WeaklyPointed.loopMap_homotopic_of_homotopyRel
    f₀ f₁ H hp gamma

end Relative

#print axioms ContinuousMap.WeaklyPointed.prod
#print axioms ContinuousMap.WeaklyPointed.loopMap_prod
#print axioms ContinuousMap.HomotopyRel.mappedLoopHomotopy
#print axioms
  ContinuousMap.WeaklyPointed.loopMap_homotopic_of_homotopyRel
#print axioms Path.Homotopic.of_prod_projections
#print axioms Path.map_cast

end WeaklyPointedHomotopyRelTests
end MathlibExtTest.Topology.Homotopy
