/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.RootUnitContraction

/-!
# Mapping the same full root-unit contraction

Mapping the actual continuously varying root family through a continuous
map preserves every whole-loop value of the same joint contraction.
Its original clock and all family/contraction/loop coordinates remain fixed.
-/

public section

noncomputable section

open unitInterval
open scoped Topology ContinuousMap

universe u v w

namespace ContinuousMap

variable {A : Type u} {Y : Type v} {Z : Type w}
  [topA : TopologicalSpace A] [topY : TopologicalSpace Y] [topZ : TopologicalSpace Z]
  {x : A → Y} {y : Y}

private theorem actualMappedRootFamilyContinuousComputed
    (p : ∀ a : A, Path (x a) y)
    (hp : Continuous (fun z : A × I => p z.1 z.2)) (f : C(Y, Z)) :
    Continuous (fun z : A × I =>
      ((p z.1).map (f := fun y : Y => f y) f.continuous) z.2) := by
  have h : Continuous (fun z : A × I => f (p z.1 z.2)) := f.continuous.comp hp
  exact h.congr (fun z => (congrFun
    (Path.map_coe (p z.1) (f := fun y : Y => f y) f.continuous) z.2).symm)

/-- The actual mapped whole root family has jointly continuous values
by the public Path.map equation and the original family continuity. -/
theorem rootUnitMappedFamily_continuous (p : ∀ a : A, Path (x a) y)
    (hp : Continuous (fun z : A × I => p z.1 z.2)) (f : C(Y, Z)) :
    Continuous (fun z : A × I =>
      ((p z.1).map (f := fun y : Y => f y) f.continuous) z.2) :=
  actualMappedRootFamilyContinuousComputed p hp f

private theorem originalRootUnitContractionMapComputed
    (p : ∀ a : A, Path (x a) y)
    (hp : Continuous (fun z : A × I => p z.1 z.2)) (f : C(Y, Z)) (t : I) (a : A) :
    (@rootUnitContraction A Y topA topY x y p hp (t, a)).map
      (f := fun y : Y => f y) f.continuous =
      @rootUnitContraction A Z topA topZ (fun a => f (x a)) (f y)
        (fun a => (p a).map (f := fun y : Y => f y) f.continuous)
        (@rootUnitMappedFamily_continuous A Y Z topA topY topZ x y p hp f) (t, a) := by
  apply Path.ext
  funext s
  change f (@rootUnitContraction A Y topA topY x y p hp (t, a) s) =
    @rootUnitContraction A Z topA topZ (fun a => f (x a)) (f y)
      (fun a => (p a).map (f := fun y : Y => f y) f.continuous)
      (@rootUnitMappedFamily_continuous A Y Z topA topY topZ x y p hp f) (t, a) s
  exact (congrArg f (rootUnitContraction_apply p hp t a s)).trans
    (@rootUnitContraction_apply A Z topA topZ (fun a => f (x a)) (f y)
      (fun a => (p a).map (f := fun y : Y => f y) f.continuous)
      (@rootUnitMappedFamily_continuous A Y Z topA topY topZ x y p hp f) t a s).symm

/-- Every time and family parameter of the whole original joint
contraction commutes with mapping the actual moving-source root family. -/
theorem rootUnitContraction_map (p : ∀ a : A, Path (x a) y)
    (hp : Continuous (fun z : A × I => p z.1 z.2)) (f : C(Y, Z)) (t : I) (a : A) :
    (@rootUnitContraction A Y topA topY x y p hp (t, a)).map
      (f := fun y : Y => f y) f.continuous =
      @rootUnitContraction A Z topA topZ (fun a => f (x a)) (f y)
        (fun a => (p a).map (f := fun y : Y => f y) f.continuous)
        (@rootUnitMappedFamily_continuous A Y Z topA topY topZ x y p hp f) (t, a) :=
  originalRootUnitContractionMapComputed p hp f t a

end ContinuousMap

end
