/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# Continuous maps and original based path transport

The original fundamental groups are End groups of the fundamental groupoid.
Their existing path transport is conjugation by the same path class. Mapping
this conjugation is conjugation by the mapped path, with the original End
multiplication order. Endpoint equalities give the corresponding formula for
the original `mapOfEq`, between spaces with independent carrier universes.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u v

namespace FundamentalGroup

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- A specified endpoint equality preserves killing of an original based
loop. The original equality-pointed map and its literal-image map are
compared without assuming their printed image points are definitionally equal. -/
public theorem mapOfEq_eq_one_iff (f : C(X, Y)) {x : X} {y : Y}
    (h : f x = y) (p : FundamentalGroup X x) :
    mapOfEq f h p = 1 ↔ mapOfEq f rfl p = 1 := by
  cases h
  rfl

/-- Equality of the ORIGINAL continuous maps gives equality of the
actual based homomorphisms, preserving the specified endpoint proofs.
No path or group dictionary is replaced. -/
public theorem mapOfEq_congr {f g : C(X, Y)} {x : X} {y : Y}
    (h : f = g) (hf : f x = y) (hg : g x = y) :
    mapOfEq f hf = mapOfEq g hg := by
  cases h
  rfl

/-- With its literal image basepoint, the existing equality-pointed map is the ordinary map. -/
theorem mapOfEq_rfl (f : C(X, Y)) (x : X) :
    mapOfEq f (rfl : f x = f x) = map f x := by
  apply MonoidHom.ext
  intro q
  change (eqToIso (congrArg FundamentalGroupoid.mk (rfl : f x = f x))).conj
    (map f x q) = map f x q
  rw [eqToIso_refl, Iso.refl_conj]

/-- Mapping the original End conjugation maps the same original basepoint path. -/
theorem map_fundamentalGroupMulEquivOfPath (f : C(X, Y))
    {a b : X} (p : Path a b) (q : FundamentalGroup X a) :
    map f b (fundamentalGroupMulEquivOfPath p q) =
      fundamentalGroupMulEquivOfPath (p.map f.continuous) (map f a q) := by
  let F := FundamentalGroupoid.map f
  let α : FundamentalGroupoid.mk a ≅ FundamentalGroupoid.mk b :=
    (Groupoid.isoEquivHom _ _).symm (Path.Homotopic.Quotient.mk p)
  let β : FundamentalGroupoid.mk (f a) ≅ FundamentalGroupoid.mk (f b) :=
    (Groupoid.isoEquivHom _ _).symm
      (Path.Homotopic.Quotient.mk (p.map f.continuous))
  have hIso : F.mapIso α = β := by
    apply Iso.ext
    change Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.mk p) f =
      Path.Homotopic.Quotient.mk (p.map f.continuous)
    exact (Path.Homotopic.Quotient.mk_map p f).symm
  apply End.ext
  change F.map (α.conj q).asHom =
    (β.conj (F.mapEnd (FundamentalGroupoid.mk a) q)).asHom
  have hMap : F.map (α.conj q).asHom =
      ((F.mapIso α).conj (F.mapEnd (FundamentalGroupoid.mk a) q)).asHom :=
    F.map_conj α q
  exact hMap.trans (congrArg
    (fun e : FundamentalGroupoid.mk (f a) ≅ FundamentalGroupoid.mk (f b) =>
      (e.conj (F.mapEnd (FundamentalGroupoid.mk a) q)).asHom) hIso)

/-- The same naturality formula retains both selected target basepoints and their equalities. -/
theorem mapOfEq_fundamentalGroupMulEquivOfPath (f : C(X, Y))
    {a b : X} {c d : Y} (ha : f a = c) (hb : f b = d)
    (p : Path a b) (q : FundamentalGroup X a) :
    mapOfEq f hb (fundamentalGroupMulEquivOfPath p q) =
      fundamentalGroupMulEquivOfPath ((p.map f.continuous).cast ha.symm hb.symm)
        (mapOfEq f ha q) := by
  cases ha
  cases hb
  simpa only [mapOfEq_rfl, Path.cast_rfl_rfl] using
    map_fundamentalGroupMulEquivOfPath f p q

/-- Transport along the actual constant path fixes every original based class. -/
theorem fundamentalGroupMulEquivOfPath_refl (x : X) (q : FundamentalGroup X x) :
    fundamentalGroupMulEquivOfPath (Path.refl x) q = q := by
  let α : FundamentalGroupoid.mk x ≅ FundamentalGroupoid.mk x :=
    (Groupoid.isoEquivHom _ _).symm (Path.Homotopic.Quotient.mk (Path.refl x))
  have hα : α = Iso.refl (FundamentalGroupoid.mk x) := by
    apply Iso.ext
    rfl
  change α.conj q = q
  rw [hα, Iso.refl_conj]

/-- Bijectivity at one original source point propagates along the actual
source paths, with the same mapped target paths. -/
public theorem mapOfEq_bijective_of_pathConnected [PathConnectedSpace X]
    (f : C(X, Y)) (x : X)
    (h : Function.Bijective (mapOfEq f rfl (x := x))) :
    ∀ b : X, Function.Bijective (mapOfEq f rfl (x := b)) := by
  have hm : Function.Bijective (map f x) := by
    simpa only [mapOfEq_rfl] using h
  intro b
  let p := PathConnectedSpace.somePath x b
  let es := fundamentalGroupMulEquivOfPath p
  let et := fundamentalGroupMulEquivOfPath (p.map f.continuous)
  let em := Equiv.ofBijective (map f x) hm
  let e := es.symm.toEquiv.trans (em.trans et.toEquiv)
  have he (q : FundamentalGroup X b) : mapOfEq f rfl q = e q := by
    have hn := map_fundamentalGroupMulEquivOfPath f p (es.symm q)
    rw [show fundamentalGroupMulEquivOfPath p (es.symm q) = q from
      es.apply_symm_apply q] at hn
    rw [mapOfEq_rfl]
    exact hn
  rw [show (mapOfEq f rfl : FundamentalGroup X b → FundamentalGroup Y (f b)) =
    e from funext he]
  exact e.bijective

/-- A source homotopy triangle calibrates the original fundamental-group
maps by its ACTUAL image-point path. No unrelated basepoint path is chosen. -/
public theorem map_homotopy_naturality {f g : C(X, Y)}
    (H : ContinuousMap.Homotopy f g) (x : X) (q : FundamentalGroup X x) :
    fundamentalGroupMulEquivOfPath (H.evalAt x) (map f x q) = map g x q := by
  let F := FundamentalGroupoid.map f
  let G := FundamentalGroupoid.map g
  let η := FundamentalGroupoidFunctor.homotopicMapsNatIso H
  let p := H.evalAt x
  let α : FundamentalGroupoid.mk (f x) ≅ FundamentalGroupoid.mk (g x) :=
    (Groupoid.isoEquivHom _ _).symm (Path.Homotopic.Quotient.mk p)
  have hα : η.app (FundamentalGroupoid.mk x) = α.hom := rfl
  have hn := η.naturality q.asHom
  rw [hα] at hn
  apply End.ext
  change α.inv ≫ F.map q.asHom ≫ α.hom = G.map q.asHom
  dsimp only [F, G, FundamentalGroupoid.map] at hn ⊢
  rw [hn,
    ← Category.assoc,
    α.inv_hom_id,
    Category.id_comp]

/-- The same source-homotopy calibration retains the specified original
target points and casts its actual path through those literal equalities. -/
public theorem mapOfEq_homotopy_naturality {f g : C(X, Y)}
    (H : ContinuousMap.Homotopy f g) (x : X) {a b : Y}
    (ha : f x = a) (hb : g x = b) (q : FundamentalGroup X x) :
    fundamentalGroupMulEquivOfPath ((H.evalAt x).cast ha.symm hb.symm)
      (mapOfEq f ha q) = mapOfEq g hb q := by
  cases ha
  cases hb
  simpa only [Path.cast_rfl_rfl, mapOfEq_rfl] using map_homotopy_naturality H x q

/-- An actual homotopy preserves killing of each original based loop.
The two image basepoints are connected by its actual trace; the homotopy
need not fix the source point or have equal image basepoints. -/
public theorem mapOfEq_eq_one_iff_of_homotopy {f g : C(X, Y)}
    (H : ContinuousMap.Homotopy f g) (x : X) (p : FundamentalGroup X x) :
    mapOfEq f rfl p = 1 ↔ mapOfEq g rfl p = 1 := by
  let e := fundamentalGroupMulEquivOfPath (H.evalAt x)
  have hn : e (mapOfEq f rfl p) = mapOfEq g rfl p := by
    simpa only [mapOfEq_rfl] using map_homotopy_naturality H x p
  constructor
  · intro hp
    exact hn.symm.trans ((congrArg e hp).trans e.map_one)
  · intro hp
    apply e.injective
    exact hn.trans (hp.trans e.map_one.symm)

end FundamentalGroup

end

end
