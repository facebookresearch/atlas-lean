/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Lean.Elab.Command

import MathlibExt.Topology.Homotopy.TopCat.SingularFundamentalGroupoid

/-!
# Singular fundamental-groupoid tests

These tests pin the endpoint-relative singular square, its two ordered
shuffle triangles, and the object and edge formulas for the comparison
equivalence.  They make no realization-unit, weak-equivalence, or K-theory
claim.
-/

noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace MathlibExtTest.Topology.Homotopy.TopCat

example {Y : _root_.TopCat.{u}} (p : _root_.TopCat.I.{u} ⟶ Y) :
    SSet.stdSimplex.toSSetObjI ≫ _root_.TopCat.toSSet.map p =
      SSet.yonedaEquiv.symm (_root_.TopCat.toSSetObj₁Equiv.symm p) :=
  _root_.TopCat.toSSetObjI_comp_map_eq_yonedaEdge p

example {Y : _root_.TopCat.{u}} {x y : Y} {p q : Y.Path x y}
    (H : (_root_.TopCat.pathEquiv p).Homotopy
      (_root_.TopCat.pathEquiv q)) (t : unitInterval) :
    _root_.TopCat.Path.homotopyOfPathHomotopy H
        (t, (0 : _root_.TopCat.I.{u})) = x ∧
      _root_.TopCat.Path.homotopyOfPathHomotopy H
        (t, (1 : _root_.TopCat.I.{u})) = y :=
  ⟨by simp, by simp⟩

example {Y : _root_.TopCat.{u}} {x y : Y} {p q : Y.Path x y}
    (H : (_root_.TopCat.pathEquiv p).Homotopy
      (_root_.TopCat.pathEquiv q)) :
    H.toSingularHomotopySourceEdge =
        SSet.Edge.id (_root_.TopCat.toSSetObj₀Equiv.symm x) ∧
      H.toSingularHomotopyTargetEdge =
        SSet.Edge.id (_root_.TopCat.toSSetObj₀Equiv.symm y) :=
  ⟨H.toSingularHomotopy_sourceEdge, H.toSingularHomotopy_targetEdge⟩

example {Y : _root_.TopCat.{u}}
    {x y : (_root_.TopCat.toSSet.obj Y) _⦋0⦌}
    (e : (_root_.TopCat.toSSet.obj Y).Edge x y) :
    _root_.TopCat.toSSetObjEdgeEquiv.symm
        (_root_.TopCat.singularEdgePath e) =
      SSet.Edge.ofEq e
        ((_root_.TopCat.toSSetObj₀Equiv (X := Y)).symm_apply_apply x).symm
        ((_root_.TopCat.toSSetObj₀Equiv (X := Y)).symm_apply_apply y).symm := by
  exact _root_.TopCat.toSSetObjEdgeEquiv_symm_singularEdgePath e

/-- The first shuffle triangle has the original edge horizontally first and
the target-time edge second. -/
example {Y : _root_.TopCat.{u}} {x y : Y} {p q : Y.Path x y}
    (H : (_root_.TopCat.pathEquiv p).Homotopy
      (_root_.TopCat.pathEquiv q))
    {a b : (Δ[1] : SSet.{u}) _⦋0⦌}
    (d : (Δ[1] : SSet.{u}).Edge a b) :
    SSet.Edge.CompStruct
      (d.map (SSet.yonedaEquiv.symm
        (_root_.TopCat.toSSetObjEdgeEquiv.symm p).edge))
      (SSet.Edge.ofSimplicialObjectHomotopy
        H.toSingularHomotopy.toSimplicialObjectHomotopy b)
      (SSet.Edge.diagOfSimplicialObjectHomotopy
        H.toSingularHomotopy.toSimplicialObjectHomotopy d) :=
  SSet.Edge.CompStruct.ofSimplicialObjectHomotopy
    H.toSingularHomotopy.toSimplicialObjectHomotopy d

/-- The second shuffle triangle has the source-time edge first and the new
horizontal edge second. -/
example {Y : _root_.TopCat.{u}} {x y : Y} {p q : Y.Path x y}
    (H : (_root_.TopCat.pathEquiv p).Homotopy
      (_root_.TopCat.pathEquiv q))
    {a b : (Δ[1] : SSet.{u}) _⦋0⦌}
    (d : (Δ[1] : SSet.{u}).Edge a b) :
    SSet.Edge.CompStruct
      (SSet.Edge.ofSimplicialObjectHomotopy
        H.toSingularHomotopy.toSimplicialObjectHomotopy a)
      (d.map (SSet.yonedaEquiv.symm
        (_root_.TopCat.toSSetObjEdgeEquiv.symm q).edge))
      (SSet.Edge.diagOfSimplicialObjectHomotopy
        H.toSingularHomotopy.toSimplicialObjectHomotopy d) :=
  SSet.Edge.CompStruct.ofSimplicialObjectHomotopy'
    H.toSingularHomotopy.toSimplicialObjectHomotopy d

example (Y : _root_.TopCat.{u})
    (x : (_root_.TopCat.toSSet.obj Y) _⦋0⦌) :
    (_root_.TopCat.singularFundamentalGroupoidFunctor Y).obj
        (SSet.FundamentalGroupoid.mk x) =
      _root_.FundamentalGroupoid.mk
        (_root_.TopCat.toSSetObj₀Equiv x) := by
  simp

example (Y : _root_.TopCat.{u})
    {x y : (_root_.TopCat.toSSet.obj Y) _⦋0⦌}
    (e : (_root_.TopCat.toSSet.obj Y).Edge x y) :
    (_root_.TopCat.singularFundamentalGroupoidFunctor Y).map
        (SSet.FundamentalGroupoid.homMk e) =
      Path.Homotopic.Quotient.mk
        ((_root_.TopCat.pathEquiv
          (_root_.TopCat.singularEdgePath e)).cast
            (_root_.TopCat.counit_realizedVertex x)
            (_root_.TopCat.counit_realizedVertex y)) :=
  _root_.TopCat.singularFundamentalGroupoidFunctor_map_homMk Y e

example (Y : _root_.TopCat.{u}) :
    (_root_.TopCat.singularFundamentalGroupoidFunctor Y).EssSurj :=
  _root_.TopCat.singularFundamentalGroupoidFunctor_essSurj Y

example (Y : _root_.TopCat.{u}) :
    (_root_.TopCat.singularFundamentalGroupoidFunctor Y).FullyFaithful :=
  _root_.TopCat.singularFundamentalGroupoidFunctor_fullyFaithful Y

example (Y : _root_.TopCat.{u}) :
    SSet.FundamentalGroupoid (_root_.TopCat.toSSet.obj Y) ≌
      _root_.FundamentalGroupoid Y :=
  _root_.TopCat.singularFundamentalGroupoidEquivalence Y

end MathlibExtTest.Topology.Homotopy.TopCat

end

universe u
open scoped Simplicial

-- The preserved compatibility name supplies the same original fully faithful data.
#check @TopCat.singularFundamentalGroupoidFunctor_fullyFaithful
#print axioms TopCat.singularFundamentalGroupoidFunctor_fullyFaithful

example (Y : TopCat.{u}) : (TopCat.singularFundamentalGroupoidFunctor Y).Full :=
  (TopCat.singularFundamentalGroupoidFunctor_fullyFaithful Y).full

example {Y : TopCat.{u}} {x y : (TopCat.toSSet.obj Y) _⦋0⦌}
    (e : (TopCat.toSSet.obj Y).Edge x y) :
    (TopCat.toSSetObjEdgeEquiv.symm (TopCat.singularEdgePath e)).edge = e.edge :=
  TopCat.toSSetObjEdgeEquiv_symm_singularEdgePath_edge e


run_cmd do
  let env ← Lean.getEnv
  let legacy := `TopCat.singularFundamentalGroupoidFunctor_fullyFaithful
  unless (env.find? legacy).isSome do
    throwError "the original fully faithful name must remain an actual constant"
  unless env.getModuleIdxFor? legacy == env.getModuleIdx?
      `MathlibExt.Topology.Homotopy.TopCat.SingularFundamentalGroupoid do
    throwError "the original declaration must remain in its original module"
