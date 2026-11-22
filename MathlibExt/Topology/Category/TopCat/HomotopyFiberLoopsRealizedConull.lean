/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyFiberLoopsOfBasedContraction
public import MathlibExt.Topology.Category.TopCat.RealizedVertexBasedContraction

/-!
# Full homotopy fibers and loops from realized total conullity

Derive the actual based contraction at the original realized vertex from
terminal weakness, then specialize the generic full homotopy-fiber/loop
construction. The original total, projection, base point, full carried paths
and both actual relative inverse families are retained.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Topology
open scoped unitInterval Topology.Homotopy Simplicial

universe u

namespace TopCat

/-- The genuine full-path return map derives its contraction from original total conullity. -/
def homotopyFiberToLoopsOfRealizedConull (K : SSet.{u}) (x : K _⦋0⦌)
    {B : TopCat.{u}} (p : SSet.toTop.obj K ⟶ B) (b : B)
    (he : p (SSet.realizedVertex x) = b)
    (hK : weakHomotopyEquivalences (terminal.from (SSet.toTop.obj K))) :
    homotopyFiber p b ⟶ TopCat.of (LoopSpace B b) :=
  homotopyFiberToLoopsOfBasedContraction p (SSet.realizedVertex x) b he
    (SSet.basedContractionAtRealizedVertex K x hK)

/-- The inverse path is the reverse projected contraction followed by the whole carried path. -/
theorem homotopyFiberToLoopsOfRealizedConull_apply (K : SSet.{u}) (x : K _⦋0⦌)
    {B : TopCat.{u}} (p : SSet.toTop.obj K ⟶ B) (b : B)
    (he : p (SSet.realizedVertex x) = b)
    (hK : weakHomotopyEquivalences (terminal.from (SSet.toTop.obj K)))
    (z : homotopyFiber p b) (t : unitInterval) :
    homotopyFiberToLoopsOfRealizedConull K x p b he hK z t =
      if ht : (t : ℝ) ≤ 1 / 2 then
        p ((SSet.basedContractionAtRealizedVertex K x hK).homotopy.symm.toContinuousMap
          (⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩,
            homotopyFiberToTotal p b z))
      else
        homotopyFiberPath p b z
          ((TopCat.I.homeomorph.{u}).symm
            ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2
              ⟨(not_le.1 ht).le, t.2.2⟩⟩) :=
  homotopyFiberToLoopsOfBasedContraction_apply p (SSet.realizedVertex x) b he
    (SSet.basedContractionAtRealizedVertex K x hK) z t

/-- The independently selected original fiber point is sent to the constant based loop. -/
theorem homotopyFiberToLoopsOfRealizedConull_selectedPoint (K : SSet.{u}) (x : K _⦋0⦌)
    {B : TopCat.{u}} (p : SSet.toTop.obj K ⟶ B) (b : B)
    (he : p (SSet.realizedVertex x) = b)
    (hK : weakHomotopyEquivalences (terminal.from (SSet.toTop.obj K))) :
    homotopyFiberSelectedPointMap p (SSet.realizedVertex x) b he ≫
        homotopyFiberToLoopsOfRealizedConull K x p b he hK =
      (TopCat.const (Path.refl b) : TopCat.of PUnit.{u + 1} ⟶ TopCat.of (LoopSpace B b)) :=
  homotopyFiberToLoopsOfBasedContraction_selectedPoint p (SSet.realizedVertex x) b he
    (SSet.basedContractionAtRealizedVertex K x hK)

/-- Both actual full-path inverse homotopies identify the original fiber with its loop space. -/
def realizedConullHomotopyFiberLoopEquiv (K : SSet.{u}) (x : K _⦋0⦌)
    {B : TopCat.{u}} (p : SSet.toTop.obj K ⟶ B) (b : B)
    (he : p (SSet.realizedVertex x) = b)
    (hK : weakHomotopyEquivalences (terminal.from (SSet.toTop.obj K))) :
    ContinuousMap.HomotopyEquiv (homotopyFiber p b) (LoopSpace B b) :=
  homotopyFiberLoopEquivOfBasedContraction p (SSet.realizedVertex x) b he
    (SSet.basedContractionAtRealizedVertex K x hK)

/-- The forward map is the derived return carrying every original path. -/
theorem realizedConullHomotopyFiberLoopEquiv_toFun (K : SSet.{u}) (x : K _⦋0⦌)
    {B : TopCat.{u}} (p : SSet.toTop.obj K ⟶ B) (b : B)
    (he : p (SSet.realizedVertex x) = b)
    (hK : weakHomotopyEquivalences (terminal.from (SSet.toTop.obj K))) :
    (realizedConullHomotopyFiberLoopEquiv K x p b he hK).toFun =
      (homotopyFiberToLoopsOfRealizedConull K x p b he hK).hom :=
  homotopyFiberLoopEquivOfBasedContraction_toFun p (SSet.realizedVertex x) b he
    (SSet.basedContractionAtRealizedVertex K x hK)

/-- The inverse is exactly the existing full selected-loop inclusion. -/
theorem realizedConullHomotopyFiberLoopEquiv_invFun (K : SSet.{u}) (x : K _⦋0⦌)
    {B : TopCat.{u}} (p : SSet.toTop.obj K ⟶ B) (b : B)
    (he : p (SSet.realizedVertex x) = b)
    (hK : weakHomotopyEquivalences (terminal.from (SSet.toTop.obj K))) :
    (realizedConullHomotopyFiberLoopEquiv K x p b he hK).invFun =
      (loopToHomotopyFiber p (SSet.realizedVertex x) b he).hom :=
  homotopyFiberLoopEquivOfBasedContraction_invFun p (SSet.realizedVertex x) b he
    (SSet.basedContractionAtRealizedVertex K x hK)

/-- The very same fiber-side inverse family used in the ordinary equivalence
is relative to the independently constructed constant-path selected point. -/
@[nolint defsWithUnderscore] -- component name of the equivalence; used downstream
def realizedConullHomotopyFiberLoopEquiv_leftHomotopyRel
    (K : SSet.{u}) (x : K _⦋0⦌)
    {B : TopCat.{u}} (p : SSet.toTop.obj K ⟶ B) (b : B)
    (he : p (SSet.realizedVertex x) = b)
    (hK : weakHomotopyEquivalences (terminal.from (SSet.toTop.obj K))) :
    ContinuousMap.HomotopyRel
      ((realizedConullHomotopyFiberLoopEquiv K x p b he hK).invFun.comp
        (realizedConullHomotopyFiberLoopEquiv K x p b he hK).toFun)
      (ContinuousMap.id (homotopyFiber p b))
      {homotopyFiberSelectedPointMap p (SSet.realizedVertex x) b he PUnit.unit} :=
  homotopyFiberLoopEquivOfBasedContraction_leftHomotopyRel p (SSet.realizedVertex x) b he
    (SSet.basedContractionAtRealizedVertex K x hK)

/-- The ordinary loop-side affine inverse family is relative to the literal
constant loop, at every time and on the entire raw compact-open loop space. -/
@[nolint defsWithUnderscore] -- component name of the equivalence; used downstream
def realizedConullHomotopyFiberLoopEquiv_rightHomotopyRel
    (K : SSet.{u}) (x : K _⦋0⦌)
    {B : TopCat.{u}} (p : SSet.toTop.obj K ⟶ B) (b : B)
    (he : p (SSet.realizedVertex x) = b)
    (hK : weakHomotopyEquivalences (terminal.from (SSet.toTop.obj K))) :
    ContinuousMap.HomotopyRel
      ((realizedConullHomotopyFiberLoopEquiv K x p b he hK).toFun.comp
        (realizedConullHomotopyFiberLoopEquiv K x p b he hK).invFun)
      (ContinuousMap.id (LoopSpace B b)) {Path.refl b} :=
  homotopyFiberLoopEquivOfBasedContraction_rightHomotopyRel p (SSet.realizedVertex x) b he
    (SSet.basedContractionAtRealizedVertex K x hK)

end TopCat

end
