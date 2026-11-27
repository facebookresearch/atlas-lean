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

import MathlibExt.Topology.Homotopy.LoopComponentsMap

/-!
# Based loop-component map tests

These tests pin mixed-universe inference, the literal basepoint-conjugation
order, and descent from endpoint-fixed homotopies.  They also guard the
intended set-level scope: this module does not install a group structure on
loop components.
-/

noncomputable section

universe u v

namespace MathlibExtTest.Topology.Homotopy.LoopComponentsMapTests

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) {x : X} {y : Y} (p : Path (f x) y)

/-- The generic based map supports different source and target universes. -/
example : FundamentalGroup X x →* FundamentalGroup Y y :=
  basedFundamentalGroupMap f p

/-- The representative formula pins the order `p⁻¹`, mapped loop, `p`. -/
example (gamma : LoopSpace X x) :
    basedFundamentalGroupMap f p
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk gamma)) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (p.symm.trans ((gamma.map f.continuous).trans p))) :=
  basedFundamentalGroupMap_mk f p gamma

/-- The component map has the same literal representative formula. -/
example (gamma : LoopSpace X x) :
    loopComponentsMap f p (ZerothHomotopy.mk gamma) =
      ZerothHomotopy.mk
        (p.symm.trans ((gamma.map f.continuous).trans p)) :=
  loopComponentsMap_mk f p gamma

/-- Endpoint-fixed homotopy is sufficient for equality after quotienting. -/
example {gamma delta : LoopSpace X x} (h : gamma.Homotopic delta) :
    ZerothHomotopy.mk gamma = ZerothHomotopy.mk delta :=
  zerothHomotopy_mk_eq_of_pathHomotopic h

/-- No global group structure is introduced on loop components. -/
example : True := by
  fail_if_success
    have witness : Group (ZerothHomotopy (LoopSpace X x)) := inferInstance
  trivial

/-- Installing the transported group locally makes the guard fail. -/
example : True := by
  let : Group (ZerothHomotopy (LoopSpace X x)) :=
    (loopComponentsEquivFundamentalGroup X x).group
  fail_if_success
    fail_if_success
      have witness : Group (ZerothHomotopy (LoopSpace X x)) := inferInstance
  trivial

end MathlibExtTest.Topology.Homotopy.LoopComponentsMapTests
