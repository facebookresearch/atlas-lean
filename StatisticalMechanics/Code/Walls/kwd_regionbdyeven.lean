/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































import Mathlib
import Code.Ising.KramersWannierClose
import Code.Ising.KramersWannierDuality
import Code.Ising.KramersWannierGeneral
import Code.Ising.KWClosedWalkParity

open scoped BigOperators
open Finset SimpleGraph

namespace StatMech

namespace Walls

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Gp : SimpleGraph V} [DecidableRel Gp.Adj]




















theorem kwd_regionbdyeven (S : V → Bool) :
    EvenOnCycles Gp (regionBoundary Gp S) :=
  evenOnCycles_of_isCoboundary S (fun h => mem_regionBoundary_iff S h)









theorem kwd_regionbdyeven_walkParity (S : V → Bool) {x : V} (p : Gp.Walk x x) :
    walkParity Gp (regionBoundary Gp S) p = false :=
  kwd_regionbdyeven S x p






omit [DecidableEq V] in




theorem kwd_regionbdyeven_mem_iff (S : V → Bool) {u v : V} (h : Gp.Adj u v) :
    s(u, v) ∈ regionBoundary Gp S ↔ S u ≠ S v :=
  mem_regionBoundary_iff S h

end Walls

end StatMech
