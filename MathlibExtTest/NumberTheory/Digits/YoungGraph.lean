/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.YoungGraph
import Mathlib.Tactic

namespace MetaMathlibExt

example {V : Type*} (pivot : V → Prop) (precedes : V → V → Prop) (v : V)
    (hv : pivot v) : isYoungRetained pivot precedes v :=
  (isYoungRetained_iff pivot precedes v).mpr (Or.inl hv)

example {V : Type*} (pivot : V → Prop) (precedes : V → V → Prop) (v w : V)
    (hw : pivot w) (hvw : precedes v w) : isYoungRetained pivot precedes v :=
  (isYoungRetained_iff pivot precedes v).mpr (Or.inr ⟨w, hw, hvw⟩)

example {V : Type*} (pivot : V → Prop) (precedes : V → V → Prop) (v : V)
    (h : isYoungRetained pivot precedes v) : pivot v ∨ ∃ w, pivot w ∧ precedes v w :=
  (isYoungRetained_iff pivot precedes v).mp h

example {V E L : Type*} (G : LabeledDigraph V E L)
    (pivot : V → Prop) (precedes : V → V → Prop)
    (e : {e : E // isYoungRetained pivot precedes (G.src e) ∧
      isYoungRetained pivot precedes (G.tgt e)}) :
    ((youngGraph G pivot precedes).src e).val = G.src e.val :=
  youngGraph_src G pivot precedes e

example {V E L : Type*} (G : LabeledDigraph V E L)
    (pivot : V → Prop) (precedes : V → V → Prop)
    (e : {e : E // isYoungRetained pivot precedes (G.src e) ∧
      isYoungRetained pivot precedes (G.tgt e)}) :
    ((youngGraph G pivot precedes).tgt e).val = G.tgt e.val :=
  youngGraph_tgt G pivot precedes e

example {V E L : Type*} (G : LabeledDigraph V E L)
    (pivot : V → Prop) (precedes : V → V → Prop)
    (e : {e : E // isYoungRetained pivot precedes (G.src e) ∧
      isYoungRetained pivot precedes (G.tgt e)}) :
    (youngGraph G pivot precedes).label e = G.label e.val :=
  youngGraph_label G pivot precedes e

end MetaMathlibExt
