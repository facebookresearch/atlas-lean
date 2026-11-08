/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Digraph.LabeledDigraph
import Mathlib.Tactic

namespace MetaMathlibExt

example {V E L : Type*} (G H : LabeledDigraph V E L)
    (hsrc : G.src = H.src) (htgt : G.tgt = H.tgt) (hlabel : G.label = H.label) :
    G = H :=
  LabeledDigraph.ext hsrc htgt hlabel

example {V E L : Type*} (G : LabeledDigraph V E L) : G = G := by
  ext <;> rfl

example {V E L : Type*} (G : LabeledDigraph V E L) (p : V → Prop)
    (e : {e : E // p (G.src e) ∧ p (G.tgt e)}) :
    ((G.restrict p).src e).val = G.src e.val :=
  LabeledDigraph.restrict_src G p e

example {V E L : Type*} (G : LabeledDigraph V E L) (p : V → Prop)
    (e : {e : E // p (G.src e) ∧ p (G.tgt e)}) :
    ((G.restrict p).tgt e).val = G.tgt e.val :=
  LabeledDigraph.restrict_tgt G p e

example {V E L : Type*} (G : LabeledDigraph V E L) (p : V → Prop)
    (e : {e : E // p (G.src e) ∧ p (G.tgt e)}) :
    (G.restrict p).label e = G.label e.val :=
  LabeledDigraph.restrict_label G p e

end MetaMathlibExt
