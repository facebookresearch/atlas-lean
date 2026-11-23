/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.ContextualEquivalence
public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Contextual

/-!
# STLC instance of contextual equivalence

The STLC instance of generic contextual equivalence over STLC terms and one-hole contexts.
There is no operational contextual equivalence relation for STLC to
bridge to; `ModelEq` is registered only as a context-closed equivalence family. No equality,
adequacy, or coincidence claim with any operational observation is made. No STLC observations,
bridges, or compatibility results appear here.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Languages.ContextualEquivalence.STLC

open Cslib.Languages.LambdaCalculus.Stlc

universe u

/-- Context algebra from STLC terms and one-hole contexts. -/
def stlcAlgebra (Base : Type u) : CtxAlgebra (List (Ty Base) × Ty Base) where
  Tm := fun j => Tm j.1 j.2
  Ctx := fun j k => TmCtx j.1 j.2 k.1 k.2
  plug := fun C t => TmCtx.plug C t
  hole := TmCtx.hole
  comp := fun D C => TmCtx.comp D C
  plug_hole := fun t => TmCtx.plug_hole t
  plug_comp := fun D C t => TmCtx.plug_comp D C t

/-- STLC model equality as a judgment-indexed relation family. -/
def modelEqFamily (Base : Type u) : RelFamily (stlcAlgebra Base) :=
  fun _j t u => ModelEq t u

/-- The STLC model equality family is closed under contexts. -/
theorem modelEqFamily_ctxClosed {Base : Type u} :
    CtxClosed (modelEqFamily Base) := by intro _ _ C _ _ h; exact ModelEq.context C h

/-- The STLC model equality family is an equivalence at each judgment. -/
theorem modelEqFamily_equiv {Base : Type u}
    {j : List (Ty Base) × Ty Base} :
    Equivalence (modelEqFamily Base j) := by exact ModelEq.equivalence

end Cslib.Languages.ContextualEquivalence.STLC
