/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.ContextualEquivalencePCF
public import CSLibExt.Languages.LambdaCalculus.PCF.ContextualEquivalence
public import CSLibExt.Languages.LambdaCalculus.PCF.SmallStep

/-!
# PCF contextual equivalence tests

Tests for the PCF instance of generic contextual equivalence: a nonvacuity statement separating
a diverging term from a numeral, and examples of generic equivalence and approximation. No STLC
work appears here.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Languages.ContextualEquivalencePCFTests

open Cslib.Languages.ContextualEquivalence
open Cslib.Languages.ContextualEquivalence.PCF
open Cslib.Languages.LambdaCalculus.PCF

/-- A diverging term is not equivalent to the numeral one. -/
theorem omega_not_ctxEquiv_one :
    ¬ CtxEquiv pcfObs (j := ([], .nat))
      (.fix (.lam (.var .zero)) : Tm [] .nat) (Tm.numeral 1) := by
  intro h
  have _hEquiv := pcf_ctxEquiv_iff.mp h
  have _hEval := (_hEquiv Ctx.hole 1).mpr (Tm.Eval.numeral 1)
  rw [Ctx.plug_hole] at _hEval
  have _hBot : ∀ η, Tm.denote (.fix (.lam (.var .zero)) : Tm [] .nat) η = ⊥ := by
    intro η
    rw [Tm.denote_fix]
    exact le_antisymm (OmegaCompletePartialOrder.ContinuousHom.lfp_le _ le_rfl) bot_le
  have _hDenote := Tm.Eval.denote_numeral _hEval PUnit.unit
  rw [_hBot PUnit.unit] at _hDenote
  exact Part.notMem_none 1 (_hDenote ▸ Part.mem_some 1)

/-- Predecessor of successor is equivalent to the identity. -/
theorem predSucc_generic_equiv_example :
    CtxEquiv pcfObs (j := ([Ty.nat], .nat))
      (.pred (.succ (.var .zero)) : Tm [Ty.nat] .nat) (.var .zero) := by
  refine pcf_ctxEquiv_iff.mpr ?_
  refine Tm.ctxEquiv_of_denote_eq ?_
  refine OmegaCompletePartialOrder.ContinuousHom.ext _ _ fun η => ?_
  rw [Tm.denote_pred, Tm.denote_succ, Part.map_map]
  exact Part.map_id' (fun _ => rfl) _

/-- A diverging term approximates zero. -/
theorem omega_generic_approx_zero_example :
    CtxApprox pcfObs (j := ([], .nat))
      (.fix (.lam (.var .zero)) : Tm [] .nat) .zero := by
  refine pcf_ctxApprox_iff.mpr ?_
  refine Tm.ctxApprox_of_denote_le fun η => ?_
  rw [Tm.denote_fix]
  exact le_trans (OmegaCompletePartialOrder.ContinuousHom.lfp_le _ le_rfl) bot_le

end Cslib.Languages.ContextualEquivalencePCFTests
