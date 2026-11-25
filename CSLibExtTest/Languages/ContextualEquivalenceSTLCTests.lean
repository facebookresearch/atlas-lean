/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.ContextualEquivalence
public import CSLibExt.Languages.ContextualEquivalenceSTLC
public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Contextual

/-!
# STLC contextual equivalence tests

Tests for the STLC model equality family: a beta example and a reflexivity
example.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Languages.ContextualEquivalenceSTLCTests

open Cslib.Languages.ContextualEquivalence.STLC
open Cslib.Languages.LambdaCalculus.Stlc
open scoped CslibStlc

universe u

/-- Beta example for the STLC model equality family. -/
theorem modelEq_family_beta_example {Base : Type u} {A : Ty Base} :
    modelEqFamily Base ([], A ⇒ A)
      (.app (.lam (.var .zero)) (.lam (.var .zero)))
      (Tm.instantiate (.var .zero) (.lam (.var .zero))) := by exact ModelEq.beta _ _

/-- Reflexivity example for the STLC model equality family. -/
theorem modelEq_family_refl_example {Base : Type u} {A : Ty Base} :
    modelEqFamily Base ([A], A) (.var .zero) (.var .zero) := by exact ModelEq.refl _

end Cslib.Languages.ContextualEquivalenceSTLCTests
