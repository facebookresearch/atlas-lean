/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExtTest.Logics.LTL.ModelCheckingTests

/-!
# Kernel replay of temporal model-checker computations

These bounded, full-until computations are kept separate from the faster
semantic/lasso consumers. They evaluate the actual finite-state product and
reachability closure, with no native decision procedure or assumed oracle.
-/

@[expose] public section

namespace Cslib.LTL.ModelCheckingTests

open ModelChecking

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- A real until counterexample, not just a propositional checker smoke test. -/
example : checkB stutter one labels (.until .top (.atom 1)) = false := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The temporal happy path succeeds on an inhabited infinite model. -/
example : checkB stutter one labels (.until .top (.atom 0)) = true := by decide

end Cslib.LTL.ModelCheckingTests
