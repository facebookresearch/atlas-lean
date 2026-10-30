/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sequence.BaumWelch

/-!
# Baum-Welch tests

Closed checks: the theorems instantiated for a two-state HMM over binary observations, three
sequences of length 5. They cover the monotone likelihood along the Baum-Welch iterates and the
M-step maximizing `Q` against an arbitrary valid HMM. The definitions are real-valued and not
executable.
-/

namespace Cslib.MachineLearning.Sequence.BaumWelch

open Real Cslib.MachineLearning.LatentVariable.ExpectationMaximization
open Cslib.MachineLearning.Sequence.HiddenMarkov

example (xs : Fin 3 → ℕ → Bool) (hx : Rich 4 xs) (h₀ : ValidHMM (Fin 2) Bool) {s t : ℕ}
    (hst : s ≤ t) :
    ∑ n, log (likelihood ((emStep 4 xs hx)^[s] h₀).1 (xs n) 4) ≤
      ∑ n, log (likelihood ((emStep 4 xs hx)^[t] h₀).1 (xs n) 4) :=
  logLik_iterate_emStep_monotone 4 xs hx h₀ hst

example (xs : Fin 3 → ℕ → Bool) (hx : Rich 4 xs) (h h' : ValidHMM (Fin 2) Bool) :
    emQ (joint 4) xs h' h ≤ emQ (joint 4) xs (emStep 4 xs hx h) h :=
  emQ_le_emStep 4 xs hx h' h

#print axioms logLik_iterate_emStep_monotone
#print axioms emQ_le_emStep

end Cslib.MachineLearning.Sequence.BaumWelch
