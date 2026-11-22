/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sequence.BaumWelchForwardBackward

/-!
# Baum-Welch forward-backward tests

Closed checks: the count identities instantiated for a two-state HMM over binary observations,
two sequences of length 4, and pairwise forward-backward over the rationals. The counts are
real-valued and not executable.
-/

namespace Cslib.MachineLearning.Sequence.BaumWelch

open Cslib.MachineLearning.Sequence.HiddenMarkov

example (xs : Fin 2 → ℕ → Bool) (h : ValidHMM (Fin 2) Bool) (s : Fin 2) :
    initCount 3 xs h s =
      ∑ n, forward h.1 (xs n) 0 s * backward h.1 (xs n) 3 0 s / likelihood h.1 (xs n) 3 :=
  initCount_eq xs h s

example (xs : Fin 2 → ℕ → Bool) (h : ValidHMM (Fin 2) Bool) (s s' : Fin 2) :
    transCount 3 xs h s s' = ∑ n, ∑ t : Fin 3,
      forward h.1 (xs n) t s * h.1.trans s s' * h.1.emit s' (xs n (t + 1)) *
        backward h.1 (xs n) (3 - t - 1) (t + 1) s' / likelihood h.1 (xs n) 3 :=
  transCount_eq xs h s s'

example (hm : HMM (Fin 2) Bool ℚ) (x : ℕ → Bool) (s s' : Fin 2) :
    pairMarg hm x 1 2 s s' = forward hm x 1 s * hm.trans s s' * hm.emit s' (x 2) *
      backward hm x 2 2 s' :=
  pairMarg_eq hm x 1 2 s s'

#print axioms emitCount_eq
#print axioms transCount_eq

end Cslib.MachineLearning.Sequence.BaumWelch
