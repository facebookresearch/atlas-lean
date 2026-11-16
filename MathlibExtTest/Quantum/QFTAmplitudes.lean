/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.QFTAmplitudes

@[expose] public section

/-- With `N = 1`, `s = 1`, the single amplitude has normSq 1. -/
example : ∑ k ∈ Finset.range 1, Complex.normSq (qftAmp 1 1 0 k) = 1 :=
  qftAmp_norm_sum (N := 1) 1 (by norm_num) 1 (by norm_num) 0

end
