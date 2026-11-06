/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic

/-!
# Perrin sequence

Sources:
<https://cs.uwaterloo.ca/journals/JIS/VOL11/Marichal/marichal.tex>,
<https://cs.uwaterloo.ca/journals/JIS/VOL16/MacHenry/machenry7.tex>, and
<https://cs.uwaterloo.ca/journals/JIS/VOL23/Togbe/togbe16.tex>.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Perrin sequence.** The Perrin sequence $E_n$, for natural numbers $n$, is defined by
$E_0 = 3$, $E_1 = 0$, $E_2 = 2$ and $E_n = E_{n-2} + E_{n-3}$ for every $n \ge 3$.

Source: JIS concept `jis_sem_4f37e8f82153e07bac03f158`; statements
`jis_013645d8a02b3ef65aa100f4`, `jis_4a7feefed2ca398758f666fc`, and
`jis_6027c59af02d1d1dfc3e7b1a`. -/
def perrinSequence : Nat → Nat
  | 0 => 3
  | 1 => 0
  | 2 => 2
  | (n + 3) => perrinSequence (n + 1) + perrinSequence n

end

end MetaMathlibExt
