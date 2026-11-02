/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.CommaSequence

namespace MetaMathlibExt

@[expose] public section

/-- **Comma sequences terminate in bases 3 to 633.** For every base $b$ with $3 \le b \le 633$
and every positive integer $v$, the comma sequence in base $b$ starting at $v$ terminates, that
is, there is no infinite comma sequence in base $b$ starting at $v$.

Source: Dougherty, *Comma Sequences*, JIS 28, lines 134–137. -/
public theorem_wanted commaSequence_terminates_of_base_le_633
    (b v : ℕ) (hb1 : 3 ≤ b) (hb2 : b ≤ 633) (hv : 0 < v) :
    IsCommaTerminating b v

end

end MetaMathlibExt
