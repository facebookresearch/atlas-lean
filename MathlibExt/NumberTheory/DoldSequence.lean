/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Dold sequences

This file records the local trace characterization from Lemma 3 of Klaudiusz
Wójcik, *Binomial Transform and Dold Sequences*:
<https://cs.uwaterloo.ca/journals/JIS/VOL18/Wojcik/wojcik6.tex>.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Dold sequences.** A sequence $a_0, a_1, a_2, \dots$ of integers is a Dold sequence when
for every integer $m \ge 1$ there is an $m \times m$ matrix $A$ with integer entries such that
$a_n = \operatorname{tr}(A^n)$ for every $n$ with $1 \le n \le m$. The term $a_0$ is not
constrained.

Source: Wójcik, *Binomial Transform and Dold Sequences*, Lemma 3; this equivalent trace
characterization is taken here as the definition.
-/
def IsDoldSequence (a : ℕ → ℤ) : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    ∃ A : Matrix (Fin m) (Fin m) ℤ,
      ∀ n : ℕ, 1 ≤ n → n ≤ m → a n = Matrix.trace (A ^ n)

end MetaMathlibExt
