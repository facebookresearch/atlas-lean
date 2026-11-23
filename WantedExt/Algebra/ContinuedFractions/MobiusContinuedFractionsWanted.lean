/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.ContinuedFractions.Basic
public import Mathlib.Analysis.Complex.Basic

namespace MetaMathlibExt

@[expose] public section

open Filter Topology

/-- **Śleszyński–Pringsheim convergence criterion.** Let $a_0, a_1, a_2, \dots$ and
$b_0, b_1, b_2, \dots$ be complex numbers with $1 + |a_k| \le |b_k|$ for every $k$. For $n \ge 0$
let $f_n$ be the $n$-th approximant of the continued fraction $a_0 / (b_0 + a_1 / (b_1 + \cdots))$,
that is $f_0 = 0$ and $f_n = a_0 / (b_0 + a_1 / (b_1 + \cdots + a_{n-1} / b_{n-1}))$ for $n \ge 1$.
Then there is a complex number $v$ with $|v| \le 1$ such that $f_n \to v$ as $n \to \infty$.

Zero partial numerators are admitted.

Source: Carminda M. Mennen, *Möbius Maps and Continued Fractions*, INTEGERS 24 (2024),
Article A52, Theorem 1 (`integers-2024-A52-thm-1`). -/
public theorem_wanted contFract_tendsto_of_pringsheim (a b : ℕ → ℂ)
    (h : ∀ k, 1 + ‖a k‖ ≤ ‖b k‖) :
    ∃ v : ℂ, ‖v‖ ≤ 1 ∧
      Tendsto
        (fun n ↦ (⟨0, Stream'.Seq.ofStream fun k ↦ ⟨a k, b k⟩⟩ : GenContFract ℂ).convs' n)
        atTop (𝓝 v)

end

end MetaMathlibExt
