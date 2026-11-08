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

/-- Śleszyński–Pringsheim convergence criterion, as quoted by Mennen: if the partial numerators
`a k` and partial denominators `b k` satisfy `1 + |a k| ≤ |b k|` for every `k`, then the
continued fraction `a₀ / (b₀ + a₁ / (b₁ + ⋯))` converges to a value `v` with `|v| ≤ 1`.

The continued fraction is Mathlib's `GenContFract` with head `0` and pairs `⟨a k, b k⟩`; its
`n`-th approximant is the nested finite fraction `convs' n`. Stated over `ℂ` (the classical
setting of the criterion), which contains the real case. Zero partial numerators are admitted.

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
