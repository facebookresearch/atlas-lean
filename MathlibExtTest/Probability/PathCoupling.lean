/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.PathCoupling

/-- Boundary check: at time `0` with equal starts the left side is
the distance of a point mass to itself, `0`, bounded by
`dist x x / δ = 0` for any coupling data; here we instantiate the
statement shape with an abstract coupling. -/
example {α : Type*} [PseudoMetricSpace α] [Fintype α]
    (K : α → PMF α) (C : α → α → PMF (α × α))
    (hC_fst : ∀ x y, (C x y).map Prod.fst = K x)
    (hC_snd : ∀ x y, (C x y).map Prod.snd = K y)
    {β δ : ℝ} (hβ : β ≤ 1) (hδ : 0 < δ)
    (hdist : ∀ x y : α, x ≠ y → δ ≤ dist x y)
    (hcontract : ∀ x y, ∑ z, (C x y z).toReal * dist z.1 z.2 ≤
      β * dist x y)
    (x y : α) :
    tvDist (chainDist K x 0) (chainDist K y 0) ≤ β ^ 0 * dist x y / δ :=
  path_coupling_tv K C hC_fst hC_snd hβ hδ hdist hcontract x y 0
