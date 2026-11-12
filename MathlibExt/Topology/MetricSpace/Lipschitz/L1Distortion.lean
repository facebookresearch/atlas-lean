/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Babak Modami
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Geometry 514

open MeasureTheory

/-!
# L1 distortion of a metric space

## References

* https://arxiv.org/abs/0910.2024 page 1 before Theorem 1.1 (for `c1`)

## References

* https://arxiv.org/abs/0910.2024 page 1 before Theorem 1.1 (for `c1`)

## References

* https://arxiv.org/abs/0910.2024 page 1 before Theorem 1.1 (for `c1`)

## References

* https://arxiv.org/abs/0910.2024 page 1 before Theorem 1.1 (for `c1`)

## References

* https://arxiv.org/abs/0910.2024 page 1 before Theorem 1.1 (for `c1`)

## References

* https://arxiv.org/abs/0910.2024 page 1 before Theorem 1.1 (for `c1`)

## References

* https://arxiv.org/abs/0910.2024 page 1 before Theorem 1.1 (for `c1`)
-/

namespace MetaMathlibExt

-- Geometry 514: L1 distortion of a metric space

def IsStdL1EmbeddingWithDistortion (X : Type*) (ρ : X × X → ℝ)
    (f : X → (Lp ℝ 1 (volume : Measure ℝ))) (D : ℝ) : Prop :=
  1 ≤ D ∧ ∀ x y : X, ρ (x, y) ≠ 0 →
    ρ (x, y) ≤ ‖f x - f y‖ ∧ ‖f x - f y‖ ≤ D * ρ (x, y)

def HasStdL1DistortionLe (X : Type*) (ρ : X × X → ℝ) (D : ℝ) : Prop :=
  ∃ f : X → (Lp ℝ 1 (volume : Measure ℝ)), IsStdL1EmbeddingWithDistortion X ρ f D

/-- Let ρ : X × X  → ℝ, the L₁ distortion of (X,ρ),
denoted c₁(X,ρ), is the infimum over D ≥ 1 for which there
exists a mapping f : X → L₁ such that (‖ f (x)-f (y) ‖₁)/(ρ(x,y)) ∈ [1,D] for all x,y ∈ X with
ρ(x,y) ≠ 0. If no such D exists we set
c₁(X,d)= ∞.

The L₁ distortion is usually defined for a metric space (X,d). We define c₁(X,ρ) for any ρ : X × X
→ ℝ to avoid having to prove rho is a metric in applications which could be cumbersome in lean.
-/
noncomputable def c1 (X : Type*) (ρ : X × X → ℝ) : WithTop ℝ :=
  sInf ((WithTop.some : ℝ → WithTop ℝ) '' { D | HasStdL1DistortionLe X ρ D })

end MetaMathlibExt

end
