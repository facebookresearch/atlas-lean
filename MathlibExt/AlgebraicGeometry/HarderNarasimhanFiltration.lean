/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CurveVectorBundles

/-!
# Slope semistability and Harder–Narasimhan filtrations on curves

Semistability tests saturated positive-rank subbundles, expressed by an
actual monomorphism and a locally free cokernel. A filtration is a finite
chain of actual bundle monomorphisms with semistable cokernels of strictly
decreasing slopes, starting at zero and ending at the specified bundle.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HarderNarasimhanFiltration

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CurveVectorBundles

universe u

def IsSemistable {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (E : X.Modules) (r : ℕ) : Prop :=
  IsVectorBundle E r ∧ ∀ (s : ℕ), 0 < s → s < r →
    ∀ (F : X.Modules) (i : F ⟶ E), Mono i → IsVectorBundle F s →
      IsVectorBundle (cokernel i) (r - s) → slope f F s ≤ slope f E r

structure Filtration {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (E : X.Modules) (r : ℕ) where
  steps : ℕ
  steps_pos : 0 < steps
  bundle : Fin (steps + 1) → X.Modules
  rank : Fin (steps + 1) → ℕ
  zero : IsZero (bundle 0)
  rank_zero : rank 0 = 0
  final : bundle (Fin.last steps) ≅ E
  rank_final : rank (Fin.last steps) = r
  locallyFree : ∀ j, IsVectorBundle (bundle j) (rank j)
  inclusion : ∀ j : Fin steps, bundle j.castSucc ⟶ bundle j.succ
  monic : ∀ j, Mono (inclusion j)
  rank_increases : ∀ j : Fin steps, rank j.castSucc < rank j.succ
  semistable : ∀ j : Fin steps,
    IsSemistable f (cokernel (inclusion j)) (rank j.succ - rank j.castSucc)
  slope_decreases : ∀ i j : Fin steps, i < j →
    slope f (cokernel (inclusion j)) (rank j.succ - rank j.castSucc) <
      slope f (cokernel (inclusion i)) (rank i.succ - rank i.castSucc)

end MathlibExt.AlgebraicGeometry.HarderNarasimhanFiltration
