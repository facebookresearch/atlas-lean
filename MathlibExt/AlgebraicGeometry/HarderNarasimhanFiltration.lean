/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CurveVectorBundles
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Slope semistability and Harder–Narasimhan filtrations on curves

On a smooth integral proper curve, semistability of a vector bundle of
positive rank tests its saturated subbundles of intermediate rank, expressed
by an actual monomorphism from a vector bundle with a locally free cokernel.
On such a curve every coherent subsheaf of a vector bundle is locally free
and its saturation is a subbundle of the same rank and at least the same
slope, so this is equivalent to testing all coherent subsheaves. (On singular or reducible
curves subbundles of one constant rank do not suffice, so the interface is
not stated there.) A filtration is a finite chain of actual bundle
monomorphisms, starting at zero and ending at the specified bundle, whose
cokernels are vector bundles of positive rank that are semistable with
strictly decreasing slopes. The chain is empty exactly for the bundle of
rank zero, which is the zero sheaf.

Reference: Huybrechts–Lehn, *The Geometry of Moduli Spaces of Sheaves*,
Section 1.3, https://doi.org/10.1017/CBO9780511711985.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HarderNarasimhanFiltration

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.CurveVectorBundles

universe u

/-- Slope semistability of a vector bundle `E` of positive rank `r` on a smooth
integral proper curve: every saturated subbundle of rank `0 < s < r`, that is an
actual monomorphism `F ⟶ E` from a vector bundle of rank `s` whose cokernel is a
vector bundle of rank `r - s`, has slope at most the slope of `E`. -/
def IsSemistable {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProperCurve f] [SmoothOfRelativeDimension 1 f] [IsIntegral X]
    (E : X.Modules) (r : ℕ)
    (hE : IsVectorBundle E r) (hr : 0 < r) : Prop :=
  ∀ (s : ℕ) (hs : 0 < s), s < r →
    ∀ (F : X.Modules) (i : F ⟶ E), Mono i → ∀ hF : IsVectorBundle F s,
      IsVectorBundle (cokernel i) (r - s) → slope f F s hF hs ≤ slope f E r hE hr

/-- A Harder–Narasimhan filtration `0 = E₀ ⊂ E₁ ⊂ ⋯ ⊂ Eₙ ≅ E` of a vector bundle
of rank `r` on a smooth integral proper curve: actual monomorphisms of vector
bundles of strictly increasing ranks whose cokernels are semistable vector
bundles with strictly decreasing slopes. The number of steps `n` is zero exactly
when `r = 0`, for the zero bundle. -/
structure Filtration {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProperCurve f] [SmoothOfRelativeDimension 1 f] [IsIntegral X]
    (E : X.Modules) (r : ℕ) where
  /-- The number of steps. -/
  steps : ℕ
  /-- The bundles of the filtration. -/
  bundle : Fin (steps + 1) → X.Modules
  /-- Their ranks. -/
  rank : Fin (steps + 1) → ℕ
  zero : IsZero (bundle 0)
  rank_zero : rank 0 = 0
  /-- The last bundle is `E`. -/
  final : bundle (Fin.last steps) ≅ E
  rank_final : rank (Fin.last steps) = r
  locallyFree : ∀ j, IsVectorBundle (bundle j) (rank j)
  /-- The inclusions of consecutive bundles. -/
  inclusion : ∀ j : Fin steps, bundle j.castSucc ⟶ bundle j.succ
  monic : ∀ j, Mono (inclusion j)
  rank_increases : ∀ j : Fin steps, rank j.castSucc < rank j.succ
  /-- Each graded piece is a vector bundle of the rank difference. -/
  quotientLocallyFree : ∀ j : Fin steps,
    IsVectorBundle (cokernel (inclusion j)) (rank j.succ - rank j.castSucc)
  semistable : ∀ j : Fin steps,
    IsSemistable f (cokernel (inclusion j)) (rank j.succ - rank j.castSucc)
      (quotientLocallyFree j) (Nat.sub_pos_of_lt (rank_increases j))
  slope_decreases : ∀ i j : Fin steps, i < j →
    slope f (cokernel (inclusion j)) (rank j.succ - rank j.castSucc)
        (quotientLocallyFree j) (Nat.sub_pos_of_lt (rank_increases j)) <
      slope f (cokernel (inclusion i)) (rank i.succ - rank i.castSucc)
        (quotientLocallyFree i) (Nat.sub_pos_of_lt (rank_increases i))

end MathlibExt.AlgebraicGeometry.HarderNarasimhanFiltration
