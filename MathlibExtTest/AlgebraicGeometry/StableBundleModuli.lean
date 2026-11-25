/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.StableBundleModuli

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.StableBundleModuli

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open _root_.MathlibExt.AlgebraicGeometry.CurveVectorBundles

universe u

variable {k : Type u} [Field k]

-- Every line bundle is stable: there is no subbundle rank strictly between `0` and `1`.
example {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProperCurve f]
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] (L : X.Modules) (hL : IsVectorBundle L 1) :
    IsStable f L 1 hL one_pos :=
  fun _ hs hs1 ↦ absurd hs1 (by omega)

variable [IsAlgClosed k] (C : Over (Spec (.of k))) [IsProperCurve C.hom]
  [SmoothOfRelativeDimension 1 C.hom] [IsIntegral C.left]

-- The dimension `r²(g - 1) + 1` is computed in `ℤ`: rank two in genus two gives `5`.
example (d : ℤ) (M : StableModuliModel C 2 two_pos d) (hg : genus C.hom = 2) :
    M.dimension = 5 := by
  have := M.dimension_eq
  rw [hg] at this
  omega

-- Line bundles on a genus-zero curve: dimension `0`, not the `1` of truncated subtraction.
example (d : ℤ) (M : StableModuliModel C 1 one_pos d) (hg : genus C.hom = 0) :
    M.dimension = 0 := by
  have := M.dimension_eq
  rw [hg] at this
  omega

-- A stable family is a vector bundle on `C × T`, for `T` of finite type.
example (T : Over (Spec (.of k))) (r : ℕ) (hr : 0 < r) (d : ℤ)
    (E : (prod C T).left.Modules) (hE : IsStableFamily C T r hr d E) : IsVectorBundle E r :=
  hE.2.2.1

example (T : Over (Spec (.of k))) (r : ℕ) (hr : 0 < r) (d : ℤ)
    (E : (prod C T).left.Modules) (hE : IsStableFamily C T r hr d E) :
    LocallyOfFiniteType T.hom ∧ QuasiCompact T.hom :=
  ⟨hE.1, hE.2.1⟩

end MathlibExt.AlgebraicGeometry.StableBundleModuli
