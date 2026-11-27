/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.ConstantRank

/-! Tests for the constant rank theorem: both forms restated. -/

namespace MathlibExtTest.Analysis.Calculus.ConstantRank

open MathlibExt.Analysis.Calculus.ConstantRank


open Filter Set
open scoped Topology


/-- **Constant rank theorem.** Let `E`, `F` be finite-dimensional real normed spaces, `U ⊆ E`
open, `x ∈ U`, and `f : E → F` of class `Cⁿ` on `U` with `1 ≤ n`. If the derivative of `f` has
rank `r` at every point of a neighbourhood of `x`, there are `Cⁿ` charts `φ` (around `x`, inside
`U`) and `ψ` (around `f x`), centred at `x` and `f x`, with `f` mapping the source of `φ` into
the source of `ψ`, in which `f` reads `(u, v) ↦ (u, 0)`. Each local fibre of `f` is mapped by `φ`
onto the slice of `φ.target` where the `ℝʳ` coordinate is fixed; the free coordinate ranges over
an open subset of `ℝ^(dim E - r)`. -/
example
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {n : WithTop ℕ∞} (hn : 1 ≤ n) {f : E → F} {U : Set E} {x : E} {r : ℕ}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ContDiffOn ℝ n f U)
    (hrank : ∀ᶠ y in 𝓝 x, Module.finrank ℝ (LinearMap.range (fderiv ℝ f y : E →ₗ[ℝ] F)) = r) :
    ∃ (φ : OpenPartialHomeomorph E
          (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin (Module.finrank ℝ E - r))))
      (ψ : OpenPartialHomeomorph F
          (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin (Module.finrank ℝ F - r)))),
      x ∈ φ.source ∧ φ.source ⊆ U ∧ φ x = 0 ∧ ψ (f x) = 0 ∧
      ContDiffOn ℝ n φ φ.source ∧ ContDiffOn ℝ n φ.symm φ.target ∧
      ContDiffOn ℝ n ψ ψ.source ∧ ContDiffOn ℝ n ψ.symm ψ.target ∧
      MapsTo f φ.source ψ.source ∧
      (∀ p ∈ φ.target, ψ (f (φ.symm p)) = (p.1, 0)) ∧
      ∀ y ∈ φ.source, φ '' (φ.source ∩ f ⁻¹' {f y}) = φ.target ∩ {p | p.1 = (φ y).1} := by
  apply MathlibExt.Analysis.Calculus.ConstantRank.exists_constantRank_coordinates <;> assumption

/-- **Constant rank theorem, `ℝᵈ → ℝᵐ` form.** For `f : ℝᵈ → ℝᵐ` of class `Cⁿ` (`1 ≤ n`) on an
open `U ∋ x` whose derivative has rank `r` on a neighbourhood of `x`, there are centred `Cⁿ`
coordinate changes `φ` of `ℝᵈ` near `x` (inside `U`) and `ψ` of `ℝᵐ` near `f x` with
`ψ (f (φ⁻¹ u)) = (u₁, …, u_r, 0, …, 0)` on the target of `φ`, and `φ` maps each local fibre of
`f` onto the slice of `φ.target` where the first `r` coordinates are fixed (the other `d - r`
coordinates are free). The guard `(i : ℕ) < d` only makes the index typecheck: the rank
hypothesis forces `r ≤ d`. -/
example {d m r : ℕ} {n : WithTop ℕ∞} (hn : 1 ≤ n)
    {f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m)}
    {U : Set (EuclideanSpace ℝ (Fin d))} {x : EuclideanSpace ℝ (Fin d)}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ContDiffOn ℝ n f U)
    (hrank : ∀ᶠ y in 𝓝 x, Module.finrank ℝ (LinearMap.range
      (fderiv ℝ f y : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) = r) :
    ∃ (φ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
      (ψ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m))),
      x ∈ φ.source ∧ φ.source ⊆ U ∧ φ x = 0 ∧ ψ (f x) = 0 ∧
      ContDiffOn ℝ n φ φ.source ∧ ContDiffOn ℝ n φ.symm φ.target ∧
      ContDiffOn ℝ n ψ ψ.source ∧ ContDiffOn ℝ n ψ.symm ψ.target ∧
      MapsTo f φ.source ψ.source ∧
      (∀ u ∈ φ.target, ∀ i : Fin m,
        ψ (f (φ.symm u)) i = if h : (i : ℕ) < r ∧ (i : ℕ) < d then u ⟨i, h.2⟩ else 0) ∧
      ∀ y ∈ φ.source, φ '' (φ.source ∩ f ⁻¹' {f y}) =
        φ.target ∩ {u | ∀ i : Fin d, (i : ℕ) < r → u i = φ y i} := by
  apply MathlibExt.Analysis.Calculus.ConstantRank.exists_constantRank_coordinates_euclidean <;> assumption

end MathlibExtTest.Analysis.Calculus.ConstantRank
