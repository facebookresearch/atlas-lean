/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.Ring

/-!
# Wold decomposition for isometries on Hilbert spaces

For an isometry `V` on a Hilbert space `H`, let `W = (range V)ᗮ` be the
**wandering subspace**. Wold's decomposition says every vector splits into a
finite sum of pushed-forward wandering vectors plus a remainder in the range
of `V ^ n` (`exists_wold_decomposition`), the pieces are pairwise orthogonal
(`inner_pow_wandering`), the squared norms add up (`wold_norm_sq`), and the
decomposition is unique (`wold_decomposition_unique`). The intersection
`⋂ n, range (V ^ n)` of all ranges is the **residual subspace**; `V` restricts
to a unitary operator there (`woldResidualEquiv`), and the residual subspace
is orthogonal to every wandering piece (`inner_residual_wandering`).

For the unilateral shift on `ℓ²(ℕ)`, the wandering subspace is the span of
`e₀` and the residual subspace is trivial; see the test file.

This is a companion to the Hilbert-space / spectral material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` and
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`
(it is the operator-theoretic form of the decomposition underlying the
unilateral shift, whose spectrum was treated in batch 47). It is not one of
the 72 v1 targets, and it is in neither the pinned Mathlib (which has no
Wold decomposition) nor base MathlibExt.

Sources: H. Wold, *A Study in the Analysis of Stationary Time Series*
(Almqvist & Wiksell, 1938); P. R. Halmos, *Shifts on Hilbert spaces*,
Journal für die reine und angewandte Mathematik 208 (1961), 102–112.

## Main declarations

* `wanderingSub` : the wandering subspace `(range V)ᗮ`.
* `exists_wold_decomposition` : finite Wold decomposition.
* `wold_norm_sq` : Pythagoras for the decomposition.
* `wold_decomposition_unique` : uniqueness of the decomposition.
* `residualSub` : the residual subspace `⋂ n, range (V ^ n)`.
* `woldResidualEquiv` : `V` restricted to a unitary on the residual subspace.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.WoldDecomposition

open scoped _root_.InnerProductSpace
open Submodule Finset

section Basic

variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H]

/-- The **wandering subspace** of an isometry `V`: the orthogonal complement of
its range. Vectors here are orthogonal to every vector in the range of `V`. -/
noncomputable def wanderingSub (V : H →ₗᵢ[𝕜] H) : Submodule 𝕜 H :=
  (LinearMap.range (V : H →ₗ[𝕜] H))ᗮ

/-- Pulling inner products back along powers of an isometry. -/
theorem inner_pow_pullback (V : H →ₗᵢ[𝕜] H) (k d : ℕ) (a b : H) :
    ⟪(V ^ k) a, (V ^ (k + d)) b⟫_𝕜 = ⟪a, (V ^ d) b⟫_𝕜 := by
  induction k generalizing a b with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', LinearIsometry.coe_mul, Function.comp_apply,
      show k + 1 + d = (k + d) + 1 by omega,
      pow_succ', LinearIsometry.coe_mul, Function.comp_apply,
      LinearIsometry.inner_map_map]
    exact ih a b

/-- A positive power of an isometry lands in the range of the isometry. -/
theorem pow_mem_range (V : H →ₗᵢ[𝕜] H) {d : ℕ} (hd : 0 < d) (b : H) :
    (V ^ d) b ∈ LinearMap.range (V : H →ₗ[𝕜] H) := by
  obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  rw [pow_succ', LinearIsometry.coe_mul]
  exact ⟨(V ^ d') b, by simp [Function.comp_apply]⟩

/-- A wandering vector, pushed forward `k` times, is orthogonal to any vector
pushed forward strictly more times. -/
theorem inner_pow_wandering (V : H →ₗᵢ[𝕜] H) {k l : ℕ} (hkl : k < l) (a : H)
    (ha : a ∈ wanderingSub V) (b : H) :
    ⟪(V ^ k) a, (V ^ l) b⟫_𝕜 = 0 := by
  obtain ⟨d, hd, hd1⟩ : ∃ d, l = k + d ∧ 1 ≤ d := ⟨l - k, by omega, by omega⟩
  subst hd
  rw [inner_pow_pullback V k d a b]
  have hmem : (V ^ d) b ∈ LinearMap.range (V : H →ₗ[𝕜] H) :=
    pow_mem_range V (by omega) b
  have h0 := (Submodule.mem_orthogonal _ _).mp ha _ hmem
  have hs : ⟪a, (V ^ d) b⟫_𝕜 = (starRingEnd 𝕜) ⟪(V ^ d) b, a⟫_𝕜 :=
    (inner_conj_symm _ _).symm
  rw [hs, h0]
  exact map_zero _

/-- The symmetric form of `inner_pow_wandering`. -/
theorem inner_pow_wandering' (V : H →ₗᵢ[𝕜] H) {k l : ℕ} (hkl : k < l) (a : H)
    (ha : a ∈ wanderingSub V) (b : H) :
    ⟪(V ^ l) b, (V ^ k) a⟫_𝕜 = 0 := by
  have h0 := inner_pow_wandering V hkl a ha b
  have hs : ⟪(V ^ l) b, (V ^ k) a⟫_𝕜 =
      (starRingEnd 𝕜) ⟪(V ^ k) a, (V ^ l) b⟫_𝕜 :=
    (inner_conj_symm _ _).symm
  rw [hs, h0]
  exact map_zero _

end Basic

section Complete

variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The range of an isometry is complete. -/
instance (V : H →ₗᵢ[𝕜] H) : CompleteSpace (LinearMap.range (V : H →ₗ[𝕜] H)) := by
  have h : IsComplete ((LinearMap.range (V : H →ₗ[𝕜] H)) : Set H) := by
    rw [LinearMap.coe_range]
    exact V.isometry.isUniformInducing.isComplete_range
  exact h.completeSpace_coe

/-- The range of an isometry admits an orthogonal projection. -/
instance (V : H →ₗᵢ[𝕜] H) :
    (LinearMap.range (V : H →ₗ[𝕜] H)).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- The ambient space splits as the wandering subspace plus the range. -/
theorem isCompl_wandering (V : H →ₗᵢ[𝕜] H) :
    IsCompl (wanderingSub V) (LinearMap.range (V : H →ₗ[𝕜] H)) :=
  (LinearMap.range (V : H →ₗ[𝕜] H)).isCompl_orthogonal.symm

/-- One step of the Wold decomposition: every vector splits as a wandering
vector plus a vector in the range. -/
theorem exists_wandering_add_range (V : H →ₗᵢ[𝕜] H) (x : H) :
    ∃ w ∈ wanderingSub V, ∃ y : H, x = w + V y := by
  obtain ⟨⟨w, hw⟩, ⟨y, hy⟩, hxy, -⟩ :=
    existsUnique_add_of_isCompl (isCompl_wandering V) x
  obtain ⟨y', hy'⟩ := LinearMap.mem_range.mp hy
  have hy'' : V y' = y := hy'
  exact ⟨w, hw, y', by calc x = w + y := hxy.symm
                            _ = w + V y' := by rw [hy'']⟩

/-- Finite Wold decomposition: every vector is a finite sum of pushed-forward
wandering vectors plus a remainder in the range of `V ^ n`. The wandering
coefficients vanish at and beyond `n`. -/
theorem exists_wold_decomposition (V : H →ₗᵢ[𝕜] H) (x : H) (n : ℕ) :
    ∃ w : ℕ → H, ∃ y : H, (∀ k, w k ∈ wanderingSub V) ∧ (∀ k ≥ n, w k = 0) ∧
      x = (∑ k ∈ Finset.range n, (V ^ k) (w k)) + (V ^ n) y := by
  induction n generalizing x with
  | zero =>
    refine ⟨fun _ => 0, x, fun _ => by simp [wanderingSub], fun k _ => rfl, by simp⟩
  | succ n ih =>
    obtain ⟨w, y, hwW, hwsupp, hy⟩ := ih x
    obtain ⟨wn, hwn, y', hy'⟩ := exists_wandering_add_range V y
    have hsum : (∑ k ∈ Finset.range n,
        (V ^ k) (Function.update w n wn k)) =
        ∑ k ∈ Finset.range n, (V ^ k) (w k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≠ n := by
        have : k < n := Finset.mem_range.mp hk
        omega
      rw [Function.update_of_ne hkn wn w]
    refine ⟨Function.update w n wn, y', ?_, ?_, ?_⟩
    · intro k
      by_cases hk : k = n
      · subst hk
        rw [Function.update_self]
        exact hwn
      · rw [Function.update_of_ne hk wn w]
        exact hwW k
    · intro k hk
      rw [Function.update_of_ne (by omega : k ≠ n) wn w]
      exact hwsupp k (by omega)
    · calc x = (∑ k ∈ Finset.range n, (V ^ k) (w k)) + (V ^ n) y := hy
        _ = (∑ k ∈ Finset.range n, (V ^ k) (w k)) +
              ((V ^ n) wn + (V ^ (n + 1)) y') := by
            rw [hy', map_add, pow_succ, LinearIsometry.coe_mul,
              Function.comp_apply]
        _ = ((∑ k ∈ Finset.range n, (V ^ k) (w k)) + (V ^ n) wn) +
              (V ^ (n + 1)) y' := by rw [add_assoc]
        _ = (∑ k ∈ Finset.range (n + 1), (V ^ k) (Function.update w n wn k)) +
              (V ^ (n + 1)) y' := by
            rw [Finset.sum_range_succ, Function.update_self, hsum]

omit [CompleteSpace H] in
/-- Pythagoras for a Wold decomposition: the squared norm of a vector is the sum
of the squared norms of its wandering coefficients plus the squared norm of
the remainder. -/
theorem wold_norm_sq (V : H →ₗᵢ[𝕜] H) (n : ℕ) (w : ℕ → H)
    (hw : ∀ k, w k ∈ wanderingSub V) (y : H) (x : H)
    (hx : x = (∑ k ∈ Finset.range n, (V ^ k) (w k)) + (V ^ n) y) :
    ‖x‖ ^ 2 = (∑ k ∈ Finset.range n, ‖w k‖ ^ 2) + ‖y‖ ^ 2 := by
  induction n generalizing w y x with
  | zero =>
    rw [hx]
    simp
  | succ n ih =>
    have hgroup : x = (∑ k ∈ Finset.range n, (V ^ k) (w k)) +
        (V ^ n) (w n + V y) := by
      rw [hx, Finset.sum_range_succ, map_add, pow_succ, LinearIsometry.coe_mul,
        Function.comp_apply, add_assoc]
    have hstep := ih w hw (w n + V y) x hgroup
    have hpyth : ‖w n + V y‖ ^ 2 = ‖w n‖ ^ 2 + ‖y‖ ^ 2 := by
      have hmem : V y ∈ LinearMap.range (V : H →ₗ[𝕜] H) := ⟨y, rfl⟩
      have h0 := (Submodule.mem_orthogonal _ _).mp (hw n) _ hmem
      have hs : ⟪w n, V y⟫_𝕜 = (starRingEnd 𝕜) ⟪V y, w n⟫_𝕜 :=
        (inner_conj_symm _ _).symm
      have hinner : ⟪w n, V y⟫_𝕜 = 0 := by
        rw [hs, h0]
        exact map_zero _
      calc ‖w n + V y‖ ^ 2 = ‖w n‖ ^ 2 + ‖V y‖ ^ 2 := by
            simpa only [pow_two] using
              norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hinner
        _ = ‖w n‖ ^ 2 + ‖y‖ ^ 2 := by rw [LinearIsometry.norm_map]
    rw [hstep, hpyth, Finset.sum_range_succ]
    ring

omit [CompleteSpace H] in
/-- Uniqueness of the Wold decomposition at level `n`: the remainder and the
finite wandering sum are uniquely determined. -/
theorem wold_decomposition_unique (V : H →ₗᵢ[𝕜] H) (n : ℕ) (w₁ w₂ : ℕ → H)
    (hw₁ : ∀ k, w₁ k ∈ wanderingSub V) (hw₂ : ∀ k, w₂ k ∈ wanderingSub V)
    (y₁ y₂ : H) (x : H)
    (hx₁ : x = (∑ k ∈ Finset.range n, (V ^ k) (w₁ k)) + (V ^ n) y₁)
    (hx₂ : x = (∑ k ∈ Finset.range n, (V ^ k) (w₂ k)) + (V ^ n) y₂) :
    y₁ = y₂ ∧
      (∑ k ∈ Finset.range n, (V ^ k) (w₁ k)) =
        ∑ k ∈ Finset.range n, (V ^ k) (w₂ k) := by
  have hdiff : (∑ k ∈ Finset.range n, (V ^ k) (w₁ k - w₂ k)) = (V ^ n) (y₂ - y₁) := by
    have h1 : (∑ k ∈ Finset.range n, (V ^ k) (w₁ k - w₂ k)) =
        (∑ k ∈ Finset.range n, (V ^ k) (w₁ k)) -
          ∑ k ∈ Finset.range n, (V ^ k) (w₂ k) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [map_sub]
    rw [h1, map_sub]
    have hEq : (∑ k ∈ Finset.range n, (V ^ k) (w₁ k)) + (V ^ n) y₁ =
        (∑ k ∈ Finset.range n, (V ^ k) (w₂ k)) + (V ^ n) y₂ :=
      hx₁.symm.trans hx₂
    have hdiff2 : (∑ k ∈ Finset.range n, (V ^ k) (w₁ k)) -
        ∑ k ∈ Finset.range n, (V ^ k) (w₂ k) =
        (V ^ n) y₂ - (V ^ n) y₁ := by
      rw [sub_eq_sub_iff_add_eq_add, add_comm ((V ^ n) y₂)]
      exact hEq
    exact hdiff2
  have horth : ⟪(∑ k ∈ Finset.range n, (V ^ k) (w₁ k - w₂ k)),
      (V ^ n) (y₂ - y₁)⟫_𝕜 = 0 := by
    rw [sum_inner]
    apply Finset.sum_eq_zero
    intro k hk
    have hkn : k < n := Finset.mem_range.mp hk
    exact inner_pow_wandering V hkn _ (sub_mem (hw₁ k) (hw₂ k)) _
  rw [← hdiff] at horth
  have hzero : (∑ k ∈ Finset.range n, (V ^ k) (w₁ k - w₂ k)) = 0 :=
    inner_self_eq_zero.mp horth
  have hy : y₁ = y₂ := by
    have hVn : (V ^ n) (y₂ - y₁) = 0 := by rw [← hdiff, hzero]
    have hsub : y₂ - y₁ = 0 := (V ^ n).injective (by rw [hVn, map_zero])
    exact (eq_of_sub_eq_zero hsub).symm
  refine ⟨hy, ?_⟩
  have hsum : (∑ k ∈ Finset.range n, (V ^ k) (w₁ k)) -
      ∑ k ∈ Finset.range n, (V ^ k) (w₂ k) = 0 := by
    have h1 : (∑ k ∈ Finset.range n, (V ^ k) (w₁ k - w₂ k)) =
        (∑ k ∈ Finset.range n, (V ^ k) (w₁ k)) -
          ∑ k ∈ Finset.range n, (V ^ k) (w₂ k) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [map_sub]
    rw [← h1, hzero]
  exact eq_of_sub_eq_zero hsum

omit [CompleteSpace H] in
/-- The **residual subspace** of an isometry: vectors in the range of every
power of `V`. -/
noncomputable def residualSub (V : H →ₗᵢ[𝕜] H) : Submodule 𝕜 H :=
  ⨅ n, LinearMap.range ((V ^ n : H →ₗᵢ[𝕜] H) : H →ₗ[𝕜] H)

omit [CompleteSpace H] in
/-- The isometry maps its residual subspace into itself. -/
theorem mapsTo_residual (V : H →ₗᵢ[𝕜] H) :
    ∀ x ∈ residualSub V, V x ∈ residualSub V := by
  intro x hx
  show V x ∈ ⨅ n, LinearMap.range ((V ^ n : H →ₗᵢ[𝕜] H) : H →ₗ[𝕜] H)
  rw [Submodule.mem_iInf]
  intro n
  cases n with
  | zero =>
    exact ⟨V x, by simp⟩
  | succ n =>
    have hxn : x ∈ LinearMap.range ((V ^ n : H →ₗᵢ[𝕜] H) : H →ₗ[𝕜] H) :=
      (Submodule.mem_iInf _).mp hx n
    obtain ⟨z, hz⟩ := hxn
    have hz' : (V ^ n : H →ₗᵢ[𝕜] H) z = x := hz
    refine ⟨z, ?_⟩
    show (V ^ (n + 1) : H →ₗᵢ[𝕜] H) z = V x
    rw [pow_succ', LinearIsometry.coe_mul, Function.comp_apply, hz']

omit [CompleteSpace H] in
/-- The residual subspace is orthogonal to every pushed-forward wandering
vector: the wandering part and the residual part of Wold's decomposition are
orthogonal. -/
theorem inner_residual_wandering (V : H →ₗᵢ[𝕜] H) (x : H) (hx : x ∈ residualSub V)
    (k : ℕ) (a : H) (ha : a ∈ wanderingSub V) :
    ⟪x, (V ^ k) a⟫_𝕜 = 0 := by
  have hxk : x ∈ LinearMap.range ((V ^ (k + 1) : H →ₗᵢ[𝕜] H) : H →ₗ[𝕜] H) :=
    (Submodule.mem_iInf _).mp hx (k + 1)
  obtain ⟨z, hz⟩ := hxk
  rw [← hz]
  exact inner_pow_wandering' V (by omega : k < k + 1) a ha z

omit [CompleteSpace H] in
/-- The restriction of an isometry to its residual subspace is bijective. -/
theorem restrict_residual_bijective (V : H →ₗᵢ[𝕜] H) :
    Function.Bijective (((V : H →ₗ[𝕜] H).restrict (mapsTo_residual V) :
      residualSub V →ₗ[𝕜] residualSub V)) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    have h := congrArg (fun z : residualSub V => (z : H)) hxy
    have h' : V (x : H) = V (y : H) := h
    exact V.injective h'
  · intro y
    have hy1 : (y : H) ∈
        LinearMap.range ((V ^ 1 : H →ₗᵢ[𝕜] H) : H →ₗ[𝕜] H) :=
      (Submodule.mem_iInf _).mp y.property 1
    rw [pow_one] at hy1
    obtain ⟨x₀, hx₀⟩ := hy1
    have hx₀' : V x₀ = (y : H) := hx₀
    have hx₀res : x₀ ∈ residualSub V := by
      show x₀ ∈ ⨅ n, LinearMap.range ((V ^ n : H →ₗᵢ[𝕜] H) : H →ₗ[𝕜] H)
      rw [Submodule.mem_iInf]
      intro n
      have hyn : (y : H) ∈
          LinearMap.range ((V ^ (n + 1) : H →ₗᵢ[𝕜] H) : H →ₗ[𝕜] H) :=
        (Submodule.mem_iInf _).mp y.property (n + 1)
      obtain ⟨z, hz⟩ := hyn
      have hz' : (V ^ (n + 1) : H →ₗᵢ[𝕜] H) z = (y : H) := hz
      rw [pow_succ', LinearIsometry.coe_mul, Function.comp_apply] at hz'
      rw [← hx₀'] at hz'
      have hzx : (V ^ n) z = x₀ := V.injective hz'
      exact ⟨z, hzx⟩
    refine ⟨⟨x₀, hx₀res⟩, ?_⟩
    apply Subtype.ext
    show V x₀ = (y : H)
    exact hx₀'

omit [CompleteSpace H] in
/-- The restriction of an isometry to its residual subspace preserves inner
products. -/
theorem inner_restrict_residual (V : H →ₗᵢ[𝕜] H) (x y : residualSub V) :
    ⟪((V : H →ₗ[𝕜] H).restrict (mapsTo_residual V) x : H),
        ((V : H →ₗ[𝕜] H).restrict (mapsTo_residual V) y : H)⟫_𝕜 =
      ⟪(x : H), (y : H)⟫_𝕜 := by
  show ⟪V (x : H), V (y : H)⟫_𝕜 = ⟪(x : H), (y : H)⟫_𝕜
  exact LinearIsometry.inner_map_map V _ _

omit [CompleteSpace H] in
/-- The isometry restricts to a unitary operator (a linear isometric
equivalence) on its residual subspace. -/
noncomputable def woldResidualEquiv (V : H →ₗᵢ[𝕜] H) :
    residualSub V ≃ₗᵢ[𝕜] residualSub V :=
  LinearEquiv.isometryOfInner
    (LinearEquiv.ofBijective ((V : H →ₗ[𝕜] H).restrict (mapsTo_residual V))
      (restrict_residual_bijective V))
    (inner_restrict_residual V)

omit [CompleteSpace H] in
/-- Applying the residual unitary is the same as applying `V` and viewing the
result in the ambient space. -/
@[simp]
theorem woldResidualEquiv_apply_coe (V : H →ₗᵢ[𝕜] H) (x : residualSub V) :
    ((woldResidualEquiv V x : residualSub V) : H) = V (x : H) :=
  rfl

end Complete

end MathlibExt.Analysis.InnerProductSpace.WoldDecomposition
