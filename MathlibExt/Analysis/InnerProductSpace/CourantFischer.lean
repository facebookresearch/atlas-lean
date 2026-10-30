/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Courant–Fischer min–max and max–min principles

For a self-adjoint operator `T` on a finite-dimensional inner product space,
let `λ₀ ≥ λ₁ ≥ ⋯ ≥ λ_{n-1}` be its eigenvalues in decreasing order
(`LinearMap.IsSymmetric.eigenvalues`). The Courant–Fischer principles
characterize each `λₖ` variationally:

* **Min–max:** `λₖ` is the smallest possible value of the largest Rayleigh
  quotient on a subspace of codimension `k`. Precisely, there is a subspace
  `W` of dimension `n - k` on which every unit vector has Rayleigh quotient
  at most `λₖ`, attained at an eigenvector, and every subspace of dimension
  `n - k` contains a unit vector with Rayleigh quotient at least `λₖ`
  (`exists_tail_submodule`, `exists_unit_ge_of_submodule`).
* **Max–min:** dually, there is a subspace `U` of dimension `k + 1` on which
  every unit vector has Rayleigh quotient at least `λₖ`, attained at an
  eigenvector, and every subspace of dimension `k + 1` contains a unit
  vector with Rayleigh quotient at most `λₖ`
  (`exists_head_submodule`, `exists_unit_le_of_submodule`).

The statements are given in this attained-inequality form rather than as
`⨅`/`⨆` over subspaces, which is equivalent (the extremal subspaces are the
spans of the tail and head of the eigenbasis) and avoids infima over the
type of subspaces.

This is a companion to the self-adjoint spectral material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`
(the maximum principle for compact self-adjoint operators, whose
finite-dimensional case is the endpoint `k = 0` of the min–max principle).
It is not one of the 72 v1 targets, and it is in neither the pinned Mathlib
(which has the eigenvalue API and the `k = 0` Rayleigh extremum, but no
Courant–Fischer statement) nor base MathlibExt (whose `KyFan.lean` proves
the Ky Fan maximum principle for sums of the top `k` eigenvalues, a
different variational statement).

## Main declarations

* `rayleighForm` : the Rayleigh quotient `re ⟪T x, x⟫` of a vector.
* `rayleighForm_eq_expansion` : the Rayleigh quotient in the eigenbasis.
* `exists_tail_submodule`, `exists_unit_ge_of_submodule` : min–max.
* `exists_head_submodule`, `exists_unit_le_of_submodule` : max–min.

Sources: R. Courant and E. Hilbert, *Methods of Mathematical Physics*,
Vol. I, 1924; E. Fischer, "Über quadratische Formen mit reellen
Koeffizienten", *Monatshefte für Mathematik und Physik* 16 (1905), 234–249.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.CourantFischer

open Filter Topology
open scoped _root_.InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The Rayleigh form of a vector for an operator `T`: `re ⟪T x, x⟫`.
On unit vectors this is the Rayleigh quotient. -/
noncomputable def rayleighForm (T : E →ₗ[𝕜] E) (x : E) : ℝ :=
  RCLike.re ⟪T x, x⟫_𝕜

omit [FiniteDimensional 𝕜 E] in
/-- Scaling a vector by a real scalar scales the Rayleigh form by the
square of the scalar. -/
theorem rayleighForm_smul (T : E →ₗ[𝕜] E) (c : ℝ) (x : E) :
    rayleighForm T ((c : 𝕜) • x) = c ^ 2 * rayleighForm T x := by
  unfold rayleighForm
  rw [map_smul, inner_smul_left, inner_smul_right, RCLike.conj_ofReal,
    ← mul_assoc, ← RCLike.ofReal_mul, RCLike.re_ofReal_mul, pow_two]

variable {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {n : ℕ}
  (hn : Module.finrank 𝕜 E = n)

/-- Expansion of `⟪x, T x⟫` in the orthonormal eigenbasis: a weighted sum
of the eigenvalues with weights `‖⟪eᵢ, x⟫‖²`. -/
theorem inner_self_apply_eq_expansion (x : E) :
    ⟪x, T x⟫_𝕜 = ((∑ i : Fin n, hT.eigenvalues hn i *
      ‖⟪(hT.eigenvectorBasis hn) i, x⟫_𝕜‖ ^ 2 : ℝ) : 𝕜) := by
  set b := hT.eigenvectorBasis hn with hb
  have hexp : x = ∑ i, ⟪b i, x⟫_𝕜 • b i := (b.sum_repr' x).symm
  have hTexp : T x =
      ∑ i, ⟪b i, x⟫_𝕜 • (((hT.eigenvalues hn i : ℝ) : 𝕜) • b i) := by
    conv_lhs => rw [hexp, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hT.apply_eigenvectorBasis hn i]
  calc ⟪x, T x⟫_𝕜
      = ∑ i, ⟪b i, x⟫_𝕜 *
          (((hT.eigenvalues hn i : ℝ) : 𝕜) * ⟪x, b i⟫_𝕜) := by
        rw [hTexp, inner_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [inner_smul_right, inner_smul_right]
    _ = ((∑ i : Fin n, hT.eigenvalues hn i *
        ‖⟪b i, x⟫_𝕜‖ ^ 2 : ℝ) : 𝕜) := by
        rw [RCLike.ofReal_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have ci : ⟪x, b i⟫_𝕜 = (starRingEnd 𝕜) ⟪b i, x⟫_𝕜 :=
          (inner_conj_symm x (b i)).symm
        rw [ci, ← mul_assoc, mul_comm ⟪b i, x⟫_𝕜 _,
          mul_assoc, RCLike.mul_conj]
        simp [RCLike.ofReal_mul, RCLike.ofReal_pow]

/-- The Rayleigh form expanded in the orthonormal eigenbasis. -/
theorem rayleighForm_eq_expansion (x : E) :
    rayleighForm T x = ∑ i : Fin n, hT.eigenvalues hn i *
      ‖⟪(hT.eigenvectorBasis hn) i, x⟫_𝕜‖ ^ 2 := by
  have h1 := inner_self_apply_eq_expansion hT hn x
  have h2 : ⟪T x, x⟫_𝕜 = (starRingEnd 𝕜) ⟪x, T x⟫_𝕜 := (inner_conj_symm _ _).symm
  unfold rayleighForm
  rw [h2, h1, RCLike.conj_ofReal, RCLike.ofReal_re]

/-- A vector in the span of some of the eigenvectors is orthogonal to the
remaining eigenvectors. -/
theorem inner_eigenvectorBasis_eq_zero_of_mem_span {m : ℕ} {v : Fin m → E}
    {x : E} (hx : x ∈ Submodule.span 𝕜 (Set.range v)) {i : Fin n}
    (hi : ∀ j, ⟪(hT.eigenvectorBasis hn) i, v j⟫_𝕜 = 0) :
    ⟪(hT.eigenvectorBasis hn) i, x⟫_𝕜 = 0 := by
  refine Submodule.span_induction (fun y hy => ?_) (by simp)
    (fun y z _ _ hy hz => ?_) (fun a y _ hy => ?_) hx
  · obtain ⟨j, rfl⟩ := hy
    exact hi j
  · rw [inner_add_right, hy, hz, add_zero]
  · rw [inner_smul_right, hy, mul_zero]

/-- The tail of the eigenbasis: the eigenvectors with index `≥ k`,
as a family indexed by `Fin (n - k)`. -/
noncomputable def tailFamily {k : ℕ} (hk : k < n) : Fin (n - k) → E :=
  fun j => (hT.eigenvectorBasis hn) ⟨k + j.val, by have hj := j.isLt; omega⟩

/-- The head of the eigenbasis: the eigenvectors with index `≤ k`,
as a family indexed by `Fin (k + 1)`. -/
noncomputable def headFamily {k : ℕ} (hk : k < n) : Fin (k + 1) → E :=
  fun j => (hT.eigenvectorBasis hn) ⟨j.val, by have hj := j.isLt; omega⟩

/-- The tail family is linearly independent, as a restriction of the
orthonormal eigenbasis. -/
theorem tailFamily_linearIndependent {k : ℕ} (hk : k < n) :
    LinearIndependent 𝕜 (tailFamily hT hn hk) := by
  have hcomp := (hT.eigenvectorBasis hn).orthonormal.linearIndependent.comp
    (fun j : Fin (n - k) => (⟨k + j.val, by have hj := j.isLt; omega⟩ : Fin n))
    (by
      intro a b hab
      have h : k + a.val = k + b.val := by simpa using congrArg Fin.val hab
      exact Fin.ext (Nat.add_left_cancel h))
  exact hcomp

/-- The head family is linearly independent, as a restriction of the
orthonormal eigenbasis. -/
theorem headFamily_linearIndependent {k : ℕ} (hk : k < n) :
    LinearIndependent 𝕜 (headFamily hT hn hk) := by
  have hcomp := (hT.eigenvectorBasis hn).orthonormal.linearIndependent.comp
    (fun j : Fin (k + 1) => (⟨j.val, by have hj := j.isLt; omega⟩ : Fin n))
    (by
      intro a b hab
      have h : a.val = b.val := by simpa using congrArg Fin.val hab
      exact Fin.ext h)
  exact hcomp

/-- The span of the tail of the eigenbasis has dimension `n - k`. -/
theorem finrank_span_tailFamily {k : ℕ} (hk : k < n) :
    Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range (tailFamily hT hn hk))) = n - k := by
  rw [finrank_span_eq_card (tailFamily_linearIndependent hT hn hk)]
  simp

/-- The span of the head of the eigenbasis has dimension `k + 1`. -/
theorem finrank_span_headFamily {k : ℕ} (hk : k < n) :
    Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range (headFamily hT hn hk))) = k + 1 := by
  rw [finrank_span_eq_card (headFamily_linearIndependent hT hn hk)]
  simp

/-- On the span of the tail of the eigenbasis, the Rayleigh form is at
most `λₖ * ‖x‖²`. -/
theorem rayleighForm_le_of_mem_tail {k : ℕ} (hk : k < n) {x : E}
    (hx : x ∈ Submodule.span 𝕜 (Set.range (tailFamily hT hn hk))) :
    rayleighForm T x ≤ hT.eigenvalues hn ⟨k, hk⟩ * ‖x‖ ^ 2 := by
  set b := hT.eigenvectorBasis hn with hb
  set Λ := hT.eigenvalues hn with hΛ
  set w : Fin n → ℝ := fun i => ‖⟪b i, x⟫_𝕜‖ ^ 2 with hw
  have hvan : ∀ i : Fin n, i.val < k → w i = 0 := by
    intro i hi
    have h0 : ⟪b i, x⟫_𝕜 = 0 := by
      apply inner_eigenvectorBasis_eq_zero_of_mem_span hT hn hx
      intro j
      show ⟪b i, tailFamily hT hn hk j⟫_𝕜 = 0
      apply b.inner_eq_zero
      intro hcon
      have : i.val = k + j.val := congrArg Fin.val hcon
      omega
    simp [hw, h0]
  have hsum : ∑ i : Fin n, w i = ‖x‖ ^ 2 := b.sum_sq_norm_inner_right x
  have hfilter : ∑ i : Fin n, Λ i * w i =
      ∑ i ∈ Finset.univ.filter (fun i => k ≤ i.val), Λ i * w i := by
    refine (Finset.sum_subset (Finset.filter_subset _ _)
      (fun i _ hi => ?_)).symm
    have hi' : i.val < k := by
      rw [Finset.mem_filter] at hi
      exact Nat.lt_of_not_ge (fun h => hi ⟨Finset.mem_univ i, h⟩)
    rw [hvan i hi']
    simp
  have hweights : ∑ i ∈ Finset.univ.filter (fun i => k ≤ i.val), w i = ‖x‖ ^ 2 := by
    rw [← hsum]
    refine Finset.sum_subset (Finset.filter_subset _ _)
      (fun i _ hi => ?_)
    have hi' : i.val < k := by
      rw [Finset.mem_filter] at hi
      exact Nat.lt_of_not_ge (fun h => hi ⟨Finset.mem_univ i, h⟩)
    exact hvan i hi'
  rw [rayleighForm_eq_expansion hT hn x, hfilter]
  calc ∑ i ∈ Finset.univ.filter (fun i => k ≤ i.val), Λ i * w i
      ≤ ∑ i ∈ Finset.univ.filter (fun i => k ≤ i.val),
          Λ ⟨k, hk⟩ * w i := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [Finset.mem_filter] at hi
        have hle : Λ i ≤ Λ ⟨k, hk⟩ :=
          hT.eigenvalues_antitone hn (Fin.le_def.mpr hi.2)
        exact mul_le_mul_of_nonneg_right hle (by positivity)
    _ = Λ ⟨k, hk⟩ * ‖x‖ ^ 2 := by
        rw [← hweights, Finset.mul_sum]

/-- On the span of the head of the eigenbasis, the Rayleigh form is at
least `λₖ * ‖x‖²`. -/
theorem rayleighForm_ge_of_mem_head {k : ℕ} (hk : k < n) {x : E}
    (hx : x ∈ Submodule.span 𝕜 (Set.range (headFamily hT hn hk))) :
    hT.eigenvalues hn ⟨k, hk⟩ * ‖x‖ ^ 2 ≤ rayleighForm T x := by
  set b := hT.eigenvectorBasis hn with hb
  set Λ := hT.eigenvalues hn with hΛ
  set w : Fin n → ℝ := fun i => ‖⟪b i, x⟫_𝕜‖ ^ 2 with hw
  have hvan : ∀ i : Fin n, k < i.val → w i = 0 := by
    intro i hi
    have h0 : ⟪b i, x⟫_𝕜 = 0 := by
      apply inner_eigenvectorBasis_eq_zero_of_mem_span hT hn hx
      intro j
      show ⟪b i, headFamily hT hn hk j⟫_𝕜 = 0
      apply b.inner_eq_zero
      intro hcon
      have : i.val = j.val := congrArg Fin.val hcon
      omega
    simp [hw, h0]
  have hsum : ∑ i : Fin n, w i = ‖x‖ ^ 2 := b.sum_sq_norm_inner_right x
  have hfilter : ∑ i : Fin n, Λ i * w i =
      ∑ i ∈ Finset.univ.filter (fun i => i.val ≤ k), Λ i * w i := by
    refine (Finset.sum_subset (Finset.filter_subset _ _)
      (fun i _ hi => ?_)).symm
    have hi' : k < i.val := by
      rw [Finset.mem_filter] at hi
      exact Nat.lt_of_not_ge (fun h => hi ⟨Finset.mem_univ i, h⟩)
    rw [hvan i hi']
    simp
  have hweights : ∑ i ∈ Finset.univ.filter (fun i => i.val ≤ k), w i = ‖x‖ ^ 2 := by
    rw [← hsum]
    refine Finset.sum_subset (Finset.filter_subset _ _)
      (fun i _ hi => ?_)
    have hi' : k < i.val := by
      rw [Finset.mem_filter] at hi
      exact Nat.lt_of_not_ge (fun h => hi ⟨Finset.mem_univ i, h⟩)
    exact hvan i hi'
  rw [rayleighForm_eq_expansion hT hn x, hfilter]
  calc Λ ⟨k, hk⟩ * ‖x‖ ^ 2
      = ∑ i ∈ Finset.univ.filter (fun i => i.val ≤ k), Λ ⟨k, hk⟩ * w i := by
        rw [← hweights, Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i => i.val ≤ k), Λ i * w i := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [Finset.mem_filter] at hi
        have hle : Λ ⟨k, hk⟩ ≤ Λ i :=
          hT.eigenvalues_antitone hn (Fin.le_def.mpr hi.2)
        exact mul_le_mul_of_nonneg_right hle (by positivity)

/-- The `k`-th eigenvector lies in the tail span, is a unit vector, and
attains the Rayleigh value `λₖ`. -/
theorem exists_eigenvector_mem_tail {k : ℕ} (hk : k < n) :
    ∃ x ∈ Submodule.span 𝕜 (Set.range (tailFamily hT hn hk)), ‖x‖ = 1 ∧
      rayleighForm T x = hT.eigenvalues hn ⟨k, hk⟩ := by
  refine ⟨(hT.eigenvectorBasis hn) ⟨k, hk⟩, ?_, ?_, ?_⟩
  · apply Submodule.subset_span
    exact ⟨⟨0, by omega⟩, by simp [tailFamily]⟩
  · exact (hT.eigenvectorBasis hn).orthonormal.norm_eq_one ⟨k, hk⟩
  · rw [rayleighForm_eq_expansion hT hn]
    rw [Finset.sum_eq_single ⟨k, hk⟩]
    · simp [(hT.eigenvectorBasis hn).orthonormal.norm_eq_one ⟨k, hk⟩]
    · intro i _ hi
      have h0 : ⟪(hT.eigenvectorBasis hn) i,
          (hT.eigenvectorBasis hn) ⟨k, hk⟩⟫_𝕜 = 0 :=
        (hT.eigenvectorBasis hn).inner_eq_zero hi
      simp [h0]
    · simp

/-- The `k`-th eigenvector lies in the head span, is a unit vector, and
attains the Rayleigh value `λₖ`. -/
theorem exists_eigenvector_mem_head {k : ℕ} (hk : k < n) :
    ∃ x ∈ Submodule.span 𝕜 (Set.range (headFamily hT hn hk)), ‖x‖ = 1 ∧
      rayleighForm T x = hT.eigenvalues hn ⟨k, hk⟩ := by
  refine ⟨(hT.eigenvectorBasis hn) ⟨k, hk⟩, ?_, ?_, ?_⟩
  · apply Submodule.subset_span
    exact ⟨⟨k, by omega⟩, by simp [headFamily]⟩
  · exact (hT.eigenvectorBasis hn).orthonormal.norm_eq_one ⟨k, hk⟩
  · rw [rayleighForm_eq_expansion hT hn]
    rw [Finset.sum_eq_single ⟨k, hk⟩]
    · simp [(hT.eigenvectorBasis hn).orthonormal.norm_eq_one ⟨k, hk⟩]
    · intro i _ hi
      have h0 : ⟪(hT.eigenvectorBasis hn) i,
          (hT.eigenvectorBasis hn) ⟨k, hk⟩⟫_𝕜 = 0 :=
        (hT.eigenvectorBasis hn).inner_eq_zero hi
      simp [h0]
    · simp

/-- **Courant–Fischer min–max, extremal subspace form.** There is a
subspace `W` of dimension `n - k` on which every unit vector has Rayleigh
quotient at most `λₖ`, and the bound is attained. -/
theorem exists_tail_submodule {k : ℕ} (hk : k < n) :
    ∃ W : Submodule 𝕜 E, Module.finrank 𝕜 W = n - k ∧
      (∀ x ∈ W, ‖x‖ = 1 → rayleighForm T x ≤ hT.eigenvalues hn ⟨k, hk⟩) ∧
      ∃ x ∈ W, ‖x‖ = 1 ∧ rayleighForm T x = hT.eigenvalues hn ⟨k, hk⟩ := by
  refine ⟨Submodule.span 𝕜 (Set.range (tailFamily hT hn hk)),
    finrank_span_tailFamily hT hn hk, ?_, exists_eigenvector_mem_tail hT hn hk⟩
  intro x hx hx1
  have h := rayleighForm_le_of_mem_tail hT hn hk hx
  rwa [hx1, one_pow, mul_one] at h

/-- **Courant–Fischer min–max, lower-bound form.** Every subspace of
dimension `n - k` contains a unit vector with Rayleigh quotient at
least `λₖ`. -/
theorem exists_unit_ge_of_submodule {k : ℕ} (hk : k < n) (W : Submodule 𝕜 E)
    (hW : Module.finrank 𝕜 W = n - k) :
    ∃ x ∈ W, ‖x‖ = 1 ∧ hT.eigenvalues hn ⟨k, hk⟩ ≤ rayleighForm T x := by
  set S := Submodule.span 𝕜 (Set.range (headFamily hT hn hk)) with hS
  have hdimS : Module.finrank 𝕜 S = k + 1 := finrank_span_headFamily hT hn hk
  have hdim : 1 ≤ Module.finrank 𝕜 ↥(W ⊓ S) := by
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq W S
    have hle : Module.finrank 𝕜 ↥(W ⊔ S) ≤ n := by
      rw [← hn]
      exact Submodule.finrank_le _
    omega
  obtain ⟨y, hy0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hdim
  have hyE0 : (y : E) ≠ 0 := by exact_mod_cast hy0
  have hyW : (y : E) ∈ W := (Submodule.mem_inf.mp y.2).1
  have hyS : (y : E) ∈ S := (Submodule.mem_inf.mp y.2).2
  have hnorm : (0 : ℝ) < ‖(y : E)‖ := norm_pos_iff.mpr hyE0
  refine ⟨((‖(y : E)‖⁻¹ : ℝ) : 𝕜) • (y : E), W.smul_mem _ hyW, ?_, ?_⟩
  · rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.mpr hnorm.le),
      inv_mul_cancel₀ hnorm.ne']
  · have hhead := rayleighForm_ge_of_mem_head hT hn hk hyS
    have hsmul := rayleighForm_smul T ‖(y : E)‖⁻¹ (y : E)
    rw [hsmul]
    calc hT.eigenvalues hn ⟨k, hk⟩
        = ‖(y : E)‖⁻¹ ^ 2 * (hT.eigenvalues hn ⟨k, hk⟩ * ‖(y : E)‖ ^ 2) := by
          field_simp
      _ ≤ ‖(y : E)‖⁻¹ ^ 2 * rayleighForm T (y : E) :=
          mul_le_mul_of_nonneg_left hhead (by positivity)

/-- **Courant–Fischer max–min, extremal subspace form.** There is a
subspace `U` of dimension `k + 1` on which every unit vector has Rayleigh
quotient at least `λₖ`, and the bound is attained. -/
theorem exists_head_submodule {k : ℕ} (hk : k < n) :
    ∃ U : Submodule 𝕜 E, Module.finrank 𝕜 U = k + 1 ∧
      (∀ x ∈ U, ‖x‖ = 1 → hT.eigenvalues hn ⟨k, hk⟩ ≤ rayleighForm T x) ∧
      ∃ x ∈ U, ‖x‖ = 1 ∧ rayleighForm T x = hT.eigenvalues hn ⟨k, hk⟩ := by
  refine ⟨Submodule.span 𝕜 (Set.range (headFamily hT hn hk)),
    finrank_span_headFamily hT hn hk, ?_, exists_eigenvector_mem_head hT hn hk⟩
  intro x hx hx1
  have h := rayleighForm_ge_of_mem_head hT hn hk hx
  rwa [hx1, one_pow, mul_one] at h

/-- **Courant–Fischer max–min, lower-bound form.** Every subspace of
dimension `k + 1` contains a unit vector with Rayleigh quotient at
most `λₖ`. -/
theorem exists_unit_le_of_submodule {k : ℕ} (hk : k < n) (U : Submodule 𝕜 E)
    (hU : Module.finrank 𝕜 U = k + 1) :
    ∃ x ∈ U, ‖x‖ = 1 ∧ rayleighForm T x ≤ hT.eigenvalues hn ⟨k, hk⟩ := by
  set S := Submodule.span 𝕜 (Set.range (tailFamily hT hn hk)) with hS
  have hdimS : Module.finrank 𝕜 S = n - k := finrank_span_tailFamily hT hn hk
  have hdim : 1 ≤ Module.finrank 𝕜 ↥(U ⊓ S) := by
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq U S
    have hle : Module.finrank 𝕜 ↥(U ⊔ S) ≤ n := by
      rw [← hn]
      exact Submodule.finrank_le _
    omega
  obtain ⟨y, hy0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hdim
  have hyE0 : (y : E) ≠ 0 := by exact_mod_cast hy0
  have hyU : (y : E) ∈ U := (Submodule.mem_inf.mp y.2).1
  have hyS : (y : E) ∈ S := (Submodule.mem_inf.mp y.2).2
  have hnorm : (0 : ℝ) < ‖(y : E)‖ := norm_pos_iff.mpr hyE0
  refine ⟨((‖(y : E)‖⁻¹ : ℝ) : 𝕜) • (y : E), U.smul_mem _ hyU, ?_, ?_⟩
  · rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.mpr hnorm.le),
      inv_mul_cancel₀ hnorm.ne']
  · have htail := rayleighForm_le_of_mem_tail hT hn hk hyS
    have hsmul := rayleighForm_smul T ‖(y : E)‖⁻¹ (y : E)
    rw [hsmul]
    calc ‖(y : E)‖⁻¹ ^ 2 * rayleighForm T (y : E)
        ≤ ‖(y : E)‖⁻¹ ^ 2 * (hT.eigenvalues hn ⟨k, hk⟩ * ‖(y : E)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left htail (by positivity)
      _ = hT.eigenvalues hn ⟨k, hk⟩ := by
          field_simp

end MathlibExt.Analysis.InnerProductSpace.CourantFischer
