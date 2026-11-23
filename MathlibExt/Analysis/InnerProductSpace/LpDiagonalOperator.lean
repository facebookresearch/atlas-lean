/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.HilbertBasisDiagonal
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Diagonal operators on `ℓ²`

For a bounded coefficient sequence `a : ι → 𝕜`, the diagonal operator on
`ℓ²(ι, 𝕜)` is pointwise multiplication by `a`. This file develops its basic
theory: it is a bounded operator with norm `⨆ i, ‖a i‖`, its adjoint is the
diagonal operator with conjugate coefficients, it is self-adjoint exactly
when the coefficients are real, and it is compact exactly when the
coefficients vanish at infinity (in the cofinite-filter sense).

These are supporting results for the existing bundled
`MathlibExt.Analysis.InnerProductSpace.HilbertBasisDiagonal.diagonalOperator`.
Its `ℓ²` specialization uses the identity Hilbert basis, and its bounded coordinate
multiplication is implemented by Mathlib's `lp.mapCLM`. The original `diagonalCLM`
and `diagonalLinMap` names are compatibility abbreviations for that specialization
and its linear-map projection.

The development is a companion to the Hilbert-space and spectral material in
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` and
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`. The latter's
Green's square-root expansion supplies the source context for the canonical
Hilbert-basis diagonal construction. The norm, adjoint, compactness, and spectrum
results here are supporting theorems; they are not identified as imported v1 targets.
The archived sources are preserved.

## Main declarations

* `diagonalCLM` : the diagonal operator as a bounded operator on `ℓ²(ι, 𝕜)`.
* `diagonalCLM_apply` : its pointwise action.
* `norm_diagonalCLM` : `‖diagonalCLM a hbdd‖ = ⨆ i, ‖a i‖`.
* `adjoint_diagonalCLM` : `(diagonalCLM a hbdd)† = diagonalCLM (star ∘ a) _`.
* `isSelfAdjoint_diagonalCLM_iff` : self-adjointness iff every `a i` is real.
* `isCompactOperator_diagonalCLM_iff` : compactness iff `a → 0` along `cofinite`.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.LpDiagonalOperator

open Filter Topology Set
open scoped _root_.lp _root_.InnerProduct _root_.InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*}

/-- A bounded coefficient sequence has a nonnegative uniform bound. -/
private theorem exists_nonneg_bound {a : ι → 𝕜} (hbdd : ∃ C, ∀ i, ‖a i‖ ≤ C) :
    ∃ C, 0 ≤ C ∧ ∀ i, ‖a i‖ ≤ C := by
  obtain ⟨C, hC⟩ := hbdd
  exact ⟨max C 0, le_max_right _ _, fun i => (hC i).trans (le_max_left _ _)⟩

/-- **Scalar multiplication on $\ell^2$ is pointwise.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$. For every $c \in \mathbb{K}$, every $x \in \ell^2(\iota, \mathbb{K})$ and every
$i \in \iota$, the $i$-th coordinate of $c x$ is $(c x)_i = c \, x_i$. -/
theorem lp_smul_apply (c : 𝕜) (x : ℓ²(ι, 𝕜)) (i : ι) : (c • x) i = c * x i :=
  rfl

/-- **Bounded multipliers preserve $\ell^2$.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$. If
$a : \iota \to \mathbb{K}$ is bounded, that is, $|a_i| \le C$ for some real $C$ and all $i$, then
for every $x \in \ell^2(\iota, \mathbb{K})$ the sequence $(a_i x_i)_{i \in \iota}$ lies in
$\ell^2(\iota, \mathbb{K})$, that is, the family $(|a_i x_i|^2)_{i \in \iota}$ is summable. -/
theorem memℓp_diagonal (a : ι → 𝕜) (hbdd : ∃ C, ∀ i, ‖a i‖ ≤ C)
    (x : ℓ²(ι, 𝕜)) : Memℓp (fun i => a i * x i) 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_nonneg_bound hbdd
  refine (x.2.const_mul (C : 𝕜)).mono' (fun i => ?_)
  simp only [norm_mul, RCLike.norm_ofReal, abs_of_nonneg hC0]
  exact mul_le_mul_of_nonneg_right (hC i) (norm_nonneg _)

/-- **Diagonal operator on ℓ².** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $\iota$ be
a type and let $a : \iota \to \mathbb{K}$ be a bounded sequence, that is, $\|a_i\| \le C$ for some
real $C$ and all $i \in \iota$. The diagonal operator $D_a$ with coefficients $a$ is the bounded
linear operator on $\ell^2(\iota, \mathbb{K})$ that sends $x$ to the sequence
$(a_i x_i)_{i \in \iota}$.

It is defined as the Hilbert-basis diagonal operator for the standard Hilbert basis of
$\ell^2(\iota, \mathbb{K})$, using the bound $\max(C, 0)$ for a chosen bound $C$, so that empty
index types also admit a nonnegative bound. -/
noncomputable abbrev diagonalCLM (a : ι → 𝕜) (hbdd : ∃ C, ∀ i, ‖a i‖ ≤ C) :
    ℓ²(ι, 𝕜) →L[𝕜] ℓ²(ι, 𝕜) :=
  MathlibExt.Analysis.InnerProductSpace.HilbertBasisDiagonal.diagonalOperator
    (HilbertBasis.ofRepr (LinearIsometryEquiv.refl 𝕜 (ℓ²(ι, 𝕜)))) a
    (C := max hbdd.choose 0)
    (fun i => (hbdd.choose_spec i).trans (le_max_left _ _))

/-- **Coordinates of a diagonal operator on ℓ².** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, let $\iota$ be a type, let $a : \iota \to \mathbb{K}$ be a bounded sequence and let
$D_a$ be the diagonal operator on $\ell^2(\iota, \mathbb{K})$ with coefficients $a$. For every
$x \in \ell^2(\iota, \mathbb{K})$ and every $i \in \iota$, the $i$-th coordinate of $D_a x$ is
$a_i x_i$. -/
theorem diagonalCLM_apply (a : ι → 𝕜) (hbdd : ∃ C, ∀ i, ‖a i‖ ≤ C)
    (x : ℓ²(ι, 𝕜)) (i : ι) :
    diagonalCLM a hbdd x i = a i * x i := by
  let b : HilbertBasis ι 𝕜 (ℓ²(ι, 𝕜)) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl 𝕜 (ℓ²(ι, 𝕜)))
  have h := MathlibExt.Analysis.InnerProductSpace.HilbertBasisDiagonal.repr_diagonalOperator_apply
    (b := b) (a := a) (C := max hbdd.choose 0)
    (fun j => (hbdd.choose_spec j).trans (le_max_left _ _)) x i
  rw [← b.repr_apply_apply] at h
  exact h

/-- **Diagonal operator on ℓ² as a linear map.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, let $\iota$ be a type and let $a : \iota \to \mathbb{K}$ be a bounded sequence. This
is the diagonal operator on $\ell^2(\iota, \mathbb{K})$ with coefficients $a$, regarded as a
$\mathbb{K}$-linear map $\ell^2(\iota, \mathbb{K}) \to \ell^2(\iota, \mathbb{K})$ by forgetting
its continuity. -/
noncomputable abbrev diagonalLinMap (a : ι → 𝕜) (hbdd : ∃ C, ∀ i, ‖a i‖ ≤ C) :
    ℓ²(ι, 𝕜) →ₗ[𝕜] ℓ²(ι, 𝕜) :=
  (diagonalCLM a hbdd).toLinearMap

/-- **Coordinates of the diagonal linear map on ℓ².** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, let $\iota$ be a type and let $a : \iota \to \mathbb{K}$ be a bounded sequence. For
every $x \in \ell^2(\iota, \mathbb{K})$ and every $i \in \iota$, the diagonal operator with
coefficients $a$, regarded as a linear map, sends $x$ to a sequence whose $i$-th coordinate is
$a_i x_i$. -/
theorem diagonalLinMap_apply (a : ι → 𝕜) (hbdd : ∃ C, ∀ i, ‖a i‖ ≤ C)
    (x : ℓ²(ι, 𝕜)) (i : ι) :
    diagonalLinMap a hbdd x i = a i * x i :=
  diagonalCLM_apply a hbdd x i

/-- **Pointwise bound for diagonal operators.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$,
let $a : \iota \to \mathbb{K}$ be bounded, and let $D_a$ be the diagonal operator
$x \mapsto (a_i x_i)_{i \in \iota}$ on $\ell^2(\iota, \mathbb{K})$, viewed as a linear map. If
$C \ge 0$ and $|a_i| \le C$ for every $i \in \iota$, then $\|D_a x\| \le C \|x\|$ for every
$x \in \ell^2(\iota, \mathbb{K})$. -/
theorem norm_diagonalLinMap_le (a : ι → 𝕜) (hbdd : ∃ C, ∀ i, ‖a i‖ ≤ C)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, ‖a i‖ ≤ C) (x : ℓ²(ι, 𝕜)) :
    ‖diagonalLinMap a hbdd x‖ ≤ C * ‖x‖ := by
  have hpt : ∀ i, ‖(diagonalLinMap a hbdd x) i‖ ≤ ‖((C : 𝕜) • x) i‖ := by
    intro i
    rw [diagonalLinMap_apply, lp_smul_apply]
    simp only [norm_mul, RCLike.norm_ofReal, abs_of_nonneg hC0]
    exact mul_le_mul_of_nonneg_right (hC i) (norm_nonneg _)
  calc ‖diagonalLinMap a hbdd x‖ ≤ ‖(C : 𝕜) • x‖ :=
        lp.norm_mono (by norm_num) hpt
    _ = C * ‖x‖ := by
        rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg hC0]

/-- **Diagonal operators on standard basis vectors.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, let $\iota$ be a type, let $a : \iota \to \mathbb{K}$ be a bounded sequence and let
$D_a$ be the diagonal operator on $\ell^2(\iota, \mathbb{K})$ with coefficients $a$. For
$i \in \iota$ let $e_i \in \ell^2(\iota, \mathbb{K})$ be the sequence equal to $1$ at $i$ and $0$
elsewhere. Then for every $i \in \iota$ and every $c \in \mathbb{K}$ we have
$D_a(c\,e_i) = a_i \, (c\,e_i)$. -/
theorem diagonalCLM_single [DecidableEq ι] (a : ι → 𝕜) (hbdd : ∃ C, ∀ i, ‖a i‖ ≤ C)
    (i : ι) (c : 𝕜) :
    diagonalCLM a hbdd (lp.single 2 i c) = a i • lp.single 2 i c := by
  apply lp.ext
  funext j
  rw [diagonalCLM_apply]
  by_cases h : j = i
  · subst h
    simp [lp.single_apply, Pi.single_eq_same, smul_eq_mul]
  · simp [lp.single_apply, Pi.single_eq_of_ne h, smul_eq_mul]

/-- **The diagonal operator with all coefficients one is the identity.** Let $\mathbb{K}$ be
$\mathbb{R}$ or $\mathbb{C}$ and let $\iota$ be a type. The diagonal operator on
$\ell^2(\iota, \mathbb{K})$ whose coefficients all equal $1$ is the identity operator. -/
theorem diagonalCLM_one : diagonalCLM (fun _ : ι => (1 : 𝕜)) ⟨1, fun _ => by simp⟩ = 1 := by
  ext x i
  simp [diagonalCLM_apply]

/-- **Composition of diagonal operators.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let
$\iota$ be a type, and for a bounded sequence $c : \iota \to \mathbb{K}$ let $D_c$ be the diagonal
operator on $\ell^2(\iota, \mathbb{K})$ with coefficients $c$. For bounded sequences
$a, b : \iota \to \mathbb{K}$, we have $D_b \circ D_a = D_{ba}$, where $ba$ is the pointwise
product $i \mapsto b_i a_i$. -/
theorem diagonalCLM_comp (a b : ι → 𝕜) (ha : ∃ C, ∀ i, ‖a i‖ ≤ C)
    (hb : ∃ C, ∀ i, ‖b i‖ ≤ C) :
    diagonalCLM b hb ∘L diagonalCLM a ha =
      diagonalCLM (fun i => b i * a i) (by
        obtain ⟨Ca, _hCa0, hCa⟩ := exists_nonneg_bound ha
        obtain ⟨Cb, hCb0, hCb⟩ := exists_nonneg_bound hb
        exact ⟨Cb * Ca, fun i => by
          rw [norm_mul]
          exact mul_le_mul (hCb i) (hCa i) (norm_nonneg _) hCb0⟩) := by
  ext x i
  simp only [ContinuousLinearMap.comp_apply, diagonalCLM_apply]
  rw [mul_assoc]

/-- **Difference of diagonal operators.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let
$\iota$ be a type, and for a bounded sequence $c : \iota \to \mathbb{K}$ let $D_c$ be the diagonal
operator on $\ell^2(\iota, \mathbb{K})$ with coefficients $c$. For bounded sequences
$a, b : \iota \to \mathbb{K}$, we have $D_a - D_b = D_{a - b}$, where $a - b$ is the sequence
$i \mapsto a_i - b_i$. -/
theorem diagonalCLM_sub (a b : ι → 𝕜) (ha : ∃ C, ∀ i, ‖a i‖ ≤ C)
    (hb : ∃ C, ∀ i, ‖b i‖ ≤ C) :
    diagonalCLM a ha - diagonalCLM b hb =
      diagonalCLM (fun i => a i - b i) (by
        obtain ⟨Ca, _hCa0, hCa⟩ := exists_nonneg_bound ha
        obtain ⟨Cb, _hCb0, hCb⟩ := exists_nonneg_bound hb
        exact ⟨Ca + Cb, fun i => by
          calc ‖a i - b i‖ ≤ ‖a i‖ + ‖b i‖ := norm_sub_le _ _
            _ ≤ Ca + Cb := add_le_add (hCa i) (hCb i)⟩) := by
  ext x i
  simp only [sub_apply, diagonalCLM_apply, lp.coeFn_sub, Pi.sub_apply]
  rw [sub_mul]

/-- **Operator norm bound for diagonal operators.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, let $a : \iota \to \mathbb{K}$ be bounded, and let $D_a$ be the diagonal operator
$x \mapsto (a_i x_i)_{i \in \iota}$ on $\ell^2(\iota, \mathbb{K})$. If $C \ge 0$ and $|a_i| \le C$
for every $i \in \iota$, then the operator norm satisfies $\|D_a\| \le C$. -/
theorem norm_diagonalCLM_le (a : ι → 𝕜) (hbdd : ∃ C, ∀ i, ‖a i‖ ≤ C)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, ‖a i‖ ≤ C) :
    ‖diagonalCLM a hbdd‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC0 (fun x => norm_diagonalLinMap_le a hbdd hC0 hC x)

/-- **Operator norm of a diagonal operator.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let
$a : \iota \to \mathbb{K}$ be bounded, and let $D_a$ be the diagonal operator
$x \mapsto (a_i x_i)_{i \in \iota}$ on $\ell^2(\iota, \mathbb{K})$. Then the operator norm of $D_a$
is $\|D_a\| = \sup_{i \in \iota} |a_i|$, where the supremum is taken to be $0$ when $\iota$ is
empty. -/
theorem norm_diagonalCLM (a : ι → 𝕜) (hbdd : ∃ C, ∀ i, ‖a i‖ ≤ C) :
    ‖diagonalCLM a hbdd‖ = ⨆ i, ‖a i‖ := by
  classical
  by_cases hι : Nonempty ι
  · obtain ⟨i₀⟩ := hι
    obtain ⟨C, hC0, hC⟩ := exists_nonneg_bound hbdd
    have hbdd' : BddAbove (Set.range fun i => ‖a i‖) :=
      ⟨C, fun _ ⟨i, hi⟩ => hi ▸ hC i⟩
    have hsup_nonneg : 0 ≤ ⨆ i, ‖a i‖ :=
      (norm_nonneg (a i₀)).trans (le_ciSup hbdd' i₀)
    apply le_antisymm
    · apply norm_diagonalCLM_le a hbdd hsup_nonneg
      intro i
      exact le_ciSup hbdd' i
    · have hsup_eq : (⨆ i, ‖a i‖) = sSup (Set.range fun i => ‖a i‖) := rfl
      rw [hsup_eq]
      refine csSup_le ⟨‖a i₀‖, ⟨i₀, rfl⟩⟩ ?_
      rintro - ⟨i, rfl⟩
      show ‖a i‖ ≤ ‖diagonalCLM a hbdd‖
      have hsingle : ‖a i‖ = ‖diagonalCLM a hbdd (lp.single 2 i (1 : 𝕜))‖ := by
        rw [diagonalCLM_single, norm_smul, lp.norm_single (by norm_num), norm_one, mul_one]
      rw [hsingle]
      have hle := (diagonalCLM a hbdd).le_opNorm (lp.single 2 i (1 : 𝕜))
      rw [lp.norm_single (by norm_num), norm_one, mul_one] at hle
      exact hle
  · have hι' : IsEmpty ι := not_nonempty_iff.mp hι
    have hD : diagonalCLM a hbdd = 0 := by
      ext x
      have hx : x = 0 := by
        apply lp.ext
        funext i
        exact IsEmpty.elim hι' i
      rw [hx]
      simp
    rw [hD, norm_zero]
    have hsup : (⨆ i, ‖a i‖) = 0 := by
      have hsup' : (⨆ i, ‖a i‖) = sSup (Set.range fun i => ‖a i‖) := rfl
      have hrange : Set.range (fun i => ‖a i‖) = ∅ := by
        rw [Set.range_eq_empty_iff]
        exact hι'
      simp only [hsup', hrange, Real.sSup_empty]
    rw [hsup]

/-- **Adjoint of a diagonal operator.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let
$\iota$ be a type and let $a : \iota \to \mathbb{K}$ be a bounded sequence. The adjoint of the
diagonal operator $D_a$ on $\ell^2(\iota, \mathbb{K})$ with coefficients $a$ is the diagonal
operator with the conjugate coefficients $i \mapsto \overline{a_i}$. -/
theorem adjoint_diagonalCLM (a : ι → 𝕜) (hbdd : ∃ C, ∀ i, ‖a i‖ ≤ C) :
    (diagonalCLM a hbdd)† =
      diagonalCLM (fun i => star (a i)) (by
        obtain ⟨C, hC⟩ := hbdd
        exact ⟨C, fun i => by rw [norm_star]; exact hC i⟩) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr (fun i => ?_)
  rw [diagonalCLM_apply, diagonalCLM_apply, ← smul_eq_mul, ← smul_eq_mul,
    inner_smul_left, inner_smul_right, starRingEnd_apply, star_star]

/-- **Self-adjoint diagonal operators on $\ell^2$.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, let $a : \iota \to \mathbb{K}$ be bounded, and let $D_a$ be the diagonal operator
$x \mapsto (a_i x_i)_{i \in \iota}$ on $\ell^2(\iota, \mathbb{K})$. Then $D_a$ is self-adjoint if
and only if $\overline{a_i} = a_i$, that is, $a_i$ is real, for every $i \in \iota$. -/
theorem isSelfAdjoint_diagonalCLM_iff (a : ι → 𝕜) (hbdd : ∃ C, ∀ i, ‖a i‖ ≤ C) :
    IsSelfAdjoint (diagonalCLM a hbdd) ↔ ∀ i, star (a i) = a i := by
  classical
  show star (diagonalCLM a hbdd) = diagonalCLM a hbdd ↔ _
  rw [ContinuousLinearMap.star_eq_adjoint, adjoint_diagonalCLM]
  constructor
  · intro h i
    have hsingle := DFunLike.congr_fun h (lp.single 2 i (1 : 𝕜))
    rw [diagonalCLM_single, diagonalCLM_single] at hsingle
    have hsingle := congr_arg (fun z : ℓ²(ι, 𝕜) => (z : ∀ i, 𝕜) i) hsingle
    rw [lp_smul_apply, lp_smul_apply, lp.single_apply, Pi.single_eq_same, mul_one,
      mul_one] at hsingle
    exact hsingle
  · intro h
    congr 1
    funext i
    exact h i

/-- A finite sum of compact operators is compact. -/
private theorem isCompactOperator_finset_sum {S : Finset ι}
    {T : ι → ℓ²(ι, 𝕜) →L[𝕜] ℓ²(ι, 𝕜)} (hT : ∀ i ∈ S, IsCompactOperator (T i)) :
    IsCompactOperator ((∑ i ∈ S, T i : ℓ²(ι, 𝕜) →L[𝕜] ℓ²(ι, 𝕜)) :
      ℓ²(ι, 𝕜) →ₗ[𝕜] ℓ²(ι, 𝕜)) := by
  classical
  induction S using Finset.induction with
  | empty => exact isCompactOperator_zero
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, ContinuousLinearMap.toLinearMap_add]
      exact (hT _ (Finset.mem_insert_self _ _)).add
        (ih (fun i hi' => hT i (Finset.mem_insert_of_mem hi')))

/-- The truncation of a coefficient sequence at level `n`: keep `a i` when
`‖a i‖ ≥ 1 / (n + 1)`, otherwise replace it by `0`. -/
private noncomputable def truncCoeff (a : ι → 𝕜) (n : ℕ) (i : ι) : 𝕜 :=
  if (1 : ℝ) / (n + 1) ≤ ‖a i‖ then a i else 0

/-- A rank-one term of the finite-support decomposition, evaluated pointwise. -/
theorem singleCLM_comp_evalCLM_apply [DecidableEq ι] (b : ι → 𝕜) (i : ι) (x : ℓ²(ι, 𝕜)) :
    (lp.singleContinuousLinearMap 𝕜 (fun _ : ι => 𝕜) 2 i ∘L
        ((b i) • lp.evalCLM 𝕜 (fun _ : ι => 𝕜) 2 i)) x
      = lp.single 2 i (b i * x i) :=
  rfl

/-- A diagonal operator with finitely supported coefficients is compact: it is a finite
sum of rank-one operators, each compact since it factors through the one-dimensional
domain `𝕜`. -/
private theorem isCompactOperator_diagonalCLM_of_finite_support
    {b : ι → 𝕜} (hbdd : ∃ C, ∀ i, ‖b i‖ ≤ C) (hfin : (Function.support b).Finite) :
    IsCompactOperator (diagonalCLM b hbdd) := by
  classical
  have hsum : diagonalCLM b hbdd =
      ∑ i ∈ hfin.toFinset, (lp.singleContinuousLinearMap 𝕜 (fun _ : ι => 𝕜) 2 i ∘L
        ((b i) • lp.evalCLM 𝕜 (fun _ : ι => 𝕜) 2 i)) := by
    ext x j
    rw [diagonalCLM_apply]
    simp only [sum_apply, lp.coeFn_sum, Finset.sum_apply,
      singleCLM_comp_evalCLM_apply, lp.single_apply, Finset.sum_pi_single]
    by_cases hj : j ∈ hfin.toFinset
    · simp only [hj, ite_true]
    · simp only [hj, ite_false]
      have hb : b j = 0 := by
        by_contra hne
        exact hj ((Set.Finite.mem_toFinset hfin).mpr (Function.mem_support.mpr hne))
      rw [hb, zero_mul]
  rw [hsum]
  apply isCompactOperator_finset_sum
  intro i _
  exact (isCompactOperator_of_locallyCompactSpace_rng
    (lp.singleContinuousLinearMap 𝕜 (fun _ : ι => 𝕜) 2 i)).comp_clm
      ((b i) • lp.evalCLM 𝕜 (fun _ : ι => 𝕜) 2 i)

/-- If the coefficients vanish at infinity, the diagonal operator is compact: it is the
norm limit of its finitely supported truncations. -/
private theorem isCompactOperator_diagonalCLM_of_tendsto {a : ι → 𝕜}
    (hbdd : ∃ C, ∀ i, ‖a i‖ ≤ C) (ha : Tendsto a cofinite (𝓝 0)) :
    IsCompactOperator (diagonalCLM a hbdd) := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_nonneg_bound hbdd
  have hfin : ∀ n : ℕ, {i | (1 : ℝ) / (n + 1) ≤ ‖a i‖}.Finite := by
    intro n
    have hev : ∀ᶠ i in cofinite, ‖a i‖ < 1 / (n + 1 : ℝ) := by
      have h := Metric.tendsto_nhds.mp ha (1 / (n + 1 : ℝ)) (by positivity)
      filter_upwards [h] with i hi
      simpa [dist_eq_norm] using hi
    rw [Filter.eventually_cofinite] at hev
    simpa only [not_lt] using hev
  have htrunc_bdd : ∀ n, ∃ C', ∀ i, ‖truncCoeff a n i‖ ≤ C' := fun n =>
    ⟨C, fun i => by
      show ‖(if (1 : ℝ) / (n + 1) ≤ ‖a i‖ then a i else 0)‖ ≤ C
      split_ifs with h
      · exact hC i
      · simpa using hC0⟩
  have hsupp : ∀ n, (Function.support (truncCoeff a n)).Finite := fun n =>
    (hfin n).subset fun i hi => by
      by_contra hcon
      have htr : truncCoeff a n i = 0 := by
        show (if (1 : ℝ) / (n + 1) ≤ ‖a i‖ then a i else 0) = 0
        split_ifs with h
        · exact absurd h hcon
        · rfl
      exact hi htr
  have htrunc_compact : ∀ n,
      IsCompactOperator (diagonalCLM (truncCoeff a n) (htrunc_bdd n)) := fun n =>
    isCompactOperator_diagonalCLM_of_finite_support _ (hsupp n)
  have hclose : ∀ n, ‖diagonalCLM a hbdd - diagonalCLM (truncCoeff a n) (htrunc_bdd n)‖
      ≤ 1 / (n + 1 : ℝ) := by
    intro n
    rw [diagonalCLM_sub a (truncCoeff a n) hbdd (htrunc_bdd n)]
    apply norm_diagonalCLM_le _ _ (by positivity)
    intro i
    show ‖a i - (if (1 : ℝ) / (n + 1) ≤ ‖a i‖ then a i else 0)‖ ≤ 1 / (n + 1 : ℝ)
    split_ifs with h
    · rw [sub_self, norm_zero]
      positivity
    · rw [sub_zero]
      exact le_of_not_ge h
  have hlim : Tendsto (fun n => diagonalCLM (truncCoeff a n) (htrunc_bdd n)) atTop
      (𝓝 (diagonalCLM a hbdd)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    rw [norm_sub_rev]
    exact hclose n
  exact isCompactOperator_of_tendsto hlim (Filter.Eventually.of_forall htrunc_compact)

/-- The image of a standard basis vector under a diagonal operator has norm at least
`ε` when the corresponding coefficient does. -/
private theorem norm_diagonalCLM_single_ge [DecidableEq ι] {a : ι → 𝕜} (hbdd : ∃ C, ∀ i, ‖a i‖ ≤ C)
    {ε : ℝ} {u : ℕ → ι} (hu_mem : ∀ n, ε ≤ ‖a (u n)‖) (n : ℕ) :
    ε ≤ ‖diagonalCLM a hbdd (lp.single 2 (u n) (1 : 𝕜))‖ := by
  classical
  rw [diagonalCLM_single, norm_smul, lp.norm_single (by norm_num), norm_one, mul_one]
  exact hu_mem n

/-- Images of distinct standard basis vectors under a diagonal operator are orthogonal. -/
private theorem inner_diagonalCLM_single_eq_zero [DecidableEq ι] {a : ι → 𝕜}
    (hbdd : ∃ C, ∀ i, ‖a i‖ ≤ C) {u : ℕ → ι} (hu_inj : Function.Injective u)
    {m n : ℕ} (hmn : m ≠ n) :
    ⟪diagonalCLM a hbdd (lp.single 2 (u m) (1 : 𝕜)),
      diagonalCLM a hbdd (lp.single 2 (u n) (1 : 𝕜))⟫_𝕜 = 0 := by
  classical
  rw [diagonalCLM_single, diagonalCLM_single, inner_smul_left, inner_smul_right,
    lp.inner_single_left]
  have hne : u m ≠ u n := fun h => hmn (hu_inj h)
  simp [lp.single_apply, Pi.single_eq_of_ne hne]

/-- Images of distinct standard basis vectors along an `ε`-separated coefficient sequence
are `ε * √2`-separated, by Pythagoras. -/
private theorem separation_diagonalCLM_single [DecidableEq ι] {a : ι → 𝕜} (hbdd : ∃ C, ∀ i, ‖a i‖ ≤ C)
    {ε : ℝ} (hε : 0 < ε) {u : ℕ → ι} (hu_inj : Function.Injective u)
    (hu_mem : ∀ n, ε ≤ ‖a (u n)‖) {m n : ℕ} (hmn : m ≠ n) :
    ε * Real.sqrt 2 ≤
      ‖diagonalCLM a hbdd (lp.single 2 (u m) (1 : 𝕜)) -
        diagonalCLM a hbdd (lp.single 2 (u n) (1 : 𝕜))‖ := by
  set y : ℕ → ℓ²(ι, 𝕜) := fun n => diagonalCLM a hbdd (lp.single 2 (u n) (1 : 𝕜)) with hy
  have hy_norm : ∀ n, ε ≤ ‖y n‖ := fun n => norm_diagonalCLM_single_ge hbdd hu_mem n
  have hinner : ⟪y m, -y n⟫_𝕜 = 0 := by
    rw [inner_neg_right, inner_diagonalCLM_single_eq_zero hbdd hu_inj hmn, neg_zero]
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (y m) (-y n) hinner
  have hsq : (ε * Real.sqrt 2) ^ 2 ≤ ‖y m - y n‖ ^ 2 := by
    rw [pow_two, pow_two, sub_eq_add_neg, hpyth, norm_neg]
    have h1 : ε * ε ≤ ‖y m‖ * ‖y m‖ :=
      mul_le_mul (hy_norm m) (hy_norm m) hε.le (norm_nonneg _)
    have h2 : ε * ε ≤ ‖y n‖ * ‖y n‖ :=
      mul_le_mul (hy_norm n) (hy_norm n) hε.le (norm_nonneg _)
    have h3 : (ε * Real.sqrt 2) * (ε * Real.sqrt 2) = ε * ε + ε * ε := by
      rw [mul_mul_mul_comm, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2), ← two_mul]
      ring
    rw [h3]
    linarith
  exact (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ ε * Real.sqrt 2) (norm_nonneg _)).mp hsq

/-- A `δ`-separated sequence in a compact set has no convergent subsequence: the
sequential-compactness / Cauchy contradiction, in a general metric space. -/
private theorem not_separated_of_isSeqCompact {X : Type*} [PseudoMetricSpace X]
    [FirstCountableTopology X] {s : Set X} (hs : IsCompact s)
    {y : ℕ → X} (hymem : ∀ n, y n ∈ s) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ {m n}, m ≠ n → δ ≤ dist (y m) (y n)) : False := by
  obtain ⟨z, -, φ, hφmono, hφlim⟩ := hs.isSeqCompact hymem
  have hcau := hφlim.cauchySeq
  obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hcau) δ hδ
  have hlt : dist (y (φ (N + 1))) (y (φ N)) < δ := hN (N + 1) (by omega) N (by omega)
  have hne : φ (N + 1) ≠ φ N := fun h => (hφmono.injective.ne (by norm_num : N ≠ N + 1)) h.symm
  have hge := hsep hne
  linarith

/-- If the coefficients do not vanish at infinity, there is an `ε > 0` and an
injective sequence of indices along which every coefficient has norm at least `ε`. -/
private theorem exists_injective_eps_le_of_not_tendsto {a : ι → 𝕜}
    (hnot : ¬ Tendsto a cofinite (𝓝 0)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ u : ℕ → ι, Function.Injective u ∧ ∀ n, ε ≤ ‖a (u n)‖ := by
  rw [Metric.tendsto_nhds] at hnot
  push Not at hnot
  obtain ⟨ε, hε, hε'⟩ := hnot
  rw [Filter.frequently_cofinite_iff_infinite] at hε'
  have hSinf : {i | ε ≤ ‖a i‖}.Infinite := by
    simpa only [dist_eq_norm, sub_zero] using hε'
  refine ⟨ε, hε, fun n => ((Set.Infinite.natEmbedding _ hSinf n :
      {i // i ∈ {i | ε ≤ ‖a i‖}}) : ι), ?_, fun n => ?_⟩
  · exact Subtype.val_injective.comp (Set.Infinite.natEmbedding _ hSinf).injective
  · exact (Set.Infinite.natEmbedding _ hSinf n).2

/-- The image of the closed unit ball under a compact diagonal operator has compact
closure. -/
private theorem isCompact_closure_image_closedBall_diagonalCLM {a : ι → 𝕜}
    (hbdd : ∃ C, ∀ i, ‖a i‖ ≤ C) (hcomp : IsCompactOperator (diagonalCLM a hbdd)) :
    IsCompact (closure (diagonalCLM a hbdd '' Metric.closedBall 0 1)) :=
  hcomp.isCompact_closure_image_closedBall 1

/-- Each image of a standard basis vector under a diagonal operator lies in the
closure of the image of the closed unit ball. -/
private theorem mem_closure_image_closedBall_diagonalCLM_single [DecidableEq ι]
    {a : ι → 𝕜} (hbdd : ∃ C, ∀ i, ‖a i‖ ≤ C) (u : ℕ → ι) (n : ℕ) :
    diagonalCLM a hbdd (lp.single 2 (u n) (1 : 𝕜)) ∈
      closure (diagonalCLM a hbdd '' Metric.closedBall 0 1) := by
  apply subset_closure
  refine ⟨lp.single 2 (u n) (1 : 𝕜), ?_, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right, lp.norm_single (by norm_num), norm_one]

/-- If the diagonal operator is compact, then the coefficients vanish at infinity:
otherwise the images of the standard basis vectors along an infinite
`ε`-separated set would contain no convergent subsequence. -/
private theorem tendsto_of_isCompactOperator_diagonalCLM {a : ι → 𝕜}
    (hbdd : ∃ C, ∀ i, ‖a i‖ ≤ C) (hcomp : IsCompactOperator (diagonalCLM a hbdd)) :
    Tendsto a cofinite (𝓝 0) := by
  classical
  by_contra hnot
  obtain ⟨ε, hε, u, hu_inj, hu_mem⟩ := exists_injective_eps_le_of_not_tendsto hnot
  exact not_separated_of_isSeqCompact (δ := ε * Real.sqrt 2)
    (isCompact_closure_image_closedBall_diagonalCLM hbdd hcomp)
    (fun n => mem_closure_image_closedBall_diagonalCLM_single hbdd u n)
    (mul_pos hε (by positivity : (0 : ℝ) < Real.sqrt 2)) (fun hmn => by
      rw [dist_eq_norm]
      exact separation_diagonalCLM_single hbdd hε hu_inj hu_mem hmn)

/-- **Compact diagonal operators on ℓ².** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let
$\iota$ be a type and let $a : \iota \to \mathbb{K}$ be a bounded sequence. The diagonal operator
on $\ell^2(\iota, \mathbb{K})$ with coefficients $a$ is compact if and only if $a$ tends to $0$
along the cofinite filter on $\iota$, that is, for every $\varepsilon > 0$ only finitely many
$i \in \iota$ satisfy $\|a_i\| \ge \varepsilon$. -/
theorem isCompactOperator_diagonalCLM_iff {a : ι → 𝕜}
    (hbdd : ∃ C, ∀ i, ‖a i‖ ≤ C) :
    IsCompactOperator (diagonalCLM a hbdd) ↔ Tendsto a cofinite (𝓝 0) :=
  ⟨tendsto_of_isCompactOperator_diagonalCLM hbdd,
    isCompactOperator_diagonalCLM_of_tendsto hbdd⟩

end MathlibExt.Analysis.InnerProductSpace.LpDiagonalOperator
