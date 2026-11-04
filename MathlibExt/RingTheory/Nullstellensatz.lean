/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section

/-!
# Weak Nullstellensatz: maximal ideals as evaluation kernels, and in quotients

Hilbert's weak Nullstellensatz, from AlgebraNotes (Lecture 11, Review:
Hilbert's Nullstellensatz):

* The maximal ideals in `ℂ[x₁, …, xₙ]` are exactly the kernels of
  evaluation homomorphisms, hence in bijection with `ℂⁿ`.
* The maximal ideals in `ℂ[x₁, …, xₙ] / (P₁, …, Pₘ)` are in bijection
  with the common zeroes of `P₁, …, Pₘ`.

Source: `v1/Atlas/AlgebraNotes/code/CommutativeAlgebra.lean` (theorems
`CommutativeAlgebra.hilbert_nullstellensatz_weak_ker` and
`CommutativeAlgebra.hilbert_nullstellensatz_weak`). Mathlib has the base
case — maximal ideals are vanishing ideals of singletons
(`MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton`) — but no
statement of either the kernel form or the quotient form.
-/

namespace HilbertNullstellensatz

open MvPolynomial Ideal

/-- **Vanishing ideal of a point.** For a point $a \in \mathbb{C}^n$, the ideal of polynomials in
$\mathbb{C}[x_1, \ldots, x_n]$ that vanish on $\{a\}$ equals the kernel of the evaluation
homomorphism $\mathbb{C}[x_1, \ldots, x_n] \to \mathbb{C}$, $f \mapsto f(a)$. -/
theorem vanishingIdeal_singleton_eq_ker_aeval (n : ℕ) (a : Fin n → ℂ) :
    (vanishingIdeal ℂ {a} : Ideal (MvPolynomial (Fin n) ℂ)) =
      RingHom.ker (aeval a : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ) := by
  ext p
  simp [RingHom.mem_ker]

/-- **Weak Nullstellensatz, kernel form.** Let $n$ be a natural number. An ideal $I$ of the
polynomial ring $\mathbb{C}[x_1, \ldots, x_n]$ is maximal if and only if there is a point
$a \in \mathbb{C}^n$ such that $I$ is the kernel of the evaluation homomorphism
$\mathbb{C}[x_1, \ldots, x_n] \to \mathbb{C}$, $f \mapsto f(a)$. -/
theorem isMaximal_iff_eq_ker_aeval (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    I.IsMaximal ↔
      ∃ a : Fin n → ℂ, I = RingHom.ker (aeval a : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ) := by
  rw [MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, ha.trans (vanishingIdeal_singleton_eq_ker_aeval n a)⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, ha.trans (vanishingIdeal_singleton_eq_ker_aeval n a).symm⟩

set_option linter.style.haveILetI false in
/-- **Weak Nullstellensatz, quotient form.** Let $P_1, \ldots, P_m$ be polynomials in
$\mathbb{C}[x_1, \ldots, x_n]$ and let $A = \mathbb{C}[x_1, \ldots, x_n]/(P_1, \ldots, P_m)$.
An ideal $J$ of $A$ is maximal if and only if there is a common zero $a \in \mathbb{C}^n$ of
$P_1, \ldots, P_m$ such that $J$ is the image in $A$ of the ideal of polynomials vanishing at
$a$. -/
theorem isMaximal_quotient_iff_exists_common_zero (n m : ℕ)
    (P : Fin m → MvPolynomial (Fin n) ℂ)
    (J : Ideal (MvPolynomial (Fin n) ℂ ⧸ Ideal.span (Set.range P))) :
    J.IsMaximal ↔
      ∃ a : Fin n → ℂ, (∀ i, MvPolynomial.aeval a (P i) = 0) ∧
        J = Ideal.map (Ideal.Quotient.mk (Ideal.span (Set.range P))) (vanishingIdeal ℂ {a}) := by
  constructor
  · intro hJ
    haveI : J.IsMaximal := hJ
    have hcomap : (Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range P))) J).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    obtain ⟨a, ha⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mp hcomap
    refine ⟨a, ?_, ?_⟩
    · intro i
      have hPi : P i ∈ Ideal.span (Set.range P) := Ideal.subset_span ⟨i, rfl⟩
      have hle : Ideal.span (Set.range P) ≤
          Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range P))) J := by
        intro x hx
        rw [Ideal.mem_comap]
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
        exact J.zero_mem
      have hPiV : P i ∈ vanishingIdeal ℂ ({a} : Set (Fin n → ℂ)) := ha ▸ hle hPi
      simp [vanishingIdeal] at hPiV
      exact hPiV
    · have h := (Ideal.map_comap_of_surjective (Ideal.Quotient.mk (Ideal.span (Set.range P)))
        Ideal.Quotient.mk_surjective J).symm
      rw [ha] at h
      exact h
  · rintro ⟨a, ha, rfl⟩
    have hmax : (vanishingIdeal ℂ ({a} : Set (Fin n → ℂ))).IsMaximal :=
      MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mpr ⟨a, rfl⟩
    have hle : Ideal.span (Set.range P) ≤ vanishingIdeal ℂ ({a} : Set (Fin n → ℂ)) := by
      rw [Ideal.span_le]
      intro p ⟨i, hi⟩
      simp [vanishingIdeal]
      rw [← hi]
      exact ha i
    haveI := hmax
    have hker : RingHom.ker (Ideal.Quotient.mk (Ideal.span (Set.range P))) ≤
        vanishingIdeal ℂ ({a} : Set (Fin n → ℂ)) := by
      rw [Ideal.mk_ker]
      exact hle
    exact Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective hker

end HilbertNullstellensatz
