/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

/-!
# Fundamental parallelograms of complex lattices
-/

@[expose] public section

namespace PeriodPair

/-- **Fundamental parallelogram.** Let $\omega_1, \omega_2$ be $\mathbb{R}$-linearly independent
complex numbers and let $\alpha \in \mathbb{C}$. The fundamental parallelogram with vertex $\alpha$
is the half-open parallelogram $\alpha + P$, where $P$ is the set of $z \in \mathbb{C}$ whose two
coordinates in the $\mathbb{R}$-basis $\omega_1, \omega_2$ of $\mathbb{C}$ both lie in $[0, 1)$;
that is, $P = \{t_1 \omega_1 + t_2 \omega_2 : t_1, t_2 \in [0, 1)\}$. -/
noncomputable def fundamentalParallelogram (L : PeriodPair) (α : ℂ) : Set ℂ :=
  (α + ·) '' ZSpan.fundamentalDomain L.basis

/-- **Fundamental parallelogram at the origin.** Let $\omega_1, \omega_2$ be $\mathbb{R}$-linearly
independent complex numbers. The fundamental parallelogram with vertex $0$ equals the set of
$z \in \mathbb{C}$ whose two coordinates in the $\mathbb{R}$-basis $\omega_1, \omega_2$ of
$\mathbb{C}$ both lie in $[0, 1)$. -/
@[simp]
theorem fundamentalParallelogram_zero (L : PeriodPair) :
    L.fundamentalParallelogram 0 = ZSpan.fundamentalDomain L.basis := by
  simp [fundamentalParallelogram]

/-- **Coordinates in the period basis.** Let $\omega_1, \omega_2$ be $\mathbb{R}$-linearly
independent complex numbers, so that they form a basis of $\mathbb{C}$ over $\mathbb{R}$. For all
real numbers $t_1, t_2$, the first coordinate of $t_1 \omega_1 + t_2 \omega_2$ in this basis is
$t_1$ and the second is $t_2$. -/
lemma basis_repr_omega (L : PeriodPair) (t₁ t₂ : ℝ) (i : Fin 2) :
    L.basis.repr (t₁ • L.ω₁ + t₂ • L.ω₂) i = ![t₁, t₂] i := by
  rw [show t₁ • L.ω₁ + t₂ • L.ω₂ = t₁ • L.basis 0 + t₂ • L.basis 1 from by simp]
  simp only [map_add, map_smul, Module.Basis.repr_self, Finsupp.smul_single,
    smul_eq_mul, mul_one, Finsupp.add_apply, Finsupp.single_apply]
  fin_cases i <;>
    simp [show (1 : Fin 2) ≠ 0 from by decide, show (0 : Fin 2) ≠ 1 from by decide]

/-- **Membership in a fundamental parallelogram.** Let $\omega_1, \omega_2$ be
$\mathbb{R}$-linearly independent complex numbers and let $\alpha, z \in \mathbb{C}$. Then $z$ lies
in the fundamental parallelogram with vertex $\alpha$ if and only if there are real numbers
$t_1, t_2$ with $0 \le t_1 < 1$ and $0 \le t_2 < 1$ such that
$z = \alpha + t_1 \omega_1 + t_2 \omega_2$. -/
theorem mem_fundamentalParallelogram_iff (L : PeriodPair) {α z : ℂ} :
    z ∈ L.fundamentalParallelogram α ↔
      ∃ t₁ t₂ : ℝ, 0 ≤ t₁ ∧ t₁ < 1 ∧ 0 ≤ t₂ ∧ t₂ < 1 ∧
        z = α + t₁ • L.ω₁ + t₂ • L.ω₂ := by
  simp only [fundamentalParallelogram, Set.mem_image, ZSpan.mem_fundamentalDomain]
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨L.basis.repr w 0, L.basis.repr w 1, (hw 0).1, (hw 0).2,
      (hw 1).1, (hw 1).2, ?_⟩
    have hw_repr : w = L.basis.repr w 0 • L.ω₁ + L.basis.repr w 1 • L.ω₂ := by
      have h := L.basis.sum_repr w
      rw [Fin.sum_univ_two, L.basis_zero, L.basis_one] at h
      exact h.symm
    calc
      α + w = α + (L.basis.repr w 0 • L.ω₁ + L.basis.repr w 1 • L.ω₂) :=
        congrArg (α + ·) hw_repr
      _ = α + L.basis.repr w 0 • L.ω₁ + L.basis.repr w 1 • L.ω₂ := by abel
  · rintro ⟨t₁, t₂, h1, h2, h3, h4, rfl⟩
    refine ⟨t₁ • L.ω₁ + t₂ • L.ω₂, fun i ↦ ?_, by abel⟩
    rw [L.basis_repr_omega]
    fin_cases i
    · simpa using ⟨h1, h2⟩
    · simpa using ⟨h3, h4⟩

end PeriodPair
