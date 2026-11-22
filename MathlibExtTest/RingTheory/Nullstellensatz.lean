/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.Nullstellensatz
import Mathlib.Tactic

namespace MathlibExtTest.RingTheory.Nullstellensatz

open HilbertNullstellensatz MvPolynomial Ideal

/-- The vanishing ideal of the singleton `{0}` in one variable is the
kernel of evaluation at `0`. -/
example :
    (vanishingIdeal ℂ {fun _ : Fin 1 => (0 : ℂ)} :
      Ideal (MvPolynomial (Fin 1) ℂ)) =
      RingHom.ker (aeval (fun _ : Fin 1 => (0 : ℂ)) :
        MvPolynomial (Fin 1) ℂ →ₐ[ℂ] ℂ) :=
  vanishingIdeal_singleton_eq_ker_aeval 1 _

/-- The kernel of evaluation at `0` is a maximal ideal of `ℂ[x]`. -/
example :
    (RingHom.ker (aeval (fun _ : Fin 1 => (0 : ℂ)) :
      MvPolynomial (Fin 1) ℂ →ₐ[ℂ] ℂ)).IsMaximal := by
  exact (isMaximal_iff_eq_ker_aeval 1 _).mpr ⟨fun _ => 0, rfl⟩

/-- In `ℂ[x] / (x)`, the image of the vanishing ideal of `{0}` is
maximal: `0` is the unique common zero of `P = (x)`. -/
example :
    (Ideal.map (Ideal.Quotient.mk
      (Ideal.span (Set.range (fun _ : Fin 1 => (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℂ)))))
      (vanishingIdeal ℂ {fun _ : Fin 1 => (0 : ℂ)})).IsMaximal := by
  apply (isMaximal_quotient_iff_exists_common_zero 1 1
    (fun _ : Fin 1 => (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℂ)) _).mpr
  refine ⟨fun _ => 0, ?_, rfl⟩
  intro i
  simp

/-- Forward direction in `ℂ[x] / (x)`: every maximal ideal comes from a
common zero of `x`, and that zero must be `0`. -/
example
    (J : Ideal (MvPolynomial (Fin 1) ℂ ⧸
      Ideal.span (Set.range (fun _ : Fin 1 => (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℂ)))))
    (hJ : J.IsMaximal) :
    ∃ a : Fin 1 → ℂ, (∀ i, MvPolynomial.aeval a
        ((fun _ : Fin 1 => (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℂ)) i) = 0) ∧
      J = Ideal.map (Ideal.Quotient.mk
        (Ideal.span (Set.range (fun _ : Fin 1 => (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℂ)))))
        (vanishingIdeal ℂ {a}) :=
  (isMaximal_quotient_iff_exists_common_zero 1 1
    (fun _ : Fin 1 => (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℂ)) J).mp hJ

/-- Two-variable case: in `ℂ[x, y] / (x, y)`, the image of the
vanishing ideal of `{(0, 0)}` is maximal. -/
example :
    (Ideal.map (Ideal.Quotient.mk
      (Ideal.span (Set.range (fun i : Fin 2 => (MvPolynomial.X i : MvPolynomial (Fin 2) ℂ)))))
      (vanishingIdeal ℂ {fun _ : Fin 2 => (0 : ℂ)})).IsMaximal := by
  apply (isMaximal_quotient_iff_exists_common_zero 2 2
    (fun i : Fin 2 => (MvPolynomial.X i : MvPolynomial (Fin 2) ℂ)) _).mpr
  refine ⟨fun _ => 0, ?_, rfl⟩
  intro i
  simp

end MathlibExtTest.RingTheory.Nullstellensatz
