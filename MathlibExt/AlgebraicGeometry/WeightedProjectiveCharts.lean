/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Actual cyclic charts and character modules of weighted projective space

The projective scheme is the actual Proj of the weighted polynomial
grading. Its chart algebra is the actual degree-zero homogeneous
localization. The comparison target is the actual fixed subring of the
cyclic root-of-unity action on the remaining polynomial coordinates.
Integer-character polynomials and degree-t localized pieces fix the
graded twisting-module comparison, including its formula on every entry.

Source: Dolgachev, *Weighted projective varieties*, Lecture Notes in
Mathematics 956 (1982), §1.1 (graded localization), §1.3.3 (cyclic charts)
and §1.5.1 (twisting modules need not be invertible);
Cadman, *Using stacks to impose tangency conditions on curves*,
Amer. J. Math. 129 (2007), §2 (root charts and character line bundles).
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.WeightedProjectiveCharts

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

section Diagonal

variable {σ : Type} (k : Type u) [Field k] (w : σ → ℕ)

/-- The actual polynomial homomorphism rescaling a coordinate by its weight. -/
def diagonalHom (a : kˣ) : MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  MvPolynomial.aeval (fun j ↦ MvPolynomial.C ((a : k) ^ w j) * MvPolynomial.X j)

@[simp] theorem diagonalHom_X (a : kˣ) (j : σ) :
    diagonalHom k w a (MvPolynomial.X j) =
      MvPolynomial.C ((a : k) ^ w j) * MvPolynomial.X j := MvPolynomial.aeval_X ..

theorem diagonalHom_mul (a b : kˣ) :
    diagonalHom k w (a * b) = (diagonalHom k w a).comp (diagonalHom k w b) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp [diagonalHom, mul_pow, MvPolynomial.C_mul, mul_assoc, mul_left_comm]

@[simp] theorem diagonalHom_one : diagonalHom k w 1 = AlgHom.id k (MvPolynomial σ k) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp [diagonalHom]

/-- Actual inverse rescaling produces the polynomial algebra automorphism. -/
def diagonalEquiv (a : kˣ) : MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k :=
  AlgEquiv.ofAlgHom (diagonalHom k w a) (diagonalHom k w a⁻¹)
    (by rw [← diagonalHom_mul, mul_inv_cancel, diagonalHom_one])
    (by rw [← diagonalHom_mul, inv_mul_cancel, diagonalHom_one])

/-- The actual diagonal action homomorphism on the polynomial algebra. -/
def diagonalAction : kˣ →* RingAut (MvPolynomial σ k) where
  toFun a := (diagonalEquiv k w a).toRingEquiv
  map_one' := by
    apply RingEquiv.toRingHom_injective
    exact congrArg AlgHom.toRingHom (diagonalHom_one k w)
  map_mul' a b := by
    apply RingEquiv.toRingHom_injective
    exact congrArg AlgHom.toRingHom (diagonalHom_mul k w a b)

/-- Restrict to the actual cyclic root-of-unity subgroup. -/
@[instance_reducible]
def cyclicAction (m : ℕ) : MulSemiringAction (rootsOfUnity m k) (MvPolynomial σ k) :=
  MulSemiringAction.compHom _ ((diagonalAction k w).comp (rootsOfUnity m k).subtype)

end Diagonal

variable (k : Type u) [Field k] (n : ℕ) (w : Fin (n + 1) → ℕ)

/-- The actual weighted polynomial grading. -/
def grading : ℕ → Submodule k (MvPolynomial (Fin (n + 1)) k) :=
  MvPolynomial.weightedHomogeneousSubmodule k w

instance weightedGrading : GradedAlgebra (grading k n w) := MvPolynomial.weightedGradedAlgebra k w

/-- The actual weighted projective scheme. -/
abbrev weightedProjective : Scheme.{u} := Proj (grading k n w)

/-- The actual principal chart and its degree-zero homogeneous localization. -/
abbrev chart (i : Fin (n + 1)) := Proj.basicOpen (grading k n w) (MvPolynomial.X i)

abbrev chartRing (i : Fin (n + 1)) :=
  HomogeneousLocalization.Away (grading k n w) (MvPolynomial.X i)

/-- Coordinates remaining after normalizing the chosen projective coordinate. -/
abbrev OtherCoordinate (i : Fin (n + 1)) := {j : Fin (n + 1) // j ≠ i}

abbrev cyclicPolynomialRing (i : Fin (n + 1)) := MvPolynomial (OtherCoordinate n i) k

instance chartCyclicAction (i : Fin (n + 1)) :
    MulSemiringAction (rootsOfUnity (w i) k) (cyclicPolynomialRing k n i) :=
  cyclicAction k (fun j : OtherCoordinate n i ↦ w j.1) (w i)

/-- The actual cyclic invariant algebra, not an arbitrary quotient ring. -/
abbrev invariantChartRing (i : Fin (n + 1)) :=
  FixedPoints.subring (cyclicPolynomialRing k n i) (rootsOfUnity (w i) k)

/-- The actual character acting on a remaining coordinate. -/
def coordinateCharacter (i : Fin (n + 1)) (j : OtherCoordinate n i) :
    rootsOfUnity (w i) k →* kˣ where
  toFun a := a.1 ^ w j.1
  map_one' := by simp
  map_mul' := by intro a b; simp [mul_pow]

/-- The geometric stabilizer of a chart point is the actual intersection
of the coordinate-character kernels on its nonzero coordinates. -/
def geometricStabilizer (i : Fin (n + 1)) (z : OtherCoordinate n i → k) :
    Subgroup (rootsOfUnity (w i) k) :=
  ⨅ j : {j : OtherCoordinate n i // z j ≠ 0}, (coordinateCharacter k n w i j.1).ker

/-- The actual ordinary localization in which all comparison formulas live. -/
abbrev ordinaryChart (i : Fin (n + 1)) :=
  Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) k)

/-- The actual localized projective coordinate, as a unit. -/
def coordinateUnit (i : Fin (n + 1)) : (ordinaryChart k n i)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit
    (S := ordinaryChart k n i) (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) k)).unit

/-- Weighted degree of a monomial in the remaining coordinates. -/
def monomialWeight (i : Fin (n + 1)) (a : OtherCoordinate n i →₀ ℕ) : ℕ :=
  a.sum (fun j e ↦ w j.1 * e)

/-- The value in the localization $k[x_0, \dots, x_n][x_i^{-1}]$ of a polynomial
$p = \sum_a c_a x^a$ in the coordinates other than $x_i$, at an integer character $t$: the sum
$\sum_a c_a x^a x_i^{e(a)}$, where $\mathrm{wt}(a) = \sum_{j \ne i} w_j a_j$ is the weighted degree
of $x^a$ and $e(a) = (t - \mathrm{wt}(a)) / w_i$ is integer division rounded down ($0$ when
$w_i = 0$). If $k$ has $w_i$ distinct $w_i$-th roots of unity and $p$ has character $t$ for their
action $x_j \mapsto \zeta^{w_j} x_j$, then $w_i$ divides $t - \mathrm{wt}(a)$ whenever $c_a \ne 0$,
so the division is exact. -/
def chartValue (i : Fin (n + 1)) (t : ℤ) (p : cyclicPolynomialRing k n i) :
    ordinaryChart k n i :=
  ∑ a ∈ p.support, algebraMap k (ordinaryChart k n i) (p.coeff a) *
    (∏ j : OtherCoordinate n i,
      algebraMap (MvPolynomial (Fin (n + 1)) k) (ordinaryChart k n i)
        (MvPolynomial.X j.1) ^ (a j)) *
      ((coordinateUnit k n i) ^ ((t - (monomialWeight n w i a : ℤ)) / (w i : ℤ)) :
        (ordinaryChart k n i)ˣ)

/-- The actual character-t polynomial space of the cyclic action. -/
def characterSpace (i : Fin (n + 1)) (t : ℤ) : Submodule k (cyclicPolynomialRing k n i) where
  carrier := {p | ∀ a : rootsOfUnity (w i) k,
    diagonalHom k (fun j : OtherCoordinate n i ↦ w j.1) a.1 p =
      MvPolynomial.C ((a.1 ^ t : kˣ) : k) * p}
  zero_mem' := by intro a; simp
  add_mem' := by intro p q hp hq a; simp [hp a, hq a, mul_add]
  smul_mem' := by
    intro c p hp a
    simp [hp a, Algebra.smul_def, mul_left_comm]

/-- The actual degree-t localized piece, generated by homogeneous fractions
whose numerator/denominator weighted degrees differ by t. -/
def shiftedPiece (i : Fin (n + 1)) (t : ℤ) : Submodule k (ordinaryChart k n i) :=
  Submodule.span k {x | ∃ m d : ℕ, ∃ p : MvPolynomial (Fin (n + 1)) k,
    p ∈ grading k n w d ∧ (d : ℤ) - m * (w i : ℤ) = t ∧
      x = algebraMap (MvPolynomial (Fin (n + 1)) k) (ordinaryChart k n i) p *
        ((coordinateUnit k n i) ^ (-(m : ℤ)) : (ordinaryChart k n i)ˣ)}

/-- All comparison maps are pinned by the actual localization formulas. -/
structure WeightedChartComparison (i : Fin (n + 1)) where
  invariantIso : invariantChartRing k n w i ≃+* chartRing k n w i
  invariant_normalization : ∀ p : invariantChartRing k n w i,
    HomogeneousLocalization.val (invariantIso p) = chartValue k n w i 0 p.1
  twistingIso : ∀ t : ℤ, characterSpace k n w i t ≃ₗ[k] shiftedPiece k n w i t
  twisting_normalization : ∀ (t : ℤ) (p : characterSpace k n w i t),
    (twistingIso t p).1 = chartValue k n w i t p.1
  twisting_module_law : ∀ (t : ℤ) (a : invariantChartRing k n w i)
      (p : characterSpace k n w i t),
    chartValue k n w i t (a.1 * p.1) =
      HomogeneousLocalization.val (invariantIso a) * chartValue k n w i t p.1

end MathlibExt.AlgebraicGeometry.WeightedProjectiveCharts
