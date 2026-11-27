/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.ChartAtInfinity
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.Tactic.ComputeDegree

/-!
# The chart at infinity of a Weierstrass cubic is free and finitely presented

Let `W` be a Weierstrass curve over a commutative ring `R`, with coordinate ring at infinity
`B_W = R[z, w] / (h)`, `h = w + a₁ z w + a₃ w² - z³ - a₂ z² w - a₄ z w² - a₆ w³`
(`WeierstrassCurve.CoordinateRingAtInfinity`), the chart `Y ≠ 0` of the projective cubic.
This file proves:

* as a polynomial in `z` over `R[w]`, `-h = z³ + a₂ w z² + (a₄ w² - a₁ w) z - (w + a₃ w² - a₆ w³)`
  is monic (`WeierstrassCurve.monic_monicPolynomialAtInfinity`), so
  `B_W ≃ R[w][z] / (-h)` (`WeierstrassCurve.coordinateRingAtInfinityEquivAdjoinRoot`) is free
  over `R[w]` with basis `1, z, z²`, hence free over `R`;
* `B_W` is a free, hence flat, `R`-module, and a finitely presented `R`-algebra;
* base change: `S ⊗[R] B_W ≃ B_{W_S}` for every `R`-algebra `S`
  (`WeierstrassCurve.tensorCoordinateRingAtInfinityEquiv`), so the fibres of the chart are the
  charts of the reduced curves.

The source states flatness over a discrete valuation ring `R`; the argument here (monicity in
`z`) works over every commutative ring. For the other chart `Z ≠ 0`, Mathlib already provides
`WeierstrassCurve.Affine.CoordinateRing.instFree` (free over `R`) and
`AdjoinRoot.finitePresentation` (finitely presented).

## References

* B. Conrad, *Minimal models for elliptic curves*, notes, 21 November 2015,
  <http://math.stanford.edu/~conrad/papers/minimalmodel.pdf>, §2, p. 2: "the monicity of the
  leading terms in (2.1) implies that they are `R`-flat".
-/

@[expose] public section

open Polynomial
open scoped TensorProduct

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- **The equation at infinity as a monic cubic in `z`.** Let `W` be a Weierstrass curve over a
commutative ring `R`. This is the polynomial
`z³ + a₂ w z² + (a₄ w² - a₁ w) z - (w + a₃ w² - a₆ w³)` in `R[w][z]`, written
`(MvPolynomial (Fin 1) R)[X]` with `w` the variable `0`; it is `-h` for
`h = w + a₁ z w + a₃ w² - z³ - a₂ z² w - a₄ z w² - a₆ w³` read as a polynomial in `z`
(`finSuccEquiv_polynomialAtInfinity`). -/
noncomputable def monicPolynomialAtInfinity : (MvPolynomial (Fin 1) R)[X] :=
  X ^ 3 + C (MvPolynomial.C W.a₂ * MvPolynomial.X 0) * X ^ 2 +
    C (MvPolynomial.C W.a₄ * MvPolynomial.X 0 ^ 2 - MvPolynomial.C W.a₁ * MvPolynomial.X 0) * X -
    C (MvPolynomial.X 0 + MvPolynomial.C W.a₃ * MvPolynomial.X 0 ^ 2 -
      MvPolynomial.C W.a₆ * MvPolynomial.X 0 ^ 3)

/-- **`h` as a polynomial in `z`.** Let `W` be a Weierstrass curve over a commutative ring `R`.
Under `R[z, w] ≃ R[w][z]` (Mathlib's `MvPolynomial.finSuccEquiv`, which keeps `z`, the variable
`0`, as the polynomial variable), `h = w + a₁ z w + a₃ w² - z³ - a₂ z² w - a₄ z w² - a₆ w³` is
sent to `-(z³ + a₂ w z² + (a₄ w² - a₁ w) z - (w + a₃ w² - a₆ w³))`. -/
theorem finSuccEquiv_polynomialAtInfinity :
    MvPolynomial.finSuccEquiv R 1 W.polynomialAtInfinity = -W.monicPolynomialAtInfinity := by
  have h1 : MvPolynomial.finSuccEquiv R 1 (MvPolynomial.X 1) = C (MvPolynomial.X 0) :=
    MvPolynomial.finSuccEquiv_X_succ (j := 0)
  have h0 (a : R) : MvPolynomial.finSuccEquiv R 1 (MvPolynomial.C a) = C (MvPolynomial.C a) := by
    rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]; rfl
  simp only [polynomialAtInfinity, monicPolynomialAtInfinity, map_add, map_sub, map_mul, map_pow,
    MvPolynomial.finSuccEquiv_X_zero, h1, h0]
  ring

/-- **The equation at infinity is monic in `z`.** Let `W` be a Weierstrass curve over a
commutative ring `R`. The polynomial `z³ + a₂ w z² + (a₄ w² - a₁ w) z - (w + a₃ w² - a₆ w³)`
in `R[w][z]`, that is `-h` read as a polynomial in `z`, is monic. -/
theorem monic_monicPolynomialAtInfinity : W.monicPolynomialAtInfinity.Monic := by
  unfold monicPolynomialAtInfinity
  monicity!

/-- **The chart at infinity as a monic extension of `R[w]`.** Let `W` be a Weierstrass curve over
a commutative ring `R`. The `R`-algebra isomorphism
`B_W = R[z, w] / (h) ≃ R[w][z] / (z³ + a₂ w z² + (a₄ w² - a₁ w) z - (w + a₃ w² - a₆ w³))`
induced by `R[z, w] ≃ R[w][z]`, since this cubic is `-h` read in `z`. -/
noncomputable def coordinateRingAtInfinityEquivAdjoinRoot :
    W.CoordinateRingAtInfinity ≃ₐ[R] AdjoinRoot W.monicPolynomialAtInfinity :=
  Ideal.quotientEquivAlg _ _ (MvPolynomial.finSuccEquiv R 1) (by
    rw [Ideal.map_span, Set.image_singleton, RingHom.coe_coe, finSuccEquiv_polynomialAtInfinity,
      Ideal.span_singleton_neg])

/-- **The chart at infinity is free.** Let `W` be a Weierstrass curve over a commutative ring
`R`. The coordinate ring at infinity `B_W = R[z, w] / (h)`,
`h = w + a₁ z w + a₃ w² - z³ - a₂ z² w - a₄ z w² - a₆ w³`, is a free `R`-module. Proof: `-h` is
monic of degree `3` in `z` over `R[w]` (`monic_monicPolynomialAtInfinity`), so `B_W` is free over
`R[w]` with basis `1, z, z²` (`coordinateRingAtInfinityEquivAdjoinRoot`), and `R[w]` is free
over `R`.

In particular `B_W` is a flat `R`-module (Mathlib's `Module.Flat.of_free`). The source states
flatness for `R` a discrete valuation ring, through `π` being a nonzerodivisor on `B_W`; this
statement holds for every commutative ring `R`.

Source: B. Conrad, *Minimal models for elliptic curves*, 2015,
<http://math.stanford.edu/~conrad/papers/minimalmodel.pdf>, §2, p. 2 ("the monicity of the
leading terms in (2.1) implies that they are `R`-flat"). -/
instance : Module.Free R W.CoordinateRingAtInfinity := by
  have : Module.Free (MvPolynomial (Fin 1) R) (AdjoinRoot W.monicPolynomialAtInfinity) :=
    .of_basis (AdjoinRoot.powerBasis' W.monic_monicPolynomialAtInfinity).basis
  have : Module.Free R (AdjoinRoot W.monicPolynomialAtInfinity) :=
    Module.Free.trans (S := MvPolynomial (Fin 1) R)
  exact .of_equiv W.coordinateRingAtInfinityEquivAdjoinRoot.symm.toLinearEquiv

/-- **The chart at infinity is flat.** Let `W` be a Weierstrass curve over a commutative ring
`R`. The coordinate ring at infinity `B_W = R[z, w] / (h)`,
`h = w + a₁ z w + a₃ w² - z³ - a₂ z² w - a₄ z w² - a₆ w³`, is a flat `R`-module, being free.
The source assumes `R` is a discrete valuation ring, which is not used.

Source: B. Conrad, *Minimal models for elliptic curves*, 2015,
<http://math.stanford.edu/~conrad/papers/minimalmodel.pdf>, §2, p. 2. -/
theorem flat_coordinateRingAtInfinity : Module.Flat R W.CoordinateRingAtInfinity :=
  inferInstance

/-- **The chart at infinity is finitely presented.** Let `W` be a Weierstrass curve over a
commutative ring `R`. The coordinate ring at infinity `B_W = R[z, w] / (h)` is a finitely
presented `R`-algebra: a quotient of a polynomial ring in two variables by a principal ideal.
The source assumes `R` is a discrete valuation ring, which is not used.

Source: B. Conrad, *Minimal models for elliptic curves*, 2015,
<http://math.stanford.edu/~conrad/papers/minimalmodel.pdf>, §2, p. 2. -/
instance : Algebra.FinitePresentation R W.CoordinateRingAtInfinity :=
  Algebra.FinitePresentation.quotient ⟨{W.polynomialAtInfinity}, by simp⟩

/-- **The polynomial at infinity commutes with base change.** Let `W` be a Weierstrass curve over
a commutative ring `R` and let `S` be a commutative `R`-algebra. The polynomial at infinity of the
base change `W_S` is the image of `h = w + a₁ z w + a₃ w² - z³ - a₂ z² w - a₄ z w² - a₆ w³` under
`R[z, w] → S[z, w]`. -/
theorem baseChange_polynomialAtInfinity (S : Type*) [CommRing S] [Algebra R S] :
    (W.baseChange S).polynomialAtInfinity =
      MvPolynomial.map (algebraMap R S) W.polynomialAtInfinity := by
  simp [polynomialAtInfinity, baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]

/-- **The fibres of the chart at infinity.** Let `W` be a Weierstrass curve over a commutative
ring `R` and let `S` be a commutative `R`-algebra, for instance the residue field of a point of
`Spec R`. Then `S ⊗[R] B_W ≃ B_{W_S}` as `S`-algebras: the base change of
`B_W = R[z, w] / (h)` is `S[z, w] / (h_S)`, the coordinate ring at infinity of the base change
`W_S`, with `1 ⊗ z ↦ z` and `1 ⊗ w ↦ w` (`tensorCoordinateRingAtInfinityEquiv_tmul_zAtInfinity`,
`tensorCoordinateRingAtInfinityEquiv_tmul_wAtInfinity`).

Source: B. Conrad, *Minimal models for elliptic curves*, 2015,
<http://math.stanford.edu/~conrad/papers/minimalmodel.pdf>, §2, p. 2 (the fibres of the
projective Weierstrass curve are the plane cubics cut out by the reduced equation); stated here
for the chart `Y ≠ 0`. -/
noncomputable def tensorCoordinateRingAtInfinityEquiv (S : Type*) [CommRing S] [Algebra R S] :
    S ⊗[R] W.CoordinateRingAtInfinity ≃ₐ[S] (W.baseChange S).CoordinateRingAtInfinity :=
  (Algebra.TensorProduct.tensorQuotientEquiv S _ S _).trans
    (Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv R S) (by
      rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
        baseChange_polynomialAtInfinity]
      congr 2
      simp [MvPolynomial.algebraTensorAlgEquiv_tmul]))

/-- The isomorphism `S ⊗[R] B_W ≃ B_{W_S}` sends `1 ⊗ z` to `z`. -/
theorem tensorCoordinateRingAtInfinityEquiv_tmul_zAtInfinity (S : Type*) [CommRing S]
    [Algebra R S] :
    W.tensorCoordinateRingAtInfinityEquiv S (1 ⊗ₜ W.zAtInfinity) =
      (W.baseChange S).zAtInfinity := by
  rw [tensorCoordinateRingAtInfinityEquiv, AlgEquiv.trans_apply, zAtInfinity, zAtInfinity,
    Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul, Ideal.quotientEquivAlg_mk]
  simp [MvPolynomial.algebraTensorAlgEquiv_tmul]

/-- The isomorphism `S ⊗[R] B_W ≃ B_{W_S}` sends `1 ⊗ w` to `w`. -/
theorem tensorCoordinateRingAtInfinityEquiv_tmul_wAtInfinity (S : Type*) [CommRing S]
    [Algebra R S] :
    W.tensorCoordinateRingAtInfinityEquiv S (1 ⊗ₜ W.wAtInfinity) =
      (W.baseChange S).wAtInfinity := by
  rw [tensorCoordinateRingAtInfinityEquiv, AlgEquiv.trans_apply, wAtInfinity, wAtInfinity,
    Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul, Ideal.quotientEquivAlg_mk]
  simp [MvPolynomial.algebraTensorAlgEquiv_tmul]

end WeierstrassCurve
