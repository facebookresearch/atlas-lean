/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Topology.Algebra.Order.Archimedean
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Topology.Algebra.Ring.Real

@[expose] public section

/-! Soundness of Gram-matrix sum-of-squares certificates over the rationals.
Prajna-Jadbabaie, "Safety Verification of Hybrid Systems Using Barrier Certificates",
HSCC 2004, Section 4; Parrilo, PhD thesis (Caltech 2000), Chapter 4, eq. (4.4). -/

open scoped BigOperators Matrix

namespace SOSCertificate

/-- The Gram polynomial `z^T Q z` for `z : iota -> MvPolynomial sigma Rat` and
`Q : Matrix iota iota Rat`. -/
noncomputable def gramPoly {sigma iota : Type*} [Fintype iota]
    (z : iota -> MvPolynomial sigma Rat)
    (Q : Matrix iota iota Rat) : MvPolynomial sigma Rat :=
  ∑ i, ∑ j, MvPolynomial.C (Q i j) * z i * z j

/-- The real quadratic form agrees with the cast of the rational one on rational vectors. -/
private theorem quadForm_ratCast {iota : Type*} [Fintype iota] (Q : Matrix iota iota Rat)
    (q : iota -> Rat) :
    star (fun i => (Rat.cast : Rat -> Real) (q i)) ⬝ᵥ
        ((Q.map (Rat.cast : Rat -> Real)) *ᵥ (fun i => (Rat.cast : Rat -> Real) (q i)))
      = (Rat.cast : Rat -> Real) (star q ⬝ᵥ (Q *ᵥ q)) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, star_trivial]
  norm_cast

/-- The quadratic form of a real matrix is continuous. -/
private theorem continuous_quadForm {iota : Type*} [Fintype iota]
    (M : Matrix iota iota Real) :
    Continuous fun x : iota -> Real => star x ⬝ᵥ (M *ᵥ x) := by
  have heq : (fun x : iota -> Real => star x ⬝ᵥ (M *ᵥ x))
      = fun x => ∑ i, x i * (∑ j, M i j * x j) := by
    funext x
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial]
  rw [heq]
  refine continuous_finsetSum Finset.univ fun i _ => ?_
  exact (continuous_apply i).mul
    (continuous_finsetSum Finset.univ fun j _ => continuous_const.mul (continuous_apply j))

/-- A rational PSD matrix casts to a real PSD matrix. This must be proved
(e.g. density of rational vectors + continuity of the quadratic form), not assumed. -/
theorem posSemidef_map_ratCast {iota : Type*} [Fintype iota] {Q : Matrix iota iota Rat}
    (hQ : Q.PosSemidef) : (Q.map (Rat.cast : Rat -> Real)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (hQ.isHermitian.map (Rat.cast : Rat -> Real) (fun q => by simp)) ?_
  have hdense : DenseRange (Pi.map fun (_ : iota) => (Rat.cast : Rat -> Real)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  have hcont : Continuous fun x : iota -> Real =>
      star x ⬝ᵥ ((Q.map (Rat.cast : Rat -> Real)) *ᵥ x) :=
    continuous_quadForm (Q.map (Rat.cast : Rat -> Real))
  have hclosed : IsClosed {x : iota -> Real |
      0 ≤ star x ⬝ᵥ ((Q.map (Rat.cast : Rat -> Real)) *ᵥ x)} :=
    isClosed_le continuous_const hcont
  have hrat : ∀ q : iota -> Rat,
      (0 : Real) ≤ star (Pi.map (fun (_ : iota) => (Rat.cast : Rat -> Real)) q) ⬝ᵥ
        ((Q.map (Rat.cast : Rat -> Real)) *ᵥ
          (Pi.map (fun (_ : iota) => (Rat.cast : Rat -> Real)) q)) := by
    intro q
    have heq : star (Pi.map (fun (_ : iota) => (Rat.cast : Rat -> Real)) q) ⬝ᵥ
        ((Q.map (Rat.cast : Rat -> Real)) *ᵥ
          (Pi.map (fun (_ : iota) => (Rat.cast : Rat -> Real)) q))
        = ((star q ⬝ᵥ (Q *ᵥ q) : Rat) : Real) := quadForm_ratCast Q q
    rw [heq]
    exact Rat.cast_nonneg.mpr (hQ.dotProduct_mulVec_nonneg q)
  exact isClosed_property hdense hclosed hrat

/-- Evaluation of the Gram polynomial is the real quadratic form in the evaluated entries. -/
private theorem eval₂_gramPoly {sigma iota : Type*} [Fintype iota]
    (z : iota -> MvPolynomial sigma Rat) (Q : Matrix iota iota Rat) (x : sigma -> Real) :
    (gramPoly z Q).eval₂ (Rat.castHom Real) x
      = star (fun i => (z i).eval₂ (Rat.castHom Real) x) ⬝ᵥ
        ((Q.map (Rat.cast : Rat -> Real)) *ᵥ
          (fun i => (z i).eval₂ (Rat.castHom Real) x)) := by
  simp only [gramPoly, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
    Rat.coe_castHom, dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, star_trivial,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

-- Clause map (Prajna-Jadbabaie HSCC 2004 Sec. 4; Parrilo thesis Ch. 4, eq. (4.4)):
-- `gramPoly z Q` over `MvPolynomial sigma Rat` formalizes `p = z^T Q z` with rational
-- coefficients; `hQ : Q.PosSemidef` (`Matrix.PosSemidef`, hence Hermitian) is rationality
-- plus positive semidefiniteness of `Q`; `0 <= eval₂ ...` at every real point `x` is the
-- conclusion "F(x) is also psd" (nonnegativity on `Real`).
/-- Gram soundness: if `Q` is rational PSD then `z^T Q z` is nonnegative at
every real point. Parrilo (4.4); Prajna-Jadbabaie Sec. 4. -/
theorem eval_gramPoly_nonneg {sigma iota : Type*} [Fintype iota]
    (z : iota -> MvPolynomial sigma Rat) {Q : Matrix iota iota Rat} (hQ : Q.PosSemidef)
    (x : sigma -> Real) : 0 <= (gramPoly z Q).eval₂ (Rat.castHom Real) x := by
  rw [eval₂_gramPoly z Q x]
  exact (posSemidef_map_ratCast hQ).dotProduct_mulVec_nonneg _

/-- The vector of monomials of total degree at most 1 in `n` variables. -/
noncomputable def monomialVecDegLE1 (n : Nat) : Option (Fin n) -> MvPolynomial (Fin n) Rat
  | none => 1
  | some i => MvPolynomial.X i

/-- Gram soundness for the degree-`≤ 1` monomial vector. -/
theorem eval_gramPoly_monomials_nonneg (n : Nat)
    {Q : Matrix (Option (Fin n)) (Option (Fin n)) Rat} (hQ : Q.PosSemidef)
    (x : Fin n -> Real) :
    0 <= (gramPoly (monomialVecDegLE1 n) Q).eval₂ (Rat.castHom Real) x :=
  eval_gramPoly_nonneg _ hQ x

end SOSCertificate
