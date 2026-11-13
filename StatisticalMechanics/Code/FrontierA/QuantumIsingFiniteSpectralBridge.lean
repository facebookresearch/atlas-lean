/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.QuantumIsingSquareTorusAdapter
import Code.FrontierA.QuantumIsingSymbolReduction









open scoped BigOperators

namespace StatMech.FrontierA

open StatMech.Onsager

private theorem quantumIsing_sinh_neg_log
    {x : Real} (hx : 0 < x) :
    Real.sinh (-Real.log x) = (1 - x ^ 2) / (2 * x) := by
  rw [Real.sinh_eq, Real.exp_neg, neg_neg, Real.exp_log hx]
  field_simp [hx.ne']



theorem quantumIsingVerticalNormalization_mul_symbol_eq_reduced
    (beta h : Real) (n : Nat) (k q : Real)
    (hx : 0 < beta * h / (2 * n))
    (hx1 : beta * h / (2 * n) < 1) :
    4 * Real.exp (-2 * quantumIsingVerticalCoupling beta h n) *
        triangularIsingSymbol (beta / (4 * n))
          (quantumIsingVerticalCoupling beta h n) 0 (k + Real.pi) q =
      2 * (1 - (beta * h / (2 * n)) ^ 2) *
        (quantumIsingTrotterReducedParameter beta h n k - Real.cos q) := by
  let x := beta * h / (2 * n)
  have hJ : 2 * quantumIsingVerticalCoupling beta h n = -Real.log x := by
    unfold quantumIsingVerticalCoupling
    dsimp only [x]
    ring
  have hexp : Real.exp (-2 * quantumIsingVerticalCoupling beta h n) = x := by
    rw [show -2 * quantumIsingVerticalCoupling beta h n =
      -(2 * quantumIsingVerticalCoupling beta h n) by ring,
      hJ, neg_neg, Real.exp_log hx]
  have hsinh : Real.sinh (2 * quantumIsingVerticalCoupling beta h n) =
      (1 - x ^ 2) / (2 * x) := by
    rw [hJ]
    exact quantumIsing_sinh_neg_log hx
  have hsinh0 : Real.sinh (2 * quantumIsingVerticalCoupling beta h n) ≠ 0 := by
    rw [hsinh]
    have hxSq : x ^ 2 < 1 := by nlinarith
    positivity
  have hreduced := triangularIsingTrotterSymbol_reduced beta h n k q hx hx1
  have hsymbol :
      triangularIsingSymbol (beta / (4 * n))
          (quantumIsingVerticalCoupling beta h n) 0 (k + Real.pi) q =
        Real.sinh (2 * quantumIsingVerticalCoupling beta h n) *
          (quantumIsingTrotterReducedParameter beta h n k - Real.cos q) := by
    simpa [mul_comm] using (div_eq_iff hsinh0).mp hreduced
  rw [hsymbol, hexp, hsinh]
  change 4 * x * ((1 - x ^ 2) / (2 * x) *
      (quantumIsingTrotterReducedParameter beta h n k - Real.cos q)) =
    2 * (1 - x ^ 2) *
      (quantumIsingTrotterReducedParameter beta h n k - Real.cos q)
  have hx0 : x ≠ 0 := hx.ne'
  field_simp [hx0] <;> ring



noncomputable def quantumIsingNormalizedSpinSector
    (beta h : Real) (L : Nat) [Fact (2 < L)] (a b : Fin 2) : Complex :=
  ((2 * Real.exp (-quantumIsingVerticalCoupling beta h L) *
      (Real.cosh (beta / (4 * L)) *
        Real.cosh (quantumIsingVerticalCoupling beta h L))) ^ (L * L) : Real) *
    ons_weightedSpinCharacterSum L
      (anisotropicSquareEdgeWeight L
        (Real.tanh (beta / (4 * L)))
        (Real.tanh (quantumIsingVerticalCoupling beta h L))) a b



theorem two_mul_quantumIsingNormalizedClassicalPartition_eq_sectors
    (beta h : Real) (L : Nat) [Fact (2 < L)] :
    (2 : Complex) *
        (Real.exp (-quantumIsingVerticalCoupling beta h L) ^ (L * L) *
          quantumIsingClassicalCylinderPartition beta h L L : Real) =
      quantumIsingNormalizedSpinSector beta h L 1 1 +
        quantumIsingNormalizedSpinSector beta h L 0 1 +
        quantumIsingNormalizedSpinSector beta h L 1 0 -
        quantumIsingNormalizedSpinSector beta h L 0 0 := by
  let E : Real := Real.exp (-quantumIsingVerticalCoupling beta h L)
  let C : Real := Real.cosh (beta / (4 * L)) *
    Real.cosh (quantumIsingVerticalCoupling beta h L)
  let P : Real := (2 : Real) ^ (L * L) * C ^ (L * L)
  let spinSum : Complex :=
    ons_weightedSpinCharacterSum L
        (anisotropicSquareEdgeWeight L
          (Real.tanh (beta / (4 * L)))
          (Real.tanh (quantumIsingVerticalCoupling beta h L))) 1 1 +
      ons_weightedSpinCharacterSum L
        (anisotropicSquareEdgeWeight L
          (Real.tanh (beta / (4 * L)))
          (Real.tanh (quantumIsingVerticalCoupling beta h L))) 0 1 +
      ons_weightedSpinCharacterSum L
        (anisotropicSquareEdgeWeight L
          (Real.tanh (beta / (4 * L)))
          (Real.tanh (quantumIsingVerticalCoupling beta h L))) 1 0 -
      ons_weightedSpinCharacterSum L
        (anisotropicSquareEdgeWeight L
          (Real.tanh (beta / (4 * L)))
          (Real.tanh (quantumIsingVerticalCoupling beta h L))) 0 0
  have harf : (2 : Complex) *
        quantumIsingClassicalCylinderPartition beta h L L =
      (P : Complex) * spinSum := by
    exact two_mul_quantumIsingClassicalCylinderPartition_eq_spin beta h L
  have hcoefficient : ((E ^ (L * L) : Real) : Complex) * (P : Complex) =
      (((2 * E * C) ^ (L * L) : Real) : Complex) := by
    dsimp only [P]
    push_cast
    rw [mul_pow, mul_pow]
    ring
  calc
    (2 : Complex) * ((E ^ (L * L) *
        quantumIsingClassicalCylinderPartition beta h L L : Real) : Complex) =
        (2 : Complex) *
        (((E ^ (L * L) : Real) : Complex) *
          quantumIsingClassicalCylinderPartition beta h L L) := by
      norm_cast
    _ =
        ((E ^ (L * L) : Real) : Complex) *
          ((2 : Complex) *
            quantumIsingClassicalCylinderPartition beta h L L) := by ring
    _ = ((E ^ (L * L) : Real) : Complex) *
        ((P : Complex) * spinSum) := by rw [harf]
    _ = (((2 * E * C) ^ (L * L) : Real) : Complex) * spinSum := by
      rw [← mul_assoc, hcoefficient]
    _ = _ := by
      unfold quantumIsingNormalizedSpinSector
      dsimp only [E, C, spinSum]
      ring


theorem quantumIsingNormalizedSpinSector_sq_eq_symbolProduct
    (beta h : Real) (L : Nat) [Fact (2 < L)] (a b : Fin 2) :
    quantumIsingNormalizedSpinSector beta h L a b ^ 2 =
      ∏ j : ZMod L × ZMod L,
        (4 * Real.exp (-2 * quantumIsingVerticalCoupling beta h L) *
          triangularIsingSymbol (beta / (4 * L))
            (quantumIsingVerticalCoupling beta h L) 0
            (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
            (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) : Complex) := by
  let C : Real := Real.cosh (beta / (4 * L)) *
    Real.cosh (quantumIsingVerticalCoupling beta h L)
  let e : Real := 2 * Real.exp (-quantumIsingVerticalCoupling beta h L)
  let W : Complex := ons_weightedSpinCharacterSum L
    (anisotropicSquareEdgeWeight L
      (Real.tanh (beta / (4 * L)))
      (Real.tanh (quantumIsingVerticalCoupling beta h L))) a b
  have hnormalized : (((C ^ (L * L) : Real) : Complex) * W) ^ 2 =
      ∏ j : ZMod L × ZMod L,
        (triangularIsingSymbol (beta / (4 * L))
          (quantumIsingVerticalCoupling beta h L) 0
          (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
          (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) : Complex) :=
    anisotropicSquare_normalizedSpin_tanh_sq_eq_triangularProduct L
      (beta / (4 * L)) (quantumIsingVerticalCoupling beta h L) a b
  unfold quantumIsingNormalizedSpinSector
  change ((((e * C) ^ (L * L) : Real) : Complex) * W) ^ 2 = _
  have hsplit : (((e * C) ^ (L * L) : Real) : Complex) =
      ((e ^ (L * L) : Real) : Complex) *
        ((C ^ (L * L) : Real) : Complex) := by
    rw [mul_pow]
    push_cast
    ring
  rw [hsplit, show
      (((e ^ (L * L) : Real) : Complex) *
          ((C ^ (L * L) : Real) : Complex) * W) ^ 2 =
        (((e ^ (L * L) : Real) : Complex) ^ 2) *
          ((((C ^ (L * L) : Real) : Complex) * W) ^ 2) by ring,
    hnormalized]
  have he2Real : (4 * Real.exp (-2 * quantumIsingVerticalCoupling beta h L) :
      Real) = e ^ 2 := by
    dsimp only [e]
    calc
      4 * Real.exp (-2 * quantumIsingVerticalCoupling beta h L) =
          4 * Real.exp
            (-quantumIsingVerticalCoupling beta h L +
              -quantumIsingVerticalCoupling beta h L) := by
        congr 2
        ring
      _ = 4 * (Real.exp (-quantumIsingVerticalCoupling beta h L) *
          Real.exp (-quantumIsingVerticalCoupling beta h L)) := by
        rw [Real.exp_add]
      _ = (2 * Real.exp (-quantumIsingVerticalCoupling beta h L)) ^ 2 := by
        ring
  have he2 : (4 : Complex) *
      (Real.exp (-2 * quantumIsingVerticalCoupling beta h L) : Complex) =
      (e : Complex) ^ 2 := by
    norm_cast
    convert he2Real using 1 <;> norm_num
  simp_rw [he2]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_prod, ZMod.card]
  push_cast
  have hpow : ((e : Complex) ^ (L * L)) ^ 2 =
      ((e : Complex) ^ 2) ^ (L * L) := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  rw [hpow]



theorem quantumIsingNormalizedSpinSector_sq_eq_reducedProduct
    (beta h : Real) (L : Nat) [Fact (2 < L)] (a b : Fin 2)
    (hx : 0 < beta * h / (2 * L))
    (hx1 : beta * h / (2 * L) < 1) :
    quantumIsingNormalizedSpinSector beta h L a b ^ 2 =
      ∏ j : ZMod L × ZMod L,
        (2 * (1 - (beta * h / (2 * L)) ^ 2) *
          (quantumIsingTrotterReducedParameter beta h L
              (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L - Real.pi) -
            Real.cos
              (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L)) : Complex) := by
  rw [quantumIsingNormalizedSpinSector_sq_eq_symbolProduct]
  apply Finset.prod_congr rfl
  intro j _
  have hcast := congrArg (fun r : Real ↦ (r : Complex)) (by
    simpa only [sub_add_cancel] using
      quantumIsingVerticalNormalization_mul_symbol_eq_reduced beta h L
      (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L - Real.pi)
      (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) hx hx1)
  push_cast at hcast ⊢
  exact hcast

end StatMech.FrontierA
