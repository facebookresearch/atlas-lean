/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.TriangularIsingTorusSectors
import Code.FrontierA.KacWardPolygonGlobalReduction





open scoped BigOperators

namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager

def triangularTorusVerticalEdge (L : Nat)
    (edge : Sym2 (ZMod L × ZMod L)) : Prop :=
  ∃ p : ZMod L × ZMod L, edge = s(p, (p.1, p.2 + 1))

noncomputable instance triangularTorusVerticalEdge_decidable
    (L : Nat) (edge : Sym2 (ZMod L × ZMod L)) :
    Decidable (triangularTorusVerticalEdge L edge) := Classical.dec _



noncomputable def triangularTorusEdgeWeight
    (L : Nat) (t1 t2 t3 : Complex) :
    Sym2 (ZMod L × ZMod L) → Complex :=
  fun edge =>
    if squareTorusHorizontalEdge L edge then t1
    else if triangularTorusVerticalEdge L edge then t2
    else t3

noncomputable def triangularTorusSpinScalePolynomial
    (L : Nat) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → Complex)
    (a b : Fin 2) : Polynomial Complex :=
  ∑ F ∈ evenSubgraphs (triangularTorusGraph L),
    Polynomial.monomial F.card
      ((ons_spinCharacter a b
        (triangularTorusEvenHomology L F) : Complex) *
        ∏ edge ∈ F, weight edge)

theorem triangularTorusSpinScalePolynomial_eval
    (L : Nat) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → Complex)
    (a b : Fin 2) (t : Complex) :
    (triangularTorusSpinScalePolynomial L weight a b).eval t =
      triangularTorusWeightedSpinCharacterSum L
        (fun edge => t * weight edge) a b := by
  classical
  unfold triangularTorusSpinScalePolynomial
    triangularTorusWeightedSpinCharacterSum
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro F hF
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  ring

theorem triangularTorusEdgeWeight_scale
    (L : Nat) (t1 t2 t3 s : Complex) :
    (fun edge => s * triangularTorusEdgeWeight L t1 t2 t3 edge) =
      triangularTorusEdgeWeight L (s * t1) (s * t2) (s * t3) := by
  funext edge
  by_cases hhorizontal : squareTorusHorizontalEdge L edge
  · simp [triangularTorusEdgeWeight, hhorizontal]
  · by_cases hvertical : triangularTorusVerticalEdge L edge
    · simp [triangularTorusEdgeWeight, hhorizontal, hvertical]
    · simp [triangularTorusEdgeWeight, hhorizontal, hvertical]

theorem triangularTorusKWMatrix_scale
    (L : Nat) (t1 t2 t3 rho u v s : Complex) :
    triangularTorusKWMatrix L (s * t1) (s * t2) (s * t3) rho u v =
      s • triangularTorusKWMatrix L t1 t2 t3 rho u v := by
  ext p q
  unfold triangularTorusKWMatrix ons_blockCirculant2D
    triangularTorusKWBlock triangularTorusDirectionWeight
  simp only [Matrix.smul_apply, smul_eq_mul]
  by_cases hstep :
      (p.1.1 - q.1.1, p.1.2 - q.1.2) =
        triangularTorusDirectionStep L p.2
  · rw [if_pos hstep, if_pos hstep]
    generalize ha : p.2 = a at *
    fin_cases a <;> simp <;> ring
  · rw [if_neg hstep, if_neg hstep]
    ring





theorem triangularTorus_sector_sq_eq_det_of_interval
    (L : Nat) [Fact (2 < L)]
    (t1 t2 t3 rho u v : Complex) (a b : Fin 2)
    (hinterval : ∃ delta : Real, 0 < delta ∧
      ∀ r : Real, r ∈ Set.Ioo 0 delta →
        triangularTorusWeightedSpinCharacterSum L
            (triangularTorusEdgeWeight L
              ((r : Complex) * t1) ((r : Complex) * t2)
                ((r : Complex) * t3)) a b ^ 2 =
          (1 - triangularTorusKWMatrix L
            ((r : Complex) * t1) ((r : Complex) * t2)
              ((r : Complex) * t3) rho u v).det) :
    triangularTorusWeightedSpinCharacterSum L
        (triangularTorusEdgeWeight L t1 t2 t3) a b ^ 2 =
      (1 - triangularTorusKWMatrix L t1 t2 t3 rho u v).det := by
  let M := triangularTorusKWMatrix L t1 t2 t3 rho u v
  let P := kwDetScalePolynomial M
  let Q :=
    (triangularTorusSpinScalePolynomial L
      (triangularTorusEdgeWeight L t1 t2 t3) a b) ^ 2
  obtain ⟨delta, hdelta, hsmall⟩ := hinterval
  have heval (r : Real) (hr : r ∈ Set.Ioo (0 : Real) delta) :
      P.eval (r : Complex) = Q.eval (r : Complex) := by
    dsimp only [P, Q]
    rw [kwDetScalePolynomial_eval, Polynomial.eval_pow,
      triangularTorusSpinScalePolynomial_eval,
      triangularTorusEdgeWeight_scale]
    rw [← triangularTorusKWMatrix_scale]
    exact (hsmall r hr).symm
  have hinfinite : Set.Infinite {z : Complex | P.eval z = Q.eval z} := by
    have hreal : Set.Infinite (Set.Ioo (0 : Real) delta) :=
      Set.Ioo_infinite hdelta
    have himage : Set.Infinite
        ((fun r : Real => (r : Complex)) '' Set.Ioo (0 : Real) delta) :=
      hreal.image Complex.ofReal_injective.injOn
    apply himage.mono
    rintro z ⟨r, hr, rfl⟩
    exact heval r hr
  have hpoly : P = Q := Polynomial.eq_of_infinite_eval_eq P Q hinfinite
  have hone := congrArg (Polynomial.eval (1 : Complex)) hpoly
  dsimp only [P, Q] at hone
  rw [kwDetScalePolynomial_eval, Polynomial.eval_pow,
    triangularTorusSpinScalePolynomial_eval] at hone
  simpa [M] using hone.symm

end StatMech.FrontierA
