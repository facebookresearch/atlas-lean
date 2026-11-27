/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Binomial
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The Alzer–Richards reciprocal-sum identity

Lagrange interpolation at consecutive integers expresses the difference between
the derivative of a power and its product with a reciprocal sum in terms of
generalized binomial coefficients.
-/

namespace MetaMathlibExt

open Finset Polynomial Lagrange

namespace mul_pow_pred_sub_pow_mul_sum_inv_eq_sum_choose

-- Omitting node k splits the nodal product into two falling factorials.
private lemma prod_erase_node (k m : ℕ) (w : ℂ) :
    ∏ j ∈ (range (k + 1 + m)).erase k, (w - j) =
      (descPochhammer ℂ k).eval w * (descPochhammer ℂ m).eval (w - k - 1) := by
  induction m with
  | zero => simp [range_add_one, descPochhammer_eval_eq_prod_range]
  | succ m ih =>
    rw [Nat.add_succ, range_add_one, erase_insert_of_ne (by omega),
      prod_insert (by simp), ih, descPochhammer_succ_eval]
    push_cast
    ring

private lemma eval_falling (w : ℂ) (n : ℕ) :
    (descPochhammer ℂ n).eval w = n.factorial * Ring.choose w n := by
  rw [← nsmul_eq_mul, ← Ring.descPochhammer_eq_factorial_smul_choose,
    descPochhammer_smeval_eq_ascPochhammer, ascPochhammer_smeval_eq_eval,
    descPochhammer_eval_eq_ascPochhammer]

private lemma eval_basis_range {p k : ℕ} (hk : k < p) (z : ℂ) :
    (Lagrange.basis (range p) (Nat.cast : ℕ → ℂ) k).eval z =
      (-1 : ℂ) ^ (p - k - 1) * Ring.choose z k * Ring.choose (z - k - 1) (p - k - 1) := by
  let m := p - k - 1
  have hp : p = k + 1 + m := by
    dsimp [m]
    omega
  change _ = (-1 : ℂ) ^ m * Ring.choose z k * Ring.choose (z - k - 1) m
  simp only [Lagrange.basis, basisDivisor, eval_prod, eval_mul, eval_C, eval_sub, eval_X,
    prod_mul_distrib, prod_inv_distrib]
  rw [hp, prod_erase_node, prod_erase_node]
  simp only [eval_falling, sub_self, zero_sub, Ring.choose_natCast, Nat.choose_self, Nat.cast_one,
    mul_one, Ring.choose_neg, add_sub_cancel_left, Units.smul_def, zsmul_eq_mul,
    Int.cast_negOnePow_natCast, mul_inv_rev, ← inv_pow, inv_neg, inv_one]
  have hkf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hmf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  field_simp

-- Away from the nodes, each term of the derivative omits exactly one nonzero factor.
private lemma eval_derivative_nodal {p : ℕ} {z : ℂ} (hz : ∀ k < p, z ≠ k) :
    (nodal (range p) (Nat.cast : ℕ → ℂ)).derivative.eval z =
      (nodal (range p) Nat.cast).eval z * ∑ k ∈ range p, 1 / (z - k) := by
  rw [derivative_nodal, eval_finsetSum, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [nodal_eq_mul_nodal_erase hi, eval_mul, eval_sub, eval_X, eval_C]
  field_simp [sub_ne_zero.mpr (hz i (mem_range.mp hi))]

end mul_pow_pred_sub_pow_mul_sum_inv_eq_sum_choose

open mul_pow_pred_sub_pow_mul_sum_inv_eq_sum_choose in
/-- **A reciprocal-sum identity for generalized binomial coefficients.** For a complex number $w$
and a natural number $j$ write $\binom{w}{j} = w(w-1)\cdots(w-j+1)/j!$. Let $p \ge 1$ be a
natural number and let $z$ be a complex number with $z \ne k$ for every natural number $k < p$.
Then
$$
p z^{p-1} - z^p \sum_{k=0}^{p-1} \frac{1}{z-k} =
\sum_{k=0}^{p-1} \frac{(-1)^{p-k} k^p}{z-k} \binom{z}{k} \binom{z-k-1}{p-k-1}.
$$

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Corollary 1, Equation (10). -/
public theorem mul_pow_pred_sub_pow_mul_sum_inv_eq_sum_choose {p : ℕ} (hp : 1 ≤ p) {z : ℂ}
    (hz : ∀ k < p, z ≠ k) :
    p * z ^ (p - 1) - z ^ p * ∑ k ∈ range p, 1 / (z - k) =
      ∑ k ∈ range p, (-1 : ℂ) ^ (p - k) * (k : ℂ) ^ p / (z - k) * Ring.choose z k *
        Ring.choose (z - k - 1) (p - k - 1) := by
  let N := nodal (range p) (Nat.cast : ℕ → ℂ)
  have hN : N.eval z ≠ 0 := eval_nodal_not_at_node fun k hk => hz k (mem_range.mp hk)
  -- Subtract a multiple of the nodal polynomial so that the result vanishes at z.
  let F := X ^ p - C (z ^ p / N.eval z) * N
  let Q := F /ₘ (X - C z)
  have hfactor : (X - C z) * Q = F := by
    apply mul_divByMonic_eq_iff_isRoot.mpr
    simp [IsRoot, F, hN]
  have hdeg : F.natDegree ≤ p := by
    apply (natDegree_sub_le _ _).trans (max_le (natDegree_X_pow_le _) _)
    exact (natDegree_C_mul_le _ _).trans (by simp [N, natDegree_nodal])
  have hQdeg : Q.natDegree < p := by
    rw [natDegree_divByMonic _ (monic_X_sub_C _), natDegree_X_sub_C]
    omega
  have hQ : Q.degree < ↑(range p).card := by
    rw [card_range]
    exact degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hQdeg)
  have hinterp := eq_interpolate_of_eval_eq (fun k : ℕ => (k : ℂ) ^ p / (k - z))
    Nat.cast_injective.injOn hQ (by
      intro k hk
      apply (eq_div_iff (sub_ne_zero.mpr (hz k (mem_range.mp hk)).symm)).mpr
      simpa [F, N, eval_nodal_at_node hk, mul_comm] using congrArg (eval (k : ℂ)) hfactor)
  -- At z the product rule leaves only Q(z).
  calc
    _ = Q.eval z := by
      have hderiv : N.derivative.eval z = N.eval z * ∑ k ∈ range p, 1 / (z - k) :=
        eval_derivative_nodal hz
      simpa [F, derivative_X_pow, hderiv, ← mul_assoc, hN] using
        (congrArg (fun P : ℂ[X] => P.derivative.eval z) hfactor).symm
    _ = _ := by
      rw [hinterp, interpolate_apply, eval_finsetSum]
      refine sum_congr rfl fun k hk => ?_
      have hkp := mem_range.mp hk
      have hsign : (-1 : ℂ) ^ (p - k) = (-1) ^ (p - k - 1) * (-1) := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p - k)]
      rw [eval_mul, eval_C, eval_basis_range hkp, hsign, ← neg_sub z (k : ℂ), div_neg]
      ring

end MetaMathlibExt
