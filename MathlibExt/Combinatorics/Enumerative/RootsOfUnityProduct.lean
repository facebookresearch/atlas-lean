/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Roots-of-unity products of integer polynomials

The product of the rotations of an integer polynomial by the `k`th roots of unity is an
integer polynomial in `X ^ k`. Resultants over `ℤ[X]` give both this polynomial and the
product with the trivial rotation omitted.
-/

namespace MetaMathlibExt

open Polynomial

namespace rootsOfUnity_product_mul_eq_comp_pow

/-- Specializing a resultant at a split monic polynomial gives a product of evaluations. -/
private theorem map_resultant (f : ℤ[X]) (p : ℤ[X][X]) (φ : ℤ[X] →+* ℂ[X])
    (s : Finset ℕ) (a : ℕ → ℂ[X]) (hp : p.map φ = ∏ j ∈ s, (X - C (a j))) :
    φ (p.resultant (f.map C) s.card f.natDegree) =
      ∏ j ∈ s, (f.map (Int.castRingHom ℂ)).comp (a j) := by
  let g := (f.map (Int.castRingHom ℂ)).map (C : ℂ →+* ℂ[X])
  have hmap : (f.map C).map φ = g := by
    dsimp only [g]
    rw [map_map, map_map, Subsingleton.elim (φ.comp C) (C.comp (Int.castRingHom ℂ))]
  have hg : g.natDegree ≤ f.natDegree := natDegree_map_le.trans natDegree_map_le
  have hd : (∏ j ∈ s, (X - C (a j))).natDegree = s.card := by
    simp [natDegree_prod_of_monic _ _ (fun j _ ↦ monic_X_sub_C (a j))]
  rw [← resultant_map_map, hp, hmap, ← hd, resultant_prod_left _ _ _ _ (by simp) hg]
  simp only [natDegree_X_sub_C, resultant_X_sub_C_left _ _ _ hg, g, eval_map]
  rfl

end rootsOfUnity_product_mul_eq_comp_pow

/-- **Roots-of-unity products of integer polynomials.** Let $f \in \mathbb{Z}[x]$ have degree
$r$, let $k > 0$ be a natural number and let $\omega = e^{2\pi i/k}$. Then there are
$G, T \in \mathbb{Z}[x]$ such that $G(x) = f(\omega x) f(\omega^2 x) \cdots f(\omega^{k-1} x)$
as polynomials over $\mathbb{C}$, $T$ has degree $r$, and $f(x) G(x) = T(x^k)$.

Source: Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial Coefficients and
Some Generalizations*, Journal of Integer Sequences 27 (2024), Article 24.3.4, Proposition 2. -/
public theorem rootsOfUnity_product_mul_eq_comp_pow (f : ℤ[X]) (r k : ℕ) (hk : 0 < k)
    (hf : f.degree = r) :
    ∃ G T : ℤ[X],
      G.map (Int.castRingHom ℂ) =
        ∏ j ∈ Finset.Ico 1 k,
          (f.map (Int.castRingHom ℂ)).comp
            (C (Complex.exp (2 * Real.pi * Complex.I / k) ^ j) * X) ∧
      T.natDegree = r ∧ f * G = T.comp (X ^ k) := by
  classical
  let ζ := Complex.exp (2 * Real.pi * Complex.I / k)
  have hζ : IsPrimitiveRoot ζ k := Complex.isPrimitiveRoot_exp k hk.ne'
  let a (j : ℕ) : ℂ[X] := C (ζ ^ j) * X
  let F (j : ℕ) := (f.map (Int.castRingHom ℂ)).comp (a j)
  have hsplit : (X ^ k - C (X ^ k) : ℂ[X][X]) =
      ∏ j ∈ Finset.range k, (X - C (a j)) := by
    simpa only [a, map_pow] using
      X_pow_sub_C_eq_prod (hζ.map_of_injective (f := C) C_injective) hk
        (rfl : X ^ k = (X : ℂ[X]) ^ k)
  let φ := mapRingHom (Int.castRingHom ℂ)
  let T := (X ^ k - C X : ℤ[X][X]).resultant (f.map C) k f.natDegree
  have hT : φ (T.comp (X ^ k)) = ∏ j ∈ Finset.range k, F j := by
    have hp : (X ^ k - C X : ℤ[X][X]).map (φ.comp (compRingHom (X ^ k))) =
        ∏ j ∈ Finset.range k, (X - C (a j)) := by simpa [φ] using hsplit
    simpa only [Finset.card_range, RingHom.comp_apply, coe_compRingHom_apply] using
      rootsOfUnity_product_mul_eq_comp_pow.map_resultant f _ _ _ _ hp
  let q := (X ^ k - C (X ^ k) : ℤ[X][X]) /ₘ (X - C X)
  let G := q.resultant (f.map C) (Finset.Ico 1 k).card f.natDegree
  have hG : φ G = ∏ j ∈ Finset.Ico 1 k, F j := by
    apply rootsOfUnity_product_mul_eq_comp_pow.map_resultant
    rw [show q.map φ = (X ^ k - C (X ^ k) : ℂ[X][X]) /ₘ (X - C X) by
      simp [q, map_divByMonic φ (monic_X_sub_C _), φ]]
    rw [hsplit, Finset.prod_range_eq_mul_Ico _ hk]
    simp only [a, pow_zero, map_one, one_mul, mul_divByMonic_cancel_left _ (monic_X_sub_C _)]
  have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  refine ⟨G, T, hG, ?_, ?_⟩
  · have hdeg (j : ℕ) : (F j).degree = r := by
      have hlinear : (a j).degree = 1 := degree_C_mul_X (pow_ne_zero _ (Complex.exp_ne_zero _))
      dsimp only [F]
      rw [degree_comp (by rw [hlinear]; decide), hlinear, mul_one,
        degree_map_eq_of_injective hinj, hf]
    have hn (j : ℕ) : F j ≠ 0 := by
      intro he
      simpa [he] using hdeg j
    have hd := congrArg natDegree hT
    rw [show (φ (T.comp (X ^ k))).natDegree = T.natDegree * k by
      simp [φ, natDegree_map_eq_of_injective hinj, natDegree_comp],
      natDegree_prod _ _ (fun j _ ↦ hn j)] at hd
    simp only [fun j ↦ natDegree_eq_of_degree_eq_some (hdeg j), Finset.sum_const,
      Finset.card_range, smul_eq_mul] at hd
    exact Nat.eq_of_mul_eq_mul_right hk (hd.trans (Nat.mul_comm k r))
  · apply map_injective (Int.castRingHom ℂ) hinj
    change φ (f * G) = φ (T.comp (X ^ k))
    rw [map_mul, hT, hG, Finset.prod_range_eq_mul_Ico _ hk]
    simp [F, a, φ]

end MetaMathlibExt
