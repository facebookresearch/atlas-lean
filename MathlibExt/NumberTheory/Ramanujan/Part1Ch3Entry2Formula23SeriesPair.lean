/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.Ramanujan.Part1Ch3Entry2
import MathlibExt.NumberTheory.Ramanujan.Part1Ch3Entry2Rightsummable

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 2, formula (2.3)

∑ x^(j+1)/((z+1)⋯(z+j+1)) is eˣ times an alternating factorial series.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry2Formula23SeriesPair

/-- Pole-avoidance for the Entry 2 API instantiated at `(z + 1)`. -/
private lemma hzE (z : ℂ) (hz : ∀ n : ℕ, z ≠ -((n : ℂ) + 1)) (r : ℕ) :
    (z + 1 + (r : ℂ)) ≠ 0 := by
  intro h
  apply hz r
  linear_combination h

/-- **Ramanujan's companion series transformation (Chapter 3, Entry 2, formula (2.3)).** Let $x$
and $z$ be complex numbers with $z \ne -(n+1)$ for every natural number $n$. Then the series
$\sum_{j \ge 0} \frac{(-1)^j x^{j+1}}{(z+j+1)\, j!}$ converges absolutely, say with sum $S$, and
the series $\sum_{j \ge 0} \frac{x^{j+1}}{(z+1)(z+2)\cdots(z+j+1)}$ converges absolutely with sum
$e^x S$.

The identity follows from Entry 2 applied with $-x$ and $z + 1$ in place of $x$ and $z$, using
$e^x e^{-x} = 1$.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 2, formula (2.3) and
    Corollary 2, printed pp. 46--47 / PDF pp. 56--57.
Proves `Wanted` entry `ramanujan_part1_ch3_entry2_formula23_series_pair`. -/
theorem ramanujan_part1_ch3_entry2_formula23_series_pair
    (x z : ℂ) (hz : ∀ n : ℕ, z ≠ -((n : ℂ) + 1)) :
    HasSum (fun j : ℕ => (x ^ (j + 1) / ∏ i ∈ Finset.range (j + 1), (z + ((i : ℂ) + 1)),
      (-1 : ℂ) ^ j * x ^ (j + 1) / ((z + ((j : ℂ) + 1)) * ((Nat.factorial j : ℕ) : ℂ))))
      (Complex.exp x * ∑' j : ℕ,
          ((-1 : ℂ) ^ j * x ^ (j + 1) / ((z + ((j : ℂ) + 1)) * ((Nat.factorial j : ℕ) : ℂ))),
       ∑' j : ℕ, ((-1 : ℂ) ^ j * x ^ (j + 1) / ((z + ((j : ℂ) + 1)) * ((Nat.factorial j : ℕ) : ℂ)))) := by
  have hE := Entry2.ramanujan_part1_ch3_entry2 (-x) (z + 1) (hzE z hz)
  have hR := Entry2Rightsummable.ramanujan_part1_ch3_entry2_rightsummable (-x) (z + 1) (hzE z hz)
  -- Entry 2 left summand at `(-x, z+1)` is the negation of our right summand.
  have hBE : ∀ j : ℕ, (((-1 : ℂ) ^ j * x ^ (j + 1)) /
      ((z + ((j : ℂ) + 1)) * ((Nat.factorial j : ℕ) : ℂ)))
      = -(((-x) ^ (j + 1)) / ((z + 1 + (j : ℂ)) * (Nat.factorial j : ℂ))) := by
    intro j
    have h1 : (-x : ℂ) ^ (j + 1) = -(((-1 : ℂ) ^ j) * x ^ (j + 1)) := by
      rw [show (-x : ℂ) = (-1) * x from by ring, mul_pow, pow_succ]
      ring
    have h2 : (z + 1 + (j : ℂ)) = (z + ((j : ℂ) + 1)) := by ring
    rw [h1, h2]
    ring
  -- Entry 2 right summand at `(-x, z+1)` is the negation of our left summand.
  have h21 : ∀ j : ℕ, (-1 : ℂ) ^ (2 * j + 1) = -1 := by
    intro j
    rw [pow_succ]
    have hsq : (-1 : ℂ) ^ (2 * j) = 1 := by
      rw [show 2 * j = j + j from by ring, pow_add, ← mul_pow,
        show ((-1 : ℂ) * (-1)) = 1 from by ring, one_pow]
    rw [hsq, one_mul]
  have hCE : ∀ j : ℕ, (x ^ (j + 1) /
      ∏ i ∈ Finset.range (j + 1), (z + ((i : ℂ) + 1)))
      = -(((-1 : ℂ) ^ j * (-x) ^ (j + 1)) /
        ∏ k ∈ Finset.range (j + 1), (z + 1 + (k : ℂ))) := by
    intro j
    have h1 : (-1 : ℂ) ^ j * (-x) ^ (j + 1) = -(x ^ (j + 1)) := by
      rw [show (-x : ℂ) = (-1) * x from by ring, mul_pow, ← mul_assoc, ← pow_add,
        show j + (j + 1) = 2 * j + 1 from by ring, h21 j]
      ring
    have hP : (∏ k ∈ Finset.range (j + 1), (z + 1 + (k : ℂ)))
        = ∏ i ∈ Finset.range (j + 1), (z + ((i : ℂ) + 1)) :=
      Finset.prod_congr rfl (fun i _ => by ring)
    rw [h1, hP]
    ring
  have hBright : HasSum (fun j : ℕ => (-1 : ℂ) ^ j * x ^ (j + 1) /
      ((z + ((j : ℂ) + 1)) * ((Nat.factorial j : ℕ) : ℂ)))
      (-(Complex.exp (-x) * ∑' j : ℕ, ((-1 : ℂ) ^ j * (-x) ^ (j + 1) /
        ∏ k ∈ Finset.range (j + 1), (z + 1 + (k : ℂ))))) :=
    hE.neg.congr_fun (fun j => hBE j)
  have hB := hBright.summable
  have hBsum := hB.hasSum
  have hS : (∑' j : ℕ, ((-1 : ℂ) ^ j * x ^ (j + 1) /
      ((z + ((j : ℂ) + 1)) * ((Nat.factorial j : ℕ) : ℂ))))
      = -(Complex.exp (-x) * ∑' j : ℕ, ((-1 : ℂ) ^ j * (-x) ^ (j + 1) /
        ∏ k ∈ Finset.range (j + 1), (z + 1 + (k : ℂ)))) :=
    hBsum.unique hBright
  have hCneg : HasSum (fun j : ℕ => x ^ (j + 1) /
      ∏ i ∈ Finset.range (j + 1), (z + ((i : ℂ) + 1)))
      (-∑' j : ℕ, ((-1 : ℂ) ^ j * (-x) ^ (j + 1) /
        ∏ k ∈ Finset.range (j + 1), (z + 1 + (k : ℂ)))) :=
    hR.hasSum.neg.congr_fun (fun j => hCE j)
  have hC := hCneg.summable
  have hT : (∑' j : ℕ, x ^ (j + 1) /
      ∏ i ∈ Finset.range (j + 1), (z + ((i : ℂ) + 1)))
      = -∑' j : ℕ, ((-1 : ℂ) ^ j * (-x) ^ (j + 1) /
        ∏ k ∈ Finset.range (j + 1), (z + 1 + (k : ℂ))) :=
    hC.hasSum.unique hCneg
  have hexp : Complex.exp x * Complex.exp (-x) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hval : Complex.exp x * (∑' j : ℕ, ((-1 : ℂ) ^ j * x ^ (j + 1) /
      ((z + ((j : ℂ) + 1)) * ((Nat.factorial j : ℕ) : ℂ))))
      = ∑' j : ℕ, x ^ (j + 1) / ∏ i ∈ Finset.range (j + 1), (z + ((i : ℂ) + 1)) := by
    rw [hS, hT, mul_neg, ← mul_assoc, hexp, one_mul]
  have hCsum : HasSum (fun j : ℕ => x ^ (j + 1) /
      ∏ i ∈ Finset.range (j + 1), (z + ((i : ℂ) + 1)))
      (Complex.exp x * ∑' j : ℕ, ((-1 : ℂ) ^ j * x ^ (j + 1) /
        ((z + ((j : ℂ) + 1)) * ((Nat.factorial j : ℕ) : ℂ)))) := by
    rw [hval]
    exact hC.hasSum
  exact HasSum.prodMk hCsum hBsum

end Entry2Formula23SeriesPair

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
