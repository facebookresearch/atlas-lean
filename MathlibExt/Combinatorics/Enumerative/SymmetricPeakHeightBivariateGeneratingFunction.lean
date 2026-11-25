/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Combinatorics.Enumerative.SymmetricPeaksCompositions
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-!
# Bivariate generating function of the total symmetric peak height over compositions

This file proves `MetaMathlibExt.symmetricPeakHeightSum_compositions_bivariate_genFun`: if
`hsp(n, k)` is the sum of the heights of the symmetric peaks over all compositions of `n` with
`k` parts, then `∑ₙ ∑ₖ hsp(n, k) yᵏ xⁿ = y³ x⁴ / ((1 - x³)(1 - x - y x)²)` in the ring of power
series in `x` over `ℤ[y]`. The theorem's docstring cites the journal version of Walaa Asakly and
Noor Kezil's paper (INTEGERS 26 (2026), Article A65), Lemma 1; in its preprint
arXiv:2408.09166v1 the identity is equation (6) of Lemma 2.

The proof refines the one of `MetaMathlibExt.symmetricPeakHeightSum_compositions_genFun` by a
weight `y` on every part, over an arbitrary commutative ring. Writing `C(x)` for the generating
function of all compositions weighted by `y ^ (number of parts)`, a composition is empty or a
part followed by a composition, so `C = 1 + y x/(1 - x) · C`. The height sum of `a :: w` is the
height sum of `w` plus the height `b - a` of the symmetric peak `a b a` at the start, present
when `w` starts with `b a` and `b > a`. These words `w`, weighted by `b - a`, have generating
function `y² x^(2a) · x/(1 - x)² · C(x)`; summing `y xᵃ` times it over `a ≥ 1` gives the
relation `H = y x/(1 - x) · H + y³ x⁴/((1 - x³)(1 - x)²) · C` for the generating function `H` of
`hsp`, from which the identity follows by algebra in `R⟦X⟧`.
-/

open Finset PowerSeries

namespace MetaMathlibExt

namespace symmetricPeakHeightSum_compositions_bivariate_genFun

/-- A sum over the compositions of `0` is the value at the empty composition. -/
private theorem sum_zero {M : Type*} [AddCommMonoid M] (f : List ℕ → M) :
    ∑ c : Composition 0, f c.blocks = f [] := by
  simp [(Composition.blocks_eq_nil _).mpr rfl, composition_card]

/-- Remove the first part `a + 1` of a composition. -/
private def tailComp {m k : ℕ} (a : ℕ) (c : Composition m) (ha : c.blocks.headI = a + 1)
    (h : a + 1 + k = m) : Composition k where
  blocks := c.blocks.tail
  blocks_pos hi := c.blocks_pos (List.mem_of_mem_tail hi)
  blocks_sum := by
    have hs := c.blocks_sum
    cases hc : c.blocks with
    | nil => rw [hc] at ha; simp at ha
    | cons b t =>
      rw [hc] at ha hs
      simp only [List.headI_cons] at ha
      simp only [List.sum_cons] at hs
      simp only [List.tail_cons]
      omega

/-- Prepend the part `a + 1` to a composition. -/
private def consComp {m k : ℕ} (a : ℕ) (c : Composition m) (h : a + 1 + m = k) :
    Composition k where
  blocks := (a + 1) :: c.blocks
  blocks_pos hi := by
    rcases List.mem_cons.mp hi with rfl | hi
    · exact Nat.succ_pos a
    · exact c.blocks_pos hi
  blocks_sum := by
    rw [List.sum_cons, c.blocks_sum, h]

/-- A composition of `n + 1` has a first part. -/
private theorem exists_blocks_eq_cons {n : ℕ} (c : Composition (n + 1)) :
    ∃ a t, c.blocks = (a + 1) :: t ∧ a + 1 + t.sum = n + 1 := by
  have hs := c.blocks_sum
  rcases hc : c.blocks with _ | ⟨b, t⟩
  · rw [hc] at hs; simp at hs
  · have hb : 0 < b := c.blocks_pos (by rw [hc]; exact List.mem_cons_self)
    refine ⟨b - 1, t, by rw [Nat.sub_add_cancel hb], ?_⟩
    rw [hc, List.sum_cons] at hs
    omega

/-- A sum over the compositions of `n + 1`, split according to the first part `a + 1`. -/
private theorem sum_succ {M : Type*} [AddCommMonoid M] (n : ℕ) (f : List ℕ → M) :
    ∑ c : Composition (n + 1), f c.blocks =
      ∑ p ∈ antidiagonal n, ∑ c : Composition p.2, f ((p.1 + 1) :: c.blocks) := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun c : Composition (n + 1) => (c.blocks.headI - 1, n + 1 - c.blocks.headI))
    (t := antidiagonal n) (fun c _ => by
      obtain ⟨a, t, hc, hs⟩ := exists_blocks_eq_cons c
      simp only [mem_antidiagonal, hc, List.headI_cons]
      omega)]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p.1 + p.2 = n := mem_antidiagonal.mp hp
  refine Finset.sum_bij'
    (fun c hc => tailComp p.1 c (by
        obtain ⟨a, t, hct, hs⟩ := exists_blocks_eq_cons c
        simp only [mem_filter, mem_univ, true_and, hct, List.headI_cons, Prod.ext_iff] at hc ⊢
        omega) (by omega))
    (fun c _ => consComp p.1 c (by omega)) ?_ ?_ ?_ ?_ ?_
  · intro c _
    exact mem_univ _
  · intro c _
    simp only [mem_filter, mem_univ, true_and, consComp, List.headI_cons, Prod.ext_iff]
    omega
  · intro c hc
    obtain ⟨a, t, hct, hs⟩ := exists_blocks_eq_cons c
    simp only [mem_filter, mem_univ, true_and, hct, List.headI_cons, Prod.ext_iff] at hc
    ext1
    simp only [consComp, tailComp, hct, List.tail_cons]
    congr 1
    omega
  · intro c _
    ext1
    simp [consComp, tailComp]
  · intro c hc
    obtain ⟨a, t, hct, hs⟩ := exists_blocks_eq_cons c
    simp only [mem_filter, mem_univ, true_and, hct, List.headI_cons, Prod.ext_iff] at hc
    simp only [tailComp, hct, List.tail_cons]
    congr 2
    omega

variable {R : Type*} [CommRing R]

/-- The generating function `∑ₙ (∑_{c ⊨ n} f(c)) xⁿ` of a statistic `f` of compositions, read on
the list of parts. -/
private noncomputable def genFun (f : List ℕ → R) : R⟦X⟧ :=
  mk fun n => ∑ c : Composition n, f c.blocks

private theorem coeff_genFun (f : List ℕ → R) (n : ℕ) :
    coeff n (genFun f) = ∑ c : Composition n, f c.blocks :=
  coeff_mk _ _

private theorem coeff_zero_genFun (f : List ℕ → R) : coeff 0 (genFun f) = f [] := by
  rw [coeff_genFun, sum_zero]

private theorem coeff_succ_genFun (f : List ℕ → R) (n : ℕ) :
    coeff (n + 1) (genFun f) =
      ∑ p ∈ antidiagonal n, coeff p.2 (genFun fun l => f ((p.1 + 1) :: l)) := by
  simp only [coeff_genFun, sum_succ]

private theorem genFun_add (f g : List ℕ → R) :
    genFun (fun l => f l + g l) = genFun f + genFun g := by
  ext n
  simp [coeff_genFun, Finset.sum_add_distrib]

private theorem genFun_const_mul (a : R) (f : List ℕ → R) :
    genFun (fun l => a * f l) = C a * genFun f := by
  ext n
  simp [coeff_genFun, Finset.mul_sum]

/-- A statistic that factors through the first part has a factored generating function. -/
private theorem genFun_eq (f : List ℕ → R) (u : ℕ → R) (g : List ℕ → R)
    (h : ∀ a l, f (a :: l) = u a * g l) :
    genFun f = C (f []) + X * (mk (fun k => u (k + 1)) * genFun g) := by
  ext n
  cases n with
  | zero => simp [coeff_zero_genFun]
  | succ n =>
    rw [coeff_succ_genFun, map_add, coeff_C, coeff_succ_X_mul, coeff_mul]
    simp only [Nat.succ_ne_zero, ↓reduceIte, zero_add]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [h, coeff_genFun, coeff_mk, Finset.mul_sum]

/-- The series `1 + x + x² + ⋯ = 1 / (1 - x)`. -/
private noncomputable def geom : R⟦X⟧ := mk fun _ => 1

private theorem geom_mul_one_sub : (geom : R⟦X⟧) * (1 - X) = 1 :=
  mk_one_mul_one_sub_eq_one R

private theorem coeff_geom_mul_geom (m : ℕ) :
    coeff m ((geom : R⟦X⟧) * geom) = ((m + 1 : ℕ) : R) := by
  simp [geom, coeff_mul]

/-- The generating function of compositions, weighted by `y ^ (number of parts)`. -/
private noncomputable def count (y : R) : R⟦X⟧ := genFun fun l => y ^ l.length

private theorem count_eq (y : R) : count y = 1 + X * (C y * geom * count y) := by
  conv_lhs =>
    rw [count, genFun_eq (fun l => y ^ l.length) (fun _ => y) (fun l => y ^ l.length)
      (fun _ _ => by simp [pow_succ'])]
  have : (mk fun _ => y : R⟦X⟧) = C y * geom := by
    ext k
    simp [geom]
  simp [this, count]

/-- `1` if the word starts with `a`, and `0` otherwise. -/
private def startsWith (a : ℕ) : List ℕ → R
  | c :: _ => if a = c then 1 else 0
  | [] => 0

/-- The compositions starting with `j + 1`, weighted by `y ^ (number of parts)`, have generating
function `y x ^ (j + 1) · C(x)`. -/
private theorem genFun_startsWith (y : R) (j : ℕ) :
    genFun (fun l => startsWith (j + 1) l * y ^ l.length) = C y * X ^ (j + 1) * count y := by
  rw [genFun_eq (fun l => startsWith (j + 1) l * y ^ l.length)
    (fun k => if j + 1 = k then y else 0) (fun l => y ^ l.length)
    (fun a l => by simp only [startsWith, List.length_cons, pow_succ']; split_ifs <;> ring)]
  have : (mk fun k => if j + 1 = k + 1 then y else 0 : R⟦X⟧) = C y * X ^ j := by
    ext k
    simp [coeff_X_pow, eq_comm]
  rw [this, ← count]
  simp [startsWith, pow_succ]
  ring

/-- The height of a symmetric peak `a b a` at the start of the word `a :: w`, read on `w`. -/
private def headHeight (a : ℕ) : List ℕ → ℕ
  | b :: c :: _ => if a = c ∧ a < b then b - a else 0
  | _ => 0

private theorem symmetricPeakHeightSum_cons (a : ℕ) (l : List ℕ) :
    symmetricPeakHeightSum (a :: l) = symmetricPeakHeightSum l + headHeight a l := by
  match l with
  | [] => simp [symmetricPeakHeightSum, headHeight]
  | [b] => simp [symmetricPeakHeightSum, headHeight]
  | b :: c :: t => simp [symmetricPeakHeightSum, headHeight, add_comm]

/-- The compositions starting with `b` and then `j + 1`, weighted by `b - (j + 1)` when
`b > j + 1` and by `y ^ (number of parts)`, have generating function
`y² x ^ (2 j + 3) / (1 - x)² · C(x)`. -/
private theorem genFun_headHeight (y : R) (j : ℕ) :
    genFun (fun l => (headHeight (j + 1) l : R) * y ^ l.length) =
      C (y ^ 2) * X ^ (2 * j + 3) * (geom * geom * count y) := by
  rw [genFun_eq (fun l => (headHeight (j + 1) l : R) * y ^ l.length)
    (fun b => (if j + 1 < b then ((b - (j + 1) : ℕ) : R) else 0) * y)
    (fun l => startsWith (j + 1) l * y ^ l.length)
    (fun b l => by
      rcases l with _ | ⟨c, t⟩
      · simp [headHeight, startsWith]
      · simp only [headHeight, startsWith, List.length_cons, pow_succ']
        split_ifs <;> first | omega | ring)]
  have : (mk fun k => (if j + 1 < k + 1 then ((k + 1 - (j + 1) : ℕ) : R) else 0) * y : R⟦X⟧) =
      C y * X ^ (j + 1) * (geom * geom) := by
    ext k
    rw [coeff_mk, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
    split_ifs with h1 h2 h2
    · rw [coeff_geom_mul_geom, mul_comm]
      congr 2
      omega
    · omega
    · rw [coeff_geom_mul_geom]
      omega
    · simp
  rw [this, genFun_startsWith]
  simp [headHeight]
  ring

/-- The generating function of the total symmetric peak height over compositions, weighted by
`y ^ (number of parts)`. -/
private noncomputable def hsp (y : R) : R⟦X⟧ :=
  genFun fun l => (symmetricPeakHeightSum l : R) * y ^ l.length

/-- The series `∑ₙ (∑_{a + m = n} [x^m] (x ^ (2 a) · Y)) xⁿ = Y / (1 - x³)`. -/
private noncomputable def shiftSum (Y : R⟦X⟧) : R⟦X⟧ :=
  mk fun n => ∑ p ∈ antidiagonal n, coeff p.2 (X ^ (2 * p.1) * Y)

private theorem shiftSum_mul (Y : R⟦X⟧) : shiftSum Y * (1 - X ^ 3) = Y := by
  ext n
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', shiftSum, coeff_mk]
  split_ifs with hn
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [Nat.add_sub_cancel, coeff_mk, show m + 3 = m + 2 + 1 from rfl,
      Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ',
      Finset.Nat.sum_antidiagonal_succ']
    simp only [coeff_X_pow_mul']
    have h1 : ∀ x ∈ antidiagonal m,
        (if 2 * (x.1 + 1) ≤ x.2 + 1 + 1 then coeff (x.2 + 1 + 1 - 2 * (x.1 + 1)) Y else 0) =
          if 2 * x.1 ≤ x.2 then coeff (x.2 - 2 * x.1) Y else 0 := by
      intro x _
      split_ifs with h h' h'
      · rw [show x.2 + 1 + 1 - 2 * (x.1 + 1) = x.2 - 2 * x.1 by omega]
      · omega
      · omega
      · rfl
    have h2 : ¬ 2 * (m + 1 + 1 + 1) ≤ 0 := by omega
    have h3 : ¬ 2 * (m + 1 + 1) ≤ 0 + 1 := by omega
    rw [Finset.sum_congr rfl h1]
    simp [h2, h3]
  · interval_cases n <;> simp [Finset.Nat.sum_antidiagonal_succ, coeff_X_pow_mul']

/-- Splitting off the first part:
`H = y x/(1 - x) · H + y x · y² x³/((1 - x³)(1 - x)²) · C`. -/
private theorem hsp_eq (y : R) :
    hsp y = X * (C y * geom * hsp y) +
      X * (C y * shiftSum (C (y ^ 2) * X ^ 3 * (geom * geom * count y))) := by
  ext n
  cases n with
  | zero => simp [hsp, coeff_zero_genFun, symmetricPeakHeightSum]
  | succ n =>
    rw [map_add, coeff_succ_X_mul, coeff_succ_X_mul, coeff_mul, coeff_C_mul, hsp,
      coeff_succ_genFun, shiftSum, coeff_mk, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hf : (fun l => ((symmetricPeakHeightSum ((p.1 + 1) :: l) : ℕ) : R) *
        y ^ ((p.1 + 1) :: l).length) = fun l =>
          y * ((symmetricPeakHeightSum l : R) * y ^ l.length) +
            y * ((headHeight (p.1 + 1) l : R) * y ^ l.length) := by
      funext l
      simp only [symmetricPeakHeightSum_cons, Nat.cast_add, List.length_cons, pow_succ']
      ring
    rw [hf, genFun_add, genFun_const_mul, genFun_const_mul, genFun_headHeight, map_add,
      coeff_C_mul, coeff_C_mul]
    have hg : coeff p.1 (C y * geom : R⟦X⟧) = y := by simp [geom]
    rw [hg]
    congr 2
    rw [show (C (y ^ 2) * X ^ (2 * p.1 + 3) * (geom * geom * count y) : R⟦X⟧) =
      X ^ (2 * p.1) * (C (y ^ 2) * X ^ 3 * (geom * geom * count y)) by ring]

/-- The weighted generating function `H` of the total symmetric peak height satisfies
`H (1 - x³)(1 - x - y x)² = y³ x⁴`. -/
private theorem hsp_mul (y : R) :
    hsp y * ((1 - X ^ 3) * (1 - X - C y * X) ^ 2) = C (y ^ 3) * X ^ 4 := by
  have e1 := hsp_eq y
  have e2 := shiftSum_mul (C (y ^ 2) * X ^ 3 * (geom * geom * count y))
  have e3 := count_eq y
  have e4 := geom_mul_one_sub (R := R)
  have e5 : count y * (1 - X - C y * X) = 1 - X := by
    linear_combination (1 - X) * e3 + X * C y * count y * e4
  have e6 : geom * geom * count y * ((1 - X) * (1 - X - C y * X)) = 1 := by
    linear_combination (geom * (1 - X) + 1) * e4 + geom ^ 2 * (1 - X) * e5
  have e7 : hsp y * (1 - X - C y * X) =
      X * C y * shiftSum (C (y ^ 2) * X ^ 3 * (geom * geom * count y)) * (1 - X) := by
    linear_combination (1 - X) * e1 + X * C y * hsp y * e4
  generalize shiftSum (C (y ^ 2) * X ^ 3 * (geom * geom * count y)) = S at e2 e7
  rw [map_pow] at e2 ⊢
  linear_combination (1 - X - C y * X) * (1 - X ^ 3) * e7 +
    X * C y * (1 - X) * (1 - X - C y * X) * e2 + C y ^ 3 * X ^ 4 * e6

end symmetricPeakHeightSum_compositions_bivariate_genFun

open symmetricPeakHeightSum_compositions_bivariate_genFun in
/-- **Bivariate generating function of the total symmetric peak height over compositions.**
For $n, k \ge 0$ let $\mathrm{hsp}(n, k)$ be the sum, over all compositions $c$ of $n$ with
exactly $k$ parts, of the symmetric peak height sum of the sequence of parts of $c$. Then in
the ring $\mathbb{Z}[y][[x]]$ of formal power series in $x$ over $\mathbb{Z}[y]$,
$$
\left(\sum_{n \ge 0} \sum_{k \ge 0} \mathrm{hsp}(n, k)\, y^k x^n\right)
(1 - x^3)(1 - x - yx)^2 = y^3 x^4,
$$
that is, $\sum_{n, k \ge 0} \mathrm{hsp}(n, k)\, x^n y^k = y^3 x^4 / ((1 - x^3)(1 - x - yx)^2)$.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Lemma 1 (`integers-2026-A65-lem-1`). -/
public theorem symmetricPeakHeightSum_compositions_bivariate_genFun :
    PowerSeries.mk (fun n => ∑ c : Composition n,
        Polynomial.C ((symmetricPeakHeightSum c.blocks : ℕ) : ℤ) * Polynomial.X ^ c.length) *
        ((1 - X ^ 3) * (1 - X - PowerSeries.C (Polynomial.X : Polynomial ℤ) * X) ^ 2) =
      PowerSeries.C (Polynomial.X ^ 3 : Polynomial ℤ) * X ^ 4 := by
  have hH : PowerSeries.mk (fun n => ∑ c : Composition n,
      Polynomial.C ((symmetricPeakHeightSum c.blocks : ℕ) : ℤ) * Polynomial.X ^ c.length) =
      hsp (Polynomial.X : Polynomial ℤ) := by
    ext n
    simp [hsp, coeff_genFun]
  rw [hH, hsp_mul]

end MetaMathlibExt
