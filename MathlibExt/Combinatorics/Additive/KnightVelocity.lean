/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.Interval
public import Mathlib.Topology.Instances.Real.Lemmas
public import MathlibExt.Combinatorics.Additive.KnightDistance
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Knight velocity on the integer lattice

The square shells reduce by symmetry to a sum along one sector, with half weight at the
axis and diagonal. The piecewise-linear approximation to distance has a piecewise-quadratic
primitive, so we can telescope unit increments even on a cell that straddles the breakpoint.
-/

namespace MetaMathlibExt

open Pointwise
open scoped BigOperators

@[expose] public section

/--
**Max-norm ball.** For a natural number $h$, the max-norm ball $B_h \subset \mathbb{Z}^2$ is the
product of two copies of the integer interval $\{-h, \dots, h\}$, that is, the set of lattice
points $(x, y)$ with $\max(|x|, |y|) \le h$.

Source: Christian Táfula, *Knights Are 24/13 Times Faster than the King*, The Fibonacci Quarterly
62(3) (2024), definition of `B_h`.
-/
public def maxNormBall (h : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(h : ℤ)) h ×ˢ Finset.Icc (-(h : ℤ)) h

/--
**Number of points in the max-norm ball.** For every natural number $h$, the max-norm ball
$B_h = \{(x, y) \in \mathbb{Z}^2 : \max(|x|, |y|) \le h\}$ has exactly $(2h+1)^2$ points.

Source: Christian Táfula, *Knights Are 24/13 Times Faster than the King*, The Fibonacci Quarterly
62(3) (2024), definition of `B_h`.
-/
public theorem card_maxNormBall (h : ℕ) : (maxNormBall h).card = (2 * h + 1) ^ 2 := by
  have hcard : (Finset.Icc (-(h : ℤ)) h).card = 2 * h + 1 := by
    rw [Int.card_Icc]
    omega
  simp [maxNormBall, Finset.card_product, hcard, pow_two]

private theorem pieceDistance_involutive {A : Finset (ℤ × ℤ)}
    (e : (ℤ × ℤ) ≃+ (ℤ × ℤ)) (he : Function.Involutive e)
    (hA : ∀ p ∈ A, e p ∈ A) (p : ℤ × ℤ) :
    pieceDistance A (e p) = pieceDistance A p := by
  have hfold (n : ℕ) (q : ℤ × ℤ) (hq : q ∈ n • A) : e q ∈ n • A := by
    induction n generalizing q with
    | zero => simpa using (show q = 0 by simpa using hq)
    | succ n ih =>
      rw [succ_nsmul, Finset.mem_add] at hq ⊢
      obtain ⟨u, hu, v, hv, rfl⟩ := hq
      exact ⟨e u, ih u hu, e v, hA v hv, (map_add e u v).symm⟩
  have hmem (n : ℕ) : e p ∈ n • A ↔ p ∈ n • A :=
    ⟨fun hp => he p ▸ hfold n (e p) hp, hfold n p⟩
  have hz : e p = 0 ↔ p = 0 := by
    constructor
    · intro hp
      exact e.injective (hp.trans (map_zero e).symm)
    · rintro rfl
      exact map_zero e
  simp only [pieceDistance, hz, hmem]

private theorem knightDistance_neg_fst (a b x y : ℤ) :
    pieceDistance (knightMoves a b) (-x, y) = pieceDistance (knightMoves a b) (x, y) := by
  let e : (ℤ × ℤ) ≃+ (ℤ × ℤ) := (AddEquiv.neg ℤ).prodCongr (AddEquiv.refl ℤ)
  refine pieceDistance_involutive e (fun p => ?_) (fun p hp => ?_) (x, y)
  · change (-(-p.1), p.2) = p
    simp
  · change (-p.1, p.2) ∈ knightMoves a b
    simp only [knightMoves, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp [knightMoves]

private theorem knightDistance_swap (a b x y : ℤ) :
    pieceDistance (knightMoves a b) (y, x) = pieceDistance (knightMoves a b) (x, y) := by
  refine pieceDistance_involutive AddEquiv.prodComm (fun _ => rfl) (fun p hp => ?_) (x, y)
  change (p.2, p.1) ∈ knightMoves a b
  simp only [knightMoves, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp [knightMoves]

private theorem knightDistance_neg_snd (a b x y : ℤ) :
    pieceDistance (knightMoves a b) (x, -y) = pieceDistance (knightMoves a b) (x, y) := by
  rw [knightDistance_swap a b (-y) x, knightDistance_neg_fst, knightDistance_swap]

private theorem sum_centered_succ (f : ℤ → ℝ) (h : ℕ) :
    (∑ z ∈ Finset.Icc (-((h + 1 : ℕ) : ℤ)) (↑(h + 1 : ℕ)), f z) =
      f ((h : ℤ) + 1) + f (-((h : ℤ) + 1)) + (∑ z ∈ Finset.Icc (-(h : ℤ)) h, f z) := by
  push_cast
  have hI : Finset.Icc (-((h : ℤ) + 1)) ((h : ℤ) + 1) =
      insert ((h : ℤ) + 1) (insert (-((h : ℤ) + 1)) (Finset.Icc (-(h : ℤ)) h)) := by
    ext z
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hp : (h : ℤ) + 1 ∉ insert (-((h : ℤ) + 1)) (Finset.Icc (-(h : ℤ)) h) := by
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega
  have hn : -((h : ℤ) + 1) ∉ Finset.Icc (-(h : ℤ)) h := by
    simp only [Finset.mem_Icc]
    omega
  rw [hI, Finset.sum_insert hp, Finset.sum_insert hn, add_assoc]

private theorem sum_centered_even (f : ℤ → ℝ) (hf : ∀ x, f (-x) = f x) (h : ℕ) :
    (∑ z ∈ Finset.Icc (-(h : ℤ)) h, f z) =
      f 0 + 2 * (∑ i ∈ Finset.range h, f ((i : ℤ) + 1)) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [sum_centered_succ, hf, ih, Finset.sum_range_succ]
    ring

-- The shell at radius h + 1 has eight copies of the open sector. The endpoints
-- of the sector (axis and diagonal) occur four times each, not eight.
private theorem sum_maxNormBall_succ (f : ℤ → ℤ → ℝ) (h : ℕ)
    (hx : ∀ x y, f (-x) y = f x y) (hy : ∀ x y, f x (-y) = f x y)
    (hs : ∀ x y, f y x = f x y) :
    (∑ p ∈ maxNormBall (h + 1), f p.1 p.2) =
      (∑ p ∈ maxNormBall h, f p.1 p.2) +
        4 * (∑ i ∈ Finset.range (h + 1),
          (f ((h : ℤ) + 1) i + f ((h : ℤ) + 1) ((i : ℤ) + 1))) := by
  let r : ℤ := (h : ℤ) + 1
  let I := Finset.Icc (-(h : ℤ)) h
  have hinner (x : ℤ) :
      (∑ y ∈ Finset.Icc (-((h + 1 : ℕ) : ℤ)) (↑(h + 1 : ℕ)), f x y) =
        f x r + f x r + (∑ y ∈ I, f x y) := by
    rw [sum_centered_succ, hy]
  have hswap : (∑ x ∈ I, f x r) = ∑ y ∈ I, f r y :=
    Finset.sum_congr rfl fun x _ => hs r x
  simp only [maxNormBall, Finset.sum_product]
  rw [sum_centered_succ]
  change (∑ y ∈ Finset.Icc (-((h + 1 : ℕ) : ℤ)) (↑(h + 1 : ℕ)), f r y) +
      (∑ y ∈ Finset.Icc (-((h + 1 : ℕ) : ℤ)) (↑(h + 1 : ℕ)), f (-r) y) +
      (∑ x ∈ I, ∑ y ∈ Finset.Icc (-((h + 1 : ℕ) : ℤ)) (↑(h + 1 : ℕ)), f x y) = _
  simp only [hinner, hx, Finset.sum_add_distrib, hswap]
  rw [sum_centered_even (f r) (hy r)]
  rw [Finset.sum_range_succ' (f := fun i => f r i),
    Finset.sum_range_succ (f := fun i => f r ((i : ℤ) + 1))]
  push_cast
  change _ = (∑ x ∈ I, ∑ y ∈ I, f x y) +
    4 * ((∑ i ∈ Finset.range h, f r ((i : ℤ) + 1)) + f r 0 +
      ((∑ i ∈ Finset.range h, f r ((i : ℤ) + 1)) + f r r))
  ring

-- The secant of half the squared positive part on a unit cell lies between
-- its endpoint slopes, including when the cell crosses zero.
private theorem positivePart_secant (t : ℝ) :
    max 0 t ≤ (max 0 (t + 1)) ^ 2 / 2 - (max 0 t) ^ 2 / 2 ∧
      (max 0 (t + 1)) ^ 2 / 2 - (max 0 t) ^ 2 / 2 ≤ max 0 (t + 1) := by
  by_cases ht : 0 ≤ t
  · rw [max_eq_right ht, max_eq_right (show 0 ≤ t + 1 by linarith)]
    constructor <;> nlinarith
  · rw [max_eq_left (le_of_not_ge ht)]
    by_cases ht' : 0 ≤ t + 1
    · rw [max_eq_right ht']
      constructor
      · simpa only [zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero] using
          div_nonneg (sq_nonneg (t + 1)) (by norm_num : (0 : ℝ) ≤ 2)
      · nlinarith only [mul_nonneg ht' (show 0 ≤ 1 - (t + 1) by linarith), ht']
    · rw [max_eq_left (le_of_not_ge ht')]
      norm_num

private noncomputable def sectorDistance (a b x y : ℝ) : ℝ :=
  x / b + max 0 (y - a * x / b) / (a + b)

private noncomputable def sectorPrimitive (a b x y : ℝ) : ℝ :=
  x / b * y + ((max 0 (y - a * x / b)) ^ 2 / 2) / (a + b)

private noncomputable def sectorCoeff (a b : ℝ) : ℝ :=
  (a ^ 2 + 3 * b ^ 2) / (2 * (a + b) * b ^ 2)

private theorem sector_cell (a b x y : ℝ) (h : 0 < a + b) :
    let d := sectorDistance a b x
    let F := sectorPrimitive a b x
    d y ≤ F (y + 1) - F y ∧ F (y + 1) - F y ≤ d (y + 1) ∧
      d (y + 1) - d y ≤ 1 / (a + b) := by
  let t := y - a * x / b
  have heq : y + 1 - a * x / b = t + 1 := by dsimp [t]; ring
  obtain ⟨hlo, hhi⟩ := positivePart_secant t
  have hlo' := div_le_div_of_nonneg_right hlo h.le
  have hhi' := div_le_div_of_nonneg_right hhi h.le
  have hdiff : max 0 (t + 1) ≤ max 0 t + 1 :=
    max_le (by positivity) (by linarith only [le_max_right (0 : ℝ) t])
  have hdiff' := div_le_div_of_nonneg_right hdiff h.le
  rw [sub_div] at hlo' hhi'
  rw [add_div] at hdiff'
  dsimp only [sectorDistance, sectorPrimitive]
  rw [heq]
  change _ ∧ _ ∧ _
  simp only [mul_add, mul_one]
  exact ⟨by linarith only [hlo'], by linarith only [hhi'], by linarith only [hdiff']⟩

private theorem sectorPrimitive_endpoints (a b x : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : 0 < b) (hx : 0 ≤ x) :
    sectorPrimitive a b x x - sectorPrimitive a b x 0 = sectorCoeff a b * x ^ 2 := by
  have hzero : 0 - a * x / b ≤ 0 := by
    exact sub_nonpos.mpr (by positivity)
  have hx' : 0 ≤ x - a * x / b := by
    apply sub_nonneg.mpr ((div_le_iff₀ hb).2 _)
    simpa only [mul_comm x b] using mul_le_mul_of_nonneg_right hab hx
  simp only [sectorPrimitive, sectorCoeff, max_eq_right hx', max_eq_left hzero, mul_zero,
    zero_pow (by decide : 2 ≠ 0), zero_div, add_zero, sub_zero]
  have hs : 0 < a + b := add_pos_of_nonneg_of_pos ha hb
  field_simp [hb.ne', hs.ne']
  ring

private theorem sector_trapezoids_error (a b : ℝ) (x : ℕ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : 0 < b) (d : ℕ → ℝ) (E : ℝ)
    (hd : ∀ y : ℕ, y ≤ x → |d y - sectorDistance a b x y| ≤ E) :
    |4 * (∑ y ∈ Finset.range x, (d y + d (y + 1))) - 8 * sectorCoeff a b * (x : ℝ) ^ 2| ≤
      8 * (E + 1 / (a + b)) * (x : ℝ) := by
  let F (y : ℕ) := sectorPrimitive a b x y
  have hcell (y : ℕ) (hy : y ∈ Finset.range x) :
      |d y + d (y + 1) - 2 * (F (y + 1) - F y)| ≤ 2 * (E + 1 / (a + b)) := by
    have hy' := Finset.mem_range.mp hy
    obtain ⟨hl, hu, hdiff⟩ := sector_cell a b x y (add_pos_of_nonneg_of_pos ha hb)
    obtain ⟨hd₀, hd₁⟩ := abs_le.mp (hd y hy'.le)
    obtain ⟨hd₂, hd₃⟩ := abs_le.mp (hd (y + 1) hy')
    change sectorDistance a b x y ≤ _ at hl
    change _ ≤ sectorDistance a b x ((y : ℝ) + 1) at hu
    change sectorDistance a b x ((y : ℝ) + 1) - sectorDistance a b x y ≤ _ at hdiff
    simp only [Nat.cast_add, Nat.cast_one] at hd₂ hd₃
    have hF : F (y + 1) = sectorPrimitive a b x ((y : ℝ) + 1) := by simp [F]
    rw [hF]
    change |d y + d (y + 1) - 2 *
      (sectorPrimitive a b x ((y : ℝ) + 1) - sectorPrimitive a b x y)| ≤ _
    exact abs_le.mpr ⟨by linarith only [hl, hu, hdiff, hd₀, hd₂],
      by linarith only [hl, hu, hdiff, hd₁, hd₃]⟩
  have htelescope (n : ℕ) : (∑ y ∈ Finset.range n, (F (y + 1) - F y)) = F n - F 0 := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  have heq : 4 * (∑ y ∈ Finset.range x, (d y + d (y + 1) - 2 * (F (y + 1) - F y))) =
      4 * (∑ y ∈ Finset.range x, (d y + d (y + 1))) - 8 * sectorCoeff a b * (x : ℝ) ^ 2 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, htelescope]
    have hends : F x - F 0 = sectorCoeff a b * (x : ℝ) ^ 2 := by
      simpa only [F, Nat.cast_zero] using
        sectorPrimitive_endpoints a b x ha hab hb (Nat.cast_nonneg x)
    rw [hends]
    ring
  rw [← heq, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  calc
    _ ≤ 4 * (∑ y ∈ Finset.range x, |d y + d (y + 1) - 2 * (F (y + 1) - F y)|) :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ 4 * (∑ _y ∈ Finset.range x, (2 * (E + 1 / (a + b)))) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) (by norm_num)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

private theorem knightDistance_sector_error {a b : ℕ} {M : ℝ} {x y : ℤ}
    (hb : 0 < (b : ℝ))
    (hlo : (b : ℤ) * y ≤ (a : ℤ) * x →
      |(pieceDistance (knightMoves a b) (x, y) : ℝ) - (x : ℝ) / b| ≤ M * b)
    (hhi : (a : ℤ) * x < (b : ℤ) * y →
      |(pieceDistance (knightMoves a b) (x, y) : ℝ) -
        ((x : ℝ) + y) / ((a : ℝ) + b)| ≤ M * b) :
    |(pieceDistance (knightMoves a b) (x, y) : ℝ) - sectorDistance a b x y| ≤ M * b := by
  by_cases h : (b : ℤ) * y ≤ (a : ℤ) * x
  · have hr : (b : ℝ) * y ≤ (a : ℝ) * x := by exact_mod_cast h
    have ht : (y : ℝ) ≤ (a : ℝ) * x / b := (le_div_iff₀ hb).2 (by linarith only [hr])
    simpa only [sectorDistance, max_eq_left (sub_nonpos.mpr ht), zero_div, add_zero] using hlo h
  · have h' := lt_of_not_ge h
    have hr : (a : ℝ) * x < (b : ℝ) * y := by exact_mod_cast h'
    have ht : (a : ℝ) * x / b ≤ y := (div_le_iff₀ hb).2 (by linarith only [hr])
    have heq : sectorDistance a b x y = ((x : ℝ) + y) / ((a : ℝ) + b) := by
      rw [sectorDistance, max_eq_right (sub_nonneg.mpr ht)]
      field_simp [hb.ne']
      ring
    rw [heq]
    exact hhi h'

private noncomputable def knightBallSum (a b h : ℕ) : ℝ :=
  ∑ p ∈ maxNormBall h, (pieceDistance (knightMoves a b) p : ℝ)

private noncomputable def knightBallPolynomial (a b h : ℕ) : ℝ :=
  8 * sectorCoeff a b * ((h : ℝ) * ((h : ℝ) + 1) * (2 * (h : ℝ) + 1) / 6)

-- The shell error is linear in its radius; adding the shells gives a quadratic error.
private theorem knightBallSum_error {a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
    (hcoprime : Nat.Coprime a b) (hodd : Odd (a + b)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℕ,
      |knightBallSum a b h - knightBallPolynomial a b h| ≤ K * (h : ℝ) ^ 2 := by
  have ha' : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have hb : (0 : ℝ) < b := ha'.trans_lt hab'
  obtain ⟨M, hM⟩ := knight_distance_asymptotics
  let K : ℝ := 8 * (|M * (b : ℝ)| + 1 / ((a : ℝ) + b))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hstep (h : ℕ) :
      |knightBallSum a b (h + 1) - knightBallSum a b h -
        (knightBallPolynomial a b (h + 1) - knightBallPolynomial a b h)| ≤
        K * ((h : ℝ) + 1) := by
    let f (x y : ℤ) : ℝ := pieceDistance (knightMoves a b) (x, y)
    have hball := sum_maxNormBall_succ f h
      (fun x y => congrArg (Nat.cast : ℕ → ℝ) (knightDistance_neg_fst a b x y))
      (fun x y => congrArg (Nat.cast : ℕ → ℝ) (knightDistance_neg_snd a b x y))
      (fun x y => congrArg (Nat.cast : ℕ → ℝ) (knightDistance_swap a b x y))
    have hsum : knightBallSum a b (h + 1) - knightBallSum a b h =
        4 * (∑ i ∈ Finset.range (h + 1),
          (f ((h : ℤ) + 1) i + f ((h : ℤ) + 1) ((i : ℤ) + 1))) := by
      exact sub_eq_of_eq_add (hball.trans (add_comm _ _))
    have hpoly : knightBallPolynomial a b (h + 1) - knightBallPolynomial a b h =
        8 * sectorCoeff a b * ((h : ℝ) + 1) ^ 2 := by
      simp only [knightBallPolynomial, Nat.cast_add, Nat.cast_one]
      ring
    rw [hsum, hpoly]
    have hrow (y : ℕ) (hy : y ≤ h + 1) :
        |f (↑(h + 1 : ℕ)) y - sectorDistance a b (↑(h + 1 : ℕ)) y| ≤ |M * (b : ℝ)| := by
      obtain ⟨hl, hu⟩ := hM a b (h + 1 : ℕ) y ha hab hcoprime hodd (by positivity)
        (by exact_mod_cast hy)
      have hdist := (knightDistance_sector_error hb hl hu).trans (le_abs_self (M * (b : ℝ)))
      simpa only [Int.cast_natCast] using hdist
    simpa only [Nat.cast_add, Nat.cast_one, K] using
      sector_trapezoids_error a b (h + 1) ha' hab'.le hb (fun y => f (↑(h + 1 : ℕ)) y)
        |M * (b : ℝ)| hrow
  refine ⟨K, hK, fun h => ?_⟩
  induction h with
  | zero => simp [knightBallSum, knightBallPolynomial, maxNormBall, pieceDistance]
  | succ h ih =>
    calc
      _ = |(knightBallSum a b h - knightBallPolynomial a b h) +
          (knightBallSum a b (h + 1) - knightBallSum a b h -
            (knightBallPolynomial a b (h + 1) - knightBallPolynomial a b h))| := by
        congr 1
        ring
      _ ≤ |knightBallSum a b h - knightBallPolynomial a b h| +
          |knightBallSum a b (h + 1) - knightBallSum a b h -
            (knightBallPolynomial a b (h + 1) - knightBallPolynomial a b h)| := abs_add_le _ _
      _ ≤ K * (h : ℝ) ^ 2 + K * ((h : ℝ) + 1) := add_le_add ih (hstep h)
      _ ≤ _ := by
        push_cast
        nlinarith only [mul_nonneg hK (Nat.cast_nonneg h : (0 : ℝ) ≤ h)]

open Filter

private theorem tendsto_knightBallSum {a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
    (hcoprime : Nat.Coprime a b) (hodd : Odd (a + b)) :
    Tendsto (fun h : ℕ => knightBallSum a b h / (h : ℝ) ^ 3) atTop
      (nhds (8 * sectorCoeff a b / 3)) := by
  let c := sectorCoeff a b
  have hinv : Tendsto (fun h : ℕ => (h : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hpoly : Tendsto (fun h : ℕ => knightBallPolynomial a b h / (h : ℝ) ^ 3)
      atTop (nhds (8 * c / 3)) := by
    have h := (((hinv.const_add 1).const_mul (8 * c)).mul (hinv.const_add 2)).div_const 6
    have h' : Tendsto (fun h : ℕ => 8 * c * (1 + (h : ℝ)⁻¹) * (2 + (h : ℝ)⁻¹) / 6)
        atTop (nhds (8 * c / 3)) := by
      have hc' : 8 * c * 1 * 2 / 6 = 8 * c / 3 := by ring
      simpa only [add_zero, hc'] using h
    apply h'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    dsimp [knightBallPolynomial, c]
    field_simp [hn']
  obtain ⟨K, _, hK⟩ := knightBallSum_error ha hab hcoprime hodd
  have herr : Tendsto (fun h : ℕ => (knightBallSum a b h - knightBallPolynomial a b h) /
      (h : ℝ) ^ 3) atTop (nhds 0) := by
    have hbound : Tendsto (fun h : ℕ => K * (h : ℝ)⁻¹) atTop (nhds 0) := by
      simpa only [mul_zero] using hinv.const_mul K
    have hle : ∀ᶠ h : ℕ in atTop,
        |(knightBallSum a b h - knightBallPolynomial a b h) / (h : ℝ) ^ 3| ≤ K * (h : ℝ)⁻¹ := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with h hh
      have hh' : (0 : ℝ) < h := by exact_mod_cast hh
      rw [abs_div, abs_of_pos (pow_pos hh' _)]
      calc
        _ ≤ K * (h : ℝ) ^ 2 / (h : ℝ) ^ 3 := div_le_div_of_nonneg_right (hK h) (by positivity)
        _ = _ := by field_simp [hh'.ne']
    have hlow : Tendsto (fun h : ℕ => -(K * (h : ℝ)⁻¹)) atTop (nhds 0) := by
      simpa only [neg_zero] using hbound.neg
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hbound
      (hle.mono fun _ hx => (abs_le.mp hx).1) (hle.mono fun _ hx => (abs_le.mp hx).2)
  have h := hpoly.add herr
  simp only [add_zero] at h
  refine h.congr fun n => ?_
  simp [sub_div]

private theorem tendsto_card_maxNormBall :
    Tendsto (fun h : ℕ => ((maxNormBall h).card : ℝ) / (h : ℝ) ^ 2) atTop (nhds 4) := by
  have hinv : Tendsto (fun h : ℕ => (h : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have h : Tendsto (fun h : ℕ => (2 + (h : ℝ)⁻¹) ^ 2) atTop (nhds 4) := by
    simpa only [add_zero, show (2 : ℝ) ^ 2 = 4 by norm_num] using
      (hinv.const_add (2 : ℝ)).pow 2
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [card_maxNormBall]
  push_cast
  field_simp [hn']

/--
**Velocity formula for the (a, b)-knight.** Let $a$ and $b$ be natural numbers with
$1 \le a < b$, $\gcd(a, b) = 1$ and $a + b$ odd, let
$N_{a,b} = \{(\pm a, \pm b), (\pm b, \pm a)\}$ be the $(a,b)$-knight's move set, and for
$p \in \mathbb{Z}^2$ let $d_{a,b}(p)$ be the piece distance of $p$ for $N_{a,b}$. For a natural
number $h$, let $B_h = \{(x, y) \in \mathbb{Z}^2 : \max(|x|, |y|) \le h\}$ be the max-norm
ball and let $\bar{d}(h) = |B_h|^{-1} \sum_{p \in B_h} d_{a,b}(p)$ be the average of $d_{a,b}$
over $B_h$. Then
$$\lim_{h \to \infty} \frac{2h}{3} \, \bar{d}(h)^{-1} = \frac{2(a+b)b^2}{a^2 + 3b^2}.$$

Source: Christian Táfula, *Knights Are 24/13 Times Faster than the King*, The Fibonacci Quarterly
62(3) (2024), Theorem 1.3.
-/
public theorem knight_velocity_formula (a b : ℕ)
    (ha : 1 ≤ a) (hab : a < b) (hcoprime : Nat.Coprime a b)
    (hodd : Odd (a + b)) :
    Filter.Tendsto
      (fun h : ℕ =>
        (2 * (h : ℝ) / 3) *
          (((∑ p ∈ maxNormBall h,
              (pieceDistance (knightMoves (a : ℤ) (b : ℤ)) p : ℝ)) /
            ((maxNormBall h).card : ℝ))⁻¹))
      Filter.atTop
      (nhds
        (2 * ((a : ℝ) + (b : ℝ)) * (b : ℝ) ^ 2 /
          ((a : ℝ) ^ 2 + 3 * (b : ℝ) ^ 2))) := by
  have hb : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  -- The average divided by the radius has a strictly positive limit.
  have hmean := (tendsto_knightBallSum ha hab hcoprime hodd).div
    tendsto_card_maxNormBall (by norm_num : (4 : ℝ) ≠ 0)
  have hc : 0 < (8 * sectorCoeff a b / 3) / 4 := by unfold sectorCoeff; positivity
  have h := (hmean.inv₀ hc.ne').const_mul (2 / 3 : ℝ)
  have htarget : (2 / 3 : ℝ) * ((8 * sectorCoeff a b / 3) / 4)⁻¹ =
      2 * ((a : ℝ) + b) * (b : ℝ) ^ 2 / ((a : ℝ) ^ 2 + 3 * (b : ℝ) ^ 2) := by
    have hs : (0 : ℝ) < (a : ℝ) + b := by positivity
    have hd : (0 : ℝ) < (a : ℝ) ^ 2 + 3 * (b : ℝ) ^ 2 := by positivity
    unfold sectorCoeff
    field_simp [hb.ne', hs.ne', hd.ne']
    ring
  rw [htarget] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  change (2 / 3 : ℝ) * ((knightBallSum a b n / (n : ℝ) ^ 3) /
      ((maxNormBall n).card / (n : ℝ) ^ 2))⁻¹ =
    (2 * (n : ℝ) / 3) * (knightBallSum a b n / (maxNormBall n).card)⁻¹
  by_cases hsum : knightBallSum a b n = 0
  · simp [hsum]
  · have hcard : ((maxNormBall n).card : ℝ) ≠ 0 := by rw [card_maxNormBall]; positivity
    field_simp [hn', hsum, hcard]

end

end MetaMathlibExt
