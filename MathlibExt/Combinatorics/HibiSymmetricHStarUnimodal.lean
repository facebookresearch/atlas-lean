/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.WeightedProjectiveSimplexEhrhart
public import MathlibExt.Combinatorics.WeightedProjectiveSimplexReflexive
public import MathlibExt.Geometry.LatticePointEnumerator
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.Convex.Combination
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Hibi's conjecture on symmetric h*-vectors

The weighted simplex with weights `(1, 1, 1, 1, 1, 3)` is a counterexample. The seven integral
parts of the homogenized barycentric coordinates give the denominator `(1 - X)^7`. The nine
possible residues give the palindromic numerator `(1, 1, 2, 1, 2, 1, 1)`.

## References

* C. A. Athanasiadis, *On the unimodality of h*-vectors*, in *Ehrhart Quasipolynomials: Algebra,
  Combinatorics, and Geometry*, Oberwolfach Reports 1 (2004), no. 39, p. 2078, Conjecture 2.
* M. Mustaţă and S. Payne, *Ehrhart polynomials and stringy Betti numbers*, Math. Ann. 333 (2005),
  787–795, Example 1.1 (a different six-dimensional counterexample).
* S. Payne, *Ehrhart series and lattice triangulations*, Discrete Comput. Geom. 40 (2008), 365–376,
  Example 4.2 and the proof of Theorem 1.4 (the case `b = 3`, `k = 2`, `r = 0`).
* B. Braun, R. Davis, and L. Solus, *Detecting the integer decomposition property and Ehrhart
  unimodality in reflexive simplices*, Adv. in Appl. Math. 100 (2018), 122–142, equation (2)
  (Payne's family in weight notation) and Theorem 2.2 (the general weighted-simplex formula and
  its proof by counting lattice points in the fundamental parallelepiped).
* B. Braun, R. Davis, D. Hanely, M. Lane, and L. Solus, *The Integer Decomposition Property and
  Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article A60, Theorem 5 (restating
  Braun–Davis–Solus, Theorem 2.2).
-/

namespace MathlibExt.Combinatorics

open MetaMathlibExt
open scoped BigOperators Pointwise

noncomputable section

private def weights : Fin 6 → ℕ := ![1, 1, 1, 1, 1, 3]

private theorem sum_weights : ∑ i, weights i = 8 := by decide +kernel

private def barycentricMap : (Fin 7 → ℝ) →ₗ[ℝ] (Fin 6 → ℝ) where
  toFun a i := a i.succ - weights i * a 0
  map_add' a b := by
    funext i
    change (a i.succ + b i.succ) - weights i * (a 0 + b 0) =
      (a i.succ - weights i * a 0) + (b i.succ - weights i * b 0)
    ring
  map_smul' c a := by
    funext i
    change c * a i.succ - weights i * (c * a 0) = c * (a i.succ - weights i * a 0)
    ring

private theorem barycentricMap_apply (a : Fin 7 → ℝ) (i : Fin 6) :
    barycentricMap a i = a i.succ - weights i * a 0 := rfl

private theorem hull_single_eq :
    convexHull ℝ (Set.range fun j : Fin 7 => Pi.single j (1 : ℝ)) =
      {a : Fin 7 → ℝ | (∀ j, 0 ≤ a j) ∧ ∑ j, a j = 1} := by
  refine Set.Subset.antisymm (convexHull_min ?_ ?_) ?_
  · rintro _ ⟨i, rfl⟩
    exact ⟨fun j => by by_cases h : j = i <;> simp [h], by simp⟩
  · intro a ha b hb u v hu hv huv
    change (∀ j, 0 ≤ (u • a + v • b) j) ∧ ∑ j, (u • a + v • b) j = 1
    refine ⟨fun j => add_nonneg (mul_nonneg hu (ha.1 j)) (mul_nonneg hv (hb.1 j)), ?_⟩
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, ha.2, hb.2, mul_one] using huv
  · rintro a ⟨ha, hs⟩
    have he : (∑ j, a j • Pi.single j (1 : ℝ)) = a := by
      funext i
      simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite]
    rw [← he]
    exact (convex_convexHull ℝ _).sum_mem (fun j _ => ha j) hs
      (fun j _ => subset_convexHull ℝ _ ⟨j, rfl⟩)

private theorem simplex_eq_image : weightedSimplex weights =
    barycentricMap '' {a : Fin 7 → ℝ | (∀ j, 0 ≤ a j) ∧ ∑ j, a j = 1} := by
  rw [← hull_single_eq, barycentricMap.image_convexHull, weightedSimplex]
  congr 1
  ext x
  constructor
  · rintro (⟨i, rfl⟩ | hx)
    · exact ⟨Pi.single i.succ 1, ⟨i.succ, rfl⟩, by
        ext j
        by_cases h : j = i <;> simp [barycentricMap_apply, h]⟩
    · rw [Set.mem_singleton_iff] at hx
      refine ⟨Pi.single 0 1, ⟨0, rfl⟩, ?_⟩
      ext j
      simp [hx, barycentricMap_apply]
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · right
      ext j
      simp [barycentricMap_apply]
    · left
      refine ⟨j, ?_⟩
      ext k
      by_cases h : k = j <;> simp [barycentricMap_apply, h]

private theorem mem_simplex_smul (t : ℕ) (x : Fin 6 → ℝ) :
    x ∈ (t : ℝ) • weightedSimplex weights ↔
      ∃ a : Fin 7 → ℝ, (∀ j, 0 ≤ a j) ∧ ∑ j, a j = t ∧ barycentricMap a = x := by
  rw [simplex_eq_image]
  constructor
  · rintro ⟨_, ⟨a, ⟨ha, hs⟩, rfl⟩, rfl⟩
    refine ⟨(t : ℝ) • a, fun i => mul_nonneg (Nat.cast_nonneg _) (ha i), ?_, ?_⟩
    · simp [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hs]
    · exact barycentricMap.map_smul _ _
  · rintro ⟨a, ha, hs, rfl⟩
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · have ha0 : a = 0 := by
        funext j
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => ha i)).1
          (by simpa using hs) j (Finset.mem_univ j)
      refine ⟨barycentricMap (Pi.single 0 1), ⟨_, ⟨?_, by simp⟩, rfl⟩, ?_⟩
      · intro i
        by_cases h : i = 0 <;> simp [h]
      · simp [ha0]
    · have ht' : (0 : ℝ) < t := by exact_mod_cast ht
      let b : Fin 7 → ℝ := fun j => a j / t
      refine ⟨barycentricMap b, ⟨b, ⟨fun j => div_nonneg (ha j) ht'.le, ?_⟩, rfl⟩, ?_⟩
      · simp [b, ← Finset.sum_div, hs, ht'.ne']
      · change (t : ℝ) • barycentricMap b = barycentricMap a
        rw [← map_smul]
        congr 1
        ext j
        change (t : ℝ) * (a j / t) = a j
        rw [mul_comm, div_mul_cancel₀ _ ht'.ne']

private theorem mem_simplex_smul_iff (t : ℕ) (x : Fin 6 → ℝ) :
    x ∈ (t : ℝ) • weightedSimplex weights ↔
      0 ≤ (t : ℝ) - ∑ i, x i ∧
        ∀ i, 0 ≤ 9 * x i + weights i * ((t : ℝ) - ∑ j, x j) := by
  have hq : (∑ i, (weights i : ℝ)) = 8 := by exact_mod_cast sum_weights
  rw [mem_simplex_smul]
  constructor
  · rintro ⟨a, ha, hs, rfl⟩
    rw [Fin.sum_univ_succ] at hs
    simp only [barycentricMap_apply]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hq]
    constructor
    · linarith [ha 0]
    · intro i
      have h0 : (t : ℝ) - ((∑ j : Fin 6, a j.succ) - 8 * a 0) = 9 * a 0 := by linarith
      rw [h0]
      linarith only [ha i.succ]
  · rintro ⟨h0, hi⟩
    let z : ℝ := ((t : ℝ) - ∑ i, x i) / 9
    refine ⟨Fin.cons z (fun i => x i + weights i * z), ?_, ?_, ?_⟩
    · refine Fin.cases ?_ (fun i => ?_)
      · exact div_nonneg h0 (by norm_num)
      · change 0 ≤ x i + weights i * z
        have hzi : 9 * (x i + weights i * z) = 9 * x i + weights i * (t - ∑ j, x j) := by
          dsimp only [z]
          ring
        linarith only [hi i, hzi]
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Finset.sum_add_distrib, ← Finset.sum_mul, hq]
      dsimp only [z]
      linarith
    · ext i
      simp [barycentricMap_apply]

private theorem zero_mem_interior : (0 : Fin 6 → ℝ) ∈ interior (weightedSimplex weights) := by
  let U : Set (Fin 6 → ℝ) := {x | ∑ i, x i < 1 ∧ ∀ i,
    0 < 9 * x i + weights i * (1 - ∑ j, x j)}
  have hs : Continuous fun x : Fin 6 → ℝ => ∑ i, x i :=
    continuous_finsetSum _ fun i _ => continuous_apply i
  have hU : IsOpen U := by
    have he : U = {x : Fin 6 → ℝ | ∑ i, x i < 1} ∩ ⋂ i : Fin 6,
        {x : Fin 6 → ℝ | 0 < 9 * x i + weights i * (1 - ∑ j, x j)} := by
      ext x
      simp [U]
    rw [he]
    exact (isOpen_lt hs continuous_const).inter (isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (((continuous_apply i).const_mul 9).add
        ((continuous_const.sub hs).const_mul _)))
  have hUP : U ⊆ weightedSimplex weights := by
    intro x hx
    change _ ∧ _ at hx
    simpa only [Nat.cast_one, one_smul] using (mem_simplex_smul_iff 1 x).2
      ⟨by simpa using sub_nonneg.mpr hx.1.le, fun i => by simpa using (hx.2 i).le⟩
  refine interior_maximal hUP hU ?_
  have hpos : ∀ i, 0 < weights i := by decide +kernel
  simpa [U] using hpos

-- The barycentric coefficient at the negative vertex, multiplied by 9.
private def slack (n : ℕ) (x : Fin 6 → ℤ) : ℤ := n - ∑ i, x i

private def integralSlack (n : ℕ) (x : Fin 6 → ℤ) : Prop :=
  0 ≤ slack n x ∧ ∀ i, 0 ≤ 9 * x i + (weights i : ℤ) * slack n x

private theorem latticePoint_iff (n : ℕ) (x : Fin 6 → ℤ) :
    (fun i => (x i : ℝ)) ∈ LatticePointEnumerator.latticePointSet 6 (weightedSimplex weights) n ↔
      integralSlack n x := by
  rw [LatticePointEnumerator.latticePointSet, Set.mem_inter_iff, mem_simplex_smul_iff]
  constructor
  · rintro ⟨⟨h0, hi⟩, _⟩
    exact ⟨by exact_mod_cast h0, fun i => by exact_mod_cast hi i⟩
  · rintro ⟨h0, hi⟩
    change 0 ≤ (n : ℤ) - ∑ j, x j at h0
    change ∀ i, 0 ≤ 9 * x i + (weights i : ℤ) * ((n : ℤ) - ∑ j, x j) at hi
    exact ⟨⟨by exact_mod_cast h0, fun i => by exact_mod_cast hi i⟩,
      LatticePointEnumerator.mem_stdLattice_iff.2 fun i => ⟨x i, rfl⟩⟩

-- For b < 9, the first five floors vanish and the last is b / 3.
private def shift (b : Fin 9) (i : Fin 6) : ℤ := (weights i * (b.val : ℤ)) / 9

private def residueHeight (b : Fin 9) : ℕ := b.val - b.val / 3

private theorem sum_shift (b : Fin 9) : ∑ i, shift b i = ((b.val / 3 : ℕ) : ℤ) := by
  fin_cases b <;> decide +kernel

private theorem residueHeight_cast (b : Fin 9) :
    (residueHeight b : ℤ) = (b.val : ℤ) - ((b.val / 3 : ℕ) : ℤ) :=
  Nat.cast_sub (Nat.div_le_self _ _)

-- The integer part is nonnegative iff the original barycentric coordinate is.
private theorem coordinate_nonneg (x u : ℤ) (b : Fin 9) (i : Fin 6) :
    0 ≤ 9 * x + (weights i : ℤ) * (9 * u + b.val) ↔
      0 ≤ x + (weights i : ℤ) * u + shift b i := by
  let v : ℤ := weights i * (b.val : ℤ)
  have hv : v % 9 + 9 * shift b i = v := by
    change v % 9 + 9 * (v / 9) = v
    omega
  have h : 9 * x + (weights i : ℤ) * (9 * u + b.val) =
      9 * (x + (weights i : ℤ) * u + shift b i) + v % 9 := by
    calc
      _ = 9 * (x + (weights i : ℤ) * u) + v := by dsimp only [v]; ring
      _ = _ := by omega
  rw [h]
  have h0 := Int.emod_nonneg v (by decide : (9 : ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos v (by decide : (0 : ℤ) < 9)
  omega

private def point (b : Fin 9) (k : Fin 7 → ℕ) (i : Fin 6) : ℤ :=
  (k i.succ : ℤ) - weights i * (k 0 : ℤ) - shift b i

private theorem slack_point_iff (n : ℕ) (b : Fin 9) (k : Fin 7 → ℕ) :
    slack n (point b k) = 9 * (k 0 : ℤ) + b.val ↔ residueHeight b + ∑ i, k i = n := by
  have hq : (∑ i, (weights i : ℤ)) = 8 := by exact_mod_cast sum_weights
  unfold slack point
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hq, sum_shift]
  rw [← Nat.cast_inj (R := ℤ)]
  simp only [Fin.sum_univ_succ k]
  push_cast
  rw [residueHeight_cast]
  omega

private abbrev Parameters (n : ℕ) :=
  Σ b : Fin 9, {k : Fin 7 → ℕ // residueHeight b + ∑ i, k i = n}

-- A lattice point at height n is uniquely specified by its residue and its seven integer parts.
private def pointEquiv (n : ℕ) : Parameters n ≃ {x : Fin 6 → ℤ // integralSlack n x} := by
  refine Equiv.ofBijective (fun ⟨b, k, hk⟩ => ⟨point b k, ?_⟩) ⟨?_, ?_⟩
  · have he := (slack_point_iff n b k).2 hk
    unfold integralSlack
    rw [he]
    refine ⟨by positivity, fun i => (coordinate_nonneg _ _ _ _).2 ?_⟩
    dsimp only [point]
    have hnonneg : 0 ≤ (k i.succ : ℤ) := Nat.cast_nonneg _
    omega
  · rintro ⟨b, k, hk⟩ ⟨c, l, hl⟩ h
    have he : point b k = point c l := congrArg Subtype.val h
    have hb := (slack_point_iff n b k).2 hk
    have hc := (slack_point_iff n c l).2 hl
    rw [he] at hb
    have hb' := b.isLt
    have hc' := c.isLt
    have hbc : b = c := Fin.ext (by omega)
    have hkl : k 0 = l 0 := by omega
    subst c
    have hparts : k = l := by
      funext i
      refine Fin.cases hkl (fun j => ?_) i
      have hj := congrFun he j
      dsimp only [point] at hj
      rw [hkl] at hj
      omega
    subst l
    rfl
  · rintro ⟨x, hx0, hxi⟩
    let s := slack n x
    let b : Fin 9 := ⟨(s % 9).toNat, by omega⟩
    let u := (s / 9).toNat
    have hs : slack n x = 9 * (u : ℤ) + b.val := by
      change 0 ≤ s at hx0
      dsimp only [b, u, s] at *
      omega
    let v (i : Fin 6) : ℤ := x i + (weights i : ℤ) * u + shift b i
    have hv (i : Fin 6) : 0 ≤ v i := by
      apply (coordinate_nonneg _ _ _ _).1
      simpa only [← hs] using hxi i
    let k : Fin 7 → ℕ := Fin.cons u (fun i => (v i).toNat)
    have he : point b k = x := by
      funext i
      simp only [point, k, Fin.cons_succ, Fin.cons_zero, Int.toNat_of_nonneg (hv i), v]
      ring
    refine ⟨⟨b, k, (slack_point_iff n b k).1 ?_⟩, Subtype.ext he⟩
    simpa only [he, k, Fin.cons_zero] using hs

private def integralLatticeEquiv (n : ℕ) :
    {x : Fin 6 → ℤ // integralSlack n x} ≃
      LatticePointEnumerator.latticePointSet 6 (weightedSimplex weights) n := by
  refine Equiv.ofBijective (fun x => ⟨fun i => (x.val i : ℝ), (latticePoint_iff n x.val).2 x.2⟩)
    ⟨?_, ?_⟩
  · intro x y h
    apply Subtype.ext
    funext i
    have hi : (x.val i : ℝ) = (y.val i : ℝ) := congrFun (congrArg Subtype.val h) i
    exact_mod_cast hi
  · rintro ⟨y, hy⟩
    have hz := hy.2
    choose x hx using LatticePointEnumerator.mem_stdLattice_iff.1 hz
    have he : (fun i => (x i : ℝ)) = y := funext hx
    exact ⟨⟨x, (latticePoint_iff n x).1 (he.symm ▸ hy)⟩, Subtype.ext he⟩

-- Stars and bars, via the finite set of finitely supported tuples of the given weight.
private def tupleEquiv (m : ℕ) : {k : Fin 7 → ℕ // ∑ i, k i = m} ≃
    (Finset.univ : Finset (Fin 7)).finsuppAntidiag m :=
  Finsupp.equivFunOnFinite.symm.subtypeEquiv fun k => by simp

private theorem card_tuple (m : ℕ) :
    Nat.card {k : Fin 7 → ℕ // ∑ i, k i = m} = (6 + m).choose 6 := by
  classical
  rw [Nat.card_congr (tupleEquiv m), Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_finsuppAntidiag_nat_eq_choose]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [show 7 + m - 1 = 6 + m by omega]
  exact Nat.choose_symm_add.symm

private theorem card_residue (n : ℕ) (b : Fin 9) :
    Nat.card {k : Fin 7 → ℕ // residueHeight b + ∑ i, k i = n} =
      if residueHeight b ≤ n then (6 + (n - residueHeight b)).choose 6 else 0 := by
  split_ifs with hb
  · rw [← card_tuple]
    exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) (fun k => by dsimp; omega))
  · have hempty : IsEmpty {k : Fin 7 → ℕ // residueHeight b + ∑ i, k i = n} :=
      ⟨fun k => by have := k.2; omega⟩
    exact Nat.card_eq_zero.2 (Or.inl hempty)

private theorem latticeEnumerator_eq_sum (n : ℕ) :
    LatticePointEnumerator.latticeEnumerator 6 (weightedSimplex weights) n =
      ∑ b : Fin 9, if residueHeight b ≤ n then (6 + (n - residueHeight b)).choose 6 else 0 := by
  let _ (b : Fin 9) : Finite {k : Fin 7 → ℕ // residueHeight b + ∑ i, k i = n} := by
    let f (k : {k : Fin 7 → ℕ // residueHeight b + ∑ i, k i = n}) (i : Fin 7) : Fin (n + 1) :=
      ⟨k.val i, by
        have hle := Finset.single_le_sum (f := k.val) (fun j _ => Nat.zero_le (k.val j))
          (Finset.mem_univ i)
        have := k.2
        omega⟩
    refine Finite.of_injective f (fun k l h => ?_)
    exact Subtype.ext (funext fun i => congrArg Fin.val (congrFun h i))
  rw [LatticePointEnumerator.latticeEnumerator, ← Nat.card_coe_set_eq,
    ← Nat.card_congr ((pointEquiv n).trans (integralLatticeEquiv n))]
  unfold Parameters
  rw [Nat.card_sigma]
  exact Finset.sum_congr rfl fun b _ => card_residue n b

private theorem numerator_eq :
    (∑ b : Fin 9, (Polynomial.X : Polynomial ℤ) ^ residueHeight b) =
      1 + Polynomial.X + 2 * Polynomial.X ^ 2 + Polynomial.X ^ 3 +
        2 * Polynomial.X ^ 4 + Polynomial.X ^ 5 + Polynomial.X ^ 6 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, residueHeight]
  norm_num
  ring

/-- **Full dimension of the counterexample simplex.** The weighted simplex with weights
$(1,1,1,1,1,3)$ is the convex hull of the standard basis vectors $e_1,\ldots,e_6$ and
$-(1,1,1,1,1,3)$ in $\mathbb{R}^6$. It has nonempty interior. -/
public theorem hibiWeightedSimplex_interior_nonempty :
    (interior (weightedSimplex ![1, 1, 1, 1, 1, 3])).Nonempty :=
  ⟨0, zero_mem_interior⟩

/-- **Ehrhart numerator of the six-dimensional counterexample simplex.** The full-dimensional
weighted simplex with weights $(1,1,1,1,1,3)$ has Ehrhart numerator
$1 + X + 2X^2 + X^3 + 2X^4 + X^5 + X^6$.

Source: S. Payne, *Ehrhart series and lattice triangulations*, Discrete Comput. Geom. 40 (2008),
365–376, Example 4.2 with $b = 3$, $k = 2$, $r = 0$ (the simplex and its numerator);
Benjamin Braun, Robert Davis, and Liam Solus, *Detecting the integer decomposition property and
Ehrhart unimodality in reflexive simplices*, Adv. in Appl. Math. 100 (2018), 122–142, Theorem 2.2
(the general formula and its fundamental-parallelepiped proof); restated by Benjamin Braun,
Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer Decomposition Property and
Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article A60, Theorem 5. -/
public theorem hibiWeightedSimplex_hStar :
    IsHStarPolynomial (weightedSimplex ![1, 1, 1, 1, 1, 3])
      (1 + Polynomial.X + 2 * Polynomial.X ^ 2 + Polynomial.X ^ 3 +
        2 * Polynomial.X ^ 4 + Polynomial.X ^ 5 + Polynomial.X ^ 6) := by
  unfold IsHStarPolynomial
  simp only [ehrhart_eq_latticeEnumerator, Fintype.card_fin]
  let G : PowerSeries ℤ := PowerSeries.mk fun n => ((6 + n).choose 6 : ℤ)
  have hG : G * (1 - PowerSeries.X) ^ 7 = 1 :=
    PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one ℤ 6
  have hseries : PowerSeries.mk (fun n =>
      (LatticePointEnumerator.latticeEnumerator 6 (weightedSimplex weights) n : ℤ)) =
        (∑ b : Fin 9, (PowerSeries.X : PowerSeries ℤ) ^ residueHeight b) * G := by
    ext n
    rw [PowerSeries.coeff_mk, latticeEnumerator_eq_sum, Nat.cast_sum, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm, PowerSeries.coeff_mul_X_pow']
    split_ifs <;> simp [G]
  change PowerSeries.mk (fun n =>
    (LatticePointEnumerator.latticeEnumerator 6 (weightedSimplex weights) n : ℤ)) *
      (1 - PowerSeries.X) ^ 7 = _
  rw [hseries, mul_assoc, hG, mul_one, ← numerator_eq]
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_pow, Polynomial.coe_X]

end

end MathlibExt.Combinatorics

@[expose] public section

namespace MathlibExt.Combinatorics.HibiSymmetricHStarUnimodalOWR741Problem003Wanted

open MetaMathlibExt

/-- The lattice polytope in `ℝ^d` spanned by the finite set `S ⊆ ℤ^d` of integer points. -/
def latticePolytope {d : ℕ} (S : Finset (Fin d → ℤ)) : Set (Fin d → ℝ) :=
  convexHull ℝ ((fun v : Fin d → ℤ => fun i => (v i : ℝ)) '' (S : Set (Fin d → ℤ)))

/-- **Hibi's conjecture on symmetric $h^*$-vectors.** For every natural number $d$, every finite
set $S \subseteq \mathbb{Z}^d$ whose convex hull $P \subseteq \mathbb{R}^d$ has nonempty interior,
and every polynomial $h = \sum_i h^*_i z^i \in \mathbb{Z}[z]$ that is an $h^*$-polynomial of $P$,
that is,
$$\Big(\sum_{t \ge 0} \#(tP \cap \mathbb{Z}^d)\, z^t\Big) (1 - z)^{d+1} = h(z)$$
as formal power series, if $h^*_i = h^*_{d-i}$ for all $0 \le i \le d$, then $h$ is unimodal.

This is Hibi's conjecture, Conjecture 2 of C. A. Athanasiadis's Oberwolfach report (Oberwolfach
Reports 1 (2004), no. 39, p. 2078), stated there for $d$-dimensional integral polytopes; every
such polytope is lattice-equivalent to a full-dimensional lattice polytope in $\mathbb{R}^d$. -/
def hibiSymmetricUnimodal : Prop :=
  ∀ (d : ℕ) (S : Finset (Fin d → ℤ)), (interior (latticePolytope S)).Nonempty →
    ∀ h : Polynomial ℤ, IsHStarPolynomial (latticePolytope S) h →
      (∀ i ≤ d, h.coeff i = h.coeff (d - i)) → IsUnimodal h

/--
**Hibi's conjecture on symmetric $h^*$-vectors is false.** There are a natural number $d$, a
finite set $S \subseteq \mathbb{Z}^d$ whose convex hull $P \subseteq \mathbb{R}^d$ has nonempty
interior, and a polynomial $h = \sum_i h^*_i z^i \in \mathbb{Z}[z]$ that is an $h^*$-polynomial
of $P$, that is,
$$\Big(\sum_{t \ge 0} \#(tP \cap \mathbb{Z}^d)\, z^t\Big) (1 - z)^{d+1} = h(z)$$
as formal power series, such that $h^*_i = h^*_{d-i}$ for all $0 \le i \le d$ but $h$ is not
unimodal.

Mustaţă and Payne (Example 1.1) give a reflexive $6$-dimensional lattice polytope with
$h^*$-vector $(1, 6, 8, 6, 8, 6, 1)$, which is symmetric and not unimodal.

Payne's Example 4.2 with $b = 3$, $k = 2$, and $r = 0$ gives another counterexample. In the
lattice basis $e_1,\ldots,e_5,-f$, where $f = (e_1 + \cdots + e_6)/3$, it is the weighted simplex
with weights $(1,1,1,1,1,3)$ and $h^*$-vector $(1,1,2,1,2,1,1)$; see
`MathlibExt.Combinatorics.hibiWeightedSimplex_hStar`.

Source: S. Payne, *Ehrhart series and lattice triangulations*, Discrete Comput. Geom. 40 (2008),
365–376, Example 4.2 and the proof of Theorem 1.4; C. A. Athanasiadis, On the unimodality of
h*-vectors, in Ehrhart Quasipolynomials: Algebra, Combinatorics, and Geometry, Oberwolfach Reports 1
(2004), no. 39, p. 2078, Conjecture 2, DOI 10.4171/OWR/2004/39; resolution: M. Mustaţă and S. Payne,
Ehrhart polynomials and stringy Betti numbers, Math. Ann. 333 (2005), 787-795, DOI
10.1007/s00208-005-0691-x, arXiv:math/0504486, Example
1.1: for f = (e1 + ... + e6)/3, N = ℤ⁶ + ℤ f and P the polytope with vertices e1, ..., e6, e1 - f,
..., e6 - f, P is reflexive with δ_P = (1, 6, 8, 6, 8, 6, 1), a counterexample to Hibi's conjecture
for d = 6 (abstract: 'counterexamples to Hibi's conjecture on the unimodality of delta-vectors of
reflexive polytopes'), https://arxiv.org/abs/math/0504486.
-/
public theorem hibiSymmetricUnimodal_refuted : ¬ hibiSymmetricUnimodal := by
  classical
  intro hibi
  -- Use the weighted simplex with vertex set {e₀, …, e₅, −(1, 1, 1, 1, 1, 3)}.
  let S : Finset (Fin 6 → ℤ) :=
    insert ![-1, -1, -1, -1, -1, -3] (Finset.univ.image fun i => Pi.single i 1)
  have hS : latticePolytope S = weightedSimplex ![1, 1, 1, 1, 1, 3] := by
    unfold latticePolytope S weightedSimplex
    congr 1
    rw [Finset.coe_insert, Finset.coe_image, Finset.coe_univ, Set.image_insert_eq,
      Set.image_image, Set.image_univ, Set.insert_eq, Set.union_comm]
    congr 1
    · congr 1
      funext j i
      by_cases h : i = j <;> simp [h]
    · congr 1
      funext i
      fin_cases i <;> norm_num
  let h : Polynomial ℤ := 1 + Polynomial.X + 2 * Polynomial.X ^ 2 + Polynomial.X ^ 3 +
    2 * Polynomial.X ^ 4 + Polynomial.X ^ 5 + Polynomial.X ^ 6
  have hStar : IsHStarPolynomial (latticePolytope S) h := by
    rw [hS]
    exact hibiWeightedSimplex_hStar
  have hSymm : ∀ i ≤ 6, h.coeff i = h.coeff (6 - i) := by
    intro i hi
    interval_cases i <;> norm_num only [h, Polynomial.coeff_add, Polynomial.coeff_one,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_ofNat_mul] <;> decide
  have hDip : h.coeff 2 = 2 ∧ h.coeff 3 = 1 ∧ h.coeff 4 = 2 := by
    norm_num only [h, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_ofNat_mul]
    decide
  obtain ⟨h₂, h₃, h₄⟩ := hDip
  have hdeg : 4 ≤ h.natDegree := Polynomial.le_natDegree_of_ne_zero (by rw [h₄]; decide)
  have hInterior : (interior (latticePolytope S)).Nonempty :=
    hS ▸ hibiWeightedSimplex_interior_nonempty
  obtain ⟨t, _, hinc, hdec⟩ := hibi 6 S hInterior h hStar hSymm
  by_cases ht : 3 ≤ t
  · have := hinc 2 3 (by decide) ht
    omega
  · have := hdec 3 4 (by omega) (by decide) hdeg
    omega

end MathlibExt.Combinatorics.HibiSymmetricHStarUnimodalOWR741Problem003Wanted

end
