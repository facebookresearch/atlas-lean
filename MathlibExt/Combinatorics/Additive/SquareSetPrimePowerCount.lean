/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.SquareWeightedZeroSum
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Algebra.BigOperators.Fin

/-!
# Counting nonzero squares modulo prime powers

## References

* Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
  Sequences 27 (2024), Article 24.6.6, pp. 1–16, §2, Theorem 6. The argument uses the valuation
  decomposition of Observation 3 and Lemma 4, and the count of each layer from Lemma 5.
* Santanu Mondal, Krishnendu Paul, and Shameek Paul, *Extremal Sequences for a Weighted Zero-Sum
  Constant*, Integers 22 (2022), Article A93, pp. 1–16, Lemma 7 (surjectivity of reduction on
  units and unit squares, cited by Paul and Paul in the introduction; for prime powers it follows
  directly from coprimality with the prime).
-/

namespace MetaMathlibExt

open scoped Pointwise

-- Reduction preserves divisibility by every power up to the modulus.
private theorem pow_dvd_zmod_val_iff {p r j a : ℕ} (hj : j ≤ r) :
    p ^ j ∣ (a : ZMod (p ^ r)).val ↔ p ^ j ∣ a := by
  simp only [ZMod.val_natCast, Nat.dvd_iff_mod_eq_zero, Nat.mod_mod_of_dvd _ (pow_dvd_pow p hj)]

private theorem scaled_unitSquare_val {p r k : ℕ} (hp : p.Prime) (hk : 2 * k < r)
    {x : ZMod (p ^ r)} (hx : x ∈ ((p : ZMod (p ^ r)) ^ (2 * k)) • unitSquareSet (p ^ r)) :
    p ^ (2 * k) ∣ x.val ∧ ¬p ^ (2 * k + 1) ∣ x.val := by
  have : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [Set.mem_smul_set] at hx
  obtain ⟨_, ⟨u, hu, rfl⟩, rfl⟩ := hx
  let a := (u ^ 2).val
  have hcast : (a : ZMod (p ^ r)) = u ^ 2 := ZMod.natCast_zmod_val _
  have ha : ¬p ∣ a := (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega)).mp
    (hcast ▸ hu.pow 2)
  rw [smul_eq_mul, ← hcast, ← Nat.cast_pow, ← Nat.cast_mul,
    pow_dvd_zmod_val_iff hk.le, pow_dvd_zmod_val_iff (Nat.succ_le_of_lt hk)]
  refine ⟨dvd_mul_right _ _, fun h => ha ?_⟩
  rw [pow_succ] at h
  exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos _) h

private theorem squareSet_eq_iUnion_scaled_unitSquares {p r : ℕ} (hp : p.Prime) (hr : 0 < r) :
    squareSet (p ^ r) = ⋃ k : Fin ((r + 1) / 2),
      ((p : ZMod (p ^ r)) ^ (2 * (k : ℕ))) • unitSquareSet (p ^ r) := by
  have : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  ext x
  rw [Set.mem_iUnion]
  constructor
  · rintro ⟨hx, y, rfl⟩
    let k := y.val.factorization p
    let a := y.val / p ^ k
    have hy : y.val ≠ 0 := by
      intro h
      apply hx
      rw [← ZMod.natCast_zmod_val y, h, Nat.cast_zero, zero_pow (by decide)]
    have hy' : p ^ k * a = y.val := Nat.ordProj_mul_ordCompl_eq_self _ _
    have ha : IsUnit (a : ZMod (p ^ r)) := by
      rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff hr]
      exact (Nat.coprime_ordCompl hp hy).symm
    have hsq : y ^ 2 = (p : ZMod (p ^ r)) ^ (2 * k) * (a : ZMod (p ^ r)) ^ 2 := by
      rw [show y = (p : ZMod (p ^ r)) ^ k * (a : ZMod (p ^ r)) by
        rw [← Nat.cast_pow, ← Nat.cast_mul, hy', ZMod.natCast_zmod_val],
        mul_pow, ← pow_mul']
    have hk : 2 * k < r := by
      by_contra! h
      have hz : ((p : ZMod (p ^ r)) ^ (2 * k)) = 0 := by
        rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
        exact pow_dvd_pow p h
      exact hx (by rw [hsq, hz, zero_mul])
    refine ⟨⟨k, by omega⟩, Set.mem_smul_set.mpr ⟨_, ⟨(a : ZMod (p ^ r)), ha, rfl⟩, ?_⟩⟩
    exact hsq.symm
  · rintro ⟨k, hx⟩
    have hk : 2 * (k : ℕ) < r := by omega
    have hval := (scaled_unitSquare_val hp hk hx).2
    refine ⟨fun h => hval (by simp [h]), ?_⟩
    rw [Set.mem_smul_set] at hx
    obtain ⟨_, ⟨u, _, rfl⟩, rfl⟩ := hx
    refine ⟨(p : ZMod (p ^ r)) ^ (k : ℕ) * u, ?_⟩
    rw [smul_eq_mul, mul_pow, ← pow_mul']

/-- **Number of nonzero squares modulo a prime power.** Let $p$ be a prime and $r \ge 1$, and write
$S(m)$ for the set of nonzero squares and $U(m)^2$ for the set of squares of units in
$\mathbb{Z}/m\mathbb{Z}$. If $r$ is even, then
$|S(p^r)| = \sum_{k=0}^{r/2-1} |U(p^{r-2k})^2|$, and if $r$ is odd, then
$|S(p^r)| = \sum_{k=0}^{(r-1)/2} |U(p^{r-2k})^2|$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Theorem 6. -/
public theorem ncard_squareSet_primePower (p r : ℕ) (hp : p.Prime) (hr : 0 < r) :
    (Even r → (squareSet (p ^ r)).ncard =
      ∑ k ∈ Finset.range (r / 2), (unitSquareSet (p ^ (r - 2 * k))).ncard) ∧
    (Odd r → (squareSet (p ^ r)).ncard =
      ∑ k ∈ Finset.range ((r + 1) / 2), (unitSquareSet (p ^ (r - 2 * k))).ncard) := by
  classical
  have : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let pieces (k : Fin ((r + 1) / 2)) :=
    ((p : ZMod (p ^ r)) ^ (2 * (k : ℕ))) • unitSquareSet (p ^ r)
  have hltDisj {i j : Fin ((r + 1) / 2)} (hij : i < j) : Disjoint (pieces i) (pieces j) := by
    apply Set.disjoint_left.mpr
    intro x hi hj
    have hv₁ := (scaled_unitSquare_val hp (show 2 * (i : ℕ) < r by omega) hi).2
    have hv₂ := (scaled_unitSquare_val hp (show 2 * (j : ℕ) < r by omega) hj).1
    have hlt : (i : ℕ) < (j : ℕ) := hij
    exact hv₁ ((pow_dvd_pow p (by omega)).trans hv₂)
  have hdisj : Pairwise (fun i j => Disjoint (pieces i) (pieces j)) := by
    intro i j hne
    obtain h | h := lt_or_gt_of_ne hne
    · exact hltDisj h
    · exact (hltDisj h).symm
  have hcount : (squareSet (p ^ r)).ncard =
      ∑ k ∈ Finset.range ((r + 1) / 2), (unitSquareSet (p ^ (r - 2 * k))).ncard := by
    calc
      _ = (⋃ k, pieces k).ncard := congrArg Set.ncard (squareSet_eq_iUnion_scaled_unitSquares hp hr)
      _ = ∑ k, (pieces k).ncard := by
        simp only [Set.ncard_eq_toFinset_card', Set.toFinset_iUnion]
        apply Finset.card_biUnion
        intro i _ j _ hij
        exact Finset.disjoint_left.mpr fun x hx hy =>
          Set.disjoint_left.mp (hdisj hij) (Set.mem_toFinset.mp hx) (Set.mem_toFinset.mp hy)
      _ = ∑ k : Fin ((r + 1) / 2), (unitSquareSet (p ^ (r - 2 * (k : ℕ)))).ncard := by
        exact Finset.sum_congr rfl fun k _ => ncard_scale_unitSquares_primePower p r k hp (by omega)
      _ = _ := Fin.sum_univ_eq_sum_range (fun k => (unitSquareSet (p ^ (r - 2 * k))).ncard) _
  refine ⟨fun he => ?_, fun _ => hcount⟩
  obtain ⟨a, ha⟩ := he
  simpa only [show (r + 1) / 2 = r / 2 by omega] using hcount

end MetaMathlibExt
