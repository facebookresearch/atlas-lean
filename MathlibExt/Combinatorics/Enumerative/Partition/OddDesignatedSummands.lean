/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProductCongruence
import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Topology.Instances.ZMod
import MathlibExt.Combinatorics.Enumerative.Partition.RamanujanPartitionCongruence

/-!
# Odd arguments of the designated-summand partition function

The counts at `4n + 3`, `6n + 3` and `6n + 5` are divisible by four. Modulo four,
Jacobi's cube identity expresses `fₖ³` as a sum over triangular numbers. Writing
`T(z) = 2z² + z` for their bilateral enumeration, we split `T(x) + 3T(y)` by parity.
After cancellation of Euler factors the odd part of the counting series is `X * f₁₂²`.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

@[expose] public section

local notation "𝔣" => qEulerProduct

/-- **Generating function of odd designated-summand partitions.** For $k \ge 1$ let
$f_k = \prod_{m \ge 1} (1 - q^{km})$ be the Euler product. This is the integer power series
$f_4 f_6^2 / (f_1 f_3 f_{12})$ in $q$, where the denominator $f_1 f_3 f_{12}$ is invertible
because its constant coefficient is $1$. It is the generating function
$\sum_{n \ge 0} \mathrm{PD}_2(n) q^n$ of the numbers $\mathrm{PD}_2(n)$ of partitions of $n$ with
designated summands into odd parts.

Source: James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for 2-Regular
Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16, Section 2, eq. (1)
(quoting G. E. Andrews, R. P. Lewis, and J. Lovejoy, *Partitions with designated summands*,
Acta Arith. 105 (2002)). -/
noncomputable def oddDesignatedSummandsSeries : ℤ⟦X⟧ :=
  𝔣 4 * 𝔣 6 ^ 2 * invOfUnit (𝔣 1 * 𝔣 3 * 𝔣 12) 1

/-- **The odd designated-summand partition function.** For a natural number $n$, the integer
$\mathrm{PD}_2(n)$ is defined as the coefficient of $q^n$ in the integer power series
$f_4 f_6^2 / (f_1 f_3 f_{12})$, where $f_k = \prod_{m \ge 1} (1 - q^{km})$ is the Euler product
(the denominator has constant coefficient $1$, so it is invertible). It counts the partitions of
$n$ with designated summands in which all parts are odd.

Source: James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for 2-Regular
Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16, Sections 1-2, eq. (1). -/
noncomputable def oddDesignatedSummandsCount (n : ℕ) : ℤ :=
  coeff n oddDesignatedSummandsSeries

/-- **Generating function for partitions with designated summands into odd parts.** Let
$f_k = \prod_{m \ge 1} (1 - q^{km})$ in the ring of integer power series in $q$, and let $PD_2(n)$
be the number of partitions of $n$ with designated summands in which every part is odd, defined as
the coefficient of $q^n$ in $f_4 f_6^2 / (f_1 f_3 f_{12})$. Then
$f_1 f_3 f_{12} \sum_{n \ge 0} PD_2(n) q^n = f_4 f_6^2$.

Source: James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for 2-Regular
Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16, Section 2, eq. (1). -/
theorem oddDesignatedSummandsCount_generatingFunction :
    𝔣 1 * 𝔣 3 * 𝔣 12 * PowerSeries.mk oddDesignatedSummandsCount = 𝔣 4 * 𝔣 6 ^ 2 := by
  have hmk : PowerSeries.mk oddDesignatedSummandsCount = oddDesignatedSummandsSeries := by
    ext n
    simp [oddDesignatedSummandsCount]
  have hc : constantCoeff (𝔣 1 * 𝔣 3 * 𝔣 12) = ((1 : ℤˣ) : ℤ) := by
    simp [constantCoeff_qEulerProduct (le_refl 1),
      constantCoeff_qEulerProduct (by norm_num : 1 ≤ 3),
      constantCoeff_qEulerProduct (by norm_num : 1 ≤ 12)]
  rw [hmk, oddDesignatedSummandsSeries, mul_left_comm, mul_invOfUnit _ _ hc, mul_one]

/-- **Odd designated-summand partitions of zero.** The odd designated-summand partition function
satisfies $\mathrm{PD}_2(0) = 1$.

Source: James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for 2-Regular
Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16, Section 2, eq. (1). -/
theorem oddDesignatedSummandsCount_zero : oddDesignatedSummandsCount 0 = 1 := by
  have h := congrArg (coeff 0) oddDesignatedSummandsCount_generatingFunction
  simp only [coeff_zero_eq_constantCoeff, map_mul, map_pow,
    constantCoeff_qEulerProduct (le_refl 1), constantCoeff_qEulerProduct (by norm_num : 1 ≤ 3),
    constantCoeff_qEulerProduct (by norm_num : 1 ≤ 12),
    constantCoeff_qEulerProduct (by norm_num : 1 ≤ 4),
    constantCoeff_qEulerProduct (by norm_num : 1 ≤ 6), one_pow, one_mul] at h
  simpa using h

end

namespace oddDesignatedSummandsCount_odd_args_mod_four

private abbrev S := (ZMod 4)⟦X⟧

private noncomputable abbrev red := PowerSeries.map (Int.castRingHom (ZMod 4))

private noncomputable abbrev F (k : ℕ) : S := red (qEulerProduct k)

private lemma expand_continuous {R : Type*} [CommRing R] [TopologicalSpace R]
    (k : ℕ) (hk : k ≠ 0) : Continuous (expand k hk : R⟦X⟧ → R⟦X⟧) := by
  rw [continuous_iff_continuousAt]
  intro f
  rw [ContinuousAt, WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  by_cases h : k ∣ n
  · simpa [coeff_expand, h] using (WithPiTopology.continuous_coeff R (n / k)).tendsto f
  · simpa [coeff_expand, h] using (tendsto_const_nhds (x := (0 : R)) (f := nhds f))

private lemma expand_F (k : ℕ) (hk : k ≠ 0) : expand k hk (F 1) = F k := by
  rw [F, ← map_expand, qEulerProduct_one]
  congr 1
  have h := (WithPiTopology.hasProd_one_sub_X_pow ℤ).map (expand k hk) (expand_continuous k hk)
  simpa [qEulerProduct, Function.comp_def, pow_mul] using h.tprod_eq.symm

private lemma fourth {k : ℕ} (hk : 0 < k) : F k ^ 4 = F (k * 2) ^ 2 := by
  ext n
  simp only [F, ← map_pow, coeff_map, Int.coe_castRingHom]
  apply (ZMod.intCast_eq_intCast_iff _ _ 4).mpr
  simpa using qEulerProduct_iterated_primePower_congruence 2 2 k 1 1
    Nat.prime_two hk (by decide) (by decide) (by decide) n

private lemma unit_F {k : ℕ} (hk : 0 < k) : IsUnit (F k) := by
  apply IsUnit.map red
  rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_qEulerProduct hk]
  exact isUnit_one

/-- A bilateral indexing of the triangular numbers. -/
private def tri (z : ℤ) : ℕ := (2 * z * z + z).toNat

private lemma cast_tri (z : ℤ) : (tri z : ℤ) = 2 * z * z + z := by
  apply Int.toNat_of_nonneg
  rcases le_or_gt 0 z with h | h
  · positivity
  · nlinarith [mul_nonneg_of_nonpos_of_nonpos (show z + 1 ≤ 0 by omega) h.le]

private def triIndex : ℤ ≃ ℕ where
  toFun z := if 0 ≤ z then (2 * z).toNat else (-2 * z - 1).toNat
  invFun n := if n % 2 = 0 then (n / 2 : ℕ) else -((n / 2 : ℕ) : ℤ) - 1
  left_inv z := by dsimp only; split_ifs <;> omega
  right_inv n := by dsimp only; split_ifs <;> omega

private lemma tri_eq_choose (z : ℤ) : tri z = ((triIndex z + 1).choose 2) := by
  have h := congrArg ((↑) : ℕ → ℤ) (two_mul_choose_two_succ (triIndex z))
  push_cast at h
  apply Int.ofNat_inj.mp
  rw [cast_tri]
  simp only [triIndex, Equiv.coe_fn_mk] at h ⊢
  split_ifs at h ⊢ with hz <;> rw [Int.toNat_of_nonneg (by omega)] at h <;> linarith

private lemma jacobi_weight (t : ℕ) : (-1 : ZMod 4) ^ t * (2 * t + 1) = 1 := by
  induction t with
  | zero => simp
  | succ t ih =>
    push_cast
    rw [pow_succ]
    have h4 : (4 : ZMod 4) = 0 := rfl
    linear_combination -((-1 : ZMod 4) ^ t * (t + 1)) * h4 + ih

private lemma tri_sum_one : HasSum (fun z : ℤ ↦ (X : S) ^ tri z) (F 1 ^ 3) := by
  have hs := PowerSeries.hasSum_of_monomials_self (F 1 ^ 3)
  have hc (n : ℕ) : coeff n (F 1 ^ 3) = ((jacobiCubeSeries.coeff n : ℤ) : ZMod 4) := by
    simp [F, red, ← map_pow, qEulerProduct_one, pentagonalSeries_pow_three]
  have hm : StrictMono (fun t : ℕ ↦ (t + 1).choose 2) := by
    intro a b hab
    nlinarith [two_mul_choose_two_succ a, two_mul_choose_two_succ b,
      Nat.mul_self_lt_mul_self hab]
  have h := (hm.injective.hasSum_iff (f := fun d ↦ monomial d (coeff d (F 1 ^ 3))) (by
    intro d hd
    rw [hc, coeff_jacobiCubeSeries_eq_zero (fun t ht ↦ hd ⟨t, ht⟩)]
    simp)).mpr hs
  have h := (triIndex.hasSum_iff).mpr h
  refine h.congr_fun fun z ↦ ?_
  rw [tri_eq_choose, X_pow_eq]
  simp [Function.comp_def, hc, coeff_jacobiCubeSeries_triangle, jacobi_weight]

private lemma tri_sum (k : ℕ) (hk : k ≠ 0) :
    HasSum (fun z : ℤ ↦ (X : S) ^ (k * tri z)) (F k ^ 3) := by
  simpa [Function.comp_def, pow_mul, expand_F] using
    tri_sum_one.map (expand k hk) (expand_continuous k hk)

private def sq (z : ℤ) := (z * z).toNat

private lemma cast_sq (z : ℤ) : (sq z : ℤ) = z * z :=
  Int.toNat_of_nonneg (mul_self_nonneg z)

private def Bounds (e : ℤ → ℕ) : Prop := ∀ z, -(e z : ℤ) ≤ z ∧ z ≤ e z

private lemma bounds_tri : Bounds tri := by
  intro z
  rw [cast_tri]
  rcases le_or_gt 0 z with h | h
  · constructor <;> nlinarith [sq_nonneg z]
  · constructor <;> nlinarith [mul_nonneg_of_nonpos_of_nonpos (show z + 1 ≤ 0 by omega) h.le]

private lemma bounds_sq : Bounds sq := by
  intro z
  rw [cast_sq]
  rcases le_or_gt 1 z with h | h
  · constructor <;> nlinarith [mul_nonneg (show 0 ≤ z - 1 by omega) (show 0 ≤ z by omega)]
  · by_cases h0 : z = 0
    · simp [h0]
    · constructor <;> nlinarith [mul_nonneg_of_nonpos_of_nonpos (show z + 1 ≤ 0 by omega)
        (show z ≤ 0 by omega)]

private lemma Bounds.scale {e : ℤ → ℕ} (he : Bounds e) {k : ℕ} (hk : 0 < k) :
    Bounds (fun z ↦ k * e z) := by
  intro z
  have h := he z
  have h' : e z ≤ k * e z := Nat.le_mul_of_pos_left _ hk
  dsimp only
  omega

private noncomputable def theta (k : ℕ) : S := ∑' z : ℤ, X ^ (k * sq z)

private lemma theta_sum {k : ℕ} (hk : 0 < k) :
    HasSum (fun z : ℤ ↦ (X : S) ^ (k * sq z)) (theta k) := by
  apply Summable.hasSum
  refine (WithPiTopology.summable_iff_summable_coeff _).mpr fun d ↦
    summable_of_hasFiniteSupport ((Set.finite_Icc (-(d : ℤ)) d).subset ?_)
  intro z hz
  have h := (bounds_sq.scale hk) z
  have hd : d = k * sq z := by
    by_contra hn
    exact hz (by simp [coeff_X_pow, hn])
  simpa only [hd, Set.mem_Icc] using h

private lemma pair_sum {e f : ℤ → ℕ} {a b : S} (he : Bounds e) (hf : Bounds f)
    (ha : HasSum (fun z : ℤ ↦ (X : S) ^ e z) a) (hb : HasSum (fun z : ℤ ↦ (X : S) ^ f z) b) :
    HasSum (fun p : ℤ × ℤ ↦ (X : S) ^ (e p.1 + f p.2)) (a * b) := by
  simp_rw [pow_add]
  apply ha.mul hb
  refine (WithPiTopology.summable_iff_summable_coeff _).mpr fun d ↦ summable_of_hasFiniteSupport
    (((Set.finite_Icc (-(d : ℤ)) d).prod (Set.finite_Icc (-(d : ℤ)) d)).subset ?_)
  rintro ⟨x, y⟩ h
  have hd : d = e x + f y := by
    by_contra hn
    exact h (by simp [← pow_add, coeff_X_pow, hn])
  have hx := he x
  have hy := hf y
  change (_ ≤ x ∧ x ≤ _) ∧ (_ ≤ y ∧ y ≤ _)
  omega

/-- Select the one of the two triangular indices with the requested parity. -/
private def foldTri (a z : ℤ) := if a % 2 = 0 then 2 * z else -2 * z - 1

private def unfoldTri (b : ℤ) := if b % 2 = 0 then b / 2 else -(b + 1) / 2

private lemma fold_unfold (a b : ℤ) (h : a % 2 = b % 2) : foldTri a (unfoldTri b) = b := by
  unfold foldTri unfoldTri
  split_ifs <;> omega

private lemma unfold_fold (a z : ℤ) : unfoldTri (foldTri a z) = z := by
  unfold foldTri unfoldTri
  split_ifs <;> omega

private lemma fold_parity (a z : ℤ) : foldTri a z % 2 = a % 2 := by
  unfold foldTri
  split_ifs <;> omega

private lemma fold_weight (a z : ℤ) :
    foldTri a z * (foldTri a z + 1) = 2 * (tri z : ℤ) := by
  rw [cast_tri]
  unfold foldTri
  split_ifs <;> ring

/-- Write a pair of triangular indices in terms of their difference and their sum. -/
private def squareEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun := fun (a, z) ↦ ((foldTri a z + a) / 2, (foldTri a z - a) / 2)
  invFun := fun (x, y) ↦ (x - y, unfoldTri (x + y))
  left_inv := by
    rintro ⟨a, z⟩
    have hp := fold_parity a z
    dsimp
    refine Prod.ext (by omega) ?_
    rw [show (foldTri a z + a) / 2 + (foldTri a z - a) / 2 = foldTri a z by omega, unfold_fold]
  right_inv := by
    rintro ⟨x, y⟩
    dsimp
    rw [fold_unfold _ _ (by omega)]
    exact Prod.ext (by omega) (by omega)

private lemma square_weight (a z : ℤ) :
    tri (squareEquiv (a, z)).1 + tri (squareEquiv (a, z)).2 = sq a + 2 * tri z := by
  generalize hxy : squareEquiv (a, z) = p
  obtain ⟨x, y⟩ := p
  have hp := fold_parity a z
  have hx : 2 * x = foldTri a z + a := by
    have := congrArg Prod.fst hxy
    dsimp [squareEquiv] at this
    omega
  have hy : 2 * y = foldTri a z - a := by
    have := congrArg Prod.snd hxy
    dsimp [squareEquiv] at this
    omega
  apply Int.ofNat_inj.mp
  push_cast
  rw [cast_tri, cast_tri, cast_sq, ← fold_weight a z]
  have hsum : foldTri a z = x + y := by omega
  have hdiff : a = x - y := by omega
  rw [hsum, hdiff]
  ring

private lemma square_identity (k : ℕ) (hk : 0 < k) :
    F k ^ 3 * F k ^ 3 = theta k * F (2 * k) ^ 3 := by
  have h2 : 0 < 2 * k := by omega
  have hs := pair_sum (bounds_tri.scale hk) (bounds_tri.scale hk)
    (tri_sum k hk.ne') (tri_sum k hk.ne')
  have ht := pair_sum (bounds_sq.scale hk) (bounds_tri.scale h2) (theta_sum hk)
    (tri_sum _ h2.ne')
  apply ((squareEquiv.hasSum_iff).mpr hs).unique
  refine ht.congr_fun fun (a, z) ↦ ?_
  simp only [Function.comp_apply]
  congr 1
  linear_combination k * square_weight a z

/-- The identity `2(T(x) + 3T(y)) + 1 = (x + 3y + 1)² + 3(x - y)²` separates two
parity classes. One of the two linear forms is even and the other is odd. Halving the
even one gives the square index, and folding the odd one gives the triangular index. -/
private def parityEquiv : (ℤ × ℤ) ⊕ (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun := Sum.elim
    (fun (a, z) ↦ ((foldTri a z + 3 * a) / 2, (foldTri a z - a) / 2))
    (fun (a, z) ↦ ((a + 3 * foldTri (a + 1) z + 1) / 2, (a - foldTri (a + 1) z - 1) / 2))
  invFun := fun (x, y) ↦ if (x - y) % 2 = 0 then
    .inl ((x - y) / 2, unfoldTri ((x + 3 * y) / 2))
    else .inr ((x + 3 * y + 1) / 2, unfoldTri ((x - y - 1) / 2))
  left_inv := by
    rintro (⟨a, z⟩ | ⟨a, z⟩)
    · dsimp
      have hp := fold_parity a z
      rw [ite_eq_left (by omega)]
      congr 2
      · omega
      · rw [show ((foldTri a z + 3 * a) / 2 + 3 * ((foldTri a z - a) / 2)) / 2 =
            foldTri a z by omega, unfold_fold]
    · dsimp
      have hp := fold_parity (a + 1) z
      rw [ite_eq_right (by omega)]
      congr 2
      · omega
      · rw [show ((a + 3 * foldTri (a + 1) z + 1) / 2 - (a - foldTri (a + 1) z - 1) / 2 - 1) / 2 =
            foldTri (a + 1) z by omega, unfold_fold]
  right_inv := by
    rintro ⟨x, y⟩
    dsimp
    split_ifs <;> dsimp <;> rw [fold_unfold _ _ (by omega)] <;> exact Prod.ext (by omega) (by omega)

private lemma even_weight (a z : ℤ) :
    let p := parityEquiv (.inl (a, z))
    tri p.1 + 3 * tri p.2 = 6 * sq a + 4 * tri z := by
  dsimp only
  generalize hxy : parityEquiv (.inl (a, z)) = p
  obtain ⟨x, y⟩ := p
  have hp := fold_parity a z
  have hx := congrArg Prod.fst hxy
  have hy := congrArg Prod.snd hxy
  dsimp [parityEquiv] at hx hy
  have hs : 2 * foldTri a z = x + 3 * y := by omega
  have hd : 2 * a = x - y := by omega
  apply Int.ofNat_inj.mp
  push_cast
  rw [cast_tri, cast_tri, cast_sq]
  have hw := fold_weight a z
  nlinarith only [hw, congrArg (· ^ 2) hs, congrArg (· ^ 2) hd, hs]

private lemma odd_weight (a z : ℤ) :
    let p := parityEquiv (.inr (a, z))
    tri p.1 + 3 * tri p.2 = 1 + (2 * sq a + 12 * tri z) := by
  dsimp only
  generalize hxy : parityEquiv (.inr (a, z)) = p
  obtain ⟨x, y⟩ := p
  have hp := fold_parity (a + 1) z
  have hx := congrArg Prod.fst hxy
  have hy := congrArg Prod.snd hxy
  dsimp [parityEquiv] at hx hy
  have hs : 2 * a = x + 3 * y + 1 := by omega
  have hd : 2 * foldTri (a + 1) z = x - y - 1 := by omega
  apply Int.ofNat_inj.mp
  push_cast
  rw [cast_tri, cast_tri, cast_sq]
  have hw := fold_weight (a + 1) z
  nlinarith only [hw, congrArg (· ^ 2) hs, congrArg (· ^ 2) hd, hd]

private lemma dissection :
    F 1 ^ 3 * F 3 ^ 3 = theta 6 * F 4 ^ 3 + X * (theta 2 * F 12 ^ 3) := by
  have hs := pair_sum (bounds_tri.scale (by decide : 0 < 1)) (bounds_tri.scale (by decide : 0 < 3))
    (tri_sum 1 one_ne_zero) (tri_sum 3 (by decide))
  have he := pair_sum (bounds_sq.scale (by decide : 0 < 6)) (bounds_tri.scale (by decide : 0 < 4))
    (theta_sum (by decide : 0 < 6)) (tri_sum 4 (by decide))
  have ho := pair_sum (bounds_sq.scale (by decide : 0 < 2)) (bounds_tri.scale (by decide : 0 < 12))
    (theta_sum (by decide : 0 < 2)) (tri_sum 12 (by decide))
  apply (parityEquiv.hasSum_iff.mpr hs).unique
  apply HasSum.sum
  · refine he.congr_fun fun (a, z) ↦ ?_
    simp only [Function.comp_apply, one_mul, even_weight]
  · refine (ho.mul_left X).congr_fun fun (a, z) ↦ ?_
    simp only [Function.comp_apply, one_mul]
    rw [odd_weight, pow_add, pow_one]

private lemma theta_two_mul : theta 2 * F 4 = F 2 ^ 2 := by
  apply ((unit_F (by decide : 0 < 4)).pow 2).mul_right_cancel
  calc
    theta 2 * F 4 * F 4 ^ 2 = theta 2 * F 4 ^ 3 := by ring
    _ = F 2 ^ 3 * F 2 ^ 3 := (square_identity 2 (by decide)).symm
    _ = F 2 ^ 2 * F 2 ^ 4 := by ring
    _ = _ := by rw [fourth (by decide : 0 < 2)]

private lemma expand_F_mul (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    expand a ha (F b) = F (a * b) := by
  rw [← expand_F b hb, ← expand_mul, expand_F]

private lemma expand_theta : expand 2 two_ne_zero (theta 3) = theta 6 := by
  have h := (theta_sum (by decide : 0 < 3)).map (expand 2 two_ne_zero)
    (expand_continuous 2 two_ne_zero)
  apply h.unique
  simpa [Function.comp_def, ← pow_mul, ← Nat.mul_assoc] using theta_sum (by decide : 0 < 6)

/-- After reduction modulo four the entire odd part is `X * f₁₂²`. -/
private lemma odd_part : ∃ E : S,
    red oddDesignatedSummandsSeries = expand 2 two_ne_zero E + X * F 12 ^ 2 := by
  let P := red oddDesignatedSummandsSeries
  have hg : F 1 * F 3 * F 12 * P = F 4 * F 6 ^ 2 := by
    have hmk : PowerSeries.mk oddDesignatedSummandsCount = oddDesignatedSummandsSeries := by
      ext n
      simp [oddDesignatedSummandsCount]
    simpa only [hmk, map_mul, map_pow] using
      congrArg red oddDesignatedSummandsCount_generatingFunction
  have hscale : F 2 ^ 2 * F 12 * P = F 4 * (F 1 ^ 3 * F 3 ^ 3) := by
    apply ((unit_F (by decide : 0 < 6)).pow 2).mul_right_cancel
    calc
      F 2 ^ 2 * F 12 * P * F 6 ^ 2 = F 1 ^ 4 * F 12 * P * F 3 ^ 4 := by
        rw [fourth (by decide : 0 < 1), fourth (by decide : 0 < 3)]
      _ = (F 1 * F 3 * F 12 * P) * (F 1 ^ 3 * F 3 ^ 3) := by ring
      _ = _ := by rw [hg]; ring
  let D : Sˣ := (((unit_F (by decide : 0 < 1)).pow 2).mul (unit_F (by decide : 0 < 6))).unit
  refine ⟨theta 3 * F 2 ^ 4 * (↑D⁻¹ : S), ?_⟩
  have hD : expand 2 two_ne_zero (↑D⁻¹ : S) * (F 2 ^ 2 * F 12) = 1 := by
    have h := congrArg (expand 2 two_ne_zero) D.inv_mul
    rw [map_mul, map_one] at h
    have hval : (D : S) = F 1 ^ 2 * F 6 := IsUnit.unit_spec _
    rwa [hval, map_mul, map_pow, expand_F, expand_F_mul 2 6 two_ne_zero (by decide)] at h
  apply (((unit_F (by decide : 0 < 2)).pow 2).mul (unit_F (by decide : 0 < 12))).mul_right_cancel
  change P * _ = _
  rw [map_mul, map_mul, map_pow, expand_theta, expand_F_mul 2 2 two_ne_zero two_ne_zero]
  change P * _ = (theta 6 * F 4 ^ 4 * _ + X * F 12 ^ 2) * _
  calc
    P * (F 2 ^ 2 * F 12) = F 4 * (F 1 ^ 3 * F 3 ^ 3) := by simpa [mul_comm P] using hscale
    _ = theta 6 * F 4 ^ 4 + X * (theta 2 * F 4) * F 12 ^ 3 := by rw [dissection]; ring
    _ = _ := by rw [theta_two_mul, add_mul, mul_assoc (theta 6 * F 4 ^ 4), hD]; ring

private lemma coeff_vanish (m : ℕ) (hm : ¬ 2 ∣ m + 1) (hm' : ¬ 12 ∣ m) :
    oddDesignatedSummandsCount (m + 1) ≡ 0 [ZMOD 4] := by
  obtain ⟨E, hE⟩ := odd_part
  apply (ZMod.intCast_eq_intCast_iff _ _ 4).mp
  have h := congrArg (coeff (m + 1)) hE
  rw [map_add, coeff_expand_of_not_dvd _ _ _ hm, zero_add, ← pow_one (X : S),
    coeff_X_pow_mul, ← expand_F 12 (by decide), ← map_pow, coeff_expand_of_not_dvd _ _ _ hm'] at h
  simpa [red, oddDesignatedSummandsCount] using h

end oddDesignatedSummandsCount_odd_args_mod_four

open oddDesignatedSummandsCount_odd_args_mod_four in
/-- **Congruences modulo 4 for $\mathrm{PD}_2$ at $4n + 3$, $6n + 3$ and $6n + 5$.** Write
$\mathrm{PD}_2(m)$ for the number of partitions of $m$ with designated summands in which every part
is odd. For every natural number $n$, $\mathrm{PD}_2(4n + 3)$, $\mathrm{PD}_2(6n + 3)$ and
$\mathrm{PD}_2(6n + 5)$ are all congruent to $0$ modulo $4$.

Source: James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for 2-Regular
Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16, Corollary 1
(`integers-2024-A16-cor-1`). -/
public theorem oddDesignatedSummandsCount_odd_args_mod_four (n : ℕ) :
    oddDesignatedSummandsCount (4 * n + 3) ≡ 0 [ZMOD 4] ∧
      oddDesignatedSummandsCount (6 * n + 3) ≡ 0 [ZMOD 4] ∧
      oddDesignatedSummandsCount (6 * n + 5) ≡ 0 [ZMOD 4] := by
  exact ⟨coeff_vanish (4 * n + 2) (by omega) (by omega),
    coeff_vanish (6 * n + 2) (by omega) (by omega),
    coeff_vanish (6 * n + 4) (by omega) (by omega)⟩

end MetaMathlibExt
