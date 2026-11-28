/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import MathlibExt.Data.Set.Density
public import MathlibExt.NumberTheory.StrongPseudoprime
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.SumTwoSquares
import MathlibExt.NumberTheory.FermatNumbersModPrime
import MathlibExt.NumberTheory.PrimeCounting.LandauRamanujan

/-!
# Density of odd composites whose strong pseudoprime bases do not form a subgroup

If an odd composite `n` has a prime divisor congruent to `3` modulo `4`, its strong
pseudoprime bases form a subgroup of `(ZMod n)ˣ`: they are the preimage of the two global
signs under the power map with exponent the odd part of `n - 1`. Thus any exceptional
odd composite is a sum of two squares, and Landau's asymptotic gives density zero.
The paper uses the group of Fermat pseudoprime bases as the ambient group. Since all
strong pseudoprime bases are Fermat pseudoprime bases, this is equivalent to asking
whether they form a subgroup of the full unit group.

## References

* Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
  Article A23, pp. 1–10, proof of Theorem 4 and Corollary 2.
* E. Landau, *Über die Einteilung der positiven ganzen Zahlen in vier Klassen nach der
  Mindestzahl der zu ihrer additiven Zusammensetzung erforderlichen Quadrate*,
  Archiv der Mathematik und Physik (3) 13 (1908), pp. 305–312. The counting asymptotic is
  `landau_ramanujan_asymptotic` in `MathlibExt.NumberTheory.PrimeCounting.LandauRamanujan`.
-/

open Filter Set Topology

namespace MetaMathlibExt

private theorem subgroup_of_primeFactor_mod_four_eq_three {n p : ℕ}
    (hn : 1 < n) (hcomp : ¬n.Prime) (hodd : Odd n) (hp : p ∈ n.primeFactors) (hp4 : p % 4 = 3) :
    ∃ H : Subgroup (ZMod n)ˣ, ∀ u : (ZMod n)ˣ, u ∈ H ↔ IsStrongPseudoprime n (u : ZMod n) := by
  obtain ⟨k, d, hd, hnd⟩ := Nat.exists_eq_two_pow_mul_odd (n := n - 1) (by omega)
  have hk : 0 < k := by
    by_contra! h
    have : k = 0 := by omega
    simp [this] at hnd
    have := Nat.odd_iff.mp hodd
    have := Nat.odd_iff.mp hd
    omega
  have hnsq : ¬IsSquare (-1 : ZMod n) := fun hs =>
    (Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one hp hs) hp4
  let signs := Subgroup.zpowers (-1 : (ZMod n)ˣ)
  refine ⟨signs.comap (powMonoidHom d), fun u => ?_⟩
  have hsigns (v : (ZMod n)ˣ) : v ∈ signs ↔ (v : ZMod n) = 1 ∨ (v : ZMod n) = -1 := by
    change v ∈ Subgroup.zpowers (-1 : (ZMod n)ˣ) ↔ _
    rw [Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨j, rfl⟩
      rw [neg_one_zpow_eq_ite]
      split <;> simp [Units.val_neg]
    · rintro (hv | hv)
      · exact ⟨0, Units.ext (by simpa using hv.symm)⟩
      · exact ⟨1, Units.ext (by simpa [Units.val_neg] using hv.symm)⟩
  rw [Subgroup.mem_comap, hsigns]
  change (u : ZMod n) ^ d = 1 ∨ (u : ZMod n) ^ d = -1 ↔ _
  constructor
  · rintro (h | h)
    · exact ⟨hn, hcomp, hodd, k, d, hnd, hd, Or.inl h⟩
    · exact ⟨hn, hcomp, hodd, k, d, hnd, hd, Or.inr ⟨0, hk, by simpa using h⟩⟩
  · rintro ⟨_, _, _, k', d', hnd', hd', hu⟩
    have hd_eq := ((Nat.two_pow_mul_odd_inj hd' hd).mp (hnd'.symm.trans hnd)).2
    subst d'
    rcases hu with h | ⟨i, _, hi⟩
    · exact Or.inl h
    cases i with
    | zero => exact Or.inr (by simpa using hi)
    | succ i =>
      exfalso
      apply hnsq
      refine ⟨(u : ZMod n) ^ (2 ^ i * d), ?_⟩
      rw [← sq, ← pow_mul, show (2 ^ i * d) * 2 = 2 ^ (i + 1) * d by rw [pow_succ]; ac_rfl]
      exact hi.symm

/-- **Strong pseudoprime bases almost always form a subgroup.** The set of odd composite natural
numbers $n$ for which the units $b$ of $\mathbb{Z}/n\mathbb{Z}$ such that $n$ is a strong
pseudoprime to the base $b$ do not form a subgroup of the unit group has natural density $0$.

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, Corollary 2 (`integers-2024-A23-cor-2`). -/
public theorem hasDensity_zero_strongPseudoprime_bases_not_subgroup :
    Set.HasDensity {n : ℕ | 1 < n ∧ ¬n.Prime ∧ Odd n ∧
      ¬∃ H : Subgroup (ZMod n)ˣ, ∀ u : (ZMod n)ˣ,
        u ∈ H ↔ IsStrongPseudoprime n (u : ZMod n)} 0 := by
  let count (x : ℝ) := ({m : ℕ | (m : ℝ) ≤ x ∧ ∃ a b : ℕ, m = a ^ 2 + b ^ 2}.ncard : ℝ)
  obtain ⟨c, _, hc⟩ := landau_ramanujan_asymptotic
  have hsmall : Tendsto (fun x : ℝ => c * x / Real.sqrt (Real.log x) / x) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := c)).div_atTop
      (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    change c / Real.sqrt (Real.log x) = c * x / Real.sqrt (Real.log x) / x
    rw [div_div, mul_div_mul_right _ _ hx.ne']
  have hratio : Asymptotics.IsEquivalent atTop (fun x : ℝ => count x / x)
      (fun x : ℝ => c * x / Real.sqrt (Real.log x) / x) :=
    hc.div (Asymptotics.IsEquivalent.refl (u := fun x : ℝ => x))
  have hcount : Tendsto (fun x : ℝ => count x / x) atTop (𝓝 0) := hratio.symm.tendsto_nhds hsmall
  simp only [HasDensity, partialDensity, inter_univ, univ_inter, ncard_Iio_nat]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hcount.comp (tendsto_natCast_atTop_atTop (R := ℝ))) (fun _ => by positivity) fun N => ?_
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply Nat.cast_le.mpr
  apply ncard_le_ncard
  · rintro m ⟨⟨hm, hcomp, hodd, hsub⟩, hlt⟩
    refine ⟨by exact_mod_cast (mem_Iio.mp hlt).le, Nat.eq_sq_add_sq_iff.mpr fun p hp hp4 => ?_⟩
    exact (hsub <| subgroup_of_primeFactor_mod_four_eq_three hm hcomp hodd hp hp4).elim
  · refine (finite_Iic ⌊(N : ℝ)⌋₊).subset fun m hm => ?_
    exact Nat.le_floor hm.1

end MetaMathlibExt
