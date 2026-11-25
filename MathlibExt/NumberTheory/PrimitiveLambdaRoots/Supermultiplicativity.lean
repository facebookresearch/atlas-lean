/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PrimitiveLambdaRoots
import Mathlib.Data.Set.Card

/-!
# Inequalities for primitive λ-roots modulo n

The number of primitive λ-roots is supermultiplicative on coprime moduli greater than one.
Equality holds exactly when one of the moduli is two.
-/

public section

namespace MathlibExt.NumberTheory.PrimitiveLambdaRootsWanted

open ArithmeticFunction

-- Halving the order with smaller 2-adic valuation preserves the lcm.
private theorem lcm_half_left {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hd : 2 ∣ a)
    (hv : a.factorization 2 ≤ b.factorization 2) :
    (a / 2).lcm b = a.lcm b := by
  have hhalf : a / 2 ≠ 0 := (Nat.div_pos (Nat.le_of_dvd ha.bot_lt hd) (by decide)).ne'
  apply Nat.eq_of_factorization_eq (Nat.lcm_ne_zero hhalf hb) (Nat.lcm_ne_zero ha hb)
  intro p
  rw [Nat.factorization_lcm hhalf hb, Nat.factorization_lcm ha hb, Nat.factorization_div hd,
    Finsupp.sup_apply, Finsupp.sup_apply, Finsupp.tsub_apply]
  by_cases hp : p = 2
  · subst p
    rw [sup_of_le_right (le_trans (Nat.sub_le ..) hv), sup_of_le_right hv]
  · simp [Nat.prime_two.factorization, Ne.symm hp]

-- A primitive pair can have an imprimitive first component: square a maximal-order unit
-- on the side where halving its order leaves the lcm unchanged.
private theorem exists_extra_pair {m n : ℕ} [NeZero m] [NeZero n] (hm : 2 < m)
    (hv : (carmichael m).factorization 2 ≤ (carmichael n).factorization 2) :
    ∃ (x : (ZMod m)ˣ) (y : (ZMod n)ˣ),
      (orderOf x).lcm (orderOf y) = (carmichael m).lcm (carmichael n) ∧
        orderOf x ≠ carmichael m := by
  have : Fact (1 < m) := ⟨by omega⟩
  obtain ⟨x, hx⟩ := Monoid.exists_orderOf_eq_exponent (G := (ZMod m)ˣ) .of_finite
  obtain ⟨y, hy⟩ := Monoid.exists_orderOf_eq_exponent (G := (ZMod n)ˣ) .of_finite
  rw [← carmichael_eq_exponent'] at hx hy
  have hd : 2 ∣ carmichael m := by
    have h := orderOf_dvd_of_pow_eq_one (pow_carmichael (-1 : (ZMod m)ˣ))
    simpa [Units.orderOf_neg_one, ZMod.ringChar_zmod_n, hm.ne'] using h
  have hpos := orderOf_pos x
  refine ⟨x ^ 2, y, ?_⟩
  rw [orderOf_pow_of_dvd (by decide : 2 ≠ 0) (hx ▸ hd), hx, hy]
  exact ⟨lcm_half_left (hx ▸ hpos.ne') (hy ▸ (orderOf_pos y).ne') hd hv,
    (Nat.div_lt_self (hx ▸ hpos) (by decide)).ne⟩

/-- **Supermultiplicativity of the number of primitive λ-roots.** Let $R(n)$ be the number of
primitive λ-roots modulo $n$. For coprime natural numbers $m, n > 1$, we have
$R(m)\,R(n) \le R(mn)$, and $R(mn) = R(m)\,R(n)$ if and only if $m = 2$ and $n$ is odd, or
$n = 2$ and $m$ is odd.

Source: Benjamin Huang and Shuguang Li, "Notes on the Number of
Primitive λ-roots mod n and Its Multiplicative Properties",
Theorem 1. -/
theorem primitiveLambdaRootCount_mul_ge_and_eq_iff
    (m n : ℕ) (hm : 1 < m) (hn : 1 < n) (hcop : Nat.Coprime m n) :
    primitiveLambdaRootCount m * primitiveLambdaRootCount n ≤
        primitiveLambdaRootCount (m * n) ∧
      (primitiveLambdaRootCount (m * n) =
          primitiveLambdaRootCount m * primitiveLambdaRootCount n ↔
        (m = 2 ∧ Odd n) ∨ (n = 2 ∧ Odd m)) := by
  wlog hv : (carmichael m).factorization 2 ≤ (carmichael n).factorization 2 generalizing m n
  · have h := this n m hn hm hcop.symm (by omega)
    rwa [Nat.mul_comm n m, Nat.mul_comm (primitiveLambdaRootCount n), or_comm] at h
  have : NeZero m := ⟨by omega⟩
  have : NeZero n := ⟨by omega⟩
  let roots (k : ℕ) := {x : (ZMod k)ˣ | orderOf x = carmichael k}
  let pairs := {z : (ZMod m)ˣ × (ZMod n)ˣ |
    (orderOf z.1).lcm (orderOf z.2) = (carmichael m).lcm (carmichael n)}
  have hcount : primitiveLambdaRootCount (m * n) = pairs.ncard := by
    let e := (Units.mapEquiv (ZMod.chineseRemainder hcop).toMulEquiv).trans .prodUnits
    apply Nat.card_congr (e.toEquiv.subtypeEquiv ?_)
    intro x
    change orderOf x = carmichael (m * n) ↔
      (orderOf (e x).1).lcm (orderOf (e x).2) = (carmichael m).lcm (carmichael n)
    rw [← Prod.orderOf, e.orderOf_eq, carmichael_mul hcop]
  have hsub : roots m ×ˢ roots n ⊆ pairs := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact congrArg₂ Nat.lcm hx hy
  rw [hcount]
  change (roots m).ncard * (roots n).ncard ≤ pairs.ncard ∧
    (pairs.ncard = (roots m).ncard * (roots n).ncard ↔ _)
  rw [← Set.ncard_prod]
  refine ⟨Set.ncard_le_ncard hsub, ?_, ?_⟩
  · intro heq
    have hm₂ : m = 2 := by
      by_contra hne
      obtain ⟨x, y, hxy, hx⟩ := exists_extra_pair (by omega : 2 < m) hv
      have hsets := Set.eq_of_subset_of_ncard_le hsub heq.le
      have hmem : (x, y) ∈ roots m ×ˢ roots n := hsets ▸ hxy
      exact hx hmem.1
    exact Or.inl ⟨hm₂, (hm₂ ▸ hcop : Nat.Coprime 2 n).odd_of_left⟩
  · intro h
    apply congrArg Set.ncard (Set.Subset.antisymm ?_ hsub)
    rintro ⟨x, y⟩ hxy
    change (orderOf x).lcm (orderOf y) = (carmichael m).lcm (carmichael n) at hxy
    change orderOf x = carmichael m ∧ orderOf y = carmichael n
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · simpa [Subsingleton.elim x 1, carmichael_two] using hxy
    · simpa [Subsingleton.elim y 1, carmichael_two] using hxy

end MathlibExt.NumberTheory.PrimitiveLambdaRootsWanted
