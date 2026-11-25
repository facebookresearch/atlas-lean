/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The minimum valuation of complementary products plus one

Reducing the complementary-product identity modulo one prime power beyond the minimum
valuation shows that three entries cannot have valuation strictly above the fourth.
-/

namespace MetaMathlibExt

private theorem minTwice_of_sub_one_mul_eq {ℓ : ℕ} (hℓ : ℓ.Prime) (s : Fin 4 → ℕ)
    {v : Fin 4 → ℕ} (hv : ∀ i, v i = padicValNat ℓ (s i)) (hs : ∀ i, s i ≠ 0)
    (h : ((s 0 : ℤ) - 1) * ((s 3 : ℤ) - 1) = ((s 1 : ℤ) - 1) * ((s 2 : ℤ) - 1)) :
    (fun x : Fin 4 → ℕ => ∃ i j, i ≠ j ∧ x i = x j ∧ ∀ k, x i ≤ x k) v := by
  rw [funext hv]
  obtain ⟨i, -, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun k => padicValNat ℓ (s k)) Finset.univ_nonempty
  have hle (k : Fin 4) : padicValNat ℓ (s i) ≤ padicValNat ℓ (s k) :=
    hmin k (Finset.mem_univ k)
  by_contra hu
  let q := ℓ ^ (padicValNat ℓ (s i) + 1)
  let r (k : Fin 4) : ZMod q := s k
  have hdvd (k : Fin 4) : q ∣ s k ↔ padicValNat ℓ (s i) + 1 ≤ padicValNat ℓ (s k) := by
    rw [Nat.padicValNat_def (n := s k)]
    exact Nat.pow_dvd_iff_le_multiplicity (k := padicValNat ℓ (s i) + 1) hℓ.ne_one (hs k)
  have hz (k : Fin 4) (hk : i ≠ k) : r k = 0 :=
    (ZMod.natCast_eq_zero_iff (s k) q).2 <| (hdvd k).2 <|
      Nat.succ_le_of_lt (lt_of_le_of_ne (hle k) (fun he => hu ⟨i, k, hk, he, hle⟩))
  have hmod : (r 0 - 1) * (r 3 - 1) = (r 1 - 1) * (r 2 - 1) := by
    simpa only [r, map_mul, map_sub, map_one, map_natCast] using
      congrArg (Int.castRingHom (ZMod q)) h
  have vanish (w x y z : ZMod q) (he : (w - 1) * (x - 1) = (y - 1) * (z - 1))
      (hx : x = 0) (hy : y = 0) (hz' : z = 0) : w = 0 := by
    simpa [hx, hy, hz', sub_eq_add_neg, add_comm] using he
  have hi : r i = 0 := by
    fin_cases i
    · exact vanish _ _ _ _ hmod (hz 3 (by decide)) (hz 1 (by decide)) (hz 2 (by decide))
    · exact vanish _ _ _ _ hmod.symm (hz 2 (by decide)) (hz 0 (by decide)) (hz 3 (by decide))
    · exact vanish (r 2) _ _ _ ((mul_comm _ _).trans hmod.symm)
        (hz 1 (by decide)) (hz 0 (by decide)) (hz 3 (by decide))
    · exact vanish (r 3) _ _ _ ((mul_comm _ _).trans hmod)
        (hz 0 (by decide)) (hz 1 (by decide)) (hz 2 (by decide))
  exact Nat.not_succ_le_self _ ((hdvd i).1 ((ZMod.natCast_eq_zero_iff (s i) q).1 hi))

/-- **The two smallest valuations coincide.** Let $\ell$ be a prime and $a, b, c, d$ natural
numbers. Put $s_1 = ab + 1$, $s_2 = ac + 1$, $s_3 = ad + 1$, $s_4 = bc + 1$, $s_5 = bd + 1$,
$s_6 = cd + 1$, and let $v_i$ be the $\ell$-adic valuation of $s_i$. Then in each of the tuples
$(v_2, v_3, v_4, v_5)$, $(v_1, v_2, v_5, v_6)$ and $(v_1, v_3, v_4, v_6)$ the minimum value occurs
at two different positions.

Taking $\ell = p$ and $\ell = q$ gives the source's statements for the exponents of a
$\{p, q\}$-Diophantine quadruple. No Diophantine hypothesis is needed: the proof uses only the
identities $abcd = (s_1 - 1)(s_6 - 1) = (s_2 - 1)(s_5 - 1) = (s_3 - 1)(s_4 - 1)$.

Source: Volker Ziegler, *On the Existence of `{p, q}`-Diophantine Quadruples and Quintuples*,
INTEGERS 25 (2025), Article A92, Lemma 2, quoting Szalay and Ziegler (2013), Proposition 1
(`integers-2025-A92-lem-2`). -/
public theorem padicValNat_two_smallest_eq {ℓ : ℕ} (hℓ : ℓ.Prime) (a b c d : ℕ) :
    let v : Fin 6 → ℕ := ![padicValNat ℓ (a * b + 1), padicValNat ℓ (a * c + 1),
      padicValNat ℓ (a * d + 1), padicValNat ℓ (b * c + 1), padicValNat ℓ (b * d + 1),
      padicValNat ℓ (c * d + 1)]
    let minTwice : (Fin 4 → ℕ) → Prop := fun x => ∃ i j, i ≠ j ∧ x i = x j ∧ ∀ k, x i ≤ x k
    minTwice ![v 1, v 2, v 3, v 4] ∧ minTwice ![v 0, v 1, v 4, v 5] ∧
      minTwice ![v 0, v 2, v 3, v 5] := by
  intro v minTwice
  refine ⟨
    minTwice_of_sub_one_mul_eq hℓ ![a * c + 1, a * d + 1, b * c + 1, b * d + 1] ?_ ?_ ?_,
    minTwice_of_sub_one_mul_eq hℓ ![a * b + 1, a * c + 1, b * d + 1, c * d + 1] ?_ ?_ ?_,
    minTwice_of_sub_one_mul_eq hℓ ![a * b + 1, a * d + 1, b * c + 1, c * d + 1] ?_ ?_ ?_⟩
  all_goals
    first
    | intro i; fin_cases i <;> rfl
    | intro i; fin_cases i <;> exact Nat.succ_ne_zero _
    | simp only [Matrix.cons_val, Nat.cast_add, Nat.cast_mul, Nat.cast_one, add_sub_cancel_right]
      ring

end MetaMathlibExt
