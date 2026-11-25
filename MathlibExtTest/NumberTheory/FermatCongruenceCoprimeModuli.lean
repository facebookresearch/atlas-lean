/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.FermatCongruenceCoprimeModuli

open MetaMathlibExt

-- For distinct primes `p < q`, Fermat's little theorem for `p` and for `q` gives both
-- equalities in `ZMod (p * q)`.
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (a : ℤ)
    (ha : IsCoprime a ((p : ℤ) * q)) :
    (a : ZMod (p * q)) ^ (q - 1) =
        ((a : ZMod (p * q)) ^ (q - p) - 1) * ((q - p : ℕ) : ZMod (p * q))⁻¹ * p +
          (a : ZMod (p * q)) ^ (q - p) ∧
      ((a : ZMod (p * q)) ^ (q - p) - 1) * ((q - p : ℕ) : ZMod (p * q))⁻¹ * p +
          (a : ZMod (p * q)) ^ (q - p) =
        ((a : ZMod (p * q)) ^ (q - p) - 1) * ((q - p : ℕ) : ZMod (p * q))⁻¹ * q + 1 :=
  (forall_fermat_congruence_iff_of_coprime hp.pos hpq ((Nat.coprime_primes hp hq).mpr hpq.ne)).mpr
    ⟨fun _ hb ↦ Int.ModEq.pow_card_sub_one_eq_one hp hb,
      fun _ hb ↦ Int.ModEq.pow_card_sub_one_eq_one hq hb⟩ a ha

-- At `n = 1` every congruence modulo `n` holds, so the equalities characterize the Fermat
-- property of `m` alone.
example {m : ℕ} (hm : 1 < m) :
    (∀ a : ℤ, IsCoprime a (((1 : ℕ) : ℤ) * m) →
        ((a : ZMod (1 * m)) ^ (m - 1) =
            ((a : ZMod (1 * m)) ^ (m - 1) - 1) * ((m - 1 : ℕ) : ZMod (1 * m))⁻¹ * (1 : ℕ) +
              (a : ZMod (1 * m)) ^ (m - 1) ∧
          ((a : ZMod (1 * m)) ^ (m - 1) - 1) * ((m - 1 : ℕ) : ZMod (1 * m))⁻¹ * (1 : ℕ) +
              (a : ZMod (1 * m)) ^ (m - 1) =
            ((a : ZMod (1 * m)) ^ (m - 1) - 1) * ((m - 1 : ℕ) : ZMod (1 * m))⁻¹ * m + 1)) ↔
      ∀ a : ℤ, IsCoprime a (m : ℤ) → a ^ (m - 1) ≡ 1 [ZMOD m] :=
  (forall_fermat_congruence_iff_of_coprime one_pos hm (Nat.coprime_one_left m)).trans
    ⟨And.right, fun h ↦ ⟨fun _ _ ↦ Int.modEq_one, h⟩⟩

-- `4` lacks the Fermat property (`7 ^ 3 ≡ 3 [ZMOD 4]`), so for `n = 3` and `m = 4` the
-- equalities fail for some integer coprime to `12`.
example : ¬∀ a : ℤ, IsCoprime a (((3 : ℕ) : ℤ) * ((4 : ℕ) : ℤ)) →
    ((a : ZMod (3 * 4)) ^ (4 - 1) =
        ((a : ZMod (3 * 4)) ^ (4 - 3) - 1) * ((4 - 3 : ℕ) : ZMod (3 * 4))⁻¹ * (3 : ℕ) +
          (a : ZMod (3 * 4)) ^ (4 - 3) ∧
      ((a : ZMod (3 * 4)) ^ (4 - 3) - 1) * ((4 - 3 : ℕ) : ZMod (3 * 4))⁻¹ * (3 : ℕ) +
          (a : ZMod (3 * 4)) ^ (4 - 3) =
        ((a : ZMod (3 * 4)) ^ (4 - 3) - 1) * ((4 - 3 : ℕ) : ZMod (3 * 4))⁻¹ * (4 : ℕ) + 1) := by
  intro h
  obtain ⟨-, h4⟩ :=
    (forall_fermat_congruence_iff_of_coprime (by decide) (by decide) (by norm_num)).mp h
  have h7 : IsCoprime (7 : ℤ) ((4 : ℕ) : ℤ) := ⟨-1, 2, by norm_num⟩
  exact absurd (h4 7 h7) (by decide)
