/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Van der Waerden-type vanishing for sum-plus-product families

Statements from Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden
Theorem to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25 (arXiv:2502.07921).
Labels follow the journal numbering (Lemmas 1-9); the arXiv version calls Lemmas 1-5 and
7-9 Propositions 1-5 and 7-9, and Lemma 6 Proposition 6.

A family `F = {f^(l)}_{l ≥ 2}` of functions `f^(l) : (ℤ/n)^l → M` is `m`-vanishing when
every sequence over `ℤ/n` contains `m` consecutive blocks of a common length `l > 1` on which
`f^(l)` vanishes, and vanishing when it is `m`-vanishing for every `m > 0`. Sequences are
indexed from `0` rather than `1`, which does not affect either property. Values of `f^(l)`
at `l < 2` never enter the definitions.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.ZMod.Basic

namespace MetaMathlibExt

@[expose] public section

/-- A family `F` of functions on blocks over `ℤ/n` is `m`-vanishing if every sequence `a`
over `ℤ/n` contains `m` consecutive blocks `(a (s + j l), …, a (s + j l + l - 1))`,
`j < m`, of a common length `l > 1` on each of which `F l` vanishes.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Section 2 (definition of
`m`-vanishing). -/
public def IsMVanishingFamily {n : ℕ} {M : Type*} [Zero M] (m : ℕ)
    (F : (l : ℕ) → (Fin l → ZMod n) → M) : Prop :=
  ∀ a : ℕ → ZMod n, ∃ l, 1 < l ∧ ∃ s, ∀ j < m, F l (fun i => a (s + j * l + i)) = 0

/-- A family is vanishing if it is `m`-vanishing for every positive `m`.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Section 2 (definition of
vanishing). -/
public def IsVanishingFamily {n : ℕ} {M : Type*} [Zero M]
    (F : (l : ℕ) → (Fin l → ZMod n) → M) : Prop :=
  ∀ m, 0 < m → IsMVanishingFamily m F

/-- The family `F_c = {(b_1, …, b_l) ↦ ∑ b_i + c ∏ b_i}` over `ℤ/n`.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Section 2 (the family
`F_c`). -/
public def sumAddMulProdFamily {n : ℕ} (c : ZMod n) (l : ℕ) (b : Fin l → ZMod n) :
    ZMod n :=
  ∑ i, b i + c * ∏ i, b i

/-- Being `m`-vanishing is inherited by every smaller `m'`.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Section 2 (definition of
`m`-vanishing). -/
public theorem IsMVanishingFamily.mono {n : ℕ} {M : Type*} [Zero M]
    {F : (l : ℕ) → (Fin l → ZMod n) → M} {m m' : ℕ} (h : IsMVanishingFamily m F)
    (hm : m' ≤ m) : IsMVanishingFamily m' F := by
  intro a
  obtain ⟨l, hl, s, hs⟩ := h a
  exact ⟨l, hl, s, fun j hj => hs j (lt_of_lt_of_le hj hm)⟩

/-- Every family is `0`-vanishing.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Section 2 (definition of
`m`-vanishing). -/
public theorem isMVanishingFamily_zero {n : ℕ} {M : Type*} [Zero M]
    (F : (l : ℕ) → (Fin l → ZMod n) → M) : IsMVanishingFamily 0 F :=
  fun _ => ⟨2, Nat.one_lt_two, 0, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩

/-- On blocks of length two, `F_c (b_0, b_1) = b_0 + b_1 + c b_0 b_1`.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Section 2 (the family
`F_c`). -/
public theorem sumAddMulProdFamily_two {n : ℕ} (c : ZMod n) (b : Fin 2 → ZMod n) :
    sumAddMulProdFamily c 2 b = b 0 + b 1 + c * (b 0 * b 1) := by
  simp [sumAddMulProdFamily, Fin.sum_univ_two, Fin.prod_univ_two]

/-- Theorem 1 (zero-sum form of van der Waerden's theorem): for a positive integer `n`,
the family `{(b_1, …, b_l) ↦ ∑ b_i}` over `ℤ/n` is vanishing.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Theorem 1
(`integers-2026-A25-thm-1`). -/
public theorem_wanted isVanishingFamily_sum {n : ℕ} (hn : 0 < n) :
    IsVanishingFamily (fun (l : ℕ) (b : Fin l → ZMod n) => ∑ i, b i)

/-- Theorem 2: for `n > 1` and `c ∈ ℤ/n ∖ {0, 1, -1}`, `F_c` is not `m`-vanishing for any
`m > 0`.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Theorem 2
(`integers-2026-A25-thm-2`). -/
public theorem_wanted not_isMVanishingFamily_sumAddMulProd_of_ne {n : ℕ} (hn : 1 < n)
    (c : ZMod n) (hc0 : c ≠ 0) (hc1 : c ≠ 1) (hcm1 : c ≠ -1) {m : ℕ} (hm : 0 < m) :
    ¬ IsMVanishingFamily m (sumAddMulProdFamily c)

/-- Theorem 3 (classification for `c = 1`), for `n > 1`: (a) if `n ∉ {2, 3, 4, 6, 8}`, then
`F_1` is not `m`-vanishing for any `m > 0`; (b) if `n ∈ {2, 3, 4, 8}`, then `F_1` is
vanishing; (c) if `n = 6`, then `F_1` is `1`-vanishing but not `m`-vanishing for any
`m > 1`.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Theorem 3
(`integers-2026-A25-thm-3`). -/
public theorem_wanted sumAddMulProd_one_classification {n : ℕ} (hn : 1 < n) :
    (n ∉ ({2, 3, 4, 6, 8} : Finset ℕ) →
      ∀ m, 0 < m → ¬ IsMVanishingFamily m (sumAddMulProdFamily (1 : ZMod n))) ∧
    (n ∈ ({2, 3, 4, 8} : Finset ℕ) → IsVanishingFamily (sumAddMulProdFamily (1 : ZMod n))) ∧
    (n = 6 → IsMVanishingFamily 1 (sumAddMulProdFamily (1 : ZMod n)) ∧
      ∀ m, 1 < m → ¬ IsMVanishingFamily m (sumAddMulProdFamily (1 : ZMod n)))

/-- Lemma 1: over `ℤ/3`, `F_1` is vanishing.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Lemma 1
(`integers-2026-A25-lem-1`). -/
public theorem_wanted isVanishingFamily_sumAddMulProd_one_three :
    IsVanishingFamily (sumAddMulProdFamily (1 : ZMod 3))

/-- Lemma 2: for `n ∈ {4, 8}`, `F_1` over `ℤ/n` is vanishing.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Lemma 2
(`integers-2026-A25-lem-2`). -/
public theorem_wanted isVanishingFamily_sumAddMulProd_one_four_eight {n : ℕ}
    (hn : n = 4 ∨ n = 8) : IsVanishingFamily (sumAddMulProdFamily (1 : ZMod n))

/-- Lemma 3: over `ℤ/6`, `F_1` is `1`-vanishing.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Lemma 3
(`integers-2026-A25-lem-3`). -/
public theorem_wanted isMVanishingFamily_one_sumAddMulProd_one_six :
    IsMVanishingFamily 1 (sumAddMulProdFamily (1 : ZMod 6))

/-- Lemma 4: over `ℤ/6` and for `m > 1`, neither `F_{-1}` nor `F_1` is `m`-vanishing.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Lemma 4
(`integers-2026-A25-lem-4`). -/
public theorem_wanted not_isMVanishingFamily_sumAddMulProd_six {m : ℕ} (hm : 1 < m) :
    ¬ IsMVanishingFamily m (sumAddMulProdFamily (-1 : ZMod 6)) ∧
      ¬ IsMVanishingFamily m (sumAddMulProdFamily (1 : ZMod 6))

/-- Lemma 5: for a prime `n ≡ 1 (mod 4)`, `F_1` over `ℤ/n` is not `m`-vanishing for any
`m > 0`.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Lemma 5
(`integers-2026-A25-lem-5`), quoting Theorem 3.6 of Bialostocki and Dierker. -/
public theorem_wanted not_isMVanishingFamily_sumAddMulProd_one_prime_one_mod_four {n : ℕ}
    (hp : n.Prime) (h4 : n % 4 = 1) {m : ℕ} (hm : 0 < m) :
    ¬ IsMVanishingFamily m (sumAddMulProdFamily (1 : ZMod n))

/-- Lemma 6: for a prime `n > 3` with `n ≡ 3 (mod 4)` there are nonzero `x, y ∈ ℤ/n` and
`r ∈ {2, 3}` with `x + r y = 0` and `x y^r = 1`. The record's garbled `xy r = 1` is read
as `x y^r = 1`, as in the proof (`x y^2 = x^3 / 4 = 1` in its first case).

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Lemma 6
(`integers-2026-A25-lem-6`). -/
public theorem_wanted exists_add_mul_eq_zero_mul_pow_eq_one {n : ℕ} (hp : n.Prime)
    (h3 : 3 < n) (h4 : n % 4 = 3) :
    ∃ x y : ZMod n, x ≠ 0 ∧ y ≠ 0 ∧ ∃ r : ℕ, (r = 2 ∨ r = 3) ∧
      x + r * y = 0 ∧ x * y ^ r = 1

/-- Lemma 7: for a prime `n > 3` with `n ≡ 3 (mod 4)`, `F_1` over `ℤ/n` is not
`m`-vanishing for any `m > 0`.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Lemma 7
(`integers-2026-A25-lem-7`). -/
public theorem_wanted not_isMVanishingFamily_sumAddMulProd_one_prime_three_mod_four
    {n : ℕ} (hp : n.Prime) (h3 : 3 < n) (h4 : n % 4 = 3) {m : ℕ} (hm : 0 < m) :
    ¬ IsMVanishingFamily m (sumAddMulProdFamily (1 : ZMod n))

/-- Lemma 8: for `n = 8u` with `u > 1`, `F_1` over `ℤ/n` is not `m`-vanishing for any
`m > 0`.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Lemma 8
(`integers-2026-A25-lem-8`). -/
public theorem_wanted not_isMVanishingFamily_sumAddMulProd_one_eight_mul {u : ℕ}
    (hu : 1 < u) {m : ℕ} (hm : 0 < m) :
    ¬ IsMVanishingFamily m (sumAddMulProdFamily (1 : ZMod (8 * u)))

/-- Lemma 9: for `n = 9u` with `u > 0`, `F_1` over `ℤ/n` is not `m`-vanishing for any
`m > 0`.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Lemma 9
(`integers-2026-A25-lem-9`). -/
public theorem_wanted not_isMVanishingFamily_sumAddMulProd_one_nine_mul {u : ℕ}
    (hu : 0 < u) {m : ℕ} (hm : 0 < m) :
    ¬ IsMVanishingFamily m (sumAddMulProdFamily (1 : ZMod (9 * u)))

/-- Theorem 4: for `n = p^k` with `p` prime and `k > 0`, `F_{-1}` over `ℤ/n` is vanishing.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Theorem 4
(`integers-2026-A25-thm-4`). -/
public theorem_wanted isVanishingFamily_sumAddMulProd_neg_one_prime_pow {p k : ℕ}
    (hp : p.Prime) (hk : 0 < k) :
    IsVanishingFamily (sumAddMulProdFamily (-1 : ZMod (p ^ k)))

/-- Theorem 6: for positive integers `n`, `d` and maps `g_1, …, g_d : ℤ/n → ℤ/n`, the family
`F(g_1, …, g_d) = {(b_1, …, b_l) ↦ (∑ g_1(b_i), …, ∑ g_d(b_i))}` is vanishing (a block
counts when all `d` coordinates vanish). The hypothesis `d > 0` is dropped: for `d = 0`
the statement is trivial.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Theorem 6
(`integers-2026-A25-thm-6`). -/
public theorem_wanted isVanishingFamily_transformation_sums {n d : ℕ} (hn : 0 < n)
    (g : Fin d → ZMod n → ZMod n) :
    IsVanishingFamily (fun (l : ℕ) (b : Fin l → ZMod n) (t : Fin d) => ∑ i, g t (b i))

end

end MetaMathlibExt
