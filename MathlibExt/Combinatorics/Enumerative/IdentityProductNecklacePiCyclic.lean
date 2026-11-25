/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Set.Card
public import Mathlib.Data.ZMod.Basic
public import MathlibExt.Combinatorics.Enumerative.TupleRotationOrbit
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import MathlibExt.Combinatorics.Enumerative.IdentityProductNecklace

/-!
# Identity-product necklaces over a product of cyclic groups

Let `G = C_{k_1} × ⋯ × C_{k_m}` be a finite product of cyclic groups, written here as
`∀ i : Fin m, Multiplicative (ZMod (k i))` with every `k i` positive. For `n ≥ 1`, the number of
identity-product `n`-necklaces over `G`, that is, of rotation orbits (`tupleRotationOrbit`) of
`n`-tuples over `G` whose entries multiply to `1`, is
$$\frac{1}{n} \sum_{d \mid n} \varphi(n/d) \prod_{i=1}^{m} \gcd(k_i, n/d)\, k_i^{d-1}.$$
This is Corollary 3.2 of the arXiv text of Darij Grinberg and Peter Mao, *Necklaces over a Group
with Identity Product* (arXiv:2405.08937v4), published in the Journal of Integer Sequences 29
(2026), Article 26.4.6.

The proof follows theirs. It specialises their count for an arbitrary finite group (Theorem 3.1
of the arXiv text), `MetaMathlibExt.identity_product_necklace_count`, whose necklaces are written
with explicit shifts of indices; the rotation orbits `tupleRotationOrbit x` are the same sets.
In `G`, the order is `k_1 ⋯ k_m`, and `g ^ e = 1` holds coordinatewise, so the number of solutions
of `g ^ e = 1` is the product over `i` of the number of solutions in `C_{k_i}`. That number is
`gcd(k_i, e)` (Lemma 4.6 of the arXiv text), here because the kernel of the `e`-th power map of a
finite cyclic group of order `a` has `gcd(a, e)` elements (`IsCyclic.card_powMonoidHom_ker`).

## Main statements

* `MetaMathlibExt.identityProductNecklace_count_pi_cyclic`: the formula above.
-/

namespace MetaMathlibExt

/-- **Counting solutions of $x^b = 1$ in a cyclic group.** For natural numbers $a \ge 1$ and
$b$, the cyclic group of order $a$ has exactly $\gcd(a, b)$ elements $x$ with $x^b = 1$.

The paper takes $b$ positive; for $b = 0$ both sides equal $a$.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Lemma 12
(`jis-2026-26.4.6-lem-12`). -/
public theorem card_pow_eq_one_zmod (a b : ℕ) [NeZero a] :
    Fintype.card {x : Multiplicative (ZMod a) // x ^ b = 1} = Nat.gcd a b := by
  rw [← Nat.card_eq_fintype_card]
  have h := IsCyclic.card_powMonoidHom_ker (G := Multiplicative (ZMod a)) b
  rw [Nat.card_eq_fintype_card (α := Multiplicative (ZMod a)), Fintype.card_multiplicative,
    ZMod.card] at h
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [MonoidHom.mem_ker])

namespace identityProductNecklace_count_pi_cyclic

/-- Rotating the indices `m` times by `finRotate n` adds `m` to them, modulo `n`. -/
private theorem finRotate_pow_apply_val {n : ℕ} (m : ℕ) (i : Fin n) :
    (((finRotate n) ^ m) i : ℕ) = (i.val + m) % n := by
  induction m with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ m ih =>
    have := i.neZero
    rw [pow_succ', Equiv.Perm.mul_apply, finRotate_apply, Fin.val_add, ih, Fin.val_one',
      Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

/-- The rotation orbit of a tuple is the set of its shifts by `m < n` positions, written as in
`MetaMathlibExt.identity_product_necklace_count`. -/
private theorem tupleRotationOrbit_eq_shifts {α : Type*} {n : ℕ} (hn : 0 < n) (x : Fin n → α) :
    tupleRotationOrbit x =
      {y | ∃ m : ℕ, m < n ∧ ∀ i : Fin n, y i = x ⟨(i.val + m) % n, Nat.mod_lt _ hn⟩} := by
  ext y
  constructor
  · rintro ⟨m, rfl⟩
    refine ⟨m % n, Nat.mod_lt _ hn, fun i => congrArg x (Fin.ext ?_)⟩
    rw [finRotate_pow_apply_val]
    exact (Nat.add_mod_mod _ _ _).symm
  · rintro ⟨m, -, hm⟩
    exact ⟨m, funext fun i =>
      (hm i).trans (congrArg x (Fin.ext (finRotate_pow_apply_val m i).symm))⟩

/-- In `C_{k_1} × ⋯ × C_{k_m}`, the equation `g ^ e = 1` has `∏ i, gcd(k_i, e)` solutions. -/
private theorem card_pow_eq_one_pi {m : ℕ} (k : Fin m → ℕ) [∀ i, NeZero (k i)] (e : ℕ) :
    Nat.card {g : ∀ i, Multiplicative (ZMod (k i)) // g ^ e = 1} = ∏ i, Nat.gcd (k i) e := by
  rw [Nat.card_congr ((Equiv.subtypeEquivRight fun g => ?_).trans
    (Equiv.subtypePiEquivPi (p := fun i (x : Multiplicative (ZMod (k i))) => x ^ e = 1))),
    Nat.card_pi]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.card_eq_fintype_card]
    exact card_pow_eq_one_zmod (k i) e
  · simp [funext_iff]

end identityProductNecklace_count_pi_cyclic

open identityProductNecklace_count_pi_cyclic

/-- **Identity-product necklaces over a product of cyclic groups.** Let $k_1, \dots, k_m$ be
positive integers and let $G = C_{k_1} \times \dots \times C_{k_m}$, where $C_k$ is the cyclic
group $\mathbb{Z} / k\mathbb{Z}$ written multiplicatively. For $n \ge 1$, the number of rotation
orbits of $n$-tuples $(x_1, \dots, x_n) \in G^n$ with $x_1 x_2 \cdots x_n = 1$ (identity-product
$n$-necklaces) is
$$\frac{1}{n} \sum_{d \mid n} \varphi(n/d) \prod_{i=1}^{m} \gcd(k_i, n/d)\, k_i^{d-1},$$
where $\varphi$ is Euler's totient function.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Corollary 6
(`jis-2026-26.4.6-cor-6`). -/
public theorem identityProductNecklace_count_pi_cyclic (m : ℕ) (k : Fin m → ℕ)
    [∀ i, NeZero (k i)] (n : ℕ) (hn : 0 < n) :
    (Set.ncard {O : Set (Fin n → ∀ i, Multiplicative (ZMod (k i))) |
        ∃ x, (List.ofFn x).prod = 1 ∧ O = tupleRotationOrbit x} : ℚ) =
      (1 / n : ℚ) * ∑ d ∈ n.divisors, (Nat.totient (n / d) : ℚ) *
        ∏ i, ((Nat.gcd (k i) (n / d) : ℚ) * (k i : ℚ) ^ (d - 1)) := by
  classical
  simp_rw [tupleRotationOrbit_eq_shifts hn]
  rw [identity_product_necklace_count _ n hn]
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [mul_assoc, Finset.prod_mul_distrib, Finset.prod_pow, ← Nat.card_eq_fintype_card,
    card_pow_eq_one_pi, Fintype.card_pi]
  simp [ZMod.card]

end MetaMathlibExt
