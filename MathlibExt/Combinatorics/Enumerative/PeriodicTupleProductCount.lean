/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Set.Card
public import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.OfFn

/-!
# Periodic tuples with product in a conjugation-closed set

Let `G` be a finite group, `K ⊆ G`, `n ≥ 1` and `k` a divisor of `n`. An `n`-tuple
`x : Fin n → G` is invariant under rotation by `k` positions, `x ∘ finRotate n ^ k = x`, when
`x_{i+k} = x_i` for all `i`, indices taken modulo `n`. The number of such tuples whose entries
multiply, in order, to an element of `K` is `#{a ∈ G | a ^ (n / k) ∈ K} * |G| ^ (k - 1)`. This is
Lemma 8.4 of the arXiv text of Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity
Product* (arXiv:2405.08937v4), published in the Journal of Integer Sequences 29 (2026),
Article 26.4.6.

The proof follows theirs, which is the proof of their Lemma 5.1 (the case `K = {1}`) with `1`
replaced by `K`. Such a tuple is the `n / k`-fold repetition (`Fin.repeat`) of its first `k`
entries, so its product is the `(n / k)`-th power of the product `h` of these entries. The last
`k - 1` of these entries are arbitrary, and together with `h` they determine the first one. The
paper assumes throughout its Section 8 that `K` is closed under conjugation; this count does not
use that hypothesis.

## Main statements

* `MetaMathlibExt.card_productIn_period`: the count above.
-/

namespace MetaMathlibExt

namespace card_productIn_period

/-- Rotating the indices `m` times by `finRotate n` adds `m` to them, modulo `n`. -/
private theorem finRotate_pow_apply_val {n : ℕ} (m : ℕ) (i : Fin n) :
    (((finRotate n) ^ m) i : ℕ) = (i.val + m) % n := by
  induction m with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ m ih =>
    have := i.neZero
    rw [pow_succ', Equiv.Perm.mul_apply, finRotate_apply, Fin.val_add, ih, Fin.val_one',
      Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

/-- The `m`-fold repetition of a `k`-tuple is invariant under rotation by `k` positions. -/
private theorem repeat_comp_finRotate_pow {α : Type*} (m k : ℕ) (y : Fin k → α) :
    Fin.repeat m y ∘ ⇑((finRotate (m * k)) ^ k) = Fin.repeat m y := by
  funext i
  simp only [Function.comp_apply, Fin.repeat_apply]
  congr 1
  ext
  rw [Fin.coe_modNat, Fin.coe_modNat, finRotate_pow_apply_val,
    Nat.mod_mod_of_dvd _ (dvd_mul_left k m), Nat.add_mod_right]

/-- A tuple of length `m * k` that is invariant under rotation by `k` positions is the `m`-fold
repetition of its first `k` entries. -/
private theorem repeat_eq_of_comp_finRotate_pow {α : Type*} {m k : ℕ} (hk : k ≤ m * k)
    (x : Fin (m * k) → α) (hx : x ∘ ⇑((finRotate (m * k)) ^ k) = x) :
    Fin.repeat m (fun j => x (Fin.castLE hk j)) = x := by
  have hpow : ∀ q : ℕ, x ∘ ⇑((finRotate (m * k)) ^ (k * q)) = x := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [mul_add_one, pow_add, Equiv.Perm.coe_mul, ← Function.comp_assoc, ih, hx]
  funext i
  have hq := congrFun (hpow (i.val / k)) (Fin.castLE hk i.modNat)
  change x (Fin.castLE hk i.modNat) = x i
  rw [← hq, Function.comp_apply]
  congr 1
  ext
  rw [finRotate_pow_apply_val, Fin.val_castLE, Fin.coe_modNat, Nat.mod_add_div,
    Nat.mod_eq_of_lt i.isLt]

/-- The product of the `m`-fold repetition of a tuple is the `m`-th power of its product. -/
private theorem prod_ofFn_repeat {M : Type*} [Monoid M] (m : ℕ) {k : ℕ} (y : Fin k → M) :
    (List.ofFn (Fin.repeat m y)).prod = (List.ofFn y).prod ^ m := by
  rw [List.ofFn_fin_repeat, List.prod_flatten, List.map_replicate, List.prod_replicate]

/-- A `(k + 1)`-tuple over a group is determined by its product and its last `k` entries. -/
private def prodTailEquiv (G : Type*) [Group G] (k : ℕ) :
    (Fin (k + 1) → G) ≃ G × (Fin k → G) where
  toFun y := ((List.ofFn y).prod, Fin.tail y)
  invFun p := Fin.cons (p.1 * ((List.ofFn p.2).prod)⁻¹) p.2
  left_inv y := by
    change Fin.cons ((List.ofFn y).prod * ((List.ofFn (Fin.tail y)).prod)⁻¹) (Fin.tail y) = y
    rw [List.ofFn_succ, List.prod_cons]
    exact (congrArg (Fin.cons · (Fin.tail y)) (mul_inv_cancel_right _ _)).trans
      (Fin.cons_self_tail y)
  right_inv p := by
    obtain ⟨a, t⟩ := p
    change ((List.ofFn (Fin.cons (a * ((List.ofFn t).prod)⁻¹) t : Fin (k + 1) → G)).prod,
      Fin.tail (Fin.cons (a * ((List.ofFn t).prod)⁻¹) t : Fin (k + 1) → G)) = (a, t)
    rw [List.ofFn_succ, List.prod_cons, Fin.cons_zero, Fin.tail_cons]
    simp only [Fin.cons_succ, inv_mul_cancel_right]

/-- The `(k + 1)`-tuples over a finite group `G` whose product `h` satisfies `h ^ m ∈ K` number
`#{a ∈ G | a ^ m ∈ K} * |G| ^ k`. -/
private theorem ncard_prod_pow_mem (G : Type*) [Group G] [Fintype G] (K : Set G) (m k : ℕ) :
    Set.ncard {y : Fin (k + 1) → G | (List.ofFn y).prod ^ m ∈ K} =
      Set.ncard {a : G | a ^ m ∈ K} * Fintype.card G ^ k := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    Nat.card_congr (((prodTailEquiv G k).subtypeEquiv
      (p := fun y => y ∈ {y : Fin (k + 1) → G | (List.ofFn y).prod ^ m ∈ K})
      (q := fun p : G × (Fin k → G) => p.1 ^ m ∈ K) fun _ => Iff.rfl).trans
      (Equiv.prodSubtypeFstEquivSubtypeProd (p := fun a : G => a ^ m ∈ K))),
    Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card (α := G),
    Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin]
  rfl

end card_productIn_period

open card_productIn_period

-- The proof does not use `hK`; it is kept so that the statement is the wanted one.
set_option linter.unusedVariables false in
/-- **Counting periodic tuples with product in a conjugation-closed set.** Let $G$ be a finite
group, let $K \subseteq G$ satisfy $g c g^{-1} \in K$ for all $g \in G$ and $c \in K$, let
$n \ge 1$ and let $k$ be a divisor of $n$. The number of tuples
$x = (x_0, \dots, x_{n-1}) \in G^n$ with $x_0 x_1 \cdots x_{n-1} \in K$ and $x_{i+k} = x_i$ for
all $i$ (indices taken mod $n$) is $\#\{a \in G : a^{n/k} \in K\} \cdot |G|^{k-1}$.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Lemma 23
(`jis-2026-26.4.6-lem-23`). -/
public theorem card_productIn_period (G : Type*) [Group G] [Fintype G] (K : Set G)
    (hK : ∀ g k, k ∈ K → g * k * g⁻¹ ∈ K) (n k : ℕ) (hn : 0 < n) (hk : k ∣ n) :
    Set.ncard {x : Fin n → G | (List.ofFn x).prod ∈ K ∧ x ∘ ⇑((finRotate n) ^ k) = x} =
      Set.ncard {a : G | a ^ (n / k) ∈ K} * Fintype.card G ^ (k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m * k := ⟨n / k, (Nat.div_mul_cancel hk).symm⟩
  have hk0 : 0 < k := Nat.pos_of_mul_pos_left hn
  have hm0 : 0 < m := Nat.pos_of_mul_pos_right hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk0.ne'
  rw [Nat.mul_div_cancel m hk0, Nat.add_sub_cancel, ← ncard_prod_pow_mem G K m k]
  have hle : k + 1 ≤ m * (k + 1) := Nat.le_mul_of_pos_left _ hm0
  have hinj : Function.Injective
      (Fin.repeat m : (Fin (k + 1) → G) → Fin (m * (k + 1)) → G) := by
    intro y y' h
    funext j
    have hj := congrFun h (Fin.castLE hle j)
    simp only [Fin.repeat_apply] at hj
    have hmod : (Fin.castLE hle j).modNat = j := by
      ext
      rw [Fin.coe_modNat, Fin.val_castLE, Nat.mod_eq_of_lt j.isLt]
    rwa [hmod] at hj
  rw [← Set.ncard_image_of_injective {y : Fin (k + 1) → G | (List.ofFn y).prod ^ m ∈ K} hinj]
  congr 1
  ext x
  constructor
  · rintro ⟨hxK, hx⟩
    refine ⟨fun j => x (Fin.castLE hle j), ?_, repeat_eq_of_comp_finRotate_pow hle x hx⟩
    change (List.ofFn fun j => x (Fin.castLE hle j)).prod ^ m ∈ K
    rw [← prod_ofFn_repeat, repeat_eq_of_comp_finRotate_pow hle x hx]
    exact hxK
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, repeat_comp_finRotate_pow m (k + 1) y⟩
    rw [prod_ofFn_repeat]
    exact hy

/-- **Counting identity-product tuples with a given period.** Let $G$ be a finite group,
$n \ge 1$ and $k$ a divisor of $n$. The number of tuples $x = (x_0, \dots, x_{n-1}) \in G^n$
with $x_0 x_1 \cdots x_{n-1} = 1$ and $x_{i+k} = x_i$ for all $i$ (indices taken mod $n$) is
$r_{n/k}(G) \, |G|^{k-1}$, where $r_m(G)$ is the number of $g \in G$ with $g^m = 1$.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Lemma 13, with `A_k` as defined in
Section 5 of the arXiv text (`jis-2026-26.4.6-lem-13`). -/
public theorem card_identityProduct_period (G : Type*) [Group G] [Fintype G]
    [DecidableEq G] (n k : ℕ) (hn : 0 < n) (hk : k ∣ n) :
    Set.ncard {x : Fin n → G | (List.ofFn x).prod = 1 ∧ x ∘ ⇑((finRotate n) ^ k) = x} =
      Fintype.card {g : G // g ^ (n / k) = 1} * Fintype.card G ^ (k - 1) := by
  have hcount := card_productIn_period G {1} (fun g c hc => by simp_all) n k hn hk
  simp only [Set.mem_singleton_iff] at hcount
  rw [← Nat.card_coe_set_eq {g : G | g ^ (n / k) = 1}, Nat.card_eq_fintype_card] at hcount
  exact hcount

end MetaMathlibExt
