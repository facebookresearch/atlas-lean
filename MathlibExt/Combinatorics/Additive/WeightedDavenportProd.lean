/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Data.Nat.Prime.Defs
public import MathlibExt.Combinatorics.Additive.WeightedDavenport
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.OfFn
import Mathlib.Data.ZMod.Basic

/-!
# Long weighted zero-sum free sequences in products of cyclic groups

The main results construct long weighted zero-sum free sequences in the groups
$\mathbb{Z}/n\mathbb{Z} \oplus \mathbb{Z}/kn\mathbb{Z}$ of rank two
(`exists_weightedZeroSumFree_zmod_prod`) and in the abelian $p$-groups
$\mathbb{Z}/p^{e_1}\mathbb{Z} \oplus \dots \oplus \mathbb{Z}/p^{e_r}\mathbb{Z}$
(`exists_weightedZeroSumFree_pi_zmod_prime_pow`). The second one is a special case of a
construction in every product
$\mathbb{Z}/n_1\mathbb{Z} \oplus \dots \oplus \mathbb{Z}/n_r\mathbb{Z}$
(`exists_weightedZeroSumFree_pi_zmod_prime_pow.exists_weightedZeroSumFree_pi_zmod`).

Each sequence consists of blocks of coordinate generators. In each block, the sum of the
selected weights is strictly below the order of the generator.
-/

namespace MetaMathlibExt

namespace exists_weightedZeroSumFree_zmod_prod

private theorem weights_eq_zero {l α n : ℕ} (w : Fin l → ℕ) (hw : ∀ i, w i ≤ α)
    (hlt : l * α < n) (hz : ∑ i, (w i : ZMod n) = 0) : ∀ i, w i = 0 := by
  rw [← Nat.cast_sum, ZMod.natCast_eq_zero_iff] at hz
  have hsum : ∑ i, w i < n := calc
    ∑ i, w i ≤ ∑ _ : Fin l, α := Finset.sum_le_sum fun i _ => hw i
    _ = l * α := by simp
    _ < n := hlt
  apply congrFun
  exact (Fintype.sum_eq_zero_iff_of_nonneg (fun i => Nat.zero_le (w i))).mp
    (Nat.eq_zero_of_dvd_of_lt hz hsum)

end exists_weightedZeroSumFree_zmod_prod

/-- **Long weighted zero-sum free sequences in groups of rank two.** Let $m, n \ge 2$ be natural
numbers with $m \mid n$, let $k \ge 1$ and put $\alpha = \lceil n/(m-1) \rceil - 1$. Then there is
a sequence $s$ over $\mathbb{Z}/n\mathbb{Z} \oplus \mathbb{Z}/kn\mathbb{Z}$ of length
$m + \lceil kn/\alpha \rceil - 2$ that is $\{1, \dots, \alpha\}$-weighted zero-sum free: for every
non-empty set $I$ of positions and all weights $a_i \in \{1, \dots, \alpha\}$, the weighted sum
$\sum_{i \in I} a_i s_i$ is non-zero.

In particular the $\{1, \dots, \alpha\}$-weighted Davenport constant of
$\mathbb{Z}/n\mathbb{Z} \oplus \mathbb{Z}/kn\mathbb{Z}$ is at least
$m + \lceil kn/\alpha \rceil - 1$.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum
Constants*, INTEGERS 26 (2026), Article A89, Lemma 2 (`integers-2026-A89-lem-2`). -/
public theorem exists_weightedZeroSumFree_zmod_prod (m n k : ℕ) (hm : 2 ≤ m)
    (hn : 2 ≤ n) (hdvd : m ∣ n) (hk : 1 ≤ k) :
    ∃ s : List (ZMod n × ZMod (k * n)),
      s.length = m + (k * n) ⌈/⌉ (n ⌈/⌉ (m - 1) - 1) - 2 ∧
        IsWeightedZeroSumFree (Finset.Icc 1 (n ⌈/⌉ (m - 1) - 1)) s := by
  let p := m - 1
  let α := n ⌈/⌉ p - 1
  let q := (k * n) ⌈/⌉ α - 1
  have hp : 0 < p := by dsimp [p]; omega
  have hpn : p < n := by
    have := Nat.le_of_dvd (by omega : 0 < n) hdvd
    dsimp [p]
    omega
  have hceil : 1 < n ⌈/⌉ p := (gc_mul_ceilDiv hp).lt_iff_lt.mpr (by simpa using hpn)
  have hα : 0 < α := by dsimp [α]; omega
  have hkn : 0 < k * n := Nat.mul_pos hk (by omega)
  have hceil' : 0 < (k * n) ⌈/⌉ α := (gc_mul_ceilDiv hα).lt_iff_lt.mpr (by simpa using hkn)
  have hleft : p * α < n := (gc_mul_ceilDiv hp).lt_iff_lt.mp (by dsimp [α]; omega)
  have hright : q * α < k * n := by
    rw [Nat.mul_comm]
    exact (gc_mul_ceilDiv hα).lt_iff_lt.mp (by dsimp [q]; omega)
  let e : Fin (p + q) → ZMod n × ZMod (k * n) :=
    Fin.append (fun _ : Fin p => (1, 0)) (fun _ : Fin q => (0, 1))
  refine ⟨List.ofFn e, ?_, ?_⟩
  · rw [List.length_ofFn]
    change p + q = m + (k * n) ⌈/⌉ α - 2
    dsimp [p, q]
    omega
  unfold IsWeightedZeroSumFree
  simp only [List.get_ofFn]
  -- Index the list by the sum of the two block lengths.
  generalize_proofs hlen
  generalize (List.ofFn e).length = L at hlen ⊢
  subst L
  intro I hI a ha hsum
  -- Extend the selected weights by zero so that the full sum splits at the block boundary.
  let w (i : Fin (p + q)) := if i ∈ I then a i else 0
  have hw (i) : w i ≤ α := by
    by_cases hi : i ∈ I
    · simpa [w, hi] using (Finset.mem_Icc.mp (ha i hi)).2
    · simp [w, hi]
  have hz : ∑ i, w i • e i = 0 := by
    simpa [w, ite_smul, Finset.sum_ite_mem_eq] using hsum
  rw [Fin.sum_univ_add] at hz
  have hw0 : ∀ i, w i = 0 := Fin.addCases
    (exists_weightedZeroSumFree_zmod_prod.weights_eq_zero _ (fun i => hw (i.castAdd q)) hleft
      (by simpa [e, Prod.fst_sum, nsmul_eq_mul] using congrArg Prod.fst hz))
    (exists_weightedZeroSumFree_zmod_prod.weights_eq_zero _ (fun i => hw (i.natAdd p)) hright
      (by simpa [e, Prod.snd_sum, nsmul_eq_mul] using congrArg Prod.snd hz))
  obtain ⟨i, hi⟩ := hI
  exact (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp (ha i hi)).1)
    (by simpa [w, hi] using hw0 i)

namespace exists_weightedZeroSumFree_pi_zmod_prime_pow

/-- **Long weighted zero-sum free sequences in finite products of cyclic groups.** Let $r$ and
$\beta$ be natural numbers and let $n_1, \dots, n_r$ be natural numbers. Then there is a
sequence $s$ over $\mathbb{Z}/n_1\mathbb{Z} \oplus \dots \oplus \mathbb{Z}/n_r\mathbb{Z}$ of
length $\sum_{i=1}^{r} (\lceil n_i/\beta \rceil - 1)$ that is $\{1, \dots, \beta\}$-weighted
zero-sum free: for every non-empty set $I$ of positions and all weights
$a_i \in \{1, \dots, \beta\}$, the weighted sum $\sum_{i \in I} a_i s_i$ is non-zero. Here
$\lceil n_i/\beta \rceil - 1$ is computed in $\mathbb{N}$, so it is $0$ when $n_i = 0$ or
$\beta = 0$.

The sequence consists of $\lceil n_i/\beta \rceil - 1$ copies of the $i$-th coordinate generator
for each $i$. In a coordinate $i$ whose block meets $I$, the selected weights add up to a number
between $1$ and $(\lceil n_i/\beta \rceil - 1)\beta < n_i$, so that coordinate of the weighted sum
is non-zero. -/
public theorem exists_weightedZeroSumFree_pi_zmod {r : ℕ} (n : Fin r → ℕ) (β : ℕ) :
    ∃ s : List ((i : Fin r) → ZMod (n i)),
      s.length = ∑ i, (n i ⌈/⌉ β - 1) ∧ IsWeightedZeroSumFree (Finset.Icc 1 β) s := by
  set q : Fin r → ℕ := fun i => n i ⌈/⌉ β - 1
  let σ : (Σ i : Fin r, Fin (q i)) ≃ Fin (∑ i, q i) := finSigmaFinEquiv
  -- Position `k` carries the generator of the coordinate whose block contains `k`.
  let f : Fin (∑ i, q i) → (i : Fin r) → ZMod (n i) := fun k j =>
    if (σ.symm k).1 = j then 1 else 0
  refine ⟨List.ofFn f, List.length_ofFn, ?_⟩
  unfold IsWeightedZeroSumFree
  simp only [List.get_ofFn]
  generalize_proofs hlen
  generalize (List.ofFn f).length = L at hlen ⊢
  subst L
  intro I hI a ha hsum
  -- Extend the selected weights by zero, so that the sum runs over all positions.
  let w (k : Fin (∑ i, q i)) : ℕ := if k ∈ I then a k else 0
  have hw (k) : w k ≤ β := by
    by_cases hk : k ∈ I
    · simpa [w, hk] using (Finset.mem_Icc.mp (ha k hk)).2
    · simp [w, hk]
  have hz : ∑ k, w k • f k = 0 := by
    simpa [w, ite_smul, Finset.sum_ite_mem_eq] using hsum
  -- In the coordinate `j`, only the block of `j` contributes.
  have hcoord (j : Fin r) : ∑ t : Fin (q j), (w (σ ⟨j, t⟩) : ZMod (n j)) = 0 := by
    have h := congrFun hz j
    rw [Finset.sum_apply, ← σ.sum_comp, Fintype.sum_sigma, Fintype.sum_eq_single j] at h
    · simpa [f, nsmul_eq_mul] using h
    · intro i hij
      simp [f, hij]
  -- Each block has fewer than `n j / β` positions, so its weights vanish.
  have hblock (j : Fin r) (t : Fin (q j)) : w (σ ⟨j, t⟩) = 0 := by
    have hqpos : 0 < n j ⌈/⌉ β - 1 := t.pos
    have hβ : 0 < β := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hqpos
    have hlt : q j * β < n j := by
      rw [Nat.mul_comm]
      exact (gc_mul_ceilDiv hβ).lt_iff_lt.mp (by change n j ⌈/⌉ β - 1 < n j ⌈/⌉ β; omega)
    exact exists_weightedZeroSumFree_zmod_prod.weights_eq_zero _ (fun t => hw _) hlt
      (hcoord j) t
  obtain ⟨k, hk⟩ := hI
  have h0 : w k = 0 := by simpa using hblock (σ.symm k).1 (σ.symm k).2
  exact (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp (ha k hk)).1) (by simpa [w, hk] using h0)

end exists_weightedZeroSumFree_pi_zmod_prime_pow

-- `hp`, `hmono`, `hc` and `hce` are hypotheses of the source statement, kept for fidelity; the
-- construction works for every weight bound.
set_option linter.unusedVariables false in
/-- **Long weighted zero-sum free sequences in abelian $p$-groups.** Let $p$ be a prime, let
$r \ge 1$, let $e_1 \le e_2 \le \dots \le e_r$ be natural numbers and let
$G = \mathbb{Z}/p^{e_1}\mathbb{Z} \oplus \dots \oplus \mathbb{Z}/p^{e_r}\mathbb{Z}$. Let $c$ be a
natural number with $1 \le c \le e_1$ and put $\beta = \lceil p^{e_1}/(p^c - 1) \rceil - 1$. Then
there is a sequence $s$ over $G$ of length $\sum_{i=1}^{r} (\lceil p^{e_i}/\beta \rceil - 1)$ that
is $\{1, \dots, \beta\}$-weighted zero-sum free: for every non-empty set $I$ of positions and all
weights $a_i \in \{1, \dots, \beta\}$, the weighted sum $\sum_{i \in I} a_i s_i$ is non-zero.

In particular the $\{1, \dots, \beta\}$-weighted Davenport constant of $G$ is at least
$1 + \sum_{i=1}^{r} (\lceil p^{e_i}/\beta \rceil - 1)$.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum
Constants*, INTEGERS 26 (2026), Article A89, Lemma 3 (`integers-2026-A89-lem-3`). -/
public theorem exists_weightedZeroSumFree_pi_zmod_prime_pow (p r c : ℕ)
    (hp : p.Prime) (hr : 0 < r) (e : Fin r → ℕ) (hmono : Monotone e) (hc : 1 ≤ c)
    (hce : c ≤ e ⟨0, hr⟩) :
    ∃ s : List ((i : Fin r) → ZMod (p ^ e i)),
      s.length = ∑ i, (p ^ e i ⌈/⌉ (p ^ e ⟨0, hr⟩ ⌈/⌉ (p ^ c - 1) - 1) - 1) ∧
        IsWeightedZeroSumFree (Finset.Icc 1 (p ^ e ⟨0, hr⟩ ⌈/⌉ (p ^ c - 1) - 1)) s :=
  exists_weightedZeroSumFree_pi_zmod_prime_pow.exists_weightedZeroSumFree_pi_zmod
    (fun i => p ^ e i) _

end MetaMathlibExt
