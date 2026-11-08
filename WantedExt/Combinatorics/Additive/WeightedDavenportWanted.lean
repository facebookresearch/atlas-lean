/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Order.Lattice.Nat
public import MathlibExt.Combinatorics.Additive.WeightedDavenport
public import Mathlib.NumberTheory.Padics.PadicVal.Defs

namespace MetaMathlibExt

@[expose] public section

/-- Xia's theorem: if `A ⊆ Z_n \ {0}` is an arithmetic progression of length `⌈n/2⌉` with
common difference `1`, then `D_A(Z_n) = 2`. The progression is the image of
`i ↦ (a + i) % n` for `i < ⌈n/2⌉`, and `0` is assumed not to be among its terms.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum
Constants*, INTEGERS 26 (2026), Article A89, Theorem 1 (`integers-2026-A89-thm-1`). -/
public theorem_wanted weightedDavenport_zmod_arithmeticProgression (n a : ℕ) (hn : 2 ≤ n)
    (hzero : 0 ∉ (Finset.range (n ⌈/⌉ 2)).image (fun i => (a + i) % n)) :
    weightedDavenport ((Finset.range (n ⌈/⌉ 2)).image (fun i => (a + i) % n)) (ZMod n) =
      ((2 : ℕ) : ℕ∞)

/-- Xia's theorem: for a prime `p` and `k = v_p(n)`, the weight set
`A = {a ∈ [1, n-1] : a ≢ 0 (mod p)}` has `D_A(Z_n) = k + 1`. The hypothesis `p ∣ n` is
added: the residue condition is a condition on `Z_n` only when `p ∣ n`, and without it
the claim fails (`n = 10`, `p = 3`: `k = 0` but `D_A(Z_10) = 2`).

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum
Constants*, INTEGERS 26 (2026), Article A89, Theorem 2 (`integers-2026-A89-thm-2`). -/
public theorem_wanted weightedDavenport_zmod_not_dvd_prime (n p : ℕ) (hp : p.Prime)
    (hpn : p ∣ n) (hn : 0 < n) :
    weightedDavenport ((Finset.Icc 1 (n - 1)).filter (fun a => ¬ p ∣ a)) (ZMod n) =
      ((padicValNat p n + 1 : ℕ) : ℕ∞)

/-- Olson's theorem: for `h ∣ k`, `D(Z_h ⊕ Z_k) = h + k - 1`.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum
Constants*, INTEGERS 26 (2026), Article A89, Theorem 3 (`integers-2026-A89-thm-3`). -/
public theorem_wanted weightedDavenport_one_zmod_prod_of_dvd (h k : ℕ) (hh : 1 ≤ h)
    (hdvd : h ∣ k) (hk : 1 ≤ k) :
    weightedDavenport {1} (ZMod h × ZMod k) = ((h + k - 1 : ℕ) : ℕ∞)

/-- Olson's theorem: for a prime `p` and exponents `e_i ≥ 1`,
`D(Z_{p^{e_1}} ⊕ ⋯ ⊕ Z_{p^{e_r}}) = 1 + ∑ (p^{e_i} - 1)` (the rank `r = 0` case is the
trivial group and is included).

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum
Constants*, INTEGERS 26 (2026), Article A89, Theorem 4 (`integers-2026-A89-thm-4`). -/
public theorem_wanted weightedDavenport_one_pi_zmod_prime_pow (p r : ℕ) (hp : p.Prime)
    (e : Fin r → ℕ) (he : ∀ i, 1 ≤ e i) :
    weightedDavenport {1} ((i : Fin r) → ZMod (p ^ e i)) =
      ((1 + ∑ i, (p ^ e i - 1) : ℕ) : ℕ∞)

/-- For `m, n ≥ 2` with `m ∣ n`: `⌈n / (⌈n/(m-1)⌉ - 1)⌉ = m`.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum
Constants*, INTEGERS 26 (2026), Article A89, Lemma 1 (`integers-2026-A89-lem-1`). -/
public theorem_wanted ceilDiv_ceilDiv_sub_one_sub_one_of_dvd (m n : ℕ) (hm : 2 ≤ m)
    (hn : 2 ≤ n) (hdvd : m ∣ n) :
    n ⌈/⌉ (n ⌈/⌉ (m - 1) - 1) = m

/-- Main theorem: for `n ≥ 2` and a divisor `m ≥ 2` of `n`, every weight set `A` with
`n/m ∈ A ⊆ {1, …, ⌈n/(m-1)⌉ - 1}` has `D_A(Z_n) = m`. The extracted statement is garbled;
this is the reading Corollaries 1 and 2 restate.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum
Constants*, INTEGERS 26 (2026), Article A89, Theorem 5 (`integers-2026-A89-thm-5`). -/
public theorem_wanted weightedDavenport_zmod_of_dvd (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hdvd : m ∣ n) (A : Finset ℕ) (hmem : n / m ∈ A)
    (hsub : A ⊆ Finset.Icc 1 (n ⌈/⌉ (m - 1) - 1)) :
    weightedDavenport A (ZMod n) = ((m : ℕ) : ℕ∞)

/-- Adhikari, David, Urroz and Xia, Li: for `1 < r < n` and `A = {1, …, r}`,
`D_A(Z_n) = ⌈n/r⌉`.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum
Constants*, INTEGERS 26 (2026), Article A89, Corollary 1, first part (`integers-2026-A89-cor-1`). -/
public theorem_wanted weightedDavenport_zmod_Icc (n r : ℕ) (hr : 1 < r) (hrn : r < n) :
    weightedDavenport (Finset.Icc 1 r) (ZMod n) = ((n ⌈/⌉ r : ℕ) : ℕ∞)

/-- For `m, n ≥ 2` with `m ∣ n` and `r = ⌈n/(m-1)⌉ - 1`, the weight set `{1, …, r}` has
`D_A(Z_n) = m`.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum
Constants*, INTEGERS 26 (2026), Article A89, Corollary 1, second part (`integers-2026-A89-cor-1`).
-/
public theorem_wanted weightedDavenport_zmod_Icc_of_dvd (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hdvd : m ∣ n) :
    weightedDavenport (Finset.Icc 1 (n ⌈/⌉ (m - 1) - 1)) (ZMod n) = ((m : ℕ) : ℕ∞)

/-- For `m, n ≥ 2` with `m ∣ n`, `k ≥ 1` and `α = ⌈n/(m-1)⌉ - 1`, there is a sequence over
`Z_n ⊕ Z_{kn}` of length `m + ⌈kn/α⌉ - 2` with no non-empty `{1, …, α}`-weighted zero-sum
subsequence (the existence form; it gives `D_{1..α}(Z_n ⊕ Z_{kn}) ≥ m + ⌈kn/α⌉ - 1`).

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum
Constants*, INTEGERS 26 (2026), Article A89, Lemma 2 (`integers-2026-A89-lem-2`). -/
public theorem_wanted exists_weightedZeroSumFree_zmod_prod (m n k : ℕ) (hm : 2 ≤ m)
    (hn : 2 ≤ n) (hdvd : m ∣ n) (hk : 1 ≤ k) :
    ∃ s : List (ZMod n × ZMod (k * n)),
      s.length = m + (k * n) ⌈/⌉ (n ⌈/⌉ (m - 1) - 1) - 2 ∧
        IsWeightedZeroSumFree (Finset.Icc 1 (n ⌈/⌉ (m - 1) - 1)) s

/-- For `m, n ≥ 2` with `m ∣ n`, `α = ⌈n/(m-1)⌉ - 1` and `A ⊆ {1, …, α}` with `n/m ∈ A`:
if `α ∣ n`, then `D_A(Z_n ⊕ Z_{kn}) = m + ⌈kn/α⌉ - 1` for every `k ≥ 1`. The paper's
"non-empty" is implied by `n/m ∈ A` and is not repeated.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum
Constants*, INTEGERS 26 (2026), Article A89, Theorem 6(i) (`integers-2026-A89-thm-6`). -/
public theorem_wanted weightedDavenport_zmod_prod_of_dvd (m n k : ℕ) (hm : 2 ≤ m)
    (hn : 2 ≤ n) (hdvd : m ∣ n) (A : Finset ℕ) (hmem : n / m ∈ A)
    (hsub : A ⊆ Finset.Icc 1 (n ⌈/⌉ (m - 1) - 1)) (hα : n ⌈/⌉ (m - 1) - 1 ∣ n)
    (hk : 1 ≤ k) :
    weightedDavenport A (ZMod n × ZMod (k * n)) =
      ((m + (k * n) ⌈/⌉ (n ⌈/⌉ (m - 1) - 1) - 1 : ℕ) : ℕ∞)

/-- Same setting with `α ∤ n`: writing `r = n mod α` (so `1 ≤ r < α`), for every `k ≥ 1`
with `(k - 1)α < kr`, `D_A(Z_n ⊕ Z_{kn}) = m + ⌈kn/α⌉ - 1`. The paper's `α ∤ n`,
`n ≡ r (mod α)` and `1 ≤ r < α` are encoded as `0 < n % α` with `r = n % α`.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum
Constants*, INTEGERS 26 (2026), Article A89, Theorem 6(ii) (`integers-2026-A89-thm-6`). -/
public theorem_wanted weightedDavenport_zmod_prod_of_not_dvd (m n k : ℕ) (hm : 2 ≤ m)
    (hn : 2 ≤ n) (hdvd : m ∣ n) (A : Finset ℕ) (hmem : n / m ∈ A)
    (hsub : A ⊆ Finset.Icc 1 (n ⌈/⌉ (m - 1) - 1)) (hr : 0 < n % (n ⌈/⌉ (m - 1) - 1))
    (hk : 1 ≤ k)
    (hkr : (k - 1) * (n ⌈/⌉ (m - 1) - 1) < k * (n % (n ⌈/⌉ (m - 1) - 1))) :
    weightedDavenport A (ZMod n × ZMod (k * n)) =
      ((m + (k * n) ⌈/⌉ (n ⌈/⌉ (m - 1) - 1) - 1 : ℕ) : ℕ∞)

/-- For `n ≥ 2` and a divisor `m ≥ 2` of `n`, every `A ⊆ {1, …, ⌈n/(m-1)⌉ - 1}` with
`n/m ∈ A` has `D_A(Z_n ⊕ Z_n) = 2m - 1`.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum
Constants*, INTEGERS 26 (2026), Article A89, Corollary 2 (`integers-2026-A89-cor-2`). -/
public theorem_wanted weightedDavenport_zmod_prod_self_of_dvd (m n : ℕ) (hm : 2 ≤ m)
    (hn : 2 ≤ n) (hdvd : m ∣ n) (A : Finset ℕ) (hmem : n / m ∈ A)
    (hsub : A ⊆ Finset.Icc 1 (n ⌈/⌉ (m - 1) - 1)) :
    weightedDavenport A (ZMod n × ZMod n) = ((2 * m - 1 : ℕ) : ℕ∞)

/-- Let `G = Z_{p^{e_1}} ⊕ ⋯ ⊕ Z_{p^{e_r}}` with `p` prime and `e_1 ≤ ⋯ ≤ e_r` (`e`
monotone, `r ≥ 1`, `e_1 = e 0`), and `1 ≤ c ≤ e_1`, `β = ⌈p^{e_1}/(p^c - 1)⌉ - 1`. There is a
sequence over `G` of length `∑ (⌈p^{e_i}/β⌉ - 1)` with no non-empty `{1, …, β}`-weighted
zero-sum subsequence (existence form of `D_B(G) ≥ 1 + ∑ (⌈p^{e_i}/β⌉ - 1)`). The paper's
exponent `e` is named `c`; `e_i ≥ 1` follows from `1 ≤ c ≤ e_1` and monotonicity.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum
Constants*, INTEGERS 26 (2026), Article A89, Lemma 3 (`integers-2026-A89-lem-3`). -/
public theorem_wanted exists_weightedZeroSumFree_pi_zmod_prime_pow (p r c : ℕ)
    (hp : p.Prime) (hr : 0 < r) (e : Fin r → ℕ) (hmono : Monotone e) (hc : 1 ≤ c)
    (hce : c ≤ e ⟨0, hr⟩) :
    ∃ s : List ((i : Fin r) → ZMod (p ^ e i)),
      s.length = ∑ i, (p ^ e i ⌈/⌉ (p ^ e ⟨0, hr⟩ ⌈/⌉ (p ^ c - 1) - 1) - 1) ∧
        IsWeightedZeroSumFree (Finset.Icc 1 (p ^ e ⟨0, hr⟩ ⌈/⌉ (p ^ c - 1) - 1)) s

/-- Same `G`, `c`, `β`; `A ⊆ {1, …, β}` with `p^{e_1 - c} ∈ A`. If `β ∣ p^{e_1}`, then
`D_A(G) = 1 + ∑ (⌈p^{e_i}/β⌉ - 1)`.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum
Constants*, INTEGERS 26 (2026), Article A89, Theorem 7(i) (`integers-2026-A89-thm-7`). -/
public theorem_wanted weightedDavenport_pi_zmod_prime_pow_of_dvd (p r c : ℕ) (hp : p.Prime)
    (hr : 0 < r) (e : Fin r → ℕ) (hmono : Monotone e) (hc : 1 ≤ c) (hce : c ≤ e ⟨0, hr⟩)
    (A : Finset ℕ) (hmem : p ^ (e ⟨0, hr⟩ - c) ∈ A)
    (hsub : A ⊆ Finset.Icc 1 (p ^ e ⟨0, hr⟩ ⌈/⌉ (p ^ c - 1) - 1))
    (hβ : p ^ e ⟨0, hr⟩ ⌈/⌉ (p ^ c - 1) - 1 ∣ p ^ e ⟨0, hr⟩) :
    weightedDavenport A ((i : Fin r) → ZMod (p ^ e i)) =
      ((1 + ∑ i, (p ^ e i ⌈/⌉ (p ^ e ⟨0, hr⟩ ⌈/⌉ (p ^ c - 1) - 1) - 1) : ℕ) : ℕ∞)

/-- Same setting with `β ∤ p^{e_1}`: writing `s = p^{e_1} mod β` (so `1 ≤ s < β`), if
`(p^{e_j - e_1} - 1)β < s p^{e_j - e_1}` for every `j ≥ 2`, then
`D_A(G) = 1 + ∑ (⌈p^{e_i}/β⌉ - 1)`. The paper's `β ∤ p^{e_1}`, `p^{e_1} ≡ s (mod β)` and
`1 ≤ s < β` are encoded as `0 < p^{e_1} % β` with `s = p^{e_1} % β`; `j ∈ {2, …, r}` is
`0 < j` in `Fin r`.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum
Constants*, INTEGERS 26 (2026), Article A89, Theorem 7(ii) (`integers-2026-A89-thm-7`). -/
public theorem_wanted weightedDavenport_pi_zmod_prime_pow_of_not_dvd (p r c : ℕ)
    (hp : p.Prime) (hr : 0 < r) (e : Fin r → ℕ) (hmono : Monotone e) (hc : 1 ≤ c)
    (hce : c ≤ e ⟨0, hr⟩) (A : Finset ℕ) (hmem : p ^ (e ⟨0, hr⟩ - c) ∈ A)
    (hsub : A ⊆ Finset.Icc 1 (p ^ e ⟨0, hr⟩ ⌈/⌉ (p ^ c - 1) - 1))
    (hs : 0 < p ^ e ⟨0, hr⟩ % (p ^ e ⟨0, hr⟩ ⌈/⌉ (p ^ c - 1) - 1))
    (hineq : ∀ j : Fin r, 0 < j.val →
      (p ^ (e j - e ⟨0, hr⟩) - 1) * (p ^ e ⟨0, hr⟩ ⌈/⌉ (p ^ c - 1) - 1) <
        p ^ e ⟨0, hr⟩ % (p ^ e ⟨0, hr⟩ ⌈/⌉ (p ^ c - 1) - 1) * p ^ (e j - e ⟨0, hr⟩)) :
    weightedDavenport A ((i : Fin r) → ZMod (p ^ e i)) =
      ((1 + ∑ i, (p ^ e i ⌈/⌉ (p ^ e ⟨0, hr⟩ ⌈/⌉ (p ^ c - 1) - 1) - 1) : ℕ) : ℕ∞)

/-- For a prime `p`, `1 ≤ a ≤ e` and `r ≥ 1`, every `A ⊆ {1, …, ⌈p^e/(p^a - 1)⌉ - 1}` with
`p^{e-a} ∈ A` has `D_A((Z_{p^e})^r) = 1 + r(p^a - 1)`.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum
Constants*, INTEGERS 26 (2026), Article A89, Corollary 3 (`integers-2026-A89-cor-3`). -/
public theorem_wanted weightedDavenport_pi_zmod_prime_pow_const (p e a r : ℕ) (hp : p.Prime)
    (ha : 1 ≤ a) (hae : a ≤ e) (hr : 1 ≤ r) (A : Finset ℕ) (hmem : p ^ (e - a) ∈ A)
    (hsub : A ⊆ Finset.Icc 1 (p ^ e ⌈/⌉ (p ^ a - 1) - 1)) :
    weightedDavenport A ((_ : Fin r) → ZMod (p ^ e)) = ((1 + r * (p ^ a - 1) : ℕ) : ℕ∞)

end

end MetaMathlibExt
