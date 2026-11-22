/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.FLT.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import MathlibExt.NumberTheory.WieferichPrime

/-!
# Regular primes, non-Wieferich primes and finite multiple zeta values of level `N`

Statements from Shin-ichiro Seki, *Regular Primes, Non-Wieferich Primes, and Finite
Multiple Zeta Values of Level N*, INTEGERS 24 (2024), Article A22 (arXiv:2310.06809).

The paper works in `𝒜 = (∏_p ℤ/pℤ) / (⊕_p ℤ/pℤ)`. An identity "holds in `𝒜`" exactly
when it holds modulo `p` for all but finitely many primes `p`; it is stated here as
`∀ᶠ p in atTop, p.Prime → …` in `ZMod p`. A rational number `a/b` is reduced modulo `p`
as `(a : ZMod p) * (b : ZMod p)⁻¹`. The Bernoulli–Seki numbers (`B₁ = +1/2`) are
Mathlib's `bernoulli'`; only even indices `≥ 2` occur below.

For an index `k = (k₁, …, k_r)` (here `k : Fin r → ℕ`) and colors
`α ∈ (ℤ/Nℤ)^r`, `ζ^α_{p,N}(k) = ∑ 1/(m₁^{k₁} ⋯ m_r^{k_r})` over `0 < m₁ < ⋯ < m_r < p`
with `mᵢ ≡ αᵢ (mod N)` (`coloredFiniteMZV`). The color map `[j]` sends the class of `p`
to `(-j p, …, -j p)`, so `ζ^{[j]}_{𝒜,N}(k)` has `p`-component
`ζ^{(-jp, …, -jp)}_{p,N}(k)`.
-/

namespace MetaMathlibExt

@[expose] public section

open Filter

open scoped Classical in
/-- The colored finite multiple harmonic sum `ζ^α_{p,N}(k) ∈ ℤ/pℤ`: the sum of
`∏ᵢ mᵢ^{-kᵢ}` over `0 < m₁ < ⋯ < m_r < p` with `mᵢ ≡ αᵢ (mod N)`.

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Section 2.2 (definition of `ζ^α_{p,N}(k)`). -/
noncomputable def coloredFiniteMZV (p N : ℕ) {r : ℕ} (k : Fin r → ℕ) (α : Fin r → ZMod N) :
    ZMod p :=
  ∑ m ∈ (Finset.univ : Finset (Fin r → Fin p)).filter
      (fun m : Fin r → Fin p => StrictMono m ∧
        ∀ i, 0 < (m i : ℕ) ∧ ((m i : ℕ) : ZMod N) = α i),
    ∏ i, (((m i : ℕ) : ZMod p)⁻¹) ^ k i

/-- The empty index has value `1`.

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Section 2.2 (`ζ^∅_{p,N}(∅) = 1`). -/
theorem coloredFiniteMZV_zero (p N : ℕ) (k : Fin 0 → ℕ) (α : Fin 0 → ZMod N) :
    coloredFiniteMZV p N k α = 1 := by
  classical
  rw [coloredFiniteMZV, Finset.filter_true_of_mem fun m _ =>
    ⟨fun a => Fin.elim0 a, fun i => Fin.elim0 i⟩]
  simp

/-- **Lemma 1.** For an index `k` of weight `w`, `N ≥ 1` and `0 ≤ j < N`,
`∑_{jp/N < m₁ < ⋯ < m_r < (j+1)p/N} 1/(m₁^{k₁} ⋯ m_r^{k_r}) ≡ N^w ζ^{[j]}_{𝒜,N}(k)` in `𝒜`.

The entries of `k` may be `0`; the paper's indices have positive entries.

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Lemma 1 (`integers-2024-A22-lem-1`). -/
public theorem_wanted sum_Ioo_eq_pow_mul_coloredFiniteMZV {N j r : ℕ} (hN : 0 < N) (hj : j < N)
    (k : Fin r → ℕ) :
    ∀ᶠ p in atTop, p.Prime →
      (∑ m ∈ (Finset.univ : Finset (Fin r → Fin p)).filter
          (fun m : Fin r → Fin p => StrictMono m ∧
            ∀ i, j * p < N * (m i : ℕ) ∧ N * (m i : ℕ) < (j + 1) * p),
        ∏ i, (((m i : ℕ) : ZMod p)⁻¹) ^ k i) =
        (N : ZMod p) ^ (∑ i, k i) * coloredFiniteMZV p N k fun _ => -(j : ZMod N) * p

/-- **Proposition 3.** For odd `k ≥ 3`, in `𝒜`:
`2 ζ^{[2]}_{𝒜,12}(k) = (2^{-k} - 3^{-k} - 4^{-k} + 12^{-k}) Z(k)` and
`2 ζ^{[3]}_{𝒜,12}(k) = (3^{-k} - 4^{-k} - 6^{-k} + 12^{-k}) Z(k)`, where
`Z(k) = (B_{p-k} / k mod p)_p`.

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Proposition 3 (`integers-2024-A22-prop-3`). -/
public theorem_wanted two_mul_coloredFiniteMZV_twelve {k : ℕ} (hk : Odd k) (hk3 : 3 ≤ k) :
    ∀ᶠ p in atTop, p.Prime →
      let Z : ZMod p := ((bernoulli' (p - k)).num : ZMod p) *
        ((bernoulli' (p - k)).den : ZMod p)⁻¹ * (k : ZMod p)⁻¹
      2 * coloredFiniteMZV p 12 ![k] ![-(2 : ZMod 12) * p] =
          (((2 : ZMod p) ^ k)⁻¹ - ((3 : ZMod p) ^ k)⁻¹ - ((4 : ZMod p) ^ k)⁻¹ +
            ((12 : ZMod p) ^ k)⁻¹) * Z ∧
        2 * coloredFiniteMZV p 12 ![k] ![-(3 : ZMod 12) * p] =
          (((3 : ZMod p) ^ k)⁻¹ - ((4 : ZMod p) ^ k)⁻¹ - ((6 : ZMod p) ^ k)⁻¹ +
            ((12 : ZMod p) ^ k)⁻¹) * Z

/-- **Theorem 1** (Kummer). If `p` is a regular prime (odd, and `p` does not divide the
class number of the `p`-th cyclotomic field), then Fermat's last theorem holds for the
exponent `p`.

The cyclotomic field is any `K` with `IsCyclotomicExtension {p} ℚ K`.

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Theorem 1 (`integers-2024-A22-thm-1`). -/
public theorem_wanted fermatLastTheoremFor_of_regular {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hreg : ¬ p ∣ NumberField.classNumber K) : FermatLastTheoremFor p

/-- **Theorem 2** (Wieferich). If `p` is a non-Wieferich prime (`p² ∤ 2^{p-1} - 1`), then
the first case of Fermat's last theorem holds for the exponent `p`: there are no integers
`x, y, z` with `p ∤ x y z` and `x^p + y^p = z^p`.

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Theorem 2 (`integers-2024-A22-thm-2`). -/
public theorem_wanted fermat_first_case_of_not_isWieferichPrime {p : ℕ} (hp : p.Prime)
    (hW : ¬ p.IsWieferichPrime) (x y z : ℤ) (hxyz : ¬ (p : ℤ) ∣ x * y * z) :
    x ^ p + y ^ p ≠ z ^ p

/-- **Theorem 3** (Skula, Dobson, Ichimura). For an odd prime `p` and a positive integer
`N` with `p ∤ N`, `(N + 1) q_p(2) ≡ -∑_{0 ≤ j < N/2} s_p(2j, 2N) (mod p)`, where
`q_p(2) = (2^{p-1} - 1)/p` and `s_p(i, M) = ∑_{ip/M < m < (i+1)p/M} 1/m`.

The record's trailing discussion (the logarithm `log_𝒜` and equation (3)) is not part of
the statement.

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Theorem 3 (`integers-2024-A22-thm-3`). -/
public theorem_wanted fermatQuotient_two_mul_eq_neg_sum {p N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hN : 0 < N) (hpN : ¬ p ∣ N) :
    ((N + 1 : ℕ) : ZMod p) * (((2 ^ (p - 1) - 1) / p : ℕ) : ZMod p) =
      -∑ j ∈ (Finset.range N).filter (fun j => 2 * j < N),
        ∑ m ∈ (Finset.Ioo 0 p).filter
            (fun m => 2 * j * p < 2 * N * m ∧ 2 * N * m < (2 * j + 1) * p),
          ((m : ZMod p)⁻¹)

/-- **Proposition 5.** For every prime `p ≥ 11` there is an odd `k ≥ 3` with
`p ∤ B_{p-k}` and `k ≤ (p - 3)/2` if `p ≡ 1 (mod 4)`, `k ≤ (p - 5)/2` if `p ≡ 3 (mod 4)`;
equivalently `g_p` (the least such odd `k`, Definition 5.5 of the paper) is at most that
bound. `p ∤ B_{p-k}` means `p` does not divide the numerator.

The record's `ðp` is the paper's `g_p`.

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Proposition 5 (`integers-2024-A22-prop-5`). -/
public theorem_wanted exists_odd_not_dvd_bernoulli_num_le {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    ∃ k, Odd k ∧ 3 ≤ k ∧ ¬ (p : ℤ) ∣ (bernoulli' (p - k)).num ∧
      k ≤ if p % 4 = 1 then (p - 3) / 2 else (p - 5) / 2

/-- The `p`-component of `ζ^c_{𝒜,N}(k)` for a color map `c`: `ζ^{c(p)}_{p,N}(k)` when
`c(p mod N)` is a color tuple and `0` when it is `∅` (`none`). Color maps are taken on all of
`ℤ/Nℤ`; only their values at units matter for all but finitely many `p`.

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Definition 2.1 (finite multiple zeta values of
level `N` with color map). -/
noncomputable def finiteMZVColored (p N : ℕ) {r : ℕ} (k : Fin r → ℕ)
    (c : ZMod N → Option (Fin r → ZMod N)) : ZMod p :=
  match c (p : ZMod N) with
  | none => 0
  | some α => coloredFiniteMZV p N k α

/-- The color map that is constantly `∅` gives `0`.

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Definition 2.1. -/
theorem finiteMZVColored_none (p N : ℕ) {r : ℕ} (k : Fin r → ℕ) :
    finiteMZVColored p N k (fun _ => none) = 0 :=
  rfl

/-- A constant color map gives the colored sum.

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Definition 2.1. -/
theorem finiteMZVColored_some (p N : ℕ) {r : ℕ} (k : Fin r → ℕ) (α : Fin r → ZMod N) :
    finiteMZVColored p N k (fun _ => some α) = coloredFiniteMZV p N k α :=
  rfl

/-- **Proposition 1 (i)** (reversal). For an index `k` of weight `w` and a color map `c`,
`ζ^c_{𝒜,N}(k) = (-1)^w ζ^{c←}_{𝒜,N}(k←)`, where `k← = (k_r, …, k₁)` and
`c←(α) = (α - α_r, …, α - α₁)` when `c(α) = (α₁, …, α_r)`, `c←(α) = ∅` when `c(α) = ∅`.

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Proposition 1 (`integers-2024-A22-prop-1`). -/
public theorem_wanted finiteMZVColored_eq_neg_one_pow_mul_reverse {N r : ℕ} (hN : 0 < N)
    (k : Fin r → ℕ) (c : ZMod N → Option (Fin r → ZMod N)) :
    ∀ᶠ p in atTop, p.Prime →
      finiteMZVColored p N k c = (-1) ^ (∑ i, k i) *
        finiteMZVColored p N (k ∘ Fin.rev) (fun a => (c a).map fun β i => a - β (Fin.rev i))

open scoped Classical in
/-- **Proposition 1 (ii)** (decomposition). For an index `k = (k₁, …, k_r)` of weight `w`,
`ζ_𝒜(k) = N^w ∑_{0 ≤ i₁ ≤ ⋯ ≤ i_{N-1} ≤ r} ∏_{j=0}^{N-1} ζ^{[j]}_{𝒜,N}(k_{(i);j})` with
`k_{(i);j} = (k_{i_j+1}, …, k_{i_{j+1}})`, `i₀ = 0`, `i_N = r`.

The index is a list; `ζ_𝒜` is the level-`1` value. The tuple `(i₁, …, i_{N-1})` is a
monotone map `Fin (N - 1) → Fin (r + 1)`, extended by `i₀ = 0` and `i_N = r`.

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Proposition 1 (`integers-2024-A22-prop-1`). -/
public theorem_wanted coloredFiniteMZV_one_eq_pow_mul_sum_prod {N : ℕ} (hN : 0 < N)
    (κ : List ℕ) :
    ∀ᶠ p in atTop, p.Prime →
      coloredFiniteMZV p 1 (fun t : Fin κ.length => κ.get t) 0 =
        (N : ZMod p) ^ κ.sum *
          ∑ i ∈ (Finset.univ : Finset (Fin (N - 1) → Fin (κ.length + 1))).filter Monotone,
            ∏ j : Fin N,
              let e : ℕ → ℕ := fun t =>
                if t = 0 then 0 else if h : t - 1 < N - 1 then (i ⟨t - 1, h⟩ : ℕ) else κ.length
              let sub := (κ.drop (e j)).take (e ((j : ℕ) + 1) - e j)
              coloredFiniteMZV p N (fun t : Fin sub.length => sub.get t)
                (fun _ => -((j : ℕ) : ZMod N) * p)

/-- **Lemma 2.** For `N ∣ M` (both positive), `Z_{𝒜,w}(N) ⊆ Z_{𝒜,w}(M)`: every finite
multiple zeta value of level `N` and weight `w` is a `ℚ`-linear combination, in `𝒜`, of
finite multiple zeta values of level `M` and weight `w`.

The inclusion of `ℚ`-spans is stated on generators; a rational `q` acts modulo `p` as
`q.num · q.den⁻¹`.

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Lemma 2 (`integers-2024-A22-lem-2`). -/
public theorem_wanted exists_finiteMZVColored_eq_sum_of_dvd {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (hNM : N ∣ M) {r : ℕ} (k : Fin r → ℕ) (hk : ∀ i, 0 < k i)
    (c : ZMod N → Option (Fin r → ZMod N)) :
    ∃ (n : ℕ) (q : Fin n → ℚ) (s : Fin n → ℕ) (k' : (i : Fin n) → Fin (s i) → ℕ)
      (c' : (i : Fin n) → ZMod M → Option (Fin (s i) → ZMod M)),
      (∀ i j, 0 < k' i j) ∧ (∀ i, ∑ j, k' i j = ∑ j, k j) ∧
        ∀ᶠ p in atTop, p.Prime →
          finiteMZVColored p N k c = ∑ i, ((q i).num : ZMod p) * ((q i).den : ZMod p)⁻¹ *
            finiteMZVColored p M (k' i) (c' i)

/-- **Lemma 3** (Lemma 5.4). Problem 5.3 (a uniform bound `M` with `ℓ_p ≤ M` for every odd
prime `p`, where `ℓ_p` is the least `N` with `p ∤ N` and `p ∤ q_p(N)`) holds iff for some
`M ≥ 3` the set `⋂_{N=2}^M W(N)` is finite, `W(N) = {p prime : N^{p-1} ≡ 1 (mod p²)}`.

`ℓ_p ≤ M` is written as the existence of such an `N ≤ M`; `p ∤ q_p(N)` as
`p² ∤ N^{p-1} - 1`.

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Lemma 3 (`integers-2024-A22-lem-3`). -/
public theorem_wanted exists_bound_fermatQuotient_iff_finite_iInter :
    (∃ M : ℕ, ∀ p : ℕ, p.Prime → p ≠ 2 →
        ∃ N, 1 ≤ N ∧ N ≤ M ∧ ¬ p ∣ N ∧ ¬ p ^ 2 ∣ N ^ (p - 1) - 1) ↔
      ∃ M : ℕ, 3 ≤ M ∧
        {p : ℕ | p.Prime ∧ ∀ N ∈ Finset.Icc 2 M, p ^ 2 ∣ N ^ (p - 1) - 1}.Finite

/-- **Lemma 4** (Lemma 5.9). Problem 5.8 (a uniform bound `M` with `g_p ≤ M` for every
prime `p ≥ 5`) holds iff for some `M ≥ 5` the set `⋂_{3 ≤ k ≤ M, k odd} I(k)` is finite,
`I(k) = {p prime : p ∣ B_{p-k}}`.

`g_p ≤ M` is written as the existence of an odd `3 ≤ k ≤ M`, `k < p`, with
`p ∤ num(B_{p-k})`; `I(k)` is restricted to `p > k`, where `B_{p-k}` is defined.

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Lemma 4 (`integers-2024-A22-lem-4`). -/
public theorem_wanted exists_bound_bernoulli_iff_finite_iInter :
    (∃ M : ℕ, ∀ p : ℕ, p.Prime → 5 ≤ p →
        ∃ k, Odd k ∧ 3 ≤ k ∧ k ≤ M ∧ k < p ∧ ¬ (p : ℤ) ∣ (bernoulli' (p - k)).num) ↔
      ∃ M : ℕ, 5 ≤ M ∧
        {p : ℕ | p.Prime ∧ ∀ k ∈ Finset.Icc 3 M, Odd k →
          k < p ∧ (p : ℤ) ∣ (bernoulli' (p - k)).num}.Finite

/-- **Proposition 2.** (i) If there are infinitely many regular primes, then for every
`w ∉ {1, 2, 4}` some finite multiple zeta value of weight `w` is non-zero in `𝒜`.
(ii) If there are infinitely many non-Wieferich primes, then for every even `N > 0` and
every `w` some finite multiple zeta value of level `N` and weight `w` is non-zero.

Non-zero in `𝒜` means non-zero modulo infinitely many primes. Regular primes use the class
number of any `K` with `IsCyclotomicExtension {p} ℚ K`. The paper's positive weight is
relaxed to `w ≥ 0` (the empty index has value `1`).

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Proposition 2 (`integers-2024-A22-prop-2`). -/
public theorem_wanted exists_finiteMZV_ne_zero_of_conjectures :
    ({p : ℕ | p.Prime ∧ p ≠ 2 ∧ ∀ (K : Type) [Field K] [NumberField K]
        [IsCyclotomicExtension {p} ℚ K], ¬ p ∣ NumberField.classNumber K}.Infinite →
      ∀ w : ℕ, w ≠ 1 → w ≠ 2 → w ≠ 4 →
        ∃ (r : ℕ) (k : Fin r → ℕ), (∀ i, 0 < k i) ∧ ∑ i, k i = w ∧
          {p : ℕ | p.Prime ∧ coloredFiniteMZV p 1 k 0 ≠ 0}.Infinite) ∧
    ({p : ℕ | p.Prime ∧ ¬ p.IsWieferichPrime}.Infinite →
      ∀ N w : ℕ, 0 < N → Even N →
        ∃ (r : ℕ) (k : Fin r → ℕ) (c : ZMod N → Option (Fin r → ZMod N)),
          (∀ i, 0 < k i) ∧ ∑ i, k i = w ∧
            {p : ℕ | p.Prime ∧ finiteMZVColored p N k c ≠ 0}.Infinite)

end

end MetaMathlibExt
