/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fintype.Perm
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

namespace MetaMathlibExt

@[expose] public section

/-- The value `τ(j)` of a permutation `τ` of `Fin d` at a natural position `j` (`0` when
`j ≥ d`), used to read off descents.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Section 1 (descent statistics). -/
public def permValueAt {d : ℕ} (τ : Equiv.Perm (Fin d)) (j : ℕ) : ℕ :=
  if h : j < d then τ ⟨j, h⟩ else 0

/-- The descent set `Des(τ) = {j : τ(j) > τ(j + 1)}` of a permutation `τ ∈ S_d`, with positions
`j ∈ {1, …, d - 1}` numbered from `1` as in the paper.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Section 1. -/
public def permDescentSet {d : ℕ} (τ : Equiv.Perm (Fin d)) : Finset ℕ :=
  ((Finset.range (d - 1)).filter fun j => permValueAt τ (j + 1) < permValueAt τ j).map
    ⟨(· + 1), add_left_injective 1⟩

/-- The number of descents `des(τ) = |Des(τ)|`.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Section 1. -/
public def permDes {d : ℕ} (τ : Equiv.Perm (Fin d)) : ℕ := (permDescentSet τ).card

/-- The major index `maj(τ) = ∑_{j ∈ Des(τ)} j`.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Section 1. -/
public def permMaj {d : ℕ} (τ : Equiv.Perm (Fin d)) : ℕ := ∑ j ∈ permDescentSet τ, j

/-- The Euler-Mahonian polynomial `E_d(x, y) = ∑_{τ ∈ S_d} x^{des(τ)} y^{maj(τ)}`, evaluated
at elements `x, y` of a commutative ring.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Section 1. -/
public def eulerMahonian (R : Type*) [CommRing R] (d : ℕ) (x y : R) : R :=
  ∑ τ : Equiv.Perm (Fin d), x ^ permDes τ * y ^ permMaj τ

/-- `E_1(x, y) = 1`.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Section 1 (`F_1 = 1` in recursion (1)). -/
public theorem eulerMahonian_one (R : Type*) [CommRing R] (x y : R) :
    eulerMahonian R 1 x y = 1 := by
  simp [eulerMahonian, permDes, permMaj, permDescentSet]

/-- `E_3(x, y) = 1 + 2xy + 2xy² + x²y³`, checked at `x = 2`, `y = 3`: the six permutations of
`S_3` have `(des, maj) = (0,0), (1,1), (1,1), (1,2), (1,2), (2,3)`.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Section 1. -/
public theorem eulerMahonian_three_two_three : eulerMahonian ℤ 3 2 3 = 157 := by decide

/-- In `S_3` exactly two permutations have one descent at position `1` (`maj = 1`).

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Section 1. -/
public theorem card_perm_three_des_one_maj_one :
    ((Finset.univ : Finset (Equiv.Perm (Fin 3))).filter
      fun τ => permDes τ = 1 ∧ permMaj τ = 1).card = 2 := by decide

/-- Position (counted from `0`) of the `k`th link of the multifold partition diamond whose
diamonds have `d₁, …, d_M` folds (`ds = [d₁, …, d_M]`): `∑_{m < k} (d_{m+1} + 1)`.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Figure 3 and Section 3. -/
public def diamondLinkPos (ds : List ℕ) (k : ℕ) : ℕ := ((ds.take k).map (· + 1)).sum

/-- Number of parts `c = d₁ + ⋯ + d_M + M + 1` of the multifold partition diamond.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Figure 3 (`c = M(d + 1) + 1`). -/
public def diamondSize (ds : List ℕ) : ℕ := diamondLinkPos ds ds.length + 1

/-- The link positions `0 = L₀ < L₁ < ⋯ < L_M = c - 1`.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Figure 3. -/
public def diamondLinks (ds : List ℕ) : Finset ℕ :=
  (Finset.range (ds.length + 1)).image (diamondLinkPos ds)

/-- The parts `b : ℕ → ℕ` (positions `0, …, c - 1`) form a multifold partition diamond with fold
sum `i` and link sum `j`: in the `k`th diamond the link `b(L_k)` is at most each of its `d_k`
folds, each of which is at most the next link `b(L_{k+1})`. This is the paper's model of a
`P`-partition `m` of the poset `{1} ⊕ Q_{d₁} ⊕ ⋯ ⊕ Q_{d_M}` (order preserving,
`j ⪯ k ⇒ m_j ≤ m_k`, parts in `ℤ_{≥0}`), so the first part is the smallest.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Sections 2-3. -/
public def IsMultifoldDiamond (ds : List ℕ) (i j : ℕ) (b : ℕ → ℕ) : Prop :=
  (∀ k ∈ Finset.range ds.length, ∀ f ∈ Finset.Icc 1 (ds.getD k 0),
      b (diamondLinkPos ds k) ≤ b (diamondLinkPos ds k + f) ∧
        b (diamondLinkPos ds k + f) ≤ b (diamondLinkPos ds (k + 1))) ∧
    (∑ p ∈ (Finset.range (diamondSize ds)).filter (· ∉ diamondLinks ds), b p) = i ∧
    (∑ p ∈ diamondLinks ds, b p) = j

/-- Decidability of `IsMultifoldDiamond`.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Sections 2-3. -/
public instance (ds : List ℕ) (i j : ℕ) : DecidablePred (IsMultifoldDiamond ds i j) :=
  fun b => by unfold IsMultifoldDiamond; infer_instance

/-- Reads a part vector `a : Fin c → Fin n` as a function `ℕ → ℕ` (`0` beyond `c`).

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Section 2. -/
public def diamondPart {ds : List ℕ} {n : ℕ} (a : Fin (diamondSize ds) → Fin n) (p : ℕ) : ℕ :=
  if h : p < diamondSize ds then (a ⟨p, h⟩ : ℕ) else 0

/-- Number of multifold partition diamonds with fold sum `i` and link sum `j` (every part is
at most `i + j`, so the search over `Fin c → Fin (i + j + 1)` is exhaustive).

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, equation (2) and Section 3. -/
public def multifoldDiamondCount (ds : List ℕ) (i j : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (diamondSize ds) → Fin (i + j + 1))).filter fun a =>
    IsMultifoldDiamond ds i j (diamondPart a)).card

/-- Small value: one single-fold diamond `a₁ ≤ a₂ ≤ a₃` with fold sum `1` and link sum `1`.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, equation (2). -/
public theorem multifoldDiamondCount_one_one_one : multifoldDiamondCount [1] 1 1 = 1 := by
  decide

/-- Small value: two `2`-fold diamonds of length `1` with fold sum `1` and link sum `2`.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, equation (2). -/
public theorem multifoldDiamondCount_two_one_two : multifoldDiamondCount [2] 1 2 = 2 := by
  decide

/-- The bivariate generating function `σ_{d₁,…,d_M}(a, b) = ∑ a^{fold sum} b^{link sum}` in
`ℤ⟦a, b⟧` (`a = X 0`, `b = X 1`); `σ_{d,M}` is the case `ds = [d, …, d]` (`M` copies).

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, equation (2) and Section 3. -/
public def multifoldDiamondSeries (ds : List ℕ) : MvPowerSeries (Fin 2) ℤ :=
  fun e => (multifoldDiamondCount ds (e 0) (e 1) : ℤ)

/-- The Dockery-Jameson-Sellers-Wilson polynomials `F_d`, defined by `F_1 = 1` and
`F_d(q₀, w) = ((1 - q₀w^d) F_{d-1}(q₀, w) - w(1 - q₀) F_{d-1}(q₀w, w))/(1 - w)`, are the
Euler-Mahonian polynomials. Since `1 - w` is a nonzerodivisor in `ℤ[q₀, w]` and `E_1 = 1`
(`eulerMahonian_one`), this is stated as: `E_d` satisfies the recursion (1) multiplied by
`1 - w`, for every `d ≥ 1`, as an identity in every commutative ring.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Theorem 1 (`integers-2026-A13-thm-1`) with
recursion (1). -/
public theorem_wanted eulerMahonian_succ_recursion (R : Type*) [CommRing R] (d : ℕ)
    (hd : 1 ≤ d) (x y : R) :
    (1 - y) * eulerMahonian R (d + 1) x y =
      (1 - x * y ^ (d + 1)) * eulerMahonian R d x y -
        y * (1 - x) * eulerMahonian R d (x * y) y

/-- For positive integers `d` and `M`,
`σ_{d,M}(a, b) = ∏_{n=1}^M E_d(a^{(n-1)d} bⁿ, a) /
((1 - a^{Md} b^{M+1}) ∏_{n=1}^M ∏_{j=0}^d (1 - a^{nd-j} bⁿ))`, stated with the denominator
multiplied out in `ℤ⟦a, b⟧`.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Theorem 2 (`integers-2026-A13-thm-2`). -/
public theorem_wanted partitionDiamond_genFun (d M : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M) :
    (1 - MvPowerSeries.X 0 ^ (M * d) * MvPowerSeries.X 1 ^ (M + 1)) *
        (∏ n ∈ Finset.Icc 1 M, ∏ j ∈ Finset.range (d + 1),
          (1 - MvPowerSeries.X 0 ^ (n * d - j) * MvPowerSeries.X 1 ^ n)) *
        multifoldDiamondSeries (List.replicate M d) =
      ∏ n ∈ Finset.Icc 1 M, eulerMahonian (MvPowerSeries (Fin 2) ℤ) d
        (MvPowerSeries.X 0 ^ ((n - 1) * d) * MvPowerSeries.X 1 ^ n) (MvPowerSeries.X 0)

/-- Multifold partition diamonds: for positive integers `d₁, …, d_M` (`ds = [d₁, …, d_M]`,
`M ≥ 1`) and `ω_k = ∑_{j=k+1}^M d_j`,
`σ_{d₁,…,d_M}(a, b) = ∏_{k=1}^M E_{d_k}(a^{ω_k} b^{M-k+1}, a) /
((1 - a^{ω₀} b^{M+1}) ∏_{k=1}^M ∏_{j=0}^{d_k} (1 - a^{ω_k + d_k - j} b^{M-k+1}))`, stated with
the denominator multiplied out in `ℤ⟦a, b⟧`. The `k`th diamond (with `d_k` folds) is the `k`th
from the smallest part, as in the paper's poset `{1} ⊕ Q_{d₁} ⊕ ⋯ ⊕ Q_{d_M}`; with the parts
read in the opposite order the formula holds for the reversed sequence only (for `ds = [1, 2]`
the coefficient of `ab` would be `1`, not `2`).

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Theorem 3 (`integers-2026-A13-thm-3`). -/
public theorem_wanted multifoldPartitionDiamond_genFun (ds : List ℕ) (hds : ds ≠ [])
    (hpos : ∀ d ∈ ds, 1 ≤ d) :
    (1 - MvPowerSeries.X 0 ^ ds.sum * MvPowerSeries.X 1 ^ (ds.length + 1)) *
        (∏ k ∈ Finset.Icc 1 ds.length, ∏ j ∈ Finset.range (ds.getD (k - 1) 0 + 1),
          (1 - MvPowerSeries.X 0 ^ ((ds.drop k).sum + ds.getD (k - 1) 0 - j) *
            MvPowerSeries.X 1 ^ (ds.length - k + 1))) *
        multifoldDiamondSeries ds =
      ∏ k ∈ Finset.Icc 1 ds.length, eulerMahonian (MvPowerSeries (Fin 2) ℤ) (ds.getD (k - 1) 0)
        (MvPowerSeries.X 0 ^ (ds.drop k).sum * MvPowerSeries.X 1 ^ (ds.length - k + 1))
        (MvPowerSeries.X 0)

/-- Schmidt type `d`-fold partition diamonds (Dockery-Jameson-Sellers-Wilson): their generating
function, summing only the links, is `∏_{n ≥ 1} E_d(qⁿ, 1)/(1 - qⁿ)^{d+1}`. A Schmidt type
diamond is a finitely supported `a : ℕ →₀ ℕ` with links at positions `k(d + 1)` and folds
`a(k(d+1) + f)`, `1 ≤ f ≤ d`, between `a(k(d+1)) ≥ a(k(d+1) + f) ≥ a((k+1)(d+1))`; its weight is
the link sum. The infinite product is stated through its truncations: for every `N`, the
coefficients of `qⁿ`, `n ≤ N`, of `∏_{m=1}^N (1 - q^m)^{d+1} · S(q)` and of
`∏_{m=1}^N E_d(q^m, 1)` agree (factors with `m > N` are `1` modulo `q^{N+1}`).

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Corollary 1 (`integers-2026-A13-cor-1`), quoting
Dockery-Jameson-Sellers-Wilson. -/
public theorem_wanted schmidtPartitionDiamond_genFun (d : ℕ) (hd : 1 ≤ d) (N n : ℕ)
    (hn : n ≤ N) :
    PowerSeries.coeff n
        ((∏ m ∈ Finset.Icc 1 N, (1 - PowerSeries.X ^ m) ^ (d + 1)) *
          PowerSeries.mk fun w => ((Set.ncard {a : ℕ →₀ ℕ |
            (∀ k f : ℕ, 1 ≤ f → f ≤ d →
              a (k * (d + 1) + f) ≤ a (k * (d + 1)) ∧
                a ((k + 1) * (d + 1)) ≤ a (k * (d + 1) + f)) ∧
            (a.support.filter fun p => p % (d + 1) = 0).sum a = w} : ℕ) : ℤ)) =
      PowerSeries.coeff n
        (∏ m ∈ Finset.Icc 1 N, eulerMahonian (PowerSeries ℤ) d (PowerSeries.X ^ m) 1)

end

end MetaMathlibExt
