/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Winnowing: density of local fingerprinting algorithms

Schleimer, Wilkerson and Aiken (2003): a document is hashed into the sequence `h_1, …, h_n` of the
hashes of its `k`-grams; with guarantee threshold `t` the window size is `w = t - k + 1`, and every
window of `w` consecutive hashes must contribute a selected hash. A fingerprinting algorithm is
local (Definition 2) with selection function `S`, which maps a `w`-tuple of hashes to an offset in
`{0, …, w - 1}`, if for every window `h_i, …, h_{i+w-1}` the hash at position `i + S(window)` is
selected; other positions of the input may be selected too. Winnowing (Definition 1) selects the
minimum hash of each window, the rightmost one on ties, and saves exactly the selected positions.

* Lemma 1: any matching pair of substrings of length at least `t` is found by any local algorithm.
* Section 3.1: for independent uniformly distributed hashes, ignoring ties (the source assumes
  "the space of hash values is very large so that we can safely ignore the possibility that there
  is a tie"), the density of winnowing (the expected proportion of selected hashes) is
  `2 / (w + 1)`: a window other than the first is charged (is the first window selecting its
  minimum) with probability `2 / (w + 1)`.
* Theorem 1: any local algorithm with noise threshold `k` and guarantee `t = w + k - 1` has density
  at least `1.5 / (w + 1)` for independent uniformly distributed hashes.

Positions and windows are `0`-based here (the source numbers windows from `1`). The no-ties model
is formalized exactly: the hashes are i.i.d. uniform on a finite linear order `H` conditioned on
all `n` values being distinct, which needs `n ≤ |H|`; the same counts hold for a uniformly random
permutation of the positions. The density limit `n → ∞` is stated for uniform permutations as the
source's no-ties idealization: for a fixed finite `H` with ties allowed, the limit can differ
from `2 / (w + 1)` (for `w = 2` and `|H| = 2` it is `3 / 4`). Theorem 1 allows ties: the hashes
are uniform on all of `Fin n → H` for a finite nonempty `H`, and density is the limit inferior of
`E[#selected] / n`.

Sources: S. Schleimer, D. S. Wilkerson and A. Aiken, "Winnowing: local algorithms for document
fingerprinting", Proceedings of the 2003 ACM SIGMOD International Conference on Management of Data,
76–85, doi:10.1145/872757.872770, Definitions 1–2, Section 3.1, Lemma 1 and Theorem 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Bioinformatics.Assembly.DeBruijn
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.WinnowingFingerprintWanted

open Filter Topology
open Cslib.Bioinformatics.Assembly.DeBruijn (kmers)

variable {H : Type*} [LinearOrder H]

/-- The window of `w` hashes starting at position `i` (`i + w ≤ n`), as a `w`-tuple. -/
def window {n : ℕ} (w : ℕ) (h : Fin n → H) (i : ℕ) (hi : i + w ≤ n) : Fin w → H :=
  fun j => h ⟨i + j, by omega⟩

/-- The offset of the **rightmost minimum** of a `w`-tuple (`0` for `w = 0`). -/
noncomputable def rightmostArgmin {w : ℕ} (x : Fin w → H) : ℕ :=
  ((Finset.univ.filter fun j : Fin w => ∀ j', x j ≤ x j').image Fin.val).sup id

/-- The positions selected by the local algorithm with selection function `S`: `i + S(window i)`
for every window `i` with `i + w ≤ n`. -/
noncomputable def localSel {n w : ℕ} (S : (Fin w → H) → Fin w) (h : Fin n → H) : Finset ℕ :=
  (Finset.range (n + 1 - w)).attach.image fun i =>
    if hi : i.1 + w ≤ n then i.1 + S (window w h i.1 hi) else 0

/-- **Winnowing** (Definition 1): the positions of the rightmost minimum of every window of size
`w ≥ 1`, all of them positions of the input; no position for `w = 0`, which has no windows. -/
noncomputable def winnow {n : ℕ} (w : ℕ) (h : Fin n → H) : Finset ℕ :=
  if w = 0 then ∅ else
    (Finset.range (n + 1 - w)).attach.image fun i =>
      if hi : i.1 + w ≤ n then i.1 + rightmostArgmin (window w h i.1 hi) else 0

/-- **Charged window.** Window `i` of winnowing, of size `w ≥ 1`, is charged when it selects a
position that no window to its left selects (`C(p)` is the leftmost window selecting `p`); no
window is charged for `w = 0`. -/
def Charged {n : ℕ} (w : ℕ) (h : Fin n → H) (i : ℕ) : Prop :=
  0 < w ∧ ∃ hi : i + w ≤ n, ∀ i' (hi' : i' + w ≤ n), i' < i →
    i' + rightmostArgmin (window w h i' hi') ≠ i + rightmostArgmin (window w h i hi)

/-- **Local algorithm** (Definition 2). The output map `F` is local with selection function `S`
when, on every input `h` of every length `n`, it selects at least the positions `i + S(window i)`
and only positions of the input (`F n h ⊆ {0, …, n - 1}`). -/
def IsLocal {w : ℕ} (S : (Fin w → H) → Fin w) (F : ∀ n, (Fin n → H) → Finset ℕ) : Prop :=
  ∀ n (h : Fin n → H), localSel S h ⊆ F n h ∧ F n h ⊆ Finset.range n

/-- The hashes of the `k`-grams of a document `u`: at `i`, `g` applied to entry `i` of
`Cslib.Bioinformatics.Assembly.DeBruijn.kmers k u`, the `k`-gram `(u.drop i).take k` starting at
position `i ≤ |u| - k` (the `range` and `map` in `kmers` give it length `|u| + 1 - k`). -/
def kgramHashes {α : Type*} (k : ℕ) (g : List α → H) (u : List α) :
    Fin (u.length + 1 - k) → H :=
  fun i => g ((kmers k u)[i.1]'(by
    simpa only [kmers, List.length_map, List.length_range] using i.2))

/-- **Local algorithms find every long match** (Schleimer, Wilkerson and Aiken 2003, Lemma 1): for
`k ≥ 1`, `w ≥ 1`, guarantee `t = w + k - 1`, any hash `g` of `k`-grams, any selection function
`S` and any local algorithm `F` with selection function `S`: if documents `u` and `v` share a
substring of length `L ≥ t`, at offset `p` in `u` and `q` in `v`, then some `j ≤ L - k` gives
selected `k`-gram positions `p + j` in `u` and `q + j` in `v`, both of which hash the same
`k`-gram of the shared substring.

Source: Schleimer, Wilkerson and Aiken (2003), Lemma 1. -/
public theorem_wanted exists_selected_of_shared_substring {α : Type*} (k w : ℕ) (hk : 1 ≤ k)
    (hw : 1 ≤ w) (g : List α → H) (S : (Fin w → H) → Fin w) (F : ∀ n, (Fin n → H) → Finset ℕ)
    (hF : IsLocal S F) (u v : List α) (p q L : ℕ) (hL : w + k - 1 ≤ L)
    (hpu : p + L ≤ u.length) (hqv : q + L ≤ v.length)
    (hshared : (u.drop p).take L = (v.drop q).take L) :
    ∃ j, j + k ≤ L ∧ p + j ∈ F _ (kgramHashes k g u) ∧ q + j ∈ F _ (kgramHashes k g v)

/-- **Charging probability under uniform permutations** (Schleimer, Wilkerson and Aiken 2003,
Section 3.1, the no-ties model): for `w ≥ 1` and a window `i` with `1 ≤ i` and `i + w ≤ n`, among
all permutations `σ` of the `n` positions, used as hashes, exactly the fraction `2 / (w + 1)`
charge window `i`: `#{σ | window i charged} · (w + 1) = 2 · n!`.

Source: Schleimer, Wilkerson and Aiken (2003), Section 3.1. -/
public theorem_wanted card_charged_perm (n w i : ℕ) (hw : 1 ≤ w) (hi₁ : 1 ≤ i) (hi : i + w ≤ n) :
    Nat.card {σ : Equiv.Perm (Fin n) // Charged w (fun x => σ x) i} * (w + 1) =
      2 * n.factorial

/-- **Expected number of winnowing fingerprints, uniform permutations**, a finite-length
consequence of Schleimer, Wilkerson and Aiken (2003), Section 3.1, which gives the charging
probability and the density but not this boundary-corrected count: for `n ≥ w ≥ 1`, the average
over all permutations `σ` of the `n` positions of `#winnow σ` is `1 + 2 (n - w) / (w + 1)`, exactly
one at `n = w`:
`(∑_σ #winnow σ) · (w + 1) = n! · ((w + 1) + 2 (n - w))`.

Source: a finite-length consequence of Schleimer, Wilkerson and Aiken (2003), Section 3.1. -/
public theorem_wanted sum_card_winnow_perm (n w : ℕ) (hw : 1 ≤ w) (hn : w ≤ n) :
    (∑ σ : Equiv.Perm (Fin n), (winnow w fun x => σ x).card) * (w + 1) =
      n.factorial * ((w + 1) + 2 * (n - w))

/-- **Expected number of winnowing fingerprints, i.i.d. uniform hashes without ties**, a
finite-length consequence of Schleimer, Wilkerson and Aiken (2003), Section 3.1, with the source's
no-ties assumption made exact; the source gives the charging probability and the density but not
this boundary-corrected count: for a finite linear order `H`, `n ≥ w ≥ 1` and `n ≤ |H|` (so that
injective hash sequences exist), the average of `#winnow h` over the injective `h : Fin n → H`
(i.i.d. uniform hashes conditioned on being distinct) is `1 + 2 (n - w) / (w + 1)`, exactly one at
`n = w`:
`(∑_{h injective} #winnow h) · (w + 1) = #{h injective} · ((w + 1) + 2 (n - w))`.

Source: a finite-length consequence of Schleimer, Wilkerson and Aiken (2003), Section 3.1. -/
public theorem_wanted sum_card_winnow_injective [Fintype H] [DecidableEq H] (n w : ℕ)
    (hw : 1 ≤ w) (hn : w ≤ n) (hH : n ≤ Fintype.card H) :
    (∑ h ∈ Finset.univ.filter (fun h : Fin n → H => Function.Injective h), (winnow w h).card) *
        (w + 1) =
      (Finset.univ.filter fun h : Fin n → H => Function.Injective h).card *
        ((w + 1) + 2 * (n - w))

/-- **Winnowing density `2 / (w + 1)`** (Schleimer, Wilkerson and Aiken 2003, Section 3.1, the
source's no-ties idealization): for `w ≥ 1`, the expected proportion of positions selected by
winnowing a uniformly random permutation of `n` positions tends to `2 / (w + 1)` as `n → ∞`.

Source: Schleimer, Wilkerson and Aiken (2003), Section 3.1. -/
public theorem_wanted tendsto_density_winnow_perm (w : ℕ) (hw : 1 ≤ w) :
    Tendsto (fun n : ℕ => ((∑ σ : Equiv.Perm (Fin n), (winnow w fun x => σ x).card : ℕ) : ℝ) /
        (n.factorial * n)) atTop (𝓝 (2 / (w + 1)))

/-- **Lower bound for local algorithms** (Schleimer, Wilkerson and Aiken 2003, Theorem 1): for a
finite nonempty linear order `H` of hash values, `w ≥ 1`, any selection function `S` and any
local algorithm `F` with selection function `S`, under i.i.d. uniform hashes (`h` uniform on
`Fin n → H`, ties allowed) the density is at least `1.5 / (w + 1)`: for every `ε > 0`, for all
large `n`, `E[#F h] / n ≥ 1.5 / (w + 1) - ε`.

Source: Schleimer, Wilkerson and Aiken (2003), Theorem 1. -/
public theorem_wanted density_local_ge [Fintype H] [Nonempty H] (w : ℕ) (hw : 1 ≤ w)
    (S : (Fin w → H) → Fin w) (F : ∀ n, (Fin n → H) → Finset ℕ) (hF : IsLocal S F) (ε : ℝ)
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 1.5 / (w + 1) - ε ≤
      ((∑ h : Fin n → H, (F n h).card : ℕ) : ℝ) / ((Fintype.card H : ℝ) ^ n * n)

end WantedExt.Biology.ComputationalBiology.WinnowingFingerprintWanted
