/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Young.SemistandardTableau
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Multiset.Powerset
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.Combinatorics.Enumerative.ParkingFunction
public import MathlibExt.Combinatorics.FineNumber

/-!
# Discrete statistics of parking functions: wishlist

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6 (arXiv:2312.16786).

Parking functions are `MetaMathlibExt.IsParkingFunction n f` with `f : Fin n → Fin n`;
the value `f i` stands for the paper's preference `a_{i+1} = f i + 1`. Positions in
descent and ascent sets are the paper's 1-based indices `i ∈ [n-1]`. A descent at `i`
means `a_i > a_{i+1}`, an ascent `a_i < a_{i+1}`, a tie `a_i = a_{i+1}`, a peak
`a_{i-1} < a_i > a_{i+1}`, a valley `a_{i-1} > a_i < a_{i+1}`. A word over the multiset
`M(β)` of entries of `β` is an `f` with the same multiset of values. The statistic
encoding uses `Ordering`: `A = .lt`, `D = .gt`, `T = .eq`. These are written inline via
local notation; the new definitions are the bijection `peaklessTielessOfNondecreasing`
(the paper's `φ`) and the rearrangement `ascentToDescentRearrangement` (the paper's `ν`,
computed by the fuelled recursion `ascentToDescentRearrangementAux`).
-/

namespace MetaMathlibExt

@[expose] public section

open Classical

set_option quotPrecheck false in
/-- The parking functions of length `n`. -/
local notation "pfSet" n:max =>
  Finset.filter (fun f : Fin n → Fin n => IsParkingFunction n f) Finset.univ

set_option quotPrecheck false in
/-- The nondecreasing parking functions of length `n`. -/
local notation "ndpfSet" n:max =>
  Finset.filter (fun f : Fin n → Fin n => IsParkingFunction n f ∧ Monotone f) Finset.univ

set_option quotPrecheck false in
/-- Descent set (1-based positions) of a word `w : Fin m → Fin n`. -/
local notation "desSet" w:max =>
  Finset.image (fun i => i.val + 1)
    (Finset.filter (fun i => ∃ j, j.val = i.val + 1 ∧ w j < w i) Finset.univ)

set_option quotPrecheck false in
/-- Ascent set (1-based positions) of a word `w : Fin m → Fin n`. -/
local notation "ascSet" w:max =>
  Finset.image (fun i => i.val + 1)
    (Finset.filter (fun i => ∃ j, j.val = i.val + 1 ∧ w i < w j) Finset.univ)

set_option quotPrecheck false in
/-- `w` has no ties. -/
local notation "NoTies" w:max => ∀ i j, j.val = i.val + 1 → w i ≠ w j

set_option quotPrecheck false in
/-- `w` has no peaks. -/
local notation "NoPeaks" w:max =>
  ∀ i j k, j.val = i.val + 1 → k.val = j.val + 1 → ¬ (w i < w j ∧ w k < w j)

set_option quotPrecheck false in
/-- `w` has no valleys. -/
local notation "NoValleys" w:max =>
  ∀ i j k, j.val = i.val + 1 → k.val = j.val + 1 → ¬ (w j < w i ∧ w j < w k)

set_option quotPrecheck false in
/-- The peakless-tieless parking functions `PTPF_n`. -/
local notation "ptpfSet" n:max =>
  Finset.filter (fun f : Fin n → Fin n => IsParkingFunction n f ∧ (NoTies f) ∧ NoPeaks f)
    Finset.univ

set_option quotPrecheck false in
/-- The valleyless-tieless parking functions `VTPF_n`. -/
local notation "vtpfSet" n:max =>
  Finset.filter (fun f : Fin n → Fin n => IsParkingFunction n f ∧ (NoTies f) ∧ NoValleys f)
    Finset.univ

set_option quotPrecheck false in
/-- Statistic encoding of `f : Fin n → Fin n`: `compare a_i a_{i+1}` for `i ∈ [n-1]`. -/
local notation "statEnc" n:max f:max => fun i : Fin (n - 1) =>
  compare (f ⟨i.val, by have := i.isLt; omega⟩) (f ⟨i.val + 1, by have := i.isLt; omega⟩)

set_option quotPrecheck false in
/-- `w` has the form `A*T*`. -/
local notation "IsAstarTstar" w:max =>
  ∃ k : ℕ, ∀ i, (i.val < k → w i = Ordering.lt) ∧ (k ≤ i.val → w i = Ordering.eq)

set_option quotPrecheck false in
/-- `w` has the form `T*D*`. -/
local notation "IsTstarDstar" w:max =>
  ∃ k : ℕ, ∀ i, (i.val < k → w i = Ordering.eq) ∧ (k ≤ i.val → w i = Ordering.gt)

/-- The descent generating function of parking functions: for each `n ≥ 1`,
`∑_{α ∈ PF_n} y^{des α} = ∑_{j=0}^{n-1} d(n,j) y^j = ∑_{β ∈ PF↑_n} A_{M(β)}(y)`, where
`A_{M(β)}(y) = ∑_π y^{des π}` over the multipermutations `π` of the entries of `β`. The
printed middle sum starts at `j = 1`; it is read from `j = 0` (at `n = 1` the printed
middle sum is `0` while the other two sides are `1`). At `n = 0` the left side is `1` (the empty
function) and the middle sum is empty, so `n ≥ 1` is assumed, as in the paper.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Theorems 1 and 2
(`jis-2024-24.8.6-thm-1`, `jis-2024-24.8.6-thm-2`). -/
public theorem_wanted parkingFunction_descent_genFun (n : ℕ) (hn : 1 ≤ n) :
    ∑ f ∈ pfSet n, (Polynomial.X : Polynomial ℕ) ^ (desSet f).card =
      ∑ j ∈ Finset.range n,
        Polynomial.C ((pfSet n).filter (fun f => (desSet f).card = j)).card *
          Polynomial.X ^ j ∧
    ∑ j ∈ Finset.range n,
        Polynomial.C ((pfSet n).filter (fun f => (desSet f).card = j)).card *
          Polynomial.X ^ j =
      ∑ β ∈ ndpfSet n, ∑ w ∈ Finset.univ.filter
        (fun w : Fin n → Fin n => Finset.univ.val.map w = Finset.univ.val.map β),
          (Polynomial.X : Polynomial ℕ) ^ (desSet w).card

/-- `d(I;n) = a(J;n)` for `I ⊆ [n-1]` and `J = {n - i : i ∈ I}`, where `d` and `a` count
parking functions with descent set, respectively ascent set, exactly the given set.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Proposition 6
(`jis-2024-24.8.6-prop-6`). -/
public theorem_wanted parkingFunction_descentSet_card_eq_ascentSet_reflect (n : ℕ)
    (I : Finset ℕ) (hI : I ⊆ Finset.Ico 1 n) :
    ((pfSet n).filter (fun f => desSet f = I)).card =
      ((pfSet n).filter (fun f => ascSet f = I.image (fun i => n - i))).card

/-- There is a bijection between parking functions with descent set `I` and parking
functions with ascent set `I`, stated as equality of the two finite cardinalities.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Corollary 15
(`jis-2024-24.8.6-cor-15`). -/
public theorem_wanted parkingFunction_descentSet_card_eq_ascentSet (n : ℕ) (I : Finset ℕ)
    (hI : I ⊆ Finset.Ico 1 n) :
    ((pfSet n).filter (fun f => desSet f = I)).card =
      ((pfSet n).filter (fun f => ascSet f = I)).card

/-- Parking functions with descent set `I` and with descent set `J = {n - i : i ∈ I}` are
equinumerous, `d(I;n) = d(J;n)`.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Theorem 16
(`jis-2024-24.8.6-thm-16`). -/
public theorem_wanted parkingFunction_descentSet_card_reflect (n : ℕ) (I : Finset ℕ)
    (hI : I ⊆ Finset.Ico 1 n) :
    ((pfSet n).filter (fun f => desSet f = I)).card =
      ((pfSet n).filter (fun f => desSet f = I.image (fun i => n - i))).card

/-- `∑_{β ∈ PF↑_n} d_{M(β)}(I) = d(I;n)`, where `d_{M(β)}(I)` counts words with letters the
multiset of entries of `β` and descent set `I`.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Lemma 17
(`jis-2024-24.8.6-lem-17`). -/
public theorem_wanted sum_ndpf_multisetDescent_eq (n : ℕ) (I : Finset ℕ)
    (hI : I ⊆ Finset.Ico 1 n) :
    ∑ β ∈ ndpfSet n, (Finset.univ.filter (fun w : Fin n → Fin n =>
        Finset.univ.val.map w = Finset.univ.val.map β ∧ desSet w = I)).card =
      ((pfSet n).filter (fun f => desSet f = I)).card

/-- Recursion for `d(I;n)`: for nonempty `I ⊆ [n-1]` with `m = max I` and `I⁻ = I \ {m}`,
`d(I;n) = ∑_{β ∈ PF↑_n} ∑_{X ∈ M(β,m)} d_X(I⁻;m) - d(I⁻;n)`, with `M(β,m)` the (distinct)
sub-multisets of size `m` of the entries of `β`.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Theorem 18
(`jis-2024-24.8.6-thm-18`). -/
public theorem_wanted parkingFunction_descentSet_recursion (n : ℕ) (I : Finset ℕ)
    (hI : I ⊆ Finset.Ico 1 n) (hne : I.Nonempty) :
    (((pfSet n).filter (fun f => desSet f = I)).card : ℤ) =
      ∑ β ∈ ndpfSet n, ∑ X ∈ ((Finset.univ.val.map β).powersetCard (I.max' hne)).toFinset,
        ((Finset.univ.filter (fun w : Fin (I.max' hne) → Fin n =>
          Finset.univ.val.map w = X ∧ desSet w = I.erase (I.max' hne))).card : ℤ) -
      ((pfSet n).filter (fun f => desSet f = I.erase (I.max' hne))).card

/-- For `n ≥ 1` and `0 ≤ k ≤ n - 1`, `d([k];n) = (1/n) C(n,k) C(2n-k, n-k-1)`.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Proposition 24
(`jis-2024-24.8.6-prop-24`). -/
public theorem_wanted parkingFunction_descentSet_initial_card (n k : ℕ) (hn : 1 ≤ n)
    (hk : k ≤ n - 1) :
    ((((pfSet n).filter (fun f => desSet f = Finset.Icc 1 k)).card : ℕ) : ℚ) =
      1 / n * (n.choose k : ℚ) * ((2 * n - k).choose (n - k - 1) : ℚ)

/-- For `n ≥ 1`, the number of peakless-tieless parking functions of length `n` is the
Catalan number `C_n`.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Corollary 31
(`jis-2024-24.8.6-cor-31`). -/
public theorem_wanted card_peakless_tieless_parkingFunction (n : ℕ) (hn : 1 ≤ n) :
    (ptpfSet n).card = catalan n

/-- For `1 ≤ i ≤ n`, the number of peakless-tieless parking functions of length `n` with
last entry `a_n = i` is the Catalan-triangle entry `C_{n,i} = C(n+i-2, i-1) (n-i+1) / n`
(OEIS A009766 `T(n-1, i-1)`, with the 1-based indexing of the paper's proof).

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Corollary 32
(`jis-2024-24.8.6-cor-32`). -/
public theorem_wanted card_peakless_tieless_parkingFunction_last (n i : ℕ) (hi : 1 ≤ i)
    (hin : i ≤ n) :
    ((((ptpfSet n).filter (fun f => ∀ j : Fin n, j.val + 1 = n → (f j : ℕ) + 1 = i)).card :
      ℕ) : ℚ) = ((n + i - 2).choose (i - 1) : ℚ) * ((n - i + 1 : ℕ) : ℚ) / n

/-- For `n ≥ 1`, the number of valleyless-tieless parking functions of length `n` is the
Fine number `fineNumber (n + 1)` (OEIS A000957 at `n + 1`: `1, 2, 6, 18, 57, …`). The
printed index `F_{n+2}` is off by one in the A000957 indexing the paper cites.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Theorem 33
(`jis-2024-24.8.6-thm-33`). -/
public theorem_wanted card_valleyless_tieless_parkingFunction (n : ℕ) (hn : 1 ≤ n) :
    (((vtpfSet n).card : ℕ) : ℚ) = fineNumber (n + 1)

/-- The map `(a_1, …, a_n) ↦ (1, a_1 + 1, …, a_n + 1)` is a bijection from `VTPF_n` onto
the valleyless-tieless parking functions of length `n + 1` with `a_1 = 1` and
`a_{n+1} > 1`.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Lemma 34
(`jis-2024-24.8.6-lem-34`). -/
public theorem_wanted valleyless_tieless_prepend_one_bijOn (n : ℕ) (hn : 1 ≤ n) :
    Set.BijOn (fun f : Fin n → Fin n => (Fin.cons (0 : Fin (n + 1)) (fun i => (f i).succ) :
        Fin (n + 1) → Fin (n + 1)))
      (vtpfSet n : Set (Fin n → Fin n))
      {g | g ∈ vtpfSet (n + 1) ∧ g 0 = 0 ∧ g (Fin.last n) ≠ 0}

set_option quotPrecheck false in
/-- Number of `α ∈ PTPF_m` whose first and last entries satisfy `r`. -/
local notation "ptpfEnds" m:max r:max =>
  ((ptpfSet m).filter (fun f => ∃ i j : Fin m, i.val = 0 ∧ j.val + 1 = m ∧ r (f i) (f j))).card

/-- With `G_m`, `E_m`, `L_m` the peakless-tieless parking functions of length `m` with
`a_1 > a_m`, `a_1 = a_m`, `a_1 < a_m` (so `G_1 = L_1 = ∅`, `E_1 = {(1)}`):
`|E_{n+1}| = |L_n|` for `n ≥ 1` and `|G_{n+1}| = |L_{n+1}|` for `n ≥ 0`.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Lemma 40
(`jis-2024-24.8.6-lem-40`). -/
public theorem_wanted peakless_tieless_ends_card (n : ℕ) :
    (1 ≤ n → ptpfEnds (n + 1) (fun a b : Fin (n + 1) => a = b) =
      ptpfEnds n (fun a b : Fin n => a < b)) ∧
    ptpfEnds (n + 1) (fun a b : Fin (n + 1) => b < a) =
      ptpfEnds (n + 1) (fun a b : Fin (n + 1) => a < b)

/-- For `n ≥ 0`, the number of peakless-tieless parking functions of length `n + 1` with
`a_1 < a_{n+1}` is the Fine number `F_{n+1}` (OEIS A000957), `fineNumber (n + 1)`.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Theorem 41
(`jis-2024-24.8.6-thm-41`). -/
public theorem_wanted card_peakless_tieless_first_lt_last (n : ℕ) :
    ((ptpfEnds (n + 1) (fun a b : Fin (n + 1) => a < b) : ℕ) : ℚ) = fineNumber (n + 1)

/-- For `n ≥ 1`, exactly one parking function of length `n` has no peaks and `n - 1` ties.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Lemma 42
(`jis-2024-24.8.6-lem-42`). -/
public theorem_wanted card_peakless_parkingFunction_max_ties (n : ℕ) (hn : 1 ≤ n) :
    ((pfSet n).filter (fun f => (NoPeaks f) ∧
      (Finset.univ.filter (fun i : Fin n => ∃ j : Fin n, j.val = i.val + 1 ∧ f i = f j)).card =
        n - 1)).card = 1

/-- Every word `w ∈ {A, D, T}^{n-1}` is the statistic encoding of some parking function of
length `n`.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Theorem 48
(`jis-2024-24.8.6-thm-48`). -/
public theorem_wanted exists_parkingFunction_statEnc (n : ℕ) (w : Fin (n - 1) → Ordering) :
    ∃ f : Fin n → Fin n, IsParkingFunction n f ∧ statEnc n f = w

/-- If `α` is the unique parking function with statistic encoding `w`, then consecutive
entries of `α` differ by at most one, and every value below a value of `α` also occurs.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Lemma 49
(`jis-2024-24.8.6-lem-49`). -/
public theorem_wanted unique_statEnc_adjacent_and_downward_closed (n : ℕ)
    (f : Fin n → Fin n) (hf : IsParkingFunction n f)
    (huniq : ∀ g : Fin n → Fin n, IsParkingFunction n g → statEnc n g = statEnc n f → g = f) :
    (∀ i j : Fin n, j.val = i.val + 1 → (f j : ℕ) ≤ f i + 1 ∧ (f i : ℕ) ≤ f j + 1) ∧
    ∀ p q : Fin n, q < p → (∃ i, f i = p) → ∃ i, f i = q

/-- If `α` is the unique parking function with statistic encoding `w`, then the statistic
encoding of the nondecreasing rearrangement `β` of `α` has the form `A*T*`.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Lemma 50
(`jis-2024-24.8.6-lem-50`). -/
public theorem_wanted unique_statEnc_sorted_form (n : ℕ) (f : Fin n → Fin n)
    (hf : IsParkingFunction n f)
    (huniq : ∀ g : Fin n → Fin n, IsParkingFunction n g → statEnc n g = statEnc n f → g = f)
    (β : Fin n → Fin n) (hβ : Monotone β)
    (hβf : Finset.univ.val.map β = Finset.univ.val.map f) :
    IsAstarTstar (statEnc n β)

/-- If `α` is the unique parking function with its statistic encoding and
`α_{i-1} > α_i = ⋯ = α_j < α_{j+1}` for some `i ≤ j`, then `α_i = ⋯ = α_j = 1`.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Lemma 51
(`jis-2024-24.8.6-lem-51`). -/
public theorem_wanted unique_statEnc_valley_plateau_eq_one (n : ℕ) (f : Fin n → Fin n)
    (hf : IsParkingFunction n f)
    (huniq : ∀ g : Fin n → Fin n, IsParkingFunction n g → statEnc n g = statEnc n f → g = f)
    (a b c d : Fin n) (hab : a.val + 1 = b.val) (hbc : b ≤ c) (hcd : c.val + 1 = d.val)
    (hfa : f b < f a) (hconst : ∀ k : Fin n, b ≤ k → k ≤ c → f k = f b) (hfd : f c < f d) :
    ∀ k : Fin n, b ≤ k → k ≤ c → (f k : ℕ) = 0

/-- A word `w ∈ {A, D, T}^{n-1}` is the statistic encoding of a unique parking function of
length `n` if and only if `w ∈ {A*T*} ∪ {T*D*}`.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Theorem 52
(`jis-2024-24.8.6-thm-52`). -/
public theorem_wanted unique_parkingFunction_statEnc_iff (n : ℕ)
    (w : Fin (n - 1) → Ordering) :
    (∃! f : Fin n → Fin n, IsParkingFunction n f ∧ statEnc n f = w) ↔
      (IsAstarTstar w) ∨ IsTstarDstar w

/-- The paper's map `φ : PF↑_n → PTPF_n`: for `α = (a_1, …, a_n)`, list the tie set
`Tie(α) = {j + 1 : a_j = a_{j+1}}` in decreasing order, followed by the value set `Val(α)` in
increasing order. Zero-based: the tie `j + 1` (1-based position of the second entry of a tie)
is the value `i : Fin n` for the zero-based position `i` with `f (i - 1) = f i`, and the values
are those of `f` (both lists are read off `List.finRange n`, which is already ordered); the
concatenated list has length `n` for nondecreasing `f` (the default `k` of `getD` is never used
there).

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, the function `φ` of
Theorem 30 (`jis-2024-24.8.6-thm-30`), defined as in arXiv:2312.16786v1, Definition 4.2. -/
public def peaklessTielessOfNondecreasing (n : ℕ) (f : Fin n → Fin n) : Fin n → Fin n :=
  fun k =>
    ((List.finRange n).reverse.filter (fun i => (List.finRange n).any fun j =>
        Nat.beq (j.val + 1) i.val && Nat.beq (f j).val (f i).val) ++
      (List.finRange n).filter (fun v => (List.finRange n).any fun i =>
        Nat.beq (f i).val v.val)).getD k.val k

/-- Example 4.3 of arXiv:2312.16786v1: `φ(1, 1, 2, 3, 4, 4) = (6, 2, 1, 2, 3, 4)` (zero-based
values).

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, the function `φ` of
Theorem 30, Example (arXiv:2312.16786v1, Example 4.3). -/
public theorem peaklessTielessOfNondecreasing_example :
    peaklessTielessOfNondecreasing 6 ![0, 0, 1, 2, 3, 3] = ![5, 1, 0, 1, 2, 3] := by
  funext k
  fin_cases k <;> rfl

/-- The map `φ` is a well-defined bijection from the nondecreasing parking functions `PF↑_n`
onto the peakless-tieless parking functions `PTPF_n`.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Theorem 30
(`jis-2024-24.8.6-thm-30`; arXiv:2312.16786v1, Theorem 4.4). -/
public theorem_wanted peaklessTielessOfNondecreasing_bijOn (n : ℕ) :
    Set.BijOn (peaklessTielessOfNondecreasing n) ↑(ndpfSet n) ↑(ptpfSet n)

/-- Fuel-bounded form of the paper's map `ν` (Definition `nu`) on words `x` over `ℕ`, given as
lists: words of length at most `1` are fixed; otherwise, with `argmin`/`argmax` the (0-based)
positions of the minimal/maximal letters, Case 1 (every `argmin` position is at least every
`argmax` position) takes `i = max argmin`, `j = min argmax` and returns
`ν(x_{<j}) x_i ν(x_{j<·<i}) x_j ν(x_{>i})`; Case 2 takes `i` the greatest `argmin` position
below some `argmax` position, `j` the least `argmax` position above `i`, and returns
`ν(x_{<i}) x_j ν(x_{i<·<j}) x_i ν(x_{>j})`. Every recursive call is on a strictly shorter word,
so fuel `length x` suffices (`ascentToDescentRearrangement`).

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6,
Definition `nu` (Section 2). -/
public def ascentToDescentRearrangementAux : ℕ → List ℕ → List ℕ
  | 0, l => l
  | fuel + 1, l =>
    if l.length ≤ 1 then l else
      let mn := l.foldr min (l.headD 0)
      let mx := l.foldr max (l.headD 0)
      let amin := (List.range l.length).filter fun k => l.getD k 0 == mn
      let amax := (List.range l.length).filter fun k => l.getD k 0 == mx
      if amin.all fun a => amax.all fun b => b ≤ a then
        let i := amin.foldr max 0
        let j := amax.foldr min l.length
        ascentToDescentRearrangementAux fuel (l.take j) ++ [l.getD i 0] ++
          ascentToDescentRearrangementAux fuel ((l.drop (j + 1)).take (i - j - 1)) ++
          [l.getD j 0] ++ ascentToDescentRearrangementAux fuel (l.drop (i + 1))
      else
        let i := (amin.filter fun a => amax.any fun b => a < b).foldr max 0
        let j := (amax.filter fun b => i < b).foldr min l.length
        ascentToDescentRearrangementAux fuel (l.take i) ++ [l.getD j 0] ++
          ascentToDescentRearrangementAux fuel ((l.drop (i + 1)).take (j - i - 1)) ++
          [l.getD i 0] ++ ascentToDescentRearrangementAux fuel (l.drop (j + 1))

/-- The paper's map `ν : 𝔖_n(y) → 𝔖_n(y)` (Definition `nu`) on words over `ℕ` written as lists;
see `ascentToDescentRearrangementAux` for the two cases.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6,
Definition `nu` (Section 2). -/
public def ascentToDescentRearrangement (x : List ℕ) : List ℕ :=
  ascentToDescentRearrangementAux x.length x

/-- `ν` fixes words of length at most one.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6,
Definition `nu`, Case 0. -/
public theorem ascentToDescentRearrangement_of_length_le_one {x : List ℕ} (hx : x.length ≤ 1) :
    ascentToDescentRearrangement x = x := by
  unfold ascentToDescentRearrangement
  cases h : x.length with
  | zero => rfl
  | succ k => simp only [ascentToDescentRearrangementAux, hx, ↓reduceIte]

/-- The paper's Example of Definition `nu`: `ν(1 4 1 3 4 3 1 2 1) = 4 1 4 3 1 1 2 1 3`, with the
sub-steps `ν(1 4) = 4 1` (Case 2) and `ν(3 1 2 1) = 1 2 1 3` (Case 1).

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6,
Example following Definition `nu`. -/
public theorem ascentToDescentRearrangement_example :
    ascentToDescentRearrangement [1, 4, 1, 3, 4, 3, 1, 2, 1] = [4, 1, 4, 3, 1, 1, 2, 1, 3] ∧
      ascentToDescentRearrangement [1, 4] = [4, 1] ∧
      ascentToDescentRearrangement [3, 1, 2, 1] = [1, 2, 1, 3] := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

set_option quotPrecheck false in
/-- Ascent set (1-based positions) of a word `x : List ℕ`. -/
local notation "ascList" x:max =>
  Finset.image (· + 1)
    ((Finset.range (List.length x - 1)).filter fun i => List.getD x i 0 < List.getD x (i + 1) 0)

set_option quotPrecheck false in
/-- Descent set (1-based positions) of a word `x : List ℕ`. -/
local notation "desList" x:max =>
  Finset.image (· + 1)
    ((Finset.range (List.length x - 1)).filter fun i => List.getD x (i + 1) 0 < List.getD x i 0)

/-- For every word `x` over `ℕ` (so for every `x ∈ 𝔖_n(y)`, `y ∈ ℕ^n`),
`Asc(x) = Des(ν(x))`.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6,
Lemma 11 (`jis-2024-24.8.6-lem-11`). -/
public theorem_wanted ascList_eq_desList_ascentToDescentRearrangement (x : List ℕ) :
    ascList x = desList (ascentToDescentRearrangement x)

/-- The map `ν` is injective (on all words over `ℕ`; since `ν` rearranges letters, this is
injectivity on each orbit `𝔖_n(y)`).

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6,
Lemma 13 (`jis-2024-24.8.6-lem-13`). -/
public theorem_wanted ascentToDescentRearrangement_injective :
    Function.Injective ascentToDescentRearrangement

/-- For `y ∈ ℕ^n` (a list) and a set `I` of positions, `ν` restricts to a bijection from the
rearrangements of `y` with ascent set `I` onto the rearrangements of `y` with descent set `I`.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6,
Proposition 10 (`jis-2024-24.8.6-prop-10`). -/
public theorem_wanted ascentToDescentRearrangement_bijOn (y : List ℕ) (I : Finset ℕ) :
    Set.BijOn ascentToDescentRearrangement {x | x.Perm y ∧ ascList x = I}
      {x | x.Perm y ∧ desList x = I}

/-- Let `φ` send a valleyless-tieless parking function `v` of length `n + 1` with `a_1 = 1` and
`a_{n+1} > 1` to `flick_i(v)`, where `i` is the unique position of its maximal entry and
`flick_i(x) = (x_i, x_{i-1}, …, x_1, x_{n+1}, x_n, …, x_{i+1})`. Then `φ` is a bijection onto the
peakless-tieless parking functions of length `n + 1` with `a_1 > a_{n+1}`. With 0-based position
`p = i - 1`, entry `q` of `flick_i(v)` is `v_{p-q}` for `q ≤ p` and `v_{n+1+p-q}` otherwise. The
record's domain condition `a_{i+1} > 1` is the paper's typo for `a_{n+1} > 1` (its domain in
the same display).

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6,
Proposition 37 (`jis-2024-24.8.6-prop-37`). -/
public theorem_wanted valleyless_tieless_flick_bijOn (n : ℕ) :
    ∃ φ : (Fin (n + 1) → Fin (n + 1)) → Fin (n + 1) → Fin (n + 1),
      (∀ v ∈ vtpfSet (n + 1), v 0 = 0 → v (Fin.last n) ≠ 0 → ∀ p : Fin (n + 1),
        (∀ j, j ≠ p → v j < v p) →
        φ v = fun q => if h : q.val ≤ p.val then v ⟨p.val - q.val, by have := p.isLt; omega⟩
          else v ⟨n + 1 + p.val - q.val, by have := q.isLt; omega⟩) ∧
      Set.BijOn φ {v | v ∈ vtpfSet (n + 1) ∧ v 0 = 0 ∧ v (Fin.last n) ≠ 0}
        {g | g ∈ ptpfSet (n + 1) ∧ g (Fin.last n) < g 0}

set_option quotPrecheck false in
/-- The two-row Young diagram of shape `(n, n)`. -/
local notation "twoRowShape" n:max =>
  YoungDiagram.ofRowLens [n, n] (by simp [List.sortedGE_cons, List.sortedGE_nil])

/-- Gudmundsson's bijection: for every `n` there is a bijection `f` from the Dyck words of
semilength `n` onto the standard Young tableaux of shape `(n, n)` such that position `i` of `w`
(1-based) carries `U` (respectively `D`) exactly when `i` is an entry of the first (respectively
second) row of `f(w)`. Standard tableaux are the semistandard tableaux of shape `(n, n)` whose
entries on the `2n` cells are distinct and lie in `[1, 2n]`.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6,
Lemma 22 (Gudmundsson, Theorem 6) (`jis-2024-24.8.6-lem-22`). -/
public theorem_wanted exists_dyckWord_standardYoungTableau_bijOn (n : ℕ) :
    ∃ f : DyckWord → SemistandardYoungTableau (twoRowShape n),
      (∀ w : DyckWord, w.semilength = n → ∀ i : ℕ,
        (w.toList[i]? = some DyckStep.U → ∃ j < n, f w 0 j = i + 1) ∧
        (w.toList[i]? = some DyckStep.D → ∃ j < n, f w 1 j = i + 1)) ∧
      Set.BijOn f {w | w.semilength = n}
        {T | (∀ c ∈ twoRowShape n,
            ∀ c' ∈ twoRowShape n, T c.1 c.2 = T c'.1 c'.2 → c = c') ∧
          ∀ c ∈ twoRowShape n, 1 ≤ T c.1 c.2 ∧ T c.1 c.2 ≤ 2 * n}

/-- For every `n` the map `g` sending a Dyck word `w` of semilength `n` to the sequence whose
`i`th entry is one plus the number of `D`s before the `i`th `U` of `w` is a bijection onto the
nondecreasing parking functions of length `n`. In the zero-based convention of this file,
`g w i` is the number of `D`s before the `(i + 1)`st `U`: if the 0-based position `k` of `w`
holds `U` and `i` letters `U` precede it, then `g w i` is the number of `D`s preceding it.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6,
Lemma 23 (`jis-2024-24.8.6-lem-23`). -/
public theorem_wanted exists_dyckWord_nondecreasing_parkingFunction_bijOn (n : ℕ) :
    ∃ g : DyckWord → Fin n → Fin n,
      (∀ w : DyckWord, w.semilength = n → ∀ (i : Fin n) (k : ℕ),
        w.toList[k]? = some DyckStep.U → (w.toList.take k).count DyckStep.U = i.val →
        ((g w i : Fin n) : ℕ) = (w.toList.take k).count DyckStep.D) ∧
      Set.BijOn g {w | w.semilength = n} ↑(ndpfSet n)

/-- For `n ≥ 2`, the number of parking functions of length `n` with no peaks and exactly `n - 2`
ties is `(n - 1) n`. The paper prints `n(n + 1)`, which contradicts its own table
(`2, 6, 12, 20, 30` for `n = 2, …, 6`); its proof counts tuples with `i` leading ones followed by
`n - i ≥ 1` copies of one value, so `1 ≤ i ≤ n - 1` and each monotone direction contributes
`∑_{i=1}^{n-1} i`.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6,
Lemma 43 (`jis-2024-24.8.6-lem-43`). -/
public theorem_wanted card_peakless_parkingFunction_ties_eq_sub_two (n : ℕ) (hn : 2 ≤ n) :
    ((pfSet n).filter (fun f => (NoPeaks f) ∧
      (Finset.univ.filter (fun i : Fin n => ∃ j : Fin n, j.val = i.val + 1 ∧ f i = f j)).card =
        n - 2)).card = (n - 1) * n

end

end MetaMathlibExt
