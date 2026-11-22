/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Combinatorics.FineNumber
public import MathlibExt.Combinatorics.NoncrossingPartition.Basic
public import Mathlib.Combinatorics.Enumerative.Catalan.Tree

namespace MetaMathlibExt

@[expose] public section

/-- The spot taken under the `k`-Naples rule on the spots `1, …, n` by a car preferring `a`
when the spots in `occ` are occupied: `a` if free; otherwise the first free spot among
`a - 1, …, a - k` (checked in decreasing order, spots `≥ 1`); otherwise the first free spot
after `a` (up to `n`); `none` if the car cannot park, including when `a` is not one of the
spots `1, …, n`.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 1. -/
public def naplesSpot (n k : ℕ) (occ : List ℕ) (a : ℕ) : Option ℕ :=
  if ¬ (1 ≤ a ∧ a ≤ n) then none else
  if a ∉ occ then some a else
    match ((List.range k).map fun j => a - (j + 1)).find? (fun s => decide (1 ≤ s ∧ s ∉ occ)) with
    | some s => some s
    | none => (List.range' (a + 1) (n - a)).find? (fun s => decide (s ∉ occ))

/-- Park the cars with preferences `as` in order under the `k`-Naples rule on the spots
`1, …, n`, starting from the occupied spots `occ`; returns the final occupied spots (most
recent first), or `none` if some car cannot park.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 1. -/
public def naplesPark (n k : ℕ) : List ℕ → List ℕ → Option (List ℕ)
  | occ, [] => some occ
  | occ, a :: as => (naplesSpot n k occ a).bind fun s => naplesPark n k (s :: occ) as

/-- A `k`-Naples parking function of length `n`: a parking preference `α ∈ [n]^n` with which
all `n` cars park under the `k`-Naples rule (`k = 0` gives ordinary parking functions).

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 1. -/
public def IsNaplesParkingFunction (k : ℕ) {n : ℕ} (α : Fin n → ℕ) : Prop :=
  (∀ i, 1 ≤ α i ∧ α i ≤ n) ∧ (naplesPark n k [] (List.ofFn α)).isSome

public instance (k n : ℕ) : DecidablePred (IsNaplesParkingFunction k (n := n)) := fun α => by
  unfold IsNaplesParkingFunction
  infer_instance

/-- Characteristic example: with `k = 2` the cars of `(6, 6, 6, 5, 5, 2, 1)` park in spots
`6, 5, 4, 3, 7, 2, 1`.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 1. -/
public theorem naplesPark_example :
    naplesPark 7 2 [] [6, 6, 6, 5, 5, 2, 1] = some [1, 2, 7, 3, 4, 5, 6] := by
  decide

/-- Characteristic example: `(6, 6, 6, 5, 5, 2, 1)` is a `2`-Naples but not a `1`-Naples
parking function.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 1. -/
public theorem isNaplesParkingFunction_example :
    IsNaplesParkingFunction 2 ![6, 6, 6, 5, 5, 2, 1] ∧
      ¬ IsNaplesParkingFunction 1 ![6, 6, 6, 5, 5, 2, 1] := by
  decide

/-- `I_{n,k}`: the number of ascending (weakly increasing) `k`-Naples parking functions of
length `n`.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Theorem 3. -/
public def ascendingNaplesCount (n k : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin n => Finset.Icc 1 n).filter fun α =>
    (∀ i j : Fin n, i ≤ j → α i ≤ α j) ∧ IsNaplesParkingFunction k α).card

/-- `U_{n,k}`: the number of ascending `k`-Naples parking functions of length `n` that start
with `1` (so `U_{0,k} = 0`).

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Theorem 3. -/
public def ascendingNaplesOneCount (n k : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin n => Finset.Icc 1 n).filter fun α =>
    (∀ i j : Fin n, i ≤ j → α i ≤ α j) ∧ IsNaplesParkingFunction k α ∧
      ∃ i : Fin n, i.val = 0 ∧ α i = 1).card

/-- The number of descending (weakly decreasing) `k`-Naples parking functions of length `n`.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Proposition 2. -/
public def descendingNaplesCount (n k : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin n => Finset.Icc 1 n).filter fun α =>
    (∀ i j : Fin n, i ≤ j → α j ≤ α i) ∧ IsNaplesParkingFunction k α).card

/-- The number of descending strictly `k`-Naples parking functions of length `n`: descending
preferences that are `k`-Naples but not `(k - 1)`-Naples (used for `k ≥ 1`).

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Proposition 4. -/
public def descendingStrictNaplesCount (n k : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin n => Finset.Icc 1 n).filter fun α =>
    (∀ i j : Fin n, i ≤ j → α j ≤ α i) ∧ IsNaplesParkingFunction k α ∧
      ¬ IsNaplesParkingFunction (k - 1) α).card

/-- Characteristic values: `I_{2,1} = 3`, `U_{2,1} = 2`, and there are `3` descending
`1`-Naples parking functions of length `2`, of which `1` is strictly `1`-Naples.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 4. -/
public theorem naplesCount_two_one :
    ascendingNaplesCount 2 1 = 3 ∧ ascendingNaplesOneCount 2 1 = 2 ∧
      descendingNaplesCount 2 1 = 3 ∧ descendingStrictNaplesCount 2 1 = 1 := by
  decide

/-- The height after the first `j` steps of a lattice path `p` (`true` = Up `(1, 1)`,
`false` = Down `(1, -1)`).

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 3. -/
public def latticeHeight {m : ℕ} (p : Fin m → Bool) (j : ℕ) : ℤ :=
  ∑ i : Fin m, if i.val < j then (if p i then 1 else -1) else 0

/-- The height after the first `j` steps of a Dyck word given by its list of steps (`U` up,
`D` down), for Mathlib's `DyckWord` API.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 3. -/
public def dyckStepHeight (l : List DyckStep) (j : ℕ) : ℤ :=
  ((l.take j).count DyckStep.U : ℤ) - ((l.take j).count DyckStep.D : ℤ)

/-- A `k`-Dyck path of length `n`: a path of `2n` Up/Down steps ending at height `0` that
never goes below the line `y = -k` and ends with a Down step.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 3. -/
public def IsKDyckPath (n k : ℕ) (p : Fin (2 * n) → Bool) : Prop :=
  latticeHeight p (2 * n) = 0 ∧ (∀ j ≤ 2 * n, -(k : ℤ) ≤ latticeHeight p j) ∧
    ∀ i : Fin (2 * n), i.val + 1 = 2 * n → p i = false

public instance (n k : ℕ) : DecidablePred (IsKDyckPath n k) := fun p => by
  unfold IsKDyckPath
  infer_instance

/-- Characteristic value: `DUUD` is a `1`-Dyck path but not a `0`-Dyck path, and the height
of `UUD` after its three steps is `1`.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 3. -/
public theorem isKDyckPath_example :
    IsKDyckPath 2 1 ![false, true, true, false] ∧ ¬ IsKDyckPath 2 0 ![false, true, true, false] ∧
      dyckStepHeight [DyckStep.U, DyckStep.U, DyckStep.D] 3 = 1 := by
  unfold IsKDyckPath latticeHeight dyckStepHeight
  decide

/-- Proposition 1: a `k`-Naples parking function is also a `(k + 1)`-Naples parking function.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Proposition 1. -/
public theorem_wanted IsNaplesParkingFunction.succ {k n : ℕ} {α : Fin n → ℕ}
    (h : IsNaplesParkingFunction k α) : IsNaplesParkingFunction (k + 1) α

/-- The spot taken under the `k`-Naples rule *on `ℤ`* (the lot extended past spot `1` and past
spot `n`) by a car preferring `a` when the spots in `occ` are occupied: `a` if free; otherwise
the first free spot among `a - 1, …, a - k` (checked in decreasing order, with no lower bound);
otherwise the first free spot after `a`, which lies among `a + 1, …, a + |occ| + 1`.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 2 (parking on `ℤ`). -/
public def naplesSpotInt (k : ℕ) (occ : List ℤ) (a : ℤ) : ℤ :=
  if a ∉ occ then a else
    match ((List.range k).map fun j => a - ((j + 1 : ℕ) : ℤ)).find? (fun s => decide (s ∉ occ)) with
    | some s => s
    | none => (((List.range (occ.length + 1)).map fun j => a + ((j + 1 : ℕ) : ℤ)).find?
        (fun s => decide (s ∉ occ))).getD a

/-- Park the cars with preferences `as` in order under the `k`-Naples rule on `ℤ`, starting
from the occupied spots `occ`; returns the final occupied spots (most recent first).

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 2 (parking on `ℤ`). -/
public def naplesParkInt (k : ℕ) : List ℤ → List ℤ → List ℤ
  | occ, [] => occ
  | occ, a :: as => naplesParkInt k (naplesSpotInt k occ a :: occ) as

/-- Characteristic example (Figure 1): under the `2`-Naples rule on `ℤ` the cars of
`(4, 2, 2, 2)` park in spots `4, 2, 1, 0`.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 2, Figure 1. -/
public theorem naplesParkInt_example :
    naplesParkInt 2 [] [4, 2, 2, 2] = [0, 1, 2, 4] := by
  decide

/-- Characteristic example (Remark 2): under the `3`-Naples rule on `ℤ` the cars of
`(1, 2, 2, 5, 7, 7, 7, 3)` park in spots `1, 2, 0, 5, 7, 6, 4, 3`.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 2, Remark 2. -/
public theorem naplesParkInt_example_three :
    naplesParkInt 3 [] [1, 2, 2, 5, 7, 7, 7, 3] = [3, 4, 6, 7, 5, 0, 2, 1] := by
  decide

/-- Lemma 1: if the cars of a parking preference `α ∈ [n]^n` park on `ℤ` under the `k`-Naples
rule exactly in the spots `1, …, n`, then under the `(k + 1)`-Naples rule on `ℤ` every car parks
in a spot `s` with `0 ≤ s ≤ n`.

Every `k ≥ 0` is admitted (the source's proof treats any `k ≥ 0`).

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Lemma 1. -/
public theorem_wanted naplesParkInt_succ_mem_Icc {k n : ℕ} {α : List ℤ} (hlen : α.length = n)
    (hα : ∀ a ∈ α, 1 ≤ a ∧ a ≤ n)
    (hpark : ∀ s : ℤ, s ∈ naplesParkInt k [] α ↔ 1 ≤ s ∧ s ≤ n) :
    ∀ s ∈ naplesParkInt (k + 1) [] α, 0 ≤ s ∧ s ≤ n

/-- Proposition 2: for `n ≥ 1`, descending `k`-Naples parking functions of length `n` are
equinumerous with `k`-Dyck paths of length `n`.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Proposition 2 (citing Christensen et al., Theorem 1.3). -/
public theorem_wanted descendingNaplesCount_eq_card_kDyckPath {n k : ℕ} (hn : 1 ≤ n)
    (hk : 1 ≤ k) :
    descendingNaplesCount n k = (Finset.univ.filter (IsKDyckPath n k)).card

open Classical in
/-- Proposition 3: for `n ≥ 1`, descending `k`-Naples parking functions of length `n` are
equinumerous with Dyck paths of length `n + k` whose first `k` steps are Up and last `k + 1`
steps are Down.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Proposition 3. -/
public theorem_wanted descendingNaplesCount_eq_card_dyckPath {n k : ℕ} (hn : 1 ≤ n)
    (hk : 1 ≤ k) :
    descendingNaplesCount n k = (Finset.univ.filter fun p : {p : DyckWord // p.semilength = n + k} =>
      List.replicate k DyckStep.U <+: p.1.toList ∧
        List.replicate (k + 1) DyckStep.D <:+ p.1.toList).card

open Classical in
/-- Proposition 4: for `n ≥ 1`, descending strictly `k`-Naples parking functions of length
`n` are equinumerous with Dyck paths of length `n + k` whose first `k` steps are Up, last
`k + 1` steps are Down, and which return to `y = 0` before the last step.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Proposition 4. -/
public theorem_wanted descendingStrictNaplesCount_eq_card_dyckPath {n k : ℕ} (hn : 1 ≤ n)
    (hk : 1 ≤ k) :
    descendingStrictNaplesCount n k = (Finset.univ.filter fun p : {p : DyckWord // p.semilength = n + k} =>
      List.replicate k DyckStep.U <+: p.1.toList ∧
        List.replicate (k + 1) DyckStep.D <:+ p.1.toList ∧
        ∃ j < 2 * (n + k), 0 < j ∧ dyckStepHeight p.1.toList j = 0).card

/-- Theorem 3: for `n - 1 ≥ k ≥ 1`,
`I_{n,k} = I_{n,k-1} + C_k ∑_{i=0}^{n-k} I_{i,k-1} U_{n-k-i,k}` and
`U_{n,k} = U_{n,k-1} + C_k ∑_{i=0}^{n-k} U_{i,k-1} U_{n-k-i,k}`.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Theorem 3. -/
public theorem_wanted ascendingNaplesCount_recurrence {n k : ℕ} (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    ascendingNaplesCount n k = ascendingNaplesCount n (k - 1) + catalan k *
        ∑ i ∈ Finset.range (n - k + 1),
          ascendingNaplesCount i (k - 1) * ascendingNaplesOneCount (n - k - i) k ∧
      ascendingNaplesOneCount n k = ascendingNaplesOneCount n (k - 1) + catalan k *
        ∑ i ∈ Finset.range (n - k + 1),
          ascendingNaplesOneCount i (k - 1) * ascendingNaplesOneCount (n - k - i) k

/-- Theorem 4: `U_{n,1} = F_{n+1}`, the `(n + 1)`-th Fine number (OEIS A000957, with
`F_0 = 1`, `F_1 = 0`; `fineNumber` uses this indexing).

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Theorem 4. -/
public theorem_wanted ascendingNaplesOneCount_one_eq_fineNumber (n : ℕ) :
    (ascendingNaplesOneCount n 1 : ℚ) = fineNumber (n + 1)

/-- Theorem 5: `I_{n,1} = ∑_{i=0}^n C_i F_{n-i}`, the convolution of the Catalan and Fine
numbers (OEIS A000958).

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Theorem 5. -/
public theorem_wanted ascendingNaplesCount_one_eq_sum (n : ℕ) :
    (ascendingNaplesCount n 1 : ℚ) =
      ∑ i ∈ Finset.range (n + 1), (catalan i : ℚ) * fineNumber (n - i)

/-- Theorem 6: with `I_k(x) = ∑ I_{n,k} xⁿ` and `U_k(x) = ∑ U_{n,k} xⁿ`, for `k ≥ 1`,
`I_k = I_{k-1} + C_k x^k I_{k-1} U_k` and `U_k = U_{k-1} + C_k x^k U_{k-1} U_k`.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Theorem 6. -/
public theorem_wanted ascendingNaples_generatingFunction {k : ℕ} (hk : 1 ≤ k) :
    PowerSeries.mk (fun n => ascendingNaplesCount n k) =
        PowerSeries.mk (fun n => ascendingNaplesCount n (k - 1)) +
          (catalan k : PowerSeries ℕ) * PowerSeries.X ^ k *
            PowerSeries.mk (fun n => ascendingNaplesCount n (k - 1)) *
            PowerSeries.mk (fun n => ascendingNaplesOneCount n k) ∧
      PowerSeries.mk (fun n => ascendingNaplesOneCount n k) =
        PowerSeries.mk (fun n => ascendingNaplesOneCount n (k - 1)) +
          (catalan k : PowerSeries ℕ) * PowerSeries.X ^ k *
            PowerSeries.mk (fun n => ascendingNaplesOneCount n (k - 1)) *
            PowerSeries.mk (fun n => ascendingNaplesOneCount n k)

/-- Theorem 7: for `n, k ≥ 1`, there are `C(2n - 1, n) - C(2n - 1, n + k + 1)` descending
`k`-Naples parking functions of length `n`, and `((k + 1)/n) C(2n, n + k + 1)` descending
strictly `k`-Naples parking functions of length `n`.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Theorem 7. -/
public theorem_wanted descendingNaplesCount_eq_choose {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    descendingNaplesCount n k = Nat.choose (2 * n - 1) n - Nat.choose (2 * n - 1) (n + k + 1) ∧
      (descendingStrictNaplesCount n k : ℚ) =
        ((k : ℚ) + 1) / n * Nat.choose (2 * n) (n + k + 1)


/-- The lattice path of a parking preference `α ∈ [n]^n`: for each spot `s = 1, …, n` in turn,
one Up step for every car preferring `s`, then one Down step. For an ascending preference
this is the path whose `i`-th Up step follows `a_i - 1` Down steps.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 3 (Remark 3.3). -/
public def preferencePath {n : ℕ} (α : Fin n → ℕ) : Fin (2 * n) → Bool := fun j =>
  ((List.range n).flatMap fun s =>
    List.replicate (Finset.univ.filter fun i => α i = s + 1).card true ++ [false]).getD j false

/-- Characteristic example: the path of `(1, 3, 3, 5, 6, 6)` is `UDDUUDDUDUUD`.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 3 (Figure 3). -/
public theorem preferencePath_example :
    preferencePath ![1, 3, 3, 5, 6, 6] =
      ![true, false, false, true, true, false, false, true, false, true, true, false] := by
  decide

/-- Lemma 2.3 (published as Lemma 2): let `α` be a `k`-Naples parking function whose cars park
in the spots `d_1, …, d_n`. Take the first `i` cars as already parked, in the spots `d_j`
except for one car `l ≤ i`, which sits in a free spot `q` with `1 ≤ q < d_l`. Then the
remaining cars `a_{i+1}, …, a_n` all park under the `k`-Naples rule (the `i`-filled preference
is a `k`-Naples parking function). Indices are `0`-based; `naplesPark` returns the spots most
recent first.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Lemma 2.3. -/
public theorem_wanted naplesPark_drop_set_isSome {n k i l q : ℕ} {α : Fin n → ℕ}
    {d : List ℕ} (hα : ∀ j, 1 ≤ α j ∧ α j ≤ n)
    (hd : naplesPark n k [] (List.ofFn α) = some d.reverse) (hl : l < i) (hi : i ≤ n)
    (hq : 1 ≤ q) (hql : q < d.getD l 0) (hqd : ∀ j < i, j ≠ l → d.getD j 0 ≠ q) :
    (naplesPark n k ((d.take i).set l q) ((List.ofFn α).drop i)).isSome

/-- Theorem 2: an ascending preference `α ∈ [n]^n` is a `k`-Naples parking function if and
only if, along its lattice path (a `k`-Dyck path when it is `k`-Naples), every step that puts
the path below `y = 0` is followed within `2k` steps by a point above `y = 0`.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Theorem 2.6 (published as Theorem 2). -/
public theorem_wanted isNaplesParkingFunction_iff_of_monotone {n k : ℕ} {α : Fin n → ℕ}
    (hα : ∀ i, 1 ≤ α i ∧ α i ≤ n) (hmono : Monotone α) :
    IsNaplesParkingFunction k α ↔
      ∀ i < 2 * n, latticeHeight (preferencePath α) (i + 1) < 0 →
        ∃ j, i + 1 < j ∧ j ≤ i + 1 + 2 * k ∧ j ≤ 2 * n ∧
          0 < latticeHeight (preferencePath α) j

/-- Corollary 1: every rearrangement of a preference `α ∈ [n]^n` is a `k`-Naples parking
function if and only if, along the lattice path of its ascending rearrangement, every step that
puts the path below `y = 0` is followed within `2k` steps by a point of height `≥ 1` (two more
Up than Down steps so far).

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Corollary 2.7 (published as Corollary 1). -/
public theorem_wanted forall_perm_isNaplesParkingFunction_iff {n k : ℕ} {α : Fin n → ℕ}
    (hα : ∀ i, 1 ≤ α i ∧ α i ≤ n) :
    (∀ σ : Equiv.Perm (Fin n), IsNaplesParkingFunction k (α ∘ σ)) ↔
      ∀ i < 2 * n, latticeHeight (preferencePath α) (i + 1) < 0 →
        ∃ j, i + 1 < j ∧ j ≤ i + 1 + 2 * k ∧ j ≤ 2 * n ∧
          0 < latticeHeight (preferencePath α) j

open Classical in
/-- Corollary 3: for `n ≥ 1`, ascending `k`-Naples parking functions of length `n` are
equinumerous with Dyck paths of length `n + k` whose first `k` steps are Up, last `k + 1` steps
are Down, and in which, before the last `k + 1` steps, every Down step that puts the path below
`y = k` is followed within `2k` steps by a point of height `> k`.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Corollary 2.12 (published as Corollary 3). -/
public theorem_wanted ascendingNaplesCount_eq_card_dyckPath {n k : ℕ} (hn : 1 ≤ n) :
    ascendingNaplesCount n k = (Finset.univ.filter fun p : {p : DyckWord // p.semilength = n + k} =>
      List.replicate k DyckStep.U <+: p.1.toList ∧
        List.replicate (k + 1) DyckStep.D <:+ p.1.toList ∧
        ∀ i, i + (k + 1) < 2 * (n + k) → p.1.toList[i]? = some DyckStep.D →
          dyckStepHeight p.1.toList (i + 1) < k →
            ∃ j, i + 1 < j ∧ j ≤ i + 1 + 2 * k ∧ j ≤ 2 * (n + k) ∧
              (k : ℤ) < dyckStepHeight p.1.toList j).card

/-- The number of nodes on the left spine of a binary tree: the root, its left child, that
child's left child, and so on (`0` for the empty tree).

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 4 (Proposition 4.12). -/
public def leftSpineLength {α : Type*} : BinaryTree α → ℕ
  | .nil => 0
  | .node _ l _ => leftSpineLength l + 1

/-- Characteristic values: the empty tree has left spine length `0`, and a node with a left
child and a right child has left spine length `2`.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 4 (Proposition 4.12). -/
public theorem leftSpineLength_examples :
    leftSpineLength (BinaryTree.nil : BinaryTree Unit) = 0 ∧
      leftSpineLength (BinaryTree.node () (BinaryTree.node () .nil .nil)
        (BinaryTree.node () .nil .nil)) = 2 := by
  decide

/-- Proposition 5: for `k ≥ 1`, descending strictly `k`-Naples parking functions of length `n`
are equinumerous with binary trees on `n + k` nodes whose root has at least `k - 1` left
children in a row (left spine of `≥ k` nodes) and has a right child that has at least `k` left
children in a row (left spine of `≥ k + 1` nodes).

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Proposition 4.12 (published as Proposition 5). -/
public theorem_wanted descendingStrictNaplesCount_eq_card_binaryTree {n k : ℕ} (hk : 1 ≤ k) :
    descendingStrictNaplesCount n k = ((BinaryTree.treesOfNumNodesEq (n + k)).filter fun t =>
      k ≤ leftSpineLength t ∧ k + 1 ≤ leftSpineLength t.right).card

/-- The polygon edges of the vertex set `R` of a convex polygon inscribed in the convex `s`-gon
with vertices `0, …, s - 1`: the pairs `a < b` of `R` with no vertex of `R` strictly between
them, and the pair `(min R, max R)`.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 6 (Theorem 6.3). -/
public def inscribedPolygonEdges {s : ℕ} (R : Finset (Fin s)) : Finset (Fin s × Fin s) :=
  (R ×ˢ R).filter fun e => e.1 < e.2 ∧
    ((∀ c ∈ R, ¬ (e.1 < c ∧ c < e.2)) ∨ ∀ c ∈ R, e.1 ≤ c ∧ c ≤ e.2)

/-- An `r`-in-`s` dissection: a set `D` of pairwise noncrossing diagonals `(a, b)`, `a < b`, of
the convex `s`-gon with vertices `0, …, s - 1`, with `s - r` diagonals, such that the polygon on
the `r` vertices `R` is a face (its edges are sides or diagonals in `D`, and no diagonal of `D`
joins two non-adjacent vertices of `R`). The remaining `s - r` faces are then triangles.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 6 (Definition 6.1). -/
public def IsInnerPolygonDissection (s r : ℕ) (D : Finset (Fin s × Fin s))
    (R : Finset (Fin s)) : Prop :=
  D.card + r = s ∧ R.card = r ∧
    (∀ e ∈ D, e.1.val + 2 ≤ e.2.val ∧ ¬ (e.1.val = 0 ∧ e.2.val + 1 = s)) ∧
    (∀ e ∈ D, ∀ f ∈ D, ¬ (e.1 < f.1 ∧ f.1 < e.2 ∧ e.2 < f.2)) ∧
    (∀ e ∈ inscribedPolygonEdges R,
      e.2.val = e.1.val + 1 ∨ (e.1.val = 0 ∧ e.2.val + 1 = s) ∨ e ∈ D) ∧
    ∀ e ∈ D, e.1 ∈ R → e.2 ∈ R → e ∈ inscribedPolygonEdges R

public instance (s r : ℕ) (D : Finset (Fin s × Fin s)) (R : Finset (Fin s)) :
    Decidable (IsInnerPolygonDissection s r D R) := by
  unfold IsInnerPolygonDissection
  exact @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance
    (@instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance
      (@instDecidableAnd _ _ inferInstance inferInstance))))

/-- Characteristic examples: the square with no diagonals is a `4`-in-`4` dissection, and the
pentagon with the diagonal `(0, 2)` is a `4`-in-`5` dissection with quadrilateral `0, 2, 3, 4`,
but not with quadrilateral `0, 1, 2, 3`.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 6 (Definition 6.1). -/
public theorem isInnerPolygonDissection_examples :
    IsInnerPolygonDissection 4 4 ∅ Finset.univ ∧
      IsInnerPolygonDissection 5 4 {(0, 2)} {0, 2, 3, 4} ∧
      ¬ IsInnerPolygonDissection 5 4 {(0, 2)} {0, 1, 2, 3} := by
  decide

open Classical in
/-- Proposition 6: for `k ≥ 1`, descending strictly `k`-Naples parking functions of length `n`
are in bijection with `(2k + 2)`-in-`(n + k + 1)` dissections up to rotation with a
distinguished edge on the `(2k + 2)`-gon. Rotations act freely on dissections with a
distinguished face edge, so this is stated as: `(n + k + 1)` times the count equals the number
of labelled such dissections with a distinguished face edge.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Theorem 6.3 (published as Proposition 6). -/
public theorem_wanted mul_descendingStrictNaplesCount_eq_card_dissection {n k : ℕ}
    (hk : 1 ≤ k) :
    (n + k + 1) * descendingStrictNaplesCount n k =
      (Finset.univ.filter fun x : Finset (Fin (n + k + 1) × Fin (n + k + 1)) ×
          Finset (Fin (n + k + 1)) × (Fin (n + k + 1) × Fin (n + k + 1)) =>
        IsInnerPolygonDissection (n + k + 1) (2 * k + 2) x.1 x.2.1 ∧
          x.2.2 ∈ inscribedPolygonEdges x.2.1).card

open Classical in
/-- Proposition 7: for `k ≥ 1`, descending strictly `k`-Naples parking functions with `n` cars
are equinumerous with noncrossing partitions of `[n + k + 1]` (here `Fin (n + k + 1)`) whose
block containing the first element has exactly `2k + 2` elements.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Theorem 6.4 (published as Proposition 7). -/
public theorem_wanted descendingStrictNaplesCount_eq_card_noncrossingPartition {n k : ℕ}
    (hk : 1 ≤ k) :
    descendingStrictNaplesCount n k = (Finset.univ.filter fun P : NoncrossingPartition (n + k + 1) =>
      (NoncrossingPartition.block P 0).card = 2 * k + 2).card

end

end MetaMathlibExt
