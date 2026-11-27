/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Metered parking functions

Cars park in order. When a car arrives, only the previous `t` cars can still occupy spots.
Spots and preferences are numbered from zero.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Outcome of the metered parking scheme.** Let $t, n \in \mathbb{N}$, number the $n$ spots
$0, \dots, n-1$, and let $a_0, a_1, \dots, a_{m-1}$ be a list of preferences in $\mathbb{N}$.
Cars arrive in order, and car $i$ parks in the least spot $s$ with $a_i \le s < n$ that is not
taken by one of the previous $t$ cars (cars $\max(0, i - t), \dots, i - 1$) that parked; if
there is no such spot, car $i$ fails. The outcome is the list whose $i$-th entry is the spot of
car $i$, or a failure marker if car $i$ fails. Thus after car $j$ arrives, car $j - t$ leaves,
and only the cars among the last $t$ entries of the outcome so far occupy spots.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 1 (definition of the `t`-metered scheme) and
Section 2
(definition of the outcome). -/
public def meteredOutcome (t n : ℕ) (prefs : List ℕ) : List (Option ℕ) :=
  prefs.foldl
    (fun out a => out ++ [(List.range' a (n - a)).find?
      (fun s => decide (s ∉ (out.drop (out.length - t)).filterMap id))])
    []

private theorem foldl_append_singleton_suffix {α β : Type*} (next : List β → α → β)
    (prefs : List α) (out : List β) :
    ∃ tail, prefs.foldl (fun out a => out ++ [next out a]) out = out ++ tail ∧
      tail.length = prefs.length := by
  induction prefs generalizing out with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons a prefs ih =>
    obtain ⟨tail, h, hlen⟩ := ih (out ++ [next out a])
    exact ⟨next out a :: tail, by simpa [List.append_assoc] using h, by simp [hlen]⟩

private theorem getElem?_meteredOutcome {t n i : ℕ} (prefs : List ℕ) (hi : i < prefs.length) :
    let out := meteredOutcome t n (prefs.take i)
    (meteredOutcome t n prefs)[i]? = some ((List.range' prefs[i] (n - prefs[i])).find?
      (fun s => decide (s ∉ (out.drop (out.length - t)).filterMap id))) := by
  dsimp only
  let out := meteredOutcome t n (prefs.take i)
  let next (out : List (Option ℕ)) (a : ℕ) :=
    (List.range' a (n - a)).find? (fun s => decide (s ∉ (out.drop (out.length - t)).filterMap id))
  obtain ⟨tail, hout, hlen⟩ := foldl_append_singleton_suffix next (prefs.take i) []
  have hi' : out.length = i := by
    change out = [] ++ tail at hout
    simpa [hout, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)] using hlen
  have hsplit : (prefs.take i ++ [prefs[i]]) ++ prefs.drop (i + 1) = prefs := by
    rw [← List.take_succ_eq_append_getElem hi, List.take_append_drop]
  obtain ⟨rest, hrest, _⟩ :=
    foldl_append_singleton_suffix next (prefs.drop (i + 1)) (out ++ [next out prefs[i]])
  have hwhole : meteredOutcome t n prefs = (out ++ [next out prefs[i]]) ++ rest := by
    conv_lhs => rw [← hsplit]
    simp only [meteredOutcome, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact hrest
  change (meteredOutcome t n prefs)[i]? = some (next out prefs[i])
  rw [hwhole, List.append_assoc, List.getElem?_append_right (by omega : out.length ≤ i),
    show i - out.length = 0 by omega]
  rfl

/-- **Displacement bound in the metered scheme.** Let $t$, $m$, $n$ be natural numbers, let
$f : \{0, \dots, m - 1\} \to \{0, \dots, n - 1\}$ be a preference function and let $i < m$ be a
car. Under the $t$-metered parking scheme on $n$ spots, if car $i$ parks in spot $s$ then
$s \le f(i) + t$, that is, its displacement is at most $t$; and if car $i$ fails to park then
$f(i) + t \ge n$.

In the source's one-based numbering, with preference $a_i = f(i) + 1$, a car that fails to park
has $a_i \ge n - t + 1$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Proposition 5 (`integers-2025-A73-prop-5`). -/
public theorem meteredOutcome_displacement_le {m n t : ℕ} (f : Fin m → Fin n) (i : Fin m) :
    (∀ s, (meteredOutcome t n (List.ofFn fun i => (f i : ℕ)))[(i : ℕ)]? = some (some s) →
        s ≤ (f i : ℕ) + t) ∧
      ((meteredOutcome t n (List.ofFn fun i => (f i : ℕ)))[(i : ℕ)]? = some none →
        n ≤ (f i : ℕ) + t) := by
  let a := (f i : ℕ)
  let out := meteredOutcome t n ((List.ofFn fun i => (f i : ℕ)).take i)
  let occupied := (out.drop (out.length - t)).filterMap id
  let free (s : ℕ) := decide (s ∉ occupied)
  have hentry : (meteredOutcome t n (List.ofFn fun i => (f i : ℕ)))[(i : ℕ)]? =
      some ((List.range' a (n - a)).find? free) := by
    simpa [a, out, occupied, free] using getElem?_meteredOutcome (t := t) (n := n)
      (List.ofFn fun i => (f i : ℕ)) (i := (i : ℕ)) (by simp)
  rw [hentry]
  simp only [Option.some.injEq]
  change (∀ s, (List.range' a (n - a)).find? free = some s → s ≤ a + t) ∧
    ((List.range' a (n - a)).find? free = none → n ≤ a + t)
  by_cases h : a + t < n
  · -- If the first `t + 1` spots exist, at least one is free.
    have hcap : occupied.length ≤ t :=
      (List.length_filterMap_le id _).trans (by simp only [List.length_drop]; omega)
    obtain ⟨s, hs⟩ : ∃ s, (List.range' a (t + 1)).find? free = some s := by
      apply Option.ne_none_iff_exists'.mp
      intro hnone
      have hsub : List.range' a (t + 1) ⊆ occupied := by
        intro x hx
        simpa [free] using List.find?_eq_none.mp hnone x hx
      have hlen := (List.nodup_range' 1).length_le_of_subset hsub
      simp only [List.length_range'] at hlen
      omega
    have hpref : List.range' a (t + 1) <+: List.range' a (n - a) := by
      refine ⟨List.range' (a + (t + 1)) (n - a - (t + 1)), ?_⟩
      rw [List.range'_append_1, Nat.add_sub_of_le (by omega : t + 1 ≤ n - a)]
    have hs' := hpref.find?_eq_some hs
    have hmem := List.mem_range'_1.mp (List.mem_of_find?_eq_some hs)
    simp only [hs', Option.some.injEq, reduceCtorEq, false_implies, and_true]
    rintro _ rfl
    omega
  · refine ⟨fun s hs => ?_, fun _ => by omega⟩
    have hmem := List.mem_range'_1.mp (List.mem_of_find?_eq_some hs)
    omega

/-- **A 1-metered example in which every car parks.** In the $1$-metered parking scheme on two
spots $\{0, 1\}$, if three cars arrive all preferring spot $0$, then they park in spots $0$, $1$
and $0$, in that order.

In the source's one-based numbering: preferences $(1, 1, 1)$ give spots $1, 2, 1$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, example after the definition of `t`-metered parking
functions (Section 1). -/
public theorem meteredOutcome_one_two_ones :
    meteredOutcome 1 2 [0, 0, 0] = [some 0, some 1, some 0] := by decide

/-- **A 1-metered example in which the third car fails.** In the $1$-metered parking scheme on
two spots $\{0, 1\}$, if three cars arrive with preferences $0$, $0$, $1$, then the first two
cars park in spots $0$ and $1$ and the third car fails to park.

In the source's one-based numbering: with preferences $(1, 1, 2)$, car $3$ fails.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, example after the definition of `t`-metered parking
functions (Section 1). -/
public theorem meteredOutcome_one_two_fail :
    meteredOutcome 1 2 [0, 0, 1] = [some 0, some 1, none] := by decide

/-- **Metered outcomes of a seven-car example on six spots.** On the six spots
$\{0, \dots, 5\}$, for seven cars with preferences $(2, 2, 2, 2, 3, 4, 5)$, the $2$-metered
parking scheme parks the cars in spots $(2, 3, 4, 2, 3, 4, 5)$, while in the $1$-metered scheme
the first six cars park in spots $(2, 3, 2, 3, 4, 5)$ and the seventh car fails to park.

In the source's one-based notation, where $O^t_n$ is the outcome of the $t$-metered scheme on
$n$ spots and $X$ marks a car that fails to park, $O^2_6(3,3,3,3,4,5,6) = (3,4,5,3,4,5,6)$ and
$O^1_6(3,3,3,3,4,5,6) = (3,4,3,4,5,6,X)$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, example after the definition of the outcome
(Section 2). -/
public theorem meteredOutcome_example_six :
    meteredOutcome 2 6 [2, 2, 2, 2, 3, 4, 5] =
        [some 2, some 3, some 4, some 2, some 3, some 4, some 5] ∧
      meteredOutcome 1 6 [2, 2, 2, 2, 3, 4, 5] =
        [some 2, some 3, some 2, some 3, some 4, some 5, none] := by decide

/-- **Metered parking function.** Let $m, n, t \in \mathbb{N}$, number the $n$ spots
$0, \dots, n-1$, and let $f : \{0, \dots, m-1\} \to \{0, \dots, n-1\}$ give the preferred spot of
each of $m$ cars. In the $t$-metered scheme the cars arrive in the order $0, 1, \dots, m-1$, and
car $i$ parks in the least spot $s$ with $f(i) \le s \le n - 1$ that is not occupied by any of the
(at most $t$) cars that arrived just before car $i$; it fails to park if there is no such spot.
Then $f$ is a $t$-metered parking function if every car parks.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 1 (definition of `t`-metered parking
functions). -/
public def IsMeteredParkingFunction {m n : ℕ} (t : ℕ) (f : Fin m → Fin n) : Prop :=
  ∀ o ∈ meteredOutcome t n (List.ofFn fun i => (f i : ℕ)), o ≠ none

/-- Decidability of `IsMeteredParkingFunction` (a finite check of the outcome list).

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 1 (definition of `t`-metered parking
functions). -/
public instance instDecidableIsMeteredParkingFunction {m n : ℕ} (t : ℕ) (f : Fin m → Fin n) :
    Decidable (IsMeteredParkingFunction t f) := by
  unfold IsMeteredParkingFunction
  infer_instance

/-- **Number of metered parking functions.** For natural numbers $t$, $m$ and $n$,
$\mathrm{mpf}_{m,n}(t)$ is the number of $t$-metered $(m, n)$-parking functions, that is, of maps
$f$ from the $m$ cars $\{0, \dots, m-1\}$ to the $n$ spots $\{0, \dots, n-1\}$ under which every
car parks in the $t$-metered parking scheme.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 1 (definition and the notation
`mpf_{m,n}(t)`). -/
public def meteredParkingCount (t m n : ℕ) : ℕ :=
  (Finset.univ.filter fun f : Fin m → Fin n => IsMeteredParkingFunction t f).card

/-- **1-metered parking functions with two cars and two spots.** The number of $1$-metered
$(2, 2)$-parking functions is $\mathrm{mpf}_{2,2}(1) = 3$.

This is an entry of the source's Table 1.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Table 1. -/
public theorem meteredParkingCount_one_two_two : meteredParkingCount 1 2 2 = 3 := by decide

namespace meteredParkingCount_eq_zero

-- A successful history uses distinct spots. Its length is therefore at most the
-- number of spots, so the meter still remembers the whole history at the next arrival.
private theorem successful_spots {n t : ℕ} (htn : n ≤ t) (prefs : List ℕ)
    (hsuccess : none ∉ meteredOutcome t n prefs) :
    ∃ spots : List ℕ, meteredOutcome t n prefs = spots.map some ∧
      spots.length = prefs.length ∧ spots.Nodup ∧ spots ⊆ List.range n := by
  induction prefs using List.reverseRecOn with
  | nil => exact ⟨[], rfl, rfl, List.nodup_nil, by simp⟩
  | append_singleton prefs a ih =>
    let out := meteredOutcome t n prefs
    let next := (List.range' a (n - a)).find?
      (fun s => decide (s ∉ (out.drop (out.length - t)).filterMap id))
    have hstep : meteredOutcome t n (prefs ++ [a]) = out ++ [next] := by
      simp [meteredOutcome, List.foldl_append, out, next]
    rw [hstep] at hsuccess ⊢
    obtain ⟨spots, hspots, hlen, hnodup, hsub⟩ := ih fun h => hsuccess (List.mem_append_left _ h)
    have hcap : spots.length ≤ n := by simpa using hnodup.length_le_of_subset hsub
    have hdrop : spots.length - t = 0 := Nat.sub_eq_zero_of_le (hcap.trans htn)
    have hnext : next ≠ none := fun h => hsuccess (by simp [h])
    obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hnext
    have hfresh : s ∉ spots := by
      simpa [hdrop, out, hspots, List.filterMap_map] using List.find?_some hs
    have hrange := List.mem_range'_1.mp (List.mem_of_find?_eq_some hs)
    refine ⟨spots ++ [s], ?_, by simp [hlen], ?_, ?_⟩
    · simp [out, hspots, hs]
    · simpa [List.nodup_append, hnodup] using fun x hx => ne_of_mem_of_not_mem hx hfresh
    · exact List.append_subset.mpr ⟨hsub, by simpa using (show s < n by omega)⟩

end meteredParkingCount_eq_zero

/-- **Vanishing of metered parking counts.** Let $m, n, t$ be natural numbers with $m > n$ and
$t \ge n$. Then there are no $t$-metered $(m, n)$-parking functions, that is,
$\mathrm{mpf}_{m,n}(t) = 0$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Proposition 2 (`integers-2025-A73-prop-2`). -/
public theorem meteredParkingCount_eq_zero {m n t : ℕ} (hmn : n < m) (htn : n ≤ t) :
    meteredParkingCount t m n = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro f _ hf
  obtain ⟨spots, _, hlen, hnodup, hsub⟩ :=
    meteredParkingCount_eq_zero.successful_spots htn _ (fun h => hf none h rfl)
  have hcap := hnodup.length_le_of_subset hsub
  simp only [List.length_range, List.length_ofFn] at hcap hlen
  omega

/-- **Lucky cars in the metered scheme.** For natural numbers $t$, $m$, $n$ and a preference
function $f : \{0, \dots, m - 1\} \to \{0, \dots, n - 1\}$ (car $i$ prefers spot $f(i)$), the
lucky count of $f$ under the $t$-metered parking scheme on $n$ spots is the number of cars $i$
that park in their preferred spot $f(i)$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 2 (`lucky(α)`). -/
public def meteredLuckyCount {m n : ℕ} (t : ℕ) (f : Fin m → Fin n) : ℕ :=
  ((List.ofFn fun i => (f i : ℕ)).zip (meteredOutcome t n (List.ofFn fun i => (f i : ℕ)))).countP
    fun p => decide (p.2 = some p.1)

/-- **One step of the lace decomposition.** Given a list of blocks (each a list of natural
numbers) and a natural number $a$: if the last block is $(p)$ with $a = p$, or the last block has
at least two entries and ends with $e$ where $a = e + 1$, then $a$ is appended to the last block;
otherwise, including when there is no block, a new block $(a)$ is added at the end.

Applied to a list of laces, where a lace is $(p)$ or $(p, p, p+1, \dots, p+\ell-2)$ for some
natural number $p$ and some length $\ell \ge 2$, this extends the last lace exactly when the
result is again a lace.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 3 (definitions of a lace and of the lace
decomposition). -/
public def laceStep (acc : List (List ℕ)) (a : ℕ) : List (List ℕ) :=
  match acc.getLast? with
  | some [p] => if a = p then acc.dropLast ++ [[p, a]] else acc ++ [[a]]
  | some l@(_ :: _ :: _) =>
      if a = l.getLastD 0 + 1 then acc.dropLast ++ [l ++ [a]] else acc ++ [[a]]
  | _ => acc ++ [[a]]

/-- **Lace decomposition.** A lace is a sequence of natural numbers of the form $(p)$ or
$(p, p, p+1, \dots, p+\ell-2)$ for some natural number $p$ and some length $\ell \ge 2$. The lace
decomposition of a finite sequence $(a_1, \dots, a_k)$ of natural numbers is its partition into
blocks of consecutive entries built greedily from left to right: starting with no blocks, each
entry $a_i$ in turn is appended to the last block if the result is again a lace, and otherwise
starts a new block $(a_i)$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 3 (definitions of a lace and of the lace
decomposition). -/
public def laceDecomposition (l : List ℕ) : List (List ℕ) :=
  l.foldl laceStep []

/-- **Examples of lace decompositions.** The lace decomposition of $(3, 3, 3, 3, 4, 6)$ is
$((3, 3), (3, 3, 4), (6))$, and the lace decomposition of $(4, 1, 2, 2, 3, 4, 5, 5, 1, 2)$ is
$((4), (1), (2, 2, 3, 4, 5), (5), (1), (2))$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 3, example after the definition of the lace
decomposition. -/
public theorem laceDecomposition_examples :
    laceDecomposition [3, 3, 3, 3, 4, 6] = [[3, 3], [3, 3, 4], [6]] ∧
      laceDecomposition [4, 1, 2, 2, 3, 4, 5, 5, 1, 2] =
        [[4], [1], [2, 2, 3, 4, 5], [5], [1], [2]] := by decide

/-- **Parking-function shuffles.** Let $m'$, $n$, $k$ be natural numbers and let
$\pi : \{0, \dots, m' - 1\} \to \{0, \dots, n - 1\}$, with one-based letters $w_i = \pi(i) + 1$.
Then $\pi$ is a parking-function shuffle with parameters $(m', n, k)$ when all of the following
hold: no letter $w_i$ equals $k$; exactly $\max(m' + k - n, 0)$ letters satisfy $w_i < k$;
exactly $\max(n - k, 0)$ letters satisfy $w_i > k$; for every $s$ with $1 \le s \le k - 1$, at
most $k - s$ letters satisfy $s \le w_i \le k - 1$; and for every $s$ with $k + 1 \le s \le n$, at
most $n + 1 - s$ letters satisfy $w_i \ge s$.

With $m = m' + 1$, the word $(w_0, \dots, w_{m'-1})$ plays the role of the source's
$(\pi_2, \dots, \pi_m)$, and the conditions express membership in the source's set
$\mathrm{Sh}_m(k - 1, n - k)$ of shuffles of a parking function of $m - n + k - 1$ cars on
$k - 1$ spots (the letters below $k$) with a parking function of length $n - k$ shifted up by
$k$ (the letters above $k$): parking-function membership does not depend on the order of the
letters, and the last two conditions are the usual counting criterion for every car to park.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 4, Definition of `(m, n)`-parking function
shuffles (`Sh_m(k - 1, n - k)`). -/
public def IsParkingShuffle (m' n k : ℕ) (π : Fin m' → Fin n) : Prop :=
  (∀ i, (π i : ℕ) + 1 ≠ k) ∧
    (Finset.univ.filter fun i => (π i : ℕ) + 1 < k).card = m' + 1 + k - n - 1 ∧
    (Finset.univ.filter fun i => k < (π i : ℕ) + 1).card = n - k ∧
    (∀ j < k - 1, (Finset.univ.filter fun i => j ≤ (π i : ℕ) ∧ (π i : ℕ) < k - 1).card ≤
      k - 1 - j) ∧
    ∀ j ∈ Finset.Ico k n, (Finset.univ.filter fun i => j ≤ (π i : ℕ)).card ≤ n - j

/-- Membership in the parking-function shuffle set is decidable.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 4 (`Sh_m(k - 1, n - k)`). -/
public instance instDecidableIsParkingShuffle (m' n k : ℕ) (π : Fin m' → Fin n) :
    Decidable (IsParkingShuffle m' n k π) := by
  unfold IsParkingShuffle
  infer_instance

/-- **An example of a parking-function shuffle.** The word $(2, 6, 1, 0, 6, 1)$ with entries
in $\{0, \dots, 7\}$, which is $(3, 7, 2, 1, 7, 2)$ in one-based values, is a
$(7, 8)$-parking-function shuffle with parameter $k = 6$, that is, it lies in
$\mathrm{Sh}_7(5, 2)$. In one-based values it is a shuffle of the parking function
$(3, 2, 1, 2)$ with $4$ cars and $5$ spots and of $(7, 7) = (1, 1) + (6, 6)$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 4, Example 5. -/
public theorem isParkingShuffle_example :
    IsParkingShuffle 6 8 6 ![2, 6, 1, 0, 6, 1] := by
  unfold IsParkingShuffle
  decide

end

end MetaMathlibExt
