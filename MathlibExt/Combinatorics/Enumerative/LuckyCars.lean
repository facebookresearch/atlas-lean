/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Combinatorics.Enumerative.ParkingFunction

/-!
# Lucky cars in parking functions

The greedy parking rule assigns spots in arrival order. It determines which cars are lucky
and the counts of parking functions with a prescribed lucky car and spot.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted

open MetaMathlibExt Polynomial

/-- **Next free spot.** Number the $n$ spots $0, \dots, n-1$. Given a set $S$ of occupied
spots and a spot $a$, the next free spot is the least spot $s \ge a$ with $s \notin S$; when
every spot $s \ge a$ is occupied, it is $a$ itself. -/
def nextFreeSpot {n : ℕ} (occ : Finset (Fin n)) (a : Fin n) : Fin n :=
  if h : (Finset.univ.filter (fun s : Fin n => a ≤ s ∧ s ∉ occ)).Nonempty then
    (Finset.univ.filter (fun s : Fin n => a ≤ s ∧ s ∉ occ)).min' h
  else a

/-- **Greedy parking from an occupied set.** Number the $n$ spots $0, \dots, n-1$. Given a list
$a_1, \dots, a_m$ of preferred spots and a set $S$ of occupied spots, cars $1, \dots, m$ arrive in
order and car $k$ takes the least spot at or after $a_k$ that is neither in $S$ nor taken by cars
$1, \dots, k-1$ (or $a_k$ itself if there is none). The result is the list of spots taken, in
arrival order. -/
def parkSpotsFrom {n : ℕ} : List (Fin n) → Finset (Fin n) → List (Fin n)
  | [], _ => []
  | a :: rest, occ =>
      nextFreeSpot occ a ::
        parkSpotsFrom rest (insert (nextFreeSpot occ a) occ)

/-- **Greedy parking outcome.** Let $f : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ give the
preferred spot of each of $n$ cars. Starting from an empty lot with spots $0, \dots, n-1$, cars
$0, 1, \dots, n-1$ arrive in order, and each takes the least free spot at or after its preference
(or its preference itself if there is none). The outcome sends each car $i$ to the spot it takes. -/
def parkSpots {n : ℕ} (f : Fin n → Fin n) : Fin n → Fin n :=
  fun i => (parkSpotsFrom (List.ofFn f) ∅).getD i.val i

/-- **Lucky car under greedy parking.** Let $f : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ give the
preferred spot of each of $n$ cars. Cars $0, 1, \dots, n-1$ arrive in order, and each takes the
least spot at or after its preference not taken by an earlier car, or its preferred spot itself
when there is no such spot. Car $i$ is lucky if the spot it takes is its preferred spot $f(i)$.

For a parking function a free spot always exists. -/
def IsLuckyCar {n : ℕ} (f : Fin n → Fin n) (i : Fin n) : Prop :=
  parkSpots f i = f i

/-- **Number of lucky cars.** Let $f : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ give the preferred
spot of each of $n$ cars, and let cars $0, 1, \dots, n-1$ arrive in order, each taking the least
spot at or after its preference not taken by an earlier car, or its preferred spot itself when
there is no such spot. The number of lucky cars of $f$ is the number of cars $i$ whose spot is
$f(i)$. -/
def luckyCount {n : ℕ} (f : Fin n → Fin n) : ℕ :=
  (Finset.univ.filter (fun i => decide (parkSpots f i = f i))).card

/-- **Lucky-car counts.** Number the cars and spots $0, \dots, n-1$. For
$i, j \in \{0, \dots, n-1\}$, $q_n(i, j)$ is the number of parking functions
$f : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ with $f(i) = j$ in which car $i$ is lucky, that is,
parks in spot $f(i)$.

In the one-based indexing of Butler et al. this is $q_n(i+1, j+1)$. -/
noncomputable def q (n : ℕ) (i j : Fin n) : ℕ :=
  Nat.card { f : Fin n → Fin n //
    IsParkingFunction n f ∧ f i = j ∧ IsLuckyCar f i }

/-- **Increasing lucky-car counts.** Number the cars and spots $0, \dots, n-1$. For
$i, j \in \{0, \dots, n-1\}$, $q^{\mathrm{inc}}_n(i, j)$ is the number of weakly increasing parking
functions $f : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ with $f(i) = j$ in which car $i$ is lucky,
that is, parks in spot $f(i)$.

In the one-based indexing of Butler et al. this is $q^i_n(i+1, j+1)$. -/
noncomputable def qInc (n : ℕ) (i j : Fin n) : ℕ :=
  Nat.card { f : Fin n → Fin n //
    IsParkingFunction n f ∧ Monotone f ∧ f i = j ∧
      IsLuckyCar f i }

/-- **Decreasing lucky-car counts.** Number the cars and spots $0, \dots, n-1$. For
$i, j \in \{0, \dots, n-1\}$, $q^{\mathrm{dec}}_n(i, j)$ is the number of weakly decreasing parking
functions $f : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ with $f(i) = j$ in which car $i$ is lucky,
that is, parks in spot $f(i)$.

In the one-based indexing of Butler et al. this is $q^d_n(i+1, j+1)$. -/
noncomputable def qDec (n : ℕ) (i j : Fin n) : ℕ :=
  Nat.card { f : Fin n → Fin n //
    IsParkingFunction n f ∧ Antitone f ∧ f i = j ∧
      IsLuckyCar f i }

/-- **Lucky-car polynomial.** For $n \in \mathbb{N}$, $f_n \in \mathbb{Q}[x]$ is the polynomial
$$f_n(x) = \frac{1}{n+1} \prod_{i=0}^{n-1} \bigl((n+1-i)\,x + i\bigr).$$

Equivalently, $f_n(x) = \frac{1}{n+1} \prod_{i=1}^{n} \bigl((n+2-i)\,x + (i-1)\bigr)$. -/
noncomputable def luckyGenPoly (n : ℕ) : Polynomial ℚ :=
  C (1 / (n + 1 : ℚ)) *
    ∏ i : Fin n, (C ((n + 1 - i.val : ℕ) : ℚ) * X + C (i.val : ℚ))

/-- **Ballot paths.** For $k, \ell \in \mathbb{N}$, a ballot path to $(k, \ell)$ is a word of length
$k + \ell$ in up steps and right steps with exactly $\ell$ up steps such that every prefix has at
least as many up steps as right steps; equivalently, a lattice path from $(0,0)$ to $(k, \ell)$
with unit up and right steps that stays on or above the line $y = x$. -/
def BallotPath (k ℓ : ℕ) : Type :=
  { w : List Bool // w.length = k + ℓ ∧ w.count true = ℓ ∧
    ∀ m : ℕ, m ≤ w.length →
      (w.take m).count false ≤ (w.take m).count true }

end MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted
