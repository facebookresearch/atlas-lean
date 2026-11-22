/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import MathlibExt.Data.Sym.Sym2
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Sym.Card
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Topology.MetricSpace.Defs

@[expose] public section

open scoped Finset

variable {X : Type*} [MetricSpace X]

/-- **Multiplicity of a distance.** Let $P$ be a finite set of points in a metric space and let
$d$ be a real number. The multiplicity of $d$ in $P$ is the number of unordered pairs
$\{p, q\}$ of distinct points of $P$ with $\operatorname{dist}(p, q) = d$. -/
noncomputable def distanceMultiplicity (points : Finset X) (d : ℝ) : ℕ :=
  #(points.offDiag.filter fun (pair : X × X) => dist pair.1 pair.2 = d) / 2

/-- **Number of unit distances.** For a finite set $S$ of points in a metric space, the number of
unit distances of $S$ is the number of unordered pairs $\{p, q\}$ of points of $S$ with
$\operatorname{dist}(p, q) = 1$, that is, the multiplicity of the distance $1$ in $S$.
-/
noncomputable def unitDistNum (s : Finset X) : ℕ := distanceMultiplicity s 1

@[simp] theorem unitDistNum_eq_distanceMultiplicity (s : Finset X) :
    unitDistNum s = distanceMultiplicity s 1 := rfl

/-- **Distance set of a finite point set.** For a finite set $P$ of points in a metric space,
the distance set of $P$ is the finite set of real numbers $\operatorname{dist}(p, q)$ with $p$
and $q$ distinct points of $P$. -/
noncomputable def distanceSet (points : Finset X) : Finset ℝ :=
  points.offDiag.image fun (pair : X × X) => dist pair.1 pair.2

/--
**Number of distinct distances.** For a finite set $P$ of points in a metric space, the number
of distinct distances of $P$ is the number of elements of its distance set, that is, the number
of distinct values $\operatorname{dist}(p, q)$ with $p$ and $q$ distinct points of $P$.
-/
noncomputable def distinctDistances (points : Finset X) : ℕ :=
  #(distanceSet points)

variable (X) in
/-- **Minimum number of distinct distances.** Let $X$ be a metric space and $n$ a natural number
such that $X$ contains a set of exactly $n$ points. The minimum number of distinct distances for
$n$ points in $X$ is the least number of distinct distances determined by a set of exactly $n$
points of $X$.

The hypothesis that some $n$-point set exists makes the minimum range over a nonempty
collection of sets. -/
noncomputable def minimalDistinctDistances (n : ℕ) (_ : ∃ points : Finset X, #points = n) : ℕ :=
  sInf {m : ℕ | ∃ points : Finset X, #points = n ∧ distinctDistances points = m}

open Classical in
/-- **Number of distinct distances from a point.** For a finite set $P$ of points in a metric
space and a point $x$ of the space, this is the number of distinct values
$\operatorname{dist}(y, x)$ with $y$ a point of $P$ other than $x$. -/
noncomputable def distinctDistancesFrom (points : Finset X) (pt : X) : ℕ :=
  #((points.erase pt).image fun x => dist x pt)

open Classical in
/-- **Trivial upper bound on unit distances.** For a finite set of $n$ points in a metric space,
the number of unit distances is at most $\binom{n}{2}$, the total number of unordered pairs of
distinct points. -/
theorem unitDistNum_le_choose_two (s : Finset X) : unitDistNum s ≤ (#s).choose 2 := by
  unfold unitDistNum distanceMultiplicity
  calc #(s.offDiag.filter fun (pair : X × X) => dist pair.1 pair.2 = 1) / 2
      ≤ #s.offDiag / 2 := Nat.div_le_div_right (Finset.card_filter_le _ _)
    _ = (#s).choose 2 := by
      rw [Finset.offDiag_card, Nat.choose_two_right, Nat.mul_sub_left_distrib, mul_one]
