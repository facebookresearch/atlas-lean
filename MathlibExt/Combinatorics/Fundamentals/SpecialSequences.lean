/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Mark Sepanski
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.List.Cycle
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Tactic.FinCases

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 29, Combinatorics 30, Combinatorics 54, Combinatorics 55, Combinatorics 56, Combinatorics 462, Combinatorics 463, Combinatorics 465, Combinatorics 464

/-!
# `MathlibExt.Combinatorics.Fundamentals.SpecialSequences`

## References

* ec1 p 28 (for `LatticePath`)
* ec1 1.105b p 136 (for `Necklace`)
* ec1 1.6 p 115 (for `Nat.lucas`)
* ec1 1.147 p 146 (for `Nat.motzkin`)
* ec1 1.9 p 116 (for `Nat.delannoy`)
* ec1 2.7.1 (for `SoutheastPath`, `SoutheastPath.weight`, `IsNonintersectingPathFamily`,
  `nonintersectingPathWeightSum`)
-/

namespace MetaMathlibExt

-- Combinatorics 29: Lattice Path with Prescribed Steps

/-- **Lattice paths with prescribed steps.** Let $d \in \mathbb{N}$, let $D \subseteq \mathbb{Z}^d$
and let $p, q \in \mathbb{Z}^d$. A lattice path from $p$ to $q$ with step set $D$ is a finite
sequence $(v_0, v_1, \dots, v_m)$ of points of $\mathbb{Z}^d$, for some $m \in \mathbb{N}$, such
that $v_0 = p$, $v_m = q$, and $v_i - v_{i-1} \in D$ for $1 \le i \le m$.

The case $m = 0$ is the path of length zero, which is a lattice path from $p$ to $q$ exactly when
$p = q$.
-/
def LatticePath (d : ℕ)
    (D : Set (Fin d → ℤ))
    (p q : Fin d → ℤ) :=
  { l : List (Fin d → ℤ) //
    l.head? = some p ∧
    l.getLast? = some q ∧
    List.IsChain
      (fun a b => b - a ∈ D) l
  }

-- Combinatorics 30: Fixed-Length Necklace

/-- **Fixed-length necklaces.** Let $A$ be a set and let $n \in \mathbb{N}$. For $n \ge 1$, a word
of length $n$ over $A$ is a tuple $(a_0, a_1, \dots, a_{n-1})$ of elements of $A$, and two words
$(a_0, \dots, a_{n-1})$ and $(b_0, \dots, b_{n-1})$ are rotationally equivalent if there is an
integer $r$ with $0 \le r < n$ such that $b_i = a_{(i+r) \bmod n}$ for $0 \le i < n$. A necklace of
length $n$ over $A$ is an equivalence class of words of length $n$ under rotational equivalence.
For $n = 0$ there is exactly one necklace over $A$, represented by the empty word.

Reflections are not identified.
-/
def Necklace (A : Type*) (n : ℕ) :=
  {c : Cycle A // c.length = n}

-- Combinatorics 54: Lucas Number Sequence

/-- **Lucas number sequence.** The Lucas numbers $(L_n)_{n \ge 0}$ are the natural numbers
defined by $L_0 = 2$, $L_1 = 1$, and $L_{n+2} = L_{n+1} + L_n$ for every $n \in \mathbb{N}$.
-/
def Nat.lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => Nat.lucas (n + 1) + Nat.lucas n

-- Combinatorics 55: Motzkin Number Sequence

/-- **Motzkin number sequence.** The Motzkin numbers $(M_n)_{n \ge 0}$ are the natural numbers
defined by $M_0 = 1$ and, for every $n \in \mathbb{N}$,
$M_{n+1} = M_n + \sum_{k=0}^{n-1} M_k M_{n-1-k}$, where the sum is empty when $n = 0$. Thus
$M_0, M_1, M_2, M_3 = 1, 1, 2, 4$.
-/
def Nat.motzkin : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    Nat.motzkin n +
      Finset.sum Finset.univ fun k : Fin n =>
        Nat.motzkin k.val *
          Nat.motzkin (n - 1 - k.val)

-- Combinatorics 56: Delannoy Numbers

/-- **Delannoy numbers.** The Delannoy numbers $D(m,n)$, for $m, n \in \mathbb{N}$, are defined by
$D(0,n) = 1$ and $D(m,0) = 1$ for all $m, n \in \mathbb{N}$, and
$D(m+1,n+1) = D(m,n+1) + D(m+1,n) + D(m,n)$ for all $m, n \in \mathbb{N}$.

Equivalently, $D(m,n)$ is the number of lattice paths from $(0,0)$ to $(m,n)$ with steps
$(1,0)$, $(0,1)$ and $(1,1)$.
-/
def Nat.delannoy : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _, 0 => 1
  | m + 1, n + 1 =>
    Nat.delannoy m (n + 1) +
      Nat.delannoy (m + 1) n +
        Nat.delannoy m n

-- Combinatorics 462: Southeast Path


/-! ### Informal statement of `SoutheastPath`

A point of the quarter plane is a pair
(a,b) with a,b∈ℤ_{≥ 0},
where a is the horizontal coordinate and
b is the height. Let
m∈ℤ_{≥ 0} and let p and q
be points of the quarter plane. A southeast
path from p to q is a list
v=[v₀,v₁,…,vₘ] of points of the
quarter plane with v₀=p, vₘ=q, and
each successive pair joined by an east step
or a south step, that is, with

  vₜ=vₜ₋₁+(1,0)
   or
  vₜ₋₁=vₜ+(0,1)

for 1≤ t≤ m. An east step increases
the horizontal coordinate by 1 and leaves
the height unchanged; a south step decreases
the height by 1 and leaves the horizontal
coordinate unchanged. Both coordinates stay
nonnegative because the points are taken in
the quarter plane.

For m=0 the list is the single point
[p], which is a southeast path from p to
p with no steps to check. The empty list
is not a southeast path, since a path has a
first point and a last point. Writing
p=(a,b) and q=(c,d), a southeast path
from p to q exists exactly when
a≤ c and d≤ b, and in that case
m=(c-a)+(b-d), so the number of steps is
determined by the endpoints. In particular
the height never increases along a path.
-/

/-- **Southeast paths.** A point of the quarter plane is a pair $(a, b) \in \mathbb{N}^2$, with $a$
the horizontal coordinate and $b$ the height. Let $p$ and $q$ be points of the quarter plane. A
southeast path from $p$ to $q$ is a list $v = [v_0, v_1, \dots, v_m]$ of points of the quarter
plane, for some $m \in \mathbb{N}$, with $v_0 = p$, $v_m = q$, and, for each $1 \le t \le m$,
either $v_t = v_{t-1} + (1, 0)$ (an east step) or $v_{t-1} = v_t + (0, 1)$ (a south step).

For $m = 0$ the path is the single point $[p]$, which is a southeast path from $p$ to $q$ exactly
when $p = q$. The empty list is not a southeast path. Writing $p = (a, b)$ and $q = (c, d)$, a
southeast path from $p$ to $q$ exists exactly when $a \le c$ and $d \le b$, and then
$m = (c - a) + (b - d)$.
-/
def SoutheastPath (p q : ℕ × ℕ) :=
  { l : List (ℕ × ℕ) //
    l.head? = some p ∧ l.getLast? = some q ∧
    l.IsChain fun a b =>
      b = (a.1 + 1, a.2) ∨ a = (b.1, b.2 + 1) }

-- Combinatorics 463: Southeast Path Weight


/-- **Weight of a southeast path.** Let $R$ be a commutative monoid, written multiplicatively, let
$x = (x_j)_{j \in \mathbb{N}}$ be a family of elements of $R$, let $p, q \in \mathbb{N}^2$, and let
$v = [v_0, \dots, v_m]$ be a southeast path from $p$ to $q$. For $1 \le t \le m$, the step from
$v_{t-1}$ to $v_t$ has weight $w_t = x_j$ if it is an east step at height $j$, that is,
$v_{t-1} = (a, j)$ and $v_t = (a+1, j)$, and weight $w_t = 1$ if it is a south step. The weight of
$v$ is $\operatorname{wt}(v) = \prod_{t=1}^{m} w_t$.

For $m = 0$ the product is empty, so the one-point path $[p]$ has weight $1$; so does every path
all of whose steps are south steps. The weight depends only on the list $v$.
-/
def SoutheastPath.weight {p q : ℕ × ℕ} {R : Type*}
    [CommMonoid R] (x : ℕ → R)
    (l : SoutheastPath p q) : R :=
  ((l.1.zip l.1.tail).map fun c =>
    if c.2 = (c.1.1 + 1, c.1.2) then x c.1.2 else 1).prod

-- Combinatorics 465: Nonintersecting Path Family


/-! ### Informal statement of `IsNonintersectingPathFamily`

Let n∈ℤ_{≥ 0} and write
[n]={1,…,n}, so that
[0]=∅. A point of the quarter
plane is a pair (a,b) of nonnegative
integers, with a the horizontal coordinate
and b the height. If n≥ 1, let
p=[p₁,…,pₙ] and
q=[q₁,…,qₙ] be tuples of points. If
n=0, each is the empty tuple.

An n-path of type (p,q) is an ordered
tuple L=[L₁,…,Lₙ] in which Lᵢ is
a southeast path from pᵢ to qᵢ for
each i∈[n]. For n=0 it is the empty
tuple. It is nonintersecting when no two of
its paths at distinct indices share a
vertex, that is, when for all i,j∈[n]
with i≠ j no point occurs both in Lᵢ
and in Lⱼ.

Endpoints count as vertices, so two paths
meeting only at a common endpoint are not
nonintersecting. Distinctness is of indices
and not of paths, so if i≠ j and
Lᵢ=Lⱼ the family is not
nonintersecting. For n=0 and for
n=1 there is no pair of distinct indices,
so the condition holds for every family.

The source writes the type as four tuples
α, β, γ, δ of
nonnegative integers, with Lᵢ running
from (βᵢ,γᵢ) to
(αᵢ,δᵢ). That is the same data
as the two tuples of points above, with
pᵢ=(βᵢ,γᵢ) and
qᵢ=(αᵢ,δᵢ).
-/

/-- **Nonintersecting families of southeast paths.** Let $n \in \mathbb{N}$ and let
$p_1, \dots, p_n$ and $q_1, \dots, q_n$ be points of $\mathbb{N}^2$. A family
$L = (L_1, \dots, L_n)$, in which $L_i$ is a southeast path from $p_i$ to $q_i$ for each $i$, is
nonintersecting when for all $i \ne j$ no point occurs both in $L_i$ and in $L_j$.

Endpoints count as points of a path, so two paths that meet only at a common endpoint do not
form a nonintersecting family. Distinctness is of indices, not of paths: if $i \ne j$ and
$L_i = L_j$, the family is not nonintersecting. For $n \le 1$ every family is nonintersecting.
-/
def IsNonintersectingPathFamily {n : ℕ}
    {p q : Fin n → ℕ × ℕ}
    (L : (i : Fin n) → SoutheastPath (p i) (q i)) :
    Prop :=
  Pairwise fun i j => ∀ v ∈ (L i).1, v ∉ (L j).1

-- Combinatorics 464: Nonintersecting Path Weight Sum


/-! ### Informal statement of `nonintersectingPathWeightSum`

For k∈ℤ_{≥ 0} write [k]={1,…,k}, so that
[0]=∅. Let n∈ℤ_{≥ 0}. If n≥ 1,
let p=[p₁,…,pₙ] and q=[q₁,…,qₙ] be tuples of
points of ℤ_{≥ 0}². If n=0, each is the empty
tuple.

For i∈[n] and m∈ℤ_{≥ 0}, a southeast path from
pᵢ to qᵢ is a list v=[v₀,v₁,…,vₘ] of points of
ℤ_{≥ 0}² with v₀=pᵢ, vₘ=qᵢ, and for each
t∈[m] either

  vₜ=vₜ₋₁+(1,0),

in which case the step from vₜ₋₁ to vₜ is an east step,
or

  vₜ₋₁=vₜ+(0,1),

in which case it is a south step. For m=0 the list is the
single point [pᵢ], which is a southeast path from pᵢ to
qᵢ only when pᵢ=qᵢ.

An n-path of type (p,q) is an ordered tuple
L=[L₁,…,Lₙ] in which Lᵢ is a southeast path from
pᵢ to qᵢ for each i∈[n]. For n=0 it is the empty
tuple. A vertex of Lᵢ is a point occurring in the list Lᵢ;
endpoints count as vertices. The n-path L is nonintersecting
when for all i,j∈[n] with i≠ j no point is a vertex of
both Lᵢ and Lⱼ. For n=0 and for n=1 there is no pair of
distinct indices, so every n-path is nonintersecting.

Let R be a commutative semiring and let x=(xⱼ) be a family
of elements of R indexed by j∈ℤ_{≥ 0}. Let
v=[v₀,…,vₘ] be a southeast path from pᵢ to qᵢ for
some i∈[n], and let t∈[m]. An east step from
vₜ₋₁=(a,j) to vₜ=(a+1,j), where
a,j∈ℤ_{≥ 0}, has weight wₜ=xⱼ, and a south
step from vₜ₋₁ to vₜ has weight wₜ=1. The weight of
v is

  wt(v)=∏ₜ₌₁ᵐwₜ,

which is 1 for m=0. The weight of an n-path L is

  wt(L)=∏ᵢ₌₁ⁿwt(Lᵢ),

which is 1 for n=0.

The nonintersecting path weight sum of type (p,q) is

  W(p,q)=∑_Lwt(L),

the sum taken over all nonintersecting n-paths L of type
(p,q). If for some i∈[n] there is no southeast path from
pᵢ to qᵢ, there are no n-paths of type (p,q) and
W(p,q)=0. For n=0 the empty tuple is the only n-path and
W(p,q)=1.
-/

/-- **Weighted sum over nonintersecting path families.** Let $R$ be a commutative semiring, let
$x = (x_j)_{j \in \mathbb{N}}$ be a family of elements of $R$, let $n \in \mathbb{N}$, and let
$p = (p_1, \dots, p_n)$ and $q = (q_1, \dots, q_n)$ be tuples of points of $\mathbb{N}^2$. The
nonintersecting path weight sum of type $(p, q)$ is
$W(p, q) = \sum_L \prod_{i=1}^{n} \operatorname{wt}(L_i)$, the sum taken over all nonintersecting
families $L = (L_1, \dots, L_n)$ in which $L_i$ is a southeast path from $p_i$ to $q_i$ for each
$i$, where $\operatorname{wt}(L_i)$ is the weight of $L_i$ with respect to $x$.

There are only finitely many such families. If for some $i$ there is no southeast path from
$p_i$ to $q_i$, then $W(p, q) = 0$. For $n = 0$ the empty family is the only one, and
$W(p, q) = 1$.
-/
noncomputable def nonintersectingPathWeightSum {n : ℕ}
    {R : Type*} [CommSemiring R] (x : ℕ → R)
    (p q : Fin n → ℕ × ℕ) : R :=
  ∑ᶠ L : {L : (i : Fin n) → SoutheastPath (p i) (q i) //
      IsNonintersectingPathFamily L},
    ∏ i, (L.1 i).weight x

end MetaMathlibExt

end
