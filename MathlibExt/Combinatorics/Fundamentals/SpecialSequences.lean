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

/-- Let d∈ℕ, let D⊆ℤᵈ, and
let p,q∈ℤᵈ. A lattice path from p to q
with prescribed step set D is a finite sequence

  (v₀,v₁,…,vₘ)

of points in ℤᵈ, for some m∈ℕ,
such that

  v₀=p,  vₘ=q,

and

  vᵢ-vᵢ₋₁∈ D (1≤ i≤ m).

The case m=0 is the length-zero path and is allowed
exactly when p=q.
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

/-- Let A be a set and let n∈ℕ. For n≥1,
a word of length n over A is an ordered tuple

  a=(a₀,a₁,…,aₙ₋₁)

of elements of A. Two words

  a=(a₀,…,aₙ₋₁)

and

  b=(b₀,…,bₙ₋₁)

are rotationally equivalent if there exists an integer r
with 0≤ r<n such that

  bᵢ=a_{(i+r)mod n} (0≤ i<n).

A fixed-length necklace of length n over A is an
equivalence class of words under rotational equivalence.
Reflections are not identified.

When n=0, there is exactly one necklace over A,
represented by the empty word.
-/
def Necklace (A : Type*) (n : ℕ) :=
  {c : Cycle A // c.length = n}

-- Combinatorics 54: Lucas Number Sequence

/-- The Lucas number sequence (Lₙ)_{n≥ 0} is defined by

  L₀=2,  L₁=1,

and, for every n∈ℕ, by

  Lₙ₊₂=Lₙ₊₁+Lₙ.
-/
def Nat.lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => Nat.lucas (n + 1) + Nat.lucas n

-- Combinatorics 55: Motzkin Number Sequence

/-- The Motzkin number sequence (Mₙ)_{n≥ 0} is
defined by

  M₀=1,

and, for every n∈ℕ, by

  Mₙ₊₁
  =
  Mₙ+∑ₖ₌₀ⁿ⁻¹MₖMₙ₋₁₋ₖ,

where the sum is empty when n=0. Thus

  M₀,M₁,M₂,M₃,…=1,1,2,4,….
-/
def Nat.motzkin : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    Nat.motzkin n +
      Finset.sum Finset.univ fun k : Fin n =>
        Nat.motzkin k.val *
          Nat.motzkin (n - 1 - k.val)

-- Combinatorics 56: Delannoy Numbers

/-- For m,n∈ℕ, the Delannoy number D(m,n)
is defined recursively by

  D(0,n)=1,  D(m,0)=1,

and

  D(m+1,n+1)
  =
  D(m,n+1)+D(m+1,n)+D(m,n).

Equivalently, D(m,n) is the number of lattice paths
from (0,0) to (m,n) using the steps

  (1,0), (0,1), (1,1).
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

/-- A point of the quarter plane is a pair (a,b) with a,b∈ℤ_{≥ 0}, where a is the horizontal
coordinate and b is the height. Let m∈ℤ_{≥ 0} and let p and q be points of the quarter plane.

The full informal statement is in the module documentation directly above.
-/
def SoutheastPath (p q : ℕ × ℕ) :=
  { l : List (ℕ × ℕ) //
    l.head? = some p ∧ l.getLast? = some q ∧
    l.IsChain fun a b =>
      b = (a.1 + 1, a.2) ∨ a = (b.1, b.2 + 1) }

-- Combinatorics 463: Southeast Path Weight


/-- Let R be a commutative monoid, written
multiplicatively, and let x=(xⱼ) be a
family of elements of R indexed by
j∈ℤ_{≥ 0}. Let p and q be
points of the quarter plane and let
v=[v₀,…,vₘ] be a southeast path
from p to q.

Every step of v is an east step or a south
step. An east step leaves the height
unchanged; if that common height is j,
the step has weight xⱼ. A south step has
weight 1. The weight of v is the product
of the weights of its steps,

  wt(v)=∏ₜ₌₁ᵐwₜ,

where wₜ is the weight of the step from
vₜ₋₁ to vₜ. Equivalently, it is the
product of the xⱼ taken over the east
steps of v, each east step contributing
the height j at which it occurs.

For m=0 the product is empty, so the
one-point path [p] has weight 1. The
same holds for a path all of whose steps are
south steps. The weight depends only on the
list v, not on p and q separately.
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

/-- Let n∈ℤ_{≥ 0} and write [n]={1,…,n}, so that [0]=∅. A point of the quarter plane is a pair (a,b)
of nonnegative integers, with a the horizontal coordinate and b the height. If n≥ 1, let p=[p₁,…,pₙ]
and q=[q₁,…,qₙ] be tuples of points. If n=0, each is the empty tuple.

The full informal statement is in the module documentation directly above.
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

/-- For k∈ℤ_{≥ 0} write [k]={1,…,k}, so that [0]=∅. Let n∈ℤ_{≥ 0}. If n≥ 1, let p=[p₁,…,pₙ] and
q=[q₁,…,qₙ] be tuples of points of ℤ_{≥ 0}². If n=0, each is the empty tuple.

The full informal statement is in the module documentation directly above.
-/
noncomputable def nonintersectingPathWeightSum {n : ℕ}
    {R : Type*} [CommSemiring R] (x : ℕ → R)
    (p q : Fin n → ℕ × ℕ) : R :=
  ∑ᶠ L : {L : (i : Fin n) → SoutheastPath (p i) (q i) //
      IsNonintersectingPathFamily L},
    ∏ i, (L.1 i).weight x

end MetaMathlibExt

end
