/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Aaronson-Wigderson: the algebrization barrier

Source:
S. Aaronson and A. Wigderson, "Algebrization: A new barrier in complexity theory",
Proceedings of the Fortieth Annual ACM Symposium on Theory of Computing (STOC 2008),
731-740 (journal version in ACM Transactions on Computation Theory 1 (2009)).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Algebrization

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Aaronson-Wigderson: the algebrization barrier

A proof technique *algebrizes* if it also works relative to any *algebraic* oracle
pair: a base Boolean oracle `B` together with its algebraic extension `B̃`, where `B̃`
answers, for each input length `n`, queries (low-degree extension) for the multilinear
extension of the Boolean function `B` restricted to length `n`, over a finite
field `F_n` of characteristic 2 (the field schedule below: `F_n` is
`AdjoinRoot (irr n)`, the quotient of `Polynomial (ZMod 2)` by a monic irreducible
polynomial of degree `n + 1`, i.e. the field `GF(2 ^ (n + 1))`; the multilinear
extension below is stated over an arbitrary field). The multilinear extension is the unique
polynomial that is affine in each variable and agrees with the base function on
`{0, 1} ^ n`. The
counterexamples are *asymmetric*: they compare a class with access to the base oracle
against a class with access to the extension oracle, distinguishing the two oracles.
Aaronson and Wigderson showed there are algebraic oracle pairs on both sides of `P` vs
`NP`, with the asymmetry in opposite directions: one pair `A` with `P^A = NP^{Ã}`
(the base-oracle `P` already captures the extension-oracle `NP`), and one pair `B`
with `NP^B ⊄ P^{B̃}` (some language in the base-oracle `NP` is outside the
extension-oracle `P`: even the extension-oracle `P` cannot capture the
base-oracle `NP`). Mere inequality `P^{B̃} ≠ NP^B` would not suffice, since
it could hold because `P^{B̃}` contains a language outside `NP^B` while every
`NP^B` language remains in `P^{B̃}`, which would not obstruct an algebrizing
proof of `NP ⊆ P`. Hence no algebrizing proof technique can resolve `P` vs `NP` in either
direction: any such technique would have to prove the same statement relative to
every algebraic oracle pair. Giving `P` and `NP` the *same* extension oracle would
reduce the claim to ordinary same-oracle relativization and would not be the
Aaronson-Wigderson barrier. The extension oracle is encoded as a Boolean function
answering, for a query `(unary length, field element bits, j)`, bit `j` of the
representative of the multilinear extension at the field point. The length
parameter is given in unary (a bitstring of length `n`), so a polynomial-time
oracle machine has `Θ(n)` time to form queries, and the field schedule is
explicitly constructible at that scale. The field at length `n` is the
characteristic-2 field `GF(2 ^ (n + 1))`, presented as `AdjoinRoot (irr n)`
for a monic irreducible polynomial `irr n` of degree `n + 1` over `ZMod 2`;
it is a genuine finite field, not a composite residue ring (an earlier version
used `ZMod (2 ^ (n + 2) + 1)`, e.g. `ZMod 9` at `n = 1`). The encoding is the
power-basis encoding: a field element is the coefficient bitstring of its
representative polynomial of degree `< n + 1` in the basis `1, X, …, X ^ n`.
The irreducible polynomial is itself polynomial-time computable from the unary
length parameter (the `IsPolyTime` conjunct of `IsAlgebraicExtension`); this
is a true, non-vacuous requirement by Shoup's deterministic polynomial-time
algorithm for finding irreducible polynomials over finite fields (V. Shoup,
"New algorithms for finding irreducible polynomials over finite fields",
Mathematics of Computation 54 (1990), 435-447), and field operations on the
power-basis encoding are polynomial arithmetic mod `irr n`, polynomial-time
in `n`. The statement fixes this power-basis encoding relative to the chosen
`irr`; different choices of `irr` give isomorphic fields. (An earlier version
used the least prime above `2 ^ (n + 1)`; Bertrand's postulate only bounds
its bit length and does not give a deterministic polynomial-time algorithm
for finding it, so computability of that schedule was unsupported.)
-/

/-- The multilinear extension of `f` at a field point `x`: the sum over Boolean inputs of
`f a` times the Lagrange basis product, over an arbitrary field `F`. -/
noncomputable def multilinearExt {n : ℕ} {F : Type*} [Field F]
    (f : (Fin n → Bool) → Bool) (x : Fin n → F) : F :=
  ∑ a : Fin n → Bool, (if f a then 1 else 0) *
    ∏ i : Fin n, (if a i then x i else 1 - x i)

/-- The base function of an oracle pair at length `n`, as a function on `n`-bit
inputs, read off the base oracle `B` (queries are the bitstrings themselves). -/
def baseAt (B : List Bool → Bool) (n : ℕ) : (Fin n → Bool) → Bool :=
  fun a => B (List.ofFn a)

/-- Coefficient bitstring of the polynomial `q`, of length `n + 2` (coefficients
`0 .. n + 1`). -/
def polyBits (q : Polynomial (ZMod 2)) (n : ℕ) : List Bool :=
  (List.range (n + 2)).map (fun i => decide (q.coeff i = 1))

/-- The answer bit of the algebraic extension oracle at field point `pt` (a list of
`n` field elements, each encoded as a coefficient bitstring of length
`p.natDegree` relative to the power basis `1, X, …, X ^ (deg - 1)` of
`AdjoinRoot p`) and coordinate `j : Fin p.natDegree`: the `j`-th power-basis
coordinate of the multilinear extension of `baseAt B n` at that field point.
The coordinate is a `Fin`, not a natural reduced modulo the dimension: an
out-of-range `j` must be rejected by the caller (`IsAlgebraicExtension`
requires `j < n + 1`), not wrapped around to coordinate `0`. -/
noncomputable def extAnswer {p : Polynomial (ZMod 2)} [Fact (Irreducible p)] (hp : p.Monic)
    (n : ℕ) (_hdeg : p.natDegree = n + 1) (B : List Bool → Bool)
    (pt : List (List Bool)) (j : Fin p.natDegree) : Bool :=
  decide (((AdjoinRoot.powerBasisAux' hp).repr
    (multilinearExt (baseAt B n)
      (fun i => AdjoinRoot.mk p (∑ k : Fin p.natDegree,
        Polynomial.monomial k.val
          (if (pt.getD i.val []).getD k.val false then (1 : ZMod 2) else 0))))
    j = 1))

/-- An oracle `O` is the algebraic extension of a base oracle `B` if `O`'s answers on
*every* bitstring are the bits of the multilinear extension of the base function
`baseAt B n`, over the field `AdjoinRoot (irr n)` for a monic irreducible
polynomial `irr n` of degree `n + 1` over `ZMod 2` (so the field is
`GF(2 ^ (n + 1))`). The irreducible polynomial schedule `irr` is
polynomial-time computable from the unary length parameter: the `IsPolyTime`
conjunct says the coefficient bitstring `polyBits (irr n) n` is computable in
time polynomial in `n` (the length of the unary input), so a polynomial-time
oracle machine can form valid extension queries and can do field arithmetic
on the power-basis encoding. A query is a bitstring decoding to
`(unary length, field point, j)`: the length parameter `u` is a bitstring whose
length is `n`, the field point is a list of `n` field elements each encoded as
`n + 1` bits, and `j` is a natural number with `j < n + 1`; the answer is bit `j`
(the `j`-th power-basis coordinate) of the multilinear extension at that field
point. Every other bitstring (malformed, wrong-length point, wrong-length field
element encodings, or `j ≥ n + 1`) is answered `false`, so no oracle machine can
route around the algebraic structure through invalid encodings, and an
out-of-range `j` does not wrap around to coordinate `0`. -/
def IsAlgebraicExtension (B O : List Bool → Bool) : Prop :=
  ∃ (irr : ℕ → Polynomial (ZMod 2))
    (hspec : ∀ n, (irr n).Monic ∧ (irr n).natDegree = n + 1 ∧ Irreducible (irr n)),
    IsPolyTime (fun u : List Bool => polyBits (irr u.length) u.length) ∧
    ∀ y : List Bool, O y =
      match MetaMathlibExt.BitstringEncoding.bitDecode
          (α := List Bool × List (List Bool) × ℕ) y with
      | some (u, pt, j) =>
        if h : pt.length = u.length ∧ (∀ e ∈ pt, e.length = u.length + 1) ∧
            j < u.length + 1 then
          @extAnswer (irr u.length) ⟨(hspec u.length).2.2⟩ (hspec u.length).1
            u.length (hspec u.length).2.1 B pt
            ⟨j, by rw [(hspec u.length).2.1]; exact h.2.2⟩
        else false
      | none => false

/-- **Aaronson-Wigderson: the algebrization barrier.** Source: S. Aaronson and A.
Wigderson, "Algebrization: A new barrier in complexity theory", Proceedings of the
Fortieth Annual ACM Symposium on Theory of Computing (STOC 2008), 731-740 (journal
version in ACM Transactions on Computation Theory 1 (2009)). -/
public theorem_wanted aaronson_wigderson_algebrization :
    (∃ B Bext : List Bool → Bool, IsAlgebraicExtension B Bext ∧
      PWithOracle B = NPWithOracle Bext) ∧
    (∃ B Bext : List Bool → Bool, IsAlgebraicExtension B Bext ∧
      ¬ (NPWithOracle B ⊆ PWithOracle Bext))

end MetaMathlibExt.Complexity.KeyTheorems.Algebrization
