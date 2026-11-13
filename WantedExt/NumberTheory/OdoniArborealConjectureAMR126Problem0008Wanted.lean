/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Odoni's conjecture on surjective arboreal Galois representations

Odoni's conjecture (1985): let `K` be a Hilbertian field and `d ≥ 2`. There exist a monic polynomial
`f(X) ∈ K[X]` of degree `d` and a point `P ∈ K` such that the Odoni index `ι_K(f, P) =
[Aut(T_{f,∞}(P)) : G_{f,∞}(P)]` equals `1`, i.e. the arboreal Galois representation of `f` at `P` is
surjective.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.SplittingField.Construction

@[expose] public section

namespace MathlibExt.NumberTheory.OdoniArborealConjectureAMR126Problem0008Wanted

/-!
Source: R. Benedetto, P. Ingram, R. Jones, M. Manes, J. H. Silverman, T. J. Tucker, Current trends
and open problems in arithmetic dynamics, Bull. Amer. Math. Soc. 56 (2019), 611-685,
arXiv:1806.04980, section 'Arboreal Representations', Conjecture (Odoni, 1985). UnsolvedMath record
UM-00800385 (`AMR-126-0008`), dataset ulamai/UnsolvedMath v1.8.0.

Hilbertian is stated in Serre's thin-set form, which is the form of the source's footnote (`P¹(K)`
is not covered by finitely many images `F(C(K))` of degree `≥ 2` covers): for finitely many
irreducible `f(T, X) ∈ K[T][X]` of degree `≥ 2` in `X` and a finite set `S`, some `a ∉ S` has no
`f(a, X)` with a root in `K`. `ι_K(f, P) = 1` is stated level by level: every `fⁿ - P` is separable
and its splitting field has degree `(d!)^(1 + d + ⋯ + d^(n-1)) = |Aut T_n|`, which is surjectivity
onto the automorphism group of the tree of preimages at every level, hence onto the inverse limit.
Fields are restricted to characteristic zero, as in Odoni's original conjecture (Dittmann–Kadets,
Conjecture 1.1); this weakens the conjecture, so its refutation is at least as strong as one for all
Hilbertian fields.
-/

open Polynomial

/-- `K` is Hilbertian (Serre's thin-set form): `K` is not the union of a finite set and finitely
many sets `{a ∈ K : f(a, x) = 0 for some x ∈ K}` with `f(T, X) ∈ K[T][X]` irreducible of degree at
least two in `X` (the images of the `K`-points of degree `≥ 2` covers of the line). -/
def IsHilbertian (K : Type*) [Field K] : Prop :=
  ∀ s : Finset (Polynomial (Polynomial K)), (∀ f ∈ s, Irreducible f ∧ 2 ≤ f.natDegree) →
    ∀ S : Finset K, ∃ a : K, a ∉ S ∧ ∀ f ∈ s, ∀ x : K, (f.map (evalRingHom a)).eval x ≠ 0

/-- `ι_K(f, P) = 1`: for every `n`, `fⁿ(X) - P` is separable and its splitting field has degree
`(d!)^(1 + d + ⋯ + d^(n-1))` over `K`, the order of the automorphism group of the `d`-ary rooted
tree of depth `n` (`d = deg f`); that is, the arboreal Galois representation of `f` at `P` is
surjective at every level. -/
def OdoniIndexOne {K : Type*} [Field K] (f : K[X]) (P : K) : Prop :=
  ∀ n : ℕ, ((f.comp)^[n] X - C P).Separable ∧
    Module.finrank K ((f.comp)^[n] X - C P).SplittingField =
      f.natDegree.factorial ^ (∑ i ∈ Finset.range n, f.natDegree ^ i)

/-- Odoni's conjecture (in characteristic zero): for every Hilbertian field `K` of characteristic
zero and every `d ≥ 2` there are a monic `f ∈ K[X]` of degree `d` and `P ∈ K` with
`ι_K(f, P) = 1`. -/
def odoniConjecture : Prop :=
  ∀ (K : Type) [Field K] [CharZero K], IsHilbertian K → ∀ d : ℕ, 2 ≤ d →
    ∃ f : K[X], f.Monic ∧ f.natDegree = d ∧ ∃ P : K, OdoniIndexOne f P

/--
Resolved false: Dittmann and Kadets construct a Hilbertian field of characteristic zero (an
algebraic extension of ℚ) over which no polynomial of degree at least two has an arboreal Galois
representation of finite index, let alone a surjective one. Source: R. Benedetto, P. Ingram, R.
Jones, M. Manes, J. H. Silverman, T. J. Tucker, Current trends and open problems in arithmetic
dynamics, Bull. Amer. Math. Soc. 56 (2019), 611-685, arXiv:1806.04980, section 'Arboreal
Representations', Conjecture (Odoni, 1985); resolution: P. Dittmann, B. Kadets, Odoni's conjecture
on arboreal Galois representations is false, Proc. Amer. Math. Soc. 150 (2022), 3335-3343,
arXiv:2012.03076, Theorem 1.2: for every countable Hilbertian field k of characteristic zero there
is a Hilbertian algebraic extension F/k such that for every f ∈ F[x] of degree d ≥ 2 the image of
the arboreal representation has infinite index in Aut T_∞(d); the abstract presents it as the
refutation of Odoni's conjecture ('Odoni conjectured that for all Hilbertian fields K there exists a
polynomial f for which φ_f is surjective. We show that this conjecture is false.'). Their
representation is the one at basepoint 0; for a basepoint P apply the theorem to the translate x ↦
f(x + P) − P, whose iterated preimages of 0 are those of P under f, shifted by −P,
https://arxiv.org/abs/2012.03076.
-/
public theorem_wanted odoniConjecture_refuted : ¬ odoniConjecture

end MathlibExt.NumberTheory.OdoniArborealConjectureAMR126Problem0008Wanted
