/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# An amenable group of Hilbert space compression below 1/2 (Oberwolfach Reports 27/2009)

Oberwolfach workshop Manifold Perspectives (2009), G. N. Arzhantseva, Uniform embeddings of groups
into a Hilbert space, open problem (ii): is there an amenable group of Hilbert space compression
value `< 1/2`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Cayley
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import MathlibExt.GroupTheory.AmenableGroup

@[expose] public section

namespace MathlibExt.GroupTheory.AmenableHilbertCompressionOWR3477Problem016Wanted

/-!
Source: G. N. Arzhantseva, Uniform embeddings of groups into a Hilbert space, in Manifold
Perspectives, Oberwolfach Reports 6 (2009), no. 27, pp. 1527-1529, open problem (ii), p. 1529, DOI
10.4171/OWR/2009/27. UnsolvedMath record UM-30001267 (`OWR-3477-016`), dataset ulamai/UnsolvedMath
v1.8.0.

Groups are finitely generated with the word metric of a finite generating set `S` (graph distance in
`SimpleGraph.mulCayley S`); the source defines the compression `R(G)` as the supremum of the `α`
with `d(g, h)^α ≼ ‖f(g) - f(h)‖` over `1`-Lipschitz maps `f` into a separable Hilbert space, `≼`
read as `C d^α - D ≤ ‖f g - f h‖`. Attained exponents form a down-set, so `R(G) < 1/2` is stated as:
some `α < 1/2` is not attained (this also keeps finite groups, which attain every exponent, out).
Amenability is MathlibExt's Følner condition `IsAmenable`. Problems (i) (the compression of
Grigorchuk's group, open-ended), (iii) and (iv) of the same list are not formalized.
-/

/-- The word metric of `G` for the finite set `S`: the graph distance in the Cayley graph
`SimpleGraph.mulCayley S` (the length of a shortest word in `S ∪ S⁻¹` representing `g⁻¹ h` when
`S` generates `G`). -/
noncomputable def wordDist {G : Type*} [Group G] (S : Finset G) (g h : G) : ℝ :=
  ((SimpleGraph.mulCayley (S : Set G)).dist g h : ℝ)

/-- The exponent `α` is attained by a uniform embedding of `(G, d_S)` into a separable real Hilbert
space: some `1`-Lipschitz `f : G → H` and constants `C > 0`, `D` satisfy
`C d_S(g, h)^α - D ≤ ‖f g - f h‖` for all `g, h`. The Hilbert space compression of `G` is the
supremum of the attained exponents. -/
def AttainsCompression (G : Type*) [Group G] (S : Finset G) (α : ℝ) : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
    (_ : TopologicalSpace.SeparableSpace H) (f : G → H) (C D : ℝ),
    0 < C ∧ (∀ g h, ‖f g - f h‖ ≤ wordDist S g h) ∧
      ∀ g h, C * wordDist S g h ^ α - D ≤ ‖f g - f h‖

/-- Arzhantseva's question (ii) (Oberwolfach Report 27/2009, p. 1529): there is a finitely generated
amenable group whose Hilbert space compression is less than `1/2`. Since the attained exponents form
a down-set (`d_S ≥ 1` off the diagonal), compression `< 1/2` means that some exponent `α < 1/2` is
not attained. -/
def amenableCompressionBelowHalf : Prop :=
  ∃ (G : Type) (_ : Group G) (S : Finset G), Subgroup.closure (S : Set G) = ⊤ ∧ IsAmenable G ∧
    ∃ α : ℝ, α < 1 / 2 ∧ ¬ AttainsCompression G S α

/--
Resolved true: Austin (Theorem 1.1) constructs a finitely generated amenable group with no
`1`-Lipschitz embedding into `L₂` (a separable Hilbert space) with positive compression exponent, so
its Hilbert space compression is `0 < 1/2`. Source: G. N. Arzhantseva, Uniform embeddings of groups
into a Hilbert space, in Manifold Perspectives, Oberwolfach Reports 6 (2009), no. 27, pp. 1527-1529,
open problem (ii), p. 1529, DOI 10.4171/OWR/2009/27; resolution: T. Austin, Amenable groups with
very poor compression into Lebesgue spaces, Duke Math. J. 159 (2011), 187-222, DOI
10.1215/00127094-1415860, arXiv:0909.2047, Theorem 1.1: there is a finitely generated amenable group
that does not admit any embedding into L_p with a positive compression exponent for any p ∈ [1, ∞)
(abstract: no coarse 1-Lipschitz embedding with positive compression exponent, answering a question
of Arzhantseva, Guba and Sapir); for p = 2 its Hilbert space compression is 0,
https://arxiv.org/abs/0909.2047.
-/
public theorem_wanted amenableCompressionBelowHalf_holds : amenableCompressionBelowHalf

end MathlibExt.GroupTheory.AmenableHilbertCompressionOWR3477Problem016Wanted
