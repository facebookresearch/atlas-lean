/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Domains not embeddable in skew fields (Kourovka Notebook Problem 1.4)

Kourovka Notebook, Archive of Solved Problems, Problem 1.4 (A. I. Mal'cev; L. A. Bokut'): does there
exist a ring without zero divisors which is not embeddable in a skew field, while the multiplicative
semigroup of its non-zero elements is embeddable in a group?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Ring.Hom.Defs

@[expose] public section

namespace MathlibExt.Algebra.DomainNotEmbeddableSkewFieldKourovka1Problem4Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.4 (A. I.
Mal'cev; L. A. Bokut'). UnsolvedMath record UM-00700004 (`KOU-1.4`), dataset ulamai/UnsolvedMath
v1.8.0.

Rings are associative with identity (`Ring`), and a ring without zero divisors is taken nonzero
(`IsDomain`), since the zero ring has no ring homomorphism to a skew field and would qualify
trivially. The multiplicative semigroup of nonzero elements of a domain is the monoid
`nonZeroDivisors R`. Embeddings are injective homomorphisms; skew fields and groups are taken in
`Type`.
-/

/-- Kourovka 1.4 (A. I. Mal'cev): there is a ring without zero divisors (a domain: a nonzero ring
with identity) that has no injective ring homomorphism into a skew field, while the multiplicative
monoid of its nonzero elements has an injective monoid homomorphism into a group. -/
def existsDomainGroupEmbeddableNotSkewFieldEmbeddable : Prop :=
  ∃ (R : Type) (_ : Ring R), IsDomain R ∧
    (¬ ∃ (D : Type) (_ : DivisionRing D) (f : R →+* D), Function.Injective f) ∧
    ∃ (H : Type) (_ : Group H) (f : nonZeroDivisors R →* H), Function.Injective f

/--
Resolved true: the Kourovka Archive answers 1.4 "Yes", citing the independent examples of Bokut',
Bowtell and Klein of rings without zero divisors whose multiplicative semigroup of nonzero elements
embeds in a group although the ring does not embed in a skew field. Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.4 (A. I. Mal'cev; L. A. Bokut');
resolution: L. A. Bokut', Soviet Math. Dokl. 8 (1967), 901-904; A. Bowtell, On a question of
Mal'cev, J. Algebra 7 (1967), 126-139; A. Klein, Rings nonembeddable in fields with multiplicative
semigroups embeddable in groups, J. Algebra 7 (1967), 100-125, Kourovka Archive, Problem 1.4 (Yes).
-/
public theorem_wanted existsDomainGroupEmbeddableNotSkewFieldEmbeddable_holds :
    existsDomainGroupEmbeddableNotSkewFieldEmbeddable

end MathlibExt.Algebra.DomainNotEmbeddableSkewFieldKourovka1Problem4Wanted
