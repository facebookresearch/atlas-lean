/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.IdeleNorm

/-!
# Norm-one idele class group

## ATLAS source correspondence

This is the number-field part of ATLAS NumberTheoryI N547, Definition 26.11.
The primary formal source is atlas-lean commit
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`,
[`v1/Atlas/NumberTheoryI/code/Ideles.lean`, lines 889--890](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/Ideles.lean#L889-L890), where
`Ideles.NormOneIdeleClassGroup` is defined as
`OneIdeleGroup K ⧸ (principalIdeles K).subgroupOf (OneIdeleGroup K)`.
The textbook statement is also indexed in
[`v1/Atlas/NumberTheoryI/targets.yaml`, lines 3904--3908](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/targets.yaml#L3904-L3908).

The declarations below map to that source as follows:

* `normOnePrincipalIdeles` is the source denominator
  `(principalIdeles K).subgroupOf (OneIdeleGroup K)`, expressed using this
  repository's native `normOneIdeles` and principal-idele API.
* `NormOneIdeleClassGroup` is exactly the source quotient `C_K^1 := I_K^1 / K^×`.
  Because it is a quotient of topological groups, it inherits the source's
  quotient topology.
* `normOne_mk_principalEmbedding` exposes the defining quotient fact that a
  principal idele represents the identity class.

The word "compact" in Definition 26.11 depends on N546, Theorem 26.9
(Fujisaki's lemma), formalized in the
[ATLAS source at `Ideles.lean`, lines 839--887](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/Ideles.lean#L839-L887).
That compactness result is intentionally outside this module's scope:
we define the quotient and its topology but do not assert a `CompactSpace`
instance.
-/

@[expose] public section

noncomputable section

namespace NumberField.TopologicalIdeleGroup

variable (K : Type*) [Field K] [NumberField K]

/-- **Principal ideles of norm one.** For a number field $K$, this is the subgroup of the group
$I_K^1$ of ideles of $K$ with adelic norm $1$ consisting of the principal ideles, that is, of the
elements of $I_K^1$ that are images of elements of $K^\times$ under the diagonal embedding. -/
public def normOnePrincipalIdeles : Subgroup (normOneIdeles K) :=
  (principalIdeles (NumberField.RingOfIntegers K) K).subgroupOf (normOneIdeles K)

/-- **Norm-one idele class group.** For a number field $K$, the norm-one idele class group
$C_K^1 = I_K^1 / K^\times$ is the quotient of the group $I_K^1$ of ideles of $K$ with adelic norm
$1$ by its subgroup of principal ideles, the images of the elements of $K^\times$ under the
diagonal embedding. -/
public abbrev NormOneIdeleClassGroup :=
  (normOneIdeles K) ⧸ (normOnePrincipalIdeles K)

/-- **Principal ideles are trivial in the norm-one idele class group.** Let $K$ be a number field.
For every $x \in K^\times$, the principal idele of $x$, viewed as an element of the group $I_K^1$
of ideles of $K$ with adelic norm $1$, has trivial class in the norm-one idele class group
$C_K^1 = I_K^1 / K^\times$. -/
@[simp]
public theorem normOne_mk_principalEmbedding (x : Kˣ) :
    QuotientGroup.mk (s := normOnePrincipalIdeles K)
        ⟨principalEmbedding (NumberField.RingOfIntegers K) K x,
          principalIdeles_le_normOneIdeles K ⟨x, rfl⟩⟩ = 1 := by
  rw [QuotientGroup.eq_one_iff]
  exact ⟨x, rfl⟩

end NumberField.TopologicalIdeleGroup
