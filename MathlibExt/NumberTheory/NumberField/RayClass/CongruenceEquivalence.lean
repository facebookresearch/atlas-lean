/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.NumberField.RayClass.CongruenceSubgroup

/-!
# Congruence subgroup pair equivalence (N420 Definition 22.3)

Pairs of a modulus with a congruence subgroup for it, and the
equivalence relation comparing two pairs inside the common ambient
group of all nonzero fractional ideals. Transitivity is not claimed
here; it needs arithmetic approximation (N421).
-/

noncomputable section
open scoped nonZeroDivisors

namespace NumberField.Modulus
variable {K : Type*} [Field K] [NumberField K]

/-- **Congruence subgroup pair.** Let $K$ be a number field. A congruence subgroup pair for $K$
consists of a modulus $\mathfrak m$ of $K$ together with a congruence subgroup for
$\mathfrak m$, that is, a subgroup of the group of invertible fractional ideals of $K$ coprime to
the finite part of $\mathfrak m$ that contains the ray group of $\mathfrak m$. -/
structure CongruenceSubgroupPair (K : Type*) [Field K] [NumberField K] where
  /-- The modulus of the pair. -/
  modulus : Modulus K
  /-- The congruence subgroup for `modulus`. -/
  subgroup : CongruenceSubgroup modulus

namespace CongruenceSubgroupPair

/-- **Equivalence of congruence subgroup pairs.** Let $K$ be a number field. For a modulus
$\mathfrak m$ of $K$, write $I^{\mathfrak m}$ for the group of nonzero fractional ideals of $K$
coprime to the finite part of $\mathfrak m$. Two pairs $(\mathfrak m, H)$ and $(\mathfrak n, H')$,
each consisting of a modulus of $K$ and a congruence subgroup for it, are equivalent when
$I^{\mathfrak m} \cap H' = I^{\mathfrak n} \cap H$, where both congruence subgroups are viewed as
subgroups of the group of all nonzero fractional ideals of $K$. -/
def IsEquivalent (P Q : CongruenceSubgroupPair K) : Prop :=
  coprimeFractionalIdeals P.modulus ⊓ Q.subgroup.toAmbientSubgroup =
    coprimeFractionalIdeals Q.modulus ⊓ P.subgroup.toAmbientSubgroup

/-- **Criterion for equivalence of congruence subgroup pairs.** Let $K$ be a number field, and for
a modulus $\mathfrak m$ of $K$ write $I^{\mathfrak m}$ for the group of nonzero fractional ideals
of $K$ coprime to the finite part of $\mathfrak m$. Two pairs $(\mathfrak m, H)$ and
$(\mathfrak n, H')$, each consisting of a modulus of $K$ and a congruence subgroup for it, are
equivalent if and only if $I^{\mathfrak m} \cap H' = I^{\mathfrak n} \cap H$ in the group of all
nonzero fractional ideals of $K$. -/
theorem isEquivalent_iff (P Q : CongruenceSubgroupPair K) :
    IsEquivalent P Q ↔
      coprimeFractionalIdeals P.modulus ⊓ Q.subgroup.toAmbientSubgroup =
        coprimeFractionalIdeals Q.modulus ⊓ P.subgroup.toAmbientSubgroup :=
  Iff.rfl

/-- **Equivalence of congruence subgroup pairs is reflexive.** Let $K$ be a number field. Every
pair consisting of a modulus of $K$ and a congruence subgroup for it is equivalent to itself. -/
theorem IsEquivalent.refl (P : CongruenceSubgroupPair K) :
    IsEquivalent P P :=
  rfl

/-- **Equivalence of congruence subgroup pairs is symmetric.** Let $K$ be a number field. If a
pair $P$, consisting of a modulus of $K$ and a congruence subgroup for it, is equivalent to such
a pair $Q$, then $Q$ is equivalent to $P$. -/
theorem IsEquivalent.symm {P Q : CongruenceSubgroupPair K} :
    IsEquivalent P Q → IsEquivalent Q P :=
  Eq.symm

end CongruenceSubgroupPair
end NumberField.Modulus
