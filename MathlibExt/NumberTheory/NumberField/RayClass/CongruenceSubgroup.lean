/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.NumberField.RayClass.Group

/-!
# Congruence subgroups (N419 Definition 22.1)
A congruence subgroup is a subgroup of the coprime ideals
containing the ray group. Its image in the ray class group,
ambient version, smallest/largest examples follow.
-/

noncomputable section
open scoped nonZeroDivisors

namespace NumberField.Modulus
variable {K : Type*} [Field K] [NumberField K]

/-- **Congruence subgroup.** Let $K$ be a number field and $\mathfrak m$ a modulus of $K$. A
congruence subgroup for $\mathfrak m$ is a subgroup $H$ of the group of invertible fractional
ideals of $K$ coprime to the finite part of $\mathfrak m$ such that $H$ contains the ray group
of $\mathfrak m$. -/
@[ext] structure CongruenceSubgroup (m : Modulus K) where
  /-- Underlying subgroup of the coprime ideals. -/
  toSubgroup : Subgroup (coprimeFractionalIdeals m)
  /-- The ray group is contained in the subgroup. -/
  rayGroup_le : rayGroup m ≤ toSubgroup

namespace CongruenceSubgroup
variable {m : Modulus K}

/-- **Image of a congruence subgroup in the ray class group.** Let $H$ be a congruence subgroup
for a modulus $\mathfrak m$ of a number field $K$, and let $\pi$ be the canonical projection from
the group of invertible fractional ideals of $K$ coprime to the finite part of $\mathfrak m$ onto
the ray class group of $\mathfrak m$. The image of $H$ is the subgroup $\pi(H)$ of the ray class
group. -/
def image (C : CongruenceSubgroup (K := K) m) :
    Subgroup (RayClassGroup m) :=
  C.toSubgroup.map (rayClassMap m)

/-- **Membership in the image of a congruence subgroup.** Let $H$ be a congruence subgroup for a
modulus $\mathfrak m$ of a number field $K$, and let $\pi$ be the canonical projection from the
group of invertible fractional ideals of $K$ coprime to the finite part of $\mathfrak m$ onto the
ray class group of $\mathfrak m$. An element $x$ of the ray class group lies in the image $\pi(H)$
if and only if $\pi(y) = x$ for some $y \in H$. -/
theorem mem_image_iff (C : CongruenceSubgroup (K := K) m)
    (x : RayClassGroup m) :
    x ∈ C.image ↔ ∃ y ∈ C.toSubgroup, rayClassMap m y = x :=
  Subgroup.mem_map

@[simp] theorem image_comap (C : CongruenceSubgroup (K := K) m) :
    C.image.comap (rayClassMap m) = C.toSubgroup := by
  unfold image
  rw [Subgroup.comap_map_eq, sup_eq_left, rayClassMap_ker]
  exact C.rayGroup_le

/-- **Congruence subgroup as a subgroup of all invertible fractional ideals.** For a congruence
subgroup $H$ for a modulus $\mathfrak m$ of a number field $K$, this is the image of $H$ under the
inclusion of the group of invertible fractional ideals of $K$ coprime to the finite part of
$\mathfrak m$ into the group of all invertible fractional ideals of $K$. -/
def toAmbientSubgroup (C : CongruenceSubgroup (K := K) m) :
    Subgroup ((FractionalIdeal (𝓞 K)⁰ K)ˣ) :=
  C.toSubgroup.map (coprimeFractionalIdeals m).subtype

theorem toAmbientSubgroup_le (C : CongruenceSubgroup (K := K) m) :
    C.toAmbientSubgroup ≤ coprimeFractionalIdeals m := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp hx
  exact y.property

/-- **Smallest congruence subgroup.** For a modulus $\mathfrak m$ of a number field $K$, the
smallest congruence subgroup for $\mathfrak m$ is the ray group of $\mathfrak m$ itself, a
subgroup of the group of invertible fractional ideals of $K$ coprime to the finite part of
$\mathfrak m$. -/
def smallest (m : Modulus K) : CongruenceSubgroup (K := K) m :=
  ⟨rayGroup m, le_rfl⟩

/-- **Largest congruence subgroup.** For a modulus $\mathfrak m$ of a number field $K$, the largest
congruence subgroup for $\mathfrak m$ is the whole group of invertible fractional ideals of $K$
coprime to the finite part of $\mathfrak m$, which contains the ray group of $\mathfrak m$. -/
def largest (m : Modulus K) : CongruenceSubgroup (K := K) m :=
  ⟨⊤, le_top⟩

theorem smallest_image (m : Modulus K) :
    (smallest (K := K) m).image = ⊥ := by
  rw [image, smallest, eq_bot_iff]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_bot, rayClassMap_eq_one_iff]
  exact hy

theorem largest_image (m : Modulus K) :
    (largest (K := K) m).image = ⊤ := by
  rw [image, largest, eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := rayClassMap_surjective m x
  exact Subgroup.mem_map_of_mem _ (Subgroup.mem_top y)

end CongruenceSubgroup
end NumberField.Modulus
