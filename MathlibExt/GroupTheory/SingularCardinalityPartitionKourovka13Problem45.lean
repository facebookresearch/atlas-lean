/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.Algebra.Group.Pointwise.Set.Card
import Mathlib.SetTheory.Cardinal.Finsupp

/-!
# Partitions of groups of singular cardinality (Kourovka Notebook Problem 13.45)

A free abelian group of cardinality `ℵ_ ω` refutes the proposed partition property.

Kourovka Notebook, Archive of Solved Problems, Problem 13.45 (I. V. Protasov): every infinite group
`G` of regular cardinality `𝔪` can be partitioned as `G = A₁ ∪ A₂` so that `A₁ F ≠ G` and `A₂ F ≠ G`
for every `F ⊆ G` with `|F| < 𝔪`. Is this true for groups of singular cardinality?
-/

@[expose] public section

namespace MathlibExt.GroupTheory.SingularCardinalityPartitionKourovka13Problem45Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 13.45 (I. V.
Protasov). UnsolvedMath record UM-00700963 (`KOU-13.45`), dataset ulamai/UnsolvedMath v1.8.0.

The target is the statement for every infinite group of singular cardinality, with `A₁ F` the
pointwise product as in the problem. The resolving paper writes `F A₁`; its counterexamples are
abelian, where the two products agree. Singular means not regular (`Cardinal.IsRegular`) for the
infinite cardinal `#G`; groups are taken in `Type`.
-/

open Cardinal
open scoped Pointwise

/-- **Partitions of groups of singular cardinality (Kourovka 13.45).** The statement that every
infinite group $G$ whose cardinality $\mathfrak{m} = |G|$ is singular (not regular) can be split
into two disjoint sets $A_1$ and $A_2$ with $A_1 \cup A_2 = G$ such that $A_1 F \ne G$ and
$A_2 F \ne G$ for every subset $F \subseteq G$ with $|F| < \mathfrak{m}$, where
$A F = \{a f : a \in A, f \in F\}$. -/
def singularCardinalityPartition : Prop :=
  ∀ (G : Type) [Group G], Infinite G → ¬ (#G).IsRegular →
    ∃ A₁ A₂ : Set G, A₁ ∪ A₂ = Set.univ ∧ Disjoint A₁ A₂ ∧
      ∀ F : Set G, #F < #G → A₁ * F ≠ Set.univ ∧ A₂ * F ≠ Set.univ

open Ordinal in
/-- In an abelian group of singular cardinality, one of two covering sets becomes the
whole group after right multiplication by a set of smaller cardinality. -/
private theorem exists_small_mul_eq_univ {G : Type} [CommGroup G] (hG : (#G).IsSingular)
    {A B : Set G} (hAB : A ∪ B = Set.univ) :
    ∃ F : Set G, #F < #G ∧ (A * F = Set.univ ∨ B * F = Set.univ) := by
  classical
  by_cases hA : ∃ F : Set G, #F < #G ∧ A * F = Set.univ
  · obtain ⟨F, hF, hAF⟩ := hA
    exact ⟨F, hF, Or.inl hAF⟩
  -- A cofinal family of proper initial segments covers the group.
  obtain ⟨_, _, hOrd⟩ := exists_ord_eq_type_lt G
  have : NoMaxOrder G := by
    rw [← isSuccPrelimit_type_lt_iff, ← hOrd]
    exact (isSuccLimit_ord hG.aleph0_le).isSuccPrelimit
  obtain ⟨s, hs, hCard⟩ := Order.exists_cof_eq G
  have hslt : #s < #G := by
    rw [hCard, ← cof_type, ← hOrd]
    exact hG.cof_ord_lt
  -- Choose a right translate of each initial segment contained in the second set.
  have hMissing (i : s) : ∃ g, g ∉ A * (Set.Iio (i : G))⁻¹ := by
    refine (Set.ne_univ_iff_exists_notMem _).1 fun hEq => hA ⟨_, ?_, hEq⟩
    rw [Cardinal.mk_inv]
    exact mk_Iio_lt i.1 hOrd
  choose g hg using hMissing
  refine ⟨Set.range (fun i => (g i)⁻¹), mk_range_le.trans_lt hslt, Or.inr ?_⟩
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨y, hxy⟩ := exists_gt x
  obtain ⟨i, hi, hyi⟩ := hs y
  let j : s := ⟨i, hi⟩
  have hx : x ∈ Set.Iio (j : G) := hxy.trans_le hyi
  have hunion : x * g j ∈ A ∪ B := hAB.symm ▸ Set.mem_univ _
  have hB : x * g j ∈ B := hunion.resolve_left fun hAx =>
    hg j (Set.mem_mul.2 ⟨x * g j, hAx, x⁻¹, Set.inv_mem_inv.2 hx,
      by rw [mul_comm x, mul_inv_cancel_right]⟩)
  exact Set.mem_mul.2 ⟨x * g j, hB, (g j)⁻¹, Set.mem_range_self j, mul_inv_cancel_right _ _⟩

/--
**Some group of singular cardinality has no such partition.** There is an infinite group $G$
whose cardinality $\mathfrak{m} = |G|$ is singular (not regular) such that for all disjoint sets
$A_1$ and $A_2$ with $A_1 \cup A_2 = G$ there is a subset $F \subseteq G$ with
$|F| < \mathfrak{m}$ and $A_1 F = G$ or $A_2 F = G$, where $A F = \{a f : a \in A, f \in F\}$.
That is, the statement of Kourovka Problem 13.45 fails.

Protasov and Slobodianiuk show that the answer depends on the algebraic structure of $G$: such a
partition exists for every free group, but not for abelian groups of singular cardinality. The
Kourovka Archive answers 13.45 "No, not always".

Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 13.45 (I. V. Protasov); resolution: I. Protasov and S.
Slobodianiuk, A note on partitions of groups, Quest. Answers Gen. Topology 33 (2015), no. 2, 61-70,
arXiv:1408.5607, abstract and Theorem 2(iii): the statement fails for abelian groups of singular
cardinality (it holds for free groups); Kourovka Archive, Problem 13.45,
https://arxiv.org/abs/1408.5607.
-/
theorem singularCardinalityPartition_refuted : ¬ singularCardinalityPartition := by
  let κ : Cardinal := ℵ_ Ordinal.omega0
  have hκ : κ.IsSingular := isSingular_aleph_omega0
  let I := κ.out
  have hI : #I = κ := mk_out κ
  have : Infinite I := aleph0_le_mk_iff.1 (hI.symm ▸ hκ.aleph0_le)
  let G := Multiplicative (I →₀ ℤ)
  have hCard : #G = κ := by
    rw [← Multiplicative.ofAdd.cardinal_eq, mk_finsupp_of_infinite, hI, mk_int,
      max_eq_left hκ.aleph0_le]
  have hG : (#G).IsSingular := hCard.symm ▸ hκ
  intro h
  obtain ⟨A, B, hAB, _, hNeither⟩ :=
    h G (aleph0_le_mk_iff.1 hG.aleph0_le) hG.not_isRegular
  obtain ⟨F, hF, hCover⟩ := exists_small_mul_eq_univ hG hAB
  exact hCover.elim (hNeither F hF).1 (hNeither F hF).2

end MathlibExt.GroupTheory.SingularCardinalityPartitionKourovka13Problem45Wanted
