/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Solvable
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Pointwise.Set.Card
import Mathlib.Data.SetLike.Fintype
import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Linear independence of permutation characters

The coset permutation characters of a finite insoluble group are linearly dependent,
answering Kourovka Notebook Problem 11.9, posed by I. I. Pyatetskiĭ-Shapiro and communicated
by Ya. G. Berkovich.
Following Brescia, Ingrosso and Trombetti, we factor the characters through the conjugacy
classes of cyclic subgroups. In a noncyclic group these omit the class of the whole group.
The dimension bound works directly over the rationals since the characters count fixed cosets.

## Record carried over from the retired wanted module

From `WantedExt/GroupTheory/PermutationCharactersIndependentKourovka11Problem9Wanted.lean`:

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 11.9 (Ya. G. Berkovich). UnsolvedMath
record UM-00700702 (`KOU-11.9`), dataset ulamai/UnsolvedMath v1.8.0.

The induced character `1_H^G` is the permutation character of `G` on the left cosets of `H`, `g ↦
#{xH : g x H = x H}`, as a `ℚ`-valued function (linear independence of integer-valued functions over
`ℚ` and over `ℂ` agree). The family is indexed by the conjugacy classes of subgroups (orbits of
`ConjAct G` on `Subgroup G`), choosing a representative of each.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.PermutationCharactersIndependentKourovka11Problem9Wanted

/-- **Rational permutation character on the cosets of a subgroup.** For a subgroup $H$ of a group
$G$, the permutation character $1_H^G : G \to \mathbb{Q}$ sends $g \in G$ to the number of left
cosets $xH$ of $H$ with $gxH = xH$, and to $0$ when $g$ fixes infinitely many cosets. -/
noncomputable def permChar {G : Type*} [Group G] (H : Subgroup G) (g : G) : ℚ :=
  Nat.card {c : G ⧸ H // g • c = c}

open scoped Pointwise in
/-- **Finite insoluble groups with independent permutation characters (Kourovka 11.9).**
The assertion that there is a finite non-soluble group $G$ such that, choosing a representative
$H$ of each conjugacy class of subgroups of $G$, the rational-valued permutation characters
$1_H^G$ of $G$ on the left cosets of these subgroups $H$ are linearly independent over
$\mathbb{Q}$. -/
def insolubleIndependentPermutationCharacters : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Finite G), ¬ Group.IsSolvable G ∧
    LinearIndependent ℚ fun c : MulAction.orbitRel.Quotient (ConjAct G) (Subgroup G) =>
      permChar (Quotient.out c)

open scoped Pointwise

private abbrev SubgroupClass (G : Type*) [Group G] :=
  MulAction.orbitRel.Quotient (ConjAct G) (Subgroup G)

private def cyclicClass {G : Type*} [Group G] (g : G) : SubgroupClass G :=
  Quotient.mk'' (Subgroup.zpowers g)

private theorem conj_smul_zpowers {G : Type*} [Group G] (a : ConjAct G) (g : G) :
    a • Subgroup.zpowers g = Subgroup.zpowers (a • g) :=
  MonoidHom.map_zpowers (MulDistribMulAction.toMonoidEnd _ _ a) g

private theorem permChar_eq_of_cyclicClass_eq {G : Type*} [Group G] (H : Subgroup G)
    {g h : G} (heq : cyclicClass g = cyclicClass h) : permChar H g = permChar H h := by
  obtain ⟨a, ha⟩ : ∃ a : ConjAct G, a • Subgroup.zpowers h = Subgroup.zpowers g :=
    Quotient.exact heq
  rw [conj_smul_zpowers] at ha
  have hfixed : MulAction.fixedBy (G ⧸ H) g = MulAction.fixedBy (G ⧸ H) (a • h) := by
    ext x
    exact ⟨smul_eq_self_of_mem_zpowers (Subgroup.zpowers_le.mp ha.le),
      smul_eq_self_of_mem_zpowers (Subgroup.zpowers_le.mp ha.ge)⟩
  change ((MulAction.fixedBy (G ⧸ H) g).ncard : ℚ) = (MulAction.fixedBy (G ⧸ H) h).ncard
  rw [hfixed, ConjAct.smul_def, ← MulAction.smul_fixedBy, Set.ncard_smul_set]

/-- **No insoluble group has independent permutation characters (Kourovka 11.9).** There is no
finite non-soluble group $G$ such that, choosing a representative $H$ of each conjugacy class of
subgroups of $G$, the rational-valued permutation characters $1_H^G$ of $G$ on the left cosets of
these subgroups $H$ are linearly independent over $\mathbb{Q}$.

Brescia, Ingrosso and Trombetti prove that these permutation characters are linearly independent
if and only if $G$ is cyclic; the Kourovka Notebook (21st issue) marks 11.9 solved, "No, there
are no such groups".

Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Problem 11.9 (Ya. G. Berkovich); resolution: M. Brescia, E. Ingrosso and M. Trombetti, On the
independence of permutation characters, arXiv:2608.16957 (2026), main theorem: the characters `π_H`,
`H` over representatives of the conjugacy classes of subgroups, are linearly independent iff `G` is
cyclic; the Kourovka Notebook (21st issue) marks 11.9 solved, https://arxiv.org/abs/2608.16957.
-/
theorem insolubleIndependentPermutationCharacters_refuted :
    ¬ insolubleIndependentPermutationCharacters := by
  classical
  rintro ⟨G, _, _, hns, hind⟩
  let := Fintype.ofFinite (SubgroupClass G)
  let cyclic := cyclicClass (G := G)
  -- Restrict each character to a generator representing each cyclic subgroup class.
  let chars (c : SubgroupClass G) (d : Set.range cyclic) :=
    permChar c.out (Set.rangeSplitting cyclic d)
  have hchars : LinearIndependent ℚ chars := by
    apply LinearIndependent.of_comp (LinearMap.funLeft ℚ ℚ (Set.rangeFactorization cyclic))
    convert hind using 1
    funext c g
    exact permChar_eq_of_cyclicClass_eq c.out
      (Set.apply_rangeSplitting cyclic (Set.rangeFactorization cyclic g))
  have hle := hchars.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at hle
  -- The class of the whole group is missing, since cyclic groups are soluble.
  have htop : (Quotient.mk'' (⊤ : Subgroup G) : SubgroupClass G) ∉ Set.range cyclic := by
    rintro ⟨g, hg⟩
    obtain ⟨a, ha⟩ : ∃ a : ConjAct G, a • Subgroup.zpowers g = ⊤ := Quotient.exact hg.symm
    rw [conj_smul_zpowers] at ha
    have : IsCyclic G := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨a • g, ha⟩
    exact hns inferInstance
  exact (Fintype.card_subtype_lt htop).not_ge hle

end MathlibExt.GroupTheory.PermutationCharactersIndependentKourovka11Problem9Wanted
