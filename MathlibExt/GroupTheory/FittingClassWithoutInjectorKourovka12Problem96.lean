/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.Solvable
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# A Fitting class and a non-soluble group without injectors (Kourovka Notebook Problem 12.96)

Kourovka Notebook, Archive of Solved Problems, Problem 12.96 (L. A. Shemetkov): find a non-empty
Fitting class `𝔉` and a non-soluble finite group `G` such that `G` has no `𝔉`-injectors.

The theorem `fittingClassWithoutInjectors_holds` uses the central product of three copies of
$L = \mathrm{SL}_2(\mathbf F_5)$. Put $S = L/Z(L)$. A group belongs to the class if each of its
subnormal subgroups maps trivially to every group receiving only trivial homomorphisms from $S$.
Each pair of coordinate groups contains a diagonal copy of $S$. Maximality on two overlapping pairs
would force an injector to project onto $S$ from both intersections. Their commutators lie in the
single shared coordinate, where the injector has trivial intersection, forcing $S$ to be abelian.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.96 (L. A.
Shemetkov). UnsolvedMath record UM-00700913 (`KOU-12.96`), dataset ulamai/UnsolvedMath v1.8.0.

Classes of finite groups are isomorphism-closed predicates on groups in `Type` (`GroupClass`, as in
the `OpenConjectures` entries `Kourovka11Problem117` and `Kourovka12Problem35`); only their finite
members are constrained. A Fitting class is closed under normal subgroups and under products of two
normal members; non-empty means that it contains some finite group. An `𝔉`-injector of `G` is a
subgroup `V` such that `V ⊓ N` is `𝔉`-maximal in `N` for every subnormal subgroup `N` (the
definition used in `OpenConjectures` entry `Kourovka11Problem117`, which asks the open variant for
Fitting classes of soluble groups).
-/

@[expose] public section

namespace MathlibExt.GroupTheory.FittingClassWithoutInjectorKourovka12Problem96Wanted

/-- **Isomorphism-closed classes of groups (Kourovka 12.96).** A class of groups is a property of
groups that is closed under isomorphism: if a group $H$ has the property and $K$ is a group
isomorphic to $H$, then $K$ has it too.

Only finite members matter for Fitting classes and for injectors of finite groups. -/
structure GroupClass where
  /-- Membership predicate. -/
  mem : ∀ (H : Type) [Group H], Prop
  /-- Closure under isomorphism. -/
  iso : ∀ (H K : Type) [Group H] [Group K], (H ≃* K) → mem H → mem K

/-- **Fitting classes of finite groups.** A class $\mathfrak{X}$ of groups is a Fitting class of
finite groups if, for every finite group $G$, every normal subgroup of $G$ lies in $\mathfrak{X}$
whenever $G$ does, and the product $N_1 N_2$ of two normal subgroups $N_1$ and $N_2$ of $G$ lies in
$\mathfrak{X}$ whenever $N_1$ and $N_2$ do. -/
def IsFitting (X : GroupClass) : Prop :=
  (∀ (G : Type) [Group G] [Finite G] (N : Subgroup G), N.Normal → X.mem G → X.mem N) ∧
  ∀ (G : Type) [Group G] [Finite G] (N₁ N₂ : Subgroup G), N₁.Normal → N₂.Normal →
    X.mem N₁ → X.mem N₂ → X.mem ↥(N₁ ⊔ N₂)

/-- **Maximal subgroups within a class of groups.** Let $\mathfrak{X}$ be a class of groups and let
$V$ and $K$ be subgroups of a group $G$. Then $V$ is $\mathfrak{X}$-maximal in $K$ if $V \le K$,
$V$ lies in $\mathfrak{X}$, and no subgroup $W$ of $G$ with $V < W \le K$ lies in $\mathfrak{X}$. -/
def IsXMaximalIn (X : GroupClass) {G : Type} [Group G] (V K : Subgroup G) : Prop :=
  V ≤ K ∧ X.mem V ∧ ∀ W : Subgroup G, V < W → W ≤ K → ¬ X.mem W

/-- **Injectors.** Let $\mathfrak{X}$ be a class of groups and $G$ a group. A subgroup $V$ of $G$ is
an $\mathfrak{X}$-injector of $G$ if, for every subnormal subgroup $N$ of $G$, the intersection
$V \cap N$ is $\mathfrak{X}$-maximal in $N$. -/
def IsInjector (X : GroupClass) {G : Type} [Group G] (V : Subgroup G) : Prop :=
  ∀ N : Subgroup G, N.IsSubnormal → IsXMaximalIn X (V ⊓ N) N

/-- **Kourovka Problem 12.96: a Fitting class without injectors.** The statement that there are a
Fitting class $\mathfrak{X}$ of finite groups that contains at least one finite group and a finite
non-soluble group $G$ such that no subgroup of $G$ is an $\mathfrak{X}$-injector of $G$.

The problem was posed by L. A. Shemetkov. -/
def fittingClassWithoutInjectors : Prop :=
  ∃ X : GroupClass, IsFitting X ∧ (∃ (H : Type) (_ : Group H) (_ : Finite H), X.mem H) ∧
    ∃ (G : Type) (_ : Group G) (_ : Finite G), ¬ Group.IsSolvable G ∧
      ∀ V : Subgroup G, ¬ IsInjector X V

open Function Subgroup

-- Test subnormal subgroups against groups receiving only trivial homomorphisms from S.
private def Null (A D : Type) [Group A] [Group D] : Prop :=
  ∀ f : A →* D, f = 1

private def Member (S G : Type) [Group S] [Group G] : Prop :=
  ∀ K : Subgroup G, K.IsSubnormal → ∀ (D : Type) [Group D], Null S D → Null K D

private lemma null_image {A B D : Type} [Group A] [Group B] [Group D]
    (p : A →* B) (hp : Surjective p) (h : Null A D) : Null B D := by
  intro f
  ext b
  obtain ⟨a, rfl⟩ := hp b
  exact DFunLike.congr_fun (h (f.comp p)) a

private lemma member_image {S A B : Type} [Group S] [Group A] [Group B]
    (p : A →* B) (hp : Surjective p) (h : Member S A) : Member S B := by
  intro K hK D _ hD
  exact null_image (p.subgroupComap K) (p.subgroupComap_surjective K hp)
    (h _ (hK.comap p) D hD)

private lemma member_subnormal {S G : Type} [Group S] [Group G] {N : Subgroup G}
    (hN : N.IsSubnormal) (h : Member S G) : Member S N := by
  intro K hK D _ hD
  let e := K.equivMapOfInjective N.subtype N.subtype_injective
  exact null_image e.symm e.symm.surjective (h _ (hK.trans' hN) D hD)

private lemma member_extension {S G B : Type} [Group S] [Group G] [Group B]
    (p : G →* B) (hp : Surjective p) (hker : Member S p.ker) (hB : Member S B) :
    Member S G := by
  intro K hK D _ hD f
  let q := p.subgroupMap K
  -- The restriction to K ∩ ker p vanishes, so f factors through the image of K.
  have hq : q.ker ≤ f.ker := by
    intro k hk
    let i := p.ker.subtype.subgroupComap K
    have hi := hker _ (hK.comap p.ker.subtype) D hD (f.comp i)
    exact DFunLike.congr_fun hi ⟨⟨k, congrArg Subtype.val hk⟩, k.property⟩
  let g := q.liftOfSurjective (p.subgroupMap_surjective K) ⟨f, hq⟩
  have hg : g = 1 := hB _ (hK.map hp) D hD g
  ext k
  exact (q.liftOfRightInverse_comp_apply _ _ _ k).symm.trans (DFunLike.congr_fun hg (q k))

private def testClass (S : Type) [Group S] : GroupClass where
  mem G _ := Member S G
  iso _ _ _ _ e := member_image e.toMonoidHom e.surjective

private lemma testClass_fitting (S : Type) [Group S] : IsFitting (testClass S) := by
  refine ⟨fun G _ _ N hN ↦ member_subnormal hN.isSubnormal, ?_⟩
  intro G _ _ H N _ hN hH hNmem
  let U := N.subgroupOf (H ⊔ N)
  let q := QuotientGroup.mk' U
  apply member_extension q (QuotientGroup.mk'_surjective U)
  · dsimp only [q]
    rw [QuotientGroup.ker_mk']
    let e := (subgroupOfEquivOfLe (le_sup_right : N ≤ H ⊔ N)).symm
    exact member_image e.toMonoidHom e.surjective hNmem
  · let e := QuotientGroup.quotientInfEquivProdNormalQuotient H N
    exact member_image e.toMonoidHom e.surjective
      (member_image (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective (N.subgroupOf H)) hH)

private lemma simple_member (S : Type) [Group S] [IsSimpleGroup S] : Member S S := by
  intro K hK D _ hD
  rcases hK.eq_bot_or_top_of_isSimpleGroup inferInstance with rfl | rfl
  · exact fun f ↦ Subsingleton.elim _ _
  · exact null_image (Subgroup.topEquiv.symm : S ≃* _) Subgroup.topEquiv.symm.surjective hD

private lemma member_null {S A D : Type} [Group S] [Group A] [Group D]
    (hA : Member S A) (hD : Null S D) : Null A D :=
  null_image (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A) Subgroup.topEquiv.surjective
    (hA _ .top D hD)

open scoped MatrixGroups

private instance five_prime : Fact (Nat.Prime 5) := ⟨by decide⟩

private abbrev Cover := SL(2, ZMod 5)
private abbrev Simple := PSL(2, ZMod 5)
private abbrev centerQuot := QuotientGroup.mk' (center Cover)

private instance simpleGroup : IsSimpleGroup Simple :=
  Matrix.ProjectiveSpecialLinearGroup.rank_two_simple' (F := ZMod 5) ⟨2, by decide, by decide⟩

private instance perfectCover : Group.IsPerfect Cover :=
  ⟨Matrix.SL2.commutator_eq_top (a := (2 : ZMod 5)) (by decide) (by decide)⟩

private lemma card_center : Nat.card (center Cover) = 2 := by
  rw [Nat.card_congr
    (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (R := ZMod 5) (0 : Fin 2)).toEquiv]
  simpa using (IsPrimitiveRoot.neg_one 5 (by decide : 5 ≠ 2)).card_rootsOfUnity (R := ZMod 5)

private lemma injective_of_ne_one {B : Type} [Group B] {f : Simple →* B} (hf : f ≠ 1) :
    Injective f := by
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with h | h
  · exact f.ker_eq_bot_iff.mp h
  · exact (hf (MonoidHom.ker_eq_top_iff.mp h)).elim

-- A copy of the simple quotient inside its double cover would have index two.
-- The resulting cyclic quotient is impossible because the cover is perfect.
private lemma cover_null : Null Simple Cover := by
  intro f
  by_contra hf
  have he := MonoidHom.ofInjective (injective_of_ne_one hf)
  have hr : Nat.card f.range = Nat.card Simple := (Nat.card_congr he.toEquiv).symm
  have hi : f.range.index = 2 := by
    have h := f.range.card_mul_index
    rw [hr, (center Cover).card_eq_card_quotient_mul_card_subgroup, card_center] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  have := f.range.normal_of_index_eq_two hi
  have hc : Nat.card (Cover ⧸ f.range) = 2 := hi
  have : Nontrivial (Cover ⧸ f.range) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have : IsCyclic (Cover ⧸ f.range) := isCyclic_of_prime_card hc
  have := IsCyclic.isMulCommutative (α := Cover ⧸ f.range)
  exact Group.IsPerfect.not_isSolvable (Cover ⧸ f.range) inferInstance

open scoped IsMulCommutative

private abbrev Triple := Fin 3 → Cover

-- In the central product a triple of central elements is killed precisely when
-- their product is one. Thus all three coordinate copies have the same center.
private def relations : Subgroup Triple where
  carrier := {x | ∃ z : Fin 3 → center Cover, (∏ k, z k) = 1 ∧ ∀ k, ↑(z k) = x k}
  one_mem' := ⟨1, by simp, fun _ ↦ rfl⟩
  mul_mem' := by
    rintro x y ⟨z, hz, hx⟩ ⟨w, hw, hy⟩
    exact ⟨z * w, by simp [Pi.mul_apply, Finset.prod_mul_distrib, hz, hw],
      fun k ↦ by simp [hx, hy]⟩
  inv_mem' := by
    rintro x ⟨z, hz, hx⟩
    exact ⟨z⁻¹, by simp [Pi.inv_apply, hz], fun k ↦ by simp [hx]⟩

private instance relationsNormal : relations.Normal := by
  apply normal_of_le_center
  rintro x ⟨z, _, hx⟩
  exact mem_center_iff.mpr fun y ↦ funext fun k ↦ by
    change y k * x k = x k * y k
    rw [← hx]
    exact mem_center_iff.mp (z k).property _

private abbrev CentralProduct := Triple ⧸ relations
private abbrev toProduct := QuotientGroup.mk' relations

private def coords (p : Fin 3 → Prop) [DecidablePred p] : Cover →* Triple where
  toFun a k := if p k then a else 1
  map_one' := by ext1 k; simp
  map_mul' a b := by ext1 k; by_cases h : p k <;> simp [h]

private def axis (i : Fin 3) : Cover →* CentralProduct :=
  toProduct.comp (coords (· = i))

private lemma axis_injective (i : Fin 3) : Injective (axis i) := by
  apply (axis i).ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro a ha
  obtain ⟨z, hz, h⟩ := (QuotientGroup.eq_one_iff _).mp ha
  have ho (k : Fin 3) (hk : k ≠ i) : z k = 1 := Subtype.ext (by simpa [coords, hk] using h k)
  have hi : z i = 1 := by rwa [Finset.prod_eq_single i (fun k _ hk ↦ ho k hk) (by simp)] at hz
  simpa [coords, hi] using (h i).symm

private lemma axis_center (i j : Fin 3) (c : center Cover) : axis i c = axis j c := by
  apply QuotientGroup.eq_iff_div_mem.mpr
  let u (i k : Fin 3) : center Cover := if k = i then c else 1
  refine ⟨fun k ↦ u i k / u j k, by simp [u, Finset.prod_div_distrib], ?_⟩
  intro k
  change ((u i k / u j k : center Cover) : Cover) =
    (if k = i then (c : Cover) else 1) / (if k = j then (c : Cover) else 1)
  simp [u, apply_ite Subtype.val]

private def proj (i : Fin 3) : CentralProduct →* Simple :=
  QuotientGroup.lift relations (centerQuot.comp (Pi.evalMonoidHom _ i)) (by
    rintro x ⟨z, _, hx⟩
    apply (QuotientGroup.eq_one_iff _).mpr
    change x i ∈ center Cover
    rw [← hx i]
    exact (z i).property)

private lemma proj_surjective (i : Fin 3) : Surjective (proj i) := by
  intro a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (center Cover) a
  exact ⟨toProduct (fun _ ↦ b), rfl⟩

-- If all other projective coordinates vanish, the element lies on the remaining axis.
private lemma mem_axis (x : CentralProduct) (i : Fin 3)
    (hx : ∀ k, k ≠ i → proj k x = 1) : x ∈ (axis i).range := by
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective relations x
  have hm (k : Fin 3) : axis k (v k) ∈ (axis i).range := by
    obtain rfl | h := eq_or_ne k i
    · exact ⟨_, rfl⟩
    · let c : center Cover := ⟨v k, (QuotientGroup.eq_one_iff _).mp (hx k h)⟩
      exact ⟨c, (axis_center k i c).symm⟩
  have hv : v = coords (· = 0) (v 0) * coords (· = 1) (v 1) * coords (· = 2) (v 2) := by
    ext1 k
    fin_cases k <;> simp [coords]
  have hprod : toProduct v = axis 0 (v 0) * axis 1 (v 1) * axis 2 (v 2) := by
    simpa only [axis, MonoidHom.comp_apply, map_mul] using congrArg toProduct hv
  rw [hprod]
  exact mul_mem (mul_mem (hm 0) (hm 1)) (hm 2)

private lemma member_on_axis {H : Subgroup CentralProduct} (hH : Member Simple H)
    (i : Fin 3) (hi : H ≤ (axis i).range) : H = ⊥ := by
  let e := (MonoidHom.ofInjective (axis_injective i)).symm
  let f := e.toMonoidHom.comp (inclusion hi)
  have hf : f = 1 := member_null hH cover_null f
  apply eq_bot_iff.mpr
  intro x hx
  exact congrArg Subtype.val ((e.injective.comp (inclusion_injective hi))
    ((DFunLike.congr_fun hf ⟨x, hx⟩).trans f.map_one.symm))

-- The center has exponent two, so duplicating an element on two axes
-- gives a homomorphism from the simple quotient into their central product.
private def diagonal (j : Fin 3) : Simple →* CentralProduct :=
  QuotientGroup.lift (center Cover) (toProduct.comp (coords (· ≠ j))) (by
    intro a ha
    let c : center Cover := ⟨a, ha⟩
    have hc : c * c = 1 := by
      simpa only [card_center, pow_two] using (pow_card_eq_one' (x := c))
    apply (QuotientGroup.eq_one_iff _).mpr
    refine ⟨fun k ↦ if k ≠ j then c else 1, ?_, fun k ↦ ?_⟩
    · fin_cases j <;> simp [Fin.prod_univ_three, hc]
    · by_cases h : k = j <;> simp [coords, h, c])

private lemma proj_diagonal (i j : Fin 3) (a : Simple) :
    proj i (diagonal j a) = if i = j then 1 else a := by
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (center Cover) a
  change centerQuot (if i ≠ j then b else 1) = _
  by_cases h : i = j <;> simp [h]

private lemma proper_null (H : Subgroup Simple) (hH : H ≠ ⊤) : Null Simple H := by
  intro f
  by_contra hf
  have hs := Finite.surjective_of_injective (H.subtype_injective.comp (injective_of_ne_one hf))
  apply hH
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := hs x
  exact (f y).property

-- Maximality on a pair forces its intersection with the injector to project
-- onto the middle simple group. A trivial projection would put it on a single axis.
private lemma surj_on_pair {V : Subgroup CentralProduct} (hV : IsInjector (testClass Simple) V)
    (j i : Fin 3) (hj : (1 : Fin 3) ≠ j) (hi : ∀ k : Fin 3, k ≠ i → k = j ∨ k = 1) :
    Surjective ((proj 1).domRestrict (V ⊓ (proj j).ker)) := by
  let P := V ⊓ (proj j).ker
  obtain ⟨_, hP, hmax⟩ := hV (proj j).ker (proj j).normal_ker.isSubnormal
  have hn : P ≠ ⊥ := by
    intro hbot
    have hD : (diagonal j).range ≠ ⊥ := by
      intro he
      obtain ⟨a, ha⟩ := exists_ne (1 : Simple)
      have h := proj_diagonal 1 j a
      rw [MonoidHom.range_eq_bot_iff.mp he] at h
      exact ha (by simpa [hj] using h.symm)
    refine hmax (diagonal j).range (show P < _ by rw [hbot]; exact hD.bot_lt) ?_ ?_
    · rintro _ ⟨a, rfl⟩
      exact (proj_diagonal j j a).trans (ite_eq_left rfl)
    · exact member_image (diagonal j).rangeRestrict (diagonal j).rangeRestrict_surjective
        (simple_member Simple)
  let f := (proj 1).domRestrict P
  apply MonoidHom.range_eq_top.mp
  by_contra h
  have hf := member_null hP (proper_null f.range h) f.rangeRestrict
  apply hn (member_on_axis hP i ?_)
  intro x hx
  apply mem_axis x i
  intro k hk
  obtain rfl | rfl := hi k hk
  · exact hx.2
  · exact congrArg Subtype.val (DFunLike.congr_fun hf ⟨x, hx⟩)

open scoped commutatorElement

private lemma no_injector (V : Subgroup CentralProduct) (hV : IsInjector (testClass Simple) V) :
    False := by
  let N := (proj 0).ker ⊓ (proj 2).ker
  have hN := hV N (inferInstance : N.Normal).isSubnormal
  have hb : V ⊓ N = ⊥ := member_on_axis hN.2.1 1 (by
    intro x hx
    apply mem_axis x 1
    intro k hk
    fin_cases k
    · exact hx.2.1
    · exact (hk rfl).elim
    · exact hx.2.2)
  -- The commutator of lifts from the two pairs lies in their common axis.
  apply Group.IsPerfect.not_isMulCommutative Simple
  refine ⟨⟨fun a b ↦ ?_⟩⟩
  obtain ⟨x, rfl⟩ := surj_on_pair hV 0 2 (by decide) (by decide) a
  obtain ⟨y, rfl⟩ := surj_on_pair hV 2 0 (by decide) (by decide) b
  apply commutatorElement_eq_one_iff_mul_comm.mp
  change ⁅proj 1 x, proj 1 y⁆ = 1
  rw [← map_commutatorElement]
  have hx : proj 0 x = 1 := x.property.2
  have hy : proj 2 y = 1 := y.property.2
  have hm : ⁅(x : CentralProduct), (y : CentralProduct)⁆ ∈ V ⊓ N :=
    ⟨V.commutator_le_self (commutator_mem_commutator x.property.1 y.property.1),
      by change proj 0 _ = 1; simp [hx], by change proj 2 _ = 1; simp [hy]⟩
  rw [hb, mem_bot] at hm
  simp [hm]

/--
**A Fitting class with no injectors in a non-soluble group.** There are a Fitting class
$\mathfrak{X}$ of finite groups that contains at least one finite group and a finite non-soluble
group $G$ such that no subgroup of $G$ is an $\mathfrak{X}$-injector of $G$.

This answers Kourovka Problem 12.96 (L. A. Shemetkov) affirmatively: the Kourovka Archive records
that E. Salomon found such a Fitting class and group; the example is presented in Section 7.1 of
Ballester-Bolinches and Ezquerro, Classes of finite groups (2006).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory:
The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem
12.96 (L. A. Shemetkov); resolution: E. Salomon (unpublished), presented in A. Ballester-Bolinches
and L. M. Ezquerro, Classes of finite groups, Springer, 2006, Section 7.1, Kourovka Archive, Problem
12.96: found by E. Salomon.
-/
public theorem fittingClassWithoutInjectors_holds : fittingClassWithoutInjectors := by
  refine ⟨testClass Simple, testClass_fitting Simple,
    ⟨Simple, _, inferInstance, simple_member Simple⟩, CentralProduct, _, inferInstance, ?_,
    no_injector⟩
  intro h
  exact Group.IsPerfect.not_isSolvable Simple (Group.isSolvable_of_surjective (proj_surjective 1))

end MathlibExt.GroupTheory.FittingClassWithoutInjectorKourovka12Problem96Wanted
