/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.PUnit
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.PGroup

import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.Data.Fintype.Lattice
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.RegularWreathProduct

/-!
# Indecomposability of the formation of finite `p`-groups (Kourovka Notebook Problem 10.72)

We prove that the formation of all finite `p`-groups is indecomposable.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 10.72 (L. A.
Shemetkov). UnsolvedMath record UM-00700687 (`KOU-10.72`), dataset ulamai/UnsolvedMath v1.8.0.

A formation is an isomorphism-closed class of finite groups (in `Type`) that contains the trivial
group and is closed under quotients and subdirect products; the product is Gaschütz's `𝔉 ∘ 𝔊` (`G ∈
𝔉 ∘ 𝔊` iff the `𝔊`-residual of `G` lies in `𝔉`). Non-trivial subformations are read as subformations
of `𝔑_p` different from the formation of trivial groups and from `𝔑_p` itself: `𝔑_p ∘ 𝔊 = 𝔉 ∘ 𝔑_p =
𝔑_p` for all subformations `𝔉, 𝔊` of `𝔑_p`, so admitting the factor `𝔑_p` would make the statement
false.

The proof takes a smallest finite `p`-group omitted by the second formation and uses a
central subgroup of order `p` to construct a regular wreath product omitted by that formation.
For any group omitted by the first formation, a second wreath product has residual surjecting
onto that group. Closure under quotients then rules out the proposed decomposition.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.PGroupFormationIndecomposableKourovka10Problem72Wanted

/-- **Class of finite groups (Kourovka 10.72).** A class of finite groups is given by a
membership predicate: a proposition $X(G)$ for every finite group $G$. It is not required to be
closed under isomorphisms. -/
abbrev GroupClass : Type 1 :=
  ∀ (G : Type) [Group G] [Finite G], Prop

/-- **Formation of finite groups (Kourovka 10.72).** A class $X$ of finite groups is a formation
when it is closed under isomorphisms, contains the trivial group, contains the quotient $G/N$ of
each of its members $G$ by every normal subgroup $N$, and contains $G/(N_1 \cap N_2)$ whenever
$N_1$ and $N_2$ are normal subgroups of a finite group $G$ with $G/N_1$ and $G/N_2$ in $X$. The
last condition is closure under subdirect products. -/
def IsFormation (X : GroupClass) : Prop :=
  (∀ (G H : Type) [Group G] [Finite G] [Group H] [Finite H], (G ≃* H) → X G → X H) ∧ X Unit ∧
  (∀ (G : Type) [Group G] [Finite G] (N : Subgroup G) [N.Normal], X G → X (G ⧸ N)) ∧
  ∀ (G : Type) [Group G] [Finite G] (N₁ N₂ : Subgroup G) [N₁.Normal] [N₂.Normal],
    X (G ⧸ N₁) → X (G ⧸ N₂) → X (G ⧸ (N₁ ⊓ N₂))

/-- **Residual of a finite group with respect to a class (Kourovka 10.72).** For a class $X$ of
finite groups and a finite group $G$, the $X$-residual of $G$ is the intersection of all normal
subgroups $N$ of $G$ with $G/N \in X$. When $X$ is a formation, it is the smallest such $N$. -/
def residual (X : GroupClass) (G : Type) [Group G] [Finite G] : Subgroup G :=
  ⨅ (N : Subgroup G) (_ : ∃ _ : N.Normal, X (G ⧸ N)), N

/-- **Indecomposability of the formation of finite $p$-groups (Kourovka 10.72).** The statement
that for every prime $p$, the class $\mathfrak{N}_p$ of all finite $p$-groups is not the Gaschütz
product $\mathfrak{F} \circ \mathfrak{G}$ of two formations $\mathfrak{F}$ and $\mathfrak{G}$ that
consist of $p$-groups, each contain a nontrivial group and each omit some finite $p$-group. Here a
finite group $G$ lies in $\mathfrak{F} \circ \mathfrak{G}$ when its $\mathfrak{G}$-residual lies
in $\mathfrak{F}$.

Omitting some finite $p$-group is part of the reading of "non-trivial": for all formations
$\mathfrak{F}, \mathfrak{G}$ consisting of $p$-groups,
$\mathfrak{N}_p \circ \mathfrak{G} = \mathfrak{F} \circ \mathfrak{N}_p = \mathfrak{N}_p$. -/
def pGroupFormationIndecomposable : Prop :=
  ∀ p : ℕ, p.Prime → ∀ F H : GroupClass, IsFormation F → IsFormation H →
    (∀ (G : Type) [Group G] [Finite G], F G → IsPGroup p G) →
    (∀ (G : Type) [Group G] [Finite G], H G → IsPGroup p G) →
    (∃ (G : Type) (_ : Group G) (_ : Finite G), Nontrivial G ∧ F G) →
    (∃ (G : Type) (_ : Group G) (_ : Finite G), Nontrivial G ∧ H G) →
    (∃ (G : Type) (_ : Group G) (_ : Finite G), IsPGroup p G ∧ ¬ F G) →
    (∃ (G : Type) (_ : Group G) (_ : Finite G), IsPGroup p G ∧ ¬ H G) →
    ¬ ∀ (G : Type) [Group G] [Finite G], IsPGroup p G ↔ F (residual H G)

private theorem formation_quotient {X : GroupClass} (hX : IsFormation X)
    {A B : Type} [Group A] [Finite A] [Group B] [Finite B]
    (f : A →* B) (hf : Function.Surjective f) (hA : X A) : X B :=
  hX.1 _ _ (QuotientGroup.quotientKerEquivOfSurjective f hf) (hX.2.2.1 _ f.ker hA)

private theorem formation_subdirect {X : GroupClass} (hX : IsFormation X)
    {A B C : Type} [Group A] [Finite A] [Group B] [Finite B] [Group C] [Finite C]
    (f : A →* B) (g : A →* C) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hinj : Function.Injective (f.prod g)) (hB : X B) (hC : X C) : X A := by
  have h₁ := hX.1 _ _ (QuotientGroup.quotientKerEquivOfSurjective f hf).symm hB
  have h₂ := hX.1 _ _ (QuotientGroup.quotientKerEquivOfSurjective g hg).symm hC
  have hker : f.ker ⊓ g.ker = ⊥ := by
    rw [← MonoidHom.ker_prod, MonoidHom.ker_eq_bot_iff]
    exact hinj
  exact hX.1 _ _ ((QuotientGroup.quotientMulEquivOfEq hker).trans QuotientGroup.quotientBot)
    (hX.2.2.2 _ _ _ h₁ h₂)

private theorem residual_le_ker {X : GroupClass} {A B : Type}
    [Group A] [Finite A] [Group B] [Finite B]
    (f : A →* B) (hf : Function.Surjective f) (hX : IsFormation X) (hB : X B) :
    residual X A ≤ f.ker :=
  iInf_le_of_le f.ker
    (iInf_le _ ⟨inferInstance, hX.1 _ _ (QuotientGroup.quotientKerEquivOfSurjective f hf).symm hB⟩)

private theorem residual_normal (X : GroupClass) (A : Type) [Group A] [Finite A] :
    (residual X A).Normal :=
  Subgroup.normal_iInf_normal fun _ => Subgroup.normal_iInf_normal fun h => h.choose

private theorem residual_quotient {X : GroupClass} (hX : IsFormation X)
    (A : Type) [Group A] [Finite A] [hR : (residual X A).Normal] :
    X (A ⧸ residual X A) := by
  classical
  let Good := {N : Subgroup A // ∃ _ : N.Normal, X (A ⧸ N)}
  let : Finite (Subgroup A) := Finite.of_injective SetLike.coe SetLike.coe_injective
  let : Fintype Good := Fintype.ofFinite _
  have htop : X (A ⧸ (⊤ : Subgroup A)) := by
    have : Subsingleton (A ⧸ (⊤ : Subgroup A)) := QuotientGroup.subsingleton_quotient_top
    let : Unique (A ⧸ (⊤ : Subgroup A)) := uniqueOfSubsingleton 1
    exact hX.1 Unit _ MulEquiv.ofUnique hX.2.1
  have hall (s : Finset Good) :
      ∃ _ : (s.inf Subtype.val).Normal, X (A ⧸ s.inf Subtype.val) := by
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.inf_empty]
      exact ⟨inferInstance, htop⟩
    | @insert N s hNs ih =>
      rw [Finset.inf_insert]
      obtain ⟨hN, hXN⟩ := N.property
      obtain ⟨hs, hXs⟩ := ih
      exact ⟨inferInstance, hX.2.2.2 _ _ _ hXN hXs⟩
  have heq : (Finset.univ : Finset Good).inf Subtype.val = residual X A := by
    rw [Finset.inf_univ_eq_iInf]
    apply le_antisymm
    · exact le_iInf fun N => le_iInf fun h => iInf_le _ (⟨N, h⟩ : Good)
    · exact le_iInf fun N => iInf_le_of_le N.val (iInf_le _ N.property)
  obtain ⟨_, h⟩ := hall Finset.univ
  exact hX.1 _ _ (QuotientGroup.quotientMulEquivOfEq heq) h

-- A transversal gives the embedding of an extension into the regular wreath product.
private theorem exists_wreath_embedding {B : Type} [Group B]
    (K : Subgroup B) [K.Normal] :
    ∃ e : B →* K ≀ᵣ (B ⧸ K), Function.Injective e ∧
      ∀ b, (e b).right = QuotientGroup.mk' K b := by
  let π := QuotientGroup.mk' K
  obtain ⟨s, hs⟩ := (QuotientGroup.mk'_surjective K).hasRightInverse
  have hsπ (q) : π (s q) = q := hs q
  let coord (b : B) (q : B ⧸ K) : K :=
    ⟨(s q)⁻¹ * b * s ((π b)⁻¹ * q), by
      apply (QuotientGroup.eq_one_iff _).mp
      change π _ = 1
      simp [hsπ, mul_assoc]⟩
  let e : B →* K ≀ᵣ (B ⧸ K) :=
    { toFun := fun b => ⟨coord b, π b⟩
      map_one' := by
        apply RegularWreathProduct.ext
        · funext q
          apply Subtype.ext
          change (s q)⁻¹ * (1 : B) * s ((π 1)⁻¹ * q) = 1
          simp
        · exact map_one π
      map_mul' := by
        intro a b
        apply RegularWreathProduct.ext
        · funext q
          apply Subtype.ext
          change (s q)⁻¹ * (a * b) * s ((π (a * b))⁻¹ * q) =
            ((s q)⁻¹ * a * s ((π a)⁻¹ * q)) *
              ((s ((π a)⁻¹ * q))⁻¹ * b * s ((π b)⁻¹ * ((π a)⁻¹ * q)))
          rw [map_mul, mul_inv_rev, mul_assoc ((π b)⁻¹)]
          group
        · exact map_mul π a b }
  refine ⟨e, ?_, fun _ => rfl⟩
  intro a b hab
  have hr : π a = π b := congrArg RegularWreathProduct.right hab
  have hl (q : B ⧸ K) : (coord a q : B) = (coord b q : B) :=
    congrArg (fun w : K ≀ᵣ (B ⧸ K) => (w.left q : B)) hab
  have h := hl 1
  change (s 1)⁻¹ * a * s ((π a)⁻¹ * 1) = (s 1)⁻¹ * b * s ((π b)⁻¹ * 1) at h
  rw [hr] at h
  exact mul_left_cancel (mul_right_cancel h)

-- With abelian base, the pullback has two surjections onto the wreath product. The
-- second multiplies the base coordinate by the embedding cocycle.
private theorem formation_of_wreath_embedding {X : GroupClass} (hX : IsFormation X)
    {K Q B : Type} [Group K] [Finite K] [IsMulCommutative K] [Group Q] [Finite Q]
    [Group B] [Finite B] (π : B →* Q) (hπ : Function.Surjective π)
    (e : B →* K ≀ᵣ Q) (he : Function.Injective e) (heπ : ∀ b, (e b).right = π b)
    (hW : X (K ≀ᵣ Q)) : X B := by
  let W := K ≀ᵣ Q
  let l := MonoidHom.fst W B
  let r := MonoidHom.snd W B
  let S := ((RegularWreathProduct.rightHom : W →* Q).comp l).eqLocus (π.comp r)
  let f : S →* K ≀ᵣ Q := l.domRestrict S
  let b : S →* B := r.domRestrict S
  have hfπ (x : S) : (f x).right = π (b x) := x.property
  let g : S →* K ≀ᵣ Q :=
    { toFun := fun x => ⟨(f x).left * (e (b x)).left, (f x).right⟩
      map_one' := by apply RegularWreathProduct.ext <;> simp
      map_mul' := by
        intro x y
        apply RegularWreathProduct.ext
        · funext q
          change ((f (x * y)).left q * (e (b (x * y))).left q) =
            ((f x).left q * (e (b x)).left q) *
              ((f y).left ((f x).right⁻¹ * q) * (e (b y)).left ((f x).right⁻¹ * q))
          simp only [map_mul, RegularWreathProduct.mul_left, Pi.mul_apply, heπ, ← hfπ]
          simp only [mul_assoc]
          congr 1
          rw [← mul_assoc, mul_comm' ((f y).left _), mul_assoc]
        · change (f (x * y)).right = (f x).right * (f y).right
          rw [map_mul]
          rfl }
  have hf : Function.Surjective f := by
    intro w
    obtain ⟨a, ha⟩ := hπ w.right
    exact ⟨⟨(w, a), ha.symm⟩, rfl⟩
  have hg : Function.Surjective g := by
    intro w
    obtain ⟨a, ha⟩ := hπ w.right
    refine ⟨⟨(⟨w.left * (e a).left⁻¹, w.right⟩, a), ha.symm⟩, ?_⟩
    apply RegularWreathProduct.ext
    · change w.left * (e a).left⁻¹ * (e a).left = w.left
      simp
    · rfl
  have hinj : Function.Injective (f.prod g) := by
    intro x y h
    have h₁ : f x = f y := congrArg (fun z : W × W => z.1) h
    have h₂ : g x = g y := congrArg (fun z : W × W => z.2) h
    have hb : b x = b y := by
      apply he
      apply RegularWreathProduct.ext
      · have hl := congrArg RegularWreathProduct.left h₂
        change (f x).left * (e (b x)).left = (f y).left * (e (b y)).left at hl
        rw [h₁] at hl
        exact mul_left_cancel hl
      · rw [heπ, heπ, ← hfπ, ← hfπ, h₁]
    exact Subtype.ext (Prod.ext h₁ hb)
  have hb : Function.Surjective b := by
    intro a
    exact ⟨⟨(⟨1, π a⟩, a), rfl⟩, rfl⟩
  exact formation_quotient hX b hb (formation_subdirect hX f g hf hg hinj hW hW)

-- A smallest omitted group has a central subgroup of order p and a quotient in the formation.
private theorem exists_omitted_wreath {X : GroupClass} (hX : IsFormation X)
    {p : ℕ} [Fact p.Prime]
    (hNot : ∃ (G : Type) (_ : Group G) (_ : Finite G), IsPGroup p G ∧ ¬ X G) :
    ∃ (K Q : Type) (_ : Group K) (_ : Finite K) (_ : Group Q) (_ : Finite Q),
      Nat.card K = p ∧ IsPGroup p Q ∧ X Q ∧ ¬ X (K ≀ᵣ Q) := by
  classical
  let omitted (n : ℕ) :=
    ∃ (G : Type) (_ : Group G) (_ : Finite G), Nat.card G = n ∧ IsPGroup p G ∧ ¬ X G
  have hex : ∃ n, omitted n := by
    obtain ⟨G, hgroup, hfinite, hpG, hG⟩ := hNot
    exact ⟨Nat.card G, G, hgroup, hfinite, rfl, hpG, hG⟩
  obtain ⟨B, _, _, hcard, hpB, hB⟩ := Nat.find_spec hex
  have : Nontrivial B := by
    rcases subsingleton_or_nontrivial B with h | h
    · let : Unique B := uniqueOfSubsingleton 1
      exact (hB (hX.1 Unit B MulEquiv.ofUnique hX.2.1)).elim
    · exact h
  have : Nontrivial (Subgroup.center B) := hpB.center_nontrivial
  have hpCenter : IsPGroup p (Subgroup.center B) := hpB.to_subgroup _
  have hdvd : p ∣ Nat.card (Subgroup.center B) :=
    hpCenter.card_eq_or_dvd.resolve_left Finite.one_lt_card.ne'
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p hdvd
  let K := Subgroup.zpowers (a : B)
  have hK : Nat.card K = p := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, ha]
  have : K.Normal := Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr a.property)
  have : IsCyclic K := isCyclic_of_prime_card hK
  have : IsMulCommutative K := IsCyclic.isMulCommutative
  have hlt : Nat.card (B ⧸ K) < Nat.find hex := by
    rw [← hcard, ← K.card_mul_index, K.index_eq_card, hK]
    exact lt_mul_of_one_lt_left Nat.card_pos (Fact.out : p.Prime).one_lt
  have hQ : X (B ⧸ K) := by
    by_contra h
    exact Nat.find_min hex hlt ⟨B ⧸ K, inferInstance, inferInstance, rfl, hpB.to_quotient K, h⟩
  refine ⟨K, B ⧸ K, inferInstance, inferInstance, inferInstance, inferInstance, hK,
    hpB.to_quotient K, hQ, fun hW => hB ?_⟩
  obtain ⟨e, he, heπ⟩ := exists_wreath_embedding K
  exact formation_of_wreath_embedding hX (QuotientGroup.mk' K)
    (QuotientGroup.mk'_surjective K) e he heπ hW

private theorem isPGroup_wreath {p : ℕ} [Fact p.Prime] {A Q : Type}
    [Group A] [Finite A] [Group Q] [Finite Q] (hA : IsPGroup p A) (hQ : IsPGroup p Q) :
    IsPGroup p (A ≀ᵣ Q) := by
  obtain ⟨a, ha⟩ := hA.exists_card_eq
  obtain ⟨q, hq⟩ := hQ.exists_card_eq
  apply IsPGroup.of_card (n := a * Nat.card Q + q)
  rw [RegularWreathProduct.card, ha, ← pow_mul, pow_add, hq]

-- A proper image of the residual under base evaluation would produce the omitted wreath
-- product as a quotient of the residual quotient.
private theorem residual_wreath_surjects {X : GroupClass} (hX : IsFormation X)
    {p : ℕ} [Fact p.Prime] {A K Q : Type}
    [Group A] [Finite A] [Group K] [Finite K] [Group Q] [Finite Q]
    (hA : IsPGroup p A) (hK : Nat.card K = p) (hQ : X Q) (hW : ¬ X (K ≀ᵣ Q)) :
    ∃ ev : residual X (A ≀ᵣ Q) →* A, Function.Surjective ev := by
  classical
  let R := residual X (A ≀ᵣ Q)
  have : R.Normal := residual_normal X _
  let π : A ≀ᵣ Q →* Q := RegularWreathProduct.rightHom
  have hR : R ≤ π.ker := residual_le_ker π (fun q => ⟨RegularWreathProduct.inl q, rfl⟩) hX hQ
  have hright {w : A ≀ᵣ Q} (hw : w ∈ R) : w.right = 1 := hR hw
  let ev : R →* A :=
    { toFun := fun w => w.val.left 1
      map_one' := rfl
      map_mul' := by
        intro x y
        change (x.val * y.val).left 1 = x.val.left 1 * y.val.left 1
        simp [hright x.property] }
  refine ⟨ev, MonoidHom.range_eq_top.mp ?_⟩
  by_contra hn
  obtain ⟨M, hM, hle⟩ := (eq_top_or_exists_le_coatom ev.range).resolve_left hn
  have : Group.IsNilpotent A := hA.isNilpotent
  have : M.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom M Group.normalizerCondition_of_isNilpotent hM
  have hMcard : Nat.card (A ⧸ M) = p := M.index_eq_card ▸ hA.isCoatom_iff_index_eq_prime.mp hM
  let e : A ⧸ M ≃* K := mulEquivOfPrimeCardEq hMcard hK
  let u : A →* K := e.toMonoidHom.comp (QuotientGroup.mk' M)
  have hu : Function.Surjective u := e.surjective.comp (QuotientGroup.mk'_surjective M)
  let f : A ≀ᵣ Q →* K ≀ᵣ Q :=
    { toFun := fun w => ⟨u ∘ w.left, w.right⟩
      map_one' := by
        apply RegularWreathProduct.ext
        · funext q
          simp
        · rfl
      map_mul' := by
        intro x y
        apply RegularWreathProduct.ext
        · funext q
          simp [Function.comp_def]
        · rfl }
  have hf : Function.Surjective f := by
    intro w
    choose pre hpre using fun q => hu (w.left q)
    exact ⟨⟨pre, w.right⟩, RegularWreathProduct.ext (funext hpre) rfl⟩
  have hRf : R ≤ f.ker := by
    intro w hw
    apply MonoidHom.mem_ker.mpr
    apply RegularWreathProduct.ext
    · funext q
      let t : A ≀ᵣ Q := RegularWreathProduct.inl q⁻¹
      have ht : t * w * t⁻¹ ∈ R := Subgroup.Normal.conj_mem _ hw t
      have hcoord : ev ⟨t * w * t⁻¹, ht⟩ = w.left q := by
        change (t * w * t⁻¹).left 1 = w.left q
        simp [t]
      have hm : w.left q ∈ M := hle ⟨_, hcoord⟩
      change e ((QuotientGroup.mk' M) (w.left q)) = 1
      rw [show QuotientGroup.mk' M (w.left q) = 1 from
        (QuotientGroup.eq_one_iff _).mpr hm, map_one]
    · exact hright hw
  exact hW (formation_quotient hX (QuotientGroup.lift R f hRf)
    (QuotientGroup.lift_surjective_of_surjective R f hf hRf) (residual_quotient hX _))

/--
**The formation of finite $p$-groups is indecomposable.** For every prime $p$, the class
$\mathfrak{N}_p$ of all finite $p$-groups is not the Gaschütz product $\mathfrak{F} \circ
\mathfrak{G}$ of two formations $\mathfrak{F}$ and $\mathfrak{G}$ that consist of $p$-groups, each
contain a nontrivial group and each omit some finite $p$-group. Here a finite group $G$ lies in
$\mathfrak{F} \circ \mathfrak{G}$ when its $\mathfrak{G}$-residual lies in $\mathfrak{F}$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory:
The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem
10.72 (L. A. Shemetkov); resolution: A. N. Skiba and L. A. Shemetkov, Dokl. Akad. Nauk BSSR 33
(1989), 581-582 (Russian), Kourovka Archive, Problem 10.72 ("This has been proved").
-/
theorem pGroupFormationIndecomposable_holds : pGroupFormationIndecomposable := by
  intro p hp F H hF hH _ _ _ _ hFproper hHproper hprod
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, _, _, hpA, hA⟩ := hFproper
  obtain ⟨K, Q, _, _, _, _, hK, hpQ, hQ, hW⟩ := exists_omitted_wreath hH hHproper
  obtain ⟨ev, hev⟩ := residual_wreath_surjects hH hpA hK hQ hW
  exact hA (formation_quotient hF ev hev ((hprod (A ≀ᵣ Q)).mp (isPGroup_wreath hpA hpQ)))

end MathlibExt.GroupTheory.PGroupFormationIndecomposableKourovka10Problem72Wanted
