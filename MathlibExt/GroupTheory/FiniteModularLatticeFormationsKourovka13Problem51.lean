/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Index
public import Mathlib.Order.ModularLattice
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Bitwise
import Mathlib.GroupTheory.FiniteIndexNormalSubgroup
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Group

/-!
# Finite modular lattices and the lattice of formations (Kourovka Notebook Problem 13.51)

Kourovka Notebook, Problem 13.51 (A. N. Skiba): is every finite modular lattice embeddable in the
lattice of formations of finite groups? The dual of the order-nine nearfield plane gives a
counterexample. Its two perspective triangles violate a Desargues implication for formations.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 13.51 (A. N. Skiba). UnsolvedMath record
UM-00700969 (`KOU-13.51`), dataset ulamai/UnsolvedMath v1.8.0.

A class of finite groups is a predicate on finite groups in `Type`; a formation is closed under
homomorphic images and finite subdirect products (`G / N₁, G / N₂ ∈ 𝔉 → G / (N₁ ∩ N₂) ∈ 𝔉`), and the
empty class counts as a formation, as in the resolving preprint. Meets are intersections and joins
are generated formations. An embedding is an injective map preserving binary meets and joins;
preservation of the least or greatest element is not required. Allowing the empty formation makes
the refuted statement weaker, since the nonempty formations form a sublattice.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.FiniteModularLatticeFormationsKourovka13Problem51Wanted

/-- **Class of finite groups (Kourovka 13.51).** A class of finite groups is a property of finite
groups: for each finite group $G$ it states whether $G$ belongs to the class.

Closure under isomorphism is not part of the definition. -/
abbrev FiniteGroupClass : Type 1 := ∀ (G : Type) [Group G] [Finite G], Prop

/-- **Formation of finite groups (Kourovka 13.51).** A class $\mathfrak F$ of finite groups is a
formation when it is closed under homomorphic images (if $G \in \mathfrak F$ and $\varphi : G
\to H$ is a surjective homomorphism of finite groups, then $H \in \mathfrak F$) and, for every
finite group $G$ and normal subgroups $N_1$ and $N_2$ of $G$, $G/N_1 \in \mathfrak F$ and $G/N_2
\in \mathfrak F$ imply $G/(N_1 \cap N_2) \in \mathfrak F$ (closure under finite subdirect
products).

The empty class is a formation. -/
def IsFormation (𝔉 : FiniteGroupClass) : Prop :=
  (∀ (G H : Type) [Group G] [Finite G] [Group H] [Finite H] (φ : G →* H),
      Function.Surjective φ → 𝔉 G → 𝔉 H) ∧
    ∀ (G : Type) [Group G] [Finite G] (N₁ N₂ : Subgroup G) [N₁.Normal] [N₂.Normal],
      𝔉 (G ⧸ N₁) → 𝔉 (G ⧸ N₂) → 𝔉 (G ⧸ (N₁ ⊓ N₂))

/-- **Intersection of classes of finite groups.** For classes $\mathfrak F_1$ and $\mathfrak F_2$ of
finite groups, their intersection $\mathfrak F_1 \cap \mathfrak F_2$ is the class of finite
groups $G$ with $G \in \mathfrak F_1$ and $G \in \mathfrak F_2$. For formations $\mathfrak F_1$
and $\mathfrak F_2$ it is their meet in the lattice of formations. -/
def classMeet (𝔉₁ 𝔉₂ : FiniteGroupClass) : FiniteGroupClass :=
  fun G _ _ => 𝔉₁ G ∧ 𝔉₂ G

/-- **Join of formations (Kourovka 13.51).** For classes $\mathfrak F_1$ and $\mathfrak F_2$ of
finite groups, their formation join is the class of finite groups $G$ that belong to every
formation containing all groups of $\mathfrak F_1$ and of $\mathfrak F_2$: the intersection of
all formations containing $\mathfrak F_1 \cup \mathfrak F_2$, which is the smallest such
formation. For formations $\mathfrak F_1$ and $\mathfrak F_2$ it is their join in the lattice of
formations. -/
def formationJoin (𝔉₁ 𝔉₂ : FiniteGroupClass) : FiniteGroupClass :=
  fun G _ _ => ∀ 𝔉 : FiniteGroupClass, IsFormation 𝔉 →
    (∀ (H : Type) [Group H] [Finite H], 𝔉₁ H ∨ 𝔉₂ H → 𝔉 H) → 𝔉 G

/-- **Kourovka Problem 13.51 (Skiba): finite modular lattices embed in the lattice of formations.**
For every finite modular lattice $L$ there is an injective map $f$ from $L$ to the formations of
finite groups such that, for all $a, b \in L$, $f(a \wedge b) = f(a) \cap f(b)$ and $f(a \vee
b)$ is the smallest formation containing $f(a) \cup f(b)$.

The map is not required to preserve the least or the greatest element. -/
def finiteModularLatticeEmbedsInFormations : Prop :=
  ∀ (L : Type) [Lattice L] [IsModularLattice L] [Finite L],
    ∃ f : L → FiniteGroupClass, (∀ a, IsFormation (f a)) ∧ Function.Injective f ∧
      (∀ a b, f (a ⊓ b) = classMeet (f a) (f b)) ∧ ∀ a b, f (a ⊔ b) = formationJoin (f a) (f b)

private abbrev F := FreeGroup ℕ
private abbrev N := FiniteIndexNormalSubgroup F

-- A surjection from the countably generated free group lifts surjectively through finite covers.
private theorem lift_mark {B G : Type} [Group B] [Finite B] [Group G] [Finite G]
    (u : B →* G) (hu : Function.Surjective u) (p : F →* G) (hp : Function.Surjective p) :
    ∃ q : F →* B, Function.Surjective q ∧ u.comp q = p := by
  classical
  -- Infinitely many generators have the same image g. Use them to cover the entire fiber over g.
  let s := p ∘ FreeGroup.of
  obtain ⟨g, h⟩ := Finite.exists_infinite_fiber s
  let I := {i : ℕ // s i = g}
  let J := {b : B // u b = g}
  have : Infinite I := h
  obtain ⟨b, hb⟩ := hu g
  have : Nonempty J := ⟨⟨b, hb⟩⟩
  obtain ⟨enum, he⟩ := exists_surjective_nat J
  let j := Infinite.natEmbedding I
  let select : I → J := enum ∘ Function.invFun j
  have hs : Function.Surjective select :=
    he.comp (Function.leftInverse_invFun j.injective).surjective
  let v (i : ℕ) : B := if hi : s i = g then (select ⟨i, hi⟩).val else (hu (s i)).choose
  let q := FreeGroup.lift v
  have heq : u.comp q = p := by
    apply FreeGroup.lift.symm.injective
    funext i
    change u (FreeGroup.lift v (FreeGroup.of i)) = s i
    rw [FreeGroup.lift_apply_of]
    by_cases hi : s i = g
    · simpa [v, hi] using (select ⟨i, hi⟩).property
    · simpa [v, hi] using (hu (s i)).choose_spec
  have hfib (z : B) (hz : u z = g) : z ∈ q.range := by
    obtain ⟨i, hi⟩ := hs ⟨z, hz⟩
    exact ⟨FreeGroup.of i.val, by simpa [q, v, i.property] using congrArg Subtype.val hi⟩
  refine ⟨q, ?_, heq⟩
  intro z
  obtain ⟨x, hx⟩ := hp (u z)
  have huq : u (q x) = u z := (DFunLike.congr_fun heq x).trans hx
  have hzb : u (z * (q x)⁻¹ * b) = g := by simp [huq, hb]
  have hmem := q.range.mul_mem (q.range.mul_mem (hfib _ hzb) (q.range.inv_mem (hfib _ hb)))
    (show q x ∈ q.range from ⟨x, rfl⟩)
  simpa [mul_assoc] using hmem

private abbrev quotientMap {G : Type} [Group G] {A B : Subgroup G} [A.Normal] [B.Normal]
    (h : A ≤ B) := QuotientGroup.map A B (MonoidHom.id G) h

private theorem quotientMap_surj {G : Type} [Group G] {A B : Subgroup G} [A.Normal] [B.Normal]
    (h : A ≤ B) : Function.Surjective (quotientMap h) :=
  QuotientGroup.map_surjective_of_surjective _ _ _ QuotientGroup.mk_surjective _

private theorem quotient_inf_ker {G : Type} [Group G] (A B : Subgroup G) [A.Normal] [B.Normal] :
    (quotientMap (inf_le_left : A ⊓ B ≤ A)).ker ⊓ (quotientMap (inf_le_right : A ⊓ B ≤ B)).ker =
      ⊥ := by
  apply le_antisymm _ bot_le
  rintro x ⟨ha, hb⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (A ⊓ B) x
  exact (QuotientGroup.eq_one_iff x).2
    ⟨(QuotientGroup.eq_one_iff x).1 ha, (QuotientGroup.eq_one_iff x).1 hb⟩

-- A formation gives an upward-closed family of kernels, closed under binary intersections.
private def family (X : FiniteGroupClass) (A : N) : Prop := X (F ⧸ A.toSubgroup)

private theorem family_up {X : FiniteGroupClass} (hx : IsFormation X) {A B : N} (h : A ≤ B) :
    family X A → family X B := hx.1 _ _ (quotientMap h) (quotientMap_surj h)

private theorem of_iso {X : FiniteGroupClass} (hx : IsFormation X)
    {G H : Type} [Group G] [Finite G] [Group H] [Finite H] (e : G ≃* H) : X G → X H :=
  hx.1 _ _ e.toMonoidHom e.surjective

private theorem family_inf {X : FiniteGroupClass} (hx : IsFormation X) {A B : N}
    (ha : family X A) (hb : family X B) : family X (A ⊓ B) := by
  let f := quotientMap (inf_le_left : A.toSubgroup ⊓ B.toSubgroup ≤ A.toSubgroup)
  let g := quotientMap (inf_le_right : A.toSubgroup ⊓ B.toSubgroup ≤ B.toSubgroup)
  have hf := of_iso hx (QuotientGroup.quotientKerEquivOfSurjective f
    (quotientMap_surj _)).symm ha
  have hg := of_iso hx (QuotientGroup.quotientKerEquivOfSurjective g
    (quotientMap_surj _)).symm hb
  have h := hx.2 _ f.ker g.ker hf hg
  have hk : f.ker ⊓ g.ker = ⊥ := quotient_inf_ker _ _
  exact of_iso hx ((QuotientGroup.quotientMulEquivOfEq hk).trans QuotientGroup.quotientBot) h

private abbrev kernel {G : Type} [Group G] [Finite G] (p : F →* G) : N :=
  FiniteIndexNormalSubgroup.ofSubgroup p.ker

-- Conversely, test every marking of a finite group against a family of kernels.
private def allMarks (P : N → Prop) : FiniteGroupClass :=
  fun G _ _ => ∀ (p : F →* G), Function.Surjective p → P (kernel p)

private theorem marks_formation {P : N → Prop}
    (up : ∀ {a b}, a ≤ b → P a → P b) (inter : ∀ {a b}, P a → P b → P (a ⊓ b)) :
    IsFormation (allMarks P) := by
  constructor
  · intro B G _ _ _ _ u hu h p hp
    obtain ⟨q, hq, rfl⟩ := lift_mark u hu p hp
    exact up (fun x hx => show u (q x) = 1 by rw [show q x = 1 from hx, map_one]) (h q hq)
  · intro G _ _ A B _ _ ha hb p hp
    let f := quotientMap (inf_le_left : A ⊓ B ≤ A)
    let g := quotientMap (inf_le_right : A ⊓ B ≤ B)
    have hf := ha (f.comp p) ((quotientMap_surj (inf_le_left : A ⊓ B ≤ A)).comp hp)
    have hg := hb (g.comp p) ((quotientMap_surj (inf_le_right : A ⊓ B ≤ B)).comp hp)
    apply up (b := kernel p) _ (inter hf hg)
    intro x hx
    have h : p x ∈ f.ker ⊓ g.ker := hx
    rwa [show f.ker ⊓ g.ker = ⊥ from quotient_inf_ker _ _] at h

private abbrev joinFamily (X Y : FiniteGroupClass) (k : N) :=
  ∃ a b : N, family X a ∧ family Y b ∧ a ⊓ b ≤ k

private def fullKernel : N := FiniteIndexNormalSubgroup.ofSubgroup ⊤

private theorem family_top {X : FiniteGroupClass} (hx : IsFormation X) {G : Type}
    [Group G] [Finite G] (h : X G) : family X fullKernel := by
  apply hx.1 G _ 1 _ h
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective fullKernel.toSubgroup z
  exact ⟨1, ((QuotientGroup.eq_one_iff x).2 (Subgroup.mem_top _)).symm⟩

-- For nonempty formations the family of the join is generated by pairwise intersections.
private theorem join_family_forward {X Y : FiniteGroupClass} (hx : IsFormation X)
    (hy : IsFormation Y) (ex : family X fullKernel) (ey : family Y fullKernel) {k : N}
    (h : family (formationJoin X Y) k) : joinFamily X Y k := by
  have up {a b : N} (hab : a ≤ b) : joinFamily X Y a → joinFamily X Y b :=
    fun ⟨u, v, hu, hv, huv⟩ => ⟨u, v, hu, hv, huv.trans hab⟩
  have inter {a b : N} : joinFamily X Y a → joinFamily X Y b → joinFamily X Y (a ⊓ b) := by
    rintro ⟨a₁, a₂, h₁, h₂, ha⟩ ⟨b₁, b₂, h₃, h₄, hb⟩
    refine ⟨_, _, family_inf hx h₁ h₃, family_inf hy h₂ h₄, ?_⟩
    exact le_inf ((inf_le_inf inf_le_left inf_le_left).trans ha)
      ((inf_le_inf inf_le_right inf_le_right).trans hb)
  have hmark : allMarks (joinFamily X Y) (F ⧸ k.toSubgroup) := by
    apply h _ (marks_formation @up @inter)
    intro G _ _ hG p hp
    let e := (QuotientGroup.quotientKerEquivOfSurjective p hp).symm
    rcases hG with hG | hG
    · exact ⟨kernel p, fullKernel, of_iso hx e hG, ey, inf_le_left⟩
    · exact ⟨fullKernel, kernel p, ex, of_iso hy e hG, inf_le_right⟩
  have hk : kernel (QuotientGroup.mk' k.toSubgroup) = k :=
    FiniteIndexNormalSubgroup.toSubgroup_injective (QuotientGroup.ker_mk' _)
  exact hk ▸ hmark _ (QuotientGroup.mk'_surjective _)

private theorem join_family_backward {X Y : FiniteGroupClass} {k : N}
    (h : joinFamily X Y k) : family (formationJoin X Y) k := by
  intro Z hz hinc
  obtain ⟨a, b, ha, hb, hab⟩ := h
  exact family_up hz hab (family_inf hz (hinc _ (Or.inl ha)) (hinc _ (Or.inr hb)))

-- Normal subgroups satisfy the central-to-axial Desargues implication.
private theorem normal_desargues (a b c d e f : N) (h : (a ⊔ d) ⊓ (b ⊔ e) ≤ c ⊔ f) :
    (a ⊔ b) ⊓ (d ⊔ e) ≤ ((a ⊔ c) ⊓ (d ⊔ f)) ⊔ ((b ⊔ c) ⊓ (e ⊔ f)) := by
  intro x hx
  obtain ⟨a₁, ha, b₁, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.mp
    (show x ∈ a.toSubgroup ⊔ b.toSubgroup from hx.1)
  obtain ⟨d₁, hd, e₁, he, hde⟩ := Subgroup.mem_sup_of_normal_right.mp
    (show x ∈ d.toSubgroup ⊔ e.toSubgroup from hx.2)
  have ht : d₁⁻¹ * a₁ = e₁ * b₁⁻¹ := by
    rw [← mul_inv_eq_iff_eq_mul, inv_inv, mul_assoc, hab, ← hde, inv_mul_cancel_left]
  have h₁ : d₁⁻¹ * a₁ ∈ a ⊔ d :=
    (a ⊔ d).mul_mem ((a ⊔ d).inv_mem ((le_sup_right : d ≤ a ⊔ d) hd)) ((le_sup_left : a ≤ a ⊔ d) ha)
  have h₂ : e₁ * b₁⁻¹ ∈ b ⊔ e :=
    (b ⊔ e).mul_mem ((le_sup_right : e ≤ b ⊔ e) he) ((b ⊔ e).inv_mem ((le_sup_left : b ≤ b ⊔ e) hb))
  have h₃ := h (show d₁⁻¹ * a₁ ∈ (a ⊔ d) ⊓ (b ⊔ e) from ⟨h₁, ht ▸ h₂⟩)
  rw [sup_comm] at h₃
  obtain ⟨v, hv, u, hu, hvu⟩ := Subgroup.mem_sup_of_normal_right.mp
    (show d₁⁻¹ * a₁ ∈ f.toSubgroup ⊔ c.toSubgroup from h₃)
  have h₄ : a₁ * u⁻¹ = d₁ * v := by
    rw [← eq_mul_inv_iff_mul_eq] at hvu
    rw [hvu]
    group
  have h₅ : u * b₁ = v⁻¹ * e₁ := by
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, hvu, ht, inv_mul_cancel_right]
  have h₆ : a₁ * u⁻¹ ∈ (a ⊔ c) ⊓ (d ⊔ f) :=
    ⟨Subgroup.mul_mem_sup ha (c.inv_mem hu), h₄ ▸ Subgroup.mul_mem_sup hd hv⟩
  have h₇ : u * b₁ ∈ (b ⊔ c) ⊓ (e ⊔ f) := by
    rw [sup_comm b c, sup_comm e f]
    exact ⟨Subgroup.mul_mem_sup hu hb, h₅ ▸ Subgroup.mul_mem_sup (f.inv_mem hv) he⟩
  have H := Subgroup.mul_mem_sup h₆ h₇
  change x ∈ ((a ⊔ c) ⊓ (d ⊔ f)).toSubgroup ⊔ ((b ⊔ c) ⊓ (e ⊔ f)).toSubgroup
  simpa [mul_assoc, hab] using H

-- The order on the lattice of flats is dual to inclusion of the corresponding kernel families.
private structure Representation (L : Type) [Lattice L] where
  mem : L → N → Prop
  up {x k l} : k ≤ l → mem x k → mem x l
  inter {x k l} : mem x k → mem x l → mem x (k ⊓ l)
  order {x y} : x ≤ y ↔ ∀ k, mem y k → mem x k
  sup {x y k} : mem (x ⊔ y) k ↔ mem x k ∧ mem y k
  inf {x y k} : mem (x ⊓ y) k ↔ ∃ u v, mem x u ∧ mem y v ∧ u ⊓ v ≤ k

-- Refine the six kernels simultaneously, then apply Desargues inside the normal subgroup lattice.
private theorem representation_desargues {L : Type} [Lattice L] (R : Representation L)
    (a b c d e f : L) (h : (a ⊔ d) ⊓ (b ⊔ e) ≤ c ⊔ f) :
    (a ⊔ b) ⊓ (d ⊔ e) ≤ ((a ⊔ c) ⊓ (d ⊔ f)) ⊔ ((b ⊔ c) ⊓ (e ⊔ f)) := by
  apply R.order.2
  intro k hk
  obtain ⟨h₁, h₂⟩ := R.sup.1 hk
  obtain ⟨ac, df, hac, hdf, hk₁⟩ := R.inf.1 h₁
  obtain ⟨bc, ef, hbc, hef, hk₂⟩ := R.inf.1 h₂
  let C := ac ⊓ bc
  let F' := df ⊓ ef
  have hc : R.mem c C := R.inter (R.sup.1 hac).2 (R.sup.1 hbc).2
  have hf : R.mem f F' := R.inter (R.sup.1 hdf).2 (R.sup.1 hef).2
  have hcf : R.mem (c ⊔ f) (C ⊔ F') := R.sup.2 ⟨R.up le_sup_left hc, R.up le_sup_right hf⟩
  obtain ⟨ad, be, had, hbe, hcen⟩ := R.inf.1 (R.order.1 h _ hcf)
  let A := ac ⊓ ad
  let B := bc ⊓ be
  let D := df ⊓ ad
  let E := ef ⊓ be
  have ha : R.mem a A := R.inter (R.sup.1 hac).1 (R.sup.1 had).1
  have hb : R.mem b B := R.inter (R.sup.1 hbc).1 (R.sup.1 hbe).1
  have hd : R.mem d D := R.inter (R.sup.1 hdf).1 (R.sup.1 had).2
  have he : R.mem e E := R.inter (R.sup.1 hef).1 (R.sup.1 hbe).2
  refine R.inf.2 ⟨A ⊔ B, D ⊔ E, R.sup.2 ⟨R.up le_sup_left ha, R.up le_sup_right hb⟩,
    R.sup.2 ⟨R.up le_sup_left hd, R.up le_sup_right he⟩, ?_⟩
  apply (normal_desargues A B C D E F' (le_trans _ hcen)).trans
  · apply sup_le
    · exact (inf_le_inf (sup_le inf_le_left inf_le_left) (sup_le inf_le_left inf_le_left)).trans hk₁
    · exact (inf_le_inf (sup_le inf_le_left inf_le_right)
        (sup_le inf_le_left inf_le_right)).trans hk₂
  · exact inf_le_inf (sup_le inf_le_right inf_le_right) (sup_le inf_le_right inf_le_right)

private theorem family_reflect {X Y : FiniteGroupClass} (hx : IsFormation X) (hy : IsFormation Y)
    (hh : ∀ k, family X k → family Y k) (G : Type) [Group G] [Finite G] (hg : X G) : Y G := by
  obtain ⟨v, hv⟩ := exists_surjective_nat G
  let p := FreeGroup.lift v
  let e := QuotientGroup.quotientKerEquivOfSurjective p (FreeGroup.lift_surjective_of_surjective hv)
  exact of_iso hy e (hh (kernel p) (of_iso hx e.symm hg))

-- If two proper flats span the plane, the bottom of its dual must also map to a
-- nonempty formation. Both of their images contain the trivial group.
private noncomputable def representationOfClaim (claim : finiteModularLatticeEmbedsInFormations)
    (L : Type) [Lattice L] [IsModularLattice L] [Finite L] (u v t : L)
    (ht : ∀ x, x ≤ t) (hu : u ≠ t) (hv : v ≠ t) (huv : u ⊔ v = t) : Representation L := by
  classical
  let f := (claim Lᵒᵈ).choose
  obtain ⟨form, inj, meet, join⟩ := (claim Lᵒᵈ).choose_spec
  change (∀ x, IsFormation (f x)) at form
  change Function.Injective f at inj
  change ∀ a b, f (a ⊓ b) = _ at meet
  change ∀ a b, f (a ⊔ b) = _ at join
  let i := OrderDual.toDual (α := L)
  have mono {x y : Lᵒᵈ} (h : x ≤ y) (G : Type) [Group G] [Finite G] (hx : f x G) : f y G := by
    have H := meet x y
    rw [inf_eq_left.mpr h] at H
    exact (show classMeet (f x) (f y) G from H ▸ hx).2
  have proper (x : L) (ne : x ≠ t) : family (f (i x)) fullKernel := by
    by_contra hn
    have eq : f (i t) = f (i x) := by
      funext G _ _
      apply propext
      exact ⟨mono (show i t ≤ i x from ht x) G, fun hg => (hn (family_top (form _) hg)).elim⟩
    exact ne ((inj eq).symm : x = t)
  have htop : family (f (i t)) fullKernel := by
    rw [← huv]
    change family (f (i u ⊓ i v)) fullKernel
    rw [meet]
    exact ⟨proper u hu, proper v hv⟩
  have nonempty (x : L) : family (f (i x)) fullKernel := mono (show i t ≤ i x from ht x) _ htop
  refine {
    mem := fun x k => family (f (i x)) k
    up := fun h => family_up (form _) h
    inter := family_inf (form _)
    order := ?_
    sup := ?_
    inf := ?_ }
  · intro x y
    constructor
    · intro h k hy
      exact mono (show i y ≤ i x from h) _ hy
    · intro h
      have incl := family_reflect (form (i y)) (form (i x)) h
      have hxy : f (i y ⊓ i x) = f (i y) := by
        rw [meet]
        funext G _ _
        exact propext ⟨And.left, fun hg => ⟨hg, incl G hg⟩⟩
      exact (show i y ≤ i x from inf_eq_left.mp (inj hxy))
  · intro x y k
    change family (f (i x ⊓ i y)) k ↔ _
    rw [meet]
    rfl
  · intro x y k
    change family (f (i x ⊔ i y)) k ↔ _
    rw [join]
    exact ⟨join_family_forward (form _) (form _) (nonempty _) (nonempty _), join_family_backward⟩

-- Incidence masks for the projective completion of the Dickson nearfield plane of order nine.
-- Encode a + bi in 𝔽₃[i], i² = -1, by a + 3b. The affine point (x,y) has index 9x+y.
-- Line 9m+b is y = mx+b for square m (including zero), and y = mx³+b otherwise.
-- The vertical lines follow, then the line at infinity. Direction m has point index 81+m,
-- and the vertical direction has index 90. A set is represented by the sum of 2^j over its indices.
private def fieldAdd (x y : ℕ) : ℕ :=
  (x % 3 + y % 3) % 3 + 3 * ((x / 3 + y / 3) % 3)

private def fieldMul (x y : ℕ) : ℕ :=
  let a := x % 3
  let b := x / 3
  let c := y % 3
  let d := y / 3
  (a * c + 2 * b * d) % 3 + 3 * ((a * d + b * c) % 3)

private def ordinate (m b x : ℕ) : ℕ :=
  let square := m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6
  fieldAdd (fieldMul m (if square then x else fieldMul x (fieldMul x x))) b

private def incident (p l : ℕ) : Bool :=
  if l = 90 then 81 ≤ p
  else if p ≥ 81 then p - 81 == l / 9
  else if l ≥ 81 then p / 9 == l - 81
  else p % 9 == ordinate (l / 9) (l % 9) (p / 9)

private def incidenceMask (holds : ℕ → Bool) : ℕ :=
  (List.range 91).foldl (fun mask i => if holds i then mask ||| (1 <<< i) else mask) 0

private def pointsOnLine : Array ℕ := Array.ofFn fun l : Fin 91 => incidenceMask (incident · l)
private def linesThroughPoint : Array ℕ := Array.ofFn fun p : Fin 91 => incidenceMask (incident p)

private structure Flat where
  index : Fin 184
deriving DecidableEq, Fintype

private def flat (n : ℕ) : Flat := ⟨Fin.ofNat 184 n⟩

private def allIndices := 2 ^ 91 - 1

-- In order the flats are the empty flat, the points, the lines, and the whole plane.
private def points (x : Flat) : ℕ :=
  let i := x.index.val
  if i = 0 then 0
  else if i < 92 then 2 ^ (i - 1)
  else if i < 183 then pointsOnLine[i - 92]!
  else allIndices

private def lines (x : Flat) : ℕ :=
  let i := x.index.val
  if i = 0 then allIndices
  else if i < 92 then linesThroughPoint[i - 1]!
  else if i < 183 then 2 ^ (i - 92)
  else 0

private def rank (x : Flat) : ℕ :=
  let i := x.index.val
  if i = 0 then 0 else if i < 92 then 1 else if i < 183 then 2 else 3

-- For incomparable flats a nonempty intersection is a point. Its index is the sole set bit.
private def cap (x y : Flat) : Flat :=
  let a := points x
  let b := points y
  let c := a &&& b
  if c = a then x else if c = b then y else if c = 0 then flat 0 else flat (1 + c.log2)

private def span (x y : Flat) : Flat :=
  let a := lines x
  let b := lines y
  let c := a &&& b
  if c = a then x else if c = b then y else if c = 0 then flat 183 else flat (92 + c.log2)

private def subsetMask (s t : ℕ) : Prop := s &&& t = s

-- Check the meet on point sets, the join on line sets, order duality, and the rank formula.
private def PairLaws (x y : Flat) : Prop :=
    points (cap x y) = points x &&& points y ∧ lines (span x y) = lines x &&& lines y ∧
    (subsetMask (points x) (points y) ↔ subsetMask (lines y) (lines x)) ∧
    (subsetMask (points x) (points y) → x = y ∨ rank x < rank y) ∧
    rank (cap x y) + rank (span x y) = rank x + rank y

private instance decidablePairLaws (x y : Flat) : Decidable (PairLaws x y) := by
  unfold PairLaws subsetMask
  infer_instance

private def checkRow (i : Fin 184) : Bool :=
  (List.finRange 184).all fun j => decide (PairLaws ⟨i⟩ ⟨j⟩)

private theorem checkAll : (List.finRange 184).all checkRow = true := by decide +kernel

private theorem flat_laws (x y : Flat) : PairLaws x y :=
  of_decide_eq_true (List.all_eq_true.1
    (List.all_eq_true.1 checkAll x.index (List.mem_finRange _)) y.index (List.mem_finRange _))

private def bitSet (s : ℕ) : Set ℕ := {i | s.testBit i}
private theorem bits_inter (s t : ℕ) : bitSet (s &&& t) = bitSet s ∩ bitSet t := by
  ext i
  simp [bitSet, Nat.testBit_and]
private theorem bits_subset {s t : ℕ} : subsetMask s t ↔ bitSet s ⊆ bitSet t := by
  change s &&& t = s ↔ _
  rw [← Set.inter_eq_left]
  constructor
  · intro h
    rw [← bits_inter, h]
  · intro h
    rw [← bits_inter] at h
    apply Nat.eq_of_testBit_eq
    intro i
    exact Bool.eq_iff_iff.mpr (Set.ext_iff.1 h i)

private instance flatOrder : PartialOrder Flat where
  le x y := subsetMask (points x) (points y)
  le_refl _ := bits_subset.2 fun _ h => h
  le_trans _ _ _ h₁ h₂ := bits_subset.2 ((bits_subset.1 h₁).trans (bits_subset.1 h₂))
  le_antisymm a b h₁ h₂ := by
    obtain h | h := (flat_laws a b).2.2.2.1 h₁
    · exact h
    obtain h' | h' := (flat_laws b a).2.2.2.1 h₂
    · exact h'.symm
    exact (Nat.lt_asymm h h').elim

private theorem le_points {a b : Flat} : a ≤ b ↔ bitSet (points a) ⊆ bitSet (points b) :=
  bits_subset
private theorem le_lines {a b : Flat} : a ≤ b ↔ bitSet (lines b) ⊆ bitSet (lines a) :=
  (flat_laws a b).2.2.1.trans bits_subset

private instance flatLattice : Lattice Flat where
  inf := cap
  sup := span
  inf_le_left a b := le_points.2 (by
    rw [(flat_laws a b).1, bits_inter]
    exact Set.inter_subset_left)
  inf_le_right a b := le_points.2 (by
    rw [(flat_laws a b).1, bits_inter]
    exact Set.inter_subset_right)
  le_inf a b c hab hac := le_points.2 (by
    rw [(flat_laws b c).1, bits_inter]
    exact Set.subset_inter (le_points.1 hab) (le_points.1 hac))
  le_sup_left a b := le_lines.2 (by
    rw [(flat_laws a b).2.1, bits_inter]
    exact Set.inter_subset_left)
  le_sup_right a b := le_lines.2 (by
    rw [(flat_laws a b).2.1, bits_inter]
    exact Set.inter_subset_right)
  sup_le a b c hac hbc := le_lines.2 (by
    rw [(flat_laws a b).2.1, bits_inter]
    exact Set.subset_inter (le_lines.1 hac) (le_lines.1 hbc))

private instance flatModular : IsModularLattice Flat where
  sup_inf_le_assoc_of_le := by
    intro x y z hxz
    have h : x ⊔ y ⊓ z ≤ (x ⊔ y) ⊓ z :=
      le_inf (sup_le_sup_left inf_le_left _) (sup_le hxz inf_le_right)
    rcases (flat_laws _ _).2.2.2.1 h with heq | hr
    · exact heq.ge
    have dim (a b : Flat) : rank (a ⊓ b) + rank (a ⊔ b) = rank a + rank b :=
      (flat_laws a b).2.2.2.2
    have h₁ := dim x y
    have h₂ := dim y z
    have h₃ := dim (x ⊔ y) z
    have h₄ := dim x (y ⊓ z)
    have hsup : (x ⊔ y) ⊔ z = y ⊔ z := by
      rw [sup_right_comm, sup_eq_right.mpr hxz, sup_comm]
    have hinf : x ⊓ (y ⊓ z) = x ⊓ y := by
      rw [inf_comm y z, ← inf_assoc, inf_eq_left.mpr hxz]
    rw [hsup] at h₃
    rw [hinf] at h₄
    omega

private instance flatDecidableLE : DecidableLE Flat :=
  fun x y => inferInstanceAs (Decidable (points x &&& points y = points x))

private theorem flat_le_top (x : Flat) : x ≤ flat 183 := by
  have check : (List.finRange 184).all (fun i => decide ((⟨i⟩ : Flat) ≤ flat 183)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.1 check x.index (List.mem_finRange _))

/--
**Not every finite modular lattice embeds in the lattice of formations.** There is a finite modular
lattice $L$ that admits no injective map $f$ from $L$ to the formations of finite groups such that,
for all $a, b \in L$, $f(a \wedge b) = f(a) \cap f(b)$ and $f(a \vee b)$ is the smallest formation
containing $f(a) \cup f(b)$. This answers Kourovka Problem 13.51 (Skiba) in the negative.

Jayadevan constructs a modular lattice with 184 elements that admits no such map (a six-variable
Desargues implication holds for formations and fails in the lattice); the Kourovka Notebook (21st
issue) answers 13.51 "No, not every" (AI solution confirmed by A. N. Skiba).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 13.51 (A. N. Skiba); resolution: A.
Jayadevan, A finite modular lattice not embeddable in the lattice of formations of finite groups,
preprint, Zenodo record 22863019 (2026), main theorem: a modular lattice with 184 elements (the dual
of an incidence lattice with 91 points and 91 lines) admits no injective map preserving binary meets
and joins into the lattice of formations; the Kourovka Notebook (21st issue) marks 13.51 solved (AI
solution confirmed by A. N. Skiba), https://zenodo.org/records/22863019.
-/
public theorem finiteModularLatticeEmbedsInFormations_refuted :
    ¬ finiteModularLatticeEmbedsInFormations := by
  intro claim
  let R := representationOfClaim claim Flat (flat 92) (flat 93) (flat 183) flat_le_top
    (by decide) (by decide) (by decide +kernel)
  -- The triangles have point indices (0,1,9) and (70,64,11). Their center has index 10.
  -- The intersections of corresponding sides have indices 90, 72 and 58 and are noncollinear.
  have axial := representation_desargues R (flat 1) (flat 2) (flat 10) (flat 71) (flat 65)
    (flat 12) (by decide +kernel)
  exact (of_decide_eq_false (by decide +kernel)) axial

end MathlibExt.GroupTheory.FiniteModularLatticeFormationsKourovka13Problem51Wanted
