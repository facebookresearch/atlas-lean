/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Rank
import Mathlib.Algebra.Module.ZMod
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Counting subgroups of finite abelian groups

Character duality gives a bijection from subgroups of index `k` to subgroups of order `k`.
-/

namespace MetaMathlibExt

/-- **Counting subgroups by order and by index.** In a finite abelian group $G$, for every
natural number $k$ the number of subgroups of order $k$ equals the number of subgroups of
index $k$.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Lemma 3 (`integers-2026-A97-lem-3`). -/
public theorem ncard_addSubgroup_card_eq_ncard_index_eq (G : Type*) [AddCommGroup G]
    [Finite G] (k : ℕ) :
    {H : AddSubgroup G | Nat.card H = k}.ncard = {H : AddSubgroup G | H.index = k}.ncard := by
  let A := Multiplicative G
  let K := AlgebraicClosure ℚ
  obtain ⟨e⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity A K
  let annihilator := CommGroup.subgroupOrderIsoSubgroupMonoidHom A K
  let toMul := (AddSubgroup.toSubgroup (A := G)).toEquiv
  -- Identify the character group with the original group to count both families inside `G`.
  let correspondence := toMul.trans <| annihilator.toEquiv.trans <| OrderDual.ofDual.trans <|
    e.mapSubgroup.toEquiv.trans toMul.symm
  apply Eq.symm
  refine Set.ncard_congr' (correspondence.subtypeEquiv fun H ↦ ?_)
  change H.index = k ↔ Nat.card (e.mapSubgroup (annihilator H.toSubgroup).ofDual) = k
  rw [Subgroup.card_mapSubgroup, CommGroup.card_subgroupOrderIsoSubgroupMonoidHom]
  rfl

private abbrev twoTorsion (A : Type*) [AddCommGroup A] : AddSubgroup A :=
  (nsmulAddMonoidHom (α := A) 2).ker

private lemma rank_eq_rank_quotient_doubles (A : Type*) [AddCommGroup A] [Finite A]
    (hA : ∃ n : ℕ, ∀ x : A, (2 ^ n : ℕ) • x = 0) :
    AddGroup.rank A = AddGroup.rank (A ⧸ (nsmulAddMonoidHom (α := A) 2).range) := by
  classical
  let D := (nsmulAddMonoidHom (α := A) 2).range
  let q := QuotientAddGroup.mk' D
  have hq := QuotientAddGroup.mk'_surjective D
  refine le_antisymm ?_ (AddGroup.rank_le_of_surjective q hq)
  let lift := Function.surjInv hq
  have hlift : Function.RightInverse lift q := Function.rightInverse_surjInv hq
  obtain ⟨s, hs, hgen⟩ := AddGroup.rank_spec (A ⧸ D)
  let t := s.image lift
  let K := AddSubgroup.closure (t : Set A)
  have hmap : K.map q = ⊤ := by
    have hid : (fun x => q (lift x)) = id := funext hlift
    rw [AddMonoidHom.map_closure, Finset.coe_image, Set.image_image, hid, Set.image_id, hgen]
  have hstep (x : A) : ∃ y ∈ K, ∃ z : A, x = y + 2 • z := by
    have hx : q x ∈ K.map q := by rw [hmap]; exact AddSubgroup.mem_top _
    obtain ⟨y, hy, heq⟩ := hx
    have hd : x - y ∈ D := by
      rw [← QuotientAddGroup.ker_mk' D, AddMonoidHom.mem_ker, map_sub, heq, sub_self]
    obtain ⟨z, hz⟩ := hd
    exact ⟨y, hy, z, by rw [show 2 • z = x - y from hz, add_comm y, sub_add_cancel]⟩
  -- A subgroup generating modulo doubles generates the whole bounded 2-group.
  have descend (n : ℕ) (hn : ∀ x : A, (2 ^ n : ℕ) • x ∈ K) : ∀ x : A, x ∈ K := by
    induction n with
    | zero => simpa using hn
    | succ n ih =>
      apply ih
      intro x
      obtain ⟨y, hy, z, hz⟩ := hstep x
      rw [hz, smul_add, ← mul_smul, ← pow_succ]
      exact K.add_mem (K.nsmul_mem hy _) (hn z)
  obtain ⟨n, hn⟩ := hA
  have htop : K = ⊤ := (AddSubgroup.eq_top_iff' K).2 <| descend n fun x => hn x ▸ K.zero_mem
  exact (AddGroup.rank_le htop).trans (Finset.card_image_le.trans_eq hs)

private lemma rank_eq_finrank_zmod_two (V : Type*) [AddCommGroup V] [Finite V]
    [Module (ZMod 2) V] : AddGroup.rank V = Module.finrank (ZMod 2) V := by
  classical
  have hspan (s : Set V) : (Submodule.span (ZMod 2) s).toAddSubgroup = AddSubgroup.closure s := by
    apply le_antisymm
    · exact Submodule.span_le (p := AddSubgroup.toZModSubmodule 2 (AddSubgroup.closure s)) |>.mpr
        AddSubgroup.subset_closure
    · exact (AddSubgroup.closure_le (K := (Submodule.span (ZMod 2) s).toAddSubgroup)).mpr
        Submodule.subset_span
  refine le_antisymm ?_ ?_
  · let b := Module.finBasis (ZMod 2) V
    have hgen : AddSubgroup.closure (Finset.univ.image b : Set V) = ⊤ := by
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, ← hspan, b.span_eq,
        Submodule.top_toAddSubgroup]
    exact (AddGroup.rank_le hgen).trans
      (by simpa using Finset.card_image_le (s := Finset.univ) (f := b))
  · obtain ⟨s, hs, hgen⟩ := AddGroup.rank_spec V
    have htop : Submodule.span (ZMod 2) (s : Set V) = ⊤ :=
      (AddSubgroup.toZModSubmodule 2).symm.injective (by simpa [AddSubgroup.toZModSubmodule_symm,
        hspan] using hgen)
    have hle := finrank_span_finset_le_card (R := ZMod 2) s
    rw [Set.finrank, htop, finrank_top, hs] at hle
    exact hle

private lemma pow_rank_eq_card_twoTorsion (A : Type*) [AddCommGroup A] [Finite A]
    (hA : ∃ n : ℕ, ∀ x : A, (2 ^ n : ℕ) • x = 0) :
    2 ^ AddGroup.rank A = Nat.card (twoTorsion A) := by
  let d : A →+ A := nsmulAddMonoidHom 2
  let Q := A ⧸ d.range
  let : Module (ZMod 2) Q := QuotientAddGroup.zmodModule (fun x => ⟨x, rfl⟩)
  let b := Module.finBasis (ZMod 2) Q
  have hQ : Nat.card Q = 2 ^ Module.finrank (ZMod 2) Q := by
    rw [Nat.card_congr b.equivFun.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  rw [rank_eq_rank_quotient_doubles A hA, rank_eq_finrank_zmod_two Q, ← hQ]
  have hrange : Nat.card d.range ≠ 0 := Nat.card_pos.ne'
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hrange)
  rw [mul_comm _ (Nat.card (twoTorsion A)), AddSubgroup.card_ker_mul_card_range]
  exact AddSubgroup.card_mul_index (H := d.range)

private lemma ncard_index_two_eq_card_twoTorsion_sub_one (A : Type*) [AddCommGroup A] [Finite A] :
    {H : AddSubgroup A | H.index = 2}.ncard = Nat.card (twoTorsion A) - 1 := by
  classical
  rw [← ncard_addSubgroup_card_eq_ncard_index_eq]
  let S : Set (twoTorsion A) := {0}ᶜ
  have hne (x : S) : x.1.1 ≠ 0 :=
    fun h => x.2 (Set.mem_singleton_iff.mpr (Subtype.ext h))
  have hcard (x : S) : Nat.card (AddSubgroup.zmultiples x.1.1) = 2 := by
    rw [Nat.card_zmultiples]
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact addOrderOf_eq_prime x.1.2 (hne x)
  let f : S → {H : AddSubgroup A | Nat.card H = 2} :=
    fun x => ⟨AddSubgroup.zmultiples x.1.1, hcard x⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      have he : AddSubgroup.zmultiples x.1.1 = AddSubgroup.zmultiples y.1.1 :=
        congrArg Subtype.val h
      let H := AddSubgroup.zmultiples x.1.1
      let u : H := ⟨x.1.1, AddSubgroup.mem_zmultiples _⟩
      let v : H := ⟨y.1.1, by dsimp [H]; rw [he]; exact AddSubgroup.mem_zmultiples _⟩
      obtain ⟨a, _, hu⟩ := (Nat.card_eq_two_iff' (0 : H)).mp (hcard x)
      have huv : u = v :=
        (hu u (fun h => hne x (congrArg (fun z : H => (z : A)) h))).trans
          (hu v (fun h => hne y (congrArg (fun z : H => (z : A)) h))).symm
      exact Subtype.ext (Subtype.ext (congrArg (fun z : H => (z : A)) huv))
    · intro H
      have hH : Nat.card H.1 = 2 := H.2
      obtain ⟨x, hx, _⟩ := (Nat.card_eq_two_iff' (0 : H.1)).mp hH
      have hx0 : x.1 ≠ 0 := fun h => hx (Subtype.ext h)
      have hx2 := card_nsmul_eq_zero' (x := x)
      rw [hH] at hx2
      let u : twoTorsion A := ⟨x.1, congrArg Subtype.val hx2⟩
      let y : S := ⟨u, fun hu => hx0 (congrArg (fun z : twoTorsion A => (z : A))
        (Set.mem_singleton_iff.mp hu))⟩
      refine ⟨y, Subtype.ext (AddSubgroup.eq_of_le_of_card_ge ?_ ?_)⟩
      · exact AddSubgroup.zmultiples_le.mpr x.2
      · change Nat.card H.1 ≤ Nat.card (AddSubgroup.zmultiples y.1.1)
        rw [hH, hcard y]
  calc
    _ = S.ncard := Set.ncard_congr' (Equiv.ofBijective f hf).symm
    _ = Nat.card (twoTorsion A) - 1 := by simp [S]

private lemma card_twoTorsion_pi {ι : Type*} [Fintype ι] (A : ι → Type*)
    [∀ i, AddCommGroup (A i)] :
    Nat.card (twoTorsion (∀ i, A i)) = ∏ i, Nat.card (twoTorsion (A i)) := by
  let e : twoTorsion (∀ i, A i) ≃ ∀ i, twoTorsion (A i) :=
    { toFun := fun x i => ⟨x.1 i, congrFun x.2 i⟩
      invFun := fun x => ⟨fun i => (x i).1, funext fun i => (x i).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_pi]

private lemma card_twoTorsion_prod (A B : Type*) [AddCommGroup A] [AddCommGroup B] :
    Nat.card (twoTorsion (A × B)) = Nat.card (twoTorsion A) * Nat.card (twoTorsion B) := by
  let e : twoTorsion (A × B) ≃ twoTorsion A × twoTorsion B :=
    { toFun := fun x => (⟨x.1.1, congrArg Prod.fst x.2⟩, ⟨x.1.2, congrArg Prod.snd x.2⟩)
      invFun := fun x => ⟨(x.1.1, x.2.1), Prod.ext x.1.2 x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_prod]

private lemma card_twoTorsion_zmod (m : ℕ) [NeZero m] (hm : 2 ∣ m) :
    Nat.card (twoTorsion (ZMod m)) = 2 := by
  rw [IsAddCyclic.card_nsmulAddMonoidHom_ker, Nat.card_zmod, Nat.gcd_eq_right hm]

private lemma twoTorsion_zmod_le_doubles (m : ℕ) [NeZero m] (hm : 4 ∣ m) :
    twoTorsion (ZMod m) ≤ (nsmulAddMonoidHom (α := ZMod m) 2).range := by
  have h₂ : 2 ∣ m := (by decide : 2 ∣ 4).trans hm
  rw [IsAddCyclic.addSubgroup_le_iff_card_dvd, card_twoTorsion_zmod m h₂,
    IsAddCyclic.card_nsmulAddMonoidHom_range, Nat.card_zmod, Nat.gcd_eq_right h₂]
  obtain ⟨k, rfl⟩ := hm
  exact ⟨k, by omega⟩

private lemma index_two_rank_of_twoTorsion {G : Type*} [AddCommGroup G] [Finite G]
    (hG : ∃ n : ℕ, ∀ x : G, (2 ^ n : ℕ) • x = 0) {r : ℕ} (hr : 1 ≤ r)
    (hc : Nat.card (twoTorsion G) = 2 ^ r) (H : AddSubgroup G) (hH : H.index = 2) :
    (twoTorsion G ≤ H → AddGroup.rank H = r) ∧
      (¬ twoTorsion G ≤ H → AddGroup.rank H = r - 1) := by
  let T := twoTorsion G
  have hcard : Nat.card (twoTorsion H) = Nat.card (H ⊓ T : AddSubgroup G) :=
    Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, congrArg Subtype.val x.2⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext x.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hpow : 2 ^ AddGroup.rank H = Nat.card (H ⊓ T : AddSubgroup G) := by
    rw [← hcard]
    obtain ⟨n, hn⟩ := hG
    exact pow_rank_eq_card_twoTorsion H ⟨n, fun x => Subtype.ext (hn x)⟩
  have hrel := H.relIndex_mul_card T
  rw [← hpow, hc] at hrel
  constructor <;> intro hT <;> apply Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
  · have hindex : H.relIndex T = 1 := AddSubgroup.relIndex_eq_one.mpr hT
    rwa [hindex, one_mul] at hrel
  · have hdvd : H.relIndex T ∣ 2 := hH ▸ H.relIndex_dvd_index_of_normal T
    have hindex : H.relIndex T = 2 :=
      ((Nat.dvd_prime Nat.prime_two).mp hdvd).resolve_left (mt AddSubgroup.relIndex_eq_one.mp hT)
    have hr' : 2 * 2 ^ (r - 1) = 2 ^ r := by rw [← pow_succ', Nat.sub_add_cancel hr]
    rw [hindex] at hrel
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < (2 : ℕ)) (hrel.trans hr'.symm)

/-- **Ranks of the index-two subgroups of a finite abelian 2-group.** Let $r_1, r_2$ be natural
numbers with $r = r_1 + r_2 \ge 1$, let $\alpha_1, \dots, \alpha_{r_1} \ge 2$, and let
$G = \mathbb{Z}_{2^{\alpha_1}} \oplus \dots \oplus \mathbb{Z}_{2^{\alpha_{r_1}}} \oplus
\mathbb{Z}_2^{r_2}$. Then exactly $2^{r_1} - 1$ subgroups of $G$ of index $2$ have rank $r$,
and exactly $2^r - 2^{r_1}$ subgroups of $G$ of index $2$ have rank $r - 1$, where the rank
of a group is the minimal number of its generators.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Lemma 4 (`integers-2026-A97-lem-4`). -/
public theorem ncard_index_two_addSubgroup_rank (r₁ r₂ : ℕ) (hr : 1 ≤ r₁ + r₂)
    (α : Fin r₁ → ℕ) (hα : ∀ i, 2 ≤ α i) :
    {H : AddSubgroup (((i : Fin r₁) → ZMod (2 ^ α i)) × (Fin r₂ → ZMod 2)) |
        H.index = 2 ∧ AddGroup.rank H = r₁ + r₂}.ncard = 2 ^ r₁ - 1 ∧
      {H : AddSubgroup (((i : Fin r₁) → ZMod (2 ^ α i)) × (Fin r₂ → ZMod 2)) |
        H.index = 2 ∧ AddGroup.rank H = r₁ + r₂ - 1}.ncard = 2 ^ (r₁ + r₂) - 2 ^ r₁ := by
  classical
  let A := (i : Fin r₁) → ZMod (2 ^ α i)
  let B := Fin r₂ → ZMod 2
  let G := A × B
  let T := twoTorsion G
  let r := r₁ + r₂
  have hFour (i : Fin r₁) : 4 ∣ 2 ^ α i := pow_dvd_pow 2 (hα i)
  have hTwo (i : Fin r₁) : 2 ∣ 2 ^ α i := (by decide : 2 ∣ 4).trans (hFour i)
  have hA : Nat.card (twoTorsion A) = 2 ^ r₁ := by
    dsimp only [A]
    rw [card_twoTorsion_pi]
    simp only [card_twoTorsion_zmod _ (hTwo _), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have hB : Nat.card (twoTorsion B) = 2 ^ r₂ := by
    dsimp only [B]
    rw [card_twoTorsion_pi]
    simp only [card_twoTorsion_zmod 2 dvd_rfl, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have hT : Nat.card T = 2 ^ r := by
    rw [show T = twoTorsion (A × B) from rfl, card_twoTorsion_prod, hA, hB, ← pow_add]
  have hG : ∃ n : ℕ, ∀ x : G, (2 ^ n : ℕ) • x = 0 := by
    let n := (∑ i, α i) + 1
    have vanish (m : ℕ) [NeZero m] (hm : m ∣ 2 ^ n) (z : ZMod m) : (2 ^ n : ℕ) • z = 0 := by
      obtain ⟨k, hk⟩ := hm
      rw [hk, mul_comm, mul_smul, ZModModule.char_nsmul_eq_zero m, smul_zero]
    refine ⟨n, fun x => Prod.ext (funext fun i => vanish (2 ^ α i) ?_ (x.1 i))
      (funext fun i => vanish 2 (pow_dvd_pow 2 (Nat.succ_pos _)) (x.2 i))⟩
    exact pow_dvd_pow 2 ((Finset.single_le_sum (fun j _ => Nat.zero_le (α j))
      (Finset.mem_univ i)).trans (Nat.le_succ _))
  let all : Set (AddSubgroup G) := {H | H.index = 2}
  let high : Set (AddSubgroup G) := {H | H.index = 2 ∧ T ≤ H}
  have hall : all.ncard = 2 ^ r - 1 := by
    exact (ncard_index_two_eq_card_twoTorsion_sub_one G).trans (congrArg (· - 1) hT)
  -- A subgroup of index two contains all doubles. On the higher-exponent coordinates,
  -- the two-torsion is already made of doubles, so only the elementary factor matters.
  let p : G →+ A := AddMonoidHom.fst A B
  have hp : Function.Surjective p := fun a => ⟨(a, 0), rfl⟩
  have hker : p.ker ≤ T := by
    intro x hx
    change x.1 = 0 at hx
    change (2 : ℕ) • x = 0
    exact Prod.ext (by change (2 : ℕ) • x.1 = 0; rw [hx, smul_zero])
      (funext fun i => ZModModule.char_nsmul_eq_zero 2 (x.2 i))
  have hcomap (K : AddSubgroup A) (hK : K.index = 2) : T ≤ K.comap p := by
    intro x hx
    change x.1 ∈ K
    have hcoord (i : Fin r₁) : ∃ y : ZMod (2 ^ α i), (2 : ℕ) • y = x.1 i :=
      twoTorsion_zmod_le_doubles _ (hFour i) (congrFun (congrArg Prod.fst hx) i)
    choose y hy using hcoord
    rw [← show (2 : ℕ) • y = x.1 from funext hy]
    exact K.two_smul_mem_of_index_two hK y
  have hhigh : high.ncard = 2 ^ r₁ - 1 := by
    rw [← show {K : AddSubgroup A | K.index = 2}.ncard = 2 ^ r₁ - 1 from
      (ncard_index_two_eq_card_twoTorsion_sub_one A).trans (congrArg (· - 1) hA)]
    apply Set.ncard_congr'
    exact
      { toFun := fun H => ⟨H.1.map p, (H.1.index_map_eq hp (hker.trans H.2.2)).trans H.2.1⟩
        invFun := fun K => ⟨K.1.comap p, (K.1.index_comap_of_surjective hp).trans K.2,
          hcomap K.1 K.2⟩
        left_inv := fun H => Subtype.ext (AddSubgroup.comap_map_eq_self (hker.trans H.2.2))
        right_inv := fun K => Subtype.ext (AddSubgroup.map_comap_eq_self_of_surjective hp K.1) }
  have hne : r - 1 ≠ r := by change r₁ + r₂ - 1 ≠ r₁ + r₂; omega
  have high_eq : {H : AddSubgroup G | H.index = 2 ∧ AddGroup.rank H = r} = high := by
    ext H
    by_cases hH : H.index = 2
    · obtain ⟨hyes, hno⟩ := index_two_rank_of_twoTorsion hG (r := r) hr hT H hH
      by_cases h : T ≤ H
      · simp [high, hH, h, hyes h]
      · simp [high, hH, h, hno h, hne]
    · simp [high, hH]
  have low_eq : {H : AddSubgroup G | H.index = 2 ∧ AddGroup.rank H = r - 1} = all \ high := by
    ext H
    by_cases hH : H.index = 2
    · obtain ⟨hyes, hno⟩ := index_two_rank_of_twoTorsion hG (r := r) hr hT H hH
      by_cases h : T ≤ H
      · simp [all, high, hH, h, hyes h, hne.symm]
      · simp [all, high, hH, h, hno h]
    · simp [all, high, hH]
  change {H : AddSubgroup G | H.index = 2 ∧ AddGroup.rank H = r}.ncard = 2 ^ r₁ - 1 ∧
    {H : AddSubgroup G | H.index = 2 ∧ AddGroup.rank H = r - 1}.ncard = 2 ^ r - 2 ^ r₁
  rw [high_eq, low_eq, Set.ncard_sdiff' (show high ⊆ all from fun _ h => h.1), hall, hhigh]
  have h₁ : 0 < 2 ^ r₁ := pow_pos (by decide) _
  have h₂ : 0 < 2 ^ r := pow_pos (by decide) _
  omega

end MetaMathlibExt
