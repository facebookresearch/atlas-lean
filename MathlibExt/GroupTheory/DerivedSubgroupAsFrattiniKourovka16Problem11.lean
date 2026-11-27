/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Frattini
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Ring

/-!
# Derived subgroups as Frattini subgroups of `p`-groups (Kourovka Notebook Problem 16.11)

Kourovka Notebook, Problem 16.11 (Ya. G. Berkovich): let `G` be a finite `p`-group. Does there
always exist a finite `p`-group `H` such that `Φ(H) ≅ [G, G]`?

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 16.11 (Ya. G. Berkovich). UnsolvedMath
record UM-00701203 (`KOU-16.11`), dataset ulamai/UnsolvedMath v1.8.0.

`Φ(H)` is Mathlib's `frattini H` (the intersection of the maximal subgroups) and `[G, G]` is
`commutator G`. The prime is universally quantified and `H` must be a `p`-group for the same prime,
as in the problem; groups are taken in `Type`.

We prove `derivedSubgroupIsFrattini_refuted` using a two-generator permutation group and
an obstruction from automorphisms of its derived subgroup.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.DerivedSubgroupAsFrattiniKourovka16Problem11Wanted

/-- **Derived subgroups of p-groups as Frattini subgroups (Kourovka 16.11).** The conjecture of
Ya. G. Berkovich that for every prime $p$ and every finite $p$-group $G$ there is a finite
$p$-group $H$ whose Frattini subgroup $\Phi(H)$, the intersection of the maximal subgroups of $H$,
is isomorphic to the derived subgroup $[G, G]$ of $G$.
-/
def derivedSubgroupIsFrattini : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (G : Type) [Group G] [Finite G], IsPGroup p G →
    ∃ (H : Type) (_ : Group H) (_ : Finite H), IsPGroup p H ∧
      Nonempty (frattini H ≃* commutator G)

open Subgroup
open scoped commutatorElement

-- The coordinates represent x^i y^j z^k. Conjugation by z sends x to x y² and y to y x²,
-- and z² = x².
@[ext] private structure DerivedGroup where
  i : ZMod 4
  j : ZMod 4
  k : Bool
deriving DecidableEq, Fintype

private def nMul (x y : DerivedGroup) : DerivedGroup :=
  ⟨x.i + y.i + (if x.k then 2 * y.j else 0) + (if x.k && y.k then 2 else 0),
   x.j + y.j + (if x.k then 2 * y.i else 0), x.k ^^ y.k⟩

private def nInv (x : DerivedGroup) : DerivedGroup :=
  if x.k then ⟨-x.i + 2 * x.j + 2, -x.j + 2 * x.i, true⟩
  else ⟨-x.i, -x.j, false⟩

private instance nGroup : Group DerivedGroup where
  mul := nMul
  one := ⟨0, 0, false⟩
  inv := nInv
  mul_assoc := by
    intro u v w
    change nMul (nMul u v) w = nMul u (nMul v w)
    obtain ⟨ui, uj, uk⟩ := u
    obtain ⟨vi, vj, vk⟩ := v
    obtain ⟨wi, wj, wk⟩ := w
    cases uk <;> cases vk <;> cases wk <;>
      apply DerivedGroup.ext <;> simp [nMul] <;> ring_nf <;>
        simp [show (4 : ZMod 4) = 0 by decide, show (5 : ZMod 4) = 1 by decide]
  one_mul := show ∀ x : DerivedGroup, nMul ⟨0, 0, false⟩ x = x by decide
  mul_one := show ∀ x : DerivedGroup, nMul x ⟨0, 0, false⟩ = x by decide
  inv_mul_cancel := show ∀ x : DerivedGroup, nMul (nInv x) x = ⟨0, 0, false⟩ by decide

private def x : DerivedGroup := ⟨1, 0, false⟩
private def y : DerivedGroup := ⟨0, 1, false⟩
private def z : DerivedGroup := ⟨0, 0, true⟩

private def fromCoordinates {A : Type*} [Group A] (u v w : A) (n : DerivedGroup) : A :=
  u ^ n.i.val * v ^ n.j.val * (if n.k then w else 1)

private theorem n_coordinates : ∀ n, fromCoordinates x y z n = n := by decide +kernel

private theorem map_coordinates {A B : Type*} [Group A] [Group B]
    (f : A →* B) (u v w : A) (n : DerivedGroup) :
    f (fromCoordinates u v w n) = fromCoordinates (f u) (f v) (f w) n := by
  cases h : n.k <;> simp [fromCoordinates, h]

private theorem map_fromCoordinates {A : Type*} [Group A] (f : DerivedGroup →* A)
    (n : DerivedGroup) :
    f n = fromCoordinates (f x) (f y) (f z) n :=
  (congrArg f (n_coordinates n).symm).trans (map_coordinates f x y z n)

private def parity (n : DerivedGroup) : Nat × Nat × Bool := (n.i.val % 2, n.j.val % 2, n.k)

private theorem conjugation_parity :
    ∀ a n : DerivedGroup, parity (a * n * a⁻¹) = parity n := by decide +kernel

private theorem commuting_distinct_squares :
    ∀ u v : DerivedGroup, u * v = v * u → u ^ 2 ≠ 1 → v ^ 2 ≠ 1 → u ^ 2 ≠ v ^ 2 →
      u.k = false ∧ v.k = false := by decide +kernel

private theorem commuting_in_plane :
    ∀ u v : DerivedGroup, u.k = false → v.k = false → u * v = v * u := by decide +kernel

-- The images of x, y, z satisfy their commutator and square relations. If the square of the
-- map fixes z modulo the center, the coordinate calculation shows that it fixes x exactly.
private def squareTest (u v w : DerivedGroup) : Prop :=
  u ^ 2 ≠ 1 → v ^ 2 ≠ 1 → u ^ 2 ≠ v ^ 2 →
  ⁅u, w⁆ = v ^ 2 → ⁅v, w⁆ = u ^ 2 → w ^ 2 = u ^ 2 →
  parity (fromCoordinates u v w w) = parity z →
  fromCoordinates u v w u = x

private theorem square_fixes_x_of_relations :
    ∀ (i j l m r s : ZMod 4), squareTest ⟨i, j, false⟩ ⟨l, m, false⟩ ⟨r, s, true⟩ := by
  intro i
  fin_cases i <;> unfold squareTest <;> decide +kernel

private theorem centralizes_x_in_plane :
    ∀ n : DerivedGroup, n * x * n⁻¹ = x → n.k = false := by decide +kernel

private theorem inner_square_in_plane (f : DerivedGroup ≃* DerivedGroup) (a : DerivedGroup)
    (hf : ∀ n, f (f n) = a * n * a⁻¹) : a.k = false := by
  have hu : f x ^ 2 ≠ 1 := by
    rw [← map_pow, ← f.map_one]
    exact fun hh => (by decide : x ^ 2 ≠ 1) (f.injective hh)
  have hv : f y ^ 2 ≠ 1 := by
    rw [← map_pow, ← f.map_one]
    exact fun hh => (by decide : y ^ 2 ≠ 1) (f.injective hh)
  have huv : f x ^ 2 ≠ f y ^ 2 := by
    rw [← map_pow, ← map_pow]
    exact fun hh => (by decide : x ^ 2 ≠ y ^ 2) (f.injective hh)
  have huvComm : f x * f y = f y * f x := by
    rw [← map_mul, ← map_mul, (by decide : x * y = y * x)]
  obtain ⟨hx, hy⟩ := commuting_distinct_squares _ _ huvComm hu hv huv
  have hz : (f z).k = true := by
    cases h : (f z).k
    · have hcomm := commuting_in_plane _ _ hx h
      rw [← map_mul, ← map_mul] at hcomm
      exact ((by decide : x * z ≠ z * x) (f.injective hcomm)).elim
    · rfl
  apply centralizes_x_in_plane
  rw [← hf]
  change f.toMonoidHom (f x) = x
  rw [map_fromCoordinates]
  have htest : squareTest (f x) (f y) (f z) := by
    have recover (n : DerivedGroup) : DerivedGroup.mk n.i n.j n.k = n := by cases n; rfl
    rw [← recover (f x), ← recover (f y), ← recover (f z), hx, hy, hz]
    exact square_fixes_x_of_relations _ _ _ _ _ _
  apply htest hu hv huv
  · rw [← map_commutatorElement, ← map_pow, (by decide : ⁅x, z⁆ = y ^ 2)]
  · rw [← map_commutatorElement, ← map_pow, (by decide : ⁅y, z⁆ = x ^ 2)]
  · rw [← map_pow, ← map_pow, (by decide : z ^ 2 = x ^ 2)]
  · change parity (fromCoordinates (f.toMonoidHom x) (f.toMonoidHom y)
      (f.toMonoidHom z) (f z)) = _
    rw [← map_fromCoordinates]
    exact (congrArg parity (hf z)).trans (conjugation_parity a z)

-- In a finite 2-group every maximal subgroup has index 2, so it contains all squares.
private theorem square_mem_frattini {H : Type*} [Group H] [Finite H]
    (hH : IsPGroup 2 H) (g : H) : g ^ 2 ∈ frattini H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hH.isNilpotent
  rw [frattini, Order.radical, Subgroup.mem_iInf]
  simp only [Subgroup.mem_iInf, Set.mem_ofPred_eq]
  intro M hM
  change IsCoatom M at hM
  have : M.Normal := Group.normalizerCondition_of_isNilpotent.normal_of_coatom M hM
  have hc : Nat.card (H ⧸ M) = 2 :=
    M.index_eq_card.symm.trans (hH.isCoatom_iff_index_eq_prime.mp hM)
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' M (g ^ 2) = 1
  rw [map_pow, ← hc]
  exact pow_card_eq_one'

private theorem frattini_le_of_squares {H : Type*} [Group H] [Finite H]
    (K : Subgroup H) (hK : ∀ g : H, g ^ 2 ∈ K) : frattini H ≤ K := by
  -- A subgroup containing every square is normal and has an elementary abelian quotient.
  have hconj (a b : H) (hb : b ∈ K) : a * b * a⁻¹ ∈ K := by
    have hh : a * b * a⁻¹ = (a * b) ^ 2 * b⁻¹ * (a⁻¹) ^ 2 := by
      simp only [pow_two, mul_assoc, ← mul_inv_rev]
      simp [← mul_assoc]
    rw [hh]
    exact K.mul_mem (K.mul_mem (hK _) (K.inv_mem hb)) (hK _)
  have : K.Normal := ⟨fun n hn g => hconj g n hn⟩
  let Q := H ⧸ K
  have hsq (q : Q) : q ^ 2 = 1 := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K q
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hK _)
  have hsup (q : Q) : q = q⁻¹ := eq_inv_of_mul_eq_one_left (by simpa [pow_two] using hsq q)
  let : CommGroup Q :=
    { (inferInstance : Group Q) with
      mul_comm := fun a b => by
        calc
          a * b = (a * b)⁻¹ := hsup _
          _ = b⁻¹ * a⁻¹ := mul_inv_rev _ _
          _ = b * a := by rw [← hsup a, ← hsup b] }
  have hbot : frattini Q = ⊥ := by
    -- An elementary abelian group has enough linear functionals to separate points.
    apply eq_bot_iff.mpr
    intro q hq
    rw [Subgroup.mem_bot]
    let : Module (ZMod 2) (Additive Q) :=
      AddCommGroup.zmodModule fun x => congrArg Additive.ofMul (hsq (Additive.toMul x))
    by_contra hqne
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (ZMod 2)
      (show Additive.ofMul q ≠ 0 from hqne)
    let χ := AddMonoidHom.toMultiplicative f.toAddMonoidHom
    have hχ : Function.Surjective χ := by
      have hχq : χ q = Multiplicative.ofAdd 1 := hf
      intro b
      have hb : b = 1 ∨ b = Multiplicative.ofAdd 1 := by
        exact (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) b.toAdd
      rcases hb with rfl | rfl
      · exact ⟨1, χ.map_one⟩
      · exact ⟨q, hχq⟩
    have hc : IsCoatom χ.ker := by
      apply Subgroup.isCoatom_of_index_prime
      rw [χ.ker.index_eq_card,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective χ hχ).toEquiv]
      simpa [Nat.card_eq_fintype_card] using Nat.prime_two
    exact (by decide : (1 : ZMod 2) ≠ 0) (hf.symm.trans (frattini_le_coatom hc hq))
  have hle := frattini_le_comap_frattini_of_surjective (QuotientGroup.mk'_surjective K)
  rw [hbot] at hle
  intro g hg
  exact (QuotientGroup.eq_one_iff _).mp (Subgroup.mem_bot.mp (hle hg))

private abbrev Perm := Equiv.Perm (Fin 16)

-- These two permutations generate the witness. The three coordinates of its derived group
-- correspond to products of conjugates of their commutator.
private def a : Perm :=
  ⟨![9, 8, 10, 11, 13, 12, 14, 15, 7, 6, 4, 5, 0, 1, 2, 3],
   ![12, 13, 14, 15, 10, 11, 9, 8, 1, 0, 2, 3, 5, 4, 6, 7], by decide, by decide⟩

private def b : Perm :=
  ⟨![9, 8, 11, 10, 12, 13, 14, 15, 3, 2, 1, 0, 4, 5, 7, 6],
   ![11, 10, 9, 8, 12, 13, 15, 14, 1, 0, 3, 2, 4, 5, 6, 7], by decide, by decide⟩

private def c : Perm := ⁅a, b⁆

private def px : Perm := c * (b⁻¹ * c * b)

private def py : Perm := c * (a * c * a⁻¹)

private def pz : Perm := a⁻¹ * c * a

private abbrev evalPerm : DerivedGroup → Perm := fromCoordinates px py pz

private theorem evalPerm_mul (u v : DerivedGroup) : evalPerm (u * v) = evalPerm u * evalPerm v := by
  have hx : ∀ u : DerivedGroup, evalPerm (u * x) = evalPerm u * px := by decide +kernel
  have hy : ∀ u : DerivedGroup, evalPerm (u * y) = evalPerm u * py := by decide +kernel
  have hz : ∀ u : DerivedGroup, evalPerm (u * z) = evalPerm u * pz := by decide +kernel
  have step {g : DerivedGroup} {p : Perm} (hg : ∀ n, evalPerm (n * g) = evalPerm n * p)
      (n : DerivedGroup) (m : ℕ) : evalPerm (n * g ^ m) = evalPerm n * p ^ m := by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, ← mul_assoc, hg, ih, pow_succ, mul_assoc]
  conv_lhs => rw [← n_coordinates v]
  cases hk : v.k <;>
    simp [fromCoordinates, hk, ← mul_assoc, hz, step hx, step hy]

private def permHom : DerivedGroup →* Perm where
  toFun := evalPerm
  map_one' := by decide
  map_mul' u v := evalPerm_mul u v

private theorem permHom_injective : Function.Injective permHom := by
  apply (injective_iff_map_eq_one permHom).mpr
  change ∀ n : DerivedGroup, evalPerm n = 1 → n = 1
  decide +kernel

private abbrev G : Subgroup Perm := Subgroup.closure {a, b}

private def aG : G := ⟨a, subset_closure (by simp)⟩

private def bG : G := ⟨b, subset_closure (by simp)⟩

private def cG : G := ⁅aG, bG⁆

private def xG : G := cG * (bG⁻¹ * cG * bG)

private def yG : G := cG * (aG * cG * aG⁻¹)

private def zG : G := aG⁻¹ * cG * aG

private theorem evalG_coe (n : DerivedGroup) :
    G.subtype (fromCoordinates xG yG zG n) = evalPerm n :=
  map_coordinates G.subtype xG yG zG n

private def toG : DerivedGroup →* G := permHom.codRestrict G fun n => by
  change evalPerm n ∈ G
  rw [← evalG_coe n]
  exact (fromCoordinates xG yG zG n).prop

private theorem toG_eval (n : DerivedGroup) : toG n = fromCoordinates xG yG zG n :=
  Subtype.ext (evalG_coe n).symm

private theorem closure_generators : Subgroup.closure ({aG, bG} : Set G) = ⊤ := by
  apply Subgroup.map_injective G.subtype_injective
  rw [MonoidHom.map_closure, Set.image_pair, Subgroup.map_top, Subgroup.range_subtype]
  rfl

private theorem mem_derived (n : DerivedGroup) : toG n ∈ commutator G := by
  have hc : cG ∈ commutator G := Subgroup.commutator_mem_commutator trivial trivial
  have normal : (commutator G).Normal := inferInstance
  have hx : xG ∈ commutator G := mul_mem hc (by simpa [inv_inv] using normal.conj_mem cG hc bG⁻¹)
  have hy : yG ∈ commutator G := mul_mem hc (normal.conj_mem cG hc aG)
  have hz : zG ∈ commutator G := by simpa [zG] using normal.conj_mem cG hc aG⁻¹
  rw [toG_eval]
  exact mul_mem (mul_mem (pow_mem hx _) (pow_mem hy _)) (by split <;> simp_all)

private theorem normalizes_range_of_conj (p : Perm)
    (h : ∀ q ∈ ({px, py, pz} : Set Perm), p * q * p⁻¹ ∈ permHom.range) :
    ∀ t ∈ permHom.range, p * t * p⁻¹ ∈ permHom.range := by
  rintro _ ⟨n, rfl⟩
  let φ := MulAut.conj p
  change φ (evalPerm n) ∈ permHom.range
  have hx := h px (by simp)
  have hy := h py (by simp)
  have hz := h pz (by simp)
  change φ px ∈ permHom.range at hx
  change φ py ∈ permHom.range at hy
  change φ pz ∈ permHom.range at hz
  cases hn : n.k <;> simp only [evalPerm, fromCoordinates, hn, ↓reduceIte, Bool.false_eq_true,
    map_mul, map_pow, map_one] <;> apply mul_mem (mul_mem (pow_mem hx _) (pow_mem hy _))
  · exact one_mem _
  · exact hz

private theorem a_normalizes : a ∈ Subgroup.normalizer permHom.range := by
  apply Subgroup.mem_normalizer_fintype (normalizes_range_of_conj a ?_)
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨⟨0, 1, false⟩, by decide +kernel⟩
  · exact ⟨⟨3, 2, false⟩, by decide +kernel⟩
  · exact ⟨⟨3, 2, true⟩, by decide +kernel⟩

private theorem b_normalizes : b ∈ Subgroup.normalizer permHom.range := by
  apply Subgroup.mem_normalizer_fintype (normalizes_range_of_conj b ?_)
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨⟨0, 3, false⟩, by decide +kernel⟩
  · exact ⟨⟨1, 0, false⟩, by decide +kernel⟩
  · exact ⟨⟨1, 2, true⟩, by decide +kernel⟩

private instance toG_range_normal : toG.range.Normal := by
  have hn : G ≤ Subgroup.normalizer permHom.range := by
    apply (Subgroup.closure_le _).mpr
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · exact a_normalizes
    · exact b_normalizes
  refine ⟨?_⟩
  rintro - ⟨n, rfl⟩ g
  have h := (Subgroup.mem_normalizer_iff.mp (hn g.prop) (permHom n)).mp ⟨n, rfl⟩
  obtain ⟨m, hm⟩ := h
  exact ⟨m, Subtype.ext hm⟩

private theorem cG_mem_range : cG ∈ toG.range := by
  refine ⟨⟨3, 2, true⟩, Subtype.ext ?_⟩
  decide +kernel

private theorem closure_quotient_generators :
    Subgroup.closure ({QuotientGroup.mk' toG.range aG, QuotientGroup.mk' toG.range bG} :
      Set (G ⧸ toG.range)) = ⊤ := by
  rw [← Set.image_pair, ← MonoidHom.map_closure, closure_generators,
    Subgroup.map_top, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]

private theorem quotient_commutative : IsMulCommutative (G ⧸ toG.range) := by
  have hab : Commute (QuotientGroup.mk' toG.range aG) (QuotientGroup.mk' toG.range bG) := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr cG_mem_range
  have hc : IsMulCommutative (Subgroup.closure
      ({QuotientGroup.mk' toG.range aG, QuotientGroup.mk' toG.range bG} :
        Set (G ⧸ toG.range))) := Subgroup.isMulCommutative_closure (by
    exact Set.pairwise_pair.mpr fun _ => ⟨hab, hab.symm⟩)
  rw [closure_quotient_generators] at hc
  exact ⟨⟨fun g h => congrArg Subtype.val (hc.is_comm.comm ⟨g, trivial⟩ ⟨h, trivial⟩)⟩⟩

private theorem derived_eq_range : commutator G = toG.range :=
  le_antisymm (Subgroup.Normal.quotient_commutative_iff_commutator_le.mp quotient_commutative)
    (by rintro _ ⟨n, rfl⟩; exact mem_derived n)

private theorem isPGroup_G : IsPGroup 2 G := by
  let q := QuotientGroup.mk' toG.range
  let : CommGroup (G ⧸ toG.range) :=
    { (inferInstance : Group (G ⧸ toG.range)) with mul_comm := quotient_commutative.is_comm.comm }
  let pow16 : (G ⧸ toG.range) →* (G ⧸ toG.range) := powMonoidHom 16
  have hker : Subgroup.closure ({q aG, q bG} : Set _) ≤ pow16.ker := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · change q aG ^ 16 = 1
      rw [← map_pow, show aG ^ 16 = 1 from Subtype.ext (by decide), map_one]
    · change q bG ^ 16 = 1
      rw [← map_pow, show bG ^ 16 = 1 from Subtype.ext (by decide), map_one]
  rw [closure_quotient_generators] at hker
  intro g
  have hgq : q (g ^ 16) = 1 := by
    rw [map_pow]
    exact hker (show q g ∈ (⊤ : Subgroup (G ⧸ toG.range)) from trivial)
  obtain ⟨n, hn⟩ : g ^ 16 ∈ toG.range := (QuotientGroup.eq_one_iff _).mp hgq
  refine ⟨6, ?_⟩
  change g ^ (16 * 4) = 1
  rw [pow_mul, ← hn, ← map_pow, (by decide : ∀ n : DerivedGroup, n ^ 4 = 1), map_one]

private def plane : Subgroup DerivedGroup where
  carrier := {n | n.k = false}
  one_mem' := rfl
  mul_mem' := by
    intro u v hu hv
    change u.k = false at hu
    change v.k = false at hv
    change (u.k ^^ v.k) = false
    simp [hu, hv]
  inv_mem' := by
    intro u hu
    change u.k = false at hu
    change (nInv u).k = false
    simp [nInv, hu]

-- Transport conjugation by g to the coordinate group. Its square is conjugation by g²,
-- so every square of the ambient group lies in the pullback of the proper subgroup.
private theorem frattini_not_equiv {H : Type*} [Group H] [Finite H] (hH : IsPGroup 2 H)
    (e : frattini H ≃* DerivedGroup) : False := by
  let K := (plane.comap e.toMonoidHom).map (frattini H).subtype
  have hK : ∀ g : H, g ^ 2 ∈ K := by
    intro g
    let s : frattini H := ⟨g ^ 2, square_mem_frattini hH g⟩
    let f := e.symm.trans ((MulAut.conjNormal g : MulAut (frattini H)).trans e)
    refine ⟨s, inner_square_in_plane f (e s) ?_, rfl⟩
    intro n
    change e (MulAut.conjNormal g (e.symm (e (MulAut.conjNormal g (e.symm n))))) =
      e s * n * (e s)⁻¹
    rw [e.symm_apply_apply]
    have h (t : frattini H) :
        MulAut.conjNormal g (MulAut.conjNormal g t) = MulAut.conjNormal (g ^ 2) t := by
      rw [map_pow, pow_two, MulAut.mul_apply]
    rw [h]
    change e (MulAut.conjNormal (s : H) (e.symm n)) = _
    rw [MulAut.conjNormal_val, MulAut.conj_apply, map_mul, map_mul, map_inv, e.apply_symm_apply]
  have hz := frattini_le_of_squares K hK (e.symm z).prop
  obtain ⟨v, hv, hv_eq⟩ := hz
  have he : v = e.symm z := Subtype.ext hv_eq
  subst v
  change (e (e.symm z)).k = false at hv
  rw [e.apply_symm_apply] at hv
  exact (by decide : z.k ≠ false) hv

/--
**Derived subgroups of p-groups need not be Frattini subgroups of p-groups.** There exist a prime
$p$ and a finite $p$-group $G$ such that for every finite $p$-group $H$, the Frattini subgroup
$\Phi(H)$ of $H$ is not isomorphic to the derived subgroup $[G, G]$ of $G$. That is, the conjecture
of Kourovka Problem 16.11 is false.

Ionin and Semidetnov take $p = 2$ and $G$ the group SmallGroup(256, 511), whose derived subgroup
is the Hall-Senior group 32/40 (a GAP computation); by a theorem of van der Waall and de Nijs, that
group is not isomorphic to the Frattini subgroup of any finite 2-group. The authors state that
their solutions were found with the assistance of large language models and checked by them.

See the module description for the construction using a two-generator permutation group.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 16.11 (Ya. G. Berkovich); resolution: V.
Ionin and A. Semidetnov, On some more problems from the Kourovka Notebook, preprint,
arXiv:2608.29219 (2026), Answer 3.2 with Lemma 3.4 and Theorem 3.3 (van der Waall-de Nijs, Theorem
1.15): for p = 2, G = SmallGroup(256, 511) has derived subgroup the Hall-Senior group 32/40, which
is the Frattini subgroup of no finite 2-group; the Kourovka Notebook (21st issue) marks 16.11 solved
(No, not always), https://arxiv.org/abs/2608.29219.
-/
theorem derivedSubgroupIsFrattini_refuted : ¬ derivedSubgroupIsFrattini := by
  intro h
  obtain ⟨H, _, _, hH, ⟨e⟩⟩ := h 2 Nat.prime_two G isPGroup_G
  have hinj : Function.Injective toG := fun _ _ hh =>
    permHom_injective (congrArg Subtype.val hh)
  let equivalence :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr derived_eq_range.symm)
  exact frattini_not_equiv hH (e.trans equivalence.symm)

end MathlibExt.GroupTheory.DerivedSubgroupAsFrattiniKourovka16Problem11Wanted
