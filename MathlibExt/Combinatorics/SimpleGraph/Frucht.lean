/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

namespace SimpleGraph

/-- Composition of graph automorphisms, matching permutation order:
`(a * b) x = a (b x)`. -/
instance {V : Type*} {G : SimpleGraph V} : Mul (G ≃g G) := ⟨fun a b => b.trans a⟩

/-- Identity automorphism. -/
instance {V : Type*} {G : SimpleGraph V} : One (G ≃g G) := ⟨RelIso.refl _⟩

/-- Inverse automorphism. -/
instance {V : Type*} {G : SimpleGraph V} : Inv (G ≃g G) := ⟨fun a => a.symm⟩

/-- Automorphisms of a graph form a group under composition. -/
instance instGroupIsoSelf {V : Type*} {G : SimpleGraph V} : Group (G ≃g G) where
  mul_assoc a b c := RelIso.ext fun x => rfl
  one_mul a := RelIso.ext fun x => rfl
  mul_one a := RelIso.ext fun x => rfl
  inv_mul_cancel a := RelIso.ext fun x => RelIso.symm_apply_apply a x

end SimpleGraph

section
namespace MathlibExt.Combinatorics.SimpleGraph.FruchtWanted

private def fruchtAdj (N : ℕ) {G : Type*} [Group G] [DecidableEq G] (e : G ≃ Fin N) :
    (G ⊕ (G × Fin N)) → (G ⊕ (G × Fin N)) → Prop
  | .inl x, .inl y => x ≠ y
  | .inl x, .inr (g, j) => e (g⁻¹ * x) ≤ j
  | .inr (g, j), .inl x => e (g⁻¹ * x) ≤ j
  | .inr (g, i), .inr (h, j) => g = h ∧ i ≠ j

private noncomputable def fruchtGraph (N : ℕ) {G : Type*} [Group G] [DecidableEq G] [Fintype G]
    (e : G ≃ Fin N) : SimpleGraph (G ⊕ (G × Fin N)) where
  Adj := fruchtAdj N e
  symm := Std.Symm.mk (fun a b h => by
    cases a with
    | inl x =>
      cases b with
      | inl y => exact Ne.symm h
      | inr p => obtain ⟨g, j⟩ := p; exact h
    | inr p =>
      obtain ⟨g, i⟩ := p
      cases b with
      | inl y => exact h
      | inr q => obtain ⟨h2, j⟩ := q; exact ⟨Eq.symm h.1, Ne.symm h.2⟩)
  loopless := Std.Irrefl.mk (fun a h => by
    cases a with
    | inl x => exact absurd rfl h
    | inr p => obtain ⟨g, j⟩ := p; exact absurd rfl h.2)

private noncomputable instance fruchtGraphDec (N : ℕ) {G : Type*} [Group G] [DecidableEq G]
    [Fintype G] (e : G ≃ Fin N) : DecidableRel (fruchtGraph N e).Adj :=
  Classical.decRel _

private theorem fruchtGraph_adj_inl_inl (N : ℕ) {G : Type*} [Group G] [DecidableEq G] [Fintype G]
    (e : G ≃ Fin N) (x y : G) :
    (fruchtGraph N e).Adj (.inl x) (.inl y) ↔ x ≠ y := Iff.rfl

private theorem fruchtGraph_adj_inl_inr (N : ℕ) {G : Type*} [Group G] [DecidableEq G] [Fintype G]
    (e : G ≃ Fin N) (x g : G) (j : Fin N) :
    (fruchtGraph N e).Adj (.inl x) (.inr (g, j)) ↔ e (g⁻¹ * x) ≤ j := Iff.rfl

private theorem fruchtGraph_adj_inr_inl (N : ℕ) {G : Type*} [Group G] [DecidableEq G] [Fintype G]
    (e : G ≃ Fin N) (g x : G) (j : Fin N) :
    (fruchtGraph N e).Adj (.inr (g, j)) (.inl x) ↔ e (g⁻¹ * x) ≤ j := Iff.rfl

private theorem fruchtGraph_adj_inr_inr (N : ℕ) {G : Type*} [Group G] [DecidableEq G] [Fintype G]
    (e : G ≃ Fin N) (g h : G) (i j : Fin N) :
    (fruchtGraph N e).Adj (.inr (g, i)) (.inr (h, j)) ↔ g = h ∧ i ≠ j := Iff.rfl

private def fruchtShift (N : ℕ) {G : Type*} [Group G] (a : G) :
    Equiv.Perm (G ⊕ (G × Fin N)) :=
  Equiv.sumCongr (Equiv.mulLeft a) (Equiv.prodCongr (Equiv.mulLeft a) (Equiv.refl (Fin N)))

private theorem fruchtShift_inl (N : ℕ) {G : Type*} [Group G] (a x : G) :
    fruchtShift N a (.inl x : G ⊕ (G × Fin N)) = .inl (a * x) := rfl

private theorem fruchtShift_inr (N : ℕ) {G : Type*} [Group G] (a g : G) (j : Fin N) :
    fruchtShift N a (.inr (g, j) : G ⊕ (G × Fin N)) = .inr (a * g, j) := rfl

private theorem fruchtShift_mul (N : ℕ) {G : Type*} [Group G] (a b : G) :
    fruchtShift N (a * b) = fruchtShift N a * fruchtShift N b := by
  apply Equiv.Perm.ext
  intro v
  cases v with
  | inl x =>
    change (.inl ((a * b) * x) : G ⊕ (G × Fin N)) = (fruchtShift N a * fruchtShift N b) _
    rw [Equiv.Perm.mul_apply, fruchtShift_inl, fruchtShift_inl, mul_assoc]
  | inr p =>
    obtain ⟨g, j⟩ := p
    change (.inr ((a * b) * g, j) : G ⊕ (G × Fin N)) = (fruchtShift N a * fruchtShift N b) _
    rw [Equiv.Perm.mul_apply, fruchtShift_inr, fruchtShift_inr, mul_assoc]

private theorem fruchtShift_adj (N : ℕ) {G : Type*} [Group G] [DecidableEq G] [Fintype G]
    (e : G ≃ Fin N) (a : G) (v w : G ⊕ (G × Fin N)) :
    (fruchtGraph N e).Adj v w ↔
      (fruchtGraph N e).Adj (fruchtShift N a v) (fruchtShift N a w) := by
  cases v with
  | inl x =>
    cases w with
    | inl y =>
      rw [fruchtShift_inl, fruchtShift_inl, fruchtGraph_adj_inl_inl,
        fruchtGraph_adj_inl_inl]
      exact (not_congr (mul_right_inj a)).symm
    | inr p =>
      obtain ⟨g, j⟩ := p
      rw [fruchtShift_inl, fruchtShift_inr, fruchtGraph_adj_inl_inr,
        fruchtGraph_adj_inl_inr]
      have h : (a * g)⁻¹ * (a * x) = g⁻¹ * x := by
        rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
      rw [h]
  | inr p =>
    obtain ⟨g, i⟩ := p
    cases w with
    | inl y =>
      rw [fruchtShift_inr, fruchtShift_inl, fruchtGraph_adj_inr_inl,
        fruchtGraph_adj_inr_inl]
      have h : (a * g)⁻¹ * (a * y) = g⁻¹ * y := by
        rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
      rw [h]
    | inr q =>
      obtain ⟨h2, j⟩ := q
      rw [fruchtShift_inr, fruchtShift_inr, fruchtGraph_adj_inr_inr,
        fruchtGraph_adj_inr_inr]
      constructor
      · intro hh
        exact ⟨(mul_right_inj a).mpr hh.1, hh.2⟩
      · intro hh
        exact ⟨(mul_right_inj a).mp hh.1, hh.2⟩

private noncomputable def fruchtShiftIso (N : ℕ) {G : Type*} [Group G] [DecidableEq G]
    [Fintype G] (e : G ≃ Fin N) (a : G) :
    fruchtGraph N e ≃g fruchtGraph N e :=
  RelIso.mk (fruchtShift N a) (fun {v w} => (fruchtShift_adj N e a v w).symm)

private theorem fruchtIso_degree_eq {W : Type*} [Fintype W] (Γ : SimpleGraph W)
    [DecidableRel Γ.Adj] (ι : Γ ≃g Γ) (v : W) :
    Γ.degree (ι v) = Γ.degree v :=
  SimpleGraph.Iso.degree_eq ι v

private theorem card_filter_colour_le (N : ℕ) {G : Type*} [Group G] [Fintype G]
    (e : G ≃ Fin N) (g : G) (j : Fin N) :
    (Finset.univ.filter (fun x => e (g⁻¹ * x) ≤ j)).card = (j.val + 1) := by
  have h := Finset.card_bij'
    (s := Finset.univ.filter (fun x => e (g⁻¹ * x) ≤ j))
    (t := Finset.Iic j)
    (fun x _ => e (g⁻¹ * x)) (fun k _ => g * e.symm k)
    (by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [Finset.mem_Iic]
      exact hx)
    (by
      intro k hk
      simp only [Finset.mem_Iic] at hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hgk : g⁻¹ * (g * e.symm k) = e.symm k :=
        inv_mul_cancel_left g (e.symm k)
      rw [hgk, Equiv.apply_symm_apply]
      exact hk)
    (by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      show g * e.symm (e (g⁻¹ * x)) = x
      rw [Equiv.symm_apply_apply, mul_inv_cancel_left])
    (by
      intro k hk
      simp only [Finset.mem_Iic] at hk
      show e (g⁻¹ * (g * e.symm k)) = k
      have hgk : g⁻¹ * (g * e.symm k) = e.symm k :=
        inv_mul_cancel_left g (e.symm k)
      rw [hgk, Equiv.apply_symm_apply])
  rw [h, Fin.card_Iic]

private theorem fruchtGraph_degree_inr_aux (N : ℕ) {G : Type*} [Group G] [DecidableEq G] [Fintype G]
    (e : G ≃ Fin N) (g : G) (j : Fin N) :
    (fruchtGraph N e).neighborFinset (.inr (g, j)) =
      (Finset.univ.filter (fun x => e (g⁻¹ * x) ≤ j)).image Sum.inl ∪
      (Finset.univ.erase j).image (fun i => (Sum.inr (g, i) : G ⊕ (G × Fin N))) := by
  apply Finset.ext
  intro w
  cases w with
  | inl x =>
    rw [SimpleGraph.mem_neighborFinset]
    show (fruchtGraph N e).Adj (.inr (g, j)) (.inl x) ↔ _
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
    constructor
    · intro hwx
      exact Or.inl ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hwx⟩, rfl⟩
    · intro hwx
      cases hwx with
      | inl hleft =>
        obtain ⟨y, hy, hyeq⟩ := hleft
        have hyf : e (g⁻¹ * y) ≤ j := (Finset.mem_filter.mp hy).2
        have hye : y = x := Sum.inl_injective hyeq
        rw [hye] at hyf
        exact hyf
      | inr hright =>
        obtain ⟨_, _, heq⟩ := hright
        exact absurd heq (by simp)
  | inr p =>
    obtain ⟨h2, i⟩ := p
    rw [SimpleGraph.mem_neighborFinset]
    show (fruchtGraph N e).Adj (.inr (g, j)) (.inr (h2, i)) ↔ _
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
    constructor
    · intro hwx
      have hgh1 : g = h2 := hwx.1
      have hgh2 : j ≠ i := hwx.2
      exact Or.inr ⟨i, Finset.mem_erase.mpr ⟨Ne.symm hgh2, Finset.mem_univ i⟩,
        by rw [hgh1]⟩
    · intro hwx
      cases hwx with
      | inl hleft =>
        obtain ⟨_, _, heq⟩ := hleft
        exact absurd heq (by simp)
      | inr hright =>
        obtain ⟨i', hi', heq⟩ := hright
        have hmem : i' ≠ j := (Finset.mem_erase.mp hi').1
        have heq2 : (g, i') = (h2, i) := Sum.inr_injective heq
        have hprod : g = h2 ∧ i' = i := Prod.mk.inj heq2
        change g = h2 ∧ j ≠ i
        exact ⟨hprod.1, by rw [← hprod.2]; exact Ne.symm hmem⟩

private theorem fruchtGraph_degree_inr (N : ℕ) {G : Type*} [Group G] [DecidableEq G] [Fintype G]
    (e : G ≃ Fin N) (g : G) (j : Fin N) :
    (fruchtGraph N e).degree (.inr (g, j)) = N + j.val := by
  have hcard : (fruchtGraph N e).degree (.inr (g, j)) =
      ((fruchtGraph N e).neighborFinset (.inr (g, j))).card :=
    (SimpleGraph.card_neighborFinset_eq_degree _ _).symm
  rw [hcard, fruchtGraph_degree_inr_aux]
  have hdisj : Disjoint
      ((Finset.univ.filter (fun x => e (g⁻¹ * x) ≤ j)).image (Sum.inl : G → G ⊕ (G × Fin N)))
      ((Finset.univ.erase j).image (fun i => (Sum.inr (g, i) : G ⊕ (G × Fin N)))) := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp ha1
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha2
    rw [← hx] at hi
    exact absurd hi (by simp)
  rw [Finset.card_union_of_disjoint hdisj]
  have hP : ((Finset.univ.filter (fun x => e (g⁻¹ * x) ≤ j)).image
      (Sum.inl : G → G ⊕ (G × Fin N))).card = j.val + 1 := by
    rw [Finset.card_image_of_injective (s := Finset.univ.filter (fun x => e (g⁻¹ * x) ≤ j))
      (f := (Sum.inl : G → G ⊕ (G × Fin N))) Sum.inl_injective, card_filter_colour_le]
  have hQ : ((Finset.univ.erase j).image
      (fun i => (Sum.inr (g, i) : G ⊕ (G × Fin N)))).card = N - 1 := by
    have hinj : Function.Injective (fun i => (Sum.inr (g, i) : G ⊕ (G × Fin N))) := by
      intro a b hab
      have h2 : (g, a) = (g, b) := Sum.inr_injective hab
      exact (Prod.mk.inj h2).2
    rw [Finset.card_image_of_injective _ hinj, Finset.card_erase_of_mem (Finset.mem_univ j),
      Finset.card_univ, Fintype.card_fin]
  rw [hP, hQ]
  have hj : j.val < N := Fin.is_lt j
  omega

private theorem fruchtGraph_degree_inl_ge (N : ℕ) {G : Type*} [Group G] [DecidableEq G] [Fintype G]
    (e : G ≃ Fin N) (hN : 2 ≤ N) (x : G) :
    2 * N ≤ (fruchtGraph N e).degree (.inl x) := by
  have hN1 : 1 ≤ N := by omega
  have hcardG : Fintype.card G = N := by
    rw [Fintype.card_congr e, Fintype.card_fin]
  have hz_lt : 0 < N := by omega
  have ht_lt : N - 1 < N := by omega
  let z : Fin N := ⟨0, hz_lt⟩
  let t : Fin N := ⟨N - 1, ht_lt⟩
  have hzt : z ≠ t := by
    apply Fin.ne_of_val_ne
    change (0 : ℕ) ≠ N - 1
    omega
  have ht_val : t.val = N - 1 := rfl
  -- sets
  let A : Finset (G ⊕ (G × Fin N)) :=
    (Finset.univ.erase x).image (Sum.inl : G → G ⊕ (G × Fin N))
  let B : Finset (G ⊕ (G × Fin N)) :=
    (Finset.univ.image (fun h : G => (Sum.inr (h, t) : G ⊕ (G × Fin N))))
  let c : G ⊕ (G × Fin N) := Sum.inr (x * (e.symm z)⁻¹, z)
  have hA_sub : A ⊆ (fruchtGraph N e).neighborFinset (.inl x) := by
    intro a ha
    obtain ⟨y, hy, hay⟩ := Finset.mem_image.mp ha
    have hyne : y ≠ x := (Finset.mem_erase.mp hy).1
    rw [SimpleGraph.mem_neighborFinset]
    show (fruchtGraph N e).Adj (.inl x) a
    rw [← hay]
    show (fruchtGraph N e).Adj (.inl x) (.inl y)
    exact Ne.symm hyne
  have hB_sub : B ⊆ (fruchtGraph N e).neighborFinset (.inl x) := by
    intro b hb
    obtain ⟨h, _, hbh⟩ := Finset.mem_image.mp hb
    rw [SimpleGraph.mem_neighborFinset]
    show (fruchtGraph N e).Adj (.inl x) b
    rw [← hbh]
    show (fruchtGraph N e).Adj (.inl x) (.inr (h, t))
    change e (h⁻¹ * x) ≤ t
    rw [Fin.le_iff_val_le_val, ht_val]
    have hlt : (e (h⁻¹ * x)).val < N := Fin.is_lt _
    omega
  have hc_mem : c ∈ (fruchtGraph N e).neighborFinset (.inl x) := by
    rw [SimpleGraph.mem_neighborFinset]
    show (fruchtGraph N e).Adj (.inl x) c
    change e ((x * (e.symm z)⁻¹)⁻¹ * x) ≤ z
    have heq : (x * (e.symm z)⁻¹)⁻¹ * x = e.symm z := by
      rw [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
    rw [heq, Equiv.apply_symm_apply]
  have hAB_disj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    obtain ⟨y, _, hay⟩ := Finset.mem_image.mp ha1
    obtain ⟨h, _, hbh⟩ := Finset.mem_image.mp ha2
    rw [← hay] at hbh
    exact absurd hbh (by simp)
  have hc_not : c ∉ A ∪ B := by
    rw [Finset.mem_union]
    push Not
    constructor
    · intro hcA
      obtain ⟨y, _, hay⟩ := Finset.mem_image.mp hcA
      exact absurd hay (by simp)
    · intro hcB
      obtain ⟨h, _, hbh⟩ := Finset.mem_image.mp hcB
      -- hbh : inr (h,t) = c = inr (x*(..)⁻¹, z)
      have heq : (h, t) = (x * (e.symm z)⁻¹, z) := Sum.inr_injective hbh
      have hprod : h = x * (e.symm z)⁻¹ ∧ t = z := Prod.mk.inj heq
      exact hzt hprod.2.symm
      -- careful: t = z contradicts z ≠ t
  have hsub : insert c (A ∪ B) ⊆ (fruchtGraph N e).neighborFinset (.inl x) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_union] at ha
    cases ha with
    | inl heq => rw [heq]; exact hc_mem
    | inr hun =>
      cases hun with
      | inl haA => exact hA_sub haA
      | inr haB => exact hB_sub haB
  have hcard_le := Finset.card_le_card hsub
  have hdeg : ((fruchtGraph N e).neighborFinset (.inl x)).card =
      (fruchtGraph N e).degree (.inl x) :=
    SimpleGraph.card_neighborFinset_eq_degree _ _
  rw [← hdeg]
  have hcardA : A.card = N - 1 := by
    change ((Finset.univ.erase x).image _).card = _
    rw [Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, hcardG]
  have hcardB : B.card = N := by
    change (Finset.univ.image _).card = _
    have hinj : Function.Injective (fun h : G => (Sum.inr (h, t) : G ⊕ (G × Fin N))) := by
      intro a b hab
      have h2 : (a, t) = (b, t) := Sum.inr_injective hab
      exact (Prod.mk.inj h2).1
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, hcardG]
  have hcardU : (A ∪ B).card = (N - 1) + N := by
    rw [Finset.card_union_of_disjoint hAB_disj, hcardA, hcardB]
  have hcardI : (insert c (A ∪ B)).card = (N - 1) + N + 1 := by
    rw [Finset.card_insert_of_notMem hc_not, hcardU]
  have h2N : (N - 1) + N + 1 = 2 * N := by omega
  rw [hcardI, h2N] at hcard_le
  rw [hdeg] at hcard_le
  exact hcard_le

private theorem fruchtAut_maps_inl (N : ℕ) {G : Type*} [Group G] [DecidableEq G] [Fintype G]
    (e : G ≃ Fin N) (hN : 2 ≤ N) (σ : fruchtGraph N e ≃g fruchtGraph N e) (x : G) :
    ∃ y : G, σ (.inl x) = .inl y := by
  cases hσ : σ (.inl x : G ⊕ (G × Fin N)) with
  | inl y => exact ⟨y, rfl⟩
  | inr p =>
    obtain ⟨h, j'⟩ := p
    exfalso
    have hdeg := fruchtIso_degree_eq (fruchtGraph N e) σ (.inl x)
    rw [hσ, fruchtGraph_degree_inr N e h j'] at hdeg
    have hle := fruchtGraph_degree_inl_ge N e hN x
    have hj : j'.val < N := Fin.is_lt j'
    omega
private theorem fruchtAut_maps_inr (N : ℕ) {G : Type*} [Group G] [DecidableEq G] [Fintype G]
    (e : G ≃ Fin N) (hN : 2 ≤ N) (σ : fruchtGraph N e ≃g fruchtGraph N e) (g : G) (j : Fin N) :
    ∃ h : G, σ (.inr (g, j)) = .inr (h, j) := by
  cases hσ : σ (.inr (g, j) : G ⊕ (G × Fin N)) with
  | inl y =>
    exfalso
    have hdeg := fruchtIso_degree_eq (fruchtGraph N e) σ (.inr (g, j))
    rw [hσ, fruchtGraph_degree_inr N e g j] at hdeg
    have hle := fruchtGraph_degree_inl_ge N e hN y
    have hj : j.val < N := Fin.is_lt j
    omega
  | inr p =>
    obtain ⟨h, j'⟩ := p
    have hdeg := fruchtIso_degree_eq (fruchtGraph N e) σ (.inr (g, j))
    rw [hσ, fruchtGraph_degree_inr N e g j, fruchtGraph_degree_inr N e h j'] at hdeg
    have hjj : j' = j := by
      apply Fin.ext
      omega
    exact ⟨h, by rw [hjj]⟩

private theorem fruchtAut_inr_uniform (N : ℕ) {G : Type*} [Group G] [DecidableEq G] [Fintype G]
    (e : G ≃ Fin N) (hN : 2 ≤ N) (σ : fruchtGraph N e ≃g fruchtGraph N e) (g : G) :
    ∃ h : G, ∀ j : Fin N, σ (.inr (g, j)) = .inr (h, j) := by
  have hN1 : 1 ≤ N := by omega
  let j0 : Fin N := ⟨0, by omega⟩
  obtain ⟨h, hh0⟩ := fruchtAut_maps_inr N e hN σ g j0
  refine ⟨h, fun j => ?_⟩
  obtain ⟨h', hhj⟩ := fruchtAut_maps_inr N e hN σ g j
  by_cases hjj : j = j0
  · subst hjj
    have heq : (Sum.inr (h, j0) : G ⊕ (G × Fin N)) = Sum.inr (h', j0) := by
      rw [← hh0, hhj]
    have hpair : (h, j0) = (h', j0) := Sum.inr_injective heq
    have hhh2 : h = h' := (Prod.mk.inj hpair).1
    rw [hhj, hhh2]
  · have hadj : (fruchtGraph N e).Adj (.inr (g, j0)) (.inr (g, j)) :=
      ⟨rfl, Ne.symm hjj⟩
    have himg := (σ.map_adj_iff (v := (.inr (g, j0) : G ⊕ (G × Fin N)))
      (w := (.inr (g, j) : G ⊕ (G × Fin N)))).symm.mp hadj
    rw [hh0, hhj] at himg
    have hhh : h = h' := himg.1
    rw [hhj, hhh]

private theorem fruchtAut_eq_shift (N : ℕ) {G : Type*} [Group G] [DecidableEq G] [Fintype G]
    (e : G ≃ Fin N) (hN : 2 ≤ N) (σ : fruchtGraph N e ≃g fruchtGraph N e) :
    ∃ a : G, σ = fruchtShiftIso N e a := by
  have hτ_ex : ∀ x : G, ∃ y : G, σ (.inl x : G ⊕ (G × Fin N)) = .inl y :=
    fun x => fruchtAut_maps_inl N e hN σ x
  choose τ hτ using hτ_ex
  have hH_ex : ∀ g : G, ∃ h : G, ∀ j : Fin N,
      σ (.inr (g, j) : G ⊕ (G × Fin N)) = .inr (h, j) :=
    fun g => fruchtAut_inr_uniform N e hN σ g
  choose H hH using hH_ex
  have key : ∀ g x : G, g⁻¹ * x = (H g)⁻¹ * τ x := by
    intro g x
    apply e.injective
    apply eq_of_forall_ge_iff
    intro j
    have hiff := (σ.map_adj_iff (v := (.inl x : G ⊕ (G × Fin N)))
      (w := (.inr (g, j) : G ⊕ (G × Fin N)))).symm
    rw [hτ x, hH g j] at hiff
    exact hiff
  have hτ_eq : ∀ x : G, τ x = H 1 * x := by
    intro x
    have h1 := key 1 x
    rw [inv_one, one_mul] at h1
    -- h1 : x = (H 1)⁻¹ * τ x
    have h2 : (H 1)⁻¹ * τ x = x := h1.symm
    exact eq_mul_of_inv_mul_eq h2
  have hH_eq : ∀ g : G, H g = H 1 * g := by
    intro g
    have hg := key g g
    rw [inv_mul_cancel] at hg
    -- hg : 1 = (H g)⁻¹ * τ g
    have h1 : (H g)⁻¹ * τ g = 1 := hg.symm
    have hHT : H g = τ g := inv_mul_eq_one.mp h1
    rw [hHT, hτ_eq]
  refine ⟨H 1, ?_⟩
  apply RelIso.ext
  intro v
  cases v with
  | inl x =>
    rw [hτ x, hτ_eq x]
    rfl
  | inr p =>
    obtain ⟨g, j⟩ := p
    rw [hH g j, hH_eq g]
    rfl

private noncomputable def fruchtPhi (N : ℕ) {G : Type*} [Group G] [DecidableEq G] [Fintype G]
    (e : G ≃ Fin N) : G → fruchtGraph N e ≃g fruchtGraph N e :=
  fun a => fruchtShiftIso N e a
private noncomputable def fruchtHom (N : ℕ) {G : Type*} [Group G] [DecidableEq G] [Fintype G]
    (e : G ≃ Fin N) : G →* fruchtGraph N e ≃g fruchtGraph N e :=
  MonoidHom.mk' (fruchtPhi N e) (fun a b => RelIso.ext fun x =>
    congrArg (fun p : Equiv.Perm (G ⊕ (G × Fin N)) => p x) (fruchtShift_mul N a b))
private noncomputable def fruchtMulEquiv (N : ℕ) {G : Type*} [Group G] [DecidableEq G] [Fintype G]
    (e : G ≃ Fin N) (hN : 2 ≤ N) : G ≃* fruchtGraph N e ≃g fruchtGraph N e := by
  refine MulEquiv.ofBijective (fruchtHom N e) ?_
  constructor
  · intro a b hab
    have hval2 : fruchtShift N a = fruchtShift N b := congrArg RelIso.toEquiv hab
    have h1 := congrArg (fun p : Equiv.Perm (G ⊕ (G × Fin N)) => p (.inl 1)) hval2
    simp only [fruchtShift_inl, mul_one] at h1
    exact Sum.inl_injective h1
  · intro σ
    obtain ⟨a, ha⟩ := fruchtAut_eq_shift N e hN σ
    exact ⟨a, ha.symm⟩

private theorem graphAutComapForward_adj {V1 : Type*} {W1 : Type*} (f : V1 ≃ W1)
    (Γ : SimpleGraph W1) (σ : (Γ.comap ⇑f) ≃g (Γ.comap ⇑f)) (a b : W1) :
    Γ.Adj a b ↔
      Γ.Adj ((f.permCongr σ.toEquiv) a) ((f.permCongr σ.toEquiv) b) := by
  have e1 : (Γ.comap ⇑f).Adj (f.symm a) (f.symm b) ↔ Γ.Adj a b := by
    rw [SimpleGraph.comap_adj, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have e2 := (σ.map_adj_iff (v := f.symm a) (w := f.symm b)).symm
  have e3 : (Γ.comap ⇑f).Adj (σ (f.symm a)) (σ (f.symm b)) ↔
      Γ.Adj (f (σ (f.symm a))) (f (σ (f.symm b))) :=
    SimpleGraph.comap_adj
  rw [Equiv.permCongr_apply, Equiv.permCongr_apply]
  calc Γ.Adj a b ↔ (Γ.comap ⇑f).Adj (f.symm a) (f.symm b) := e1.symm
    _ ↔ (Γ.comap ⇑f).Adj (σ (f.symm a)) (σ (f.symm b)) := e2
    _ ↔ Γ.Adj (f (σ (f.symm a))) (f (σ (f.symm b))) := e3

private theorem graphAutComapBackward_adj {V1 : Type*} {W1 : Type*} (f : V1 ≃ W1)
    (Γ : SimpleGraph W1) (τ : Γ ≃g Γ) (a b : V1) :
    (Γ.comap ⇑f).Adj a b ↔
      (Γ.comap ⇑f).Adj ((f.symm.permCongr τ.toEquiv) a)
        ((f.symm.permCongr τ.toEquiv) b) := by
  have e1 : (Γ.comap ⇑f).Adj a b ↔ Γ.Adj (f a) (f b) := SimpleGraph.comap_adj
  have e2 := (τ.map_adj_iff (v := f a) (w := f b)).symm
  have hperm : ∀ x : V1, (f.symm.permCongr τ.toEquiv) x = f.symm (τ (f x)) := by
    intro x
    simp only [Equiv.permCongr_apply, Equiv.symm_symm, RelIso.coe_fn_toEquiv]
  rw [hperm a, hperm b]
  have e3 : (Γ.comap ⇑f).Adj (f.symm (τ (f a))) (f.symm (τ (f b))) ↔
      Γ.Adj (τ (f a)) (τ (f b)) := by
    rw [SimpleGraph.comap_adj, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  calc (Γ.comap ⇑f).Adj a b ↔ Γ.Adj (f a) (f b) := e1
    _ ↔ Γ.Adj (τ (f a)) (τ (f b)) := e2
    _ ↔ (Γ.comap ⇑f).Adj (f.symm (τ (f a))) (f.symm (τ (f b))) := e3.symm

private noncomputable def graphAutComapToFun {V1 : Type*} {W1 : Type*} (f : V1 ≃ W1)
    (Γ : SimpleGraph W1) : ((Γ.comap ⇑f) ≃g (Γ.comap ⇑f)) → Γ ≃g Γ :=
  fun σ => RelIso.mk (f.permCongr σ.toEquiv)
    (fun {a b} => (graphAutComapForward_adj f Γ σ a b).symm)
private noncomputable def graphAutComapInvFun {V1 : Type*} {W1 : Type*} (f : V1 ≃ W1)
    (Γ : SimpleGraph W1) : (Γ ≃g Γ) → (Γ.comap ⇑f) ≃g (Γ.comap ⇑f) :=
  fun τ => RelIso.mk (f.symm.permCongr τ.toEquiv)
    (fun {a b} => (graphAutComapBackward_adj f Γ τ a b).symm)
private theorem permCongr_roundtrip_left {V1 : Type*} {W1 : Type*} (f : V1 ≃ W1)
    (p : Equiv.Perm V1) :
    f.symm.permCongr (f.permCongr p) = p := by
  apply Equiv.ext
  intro x
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
private theorem permCongr_roundtrip_right {V1 : Type*} {W1 : Type*} (f : V1 ≃ W1)
    (q : Equiv.Perm W1) :
    f.permCongr (f.symm.permCongr q) = q := by
  apply Equiv.ext
  intro x
  simp only [Equiv.permCongr_apply, Equiv.apply_symm_apply, Equiv.symm_symm]
private noncomputable def graphAutComapEquiv {V1 : Type*} {W1 : Type*} (f : V1 ≃ W1)
    (Γ : SimpleGraph W1) : ((Γ.comap ⇑f) ≃g (Γ.comap ⇑f)) ≃* (Γ ≃g Γ) where
  toFun := graphAutComapToFun f Γ
  invFun := graphAutComapInvFun f Γ
  left_inv := by
    intro σ
    apply RelIso.ext
    intro x
    have h := congrArg (fun p : Equiv.Perm V1 => p x)
      (permCongr_roundtrip_left f σ.toEquiv)
    exact h
  right_inv := by
    intro τ
    apply RelIso.ext
    intro x
    have h := congrArg (fun p : Equiv.Perm W1 => p x)
      (permCongr_roundtrip_right f τ.toEquiv)
    exact h
  map_mul' := by
    intro a b
    apply RelIso.ext
    intro x
    have htrans : (a * b).toEquiv = a.toEquiv * b.toEquiv := by
      apply Equiv.ext
      intro y
      rfl
    show (f.permCongr (a * b).toEquiv) x = _
    rw [htrans, Equiv.permCongr_mul, Equiv.Perm.mul_apply]
    rfl

private theorem frucht_of_card_le_one {G : Type*} [Group G] [Fintype G]
    (h : Fintype.card G ≤ 1) :
    ∃ (n : ℕ) (Γ : SimpleGraph (Fin n)), Nonempty (G ≃* (Γ ≃g Γ)) := by
  refine ⟨1, ⊥, ?_⟩
  have hsubG : Subsingleton G := Fintype.card_le_one_iff_subsingleton.mp h
  have huniqG : Unique G := @uniqueOfSubsingleton G hsubG 1
  have hsubP : Subsingleton ((⊥ : SimpleGraph (Fin 1)) ≃g (⊥ : SimpleGraph (Fin 1))) := by
    constructor
    intro a b
    apply RelIso.ext
    intro x
    exact Subsingleton.elim _ _
  have huniqP : Unique ((⊥ : SimpleGraph (Fin 1)) ≃g (⊥ : SimpleGraph (Fin 1))) :=
    @uniqueOfSubsingleton _ hsubP 1
  refine ⟨?_⟩
  haveI := huniqG
  haveI := huniqP
  exact MulEquiv.ofUnique

/--
**Frucht's theorem.** Every finite group is isomorphic to the automorphism group of a finite simple
graph.

Proves `Wanted` entry `frucht`.

Source: R. Frucht, Compositio Math. 6 (1939), 239-250.
-/
theorem frucht
    {G : Type*} [Group G] [Fintype G] [DecidableEq G] :
    ∃ (n : ℕ) (Γ : SimpleGraph (Fin n)), Nonempty (G ≃* (Γ ≃g Γ)) := by
  by_cases h : Fintype.card G ≤ 1
  · exact frucht_of_card_le_one h
  · have hN : 2 ≤ Fintype.card G := by omega
    let N := Fintype.card G
    let e : G ≃ Fin N := Fintype.equivFin G
    let V := G ⊕ (G × Fin N)
    let f : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
    refine ⟨Fintype.card V, (fruchtGraph N e).comap ⇑(f.symm), ?_⟩
    have h1 : G ≃* fruchtGraph N e ≃g fruchtGraph N e := fruchtMulEquiv N e hN
    have h2 : ((fruchtGraph N e).comap ⇑(f.symm)) ≃g ((fruchtGraph N e).comap ⇑(f.symm))
        ≃* fruchtGraph N e ≃g fruchtGraph N e :=
      graphAutComapEquiv (f.symm) (fruchtGraph N e)
    exact ⟨h1.trans h2.symm⟩

end MathlibExt.Combinatorics.SimpleGraph.FruchtWanted
end
