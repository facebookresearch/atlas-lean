/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.PGroup
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.Abel

/-!
# Prescribed conjugacy class sizes of finite p-groups

The Cossey–Hawkes theorem realizes every finite set of powers of a prime `p` containing one
as the set of conjugacy class sizes of a finite `p`-group. We use a group of triples with a
bilinear multiplication term. Its values on individual blocks fill nested coordinate subspaces,
so the largest active block determines a class size.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.PGroupConjugacyClassSizesKourovka14Problem77Wanted

/-- **Prescribed sets of conjugacy class sizes of finite p-groups (Kourovka 14.77).** The
statement that for every prime $p$ and every finite set $X$ of natural numbers that contains $1$
and consists of powers of $p$, there is a finite $p$-group $G$ whose set of conjugacy class sizes
$\{|C| : C \text{ a conjugacy class of } G\}$ equals $X$. -/
def everyPowerSetIsClassSizeSet : Prop :=
  ∀ p : ℕ, p.Prime → ∀ X : Finset ℕ, 1 ∈ X → (∀ x ∈ X, ∃ k : ℕ, x = p ^ k) →
    ∃ (G : Type) (_ : Group G) (_ : Finite G), IsPGroup p G ∧
      Set.range (fun c : ConjClasses G => Nat.card c.carrier) = (X : Set ℕ)

section Construction

variable {ι F R : Type} {n : ℕ} [Fintype ι] [Field F] [AddCommGroup R]
variable (d : ι → ℕ) (e : F ≃+ (Fin n → R))

-- Block i contributes only to the first d i coordinates of the center.
private def pairing (x y : ι → F) : Fin n → R :=
  fun j ↦ ∑ i, if j.val < d i then e (x i * y i) j else 0

private theorem pairing_add_left (x y z : ι → F) :
    pairing d e (x + y) z = pairing d e x z + pairing d e y z := by
  funext j
  simp [pairing, add_mul, ite_add_zero, Finset.sum_add_distrib]

private theorem pairing_add_right (x y z : ι → F) :
    pairing d e x (y + z) = pairing d e x y + pairing d e x z := by
  funext j
  simp [pairing, mul_add, ite_add_zero, Finset.sum_add_distrib]

private theorem pairing_neg_left (x y : ι → F) :
    pairing d e (-x) y = -pairing d e x y := by
  funext j
  simp [pairing, ← Finset.sum_neg_distrib, neg_ite]

private theorem pairing_neg_right (x y : ι → F) :
    pairing d e x (-y) = -pairing d e x y := by
  funext j
  simp [pairing, ← Finset.sum_neg_distrib, neg_ite]

private structure BlockGroup (d : ι → ℕ) (e : F ≃+ (Fin n → R)) where
  x : ι → F
  y : ι → F
  z : Fin n → R

private def compose (a b : BlockGroup d e) : BlockGroup d e :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z + pairing d e a.x b.y⟩

private instance instBlockGroup : Group (BlockGroup d e) where
  mul := compose d e
  one := ⟨0, 0, 0⟩
  inv a := ⟨-a.x, -a.y, pairing d e a.x a.y - a.z⟩
  mul_assoc a b c := by
    change compose d e (compose d e a b) c = compose d e a (compose d e b c)
    simp [compose, pairing_add_left, pairing_add_right, add_left_comm, add_comm]
  one_mul a := by
    change compose d e ⟨0, 0, 0⟩ a = a
    have h : pairing d e 0 a.y = 0 := by funext j; simp [pairing]
    simp [compose, h]
  mul_one a := by
    change compose d e a ⟨0, 0, 0⟩ = a
    have h : pairing d e a.x 0 = 0 := by funext j; simp [pairing]
    simp [compose, h]
  inv_mul_cancel a := by
    change compose d e ⟨-a.x, -a.y, pairing d e a.x a.y - a.z⟩ a = ⟨0, 0, 0⟩
    simp [compose, pairing_neg_left, sub_eq_add_neg, add_assoc]

private theorem conjugate (a b : BlockGroup d e) :
    b * a * b⁻¹ = ⟨a.x, a.y, a.z + (pairing d e b.x a.y - pairing d e a.x b.y)⟩ := by
  change BlockGroup.mk ((b.x + a.x) + -b.x) ((b.y + a.y) + -b.y)
    ((b.z + a.z + pairing d e b.x a.y) + (pairing d e b.x b.y - b.z) +
      pairing d e (b.x + a.x) (-b.y)) = _
  rw [pairing_neg_right, pairing_add_left]
  congr 1 <;> abel

private def blockEquiv : BlockGroup d e ≃ (ι → F) × (ι → F) × (Fin n → R) where
  toFun a := (a.x, a.y, a.z)
  invFun a := ⟨a.1, a.2.1, a.2.2⟩

-- A conjugator supported in one active block can produce any field element there.
private theorem block_shift (a : BlockGroup d e) (i : ι) (hi : a.x i ≠ 0 ∨ a.y i ≠ 0)
    (v : F) : IsConj a ⟨a.x, a.y, a.z + fun j ↦ if j.val < d i then e v j else 0⟩ := by
  classical
  obtain ⟨s, t, h⟩ : ∃ s t : F, s * a.y i - a.x i * t = v := by
    rcases hi with hx | hy
    · exact ⟨0, -v / a.x i, by simp [mul_comm (a.x i), hx]⟩
    · exact ⟨v / a.y i, 0, by simp [hy]⟩
  let b : BlockGroup d e := ⟨Pi.single i s, Pi.single i t, 0⟩
  refine isConj_iff.mpr ⟨b, ?_⟩
  rw [conjugate]
  congr 2
  funext j
  change (∑ l, if j.val < d l then e ((Pi.single i s : ι → F) l * a.y l) j else 0) -
    (∑ l, if j.val < d l then e (a.x l * (Pi.single i t : ι → F) l) j else 0) = _
  rw [Finset.sum_eq_single i, Finset.sum_eq_single i]
  · by_cases hj : j.val < d i <;> simp [hj, ← h, map_sub]
  · intro l _ hl
    simp [Pi.single_eq_of_ne hl]
  · simp
  · intro l _ hl
    simp [Pi.single_eq_of_ne hl]
  · simp

private def pad {k : ℕ} (u : Fin k → R) (j : Fin n) : R :=
  if h : j.val < k then u ⟨j.val, h⟩ else 0

-- The conjugates are exactly the translates by the first k central coordinates.
private theorem class_card (a : BlockGroup d e) (k : ℕ) (hkn : k ≤ n)
    (hbound : ∀ i, k < d i → a.x i = 0 ∧ a.y i = 0)
    (hactive : k = 0 ∨ ∃ i, d i = k ∧ (a.x i ≠ 0 ∨ a.y i ≠ 0)) :
    Nat.card (ConjClasses.mk a).carrier = Nat.card R ^ k := by
  let shift (u : Fin k → R) : BlockGroup d e := ⟨a.x, a.y, a.z + pad u⟩
  have hinj : Function.Injective shift := by
    intro u v huv
    funext j
    have he := congrArg (fun g : BlockGroup d e ↦ g.z (j.castLE hkn)) huv
    simpa [shift, pad, j.isLt] using he
  have hr : (ConjClasses.mk a).carrier = Set.range shift := by
    ext g
    change IsConj a g ↔ _
    constructor
    · rintro h
      obtain ⟨b, rfl⟩ := isConj_iff.mp h
      rw [conjugate]
      let w := pairing d e b.x a.y - pairing d e a.x b.y
      refine ⟨fun j ↦ w (j.castLE hkn), ?_⟩
      suffices hw : pad (fun j : Fin k ↦ w (j.castLE hkn)) = w by
        change BlockGroup.mk _ _ (a.z + _) = BlockGroup.mk _ _ (a.z + w)
        rw [hw]
      funext j
      by_cases hj : j.val < k
      · simp [pad, hj]
      · have vanish (x y : ι → F) (hz : ∀ i, k < d i → x i * y i = 0) :
            pairing d e x y j = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          split_ifs with h
          · simp [hz i (by omega)]
          · rfl
        have h₁ := vanish b.x a.y fun i h ↦ by rw [(hbound i h).2, mul_zero]
        have h₂ := vanish a.x b.y fun i h ↦ by rw [(hbound i h).1, zero_mul]
        simp [pad, hj, w, h₁, h₂]
    · rintro ⟨u, rfl⟩
      rcases hactive with rfl | ⟨i, hi, ha⟩
      · have hz : (pad u : Fin n → R) = 0 := by funext j; simp [pad]
        simpa only [shift, hz, add_zero] using IsConj.refl a
      · have he := block_shift d e a i ha (e.symm (pad u))
        have hp : (fun j : Fin n ↦ if j.val < k then pad u j else 0) = pad u := by
          funext j
          by_cases hj : j.val < k <;> simp [hj, pad]
        simpa only [hi, e.apply_symm_apply, hp, shift] using he
  rw [hr, Nat.card_range_of_injective hinj, Nat.card_fun, Nat.card_fin]

end Construction

/--
**Cossey–Hawkes theorem on conjugacy class sizes of p-groups.** For every prime $p$ and every
finite set $X$ of natural numbers that contains $1$ and consists of powers of $p$, there is a
finite $p$-group whose set of conjugacy class sizes is exactly $X$. This answers Kourovka
Problem 14.77 (Sangroniz) in the affirmative.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.77
(J. Sangroniz); resolution: J. Cossey and T. Hawkes, Proc. Amer. Math. Soc. 128 (2000), no. 1,
49-51, Kourovka Archive, Problem 14.77 (answer: Yes, it is).
-/
theorem everyPowerSetIsClassSizeSet_holds : everyPowerSetIsClassSizeSet := by
  classical
  intro p hp X h1 hX
  let : Fact p.Prime := ⟨hp⟩
  choose d hd using fun i : X ↦ hX i i.property
  let n := Finset.univ.sup d + 1
  have hn : n ≠ 0 := Nat.succ_ne_zero _
  have hdle (i : X) : d i ≤ n := (Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_succ _)
  let F := GaloisField p n
  let e : F ≃+ (Fin n → ZMod p) :=
    (Module.finBasisOfFinrankEq (ZMod p) F (GaloisField.finrank p hn)).equivFun.toAddEquiv
  let G := BlockGroup d e
  let : Finite G := Finite.of_equiv _ (blockEquiv d e).symm
  refine ⟨G, inferInstance, inferInstance, IsPGroup.iff_card.mpr ?_, ?_⟩
  · refine ⟨n * Nat.card X + (n * Nat.card X + n), ?_⟩
    rw [Nat.card_congr (blockEquiv d e)]
    simp [Nat.card_prod, Nat.card_fun, F, GaloisField.card p n hn, pow_add, pow_mul]
  · ext m
    constructor
    · rintro ⟨c, rfl⟩
      obtain ⟨a, rfl⟩ := ConjClasses.mk_surjective c
      change Nat.card (ConjClasses.mk a).carrier ∈ X
      let s := Finset.univ.filter fun i ↦ a.x i ≠ 0 ∨ a.y i ≠ 0
      have hs (i : X) : i ∈ s ↔ a.x i ≠ 0 ∨ a.y i ≠ 0 := by simp [s]
      have hz (i : X) (hi : i ∉ s) : a.x i = 0 ∧ a.y i = 0 := by
        simpa [hs, not_or] using hi
      by_cases hne : s.Nonempty
      · obtain ⟨i, hi, hmax⟩ := s.exists_max_image d hne
        have hb (l : X) (hl : d i < d l) := hz l fun h ↦ hl.not_ge (hmax l h)
        rw [class_card d e a (d i) (hdle i) hb (.inr ⟨i, rfl, (hs i).mp hi⟩),
          Nat.card_zmod, ← hd i]
        exact i.property
      · rw [class_card d e a 0 (Nat.zero_le _) (fun i _ ↦ hz i fun h ↦ hne ⟨i, h⟩)
            (.inl rfl), pow_zero]
        exact h1
    · intro hm
      let i : X := ⟨m, hm⟩
      let a : G := ⟨Pi.single i 1, 0, 0⟩
      refine ⟨ConjClasses.mk a, ?_⟩
      change Nat.card (ConjClasses.mk a).carrier = m
      have hb (l : X) (hl : d i < d l) : a.x l = 0 ∧ a.y l = 0 := by
        have hli : l ≠ i := fun h ↦ hl.ne (h ▸ rfl)
        simp [a, Pi.single_eq_of_ne hli]
      have ha : a.x i ≠ 0 := by simp [a]
      rw [class_card d e a (d i) (hdle i) hb (.inr ⟨i, rfl, .inl ha⟩), Nat.card_zmod]
      exact (hd i).symm

end MathlibExt.GroupTheory.PGroupConjugacyClassSizesKourovka14Problem77Wanted
