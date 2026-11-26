/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite `p`-groups with `p - 1` conjugacy classes of maximum size (Kourovka Notebook Problem 14.92)

Kourovka Notebook, Archive of Solved Problems, Problem 14.92 (G. Fernández-Alcober): every finite
`p`-group has at least `p - 1` conjugacy classes of maximum size (I. D. Macdonald), who found groups
of order `2ⁿ` with just one. Are there any examples with exactly `p - 1` conjugacy classes of
maximum size for odd `p`?
-/

module

public import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Finite groups with exactly two largest conjugacy classes

This module proves the existence of a finite `3`-group with exactly two conjugacy classes
of maximum size.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.92 (G.
Fernández-Alcober). UnsolvedMath record UM-00701076 (`KOU-14.92`), dataset ulamai/UnsolvedMath
v1.8.0.

The question is read existentially (some odd prime `p` and some finite `p`-group), which is what the
Archive answer "Yes, there are, for `p = 3`" settles; nothing is claimed for every odd `p`. The size
of a class is the cardinality of its carrier. For `p = 2` the trivial group would be an example,
which is why the problem asks about odd `p`.

The witness is the pullback of two copies of a matrix group of order `3^8` along a homomorphism
to the cyclic group of order three. The smallest centralizers in the pullback have order
`3^5`. For each of the two nonzero character values, the elements with this centralizer
order form a single conjugacy class of size `3^10`.
-/

namespace MathlibExt.GroupTheory.PGroupMaxSizeConjugacyClassesKourovka14Problem92Wanted

@[expose] public section

/-- **Number of conjugacy classes of maximum size.** For a group $G$, the number of conjugacy
classes $c$ of $G$ such that every conjugacy class of $G$ has size at most the size of $c$. It is
meant for finite groups: sizes and counts are taken in $\mathbb{N}$, where an infinite set has
size $0$. -/
noncomputable def numMaxSizeConjClasses (G : Type*) [Group G] : ℕ :=
  Nat.card {c : ConjClasses G // ∀ d : ConjClasses G, Nat.card d.carrier ≤ Nat.card c.carrier}

/-- **Odd $p$-groups with $p - 1$ conjugacy classes of maximum size (Kourovka 14.92).** The
statement that there exist an odd prime $p$ and a finite $p$-group with exactly $p - 1$ conjugacy
classes of maximum size. -/
def oddPGroupWithPredMaxSizeConjClasses : Prop :=
  ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ (G : Type) (_ : Group G) (_ : Finite G), IsPGroup p G ∧
    numMaxSizeConjClasses G = p - 1

end

namespace oddPGroupWithPredMaxSizeConjClasses_holds

private abbrev F := ZMod 3

-- The factor in the pullback is a subgroup of the upper unitriangular group of degree five.
-- Its first superdiagonal is (a, b, c, b + c), its second is (u, v, b*c - c^2 - v),
-- its third is (r, s), and its fourth is (t).
@[ext] private structure Block where
  a : F
  b : F
  c : F
  u : F
  v : F
  r : F
  s : F
  t : F

private def Block.d (x : Block) : F := x.b + x.c

private def Block.w (x : Block) : F := x.b * x.c - x.c ^ 2 - x.v

private def Block.mul (x y : Block) : Block where
  a := x.a + y.a
  b := x.b + y.b
  c := x.c + y.c
  u := x.u + y.u + x.a * y.b
  v := x.v + y.v + x.b * y.c
  r := x.r + y.r + (x.a * y.v + x.u * y.c)
  s := x.s + y.s + (x.b * y.w + x.v * y.d)
  t := x.t + y.t + (x.a * y.s + x.u * y.w + x.r * y.d)

private theorem Block.d_mul (x y : Block) : (x.mul y).d = x.d + y.d := by
  simp [Block.d, Block.mul]
  ring

private theorem Block.w_mul (x y : Block) :
    (x.mul y).w = x.w + y.w + x.c * y.d := by
  simp [Block.w, Block.d, Block.mul]
  have h : (3 : F) = 0 := by decide
  linear_combination -x.c * y.c * h

private def Block.one : Block := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

private def Block.inv (x : Block) : Block :=
  let u := -x.u + x.a * x.b
  let v := -x.v + x.b * x.c
  let r := -x.r + x.a * x.v - u * x.c
  ⟨-x.a, -x.b, -x.c, u, v, r, -x.s + x.b * x.w - v * x.d,
    -x.t + x.a * x.s - u * x.w - r * x.d⟩

private instance blockGroup : Group Block where
  mul := Block.mul
  one := Block.one
  inv := Block.inv
  mul_assoc x y z := by
    change (x.mul y).mul z = x.mul (y.mul z)
    have hd := Block.d_mul y z
    have hw := Block.w_mul y z
    ext <;> simp only [Block.mul] at hd hw ⊢
    case s =>
      rw [hw, hd]
      ring
    case t =>
      rw [hw, hd]
      ring
    all_goals ring
  one_mul x := by
    change Block.one.mul x = x
    ext <;> simp [Block.mul, Block.one]
  mul_one x := by
    change x.mul Block.one = x
    ext <;> simp [Block.mul, Block.one, Block.w, Block.d]
  inv_mul_cancel x := by
    change x.inv.mul x = Block.one
    ext <;> simp [Block.mul, Block.inv, Block.one] <;> ring

private def blockEquiv : Block ≃ F × F × F × F × F × F × F × F where
  toFun x := (x.a, x.b, x.c, x.u, x.v, x.r, x.s, x.t)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
    x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance blockFinite : Finite Block := Finite.of_injective _ blockEquiv.injective

private theorem block_card : Nat.card Block = 3 ^ 8 := by
  rw [Nat.card_congr blockEquiv]
  simp

private def head : Block →* Multiplicative (F × F × F) where
  toFun x := Multiplicative.ofAdd (x.a, x.b, x.c)
  map_one' := rfl
  map_mul' _ _ := rfl

private def character : Block →* Multiplicative F where
  toFun x := Multiplicative.ofAdd (x.a + x.b)
  map_one' := rfl
  map_mul' x y := by
    change (x.a + y.a) + (x.b + y.b) = (x.a + x.b) + (y.a + y.b)
    ac_rfl

private abbrev centralizer {G : Type*} [Group G] (x : G) :=
  Subgroup.centralizer ({x} : Set G)

private theorem mem_centralizer {G : Type*} [Group G] {x y : G} :
    y ∈ centralizer x ↔ Commute x y := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact ⟨Commute.symm, Commute.symm⟩

private theorem commute_block (x y : Block) : Commute x y ↔
    x.a * y.b = y.a * x.b ∧
    x.b * y.c = y.b * x.c ∧
    x.a * y.v + x.u * y.c = y.a * x.v + y.u * x.c ∧
    x.b * y.w + x.v * y.d = y.b * x.w + y.v * x.d ∧
    x.a * y.s + x.u * y.w + x.r * y.d = y.a * x.s + y.u * x.w + y.r * x.d := by
  change x.mul y = y.mul x ↔ _
  rw [Block.ext_iff]
  simp only [Block.mul]
  rw [add_comm y.a x.a, add_comm y.b x.b, add_comm y.c x.c, add_comm y.u x.u,
    add_comm y.v x.v, add_comm y.r x.r, add_comm y.s x.s, add_comm y.t x.t]
  simp

private def tail (u v r s t : F) : Block := ⟨0, 0, 0, u, v, r, s, t⟩

private theorem commute_tail (x : Block) (u v r s t : F) :
    Commute x (tail u v r s t) ↔
      x.a * v = u * x.c ∧ (x.b + x.d) * v = 0 ∧
      x.a * s - x.d * r = x.u * v + x.w * u := by
  simp only [commute_block, tail, Block.d, Block.w, zero_mul, mul_zero, zero_add,
    zero_pow (by decide : (2 : ℕ) ≠ 0), sub_self, zero_sub, mul_neg, add_zero, true_and]
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨h₁, by linear_combination -h₂, by linear_combination h₃⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨h₁, by linear_combination -h₂, by linear_combination h₃⟩

private def centralizerHead (x : Block) : centralizer x →* Multiplicative (F × F × F) :=
  head.comp (centralizer x).subtype

private def HasMinimalCentralizer (x : Block) : Prop := x.a ≠ 0 ∧ x.b ≠ 0 ∧ x.c = -x.b

private theorem head_one_iff (y : Block) : head y = 1 ↔ y.a = 0 ∧ y.b = 0 ∧ y.c = 0 := by
  change (y.a, y.b, y.c) = (0, 0, 0) ↔ _
  simp

private def centralizingTail (x : Block) (u v r s t : F) (h : Commute x (tail u v r s t)) :
    (centralizerHead x).ker :=
  ⟨⟨tail u v r s t, mem_centralizer.mpr h⟩, rfl⟩

private theorem minimal_d {x : Block} (h : HasMinimalCentralizer x) : x.d = 0 := by
  simp [Block.d, h.2.2]

private theorem head_of_minimal {x y : Block} (hx : HasMinimalCentralizer x) (hxy : Commute x y) :
    ∃ k : F, (y.a, y.b, y.c) = (k * x.a, k * x.b, k * x.c) := by
  have h := (commute_block x y).mp hxy
  refine ⟨y.b / x.b, Prod.ext ?_ (Prod.ext ?_ ?_)⟩
  · change y.a = y.b / x.b * x.a
    rw [div_mul_eq_mul_div, eq_div_iff hx.2.1]
    linear_combination -h.1
  · exact (div_mul_cancel₀ _ hx.2.1).symm
  · change y.c = y.b / x.b * x.c
    rw [div_mul_eq_mul_div, eq_div_iff hx.2.1]
    linear_combination h.2.1

private theorem character_of_commute_of_minimal {x y : Block} (hx : HasMinimalCentralizer x)
    (hz : character x = 1) (hxy : Commute x y) : character y = 1 := by
  obtain ⟨k, hk⟩ := head_of_minimal hx hxy
  change x.a + x.b = 0 at hz
  change y.a + y.b = 0
  have heq := congrArg (fun v : F × F × F ↦ v.1 + v.2.1) hk
  change y.a + y.b = k * x.a + k * x.b at heq
  rw [heq, ← mul_add, hz, mul_zero]

private theorem tail_card_of_minimal {x : Block} (hx : HasMinimalCentralizer x) :
    Nat.card (centralizerHead x).ker = 9 := by
  let equivalence : (centralizerHead x).ker ≃ F × F :=
    { toFun := fun y ↦ (y.1.1.r, y.1.1.t)
      invFun := fun (r, t) ↦ centralizingTail x 0 0 r 0 t
        ((commute_tail ..).mpr (by simp [minimal_d hx]))
      left_inv := by
        intro y
        have hhead : head y.1.1 = 1 := y.2
        obtain ⟨ha, hb, hc⟩ := head_one_iff _ |>.mp hhead
        have hy : y.1.1 = tail y.1.1.u y.1.1.v y.1.1.r y.1.1.s y.1.1.t := by
          ext <;> simp [tail, ha, hb, hc]
        have hcomm := mem_centralizer.mp y.1.2
        rw [hy] at hcomm
        obtain ⟨hu, hv, hs⟩ := (commute_tail ..).mp hcomm
        have hv₀ : y.1.1.v = 0 := by simpa [minimal_d hx, hx.2.1] using hv
        have hu₀ : y.1.1.u = 0 := by simpa [hv₀, hx.2.2, hx.2.1] using hu.symm
        have hs₀ : y.1.1.s = 0 := by simpa [minimal_d hx, hu₀, hv₀, hx.1] using hs
        apply Subtype.ext (Subtype.ext _)
        simpa [hu₀, hv₀, hs₀, centralizingTail] using hy.symm
      right_inv := fun _ ↦ rfl }
  rw [Nat.card_congr equivalence]
  simp

private theorem field_values : ∀ u v : F, u ≠ 0 → v = 0 ∨ v = u ∨ v = u + u := by
  decide

private theorem surjective_of_character_ne_one {G : Type*} [Group G]
    (f : G →* Multiplicative F) {x : G} (hx : f x ≠ 1) : Function.Surjective f := by
  intro v
  rcases field_values (f x).toAdd v.toAdd hx with h | h | h
  · exact ⟨1, (map_one f).trans h.symm⟩
  · exact ⟨x, h.symm⟩
  · exact ⟨x * x, (map_mul f x x).trans h.symm⟩

private theorem head_card_of_minimal {x : Block} (hx : HasMinimalCentralizer x) :
    Nat.card (centralizerHead x).range = 3 := by
  let proj : Multiplicative (F × F × F) →* Multiplicative F :=
    { toFun := fun z ↦ Multiplicative.ofAdd z.toAdd.2.1
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  let f := proj.comp (centralizerHead x).range.subtype
  have hinj : Function.Injective f := by
    rintro ⟨u, ⟨y, rfl⟩⟩ ⟨v, ⟨z, rfl⟩⟩ huv
    obtain ⟨k, hk⟩ := head_of_minimal hx (mem_centralizer.mp y.2)
    obtain ⟨l, hl⟩ := head_of_minimal hx (mem_centralizer.mp z.2)
    change y.1.b = z.1.b at huv
    have hkl : k = l := (mul_left_inj' hx.2.1).mp
      ((congrArg (fun v : F × F × F ↦ v.2.1) hk).symm.trans
        (huv.trans (congrArg (fun v : F × F × F ↦ v.2.1) hl)))
    subst l
    exact Subtype.ext (hk.trans hl.symm)
  let x' : centralizer x := ⟨x, mem_centralizer.mpr (Commute.refl x)⟩
  let x'' : (centralizerHead x).range := ⟨centralizerHead x x', ⟨x', rfl⟩⟩
  have hsurj := surjective_of_character_ne_one f (x := x'') hx.2.1
  rw [Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)]
  exact Nat.card_zmod 3

private theorem block_centralizer_card_of_minimal {x : Block} (hx : HasMinimalCentralizer x) :
    Nat.card (centralizer x) = 27 := by
  rw [← Subgroup.card_ker_mul_card_range (centralizerHead x), tail_card_of_minimal hx,
    head_card_of_minimal hx]

private theorem tail_card_ge_of_zero_ad (x : Block) (ha : x.a = 0) (hd : x.d = 0) :
    27 ≤ Nat.card (centralizerHead x).ker := by
  let f (p : F × F × F) := centralizingTail x 0 0 p.1 p.2.1 p.2.2
    ((commute_tail ..).mpr (by simp [ha, hd]))
  have hf : Function.Injective f := by
    intro p q h
    exact Prod.ext (congrArg (fun y ↦ y.1.1.r) h)
      (Prod.ext (congrArg (fun y ↦ y.1.1.s) h) (congrArg (fun y ↦ y.1.1.t) h))
  simpa using Nat.card_le_card_of_injective f hf

private theorem zero_head_centralizer_card {x : Block} (hx : head x = 1) :
    81 ≤ Nat.card (centralizer x) := by
  obtain ⟨ha, hb, hc⟩ := (head_one_iff x).mp hx
  have hd : x.d = 0 := by simp [Block.d, hb, hc]
  obtain ⟨u, v, hn, hcoeff⟩ : ∃ u v : F, (u ≠ 0 ∨ v ≠ 0) ∧ x.u * v + x.w * u = 0 := by
    by_cases hu : x.u = 0
    · exact ⟨0, 1, Or.inr one_ne_zero, by simp [hu]⟩
    · exact ⟨x.u, -x.w, Or.inl hu, by ring⟩
  let f (p : F × F × F × F) : centralizer x :=
    ⟨tail (u * p.1) (v * p.1) p.2.1 p.2.2.1 p.2.2.2,
      mem_centralizer.mpr ((commute_tail ..).mpr
        ⟨by simp [ha, hc], by simp [hb, hd], by
          rw [ha, hd]
          linear_combination -p.1 * hcoeff⟩)⟩
  have hf : Function.Injective f := by
    intro p q h
    refine Prod.ext ?_ (Prod.ext (congrArg (fun y ↦ y.1.r) h)
      (Prod.ext (congrArg (fun y ↦ y.1.s) h) (congrArg (fun y ↦ y.1.t) h)))
    rcases hn with hn | hn
    · exact mul_left_cancel₀ hn (congrArg (fun y ↦ y.1.u) h)
    · exact mul_left_cancel₀ hn (congrArg (fun y ↦ y.1.v) h)
  simpa using Nat.card_le_card_of_injective f hf

-- A free second-superdiagonal coordinate and one free third-superdiagonal coordinate,
-- together with the central coordinate, give at least 27 elements in the kernel.
private theorem tail_card_ge_of_direction (x : Block) {u v : F} (hn : u ≠ 0 ∨ v ≠ 0)
    (hu : x.a * v = u * x.c) (hv : (x.b + x.d) * v = 0) :
    27 ≤ Nat.card (centralizerHead x).ker := by
  have hinj {p q : F} (hu' : u * p = u * q) (hv' : v * p = v * q) : p = q :=
    hn.elim (fun h ↦ mul_left_cancel₀ h hu') (fun h ↦ mul_left_cancel₀ h hv')
  by_cases ha : x.a = 0
  · by_cases hd : x.d = 0
    · exact tail_card_ge_of_zero_ad x ha hd
    let f (p : F × F × F) := centralizingTail x (u * p.1) (v * p.1)
      (-(x.u * (v * p.1) + x.w * (u * p.1)) / x.d) p.2.1 p.2.2
      ((commute_tail ..).mpr
        ⟨by linear_combination p.1 * hu, by rw [← mul_assoc, hv, zero_mul],
          by rw [ha, zero_mul, mul_comm x.d, div_mul_cancel₀ _ hd]; ring⟩)
    have hf : Function.Injective f := by
      intro p q h
      exact Prod.ext (hinj (congrArg (fun z ↦ z.1.1.u) h) (congrArg (fun z ↦ z.1.1.v) h))
        (Prod.ext (congrArg (fun z ↦ z.1.1.s) h) (congrArg (fun z ↦ z.1.1.t) h))
    simpa using Nat.card_le_card_of_injective f hf
  · let f (p : F × F × F) := centralizingTail x (u * p.1) (v * p.1) p.2.1
      ((x.u * (v * p.1) + x.w * (u * p.1) + x.d * p.2.1) / x.a) p.2.2
      ((commute_tail ..).mpr
        ⟨by linear_combination p.1 * hu, by rw [← mul_assoc, hv, zero_mul],
          by rw [mul_comm x.a, div_mul_cancel₀ _ ha]; ring⟩)
    have hf : Function.Injective f := by
      intro p q h
      exact Prod.ext (hinj (congrArg (fun z ↦ z.1.1.u) h) (congrArg (fun z ↦ z.1.1.v) h))
        (Prod.ext (congrArg (fun z ↦ z.1.1.r) h) (congrArg (fun z ↦ z.1.1.t) h))
    simpa using Nat.card_le_card_of_injective f hf

private theorem head_card_ge_of_ne_one {x : Block} (hx : head x ≠ 1) :
    3 ≤ Nat.card (centralizerHead x).range := by
  have hp : IsPGroup 3 (Multiplicative (F × F × F)) :=
    IsPGroup.of_card_dvd_pow (n := 3) (by simp)
  let x' : centralizer x := ⟨x, mem_centralizer.mpr (Commute.refl x)⟩
  let x'' : (centralizerHead x).range := ⟨centralizerHead x x', ⟨x', rfl⟩⟩
  have hne : x'' ≠ 1 := fun h ↦ hx (congrArg Subtype.val h)
  let : Nontrivial (centralizerHead x).range := ⟨⟨x'', 1, hne⟩⟩
  obtain hc | hc := (hp.to_subgroup (centralizerHead x).range).card_eq_or_dvd
  · exact (Finite.one_lt_card.ne' hc).elim
  · exact Nat.le_of_dvd Nat.card_pos hc

-- If b = 0 and c ≠ 0, the centralizer projects onto every head (A, 0, C).
private theorem centralizer_card_ge_of_b_zero {x : Block} (hb : x.b = 0) (hc : x.c ≠ 0) :
    81 ≤ Nat.card (centralizer x) := by
  have hd : x.d = x.c := by simp [Block.d, hb]
  let k (p : F × F) := centralizingTail x 0 0 (x.a * p.1) (x.c * p.1) p.2
    ((commute_tail ..).mpr (by simp only [hd, mul_zero, zero_mul, add_zero, true_and]; ring))
  have hk : Function.Injective k := by
    intro p q h
    exact Prod.ext (mul_left_cancel₀ hc (congrArg (fun z ↦ z.1.1.s) h))
      (congrArg (fun z ↦ z.1.1.t) h)
  have hker : 9 ≤ Nat.card (centralizerHead x).ker := by
    simpa using Nat.card_le_card_of_injective k hk
  let f (a c : F) : centralizer x := by
    let v := x.v * c / x.c
    let u := (x.a * v + x.u * c - a * x.v) / x.c
    let r := (x.u * (-c ^ 2 - v) + x.r * c - a * x.s - u * x.w) / x.c
    refine ⟨⟨a, 0, c, u, v, r, 0, 0⟩, mem_centralizer.mpr ((commute_block ..).mpr ?_)⟩
    simp only [hb, Block.d, Block.w, zero_mul, mul_zero, zero_add, true_and]
    refine ⟨?_, ?_, ?_⟩
    · rw [show u * x.c = _ from div_mul_cancel₀ _ hc]
      ring
    · exact (div_mul_cancel₀ _ hc).symm
    · rw [show r * x.c = _ from div_mul_cancel₀ _ hc]
      simp [Block.w, hb]
  let lift (p : F × F) : (centralizerHead x).range :=
    ⟨centralizerHead x (f p.1 p.2), ⟨_, rfl⟩⟩
  have hinj : Function.Injective lift := by
    intro p q h
    exact Prod.ext (congrArg (fun y ↦ y.1.toAdd.1) h)
      (congrArg (fun y ↦ y.1.toAdd.2.2) h)
  have hrange : 9 ≤ Nat.card (centralizerHead x).range := by
    simpa using Nat.card_le_card_of_injective lift hinj
  rw [← Subgroup.card_ker_mul_card_range (centralizerHead x)]
  exact Nat.mul_le_mul hker hrange

private theorem field_nonzero_cases : ∀ b c : F,
    c ≠ 0 → b + (b + c) ≠ 0 → b = 0 ∨ c = -b := by
  decide

private theorem block_centralizer_card_of_not_minimal {x : Block} (hx : ¬ HasMinimalCentralizer x) :
    81 ≤ Nat.card (centralizer x) := by
  by_cases hhead : head x = 1
  · exact zero_head_centralizer_card hhead
  have hlarge (h : 27 ≤ Nat.card (centralizerHead x).ker) : 81 ≤ Nat.card (centralizer x) := by
    rw [← Subgroup.card_ker_mul_card_range (centralizerHead x)]
    exact Nat.mul_le_mul h (head_card_ge_of_ne_one hhead)
  by_cases hc : x.c = 0
  · exact hlarge (tail_card_ge_of_direction x (u := 1) (v := 0) (Or.inl one_ne_zero)
      (by simp [hc]) (mul_zero _))
  by_cases hs : x.b + x.d = 0
  · exact hlarge (tail_card_ge_of_direction x (Or.inr hc) rfl (by rw [hs, zero_mul]))
  rcases field_nonzero_cases x.b x.c hc hs with hb | hcb
  · exact centralizer_card_ge_of_b_zero hb hc
  · have hb : x.b ≠ 0 := fun h ↦ hc (by simp [h, hcb])
    have ha : x.a = 0 := by
      by_contra hn
      exact hx ⟨hn, hb, hcb⟩
    exact hlarge (tail_card_ge_of_zero_ad x ha (by simp [Block.d, hcb]))

private theorem centralizer_card_ge (x : Block) : 27 ≤ Nat.card (centralizer x) := by
  classical
  by_cases hx : HasMinimalCentralizer x
  · simp [block_centralizer_card_of_minimal hx]
  · exact le_trans (by decide) (block_centralizer_card_of_not_minimal hx)

private def difference : Block × Block →* Multiplicative F :=
  character.comp (MonoidHom.fst Block Block) / character.comp (MonoidHom.snd Block Block)

private abbrev Witness := difference.ker

private theorem mem_witness (x : Block × Block) : x ∈ Witness ↔
    character x.1 = character x.2 :=
  div_eq_one

private theorem witness_card : Nat.card Witness = 3 ^ 15 := by
  let g : Block := ⟨1, 0, 0, 0, 0, 0, 0, 0⟩
  have hsurj := surjective_of_character_ne_one difference (x := (g, 1)) (by decide)
  have h := Subgroup.card_ker_mul_card_of_surjective hsurj
  change Nat.card Witness * Nat.card F = Nat.card (Block × Block) at h
  rw [Nat.card_zmod, Nat.card_prod, block_card] at h
  omega

private def pairCentralizerCharacter (x : Witness) :
    centralizer x.1.1 × centralizer x.1.2 →* Multiplicative F :=
  difference.comp ((centralizer x.1.1).subtype.prodMap (centralizer x.1.2).subtype)

private theorem pairCentralizerCharacter_apply (x : Witness)
    (y : centralizer x.1.1 × centralizer x.1.2) :
    pairCentralizerCharacter x y = character y.1.1 / character y.2.1 := rfl

private def witnessCentralizerEquiv (x : Witness) :
    centralizer x ≃ (pairCentralizerCharacter x).ker where
  toFun y :=
    let h := (mem_centralizer.mp y.2).eq
    ⟨(⟨y.1.1.1, mem_centralizer.mpr (congrArg (fun z : Witness ↦ z.1.1) h)⟩,
        ⟨y.1.1.2, mem_centralizer.mpr (congrArg (fun z : Witness ↦ z.1.2) h)⟩), y.1.2⟩
  invFun y :=
    let z : Witness := ⟨(y.1.1.1, y.1.2.1), y.2⟩
    ⟨z, mem_centralizer.mpr (Subtype.ext (Prod.ext
      (mem_centralizer.mp y.1.1.2).eq (mem_centralizer.mp y.1.2.2).eq))⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def HasLargestClass (x : Witness) : Prop :=
  HasMinimalCentralizer x.1.1 ∧ HasMinimalCentralizer x.1.2 ∧ character x.1.1 ≠ 1

-- In a nonzero fiber, the restricted character is onto: the first component of x
-- commutes with itself. The pullback centralizer has one third of the product order.
private theorem witness_centralizer_card_of_largest {x : Witness} (hx : HasLargestClass x) :
    Nat.card (centralizer x) = 243 := by
  let y : centralizer x.1.1 × centralizer x.1.2 :=
    (⟨x.1.1, mem_centralizer.mpr (Commute.refl _)⟩, 1)
  have hy : pairCentralizerCharacter x y ≠ 1 := by
    simpa [pairCentralizerCharacter_apply, y] using hx.2.2
  have hsurj := surjective_of_character_ne_one (pairCentralizerCharacter x) hy
  have h := Subgroup.card_ker_mul_card_of_surjective hsurj
  rw [← Nat.card_congr (witnessCentralizerEquiv x), Nat.card_prod,
    block_centralizer_card_of_minimal hx.1, block_centralizer_card_of_minimal hx.2.1] at h
  change Nat.card (centralizer x) * Nat.card F = 27 * 27 at h
  rw [Nat.card_zmod] at h
  omega

private theorem witness_centralizer_lower_bound {x : Witness}
    (h : 2187 ≤ Nat.card (centralizer x.1.1) * Nat.card (centralizer x.1.2)) :
    729 ≤ Nat.card (centralizer x) := by
  let f := pairCentralizerCharacter x
  have hr := f.range.card_le_card_group
  change Nat.card f.range ≤ Nat.card F at hr
  rw [Nat.card_zmod] at hr
  have hprod := Subgroup.card_ker_mul_card_range f
  rw [Nat.card_prod] at hprod
  have hc := calc
    2187 ≤ Nat.card (centralizer x.1.1) * Nat.card (centralizer x.1.2) := h
    _ = Nat.card f.ker * Nat.card f.range := hprod.symm
    _ ≤ Nat.card f.ker * 3 := Nat.mul_le_mul_left _ hr
  rw [← Nat.card_congr (witnessCentralizerEquiv x)] at hc
  omega

-- In the zero fiber, two least-order factor centralizers already
-- lie in the character's kernel, so taking their pullback does not reduce the order.
private theorem witness_centralizer_card_of_not_largest {x : Witness} (hx : ¬ HasLargestClass x) :
    729 ≤ Nat.card (centralizer x) := by
  classical
  by_cases hl : HasMinimalCentralizer x.1.1
  · by_cases hr : HasMinimalCentralizer x.1.2
    · have hzero : character x.1.1 = 1 := by
        by_contra h
        exact hx ⟨hl, hr, h⟩
      have hzero' : character x.1.2 = 1 := ((mem_witness x.1).mp x.2).symm.trans hzero
      have htop : (pairCentralizerCharacter x).ker = ⊤ := by
        rw [MonoidHom.ker_eq_top_iff]
        ext y
        rw [pairCentralizerCharacter_apply,
          character_of_commute_of_minimal hl hzero (mem_centralizer.mp y.1.2),
          character_of_commute_of_minimal hr hzero' (mem_centralizer.mp y.2.2)]
        simp
      rw [Nat.card_congr (witnessCentralizerEquiv x), htop, Subgroup.card_top, Nat.card_prod,
        block_centralizer_card_of_minimal hl, block_centralizer_card_of_minimal hr]
    · exact witness_centralizer_lower_bound
        (Nat.mul_le_mul (centralizer_card_ge _) (block_centralizer_card_of_not_minimal hr))
  · exact witness_centralizer_lower_bound
      (Nat.mul_le_mul (block_centralizer_card_of_not_minimal hl) (centralizer_card_ge _))

private theorem class_card_mul_centralizer_card {G : Type*} [Group G] (g : G) :
    Nat.card (ConjClasses.mk g).carrier * Nat.card (centralizer g) = Nat.card G := by
  change Nat.card (conjugatesOf g) * Nat.card (centralizer g) = Nat.card G
  rw [Nat.card_coe_set_eq, ← Subgroup.index_centralizer_eq_ncard, Nat.mul_comm]
  exact Subgroup.card_mul_index _

private theorem class_card_of_largest {x : Witness} (hx : HasLargestClass x) :
    Nat.card (ConjClasses.mk x).carrier = 59049 := by
  have h := class_card_mul_centralizer_card x
  rw [witness_centralizer_card_of_largest hx, witness_card] at h
  omega

private theorem class_card_of_not_largest {x : Witness} (hx : ¬ HasLargestClass x) :
    Nat.card (ConjClasses.mk x).carrier < 59049 := by
  by_contra! h
  have hc := Nat.mul_le_mul h (witness_centralizer_card_of_not_largest hx)
  rw [class_card_mul_centralizer_card, witness_card] at hc
  omega

private abbrev TailCoords := F × F × F × F × F

private def tailCoords (x : Block) : TailCoords := (x.u, x.v, x.r, x.s, x.t)

private def withTail (x : Block) (q : TailCoords) : Block :=
  ⟨x.a, x.b, x.c, q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2⟩

private theorem withTail_eq_of_head_eq {x y : Block} (h : head x = head y) :
    withTail x (tailCoords y) = y := by
  change (x.a, x.b, x.c) = (y.a, y.b, y.c) at h
  simp only [Prod.mk.injEq] at h
  exact Block.ext h.1 h.2.1 h.2.2 rfl rfl rfl rfl rfl

private def fixedHeads (x : Witness) : Set Witness :=
  {y | head y.1.1 = head x.1.1 ∧ head y.1.2 = head x.1.2}

private theorem fixedHeads_card (x : Witness) : Nat.card (fixedHeads x) = 59049 := by
  let equiv : fixedHeads x ≃ TailCoords × TailCoords :=
    { toFun := fun y ↦ (tailCoords y.1.1.1, tailCoords y.1.1.2)
      invFun := fun (p, q) ↦ ⟨⟨(withTail x.1.1 p, withTail x.1.2 q), x.2⟩, rfl, rfl⟩
      left_inv := fun y ↦ Subtype.ext (Subtype.ext
        (Prod.ext (withTail_eq_of_head_eq y.2.1.symm) (withTail_eq_of_head_eq y.2.2.symm)))
      right_inv := fun _ ↦ rfl }
  rw [Nat.card_congr equiv]
  simp

private theorem class_eq_fixedHeads {x : Witness} (hx : HasLargestClass x) :
    (ConjClasses.mk x).carrier = fixedHeads x := by
  apply Set.eq_of_subset_of_ncard_le (ht := Set.toFinite _)
  · intro y hy
    have hxy : IsConj x y := hy
    exact ⟨(isConj_iff_eq.mp
      ((head.comp (MonoidHom.fst Block Block)).comp Witness.subtype |>.map_isConj hxy)).symm,
      (isConj_iff_eq.mp
        ((head.comp (MonoidHom.snd Block Block)).comp Witness.subtype |>.map_isConj hxy)).symm⟩
  · rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, fixedHeads_card, class_card_of_largest hx]

private def witnessCharacter : Witness →* Multiplicative F :=
  (character.comp (MonoidHom.fst Block Block)).comp Witness.subtype

private def representative (k : F) : Witness :=
  let x : Block := ⟨-k, -k, k, 0, 0, 0, 0, 0⟩
  ⟨(x, x), (mem_witness _).mpr rfl⟩

private theorem field_double_neg : ∀ k : F, -k + -k = k := by decide

private theorem representative_character (k : F) :
    witnessCharacter (representative k) = Multiplicative.ofAdd k :=
  field_double_neg k

private theorem representative_has_largest_class {k : F} (hk : k ≠ 0) :
    HasLargestClass (representative k) := by
  have h : HasMinimalCentralizer (representative k).1.1 :=
    ⟨neg_ne_zero.mpr hk, neg_ne_zero.mpr hk, (neg_neg k).symm⟩
  refine ⟨h, h, ?_⟩
  change witnessCharacter (representative k) ≠ 1
  rw [representative_character]
  exact hk

private theorem field_character_head : ∀ a b : F,
    a ≠ 0 → b ≠ 0 → a + b ≠ 0 → a = -(a + b) ∧ b = -(a + b) := by
  decide

private theorem same_minimal_head {x y : Block} (hx : HasMinimalCentralizer x)
    (hy : HasMinimalCentralizer y) (hxne : character x ≠ 1)
    (hxy : character x = character y) : head x = head y := by
  have hyne : character y ≠ 1 := hxy ▸ hxne
  have h₁ := field_character_head x.a x.b hx.1 hx.2.1 hxne
  have h₂ := field_character_head y.a y.b hy.1 hy.2.1 hyne
  have heq : -(x.a + x.b) = -(y.a + y.b) := congrArg (fun z ↦ -z.toAdd) hxy
  have ha := h₁.1.trans (heq.trans h₂.1.symm)
  have hb := h₁.2.trans (heq.trans h₂.2.symm)
  exact Prod.ext ha (Prod.ext hb (hx.2.2.trans ((congrArg Neg.neg hb).trans hy.2.2.symm)))

private theorem conj_of_same_character {x y : Witness} (hx : HasLargestClass x)
    (hy : HasLargestClass y) (hxy : witnessCharacter x = witnessCharacter y) : IsConj x y := by
  change y ∈ (ConjClasses.mk x).carrier
  rw [class_eq_fixedHeads hx]
  have hx' := (mem_witness x.1).mp x.2
  have hy' := (mem_witness y.1).mp y.2
  exact ⟨(same_minimal_head hx.1 hy.1 hx.2.2 hxy).symm,
    (same_minimal_head hx.2.1 hy.2.1 (hx' ▸ hx.2.2) (hx'.symm.trans (hxy.trans hy'))).symm⟩

private theorem class_card_le (x : Witness) : Nat.card (ConjClasses.mk x).carrier ≤ 59049 := by
  classical
  by_cases hx : HasLargestClass x
  · exact (class_card_of_largest hx).le
  · exact (class_card_of_not_largest hx).le

private theorem has_largest_class_iff (x : Witness) :
    HasLargestClass x ↔
      ∀ d : ConjClasses Witness, Nat.card d.carrier ≤ Nat.card (ConjClasses.mk x).carrier :=
  ⟨fun hx d ↦ by
    obtain ⟨y, rfl⟩ := ConjClasses.mk_surjective d
    rw [class_card_of_largest hx]
    exact class_card_le y,
  fun hx ↦ by
    by_contra h
    have hmax := hx (ConjClasses.mk (representative 1))
    rw [class_card_of_largest (representative_has_largest_class one_ne_zero)] at hmax
    exact (not_lt_of_ge hmax) (class_card_of_not_largest h)⟩

-- The two nonzero character values index the largest classes.
private theorem witness_class_count : numMaxSizeConjClasses Witness = 2 := by
  let f (k : {k : F // k ≠ 0}) :
      {c : ConjClasses Witness // ∀ d : ConjClasses Witness,
        Nat.card d.carrier ≤ Nat.card c.carrier} :=
    ⟨ConjClasses.mk (representative k.1),
      (has_largest_class_iff _).mp (representative_has_largest_class k.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro k l h
      have hconj := ConjClasses.mk_eq_mk_iff_isConj.mp (congrArg Subtype.val h)
      have hc := isConj_iff_eq.mp (witnessCharacter.map_isConj hconj)
      rw [representative_character, representative_character] at hc
      exact Subtype.ext hc
    · rintro ⟨c, hc⟩
      obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
      have hx := (has_largest_class_iff x).mpr hc
      let k : {k : F // k ≠ 0} := ⟨(witnessCharacter x).toAdd, hx.2.2⟩
      refine ⟨k, Subtype.ext (ConjClasses.mk_eq_mk_iff_isConj.mpr ?_)⟩
      exact conj_of_same_character (representative_has_largest_class k.2) hx
        (representative_character k.1)
  rw [numMaxSizeConjClasses, ← Nat.card_congr (Equiv.ofBijective f hf),
    Nat.card_eq_fintype_card]
  decide

end oddPGroupWithPredMaxSizeConjClasses_holds

/--
**Some odd $p$-group has exactly $p - 1$ conjugacy classes of maximum size.** There exist an odd
prime $p$ and a finite $p$-group with exactly $p - 1$ conjugacy classes of maximum size.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.92 (G.
Fernández-Alcober); resolution: A. Jaikin-Zapirain, M. F. Newman and E. A. O'Brien, p-groups having
the minimal number of conjugacy classes of maximal size, Israel J. Math. 172 (2009), no. 1, 119-123,
abstract (a 3-group with exactly p - 1 = 2 conjugacy classes of the largest size); Kourovka Archive,
Problem 14.92 (answer: Yes, there are, for p = 3),
http://verso.mat.uam.es/~andrei.jaikin/preprints/articulos.htm.
-/
public theorem oddPGroupWithPredMaxSizeConjClasses_holds :
    oddPGroupWithPredMaxSizeConjClasses := by
  open oddPGroupWithPredMaxSizeConjClasses_holds in
  exact ⟨3, by decide, by decide, Witness, inferInstance, inferInstance,
    IsPGroup.of_card_dvd_pow (n := 15) (by rw [witness_card]), witness_class_count⟩

end MathlibExt.GroupTheory.PGroupMaxSizeConjugacyClassesKourovka14Problem92Wanted
