/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Module.Prod
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Congruence.Hom
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Normal closures and conjugacy in finite 2-groups

We prove `normalClosureConjDerivedAbelian_refuted` using a group of order $2^{13}$.
It is the semidirect product of a seven-dimensional binary vector space by the product
of the quaternion group of order eight and three cyclic groups of order two. Its action
preserves a filtration with successive dimensions $2,2,2,1$.

For each element we identify a quotient in which its image is a central involution or
the identity. The fiber over that image is its conjugacy class. Equal normal closures
therefore force conjugacy, while two explicit commutators fail to commute.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.TwoGroupNormalClosureConjugateKourovka12Problem15Wanted

/-- **Golikova–Starostin question on finite $2$-groups in which normal closures determine
conjugacy (Kourovka 12.15).** The statement that for every finite $2$-group $G$ in which any two
elements with the same normal closure are conjugate, the derived subgroup $G'$ of $G$ is
abelian. -/
def normalClosureConjDerivedAbelian : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsPGroup 2 G →
    (∀ x y : G, Subgroup.normalClosure {x} = Subgroup.normalClosure {y} → IsConj x y) →
    ∀ a ∈ commutator G, ∀ b ∈ commutator G, a * b = b * a

private abbrev F := ZMod 2

-- Quaternion coordinates and the three independent central involutions.
@[ext] private structure Operator where
  i : F
  j : F
  z : F
  p : F
  c : F
  d : F
  deriving DecidableEq

private def compose (a b : Operator) : Operator :=
  ⟨a.i + b.i, a.j + b.j, a.z + b.z + a.i * b.i + a.j * b.i + a.j * b.j,
    a.p + b.p, a.c + b.c, a.d + b.d⟩

private def identity : Operator := ⟨0, 0, 0, 0, 0, 0⟩

private def reverse (a : Operator) : Operator :=
  { a with z := a.z + a.i * a.i + a.j * a.i + a.j * a.j }

private abbrev Plane := F × F
private def turn (s : Plane) : Plane := (s.2, s.1 + s.2)
private def shear (s : Plane) : Plane := (s.1 + s.2, 0)
private abbrev Space := Plane × Plane × Plane × F

-- The four layers of the action have dimensions 2, 2, 2 and 1.
-- In the first three layers, a pair represents an element of the field with four elements.
-- The map `turn` multiplies by a root of X² + X + 1. In normal form the action applies
-- the central generators first, then the second and first quaternion generators.
private def act (a : Operator) (v : Space) : Space :=
  let (s, t, u, r) := v
  let u₀ := u + a.z • s + a.p • turn s
  let r₀ := r + a.z * t.1 + a.p * t.2 + a.c * s.1 + a.d * s.2
  let t₁ := t + a.j • turn s
  let u₁ := u₀ + a.j • (turn (turn t) + shear s)
  let r₁ := r₀ + a.j * u₀.2
  (s, t₁ + a.i • s, u₁ + a.i • t₁, r₁ + a.i * u₁.1)

private theorem two_zero : (2 : F) = 0 := by decide

private theorem bit_sq (x : F) : x ^ 2 = x := by decide +revert

private theorem comp_action (a b : Operator) (v : Space) :
    act (compose a b) v = act a (act b v) := by
  obtain ⟨s, t, u, r⟩ := v
  ext <;> simp [act, compose, turn, shear, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    <;> ring_nf <;> simp [two_zero, bit_sq, show (3 : F) = 1 by decide]
  ring_nf
  simp [two_zero]

@[ext] private structure Element where
  op : Operator
  vec : Space
  deriving DecidableEq

private def product (x y : Element) : Element :=
  ⟨compose x.op y.op, x.vec + act x.op y.vec⟩

private def unit : Element := ⟨identity, 0⟩

private def inverse (x : Element) : Element :=
  ⟨reverse x.op, -act (reverse x.op) x.vec⟩

private theorem act_add (a : Operator) (v w : Space) :
    act a (v + w) = act a v + act a w := by
  obtain ⟨s, t, u, r⟩ := v
  obtain ⟨s', t', u', r'⟩ := w
  ext <;> simp [act, turn, shear, smul_eq_mul] <;> ring

private instance instElementGroup : Group Element where
  mul := product
  one := unit
  inv := inverse
  mul_assoc x y z := by
    change product (product x y) z = product x (product y z)
    apply Element.ext
    · ext <;> simp [product, compose] <;> ring
    · simp [product, comp_action, act_add, add_assoc]
  one_mul x := by
    change product unit x = x
    obtain ⟨h, s, t, u, r⟩ := x
    simp [product, unit, compose, identity, act, turn, shear]
  mul_one x := by
    change product x unit = x
    obtain ⟨h, v⟩ := x
    simp [product, unit, compose, identity, act, turn, shear]
  inv_mul_cancel x := by
    change product (inverse x) x = unit
    obtain ⟨a, v⟩ := x
    simp only [product, compose, inverse, reverse, neg_add_cancel, unit, identity, Element.mk.injEq,
      Operator.mk.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring_nf <;> simp [two_zero]

private def coordEquiv : Element ≃ (F × F × F × F × F × F) × Space where
  toFun | ⟨⟨i, j, z, p, c, d⟩, v⟩ => ((i, j, z, p, c, d), v)
  invFun | ((i, j, z, p, c, d), v) => ⟨⟨i, j, z, p, c, d⟩, v⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance instFiniteElement : Finite Element := Finite.of_equiv _ coordEquiv.symm

private theorem twoGroup : IsPGroup 2 Element := by
  apply IsPGroup.of_card (n := 13)
  rw [Nat.card_congr coordEquiv]
  simp [Space, Plane, F, Nat.card_eq_fintype_card, ZMod.card]

private def params (a b c : Plane) : Operator := ⟨a.1, a.2, b.1, b.2, c.1, c.2⟩
private def mix (a s : Plane) : Plane := a.1 • s + a.2 • turn s
private def mix' (a t : Plane) : Plane := a.1 • t + a.2 • turn (turn t)
private def dot (a s : Plane) : F := a.1 * s.1 + a.2 * s.2
private def bend (a s : Plane) : Plane := a.2 • shear s + (a.1 * a.2) • turn s
private def endTerm (a b s t : Plane) : F :=
  a.2 * (mix b s).2 + a.1 * (mix b s + a.2 • (turn (turn t) + shear s)).1

-- The displacement of (s, t, u, r) is triangular. The last three coordinates can be
-- prescribed successively using the nonsingularity of multiplication in the plane and
-- of its dot pairing. We use this both for translations and for the action on a vector.
private def offset (a b c s t u : Plane) : Space :=
  (0, mix a s, mix' a t + mix b s + bend a s,
    dot a u + dot b t + dot c s + endTerm a b s t)

private theorem act_params (a b c s t u : Plane) (r : F) :
    act (params a b c) (s, t, u, r) = (s, t, u, r) + offset a b c s t u := by
  ext <;> simp [act, params, offset, mix, mix', dot, bend, endTerm, turn, shear,
    smul_eq_mul] <;> ring

private theorem mix_right (a : Plane) (ha : a ≠ 0) : Function.Surjective (mix a) := by
  decide +revert
private theorem mix'_right (a : Plane) (ha : a ≠ 0) : Function.Surjective (mix' a) := by
  decide +revert
private theorem dot_right (a : Plane) (ha : a ≠ 0) : Function.Surjective (dot a) := by
  decide +revert
private theorem mix_left (s : Plane) (hs : s ≠ 0) : Function.Surjective (mix · s) := by
  decide +revert
private theorem mix'_left (s : Plane) (hs : s ≠ 0) : Function.Surjective (mix' · s) := by
  decide +revert
private theorem dot_left (s : Plane) (hs : s ≠ 0) : Function.Surjective (dot · s) := by
  decide +revert

private theorem translation_offsets (a b c T U : Plane) (R : F)
    (ht : a = 0 → T = 0) (hu : a = 0 → b = 0 → U = 0)
    (hr : a = 0 → b = 0 → c = 0 → R = 0) :
    ∃ s t u, offset a b c s t u = (0, T, U, R) := by
  by_cases ha : a = 0
  · subst a
    obtain rfl := ht rfl
    by_cases hb : b = 0
    · subst b
      obtain rfl := hu rfl rfl
      by_cases hc : c = 0
      · subst c
        obtain rfl := hr rfl rfl rfl
        exact ⟨0, 0, 0, rfl⟩
      · obtain ⟨s, hs⟩ := dot_right c hc R
        refine ⟨s, 0, 0, ?_⟩
        simpa [offset, mix, mix', bend, endTerm, dot, turn, shear] using hs
    · obtain ⟨s, hs⟩ := mix_right b hb U
      obtain ⟨t, ht⟩ := dot_right b hb (R - dot c s)
      refine ⟨s, t, 0, ?_⟩
      have hlast : dot b t + dot c s = R := by rw [ht]; abel
      simpa [offset, mix, mix', dot, bend, endTerm, turn, shear] using And.intro hs hlast
  · obtain ⟨s, hs⟩ := mix_right a ha T
    obtain ⟨t, ht⟩ := mix'_right a ha (U - mix b s - bend a s)
    obtain ⟨u, hu⟩ := dot_right a ha (R - dot b t - dot c s - endTerm a b s t)
    refine ⟨s, t, u, ?_⟩
    simp only [offset, hs, ht, hu, Prod.mk.injEq, true_and]
    constructor <;> abel

private theorem operator_offsets (s t u T U : Plane) (R : F)
    (ht : s = 0 → T = 0) (hu : s = 0 → t = 0 → U = 0)
    (hr : s = 0 → t = 0 → u = 0 → R = 0) :
    ∃ a b c, offset a b c s t u = (0, T, U, R) := by
  by_cases hs : s = 0
  · subst s
    obtain rfl := ht rfl
    by_cases ht' : t = 0
    · subst t
      obtain rfl := hu rfl rfl
      by_cases hu' : u = 0
      · subst u
        obtain rfl := hr rfl rfl rfl
        exact ⟨0, 0, 0, rfl⟩
      · obtain ⟨a, ha⟩ := dot_left u hu' R
        exact ⟨a, 0, 0, by simpa [offset, mix, mix', dot, bend, endTerm, turn, shear] using ha⟩
    · obtain ⟨a, ha⟩ := mix'_left t ht' U
      obtain ⟨b, hb⟩ := dot_left t ht' (R - dot a u - endTerm a 0 0 t)
      refine ⟨a, b, 0, ?_⟩
      change dot b t = _ at hb
      have hlast : dot a u + dot b t + endTerm a 0 0 t = R := by rw [hb]; abel
      simpa [offset, mix, mix', dot, bend, endTerm, turn, shear, ← Prod.zero_eq_mk] using
        And.intro ha hlast
  · obtain ⟨a, ha⟩ := mix_left s hs T
    obtain ⟨b, hb⟩ := mix_left s hs (U - mix' a t - bend a s)
    obtain ⟨c, hc⟩ := dot_left s hs (R - dot a u - dot b t - endTerm a b s t)
    refine ⟨a, b, c, ?_⟩
    simp only [offset, ha, hb, hc, Prod.mk.injEq, true_and]
    constructor <;> abel

-- These truncations are group congruences. At the coarsest level only the bottom vector
-- layer and the operator modulo its quaternion commutator survive. The successive
-- refinements restore that commutator, then the other three vector layers in order.
private inductive Level | coarse | first | second | third | full

private def truncate : Level → Element → Element
  | .coarse, ⟨h, s, _, _, _⟩ => ⟨{ h with z := 0 }, s, 0, 0, 0⟩
  | .first, ⟨h, s, _, _, _⟩ => ⟨h, s, 0, 0, 0⟩
  | .second, ⟨h, s, t, _, _⟩ => ⟨h, s, t, 0, 0⟩
  | .third, ⟨h, s, t, u, _⟩ => ⟨h, s, t, u, 0⟩
  | .full, x => x

private def level : Element → Level
  | ⟨h, s, t, u, _⟩ =>
    if (h.i, h.j) ≠ (0 : Plane) then .coarse else
    if s ≠ 0 then .first else
    if (h.z, h.p) ≠ (0 : Plane) ∨ t ≠ 0 then .second else
    if (h.c, h.d) ≠ (0 : Plane) ∨ u ≠ 0 then .third else .full

private theorem truncate_mul (l : Level) (x y : Element) :
    truncate l (x * y) = truncate l (truncate l x * truncate l y) := by cases l <;> rfl

private def congruence (l : Level) : Con Element where
  toSetoid := Setoid.ker (truncate l)
  mul' {x y z w} h k := by
    change truncate l x = truncate l y at h
    change truncate l z = truncate l w at k
    change truncate l (x * z) = truncate l (y * w)
    rw [truncate_mul, h, k, ← truncate_mul]

private def point (a b c s t u : Plane) (r : F) : Element := ⟨params a b c, s, t, u, r⟩

private theorem all_points {P : Element → Prop}
    (h : ∀ a b c s t u r, P (point a b c s t u r)) : ∀ x, P x :=
  fun ⟨⟨i, j, z, p, c, d⟩, s, t, u, r⟩ => h (i, j) (z, p) (c, d) s t u r

private theorem point_level (a b c s t u : Plane) (r : F) :
    level (point a b c s t u r) =
      (if a ≠ 0 then .coarse else if s ≠ 0 then .first else
       if b ≠ 0 ∨ t ≠ 0 then .second else if c ≠ 0 ∨ u ≠ 0 then .third else .full) := rfl

private theorem trunc_laws (x : Element) :
    truncate (level x) (x * x) = truncate (level x) 1 ∧
    ∀ y, truncate (level x) (x * y) = truncate (level x) (y * x) := by
  revert x
  apply all_points
  intro a b c s t u r
  have main : ∀ A B C S T U R, let x := point a b c s t u r
      let y := point A B C S T U R
      truncate (level x) (x * x) = truncate (level x) 1 ∧
        truncate (level x) (x * y) = truncate (level x) (y * x) := by
    intro A B C S T U R
    dsimp only
    simp only [show ∀ x y : Element, x * y = product x y from fun _ _ => rfl,
      show (1 : Element) = unit from rfl]
    rw [point_level]
    split_ifs with ha hs hbt hcu
    all_goals try obtain rfl := not_ne_iff.mp ha
    all_goals try obtain rfl := not_ne_iff.mp hs
    all_goals try
      simp only [not_or, not_ne_iff] at hbt
      obtain ⟨rfl, rfl⟩ := hbt
    all_goals try
      simp only [not_or, not_ne_iff] at hcu
      obtain ⟨rfl, rfl⟩ := hcu
    all_goals
      constructor <;> ext <;> simp [point, truncate, product, params, compose, unit, identity,
        act, turn, shear, smul_eq_mul] <;> ring_nf <;> simp [two_zero]
  exact ⟨(main 0 0 0 0 0 0 0).1, all_points fun A B C S T U R => (main A B C S T U R).2⟩

-- A central involution in a quotient is determined by its normal closure: the preimage
-- of the subgroup it generates consists of two fibers, and the kernel distinguishes them.
private theorem eq_of_normalClosure {G Q : Type*} [Group G] [Group Q] (f : G →* Q)
    {x y : G} (hsq : f x * f x = 1) (hc : ∀ g, f g * f x = f x * f g)
    (h : Subgroup.normalClosure {x} = Subgroup.normalClosure {y}) : f x = f y := by
  let S : Subgroup G :=
    { carrier := {g | f g = 1 ∨ f g = f x}
      one_mem' := Or.inl f.map_one
      mul_mem' := by
        intro g k hg hk
        change f (g * k) = 1 ∨ f (g * k) = f x
        rcases hg with hg|hg <;> rcases hk with hk|hk <;> simp [map_mul, hg, hk, hsq]
      inv_mem' := by
        intro g hg
        change f g⁻¹ = 1 ∨ f g⁻¹ = f x
        rcases hg with hg|hg
        · simp [hg]
        · exact Or.inr (by rw [map_inv, hg, inv_eq_of_mul_eq_one_right hsq]) }
  have : S.Normal := ⟨by
    intro g hg k
    change f (k * g * k⁻¹) = 1 ∨ f (k * g * k⁻¹) = f x
    rcases hg with hg|hg
    · simp [hg]
    · right
      rw [map_mul, map_mul, map_inv, hg, hc k, mul_inv_cancel_right]⟩
  have incl : Subgroup.normalClosure {x} ≤ S :=
    Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr (Or.inr rfl))
  rw [h] at incl
  rcases incl (Subgroup.subset_normalClosure (Set.mem_singleton y)) with hy|hy
  · have ker_le : Subgroup.normalClosure {y} ≤ f.ker :=
      Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr hy)
    rw [← h] at ker_le
    exact (ker_le (Subgroup.subset_normalClosure (Set.mem_singleton x)) : f x = 1).trans hy.symm
  · exact hy.symm

private theorem same_trunc {x y : Element}
    (h : Subgroup.normalClosure {x} = Subgroup.normalClosure {y}) :
    truncate (level x) x = truncate (level x) y := by
  let q := congruence (level x)
  obtain ⟨hs, hc⟩ := trunc_laws x
  apply q.eq.mp
  apply eq_of_normalClosure q.mk' _ _ h
  · exact q.eq.mpr hs
  · exact fun g => q.eq.mpr (hc g).symm

private theorem conjugate_of_product {x y : Element} (g : Element)
    (h : product g x = product y g) : IsConj x y :=
  isConj_iff.mpr ⟨g, mul_inv_eq_iff_eq_mul.mpr h⟩

private theorem translation_conj (x : Element) (a b c : Plane) (v : Space) (k : Operator)
    (hk : compose k x.op = compose (params a b c) k)
    (hs : (act k x.vec).1 = v.1)
    (ht : a = 0 → (act k x.vec).2.1 = v.2.1)
    (hu : a = 0 → b = 0 → (act k x.vec).2.2.1 = v.2.2.1)
    (hr : a = 0 → b = 0 → c = 0 → (act k x.vec).2.2.2 = v.2.2.2) :
    IsConj x ⟨params a b c, v⟩ := by
  let d := act k x.vec - v
  obtain ⟨s, t, u, h⟩ := translation_offsets a b c d.2.1 d.2.2.1 d.2.2.2
    (fun ha => sub_eq_zero.mpr (ht ha)) (fun ha hb => sub_eq_zero.mpr (hu ha hb))
    (fun ha hb hc => sub_eq_zero.mpr (hr ha hb hc))
  have hoff : offset a b c s t u = d := by
    rw [h]
    exact Prod.ext (sub_eq_zero.mpr hs).symm rfl
  apply conjugate_of_product ⟨k, s, t, u, 0⟩
  apply Element.ext hk
  change (s, t, u, (0 : F)) + act k x.vec = v + act (params a b c) (s, t, u, 0)
  rw [act_params, hoff]
  dsimp [d]
  abel

private theorem operator_conj (b c s t u : Plane) (r : F) (T U : Plane) (R : F)
    (ht : s = 0 → T = t) (hu : s = 0 → t = 0 → U = u)
    (hr : s = 0 → t = 0 → u = 0 → R = r) :
    IsConj (point 0 b c s t u r) (point 0 b c s T U R) := by
  obtain ⟨A, B, C, h⟩ := operator_offsets s t u (T - t) (U - u) (R - r)
    (fun hs => sub_eq_zero.mpr (ht hs)) (fun hs ht => sub_eq_zero.mpr (hu hs ht))
    (fun hs ht hu => sub_eq_zero.mpr (hr hs ht hu))
  apply conjugate_of_product ⟨params A B C, 0⟩
  apply Element.ext
  · simp [product, point, compose, params, add_comm]
  · change 0 + act (params A B C) (s, t, u, r) = (s, T, U, R) + act (params 0 b c) 0
    rw [act_params, h]
    simp [act, turn, shear]

private theorem twist (a : Plane) (ha : a ≠ 0) (z Z : F) :
    ∃ i j : F, z + i * a.1 + j * a.1 + j * a.2 = Z + a.1 * i + a.2 * i + a.2 * j := by
  decide +revert

private theorem central_translation (b c s t u : Plane) (r : F) (T U : Plane) (R : F)
    (ht : t = T) (hu : b = 0 → u = U) (hr : b = 0 → c = 0 → r = R) :
    IsConj (point 0 b c s t u r) (point 0 b c s T U R) := by
  apply translation_conj _ _ _ _ _ identity
  · simp [point, compose, params, identity]
  · rfl
  · simpa [point, act, identity] using ht
  · simpa [point, act, identity] using hu
  · simpa [point, act, identity] using hr

private theorem params_eq {a b c A B C : Plane} :
    params a b c = params A B C ↔ a = A ∧ b = B ∧ c = C := by
  simp [params, Prod.ext_iff, and_assoc]

-- Each fiber through x at its selected level is a single conjugacy class.
-- A noncentral quaternion component can first be adjusted by its central sign.
-- In the deeper layers either a translation or an operator supplies the displacement.
private theorem class_of_trunc (x y : Element) (h : truncate (level x) x = truncate (level x) y) :
    IsConj x y := by
  revert x y
  apply all_points
  intro a b c s t u r
  apply all_points
  intro A B C S T U R h
  rw [point_level] at h
  split_ifs at h with ha hs hbt hcu
  · change point a (0, b.2) c s 0 0 0 = point A (0, B.2) C S 0 0 0 at h
    simp only [point, Element.mk.injEq, params_eq, Prod.mk.injEq, true_and, and_true] at h
    obtain ⟨⟨rfl, hp, rfl⟩, rfl⟩ := h
    obtain ⟨i, j, hij⟩ := twist a ha b.1 B.1
    apply translation_conj _ _ _ _ _ (params (i, j) 0 0)
    · simp only [compose, params, Prod.fst_zero, Prod.snd_zero, point, hp, zero_add, hij, add_zero,
        Operator.mk.injEq, and_self, and_true]
      exact ⟨add_comm .., add_comm ..⟩
    · rfl
    all_goals exact fun h => (ha h).elim
  · change point a b c s 0 0 0 = point A B C S 0 0 0 at h
    simp only [point, Element.mk.injEq, params_eq, Prod.mk.injEq, and_true] at h
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
    have := not_ne_iff.mp ha
    subst a
    apply operator_conj <;> intro he <;> contradiction
  · change point a b c s t 0 0 = point A B C S T 0 0 at h
    simp only [point, Element.mk.injEq, params_eq, Prod.mk.injEq, and_true] at h
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩ := h
    have := not_ne_iff.mp ha
    subst a
    rcases hbt with hb|ht
    · apply central_translation _ _ _ _ _ _ _ _ _ rfl <;> intro he <;> contradiction
    · apply operator_conj _ _ _ _ _ _ _ _ _ (fun _ => rfl) <;> intro _ he <;> contradiction
  · change point a b c s t u 0 = point A B C S T U 0 at h
    simp only [point, Element.mk.injEq, params_eq, Prod.mk.injEq, and_true] at h
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl⟩ := h
    have := not_ne_iff.mp ha
    subst a
    rcases hcu with hc|hu
    · apply central_translation _ _ _ _ _ _ _ _ _ rfl (fun _ => rfl)
      intro _ he
      contradiction
    · apply operator_conj _ _ _ _ _ _ _ _ _ (fun _ => rfl) (fun _ _ => rfl)
      intro _ _ he
      contradiction
  · change point a b c s t u r = point A B C S T U R at h
    rw [h]


open scoped commutatorElement

/--
**Equal normal closures forcing conjugacy does not make the derived subgroup of a finite $2$-group
abelian (Kourovka 12.15).** There exists a finite $2$-group $G$ in which any two elements with the
same normal closure are conjugate, but whose derived subgroup $G'$ is not abelian.

Muliarchyk gives an explicit such group of order $2^{11} = 2048$, given by a power-commutator
presentation, whose second derived subgroup $G'' = (G')'$ is nontrivial (a ChatGPT-assisted
construction with a symbolic proof); the Kourovka Notebook (21st issue) marks 12.15 solved, "No,
not always".

Source: E. I. Khukhro and
V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Problem 12.15 (E. A. Golikova, A. I. Starostin); resolution: K.
Muliarchyk, An explicit counterexample to Kourovka Notebook Problem 12.15, preprint (13 August
2026), main result: an explicit group of order `2¹¹ = 2048`, given by a power-commutator
presentation, satisfies the hypothesis and has `G'' = ⟨z⟩ ≠ 1`; the Kourovka Notebook (21st issue)
marks 12.15 solved,
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/08/kourovka_12_15_counterexample.pdf.
-/
theorem normalClosureConjDerivedAbelian_refuted : ¬ normalClosureConjDerivedAbelian := by
  intro hall
  let i := point (1, 0) 0 0 0 0 0 0
  let j := point (0, 1) 0 0 0 0 0 0
  let v := point 0 0 0 (1, 0) 0 0 0
  have mem (x y : Element) : ⁅x, y⁆ ∈ commutator Element :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hc := hall Element twoGroup (fun x y h => class_of_trunc x y (same_trunc h))
  exact (by decide : ⁅i, j⁆ * ⁅i, v⁆ ≠ ⁅i, v⁆ * ⁅i, j⁆) (hc _ (mem i j) _ (mem i v))

end MathlibExt.GroupTheory.TwoGroupNormalClosureConjugateKourovka12Problem15Wanted
