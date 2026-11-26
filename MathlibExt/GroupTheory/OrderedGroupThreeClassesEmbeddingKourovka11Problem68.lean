/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Finsupp.Lex
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Embedding ordered groups into ordered groups with three classes (Kourovka Notebook Problem 11.68)

Kourovka Notebook, Archive of Solved Problems, Problem 11.68 (B. Neumann): can every fully ordered
group be embedded in a fully ordered group (continuing the given order) with only 3 classes of
conjugate elements?

The theorem `orderedEmbedsInThreeClasses_refuted` gives a counterexample using a dilation
that cannot acquire a square root in any bi-ordered overgroup.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.68 (B.
Neumann). UnsolvedMath record UM-00700760 (`KOU-11.68`), dataset ulamai/UnsolvedMath v1.8.0.

A fully ordered group is a group with a two-sided invariant linear order: Mathlib's `MulLeftMono`
and `MulRightMono` (`a ≤ b` implies `c * a ≤ c * b` and `a * c ≤ b * c`). "Continuing the given
order" is an order-preserving (strictly monotone, hence injective) homomorphism. "Only 3 classes" is
exactly 3: a nontrivial ordered group has at least the three classes `{1}`, the positive class and
the negative class.
-/

namespace MathlibExt.GroupTheory.OrderedGroupThreeClassesEmbeddingKourovka11Problem68Wanted

/-- **Kourovka Problem 11.68 (ordered groups with three conjugacy classes).** The statement that
for every fully ordered group $G$ there are a fully ordered group $H$ with exactly three conjugacy
classes and a strictly increasing homomorphism $G \to H$ (an order-preserving embedding). Here a
fully ordered group is a group with a linear order $\le$ such that $a \le b$ implies $ca \le cb$
and $ac \le bc$ for all $a$, $b$, $c$. -/
@[expose] public def orderedEmbedsInThreeClasses : Prop :=
  ∀ (G : Type) [Group G] [LinearOrder G] [MulLeftMono G] [MulRightMono G],
    ∃ (H : Type) (_ : Group H) (_ : LinearOrder H), MulLeftMono H ∧ MulRightMono H ∧
      Nat.card (ConjClasses H) = 3 ∧ ∃ f : G →* H, StrictMono f

noncomputable section

/-! We first build a central extension of the free abelian group on the rational line.
Its generators at indices `i` and `j` fail to commute exactly when their distance is a
power of four. Thus both translation and dilation by four preserve the group law. -/

private abbrev V := ℚ →₀ ℤ

private def weight (i j : ℚ) : ℤ :=
  open Classical in if ∃ k : ℤ, j - i = 4 ^ k then 1 else 0

private def pairing (u v : V) : ℤ :=
  u.sum fun i m ↦ m * v.sum (fun j n ↦ n * weight i j)

@[simp] private lemma pairing_zero_left (v : V) : pairing 0 v = 0 := by simp [pairing]
@[simp] private lemma pairing_zero_right (u : V) : pairing u 0 = 0 := by simp [pairing]

private lemma pairing_add_left (u v w : V) :
    pairing (u + v) w = pairing u w + pairing v w := by
  exact Finsupp.sum_add_index' (by simp) (by intros; apply add_mul)

private lemma pairing_add_right (u v w : V) :
    pairing u (v + w) = pairing u v + pairing u w := by
  have h (i : ℚ) := Finsupp.sum_add_index' (f := v) (g := w) (h := fun j n ↦ n * weight i j)
    (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul ..)
  simp only [pairing, h, mul_add, Finsupp.sum_add]

private lemma pairing_neg_left (u v : V) : pairing (-u) v = -pairing u v := by
  have h := pairing_add_left (-u) u v
  simp only [neg_add_cancel, pairing_zero_left] at h
  omega

@[ext] private structure Central where
  vec : V
  center : ℤ

private instance centralGroup : Group Central where
  one := ⟨0, 0⟩
  mul x y := ⟨x.vec + y.vec, x.center + y.center + pairing x.vec y.vec⟩
  inv x := ⟨-x.vec, -x.center + pairing x.vec x.vec⟩
  mul_assoc x y z := by
    apply Central.ext
    · exact add_assoc ..
    · change x.center + y.center + pairing x.vec y.vec + z.center + pairing (x.vec + y.vec) z.vec =
        x.center + (y.center + z.center + pairing y.vec z.vec) + pairing x.vec (y.vec + z.vec)
      rw [pairing_add_left, pairing_add_right]
      abel
  one_mul x := Central.ext (zero_add _) (by change 0 + x.center + pairing 0 x.vec = _; simp)
  mul_one x := Central.ext (add_zero _) (by change x.center + 0 + pairing x.vec 0 = _; simp)
  inv_mul_cancel x := Central.ext (neg_add_cancel _) (by
    change -x.center + pairing x.vec x.vec + x.center + pairing (-x.vec) x.vec = 0
    rw [pairing_neg_left]; abel)

private instance centralOrder : LinearOrder Central :=
  LinearOrder.lift' (fun x : Central ↦ toLex (toLex x.vec, x.center))
    (fun _ _ h ↦ Central.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

private lemma central_lt {x y : Central} :
    x < y ↔ toLex x.vec < toLex y.vec ∨ x.vec = y.vec ∧ x.center < y.center :=
  Prod.Lex.toLex_lt_toLex

private instance centralLeft : MulLeftMono Central where
  elim x {u v} huv := by
    apply StrictMono.monotone (f := (x * ·)) _ huv
    intro y z h
    rcases central_lt.mp h with h | ⟨e, h⟩
    · exact central_lt.mpr (.inl (add_lt_add_right h (toLex x.vec)))
    · apply central_lt.mpr
      exact .inr ⟨congrArg (x.vec + ·) e, by
        change x.center + y.center + pairing x.vec y.vec <
          x.center + z.center + pairing x.vec z.vec
        rw [e]; lia⟩

private instance centralRight : MulRightMono Central where
  elim x {u v} huv := by
    apply StrictMono.monotone (f := (· * x)) _ huv
    intro y z h
    rcases central_lt.mp h with h | ⟨e, h⟩
    · exact central_lt.mpr (.inl (add_lt_add_left h (toLex x.vec)))
    · apply central_lt.mpr
      exact .inr ⟨congrArg (· + x.vec) e, by
        change y.center + x.center + pairing y.vec x.vec <
          z.center + x.center + pairing z.vec x.vec
        rw [e]; lia⟩

/-! The affine group used here consists of the maps `i ↦ 4 ^ k * i + q`. -/

@[ext] private structure Aff where
  exp : ℤ
  shift : ℚ

private instance affGroup : Group Aff where
  one := ⟨0, 0⟩
  mul a b := ⟨a.exp + b.exp, a.shift + 4 ^ a.exp * b.shift⟩
  inv a := ⟨-a.exp, -(4 ^ (-a.exp) * a.shift)⟩
  mul_assoc a b c := by
    apply Aff.ext (add_assoc ..)
    change a.shift + 4 ^ a.exp * b.shift + 4 ^ (a.exp + b.exp) * c.shift =
      a.shift + 4 ^ a.exp * (b.shift + 4 ^ b.exp * c.shift)
    rw [zpow_add₀ (by norm_num : (4 : ℚ) ≠ 0)]
    ring
  one_mul a := Aff.ext (zero_add _) (by change 0 + 4 ^ (0 : ℤ) * a.shift = _; simp)
  mul_one a := Aff.ext (add_zero _) (by change a.shift + 4 ^ a.exp * 0 = _; simp)
  inv_mul_cancel a := Aff.ext (neg_add_cancel _) (neg_add_cancel _)

private instance affOrder : LinearOrder Aff :=
  LinearOrder.lift' (fun a : Aff ↦ toLex (a.exp, a.shift))
    (fun _ _ h ↦ Aff.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

private lemma aff_lt {a b : Aff} : a < b ↔ a.exp < b.exp ∨ a.exp = b.exp ∧ a.shift < b.shift :=
  Prod.Lex.toLex_lt_toLex

private instance affLeft : MulLeftMono Aff where
  elim a {u v} huv := by
    apply StrictMono.monotone (f := (a * ·)) _ huv
    intro b c h
    rcases aff_lt.mp h with h | ⟨e, h⟩
    · exact aff_lt.mpr (.inl (by change a.exp + b.exp < a.exp + c.exp; lia))
    · exact aff_lt.mpr (.inr ⟨congrArg (a.exp + ·) e, by
        change a.shift + 4 ^ a.exp * b.shift < a.shift + 4 ^ a.exp * c.shift
        exact add_lt_add_right (mul_lt_mul_of_pos_left h (zpow_pos (by norm_num) _)) _⟩)

private instance affRight : MulRightMono Aff where
  elim a {u v} huv := by
    apply StrictMono.monotone (f := (· * a)) _ huv
    intro b c h
    rcases aff_lt.mp h with h | ⟨e, h⟩
    · exact aff_lt.mpr (.inl (by change b.exp + a.exp < c.exp + a.exp; lia))
    · exact aff_lt.mpr (.inr ⟨congrArg (· + a.exp) e, by
        change b.shift + 4 ^ b.exp * a.shift < c.shift + 4 ^ c.exp * a.shift
        simpa [e] using h⟩)

private def affineMap (a : Aff) : ℚ ≃o ℚ where
  toFun i := a.shift + 4 ^ a.exp * i
  invFun j := (j - a.shift) / 4 ^ a.exp
  left_inv i := by field_simp; ring
  right_inv j := by field_simp; ring
  map_rel_iff' := by
    intro i j
    change a.shift + 4 ^ a.exp * i ≤ a.shift + 4 ^ a.exp * j ↔ _
    simp [zpow_pos (by norm_num : (0 : ℚ) < 4)]

private lemma weight_affine (a : Aff) (i j : ℚ) :
    weight (affineMap a i) (affineMap a j) = weight i j := by
  have diff : affineMap a j - affineMap a i = 4 ^ a.exp * (j - i) := by
    change a.shift + _ * j - (a.shift + _ * i) = _; ring
  unfold weight
  congr 1
  apply propext
  rw [diff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k - a.exp, ?_⟩
    rw [zpow_sub₀ (by norm_num : (4 : ℚ) ≠ 0), eq_div_iff (zpow_ne_zero _ (by norm_num)), mul_comm]
    exact hk
  · rintro ⟨k, hk⟩
    exact ⟨a.exp + k, by rw [hk, zpow_add₀ (by norm_num : (4 : ℚ) ≠ 0)]⟩

private def reindex (a : Aff) : V ≃+ V := Finsupp.domCongr (affineMap a).toEquiv

private lemma pairing_reindex (a : Aff) (u v : V) :
    pairing (reindex a u) (reindex a v) = pairing u v := by
  simp only [pairing, reindex, Finsupp.domCongr_apply, Finsupp.sum_equivMapDomain,
    OrderIso.coe_toEquiv, weight_affine]

private def act (a : Aff) : Central ≃* Central where
  toFun x := ⟨reindex a x.vec, x.center⟩
  invFun x := ⟨(reindex a).symm x.vec, x.center⟩
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := Central.ext (map_add ..) (by
    change _ = x.center + y.center + pairing (reindex a x.vec) (reindex a y.vec)
    rw [pairing_reindex]; rfl)

private def action : Aff →* MulAut Central where
  toFun := act
  map_one' := by
    have he : (affineMap 1).toEquiv = Equiv.refl ℚ := by
      ext i; change 0 + 4 ^ (0 : ℤ) * i = i; simp
    ext x : 1
    refine Central.ext ?_ rfl
    exact (congrArg (fun e ↦ Finsupp.equivMapDomain e x.vec) he).trans
      (Finsupp.equivMapDomain_refl _)
  map_mul' a b := by
    have he : (affineMap (a * b)).toEquiv =
        (affineMap b).toEquiv.trans (affineMap a).toEquiv := by
      ext i
      change a.shift + 4 ^ a.exp * b.shift + 4 ^ (a.exp + b.exp) * i =
        a.shift + 4 ^ a.exp * (b.shift + 4 ^ b.exp * i)
      rw [zpow_add₀ (by norm_num : (4 : ℚ) ≠ 0)]; ring
    ext x : 1
    refine Central.ext ?_ rfl
    exact (congrArg (fun e ↦ Finsupp.equivMapDomain e x.vec) he).trans
      (Finsupp.equivMapDomain_trans _ _ _)

private lemma act_strictMono (a : Aff) : StrictMono (action a) := by
  intro x y h
  rcases central_lt.mp h with h | ⟨e, h⟩
  · apply central_lt.mpr <| Or.inl ?_
    obtain ⟨i, hi, hi'⟩ := Finsupp.Lex.lt_iff.mp h
    apply Finsupp.Lex.lt_iff.mpr
    refine ⟨affineMap a i, ?_, ?_⟩
    · intro j hj
      exact hi _ ((affineMap a).symm_apply_lt.mpr hj)
    · change x.vec ((affineMap a).symm _) < y.vec ((affineMap a).symm _)
      simpa using hi'
  · exact central_lt.mpr (.inr ⟨congrArg (reindex a) e, h⟩)

/-! Order the semidirect product lexicographically, comparing the affine coordinates first.
Conjugation by a translation shifts the basis indices, while dilation fixes the basis at zero
and sends translation by one to translation by four. -/

private abbrev Witness := Central ⋊[action] Aff

private instance witnessOrder : LinearOrder Witness :=
  LinearOrder.lift' (fun x : Witness ↦ toLex (x.right, x.left))
    (fun _ _ h ↦ SemidirectProduct.ext (congrArg Prod.snd h) (congrArg Prod.fst h))

private lemma witness_lt {x y : Witness} :
    x < y ↔ x.right < y.right ∨ x.right = y.right ∧ x.left < y.left :=
  Prod.Lex.toLex_lt_toLex

private instance witnessLeft : MulLeftMono Witness where
  elim x {u v} huv := by
    apply StrictMono.monotone (f := (x * ·)) _ huv
    intro y z h
    rcases witness_lt.mp h with h | ⟨e, h⟩
    · exact witness_lt.mpr (.inl (mul_lt_mul_right h _))
    · exact witness_lt.mpr (.inr ⟨congrArg (x.right * ·) e,
        mul_lt_mul_right (act_strictMono x.right h) x.left⟩)

private instance witnessRight : MulRightMono Witness where
  elim x {u v} huv := by
    apply StrictMono.monotone (f := (· * x)) _ huv
    intro y z h
    rcases witness_lt.mp h with h | ⟨e, h⟩
    · exact witness_lt.mpr (.inl (mul_lt_mul_left h _))
    · apply witness_lt.mpr <| Or.inr ⟨congrArg (· * x.right) e, ?_⟩
      simp only [SemidirectProduct.mul_left, e]
      exact mul_lt_mul_left h _

private def basis (i : ℚ) : Central := ⟨Finsupp.single i 1, 0⟩
private def gen (i : ℚ) : Witness := SemidirectProduct.inl (basis i)
private def shift (q : ℚ) : Witness := SemidirectProduct.inr (⟨0, q⟩ : Aff)
private def dil : Witness := SemidirectProduct.inr (⟨1, 0⟩ : Aff)

private lemma conj_gen (a : Aff) (i : ℚ) :
    MulAut.conj (SemidirectProduct.inr a : Witness) (gen i) = gen (affineMap a i) := by
  rw [MulAut.conj_apply, gen, ← map_inv, ← SemidirectProduct.inl_aut]
  exact congrArg SemidirectProduct.inl (Central.ext (Finsupp.equivMapDomain_single ..) rfl)

private lemma shift_gen (q : ℚ) : MulAut.conj (shift q) (gen 0) = gen q := by
  rw [shift, conj_gen]
  congr 1
  change q + _ * 0 = q
  simp

private lemma dil_gen : MulAut.conj dil (gen 0) = gen 0 := by
  rw [dil, conj_gen]
  congr 1
  change 0 + _ * 0 = (0 : ℚ)
  simp

private lemma shift_square : shift 1 ^ 2 = shift 2 := by
  rw [shift, ← map_pow]
  apply congrArg SemidirectProduct.inr
  rw [sq]
  exact Aff.ext (by decide) (by change 1 + 4 ^ (0 : ℤ) * 1 = (2 : ℚ); norm_num)

private lemma dil_shift : MulAut.conj dil (shift 1) = shift 1 ^ 4 := by
  simp only [dil, shift, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_pow]
  apply congrArg SemidirectProduct.inr
  have prod (a b : Aff) : a * b = ⟨a.exp + b.exp, a.shift + 4 ^ a.exp * b.shift⟩ := rfl
  have inv : (⟨1, 0⟩ : Aff)⁻¹ = ⟨-1, 0⟩ := Aff.ext rfl (by
    change -(4 ^ (-1 : ℤ) * 0) = (0 : ℚ); simp)
  norm_num [inv, pow_succ, prod, show (1 : Aff).exp = 0 from rfl,
    show (1 : Aff).shift = 0 from rfl]

private lemma pairing_basis (i j : ℚ) :
    pairing (basis i).vec (basis j).vec = weight i j := by
  simp [pairing, basis, Finsupp.sum_single_index]

private lemma weight_backward {i j : ℚ} (h : j ≤ i) : weight i j = 0 := by
  have hn (k : ℤ) : j - i ≠ 4 ^ k :=
    ne_of_lt <| (sub_nonpos.mpr h).trans_lt (zpow_pos (by norm_num) _)
  simp [weight, hn]

private lemma gen_commute_iff (i j : ℚ) : Commute (gen i) (gen j) ↔ weight i j = weight j i := by
  change SemidirectProduct.inl (basis i) * _ = SemidirectProduct.inl (basis j) * _ ↔ _
  simp only [gen, ← map_mul, SemidirectProduct.inl_inj]
  constructor
  · intro h
    have hc := congrArg Central.center h
    change 0 + 0 + pairing (basis i).vec (basis j).vec =
      0 + 0 + pairing (basis j).vec (basis i).vec at hc
    simpa only [pairing_basis, zero_add] using hc
  · intro h
    apply Central.ext (add_comm ..)
    change 0 + 0 + pairing (basis i).vec (basis j).vec =
      0 + 0 + pairing (basis j).vec (basis i).vec
    simpa only [zero_add, pairing_basis] using h

private lemma gen_noncommute : ¬ Commute (gen 0) (gen 1) := by
  have h : ∃ k : ℤ, (1 : ℚ) - 0 = 4 ^ k := ⟨0, by norm_num⟩
  rw [gen_commute_iff, weight_backward (i := 1) (j := 0) (by norm_num)]
  simp only [weight, ite_eq_left h]
  decide

private lemma gen_commute : Commute (gen 0) (gen 2) := by
  have hn (k : ℤ) : (2 : ℚ) ≠ 4 ^ k := by
    rcases le_or_gt k 0 with hk | hk
    · have := zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℚ) ≤ 4) hk
      linarith
    · have := (zpow_right_strictMono₀ (by norm_num : (1 : ℚ) < 4)).monotone
        (show 1 ≤ k by omega)
      norm_num at this
      linarith
  rw [gen_commute_iff, weight_backward (i := 2) (j := 0) (by norm_num)]
  simp [weight, hn]

section Overgroup

variable {H : Type} [Group H] [LinearOrder H] [MulLeftMono H] [MulRightMono H]

private lemma conj_strictMono (s : H) : StrictMono (MulAut.conj s) :=
  fun _ _ h ↦ mul_lt_mul_left (mul_lt_mul_right h s) s⁻¹

-- The identity and a negative element already occupy two classes.
private lemma positive_conj {a b : H} (ha : 1 < a) (hb : 1 < b)
    (hc : Nat.card (ConjClasses H) = 3) : IsConj a b := by
  classical
  let := Nat.finite_of_card_ne_zero (α := ConjClasses H) (by omega)
  let := Fintype.ofFinite (ConjClasses H)
  have pos {x y : H} (hx : 1 < x) (h : IsConj x y) : 1 < y := by
    obtain ⟨s, rfl⟩ := isConj_iff.mp h
    simpa only [map_one, MulAut.conj_apply] using conj_strictMono s hx
  let c := @ConjClasses.mk H _
  have oneClass {x : H} : c x = c 1 ↔ x = 1 :=
    ConjClasses.mk_eq_mk_iff_isConj.trans isConj_one_left
  have hn : a⁻¹ < 1 := inv_lt_one'.mpr ha
  have h₄ : c a ≠ c a⁻¹ := fun h ↦ hn.asymm (pos ha (ConjClasses.mk_eq_mk_iff_isConj.mp h))
  have h₅ : c b ≠ c a⁻¹ := fun h ↦ hn.asymm (pos hb (ConjClasses.mk_eq_mk_iff_isConj.mp h))
  by_contra hab
  have h₆ : c a ≠ c b := fun h ↦ hab (ConjClasses.mk_eq_mk_iff_isConj.mp h)
  have bound := Finset.card_le_univ ({c a, c b, c a⁻¹, c 1} : Finset (ConjClasses H))
  simp [oneClass, ha.ne', hb.ne', hn.ne, h₄, h₅, h₆, ← Nat.card_eq_fintype_card, hc] at bound

private lemma root_of_positive (t : H) (ht : 1 < t) (hc : Nat.card (ConjClasses H) = 3) :
    ∃ s : H, s ^ 2 = t := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (positive_conj (one_lt_pow' ht (k := 2) (by decide)) ht hc)
  exact ⟨MulAut.conj g t, (map_pow (MulAut.conj g) t 2).symm.trans hg⟩

-- An increasing automorphism whose square sends x to x^(n*n) must send x to x^n.
private lemma half_action (s x : H) {n : ℕ} (hn : n ≠ 0)
    (h : MulAut.conj s (MulAut.conj s x) = x ^ (n * n)) : MulAut.conj s x = x ^ n := by
  let e := MulAut.conj s
  change e (e x) = x ^ (n * n) at h
  rcases lt_trichotomy (e x) (x ^ n) with hl | he | hg
  · have h₁ := conj_strictMono s hl
    have h₂ := pow_lt_pow_left' hn hl
    rw [show MulAut.conj s (e x) = x ^ (n * n) from h, map_pow, pow_mul] at h₁
    exact (h₁.asymm h₂).elim
  · exact he
  · have h₁ := conj_strictMono s hg
    have h₂ := pow_lt_pow_left' hn hg
    rw [show MulAut.conj s (e x) = x ^ (n * n) from h, map_pow, pow_mul] at h₁
    exact (h₁.asymm h₂).elim

end Overgroup

/--
**Not every fully ordered group embeds in one with three conjugacy classes.** There is a fully
ordered group $G$ such that for every fully ordered group $H$ with exactly three conjugacy
classes, no homomorphism $G \to H$ is strictly increasing. Here a fully ordered group is a group
with a linear order $\le$ such that $a \le b$ implies $ca \le cb$ and $ac \le bc$ for all $a$, $b$,
$c$. That is, the answer to Kourovka Problem 11.68 is negative.

The Kourovka Archive records the answer "No, not every", given by Bludov.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.68
(B. Neumann); resolution: V. V. Bludov, Algebra and Logic 44, no. 6 (2005), 370-380, Kourovka
Archive, Problem 11.68: "No, not every", https://arxiv.org/abs/1401.0300v49.
-/
public theorem orderedEmbedsInThreeClasses_refuted : ¬ orderedEmbedsInThreeClasses := by
  intro embeds
  obtain ⟨H, _, _, _, _, hc, f, hf⟩ := embeds Witness
  have hd : (1 : Witness) < dil := witness_lt.mpr (.inl (aff_lt.mpr (.inl (by decide))))
  obtain ⟨s, hs⟩ := root_of_positive (f dil) (by simpa using hf hd) hc
  let e := MulAut.conj s
  have half (x : Witness) {n : ℕ} (hn : n ≠ 0) (hx : MulAut.conj dil x = x ^ (n * n)) :
      e (f x) = (f x) ^ n := by
    apply half_action s _ hn
    calc
      _ = MulAut.conj (s ^ 2) (f x) := by rw [sq, map_mul]; rfl
      _ = f (MulAut.conj dil x) := by simp [hs, MulAut.conj_apply]
      _ = _ := by rw [hx, map_pow]
  have h₀ : e (f (gen 0)) = f (gen 0) := by
    simpa using half (gen 0) (n := 1) one_ne_zero (by simpa using dil_gen)
  have hshift := half (shift 1) (n := 2) (by decide) dil_shift
  have h₁ : e (f (gen 1)) = f (gen 2) := by
    calc
      _ = MulAut.conj (e (f (shift 1))) (e (f (gen 0))) := by
        conv_lhs => rw [← shift_gen 1]
        simp [MulAut.conj_apply]
      _ = f (gen 2) := by
        rw [h₀, hshift, ← map_pow, shift_square, ← shift_gen 2]
        simp [MulAut.conj_apply]
  -- Conjugation takes the noncommuting pair at 0 and 1 to the commuting pair at 0 and 2.
  apply gen_noncommute
  apply hf.injective
  apply e.injective
  simpa only [map_mul, h₀, h₁] using congrArg f gen_commute.eq

end

end MathlibExt.GroupTheory.OrderedGroupThreeClassesEmbeddingKourovka11Problem68Wanted
