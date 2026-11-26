/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Pairing
import Mathlib.GroupTheory.HNNExtension
import Mathlib.Logic.Equiv.List
import Mathlib.Tactic.Group

/-!
# Torsion-free three-class groups with an index-2 subgroup (Kourovka Notebook Problem 11.42)

Kourovka Notebook, Archive of Solved Problems, Problem 11.42 (A. V. Izosov): does there exist a
torsion-free group having exactly three conjugacy classes and containing a subgroup of index 2?

Minasyan's theorem answers the question affirmatively, with a finitely generated group. This
file answers the question as posed, which does not ask for finite generation, with a simpler
construction that is not shown to give a finitely generated group. Starting from the integers
with their parity homomorphism, we form a chain of HNN extensions that conjugate pairs of
nonidentity elements with the same parity. In the direct limit these pairs exhaust the two
nonidentity conjugacy classes, and the kernel of parity has index two.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.42 (A. V.
Izosov). UnsolvedMath record UM-00700734 (`KOU-11.42`), dataset ulamai/UnsolvedMath v1.8.0.

Torsion-free is "no nontrivial element has finite order". "Exactly three conjugacy classes" is
`Nat.card (ConjClasses G) = 3` (which forces finitely many classes, since `Nat.card` of an infinite
type is `0`).
-/

@[expose] public section

namespace MathlibExt.GroupTheory.TorsionFreeThreeClassesIndexTwoKourovka11Problem42Wanted

/-- **Kourovka Problem 11.42 (statement).** The statement that there is a torsion-free group $G$ (no
element of $G$ other than the identity has finite order) that has exactly three conjugacy classes
and has a subgroup of index $2$.

The problem was posed by A. V. Izosov. -/
def torsionFreeThreeClassesIndexTwo : Prop :=
  ∃ (G : Type) (_ : Group G), (∀ g : G, g ≠ 1 → ¬ IsOfFinOrder g) ∧
    Nat.card (ConjClasses G) = 3 ∧ ∃ H : Subgroup G, H.index = 2

open HNNExtension HNNExtension.NormalWord

section HNN

variable {G : Type} [Group G] {A B : Subgroup G} (φ : A ≃* B)

private abbrev Letter (G : Type) := ℤˣ × G

private abbrev follows (A B : Subgroup G) (a b : Letter G) : Prop :=
  a.2 ∈ toSubgroup A B a.1 → a.1 = b.1

private def wordValue (l : List (Letter G)) : HNNExtension G A B φ :=
  (l.map fun x ↦ t ^ (x.1 : ℤ) * of x.2).prod

private def TorsionImpliesOne {H : Type} [Group H] (x : H) : Prop := IsOfFinOrder x → x = 1

private lemma torsionImpliesOne_mul_comm {H : Type} [Group H] (x y : H) :
    TorsionImpliesOne (x * y) ↔ TorsionImpliesOne (y * x) := by
  have eqv : ∀ a b : H, TorsionImpliesOne (a * b) → TorsionImpliesOne (b * a) := by
    intro a b hab h
    have he : MulAut.conj a (b * a) = a * b := by simp [MulAut.conj_apply, mul_assoc]
    apply (MulAut.conj a).injective
    rw [he, map_one]
    exact hab (he ▸ (MulAut.conj a).toMonoidHom.isOfFinOrder h)
  exact ⟨eqv x y, eqv y x⟩

-- All positive powers of a nonempty cyclically reduced word survive by Britton's lemma.
private lemma infinite_cyclic_word {a : Letter G} {s : List (Letter G)}
    (h : ((a :: s) ++ [a]).IsChain (follows A B)) :
    ¬ IsOfFinOrder (wordValue φ (a :: s)) := by
  intro hfin
  obtain ⟨n, hn, he⟩ := hfin.exists_pow_eq_one
  have aux (k : ℕ) : ∃ r : List (Letter G),
      ((a :: r) ++ [a]).IsChain (follows A B) ∧
      wordValue φ (a :: r) = wordValue φ (a :: s) ^ (k + 1) := by
    induction k with
    | zero => exact ⟨s, h, by simp⟩
    | succ k ih =>
      obtain ⟨r, hr, hrval⟩ := ih
      refine ⟨r ++ a :: s, ?_, ?_⟩
      · simpa [List.append_assoc] using
          (List.isChain_split.mpr ⟨hr, h⟩ :
            ((a :: r) ++ a :: (s ++ [a])).IsChain (follows A B))
      · rw [pow_succ, ← hrval]
        change wordValue φ ((a :: r) ++ (a :: s)) = _
        simp [wordValue, mul_assoc]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  obtain ⟨r, hr, hrval⟩ := aux k
  let w : ReducedWord G A B := ⟨1, a :: r, (List.isChain_append.mp hr).1⟩
  have hw : w.prod φ = 1 := by
    simpa [w, ReducedWord.prod, wordValue] using hrval.trans he
  have hempty := HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range φ w
    (by rw [hw]; exact of.range.one_mem)
  exact List.cons_ne_nil _ _ hempty

private lemma pinch {u v : ℤˣ} (hne : u ≠ v) (g : G) (hg : g ∈ toSubgroup A B u) :
    ∃ c : G, (t ^ (u : ℤ) * of g * t ^ (v : ℤ) : HNNExtension G A B φ) = of c := by
  rcases Int.units_eq_one_or u with rfl | rfl <;>
    rcases Int.units_eq_one_or v with rfl | rfl <;> try contradiction
  · exact ⟨φ ⟨g, hg⟩, by simpa using (equiv_eq_conj (φ := φ) ⟨g, hg⟩).symm⟩
  · exact ⟨φ.symm ⟨g, hg⟩, by simpa using (equiv_symm_eq_conj (φ := φ) ⟨g, hg⟩).symm⟩

-- Rotate the base-group head to the end. If the two ends form a pinch, conjugating
-- them together removes two stable letters and gives a shorter reduced word.
private lemma torsionImpliesOne_reducedWord (base : ∀ x : G, TorsionImpliesOne x)
    (l : List (Letter G)) (hl : l.IsChain (follows A B)) (g : G) :
    TorsionImpliesOne (of g * wordValue φ l) := by
  classical
  rcases l.eq_nil_or_concat' with rfl | ⟨init, last, rfl⟩
  · simp only [wordValue, List.map_nil, List.prod_nil, mul_one]
    intro hf
    simp [(base g) ((of_injective φ).isOfFinOrder_iff.mp hf)]
  · obtain ⟨v, b⟩ := last
    let last' : Letter G := (v, b * g)
    apply (torsionImpliesOne_mul_comm ..).mpr
    have hend : wordValue φ (init ++ [(v, b)]) * of g = wordValue φ (init ++ [last']) := by
      simp [wordValue, last', mul_assoc]
    rw [hend]
    cases init with
    | nil =>
      intro hf
      apply False.elim (infinite_cyclic_word φ (a := last') (s := []) ?_ hf)
      simp [follows]
    | cons a mid =>
      have hchain : ((a :: mid) ++ [last']).IsChain (follows A B) := by
        rw [List.isChain_append] at hl ⊢
        simpa [follows, last'] using hl
      by_cases hwrap : follows A B last' a
      · intro hf
        apply False.elim (infinite_cyclic_word φ (a := a) (s := mid ++ [last']) ?_ hf)
        simpa [List.append_assoc, hwrap] using
          (List.isChain_append_cons_cons.mpr ⟨hchain, hwrap, List.IsChain.singleton _⟩)
      · have hp : b * g ∈ toSubgroup A B v ∧ v ≠ a.1 := by
          simpa [follows, last', Classical.not_imp] using hwrap
        obtain ⟨c, hc⟩ := pinch φ hp.2 (b * g) hp.1
        let x : HNNExtension G A B φ := t ^ (a.1 : ℤ) * of a.2 * wordValue φ mid
        let y : HNNExtension G A B φ := t ^ (v : ℤ) * of (b * g)
        have he : wordValue φ ((a :: mid) ++ [last']) = x * y := by
          simp [wordValue, x, y, last', mul_assoc]
        rw [he, torsionImpliesOne_mul_comm]
        have hyx : y * x = of (c * a.2) * wordValue φ mid := by
          dsimp only [x, y]
          rw [of.map_mul c a.2, ← hc]
          group
        rw [hyx]
        exact torsionImpliesOne_reducedWord base mid
          (List.isChain_cons.mp (List.isChain_append.mp hl).1).2 _
termination_by l.length
decreasing_by simp_all

private lemma torsionImpliesOne_hnn (base : ∀ x : G, TorsionImpliesOne x)
    (x : HNNExtension G A B φ) : TorsionImpliesOne x := by
  let d : TransversalPair G A B := Classical.choice inferInstance
  obtain ⟨w, rfl⟩ := (NormalWord.equiv φ d).symm.surjective x
  exact torsionImpliesOne_reducedWord φ base _ w.chain w.head

end HNN

private structure Stage where
  carrier : Type
  [group : Group carrier]
  [countable : Countable carrier]
  torsion : ∀ x : carrier, TorsionImpliesOne x
  sign : carrier →* ℤˣ

attribute [local instance] Stage.group Stage.countable

private def Compatible (S : Stage) (p : S.carrier × S.carrier) : Prop :=
  p.1 ≠ 1 ∧ p.2 ≠ 1 ∧ S.sign p.1 = S.sign p.2

private structure Extension (S : Stage) (p : S.carrier × S.carrier) where
  target : Stage
  incl : S.carrier →* target.carrier
  injective : Function.Injective incl
  sign_incl : ∀ x, target.sign (incl x) = S.sign x
  conjugate : Compatible S p → IsConj (incl p.1) (incl p.2)

private noncomputable def cyclicIso {G : Type} [Group G] (x : G) (hx : ¬IsOfFinOrder x) :
    Multiplicative ℤ ≃* Subgroup.zpowers x :=
  MonoidHom.ofInjective (f := zpowersHom G x)
    (fun _ _ h ↦ (injective_zpow_iff_not_isOfFinOrder.mpr hx) h)

private lemma countable_hnn {G : Type} [Group G] [Countable G] {A B : Subgroup G}
    (φ : A ≃* B) : Countable (HNNExtension G A B φ) := by
  let d : TransversalPair G A B := Classical.choice inferInstance
  let pack (w : NormalWord d) := (w.head, w.toList)
  have hinj : Function.Injective pack := fun a b h ↦
    NormalWord.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  exact (hinj.comp (NormalWord.equiv φ d).injective).countable

-- Identify the two infinite cyclic subgroups and send the stable letter to the even sign.
private noncomputable def extend (S : Stage) (p : S.carrier × S.carrier) : Extension S p := by
  classical
  by_cases h : Compatible S p
  · let e := cyclicIso p.1 (fun hf ↦ h.1 (S.torsion _ hf))
    let f := cyclicIso p.2 (fun hf ↦ h.2.1 (S.torsion _ hf))
    let φ := e.symm.trans f
    have hsign (a : Subgroup.zpowers p.1) : 1 * S.sign a = S.sign (φ a : S.carrier) * 1 := by
      obtain ⟨z, rfl⟩ := e.surjective a
      simp only [φ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, one_mul, mul_one]
      change S.sign (p.1 ^ z.toAdd) = S.sign (p.2 ^ z.toAdd)
      rw [map_zpow, map_zpow, h.2.2]
    let T : Stage := {
      carrier := HNNExtension _ _ _ φ
      countable := countable_hnn φ
      torsion := torsionImpliesOne_hnn φ S.torsion
      sign := lift S.sign 1 hsign }
    refine ⟨T, of, of_injective φ, lift_of S.sign 1 hsign, fun _ ↦ ?_⟩
    apply isConj_iff.mpr
    refine ⟨t, ?_⟩
    have rel := (equiv_eq_conj (φ := φ) (e (Multiplicative.ofAdd 1))).symm
    simp only [φ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at rel
    change t * of (p.1 ^ (1 : ℤ)) * t⁻¹ = of (p.2 ^ (1 : ℤ)) at rel
    simpa using rel
  · exact ⟨S, MonoidHom.id _, Function.injective_id, fun _ ↦ rfl, fun hp ↦ (h hp).elim⟩

private def initial : Stage where
  carrier := Multiplicative ℤ
  countable := Countable.of_equiv ℤ Multiplicative.ofAdd
  torsion := fun _ hf ↦ hf.eq_one'
  sign := zpowersHom ℤˣ (-1)

private structure Schedule where
  stage : Stage
  pairAt : ℕ → stage.carrier × stage.carrier

private noncomputable def enumerate (S : Stage) : ℕ → S.carrier × S.carrier :=
  (exists_surjective_nat _).choose

private noncomputable def next (n : ℕ) (s : Schedule) : Schedule :=
  let e := extend s.stage (s.pairAt n)
  ⟨e.target, fun k ↦ if k.unpair.1 = n + 1 then enumerate e.target k.unpair.2
    else Prod.map e.incl e.incl (s.pairAt k)⟩

-- The pair numbered j at stage i is handled at stage Nat.pair i j, which is at least i.
private noncomputable def tower : ℕ → Schedule
  | 0 => ⟨initial, fun k ↦ enumerate initial k.unpair.2⟩
  | n + 1 => next n (tower n)

private abbrev Carrier (n : ℕ) := (tower n).stage.carrier

private noncomputable abbrev extensionAt (n : ℕ) :=
  extend (tower n).stage ((tower n).pairAt n)

private noncomputable def step (n : ℕ) : Carrier n →* Carrier (n + 1) :=
  (extensionAt n).incl

private noncomputable def transition (i j : ℕ) (h : i ≤ j) : Carrier i →* Carrier j :=
  Nat.leRecOn h (fun {k} f ↦ (step k).comp f) (MonoidHom.id _)

private lemma transition_self (i : ℕ) : transition i i le_rfl = MonoidHom.id _ :=
  Nat.leRecOn_self _

private lemma transition_succ (i j : ℕ) (h : i ≤ j) :
    transition i (j + 1) (Nat.le_succ_of_le h) = (step j).comp (transition i j h) :=
  Nat.leRecOn_succ h _

private instance towerDirected : DirectedSystem Carrier (transition · · ·) where
  map_self i x := by rw [transition_self]; rfl
  map_map k j i hij hjk x := by
    induction k, hjk using Nat.le_induction with
    | base => rw [transition_self]; rfl
    | succ k hk ih =>
      rw [transition_succ _ _ hk, transition_succ _ _ (hij.trans hk)]
      exact congrArg (step k) ih

private lemma transition_injective (i j : ℕ) (h : i ≤ j) :
    Function.Injective (transition i j h) := by
  induction j, h using Nat.le_induction with
  | base => rw [transition_self]; exact Function.injective_id
  | succ j hj ih => rw [transition_succ _ _ hj]; exact (extensionAt j).injective.comp ih

private lemma transition_sign (i j : ℕ) (h : i ≤ j) (x : Carrier i) :
    (tower j).stage.sign (transition i j h x) = (tower i).stage.sign x := by
  induction j, h using Nat.le_induction with
  | base => rw [transition_self]; rfl
  | succ j hj ih =>
    rw [transition_succ _ _ hj, MonoidHom.comp_apply]
    exact ((extensionAt j).sign_incl _).trans ih

private abbrev Limit := DirectLimit Carrier transition

private noncomputable def incl (i : ℕ) : Carrier i →* Limit where
  toFun x := ⟦⟨i, x⟩⟧
  map_one' := (DirectLimit.one_def i).symm
  map_mul' _ _ := (DirectLimit.mul_def i _ _).symm

private lemma incl_injective (i : ℕ) : Function.Injective (incl i) :=
  DirectLimit.mk_injective transition transition_injective i

private lemma incl_step (n : ℕ) (x : Carrier n) : incl (n + 1) (step n x) = incl n x := by
  have h := DirectLimit.mk_apply (f := transition) n (n + 1) x (Nat.le_succ n)
  simp only [transition_succ _ _ (le_refl n), transition_self, MonoidHom.comp_apply,
    MonoidHom.id_apply] at h
  exact h

private noncomputable def parity : Limit →* ℤˣ where
  toFun := DirectLimit.lift transition (fun i ↦ (tower i).stage.sign)
    (fun i j h x ↦ (transition_sign i j h x).symm)
  map_one' := by rw [DirectLimit.one_def 0, DirectLimit.lift_def, map_one]
  map_mul' := DirectLimit.induction₂ _ fun i x y ↦ by
    rw [DirectLimit.mul_def, DirectLimit.lift_def, DirectLimit.lift_def,
      DirectLimit.lift_def, map_mul]

private lemma parity_incl (n : ℕ) (x : Carrier n) : parity (incl n x) = (tower n).stage.sign x :=
  rfl

private lemma new_pair (i j : ℕ) :
    (tower i).pairAt (Nat.pair i j) = enumerate (tower i).stage j := by
  cases i <;> simp [tower, next, Nat.unpair_pair]

private lemma keep_pair (n k : ℕ) (h : k.unpair.1 ≤ n) :
    (tower (n + 1)).pairAt k = Prod.map (step n) (step n) ((tower n).pairAt k) := by
  simp [tower, next, Nat.ne_of_lt (Nat.lt_succ_of_le h), step, extensionAt]
  rfl

private lemma scheduled_pair (i j n : ℕ) (h : i ≤ n) :
    Prod.map (incl n) (incl n) ((tower n).pairAt (Nat.pair i j)) =
      Prod.map (incl i) (incl i) (enumerate (tower i).stage j) := by
  induction n, h using Nat.le_induction with
  | base => rw [new_pair]
  | succ n hn ih =>
    rw [keep_pair _ _ (by simpa using hn)]
    simpa only [Prod.map_fst, Prod.map_snd, Prod.map, incl_step] using ih

private lemma conjugate_in_limit (x y : Limit) (hx : x ≠ 1) (hy : y ≠ 1)
    (h : parity x = parity y) : IsConj x y := by
  obtain ⟨i, a, b, rfl, rfl⟩ := DirectLimit.exists_eq_mk₂ transition x y
  change IsConj (incl i a) (incl i b)
  obtain ⟨j, hj⟩ := (exists_surjective_nat ((Carrier i) × (Carrier i))).choose_spec (a, b)
  let k := Nat.pair i j
  let p := (tower k).pairAt k
  have he : Prod.map (incl k) (incl k) p = (incl i a, incl i b) := by
    simpa [enumerate, hj] using scheduled_pair i j k (Nat.left_le_pair i j)
  have ha : incl k p.1 = incl i a := congrArg Prod.fst he
  have hb : incl k p.2 = incl i b := congrArg Prod.snd he
  have hp : Compatible (tower k).stage p := by
    refine ⟨fun e ↦ hx (ha.symm.trans (by rw [e, map_one])),
      fun e ↦ hy (hb.symm.trans (by rw [e, map_one])), ?_⟩
    rw [← parity_incl, ← parity_incl, ha, hb]
    exact h
  have hc := (incl (k + 1)).map_isConj ((extensionAt k).conjugate hp)
  change IsConj (incl (k + 1) (step k p.1)) (incl (k + 1) (step k p.2)) at hc
  rwa [incl_step, incl_step, ha, hb] at hc

-- In the initial copy of the integers, 2 and 1 represent the nonidentity even and odd classes.
private noncomputable def representative (s : ℤˣ) : Limit :=
  incl 0 (Multiplicative.ofAdd (α := ℤ) (if s = 1 then 2 else 1))

private lemma representative_ne_one (s : ℤˣ) : representative s ≠ 1 := by
  apply (map_ne_one_iff (incl 0) (incl_injective 0)).mpr
  change (if s = 1 then (2 : ℤ) else 1) ≠ 0
  split <;> decide

private lemma parity_representative (s : ℤˣ) : parity (representative s) = s := by
  change (-1 : ℤˣ) ^ (if s = 1 then (2 : ℤ) else 1) = s
  rcases Int.units_eq_one_or s with rfl | rfl <;> decide

private lemma three_classes : Nat.card (ConjClasses Limit) = 3 := by
  let f (v : Option ℤˣ) := ConjClasses.mk (v.elim 1 representative)
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have h := ConjClasses.mk_eq_mk_iff_isConj.mp hab
      cases a with
      | none =>
        cases b with
        | none => rfl
        | some b => exact (representative_ne_one b (isConj_one_right.mp h)).elim
      | some a =>
        cases b with
        | none => exact (representative_ne_one a (isConj_one_left.mp h)).elim
        | some b =>
          have hp := isConj_iff_eq.mp (parity.map_isConj h)
          change parity (representative a) = parity (representative b) at hp
          exact congrArg some (by simpa only [parity_representative] using hp)
    · intro c
      obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
      by_cases hx : x = 1
      · exact ⟨none, by subst x; rfl⟩
      · exact ⟨some (parity x), ConjClasses.mk_eq_mk_iff_isConj.mpr
          (conjugate_in_limit _ x (representative_ne_one _) hx (parity_representative _))⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card,
    Fintype.card_option, Fintype.card_units_int]

/--
**Minasyan's theorem (Kourovka Problem 11.42).** There is a torsion-free group $G$ (no element of
$G$ other than the identity has finite order) that has exactly three conjugacy classes and has a
subgroup of index $2$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.42 (A. V.
Izosov); resolution: A. Minasyan, Comment. Math. Helv. 84 (2009), 259-296, Kourovka Archive,
Problem 11.42: "Yes, there does", https://arxiv.org/abs/1401.0300v49.
-/
public theorem torsionFreeThreeClassesIndexTwo_holds : torsionFreeThreeClassesIndexTwo := by
  refine ⟨Limit, inferInstance, ?_, three_classes, parity.ker, ?_⟩
  · intro x hx hf
    obtain ⟨i, a, rfl⟩ := DirectLimit.exists_eq_mk transition x
    have h : IsOfFinOrder a := (incl_injective i).isOfFinOrder_iff.mp hf
    exact hx (show incl i a = 1 by rw [(tower i).stage.torsion a h, map_one])
  · rw [Subgroup.index_ker, parity.range_eq_top_of_surjective
        (fun s ↦ ⟨representative s, parity_representative s⟩), Subgroup.card_top,
      Nat.card_eq_fintype_card, Fintype.card_units_int]

end MathlibExt.GroupTheory.TorsionFreeThreeClassesIndexTwoKourovka11Problem42Wanted
