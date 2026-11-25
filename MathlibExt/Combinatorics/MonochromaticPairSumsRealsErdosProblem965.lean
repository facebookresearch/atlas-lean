/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Rat.Encodable
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite

/-!
# Monochromatic pairwise sums in the reals

The theorem `alephOneMonochromaticPairSums_refuted` gives a two-colouring of the reals for which
the sums of distinct elements of every set of cardinality $\aleph_1$ take both colours.

Enumerate the rational cuts and apply them to the finite Hamel support of a real number.
At the first level that separates the support, choose two occupied cells that agreed at the
previous level. Their occupants' relative order in a fixed well-order gives the colour.

In an uncountable family we can fix the base cells and rational coefficients of the support.
Thin each coordinate until it is constant or has countable initial segments. Pick a point `x`
whose cell pattern at every level occurs uncountably often. Pick `y` above `x` in all varying
coordinates, then pick `z` above `y` with the pattern of `x` at a level separating the joint
support of `x` and `y`. The same cells split last for `x + y` and `z + y`, but the well-order
comparison of their occupants reverses.

For the use of rational cuts to separate Hamel supports, see N. Hindman, I. Leader and D. Strauss,
*Pairwise sums in colourings of the reals*, https://arxiv.org/abs/1505.02500.
-/

namespace MathlibExt.Combinatorics.MonochromaticPairSumsRealsErdosProblem965Wanted

/-- **Erdős Problem 965.** The statement that for every colouring of the real numbers with two
colours there is a set $A \subseteq \mathbb{R}$ of cardinality $\aleph_1$ such that all sums
$a + b$ with $a, b \in A$ and $a \ne b$ have the same colour. -/
@[expose] public def alephOneMonochromaticPairSums : Prop :=
  ∀ c : ℝ → Fin 2, ∃ A : Set ℝ, Cardinal.mk A = Cardinal.aleph 1 ∧ ∃ i : Fin 2,
    ∀ a ∈ A, ∀ b ∈ A, a ≠ b → c (a + b) = i

open Set Filter

private abbrev Index := Module.Free.ChooseBasisIndex ℚ ℝ
private noncomputable abbrev repr := (Module.Free.chooseBasis ℚ ℝ).repr
private abbrev Cell := Finset ℕ

private noncomputable def cut : ℕ → ℚ := (exists_surjective_nat ℚ).choose

/-- The outcomes of the first `n` rational comparisons on a basis element. -/
private noncomputable def cell (n : ℕ) (b : Index) : Cell :=
  (Finset.range n).filter fun k => (cut k : ℝ) < (Module.Free.chooseBasis ℚ ℝ) b

private theorem truncate_cell {m n : ℕ} (h : m ≤ n) (b : Index) :
    cell n b ∩ Finset.range m = cell m b := by
  ext k
  simp only [cell, Finset.mem_inter, Finset.mem_filter, Finset.mem_range]
  grind

private theorem cell_eventually_ne {a b : Index} (hab : a ≠ b) :
    ∀ᶠ n in atTop, cell n a ≠ cell n b := by
  have hsep {x y : Index} (hlt : (Module.Free.chooseBasis ℚ ℝ) x <
      (Module.Free.chooseBasis ℚ ℝ) y) : ∀ᶠ n in atTop, cell n x ≠ cell n y := by
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn hlt
    obtain ⟨k, hk : cut k = q⟩ := (exists_surjective_nat ℚ).choose_spec q
    filter_upwards [eventually_ge_atTop (k + 1)] with n hn he
    have hky : k ∈ cell n y := by simp [cell, hk, hq₂, show k < n by omega]
    have hkx : k ∉ cell n x := by simp [cell, hk, not_lt.mpr hq₁.le]
    exact hkx (he ▸ hky)
  rcases lt_or_gt_of_ne ((Module.Free.chooseBasis ℚ ℝ).injective.ne hab) with h | h
  · exact hsep h
  · exact (hsep h).mono fun _ hne => hne.symm

private theorem exists_level (s : Finset Index) : ∃ n, InjOn (cell n) s := by
  apply Filter.Eventually.exists (f := atTop)
  change ∀ᶠ n in atTop, ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → cell n a = cell n b → a = b
  apply (s.eventually_all).2
  intro a ha
  apply (s.eventually_all).2
  intro b hb
  by_cases h : a = b
  · exact Eventually.of_forall fun _ _ => h
  · exact (cell_eventually_ne h).mono fun _ hne he => (hne he).elim

private noncomputable def level (s : Finset Index) : ℕ := Nat.find (exists_level s)

private theorem level_inj (s : Finset Index) : InjOn (cell (level s)) s :=
  Nat.find_spec (exists_level s)

private theorem image_truncate (s : Finset Index) {m n : ℕ} (h : m ≤ n) :
    (s.image (cell n)).image (· ∩ Finset.range m) = s.image (cell m) := by
  simp only [Finset.image_image, Function.comp_def, truncate_cell h]

/-- Once a level separates a support, its occupied cells determine the first separating level. -/
private theorem level_eq {s t : Finset Index} {n : ℕ}
    (hs : InjOn (cell n) s) (ht : InjOn (cell n) t)
    (he : s.image (cell n) = t.image (cell n)) : level s = level t := by
  have hcard : s.card = t.card := by
    rw [← Finset.card_image_iff.mpr hs, ← Finset.card_image_iff.mpr ht, he]
  have le_of (a b : Finset Index) (hb : InjOn (cell n) b)
      (hc : b.card = a.card) (hi : b.image (cell n) = a.image (cell n)) :
      level a ≤ level b := by
    have hl : level b ≤ n := Nat.find_min' (exists_level b) hb
    apply Nat.find_min' (exists_level a)
    apply Finset.card_image_iff.mp
    rw [← image_truncate a hl, ← hi, image_truncate b hl,
      Finset.card_image_iff.mpr (level_inj b), hc]
  exact le_antisymm (le_of s t ht hcard.symm he.symm) (le_of t s hs hcard he)

/-- A fork is a pair of occupied cells which the previous level did not distinguish. -/
private def IsFork (T : Finset Cell) (m : ℕ) (pq : Cell × Cell) : Prop :=
  pq.1 ∈ T ∧ pq.2 ∈ T ∧ pq.1 ≠ pq.2 ∧ pq.1 ∩ Finset.range m = pq.2 ∩ Finset.range m

private theorem exists_fork (s : Finset Index) {m : ℕ} (hm : level s = m + 1) :
    ∃ pq, IsFork (s.image (cell (m + 1))) m pq := by
  have hbad : ¬ InjOn (cell m) s := fun h =>
    (show ¬ level s ≤ m by omega) (Nat.find_min' (exists_level s) h)
  unfold InjOn at hbad
  push Not at hbad
  obtain ⟨a, ha, b, hb, he, hne⟩ := hbad
  refine ⟨(cell (m + 1) a, cell (m + 1) b), Finset.mem_image_of_mem _ ha,
    Finset.mem_image_of_mem _ hb, ?_, ?_⟩
  · exact fun e => hne (level_inj s ha hb (hm ▸ e))
  · simpa only [truncate_cell (Nat.le_succ m)] using he

open Classical in
private noncomputable def fork (T : Finset Cell) (m : ℕ) : Cell × Cell :=
  if h : ∃ pq, IsFork T m pq then h.choose else (∅, ∅)

private noncomputable def occupant (s : Finset Index) (n : ℕ) (p : Cell) : Index :=
  if h : ∃ b ∈ s, cell n b = p then h.choose else Classical.arbitrary Index

private theorem occupant_eq {s : Finset Index} {n : ℕ} (hs : InjOn (cell n) s)
    {a : Index} (ha : a ∈ s) : occupant s n (cell n a) = a := by
  have h : ∃ b ∈ s, cell n b = cell n a := ⟨a, ha, rfl⟩
  unfold occupant
  simp only [h, ↓reduceDIte]
  exact hs h.choose_spec.1 ha h.choose_spec.2

private noncomputable def rank (a : Index) : Ordinal := Ordinal.typein WellOrderingRel a

private noncomputable def colour (s : Finset Index) : Fin 2 :=
  let n := level s
  let pq := fork (s.image (cell n)) (n - 1)
  if rank (occupant s n pq.1) < rank (occupant s n pq.2) then 0 else 1

private theorem cell_eq_of_le {m n : ℕ} (h : m ≤ n) {a b : Index}
    (he : cell n a = cell n b) : cell m a = cell m b := by
  simpa only [truncate_cell h] using congrArg (· ∩ Finset.range m) he

/-- At the last split, two occupied cells still belong to a single base cell. Reversing
the order of every such pair reverses the colour. -/
private theorem colour_ne_of_reversal {s t : Finset Index} {base n : ℕ}
    (hs : InjOn (cell n) s) (ht : InjOn (cell n) t)
    (he : s.image (cell n) = t.image (cell n)) (hc : ¬ InjOn (cell base) s)
    (hrev : ∀ a ∈ s, ∀ b ∈ s, ∀ a' ∈ t, ∀ b' ∈ t,
      cell n a = cell n a' → cell n b = cell n b' → cell base a = cell base b → a ≠ b →
      (rank a < rank b ↔ ¬ rank a' < rank b')) : colour s ≠ colour t := by
  have hd := level_eq hs ht he
  have hbn : base < level s := by
    by_contra! h
    exact hc fun _ ha _ hb e => level_inj s ha hb (cell_eq_of_le h e)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (show level s ≠ 0 by omega)
  have hmn : m + 1 ≤ n := by
    rw [← Nat.succ_eq_add_one, ← hm]
    exact Nat.find_min' (exists_level s) hs
  have hi : s.image (cell (m + 1)) = t.image (cell (m + 1)) := by
    rw [← image_truncate s hmn, ← image_truncate t hmn, he]
  let pq := fork (s.image (cell (m + 1))) m
  have hfork : IsFork (s.image (cell (m + 1))) m pq := by
    simpa only [pq, fork, exists_fork s hm, ↓reduceDIte] using (exists_fork s hm).choose_spec
  obtain ⟨hp, hq, hpq, hpar⟩ := hfork
  obtain ⟨a, ha, ea⟩ := Finset.mem_image.mp hp
  obtain ⟨b, hb, eb⟩ := Finset.mem_image.mp hq
  have copy (x : Index) (hx : x ∈ s) : ∃ y ∈ t, cell n x = cell n y := by
    have := he ▸ Finset.mem_image_of_mem (cell n) hx
    simpa only [Finset.mem_image, eq_comm] using this
  obtain ⟨a', ha', ean⟩ := copy a ha
  obtain ⟨b', hb', ebn⟩ := copy b hb
  have eab : cell m a = cell m b := by
    simpa only [← ea, ← eb, truncate_cell (Nat.le_succ m)] using hpar
  have hab : a ≠ b := fun e => hpq (ea.symm.trans ((congrArg _ e).trans eb))
  have rev := hrev a ha b hb a' ha' b' hb' ean ebn (cell_eq_of_le (by omega) eab) hab
  have his : InjOn (cell (m + 1)) s := by simpa only [hm] using level_inj s
  have hit : InjOn (cell (m + 1)) t := by
    simpa only [← hd, hm] using level_inj t
  have eap := (cell_eq_of_le hmn ean).symm.trans ea
  have ebp := (cell_eq_of_le hmn ebn).symm.trans eb
  unfold colour
  simp only [← hd, hm, ← hi]
  change (if rank (occupant s _ pq.1) < rank (occupant s _ pq.2) then _ else _) ≠
    (if rank (occupant t _ pq.1) < rank (occupant t _ pq.2) then _ else _)
  rw [← ea, occupant_eq his ha, ← eb, occupant_eq his hb]
  rw [ea, eb, ← eap, occupant_eq hit ha', ← ebp, occupant_eq hit hb']
  split_ifs <;> simp_all

private theorem uncountable_fiber {X T : Type*} [Countable T] {S : Set X}
    (hS : ¬ S.Countable) (f : X → T) : ∃ t, ¬ {x ∈ S | f x = t}.Countable := by
  by_contra! h
  apply hS
  apply (countable_iUnion (t := fun t => {x ∈ S | f x = t}) h).mono
  intro x hx
  apply mem_iUnion.mpr
  exact ⟨f x, hx, rfl⟩

/-- Thin a well-ordered coordinate until it is constant or all of its initial segments
in the remaining family are countable. -/
private def RegularOn {X : Type*} (S : Set X) (f : X → Ordinal) : Prop :=
  (∀ x ∈ S, ∀ y ∈ S, f x = f y) ∨ ∀ x ∈ S, {y ∈ S | f y ≤ f x}.Countable

private theorem regularOn_mono {X : Type*} {S T : Set X} {f : X → Ordinal}
    (h : RegularOn S f) (hTS : T ⊆ S) : RegularOn T f := by
  rcases h with h | h
  · exact Or.inl fun x hx y hy => h x (hTS hx) y (hTS hy)
  · right
    intro x hx
    apply (h x (hTS hx)).mono
    intro y hy
    exact ⟨hTS hy.1, hy.2⟩

private theorem thin_one {X : Type*} (S : Set X) (hS : ¬ S.Countable) (f : X → Ordinal) :
    ∃ T ⊆ S, ¬ T.Countable ∧ RegularOn T f := by
  classical
  by_cases hf : ∃ o, ¬ {x ∈ S | f x = o}.Countable
  · obtain ⟨o, ho⟩ := hf
    exact ⟨{x ∈ S | f x = o}, fun _ hx => hx.1, ho, Or.inl fun _ hx _ hy => hx.2.trans hy.2.symm⟩
  push Not at hf
  let bad : Set Ordinal := {o | o ∈ f '' S ∧ ¬ {x ∈ S | f x ≤ o}.Countable}
  by_cases hb : bad.Nonempty
  · obtain ⟨o, ho, hmin⟩ := wellFounded_lt.has_min bad hb
    refine ⟨{x ∈ S | f x < o}, fun _ hx => hx.1, ?_, Or.inr ?_⟩
    · intro hc
      apply ho.2
      exact (hc.union (hf o)).mono fun x hx =>
        (lt_or_eq_of_le hx.2).elim (fun h => Or.inl ⟨hx.1, h⟩) (fun h => Or.inr ⟨hx.1, h⟩)
    · intro x hx
      have hc : {y ∈ S | f y ≤ f x}.Countable := by
        by_contra h
        exact hmin _ ⟨⟨x, hx.1, rfl⟩, h⟩ hx.2
      apply hc.mono
      intro y hy
      exact ⟨hy.1.1, hy.2⟩
  · refine ⟨S, Subset.rfl, hS, Or.inr fun x hx => ?_⟩
    by_contra h
    exact hb ⟨_, ⟨x, hx, rfl⟩, h⟩

private theorem thin_coordinates {X J : Type*} (S : Set X) (hS : ¬ S.Countable)
    (f : X → J → Ordinal) (js : Finset J) :
    ∃ T ⊆ S, ¬ T.Countable ∧ ∀ j ∈ js, RegularOn T (fun x => f x j) := by
  classical
  induction js using Finset.induction_on with
  | empty => exact ⟨S, Subset.rfl, hS, by simp⟩
  | insert j js _ ih =>
    obtain ⟨T, hTS, hT, hjs⟩ := ih
    obtain ⟨U, hUT, hU, hj⟩ := thin_one T hT (fun x => f x j)
    refine ⟨U, hUT.trans hTS, hU, fun k hk => ?_⟩
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hj
    · exact regularOn_mono (hjs k hk) hUT

/-- In a countable sequence of countable partitions, some point of an uncountable set
belongs to an uncountable part at every level. -/
private theorem condensation_point {X P : Type*} [Countable P] (S : Set X)
    (hS : ¬ S.Countable) (p : ℕ → X → P) :
    ∃ x ∈ S, ∀ n, ¬ {y ∈ S | p n y = p n x}.Countable := by
  let small (n : ℕ) := {v : P | {y ∈ S | p n y = v}.Countable}
  have hc : (⋃ n, ⋃ v ∈ small n, {y ∈ S | p n y = v}).Countable :=
    countable_iUnion fun n => (to_countable (small n)).biUnion fun _ hv => hv
  by_contra! h
  apply hS
  apply hc.mono
  intro x hx
  obtain ⟨n, hn⟩ := h x hx
  apply mem_iUnion.mpr
  refine ⟨n, mem_iUnion₂.mpr ?_⟩
  exact ⟨p n x, hn, hx, rfl⟩

/-- A family with one support entry per base cell and fixed rational coefficients. -/
private structure Layout (X J : Type) [Fintype J] where
  point : X ↪ ℝ
  base : ℕ
  label : J ↪ Cell
  slot : X → J → Index
  coeff : J → ℚ
  cell_slot : ∀ x j, cell base (slot x j) = label j
  support_eq : ∀ x, (repr (point x)).support = Finset.univ.image (slot x)
  coeff_slot : ∀ x j, repr (point x) (slot x j) = coeff j

namespace Layout

variable {X J : Type} [Fintype J] (L : Layout X J)

private theorem same_slot {x y : X} {i j : J} (h : L.slot x i = L.slot y j) : i = j :=
  L.label.injective (by rw [← L.cell_slot x, ← L.cell_slot y, h])

private theorem point_eq {x y : X} (h : ∀ j, L.slot x j = L.slot y j) : x = y := by
  apply L.point.injective
  apply repr.injective
  ext b
  have he := funext h
  by_cases hb : b ∈ (repr (L.point x)).support
  · rw [L.support_eq] at hb
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    rw [L.coeff_slot, h j, L.coeff_slot]
  · have hb' : b ∉ (repr (L.point y)).support := by
      simpa only [L.support_eq, ← he] using hb
    simp_all only [Finsupp.mem_support_iff, not_not]

private def entry (x y : X) (k : Bool × J) : Index := L.slot (if k.1 then y else x) k.2

private theorem cell_entry (x y : X) (k : Bool × J) :
    cell L.base (L.entry x y k) = L.label k.2 := L.cell_slot _ _

private noncomputable def joint (x y : X) : Finset Index := Finset.univ.image (L.entry x y)

private theorem mem_joint {x y : X} {a : Index} :
    a ∈ L.joint x y ↔ ∃ k, L.entry x y k = a := by simp [joint]

private theorem support_add (x y : X) :
    (repr (L.point x + L.point y)).support = L.joint x y := by
  have no_cancel (u v : X) (j : J) :
      repr (L.point u) (L.slot u j) + repr (L.point v) (L.slot u j) ≠ 0 := by
    have hu : L.slot u j ∈ (repr (L.point u)).support := by simp [L.support_eq]
    by_cases hv : L.slot u j ∈ (repr (L.point v)).support
    · rw [L.support_eq] at hv
      obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hv
      obtain rfl := L.same_slot hk
      have he := L.coeff_slot v k
      rw [hk] at he
      rw [L.coeff_slot, he]
      have hn := Finsupp.mem_support_iff.mp hu
      rw [L.coeff_slot] at hn
      exact fun h => hn (by linarith)
    · simpa only [Finsupp.notMem_support_iff.mp hv, add_zero] using Finsupp.mem_support_iff.mp hu
  rw [map_add]
  ext b
  constructor
  · intro hb
    rcases Finset.mem_union.mp (Finsupp.support_add hb) with hx | hy
    · rw [L.support_eq] at hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      exact L.mem_joint.mpr ⟨(false, j), rfl⟩
    · rw [L.support_eq] at hy
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
      exact L.mem_joint.mpr ⟨(true, j), rfl⟩
  · intro hb
    obtain ⟨⟨tag, j⟩, rfl⟩ := L.mem_joint.mp hb
    rw [Finsupp.mem_support_iff, Finsupp.add_apply]
    cases tag with
    | false => exact no_cancel x y j
    | true =>
      rw [add_comm]
      exact no_cancel y x j

/-- Replace the first summand by a copy in the same fine cells, with every nonconstant
coordinate now above the corresponding coordinate of the second summand. -/
private theorem swap_colour (x y z : X) (n : ℕ) (hn : InjOn (cell n) (L.joint x y))
    (copy : ∀ j, cell n (L.slot x j) = cell n (L.slot z j))
    (move : ∀ j, (L.slot x j = L.slot y j ∧ L.slot y j = L.slot z j) ∨
      (rank (L.slot x j) < rank (L.slot y j) ∧ rank (L.slot y j) < rank (L.slot z j)))
    (hne : x ≠ y) : colour (L.joint x y) ≠ colour (L.joint z y) := by
  let f := L.entry x y
  let g := L.entry z y
  have copy' (k : Bool × J) : cell n (f k) = cell n (g k) := by
    obtain ⟨_ | _, j⟩ := k
    · exact copy j
    · rfl
  have slot_eq {k l : Bool × J} (h : cell L.base (f k) = cell L.base (f l)) : k.2 = l.2 := by
    apply L.label.injective
    simpa only [f, L.cell_entry] using h
  have consistent (k l : Bool × J) (h : f k = f l) : g k = g l := by
    have hj := slot_eq (congrArg _ h)
    obtain ⟨a, i⟩ := k
    obtain ⟨b, j⟩ := l
    obtain rfl : i = j := hj
    rcases move i with ⟨hxy, hyz⟩ | ⟨hxy, _⟩
    · cases a <;> cases b <;> simp [g, entry, hyz]
    · cases a <;> cases b <;> try rfl
      · exact ((ne_of_lt hxy) (congrArg rank h)).elim
      · exact ((ne_of_lt hxy) (congrArg rank h.symm)).elim
  have mem (k : Bool × J) : f k ∈ L.joint x y := L.mem_joint.mpr ⟨k, rfl⟩
  apply colour_ne_of_reversal (base := L.base) hn
  · intro a ha b hb he
    obtain ⟨k, rfl⟩ := L.mem_joint.mp ha
    obtain ⟨l, rfl⟩ := L.mem_joint.mp hb
    exact consistent k l (hn (mem k) (mem l) ((copy' k).trans (he.trans (copy' l).symm)))
  · simp only [joint, Finset.image_image]
    exact Finset.image_congr fun k _ => copy' k
  · intro hi
    apply hne
    apply L.point_eq
    intro j
    apply hi (mem (false, j)) (mem (true, j))
    exact (L.cell_slot x j).trans (L.cell_slot y j).symm
  · intro a ha b hb a' ha' b' hb' ea eb ebase hne'
    obtain ⟨k, rfl⟩ := L.mem_joint.mp ha
    obtain ⟨l, rfl⟩ := L.mem_joint.mp hb
    obtain ⟨k', rfl⟩ := L.mem_joint.mp ha'
    obtain ⟨l', rfl⟩ := L.mem_joint.mp hb'
    have h₁ := consistent k k' (hn (mem k) (mem k') (ea.trans (copy' k').symm))
    have h₂ := consistent l l' (hn (mem l) (mem l') (eb.trans (copy' l').symm))
    change rank (f k) < rank (f l) ↔ ¬ rank (g k') < rank (g l')
    rw [← h₁, ← h₂]
    have hj := slot_eq ebase
    obtain ⟨a, i⟩ := k
    obtain ⟨b, j⟩ := l
    obtain rfl : i = j := hj
    rcases move i with ⟨hxy, _⟩ | ⟨hxy, hyz⟩
    · cases a <;> cases b <;> simp [entry, hxy] at hne'
    · cases a <;> cases b <;>
        simp [entry, f, g, hxy, hyz, not_lt_of_gt hxy, not_lt_of_gt hyz] at hne' ⊢

/-- In any uncountable part of the thinned family we can move strictly above a given
point in every varying coordinate. -/
private theorem above {S T : Set X}
    (reg : ∀ j, RegularOn S (fun x => rank (L.slot x j))) (hTS : T ⊆ S)
    (hT : ¬ T.Countable) {x : X} (hx : x ∈ S) :
    ∃ y ∈ T, x ≠ y ∧ ∀ j, (∀ u ∈ S, ∀ v ∈ S, L.slot u j = L.slot v j) ∨
      rank (L.slot x j) < rank (L.slot y j) := by
  let constant (j : J) := ∀ u ∈ S, ∀ v ∈ S, L.slot u j = L.slot v j
  let bad (j : J) := {y ∈ S | rank (L.slot y j) ≤ rank (L.slot x j)}
  have hc : (⋃ j, ⋃ (_ : ¬ constant j), bad j).Countable := by
    apply countable_iUnion
    intro j
    apply countable_iUnion
    intro hj
    rcases reg j with h | h
    · exact (hj fun u hu v hv => Ordinal.typein_injective WellOrderingRel (h u hu v hv)).elim
    · exact h x hx
  have hsub : ¬ T ⊆ insert x (⋃ j, ⋃ (_ : ¬ constant j), bad j) :=
    fun h => hT ((hc.insert x).mono h)
  obtain ⟨y, hy, havoid⟩ := not_subset.mp hsub
  refine ⟨y, hy, fun h => havoid (Or.inl h.symm), ?_⟩
  intro j
  by_cases hj : constant j
  · exact Or.inl hj
  · right
    by_contra! h
    apply havoid
    exact Or.inr (mem_iUnion₂.mpr ⟨j, hj, hTS hy, h⟩)

private theorem not_monochromatic (hX : ¬ (univ : Set X).Countable) (i : Fin 2)
    (mono : ∀ x y : X, x ≠ y → colour (repr (L.point x + L.point y)).support = i) : False := by
  obtain ⟨S, _, hS, hreg⟩ := thin_coordinates univ hX
    (fun x j => rank (L.slot x j)) Finset.univ
  have reg := fun j => hreg j (Finset.mem_univ j)
  let pattern (n : ℕ) (x : X) (j : J) := cell n (L.slot x j)
  obtain ⟨x, hx, hcond⟩ := condensation_point S hS pattern
  obtain ⟨y, hy, hxy, h₁⟩ := L.above reg Subset.rfl hS hx
  obtain ⟨n, hn⟩ := exists_level (L.joint x y)
  obtain ⟨z, hz, hyz, h₂⟩ := L.above reg
    (T := {z ∈ S | pattern n z = pattern n x}) (fun _ h => h.1) (hcond n) hy
  have move (j : J) : (L.slot x j = L.slot y j ∧ L.slot y j = L.slot z j) ∨
      (rank (L.slot x j) < rank (L.slot y j) ∧ rank (L.slot y j) < rank (L.slot z j)) := by
    rcases h₁ j with hc | h₁'
    · exact Or.inl ⟨hc x hx y hy, hc y hy z hz.1⟩
    rcases h₂ j with hc | h₂'
    · exact Or.inl ⟨hc x hx y hy, hc y hy z hz.1⟩
    · exact Or.inr ⟨h₁', h₂'⟩
  apply L.swap_colour x y z n hn (fun j => congrFun hz.2.symm j) move hxy
  simpa only [L.support_add] using (mono x y hxy).trans (mono z y hyz.symm).symm

end Layout

/-- Record the occupied cells of a support together with their rational coefficients.
There are countably many such patterns. -/
private noncomputable def shape (n : ℕ) (x : ℝ) : Finset (Cell × ℚ) :=
  (repr x).support.image fun b => (cell n b, repr x b)

private theorem refute_on (A : Set ℝ) (hA : ¬ A.Countable) (i : Fin 2)
    (hmono : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → colour (repr (a + b)).support = i) : False := by
  let code (x : ℝ) := (level (repr x).support, shape (level (repr x).support) x)
  obtain ⟨⟨n, t⟩, hS⟩ := uncountable_fiber hA code
  let S := {x ∈ A | code x = (n, t)}
  have hsep (x : S) : InjOn (cell n) (repr x.val).support := by
    have he : level (repr x.val).support = n := congrArg Prod.fst x.property.2
    rw [← he]
    exact level_inj _
  have ht (x : S) : shape n x.val = t := by
    have he : level (repr x.val).support = n := congrArg Prod.fst x.property.2
    simpa only [code, he] using congrArg Prod.snd x.property.2
  have exists_slot (x : S) (j : t) :
      ∃ b ∈ (repr x.val).support, (cell n b, repr x.val b) = j.val := by
    apply (Finset.mem_image (s := (repr x.val).support)).mp
    change j.val ∈ shape n x.val
    rw [ht]
    exact j.property
  choose slot hmem hslot using exists_slot
  have hcell (x : S) (j : t) : cell n (slot x j) = j.val.1 := congrArg Prod.fst (hslot x j)
  have hcoeff (x : S) (j : t) : repr x.val (slot x j) = j.val.2 := congrArg Prod.snd (hslot x j)
  have hne : S.Nonempty := by
    by_contra! h
    apply hS
    change S.Countable
    rw [h]
    exact countable_empty
  obtain ⟨x₀, hx₀⟩ := hne
  let w : S := ⟨x₀, hx₀⟩
  let L : Layout S t := {
    point := Function.Embedding.subtype _
    base := n
    label := ⟨fun j => j.val.1, by
      intro j k he
      have eq := hsep w (hmem w j) (hmem w k) ((hcell w j).trans (he.trans (hcell w k).symm))
      exact Subtype.ext ((hslot w j).symm.trans (eq ▸ hslot w k))⟩
    slot := slot
    coeff := fun j => j.val.2
    cell_slot := hcell
    support_eq := by
      intro x
      ext b
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro hb
        let j : t := ⟨(cell n b, repr x.val b), by
          rw [← ht x]
          exact Finset.mem_image_of_mem _ hb⟩
        exact ⟨j, hsep x (hmem x j) hb (hcell x j)⟩
      · rintro ⟨j, rfl⟩
        exact hmem x j
    coeff_slot := hcoeff }
  apply L.not_monochromatic (fun hu => hS (countable_coe_iff.mp (countable_univ_iff.mp hu))) i
  intro x y hne'
  exact hmono x.val x.property.1 y.val y.property.1 (Subtype.val_injective.ne hne')

/--
**Erdős Problem 965 is false.** It is not the case that for every colouring of the real
numbers with two colours there is a set $A \subseteq \mathbb{R}$ of cardinality $\aleph_1$ such
that all sums $a + b$ with $a, b \in A$ and $a \ne b$ have the same colour.

Komjáth, and independently Soukup and Weiss, constructed in ZFC a $2$-colouring of $\mathbb{R}$
such that for every uncountable $A \subseteq \mathbb{R}$, in particular every $A$ of cardinality
$\aleph_1$, the sums $a + b$ of distinct $a, b \in A$ take both colours.

Source: T. F. Bloom, Erdős Problems, Problem #965, https://www.erdosproblems.com/965
(status DISPROVED (LEAN)); resolution: P. Komjáth, A certain 2-coloring of the reals, Real Anal.
Exchange (2016), 227-231, erdosproblems.com/965: Komjáth, and independently Soukup and Weiss, proved
without the continuum hypothesis that some 2-colouring of ℝ makes the sums of k distinct elements of
any uncountable A ⊆ ℝ non-monochromatic, for every k ≥ 1 (the case k = 2 disproves the question),
https://www.erdosproblems.com/965.
-/
public theorem alephOneMonochromaticPairSums_refuted : ¬ alephOneMonochromaticPairSums := by
  intro h
  obtain ⟨A, hA, i, hmono⟩ := h (fun x => colour (repr x).support)
  apply refute_on A _ i hmono
  intro hc
  exact Cardinal.aleph0_lt_aleph_one.not_ge (hA ▸ Cardinal.le_aleph0_iff_set_countable.mpr hc)

end MathlibExt.Combinatorics.MonochromaticPairSumsRealsErdosProblem965Wanted
