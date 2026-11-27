/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.FiniteStateTreeAutomorphism
public import Mathlib.GroupTheory.Coprod.Basic

import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod

/-!
# Finite-state actions of free products (Kourovka Notebook Problem 16.85)

The free product of two groups with faithful finite-state tree actions has such an action.

The new alphabet has a copy of each factor's letters paired with reference letters and marked
with an end-of-block bit. Each factor acts on its own letters. A discrepancy with the reference
letter at the end of its block activates the other factor on the next block. For a nonidentity
syllable, choose a block whose last letter it changes. Concatenating these blocks in order of
application gives a word moved by the reduced product. Each factor element's machine needs only
its original sections and an identity state.

Kourovka Notebook, Archive of Solved Problems, Problem 16.85 (V. I. Sushchanskiĭ): suppose that
groups `G`, `H` act faithfully on a regular rooted tree by finite-state automorphisms. Can their
free product `G ∗ H` act faithfully on a regular rooted tree by finite state automorphisms?

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.85 (V. I.
Sushchanskiĭ). UnsolvedMath record UM-00701276 (`KOU-16.85`), dataset ulamai/UnsolvedMath v1.8.0.

Trees, tree automorphisms and finite-state automorphisms are as in Problem 16.34. A group acts
faithfully by finite-state automorphisms if it embeds in the finite-state automorphisms of the
`d`-regular rooted tree for some `d ≥ 2`; `G` and `H` may act on trees of different degrees, as in
the resolution. The free product is `Monoid.Coprod G H`.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.FiniteStateFreeProductKourovka16Problem85Wanted

/-- **Faithful actions by finite-state tree automorphisms.** A group $G$ acts faithfully on a
regular rooted tree by finite-state automorphisms when there are a natural number $d \ge 2$ and an
injective group homomorphism $\varphi$ from $G$ to the group of permutations of the set of finite
words over $\{0, \dots, d-1\}$ such that $\varphi(g)$ is a finite-state automorphism of the
$d$-regular rooted tree for every $g \in G$. -/
def ActsFaithfullyByFiniteStateAuts (G : Type) [Group G] : Prop :=
  ∃ (d : ℕ) (f : G →* Equiv.Perm (List (Fin d))), 2 ≤ d ∧ Function.Injective f ∧
    ∀ g : G, IsFiniteStateAut (f g)

/-- **Finite-state actions of free products (Kourovka Problem 16.85).** The statement that for all
groups $G$ and $H$, if $G$ and $H$ each act faithfully on a regular rooted tree by finite-state
automorphisms (the two trees may have different degrees), then so does their free product
$G \ast H$. -/
def finiteStateFreeProduct : Prop :=
  ∀ (G H : Type) [Group G] [Group H], ActsFaithfullyByFiniteStateAuts G →
    ActsFaithfullyByFiniteStateAuts H → ActsFaithfullyByFiniteStateAuts (Monoid.Coprod G H)

-- A section records exactly the information a tree map retains after reading a prefix.
private def sectionAt {X : Type} (f : List X → List X) (u w : List X) : List X :=
  (f (u ++ w)).drop u.length

private structure TreeMap {X : Type} (f : List X → List X) : Prop where
  length_eq (u : List X) : (f u).length = u.length
  append_eq (u v : List X) : f (u ++ v) = f u ++ sectionAt f u v

private theorem TreeMap.ofAut {d : ℕ} {f : Equiv.Perm (List (Fin d))} (hf : IsTreeAut f) :
    TreeMap f where
  length_eq u := (hf u []).1
  append_eq u v := by
    rw [← (hf u v).2]
    exact (List.take_append_drop ..).symm

private theorem treeMap_id {X : Type} : TreeMap (id : List X → List X) :=
  ⟨fun _ => rfl, fun _ _ => by simp [sectionAt]⟩

private theorem section_nil {X : Type} (f : List X → List X) : sectionAt f [] = f := by
  funext w
  simp [sectionAt]

private theorem section_section {X : Type} (f : List X → List X)
    (u v : List X) : sectionAt (sectionAt f u) v = sectionAt f (u ++ v) := by
  funext w
  simp [sectionAt, List.drop_drop, List.append_assoc]

private theorem TreeMap.sectionAt_map {X : Type} {f : List X → List X} (hf : TreeMap f)
    (u : List X) : TreeMap (sectionAt f u) where
  length_eq v := by simp [sectionAt, hf.length_eq]
  append_eq v w := by
    rw [section_section]
    apply List.append_cancel_left (as := f u)
    rw [← hf.append_eq, ← List.append_assoc (f u), ← hf.append_eq, ← hf.append_eq,
      List.append_assoc]

private theorem TreeMap.section_comp {X : Type} {f h : List X → List X} (hf : TreeMap f)
    (hh : TreeMap h) (u : List X) :
    sectionAt (f ∘ h) u = sectionAt f (h u) ∘ sectionAt h u := by
  funext w
  change (f (h (u ++ w))).drop u.length = _
  rw [hh.append_eq, hf.append_eq, ← hh.length_eq u, ← hf.length_eq (h u), List.drop_left]
  rfl

private def output {X : Type} (f : List X → List X) (x : X) : X := (f [x]).headD x

private theorem TreeMap.singleton_eq {X : Type} {f : List X → List X} (hf : TreeMap f) (x : X) :
    f [x] = [output f x] := by
  obtain ⟨y, hy⟩ := List.length_eq_one_iff.mp (hf.length_eq [x])
  simp [output, hy]

-- A letter carries an input, its reference copy, and an end-of-block flag.
private abbrev Letter (X : Type) := X × X × Bool

private abbrev View (A X Y : Type) := (Letter X ⊕ Letter Y) ≃ A

private def opposite {A X Y : Type} (e : View A X Y) : View A Y X := (Equiv.sumComm ..).trans e

private def own {A X Y : Type} (e : View A X Y) (x r : X) (stop : Bool) : A :=
  e (.inl (x, r, stop))

private def other {A X Y : Type} (e : View A X Y) (y r : Y) (stop : Bool) : A :=
  e (.inr (y, r, stop))

-- Each factor acts on its own blocks. A mismatch on the final letter of the other
-- factor's block starts the machine again at its initial state.
private def step {A X Y : Type} [DecidableEq Y] (e : View A X Y)
    (base cur : List X → List X) (a : A) : A × (List X → List X) :=
  match e.symm a with
  | .inl (x, r, stop) =>
    (own e (output cur x) r stop, if stop then id else sectionAt cur [x])
  | .inr (y, r, stop) => (a, if stop && y != r then base else id)

private def run {A X Y : Type} [DecidableEq Y] (e : View A X Y)
    (base cur : List X → List X) : List A → List A
  | [] => []
  | a :: w => (step e base cur a).1 :: run e base (step e base cur a).2 w

private theorem run_own {A X Y : Type} [DecidableEq Y] (e : View A X Y) (base cur)
    (x r : X) (b : Bool) (w : List A) :
    run e base cur (own e x r b :: w) =
      own e (output cur x) r b :: run e base (if b then id else sectionAt cur [x]) w := by
  simp [run, step, own]

private theorem run_other {A X Y : Type} [DecidableEq Y] (e : View A X Y) (base cur)
    (y r : Y) (b : Bool) (w : List A) :
    run e base cur (other e y r b :: w) =
      other e y r b :: run e base (if b && y != r then base else id) w := by
  simp [run, step, other]

private theorem section_id {X : Type} (u : List X) : sectionAt id u = id := by
  funext w
  simp [sectionAt]

private theorem run_id {A X Y : Type} [DecidableEq Y] (e : View A X Y) (w : List A) :
    run e id id w = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    obtain ⟨(⟨x, r, b⟩ | ⟨y, r, b⟩), rfl⟩ := e.surjective a
    · exact (run_own e ..).trans (by simp [output, section_id, ih, own])
    · exact (run_other e ..).trans (by simp [ih, other])

private theorem run_comp {A X Y : Type} [DecidableEq Y] (e : View A X Y)
    {f h : List X → List X} (hf : TreeMap f) (hh : TreeMap h) (w : List A)
    {p q : List X → List X} (hp : TreeMap p) (hq : TreeMap q) :
    run e (f ∘ h) (p ∘ q) w = run e f p (run e h q w) := by
  induction w generalizing p q with
  | nil => rfl
  | cons a w ih =>
    obtain ⟨(⟨x, r, b⟩ | ⟨y, r, b⟩), rfl⟩ := e.surjective a
    · change run _ _ _ (own e x r b :: w) = run _ _ _ (run _ _ _ (own e x r b :: w))
      simp only [run_own]
      have ho : output (p ∘ q) x = output p (output q x) := by
        change ((p (q [x])).headD x) = _
        rw [hq.singleton_eq x, hp.singleton_eq (output q x)]
        rfl
      rw [ho]
      congr 1
      cases b with
      | false =>
        change run _ _ (sectionAt (p ∘ q) [x]) _ = _
        rw [hp.section_comp hq, hq.singleton_eq x]
        exact ih (hp.sectionAt_map [output q x]) (hq.sectionAt_map [x])
      | true => exact ih treeMap_id treeMap_id
    · change run _ _ _ (other e y r b :: w) = run _ _ _ (run _ _ _ (other e y r b :: w))
      simp only [run_other]
      split
      · exact congrArg (_ :: ·) (ih hf hh)
      · exact congrArg (_ :: ·) (ih treeMap_id treeMap_id)

private def factorAction {A X Y G : Type} [Group G] [DecidableEq Y] (e : View A X Y)
    (f : G →* Equiv.Perm (List X)) (hf : ∀ g, TreeMap (f g)) :
    G →* Function.End (List A) where
  toFun g := run e (f g) (f g)
  map_one' := by
    funext w
    change run e (f 1) (f 1) w = w
    rw [map_one]
    exact run_id e w
  map_mul' g h := by
    funext w
    change run e (f (g * h)) (f (g * h)) w = run e (f g) (f g) (run e (f h) (f h) w)
    rw [map_mul]
    exact run_comp e (hf g) (hf h) w (hf g) (hf h)

private def stateAfter {A X Y : Type} [DecidableEq Y] (e : View A X Y)
    (base cur : List X → List X) : List A → (List X → List X)
  | [] => cur
  | a :: w => stateAfter e base (step e base cur a).2 w

private theorem run_append {A X Y : Type} [DecidableEq Y] (e : View A X Y) (base cur)
    (u v : List A) :
    run e base cur (u ++ v) = run e base cur u ++ run e base (stateAfter e base cur u) v := by
  induction u generalizing cur with
  | nil => rfl
  | cons a u ih => simp [run, stateAfter, ih]

private theorem run_length {A X Y : Type} [DecidableEq Y] (e : View A X Y) (base cur)
    (u : List A) : (run e base cur u).length = u.length := by
  induction u generalizing cur with
  | nil => rfl
  | cons a u ih => simp [run, ih]

private theorem run_tree {A X Y : Type} [DecidableEq Y] (e : View A X Y) (base cur) :
    TreeMap (run e base cur) where
  length_eq := run_length e base cur
  append_eq u v := by
    simp [sectionAt, run_append, ← run_length e base cur u]

private theorem stateAfter_mem {A X Y : Type} [DecidableEq Y] (e : View A X Y) (base cur)
    (hc : cur ∈ insert id (Set.range (sectionAt base))) (u : List A) :
    stateAfter e base cur u ∈ insert id (Set.range (sectionAt base)) := by
  induction u generalizing cur with
  | nil => exact hc
  | cons a u ih =>
    apply ih
    obtain ⟨(⟨x, r, b⟩ | ⟨y, r, b⟩), rfl⟩ := e.surjective a
    · simp only [step, Equiv.symm_apply_apply]
      split
      · exact Set.mem_insert _ _
      · rcases hc with h | ⟨v, rfl⟩
        · rw [h, section_id]
          exact Set.mem_insert _ _
        · exact Or.inr ⟨v ++ [x], (section_section base v [x]).symm⟩
    · simp only [step, Equiv.symm_apply_apply]
      split
      · exact Or.inr ⟨[], section_nil base⟩
      · exact Set.mem_insert _ _

private def FiniteTreeMap {A : Type} (f : List A → List A) : Prop :=
  TreeMap f ∧ (Set.range (sectionAt f)).Finite

private theorem run_finite {A X Y : Type} [DecidableEq Y] (e : View A X Y) {base}
    (hf : (Set.range (sectionAt base)).Finite) : FiniteTreeMap (run e base base) := by
  refine ⟨run_tree .., ((hf.insert id).image (run e base)).subset ?_⟩
  rintro _ ⟨u, rfl⟩
  have hb : base ∈ insert id (Set.range (sectionAt base)) :=
    Or.inr ⟨[], section_nil base⟩
  refine ⟨_, stateAfter_mem e base base hb u, ?_⟩
  funext w
  simp only [sectionAt, run_append, ← run_length e base base u, List.drop_left]

private theorem FiniteTreeMap.isFiniteStateAut {d : ℕ} {f : Equiv.Perm (List (Fin d))}
    (hf : FiniteTreeMap f) : IsFiniteStateAut f := by
  refine ⟨fun u v => ⟨hf.1.length_eq u, ?_⟩, hf.2⟩
  rw [hf.1.append_eq, ← hf.1.length_eq u, List.take_left]

-- On a test word both tracks initially coincide. In the dormant state such words are fixed.
private def diagonal {A X Y : Type} (e : View A X Y) (a : A) : Prop :=
  match e.symm a with
  | .inl (x, r, _) => x = r
  | .inr (y, r, _) => y = r

private def Clean {A X Y : Type} (e : View A X Y) (w : List A) := ∀ a ∈ w, diagonal e a

private theorem clean_append {A X Y : Type} {e : View A X Y} {u v : List A}
    (hu : Clean e u) (hv : Clean e v) : Clean e (u ++ v) := by
  intro a ha
  exact (List.mem_append.mp ha).elim (hu a) (hv a)

private theorem clean_opposite {A X Y : Type} {e : View A X Y} {u : List A} :
    Clean (opposite e) u ↔ Clean e u := by
  have h (a : A) : diagonal (opposite e) a ↔ diagonal e a := by
    obtain ⟨(⟨x, r, b⟩ | ⟨y, r, b⟩), rfl⟩ := e.surjective a <;>
      simp [diagonal, opposite]
  simp only [Clean, h]

private theorem run_dormant {A X Y : Type} [DecidableEq Y] (e : View A X Y) (base)
    (u : List A) (hu : Clean e u) : run e base id u = u := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    have h := hu a List.mem_cons_self
    have ht := ih (fun x hx => hu x (List.mem_cons_of_mem _ hx))
    obtain ⟨(⟨x, r, b⟩ | ⟨y, r, b⟩), rfl⟩ := e.surjective a
    · exact (run_own e ..).trans (by simp [output, own, section_id, ht])
    · have hy : y = r := by simpa [diagonal] using h
      exact (run_other e ..).trans (by simp [hy, other, ht])

-- A nonidentity tree permutation changes a letter after some prefix.
private theorem exists_moved_letter {X : Type} {f : Equiv.Perm (List X)} (hf : TreeMap f)
    (hne : f ≠ 1) : ∃ (u : List X) (x : X), output (sectionAt f u) x ≠ x := by
  by_contra! h
  apply hne
  apply Equiv.ext
  intro w
  change f w = w
  induction w using List.reverseRecOn with
  | nil => exact List.length_eq_zero_iff.mp (hf.length_eq [])
  | append_singleton u x ih =>
    rw [hf.append_eq, (hf.sectionAt_map u).singleton_eq x, h, ih]

private def block {A X Y : Type} (e : View A X Y) (u : List X) (x : X) : List A :=
  u.map (fun y => own e y y false) ++ [own e x x true]

private theorem clean_block {A X Y : Type} (e : View A X Y) (u : List X) (x : X) :
    Clean e (block e u x) := by
  intro a ha
  simp only [block, List.mem_append, List.mem_map, List.mem_singleton] at ha
  rcases ha with ⟨y, _, rfl⟩ | rfl <;> simp [diagonal, own]

private theorem run_block {A X Y : Type} [DecidableEq Y] (e : View A X Y) (base cur)
    (u : List X) (x : X) : ∃ v : List A, ∀ t,
    run e base cur (block e u x ++ t) =
      v ++ own e (output (sectionAt cur u) x) x true :: run e base id t := by
  induction u generalizing cur with
  | nil =>
    refine ⟨[], fun t => ?_⟩
    simp [block, run_own, section_nil]
  | cons y u ih =>
    obtain ⟨v, hv⟩ := ih (sectionAt cur [y])
    refine ⟨own e (output cur y) y false :: v, fun t => ?_⟩
    change run _ _ _ (own e y y false :: (block e u x ++ t)) = _
    simp [run_own, hv, section_section]

-- The last letter of a moved block activates the opposite factor. Clean suffixes
-- survive, so a fresh block can be attached for every syllable of a reduced word.
private def Witness {A X Y : Type} (e : View A X Y) (F : Function.End (List A)) : Prop :=
  ∃ w v x r, Clean e w ∧ x ≠ r ∧
    ∀ t, Clean e t → F (w ++ t) = v ++ own e x r true :: t

private theorem grow_witness {A X Y : Type} [DecidableEq Y] (e : View A X Y)
    {f : Equiv.Perm (List X)} (hf : TreeMap f) (hne : f ≠ 1) {F : Function.End (List A)}
    (hF : F = 1 ∨ Witness (opposite e) F) :
    Witness e (run e f f ∘ F) := by
  obtain ⟨u, x, hx⟩ := exists_moved_letter hf hne
  obtain ⟨z, hz⟩ := run_block e f f u x
  have start : ∃ w v, Clean e w ∧ ∀ t, Clean e t →
      run e f f (F (w ++ t)) = v ++ run e f f t := by
    rcases hF with rfl | ⟨w, v, y, r, hw, hne', h⟩
    · exact ⟨[], [], by simp [Clean], fun _ _ => rfl⟩
    · refine ⟨w, (run e f f v).concat (other e y r true), clean_opposite.mp hw, ?_⟩
      intro t ht
      rw [h t (clean_opposite.mpr ht), run_append]
      change _ ++ run e f _ (other e y r true :: t) = _
      simp [run_other, hne']
  obtain ⟨w, v, hw, hv⟩ := start
  refine ⟨w ++ block e u x, v ++ z, _, _, clean_append hw (clean_block e u x), hx, ?_⟩
  intro t ht
  change run e f f (F ((w ++ block e u x) ++ t)) = _
  simp only [List.append_assoc]
  rw [hv _ (clean_append (clean_block e u x) ht), hz, run_dormant _ _ _ ht]

private theorem Witness.ne_one {A X Y : Type} {e : View A X Y} {F : Function.End (List A)}
    (h : Witness e F) : F ≠ 1 := by
  rintro rfl
  obtain ⟨w, v, x, r, hw, hne, h⟩ := h
  have eqn := h [] (by simp [Clean])
  change w ++ [] = v ++ [own e x r true] at eqn
  rw [List.append_nil] at eqn
  have ha := hw (own e x r true) (by simp [eqn])
  exact hne (by simpa [own, diagonal] using ha)

open Monoid.Coprod

-- Only existence of an alternating representative is needed for faithfulness.
private inductive Reduced {G H : Type} [Group G] [Group H] : Bool → Monoid.Coprod G H → Prop
  | nil (b) : Reduced b 1
  | left {g : G} {w} : g ≠ 1 → Reduced false w → Reduced true (inl g * w)
  | right {h : H} {w} : h ≠ 1 → Reduced true w → Reduced false (inr h * w)

private theorem exists_reduced {G H : Type} [Group G] [Group H] (w : Monoid.Coprod G H) :
    ∃ b, Reduced b w := by
  induction w using induction_on' with
  | one => exact ⟨true, .nil _⟩
  | inl_mul g w ih =>
    by_cases hg : g = 1
    · simpa [hg] using ih
    obtain ⟨b, hr⟩ := ih
    cases hr with
    | nil => exact ⟨_, .left hg (.nil _)⟩
    | @left g' u _ hu =>
      rw [← mul_assoc, ← map_mul]
      by_cases h : g * g' = 1
      · exact ⟨_, by simpa [h] using hu⟩
      · exact ⟨_, .left h hu⟩
    | right hh hu => exact ⟨_, .left hg (.right hh hu)⟩
  | inr_mul h w ih =>
    by_cases hh : h = 1
    · simpa [hh] using ih
    obtain ⟨b, hr⟩ := ih
    cases hr with
    | nil => exact ⟨_, .right hh (.nil _)⟩
    | left hg hu => exact ⟨_, .right hh (.left hg hu)⟩
    | @right h' u _ hu =>
      rw [← mul_assoc, ← map_mul]
      by_cases he : h * h' = 1
      · exact ⟨_, by simpa [he] using hu⟩
      · exact ⟨_, .right he hu⟩

private theorem faithful_lift {A X Y G H : Type} [Group G] [Group H]
    [DecidableEq X] [DecidableEq Y] (e : View A X Y)
    (f : G →* Equiv.Perm (List X)) (h : H →* Equiv.Perm (List Y))
    (tf : ∀ g, TreeMap (f g)) (th : ∀ k, TreeMap (h k))
    (hf_inj : Function.Injective f) (hh_inj : Function.Injective h) :
    Function.Injective (lift (factorAction e f tf) (factorAction (opposite e) h th)) := by
  let act := lift (factorAction e f tf) (factorAction (opposite e) h th)
  have hw {b w} (red : Reduced b w) :
      w = 1 ∨ (if b then Witness e (act w) else Witness (opposite e) (act w)) := by
    induction red with
    | nil => exact Or.inl rfl
    | @left g w hg _ ih =>
      right
      simp only [ite_true]
      rw [map_mul]
      apply grow_witness e (tf g) (fun he => hg (hf_inj (he.trans (map_one f).symm)))
      exact ih.imp (fun eqn => by rw [eqn, map_one]) id
    | @right k w hk _ ih =>
      right
      simp only [Bool.false_eq_true, ite_false]
      rw [map_mul]
      apply grow_witness (opposite e) (th k) (fun he => hk (hh_inj (he.trans (map_one h).symm)))
      have hswap : opposite (opposite e) = e := by
        apply Equiv.ext
        rintro (_ | _) <;> rfl
      rw [hswap]
      exact ih.imp (fun eqn => by rw [eqn, map_one]) id
  apply (injective_iff_map_eq_one act).mpr
  intro w he
  obtain ⟨b, hr⟩ := exists_reduced w
  rcases hw hr with h | h
  · exact h
  · cases b <;> exact False.elim (Witness.ne_one h he)

/--
**Fedorova–Oliynyk theorem (Kourovka Problem 16.85).** For all groups $G$ and $H$, if $G$ and $H$
each act faithfully on a regular rooted tree by finite-state automorphisms, then their free product
$G \ast H$ acts faithfully on some regular rooted tree by finite-state automorphisms.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.85
(V. I. Sushchanskiĭ); resolution: M. Fedorova and A. Oliynyk, Finite automaton actions of free
products of groups, Algebra Discrete Math. 23 (2017), no. 2, 230-236, abstract (for groups G and H
that act faithfully by finite state automorphisms on regular rooted trees, G ∗ H admits a faithful
action by finite state automorphisms on some regular rooted tree) and Theorem 1 (FAut T_n ∗ FAut T_n
is isomorphic to a subgroup of FAut T_3n); Kourovka Archive, Problem 16.85 (Yes, it can),
https://admjournal.luguniv.edu.ua/index.php/adm/article/view/477.
-/
theorem finiteStateFreeProduct_holds : finiteStateFreeProduct := by
  rintro G H _ _ ⟨d, f, hd, hf, hfs⟩ ⟨k, h, hk, hh, hhs⟩
  let alphabet := Letter (Fin d) ⊕ Letter (Fin k)
  let e : View (Fin (Fintype.card alphabet)) (Fin d) (Fin k) := Fintype.equivFin alphabet
  have tf g := TreeMap.ofAut (hfs g).1
  have th j := TreeMap.ofAut (hhs j).1
  let act := lift (factorAction e f tf) (factorAction (opposite e) h th)
  have hact := faithful_lift e f h tf th hf hh
  refine ⟨_, act.toHomPerm, ?_, ?_, ?_⟩
  · let x : Fin d := ⟨0, by omega⟩
    let y : Fin k := ⟨0, by omega⟩
    exact Fintype.one_lt_card_iff.mpr ⟨.inl (x, x, false), .inr (y, y, false), by simp⟩
  · intro u v huv
    apply hact
    funext w
    exact Equiv.congr_fun huv w
  · intro w
    apply (FiniteStateTree.mem_finiteStateAutomorphisms_iff _).mp
    induction w using induction_on with
    | inl g =>
      exact (FiniteStateTree.mem_finiteStateAutomorphisms_iff _).mpr
        (FiniteTreeMap.isFiniteStateAut (run_finite e (hfs g).2))
    | inr j =>
      exact (FiniteStateTree.mem_finiteStateAutomorphisms_iff _).mpr
        (FiniteTreeMap.isFiniteStateAut (run_finite (opposite e) (hhs j).2))
    | mul u v hu hv =>
      rw [map_mul]
      exact Subgroup.mul_mem _ hu hv

end MathlibExt.GroupTheory.FiniteStateFreeProductKourovka16Problem85Wanted
