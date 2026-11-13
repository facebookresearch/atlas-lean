/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Relation

@[expose] public section

namespace MathlibExt.Combinatorics.SimpleGraph.HajnalSzemerediWanted

/-!
# Hajnal–Szemerédi equitable coloring — private development

Short proof of Kierstead–Kostochka (2008). All helpers are private with `hs`
prefix. The public declarations are `exists_equitable_coloring_of_maxDegree_lt`,
which needs no `DecidableEq V` instance, and the Wanted statement
`hajnal_szemeredi_equitable_coloring`, a wrapper around it.
-/

/-- Color class: vertices of `U` colored `c` by `f`. -/
private def hsCls {V C : Type*} [DecidableEq V] [DecidableEq C]
    (U : Finset V) (f : V → C) (c : C) : Finset V :=
  U.filter fun u => f u = c

/-- Neighbours of `v` inside `U`. -/
private def hsNbr {V : Type*} [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (v : V) : Finset V :=
  U.filter fun u => H.Adj v u

/-- Every vertex of `U` gets a color in `K`. -/
private def hsMaps {V C : Type*} [DecidableEq V] [DecidableEq C]
    (U : Finset V) (K : Finset C) (f : V → C) : Prop :=
  ∀ u ∈ U, f u ∈ K

/-- `f` is proper on `U`: adjacent vertices get different colors. -/
private def hsProper {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) (U : Finset V) (f : V → C) : Prop :=
  ∀ u ∈ U, ∀ v ∈ U, H.Adj u v → f u ≠ f v

/-- Every vertex of `U` has fewer than `K.card` neighbours in `U`. -/
private def hsDegLt {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) : Prop :=
  ∀ v ∈ U, (hsNbr H U v).card < K.card

/-- Every color of `K` is used exactly `m` times on `U`. -/
private def hsEquitable {V C : Type*} [DecidableEq V] [DecidableEq C]
    (U : Finset V) (K : Finset C) (f : V → C) (m : ℕ) : Prop :=
  ∀ c ∈ K, (hsCls U f c).card = m

/-- Nearly equitable: class `α₀` is one short, class `β₀` has one extra. -/
private def hsNearly {V C : Type*} [DecidableEq V] [DecidableEq C]
    (U : Finset V) (K : Finset C) (f : V → C) (m : ℕ) (α₀ β₀ : C) : Prop :=
  α₀ ∈ K ∧ β₀ ∈ K ∧ α₀ ≠ β₀ ∧ (hsCls U f α₀).card + 1 = m ∧
    (hsCls U f β₀).card = m + 1 ∧
    ∀ c ∈ K, c ≠ α₀ → c ≠ β₀ → (hsCls U f c).card = m

/-- Auxiliary digraph on colors: `σ → τ` when some vertex of class `σ`
has no neighbour in class `τ`. -/
private def hsEdge {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) (U : Finset V) (K : Finset C)
    (f : V → C) (σ τ : C) : Prop :=
  σ ∈ K ∧ τ ∈ K ∧ σ ≠ τ ∧
    ∃ x ∈ U, f x = σ ∧ ∀ y ∈ U, f y = τ → ¬ H.Adj x y

/-- The avoiding relation: steps of `E` that neither start nor end at `ν`. -/
private def hsAvoid {C : Type*} (E : C → C → Prop) (ν : C) : C → C → Prop :=
  fun σ τ => E σ τ ∧ σ ≠ ν ∧ τ ≠ ν

/-- Colors of `K` that can reach `α₀` in the auxiliary digraph. -/
private noncomputable def hsReachSet {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ : C) : Finset C :=
  @Finset.filter C (fun σ => Relation.ReflTransGen (hsEdge H U K f) σ α₀)
    (fun _ => Classical.propDecidable _) K

/-- Terminal colors: those in the reach set whose every fellow member reaches
`α₀` even while avoiding them. -/
private noncomputable def hsTerminal {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ : C) : Finset C :=
  @Finset.filter C
    (fun σ => ∀ γ ∈ hsReachSet H U K f α₀, γ ≠ σ →
      Relation.ReflTransGen (hsAvoid (hsEdge H U K f) σ) γ α₀)
    (fun _ => Classical.propDecidable _) (hsReachSet H U K f α₀)

private theorem hsMem_cls {V C : Type*} [DecidableEq V] [DecidableEq C]
    (U : Finset V) (f : V → C) (c : C) (u : V) :
    u ∈ hsCls U f c ↔ u ∈ U ∧ f u = c := by
  simp only [hsCls, Finset.mem_filter]

private theorem hsMem_nbr {V : Type*} [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (v u : V) :
    u ∈ hsNbr H U v ↔ u ∈ U ∧ H.Adj v u := by
  simp only [hsNbr, Finset.mem_filter]

private theorem hsMem_reach {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ σ : C) :
    σ ∈ hsReachSet H U K f α₀ ↔
      σ ∈ K ∧ Relation.ReflTransGen (hsEdge H U K f) σ α₀ := by
  simp only [hsReachSet, Finset.mem_filter]

private theorem hsMem_term {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ σ : C) :
    σ ∈ hsTerminal H U K f α₀ ↔
      σ ∈ hsReachSet H U K f α₀ ∧
        ∀ γ ∈ hsReachSet H U K f α₀, γ ≠ σ →
          Relation.ReflTransGen (hsAvoid (hsEdge H U K f) σ) γ α₀ := by
  simp only [hsTerminal, Finset.mem_filter]

/-- A path to `t ≠ ν` either avoids `ν` or first hits `ν` via one step. -/
private theorem hsReach_avoid {C : Type*} (E : C → C → Prop) (ν s t : C)
    (ht : t ≠ ν) (h : Relation.ReflTransGen E s t) :
    Relation.ReflTransGen (hsAvoid E ν) s t ∨
      ∃ c, E ν c ∧ Relation.ReflTransGen (hsAvoid E ν) c t := by
  refine Relation.ReflTransGen.head_induction_on
    (motive := fun a _ => Relation.ReflTransGen (hsAvoid E ν) a t ∨
      ∃ c, E ν c ∧ Relation.ReflTransGen (hsAvoid E ν) c t) h
    (Or.inl Relation.ReflTransGen.refl) ?_
  intro a c hstep hpath ih
  rcases ih with ih | ⟨d, hd1, hd2⟩
  · by_cases haν : a = ν
    · subst haν
      exact Or.inr ⟨_, hstep, ih⟩
    · have hcν : c ≠ ν := by
        rintro rfl
        rcases ih.cases_head with h | ⟨e, he, _⟩
        · exact ht h.symm
        · exact he.2.1 rfl
      exact Or.inl (Relation.ReflTransGen.head
        (show E a c ∧ a ≠ ν ∧ c ≠ ν from ⟨hstep, haν, hcν⟩) ih)
  · exact Or.inr ⟨d, hd1, hd2⟩

/-- Corollary: a nontrivial path starts with one step plus an avoiding tail. -/
private theorem hsReach_avoid_cor {C : Type*} (E : C → C → Prop) {s t : C}
    (hst : s ≠ t) (h : Relation.ReflTransGen E s t) :
    ∃ c, E s c ∧ Relation.ReflTransGen (hsAvoid E s) c t := by
  rcases hsReach_avoid E s s t (fun h => hst h.symm) h with h0 | h1
  · exfalso
    rcases h0.cases_head with h | ⟨d, hd, _⟩
    · exact hst h
    · exact hd.2.1 rfl
  · exact h1

/-- A path can be chosen never to re-enter its starting point. -/
private theorem hsReach_noreentry {C : Type*} (R : C → C → Prop) {s t : C}
    (h : Relation.ReflTransGen R s t) :
    Relation.ReflTransGen (fun x y => R x y ∧ y ≠ s) s t := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hpath hstep ih =>
    by_cases heq : c = s
    · subst heq
      exact Relation.ReflTransGen.refl
    · exact ih.tail ⟨hstep, heq⟩

/-- A path whose every edge towards `t` is an `R'`-edge is an `R'`-path. -/
private theorem hsReach_restrict {C : Type*} (R R' : C → C → Prop) {s t : C}
    (h : Relation.ReflTransGen R s t)
    (hall : ∀ x y, R x y → Relation.ReflTransGen R y t → R' x y) :
    Relation.ReflTransGen R' s t := by
  refine Relation.ReflTransGen.head_induction_on
    (motive := fun a _ => Relation.ReflTransGen R' a t) h
    Relation.ReflTransGen.refl ?_
  intro a c hstep hpath ih
  exact Relation.ReflTransGen.head (hall a c hstep hpath) ih

/-- Additive cancellation of two composed single-vertex moves. -/
private theorem hsArith_cancel {A B Cc : ℕ} {p q r : Prop}
    [Decidable p] [Decidable q] [Decidable r]
    (e1 : A + (if p then 1 else 0) = B + (if r then 1 else 0))
    (e2 : B + (if q then 1 else 0) = Cc + (if p then 1 else 0)) :
    A + (if q then 1 else 0) = Cc + (if r then 1 else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;>
    simp only [hp, hq, hr, ite_true, ite_false] at * <;> omega

/-- Workhorse: a set mapping into `X` fibers over `X`. -/
private theorem hsCount_gen {V C : Type*} [DecidableEq C]
    (s : Finset V) (X : Finset C) (f : V → C)
    (hmaps : ∀ u ∈ s, f u ∈ X) :
    s.card = ∑ c ∈ X, (s.filter fun u => f u = c).card := by
  apply Finset.card_eq_sum_card_fiberwise
  intro u hu
  exact Finset.mem_coe.mpr (hmaps u (Finset.mem_coe.mp hu))

/-- Vertices of `U` with color in `X`, counted by class. -/
private theorem hsCount_class {V C : Type*} [DecidableEq V] [DecidableEq C]
    (U : Finset V) (X : Finset C) (f : V → C) :
    (U.filter fun u => f u ∈ X).card = ∑ c ∈ X, (hsCls U f c).card := by
  have hgen := hsCount_gen (U.filter fun u => f u ∈ X) X f (by
    intro u hu
    simp only [Finset.mem_filter] at hu
    exact hu.2)
  refine hgen.trans ?_
  apply Finset.sum_congr rfl
  intro c hc
  have hfib : (U.filter fun u => f u ∈ X).filter (fun u => f u = c) =
      hsCls U f c := by
    ext u
    simp only [Finset.mem_filter, hsMem_cls]
    exact ⟨fun ⟨⟨huU, _⟩, hfc⟩ => ⟨huU, hfc⟩,
      fun ⟨huU, hfc⟩ => ⟨⟨huU, by rw [hfc]; exact hc⟩, hfc⟩⟩
  rw [hfib]

/-- Total vertex count as a sum of class sizes. -/
private theorem hsCount_total {V C : Type*} [DecidableEq V] [DecidableEq C]
    (U : Finset V) (K : Finset C) (f : V → C) (hmaps : hsMaps U K f) :
    U.card = ∑ c ∈ K, (hsCls U f c).card := by
  have h := hsCount_class U K f
  rw [Finset.filter_true_of_mem (fun u hu => hmaps u hu)] at h
  exact h

/-- Neighbours of `v` with color in `X`, counted by class. -/
private theorem hsCount_nbr {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (X : Finset C) (f : V → C) (v : V) :
    ((U.filter fun u => f u ∈ X).filter fun u => H.Adj v u).card =
      ∑ c ∈ X, (hsNbr H (hsCls U f c) v).card := by
  have hgen := hsCount_gen ((U.filter fun u => f u ∈ X).filter
    fun u => H.Adj v u) X f (by
    intro u hu
    simp only [Finset.mem_filter] at hu
    exact hu.1.2)
  refine hgen.trans ?_
  apply Finset.sum_congr rfl
  intro c hc
  have hfib : ((U.filter fun u => f u ∈ X).filter fun u => H.Adj v u).filter
      (fun u => f u = c) = hsNbr H (hsCls U f c) v := by
    ext u
    simp only [Finset.mem_filter, hsMem_cls, hsMem_nbr]
    exact ⟨fun ⟨⟨⟨huU, _⟩, hadj⟩, hfc⟩ => ⟨⟨huU, hfc⟩, hadj⟩,
      fun ⟨⟨huU, hfc⟩, hadj⟩ => ⟨⟨⟨huU, by rw [hfc]; exact hc⟩, hadj⟩, hfc⟩⟩
  rw [hfib]

/-- The class of a color inside a subset. -/
private theorem hsCls_sub {V C : Type*} [DecidableEq V] [DecidableEq C]
    (U' U : Finset V) (f : V → C) (c : C) (h : U' ⊆ U) :
    hsCls U' f c = (hsCls U f c).filter (· ∈ U') := by
  ext u
  simp only [Finset.mem_filter, hsMem_cls]
  exact ⟨fun ⟨huU', hfc⟩ => ⟨⟨h huU', hfc⟩, huU'⟩,
    fun ⟨⟨_, hfc⟩, huU'⟩ => ⟨huU', hfc⟩⟩

/-- Moving one vertex to a color with no neighbours there. -/
private theorem hsMove {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V)
    (U : Finset V) (K : Finset C) (f : V → C)
    (hmaps : hsMaps U K f) (hproper : hsProper H U f)
    (x : V) (hx : x ∈ U) (c : C) (hc : c ∈ K)
    (hno : ∀ u ∈ U, f u = c → ¬ H.Adj x u) :
    hsMaps U K (Function.update f x c) ∧
    hsProper H U (Function.update f x c) ∧
    (∀ u, u ≠ x → Function.update f x c u = f u) ∧
    ∀ d, (hsCls U (Function.update f x c) d).card + (if d = f x then 1 else 0) =
      (hsCls U f d).card + (if d = c then 1 else 0) := by
  by_cases hcf : c = f x
  · subst hcf
    have hff : Function.update f x (f x) = f := by
      funext u
      by_cases hux : u = x
      · rw [hux]
        exact Function.update_self x (f x) f
      · exact Function.update_of_ne hux (f x) f
    simp only [hff]
    exact ⟨hmaps, hproper, fun _ _ => trivial, fun _ => trivial⟩
  · have hne : f x ≠ c := fun h => hcf h.symm
    have hagree : ∀ u, u ≠ x → Function.update f x c u = f u :=
      fun u hu => Function.update_of_ne hu c f
    have hmaps' : hsMaps U K (Function.update f x c) := by
      intro u hu
      by_cases hux : u = x
      · rw [hux, Function.update_self]
        exact hc
      · rw [Function.update_of_ne hux]
        exact hmaps u hu
    have hproper' : hsProper H U (Function.update f x c) := by
      intro u hu v hv hadj hcon
      by_cases hux : u = x
      · by_cases hvx : v = x
        · subst hux; subst hvx
          exact absurd hadj H.irrefl
        · have h1 : Function.update f x c u = c := by
            rw [hux]
            exact Function.update_self x c f
          rw [h1, hagree v hvx] at hcon
          have hadj' : H.Adj x v := by
            rw [← hux]
            exact hadj
          exact hno v hv hcon.symm hadj'
      · by_cases hvx : v = x
        · have h2 : Function.update f x c v = c := by
            rw [hvx]
            exact Function.update_self x c f
          rw [hagree u hux, h2] at hcon
          have hadj' : H.Adj x u := by
            rw [← hvx]
            exact H.adj_symm hadj
          exact hno u hu hcon hadj'
        · rw [hagree u hux, hagree v hvx] at hcon
          exact hproper u hu v hv hadj hcon
    refine ⟨hmaps', hproper', hagree, ?_⟩
    have hxnc : x ∉ hsCls U f c := by
      rw [hsMem_cls]
      exact fun ⟨_, hfxc⟩ => hne hfxc
    have hxmem : x ∈ hsCls U f (f x) := by
      rw [hsMem_cls]
      exact ⟨hx, rfl⟩
    have hcls_ins : hsCls U (Function.update f x c) c = insert x (hsCls U f c) := by
      ext u
      simp only [hsMem_cls, Finset.mem_insert]
      constructor
      · rintro ⟨huU, hud⟩
        by_cases hux : u = x
        · subst hux
          exact Or.inl rfl
        · rw [Function.update_of_ne hux] at hud
          exact Or.inr ⟨huU, hud⟩
      · rintro (rfl | ⟨huU, hud⟩)
        · exact ⟨hx, Function.update_self u c f⟩
        · refine ⟨huU, ?_⟩
          by_cases hux : u = x
          · subst hux
            rw [Function.update_self]
          · rw [Function.update_of_ne hux]
            exact hud
    have hcls_erase : hsCls U (Function.update f x c) (f x) =
        (hsCls U f (f x)).erase x := by
      ext u
      simp only [hsMem_cls, Finset.mem_erase]
      constructor
      · rintro ⟨huU, hud⟩
        have hux : u ≠ x := by
          rintro rfl
          rw [Function.update_self] at hud
          exact hne hud.symm
        rw [Function.update_of_ne hux] at hud
        exact ⟨hux, huU, hud⟩
      · rintro ⟨hux, huU, hud⟩
        refine ⟨huU, ?_⟩
        by_cases hux' : u = x
        · exact (hux hux').elim
        · rw [Function.update_of_ne hux']
          exact hud
    have hcls_eq : ∀ d, d ≠ c → d ≠ f x →
        hsCls U (Function.update f x c) d = hsCls U f d := by
      intro d hdc hdfx
      ext u
      simp only [hsMem_cls]
      constructor
      · rintro ⟨huU, hud⟩
        by_cases hux : u = x
        · subst hux
          rw [Function.update_self] at hud
          exact (hdc hud.symm).elim
        · rw [Function.update_of_ne hux] at hud
          exact ⟨huU, hud⟩
      · rintro ⟨huU, hud⟩
        refine ⟨huU, ?_⟩
        by_cases hux : u = x
        · subst hux
          rw [Function.update_self]
          exact (hdfx hud.symm).elim
        · rw [Function.update_of_ne hux]
          exact hud
    intro d
    by_cases hdc : d = c
    · subst hdc
      rw [hcls_ins, Finset.card_insert_of_notMem hxnc, ite_eq_right hcf,
        ite_eq_left rfl]
    · by_cases hdfx : d = f x
      · subst hdfx
        have hpos : 0 < (hsCls U f (f x)).card :=
          Finset.card_pos.mpr ⟨x, hxmem⟩
        rw [hcls_erase, Finset.card_erase_of_mem hxmem, ite_eq_left rfl,
          ite_eq_right hne]
        omega
      · rw [hcls_eq d hdc hdfx, ite_eq_right hdfx, ite_eq_right hdc]

/-- Kempe-style recoloring along a path in the auxiliary digraph. -/
private theorem hsShiftPath {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V)
    (U : Finset V) (K : Finset C) (f : V → C)
    (hmaps : hsMaps U K f) (hproper : hsProper H U f)
    (S : Finset C) (hS : S ⊆ K) (s : C) (hs : s ∈ S) (t : C)
    (hpath : Relation.ReflTransGen
      (fun σ τ => hsEdge H U K f σ τ ∧ σ ∈ S ∧ τ ∈ S) s t) :
    ∃ f', hsMaps U K f' ∧ hsProper H U f' ∧
      (∀ u ∈ U, f u ∉ S → f' u = f u) ∧
      (∀ u ∈ U, f u ∈ S → f' u ∈ S) ∧
      ∀ d, (hsCls U f' d).card + (if d = s then 1 else 0) =
        (hsCls U f d).card + (if d = t then 1 else 0) := by
  induction S using Finset.strongInduction generalizing f s with
  | _ S ih =>
    by_cases hst : s = t
    · subst hst
      exact ⟨f, hmaps, hproper, fun u _ _ => rfl, fun u _ h => h, fun _ => rfl⟩
    · obtain ⟨c, ⟨hedge_sc, _hsS, hcS⟩, hpathc⟩ :=
        hsReach_avoid_cor _ hst hpath
      have hpathc' := hsReach_noreentry _ hpathc
      obtain ⟨_hsK, hcK, hsc_ne, x, hxU, hfx, hnowit⟩ := hedge_sc
      obtain ⟨hmaps1, hproper1, hagree1, hid1⟩ :=
        hsMove H U K f hmaps hproper x hxU c hcK hnowit
      set f₁ := Function.update f x c with hf₁def
      have hfx1 : f₁ x = c := by
        rw [hf₁def]
        exact Function.update_self x c f
      have hstep1 : ∀ d e,
          hsAvoid (fun σ τ => hsEdge H U K f σ τ ∧ σ ∈ S ∧ τ ∈ S) s d e → e ≠ c →
          (hsEdge H U K f₁ d e ∧ d ∈ S.erase s ∧ e ∈ S.erase s) := by
        intro d e h hec
        obtain ⟨⟨hedge, hdS, heS⟩, hdne_s, hene_s⟩ := h
        obtain ⟨hdK, heK, hde_ne, w, hwU, hfw, hwwit⟩ := hedge
        have hwx : w ≠ x := by
          intro hwx
          rw [hwx, hfx] at hfw
          exact hdne_s hfw.symm
        have hfw1 : f₁ w = d := by
          rw [hagree1 w hwx]
          exact hfw
        have hwwit1 : ∀ y ∈ U, f₁ y = e → ¬ H.Adj w y := by
          intro y hyU hfy1 hadj
          have hyx : y ≠ x := by
            intro hyx
            rw [hyx, hf₁def, Function.update_self] at hfy1
            exact hec hfy1.symm
          rw [hagree1 y hyx] at hfy1
          exact hwwit y hyU hfy1 hadj
        exact ⟨⟨hdK, heK, hde_ne, w, hwU, hfw1, hwwit1⟩,
          Finset.mem_erase.mpr ⟨hdne_s, hdS⟩,
          Finset.mem_erase.mpr ⟨hene_s, heS⟩⟩
      have hsub : ∀ d e,
          (fun x y => hsAvoid (fun σ τ => hsEdge H U K f σ τ ∧ σ ∈ S ∧ τ ∈ S)
            s x y ∧ y ≠ c) d e →
          (fun σ τ => hsEdge H U K f₁ σ τ ∧ σ ∈ S.erase s ∧ τ ∈ S.erase s)
            d e := by
        intro d e h
        obtain ⟨hstep, hne⟩ := h
        exact hstep1 d e hstep hne
      have hpath1 : Relation.ReflTransGen
          (fun σ τ => hsEdge H U K f₁ σ τ ∧ σ ∈ S.erase s ∧ τ ∈ S.erase s) c t :=
        hsReach_restrict _ _ hpathc' (fun d e h _ => hsub d e h)
      obtain ⟨f', hmaps', hproper', hagree', hstay', hid'⟩ :=
        ih (S.erase s) (Finset.erase_ssubset hs) f₁
          hmaps1 hproper1 ((Finset.erase_subset s S).trans hS) c
          (Finset.mem_erase.mpr ⟨Ne.symm hsc_ne, hcS⟩) hpath1
      have hsize : ∀ d, (hsCls U f' d).card + (if d = s then 1 else 0) =
          (hsCls U f d).card + (if d = t then 1 else 0) := by
        intro d
        have e2 := hid1 d
        rw [hfx] at e2
        exact hsArith_cancel (hid' d) e2
      have hagree_out : ∀ u ∈ U, f u ∉ S → f' u = f u := by
        intro u huU hfuS
        have hux : u ≠ x := by
          intro hux
          rw [hux, hfx] at hfuS
          exact hfuS hs
        have hfu1 : f₁ u = f u := hagree1 u hux
        have hne1 : f₁ u ∉ S := by
          rw [hfu1]
          exact hfuS
        have hfu1S : f₁ u ∉ S.erase s :=
          fun h => hne1 (Finset.erase_subset s S h)
        exact (hagree' u huU hfu1S).trans hfu1
      have hstay_in : ∀ u ∈ U, f u ∈ S → f' u ∈ S := by
        intro u huU hfuS
        have hf1uS : f₁ u ∈ S := by
          by_cases hux : u = x
          · rw [hux, hfx1]
            exact hcS
          · rw [hagree1 u hux]
            exact hfuS
        by_cases hf1e : f₁ u ∈ S.erase s
        · exact Finset.erase_subset s S (hstay' u huU hf1e)
        · rw [hagree' u huU hf1e]
          exact hf1uS
      exact ⟨f', hmaps', hproper', hagree_out, hstay_in, hsize⟩

/-- If the big class reaches the small one, shift along the path. -/
private theorem hsCase0 {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (m : ℕ) (α₀ β₀ : C)
    (hmaps : hsMaps U K f) (hproper : hsProper H U f)
    (hnear : hsNearly U K f m α₀ β₀)
    (hmem : β₀ ∈ hsReachSet H U K f α₀) :
    ∃ g, hsMaps U K g ∧ hsProper H U g ∧ hsEquitable U K g m := by
  obtain ⟨_hαK, hβK, hne, hαm, hβm, hrest⟩ := hnear
  rw [hsMem_reach] at hmem
  obtain ⟨_, hpath⟩ := hmem
  have hpathK : Relation.ReflTransGen
      (fun σ τ => hsEdge H U K f σ τ ∧ σ ∈ K ∧ τ ∈ K) β₀ α₀ :=
    hsReach_restrict _ _ hpath (fun d e h _ => ⟨h, h.1, h.2.1⟩)
  obtain ⟨f', hmaps', hproper', _, _, hid'⟩ :=
    hsShiftPath H U K f hmaps hproper K Finset.Subset.rfl β₀ hβK α₀ hpathK
  refine ⟨f', hmaps', hproper', ?_⟩
  intro d hdK
  have e := hid' d
  by_cases hdb : d = β₀
  · subst hdb
    have e1 : (if d = d then (1 : ℕ) else 0) = 1 := ite_eq_left rfl
    have e2 : (if d = α₀ then (1 : ℕ) else 0) = 0 :=
      ite_eq_right (fun h => hne h.symm)
    omega
  · by_cases hda : d = α₀
    · subst hda
      have e1 : (if d = β₀ then (1 : ℕ) else 0) = 0 := ite_eq_right hdb
      have e2 : (if d = d then (1 : ℕ) else 0) = 1 := ite_eq_left rfl
      omega
    · have e1 : (if d = β₀ then (1 : ℕ) else 0) = 0 := ite_eq_right hdb
      have e2 : (if d = α₀ then (1 : ℕ) else 0) = 0 := ite_eq_right hda
      have hdm := hrest d hdK hda hdb
      omega

/-- Setup: the 𝒜/ℬ split of colors and the A/B split of vertices. -/
private theorem hsStruct_setup {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (m : ℕ) (α₀ β₀ : C)
    (hmaps : hsMaps U K f) (hnear : hsNearly U K f m α₀ β₀)
    (hβ₀ : β₀ ∉ hsReachSet H U K f α₀) :
    α₀ ∈ hsReachSet H U K f α₀ ∧
    β₀ ∈ K \ hsReachSet H U K f α₀ ∧
    Disjoint (U.filter fun u => f u ∈ hsReachSet H U K f α₀)
      (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀) ∧
    U.filter (fun u => f u ∈ hsReachSet H U K f α₀) ∪
      U.filter (fun u => f u ∈ K \ hsReachSet H U K f α₀) = U ∧
    (K \ hsReachSet H U K f α₀).card + (hsReachSet H U K f α₀).card
      = K.card := by
  have hαK : α₀ ∈ K := hnear.1
  have hβK : β₀ ∈ K := hnear.2.1
  refine ⟨(hsMem_reach H U K f α₀ α₀).mpr ⟨hαK, Relation.ReflTransGen.refl⟩,
    Finset.mem_sdiff.mpr ⟨hβK, hβ₀⟩, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro w hwA hwB
    simp only [Finset.mem_filter] at hwA hwB
    exact (Finset.mem_sdiff.mp hwB.2).2 hwA.2
  · ext u
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨huU, _⟩ | ⟨huU, _⟩) <;> exact huU
    · intro huU
      by_cases h : f u ∈ hsReachSet H U K f α₀
      · exact Or.inl ⟨huU, h⟩
      · exact Or.inr ⟨huU, Finset.mem_sdiff.mpr ⟨hmaps u huU, h⟩⟩
  · have hsub : hsReachSet H U K f α₀ ⊆ K := by
      intro σ hσ
      exact ((hsMem_reach H U K f α₀ σ).mp hσ).1
    exact Finset.card_sdiff_add_card_eq_card hsub

/-- Both sides of the color split are nonempty; ℬ is smaller than K. -/
private theorem hsStruct_bfacts {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (m : ℕ) (α₀ β₀ : C)
    (hmaps : hsMaps U K f) (hnear : hsNearly U K f m α₀ β₀)
    (hβ₀ : β₀ ∉ hsReachSet H U K f α₀) :
    1 ≤ (K \ hsReachSet H U K f α₀).card ∧
    (K \ hsReachSet H U K f α₀).card < K.card := by
  obtain ⟨hαA, hβB, _, _, hKcard⟩ :=
    hsStruct_setup H U K f m α₀ β₀ hmaps hnear hβ₀
  have ha1 : 1 ≤ (hsReachSet H U K f α₀).card :=
    Finset.card_pos.mpr ⟨α₀, hαA⟩
  have hb1 : 1 ≤ (K \ hsReachSet H U K f α₀).card :=
    Finset.card_pos.mpr ⟨β₀, hβB⟩
  exact ⟨hb1, by omega⟩

/-- Every vertex of B has a neighbour in each 𝒜-class. -/
private theorem hsStruct_nbrA {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ : C)
    (hmaps : hsMaps U K f) :
    ∀ z ∈ U.filter (fun u => f u ∈ K \ hsReachSet H U K f α₀),
    ∀ σ ∈ hsReachSet H U K f α₀, ∃ w ∈ hsCls U f σ, H.Adj z w := by
  intro z hz σ hσA
  have hσK : σ ∈ K := ((hsMem_reach H U K f α₀ σ).mp hσA).1
  have hσpath : Relation.ReflTransGen (hsEdge H U K f) σ α₀ :=
    ((hsMem_reach H U K f α₀ σ).mp hσA).2
  have hzU : z ∈ U := (Finset.mem_filter.mp hz).1
  have hfzB : f z ∈ K \ hsReachSet H U K f α₀ := (Finset.mem_filter.mp hz).2
  by_cases h : ∃ w ∈ hsCls U f σ, H.Adj z w
  · exact h
  · exfalso
    have hnowit : ∀ y ∈ U, f y = σ → ¬ H.Adj z y := by
      intro y hyU hfy hadj
      exact h ⟨y, (hsMem_cls U f σ y).mpr ⟨hyU, hfy⟩, hadj⟩
    have hfzK : f z ∈ K := hmaps z hzU
    have hedge : hsEdge H U K f (f z) σ := by
      refine ⟨hfzK, hσK, ?_, z, hzU, rfl, hnowit⟩
      intro hcon
      rw [hcon] at hfzB
      exact (Finset.mem_sdiff.mp hfzB).2 hσA
    have hreach : Relation.ReflTransGen (hsEdge H U K f) (f z) α₀ :=
      Relation.ReflTransGen.head hedge hσpath
    have hmemA : f z ∈ hsReachSet H U K f α₀ :=
      (hsMem_reach H U K f α₀ (f z)).mpr ⟨hfzK, hreach⟩
    exact (Finset.mem_sdiff.mp hfzB).2 hmemA

/-- Degree bounds for vertices of B into A and B. -/
private theorem hsStruct_degB {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (m : ℕ) (α₀ β₀ : C)
    (hmaps : hsMaps U K f) (hdeg : hsDegLt H U K)
    (hnear : hsNearly U K f m α₀ β₀)
    (hβ₀ : β₀ ∉ hsReachSet H U K f α₀) :
    ∀ z ∈ U.filter (fun u => f u ∈ K \ hsReachSet H U K f α₀),
      (hsReachSet H U K f α₀).card ≤
        (hsNbr H (U.filter fun u => f u ∈ hsReachSet H U K f α₀) z).card ∧
      (hsNbr H (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀) z).card <
        (K \ hsReachSet H U K f α₀).card := by
  intro z hz
  obtain ⟨_, _, hABdisj, hABunion, hKcard⟩ :=
    hsStruct_setup H U K f m α₀ β₀ hmaps hnear hβ₀
  have hge : ∀ c ∈ hsReachSet H U K f α₀,
      1 ≤ (hsNbr H (hsCls U f c) z).card := by
    intro c hcA
    obtain ⟨w, hwcls, hadj⟩ := hsStruct_nbrA H U K f α₀ hmaps z hz c hcA
    have hmem : w ∈ hsNbr H (hsCls U f c) z :=
      (hsMem_nbr H _ _ _).mpr ⟨hwcls, hadj⟩
    exact Finset.card_pos.mpr ⟨w, hmem⟩
  have hAle : (hsReachSet H U K f α₀).card ≤
      (hsNbr H (U.filter fun u => f u ∈ hsReachSet H U K f α₀) z).card := by
    calc (hsReachSet H U K f α₀).card
        = ∑ _c ∈ hsReachSet H U K f α₀, 1 := by simp
      _ ≤ ∑ c ∈ hsReachSet H U K f α₀, (hsNbr H (hsCls U f c) z).card :=
        Finset.sum_le_sum hge
      _ = (hsNbr H (U.filter fun u => f u ∈ hsReachSet H U K f α₀) z).card :=
        (hsCount_nbr H U (hsReachSet H U K f α₀) f z).symm
  have hsplit : (hsNbr H U z).card =
      (hsNbr H (U.filter fun u => f u ∈ hsReachSet H U K f α₀) z).card +
      (hsNbr H (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀) z).card := by
    have h1 : hsNbr H U z =
        hsNbr H (U.filter fun u => f u ∈ hsReachSet H U K f α₀) z ∪
        hsNbr H (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀) z := by
      conv_lhs => rw [← hABunion]
      simp only [hsNbr, Finset.filter_union]
    have h2 : Disjoint
        (hsNbr H (U.filter fun u => f u ∈ hsReachSet H U K f α₀) z)
        (hsNbr H (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀) z) := by
      rw [Finset.disjoint_left]
      intro w hwA hwB
      rw [hsMem_nbr] at hwA hwB
      exact (Finset.disjoint_left.mp hABdisj hwA.1) hwB.1
    rw [h1, Finset.card_union_of_disjoint h2]
  have hzU : z ∈ U := (Finset.mem_filter.mp hz).1
  have hdegz : (hsNbr H U z).card < K.card := hdeg z hzU
  exact ⟨hAle, by omega⟩

/-- The sizes of A and B. -/
private theorem hsStruct_cards {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (m : ℕ) (α₀ β₀ : C)
    (hnear : hsNearly U K f m α₀ β₀)
    (hβ₀ : β₀ ∉ hsReachSet H U K f α₀) :
    (U.filter fun u => f u ∈ hsReachSet H U K f α₀).card + 1 =
      (hsReachSet H U K f α₀).card * m ∧
    (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).card =
      (K \ hsReachSet H U K f α₀).card * m + 1 := by
  obtain ⟨hαK, hβK, _hne, hαm, hβm, hrest⟩ := hnear
  have hαA : α₀ ∈ hsReachSet H U K f α₀ :=
    (hsMem_reach H U K f α₀ α₀).mpr ⟨hαK, Relation.ReflTransGen.refl⟩
  have hβB : β₀ ∈ K \ hsReachSet H U K f α₀ :=
    Finset.mem_sdiff.mpr ⟨hβK, hβ₀⟩
  have hAcount := hsCount_class U (hsReachSet H U K f α₀) f
  have hAterms : ∀ c ∈ hsReachSet H U K f α₀,
      (hsCls U f c).card + (if c = α₀ then 1 else 0) = m := by
    intro c hcA
    by_cases hca : c = α₀
    · subst hca
      have e1 : (if c = c then (1 : ℕ) else 0) = 1 := ite_eq_left rfl
      omega
    · have hcb : c ≠ β₀ := by
        intro hcb
        rw [hcb] at hcA
        exact (Finset.mem_sdiff.mp hβB).2 hcA
      have e0 : (if c = α₀ then (1 : ℕ) else 0) = 0 := ite_eq_right hca
      have hdm := hrest c ((hsMem_reach H U K f α₀ c).mp hcA).1 hca hcb
      omega
  have hAind : ∑ c ∈ hsReachSet H U K f α₀, (if c = α₀ then (1 : ℕ) else 0)
      = 1 := by
    have h0 : ∀ b ∈ hsReachSet H U K f α₀, b ≠ α₀ →
        (if b = α₀ then (1 : ℕ) else 0) = 0 := fun b _ hb => ite_eq_right hb
    have h1 := Finset.sum_eq_ite (s := hsReachSet H U K f α₀)
      (f := fun c => if c = α₀ then (1 : ℕ) else 0) α₀ h0
    simp only [hαA] at h1
    simpa using h1
  have hconstA : ∑ _c ∈ hsReachSet H U K f α₀, m =
      (hsReachSet H U K f α₀).card * m := by
    rw [Finset.sum_const, smul_eq_mul]
  have hA : (U.filter fun u => f u ∈ hsReachSet H U K f α₀).card + 1 =
      (hsReachSet H U K f α₀).card * m := by
    have hsum : ∑ c ∈ hsReachSet H U K f α₀,
        ((hsCls U f c).card + (if c = α₀ then 1 else 0)) =
        ∑ _c ∈ hsReachSet H U K f α₀, m :=
      Finset.sum_congr rfl (fun c hc => hAterms c hc)
    rw [Finset.sum_add_distrib] at hsum
    omega
  have hBcount := hsCount_class U (K \ hsReachSet H U K f α₀) f
  have hBterms : ∀ c ∈ K \ hsReachSet H U K f α₀,
      (hsCls U f c).card = m + (if c = β₀ then 1 else 0) := by
    intro c hcB
    have hcK : c ∈ K := (Finset.mem_sdiff.mp hcB).1
    by_cases hcb : c = β₀
    · subst hcb
      have e1 : (if c = c then (1 : ℕ) else 0) = 1 := ite_eq_left rfl
      omega
    · have hca : c ≠ α₀ := by
        intro hca
        rw [hca] at hcB
        exact (Finset.mem_sdiff.mp hcB).2 hαA
      have e0 : (if c = β₀ then (1 : ℕ) else 0) = 0 := ite_eq_right hcb
      have hdm := hrest c hcK hca hcb
      omega
  have hBind : ∑ c ∈ K \ hsReachSet H U K f α₀, (if c = β₀ then (1 : ℕ) else 0)
      = 1 := by
    have h0 : ∀ b ∈ K \ hsReachSet H U K f α₀, b ≠ β₀ →
        (if b = β₀ then (1 : ℕ) else 0) = 0 := fun b _ hb => ite_eq_right hb
    have h1 := Finset.sum_eq_ite (s := K \ hsReachSet H U K f α₀)
      (f := fun c => if c = β₀ then (1 : ℕ) else 0) β₀ h0
    simp only [hβB] at h1
    simpa using h1
  have hconstB : ∑ _c ∈ K \ hsReachSet H U K f α₀, m =
      (K \ hsReachSet H U K f α₀).card * m := by
    rw [Finset.sum_const, smul_eq_mul]
  have hB : (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).card =
      (K \ hsReachSet H U K f α₀).card * m + 1 := by
    have hsum : ∑ c ∈ K \ hsReachSet H U K f α₀, (hsCls U f c).card =
        ∑ c ∈ K \ hsReachSet H U K f α₀, (m + (if c = β₀ then 1 else 0)) :=
      Finset.sum_congr rfl (fun c hc => hBterms c hc)
    rw [Finset.sum_add_distrib] at hsum
    omega
  exact ⟨hA, hB⟩

/-- There are at least two colors in 𝒜. -/
private theorem hsStruct_age2 {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (m : ℕ) (α₀ β₀ : C)
    (hmaps : hsMaps U K f) (hdeg : hsDegLt H U K)
    (hnear : hsNearly U K f m α₀ β₀)
    (hβ₀ : β₀ ∉ hsReachSet H U K f α₀) :
    2 ≤ (hsReachSet H U K f α₀).card := by
  obtain ⟨hαA, _, _, _, hKcard⟩ :=
    hsStruct_setup H U K f m α₀ β₀ hmaps hnear hβ₀
  obtain ⟨_, hBcard⟩ := hsStruct_cards H U K f m α₀ β₀ hnear hβ₀
  rw [mul_comm] at hBcard
  by_cases ha2 : 2 ≤ (hsReachSet H U K f α₀).card
  · exact ha2
  · exfalso
    have ha1 : 1 ≤ (hsReachSet H U K f α₀).card :=
      Finset.card_pos.mpr ⟨α₀, hαA⟩
    have ha : (hsReachSet H U K f α₀).card = 1 := by omega
    have hBle : ∀ w ∈ hsCls U f α₀,
        (hsNbr H (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀) w).card ≤
        (K \ hsReachSet H U K f α₀).card := by
      intro w hwT
      have hwU : w ∈ U := ((hsMem_cls U f α₀ w).mp hwT).1
      have hsub : hsNbr H (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀) w ⊆
          hsNbr H U w := by
        intro v hv
        rw [hsMem_nbr] at hv ⊢
        exact ⟨(Finset.mem_filter.mp hv.1).1, hv.2⟩
      have hle := Finset.card_le_card hsub
      have hlt := hdeg w hwU
      omega
    have hTcard : (hsCls U f α₀).card + 1 = m := hnear.2.2.2.1
    have hmul : (hsCls U f α₀).card *
        (K \ hsReachSet H U K f α₀).card + (K \ hsReachSet H U K f α₀).card =
        m * (K \ hsReachSet H U K f α₀).card := by
      have htmp : ((hsCls U f α₀).card + 1) *
          (K \ hsReachSet H U K f α₀).card =
          m * (K \ hsReachSet H U K f α₀).card := by
        rw [hTcard]
      rw [Nat.add_mul, Nat.one_mul] at htmp
      exact htmp
    have hm : ∀ z ∈ U.filter (fun u => f u ∈ K \ hsReachSet H U K f α₀),
        1 ≤ ((hsCls U f α₀).bipartiteAbove (fun z w => H.Adj w z) z).card := by
      intro z hzB
      obtain ⟨w, hwcls, hadj⟩ := hsStruct_nbrA H U K f α₀ hmaps z hzB α₀ hαA
      have hmem : w ∈
          (hsCls U f α₀).bipartiteAbove (fun z w => H.Adj w z) z := by
        rw [Finset.mem_bipartiteAbove]
        exact ⟨hwcls, H.adj_symm hadj⟩
      exact Finset.card_pos.mpr ⟨w, hmem⟩
    have hn : ∀ w ∈ hsCls U f α₀,
        ((U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).bipartiteBelow
          (fun z w => H.Adj w z) w).card ≤
        (K \ hsReachSet H U K f α₀).card := by
      intro w hwT
      have hle : (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).bipartiteBelow
          (fun z w => H.Adj w z) w ⊆
          hsNbr H (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀) w := by
        intro z hz
        rw [Finset.mem_bipartiteBelow] at hz
        rw [hsMem_nbr]
        exact ⟨hz.1, hz.2⟩
      exact (Finset.card_le_card hle).trans (hBle w hwT)
    have hdc := Finset.card_nsmul_le_card_nsmul (r := fun z w => H.Adj w z)
      (s := U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀)
      (t := hsCls U f α₀) hm hn
    simp only [smul_eq_mul, mul_one] at hdc
    omega

/-- The small class is not terminal. -/
private theorem hsStruct_nterm {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (m : ℕ) (α₀ β₀ : C)
    (hmaps : hsMaps U K f) (hdeg : hsDegLt H U K)
    (hnear : hsNearly U K f m α₀ β₀)
    (hβ₀ : β₀ ∉ hsReachSet H U K f α₀) :
    α₀ ∉ hsTerminal H U K f α₀ := by
  intro hmem
  obtain ⟨_, hterm⟩ := (hsMem_term H U K f α₀ α₀).mp hmem
  have ha2 := hsStruct_age2 H U K f m α₀ β₀ hmaps hdeg hnear hβ₀
  obtain ⟨γ, hγA, hγne⟩ : ∃ γ ∈ hsReachSet H U K f α₀, γ ≠ α₀ := by
    by_contra hcon
    have hsub : hsReachSet H U K f α₀ ⊆ {α₀} := by
      intro γ hγA
      rw [Finset.mem_singleton]
      by_contra hne
      exact hcon ⟨γ, hγA, hne⟩
    have hle : (hsReachSet H U K f α₀).card ≤ 1 := by
      have hle2 := Finset.card_le_card hsub
      rwa [Finset.card_singleton] at hle2
    omega
  have hpath := hterm γ hγA hγne
  rcases hpath.cases_tail with h | ⟨c, _, _, _, hαne⟩
  · exact hγne h.symm
  · exact hαne rfl

/-- Terminal classes all have size m. -/
private theorem hsStruct_term {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (m : ℕ) (α₀ β₀ : C)
    (hmaps : hsMaps U K f) (hdeg : hsDegLt H U K)
    (hnear : hsNearly U K f m α₀ β₀)
    (hβ₀ : β₀ ∉ hsReachSet H U K f α₀) :
    (∀ σ ∈ hsTerminal H U K f α₀, (hsCls U f σ).card = m) ∧
    (U.filter fun u => f u ∈ hsTerminal H U K f α₀).card =
      (hsTerminal H U K f α₀).card * m := by
  have hnt := hsStruct_nterm H U K f m α₀ β₀ hmaps hdeg hnear hβ₀
  obtain ⟨_, _, _, _, _, hrest⟩ := hnear
  have hall : ∀ σ ∈ hsTerminal H U K f α₀, (hsCls U f σ).card = m := by
    intro σ hσT
    have hσA : σ ∈ hsReachSet H U K f α₀ :=
      ((hsMem_term H U K f α₀ σ).mp hσT).1
    have hσα : σ ≠ α₀ := by
      intro heq
      subst heq
      exact hnt hσT
    have hσβ : σ ≠ β₀ := by
      intro heq
      rw [heq] at hσA
      exact hβ₀ hσA
    have hσK : σ ∈ K := ((hsMem_reach H U K f α₀ σ).mp hσA).1
    exact hrest σ hσK hσα hσβ
  refine ⟨hall, ?_⟩
  have hcount := hsCount_class U (hsTerminal H U K f α₀) f
  have hsum : ∑ c ∈ hsTerminal H U K f α₀, (hsCls U f c).card =
      ∑ _c ∈ hsTerminal H U K f α₀, m :=
    Finset.sum_congr rfl (fun c hc => hall c hc)
  have hconst : ∑ _c ∈ hsTerminal H U K f α₀, m =
      (hsTerminal H U K f α₀).card * m := by
    rw [Finset.sum_const, smul_eq_mul]
  omega

/-- Recolor B minus one vertex with the colors ℬ. -/
private theorem hsRecolorB {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (m : ℕ) (α₀ β₀ : C)
    (hmaps : hsMaps U K f) (hproper : hsProper H U f) (hdeg : hsDegLt H U K)
    (hnear : hsNearly U K f m α₀ β₀)
    (hβ₀ : β₀ ∉ hsReachSet H U K f α₀)
    (hIH : ∀ (K' : Finset C) (U' : Finset V) (f' : V → C) (m' : ℕ) (α' β' : C),
      K'.card < K.card → hsMaps U' K' f' → hsProper H U' f' → hsDegLt H U' K' →
      hsNearly U' K' f' m' α' β' → ∃ g, hsMaps U' K' g ∧ hsProper H U' g ∧
        hsEquitable U' K' g m')
    (y : V) (hy : y ∈ U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀) :
    ∃ g, hsMaps ((U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y)
        (K \ hsReachSet H U K f α₀) g ∧
      hsProper H ((U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y)
        g ∧
      hsEquitable ((U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y)
        (K \ hsReachSet H U K f α₀) g m := by
  have hyU : y ∈ U := (Finset.mem_filter.mp hy).1
  have hfyB : f y ∈ K \ hsReachSet H U K f α₀ := (Finset.mem_filter.mp hy).2
  have hBsub : (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y ⊆ U :=
    (Finset.erase_subset y _).trans (Finset.filter_subset _ _)
  have hclsB : ∀ c ∈ K \ hsReachSet H U K f α₀,
      hsCls ((U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y) f c =
      (hsCls U f c).erase y := by
    intro c hcB
    rw [hsCls_sub _ _ _ _ hBsub]
    conv_rhs => rw [← Finset.filter_ne']
    apply Finset.filter_congr
    intro u hu
    have huU : u ∈ U := ((hsMem_cls U f c u).mp hu).1
    have hfc : f u = c := ((hsMem_cls U f c u).mp hu).2
    rw [Finset.mem_erase]
    constructor
    · intro h
      exact h.1
    · intro h
      exact ⟨h, Finset.mem_filter.mpr ⟨huU, by rw [hfc]; exact hcB⟩⟩
  have hαK : α₀ ∈ K := hnear.1
  have hβK : β₀ ∈ K := hnear.2.1
  have hβm : (hsCls U f β₀).card = m + 1 := hnear.2.2.2.2.1
  have hrest : ∀ c ∈ K, c ≠ α₀ → c ≠ β₀ → (hsCls U f c).card = m :=
    hnear.2.2.2.2.2
  have hαA : α₀ ∈ hsReachSet H U K f α₀ :=
    (hsMem_reach H U K f α₀ α₀).mpr ⟨hαK, Relation.ReflTransGen.refl⟩
  have hβB : β₀ ∈ K \ hsReachSet H U K f α₀ :=
    Finset.mem_sdiff.mpr ⟨hβK, hβ₀⟩
  have hmapsB : hsMaps
      ((U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y)
      (K \ hsReachSet H U K f α₀) f := by
    intro u hu
    exact (Finset.mem_filter.mp (Finset.erase_subset y _ hu)).2
  have hproperB : hsProper H
      ((U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y) f := by
    intro u hu v hv hadj
    exact hproper u (hBsub hu) v (hBsub hv) hadj
  by_cases hfy : f y = β₀
  · refine ⟨f, hmapsB, hproperB, ?_⟩
    intro c hcB
    rw [hclsB c hcB]
    by_cases hcb : c = β₀
    · subst hcb
      have hymem : y ∈ hsCls U f c := by
        rw [hsMem_cls]
        exact ⟨hyU, hfy⟩
      rw [Finset.card_erase_of_mem hymem]
      omega
    · have hynot : y ∉ hsCls U f c := by
        rw [hsMem_cls]
        exact fun ⟨_, hfc⟩ => hcb (hfy.symm.trans hfc).symm
      rw [Finset.erase_eq_of_notMem hynot]
      have hcK : c ∈ K := (Finset.mem_sdiff.mp hcB).1
      have hca : c ≠ α₀ := by
        intro hca
        rw [hca] at hcB
        exact (Finset.mem_sdiff.mp hcB).2 hαA
      exact hrest c hcK hca hcb
  · have hKlt : (K \ hsReachSet H U K f α₀).card < K.card :=
      (hsStruct_bfacts H U K f m α₀ β₀ hmaps hnear hβ₀).2
    have hdegB : hsDegLt H
        ((U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y)
        (K \ hsReachSet H U K f α₀) := by
      intro z hz
      have hsub : hsNbr H
          ((U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y) z ⊆
          hsNbr H (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀) z := by
        intro v hv
        rw [hsMem_nbr] at hv ⊢
        exact ⟨Finset.erase_subset y _ hv.1, hv.2⟩
      have hle := Finset.card_le_card hsub
      have hlt := (hsStruct_degB H U K f m α₀ β₀ hmaps hdeg hnear hβ₀ z
        (Finset.erase_subset y _ hz)).2
      omega
    have hnearB : hsNearly
        ((U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y)
        (K \ hsReachSet H U K f α₀) f m (f y) β₀ := by
      refine ⟨hfyB, hβB, hfy, ?_, ?_, ?_⟩
      · rw [hclsB (f y) hfyB]
        have hymem : y ∈ hsCls U f (f y) := by
          rw [hsMem_cls]
          exact ⟨hyU, rfl⟩
        rw [Finset.card_erase_of_mem hymem]
        have hfyα : f y ≠ α₀ := by
          intro hcon
          rw [hcon] at hfyB
          exact (Finset.mem_sdiff.mp hfyB).2 hαA
        have hcl := hrest (f y) ((Finset.mem_sdiff.mp hfyB).1) hfyα hfy
        have hpos : 0 < (hsCls U f (f y)).card :=
          Finset.card_pos.mpr ⟨y, hymem⟩
        omega
      · rw [hclsB β₀ hβB]
        have hynot : y ∉ hsCls U f β₀ := by
          rw [hsMem_cls]
          exact fun ⟨_, hfc⟩ => hfy hfc
        rw [Finset.erase_eq_of_notMem hynot]
        exact hβm
      · intro c hcB hcfy hcβ
        rw [hclsB c hcB]
        have hynot : y ∉ hsCls U f c := by
          rw [hsMem_cls]
          exact fun ⟨_, hfc⟩ => hcfy hfc.symm
        rw [Finset.erase_eq_of_notMem hynot]
        have hcK : c ∈ K := (Finset.mem_sdiff.mp hcB).1
        have hca : c ≠ α₀ := by
          intro hca
          rw [hca] at hcB
          exact (Finset.mem_sdiff.mp hcB).2 hαA
        exact hrest c hcK hca hcβ
    exact hIH (K \ hsReachSet H U K f α₀)
      ((U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y)
      f m (f y) β₀ hKlt hmapsB hproperB hdegB hnearB

/-- Case 1 (a solo partner with an escapable color) gives an equitable coloring. -/
private theorem hsCase1 {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (m : ℕ) (α₀ β₀ : C)
    (hmaps : hsMaps U K f) (hproper : hsProper H U f) (hdeg : hsDegLt H U K)
    (hnear : hsNearly U K f m α₀ β₀)
    (hβ₀ : β₀ ∉ hsReachSet H U K f α₀)
    (hIH : ∀ (K' : Finset C) (U' : Finset V) (f' : V → C) (m' : ℕ) (α' β' : C),
      K'.card < K.card → hsMaps U' K' f' → hsProper H U' f' → hsDegLt H U' K' →
      hsNearly U' K' f' m' α' β' → ∃ g, hsMaps U' K' g ∧ hsProper H U' g ∧
        hsEquitable U' K' g m')
    (w y : V) (α : C)
    (hwU : w ∈ U) (hyB : y ∈ U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀)
    (hωT : f w ∈ hsTerminal H U K f α₀)
    (hsolo : H.Adj y w ∧ ∀ v ∈ hsCls U f (f w), H.Adj y v → v = w)
    (hαA : α ∈ hsReachSet H U K f α₀) (hαω : α ≠ f w)
    (hwit : ∀ u ∈ U, f u = α → ¬ H.Adj w u) :
    ∃ g, hsMaps U K g ∧ hsProper H U g ∧ hsEquitable U K g m := by
  have hαK : α ∈ K := ((hsMem_reach H U K f α₀ α).mp hαA).1
  have hωA : f w ∈ hsReachSet H U K f α₀ :=
    ((hsMem_term H U K f α₀ (f w)).mp hωT).1
  have hωK : f w ∈ K := ((hsMem_reach H U K f α₀ (f w)).mp hωA).1
  have hyU : y ∈ U := (Finset.mem_filter.mp hyB).1
  have hfyB : f y ∈ K \ hsReachSet H U K f α₀ := (Finset.mem_filter.mp hyB).2
  have hyw : y ≠ w := by
    intro hcon
    rw [hcon] at hfyB
    exact (Finset.mem_sdiff.mp hfyB).2 hωA
  obtain ⟨hmaps1, hproper1, hagree1, hid1⟩ :=
    hsMove H U K f hmaps hproper w hwU α hαK hwit
  have hno' : ∀ u ∈ U, Function.update f w α u = f w → ¬ H.Adj y u := by
    intro u huU hfu hadj
    have huw : u ≠ w := by
      intro hcon
      rw [hcon, Function.update_self] at hfu
      exact hαω hfu
    rw [hagree1 u huw] at hfu
    have hucls : u ∈ hsCls U f (f w) := (hsMem_cls U f (f w) u).mpr ⟨huU, hfu⟩
    exact huw (hsolo.2 u hucls hadj)
  obtain ⟨hmaps2, hproper2, hagree2, hid2⟩ :=
    hsMove H U K (Function.update f w α) hmaps1 hproper1 y hyU (f w) hωK hno'
  have hfmidy : Function.update f w α y = f y := hagree1 y hyw
  have hid : ∀ d, (hsCls U (Function.update (Function.update f w α) y (f w))
      d).card + (if d = f y then 1 else 0) =
      (hsCls U f d).card + (if d = α then 1 else 0) := by
    intro d
    have e1 := hid2 d
    rw [hfmidy] at e1
    exact e1.trans (hid1 d)
  have hagree : ∀ u, u ≠ w → u ≠ y →
      Function.update (Function.update f w α) y (f w) u = f u := by
    intro u huw huy
    rw [hagree2 u huy, hagree1 u huw]
  set f₁ := Function.update (Function.update f w α) y (f w) with hf₁def
  have hf1y : f₁ y = f w := by
    rw [hf₁def]
    exact Function.update_self _ _ _
  have hf1w : f₁ w = α := by
    rw [hf₁def, Function.update_of_ne (Ne.symm hyw), Function.update_self]
  have hAsubK : hsReachSet H U K f α₀ ⊆ K := by
    intro σ hσ
    exact ((hsMem_reach H U K f α₀ σ).mp hσ).1
  have hpathα : Relation.ReflTransGen
      (hsAvoid (hsEdge H U K f) (f w)) α α₀ :=
    ((hsMem_term H U K f α₀ (f w)).mp hωT).2 α hαA hαω
  have hpathS : Relation.ReflTransGen
      (fun d e => hsEdge H U K f d e ∧
        d ∈ (hsReachSet H U K f α₀).erase (f w) ∧
        e ∈ (hsReachSet H U K f α₀).erase (f w)) α α₀ := by
    apply hsReach_restrict _ _ hpathα
    intro d e hstep htail
    obtain ⟨hedge, hdne, hene⟩ := hstep
    have htailE : Relation.ReflTransGen (hsEdge H U K f) e α₀ :=
      hsReach_restrict _ _ htail (fun x y h _ => h.1)
    have hdA : d ∈ hsReachSet H U K f α₀ := (hsMem_reach H U K f α₀ d).mpr
      ⟨hedge.1, Relation.ReflTransGen.head hedge htailE⟩
    have heA : e ∈ hsReachSet H U K f α₀ := (hsMem_reach H U K f α₀ e).mpr
      ⟨hedge.2.1, htailE⟩
    exact ⟨hedge, Finset.mem_erase.mpr ⟨hdne, hdA⟩,
      Finset.mem_erase.mpr ⟨hene, heA⟩⟩
  have hpathS' := hsReach_noreentry _ hpathS
  have hsurv : ∀ d e,
      (hsEdge H U K f d e ∧ d ∈ (hsReachSet H U K f α₀).erase (f w) ∧
        e ∈ (hsReachSet H U K f α₀).erase (f w)) ∧ e ≠ α →
      hsEdge H U K f₁ d e ∧ d ∈ (hsReachSet H U K f α₀).erase (f w) ∧
        e ∈ (hsReachSet H U K f α₀).erase (f w) := by
    intro d e h
    obtain ⟨⟨hedge, hdS, heS⟩, hene_α⟩ := h
    obtain ⟨hdK, heK, hde_ne, x', hx'U, hfx', hx'wit⟩ := hedge
    have hdne_fw : d ≠ f w := (Finset.mem_erase.mp hdS).1
    have hx'w : x' ≠ w := by
      intro hcon
      rw [hcon] at hfx'
      exact hdne_fw hfx'.symm
    have hx'y : x' ≠ y := by
      intro hcon
      rw [hcon] at hfx'
      have hdA : d ∈ hsReachSet H U K f α₀ :=
        Finset.erase_subset _ _ hdS
      rw [← hfx'] at hdA
      exact (Finset.mem_sdiff.mp hfyB).2 hdA
    have hfx'1 : f₁ x' = d := by
      rw [hagree x' hx'w hx'y]
      exact hfx'
    have hx'wit1 : ∀ z ∈ U, f₁ z = e → ¬ H.Adj x' z := by
      intro z hzU hfz1 hadj
      have hzw : z ≠ w := by
        intro hcon
        rw [hcon, hf1w] at hfz1
        exact hene_α hfz1.symm
      have hzy : z ≠ y := by
        intro hcon
        rw [hcon, hf1y] at hfz1
        exact (Finset.mem_erase.mp heS).1 hfz1.symm
      rw [hagree z hzw hzy] at hfz1
      exact hx'wit z hzU hfz1 hadj
    exact ⟨⟨hdK, heK, hde_ne, x', hx'U, hfx'1, hx'wit1⟩, hdS, heS⟩
  have hpath1 : Relation.ReflTransGen
      (fun d e => hsEdge H U K f₁ d e ∧
        d ∈ (hsReachSet H U K f α₀).erase (f w) ∧
        e ∈ (hsReachSet H U K f α₀).erase (f w)) α α₀ :=
    hsReach_restrict _ _ hpathS' (fun d e h _ => hsurv d e h)
  have hSsub : (hsReachSet H U K f α₀).erase (f w) ⊆ K :=
    (Finset.erase_subset _ _).trans hAsubK
  have hαS : α ∈ (hsReachSet H U K f α₀).erase (f w) :=
    Finset.mem_erase.mpr ⟨hαω, hαA⟩
  obtain ⟨f₂, hmaps3, hproper3, hagree3, hstay3, hid3⟩ :=
    hsShiftPath H U K f₁ hmaps2 hproper2
      ((hsReachSet H U K f α₀).erase (f w)) hSsub α hαS α₀ hpath1
  have hαm : (hsCls U f α₀).card + 1 = m := hnear.2.2.2.1
  have hrest : ∀ c ∈ K, c ≠ α₀ → c ≠ β₀ → (hsCls U f c).card = m :=
    hnear.2.2.2.2.2
  have hsizeA : ∀ d ∈ hsReachSet H U K f α₀, (hsCls U f₂ d).card = m := by
    intro d hdA
    have hdfy : d ≠ f y := by
      intro hcon
      rw [hcon] at hdA
      exact (Finset.mem_sdiff.mp hfyB).2 hdA
    have e0 : (if d = f y then (1 : ℕ) else 0) = 0 := ite_eq_right hdfy
    have e := hsArith_cancel (hid3 d) (hid d)
    rw [e0] at e
    by_cases hda : d = α₀
    · subst hda
      have e2 : (if d = d then (1 : ℕ) else 0) = 1 := ite_eq_left rfl
      omega
    · have e2 : (if d = α₀ then (1 : ℕ) else 0) = 0 := ite_eq_right hda
      have hdβ : d ≠ β₀ := by
        intro hcon
        rw [hcon] at hdA
        exact hβ₀ hdA
      have hdm := hrest d ((hsMem_reach H U K f α₀ d).mp hdA).1 hda hdβ
      omega
  have hf1A : ∀ u ∈ U, f u ∈ hsReachSet H U K f α₀ →
      f₁ u ∈ hsReachSet H U K f α₀ := by
    intro u huU hfuA
    by_cases huw : u = w
    · rw [huw, hf1w]
      exact hαA
    · by_cases huy : u = y
      · rw [huy, hf1y]
        exact hωA
      · rw [hagree u huw huy]
        exact hfuA
  have hf1yA : f₁ y ∈ hsReachSet H U K f α₀ := by
    rw [hf1y]
    exact hωA
  have hf2A : ∀ u ∈ U, f₁ u ∈ hsReachSet H U K f α₀ →
      f₂ u ∈ hsReachSet H U K f α₀ := by
    intro u huU hf1
    by_cases h : f₁ u ∈ (hsReachSet H U K f α₀).erase (f w)
    · exact (Finset.erase_subset _ _) (hstay3 u huU h)
    · rw [hagree3 u huU h]
      exact hf1
  have hf2eq : ∀ u ∈ (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y,
      f₂ u = f u := by
    intro u hu
    have huB : u ∈ U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀ :=
      Finset.erase_subset y _ hu
    have hfuB : f u ∈ K \ hsReachSet H U K f α₀ :=
      (Finset.mem_filter.mp huB).2
    have hfuS : f u ∉ (hsReachSet H U K f α₀).erase (f w) := by
      intro h
      exact (Finset.mem_sdiff.mp hfuB).2 (Finset.erase_subset _ _ h)
    have huw : u ≠ w := by
      intro hcon
      rw [hcon] at hfuB
      exact (Finset.mem_sdiff.mp hfuB).2 hωA
    have huy : u ≠ y := Finset.ne_of_mem_erase hu
    have hf1u : f₁ u = f u := hagree u huw huy
    have huU : u ∈ U := (Finset.mem_filter.mp huB).1
    have hf1S : f₁ u ∉ (hsReachSet H U K f α₀).erase (f w) := by
      rw [hf1u]
      exact hfuS
    rw [hagree3 u huU hf1S, hf1u]
  obtain ⟨g, hmapsG, hproperG, heqG⟩ :=
    hsRecolorB H U K f m α₀ β₀ hmaps hproper hdeg hnear hβ₀ hIH y hyB
  set h := fun u =>
    if u ∈ (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y
    then g u else f₂ u with hdef
  have hhB : ∀ u ∈ (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y,
      h u = g u := by
    intro u hu
    simp only [hdef, hu, ite_true]
  have hhA : ∀ u, u ∉ (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y →
      h u = f₂ u := by
    intro u hu
    simp only [hdef, hu, ite_false]
  have hf2A' : ∀ v ∈ U,
      v ∉ (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y →
      f₂ v ∈ hsReachSet H U K f α₀ := by
    intro v hvU hvB
    by_cases hvy : v = y
    · rw [hvy]
      exact hf2A y hyU hf1yA
    · have hvB' : v ∉ U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀ := by
        intro hmem
        exact hvB (Finset.mem_erase.mpr ⟨hvy, hmem⟩)
      have hfvB : f v ∉ K \ hsReachSet H U K f α₀ := by
        intro hmem
        exact hvB' (Finset.mem_filter.mpr ⟨hvU, hmem⟩)
      have hfuA : f v ∈ hsReachSet H U K f α₀ := by
        by_contra hcon
        exact hfvB (Finset.mem_sdiff.mpr ⟨hmaps v hvU, hcon⟩)
      exact hf2A v hvU (hf1A v hvU hfuA)
  have hmapsH : hsMaps U K h := by
    intro u huU
    by_cases huB : u ∈
        (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y
    · rw [hhB u huB]
      exact (Finset.mem_sdiff.mp (hmapsG u huB)).1
    · rw [hhA u huB]
      exact hmaps3 u huU
  have hproperH : hsProper H U h := by
    intro u huU v hvU hadj
    by_cases huB : u ∈
        (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y
    · by_cases hvB : v ∈
        (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y
      · rw [hhB u huB, hhB v hvB]
        exact hproperG u huB v hvB hadj
      · rw [hhB u huB, hhA v hvB]
        intro hcon
        have hgB : g u ∈ K \ hsReachSet H U K f α₀ := hmapsG u huB
        rw [hcon] at hgB
        exact (Finset.mem_sdiff.mp hgB).2 (hf2A' v hvU hvB)
    · by_cases hvB : v ∈
        (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y
      · rw [hhA u huB, hhB v hvB]
        intro hcon
        have hgB : g v ∈ K \ hsReachSet H U K f α₀ := hmapsG v hvB
        rw [← hcon] at hgB
        exact (Finset.mem_sdiff.mp hgB).2 (hf2A' u huU huB)
      · rw [hhA u huB, hhA v hvB]
        exact hproper3 u huU v hvU hadj
  have hclsA : ∀ d ∈ hsReachSet H U K f α₀, hsCls U h d = hsCls U f₂ d := by
    intro d hdA
    ext u
    simp only [hsMem_cls]
    constructor
    · rintro ⟨huU, hud⟩
      by_cases huB : u ∈
          (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y
      · rw [hhB u huB] at hud
        exfalso
        rw [← hud] at hdA
        exact (Finset.mem_sdiff.mp (hmapsG u huB)).2 hdA
      · rw [hhA u huB] at hud
        exact ⟨huU, hud⟩
    · rintro ⟨huU, hud⟩
      by_cases huB : u ∈
          (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y
      · exfalso
        have hfu := hf2eq u huB
        rw [hfu] at hud
        have hfuB2 : f u ∈ K \ hsReachSet H U K f α₀ :=
          (Finset.mem_filter.mp (Finset.erase_subset y _ huB)).2
        rw [hud] at hfuB2
        exact (Finset.mem_sdiff.mp hfuB2).2 hdA
      · rw [hhA u huB]
        exact ⟨huU, hud⟩
  have hclsB2 : ∀ d ∈ K \ hsReachSet H U K f α₀,
      hsCls U h d =
        hsCls ((U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y)
          g d := by
    intro d hdB
    ext u
    simp only [hsMem_cls]
    constructor
    · rintro ⟨huU, hud⟩
      by_cases huB : u ∈
          (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y
      · rw [hhB u huB] at hud
        exact ⟨huB, hud⟩
      · rw [hhA u huB] at hud
        exfalso
        have hAt : f₂ u ∈ hsReachSet H U K f α₀ := hf2A' u huU huB
        rw [hud] at hAt
        exact (Finset.mem_sdiff.mp hdB).2 hAt
    · rintro ⟨huB, hud⟩
      have huB' : u ∈ U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀ :=
        Finset.erase_subset y _ huB
      have huU : u ∈ U := (Finset.mem_filter.mp huB').1
      rw [hhB u huB]
      exact ⟨huU, hud⟩
  refine ⟨h, hmapsH, hproperH, ?_⟩
  intro d hdK
  by_cases hdA : d ∈ hsReachSet H U K f α₀
  · rw [hclsA d hdA]
    exact hsizeA d hdA
  · have hdB : d ∈ K \ hsReachSet H U K f α₀ :=
      Finset.mem_sdiff.mpr ⟨hdK, hdA⟩
    rw [hclsB2 d hdB]
    exact heqG d hdB

/-- Neighbour counts split over a disjoint vertex bipartition. -/
private theorem hsSplit_nbr {V : Type*} [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U A B : Finset V) (v : V) (hunion : A ∪ B = U) (hdisj : Disjoint A B) :
    (hsNbr H U v).card = (hsNbr H A v).card + (hsNbr H B v).card := by
  have h1 : hsNbr H U v = hsNbr H A v ∪ hsNbr H B v := by
    conv_lhs => rw [← hunion]
    simp only [hsNbr, Finset.filter_union]
  have h2 : Disjoint (hsNbr H A v) (hsNbr H B v) := by
    rw [Finset.disjoint_left]
    intro w hwA hwB
    rw [hsMem_nbr] at hwA hwB
    exact (Finset.disjoint_left.mp hdisj hwA.1) hwB.1
  rw [h1, Finset.card_union_of_disjoint h2]

/-- Case 2 (a doubly-solo vertex) grows the reach set. -/
private theorem hsCase2 {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (m : ℕ) (α₀ β₀ : C)
    (hmaps : hsMaps U K f) (hproper : hsProper H U f) (hdeg : hsDegLt H U K)
    (hnear : hsNearly U K f m α₀ β₀)
    (hβ₀ : β₀ ∉ hsReachSet H U K f α₀)
    (hIH : ∀ (K' : Finset C) (U' : Finset V) (f' : V → C) (m' : ℕ) (α' β' : C),
      K'.card < K.card → hsMaps U' K' f' → hsProper H U' f' → hsDegLt H U' K' →
      hsNearly U' K' f' m' α' β' → ∃ g, hsMaps U' K' g ∧ hsProper H U' g ∧
        hsEquitable U' K' g m')
    (w y z : V) (hwU : w ∈ U)
    (hyB : y ∈ U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀)
    (hzB : z ∈ U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀)
    (hωT : f w ∈ hsTerminal H U K f α₀)
    (hsoloy : H.Adj y w ∧ ∀ v ∈ hsCls U f (f w), H.Adj y v → v = w)
    (hsoloz : H.Adj z w ∧ ∀ v ∈ hsCls U f (f w), H.Adj z v → v = w)
    (hyz : y ≠ z) (hnadj : ¬ H.Adj y z)
    (hfail : ∀ σ ∈ hsReachSet H U K f α₀, σ ≠ f w →
      ∃ u ∈ U, f u = σ ∧ H.Adj w u) :
    ∃ f', hsMaps U K f' ∧ hsProper H U f' ∧ ∃ γ ∈ K \ hsReachSet H U K f α₀,
      hsNearly U K f' m α₀ γ ∧
        (hsReachSet H U K f α₀).card < (hsReachSet H U K f' α₀).card := by
  have hyU : y ∈ U := (Finset.mem_filter.mp hyB).1
  have hzU : z ∈ U := (Finset.mem_filter.mp hzB).1
  have hfyB : f y ∈ K \ hsReachSet H U K f α₀ := (Finset.mem_filter.mp hyB).2
  have hfzB : f z ∈ K \ hsReachSet H U K f α₀ := (Finset.mem_filter.mp hzB).2
  have hωA : f w ∈ hsReachSet H U K f α₀ :=
    ((hsMem_term H U K f α₀ (f w)).mp hωT).1
  obtain ⟨g, hmapsG, hproperG, heqG⟩ :=
    hsRecolorB H U K f m α₀ β₀ hmaps hproper hdeg hnear hβ₀ hIH y hyB
  obtain ⟨_, _, hABdisj, hABunion, hKcard⟩ :=
    hsStruct_setup H U K f m α₀ β₀ hmaps hnear hβ₀
  have hge1 : ∀ c ∈ (hsReachSet H U K f α₀).erase (f w),
      1 ≤ (hsNbr H (hsCls U f c) w).card := by
    intro c hc
    have hcA : c ∈ hsReachSet H U K f α₀ := Finset.erase_subset _ _ hc
    have hcne : c ≠ f w := (Finset.mem_erase.mp hc).1
    obtain ⟨u, huU, hfu, hadj⟩ := hfail c hcA hcne
    have hmem : u ∈ hsNbr H (hsCls U f c) w := (hsMem_nbr H _ _ _).mpr
      ⟨(hsMem_cls U f c u).mpr ⟨huU, hfu⟩, hadj⟩
    exact Finset.card_pos.mpr ⟨u, hmem⟩
  have hsum1 : ((hsReachSet H U K f α₀).erase (f w)).card ≤
      ∑ c ∈ hsReachSet H U K f α₀, (hsNbr H (hsCls U f c) w).card := by
    calc ((hsReachSet H U K f α₀).erase (f w)).card
        = ∑ _c ∈ (hsReachSet H U K f α₀).erase (f w), 1 := by simp
      _ ≤ ∑ c ∈ (hsReachSet H U K f α₀).erase (f w),
          (hsNbr H (hsCls U f c) w).card := Finset.sum_le_sum hge1
      _ ≤ ∑ c ∈ hsReachSet H U K f α₀, (hsNbr H (hsCls U f c) w).card := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        intro c _ _
        exact Nat.zero_le _
  have hAw : ((hsReachSet H U K f α₀).erase (f w)).card ≤
      (hsNbr H (U.filter fun u => f u ∈ hsReachSet H U K f α₀) w).card := by
    rw [show hsNbr H (U.filter fun u => f u ∈ hsReachSet H U K f α₀) w =
      (U.filter fun u => f u ∈ hsReachSet H U K f α₀).filter
        (fun u => H.Adj w u) from rfl,
      hsCount_nbr H U (hsReachSet H U K f α₀) f w]
    exact hsum1
  have hsplitw := hsSplit_nbr H U
    (U.filter fun u => f u ∈ hsReachSet H U K f α₀)
    (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀) w hABunion hABdisj
  have hdegw := hdeg w hwU
  have hae : ((hsReachSet H U K f α₀).erase (f w)).card =
      (hsReachSet H U K f α₀).card - 1 :=
    Finset.card_erase_of_mem hωA
  have hBwle : (hsNbr H (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀)
      w).card ≤ (K \ hsReachSet H U K f α₀).card := by
    omega
  have hwy : H.Adj w y := H.adj_symm hsoloy.1
  have hyw : y ≠ w := by
    intro h
    rw [h] at hwy
    exact H.irrefl hwy
  have hyBnb : y ∈ hsNbr H
      (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀) w :=
    (hsMem_nbr H _ _ _).mpr ⟨hyB, hwy⟩
  have hBstar : hsNbr H
      ((U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y) w =
      (hsNbr H (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀) w).erase
        y := by
    simp only [hsNbr, Finset.filter_erase]
  have hBwlt : (hsNbr H
      ((U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y) w).card <
      (K \ hsReachSet H U K f α₀).card := by
    rw [hBstar]
    exact lt_of_lt_of_le (Finset.card_erase_lt_of_mem hyBnb) hBwle
  have himg : ((hsNbr H
      ((U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y) w).image
      g).card < (K \ hsReachSet H U K f α₀).card :=
    lt_of_le_of_lt Finset.card_image_le hBwlt
  obtain ⟨γ, hγB, hγmiss⟩ := Finset.exists_mem_notMem_of_card_lt_card himg
  have hγK : γ ∈ K := (Finset.mem_sdiff.mp hγB).1
  have hγmiss' : ∀ v ∈ hsNbr H
      ((U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y) w,
      g v ≠ γ := by
    intro v hv hcon
    exact hγmiss (Finset.mem_image.mpr ⟨v, hv, hcon⟩)
  set f' := fun u => if u = w then γ else if u = y then f w else
    if u ∈ (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y
    then g u else f u with hf'def
  have e_w : f' w = γ := by simp [hf'def]
  have e_y : f' y = f w := by simp [hf'def, hyw]
  have e_B : ∀ x ∈ (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y,
      x ≠ w → x ≠ y → f' x = g x := by
    intro x hxB hxw hxy
    simp only [hf'def]
    rw [ite_eq_right hxw, ite_eq_right hxy, ite_eq_left hxB]
  have e_A : ∀ x, x ≠ w → x ≠ y →
      x ∉ (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y →
      f' x = f x := by
    intro x hxw hxy hxB
    simp only [hf'def]
    rw [ite_eq_right hxw, ite_eq_right hxy, ite_eq_right hxB]
  have hmaps' : hsMaps U K f' := by
    intro u huU
    by_cases huw : u = w
    · rw [huw, e_w]
      exact hγK
    · by_cases huy : u = y
      · rw [huy, e_y]
        exact ((hsMem_reach H U K f α₀ (f w)).mp hωA).1
      · by_cases huB : u ∈
          (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y
        · rw [e_B u huB huw huy]
          exact (Finset.mem_sdiff.mp (hmapsG u huB)).1
        · rw [e_A u huw huy huB]
          exact hmaps u huU
  have hwB : w ∉ (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y := by
    intro h
    exact (Finset.mem_sdiff.mp ((Finset.mem_filter.mp
      (Finset.erase_subset y _ h)).2)).2 hωA
  have hyB' : y ∉ (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y :=
    Finset.notMem_erase y _
  have outA : ∀ x ∈ U, x ≠ y →
      x ∉ (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y →
      f x ∈ hsReachSet H U K f α₀ := by
    intro x hxU hxy hxB
    by_contra hcon
    have hxBn : x ∉ U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀ := by
      intro hmem
      exact hxB (Finset.mem_erase.mpr ⟨hxy, hmem⟩)
    exact hxBn (Finset.mem_filter.mpr
      ⟨hxU, Finset.mem_sdiff.mpr ⟨hmaps x hxU, hcon⟩⟩)
  have hproper' : hsProper H U f' := by
    intro u huU v hvU hadj hcon
    have vw : v = w ∨ v ≠ w := eq_or_ne v w
    have vy : v = y ∨ v ≠ y := eq_or_ne v y
    have vB : v ∈ (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y ∨
        v ∉ (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y := by
      by_cases h : v ∈ ((U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase
          y) <;>
        [exact Or.inl h; exact Or.inr h]
    by_cases huw : u = w
    · by_cases huy : u = y
      · exfalso; rw [huy] at huw; exact hyw huw
      · by_cases huB : u ∈
            (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y
        · exfalso; rw [huw] at huB; exact hwB huB
        · rw [huw, e_w] at hcon
          rcases vw with rfl | hvw
          · rw [e_w] at hcon
            rw [huw] at hadj
            exact absurd hadj H.irrefl
          · rcases vy with rfl | hvy
            · rw [e_y] at hcon
              rw [hcon] at hγB
              exact (Finset.mem_sdiff.mp hγB).2 hωA
            · rcases vB with hvB | hvB
              · rw [e_B v hvB hvw hvy] at hcon
                have hmem : v ∈ hsNbr H
                    ((U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase
                      y) w := (hsMem_nbr H _ _ _).mpr
                  ⟨hvB, by rw [huw] at hadj; exact hadj⟩
                exact hγmiss' v hmem hcon.symm
              · rw [e_A v hvw hvy hvB] at hcon
                rw [hcon] at hγB
                exact (Finset.mem_sdiff.mp hγB).2 (outA v hvU hvy hvB)
    · by_cases huy : u = y
      · by_cases huB : u ∈
            (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y
        · exfalso; rw [huy] at huB; exact hyB' huB
        · rw [huy, e_y] at hcon
          rcases vw with rfl | hvw
          · rw [e_w] at hcon
            rw [hcon] at hωA
            exact (Finset.mem_sdiff.mp hγB).2 hωA
          · rcases vy with rfl | hvy
            · rw [huy] at hadj
              exact absurd hadj H.irrefl
            · rcases vB with hvB | hvB
              · rw [e_B v hvB hvw hvy] at hcon
                rw [hcon] at hωA
                exact (Finset.mem_sdiff.mp (hmapsG v hvB)).2 hωA
              · rw [e_A v hvw hvy hvB] at hcon
                have hvcls : v ∈ hsCls U f (f w) :=
                  (hsMem_cls U f (f w) v).mpr ⟨hvU, hcon.symm⟩
                rw [huy] at hadj
                exact hvw (hsoloy.2 v hvcls hadj)
      · by_cases huB : u ∈
            (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y
        · rcases vw with rfl | hvw
          · rw [e_B u huB huw huy, e_w] at hcon
            have hmem : u ∈ hsNbr H
                ((U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y)
                v := (hsMem_nbr H _ _ _).mpr ⟨huB, H.adj_symm hadj⟩
            exact hγmiss' u hmem hcon
          · rcases vy with rfl | hvy
            · rw [e_B u huB huw huy, e_y] at hcon
              rw [← hcon] at hωA
              exact (Finset.mem_sdiff.mp (hmapsG u huB)).2 hωA
            · rcases vB with hvB | hvB
              · rw [e_B u huB huw huy, e_B v hvB hvw hvy] at hcon
                exact hproperG u huB v hvB hadj hcon
              · rw [e_B u huB huw huy, e_A v hvw hvy hvB] at hcon
                have hfvA := outA v hvU hvy hvB
                have hgBu := hmapsG u huB
                rw [hcon] at hgBu
                exact (Finset.mem_sdiff.mp hgBu).2 hfvA
        · have hfuA2 := outA u huU huy huB
          rw [e_A u huw huy huB] at hcon
          rcases vw with rfl | hvw
          · rw [e_w] at hcon
            rw [← hcon] at hγB
            exact (Finset.mem_sdiff.mp hγB).2 hfuA2
          · rcases vy with rfl | hvy
            · rw [e_y] at hcon
              have hucls : u ∈ hsCls U f (f w) :=
                (hsMem_cls U f (f w) u).mpr ⟨huU, hcon⟩
              exact huw (hsoloy.2 u hucls (H.adj_symm hadj))
            · rcases vB with hvB | hvB
              · rw [e_B v hvB hvw hvy] at hcon
                have hgBv := hmapsG v hvB
                rw [← hcon] at hgBv
                exact (Finset.mem_sdiff.mp hgBv).2 hfuA2
              · rw [e_A v hvw hvy hvB] at hcon
                exact hproper u huU v hvU hadj hcon
  have hωK : f w ∈ K := ((hsMem_reach H U K f α₀ (f w)).mp hωA).1
  have hαA : α₀ ∈ hsReachSet H U K f α₀ :=
    (hsMem_reach H U K f α₀ α₀).mpr ⟨hnear.1, Relation.ReflTransGen.refl⟩
  have hαne_γ : α₀ ≠ γ := by
    intro h
    subst h
    exact (Finset.mem_sdiff.mp hγB).2 hαA
  have hfwβ : f w ≠ β₀ := by
    intro h
    rw [h] at hωA
    exact hβ₀ hωA
  have hA' : ∀ u ∈ U, u ≠ w → u ≠ y →
      u ∉ (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y →
      f u ∈ hsReachSet H U K f α₀ := by
    intro u huU huw huy huB
    by_contra hcon
    have huBfull : u ∈ U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀ :=
      Finset.mem_filter.mpr
        ⟨huU, Finset.mem_sdiff.mpr ⟨hmaps u huU, hcon⟩⟩
    exact huB (Finset.mem_erase.mpr ⟨huy, huBfull⟩)
  have hclsA' : ∀ c ∈ hsReachSet H U K f α₀, c ≠ f w →
      hsCls U f' c = hsCls U f c := by
    intro c hcA hfw
    ext u
    simp only [hsMem_cls]
    constructor
    · rintro ⟨huU, hfu'⟩
      by_cases huw : u = w
      · exfalso
        have hcon : γ = c := by rw [← e_w, ← huw]; exact hfu'
        have hγA : γ ∈ hsReachSet H U K f α₀ := by
          rw [hcon]
          exact hcA
        exact (Finset.mem_sdiff.mp hγB).2 hγA
      · by_cases huy : u = y
        · exfalso
          have hcon : f w = c := by rw [← e_y, ← huy]; exact hfu'
          exact hfw hcon.symm
        · by_cases huB : u ∈
              (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y
          · exfalso
            have hcon : g u = c := by
              rw [← e_B u huB huw huy]
              exact hfu'
            have hgA : g u ∈ hsReachSet H U K f α₀ := by
              rw [hcon]
              exact hcA
            exact (Finset.mem_sdiff.mp (hmapsG u huB)).2 hgA
          · rw [e_A u huw huy huB] at hfu'
            exact ⟨huU, hfu'⟩
    · rintro ⟨huU, hfu⟩
      by_cases huw : u = w
      · exfalso
        rw [huw] at hfu
        exact hfw hfu.symm
      · by_cases huy : u = y
        · exfalso
          rw [huy] at hfu
          rw [hfu] at hfyB
          exact (Finset.mem_sdiff.mp hfyB).2 hcA
        · by_cases huB : u ∈
              (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y
          · exfalso
            have hfuB : f u ∈ K \ hsReachSet H U K f α₀ :=
              (Finset.mem_filter.mp (Finset.erase_subset y _ huB)).2
            rw [hfu] at hfuB
            exact (Finset.mem_sdiff.mp hfuB).2 hcA
          · rw [e_A u huw huy huB]
            exact ⟨huU, hfu⟩
  have hpres : ∀ σ τ, σ ∈ hsReachSet H U K f α₀ → τ ∈ hsReachSet H U K f α₀ →
      σ ≠ f w → τ ≠ f w → hsEdge H U K f σ τ → hsEdge H U K f' σ τ := by
    intro σ τ hσA hτA hσω hτω hst
    obtain ⟨hσK, hτK, hστ, x, hxU, hfx, hsolo⟩ := hst
    have hxB : x ∉ U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀ := by
      intro h
      have h2 := (Finset.mem_sdiff.mp (Finset.mem_filter.mp h).2).2
      rw [hfx] at h2
      exact h2 hσA
    have hxw : x ≠ w := by
      intro h
      apply hσω
      rw [← hfx, h]
    have hxy : x ≠ y := by
      intro h
      rw [h] at hfx
      have hfyA : f y ∈ hsReachSet H U K f α₀ := by rw [hfx]; exact hσA
      exact (Finset.mem_sdiff.mp hfyB).2 hfyA
    have hxB' : x ∉
        (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y := by
      intro h
      exact hxB (Finset.erase_subset y _ h)
    refine ⟨hσK, hτK, hστ, x, hxU, ?_, ?_⟩
    · rw [e_A x hxw hxy hxB']
      exact hfx
    · intro v hvU hfv
      have hfvτ : f v = τ := by
        have hmem : v ∈ hsCls U f τ := by
          rw [← hclsA' τ hτA hτω]
          exact (hsMem_cls U f' τ v).mpr ⟨hvU, hfv⟩
        exact ((hsMem_cls U f τ v).mp hmem).2
      exact hsolo v hvU hfvτ
  have hlift : ∀ x y, hsAvoid (hsEdge H U K f) (f w) x y →
      Relation.ReflTransGen (hsAvoid (hsEdge H U K f) (f w)) y α₀ →
      hsEdge H U K f' x y := by
    intro x y hxy hyt
    obtain ⟨he, hxw, hyw⟩ := hxy
    have hye : Relation.ReflTransGen (hsEdge H U K f) y α₀ :=
      hsReach_restrict _ _ hyt (fun a b h _ => h.1)
    have hyA : y ∈ hsReachSet H U K f α₀ :=
      (hsMem_reach H U K f α₀ y).mpr ⟨he.2.1, hye⟩
    have hxe : Relation.ReflTransGen (hsEdge H U K f) x α₀ :=
      Relation.ReflTransGen.head he hye
    have hxA : x ∈ hsReachSet H U K f α₀ :=
      (hsMem_reach H U K f α₀ x).mpr ⟨he.1, hxe⟩
    exact hpres x y hxA hyA hxw hyw he
  have hmemA : ∀ ν, Relation.ReflTransGen
      (hsAvoid (hsEdge H U K f) (f w)) ν α₀ →
      ν ∈ hsReachSet H U K f' α₀ := by
    intro ν hν
    have hνK : ν ∈ K := by
      rcases hν.cases_head with h | ⟨c, hstep, -⟩
      · rw [h]
        exact hnear.1
      · exact hstep.1.1
    refine (hsMem_reach H U K f' α₀ ν).mpr ⟨hνK, ?_⟩
    exact hsReach_restrict _ _ hν (fun x y hxy hyt => hlift x y hxy hyt)
  have hterm : ∀ γ ∈ hsReachSet H U K f α₀, γ ≠ f w →
      Relation.ReflTransGen (hsAvoid (hsEdge H U K f) (f w)) γ α₀ :=
    ((hsMem_term H U K f α₀ (f w)).mp hωT).2
  have hfw' : f w ∈ hsReachSet H U K f' α₀ := by
    have hpath : Relation.ReflTransGen (hsEdge H U K f) (f w) α₀ :=
      ((hsMem_reach H U K f α₀ (f w)).mp hωA).2
    by_cases hfwα : f w = α₀
    · rw [hfwα]
      exact (hsMem_reach H U K f' α₀ α₀).mpr
        ⟨hnear.1, Relation.ReflTransGen.refl⟩
    · obtain ⟨σ₁, hstep, htail⟩ := hsReach_avoid_cor _ hfwα hpath
      obtain ⟨hfwK, hσK, hfwσ, x₀, hxU, hfx, hsolo⟩ := hstep
      have hσw : σ₁ ≠ f w := Ne.symm hfwσ
      have hσpath : Relation.ReflTransGen (hsEdge H U K f) σ₁ α₀ :=
        hsReach_restrict _ _ htail (fun a b h _ => h.1)
      have hσA : σ₁ ∈ hsReachSet H U K f α₀ :=
        (hsMem_reach H U K f α₀ σ₁).mpr ⟨hσK, hσpath⟩
      have hxw0 : x₀ ≠ w := by
        intro h
        rw [h] at hsolo
        obtain ⟨u, huU, hfu, hadj⟩ := hfail σ₁ hσA hσw
        exact hsolo u huU hfu hadj
      have hxy0 : x₀ ≠ y := by
        intro h
        rw [h] at hfx
        have hfyA : f y ∈ hsReachSet H U K f α₀ := by rw [hfx]; exact hωA
        exact (Finset.mem_sdiff.mp hfyB).2 hfyA
      have hxB0 : x₀ ∉
          (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y := by
        intro h
        have hB := (Finset.mem_filter.mp (Finset.erase_subset y _ h)).2
        rw [hfx] at hB
        exact (Finset.mem_sdiff.mp hB).2 hωA
      have hedge' : hsEdge H U K f' (f w) σ₁ := by
        refine ⟨hωK, hσK, hfwσ, x₀, hxU, ?_, ?_⟩
        · rw [e_A x₀ hxw0 hxy0 hxB0]
          exact hfx
        · intro v hvU hfv
          have hfvσ : f v = σ₁ := by
            have hmem : v ∈ hsCls U f σ₁ := by
              rw [← hclsA' σ₁ hσA hσw]
              exact (hsMem_cls U f' σ₁ v).mpr ⟨hvU, hfv⟩
            exact ((hsMem_cls U f σ₁ v).mp hmem).2
          exact hsolo v hvU hfvσ
      have hσ₁' : σ₁ ∈ hsReachSet H U K f' α₀ :=
        hmemA σ₁ (hterm σ₁ hσA hσw)
      exact (hsMem_reach H U K f' α₀ (f w)).mpr
        ⟨hωK, Relation.ReflTransGen.head hedge'
          ((hsMem_reach H U K f' α₀ σ₁).mp hσ₁').2⟩
  have hsub : hsReachSet H U K f α₀ ⊆ hsReachSet H U K f' α₀ := by
    intro δ hδA
    by_cases hδw : δ = f w
    · rw [hδw]
      exact hfw'
    · exact hmemA δ (hterm δ hδA hδw)
  have hcardA : ∀ c ∈ hsReachSet H U K f α₀, c ≠ f w →
      (hsCls U f' c).card = (hsCls U f c).card := by
    intro c hcA hfw
    rw [hclsA' c hcA hfw]
  have hsetW : hsCls U f' (f w) =
      insert y ((hsCls U f (f w)).erase w) := by
    ext u
    simp only [hsMem_cls, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨huU, hfu'⟩
      by_cases huw : u = w
      · exfalso
        have hcon : γ = f w := by conv_lhs => rw [← e_w, ← huw]; exact hfu'
        have hγA : γ ∈ hsReachSet H U K f α₀ := by
          rw [hcon]
          exact hωA
        exact (Finset.mem_sdiff.mp hγB).2 hγA
      · by_cases huy : u = y
        · exact Or.inl huy
        · by_cases huB : u ∈
              (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y
          · exfalso
            have hcon : g u = f w := by
              rw [← e_B u huB huw huy]
              exact hfu'
            have hgA : g u ∈ hsReachSet H U K f α₀ := by
              rw [hcon]
              exact hωA
            exact (Finset.mem_sdiff.mp (hmapsG u huB)).2 hgA
          · rw [e_A u huw huy huB] at hfu'
            exact Or.inr ⟨huw, huU, hfu'⟩
    · rintro (rfl | ⟨hne, huU, hfu⟩)
      · exact ⟨hyU, e_y⟩
      · by_cases huy : u = y
        · exfalso
          rw [huy] at hfu
          rw [hfu] at hfyB
          exact (Finset.mem_sdiff.mp hfyB).2 hωA
        · by_cases huB : u ∈
              (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y
          · exfalso
            have hfuB : f u ∈ K \ hsReachSet H U K f α₀ :=
              (Finset.mem_filter.mp (Finset.erase_subset y _ huB)).2
            rw [hfu] at hfuB
            exact (Finset.mem_sdiff.mp hfuB).2 hωA
          · rw [e_A u hne huy huB]
            exact ⟨huU, hfu⟩
  have hwclsW : w ∈ hsCls U f (f w) :=
    (hsMem_cls U f (f w) w).mpr ⟨hwU, rfl⟩
  have hynW : y ∉ (hsCls U f (f w)).erase w := by
    intro h
    obtain ⟨-, hycls⟩ := Finset.mem_erase.mp h
    have h2 : f y = f w := ((hsMem_cls U f (f w) y).mp hycls).2
    rw [h2] at hfyB
    exact (Finset.mem_sdiff.mp hfyB).2 hωA
  have hcardW : (hsCls U f' (f w)).card = (hsCls U f (f w)).card := by
    rw [hsetW, Finset.card_insert_of_notMem hynW,
      Finset.card_erase_of_mem hwclsW]
    have hpos := Finset.card_pos.mpr ⟨w, hwclsW⟩
    omega
  have hsetG : hsCls U f' γ =
      insert w (hsCls
        ((U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y) g γ) := by
    ext u
    simp only [hsMem_cls, Finset.mem_insert]
    constructor
    · rintro ⟨huU, hfu'⟩
      by_cases huw : u = w
      · exact Or.inl huw
      · by_cases huy : u = y
        · exfalso
          have hcon : f w = γ := by rw [← e_y, ← huy]; exact hfu'
          have hfwB : f w ∈ K \ hsReachSet H U K f α₀ := by
            rw [hcon]
            exact hγB
          exact (Finset.mem_sdiff.mp hfwB).2 hωA
        · by_cases huB : u ∈
              (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y
          · rw [e_B u huB huw huy] at hfu'
            exact Or.inr ⟨huB, hfu'⟩
          · exfalso
            have huA := hA' u huU huw huy huB
            rw [e_A u huw huy huB] at hfu'
            have hγA : γ ∈ hsReachSet H U K f α₀ := by
              rw [← hfu']
              exact huA
            exact (Finset.mem_sdiff.mp hγB).2 hγA
    · rintro (rfl | ⟨huB, hgu⟩)
      · exact ⟨hwU, e_w⟩
      · have huU : u ∈ U :=
          (Finset.mem_filter.mp (Finset.erase_subset y _ huB)).1
        have huw : u ≠ w := by
          intro h
          rw [h] at huB
          exact hwB huB
        have huy : u ≠ y := (Finset.mem_erase.mp huB).1
        rw [e_B u huB huw huy]
        exact ⟨huU, hgu⟩
  have hcardG : (hsCls U f' γ).card = m + 1 := by
    have hmem : w ∉ hsCls
        ((U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y) g γ := by
      intro h
      exact hwB ((hsMem_cls _ _ _ _).mp h).1
    rw [hsetG, Finset.card_insert_of_notMem hmem, heqG γ hγB]
  have hsetB : ∀ c ∈ K \ hsReachSet H U K f α₀, c ≠ γ →
      hsCls U f' c = hsCls
        ((U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y) g c := by
    intro c hcB hcγ
    ext u
    simp only [hsMem_cls]
    constructor
    · rintro ⟨huU, hfu'⟩
      by_cases huw : u = w
      · exfalso
        have hcon : γ = c := by rw [← e_w, ← huw]; exact hfu'
        exact hcγ hcon.symm
      · by_cases huy : u = y
        · exfalso
          have hcon : f w = c := by rw [← e_y, ← huy]; exact hfu'
          have hfwB : f w ∈ K \ hsReachSet H U K f α₀ := by
            rw [hcon]
            exact hcB
          exact (Finset.mem_sdiff.mp hfwB).2 hωA
        · by_cases huB : u ∈
              (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y
          · rw [e_B u huB huw huy] at hfu'
            exact ⟨huB, hfu'⟩
          · exfalso
            have huA := hA' u huU huw huy huB
            rw [e_A u huw huy huB] at hfu'
            have hcA : c ∈ hsReachSet H U K f α₀ := by
              rw [← hfu']
              exact huA
            exact (Finset.mem_sdiff.mp hcB).2 hcA
    · rintro ⟨huB, hgu⟩
      have huU : u ∈ U :=
        (Finset.mem_filter.mp (Finset.erase_subset y _ huB)).1
      have huw : u ≠ w := by
        intro h
        rw [h] at huB
        exact hwB huB
      have huy : u ≠ y := (Finset.mem_erase.mp huB).1
      rw [e_B u huB huw huy]
      exact ⟨huU, hgu⟩
  have hcardB : ∀ c ∈ K \ hsReachSet H U K f α₀, c ≠ γ →
      (hsCls U f' c).card = m := by
    intro c hcB hcγ
    rw [hsetB c hcB hcγ]
    exact heqG c hcB
  have hnear' : hsNearly U K f' m α₀ γ := by
    refine ⟨hnear.1, hγK, hαne_γ, ?_, hcardG, ?_⟩
    · by_cases hfw : f w = α₀
      · rw [← hfw, hcardW, hfw]
        exact hnear.2.2.2.1
      · rw [hcardA α₀ hαA (Ne.symm hfw)]
        exact hnear.2.2.2.1
    · intro c hcK hcα hcγ
      by_cases hcA : c ∈ hsReachSet H U K f α₀
      · by_cases hfw : c = f w
        · subst hfw
          rw [hcardW]
          exact hnear.2.2.2.2.2 _ hωK hcα hfwβ
        · rw [hcardA c hcA hfw]
          exact hnear.2.2.2.2.2 c hcK hcα (by
            intro h
            rw [h] at hcA
            exact hβ₀ hcA)
      · exact hcardB c (Finset.mem_sdiff.mpr ⟨hcK, hcA⟩) hcγ
  have hzB' : z ∈
      (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀).erase y :=
    Finset.mem_erase.mpr ⟨Ne.symm hyz, hzB⟩
  have hzw : z ≠ w := by
    intro h
    rw [h] at hsoloz
    exact H.irrefl hsoloz.1
  have hgzB : g z ∈ K \ hsReachSet H U K f α₀ := hmapsG z hzB'
  have hgzA : g z ∉ hsReachSet H U K f α₀ :=
    (Finset.mem_sdiff.mp hgzB).2
  have hedge : hsEdge H U K f' (g z) (f w) := by
    refine ⟨(Finset.mem_sdiff.mp hgzB).1, hωK, ?_, z, hzU, ?_, ?_⟩
    · intro h
      rw [h] at hgzA
      exact hgzA hωA
    · rw [e_B z hzB' hzw (Ne.symm hyz)]
    · intro v hvU hfv
      have hmem : v ∈ hsCls U f' (f w) := (hsMem_cls U f' (f w) v).mpr ⟨hvU, hfv⟩
      rw [hsetW] at hmem
      rcases Finset.mem_insert.mp hmem with rfl | hmem
      · intro hadj
        exact hnadj (H.adj_symm hadj)
      · obtain ⟨hvw, hvcls⟩ := Finset.mem_erase.mp hmem
        intro hadj
        exact hvw (hsoloz.2 v hvcls hadj)
  have hgz' : g z ∈ hsReachSet H U K f' α₀ :=
    (hsMem_reach H U K f' α₀ (g z)).mpr
      ⟨(Finset.mem_sdiff.mp hgzB).1,
        Relation.ReflTransGen.head hedge ((hsMem_reach H U K f' α₀ (f w)).mp hfw').2⟩
  have hgrow : (hsReachSet H U K f α₀).card < (hsReachSet H U K f' α₀).card := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨hsub, ?_⟩
    intro hcon
    rw [hcon] at hgzA
    exact hgzA hgz'
  exact ⟨f', hmaps', hproper', γ, hγB, hnear', hgrow⟩

/-- Auxiliary: colors of `𝒜` reaching `α₀` while avoiding `ν`. -/
private noncomputable def hsDset {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ ν : C) : Finset C :=
  @Finset.filter C
    (fun c => c ≠ ν ∧ Relation.ReflTransGen (hsAvoid (hsEdge H U K f) ν) c α₀)
    (fun _ => Classical.propDecidable _) (hsReachSet H U K f α₀)

private theorem hsMem_dset {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ ν c : C) :
    c ∈ hsDset H U K f α₀ ν ↔
      c ∈ hsReachSet H U K f α₀ ∧ c ≠ ν ∧
        Relation.ReflTransGen (hsAvoid (hsEdge H U K f) ν) c α₀ := by
  simp only [hsDset, Finset.mem_filter]

private theorem hsDset_sub {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ ν : C) :
    hsDset H U K f α₀ ν ⊆ hsReachSet H U K f α₀ := by
  intro c hc
  exact ((hsMem_dset H U K f α₀ ν c).mp hc).1

private theorem hsDset_self {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ ν : C) :
    ν ∉ hsDset H U K f α₀ ν := by
  intro h
  exact ((hsMem_dset H U K f α₀ ν ν).mp h).2.1 rfl

/-- Lift: if `ρ ∉ D_ν`, every `ν`-avoiding path to `α₀` is also `ρ`-avoiding. -/
private theorem hsDset_lift {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ ν ρ : C)
    (hρ : ρ ∉ hsDset H U K f α₀ ν) (c : C)
    (hc : c ∈ hsDset H U K f α₀ ν) :
    Relation.ReflTransGen (hsAvoid (hsEdge H U K f) ρ) c α₀ := by
  obtain ⟨_, _, hpath⟩ := (hsMem_dset H U K f α₀ ν c).mp hc
  refine hsReach_restrict _ _ hpath (fun x y hxy hyt => ?_)
  obtain ⟨he, hxne, hyne⟩ := hxy
  have hye : Relation.ReflTransGen (hsEdge H U K f) y α₀ :=
    hsReach_restrict _ _ hyt (fun a b h _ => h.1)
  have hyA : y ∈ hsReachSet H U K f α₀ :=
    (hsMem_reach H U K f α₀ y).mpr ⟨he.2.1, hye⟩
  have hyD : y ∈ hsDset H U K f α₀ ν :=
    (hsMem_dset H U K f α₀ ν y).mpr ⟨hyA, hyne, hyt⟩
  have hyρ : y ≠ ρ := fun h => hρ (h ▸ hyD)
  have hxe : Relation.ReflTransGen (hsEdge H U K f) x α₀ :=
    Relation.ReflTransGen.head he hye
  have hxA : x ∈ hsReachSet H U K f α₀ :=
    (hsMem_reach H U K f α₀ x).mpr ⟨he.1, hxe⟩
  have hxpath : Relation.ReflTransGen (hsAvoid (hsEdge H U K f) ν) x α₀ :=
    Relation.ReflTransGen.head ⟨he, hxne, hyne⟩ hyt
  have hxD : x ∈ hsDset H U K f α₀ ν :=
    (hsMem_dset H U K f α₀ ν x).mpr ⟨hxA, hxne, hxpath⟩
  have hxρ : x ≠ ρ := fun h => hρ (h ▸ hxD)
  exact ⟨he, hxρ, hyρ⟩

/-- Monotonicity: `D_ν ⊆ D_ρ` when `ρ ∉ D_ν`. -/
private theorem hsDset_mono {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ ν ρ : C)
    (hρ : ρ ∉ hsDset H U K f α₀ ν) :
    hsDset H U K f α₀ ν ⊆ hsDset H U K f α₀ ρ := by
  intro c hc
  obtain ⟨hcA, _, _⟩ := (hsMem_dset H U K f α₀ ν c).mp hc
  have hcρ : c ≠ ρ := fun h => hρ (h ▸ hc)
  exact (hsMem_dset H U K f α₀ ρ c).mpr
    ⟨hcA, hcρ, hsDset_lift H U K f α₀ ν ρ hρ c hc⟩

/-- Step: `ν ∈ D_ρ` when `ρ ∉ D_ν` and `ν ≠ ρ`. -/
private theorem hsDset_nu_mem {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ ν ρ : C)
    (hνA : ν ∈ hsReachSet H U K f α₀) (hνρ : ν ≠ ρ)
    (hρ : ρ ∉ hsDset H U K f α₀ ν) :
    ν ∈ hsDset H U K f α₀ ρ := by
  refine (hsMem_dset H U K f α₀ ρ ν).mpr ⟨hνA, hνρ, ?_⟩
  have hEpath : Relation.ReflTransGen (hsEdge H U K f) ν α₀ :=
    ((hsMem_reach H U K f α₀ ν).mp hνA).2
  by_cases hνα : ν = α₀
  · subst hνα
    exact Relation.ReflTransGen.refl
  · obtain ⟨c₀, hstep, htail⟩ := hsReach_avoid_cor _ hνα hEpath
    have hstep_copy := hstep
    obtain ⟨_, hc₀K, hνc₀, _⟩ := hstep_copy
    have hc₀ν : c₀ ≠ ν := Ne.symm hνc₀
    have hc₀E : Relation.ReflTransGen (hsEdge H U K f) c₀ α₀ :=
      hsReach_restrict _ _ htail (fun a b h _ => h.1)
    have hc₀A : c₀ ∈ hsReachSet H U K f α₀ :=
      (hsMem_reach H U K f α₀ c₀).mpr ⟨hc₀K, hc₀E⟩
    have hc₀D : c₀ ∈ hsDset H U K f α₀ ν :=
      (hsMem_dset H U K f α₀ ν c₀).mpr ⟨hc₀A, hc₀ν, htail⟩
    have hc₀Dρ : c₀ ∈ hsDset H U K f α₀ ρ :=
      hsDset_mono H U K f α₀ ν ρ hρ hc₀D
    have hc₀ρ : c₀ ≠ ρ := ((hsMem_dset H U K f α₀ ρ c₀).mp hc₀Dρ).2.1
    exact Relation.ReflTransGen.head ⟨hstep, hνρ, hc₀ρ⟩
      (hsDset_lift H U K f α₀ ν ρ hρ c₀ hc₀D)

/-- Step: `D_ν ⊂ D_ρ` strictly when `ρ ∈ R_ν`. -/
private theorem hsDset_strict {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ ν ρ : C)
    (hνA : ν ∈ hsReachSet H U K f α₀)
    (hρR : ρ ∈ (hsReachSet H U K f α₀).erase ν \ hsDset H U K f α₀ ν) :
    (hsDset H U K f α₀ ν).card < (hsDset H U K f α₀ ρ).card := by
  have hρE : ρ ∈ (hsReachSet H U K f α₀).erase ν :=
    (Finset.mem_sdiff.mp hρR).1
  have hρD : ρ ∉ hsDset H U K f α₀ ν := (Finset.mem_sdiff.mp hρR).2
  have hνρ : ν ≠ ρ := Ne.symm (Finset.mem_erase.mp hρE).1
  have hsub := hsDset_mono H U K f α₀ ν ρ hρD
  have hνDρ := hsDset_nu_mem H U K f α₀ ν ρ hνA hνρ hρD
  have hνDν := hsDset_self H U K f α₀ ν
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  exact ⟨hsub, fun h => hνDν (h.symm ▸ hνDρ)⟩

/-- Step: `R_ν` is nonempty when `ν` is not terminal. -/
private theorem hsR_nonempty {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ ν : C)
    (hνA : ν ∈ hsReachSet H U K f α₀)
    (hνT : ν ∉ hsTerminal H U K f α₀) :
    ((hsReachSet H U K f α₀).erase ν \ hsDset H U K f α₀ ν).Nonempty := by
  have hnt : ¬ ∀ γ ∈ hsReachSet H U K f α₀, γ ≠ ν →
      Relation.ReflTransGen (hsAvoid (hsEdge H U K f) ν) γ α₀ := by
    intro hall
    exact hνT ((hsMem_term H U K f α₀ ν).mpr ⟨hνA, hall⟩)
  push Not at hnt
  obtain ⟨γ, hγA, hγne, hγnp⟩ := hnt
  refine ⟨γ, Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hγne, hγA⟩, ?_⟩⟩
  intro hD
  exact hγnp ((hsMem_dset H U K f α₀ ν γ).mp hD).2.2

/-- Step: under maximality of `D_ν`, every member of `R_ν` is terminal. -/
private theorem hsR_terminal {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ ν : C)
    (hνA : ν ∈ hsReachSet H U K f α₀)
    (hmax : ∀ μ ∈ hsReachSet H U K f α₀ \ hsTerminal H U K f α₀,
      (hsDset H U K f α₀ μ).card ≤ (hsDset H U K f α₀ ν).card)
    (ρ : C)
    (hρR : ρ ∈ (hsReachSet H U K f α₀).erase ν \ hsDset H U K f α₀ ν) :
    ρ ∈ hsTerminal H U K f α₀ := by
  by_contra hρT
  have hρA : ρ ∈ hsReachSet H U K f α₀ :=
    Finset.erase_subset ν _ (Finset.mem_sdiff.mp hρR).1
  have hle := hmax ρ (Finset.mem_sdiff.mpr ⟨hρA, hρT⟩)
  have hlt := hsDset_strict H U K f α₀ ν ρ hνA hρR
  omega

/-- Step: every vertex of the class of `τ ∈ R_ν` has a neighbour in
each class of `D_ν`. -/
private theorem hsForced_nbr {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ ν τ d : C)
    (hτR : τ ∈ (hsReachSet H U K f α₀).erase ν \ hsDset H U K f α₀ ν)
    (hdD : d ∈ hsDset H U K f α₀ ν)
    (w : V) (hw : w ∈ hsCls U f τ) :
    ∃ v ∈ hsCls U f d, H.Adj w v := by
  obtain ⟨hτE, hτD⟩ := Finset.mem_sdiff.mp hτR
  obtain ⟨hτν, hτA⟩ := Finset.mem_erase.mp hτE
  obtain ⟨hdA, hdν, hdpath⟩ := (hsMem_dset H U K f α₀ ν d).mp hdD
  have hτK : τ ∈ K := ((hsMem_reach H U K f α₀ τ).mp hτA).1
  have hdK : d ∈ K := ((hsMem_reach H U K f α₀ d).mp hdA).1
  have hτd : τ ≠ d := fun h => hτD (h ▸ hdD)
  obtain ⟨hwU, hfw⟩ := (hsMem_cls U f τ w).mp hw
  by_contra hcon
  push Not at hcon
  have hnowit : ∀ y ∈ U, f y = d → ¬ H.Adj w y := by
    intro y hyU hfy hadj
    exact hcon y ((hsMem_cls U f d y).mpr ⟨hyU, hfy⟩) hadj
  have hedge : hsEdge H U K f τ d := ⟨hτK, hdK, hτd, w, hwU, hfw, hnowit⟩
  have hτpath : Relation.ReflTransGen (hsAvoid (hsEdge H U K f) ν) τ α₀ :=
    Relation.ReflTransGen.head ⟨hedge, hτν, hdν⟩ hdpath
  exact hτD ((hsMem_dset H U K f α₀ ν τ).mpr ⟨hτA, hτν, hτpath⟩)

/-- A terminal color with many forced neighbours. -/
private theorem hsFinish_a {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (m : ℕ) (α₀ β₀ : C)
    (hmaps : hsMaps U K f) (hdeg : hsDegLt H U K)
    (hnear : hsNearly U K f m α₀ β₀)
    (hβ₀ : β₀ ∉ hsReachSet H U K f α₀) :
    ∃ τ D, τ ∈ hsTerminal H U K f α₀ ∧ D ⊆ hsReachSet H U K f α₀ ∧ τ ∉ D ∧
      (hsReachSet H U K f α₀).card ≤ (hsTerminal H U K f α₀).card + D.card + 1 ∧
      ∀ w ∈ hsCls U f τ, ∀ d ∈ D, ∃ v ∈ hsCls U f d, H.Adj w v := by
  have hαA : α₀ ∈ hsReachSet H U K f α₀ :=
    (hsMem_reach H U K f α₀ α₀).mpr ⟨hnear.1, Relation.ReflTransGen.refl⟩
  have hαT : α₀ ∉ hsTerminal H U K f α₀ :=
    hsStruct_nterm H U K f m α₀ β₀ hmaps hdeg hnear hβ₀
  have hNTne : (hsReachSet H U K f α₀ \ hsTerminal H U K f α₀).Nonempty :=
    ⟨α₀, Finset.mem_sdiff.mpr ⟨hαA, hαT⟩⟩
  obtain ⟨ν, hνNT, hmax⟩ := Finset.exists_max_image _
    (fun ν => (hsDset H U K f α₀ ν).card) hNTne
  have hνA : ν ∈ hsReachSet H U K f α₀ := (Finset.mem_sdiff.mp hνNT).1
  have hνT : ν ∉ hsTerminal H U K f α₀ := (Finset.mem_sdiff.mp hνNT).2
  obtain ⟨τ, hτR⟩ := hsR_nonempty H U K f α₀ ν hνA hνT
  have hmax' : ∀ μ ∈ hsReachSet H U K f α₀ \ hsTerminal H U K f α₀,
      (hsDset H U K f α₀ μ).card ≤ (hsDset H U K f α₀ ν).card :=
    fun μ hμ => hmax μ hμ
  have hτT : τ ∈ hsTerminal H U K f α₀ :=
    hsR_terminal H U K f α₀ ν hνA hmax' τ hτR
  refine ⟨τ, hsDset H U K f α₀ ν, hτT, hsDset_sub H U K f α₀ ν,
    (Finset.mem_sdiff.mp hτR).2, ?_, ?_⟩
  · have hsub : hsTerminal H U K f α₀ ⊆ hsReachSet H U K f α₀ := by
      intro σ hσ
      exact ((hsMem_term H U K f α₀ σ).mp hσ).1
    have hcard := Finset.card_sdiff_add_card_eq_card hsub
    have hNTsub : hsReachSet H U K f α₀ \ hsTerminal H U K f α₀ ⊆
        hsDset H U K f α₀ ν ∪ {ν} := by
      intro μ hμ
      obtain ⟨hμA, hμT⟩ := Finset.mem_sdiff.mp hμ
      by_cases hμν : μ = ν
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr hμν))
      · by_cases hμD : μ ∈ hsDset H U K f α₀ ν
        · exact Finset.mem_union.mpr (Or.inl hμD)
        · exfalso
          exact hμT (hsR_terminal H U K f α₀ ν hνA hmax' μ
            (Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hμν, hμA⟩, hμD⟩))
    have hle1 := Finset.card_le_card hNTsub
    have hle2 := Finset.card_union_le (hsDset H U K f α₀ ν) {ν}
    rw [Finset.card_singleton] at hle2
    omega
  · intro w hw d hd
    exact hsForced_nbr H U K f α₀ ν τ d hτR hd w hw

/-- A solo vertex has at most `b` neighbours in `B`. -/
private theorem hsFinish_b1 {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (m : ℕ) (α₀ β₀ : C)
    (hmaps : hsMaps U K f) (hdeg : hsDegLt H U K)
    (hnear : hsNearly U K f m α₀ β₀)
    (hβ₀ : β₀ ∉ hsReachSet H U K f α₀)
    (w : V) (hwU : w ∈ U) (σ : C)
    (hσT : σ ∈ hsTerminal H U K f α₀)
    (hfail : ∀ ς ∈ hsReachSet H U K f α₀, ς ≠ σ →
      ∃ u ∈ U, f u = ς ∧ H.Adj w u) :
    (hsReachSet H U K f α₀).card ≤
      (hsNbr H (U.filter fun u => f u ∈ hsReachSet H U K f α₀) w).card + 1 ∧
    (hsNbr H (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀) w).card ≤
      (K \ hsReachSet H U K f α₀).card := by
  have hσA : σ ∈ hsReachSet H U K f α₀ :=
    ((hsMem_term H U K f α₀ σ).mp hσT).1
  obtain ⟨_, _, hABdisj, hABunion, hKcard⟩ :=
    hsStruct_setup H U K f m α₀ β₀ hmaps hnear hβ₀
  have hge : ∀ c ∈ (hsReachSet H U K f α₀).erase σ,
      1 ≤ (hsNbr H (hsCls U f c) w).card := by
    intro c hc
    have hcA : c ∈ hsReachSet H U K f α₀ := Finset.erase_subset _ _ hc
    have hcne : c ≠ σ := (Finset.mem_erase.mp hc).1
    obtain ⟨u, huU, hfu, hadj⟩ := hfail c hcA hcne
    exact Finset.card_pos.mpr ⟨u, (hsMem_nbr H _ _ _).mpr
      ⟨(hsMem_cls U f c u).mpr ⟨huU, hfu⟩, hadj⟩⟩
  have hsum : ((hsReachSet H U K f α₀).erase σ).card ≤
      (hsNbr H (U.filter fun u => f u ∈ hsReachSet H U K f α₀) w).card := by
    calc ((hsReachSet H U K f α₀).erase σ).card
        = ∑ _c ∈ (hsReachSet H U K f α₀).erase σ, 1 := by simp
      _ ≤ ∑ c ∈ (hsReachSet H U K f α₀).erase σ,
          (hsNbr H (hsCls U f c) w).card := Finset.sum_le_sum hge
      _ ≤ ∑ c ∈ hsReachSet H U K f α₀,
          (hsNbr H (hsCls U f c) w).card := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        intro c _ _
        exact Nat.zero_le _
      _ = (hsNbr H (U.filter fun u => f u ∈ hsReachSet H U K f α₀) w).card := by
        rw [show hsNbr H (U.filter fun u => f u ∈ hsReachSet H U K f α₀) w =
          (U.filter fun u => f u ∈ hsReachSet H U K f α₀).filter
            (fun u => H.Adj w u) from rfl,
          hsCount_nbr H U (hsReachSet H U K f α₀) f w]
  have herase : ((hsReachSet H U K f α₀).erase σ).card + 1 =
      (hsReachSet H U K f α₀).card := by
    have h1 := Finset.card_erase_of_mem hσA
    have hpos : 1 ≤ (hsReachSet H U K f α₀).card :=
      Finset.card_pos.mpr ⟨σ, hσA⟩
    omega
  have hsplit := hsSplit_nbr H U
    (U.filter fun u => f u ∈ hsReachSet H U K f α₀)
    (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀) w hABunion hABdisj
  have hdegw := hdeg w hwU
  omega

/-- A vertex of the class of `τ` has at most `b + a'` neighbours in `B`. -/
private theorem hsFinish_b2 {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (m : ℕ) (α₀ β₀ : C)
    (hmaps : hsMaps U K f) (hdeg : hsDegLt H U K)
    (hnear : hsNearly U K f m α₀ β₀)
    (hβ₀ : β₀ ∉ hsReachSet H U K f α₀)
    (τ : C) (D : Finset C) (hDsub : D ⊆ hsReachSet H U K f α₀)
    (hDbound : (hsReachSet H U K f α₀).card ≤
      (hsTerminal H U K f α₀).card + D.card + 1)
    (hforced : ∀ w ∈ hsCls U f τ, ∀ d ∈ D, ∃ v ∈ hsCls U f d, H.Adj w v)
    (w : V) (hw : w ∈ hsCls U f τ) :
    D.card ≤ (hsNbr H (U.filter fun u => f u ∈ hsReachSet H U K f α₀) w).card ∧
    (hsNbr H (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀) w).card ≤
      (K \ hsReachSet H U K f α₀).card + (hsTerminal H U K f α₀).card := by
  have hwU : w ∈ U := ((hsMem_cls U f τ w).mp hw).1
  obtain ⟨_, _, hABdisj, hABunion, hKcard⟩ :=
    hsStruct_setup H U K f m α₀ β₀ hmaps hnear hβ₀
  have hge : ∀ d ∈ D, 1 ≤ (hsNbr H (hsCls U f d) w).card := by
    intro d hd
    obtain ⟨v, hvcls, hadj⟩ := hforced w hw d hd
    exact Finset.card_pos.mpr ⟨v, (hsMem_nbr H _ _ _).mpr ⟨hvcls, hadj⟩⟩
  have hsum : D.card ≤
      (hsNbr H (U.filter fun u => f u ∈ hsReachSet H U K f α₀) w).card := by
    calc D.card = ∑ _c ∈ D, 1 := by simp
      _ ≤ ∑ d ∈ D, (hsNbr H (hsCls U f d) w).card := Finset.sum_le_sum hge
      _ ≤ ∑ c ∈ hsReachSet H U K f α₀,
          (hsNbr H (hsCls U f c) w).card := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hDsub
        intro c _ _
        exact Nat.zero_le _
      _ = (hsNbr H (U.filter fun u => f u ∈ hsReachSet H U K f α₀) w).card := by
        rw [show hsNbr H (U.filter fun u => f u ∈ hsReachSet H U K f α₀) w =
          (U.filter fun u => f u ∈ hsReachSet H U K f α₀).filter
            (fun u => H.Adj w u) from rfl,
          hsCount_nbr H U (hsReachSet H U K f α₀) f w]
  have hsplit := hsSplit_nbr H U
    (U.filter fun u => f u ∈ hsReachSet H U K f α₀)
    (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀) w hABunion hABdisj
  have hdegw := hdeg w hwU
  omega

/-- Arithmetic: the double count forces `b < a'`. -/
private theorem hsArith_blt {N M s r b a' : ℕ}
    (hdouble : N + 2 * M ≤ b * s + (b + a') * r)
    (hNle : N ≤ b * s)
    (hB : N + M = b * (s + r) + 1) :
    b * r + 2 ≤ a' * r ∧ b < a' := by
  have e1 : b * (s + r) = b * s + b * r := mul_add b s r
  have e2 : (b + a') * r = b * r + a' * r := add_mul b a' r
  have h1 : b * r + 2 ≤ a' * r := by omega
  refine ⟨h1, ?_⟩
  by_contra hcon
  push Not at hcon
  have h2 := mul_le_mul_of_nonneg_right hcon (Nat.zero_le r)
  omega

/-- Auxiliary: the solo vertices in the class of `τ`. -/
private noncomputable def hsSol {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ τ : C) : Finset V :=
  @Finset.filter V
    (fun w => ∃ z ∈ U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀,
      H.Adj z w ∧ ∀ v ∈ hsCls U f (f w), H.Adj z v → v = w)
    (fun _ => Classical.propDecidable _) (hsCls U f τ)

/-- Auxiliary: vertices of `B` adjacent to some solo vertex. -/
private noncomputable def hsN {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ : C)
    (Sol : Finset V) : Finset V :=
  @Finset.filter V (fun z => ∃ w ∈ Sol, H.Adj z w)
    (fun _ => Classical.propDecidable _)
    (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀)

private theorem hsMem_sol {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ τ : C) (v : V) :
    v ∈ hsSol H U K f α₀ τ ↔ v ∈ hsCls U f τ ∧
      ∃ z ∈ U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀,
        H.Adj z v ∧ ∀ u ∈ hsCls U f (f v), H.Adj z u → u = v := by
  simp only [hsSol, Finset.mem_filter]

private theorem hsMem_hsN {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ : C)
    (Sol : Finset V) (z : V) :
    z ∈ hsN H U K f α₀ Sol ↔
      z ∈ U.filter (fun u => f u ∈ K \ hsReachSet H U K f α₀) ∧
        ∃ w ∈ Sol, H.Adj z w := by
  simp only [hsN, Finset.mem_filter]

/-- Step: `N.card ≤ b * Sol.card`. -/
private theorem hsN_le {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (m : ℕ) (α₀ β₀ : C)
    (hmaps : hsMaps U K f) (hdeg : hsDegLt H U K)
    (hnear : hsNearly U K f m α₀ β₀)
    (hβ₀ : β₀ ∉ hsReachSet H U K f α₀)
    (τ : C) (hτT : τ ∈ hsTerminal H U K f α₀)
    (hfailw : ∀ w ∈ hsSol H U K f α₀ τ, ∀ ς ∈ hsReachSet H U K f α₀, ς ≠ τ →
      ∃ u ∈ U, f u = ς ∧ H.Adj w u) :
    (hsN H U K f α₀ (hsSol H U K f α₀ τ)).card ≤
      (K \ hsReachSet H U K f α₀).card * (hsSol H U K f α₀ τ).card := by
  set Sol := hsSol H U K f α₀ τ with hSoldef
  set B := U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀ with hBdef
  set N := hsN H U K f α₀ Sol with hNdef
  have hsub : N ⊆ Sol.biUnion (fun w => hsNbr H B w) := by
    intro z hz
    have hz' : z ∈ hsN H U K f α₀ Sol := hNdef ▸ hz
    obtain ⟨hzB, w, hwSol, hadj⟩ :=
      (hsMem_hsN H U K f α₀ Sol z).mp hz'
    exact Finset.mem_biUnion.mpr ⟨w, hwSol,
      (hsMem_nbr H _ _ _).mpr ⟨hzB, H.adj_symm hadj⟩⟩
  have hterm : ∀ w ∈ Sol, (hsNbr H B w).card ≤
      (K \ hsReachSet H U K f α₀).card := by
    intro w hwSol
    have hwSolU : w ∈ hsSol H U K f α₀ τ := hSoldef ▸ hwSol
    obtain ⟨hwT, _, _, _, _⟩ := (hsMem_sol H U K f α₀ τ w).mp hwSolU
    have hwU : w ∈ U := ((hsMem_cls U f τ w).mp hwT).1
    have hb := hsFinish_b1 H U K f m α₀ β₀ hmaps hdeg hnear hβ₀ w hwU τ hτT
      (fun ς hς hne => hfailw w hwSolU ς hς hne)
    exact hb.2
  calc N.card ≤ (Sol.biUnion fun w => hsNbr H B w).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ w ∈ Sol, (hsNbr H B w).card := Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ Sol, (K \ hsReachSet H U K f α₀).card :=
        Finset.sum_le_sum hterm
    _ = (K \ hsReachSet H U K f α₀).card * Sol.card := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- Step: a vertex of `B` outside `N` has two neighbours in `T`. -/
private theorem hsTwo_nbr {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ τ : C)
    (hmaps : hsMaps U K f) (hτT : τ ∈ hsTerminal H U K f α₀)
    (z : V) (hzB : z ∈ U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀)
    (hzN : z ∉ hsN H U K f α₀ (hsSol H U K f α₀ τ)) :
    2 ≤ (hsNbr H (hsCls U f τ) z).card := by
  have hτA : τ ∈ hsReachSet H U K f α₀ :=
    ((hsMem_term H U K f α₀ τ).mp hτT).1
  obtain ⟨w₀, hw₀cls, hadj₀⟩ := hsStruct_nbrA H U K f α₀ hmaps z hzB τ hτA
  have hmem₀ : w₀ ∈ hsNbr H (hsCls U f τ) z :=
    (hsMem_nbr H _ _ _).mpr ⟨hw₀cls, hadj₀⟩
  by_cases h2 : 2 ≤ (hsNbr H (hsCls U f τ) z).card
  · exact h2
  · exfalso
    have hle : (hsNbr H (hsCls U f τ) z).card ≤ 1 := by omega
    have hpos : 0 < (hsNbr H (hsCls U f τ) z).card :=
      Finset.card_pos.mpr ⟨w₀, hmem₀⟩
    have h1 : (hsNbr H (hsCls U f τ) z).card = 1 := by omega
    obtain ⟨a, hsingle⟩ := Finset.card_eq_one.mp h1
    have hw₀a : w₀ = a := Finset.mem_singleton.mp (hsingle ▸ hmem₀)
    have hfw₀ : f w₀ = τ := ((hsMem_cls U f τ w₀).mp hw₀cls).2
    have hsolo : H.Adj z w₀ ∧
        ∀ v ∈ hsCls U f (f w₀), H.Adj z v → v = w₀ := by
      refine ⟨hadj₀, ?_⟩
      intro v hvcls hadj
      have hfv : f v = τ := by
        rw [← hfw₀]
        exact ((hsMem_cls U f (f w₀) v).mp hvcls).2
      have hvT : v ∈ hsCls U f τ := (hsMem_cls U f τ v).mpr
        ⟨((hsMem_cls U f (f w₀) v).mp hvcls).1, hfv⟩
      have hmem : v ∈ hsNbr H (hsCls U f τ) z :=
        (hsMem_nbr H _ _ _).mpr ⟨hvT, hadj⟩
      have hva : v = a := Finset.mem_singleton.mp (hsingle ▸ hmem)
      rw [hva]
      exact hw₀a.symm
    have hw₀Sol : w₀ ∈ hsSol H U K f α₀ τ :=
      (hsMem_sol H U K f α₀ τ w₀).mpr ⟨hw₀cls, z, hzB, hsolo.1, hsolo.2⟩
    have hzN' : z ∈ hsN H U K f α₀ (hsSol H U K f α₀ τ) :=
      (hsMem_hsN H U K f α₀ _ z).mpr ⟨hzB, w₀, hw₀Sol, hadj₀⟩
    exact hzN hzN'

/-- Step: double counting edges between `B` and `T`. -/
private theorem hsDouble_eq {V : Type*} [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (B T : Finset V) :
    (∑ z ∈ B, (hsNbr H T z).card) = ∑ w ∈ T, (hsNbr H B w).card := by
  have hAbove : ∀ z, T.bipartiteAbove (fun z w => H.Adj z w) z =
      hsNbr H T z := by
    intro z
    ext w
    simp only [Finset.mem_bipartiteAbove, hsMem_nbr]
  have hBelow : ∀ w, B.bipartiteBelow (fun z w => H.Adj z w) w =
      hsNbr H B w := by
    intro w
    ext z
    simp only [Finset.mem_bipartiteBelow, hsMem_nbr]
    constructor
    · rintro ⟨hzB, hadj⟩
      exact ⟨hzB, H.adj_symm hadj⟩
    · rintro ⟨hzB, hadj⟩
      exact ⟨hzB, H.adj_symm hadj⟩
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := B) (t := T) (r := fun z w => H.Adj z w)
  simp only [hAbove, hBelow] at hdc
  exact hdc

/-- Step: `N + 2 * M ≤ b * s + (b + a') * r`. -/
private theorem hsDouble_le {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (m : ℕ) (α₀ β₀ : C)
    (hmaps : hsMaps U K f) (hdeg : hsDegLt H U K)
    (hnear : hsNearly U K f m α₀ β₀)
    (hβ₀ : β₀ ∉ hsReachSet H U K f α₀)
    (τ : C) (hτT : τ ∈ hsTerminal H U K f α₀)
    (D : Finset C) (hDsub : D ⊆ hsReachSet H U K f α₀)
    (hDbound : (hsReachSet H U K f α₀).card ≤
      (hsTerminal H U K f α₀).card + D.card + 1)
    (hforced : ∀ w ∈ hsCls U f τ, ∀ d ∈ D, ∃ v ∈ hsCls U f d, H.Adj w v)
    (hfailw : ∀ w ∈ hsSol H U K f α₀ τ, ∀ ς ∈ hsReachSet H U K f α₀, ς ≠ τ →
      ∃ u ∈ U, f u = ς ∧ H.Adj w u) :
    (hsN H U K f α₀ (hsSol H U K f α₀ τ)).card +
        2 * (U.filter (fun u => f u ∈ K \ hsReachSet H U K f α₀) \
          hsN H U K f α₀ (hsSol H U K f α₀ τ)).card ≤
      (K \ hsReachSet H U K f α₀).card * (hsSol H U K f α₀ τ).card +
        ((K \ hsReachSet H U K f α₀).card + (hsTerminal H U K f α₀).card) *
          ((hsCls U f τ) \ hsSol H U K f α₀ τ).card := by
  set Sol := hsSol H U K f α₀ τ with hSoldef
  set B := U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀ with hBdef
  set N := hsN H U K f α₀ Sol with hNdef
  set T := hsCls U f τ with hTdef
  have hτA : τ ∈ hsReachSet H U K f α₀ :=
    ((hsMem_term H U K f α₀ τ).mp hτT).1
  have h1B : ∀ z ∈ B, 1 ≤ (hsNbr H T z).card := by
    intro z hzB
    have hzB' : z ∈ U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀ :=
      hBdef ▸ hzB
    obtain ⟨v, hvcls, hadj⟩ := hsStruct_nbrA H U K f α₀ hmaps z hzB' τ hτA
    have hvT : v ∈ T := hTdef ▸ hvcls
    exact Finset.card_pos.mpr ⟨v, (hsMem_nbr H _ _ _).mpr ⟨hvT, hadj⟩⟩
  have h2B : ∀ z ∈ B \ N, 2 ≤ (hsNbr H T z).card := by
    intro z hz
    obtain ⟨hzB, hzN⟩ := Finset.mem_sdiff.mp hz
    have hzB' : z ∈ U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀ :=
      hBdef ▸ hzB
    rw [hNdef, hSoldef] at hzN
    exact hsTwo_nbr H U K f α₀ τ hmaps hτT z hzB' hzN
  have hbS : ∀ w ∈ Sol, (hsNbr H B w).card ≤
      (K \ hsReachSet H U K f α₀).card := by
    intro w hwSol
    have hwSolU : w ∈ hsSol H U K f α₀ τ := hSoldef ▸ hwSol
    obtain ⟨hwT, _, _, _, _⟩ := (hsMem_sol H U K f α₀ τ w).mp hwSolU
    have hwU : w ∈ U := ((hsMem_cls U f τ w).mp hwT).1
    have hb := hsFinish_b1 H U K f m α₀ β₀ hmaps hdeg hnear hβ₀ w hwU τ hτT
      (fun ς hς hne => hfailw w hwSolU ς hς hne)
    exact hb.2
  have hbT : ∀ w ∈ T \ Sol, (hsNbr H B w).card ≤
      (K \ hsReachSet H U K f α₀).card + (hsTerminal H U K f α₀).card := by
    intro w hw
    have hwT : w ∈ hsCls U f τ := hTdef ▸ (Finset.sdiff_subset hw)
    exact (hsFinish_b2 H U K f m α₀ β₀ hmaps hdeg hnear hβ₀ τ D hDsub
      hDbound hforced w hwT).2
  have hNB : N ⊆ B := by
    intro z hz
    have hz' : z ∈ hsN H U K f α₀ Sol := hNdef ▸ hz
    exact ((hsMem_hsN H U K f α₀ Sol z).mp hz').1
  have hST : Sol ⊆ T := by
    intro w hw
    have hw' : w ∈ hsSol H U K f α₀ τ := hSoldef ▸ hw
    have hwT : w ∈ hsCls U f τ := ((hsMem_sol H U K f α₀ τ w).mp hw').1
    exact hTdef ▸ hwT
  have hdc : (∑ z ∈ B, (hsNbr H T z).card) =
      ∑ w ∈ T, (hsNbr H B w).card := hsDouble_eq H B T
  have hsplitB : ∑ z ∈ B \ N, (hsNbr H T z).card +
      ∑ z ∈ N, (hsNbr H T z).card = ∑ z ∈ B, (hsNbr H T z).card := by
    rw [← Finset.sum_union ((Finset.disjoint_sdiff (s := N) (t := B)).symm),
      Finset.sdiff_union_of_subset hNB]
  have hsplitT : ∑ w ∈ T \ Sol, (hsNbr H B w).card +
      ∑ w ∈ Sol, (hsNbr H B w).card = ∑ w ∈ T, (hsNbr H B w).card := by
    rw [← Finset.sum_union ((Finset.disjoint_sdiff (s := Sol) (t := T)).symm),
      Finset.sdiff_union_of_subset hST]
  have hlowN : N.card ≤ ∑ z ∈ N, (hsNbr H T z).card := by
    calc N.card = ∑ _z ∈ N, 1 := by simp
      _ ≤ ∑ z ∈ N, (hsNbr H T z).card :=
        Finset.sum_le_sum (fun z hz => h1B z (hNB hz))
  have hlowM : 2 * (B \ N).card ≤
      ∑ z ∈ B \ N, (hsNbr H T z).card := by
    calc 2 * (B \ N).card = ∑ _z ∈ B \ N, 2 := by
          rw [Finset.sum_const, smul_eq_mul]
          exact Nat.mul_comm _ _
      _ ≤ ∑ z ∈ B \ N, (hsNbr H T z).card :=
        Finset.sum_le_sum (fun z hz => h2B z hz)
  have hupS : ∑ w ∈ Sol, (hsNbr H B w).card ≤
      (K \ hsReachSet H U K f α₀).card * Sol.card := by
    calc ∑ w ∈ Sol, (hsNbr H B w).card
        ≤ ∑ _w ∈ Sol, (K \ hsReachSet H U K f α₀).card :=
        Finset.sum_le_sum hbS
      _ = (K \ hsReachSet H U K f α₀).card * Sol.card := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hupT : ∑ w ∈ T \ Sol, (hsNbr H B w).card ≤
      ((K \ hsReachSet H U K f α₀).card + (hsTerminal H U K f α₀).card) *
        (T \ Sol).card := by
    calc ∑ w ∈ T \ Sol, (hsNbr H B w).card
        ≤ ∑ _w ∈ T \ Sol, ((K \ hsReachSet H U K f α₀).card +
          (hsTerminal H U K f α₀).card) := Finset.sum_le_sum hbT
      _ = ((K \ hsReachSet H U K f α₀).card +
          (hsTerminal H U K f α₀).card) * (T \ Sol).card := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  omega

/-- `b < a'`. -/
private theorem hsFinish_c {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (m : ℕ) (α₀ β₀ : C)
    (hmaps : hsMaps U K f) (hdeg : hsDegLt H U K)
    (hnear : hsNearly U K f m α₀ β₀)
    (hβ₀ : β₀ ∉ hsReachSet H U K f α₀)
    (τ : C) (hτT : τ ∈ hsTerminal H U K f α₀)
    (D : Finset C) (hDsub : D ⊆ hsReachSet H U K f α₀)
    (hDbound : (hsReachSet H U K f α₀).card ≤
      (hsTerminal H U K f α₀).card + D.card + 1)
    (hforced : ∀ w ∈ hsCls U f τ, ∀ d ∈ D, ∃ v ∈ hsCls U f d, H.Adj w v)
    (hfailw : ∀ w ∈ hsSol H U K f α₀ τ, ∀ ς ∈ hsReachSet H U K f α₀, ς ≠ τ →
      ∃ u ∈ U, f u = ς ∧ H.Adj w u) :
    (K \ hsReachSet H U K f α₀).card < (hsTerminal H U K f α₀).card := by
  have hBcard := (hsStruct_cards H U K f m α₀ β₀ hnear hβ₀).2
  have hTcard : (hsCls U f τ).card = m :=
    (hsStruct_term H U K f m α₀ β₀ hmaps hdeg hnear hβ₀).1 τ hτT
  have hNle := hsN_le H U K f m α₀ β₀ hmaps hdeg hnear hβ₀ τ hτT hfailw
  have hdouble := hsDouble_le H U K f m α₀ β₀ hmaps hdeg hnear hβ₀ τ hτT D
    hDsub hDbound hforced hfailw
  have hST : hsSol H U K f α₀ τ ⊆ hsCls U f τ := by
    intro w hw
    exact ((hsMem_sol H U K f α₀ τ w).mp hw).1
  have hNB : hsN H U K f α₀ (hsSol H U K f α₀ τ) ⊆
      U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀ := by
    intro z hz
    exact ((hsMem_hsN H U K f α₀ _ z).mp hz).1
  have hsplitT := Finset.card_sdiff_add_card_eq_card hST
  have hsplitB := Finset.card_sdiff_add_card_eq_card hNB
  have hsr : (hsSol H U K f α₀ τ).card +
      ((hsCls U f τ) \ hsSol H U K f α₀ τ).card = m := by omega
  have hB : (hsN H U K f α₀ (hsSol H U K f α₀ τ)).card +
      (U.filter (fun u => f u ∈ K \ hsReachSet H U K f α₀) \
        hsN H U K f α₀ (hsSol H U K f α₀ τ)).card =
      (K \ hsReachSet H U K f α₀).card *
        ((hsSol H U K f α₀ τ).card +
          ((hsCls U f τ) \ hsSol H U K f α₀ τ).card) + 1 := by
    rw [hsr]
    omega
  exact (hsArith_blt (hdouble := hdouble) (hNle := hNle) (hB := hB)).2

/-- Auxiliary: the solo partners of `z` (in `A'`). -/
private noncomputable def hsSoloOf {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ : C) (z : V) : Finset V :=
  @Finset.filter V
    (fun w => H.Adj z w ∧ ∀ v ∈ hsCls U f (f w), H.Adj z v → v = w)
    (fun _ => Classical.propDecidable _)
    (U.filter fun u => f u ∈ hsTerminal H U K f α₀)

private theorem hsMem_soloOf {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ : C) (z w : V) :
    w ∈ hsSoloOf H U K f α₀ z ↔
      w ∈ U.filter (fun u => f u ∈ hsTerminal H U K f α₀) ∧
        H.Adj z w ∧ ∀ v ∈ hsCls U f (f w), H.Adj z v → v = w := by
  simp only [hsSoloOf, Finset.mem_filter]

/-- Step: neighbours plus solo partners in a terminal class number ≥ 2. -/
private theorem hsClass_two {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ : C)
    (hmaps : hsMaps U K f)
    (z : V) (hzB : z ∈ U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀)
    (σ : C) (hσT : σ ∈ hsTerminal H U K f α₀) :
    1 ≤ (hsNbr H (hsCls U f σ) z).card ∧
    (hsNbr H (hsCls U f σ) z).card +
      ((hsSoloOf H U K f α₀ z).filter (fun u => f u = σ)).card ≥ 2 := by
  have hσA : σ ∈ hsReachSet H U K f α₀ :=
    ((hsMem_term H U K f α₀ σ).mp hσT).1
  obtain ⟨v₀, hv₀cls, hadj₀⟩ := hsStruct_nbrA H U K f α₀ hmaps z hzB σ hσA
  have hmem₀ : v₀ ∈ hsNbr H (hsCls U f σ) z :=
    (hsMem_nbr H _ _ _).mpr ⟨hv₀cls, hadj₀⟩
  have hn1 : 1 ≤ (hsNbr H (hsCls U f σ) z).card :=
    Finset.card_pos.mpr ⟨v₀, hmem₀⟩
  refine ⟨hn1, ?_⟩
  by_cases h1 : (hsNbr H (hsCls U f σ) z).card = 1
  · obtain ⟨u₀, hsingle⟩ := Finset.card_eq_one.mp h1
    have hva : v₀ = u₀ := Finset.mem_singleton.mp (hsingle ▸ hmem₀)
    have hu₀cls : u₀ ∈ hsCls U f σ := hva ▸ hv₀cls
    have hadj₀' : H.Adj z u₀ := hva ▸ hadj₀
    have hfu₀ : f u₀ = σ := ((hsMem_cls U f σ u₀).mp hu₀cls).2
    have hu₀U : u₀ ∈ U := ((hsMem_cls U f σ u₀).mp hu₀cls).1
    have huniq : ∀ v ∈ hsCls U f (f u₀), H.Adj z v → v = u₀ := by
      intro v hvcls hadj
      rw [hfu₀] at hvcls
      have hmem : v ∈ hsNbr H (hsCls U f σ) z :=
        (hsMem_nbr H _ _ _).mpr ⟨hvcls, hadj⟩
      exact Finset.mem_singleton.mp (hsingle ▸ hmem)
    have hA' : u₀ ∈ U.filter fun u => f u ∈ hsTerminal H U K f α₀ :=
      Finset.mem_filter.mpr ⟨hu₀U, by rw [hfu₀]; exact hσT⟩
    have hfib : u₀ ∈ (hsSoloOf H U K f α₀ z).filter (fun u => f u = σ) :=
      Finset.mem_filter.mpr
        ⟨(hsMem_soloOf H U K f α₀ z u₀).mpr ⟨hA', hadj₀', huniq⟩, hfu₀⟩
    have ht1 : 1 ≤ ((hsSoloOf H U K f α₀ z).filter
        (fun u => f u = σ)).card :=
      Finset.card_pos.mpr ⟨u₀, hfib⟩
    omega
  · have h2 : 2 ≤ (hsNbr H (hsCls U f σ) z).card := by omega
    have ht0 : 0 ≤ ((hsSoloOf H U K f α₀ z).filter
        (fun u => f u = σ)).card := Nat.zero_le _
    omega

/-- `s_z + b ≥ a' + 1 + (nbr B z).card`. -/
private theorem hsFinish_d {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (m : ℕ) (α₀ β₀ : C)
    (hmaps : hsMaps U K f) (hdeg : hsDegLt H U K)
    (hnear : hsNearly U K f m α₀ β₀)
    (hβ₀ : β₀ ∉ hsReachSet H U K f α₀)
    (z : V) (hzB : z ∈ U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀) :
    (hsSoloOf H U K f α₀ z).card + (K \ hsReachSet H U K f α₀).card ≥
      (hsTerminal H U K f α₀).card + 1 +
        (hsNbr H (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀) z).card := by
  have hTsub : hsTerminal H U K f α₀ ⊆ hsReachSet H U K f α₀ := by
    intro σ hσ
    exact ((hsMem_term H U K f α₀ σ).mp hσ).1
  obtain ⟨_, _, hABdisj, hABunion, hKcard⟩ :=
    hsStruct_setup H U K f m α₀ β₀ hmaps hnear hβ₀
  have hzU : z ∈ U := (Finset.mem_filter.mp hzB).1
  have hnA : ∀ σ ∈ hsReachSet H U K f α₀,
      1 ≤ (hsNbr H (hsCls U f σ) z).card := by
    intro σ hσA
    obtain ⟨v, hvcls, hadj⟩ := hsStruct_nbrA H U K f α₀ hmaps z hzB σ hσA
    exact Finset.card_pos.mpr ⟨v, (hsMem_nbr H _ _ _).mpr ⟨hvcls, hadj⟩⟩
  have hnt : ∀ σ ∈ hsTerminal H U K f α₀,
      (hsNbr H (hsCls U f σ) z).card +
        ((hsSoloOf H U K f α₀ z).filter (fun u => f u = σ)).card ≥ 2 := by
    intro σ hσT
    exact (hsClass_two H U K f α₀ hmaps z hzB σ hσT).2
  have hS1 : ∑ σ ∈ hsReachSet H U K f α₀, (hsNbr H (hsCls U f σ) z).card =
      (hsNbr H (U.filter fun u => f u ∈ hsReachSet H U K f α₀) z).card := by
    rw [show hsNbr H (U.filter fun u => f u ∈ hsReachSet H U K f α₀) z =
      (U.filter fun u => f u ∈ hsReachSet H U K f α₀).filter
        (fun u => H.Adj z u) from rfl,
      hsCount_nbr H U (hsReachSet H U K f α₀) f z]
  have hmaps' : ∀ u ∈ hsSoloOf H U K f α₀ z,
      f u ∈ hsTerminal H U K f α₀ := by
    intro u hu
    exact (Finset.mem_filter.mp
      ((hsMem_soloOf H U K f α₀ z u).mp hu).1).2
  have hTsolo := hsCount_gen (hsSoloOf H U K f α₀ z)
    (hsTerminal H U K f α₀) f hmaps'
  have hsplit : ∑ σ ∈ hsReachSet H U K f α₀ \ hsTerminal H U K f α₀,
        (hsNbr H (hsCls U f σ) z).card +
      ∑ σ ∈ hsTerminal H U K f α₀, (hsNbr H (hsCls U f σ) z).card =
      ∑ σ ∈ hsReachSet H U K f α₀, (hsNbr H (hsCls U f σ) z).card := by
    rw [← Finset.sum_union ((Finset.disjoint_sdiff
      (s := hsTerminal H U K f α₀) (t := hsReachSet H U K f α₀)).symm),
      Finset.sdiff_union_of_subset hTsub]
  have hsubcard := Finset.card_sdiff_add_card_eq_card hTsub
  have hlowC : (hsReachSet H U K f α₀ \ hsTerminal H U K f α₀).card ≤
      ∑ σ ∈ hsReachSet H U K f α₀ \ hsTerminal H U K f α₀,
        (hsNbr H (hsCls U f σ) z).card := by
    calc (hsReachSet H U K f α₀ \ hsTerminal H U K f α₀).card
        = ∑ _σ ∈ hsReachSet H U K f α₀ \ hsTerminal H U K f α₀, 1 := by simp
      _ ≤ ∑ σ ∈ hsReachSet H U K f α₀ \ hsTerminal H U K f α₀,
          (hsNbr H (hsCls U f σ) z).card :=
        Finset.sum_le_sum (fun σ hσ => hnA σ (Finset.sdiff_subset hσ))
  have hlowT : 2 * (hsTerminal H U K f α₀).card ≤
      ∑ σ ∈ hsTerminal H U K f α₀, ((hsNbr H (hsCls U f σ) z).card +
        ((hsSoloOf H U K f α₀ z).filter (fun u => f u = σ)).card) := by
    calc 2 * (hsTerminal H U K f α₀).card
        = ∑ _σ ∈ hsTerminal H U K f α₀, 2 := by
          rw [Finset.sum_const, smul_eq_mul]
          exact Nat.mul_comm _ _
      _ ≤ ∑ σ ∈ hsTerminal H U K f α₀, ((hsNbr H (hsCls U f σ) z).card +
          ((hsSoloOf H U K f α₀ z).filter (fun u => f u = σ)).card) :=
        Finset.sum_le_sum (fun σ hσ => hnt σ hσ)
  have hdist := Finset.sum_add_distrib (s := hsTerminal H U K f α₀)
    (f := fun σ => (hsNbr H (hsCls U f σ) z).card)
    (g := fun σ => ((hsSoloOf H U K f α₀ z).filter (fun u => f u = σ)).card)
  have hsplit_deg := hsSplit_nbr H U
    (U.filter fun u => f u ∈ hsReachSet H U K f α₀)
    (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀) z hABunion hABdisj
  have hdegz := hdeg z hzU
  omega

/-- A maximal independent set in `B` has at least `m + 1` vertices. -/
private theorem hsFinish_e {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (m : ℕ) (α₀ β₀ : C)
    (hmaps : hsMaps U K f) (hdeg : hsDegLt H U K)
    (hnear : hsNearly U K f m α₀ β₀)
    (hβ₀ : β₀ ∉ hsReachSet H U K f α₀) :
    ∃ I, I ⊆ U.filter (fun u => f u ∈ K \ hsReachSet H U K f α₀) ∧
      (∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ H.Adj u v) ∧
      (∀ z ∈ U.filter (fun u => f u ∈ K \ hsReachSet H U K f α₀),
        z ∉ I → ∃ u ∈ I, H.Adj z u) ∧
      m + 1 ≤ I.card := by
  set B := U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀ with hBdef
  have hNB : (B.powerset.filter fun s =>
      ∀ u ∈ s, ∀ v ∈ s, u ≠ v → ¬ H.Adj u v).Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset B, ?_⟩⟩
    intro u hu
    exact (Finset.notMem_empty u hu).elim
  obtain ⟨I, hImem, hImax⟩ := Finset.exists_max_image _
    (fun s => s.card) hNB
  have hIsub : I ⊆ B := Finset.mem_powerset.mp (Finset.mem_filter.mp hImem).1
  have hIpair : ∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ H.Adj u v :=
    (Finset.mem_filter.mp hImem).2
  have hex : ∀ z ∈ B, z ∉ I → ∃ u ∈ I, H.Adj z u := by
    intro z hzB hzI
    by_contra hcon
    push Not at hcon
    have hins : insert z I ∈ B.powerset.filter
        (fun s => ∀ u ∈ s, ∀ v ∈ s, u ≠ v → ¬ H.Adj u v) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr ?_, ?_⟩
      · intro w hw
        rw [Finset.mem_insert] at hw
        rcases hw with rfl | hwI
        · exact hzB
        · exact hIsub hwI
      · intro u hu v hv huv hadj
        rw [Finset.mem_insert] at hu hv
        rcases hu with rfl | huI <;> rcases hv with rfl | hvI
        · exact (huv rfl).elim
        · exact (hcon v hvI hadj).elim
        · exact (hcon u huI (H.adj_symm hadj)).elim
        · exact hIpair u huI v hvI huv hadj
    have hlt : I.card < (insert z I).card :=
      Finset.card_lt_card (Finset.ssubset_insert hzI)
    have hle' : (insert z I).card ≤ I.card := hImax _ hins
    omega
  have hcover : B \ I ⊆ I.biUnion (fun u => hsNbr H B u) := by
    intro z hz
    obtain ⟨hzB, hzI⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨u, huI, hadj⟩ := hex z hzB hzI
    exact Finset.mem_biUnion.mpr ⟨u, huI,
      (hsMem_nbr H _ _ _).mpr ⟨hzB, H.adj_symm hadj⟩⟩
  have hleBI : (B \ I).card ≤ ∑ u ∈ I, (hsNbr H B u).card := by
    calc (B \ I).card ≤ (I.biUnion fun u => hsNbr H B u).card :=
          Finset.card_le_card hcover
      _ ≤ ∑ u ∈ I, (hsNbr H B u).card := Finset.card_biUnion_le
  have hdegI : ∀ u ∈ I, (hsNbr H B u).card + 1 ≤
      (K \ hsReachSet H U K f α₀).card := by
    intro u huI
    have huB : u ∈ U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀ :=
      hBdef ▸ hIsub huI
    have hlt : (hsNbr H B u).card < (K \ hsReachSet H U K f α₀).card :=
      (hsStruct_degB H U K f m α₀ β₀ hmaps hdeg hnear hβ₀ u huB).2
    omega
  have hsum : ∑ u ∈ I, ((hsNbr H B u).card + 1) ≤
      (K \ hsReachSet H U K f α₀).card * I.card := by
    calc ∑ u ∈ I, ((hsNbr H B u).card + 1)
        ≤ ∑ _u ∈ I, (K \ hsReachSet H U K f α₀).card :=
        Finset.sum_le_sum hdegI
      _ = (K \ hsReachSet H U K f α₀).card * I.card := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hdist2 : ∑ u ∈ I, ((hsNbr H B u).card + 1) =
      (∑ u ∈ I, (hsNbr H B u).card) + ∑ _u ∈ I, 1 :=
    Finset.sum_add_distrib
  have hone : ∑ _u ∈ I, 1 = I.card := by simp
  have hsplitI := Finset.card_sdiff_add_card_eq_card hIsub
  have hBI : B.card ≤ (K \ hsReachSet H U K f α₀).card * I.card := by omega
  have hBcard' : B.card = (K \ hsReachSet H U K f α₀).card * m + 1 :=
    (hsStruct_cards H U K f m α₀ β₀ hnear hβ₀).2
  have hb1 : 1 ≤ (K \ hsReachSet H U K f α₀).card :=
    (hsStruct_bfacts H U K f m α₀ β₀ hmaps hnear hβ₀).1
  have hIm : m + 1 ≤ I.card := by
    by_cases hle : I.card ≤ m
    · have h2 := mul_le_mul_of_nonneg_left hle
        (Nat.zero_le (K \ hsReachSet H U K f α₀).card)
      omega
    · omega
  have hex' : ∀ z ∈ U.filter (fun u => f u ∈ K \ hsReachSet H U K f α₀),
      z ∉ I → ∃ u ∈ I, H.Adj z u := by
    intro z hz hzI
    exact hex z (hBdef.symm ▸ hz) hzI
  exact ⟨I, hIsub, hIpair, hex', hIm⟩

/-- Auxiliary: pairs `(z, w)` with `z ∈ I` and `w` a solo partner of `z`. -/
private noncomputable def hsP {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ : C)
    (I : Finset V) : Finset (V × V) :=
  @Finset.filter (V × V)
    (fun p => p.2 ∈ hsSoloOf H U K f α₀ p.1)
    (fun _ => Classical.propDecidable _)
    (I ×ˢ (U.filter fun u => f u ∈ hsTerminal H U K f α₀))

private theorem hsMem_P {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ : C)
    (I : Finset V) (p : V × V) :
    p ∈ hsP H U K f α₀ I ↔ p.1 ∈ I ∧ p.2 ∈ hsSoloOf H U K f α₀ p.1 := by
  simp only [hsP, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨hp1, -⟩, hp2⟩
    exact ⟨hp1, hp2⟩
  · rintro ⟨hp1, hp2⟩
    have hpA : p.2 ∈ U.filter fun u => f u ∈ hsTerminal H U K f α₀ :=
      ((hsMem_soloOf H U K f α₀ p.1 p.2).mp hp2).1
    obtain ⟨hU, hT⟩ := Finset.mem_filter.mp hpA
    exact ⟨⟨hp1, hU, hT⟩, hp2⟩

/-- Step: the fiber of `hsP` over `z` counts the solo partners of `z`. -/
private theorem hsP_fiber {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ : C)
    (I : Finset V) (z : V) (hzI : z ∈ I) :
    ((hsP H U K f α₀ I).filter (fun p => p.1 = z)).card =
      (hsSoloOf H U K f α₀ z).card := by
  have heq : (hsP H U K f α₀ I).filter (fun p => p.1 = z) =
      (hsSoloOf H U K f α₀ z).image (fun w => (z, w)) := by
    ext p
    constructor
    · intro hp
      obtain ⟨hpP, hpfst⟩ := Finset.mem_filter.mp hp
      obtain ⟨-, hp2⟩ := (hsMem_P H U K f α₀ I p).mp hpP
      refine Finset.mem_image.mpr ⟨p.2, ?_, ?_⟩
      · rw [hpfst] at hp2
        exact hp2
      · rw [← hpfst]
    · intro hp
      obtain ⟨w, hwsolo, hzw⟩ := Finset.mem_image.mp hp
      subst hzw
      apply Finset.mem_filter.mpr
      refine ⟨(hsMem_P H U K f α₀ I (z, w)).mpr ⟨?_, ?_⟩, rfl⟩
      · exact hzI
      · exact hwsolo
  rw [heq, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2)]

/-- Step: `P.card` is the sum over `I` of the solo-partner counts. -/
private theorem hsP_card {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (α₀ : C)
    (I : Finset V) :
    (hsP H U K f α₀ I).card = ∑ z ∈ I, (hsSoloOf H U K f α₀ z).card := by
  have hmaps' : ∀ p ∈ hsP H U K f α₀ I, Prod.fst p ∈ I := by
    intro p hp
    exact ((hsMem_P H U K f α₀ I p).mp hp).1
  have hgen := hsCount_gen (hsP H U K f α₀ I) I Prod.fst hmaps'
  refine hgen.trans ?_
  apply Finset.sum_congr rfl
  intro z hzI
  exact hsP_fiber H U K f α₀ I z hzI

/-- Arithmetic: the summed bound forces `P.card > a' * m`. -/
private theorem hsArith_ph {P u m b a' S : ℕ}
    (hD : P + b * u ≥ a' * u + u + S)
    (hS : S + u ≥ b * m + 1)
    (hI : m + 1 ≤ u) (hlt : b < a') :
    a' * m < P := by
  obtain ⟨d, hd_eq, hd1⟩ : ∃ d, a' = b + d ∧ 1 ≤ d := ⟨a' - b, by omega, by omega⟩
  have e1 : a' * u = b * u + d * u := by rw [hd_eq, add_mul]
  have e2 : a' * m = b * m + d * m := by rw [hd_eq, add_mul]
  have hm1 : d * (m + 1) ≤ d * u :=
    mul_le_mul_of_nonneg_left hI (Nat.zero_le d)
  have hm2 : m + 1 ≤ d * (m + 1) := by
    have h := mul_le_mul_of_nonneg_right hd1 (Nat.zero_le (m + 1))
    rwa [one_mul] at h
  have e3 : d * (m + 1) = d * m + d := by rw [mul_add, mul_one]
  omega

/-- `hsFinish`: if Cases 0 and 1 fail, Case 2 data exists. -/
private theorem hsFinish {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (K : Finset C) (f : V → C) (m : ℕ) (α₀ β₀ : C)
    (hmaps : hsMaps U K f) (hdeg : hsDegLt H U K)
    (hnear : hsNearly U K f m α₀ β₀)
    (hβ₀ : β₀ ∉ hsReachSet H U K f α₀)
    (hno1 : ∀ (w y : V) (α : C), w ∈ U →
      y ∈ U.filter (fun u => f u ∈ K \ hsReachSet H U K f α₀) →
      f w ∈ hsTerminal H U K f α₀ →
      H.Adj y w → (∀ v ∈ hsCls U f (f w), H.Adj y v → v = w) →
      α ∈ hsReachSet H U K f α₀ → α ≠ f w →
      ∃ u ∈ U, f u = α ∧ H.Adj w u) :
    ∃ w y z, w ∈ U ∧
      y ∈ U.filter (fun u => f u ∈ K \ hsReachSet H U K f α₀) ∧
      z ∈ U.filter (fun u => f u ∈ K \ hsReachSet H U K f α₀) ∧
      f w ∈ hsTerminal H U K f α₀ ∧
      (H.Adj y w ∧ ∀ v ∈ hsCls U f (f w), H.Adj y v → v = w) ∧
      (H.Adj z w ∧ ∀ v ∈ hsCls U f (f w), H.Adj z v → v = w) ∧
      y ≠ z ∧ ¬ H.Adj y z ∧
      (∀ σ ∈ hsReachSet H U K f α₀, σ ≠ f w →
        ∃ u ∈ U, f u = σ ∧ H.Adj w u) := by
  obtain ⟨τ, D, hτT, hDsub, _, hDbound, hforced⟩ :=
    hsFinish_a H U K f m α₀ β₀ hmaps hdeg hnear hβ₀
  have hfailw : ∀ w ∈ hsSol H U K f α₀ τ, ∀ ς ∈ hsReachSet H U K f α₀,
      ς ≠ τ → ∃ u ∈ U, f u = ς ∧ H.Adj w u := by
    intro w hwSol ς hς hne
    obtain ⟨hwT, z, hzB, hadj, huniq⟩ :=
      (hsMem_sol H U K f α₀ τ w).mp hwSol
    have hwU : w ∈ U := ((hsMem_cls U f τ w).mp hwT).1
    have hfw : f w = τ := ((hsMem_cls U f τ w).mp hwT).2
    have hfwT : f w ∈ hsTerminal H U K f α₀ := by
      rw [hfw]
      exact hτT
    have hne' : ς ≠ f w := by
      intro h
      rw [hfw] at h
      exact hne h
    exact hno1 w z ς hwU hzB hfwT hadj huniq hς hne'
  have hlt := hsFinish_c H U K f m α₀ β₀ hmaps hdeg hnear hβ₀ τ hτT D
    hDsub hDbound hforced hfailw
  obtain ⟨I, hIsub, hIpair, hIcover, hIm⟩ :=
    hsFinish_e H U K f m α₀ β₀ hmaps hdeg hnear hβ₀
  have hDsummed : ∑ z ∈ I, ((hsTerminal H U K f α₀).card + 1 +
      (hsNbr H (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀) z).card) ≤
      ∑ z ∈ I, ((hsSoloOf H U K f α₀ z).card +
        (K \ hsReachSet H U K f α₀).card) := by
    apply Finset.sum_le_sum
    intro z hz
    have h := hsFinish_d H U K f m α₀ β₀ hmaps hdeg hnear hβ₀ z (hIsub hz)
    omega
  have hPeq := hsP_card H U K f α₀ I
  have hdistP : ∑ z ∈ I, ((hsSoloOf H U K f α₀ z).card +
      (K \ hsReachSet H U K f α₀).card) =
      (∑ z ∈ I, (hsSoloOf H U K f α₀ z).card) +
        ∑ _z ∈ I, (K \ hsReachSet H U K f α₀).card :=
    Finset.sum_add_distrib
  have hconstP : ∑ _z ∈ I, (K \ hsReachSet H U K f α₀).card =
      (K \ hsReachSet H U K f α₀).card * I.card := by
    rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hdistA : ∑ z ∈ I, ((hsTerminal H U K f α₀).card + 1 +
      (hsNbr H (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀) z).card) =
      (∑ _z ∈ I, ((hsTerminal H U K f α₀).card + 1)) +
        ∑ z ∈ I, (hsNbr H
          (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀) z).card :=
    Finset.sum_add_distrib
  have hconstA : ∑ _z ∈ I, ((hsTerminal H U K f α₀).card + 1) =
      ((hsTerminal H U K f α₀).card + 1) * I.card := by
    rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hconv : ((hsTerminal H U K f α₀).card + 1) * I.card =
      (hsTerminal H U K f α₀).card * I.card + I.card := by
    rw [add_mul, one_mul]
  have hcover : (U.filter (fun u => f u ∈ K \ hsReachSet H U K f α₀) \ I).card ≤
      ∑ z ∈ I, (hsNbr H
        (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀) z).card := by
    calc (U.filter (fun u => f u ∈ K \ hsReachSet H U K f α₀) \ I).card
        ≤ (I.biUnion fun u => hsNbr H
          (U.filter fun v => f v ∈ K \ hsReachSet H U K f α₀) u).card := by
          apply Finset.card_le_card
          intro z hz
          obtain ⟨hzB, hzI⟩ := Finset.mem_sdiff.mp hz
          obtain ⟨u, huI, hadj⟩ := hIcover z hzB hzI
          exact Finset.mem_biUnion.mpr ⟨u, huI,
            (hsMem_nbr H _ _ _).mpr ⟨hzB, H.adj_symm hadj⟩⟩
      _ ≤ ∑ z ∈ I, (hsNbr H
          (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀) z).card :=
        Finset.card_biUnion_le
  have hsplitB := Finset.card_sdiff_add_card_eq_card hIsub
  have hBcard := (hsStruct_cards H U K f m α₀ β₀ hnear hβ₀).2
  have hD : (hsP H U K f α₀ I).card +
      (K \ hsReachSet H U K f α₀).card * I.card ≥
      (hsTerminal H U K f α₀).card * I.card + I.card +
        ∑ z ∈ I, (hsNbr H
          (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀) z).card := by
    omega
  have hS : (∑ z ∈ I, (hsNbr H
      (U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀) z).card) +
      I.card ≥ (K \ hsReachSet H U K f α₀).card * m + 1 := by
    omega
  have hplt : (hsTerminal H U K f α₀).card * m < (hsP H U K f α₀ I).card :=
    hsArith_ph (hD := hD) (hS := hS) (hI := hIm) (hlt := hlt)
  have hAcard := (hsStruct_term H U K f m α₀ β₀ hmaps hdeg hnear hβ₀).2
  have hmap : Set.MapsTo (Prod.snd : V × V → V)
      (↑(hsP H U K f α₀ I) : Set (V × V))
      (↑(U.filter fun u => f u ∈ hsTerminal H U K f α₀) : Set V) := by
    intro p hp
    have hp' : p ∈ hsP H U K f α₀ I := Finset.mem_coe.mp hp
    obtain ⟨-, hp2⟩ := (hsMem_P H U K f α₀ I p).mp hp'
    have hA : p.2 ∈ U.filter fun u => f u ∈ hsTerminal H U K f α₀ :=
      ((hsMem_soloOf H U K f α₀ p.1 p.2).mp hp2).1
    exact Finset.mem_coe.mpr hA
  have hcardlt : (U.filter fun u => f u ∈ hsTerminal H U K f α₀).card <
      (hsP H U K f α₀ I).card := by omega
  obtain ⟨p, hpP, q, hqP, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (f := Prod.snd) hcardlt hmap
  obtain ⟨hp1, hp2⟩ := (hsMem_P H U K f α₀ I p).mp hpP
  obtain ⟨hq1, hq2⟩ := (hsMem_P H U K f α₀ I q).mp hqP
  obtain ⟨hwA, hadjy, huniqy⟩ :=
    (hsMem_soloOf H U K f α₀ p.1 p.2).mp hp2
  obtain ⟨hwA', hadjz, huniqz⟩ :=
    (hsMem_soloOf H U K f α₀ q.1 q.2).mp hq2
  have hwU : p.2 ∈ U := (Finset.mem_filter.mp hwA).1
  have hfwT : f p.2 ∈ hsTerminal H U K f α₀ :=
    (Finset.mem_filter.mp hwA).2
  have hyB : p.1 ∈ U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀ :=
    hIsub hp1
  have hzB : q.1 ∈ U.filter fun u => f u ∈ K \ hsReachSet H U K f α₀ :=
    hIsub hq1
  have hyz : p.1 ≠ q.1 := by
    intro h
    apply hne
    rw [← Prod.mk.eta (p := p), ← Prod.mk.eta (p := q), h, heq]
  have hnadj : ¬ H.Adj p.1 q.1 := hIpair p.1 hp1 q.1 hq1 hyz
  have hadjz' : H.Adj q.1 p.2 := by rw [heq]; exact hadjz
  have huniqz' : ∀ v ∈ hsCls U f (f p.2), H.Adj q.1 v → v = p.2 := by
    rw [heq]
    exact huniqz
  have hfail : ∀ σ ∈ hsReachSet H U K f α₀, σ ≠ f p.2 →
      ∃ u ∈ U, f u = σ ∧ H.Adj p.2 u := by
    intro σ hσ hne2
    exact hno1 p.2 p.1 σ hwU hyB hfwT hadjy huniqy hσ hne2
  exact ⟨p.2, p.1, q.1, hwU, hyB, hzB, hfwT, ⟨hadjy, huniqy⟩,
    ⟨hadjz', huniqz'⟩, hyz, hnadj, hfail⟩

/-- The main lemma, by outer induction on `K.card` and inner induction
on `K.card − 𝒜.card`. -/
private theorem hsMain {V C : Type*} [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    ∀ (n : ℕ) (U : Finset V) (K : Finset C) (f : V → C) (m : ℕ) (α₀ β₀ : C),
    K.card = n → hsMaps U K f → hsProper H U f → hsDegLt H U K →
    hsNearly U K f m α₀ β₀ →
    ∃ g, hsMaps U K g ∧ hsProper H U g ∧ hsEquitable U K g m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IHout =>
    intro U K f m α₀ β₀ hKn hmaps hproper hdeg hnear
    have hIH : ∀ (K' : Finset C) (U' : Finset V) (f' : V → C)
        (m' : ℕ) (α' β' : C), K'.card < K.card → hsMaps U' K' f' →
        hsProper H U' f' → hsDegLt H U' K' →
        hsNearly U' K' f' m' α' β' →
        ∃ g, hsMaps U' K' g ∧ hsProper H U' g ∧
          hsEquitable U' K' g m' := by
      intro K' U' f' m' α' β' hlt hm hp hd hn
      have hlt' : K'.card < n := by omega
      exact IHout K'.card hlt' U' K' f' m' α' β' rfl hm hp hd hn
    have inner : ∀ (j : ℕ) (f : V → C) (β₀ : C),
        K.card - (hsReachSet H U K f α₀).card = j →
        hsMaps U K f → hsProper H U f → hsDegLt H U K →
        hsNearly U K f m α₀ β₀ →
        ∃ g, hsMaps U K g ∧ hsProper H U g ∧ hsEquitable U K g m := by
      intro j
      induction j using Nat.strong_induction_on with
      | _ j IHin =>
        intro f β₀ hj hmaps hproper hdeg hnear
        by_cases hβ : β₀ ∈ hsReachSet H U K f α₀
        · exact hsCase0 H U K f m α₀ β₀ hmaps hproper hnear hβ
        · by_cases hcase1 : ∃ w y α, w ∈ U ∧
              y ∈ U.filter (fun u => f u ∈ K \ hsReachSet H U K f α₀) ∧
              f w ∈ hsTerminal H U K f α₀ ∧
              (H.Adj y w ∧ ∀ v ∈ hsCls U f (f w), H.Adj y v → v = w) ∧
              α ∈ hsReachSet H U K f α₀ ∧ α ≠ f w ∧
              (∀ u ∈ U, f u = α → ¬ H.Adj w u)
          · obtain ⟨w, y, α, hwU, hyB, hωT, hsolo, hαA, hαω, hwit⟩ := hcase1
            exact hsCase1 H U K f m α₀ β₀ hmaps hproper hdeg hnear hβ hIH
              w y α hwU hyB hωT hsolo hαA hαω hwit
          · have hno1 : ∀ (w y : V) (α : C), w ∈ U →
                y ∈ U.filter (fun u => f u ∈ K \ hsReachSet H U K f α₀) →
                f w ∈ hsTerminal H U K f α₀ →
                H.Adj y w → (∀ v ∈ hsCls U f (f w), H.Adj y v → v = w) →
                α ∈ hsReachSet H U K f α₀ → α ≠ f w →
                ∃ u ∈ U, f u = α ∧ H.Adj w u := by
              intro w y α hwU hyB hωT hsolo1 hsolo2 hαA hαω
              by_contra hcon
              have hwit : ∀ u ∈ U, f u = α → ¬ H.Adj w u := by
                intro u huU hfu hadj
                exact hcon ⟨u, huU, hfu, hadj⟩
              exact hcase1 ⟨w, y, α, hwU, hyB, hωT, ⟨hsolo1, hsolo2⟩,
                hαA, hαω, hwit⟩
            obtain ⟨w, y, z, hwU, hyB, hzB, hωT, hsoloy, hsoloz, hyz, hnadj,
                hfail⟩ :=
              hsFinish H U K f m α₀ β₀ hmaps hdeg hnear hβ hno1
            obtain ⟨f', hmaps', hproper', γ, hγB, hnear', hgrow⟩ :=
              hsCase2 H U K f m α₀ β₀ hmaps hproper hdeg hnear hβ hIH
                w y z hwU hyB hzB hωT hsoloy hsoloz hyz hnadj hfail
            have hsub : hsReachSet H U K f' α₀ ⊆ K := by
              intro σ hσ
              exact ((hsMem_reach H U K f' α₀ σ).mp hσ).1
            have hcardlt : K.card - (hsReachSet H U K f' α₀).card < j := by
              have hle := Finset.card_le_card hsub
              omega
            exact IHin (K.card - (hsReachSet H U K f' α₀).card) hcardlt
              f' γ rfl hmaps' hproper' hdeg hnear'
    exact inner (K.card - (hsReachSet H U K f α₀).card) f β₀ rfl
      hmaps hproper hdeg hnear

/-- Auxiliary: the spanning subgraph of `G'` on the vertices of `S`. -/
private def hsSub {V' : Type*} [DecidableEq V'] (G' : SimpleGraph V')
    (S : Finset V') : SimpleGraph V' where
  Adj u v := G'.Adj u v ∧ u ∈ S ∧ v ∈ S
  symm := ⟨fun _ _ h => ⟨G'.adj_symm h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G'.irrefl h.1⟩

private noncomputable instance hsSub_dec {V' : Type*} [DecidableEq V']
    (G' : SimpleGraph V') (S : Finset V') :
    DecidableRel (hsSub G' S).Adj :=
  fun _ _ => Classical.propDecidable _

private theorem hsMem_sub {V' : Type*} [DecidableEq V']
    (G' : SimpleGraph V') (S : Finset V') (u v : V') :
    (hsSub G' S).Adj u v ↔ G'.Adj u v ∧ u ∈ S ∧ v ∈ S :=
  Iff.rfl

/-- Arithmetic: padding counts. -/
private theorem hsPad_arith (n k : ℕ) (hk : 0 < k) :
    ∃ m p, m = n / k + 1 ∧ k * m = n + p ∧ 1 ≤ p ∧ p ≤ k := by
  have hmod := Nat.div_add_mod n k
  have hlt := Nat.mod_lt n hk
  have e : k * (n / k + 1) = k * (n / k) + k := by rw [mul_add, mul_one]
  exact ⟨n / k + 1, k * (n / k + 1) - n, rfl, by omega, by omega, by omega⟩

/-- Auxiliary: no edges between the two sides of a sum. -/
private theorem hsSum_nocross {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (a : V) (b : W) :
    ¬ (G ⊕g H).Adj (Sum.inl a) (Sum.inr b) := by
  simp

private theorem hsSum_nocrossR {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (a : V) (b : W) :
    ¬ (G ⊕g H).Adj (Sum.inr b) (Sum.inl a) := by
  simp

/-- Every vertex of the padded graph has fewer than `k` neighbours. -/
private theorem hsDeg_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : G.maxDegree < k)
    (p : ℕ) (hp1 : 1 ≤ p) (hpk : p ≤ k) (v : V ⊕ Fin p) :
    ((G ⊕g ⊤).neighborFinset v).card < k := by
  cases v with
  | inl a =>
    have heq : (G ⊕g ⊤).neighborFinset (Sum.inl a) =
        (G.neighborFinset a).image (Sum.inl : V → V ⊕ Fin p) := by
      ext w
      rw [SimpleGraph.mem_neighborFinset]
      constructor
      · intro hadj
        cases w with
        | inl b =>
          rw [SimpleGraph.sum_adj_inl] at hadj
          have hb' : b ∈ G.neighborFinset a := by
            rw [SimpleGraph.mem_neighborFinset]
            exact hadj
          exact Finset.mem_image.mpr ⟨b, hb', rfl⟩
        | inr j =>
          exact (hsSum_nocross G ⊤ a j hadj).elim
      · intro hmem
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hmem
        rw [SimpleGraph.sum_adj_inl]
        have hb' : G.Adj a b := by
          rw [← SimpleGraph.mem_neighborFinset]
          exact hb
        exact hb'
    rw [heq, Finset.card_image_of_injective _ Sum.inl_injective,
      SimpleGraph.card_neighborFinset_eq_degree]
    exact lt_of_le_of_lt (G.degree_le_maxDegree a) hk
  | inr i =>
    have heq : (G ⊕g ⊤).neighborFinset (Sum.inr i) =
        (Finset.univ.erase i).image (Sum.inr : Fin p → V ⊕ Fin p) := by
      ext w
      rw [SimpleGraph.mem_neighborFinset]
      constructor
      · intro hadj
        cases w with
        | inl a =>
          exact (hsSum_nocrossR G ⊤ a i hadj).elim
        | inr j =>
          rw [SimpleGraph.sum_adj_inr, SimpleGraph.top_adj] at hadj
          exact Finset.mem_image.mpr
            ⟨j, Finset.mem_erase.mpr ⟨Ne.symm hadj, Finset.mem_univ j⟩, rfl⟩
      · intro hmem
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hmem
        rw [SimpleGraph.sum_adj_inr, SimpleGraph.top_adj]
        obtain ⟨hne, -⟩ := Finset.mem_erase.mp hj
        exact Ne.symm hne
    rw [heq, Finset.card_image_of_injective _ Sum.inr_injective,
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
    omega

/-- The degree bound transfers to every spanning subgraph of the sum. -/
private theorem hsSub_deg_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : G.maxDegree < k)
    (p : ℕ) (hp1 : 1 ≤ p) (hpk : p ≤ k)
    (S : Finset (V ⊕ Fin p)) :
    hsDegLt (hsSub (G ⊕g (⊤ : SimpleGraph (Fin p))) S) Finset.univ
      (Finset.univ : Finset (Fin k)) := by
  intro v _
  have hsub : hsNbr (hsSub (G ⊕g (⊤ : SimpleGraph (Fin p))) S)
      Finset.univ v ⊆
      (G ⊕g (⊤ : SimpleGraph (Fin p))).neighborFinset v := by
    intro u hu
    rw [hsMem_nbr] at hu
    obtain ⟨hadj, _, _⟩ := (hsMem_sub _ _ v u).mp hu.2
    rw [SimpleGraph.mem_neighborFinset]
    exact hadj
  have hle := Finset.card_le_card hsub
  have hlt := hsDeg_sum G k hk p hp1 hpk v
  have hK : (Finset.univ : Finset (Fin k)).card = k := by
    rw [Finset.card_univ, Fintype.card_fin]
  omega

/-- Base: a balanced coloring, proper for the empty spanning subgraph. -/
private theorem hsGrowBase {V' : Type*} [Fintype V'] [DecidableEq V']
    (G' : SimpleGraph V')
    (k m : ℕ) (hcard : Fintype.card V' = k * m) :
    ∃ f : V' → Fin k, hsProper (hsSub G' ∅) Finset.univ f ∧
      hsEquitable Finset.univ Finset.univ f m := by
  have e' : V' ≃ Fin k × Fin m :=
    (Fintype.equivFinOfCardEq hcard).trans finProdFinEquiv.symm
  set f : V' → Fin k := fun v => (e' v).1 with hfdef
  have heq : ∀ c : Fin k, hsCls Finset.univ f c =
      (({c} ×ˢ Finset.univ).map e'.symm.toEmbedding) := by
    intro c
    ext v
    rw [hsMem_cls]
    constructor
    · rintro ⟨-, hfc⟩
      apply Finset.mem_map.mpr
      refine ⟨e' v, ?_, e'.symm_apply_apply v⟩
      rw [Finset.mem_product]
      refine ⟨?_, Finset.mem_univ _⟩
      rw [Finset.mem_singleton]
      exact hfc
    · intro hmem
      obtain ⟨b, hb, hsym⟩ := Finset.mem_map.mp hmem
      obtain ⟨hb1, -⟩ := Finset.mem_product.mp hb
      have hb1' : b.1 = c := Finset.mem_singleton.mp hb1
      have hev : e' v = b := by
        rw [← hsym]
        exact e'.apply_symm_apply b
      refine ⟨Finset.mem_univ v, ?_⟩
      have hev' : f v = c := by
        simp only [hfdef]
        rw [hev]
        exact hb1'
      exact hev'
  refine ⟨f, ?_, ?_⟩
  · intro u _ v _ hadj _
    obtain ⟨-, huS, -⟩ := (hsMem_sub G' ∅ u v).mp hadj
    exact (Finset.notMem_empty u huS).elim
  · intro c _
    rw [heq c, Finset.card_map, Finset.card_product, Finset.card_singleton,
      Finset.card_univ, Fintype.card_fin, one_mul]

/-- Step: extend the coloring across one more vertex. -/
private theorem hsGrowStep {V' : Type*} [Fintype V'] [DecidableEq V']
    (G' : SimpleGraph V')
    (k m : ℕ)
    (S : Finset V') (v : V') (hvS : v ∉ S)
    (f : V' → Fin k)
    (hfproper : hsProper (hsSub G' S) Finset.univ f)
    (hfeq : hsEquitable Finset.univ Finset.univ f m)
    (hdegS : hsDegLt (hsSub G' (insert v S)) Finset.univ
      (Finset.univ : Finset (Fin k))) :
    ∃ f₁ : V' → Fin k, hsProper (hsSub G' (insert v S)) Finset.univ f₁ ∧
      hsEquitable Finset.univ Finset.univ f₁ m := by
  have hmapsS : hsMaps Finset.univ Finset.univ f :=
    fun u _ => Finset.mem_univ _
  have hcardk : (Finset.univ : Finset (Fin k)).card = k := by
    rw [Finset.card_univ, Fintype.card_fin]
  have hdegv := hdegS v (Finset.mem_univ v)
  rw [hcardk] at hdegv
  have himg : ((hsNbr (hsSub G' (insert v S)) Finset.univ v).image f).card <
      (Finset.univ : Finset (Fin k)).card := by
    rw [hcardk]
    exact lt_of_le_of_lt Finset.card_image_le hdegv
  obtain ⟨β, hβU, hβmiss⟩ := Finset.exists_mem_notMem_of_card_lt_card himg
  have hmiss : ∀ w ∈ hsNbr (hsSub G' (insert v S)) Finset.univ v, f w ≠ β := by
    intro w hw hcon
    exact hβmiss (Finset.mem_image.mpr ⟨w, hw, hcon⟩)
  have eβ : Function.update f v β v = β := Function.update_self v β f
  have ef : ∀ x, x ≠ v → Function.update f v β x = f x :=
    fun x hx => Function.update_of_ne hx β f
  have hproper₁ : hsProper (hsSub G' (insert v S)) Finset.univ
      (Function.update f v β) := by
    intro a _ b _ hadj hcon
    obtain ⟨hadjG, haS, hbS⟩ := (hsMem_sub G' (insert v S) a b).mp hadj
    by_cases hav : a = v
    · rw [hav] at hcon hadjG
      rw [eβ] at hcon
      by_cases hbv : b = v
      · rw [hbv] at hadjG
        exact absurd hadjG G'.irrefl
      · rw [ef b hbv] at hcon
        have hbN : b ∈ hsNbr (hsSub G' (insert v S)) Finset.univ v :=
          (hsMem_nbr _ _ _ _).mpr ⟨Finset.mem_univ b,
            (hsMem_sub G' (insert v S) v b).mpr
              ⟨hadjG, Finset.mem_insert_self v S, hbS⟩⟩
        exact hmiss b hbN hcon.symm
    · by_cases hbv : b = v
      · rw [hbv] at hcon hadjG hbS
        rw [ef a hav, eβ] at hcon
        have haN : a ∈ hsNbr (hsSub G' (insert v S)) Finset.univ v :=
          (hsMem_nbr _ _ _ _).mpr ⟨Finset.mem_univ a,
            (hsMem_sub G' (insert v S) v a).mpr
              ⟨G'.adj_symm hadjG, hbS, haS⟩⟩
        exact hmiss a haN hcon
      · rw [ef a hav, ef b hbv] at hcon
        have haS' : a ∈ S := (Finset.mem_insert.mp haS).resolve_left hav
        have hbS' : b ∈ S := (Finset.mem_insert.mp hbS).resolve_left hbv
        have hedge : (hsSub G' S).Adj a b :=
          (hsMem_sub G' S a b).mpr ⟨hadjG, haS', hbS'⟩
        exact hfproper a (Finset.mem_univ a) b (Finset.mem_univ b) hedge hcon
  by_cases hβfv : β = f v
  · subst hβfv
    have hff : Function.update f v (f v) = f := by
      funext u
      by_cases hux : u = v
      · rw [hux]
        exact Function.update_self v (f v) f
      · exact Function.update_of_ne hux (f v) f
    have hproper₁' : hsProper (hsSub G' (insert v S)) Finset.univ f :=
      hff ▸ hproper₁
    exact ⟨f, hproper₁', hfeq⟩
  · have hnoS : ∀ u ∈ Finset.univ, f u = β →
        ¬ (hsSub G' S).Adj v u := by
      intro u _ _ hadj
      obtain ⟨-, hvS', -⟩ := (hsMem_sub G' S v u).mp hadj
      exact hvS hvS'
    obtain ⟨-, -, -, hid⟩ := hsMove (hsSub G' S) Finset.univ Finset.univ f
      hmapsS hfproper v (Finset.mem_univ v) β (Finset.mem_univ β) hnoS
    have hnearly : hsNearly Finset.univ Finset.univ (Function.update f v β)
        m (f v) β := by
      refine ⟨Finset.mem_univ _, Finset.mem_univ _, ?_, ?_, ?_, ?_⟩
      · exact fun h => hβfv h.symm
      · have e := hid (f v)
        have e1 : (if f v = f v then (1 : ℕ) else 0) = 1 := ite_eq_left rfl
        have e2 : (if f v = β then (1 : ℕ) else 0) = 0 :=
          ite_eq_right (fun h => hβfv h.symm)
        have hdm := hfeq (f v) (Finset.mem_univ _)
        omega
      · have e := hid β
        have e1 : (if β = f v then (1 : ℕ) else 0) = 0 := ite_eq_right hβfv
        have e2 : (if β = β then (1 : ℕ) else 0) = 1 := ite_eq_left rfl
        have hdm := hfeq β (Finset.mem_univ _)
        omega
      · intro c _ hcα hcβ
        have e := hid c
        have e1 : (if c = f v then (1 : ℕ) else 0) = 0 := ite_eq_right hcα
        have e2 : (if c = β then (1 : ℕ) else 0) = 0 := ite_eq_right hcβ
        have hdm := hfeq c (Finset.mem_univ _)
        omega
    have hmaps₁ : hsMaps Finset.univ Finset.univ (Function.update f v β) :=
      fun u _ => Finset.mem_univ _
    obtain ⟨g, hmapsg, hproperg, heqg⟩ :=
      hsMain (hsSub G' (insert v S)) Finset.univ.card Finset.univ Finset.univ
        (Function.update f v β) m (f v) β rfl hmaps₁ hproper₁ hdegS hnearly
    exact ⟨g, hproperg, heqg⟩

/-- Growing an equitable proper coloring one vertex at a time. -/
private theorem hsGrow {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : G.maxDegree < k)
    (m p : ℕ)
    (hpm : k * m = Fintype.card V + p) (hp1 : 1 ≤ p) (hpk : p ≤ k) :
    ∀ S : Finset (V ⊕ Fin p),
      ∃ f : (V ⊕ Fin p) → Fin k, hsProper (hsSub (G ⊕g (⊤ : SimpleGraph (Fin p))) S) Finset.univ f ∧
        hsEquitable Finset.univ Finset.univ f m := by
  have hcard : Fintype.card (V ⊕ Fin p) = k * m := by
    rw [Fintype.card_sum, Fintype.card_fin]
    omega
  have hdegS : ∀ S : Finset (V ⊕ Fin p),
      hsDegLt (hsSub (G ⊕g (⊤ : SimpleGraph (Fin p))) S) Finset.univ
        (Finset.univ : Finset (Fin k)) :=
    fun S => hsSub_deg_sum G k hk p hp1 hpk S
  intro S
  induction S using Finset.induction with
  | empty => exact hsGrowBase (G ⊕g (⊤ : SimpleGraph (Fin p))) k m hcard
  | insert x s hx ih =>
    obtain ⟨f, hfproper, hfeq⟩ := ih
    exact hsGrowStep (G ⊕g (⊤ : SimpleGraph (Fin p))) k m s x hx f hfproper hfeq (hdegS _)

/-- Assembly: each class contains at most one padded vertex. -/
private theorem hsClassB_le1 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k p : ℕ)
    (f : V ⊕ Fin p → Fin k)
    (hfproper : hsProper (hsSub (G ⊕g (⊤ : SimpleGraph (Fin p))) Finset.univ)
      Finset.univ f)
    (i : Fin k) :
    (Finset.univ.filter (fun j : Fin p => f (Sum.inr j) = i)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro j₁ hj₁ j₂ hj₂
  have e1 : f (Sum.inr j₁) = i := (Finset.mem_filter.mp hj₁).2
  have e2 : f (Sum.inr j₂) = i := (Finset.mem_filter.mp hj₂).2
  by_contra hne
  have hedge : (hsSub (G ⊕g (⊤ : SimpleGraph (Fin p))) Finset.univ).Adj
      (Sum.inr j₁) (Sum.inr j₂) :=
    (hsMem_sub _ _ _ _).mpr
      ⟨SimpleGraph.sum_adj_inr.mpr ((SimpleGraph.top_adj _ _).mpr hne),
        Finset.mem_univ _, Finset.mem_univ _⟩
  exact hfproper _ (Finset.mem_univ _) _ (Finset.mem_univ _) hedge
    (e1.trans e2.symm)

/-- Assembly: each big class splits over the two sides of the sum. -/
private theorem hsSplit_cls {V : Type*} [Fintype V] [DecidableEq V]
    (k p : ℕ) (f : V ⊕ Fin p → Fin k) (i : Fin k) :
    hsCls Finset.univ f i =
      (Finset.univ.filter (fun v : V => f (Sum.inl v) = i)).image
        (Sum.inl : V → V ⊕ Fin p) ∪
      (Finset.univ.filter (fun j : Fin p => f (Sum.inr j) = i)).image
        (Sum.inr : Fin p → V ⊕ Fin p) := by
  ext x
  cases x with
  | inl v =>
    constructor
    · intro hx
      obtain ⟨-, hfx⟩ := (hsMem_cls _ _ _ _).mp hx
      apply Finset.mem_union.mpr
      exact Or.inl (Finset.mem_image.mpr ⟨v,
        Finset.mem_filter.mpr ⟨Finset.mem_univ v, hfx⟩, rfl⟩)
    · intro hx
      rw [Finset.mem_union] at hx
      rcases hx with hx | hx
      · obtain ⟨a, ha, hcon⟩ := Finset.mem_image.mp hx
        obtain ⟨-, hfa⟩ := Finset.mem_filter.mp ha
        have hav : a = v := Sum.inl_injective hcon
        rw [hsMem_cls]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [← hav]
        exact hfa
      · obtain ⟨j, -, hcon⟩ := Finset.mem_image.mp hx
        cases hcon
  | inr j =>
    constructor
    · intro hx
      obtain ⟨-, hfx⟩ := (hsMem_cls _ _ _ _).mp hx
      apply Finset.mem_union.mpr
      exact Or.inr (Finset.mem_image.mpr ⟨j,
        Finset.mem_filter.mpr ⟨Finset.mem_univ j, hfx⟩, rfl⟩)
    · intro hx
      rw [Finset.mem_union] at hx
      rcases hx with hx | hx
      · obtain ⟨a, -, hcon⟩ := Finset.mem_image.mp hx
        cases hcon
      · obtain ⟨b, hb, hcon⟩ := Finset.mem_image.mp hx
        obtain ⟨-, hfb⟩ := Finset.mem_filter.mp hb
        have hjb : b = j := Sum.inr_injective hcon
        rw [hsMem_cls]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [← hjb]
        exact hfb

/-- Assembly: the two sides' class sizes add to `m`. -/
private theorem hsSplit_card {V : Type*} [Fintype V] [DecidableEq V]
    (k p m : ℕ) (f : V ⊕ Fin p → Fin k) (i : Fin k)
    (hfeq : (hsCls Finset.univ f i).card = m) :
    (Finset.univ.filter (fun v : V => f (Sum.inl v) = i)).card +
      (Finset.univ.filter (fun j : Fin p => f (Sum.inr j) = i)).card = m := by
  have hdisj : Disjoint
      ((Finset.univ.filter (fun v : V => f (Sum.inl v) = i)).image
        (Sum.inl : V → V ⊕ Fin p))
      ((Finset.univ.filter (fun j : Fin p => f (Sum.inr j) = i)).image
        (Sum.inr : Fin p → V ⊕ Fin p)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨a, -, h1⟩ := Finset.mem_image.mp hx1
    obtain ⟨j, -, h2⟩ := Finset.mem_image.mp hx2
    rw [← h1] at h2
    cases h2
  rw [← hfeq, hsSplit_cls k p f i, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ Sum.inl_injective,
    Finset.card_image_of_injective _ Sum.inr_injective]

/-- Assembly: `ncard` of a pulled-back class is a `Finset` card. -/
private theorem hsNcard_eq {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k p : ℕ) (C : G.Coloring (Fin k))
    (f : V ⊕ Fin p → Fin k) (hCf : ∀ v, C v = f (Sum.inl v))
    (i : Fin k) :
    (C.colorClass i).ncard =
      (Finset.univ.filter (fun v : V => f (Sum.inl v) = i)).card := by
  have hcoe : C.colorClass i =
      ↑(Finset.univ.filter fun v : V => f (Sum.inl v) = i) := by
    ext v
    constructor
    · intro hv
      have hvv : C v = i := hv
      rw [hCf v] at hvv
      exact Finset.mem_coe.mpr
        (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hvv⟩)
    · intro hv
      obtain ⟨-, hvv⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hv)
      have hCv : C v = i := by
        rw [hCf v]
        exact hvv
      exact hCv
  rw [hcoe, Set.ncard_coe_finset]

/-- **Equitable coloring with more colors than the maximum degree.** Let $G$ be a simple graph on a
finite vertex set with maximum degree $\Delta(G)$, and let $k$ be a natural number with
$\Delta(G) < k$. Then $G$ has a proper coloring with the $k$ colors $0, 1, \dots, k-1$ that is
equitable: for any two colors $i$ and $j$, the number of vertices of color $i$ is at most one more
than the number of vertices of color $j$. -/
public theorem exists_equitable_coloring_of_maxDegree_lt
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : G.maxDegree < k) :
    ∃ C : G.Coloring (Fin k),
      ∀ i j : Fin k, (C.colorClass i).ncard ≤ (C.colorClass j).ncard + 1 := by
  classical
  have hk1 : 0 < k := by
    have h0 := Nat.zero_le G.maxDegree
    omega
  obtain ⟨m, p, hm, hpm, hp1, hpk⟩ := hsPad_arith (Fintype.card V) k hk1
  obtain ⟨f, hfproper, hfeq⟩ :=
    hsGrow G k hk m p hpm hp1 hpk Finset.univ
  have hCvalid : ∀ {v w : V}, G.Adj v w →
      (fun v => f (Sum.inl v)) v ≠ (fun v => f (Sum.inl v)) w := by
    intro v w hadj hcon
    have hedge : (hsSub (G ⊕g (⊤ : SimpleGraph (Fin p))) Finset.univ).Adj
        (Sum.inl v) (Sum.inl w) :=
      (hsMem_sub _ _ _ _).mpr
        ⟨SimpleGraph.sum_adj_inl.mpr hadj, Finset.mem_univ _,
          Finset.mem_univ _⟩
    exact hfproper _ (Finset.mem_univ _) _ (Finset.mem_univ _) hedge hcon
  set C : G.Coloring (Fin k) :=
    SimpleGraph.Coloring.mk (fun v => f (Sum.inl v)) hCvalid
  have hCf : ∀ v, C v = f (Sum.inl v) := fun v => rfl
  refine ⟨C, ?_⟩
  intro i j
  rw [hsNcard_eq G k p C f hCf i, hsNcard_eq G k p C f hCf j]
  have h1 := hsSplit_card k p m f i (hfeq i (Finset.mem_univ i))
  have h2 := hsSplit_card k p m f j (hfeq j (Finset.mem_univ j))
  have h3 := hsClassB_le1 G k p f hfproper j
  omega

/--
**Hajnal–Szemerédi theorem.** Let $G$ be a simple graph on a finite vertex set with maximum degree
$\Delta(G)$, and let $k$ be a natural number with $\Delta(G) < k$. Then $G$ has a proper coloring
with the $k$ colors $0, 1, \dots, k-1$ that is equitable: for any two colors $i$ and $j$, the
number of vertices of color $i$ is at most one more than the number of vertices of color $j$.

Proves `Wanted` entry `hajnal_szemeredi_equitable_coloring`.

Source: A. Hajnal and E. Szemerédi, "Proof of a conjecture of P. Erdős", Combinatorial Theory and
Its Applications II, Colloq. Math. Soc. János Bolyai 4 (1970), 601-623.
-/
public theorem hajnal_szemeredi_equitable_coloring
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : G.maxDegree < k) :
    ∃ C : G.Coloring (Fin k),
      ∀ i j : Fin k, (C.colorClass i).ncard ≤ (C.colorClass j).ncard + 1 :=
  exists_equitable_coloring_of_maxDegree_lt G k hk

end MathlibExt.Combinatorics.SimpleGraph.HajnalSzemerediWanted
