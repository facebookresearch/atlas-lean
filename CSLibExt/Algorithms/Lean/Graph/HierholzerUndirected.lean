/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.Hierholzer
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Logic.Relation

/-!
# Euler circuits in undirected multigraphs by Hierholzer's algorithm

Hierholzer's algorithm for undirected multigraphs (C. Hierholzer, 1873; Euler's theorem: a
connected multigraph has an Euler circuit iff every vertex has even degree, and an Euler path
between `s ≠ t` iff exactly `s` and `t` have odd degree). The directed version is
`Hierholzer.lean`; here an edge can be traversed in either direction, and traversing it removes it
for both endpoints.

The multigraph is an edge list `E : List (V × V)`, each pair one undirected edge (repeated pairs
are parallel edges, `(v, v)` is a loop). `udeg E x` is the degree of `x` (a loop counts twice).
From `v`, `uvisit` takes the first remaining edge at `v`, removes it, recurses at its other
endpoint, and then continues at `v`; when no edge is left at `v` it emits `v`.

* `IsUEulerPath E s t W`: `W` starts at `s`, ends at `t`, and its steps, as unordered pairs, are a
  permutation of the edges.
* `uhierholzer_isUEulerPath`: if exactly `s` and `t` have odd degree (`EvenExcept E s t`; every
  degree is even when `s = t`) and every edge starts at a vertex reachable from `s`
  (`UReach`), `uhierholzer E s` is an Euler path from `s` to `t`; `uhierholzer_isUEulerCircuit`
  is the case `s = t`.
* `uhierholzer_trail`: without the reachability hypothesis, the result is still a walk from `s` to
  `t` whose steps are a sub-multiset of the edges.

The proof follows `Hierholzer.lean`: a call at `v` on a remaining multigraph whose odd-degree
vertices are exactly `v` and `t` (none when `v = t`) emits a walk from `v` to `t` and leaves a
remainder of even degrees in which the walk's vertices have no edges (`uvisit_spec`).

## Cost model

One unit per edge traversal (removing an edge from the remaining list). Finding the first edge at
`v` and emitting a vertex are free, as with per-vertex incidence lists in which both copies of an
edge are removed together. A run whose edges are all reachable costs exactly `|E|`
(`uhierholzer_time`). The executable state is a list, which models those incidence lists but whose
own scans are not constant time, so the bound is in the model.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Hierholzer

open Cslib.Algorithms.Lean TimeM

universe u

variable {V : Type u} [DecidableEq V]

/-- An ordered pair as an unordered edge. -/
def usym (e : V × V) : Sym2 V := s(e.1, e.2)

/-- The degree of `x` in the edge list `R` (a loop counts twice). -/
def udeg (R : List (V × V)) (x : V) : ℕ := (R.map Prod.fst).count x + (R.map Prod.snd).count x

/-- Every degree is even, except at `v` and `t` (when `v ≠ t`). -/
def EvenExcept (R : List (V × V)) (v t : V) : Prop :=
  ∀ x, (udeg R x + (if x = v then 1 else 0) + (if x = t then 1 else 0)) % 2 = 0

/-- `x` is reachable from `s` through the edges of `E`, in either direction. -/
def UReach (E : List (V × V)) (s x : V) : Prop :=
  Relation.ReflTransGen (fun a b => (a, b) ∈ E ∨ (b, a) ∈ E) s x

/-- `W` is an Euler path of `E` from `s` to `t`: its steps, as unordered pairs, are exactly the
edges of `E`, each traversed once in one direction. -/
def IsUEulerPath (E : List (V × V)) (s t : V) (W : List V) : Prop :=
  W.head? = some s ∧ W.getLast? = some t ∧ ((walkEdges W).map usym).Perm (E.map usym)

instance (E : List (V × V)) (s t : V) (W : List V) : Decidable (IsUEulerPath E s t W) := by
  unfold IsUEulerPath; infer_instance

instance [Fintype V] (R : List (V × V)) (v t : V) : Decidable (EvenExcept R v t) := by
  unfold EvenExcept; infer_instance

/-- The other endpoint of the edge `e` at `v`. -/
def otherEnd (e : V × V) (v : V) : V := if e.1 = v then e.2 else e.1

/-- Undirected Hierholzer recursion with fuel: from `v`, take the first remaining edge at `v`,
remove it, recurse at its other endpoint, then continue at `v`; emit `v` when no edge is left at
`v`. Returns the emitted vertices prepended to `acc` and the remaining edges. -/
def uvisit : ℕ → V → List (V × V) → List V → TimeM ℕ (List V × List (V × V))
  | 0, _, R, acc => pure (acc, R)
  | fuel + 1, v, R, acc =>
      match R.find? (fun e => e.1 = v ∨ e.2 = v) with
      | none => pure (v :: acc, R)
      | some e => do
          ✓
          let r ← uvisit fuel (otherEnd e v) (R.erase e) acc
          uvisit fuel v r.2 r.1

/-- Hierholzer's algorithm on an undirected edge list, from `s`. -/
def uhierholzer (E : List (V × V)) (s : V) : TimeM ℕ (List V) := do
  let r ← uvisit (E.length + 1) s E []
  pure r.1

/-! ## Degrees -/

theorem udeg_erase {R : List (V × V)} {e : V × V} (he : e ∈ R) (x : V) :
    udeg R x = udeg (R.erase e) x + (if x = e.1 then 1 else 0) + (if x = e.2 then 1 else 0) := by
  have hp := List.perm_cons_erase he
  have h1 := (hp.map Prod.fst).count_eq x
  have h2 := (hp.map Prod.snd).count_eq x
  simp only [List.map_cons, List.count_cons, beq_iff_eq, @eq_comm _ e.1 x, @eq_comm _ e.2 x]
    at h1 h2
  unfold udeg
  rw [h1, h2]
  omega

theorem udeg_le_of_sublist {R R' : List (V × V)} (h : R'.Sublist R) (x : V) :
    udeg R' x ≤ udeg R x :=
  Nat.add_le_add ((h.map _).count_le x) ((h.map _).count_le x)

theorem udeg_pos_of_mem {R : List (V × V)} {e : V × V} (he : e ∈ R) :
    0 < udeg R e.1 ∧ 0 < udeg R e.2 := by
  have h1 : 0 < (R.map Prod.fst).count e.1 := List.count_pos_iff.2 (List.mem_map_of_mem he)
  have h2 : 0 < (R.map Prod.snd).count e.2 := List.count_pos_iff.2 (List.mem_map_of_mem he)
  unfold udeg; omega

/-- An edge at `v` joins `v` and its other endpoint. -/
theorem usym_eq_otherEnd {e : V × V} {v : V} (h : e.1 = v ∨ e.2 = v) :
    usym e = s(v, otherEnd e v) := by
  simp only [usym, otherEnd]
  split_ifs with h1
  · rw [h1]
  · rcases h with h | h
    · exact absurd h h1
    · rw [h, Sym2.eq_swap]

/-! ## The recursion -/

private theorem uvisit_none {fuel : ℕ} {v : V} {R : List (V × V)} (acc : List V)
    (h : R.find? (fun e => e.1 = v ∨ e.2 = v) = none) :
    uvisit (fuel + 1) v R acc = pure (v :: acc, R) := by
  rw [uvisit, h]

private theorem uvisit_some {fuel : ℕ} {v : V} {R : List (V × V)} {e : V × V} (acc : List V)
    (h : R.find? (fun e => e.1 = v ∨ e.2 = v) = some e) :
    (uvisit (fuel + 1) v R acc).ret =
        (uvisit fuel v (uvisit fuel (otherEnd e v) (R.erase e) acc).ret.2
          (uvisit fuel (otherEnd e v) (R.erase e) acc).ret.1).ret ∧
      (uvisit (fuel + 1) v R acc).time = 1 + (uvisit fuel (otherEnd e v) (R.erase e) acc).time +
        (uvisit fuel v (uvisit fuel (otherEnd e v) (R.erase e) acc).ret.2
          (uvisit fuel (otherEnd e v) (R.erase e) acc).ret.1).time := by
  rw [uvisit, h]
  constructor
  · simp
  · simp; omega

/-- The contract of `uvisit`: given more fuel than remaining edges and a remainder whose
odd-degree vertices are exactly `v` and `t` (none when `v = t`), the call emits a walk `W` from
`v` to `t` in front of `acc`, removes exactly its steps (as unordered pairs), leaves a remainder of
even degrees, a sublist of `R`, in which `W`'s vertices have no edges, and costs one unit per
removed edge. -/
theorem uvisit_spec : ∀ (fuel : ℕ) (v t : V) (R : List (V × V)) (acc : List V),
    R.length < fuel → EvenExcept R v t →
    ∃ W, (uvisit fuel v R acc).ret.1 = W ++ acc ∧ W.head? = some v ∧ W.getLast? = some t ∧
      (R.map usym).Perm ((walkEdges W).map usym ++ (uvisit fuel v R acc).ret.2.map usym) ∧
      (∀ x, udeg (uvisit fuel v R acc).ret.2 x % 2 = 0) ∧
      (∀ x ∈ W, udeg (uvisit fuel v R acc).ret.2 x = 0) ∧
      (uvisit fuel v R acc).ret.2.Sublist R ∧
      (uvisit fuel v R acc).time + (uvisit fuel v R acc).ret.2.length = R.length
  | 0, _, _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | fuel + 1, v, t, R, acc, hlen, hpar => by
      cases hf : R.find? (fun e => e.1 = v ∨ e.2 = v) with
      | none =>
          -- no edge at `v`, so `v = t`
          have hdeg : udeg R v = 0 := by
            have hno : ∀ e ∈ R, ¬ (e.1 = v ∨ e.2 = v) := fun e he h => by
              simpa [h] using List.find?_eq_none.1 hf e he
            unfold udeg
            rw [Nat.add_eq_zero_iff, List.count_eq_zero, List.count_eq_zero]
            constructor
            · intro hm; obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm; exact hno e he (Or.inl rfl)
            · intro hm; obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm; exact hno e he (Or.inr rfl)
          have hvt : v = t := by
            have := hpar v
            rw [hdeg] at this
            by_contra hne
            simp [hne] at this
          subst hvt
          rw [uvisit_none acc hf]
          refine ⟨[v], rfl, rfl, rfl, by simp [walkEdges], fun x => ?_, ?_, List.Sublist.refl _,
            by simp⟩
          · have := hpar x
            simp only [TimeM.ret_pure]
            split_ifs at this <;> omega
          · intro x hx
            rw [List.mem_singleton] at hx
            subst hx
            simpa using hdeg
      | some e =>
          have he : e ∈ R := List.mem_of_find?_eq_some hf
          have hev : e.1 = v ∨ e.2 = v := by simpa using List.find?_some hf
          set w := otherEnd e v with hw
          -- the edge `e` joins `v` and `w`
          have hsym : usym e = s(v, w) := usym_eq_otherEnd hev
          have hind : ∀ x, (if x = e.1 then 1 else 0) + (if x = e.2 then 1 else 0) =
              (if x = v then 1 else 0) + (if x = w then 1 else 0) := by
            intro x
            rcases hev with h | h
            · have hw' : w = e.2 := by simp [hw, otherEnd, h]
              rw [hw', h]
            · by_cases h1 : e.1 = v
              · have hw' : w = e.2 := by simp [hw, otherEnd, h1]
                rw [hw', h1]
              · have hw' : w = e.1 := by simp [hw, otherEnd, h1]
                rw [hw', h]; omega
          set R₁ := R.erase e with hR₁
          have hlenR₁ : R₁.length = R.length - 1 := by rw [hR₁]; exact List.length_erase_of_mem he
          have hRpos := List.length_pos_of_mem he
          have hlen₁ : R₁.length < fuel := by omega
          have hpar₁ : EvenExcept R₁ w t := by
            intro x
            have h1 := hpar x
            have h2 := udeg_erase he x
            have h3 := hind x
            rw [← hR₁] at h2
            split_ifs at h1 h2 h3 ⊢ <;> omega
          obtain ⟨W₁, hW₁, hW₁h, hW₁l, hp₁, hpar₂, hstuck₁, hsub₁, htime₁⟩ :=
            uvisit_spec fuel w t R₁ acc hlen₁ hpar₁
          set r₁ := (uvisit fuel w R₁ acc).ret with hr₁
          have hlen₂ : r₁.2.length < fuel := lt_of_le_of_lt hsub₁.length_le hlen₁
          have hpar₂' : EvenExcept r₁.2 v v := by
            intro x
            have := hpar₂ x
            split_ifs <;> omega
          obtain ⟨W₂, hW₂, hW₂h, hW₂l, hp₂, hpar₃, hstuck₂, hsub₂, htime₂⟩ :=
            uvisit_spec fuel v v r₁.2 r₁.1 hlen₂ hpar₂'
          obtain ⟨hret, htime⟩ := uvisit_some (fuel := fuel) acc hf
          rw [← hw, ← hR₁, ← hr₁] at hret htime
          refine ⟨W₂ ++ W₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hret, hW₂, hW₁, List.append_assoc]
          · cases W₂ with
            | nil => simp at hW₂h
            | cons y W₂ => simpa using hW₂h
          · rw [List.getLast?_append_of_ne_nil _ (by rintro rfl; simp at hW₁h)]; exact hW₁l
          · rw [hret, walkEdges_append hW₂l hW₁h]
            have hp₀ : (R.map usym).Perm (usym e :: R₁.map usym) := by
              have := (List.perm_cons_erase he).map usym
              simpa [hR₁] using this
            refine hp₀.trans ?_
            rw [hsym]
            have := (((hp₁.trans (hp₂.append_left _)).cons s(v, w)).trans
              (perm_splice s(v, w) ((walkEdges W₁).map usym) ((walkEdges W₂).map usym)
                ((uvisit fuel v r₁.2 r₁.1).ret.2.map usym)))
            simpa [List.map_append, List.map_cons, usym] using this
          · rw [hret]; exact hpar₃
          · intro x hx
            rw [hret]
            rcases List.mem_append.1 hx with hx | hx
            · exact hstuck₂ x hx
            · have := udeg_le_of_sublist hsub₂ x
              rw [hstuck₁ x hx] at this
              omega
          · rw [hret]
            exact hsub₂.trans (hsub₁.trans (List.erase_sublist))
          · rw [hret, htime]
            omega

/-! ## Correctness -/

omit [DecidableEq V] in
theorem mem_of_mem_walkEdges {W : List V} {a b : V} (h : (a, b) ∈ walkEdges W) :
    a ∈ W ∧ b ∈ W :=
  ⟨List.of_mem_zip h |>.1, List.mem_of_mem_tail (List.of_mem_zip h).2⟩

private theorem uhierholzer_facts (E : List (V × V)) (s t : V) (hpar : EvenExcept E s t) :
    ∃ R' : List (V × V), (uhierholzer E s).ret.head? = some s ∧
      (uhierholzer E s).ret.getLast? = some t ∧
      (E.map usym).Perm ((walkEdges (uhierholzer E s).ret).map usym ++ R'.map usym) ∧
      (∀ x ∈ (uhierholzer E s).ret, udeg R' x = 0) ∧ R'.Sublist E ∧
      (uhierholzer E s).time + R'.length = E.length := by
  obtain ⟨W, hW, hh, hl, hp, -, hstuck, hsub, htime⟩ :=
    uvisit_spec (E.length + 1) s t E [] (Nat.lt_succ_self _) hpar
  rw [List.append_nil] at hW
  have hret : (uhierholzer E s).ret = W := by simp [uhierholzer, hW]
  have htime' : (uhierholzer E s).time = (uvisit (E.length + 1) s E []).time := by
    simp [uhierholzer]
  exact ⟨_, by rw [hret]; exact hh, by rw [hret]; exact hl, by rw [hret]; exact hp,
    by rw [hret]; exact hstuck, hsub, by rw [htime']; exact htime⟩

/-- When exactly `s` and `t` have odd degree (none when `s = t`), the result is a walk from `s`
to `t` whose steps, as unordered pairs, are a sub-multiset of the edges: no edge is traversed
twice. -/
theorem uhierholzer_trail (E : List (V × V)) (s t : V) (hpar : EvenExcept E s t) :
    (uhierholzer E s).ret.head? = some s ∧ (uhierholzer E s).ret.getLast? = some t ∧
      ∃ rest, (E.map usym).Perm ((walkEdges (uhierholzer E s).ret).map usym ++ rest) := by
  obtain ⟨R', hh, hl, hp, -⟩ := uhierholzer_facts E s t hpar
  exact ⟨hh, hl, _, hp⟩

/-- A walk from `s` that removes its steps from `E` and leaves no edge at its own vertices
contains every vertex reachable from `s`. -/
private theorem mem_of_uReach {E R' : List (V × V)} {W : List V} {s : V}
    (hh : W.head? = some s)
    (hp : (E.map usym).Perm ((walkEdges W).map usym ++ R'.map usym))
    (hstuck : ∀ x ∈ W, udeg R' x = 0) : ∀ x, UReach E s x → x ∈ W := by
  intro x hx
  induction hx with
  | refl => exact List.mem_of_mem_head? hh
  | @tail a b _ hab ih =>
      have hmem : s(a, b) ∈ E.map usym := by
        rcases hab with h | h
        · exact List.mem_map.2 ⟨(a, b), h, rfl⟩
        · exact List.mem_map.2 ⟨(b, a), h, Sym2.eq_swap⟩
      rcases List.mem_append.1 (hp.subset hmem) with h | h
      · obtain ⟨⟨p, q⟩, hpq, he⟩ := List.mem_map.1 h
        have hpW := mem_of_mem_walkEdges hpq
        simp only [usym, Sym2.eq_iff] at he
        rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hpW.2
        · exact hpW.1
      · obtain ⟨⟨p, q⟩, hpq, he⟩ := List.mem_map.1 h
        exfalso
        have h0 := hstuck a ih
        have hpos := udeg_pos_of_mem hpq
        simp only [usym, Sym2.eq_iff] at he
        rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp only at hpos; omega
        · simp only at hpos; omega

/-- **Euler paths.** If exactly `s` and `t` have odd degree (none when `s = t`) and every edge
starts at a vertex reachable from `s`, the result is an Euler path from `s` to `t`. -/
theorem uhierholzer_isUEulerPath (E : List (V × V)) (s t : V) (hpar : EvenExcept E s t)
    (hreach : ∀ e ∈ E, UReach E s e.1) : IsUEulerPath E s t (uhierholzer E s).ret := by
  obtain ⟨R', hh, hl, hp, hstuck, hsub, -⟩ := uhierholzer_facts E s t hpar
  have hR' : R' = [] := by
    rcases R' with _ | ⟨e', R''⟩
    · rfl
    · exfalso
      have he' : e' ∈ E := hsub.subset List.mem_cons_self
      have h0 := hstuck e'.1 (mem_of_uReach hh hp hstuck e'.1 (hreach e' he'))
      have := (udeg_pos_of_mem (List.mem_cons_self (a := e') (l := R''))).1
      omega
  subst hR'
  refine ⟨hh, hl, ?_⟩
  simpa using hp.symm

/-- **Euler circuits.** If every degree is even and every edge starts at a vertex reachable from
`s`, the result is an Euler circuit from `s`. -/
theorem uhierholzer_isUEulerCircuit (E : List (V × V)) (s : V) (hpar : ∀ x, udeg E x % 2 = 0)
    (hreach : ∀ e ∈ E, UReach E s e.1) : IsUEulerPath E s s (uhierholzer E s).ret :=
  uhierholzer_isUEulerPath E s s (fun x => by have := hpar x; split_ifs <;> omega) hreach

/-- **Cost.** One unit per removed edge; when every edge is reachable, exactly `|E|`. -/
theorem uhierholzer_time (E : List (V × V)) (s t : V) (hpar : EvenExcept E s t)
    (hreach : ∀ e ∈ E, UReach E s e.1) : (uhierholzer E s).time = E.length := by
  obtain ⟨R', hh, hl, hp, hstuck, hsub, htime⟩ := uhierholzer_facts E s t hpar
  have hR' : R' = [] := by
    rcases R' with _ | ⟨e', R''⟩
    · rfl
    · exfalso
      have he' : e' ∈ E := hsub.subset List.mem_cons_self
      have h0 := hstuck e'.1 (mem_of_uReach hh hp hstuck e'.1 (hreach e' he'))
      have := (udeg_pos_of_mem (List.mem_cons_self (a := e') (l := R''))).1
      omega
  subst hR'
  simpa using htime

/-! ## The converse: degrees of an Euler path -/

/-- The number of endpoints of an unordered edge equal to `x` (`2` for the loop `s(x, x)`). -/
def endsAt (x : V) : Sym2 V → ℕ :=
  Sym2.lift ⟨fun a b => (if x = a then 1 else 0) + (if x = b then 1 else 0),
    fun _ _ => Nat.add_comm _ _⟩

theorem endsAt_usym (x : V) (e : V × V) :
    endsAt x (usym e) = (if x = e.1 then 1 else 0) + (if x = e.2 then 1 else 0) := rfl

theorem udeg_eq_sum (R : List (V × V)) (x : V) :
    udeg R x = ((R.map usym).map (endsAt x)).sum := by
  induction R with
  | nil => simp [udeg]
  | cons e R ih =>
      simp only [udeg] at ih ⊢
      simp only [List.map_cons, List.count_cons, beq_iff_eq, List.sum_cons, endsAt_usym,
        @eq_comm _ e.1 x, @eq_comm _ e.2 x]
      omega

/-- Degrees depend only on the edges as unordered pairs. -/
theorem udeg_eq_of_perm {A B : List (V × V)} (h : (A.map usym).Perm (B.map usym)) (x : V) :
    udeg A x = udeg B x := by
  rw [udeg_eq_sum, udeg_eq_sum]
  exact (h.map _).sum_eq

/-- In the steps of a walk from `s` to `t`, every degree is even except at `s` and `t`. -/
theorem evenExcept_walkEdges : ∀ (W : List V) (s t : V), W.head? = some s →
    W.getLast? = some t → EvenExcept (walkEdges W) s t
  | [], _, _, h, _, _ => by simp at h
  | [a], s, t, hs, ht, x => by
      simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hs ht
      subst hs ht
      simp only [walkEdges, List.tail_cons, List.zip_nil_right, udeg, List.map_nil,
        List.count_nil]
      split_ifs <;> omega
  | a :: b :: W, s, t, hs, ht, x => by
      simp only [List.head?_cons, Option.some.injEq] at hs
      subst hs
      rw [List.getLast?_cons_cons] at ht
      have ih := evenExcept_walkEdges (b :: W) b t rfl ht x
      have e : walkEdges (a :: b :: W) = (a, b) :: walkEdges (b :: W) := rfl
      rw [e]
      simp only [udeg, List.map_cons, List.count_cons, beq_iff_eq, @eq_comm _ a x,
        @eq_comm _ b x] at ih ⊢
      split_ifs at ih ⊢ <;> omega

/-- An Euler path from `s` to `t` forces the degree condition: exactly `s` and `t` have odd degree
(none when `s = t`). -/
theorem evenExcept_of_isUEulerPath {E : List (V × V)} {s t : V} {W : List V}
    (h : IsUEulerPath E s t W) : EvenExcept E s t := by
  intro x
  rw [← udeg_eq_of_perm h.2.2 x]
  exact evenExcept_walkEdges W s t h.1 h.2.1 x

/-- **Euler's theorem**, algorithmic form: when every edge starts at a vertex reachable from `s`,
an Euler path from `s` to `t` exists iff exactly `s` and `t` have odd degree (every degree is even
when `s = t`), and then `uhierholzer E s` finds one. -/
theorem exists_isUEulerPath_iff (E : List (V × V)) (s t : V)
    (hreach : ∀ e ∈ E, UReach E s e.1) :
    (∃ W, IsUEulerPath E s t W) ↔ EvenExcept E s t :=
  ⟨fun ⟨_, h⟩ => evenExcept_of_isUEulerPath h,
    fun h => ⟨_, uhierholzer_isUEulerPath E s t h hreach⟩⟩

end Cslib.Algorithms.Lean.Hierholzer
