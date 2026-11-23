/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.CSP.AC3
public import Mathlib.Data.Fintype.Card

/-!
# Tree CSPs: directional arc consistency makes greedy assignment backtrack-free

The constraint graph of a binary CSP (`BinaryCSP X D`, from AC-3) is a *forest* when a parent map
`parent : X → Option X` and a root-first order `order` exist such that every arc joins a variable
and its parent (`IsTreeArcs`), every variable appears exactly once in `order`, no variable is its
own parent and no variable's parent comes after it (`RootedOrder`). The domains are
*directionally arc consistent* (`DirArcConsistent`) when every arc from a parent to its child is
consistent.

The tree-CSP algorithm (Freuder, *A sufficient condition for backtrack-free search*, J. ACM 29
(1982); Dechter and Pearl, *Network-based heuristics for constraint-satisfaction problems*,
Artificial Intelligence 34 (1987); Russell and Norvig, *Artificial Intelligence: A Modern
Approach*, fourth edition, Section 6.5, Figure 6.10) has two phases:

* `dac`: for the variables in reverse order, revise the arc from the parent to the variable
  (`revise` from AC-3), shrinking the parent's domain;
* `greedy`: for the variables in order, choose (with a selection function `sel`) a value of the
  variable's domain compatible with its parent's value; fail if there is none.

`treeSolve` runs both. Main results, for symmetric constraints (`Symmetric`):

* `isSolution_of_greedy_eq_some`: whatever greedy returns is a solution.
* `greedy_ne_none`, `greedy_ne_none_iff` (**backtrack-free**): on directionally arc consistent
  domains, greedy never fails when every domain is nonempty, and succeeds iff every domain is
  nonempty.
* `dirArcConsistent_dac`: the DAC pass establishes directional arc consistency;
  `isSolution_dac`: it loses no solution when every parent edge is an arc.
* `treeSolve_ne_none_iff`, `isSolution_of_treeSolve_eq_some`: `treeSolve` succeeds iff the CSP has
  a solution, and then returns one.
* `dac_time_le`, `dac_time_le_card`: the DAC pass performs at most `n · d²` constraint checks
  for `n` variables and domains of size at most `d`.
* `dirArcConsistent_ac3All`: AC-3's domains are directionally arc consistent, so greedy after AC-3
  is backtrack-free as well.

The example of three pairwise-different variables with two colours (in the tests) shows that the
tree hypothesis is needed: all arcs are consistent there, greedy along a spanning path returns an
assignment, and no solution exists.

## Cost model

`dac` runs in `TimeM` and charges, for each variable `x` with parent `p`, `|dom p| · |dom x|`
constraint checks, the work of revising `(p, x)`; roots cost nothing. A rooted order lists each
variable exactly once, so there is one revision per non-root variable. `greedy` is not costed.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.ArcConsistency

open Cslib.Algorithms.Lean

variable {X D : Type*} [DecidableEq X] [DecidableEq D] (P : BinaryCSP X D)

/-- `order` lists the variables root first for the parent map `parent`: it contains every
variable exactly once, no variable is its own parent, and no variable's parent comes after it. -/
structure RootedOrder (parent : X → Option X) (order : List X) : Prop where
  /-- Every variable is listed. -/
  mem : ∀ x, x ∈ order
  /-- No variable is listed twice. -/
  nodup : order.Nodup
  /-- No variable is its own parent. -/
  irrefl : ∀ x, parent x ≠ some x
  /-- No variable's parent comes after it. -/
  before : order.Pairwise fun a b => parent a ≠ some b

/-- Every arc joins a variable and its parent, in either orientation: the constraint graph is
contained in the forest of `parent`. -/
def IsTreeArcs (parent : X → Option X) : Prop :=
  ∀ e ∈ P.arcs, parent e.2 = some e.1 ∨ parent e.1 = some e.2

/-- Directional arc consistency: the arc from every parent to its child is consistent. -/
def DirArcConsistent (parent : X → Option X) (dom : X → Finset D) : Prop :=
  ∀ x p, parent x = some p → ArcConsistent P dom (p, x)

/-- A selection function: it returns a member of the set, and returns one whenever the set is
nonempty. -/
structure IsSelector (sel : Finset D → Option D) : Prop where
  /-- A selected value is a member. -/
  mem : ∀ s a, sel s = some a → a ∈ s
  /-- A nonempty set has a selected value. -/
  ne_none : ∀ s : Finset D, s.Nonempty → sel s ≠ none

/-! ## The DAC pass -/

/-- One DAC step at `x`: revise the arc from the parent of `x` to `x`. -/
def dacStep (parent : X → Option X) (dom : X → Finset D) (x : X) : X → Finset D :=
  match parent x with
  | none => dom
  | some p => Function.update dom p (revise P dom p x)

/-- The constraint checks of the DAC step at `x`: `|dom p| · |dom x|` for the parent `p`. -/
def dacCost (parent : X → Option X) (dom : X → Finset D) (x : X) : ℕ :=
  match parent x with
  | none => 0
  | some p => (dom p).card * (dom x).card

/-- DAC steps at the listed variables, in list order, charging their constraint checks. -/
def dacPass (parent : X → Option X) : (X → Finset D) → List X → TimeM ℕ (X → Finset D)
  | dom, [] => pure dom
  | dom, x :: xs => do
      TimeM.tick (dacCost parent dom x)
      dacPass parent (dacStep P parent dom x) xs

/-- The DAC pass: DAC steps at the variables in reverse order. -/
def dac (parent : X → Option X) (order : List X) (dom : X → Finset D) :
    TimeM ℕ (X → Finset D) :=
  dacPass P parent dom order.reverse

variable {P} {parent : X → Option X} {order : List X}

omit [DecidableEq D] in
theorem dacStep_subset (dom : X → Finset D) (x v : X) : dacStep P parent dom x v ⊆ dom v := by
  rcases hpx : parent x with _ | p
  · simp only [dacStep, hpx, subset_refl]
  · simp only [dacStep, hpx]
    by_cases hv : v = p
    · rw [hv, Function.update_self]; exact revise_subset P dom p x
    · rw [Function.update_of_ne hv]

omit [DecidableEq D] in
/-- **Domains only shrink.** -/
theorem dacPass_subset (dom : X → Finset D) (ys : List X) (v : X) :
    (dacPass P parent dom ys).ret v ⊆ dom v := by
  induction ys generalizing dom with
  | nil => simp [dacPass]
  | cons x xs ih =>
      simp only [dacPass, TimeM.ret_bind]
      exact (ih _).trans (dacStep_subset dom x v)

omit [DecidableEq D] in
theorem dac_subset (dom : X → Finset D) (v : X) : (dac P parent order dom).ret v ⊆ dom v :=
  dacPass_subset dom _ v

omit [DecidableEq D] in
theorem isSolution_dacStep (hedge : ∀ x p, parent x = some p → (p, x) ∈ P.arcs)
    {dom : X → Finset D} {σ : X → D} (hσ : IsSolution P dom σ) (x : X) :
    IsSolution P (dacStep P parent dom x) σ := by
  refine ⟨fun v => ?_, hσ.2⟩
  rcases hpx : parent x with _ | p
  · simp only [dacStep, hpx]; exact hσ.1 v
  · simp only [dacStep, hpx]
    by_cases hv : v = p
    · rw [hv, Function.update_self]; exact mem_revise_of_isSolution P hσ (hedge x p hpx)
    · rw [Function.update_of_ne hv]; exact hσ.1 v

omit [DecidableEq D] in
theorem isSolution_dacPass (hedge : ∀ x p, parent x = some p → (p, x) ∈ P.arcs)
    (ys : List X) {dom : X → Finset D} {σ : X → D} (hσ : IsSolution P dom σ) :
    IsSolution P (dacPass P parent dom ys).ret σ := by
  induction ys generalizing dom with
  | nil => simpa [dacPass] using hσ
  | cons x xs ih =>
      simp only [dacPass, TimeM.ret_bind]
      exact ih (isSolution_dacStep hedge hσ x)

omit [DecidableEq D] in
/-- **No solution is lost** by the DAC pass when every parent edge is an arc. -/
theorem isSolution_dac (hedge : ∀ x p, parent x = some p → (p, x) ∈ P.arcs)
    {dom : X → Finset D} {σ : X → D} (hσ : IsSolution P dom σ) :
    IsSolution P (dac P parent order dom).ret σ :=
  isSolution_dacPass hedge _ hσ

omit [DecidableEq D] in
/-- The DAC pass invariant on the list `ys` of variables still to process: no listed variable
has an unlisted (processed) parent, and the arc from each processed variable's parent is
consistent. -/
theorem dirArcConsistent_dacPass (hirr : ∀ x, parent x ≠ some x) :
    ∀ (ys : List X) (dom : X → Finset D),
      ys.Pairwise (fun a b => parent b ≠ some a) →
      (∀ x ∈ ys, ∀ y, y ∉ ys → parent x ≠ some y) →
      (∀ y, y ∉ ys → ∀ q, parent y = some q → ArcConsistent P dom (q, y)) →
      DirArcConsistent P parent (dacPass P parent dom ys).ret
  | [], dom, _, _, hinv => fun x p hp => hinv x List.not_mem_nil p hp
  | x :: xs, dom, hpw, hrem, hinv => by
      simp only [dacPass, TimeM.ret_bind]
      have hpw' := List.pairwise_cons.1 hpw
      refine dirArcConsistent_dacPass hirr xs _ hpw'.2 ?_ ?_
      · intro x' hx' y hy
        by_cases hyx : y = x
        · rw [hyx]; exact hpw'.1 x' hx'
        · exact hrem x' (List.mem_cons_of_mem _ hx') y (by simp [hyx, hy])
      · intro y hy q hq
        rcases hpx : parent x with _ | p
        · have hyx : y ≠ x := fun h => by rw [h, hpx] at hq; simp at hq
          simp only [dacStep, hpx]
          exact hinv y (by simp [hyx, hy]) q hq
        · simp only [dacStep, hpx]
          by_cases hyx : y = x
          · rw [hyx, hpx] at hq
            rw [hyx, ← Option.some.inj hq]
            have hxp : x ≠ p := fun h => hirr x (by rw [hpx, h])
            intro a ha
            change a ∈ Function.update dom p (revise P dom p x) p at ha
            change ∃ b ∈ Function.update dom p (revise P dom p x) x, P.allowed p x a b = true
            rw [Function.update_self] at ha
            rw [Function.update_of_ne hxp]
            obtain ⟨-, b, hb, hab⟩ := Finset.mem_filter.1 ha
            exact ⟨b, hb, hab⟩
          · have hy' : y ∉ x :: xs := by simp [hyx, hy]
            have hyp : y ≠ p := fun h => hrem x List.mem_cons_self y hy' (by rw [hpx, h])
            have hc := hinv y hy' q hq
            intro a ha
            change a ∈ Function.update dom p (revise P dom p x) q at ha
            change ∃ b ∈ Function.update dom p (revise P dom p x) y, P.allowed q y a b = true
            rw [Function.update_of_ne hyp]
            have ha' : a ∈ dom q := by
              by_cases hqp : q = p
              · rw [hqp, Function.update_self] at ha
                rw [hqp]; exact revise_subset P dom p x ha
              · rwa [Function.update_of_ne hqp] at ha
            exact hc a ha'

omit [DecidableEq D] in
/-- **The DAC pass establishes directional arc consistency.** -/
theorem dirArcConsistent_dac (hord : RootedOrder parent order) (dom : X → Finset D) :
    DirArcConsistent P parent (dac P parent order dom).ret :=
  dirArcConsistent_dacPass hord.irrefl order.reverse dom (List.pairwise_reverse.2 hord.before)
    (fun _ _ y hy => absurd (List.mem_reverse.2 (hord.mem y)) hy)
    (fun y hy => absurd (List.mem_reverse.2 (hord.mem y)) hy)

omit [DecidableEq D] in
theorem dacPass_time_le (d : ℕ) :
    ∀ (ys : List X) (dom : X → Finset D), (∀ v, (dom v).card ≤ d) →
      (dacPass P parent dom ys).time ≤ ys.length * (d * d)
  | [], _, _ => by simp [dacPass]
  | x :: xs, dom, hd => by
      simp only [dacPass, TimeM.time_bind, TimeM.time_tick, List.length_cons]
      have h1 : dacCost parent dom x ≤ d * d := by
        rcases hpx : parent x with _ | p
        · simp [dacCost, hpx]
        · simp only [dacCost, hpx]; exact Nat.mul_le_mul (hd p) (hd x)
      have h2 := dacPass_time_le d xs (dacStep P parent dom x)
        fun v => (Finset.card_le_card (dacStep_subset dom x v)).trans (hd v)
      rw [Nat.add_mul, Nat.one_mul]
      omega

omit [DecidableEq D] in
/-- **Cost bound**: for domains of size at most `d`, the DAC pass performs at most `n · d²`
constraint checks, `n` the number of listed variables. -/
theorem dac_time_le (d : ℕ) (dom : X → Finset D) (hd : ∀ v, (dom v).card ≤ d) :
    (dac P parent order dom).time ≤ order.length * (d * d) := by
  have := dacPass_time_le (P := P) (parent := parent) d order.reverse dom hd
  rwa [List.length_reverse] at this

omit [DecidableEq D] in
/-- **Cost bound, counted by variables**: under a rooted order, which lists every variable
exactly once, the DAC pass performs at most `Fintype.card X · d²` constraint checks. -/
theorem dac_time_le_card [Fintype X] (hord : RootedOrder parent order) (d : ℕ)
    (dom : X → Finset D) (hd : ∀ v, (dom v).card ≤ d) :
    (dac P parent order dom).time ≤ Fintype.card X * (d * d) := by
  have hto : order.toFinset = Finset.univ := by
    ext x
    simp [hord.mem]
  have hlen : order.length = Fintype.card X := by
    have hcard := congrArg Finset.card hto
    rw [Finset.card_univ, List.toFinset_card_of_nodup hord.nodup] at hcard
    exact hcard
  rw [← hlen]
  exact dac_time_le d dom hd

/-- AC-3's domains are directionally arc consistent when every parent edge is an arc. -/
theorem dirArcConsistent_ac3All [Fintype X] (hedge : ∀ x p, parent x = some p → (p, x) ∈ P.arcs)
    (hsym : Symmetric P) (hdist : ∀ e ∈ P.arcs, e.1 ≠ e.2) (dom : X → Finset D) :
    DirArcConsistent P parent (ac3All P dom).ret :=
  fun x p hp => arcConsistent_ac3 P hsym hdist dom _ (hedge x p hp)

/-! ## Greedy assignment -/

variable (P parent) in
/-- The values of `x` compatible with the value of its parent under `σ`. -/
def candidates (dom : X → Finset D) (σ : X → D) (x : X) : Finset D :=
  match parent x with
  | none => dom x
  | some p => (dom x).filter fun b => P.allowed p x (σ p) b = true

variable (P parent) in
/-- Greedy assignment of the listed variables, in list order: each gets the selected candidate;
fails when a variable has no candidate. -/
def greedyFrom (sel : Finset D → Option D) (dom : X → Finset D) :
    List X → (X → D) → Option (X → D)
  | [], σ => some σ
  | x :: xs, σ =>
      match sel (candidates P parent dom σ x) with
      | none => none
      | some b => greedyFrom sel dom xs (Function.update σ x b)

variable (P parent order) in
/-- Greedy assignment of all variables in root-first order. -/
def greedy [Inhabited D] (sel : Finset D → Option D) (dom : X → Finset D) : Option (X → D) :=
  greedyFrom P parent sel dom order fun _ => default

variable (P parent) in
/-- The greedy invariant for the list `xs` of variables still to assign: every assigned variable
has a value in its domain, an assigned parent, and a value compatible with its parent's. -/
def GreedyInv (dom : X → Finset D) (xs : List X) (σ : X → D) : Prop :=
  ∀ y, y ∉ xs → σ y ∈ dom y ∧ ∀ p, parent y = some p → p ∉ xs ∧ P.allowed p y (σ p) (σ y) = true

omit [DecidableEq D] in
theorem greedyInv_step (hirr : ∀ x, parent x ≠ some x) {dom : X → Finset D} {x : X}
    {xs : List X} {σ : X → D} {b : D} (hpw : ∀ p ∈ xs, parent x ≠ some p)
    (hinv : GreedyInv P parent dom (x :: xs) σ) (hb : b ∈ candidates P parent dom σ x) :
    GreedyInv P parent dom xs (Function.update σ x b) := by
  intro y hy
  by_cases hyx : y = x
  · rw [hyx, Function.update_self]
    rcases hpx : parent x with _ | q
    · simp only [candidates, hpx] at hb
      exact ⟨hb, fun p hp => by simp at hp⟩
    · simp only [candidates, hpx, Finset.mem_filter] at hb
      refine ⟨hb.1, fun p hp => ?_⟩
      rw [← Option.some.inj hp]
      have hqx : q ≠ x := fun h => hirr x (by rw [hpx, h])
      exact ⟨fun h => hpw q h hpx, by rw [Function.update_of_ne hqx]; exact hb.2⟩
  · have hy' : y ∉ x :: xs := by simp [hyx, hy]
    obtain ⟨hσy, hpar⟩ := hinv y hy'
    rw [Function.update_of_ne hyx]
    refine ⟨hσy, fun p hp => ?_⟩
    obtain ⟨hpn, hal⟩ := hpar p hp
    have hpx : p ≠ x := fun h => hpn (by rw [h]; exact List.mem_cons_self)
    exact ⟨fun h => hpn (List.mem_cons_of_mem _ h), by rw [Function.update_of_ne hpx]; exact hal⟩

omit [DecidableEq D] in
theorem greedyInv_greedyFrom {sel : Finset D → Option D} (hsel : IsSelector sel)
    (hirr : ∀ x, parent x ≠ some x) {dom : X → Finset D} :
    ∀ (xs : List X) (σ τ : X → D), xs.Pairwise (fun a b => parent a ≠ some b) →
      GreedyInv P parent dom xs σ → greedyFrom P parent sel dom xs σ = some τ →
      GreedyInv P parent dom [] τ
  | [], σ, τ, _, hinv, h => by
      simp only [greedyFrom, Option.some.injEq] at h
      subst h; exact hinv
  | x :: xs, σ, τ, hpw, hinv, h => by
      have hpw' := List.pairwise_cons.1 hpw
      simp only [greedyFrom] at h
      split at h
      · simp at h
      · rename_i b hb
        exact greedyInv_greedyFrom hsel hirr xs _ τ hpw'.2
          (greedyInv_step hirr hpw'.1 hinv (hsel.mem _ _ hb)) h

omit [DecidableEq D] in
theorem greedyFrom_ne_none {sel : Finset D → Option D} (hsel : IsSelector sel)
    (hirr : ∀ x, parent x ≠ some x) {dom : X → Finset D} (hdac : DirArcConsistent P parent dom)
    (hne : ∀ x, (dom x).Nonempty) :
    ∀ (xs : List X) (σ : X → D), xs.Pairwise (fun a b => parent a ≠ some b) →
      GreedyInv P parent dom xs σ → greedyFrom P parent sel dom xs σ ≠ none
  | [], σ, _, _ => by simp [greedyFrom]
  | x :: xs, σ, hpw, hinv => by
      have hpw' := List.pairwise_cons.1 hpw
      have hcand : (candidates P parent dom σ x).Nonempty := by
        rcases hpx : parent x with _ | p
        · simp only [candidates, hpx]; exact hne x
        · simp only [candidates, hpx]
          have hp : p ∉ x :: xs := by
            simp only [List.mem_cons, not_or]
            exact ⟨fun h => hirr x (by rw [hpx, h]), fun h => hpw'.1 p h hpx⟩
          obtain ⟨b, hb, hab⟩ := hdac x p hpx (σ p) (hinv p hp).1
          exact ⟨b, Finset.mem_filter.2 ⟨hb, hab⟩⟩
      obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 (hsel.ne_none _ hcand)
      simp only [greedyFrom, hb]
      exact greedyFrom_ne_none hsel hirr hdac hne xs _ hpw'.2
        (greedyInv_step hirr hpw'.1 hinv (hsel.mem _ _ hb))

omit [DecidableEq X] [DecidableEq D] in
theorem greedyInv_init (hord : RootedOrder parent order) (dom : X → Finset D) (σ : X → D) :
    GreedyInv P parent dom order σ :=
  fun y hy => absurd (hord.mem y) hy

omit [DecidableEq X] [DecidableEq D] in
theorem isSolution_of_greedyInv (hsym : Symmetric P) (htree : IsTreeArcs P parent)
    {dom : X → Finset D} {σ : X → D} (h : GreedyInv P parent dom [] σ) : IsSolution P dom σ := by
  refine ⟨fun y => (h y List.not_mem_nil).1, fun e he => ?_⟩
  rcases htree e he with hp | hp
  · exact ((h e.2 List.not_mem_nil).2 e.1 hp).2
  · rw [hsym]; exact ((h e.1 List.not_mem_nil).2 e.2 hp).2

omit [DecidableEq D] in
/-- **Greedy is sound**: on a forest, whatever greedy returns is a solution. -/
theorem isSolution_of_greedy_eq_some [Inhabited D] {sel : Finset D → Option D}
    (hsel : IsSelector sel) (hord : RootedOrder parent order) (hsym : Symmetric P)
    (htree : IsTreeArcs P parent) {dom : X → Finset D} {σ : X → D}
    (h : greedy P parent order sel dom = some σ) : IsSolution P dom σ :=
  isSolution_of_greedyInv hsym htree
    (greedyInv_greedyFrom hsel hord.irrefl order _ σ hord.before (greedyInv_init hord dom _) h)

omit [DecidableEq D] in
/-- **Backtrack-free**: on directionally arc consistent nonempty domains greedy never fails. -/
theorem greedy_ne_none [Inhabited D] {sel : Finset D → Option D} (hsel : IsSelector sel)
    (hord : RootedOrder parent order) {dom : X → Finset D} (hdac : DirArcConsistent P parent dom)
    (hne : ∀ x, (dom x).Nonempty) : greedy P parent order sel dom ≠ none :=
  greedyFrom_ne_none hsel hord.irrefl hdac hne order _ hord.before (greedyInv_init hord dom _)

omit [DecidableEq D] in
/-- On a forest with directionally arc consistent domains, greedy succeeds iff every domain is
nonempty (and then returns a solution, `isSolution_of_greedy_eq_some`). -/
theorem greedy_ne_none_iff [Inhabited D] {sel : Finset D → Option D} (hsel : IsSelector sel)
    (hord : RootedOrder parent order) (hsym : Symmetric P) (htree : IsTreeArcs P parent)
    {dom : X → Finset D} (hdac : DirArcConsistent P parent dom) :
    greedy P parent order sel dom ≠ none ↔ ∀ x, (dom x).Nonempty := by
  refine ⟨fun h x => ?_, greedy_ne_none hsel hord hdac⟩
  obtain ⟨σ, hσ⟩ := Option.ne_none_iff_exists'.1 h
  exact ⟨σ x, (isSolution_of_greedy_eq_some hsel hord hsym htree hσ).1 x⟩

/-! ## The tree-CSP algorithm -/

variable (P parent order) in
/-- The tree-CSP algorithm: the DAC pass, then greedy assignment. -/
def treeSolve [Inhabited D] (sel : Finset D → Option D) (dom : X → Finset D) : Option (X → D) :=
  greedy P parent order sel (dac P parent order dom).ret

omit [DecidableEq D] in
/-- Whatever `treeSolve` returns is a solution. -/
theorem isSolution_of_treeSolve_eq_some [Inhabited D] {sel : Finset D → Option D}
    (hsel : IsSelector sel) (hord : RootedOrder parent order) (hsym : Symmetric P)
    (htree : IsTreeArcs P parent) {dom : X → Finset D} {σ : X → D}
    (h : treeSolve P parent order sel dom = some σ) : IsSolution P dom σ := by
  have hσ := isSolution_of_greedy_eq_some hsel hord hsym htree h
  exact ⟨fun v => dac_subset dom v (hσ.1 v), hσ.2⟩

omit [DecidableEq D] in
/-- **The tree-CSP algorithm is complete without backtracking**: when the constraint graph is
the forest of `parent` (every arc a parent edge and every parent edge an arc), `treeSolve`
succeeds iff the CSP has a solution. -/
theorem treeSolve_ne_none_iff [Inhabited D] {sel : Finset D → Option D} (hsel : IsSelector sel)
    (hord : RootedOrder parent order) (hsym : Symmetric P) (htree : IsTreeArcs P parent)
    (hedge : ∀ x p, parent x = some p → (p, x) ∈ P.arcs) (dom : X → Finset D) :
    treeSolve P parent order sel dom ≠ none ↔ ∃ σ, IsSolution P dom σ := by
  constructor
  · intro h
    obtain ⟨σ, hσ⟩ := Option.ne_none_iff_exists'.1 h
    exact ⟨σ, isSolution_of_treeSolve_eq_some hsel hord hsym htree hσ⟩
  · rintro ⟨σ, hσ⟩
    have hσ' := isSolution_dac (order := order) hedge hσ
    exact greedy_ne_none hsel hord (dirArcConsistent_dac hord dom) fun x => ⟨σ x, hσ'.1 x⟩

end Cslib.Algorithms.Lean.ArcConsistency
