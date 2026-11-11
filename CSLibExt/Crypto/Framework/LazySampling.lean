/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Advantage
public import CSLibExt.Crypto.Framework.Oracle
public import CSLibExt.Crypto.Hash.Birthday
public import Mathlib.Data.Fintype.Perm

/-!
# Adaptive lazy sampling and the PRP/PRF switching lemma

A random function or random permutation can be sampled **eagerly** (the whole function up front)
or **lazily** (each answer at the moment it is first asked for, recorded in a table). This file
proves the two are the same for **adaptive** oracle algorithms, whose next query may depend on
earlier answers, and derives the adaptive PRP/PRF switching lemma with the birthday bound.

**Oracle access model.** An adversary is an `OracleComp X Y α` (`CSLibExt.Crypto.Framework.Oracle`):
an adaptive oracle algorithm in CSLib's free monad. A **stateful randomized oracle**
`O : σ → X → PMF (Y × σ)` answers a query in state `s` with an answer and a new state;
`runState O c s` runs `c` against it.

**Lazy sampling.** A `Table X Y = X → Option Y` records the answers given so far.
`lazyStep fresh T x` answers a recorded query from the table (**consistency**,
`lazyStep_of_some`) and otherwise samples a fresh answer from `fresh T x` and records it
(`lazyStep_of_none`).
* `lazyRF c T`: the lazy random function, fresh answers uniform on `Y`
  (`rfStep_map_fst_of_none`).
* `lazyRP c T`: the lazy random permutation of a finite `D`, fresh answers uniform on the values
  not yet in the table, `freshSet T` (`rpStep_map_fst_of_none`, `rpStep_fst_mem_freshSet`).
* Along a lazy run, recorded answers never change (`extends_of_mem_support_runState`), and the lazy
  permutation's table stays the restriction of a permutation, so distinct queries get distinct
  answers (`injective_of_mem_support_lazyRP`).

**Lazy = eager.** `runState_lazyStep_map_fst` is the generic statement: if the uniform
distribution on the functions `ω` consistent with a table splits, at each fresh query `x`, as
"sample the answer from `fresh T x`, then sample uniformly among the functions consistent with
the extended table", the lazy run has the same output distribution as running against a function
sampled uniformly among those consistent with the table (Katz and Lindell's description of a
random function, or random oracle, sampled "on the fly", Sections 3.5.1 and 5.5.1). Instances:
* `lazyRF_map_fst`: `lazyRF c ∅` has the output distribution of `c` run against a uniformly random
  function `X → Y`.
* `lazyRP_map_fst`: `lazyRP c ∅` has the output distribution of `c` run against a uniformly random
  permutation of `D`.

**The switching lemma** (`switching_lemma`). Let `D` be a finite type with `N` elements and `c` an
adaptive distinguisher with oracle `D → D` making at most `q` queries along every path
(`FreeM.IsQueryBounded q c`; repeated queries count). Then
`|Pr[c^f = 1] - Pr[c^π = 1]| ≤ Birthday.collisionProb D q`,
with `f` a uniformly random function `D → D` and `π` a uniformly random permutation of `D`, and
`collisionProb D q = 1 - N (N - 1) ⋯ (N - q + 1) / N ^ q ≤ q (q - 1) / (2 N)`
(`switching_lemma_le`). This is the information-theoretic step in Katz and Lindell's proof that a
pseudorandom permutation is a pseudorandom function (Section 3.5.1, Proposition 3.27); the bound
is tight (`CSLibExtTest.Crypto.Framework.LazySamplingTests`). The proof is an "identical until
bad" induction on the lazy runs (`lazy_switching`): with `m` unused values left, a fresh query is
answered alike by both oracles unless the random function hits one of the `N - m` used values.

**Coexistence.** Wave 3 unifies this file with the monadic (PPT) adversaries developed in
parallel; nothing here depends on them. `Cslib.Crypto.PRF` samples its oracles eagerly and is not
migrated. The lazy random oracle of the open random-oracle pull request (its `step`, `run`,
`Table`, `Extends` and `runState`) is `rfStep`, `lazyRF`, `Table`, `Extends` and `runState` here;
after both merge, one copy is deleted. The random-tape lemmas of the open CCA and modes pull
requests concern stateless oracles with fresh randomness per query (`runState_stateless_map_fst`
relates those to `runState`), not consistent random functions, so they are not instances of
`runState_lazyStep_map_fst`.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Sections 3.5.1 and 5.5.1, Proposition 3.27, Appendix A.4.
* M. Bellare and P. Rogaway, *Code-Based Game-Playing Proofs and the Security of Triple
  Encryption*, EUROCRYPT 2006 (the PRP/PRF switching lemma, Lemma 1).
-/

@[expose] public section

namespace Cslib.Crypto.Framework.LazySampling

open Finset Cslib.Probability.PMF

universe u v w

/-! ### PMF helpers -/

section PMFHelpers

variable {α β : Type*}

/-- `PMF.bind` only depends on the continuation on the support. -/
theorem bind_congr_support (p : PMF α) {f g : α → PMF β} (h : ∀ a ∈ p.support, f a = g a) :
    p.bind f = p.bind g := by
  ext b
  simp only [PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · rw [PMF.mem_support_iff, not_not] at ha
    simp [ha]

/-- `PMF.map` only depends on the function on the support. -/
theorem map_congr_support (p : PMF α) {f g : α → β} (h : ∀ a ∈ p.support, f a = g a) :
    p.map f = p.map g := by
  rw [← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
  exact bind_congr_support p fun a ha => by simp [h a ha]

/-- The uniform distribution on a finite set, falling back to the uniform distribution on the whole
type when the set is empty (so that it is total). -/
noncomputable def condUniform [Fintype α] [Nonempty α] (s : Finset α) : PMF α :=
  if h : s.Nonempty then uniformOfFinset s h else uniformOfFintype α

theorem condUniform_of_nonempty [Fintype α] [Nonempty α] {s : Finset α} (hs : s.Nonempty) :
    condUniform s = uniformOfFinset s hs := dite_eq_left hs

@[simp] theorem condUniform_univ [Fintype α] [Nonempty α] :
    condUniform (univ : Finset α) = uniformOfFintype α := dite_eq_left univ_nonempty

theorem mem_of_mem_support_condUniform [Fintype α] [Nonempty α] {s : Finset α}
    (hs : s.Nonempty) {a : α} (h : a ∈ (condUniform s).support) : a ∈ s := by
  rw [condUniform_of_nonempty hs] at h
  exact (mem_support_uniformOfFinset_iff hs a).1 h

open scoped Classical in
theorem condUniform_apply [Fintype α] [Nonempty α] {s : Finset α} (hs : s.Nonempty) (a : α) :
    condUniform s a = if a ∈ s then ((#s : ℕ) : ENNReal)⁻¹ else 0 := by
  rw [condUniform_of_nonempty hs, uniformOfFinset_apply]

/-- **Splitting a uniform distribution along a coordinate.** If every fibre of `g` over `F`
has the same size, sampling uniformly from `S` is the same as sampling `y` uniformly from `F` and
then sampling uniformly from the fibre of `g` over `y`. -/
theorem condUniform_split [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] [DecidableEq β]
    (S : Finset α) (g : α → β) (F : Finset β) (hS : S.Nonempty) (hg : ∀ a ∈ S, g a ∈ F)
    (hcard : ∀ y ∈ F, ∀ y' ∈ F, #{a ∈ S | g a = y} = #{a ∈ S | g a = y'}) :
    condUniform S = (condUniform F).bind fun y => condUniform {a ∈ S | g a = y} := by
  classical
  obtain ⟨a₀, ha₀⟩ := hS
  have hF : F.Nonempty := ⟨g a₀, hg a₀ ha₀⟩
  have hfib : ∀ y ∈ F, ({a ∈ S | g a = y} : Finset α).Nonempty := fun y hy => by
    rw [← card_pos, hcard y hy (g a₀) (hg a₀ ha₀), card_pos]
    exact ⟨a₀, mem_filter.2 ⟨ha₀, rfl⟩⟩
  ext a
  rw [PMF.bind_apply, tsum_eq_single (g a)]
  · by_cases ha : a ∈ S
    · have hga := hg a ha
      rw [condUniform_apply ⟨a₀, ha₀⟩, condUniform_apply hF, condUniform_apply (hfib _ hga),
        ite_eq_left ha, ite_eq_left hga,
        ite_eq_left (show a ∈ ({b ∈ S | g b = g a} : Finset α) from mem_filter.2 ⟨ha, rfl⟩)]
      have hsum : #S = #F * #{b ∈ S | g b = g a} := by
        rw [card_eq_sum_card_fiberwise (fun b hb => hg b hb),
          sum_const_nat fun y hy => hcard y hy (g a) hga]
      rw [hsum, Nat.cast_mul, ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
        (Or.inl (ENNReal.natCast_ne_top _))]
    · rw [condUniform_apply ⟨a₀, ha₀⟩, ite_eq_right ha]
      by_cases hga : g a ∈ F
      · rw [condUniform_apply (hfib _ hga), ite_eq_right (fun h => ha (mem_filter.1 h).1), mul_zero]
      · rw [condUniform_apply hF, ite_eq_right hga, zero_mul]
  · intro y hy
    by_cases hyF : y ∈ F
    · rw [condUniform_apply (hfib _ hyF), ite_eq_right (fun h => hy (mem_filter.1 h).2.symm),
        mul_zero]
    · rw [condUniform_apply hF, ite_eq_right hyF, zero_mul]

/-- The success probability after a uniform choice from a nonempty finite set is the average
success probability. -/
theorem winProb_bind_uniformOfFinset [Finite α] (F : Finset α) (hF : F.Nonempty)
    (G : α → PMF Bool) :
    winProb ((uniformOfFinset F hF).bind G) = (∑ y ∈ F, winProb (G y)) / #F := by
  classical
  have := Fintype.ofFinite α
  rw [winProb, PMF.bind_apply, tsum_fintype]
  simp only [uniformOfFinset_apply, ite_mul, zero_mul]
  rw [sum_ite_mem, univ_inter, ← mul_sum, ENNReal.toReal_mul,
    ENNReal.toReal_sum fun y _ => PMF.apply_ne_top _ _, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, div_eq_inv_mul]
  rfl

end PMFHelpers

/-! ### Stateful oracles and lazy tables -/

section Lazy

variable {X : Type u} {Y : Type v}

/-- A table of the answers given so far: `T x = some y` when the query `x` was answered `y`. -/
abbrev Table (X : Type u) (Y : Type v) : Type (max u v) := X → Option Y

/-- The empty table: no query answered yet. -/
def Table.empty : Table X Y := fun _ => none

/-- A function `f` is consistent with a table `T` when it agrees with every recorded answer. -/
def Consistent (T : Table X Y) (f : X → Y) : Prop := ∀ x y, T x = some y → f x = y

/-- `T ≤ T'`: the table `T'` extends `T` (every recorded answer is kept). -/
def Extends (T T' : Table X Y) : Prop := ∀ x y, T x = some y → T' x = some y

/-- Run an oracle computation against a **stateful randomized oracle** `O`, which answers the
query `x` in state `s` by sampling an answer and a new state from `O s x`. This is oracle access
to a stateful algorithm, e.g. a lazily sampled random oracle (Katz and Lindell, Section 5.5.1).
The open random-oracle pull request defines the same function as `Cslib.Crypto.Framework.runState`;
Wave 3 keeps one of the two. -/
noncomputable def runState {σ : Type*} {α : Type w} (O : σ → X → PMF (Y × σ)) :
    OracleComp X Y α → σ → PMF (α × σ)
  | .pure a, s => PMF.pure (a, s)
  | .liftBind x k, s => (O s x).bind fun p => runState O (k p.1) p.2

/-- A stateless randomized oracle is the special case of a stateful one that ignores and keeps its
state: `runState` then has the output distribution of `FreeM.evalPMF`. -/
theorem runState_stateless_map_fst {σ : Type*} {α : Type w} (O : X → PMF Y) :
    ∀ (c : OracleComp X Y α) (s : σ),
      (runState (fun s x => (O x).map fun y => (y, s)) c s).map Prod.fst = FreeM.evalPMF O c
  | .pure a, s => by rw [runState, PMF.pure_map]; rfl
  | .liftBind x k, s => by
    rw [runState, PMF.bind_map, PMF.map_bind, FreeM.evalPMF_liftBind]
    congr 1
    funext y
    exact runState_stateless_map_fst O (k y) s

variable [DecidableEq X]

/-- One step of a **lazily sampled** oracle with table `T`: a recorded query is answered from the
table; a fresh query `x` is answered by a sample `y` of `fresh T x`, and `x ↦ y` is recorded
(Katz and Lindell, Section 5.5.1: the oracle "keeps a table" and answers a new query with a fresh
random value). -/
noncomputable def lazyStep (fresh : Table X Y → X → PMF Y) (T : Table X Y) (x : X) :
    PMF (Y × Table X Y) :=
  match T x with
  | some y => PMF.pure (y, T)
  | none => (fresh T x).map fun y => (y, Function.update T x (some y))

/-- **Consistency**: a recorded query gets its recorded answer, and the table is unchanged. -/
theorem lazyStep_of_some (fresh : Table X Y → X → PMF Y) {T : Table X Y} {x : X} {y : Y}
    (hx : T x = some y) : lazyStep fresh T x = PMF.pure (y, T) := by
  simp [lazyStep, hx]

/-- A fresh query is answered by a sample of `fresh T x`, which is recorded. -/
theorem lazyStep_of_none (fresh : Table X Y → X → PMF Y) {T : Table X Y} {x : X}
    (hx : T x = none) :
    lazyStep fresh T x = (fresh T x).map fun y => (y, Function.update T x (some y)) := by
  simp [lazyStep, hx]

/-- The answer of a fresh query is distributed as `fresh T x`. -/
theorem lazyStep_map_fst_of_none (fresh : Table X Y → X → PMF Y) {T : Table X Y} {x : X}
    (hx : T x = none) : (lazyStep fresh T x).map Prod.fst = fresh T x := by
  rw [lazyStep_of_none fresh hx, PMF.map_comp]
  exact PMF.map_id _

theorem runState_lazyStep_of_some {α : Type w} (fresh : Table X Y → X → PMF Y) {T : Table X Y}
    {x : X} {y : Y} (k : Y → OracleComp X Y α) (hx : T x = some y) :
    runState (lazyStep fresh) (.liftBind x k) T = runState (lazyStep fresh) (k y) T := by
  rw [runState, lazyStep_of_some fresh hx, PMF.pure_bind]

theorem runState_lazyStep_of_none {α : Type w} (fresh : Table X Y → X → PMF Y) {T : Table X Y}
    {x : X} (k : Y → OracleComp X Y α) (hx : T x = none) :
    runState (lazyStep fresh) (.liftBind x k) T =
      (fresh T x).bind fun y => runState (lazyStep fresh) (k y) (Function.update T x (some y)) := by
  rw [runState, lazyStep_of_none fresh hx, PMF.bind_map]
  rfl

/-- **Run-level consistency**: along a lazy run, a recorded answer is never changed, so a query
asked twice gets the same answer both times. -/
theorem extends_of_mem_support_runState {α : Type w} (fresh : Table X Y → X → PMF Y) :
    ∀ (c : OracleComp X Y α) (T : Table X Y),
      ∀ p ∈ (runState (lazyStep fresh) c T).support, Extends T p.2
  | .pure a, T, p, hp => by
    rw [runState, PMF.mem_support_pure_iff] at hp
    subst hp
    exact fun _ _ h => h
  | .liftBind x k, T, p, hp => by
    cases hx : T x with
    | some y =>
      rw [runState_lazyStep_of_some fresh k hx] at hp
      exact extends_of_mem_support_runState fresh (k y) T p hp
    | none =>
      rw [runState_lazyStep_of_none fresh k hx, PMF.mem_support_bind_iff] at hp
      obtain ⟨y, -, hp⟩ := hp
      intro z w hz
      refine extends_of_mem_support_runState fresh (k y) _ p hp z w ?_
      have hzx : z ≠ x := by rintro rfl; rw [hx] at hz; cases hz
      rwa [Function.update_of_ne hzx]

/-- A table invariant preserved by every fresh step is preserved by the whole lazy run. -/
theorem inv_of_mem_support_runState {α : Type w} (fresh : Table X Y → X → PMF Y)
    (Inv : Table X Y → Prop)
    (hinv : ∀ T x, Inv T → T x = none → ∀ y ∈ (fresh T x).support,
      Inv (Function.update T x (some y))) :
    ∀ (c : OracleComp X Y α) (T : Table X Y), Inv T →
      ∀ p ∈ (runState (lazyStep fresh) c T).support, Inv p.2
  | .pure a, T, hT, p, hp => by
    rw [runState, PMF.mem_support_pure_iff] at hp
    subst hp
    exact hT
  | .liftBind x k, T, hT, p, hp => by
    cases hx : T x with
    | some y =>
      rw [runState_lazyStep_of_some fresh k hx] at hp
      exact inv_of_mem_support_runState fresh Inv hinv (k y) T hT p hp
    | none =>
      rw [runState_lazyStep_of_none fresh k hx, PMF.mem_support_bind_iff] at hp
      obtain ⟨y, hy, hp⟩ := hp
      exact inv_of_mem_support_runState fresh Inv hinv (k y) _ (hinv T x hT hx y hy) p hp

/-! ### Lazy = eager, generically -/

open scoped Classical in
/-- The functions in a finite family `Ω` (seen as functions through `ev`) that are consistent with
the table `T`. -/
noncomputable def consistentSet {Ω : Type*} [Fintype Ω] (ev : Ω → X → Y) (T : Table X Y) :
    Finset Ω :=
  {ω | Consistent T (ev ω)}

omit [DecidableEq X] in
theorem mem_consistentSet {Ω : Type*} [Fintype Ω] {ev : Ω → X → Y} {T : Table X Y} {ω : Ω} :
    ω ∈ consistentSet ev T ↔ Consistent T (ev ω) := by
  classical
  simp [consistentSet]

omit [DecidableEq X] in
@[simp] theorem consistentSet_empty {Ω : Type*} [Fintype Ω] (ev : Ω → X → Y) :
    consistentSet ev (Table.empty : Table X Y) = univ := by
  ext ω
  simp only [mem_consistentSet, mem_univ, iff_true]
  intro x y h
  cases h

/-- The functions consistent with `T` that answer `y` at a fresh `x` are exactly those consistent
with `T` extended by `x ↦ y`. -/
theorem filter_consistentSet [DecidableEq Y] {Ω : Type*} [Fintype Ω] (ev : Ω → X → Y)
    {T : Table X Y} {x : X} (hx : T x = none) (y : Y) :
    {ω ∈ consistentSet ev T | ev ω x = y} = consistentSet ev (Function.update T x (some y)) := by
  ext ω
  simp only [mem_filter, mem_consistentSet]
  constructor
  · rintro ⟨hc, hy⟩ z w hz
    by_cases hzx : z = x
    · subst hzx
      rw [Function.update_self, Option.some.injEq] at hz
      rw [← hz, hy]
    · rw [Function.update_of_ne hzx] at hz
      exact hc z w hz
  · intro hc
    refine ⟨fun z w hz => hc z w ?_, hc x y (by simp)⟩
    have hzx : z ≠ x := by rintro rfl; rw [hx] at hz; cases hz
    rwa [Function.update_of_ne hzx]

/-- **Lazy = eager** (generic form). Suppose that, for every table `T` satisfying an invariant
`Inv` and every fresh query `x`, the uniform distribution on the functions consistent with `T`
splits as "sample the answer from `fresh T x`, then sample uniformly among the functions
consistent with `T` extended by `x ↦ y`", and that fresh steps preserve `Inv`. Then for every
adaptive algorithm `c`, the lazy run has the output distribution of `c` run against a function
sampled uniformly among those consistent with `T`. -/
theorem runState_lazyStep_map_fst {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (ev : Ω → X → Y) (fresh : Table X Y → X → PMF Y) (Inv : Table X Y → Prop)
    (hne : ∀ T, Inv T → (consistentSet ev T).Nonempty)
    (hsplit : ∀ T x, Inv T → T x = none →
      condUniform (consistentSet ev T) =
        (fresh T x).bind fun y => condUniform (consistentSet ev (Function.update T x (some y))))
    (hinv : ∀ T x, Inv T → T x = none → ∀ y ∈ (fresh T x).support,
      Inv (Function.update T x (some y))) {α : Type w} :
    ∀ (c : OracleComp X Y α) (T : Table X Y), Inv T →
      (runState (lazyStep fresh) c T).map Prod.fst =
        (condUniform (consistentSet ev T)).map fun ω => c.run (ev ω)
  | .pure a, T, _ => by
    rw [runState, PMF.pure_map]
    exact (PMF.map_const _ a).symm
  | .liftBind x k, T, hT => by
    cases hx : T x with
    | some y =>
      rw [runState_lazyStep_of_some fresh k hx,
        runState_lazyStep_map_fst ev fresh Inv hne hsplit hinv (k y) T hT]
      refine map_congr_support _ fun ω hω => ?_
      have hc := mem_consistentSet.1 (mem_of_mem_support_condUniform (hne T hT) hω)
      change OracleComp.run (ev ω) (k y) = OracleComp.run (ev ω) (k (ev ω x))
      rw [hc x y hx]
    | none =>
      rw [runState_lazyStep_of_none fresh k hx, PMF.map_bind, hsplit T x hT hx, PMF.map_bind]
      refine bind_congr_support _ fun y hy => ?_
      have hT' := hinv T x hT hx y hy
      rw [runState_lazyStep_map_fst ev fresh Inv hne hsplit hinv (k y) _ hT']
      refine map_congr_support _ fun ω hω => ?_
      have hc := mem_consistentSet.1 (mem_of_mem_support_condUniform (hne _ hT') hω)
      change OracleComp.run (ev ω) (k y) = OracleComp.run (ev ω) (k (ev ω x))
      rw [hc x y (by simp)]

/-! ### The lazy random function -/

section RF

variable [Fintype X] [Fintype Y] [Nonempty Y]

/-- The lazily sampled random function: a fresh query gets a uniform answer in `Y`. -/
noncomputable def rfStep : Table X Y → X → PMF (Y × Table X Y) :=
  lazyStep fun _ _ => uniformOfFintype Y

/-- Run an adaptive algorithm against the **lazy random function** with initial table `T`;
returns the output and the final table. -/
noncomputable def lazyRF {α : Type w} (c : OracleComp X Y α) (T : Table X Y) :
    PMF (α × Table X Y) :=
  runState rfStep c T

omit [Fintype X] in
/-- **Fresh-answer uniformity** for the lazy random function. -/
theorem rfStep_map_fst_of_none {T : Table X Y} {x : X} (hx : T x = none) :
    (rfStep T x).map Prod.fst = uniformOfFintype Y :=
  lazyStep_map_fst_of_none _ hx

omit [Fintype X] in
/-- **Consistency** for the lazy random function. -/
theorem rfStep_of_some {T : Table X Y} {x : X} {y : Y} (hx : T x = some y) :
    rfStep T x = PMF.pure (y, T) :=
  lazyStep_of_some _ hx

omit [Fintype X] [Fintype Y] [Nonempty Y] in
private theorem consistent_update {T : Table X Y} {x : X} (hx : T x = none) {f : X → Y}
    (hf : Consistent T f) (y : Y) : Consistent T (Function.update f x y) := by
  intro z w hz
  have hzx : z ≠ x := by rintro rfl; rw [hx] at hz; cases hz
  rw [Function.update_of_ne hzx]
  exact hf z w hz

private theorem consistentSet_rf_nonempty (T : Table X Y) :
    (consistentSet (fun f : X → Y => f) T).Nonempty :=
  ⟨fun x => (T x).getD (Classical.arbitrary Y),
    mem_consistentSet.2 fun x y h => by simp [h]⟩

private theorem rf_split (T : Table X Y) (x : X) (hx : T x = none) :
    condUniform (consistentSet (fun f : X → Y => f) T) =
      (uniformOfFintype Y).bind fun y =>
        condUniform (consistentSet (fun f : X → Y => f) (Function.update T x (some y))) := by
  classical
  rw [condUniform_split (consistentSet (fun f : X → Y => f) T) (fun f => f x) univ
    (consistentSet_rf_nonempty T) (fun _ _ => mem_univ _) ?_, condUniform_univ]
  · congr 1
    funext y
    rw [filter_consistentSet (fun f : X → Y => f) hx y]
  · intro y _ y' _
    refine card_nbij' (fun f => Function.update f x y') (fun f => Function.update f x y)
      ?_ ?_ ?_ ?_
    · intro f hf
      simp only [coe_filter, Set.mem_ofPred_eq, mem_consistentSet] at hf ⊢
      exact ⟨consistent_update hx hf.1 y', by simp⟩
    · intro f hf
      simp only [coe_filter, Set.mem_ofPred_eq, mem_consistentSet] at hf ⊢
      exact ⟨consistent_update hx hf.1 y, by simp⟩
    · intro f hf
      simp only [coe_filter, Set.mem_ofPred_eq] at hf
      simp [← hf.2]
    · intro f hf
      simp only [coe_filter, Set.mem_ofPred_eq] at hf
      simp [← hf.2]

/-- **Lazy = eager for random functions** (adaptive): running `c` against the lazy random function
from the empty table gives the same output distribution as running `c` against a uniformly
random function `X → Y` sampled up front (Katz and Lindell, Section 3.5.1). -/
theorem lazyRF_map_fst {α : Type w} (c : OracleComp X Y α) :
    (lazyRF c Table.empty).map Prod.fst = (uniformOfFintype (X → Y)).map fun f => c.run f := by
  have h := runState_lazyStep_map_fst (fun f : X → Y => f) (fun _ _ => uniformOfFintype Y)
    (fun _ => True) (fun T _ => consistentSet_rf_nonempty T) (fun T x _ hx => rf_split T x hx)
    (fun _ _ _ _ _ _ => trivial) c Table.empty trivial
  rwa [consistentSet_empty, condUniform_univ] at h

end RF

end Lazy

/-! ### The lazy random permutation -/

section RP

variable {D : Type u} [Fintype D] [DecidableEq D] [Nonempty D]

open scoped Classical in
/-- The values not yet used as answers in the table `T`. -/
noncomputable def freshSet (T : Table D D) : Finset D := {y | ∀ z, T z ≠ some y}

omit [Nonempty D] in
theorem mem_freshSet {T : Table D D} {y : D} : y ∈ freshSet T ↔ ∀ z, T z ≠ some y := by
  classical
  simp [freshSet]

omit [Nonempty D] in
@[simp] theorem freshSet_empty : freshSet (Table.empty : Table D D) = univ := by
  ext y
  simp only [mem_freshSet, mem_univ, iff_true]
  intro z h
  cases h

omit [Nonempty D] in
/-- Recording a fresh answer `y` removes `y` from the unused values. -/
theorem freshSet_update {T : Table D D} {x : D} (hx : T x = none) (y : D) :
    freshSet (Function.update T x (some y)) = (freshSet T).erase y := by
  ext y'
  simp only [mem_freshSet, mem_erase]
  constructor
  · intro h
    refine ⟨fun hy => h x (by simp [hy]), fun z hz => ?_⟩
    have hzx : z ≠ x := by rintro rfl; rw [hx] at hz; cases hz
    exact h z (by rwa [Function.update_of_ne hzx])
  · rintro ⟨hy, h⟩ z hz
    by_cases hzx : z = x
    · subst hzx
      simp only [Function.update_self, Option.some.injEq] at hz
      exact hy hz.symm
    · rw [Function.update_of_ne hzx] at hz
      exact h z hz

/-- The lazily sampled random permutation: a fresh query gets an answer uniform among the values
not used yet. -/
noncomputable def rpStep : Table D D → D → PMF (D × Table D D) :=
  lazyStep fun T _ => condUniform (freshSet T)

/-- Run an adaptive algorithm against the **lazy random permutation** with initial table `T`;
returns the output and the final table. -/
noncomputable def lazyRP {α : Type w} (c : OracleComp D D α) (T : Table D D) :
    PMF (α × Table D D) :=
  runState rpStep c T

/-- **Fresh-answer uniformity** for the lazy random permutation: uniform among the unused
values. -/
theorem rpStep_map_fst_of_none {T : Table D D} {x : D} (hx : T x = none)
    (hF : (freshSet T).Nonempty) :
    (rpStep T x).map Prod.fst = uniformOfFinset (freshSet T) hF := by
  rw [rpStep, lazyStep_map_fst_of_none _ hx, condUniform_of_nonempty hF]

/-- **Consistency** for the lazy random permutation. -/
theorem rpStep_of_some {T : Table D D} {x : D} {y : D} (hx : T x = some y) :
    rpStep T x = PMF.pure (y, T) :=
  lazyStep_of_some _ hx

/-- A fresh answer of the lazy random permutation is a value not used yet. -/
theorem rpStep_fst_mem_freshSet {T : Table D D} {x : D} (hx : T x = none)
    (hF : (freshSet T).Nonempty) : ∀ p ∈ (rpStep T x).support, p.1 ∈ freshSet T := by
  intro p hp
  have : p.1 ∈ ((rpStep T x).map Prod.fst).support :=
    (PMF.mem_support_map_iff _ _ _).2 ⟨p, hp, rfl⟩
  rw [rpStep_map_fst_of_none hx hF] at this
  exact (mem_support_uniformOfFinset_iff hF _).1 this

/-- The permutations of `D`, as functions. -/
abbrev permEv : Equiv.Perm D → D → D := fun π => π

/-- `T` is the restriction of some permutation. -/
def PermTable (T : Table D D) : Prop := (consistentSet permEv T).Nonempty

omit [Nonempty D] in
private theorem apply_mem_freshSet {T : Table D D} {x : D} (hx : T x = none)
    {π : Equiv.Perm D} (hπ : π ∈ consistentSet permEv T) : π x ∈ freshSet T := by
  rw [mem_freshSet]
  intro z hz
  have hzx : z = x := π.injective (mem_consistentSet.1 hπ z _ hz)
  rw [hzx, hx] at hz
  cases hz

omit [Nonempty D] in
private theorem swap_mem {T : Table D D} {x : D} {y y' : D} (hy : y ∈ freshSet T)
    (hy' : y' ∈ freshSet T) {π : Equiv.Perm D}
    (hπ : π ∈ ({σ ∈ consistentSet permEv T | permEv σ x = y} : Finset _)) :
    π.trans (Equiv.swap y y') ∈ ({σ ∈ consistentSet permEv T | permEv σ x = y'} : Finset _) := by
  rw [mem_filter, mem_consistentSet] at hπ ⊢
  refine ⟨fun z w hz => ?_, ?_⟩
  · have hw : π z = w := hπ.1 z w hz
    have hwy : w ≠ y := by rintro rfl; exact mem_freshSet.1 hy z hz
    have hwy' : w ≠ y' := by rintro rfl; exact mem_freshSet.1 hy' z hz
    simp only [permEv, Equiv.trans_apply, hw]
    exact Equiv.swap_apply_of_ne_of_ne hwy hwy'
  · simp only [permEv, Equiv.trans_apply] at hπ ⊢
    rw [hπ.2, Equiv.swap_apply_left]

omit [Nonempty D] in
private theorem rp_card {T : Table D D} {x : D} :
    ∀ y ∈ freshSet T, ∀ y' ∈ freshSet T,
      #({σ ∈ consistentSet permEv T | permEv σ x = y} : Finset _) =
        #({σ ∈ consistentSet permEv T | permEv σ x = y'} : Finset _) := by
  intro y hy y' hy'
  refine card_nbij' (fun π => π.trans (Equiv.swap y y')) (fun π => π.trans (Equiv.swap y y'))
    (fun π hπ => swap_mem hy hy' hπ) (fun π hπ => ?_) (fun π _ => ?_) (fun π _ => ?_)
  · rw [Equiv.swap_comm]
    exact swap_mem hy' hy hπ
  · ext z
    simp [Equiv.swap_apply_self]
  · ext z
    simp [Equiv.swap_apply_self]

private theorem rp_split (T : Table D D) (x : D) (hT : PermTable T) (hx : T x = none) :
    condUniform (consistentSet permEv T) =
      (condUniform (freshSet T)).bind fun y =>
        condUniform (consistentSet permEv (Function.update T x (some y))) := by
  rw [condUniform_split (consistentSet permEv T) (fun π => permEv π x) (freshSet T) hT
    (fun π hπ => apply_mem_freshSet hx hπ) rp_card]
  congr 1
  funext y
  rw [filter_consistentSet permEv hx y]

private theorem rp_inv (T : Table D D) (x : D) (hT : PermTable T) (hx : T x = none) :
    ∀ y ∈ (condUniform (freshSet T)).support, PermTable (Function.update T x (some y)) := by
  intro y hy
  obtain ⟨π, hπ⟩ := hT
  have hF : (freshSet T).Nonempty := ⟨π x, apply_mem_freshSet hx hπ⟩
  have hyF := mem_of_mem_support_condUniform hF hy
  refine ⟨π.trans (Equiv.swap (π x) y), ?_⟩
  rw [← filter_consistentSet permEv hx y]
  exact swap_mem (apply_mem_freshSet hx hπ) hyF (mem_filter.2 ⟨hπ, rfl⟩)

omit [Nonempty D] in
theorem permTable_empty : PermTable (Table.empty : Table D D) :=
  ⟨1, by rw [consistentSet_empty]; exact mem_univ _⟩

/-- **Lazy = eager for random permutations** (adaptive): running `c` against the lazy random
permutation from the empty table gives the same output distribution as running `c` against a
uniformly random permutation of `D` sampled up front (Katz and Lindell, Section 3.5.1). -/
theorem lazyRP_map_fst {α : Type w} (c : OracleComp D D α) :
    (lazyRP c Table.empty).map Prod.fst =
      (uniformOfFintype (Equiv.Perm D)).map fun π : Equiv.Perm D => c.run ⇑π := by
  have h := runState_lazyStep_map_fst permEv (fun T _ => condUniform (freshSet T)) PermTable
    (fun _ hT => hT) rp_split rp_inv c Table.empty permTable_empty
  rwa [consistentSet_empty, condUniform_univ] at h

/-- Along a lazy random-permutation run from a table that is the restriction of a permutation,
the table stays the restriction of a permutation. -/
theorem permTable_of_mem_support_lazyRP {α : Type w} (c : OracleComp D D α) {T : Table D D}
    (hT : PermTable T) : ∀ p ∈ (lazyRP c T).support, PermTable p.2 :=
  inv_of_mem_support_runState _ PermTable rp_inv c T hT

/-- **Distinct queries get distinct answers** from the lazy random permutation: the final table of
a run from the empty table is injective. -/
theorem injective_of_mem_support_lazyRP {α : Type w} (c : OracleComp D D α) :
    ∀ p ∈ (lazyRP c Table.empty).support, ∀ x x' y, p.2 x = some y → p.2 x' = some y → x = x' := by
  intro p hp x x' y hx hx'
  obtain ⟨π, hπ⟩ := permTable_of_mem_support_lazyRP c permTable_empty p hp
  have hc := mem_consistentSet.1 hπ
  exact π.injective ((hc x y hx).trans (hc x' y hx').symm)

/-! ### The switching lemma -/

/-- The switching bound with `m` unused values out of `N`, after `q` more queries:
`1 - m (m - 1) ⋯ (m - q + 1) / N ^ q`. For `m = N` it is `Birthday.collisionProb`. -/
noncomputable def switchBound (N m q : ℕ) : ℝ := 1 - (m.descFactorial q : ℝ) / (N : ℝ) ^ q

theorem switchBound_nonneg {N m : ℕ} (hm : m ≤ N) (q : ℕ) : 0 ≤ switchBound N m q := by
  rw [switchBound, sub_nonneg]
  refine div_le_one_of_le₀ ?_ (by positivity)
  exact_mod_cast (Nat.descFactorial_le_pow m q).trans (Nat.pow_le_pow_left hm q)

theorem switchBound_le_one (N m q : ℕ) : switchBound N m q ≤ 1 := by
  rw [switchBound, sub_le_self_iff]
  positivity

theorem switchBound_mono {N m : ℕ} (hN : 0 < N) (hm : m ≤ N) (q : ℕ) :
    switchBound N m q ≤ switchBound N m (q + 1) := by
  rw [switchBound, switchBound, sub_le_sub_iff_left, Nat.descFactorial_succ, pow_succ,
    Nat.cast_mul]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [mul_comm ((m - q : ℕ) : ℝ), mul_div_mul_comm]
  refine mul_le_of_le_one_right (by positivity) ?_
  rw [div_le_one hN']
  exact_mod_cast (Nat.sub_le m q).trans hm

theorem switchBound_zero_succ (N q : ℕ) : switchBound N 0 (q + 1) = 1 := by
  simp [switchBound]

theorem switchBound_succ_succ {N : ℕ} (hN : 0 < N) (m q : ℕ) :
    switchBound N (m + 1) (q + 1) = 1 - ((m + 1 : ℕ) / N : ℝ) * (1 - switchBound N m q) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [switchBound, switchBound, Nat.succ_descFactorial_succ, Nat.cast_mul, pow_succ]
  field_simp
  ring

/-- The averaging step of the switching lemma: if `a` and `b` are `[0, 1]`-valued and within `δ` on
a nonempty set `F` of `m` out of `N` points, the average of `a` over all points and the average of
`b` over `F` are within `1 - (m / N) (1 - δ)`. -/
private theorem abs_avg_sub_avg_le {ι : Type*} [Fintype ι] (F : Finset ι)
    (hF : F.Nonempty) (a b : ι → ℝ) (δ : ℝ) (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    (hb0 : ∀ i, 0 ≤ b i) (hb1 : ∀ i, b i ≤ 1) (hab : ∀ i ∈ F, |a i - b i| ≤ δ) :
    |(∑ i, a i) / Fintype.card ι - (∑ i ∈ F, b i) / #F| ≤
      1 - ((#F : ℝ) / Fintype.card ι) * (1 - δ) := by
  classical
  have hm : (0 : ℝ) < #F := by exact_mod_cast card_pos.2 hF
  have hmN : (#F : ℝ) ≤ Fintype.card ι := by exact_mod_cast card_le_univ F
  have hcompl : (#Fᶜ : ℝ) + #F = Fintype.card ι := by exact_mod_cast card_compl_add_card F
  set N : ℝ := (Fintype.card ι : ℝ)
  set m : ℝ := (#F : ℝ)
  have hN : 0 < N := hm.trans_le hmN
  set Ain := ∑ i ∈ Fᶜ, a i
  set Aout := ∑ i ∈ F, a i
  set B := ∑ i ∈ F, b i
  have hsplit : ∑ i, a i = Aout + Ain := (sum_add_sum_compl F a).symm
  have hAin0 : 0 ≤ Ain := sum_nonneg fun i _ => ha0 i
  have hAin1 : Ain ≤ N - m := by
    have := sum_le_card_nsmul Fᶜ a 1 fun i _ => ha1 i
    rw [nsmul_eq_mul, mul_one] at this
    linarith
  have hB0 : 0 ≤ B := sum_nonneg fun i _ => hb0 i
  have hB1 : B ≤ m := by
    have := sum_le_card_nsmul F b 1 fun i _ => hb1 i
    rwa [nsmul_eq_mul, mul_one] at this
  have hAB : |Aout - B| ≤ m * δ := by
    rw [← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have := sum_le_card_nsmul F (fun i => |a i - b i|) δ hab
    rwa [nsmul_eq_mul] at this
  obtain ⟨hAB1, hAB2⟩ := abs_le.1 hAB
  rw [hsplit, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  set u := N⁻¹
  set w := m⁻¹
  have hu : 0 < u := inv_pos.2 hN
  have hNu : N * u = 1 := mul_inv_cancel₀ hN.ne'
  have hmw : m * w = 1 := mul_inv_cancel₀ hm.ne'
  have huw : u ≤ w := inv_anti₀ hm hmN
  rw [abs_le]
  constructor
  · have h1 : 0 ≤ Ain * u := mul_nonneg hAin0 hu.le
    have h2 : (B - m * δ) * u ≤ Aout * u := mul_le_mul_of_nonneg_right (by linarith) hu.le
    have h3 : B * (w - u) ≤ m * (w - u) := mul_le_mul_of_nonneg_right hB1 (sub_nonneg.2 huw)
    nlinarith
  · have h1 : Ain * u ≤ (N - m) * u := mul_le_mul_of_nonneg_right hAin1 hu.le
    have h2 : Aout * u ≤ (B + m * δ) * u := mul_le_mul_of_nonneg_right (by linarith) hu.le
    have h3 : B * u ≤ B * w := mul_le_mul_of_nonneg_left huw hB0
    nlinarith

theorem lazyRF_liftBind_of_some {α : Type w} {T : Table D D} {x y : D}
    (k : D → OracleComp D D α) (hx : T x = some y) :
    lazyRF (.liftBind x k) T = lazyRF (k y) T :=
  runState_lazyStep_of_some _ k hx

theorem lazyRP_liftBind_of_some {α : Type w} {T : Table D D} {x y : D}
    (k : D → OracleComp D D α) (hx : T x = some y) :
    lazyRP (.liftBind x k) T = lazyRP (k y) T :=
  runState_lazyStep_of_some _ k hx

private theorem abs_winProb_sub_le_one (G₀ G₁ : PMF Bool) : |winProb G₀ - winProb G₁| ≤ 1 := by
  rw [abs_sub_le_iff]
  constructor <;> linarith [winProb_nonneg G₀, winProb_nonneg G₁, winProb_le_one G₀,
    winProb_le_one G₁]

/-- **Lazy switching lemma** ("identical until bad"). For an adaptive distinguisher `c` making at
most `q` queries, started from a common table `T` with `m` unused values, the lazy random function
and the lazy random permutation are distinguished with advantage at most `switchBound N m q`. -/
theorem lazy_switching :
    ∀ (c : OracleComp D D Bool) (q : ℕ) (T : Table D D), FreeM.IsQueryBounded q c →
      |winProb ((lazyRF c T).map Prod.fst) - winProb ((lazyRP c T).map Prod.fst)| ≤
        switchBound (Fintype.card D) #(freshSet T) q
  | .pure a, q, T, _ => by
    simp only [lazyRF, lazyRP, runState, PMF.pure_map, sub_self, abs_zero]
    exact switchBound_nonneg (card_le_univ _) q
  | .liftBind x k, 0, T, hc => hc.elim
  | .liftBind x k, q + 1, T, hc => by
    have hN : 0 < Fintype.card D := Fintype.card_pos
    cases hx : T x with
    | some y =>
      rw [lazyRF_liftBind_of_some k hx, lazyRP_liftBind_of_some k hx]
      exact (lazy_switching (k y) q T (hc y)).trans
        (switchBound_mono hN (card_le_univ _) q)
    | none =>
      by_cases hF : (freshSet T).Nonempty
      · obtain ⟨m, hm⟩ : ∃ m, #(freshSet T) = m + 1 :=
          ⟨_, (Nat.succ_pred_eq_of_pos (card_pos.2 hF)).symm⟩
        have hRF : (lazyRF (.liftBind x k) T).map Prod.fst =
            (uniformOfFinset univ univ_nonempty).bind fun y =>
              (lazyRF (k y) (Function.update T x (some y))).map Prod.fst := by
          rw [lazyRF, rfStep, runState_lazyStep_of_none _ k hx, PMF.map_bind]
          rfl
        have hRP : (lazyRP (.liftBind x k) T).map Prod.fst =
            (uniformOfFinset (freshSet T) hF).bind fun y =>
              (lazyRP (k y) (Function.update T x (some y))).map Prod.fst := by
          rw [lazyRP, rpStep, runState_lazyStep_of_none _ k hx, PMF.map_bind,
            condUniform_of_nonempty hF]
          rfl
        rw [hRF, hRP, winProb_bind_uniformOfFinset, winProb_bind_uniformOfFinset, card_univ,
          hm, switchBound_succ_succ hN]
        have key := abs_avg_sub_avg_le (freshSet T) hF
          (fun y => winProb ((lazyRF (k y) (Function.update T x (some y))).map Prod.fst))
          (fun y => winProb ((lazyRP (k y) (Function.update T x (some y))).map Prod.fst))
          (switchBound (Fintype.card D) m q)
          (fun _ => winProb_nonneg _) (fun _ => winProb_le_one _) (fun _ => winProb_nonneg _)
          (fun _ => winProb_le_one _) fun y hy => by
            have h := lazy_switching (k y) q (Function.update T x (some y)) (hc y)
            rwa [freshSet_update hx, card_erase_of_mem hy, hm, Nat.add_sub_cancel] at h
        rw [hm] at key
        exact key
      · rw [not_nonempty_iff_eq_empty.1 hF, card_empty, switchBound_zero_succ]
        exact abs_winProb_sub_le_one _ _

/-- **The PRP/PRF switching lemma** (adaptive, query-bounded). Let `D` be a finite type and `c` an
adaptive distinguisher with oracle access to a function `D → D`, making at most `q` queries along
every path. Its advantage in distinguishing a uniformly random function `f : D → D` from a
uniformly random permutation `π` of `D`, each sampled once and then queried, is at most the
birthday collision probability `Birthday.collisionProb D q = 1 - N (N - 1) ⋯ (N - q + 1) / N ^ q`
with `N = |D|` (Katz and Lindell, Section 3.5.1, the step behind Proposition 3.27; Bellare and
Rogaway, Lemma 1). -/
theorem switching_lemma {q : ℕ} (c : OracleComp D D Bool) (hq : FreeM.IsQueryBounded q c) :
    advantage ((uniformOfFintype (D → D)).map fun f => c.run f)
        ((uniformOfFintype (Equiv.Perm D)).map fun π : Equiv.Perm D => c.run ⇑π) ≤
      Birthday.collisionProb D q := by
  rw [← lazyRF_map_fst, ← lazyRP_map_fst, advantage]
  refine (lazy_switching c q Table.empty hq).trans (le_of_eq ?_)
  rw [freshSet_empty, card_univ, switchBound, Birthday.collisionProb_eq]

/-- The switching lemma with the explicit birthday bound `q (q - 1) / (2 N)` (Katz and Lindell,
Lemma A.15). -/
theorem switching_lemma_le {q : ℕ} (c : OracleComp D D Bool) (hq : FreeM.IsQueryBounded q c) :
    advantage ((uniformOfFintype (D → D)).map fun f => c.run f)
        ((uniformOfFintype (Equiv.Perm D)).map fun π : Equiv.Perm D => c.run ⇑π) ≤
      q * (q - 1) / (2 * Fintype.card D) :=
  (switching_lemma c hq).trans (Birthday.collisionProb_le D q)

end RP

end Cslib.Crypto.Framework.LazySampling
