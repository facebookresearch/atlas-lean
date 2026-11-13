/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Probability.PMF
public import Cslib.Foundations.Data.PFunctor.Free

/-!
# Oracle computations: probabilistic semantics and query cost

Adversaries in the generic security games of `CSLibExt.Crypto.Framework.Games` are **adaptive
oracle algorithms**: computations in CSLib's free monad `PFunctor.FreeM` over a polynomial functor
`P`, whose operations `a : P.A` are oracle queries answered by `P.B a`. This file gives them a
probabilistic semantics and a cost measure.

* `OracleComp X Y α` is the single-oracle case (queries in `X`, answers in `Y`). This file is its
  canonical home: `OracleComp.run O c` is the output against a deterministic oracle `O : X → Y` and
  `OracleComp.queries O c` the list of queries asked. `CSLibExt/Crypto/SymmetricKey/PRF.lean`
  re-exports these as `Cslib.Crypto.PRF.OracleComp` and friends, so the PRF development's
  adversaries are adversaries here.
* `evalPMF O c : PMF α` runs `c` against a **randomized** oracle `O : (a : P.A) → PMF (P.B a)`,
  sampling every answer afresh (Katz and Lindell's oracle access to a randomized algorithm such as
  `Enc_k(·)`, Section 3.4.2). `OracleComp.evalPMF_pure_comp`: for a deterministic oracle it is the
  point mass at the deterministic run `OracleComp.run`.
* `evalLog O c : PMF (α × List (X × Y))` additionally records the query transcript, which the
  forgery experiments use to check freshness (Katz and Lindell, Definitions 4.2 and 12.2).
* `OracleComp.runStateful s i c` runs `c` against a stateful deterministic oracle whose state is
  the query counter (the `i`-th query is answered by `s i`), returning the output and the
  transcript, as a stateful signer is run (Katz and Lindell, Section 12.6). `queryAt` names the
  query asked at a given counter, and `runStateful_congr` says the run only depends on the oracle
  at the counters and queries it actually reaches.
* `OracleComp.runCoins O c ρs` runs `c` against the randomized oracle `x ↦ O x ρ` on
  **presampled coins**: the `i`-th query is answered with the `i`-th coin of `ρs`.
  `OracleComp.map_runCoins`: on `q` uniform coins, a computation making at most `q` queries has
  the distribution of its run against the randomized oracle with fresh coins per query
  (`evalPMF`). This is the step of Katz and Lindell's proof of Proposition 11.3 in which a
  reduction answers encryption queries itself; `OracleComp.exists_cont_runCoins` carries a
  two-phase query bound through it.

**Cost model.** `OracleComp` has no notion of running time, and this file does not add one. The
only resource measured is the **number of oracle queries**:
* `(OracleComp.queries O c).length` is the number of queries along the run of `c` against the
  deterministic oracle `O`;
* `IsQueryBounded q c` says that `c` makes at most `q` queries **along every path**, whatever the
  answers; it is a structural (oracle-independent) bound, so it bounds the run against any oracle,
  deterministic, randomized or stateful (`OracleComp.length_queries_le`,
  `length_le_of_mem_support_evalLog`);
* `IsQueryBoundedWith cont q c` bounds a two-phase algorithm whose output carries a continuation:
  `c` makes some `j ≤ q` queries and its output `a` then satisfies `cont a (q - j)`.

What this defers: local computation is free, so a query-bounded adversary may be computationally
unbounded (an information-theoretic, "oracle model" restriction). Polynomial running time in the
security parameter (Katz and Lindell's PPT adversaries, Definition 3.4 ff.) is not modelled; see
`CSLibExt.Crypto.Framework.Asymptotic` for how asymptotic claims are stated on top of this.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Sections 3.4.2, 4.2 and 12.2.
-/

@[expose] public section

namespace Cslib.Crypto.Framework

universe u v w

/-! ### General oracle computations over a polynomial functor -/

namespace FreeM

variable {P : PFunctor.{u, v}} {α : Type w}

/-- Run an oracle computation against a randomized oracle: every query `a` is answered by a
fresh sample of `O a`. This is Katz and Lindell's oracle access to a randomized algorithm
(Section 3.4.2). -/
noncomputable def evalPMF (O : (a : P.A) → PMF (P.B a)) : P.FreeM α → PMF α
  | .pure x => PMF.pure x
  | .liftBind a k => (O a).bind fun b => evalPMF O (k b)

/-- `evalPMF` of the constructor `pure` (not `simp`: the simp normal form is the monadic `pure`). -/
theorem evalPMF_pure' (O : (a : P.A) → PMF (P.B a)) (x : α) :
    evalPMF O (.pure x : P.FreeM α) = PMF.pure x := rfl

/-- `evalPMF` of the constructor `liftBind` (not `simp`: CSLib's simp normal form is
`(lift a).bind k`; see `evalPMF_freeMBind` and `evalPMF_lift`). -/
theorem evalPMF_liftBind (O : (a : P.A) → PMF (P.B a)) (a : P.A)
    (k : P.B a → P.FreeM α) :
    evalPMF O (.liftBind a k) = (O a).bind fun b => evalPMF O (k b) := rfl

/-- `evalPMF` of the monadic `pure`. -/
@[simp] theorem evalPMF_pure (O : (a : P.A) → PMF (P.B a)) (x : α) :
    evalPMF O (pure x : P.FreeM α) = PMF.pure x := rfl

/-- `evalPMF` turns sequential composition of oracle computations into `PMF.bind`. -/
@[simp] theorem evalPMF_bind {β : Type w} (O : (a : P.A) → PMF (P.B a))
    (f : α → P.FreeM β) : ∀ c : P.FreeM α,
      evalPMF O (c >>= f) = (evalPMF O c).bind fun x => evalPMF O (f x)
  | .pure x => by
    change evalPMF O (f x) = _
    simp
  | .liftBind a k => by
    change (O a).bind (fun b => evalPMF O (k b >>= f)) = _
    simp only [evalPMF_liftBind, PMF.bind_bind]
    congr 1
    funext b
    exact evalPMF_bind O f (k b)

/-- `evalPMF` turns CSLib's `FreeM.bind` into `PMF.bind` (universe-polymorphic form of
`evalPMF_bind`). -/
@[simp] theorem evalPMF_freeMBind {β : Type*} (O : (a : P.A) → PMF (P.B a))
    (f : α → P.FreeM β) : ∀ c : P.FreeM α,
      evalPMF O (PFunctor.FreeM.bind c f) = (evalPMF O c).bind fun x => evalPMF O (f x)
  | .pure x => by
    change evalPMF O (f x) = _
    simp
  | .liftBind a k => by
    change (O a).bind (fun b => evalPMF O (PFunctor.FreeM.bind (k b) f)) = _
    simp only [evalPMF_liftBind, PMF.bind_bind]
    congr 1
    funext b
    exact evalPMF_freeMBind O f (k b)

/-- A single query is answered by one sample of the oracle. -/
@[simp] theorem evalPMF_lift (O : (a : P.A) → PMF (P.B a)) (a : P.A) :
    evalPMF O (PFunctor.FreeM.lift a : P.FreeM (P.B a)) = O a := by
  change (O a).bind (fun b => PMF.pure b) = _
  exact PMF.bind_pure _

/-- `evalPMF` commutes with mapping the output. -/
@[simp] theorem evalPMF_map {β : Type w} (O : (a : P.A) → PMF (P.B a)) (f : α → β) :
    ∀ c : P.FreeM α, evalPMF O (f <$> c) = (evalPMF O c).map f
  | .pure x => by
    change PMF.pure (f x) = _
    simp [PMF.pure_map]
  | .liftBind a k => by
    change (O a).bind (fun b => evalPMF O (f <$> k b)) = _
    simp only [evalPMF_liftBind, PMF.map_bind]
    congr 1
    funext b
    exact evalPMF_map O f (k b)

/-- A two-phase query bound: `IsQueryBoundedWith cont q c` holds when `c` makes some number
`j ≤ q` of queries along every path and its output `x` satisfies `cont x (q - j)`, the budget
left for the next phase. -/
def IsQueryBoundedWith (cont : α → ℕ → Prop) : ℕ → P.FreeM α → Prop
  | q, .pure x => cont x q
  | q, .liftBind _ k => match q with
    | 0 => False
    | q + 1 => ∀ b, IsQueryBoundedWith cont q (k b)
termination_by structural _ c => c

/-- `IsQueryBounded q c`: the computation `c` makes at most `q` oracle queries along every path,
whatever the answers. This is the adversary-cost predicate of the framework. -/
def IsQueryBounded (q : ℕ) (c : P.FreeM α) : Prop :=
  IsQueryBoundedWith (fun _ _ => True) q c

/-- A query bound with a weaker continuation condition still holds. -/
theorem IsQueryBoundedWith.mono {cont cont' : α → ℕ → Prop} (h : ∀ x j, cont x j → cont' x j) :
    ∀ {q : ℕ} {c : P.FreeM α}, IsQueryBoundedWith cont q c → IsQueryBoundedWith cont' q c
  | _, .pure x, hc => h x _ hc
  | 0, .liftBind _ _, hc => hc
  | _ + 1, .liftBind _ _, hc => fun b => IsQueryBoundedWith.mono h (hc b)

/-- A computation with no queries meets every bound. -/
theorem isQueryBounded_pure (q : ℕ) (x : α) : IsQueryBounded q (.pure x : P.FreeM α) :=
  trivial

/-- One query followed by `q`-bounded continuations is `q + 1`-bounded. -/
theorem isQueryBounded_liftBind {q : ℕ} {a : P.A} {k : P.B a → P.FreeM α}
    (h : ∀ b, IsQueryBounded q (k b)) : IsQueryBounded (q + 1) (.liftBind a k : P.FreeM α) :=
  h

/-- Query bounds are monotone in the budget. -/
theorem IsQueryBounded.mono : ∀ {q q' : ℕ} {c : P.FreeM α}, q ≤ q' →
    IsQueryBounded q c → IsQueryBounded q' c
  | _, _, .pure _, _, _ => trivial
  | 0, _, .liftBind _ _, _, hc => hc.elim
  | _ + 1, 0, .liftBind _ _, hqq, _ => absurd hqq (Nat.not_succ_le_zero _)
  | _ + 1, _ + 1, .liftBind _ _, hqq, hc => fun b =>
    IsQueryBounded.mono (Nat.le_of_succ_le_succ hqq) (hc b)

/-- A `0`-bounded computation asks no query: it is `pure` of its output. -/
theorem eq_pure_of_isQueryBoundedWith_zero {cont : α → ℕ → Prop} :
    ∀ {c : P.FreeM α}, IsQueryBoundedWith cont 0 c → ∃ x, c = .pure x ∧ cont x 0
  | .pure x, h => ⟨x, rfl, h⟩
  | .liftBind _ _, h => h.elim

end FreeM

/-! ### Single-oracle computations -/

/-- The polynomial functor of one oracle: a query `x : X` is answered by `y : Y`. Re-exported as
`Cslib.Crypto.PRF.OracleSig`. -/
abbrev OracleSig (X : Type u) (Y : Type v) : PFunctor.{u, v} := ⟨X, fun _ => Y⟩

/-- An adaptive oracle algorithm with one oracle `X → Y` and output in `α`: a computation in CSLib's
free monad over one oracle; it either stops with an output in `α`, or asks a query in `X` and
continues depending on the answer in `Y` (Katz and Lindell's oracle access, Section 3.4.2).
Re-exported as `Cslib.Crypto.PRF.OracleComp`. -/
abbrev OracleComp (X : Type u) (Y : Type v) (α : Type w) : Type (max u v w) :=
  (OracleSig X Y).FreeM α

namespace OracleComp

variable {X : Type u} {Y : Type v} {α : Type w}

/-- Stop with output `a`. -/
abbrev done (a : α) : OracleComp X Y α := .pure a

/-- Query `x` and continue with the answer. -/
abbrev query (x : X) (k : Y → OracleComp X Y α) : OracleComp X Y α := .liftBind x k

/-- The output of the algorithm when the oracle is the function `O`. -/
def run (O : X → Y) : OracleComp X Y α → α
  | .pure a => a
  | .liftBind x k => run O (k (O x))

/-- The queries the algorithm asks when the oracle is the function `O`, in order. -/
def queries (O : X → Y) : OracleComp X Y α → List X
  | .pure _ => []
  | .liftBind x k => x :: queries O (k (O x))

/-- **Locality**: the run only depends on the oracle at the queried points. -/
theorem run_congr {O O' : X → Y} :
    ∀ (c : OracleComp X Y α), (∀ x ∈ c.queries O, O x = O' x) →
      c.run O = c.run O' ∧ c.queries O = c.queries O'
  | .pure _, _ => ⟨rfl, rfl⟩
  | .liftBind x k, h => by
    have hx : O x = O' x := h x List.mem_cons_self
    have ih := run_congr (k (O x)) fun z hz => h z (List.mem_cons_of_mem _ hz)
    simp only [run, queries, ← hx]
    exact ⟨ih.1, by rw [ih.2]⟩

/-- Running a sequential composition (CSLib's `PFunctor.FreeM.bind`). -/
theorem run_bind {β : Type*} (O : X → Y) (g : α → OracleComp X Y β) :
    ∀ c : OracleComp X Y α, run O (PFunctor.FreeM.bind c g) = (g (c.run O)).run O
  | .pure _ => rfl
  | .liftBind x k => run_bind O g (k (O x))

/-- Running against a deterministic oracle, viewed as a randomized one, gives the point mass at
the deterministic run. -/
theorem evalPMF_pure_comp (O : X → Y) :
    ∀ c : OracleComp X Y α, FreeM.evalPMF (fun x => PMF.pure (O x)) c = PMF.pure (c.run O)
  | .pure _ => rfl
  | .liftBind x k => by
    simp only [FreeM.evalPMF, run, PMF.pure_bind]
    exact evalPMF_pure_comp O (k (O x))

/-- A structural query bound bounds the number of queries against every deterministic
oracle. -/
theorem length_queries_le (O : X → Y) :
    ∀ {q : ℕ} {c : OracleComp X Y α}, FreeM.IsQueryBounded q c → (c.queries O).length ≤ q
  | _, .pure _, _ => Nat.zero_le _
  | 0, .liftBind _ _, hc => hc.elim
  | _ + 1, .liftBind x _, hc => Nat.succ_le_succ (length_queries_le O (hc (O x)))

/-- Run against a randomized oracle and record the transcript of `(query, answer)` pairs, in
order. -/
noncomputable def evalLog (O : X → PMF Y) : OracleComp X Y α → PMF (α × List (X × Y))
  | .pure a => PMF.pure (a, [])
  | .liftBind x k =>
    (O x).bind fun y => (evalLog O (k y)).map fun p => (p.1, (x, y) :: p.2)

/-- `evalLog` of the constructor `pure` (not `simp`; see `evalLog_pure_monad`). -/
theorem evalLog_pure (O : X → PMF Y) (a : α) :
    evalLog O (.pure a : OracleComp X Y α) = PMF.pure (a, []) := rfl

/-- `evalLog` of the constructor `liftBind` (not `simp`; see `evalLog_lift_bind`). -/
theorem evalLog_liftBind (O : X → PMF Y) (x : X) (k : Y → OracleComp X Y α) :
    evalLog O (.liftBind x k) =
      (O x).bind fun y => (evalLog O (k y)).map fun p => (p.1, (x, y) :: p.2) := rfl

@[simp] theorem evalLog_pure_monad (O : X → PMF Y) (a : α) :
    evalLog O (pure a : OracleComp X Y α) = PMF.pure (a, []) := rfl

/-- `evalLog` of one query followed by a continuation, in CSLib's simp normal form. -/
@[simp] theorem evalLog_lift_bind (O : X → PMF Y) (x : X) (k : Y → OracleComp X Y α) :
    evalLog O (PFunctor.FreeM.bind (PFunctor.FreeM.lift x : OracleComp X Y Y) k) =
      (O x).bind fun y => (evalLog O (k y)).map fun p => (p.1, (x, y) :: p.2) := rfl

/-- `evalLog_lift_bind` for the monadic bind (output in the answer universe). -/
@[simp] theorem evalLog_lift_bind' {β : Type v} (O : X → PMF Y) (x : X)
    (k : Y → OracleComp X Y β) :
    evalLog O ((PFunctor.FreeM.lift x : OracleComp X Y Y) >>= k) =
      (O x).bind fun y => (evalLog O (k y)).map fun p => (p.1, (x, y) :: p.2) := rfl

/-- Forgetting the transcript of `evalLog` gives `evalPMF`. -/
theorem evalLog_map_fst (O : X → PMF Y) :
    ∀ c : OracleComp X Y α, (evalLog O c).map Prod.fst = FreeM.evalPMF O c
  | .pure _ => by simp [evalLog, FreeM.evalPMF, PMF.pure_map]
  | .liftBind x k => by
    simp only [evalLog, FreeM.evalPMF, PMF.map_bind, PMF.map_comp]
    congr 1
    funext y
    exact evalLog_map_fst O (k y)

/-- Every transcript of a `q`-bounded algorithm has at most `q` entries, against any randomized
oracle. -/
theorem length_le_of_mem_support_evalLog (O : X → PMF Y) :
    ∀ {q : ℕ} {c : OracleComp X Y α}, FreeM.IsQueryBounded q c →
      ∀ p ∈ (evalLog O c).support, p.2.length ≤ q
  | _, .pure _, _, p, hp => by
    simp only [evalLog, PMF.support_pure, Set.mem_singleton_iff] at hp
    simp [hp]
  | 0, .liftBind _ _, hc, _, _ => hc.elim
  | _ + 1, .liftBind x k, hc, p, hp => by
    simp only [evalLog, PMF.mem_support_bind_iff, PMF.support_map, Set.mem_image] at hp
    obtain ⟨y, -, p', hp', rfl⟩ := hp
    simpa using length_le_of_mem_support_evalLog O (hc y) p' hp'

end OracleComp

/-! ### Stateful deterministic oracles -/

namespace OracleComp

section Stateful

variable {X : Type u} {Y : Type v} {α : Type w}

/-- Run an oracle computation against a **stateful deterministic oracle** whose state is the query
counter: the query `x` asked when the counter is `i` is answered by `s i x`. Starting from counter
`i`, `runStateful s i c` returns the output and the transcript of `(query, answer)` pairs; this is
how a stateful signer (Katz and Lindell, Section 12.6) is run in a forgery experiment. Each answer
and the recursive run are computed once, so a run costs work linear in the number of queries.

Relation to `runState` (`CSLibExt.Crypto.Framework.LazySampling`, and the function of the same
name in the open random-oracle pull request): `runState` runs against a randomized oracle with an
arbitrary state and returns a `PMF` of the output and final state, while `runStateful` is
deterministic, fixes the state to the counter and returns the transcript. Whoever unifies the
stateful runners in Wave 3 can derive this one as the deterministic, transcript-logging case. -/
def runStateful (s : ℕ → X → Y) : ℕ → OracleComp X Y α → α × List (X × Y)
  | _, .pure a => (a, [])
  | i, .liftBind x k =>
    let y := s i x
    let r := runStateful s (i + 1) (k y)
    (r.1, (x, y) :: r.2)

/-- The query asked when the counter is `j`, if any, in the run of `runStateful s i`. -/
def queryAt (s : ℕ → X → Y) : ℕ → OracleComp X Y α → ℕ → Option X
  | _, .pure _, _ => none
  | i, .liftBind m k, j => if i = j then some m else queryAt s (i + 1) (k (s i m)) j

/-- No query is asked at a counter value already passed. -/
theorem queryAt_eq_none_of_lt (s : ℕ → X → Y) {j : ℕ} :
    ∀ (i : ℕ) (c : OracleComp X Y α), j < i → queryAt s i c j = none
  | _, .pure _, _ => rfl
  | i, .liftBind m k, hji => by
    have hij : i ≠ j := by omega
    simp only [queryAt, hij, ↓reduceIte]
    exact queryAt_eq_none_of_lt s (i + 1) (k (s i m)) (by omega)

/-- The query at counter `j` only depends on the oracle's answers at earlier counter values. -/
theorem queryAt_congr {s s' : ℕ → X → Y} {j : ℕ} (hs : ∀ i < j, ∀ m, s i m = s' i m) :
    ∀ (i : ℕ) (c : OracleComp X Y α), i ≤ j → queryAt s i c j = queryAt s' i c j
  | _, .pure _, _ => rfl
  | i, .liftBind m k, hij => by
    by_cases hj : i = j
    · simp only [queryAt, hj, ↓reduceIte]
    · simp only [queryAt, hj, ↓reduceIte, hs i (by omega) m]
      exact queryAt_congr hs (i + 1) (k (s' i m)) (by omega)

/-- **Locality of stateful runs**: two stateful oracles that agree at every counter value except
`j`, and at `j` on the query actually asked there, give the same run. -/
theorem runStateful_congr {s s' : ℕ → X → Y} {j : ℕ} (hs : ∀ i m, i ≠ j → s i m = s' i m) :
    ∀ (i : ℕ) (c : OracleComp X Y α), (∀ m, queryAt s i c j = some m → s j m = s' j m) →
      runStateful s i c = runStateful s' i c
  | _, .pure _, _ => rfl
  | i, .liftBind m k, hq => by
    have hsm : s i m = s' i m := by
      by_cases hij : i = j
      · subst hij
        exact hq m (by simp [queryAt])
      · exact hs i m hij
    have hq' : ∀ m', queryAt s (i + 1) (k (s i m)) j = some m' → s j m' = s' j m' := by
      intro m' hm'
      by_cases hij : i = j
      · rw [queryAt_eq_none_of_lt s (i + 1) _ (by omega)] at hm'
        exact absurd hm' (by simp)
      · exact hq m' (by simp only [queryAt, hij, ↓reduceIte]; exact hm')
    have ih := runStateful_congr hs (i + 1) (k (s i m)) hq'
    simp only [runStateful, ← hsm, ih]

/-- The query asked at counter `j` appears in the transcript. -/
theorem mem_of_queryAt (s : ℕ → X → Y) {j : ℕ} {m : X} :
    ∀ (i : ℕ) (c : OracleComp X Y α), queryAt s i c j = some m →
      m ∈ (runStateful s i c).2.map Prod.fst
  | _, .pure _, h => by simp [queryAt] at h
  | i, .liftBind m' k, h => by
    simp only [runStateful, List.map_cons, List.mem_cons]
    by_cases hij : i = j
    · simp only [queryAt, hij, ↓reduceIte, Option.some.injEq] at h
      exact Or.inl h.symm
    · simp only [queryAt, hij, ↓reduceIte] at h
      exact Or.inr (mem_of_queryAt s (i + 1) (k (s i m')) h)

end Stateful

end OracleComp

/-! ### Simulating a randomized oracle from presampled coins -/

/-- A uniform function on `Fin (n + 1)` is a uniform head followed by an independent uniform
tail. Private: open PR #9482 adds the same statement publicly as
`Cslib.Crypto.Framework.uniformOfFintype_fin_succ` (`Framework/RandomOracle.lean`); once it
merges, this copy can be replaced by that one. -/
private theorem uniformOfFintype_fin_succ (X : Type*) [Fintype X] [Nonempty X] (n : ℕ) :
    Cslib.Probability.PMF.uniformOfFintype (Fin (n + 1) → X) =
      (Cslib.Probability.PMF.uniformOfFintype X).bind fun x =>
        (Cslib.Probability.PMF.uniformOfFintype (Fin n → X)).map (Fin.cons x) := by
  let e : X × (Fin n → X) ≃ (Fin (n + 1) → X) :=
    { toFun := fun p => Fin.cons p.1 p.2
      invFun := fun f => (f 0, Fin.tail f)
      left_inv := fun p => by simp
      right_inv := fun f => by simp }
  rw [← Cslib.Probability.PMF.uniformOfFintype_map_equiv e,
    ← Cslib.Probability.PMF.uniformOfFintype_prod, PMF.map_bind]
  congr 1
  funext x
  rw [PMF.map_comp]
  rfl

namespace OracleComp

variable {X : Type u} {Y : Type v} {α : Type w} {Rnd : Type*}

/-- Run an oracle computation against the randomized oracle `x ↦ O x ρ` on presampled coins:
the `i`-th query is answered with the `i`-th coin of the list (and with `default` once the list
is exhausted). A reduction that answers its adversary's encryption queries itself does this
(Katz and Lindell, proof of Proposition 11.3). -/
def runCoins [Inhabited Rnd] (O : X → Rnd → Y) : OracleComp X Y α → List Rnd → α
  | .pure a, _ => a
  | .liftBind x k, [] => runCoins O (k (O x default)) []
  | .liftBind x k, ρ :: ρs => runCoins O (k (O x ρ)) ρs

/-- **Presampling the oracle's coins**: a computation making at most `n` queries, run on `n`
uniform coins, has the distribution of the same computation run against the randomized oracle
`x ↦ O x ρ` with fresh uniform `ρ` per query. -/
theorem map_runCoins [Fintype Rnd] [Nonempty Rnd] [Inhabited Rnd] (O : X → Rnd → Y) :
    ∀ {n : ℕ} {c : OracleComp X Y α}, FreeM.IsQueryBounded n c →
      (Cslib.Probability.PMF.uniformOfFintype (Fin n → Rnd)).map
          (fun f => runCoins O c (List.ofFn f)) =
        FreeM.evalPMF (fun x => (Cslib.Probability.PMF.uniformOfFintype Rnd).map (O x)) c
  | _, .pure a, _ => by
    rw [FreeM.evalPMF_pure']
    exact PMF.map_const _ a
  | 0, .liftBind _ _, hc => hc.elim
  | n + 1, .liftBind x k, hc => by
    rw [FreeM.evalPMF_liftBind, PMF.bind_map, uniformOfFintype_fin_succ, PMF.map_bind]
    congr 1
    funext ρ
    rw [PMF.map_comp, Function.comp_def, Function.comp_def]
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
    exact map_runCoins O (hc (O x ρ))

/-- The output of a two-phase computation run on presampled coins satisfies the continuation
bound for some budget `j ≤ n`. -/
theorem exists_cont_runCoins [Inhabited Rnd] (O : X → Rnd → Y) {cont : α → ℕ → Prop} :
    ∀ {n : ℕ} {c : OracleComp X Y α}, FreeM.IsQueryBoundedWith cont n c →
      ∀ ρs : List Rnd, ∃ j ≤ n, cont (runCoins O c ρs) j
  | n, .pure a, hc, _ => ⟨n, le_rfl, hc⟩
  | 0, .liftBind _ _, hc, _ => hc.elim
  | n + 1, .liftBind x k, hc, [] => by
    obtain ⟨j, hj, h⟩ := exists_cont_runCoins O (hc (O x default)) []
    exact ⟨j, by omega, h⟩
  | n + 1, .liftBind x k, hc, ρ :: ρs => by
    obtain ⟨j, hj, h⟩ := exists_cont_runCoins O (hc (O x ρ)) ρs
    exact ⟨j, by omega, h⟩

end OracleComp

end Cslib.Crypto.Framework
