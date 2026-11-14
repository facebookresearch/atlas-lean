/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Games

/-!
# Monadic adversaries: sampling as an operation

The adversaries of `CSLibExt.Crypto.Framework.Games` draw all their randomness up front
(`coins : PMF R`) and are otherwise deterministic oracle algorithms. This file adds the
**monadic** form, in which an adversary samples whenever it likes: sampling is one more kind of
operation of the free monad, next to the oracle queries. Every coin adversary is the special case
that samples once at the start (`ofCoins`), and the `ofCoins` equalities show that the monadic
games agree with the coin games on it. The two forms coexist; nothing in `Games` changes.

* `SampleFam.{u}`: a family of sampling operations, `i : ι` returning `B i` with distribution
  `dist i`. `coinFam μ` is the one-operation family drawing from `μ`.
* `WithSample Smp P`: the signature `P` extended by the sampling operations of `Smp`, and
  `withSampleOracle Smp O` the randomized oracle answering sampling operations by `Smp.dist` and
  queries by `O`; `FreeM.evalPMF` then interprets monadic adversaries unchanged.
* `sampleThen i k` (sample from `dist i`, continue with `k`), `queryThen a k`, and
  `embed : P.FreeM α → (WithSample Smp P).FreeM α`, with `evalPMF_embed`: an embedded
  computation that never samples has the same output distribution.
* `mEvalLog`: the transcript semantics of `OracleComp.evalLog`, recording oracle queries only.
* `FreeM.CostBoundedWith costly`: the two-phase bound of `FreeM.IsQueryBoundedWith`, counting only
  the operations selected by `costly`. `OracleBoundedWith` counts oracle queries (sampling free),
  `SampleBoundedWith` counts sampling operations (queries free).
* Monadic adversaries `MCPAAdversary`, `MCCAAdversary`, `MPubCCAAdversary`, `MMACForger`,
  `MSigForger`, their experiments `mCpaExp`, `mCcaExp`, `mPubCcaExp`, `mMacGame`, `mSigGame`, and
  the `ofCoins` equalities `mCpaExp_ofCoins`, `mCcaExp_ofCoins`, `mPubCcaExp_ofCoins`,
  `mMacGame_ofCoins`, `mSigGame_ofCoins`.

**Representation constraints.** The `ofCoins` equalities close by one `simp` call only because of
three choices, which any extension of this file must keep:
1. `WithSample`'s answer family is `Sum.rec Smp.B P.B`, not `Sum.elim`. `Sum.rec` reduces on
   `Sum.inl i` by iota reduction at every transparency; `Sum.elim` is a definition and does not
   unfold at reducible transparency, so continuations `fun r : (WithSample Smp P).B (.inl i) => _`
   are ill-typed for `rw` and `simp`.
2. A sampling step followed by a continuation is the head symbol `sampleThen i k`, with its own
   `simp` lemma `evalPMF_sampleThen`, rather than `lift (.inl i) >>= k`: the generic
   `evalPMF_lift` indexes its result as `P.B a`, which `simp`'s discrimination tree does not match
   against the reduced type.
3. `coinFam` and `WithSample` are `abbrev`s, so their fields reduce at reducible transparency.

**Universes.** One universe `u` holds the messages, ciphertexts, keys, coins and sampling outcomes
of a monadic adversary: `WithSample Smp P` is a `PFunctor.{u, u}` whose operations are a sum
`Smp.ι ⊕ P.A`, so `Smp.ι` and `P.A` (and, through `Sum.rec`, the answer types) share a universe.
This is the restriction `CCAAdversary` already has. The coin form `CPAAdversary M C R` allows three
independent universes; `ofCoins` needs `R : Type u` like `M` and `C`. Because the family `Smp` is
a parameter rather than a field, the monadic adversary types stay in `Type u`.

Katz and Lindell's adversaries are probabilistic algorithms; the coin form gives one its random
tape up front, the monadic form lets it toss coins on demand, and `ofCoins` shows the coin form is
a special case of the monadic one.

**Reductions.** `simulate h c` replaces every oracle query `a` of `c` by a subroutine `h a`,
keeping the sampling steps: the shape of a black-box reduction that runs an adversary and answers
its queries itself. `evalPMF_simulate` (a perfect simulation preserves the output distribution),
`oracleBounded_simulate` (`q * q'` queries) and `sampleBounded_simulate` (`s + q * s'` sampling
steps) are the generic facts from which a polynomial-cost class would show that reductions
preserve polynomial cost. Such a class is future work; it is not part of this repository.

**Migration note.** The monadic games duplicate `cpaExp`, `ccaExp`, `pubCcaExp`, `macGame` and
`sigGame` of `CSLibExt.Crypto.Framework.Games`; the `ofCoins` equalities are the migration
lemmas. A later step may restate the coin games as the `ofCoins` special case.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Section 3.4.2, Definitions 3.22, 3.33, 4.2, 11.8, 12.2.
-/

@[expose] public section

namespace Cslib.Crypto.Framework

open FreeM OracleComp

universe u v w

/-! ### Sampling families -/

/-- A family of sampling operations: operation `i : ι` returns an element of `B i` drawn from
`dist i`. All three live in one universe `u` (see the module docstring). -/
structure SampleFam where
  /-- The sampling operations. -/
  ι : Type u
  /-- The outcome type of each operation. -/
  B : ι → Type u
  /-- The distribution of each operation's outcome. -/
  dist : (i : ι) → PMF (B i)

/-- The family with one sampling operation, drawing from `μ`. An `abbrev`, so its fields reduce at
reducible transparency (constraint 3 of the module docstring). -/
abbrev coinFam {R : Type u} (μ : PMF R) : SampleFam.{u} := ⟨PUnit, fun _ => R, fun _ => μ⟩

/-- The signature `P` extended with the sampling operations of `Smp`: an operation is either a
sampling operation `.inl i` (answered in `Smp.B i`) or an oracle query `.inr a` (answered in
`P.B a`). The answer family uses `Sum.rec` (constraint 1 of the module docstring). -/
abbrev WithSample (Smp : SampleFam.{u}) (P : PFunctor.{u, u}) : PFunctor.{u, u} :=
  ⟨Smp.ι ⊕ P.A, Sum.rec (motive := fun _ => Type u) Smp.B P.B⟩

variable {Smp : SampleFam.{u}} {P : PFunctor.{u, u}}

/-- The randomized oracle of a monadic computation: sampling operations are answered by the
family's distributions, oracle queries by `O`. -/
noncomputable def withSampleOracle (Smp : SampleFam.{u}) (O : (a : P.A) → PMF (P.B a)) :
    (a : (WithSample Smp P).A) → PMF ((WithSample Smp P).B a)
  | .inl i => Smp.dist i
  | .inr a => O a

@[simp] theorem withSampleOracle_inl (O : (a : P.A) → PMF (P.B a)) (i : Smp.ι) :
    withSampleOracle Smp O (.inl i) = Smp.dist i := rfl

@[simp] theorem withSampleOracle_inr (O : (a : P.A) → PMF (P.B a)) (a : P.A) :
    withSampleOracle Smp O (.inr a) = O a := rfl

/-- Sample from `Smp.dist i` and continue with `k`. One head symbol (constraint 2 of the module
docstring); `sampleThen_eq` relates it to the monadic bind. -/
def sampleThen {α : Type w} (i : Smp.ι) (k : Smp.B i → (WithSample Smp P).FreeM α) :
    (WithSample Smp P).FreeM α :=
  .liftBind (Sum.inl i) k

/-- Ask the oracle query `a` and continue with `k`. -/
def queryThen {α : Type w} (a : P.A) (k : P.B a → (WithSample Smp P).FreeM α) :
    (WithSample Smp P).FreeM α :=
  .liftBind (Sum.inr a) k

/-- `sampleThen` is sampling followed by monadic bind. -/
theorem sampleThen_eq {α : Type u} (i : Smp.ι) (k : Smp.B i → (WithSample Smp P).FreeM α) :
    sampleThen i k =
      (PFunctor.FreeM.lift (P := WithSample Smp P) (Sum.inl i) : (WithSample Smp P).FreeM (Smp.B i))
        >>= k :=
  rfl

/-- The output distribution of a sampling step. -/
@[simp] theorem evalPMF_sampleThen {α : Type w} (O : (a : P.A) → PMF (P.B a)) (i : Smp.ι)
    (k : Smp.B i → (WithSample Smp P).FreeM α) :
    evalPMF (withSampleOracle Smp O) (sampleThen i k) =
      (Smp.dist i).bind fun b => evalPMF (withSampleOracle Smp O) (k b) := rfl

/-- The output distribution of a query step. -/
@[simp] theorem evalPMF_queryThen {α : Type w} (O : (a : P.A) → PMF (P.B a)) (a : P.A)
    (k : P.B a → (WithSample Smp P).FreeM α) :
    evalPMF (withSampleOracle Smp O) (queryThen a k) =
      (O a).bind fun b => evalPMF (withSampleOracle Smp O) (k b) := rfl

/-- View a computation that never samples as a monadic one: every query `a` becomes `.inr a`. -/
def embed {α : Type w} : P.FreeM α → (WithSample Smp P).FreeM α
  | .pure x => .pure x
  | .liftBind a k => .liftBind (Sum.inr a) fun b => embed (k b)

@[simp] theorem embed_pure {α : Type w} (x : α) :
    (embed (pure x : P.FreeM α) : (WithSample Smp P).FreeM α) = pure x := rfl

/-- **Embedding preserves the output distribution.** Proved once, by induction, and reused by
every `ofCoins` equality. -/
@[simp] theorem evalPMF_embed {α : Type w} (O : (a : P.A) → PMF (P.B a)) :
    ∀ c : P.FreeM α, evalPMF (withSampleOracle Smp O) (embed c) = evalPMF O c
  | .pure _ => rfl
  | .liftBind a k => by
    change (O a).bind (fun b => evalPMF (withSampleOracle Smp O) (embed (k b))) = _
    simp only [evalPMF_liftBind]
    congr 1
    funext b
    exact evalPMF_embed O (k b)

/-! ### Transcripts -/

section Log

variable {X Y : Type u} {α : Type w}

/-- Run a monadic single-oracle computation against the randomized oracle `O` and record the
transcript of oracle queries with their answers, in order. Sampling steps are not recorded. The
monadic counterpart of `OracleComp.evalLog`. -/
noncomputable def mEvalLog (Smp : SampleFam.{u}) (O : X → PMF Y) :
    (WithSample Smp (OracleSig X Y)).FreeM α → PMF (α × List (X × Y))
  | .pure a => PMF.pure (a, [])
  | .liftBind (.inl i) k => (Smp.dist i).bind fun b => mEvalLog Smp O (k b)
  | .liftBind (.inr x) k =>
    (O x).bind fun y => (mEvalLog Smp O (k y)).map fun p => (p.1, (x, y) :: p.2)

@[simp] theorem mEvalLog_pure (O : X → PMF Y) (a : α) :
    mEvalLog Smp O (pure a : (WithSample Smp (OracleSig X Y)).FreeM α) = PMF.pure (a, []) := rfl

@[simp] theorem mEvalLog_sampleThen (O : X → PMF Y) (i : Smp.ι)
    (k : Smp.B i → (WithSample Smp (OracleSig X Y)).FreeM α) :
    mEvalLog Smp O (sampleThen i k) = (Smp.dist i).bind fun b => mEvalLog Smp O (k b) := rfl

@[simp] theorem mEvalLog_queryThen (O : X → PMF Y) (x : X)
    (k : Y → (WithSample Smp (OracleSig X Y)).FreeM α) :
    mEvalLog Smp O (queryThen x k) =
      (O x).bind fun y => (mEvalLog Smp O (k y)).map fun p => (p.1, (x, y) :: p.2) := rfl

/-- The transcript of an embedded computation is its `evalLog` transcript. -/
@[simp] theorem mEvalLog_embed (O : X → PMF Y) :
    ∀ c : OracleComp X Y α, mEvalLog Smp O (embed c) = evalLog O c
  | .pure _ => rfl
  | .liftBind x k => by
    change (O x).bind (fun y => (mEvalLog Smp O (embed (k y))).map _) = _
    rw [evalLog_liftBind]
    congr 1
    funext y
    rw [mEvalLog_embed O (k y)]

/-- Forgetting the transcript of `mEvalLog` gives `evalPMF`. -/
theorem mEvalLog_map_fst (O : X → PMF Y) :
    ∀ c : (WithSample Smp (OracleSig X Y)).FreeM α,
      (mEvalLog Smp O c).map Prod.fst = evalPMF (withSampleOracle Smp O) c
  | .pure _ => by simp [mEvalLog, evalPMF, PMF.pure_map]
  | .liftBind (.inl i) k => by
    change ((Smp.dist i).bind fun b => mEvalLog Smp O (k b)).map Prod.fst =
      (Smp.dist i).bind fun b => evalPMF (withSampleOracle Smp O) (k b)
    rw [PMF.map_bind]
    congr 1
    funext b
    exact mEvalLog_map_fst O (k b)
  | .liftBind (.inr x) k => by
    change ((O x).bind fun y => (mEvalLog Smp O (k y)).map _).map Prod.fst =
      (O x).bind fun y => evalPMF (withSampleOracle Smp O) (k y)
    simp only [PMF.map_bind, PMF.map_comp]
    congr 1
    funext y
    exact mEvalLog_map_fst O (k y)

end Log

/-! ### Cost bounds -/

namespace FreeM

variable {Q : PFunctor.{v, w}} {α β : Type*}

/-- A two-phase bound counting only the operations selected by `costly`:
`CostBoundedWith costly cont q c` holds when, along every path of `c`, at most `q` operations `a`
with `costly a = true` occur (the others are free) and the output `x` satisfies `cont x j`, where
`j` is the budget left. With `costly = fun _ => true` this is `IsQueryBoundedWith`
(`costBoundedWith_true_iff`). -/
def CostBoundedWith (costly : Q.A → Bool) (cont : α → ℕ → Prop) : ℕ → Q.FreeM α → Prop
  | q, .pure x => cont x q
  | 0, .liftBind a k => costly a = false ∧ ∀ b, CostBoundedWith costly cont 0 (k b)
  | q + 1, .liftBind a k =>
    ∀ b, CostBoundedWith costly cont (if costly a then q else q + 1) (k b)
termination_by structural _ c => c

variable {costly : Q.A → Bool} {cont cont' : α → ℕ → Prop}

/-- `CostBoundedWith` of `pure`. -/
@[simp] theorem costBoundedWith_pure (q : ℕ) (x : α) :
    CostBoundedWith costly cont q (pure x : Q.FreeM α) ↔ cont x q := by
  cases q <;> rfl

/-- `CostBoundedWith` of the constructor `pure` (not `simp`; see `costBoundedWith_pure`). -/
theorem costBoundedWith_pure' (q : ℕ) (x : α) :
    CostBoundedWith costly cont q (.pure x : Q.FreeM α) ↔ cont x q := by
  cases q <;> rfl

/-- A costly operation consumes one unit of budget. -/
theorem costBoundedWith_liftBind_of_costly {a : Q.A} (ha : costly a = true)
    {k : Q.B a → Q.FreeM α} (q : ℕ) :
    CostBoundedWith costly cont (q + 1) (.liftBind a k) ↔
      ∀ b, CostBoundedWith costly cont q (k b) := by
  simp [CostBoundedWith, ha]

/-- A costly operation is not allowed with no budget left. -/
theorem not_costBoundedWith_zero_of_costly {a : Q.A} (ha : costly a = true)
    {k : Q.B a → Q.FreeM α} : ¬ CostBoundedWith costly cont 0 (.liftBind a k) := by
  simp [CostBoundedWith, ha]

/-- A free operation consumes no budget. -/
theorem costBoundedWith_liftBind_of_free {a : Q.A} (ha : costly a = false)
    {k : Q.B a → Q.FreeM α} (q : ℕ) :
    CostBoundedWith costly cont q (.liftBind a k) ↔
      ∀ b, CostBoundedWith costly cont q (k b) := by
  cases q <;> simp [CostBoundedWith, ha]

/-- Counting every operation recovers `IsQueryBoundedWith`. -/
theorem costBoundedWith_true_iff :
    ∀ {q : ℕ} {c : Q.FreeM α},
      CostBoundedWith (fun _ => true) cont q c ↔ IsQueryBoundedWith cont q c
  | q, .pure x => by cases q <;> rfl
  | 0, .liftBind a k => by simp [CostBoundedWith, IsQueryBoundedWith]
  | q + 1, .liftBind a k => by
    simp only [CostBoundedWith, ite_true, IsQueryBoundedWith]
    exact forall_congr' fun b => costBoundedWith_true_iff

/-- A cost bound with a weaker continuation condition still holds. -/
theorem CostBoundedWith.mono_cont (h : ∀ x j, cont x j → cont' x j) :
    ∀ {q : ℕ} {c : Q.FreeM α}, CostBoundedWith costly cont q c →
      CostBoundedWith costly cont' q c
  | q, .pure x, hc => by cases q <;> exact h x _ hc
  | 0, .liftBind _ _, hc => ⟨hc.1, fun b => CostBoundedWith.mono_cont h (hc.2 b)⟩
  | _ + 1, .liftBind _ _, hc => fun b => CostBoundedWith.mono_cont h (hc b)

/-- Cost bounds are monotone in the budget, for a continuation condition monotone in the
budget. -/
theorem CostBoundedWith.mono (hcont : ∀ x j j', j ≤ j' → cont x j → cont x j') :
    ∀ {q q' : ℕ} {c : Q.FreeM α}, q ≤ q' → CostBoundedWith costly cont q c →
      CostBoundedWith costly cont q' c
  | q, q', .pure x, hq, hc => by
    cases q <;> cases q' <;> exact hcont x _ _ hq hc
  | q, q', .liftBind a k, hq, hc => by
    cases ha : costly a
    · rw [costBoundedWith_liftBind_of_free ha] at hc ⊢
      exact fun b => CostBoundedWith.mono hcont hq (hc b)
    · obtain ⟨q₀, rfl⟩ : ∃ q₀, q = q₀ + 1 := by
        cases q with
        | zero => exact absurd hc (not_costBoundedWith_zero_of_costly ha)
        | succ q₀ => exact ⟨q₀, rfl⟩
      obtain ⟨q₁, rfl⟩ : ∃ q₁, q' = q₁ + 1 := ⟨q' - 1, by omega⟩
      rw [costBoundedWith_liftBind_of_costly ha] at hc ⊢
      exact fun b => CostBoundedWith.mono hcont (by omega) (hc b)

/-- **Sequential composition**: if `c` stays within budget `q` and leaves budget `j` at an output
`x` from which `f x` stays within `j`, then `c >>= f` stays within `q`. No loss. -/
theorem CostBoundedWith.bind {cont : β → ℕ → Prop} {f : α → Q.FreeM β} :
    ∀ {q : ℕ} {c : Q.FreeM α},
      CostBoundedWith costly (fun x j => CostBoundedWith costly cont j (f x)) q c →
        CostBoundedWith costly cont q (PFunctor.FreeM.bind c f)
  | q, .pure x, hc => by
    cases q <;> exact hc
  | 0, .liftBind _ _, hc => ⟨hc.1, fun b => CostBoundedWith.bind (hc.2 b)⟩
  | _ + 1, .liftBind _ _, hc => fun b => CostBoundedWith.bind (hc b)

/-- Mapping the output: the continuation condition is checked on the mapped output. -/
theorem CostBoundedWith.map {cont : β → ℕ → Prop} {f : α → β} :
    ∀ {q : ℕ} {c : Q.FreeM α}, CostBoundedWith costly (fun x j => cont (f x) j) q c →
      CostBoundedWith costly cont q (PFunctor.FreeM.map f c)
  | q, .pure x, hc => by
    cases q <;> exact hc
  | 0, .liftBind _ _, hc => ⟨hc.1, fun b => CostBoundedWith.map (hc.2 b)⟩
  | _ + 1, .liftBind _ _, hc => fun b => CostBoundedWith.map (hc b)

/-- A computation within budget `q` with no continuation condition fits budget `q + r` with any
continuation condition that holds whenever at least `r` is left. -/
theorem CostBoundedWith.add_right {r : ℕ} (hcont : ∀ x j, r ≤ j → cont x j) :
    ∀ {q : ℕ} {c : Q.FreeM α}, CostBoundedWith costly (fun _ _ => True) q c →
      CostBoundedWith costly cont (q + r) c
  | q, .pure x, _ => (costBoundedWith_pure' _ x).mpr (hcont x _ (Nat.le_add_left r q))
  | q, .liftBind a k, hc => by
    cases ha : costly a
    · rw [costBoundedWith_liftBind_of_free ha] at hc ⊢
      exact fun b => CostBoundedWith.add_right hcont (hc b)
    · obtain ⟨q₀, rfl⟩ : ∃ q₀, q = q₀ + 1 := by
        cases q with
        | zero => exact absurd hc (not_costBoundedWith_zero_of_costly ha)
        | succ q₀ => exact ⟨q₀, rfl⟩
      rw [show q₀ + 1 + r = (q₀ + r) + 1 by omega, costBoundedWith_liftBind_of_costly ha]
      rw [costBoundedWith_liftBind_of_costly ha] at hc
      exact fun b => CostBoundedWith.add_right hcont (hc b)

/-- Bounds without a continuation condition are monotone in the budget. -/
theorem CostBoundedWith.mono_true {q q' : ℕ} {c : Q.FreeM α} (hq : q ≤ q')
    (hc : CostBoundedWith costly (fun _ _ => True) q c) :
    CostBoundedWith costly (fun _ _ => True) q' c :=
  CostBoundedWith.mono (fun _ _ _ _ _ => trivial) hq hc

end FreeM

/-- `OracleBoundedWith cont q c`: along every path, the monadic computation `c` makes at most `q`
**oracle queries**; sampling steps are free. The output `x` satisfies `cont x j` for the budget
`j` left (the two-phase form of `IsQueryBoundedWith`). Counting sampling steps as queries would
make a coin-tossing adversary look expensive; `SampleBoundedWith` counts those separately. -/
abbrev OracleBoundedWith {α : Type w} (cont : α → ℕ → Prop) (q : ℕ)
    (c : (WithSample Smp P).FreeM α) : Prop :=
  FreeM.CostBoundedWith Sum.isRight cont q c

/-- At most `q` oracle queries along every path; sampling is free. -/
abbrev OracleBounded {α : Type w} (q : ℕ) (c : (WithSample Smp P).FreeM α) : Prop :=
  OracleBoundedWith (fun _ _ => True) q c

/-- `SampleBoundedWith cont s c`: along every path, the monadic computation `c` makes at most `s`
**sampling steps**; oracle queries are free (they are counted by `OracleBoundedWith`). -/
abbrev SampleBoundedWith {α : Type w} (cont : α → ℕ → Prop) (s : ℕ)
    (c : (WithSample Smp P).FreeM α) : Prop :=
  FreeM.CostBoundedWith Sum.isLeft cont s c

/-- At most `s` sampling steps along every path; queries are free. -/
abbrev SampleBounded {α : Type w} (s : ℕ) (c : (WithSample Smp P).FreeM α) : Prop :=
  SampleBoundedWith (fun _ _ => True) s c

/-- Oracle bounds are monotone in the budget. -/
theorem OracleBounded.mono {α : Type w} {q q' : ℕ} {c : (WithSample Smp P).FreeM α}
    (hq : q ≤ q') (h : OracleBounded q c) : OracleBounded q' c :=
  FreeM.CostBoundedWith.mono_true hq h

/-- Sampling bounds are monotone in the budget. -/
theorem SampleBounded.mono {α : Type w} {s s' : ℕ} {c : (WithSample Smp P).FreeM α}
    (hs : s ≤ s') (h : SampleBounded s c) : SampleBounded s' c :=
  FreeM.CostBoundedWith.mono_true hs h

/-- An embedded computation makes as many oracle queries as the original. -/
theorem oracleBoundedWith_embed {α : Type w} {cont : α → ℕ → Prop} {cont' : α → ℕ → Prop}
    (h : ∀ x j, cont x j → cont' x j) :
    ∀ {q : ℕ} {c : P.FreeM α}, IsQueryBoundedWith cont q c →
      OracleBoundedWith (Smp := Smp) cont' q (embed c)
  | q, .pure x, hc => by cases q <;> exact h x _ hc
  | 0, .liftBind _ _, hc => hc.elim
  | _ + 1, .liftBind _ _, hc => fun b => oracleBoundedWith_embed h (hc b)

/-- An embedded computation makes no sampling step. -/
theorem sampleBoundedWith_embed {α : Type w} {cont : α → ℕ → Prop} {s : ℕ} (h : ∀ x, cont x s) :
    ∀ c : P.FreeM α, SampleBoundedWith (Smp := Smp) cont s (embed c)
  | .pure x => by cases s <;> exact h x
  | .liftBind a k => by
    change FreeM.CostBoundedWith Sum.isLeft cont s (.liftBind (Sum.inr a) fun b => embed (k b))
    exact (FreeM.costBoundedWith_liftBind_of_free rfl s).mpr fun b =>
      sampleBoundedWith_embed h (k b)

/-- One sampling step followed by computations within query budget `q` stays within `q`. -/
theorem oracleBoundedWith_sampleThen {α : Type w} {cont : α → ℕ → Prop} {q : ℕ} {i : Smp.ι}
    {k : Smp.B i → (WithSample Smp P).FreeM α} (h : ∀ b, OracleBoundedWith cont q (k b)) :
    OracleBoundedWith cont q (sampleThen i k) :=
  (FreeM.costBoundedWith_liftBind_of_free rfl q).mpr h

/-- One sampling step costs one unit of sampling budget. -/
theorem sampleBoundedWith_sampleThen {α : Type w} {cont : α → ℕ → Prop} {s : ℕ} {i : Smp.ι}
    {k : Smp.B i → (WithSample Smp P).FreeM α} (h : ∀ b, SampleBoundedWith cont s (k b)) :
    SampleBoundedWith cont (s + 1) (sampleThen i k) :=
  (FreeM.costBoundedWith_liftBind_of_costly rfl s).mpr h

/-! ### Simulating an oracle by a subroutine -/

section Simulate

variable {Q : PFunctor.{u, u}} {α : Type w}

/-- Replace every oracle query `a` of a monadic computation over `P` by the monadic subroutine
`h a` over `Q`, keeping the sampling steps. This is the shape of a black-box reduction that runs
an adversary and answers its queries itself. -/
def simulate (h : (a : P.A) → (WithSample Smp Q).FreeM (P.B a)) :
    (WithSample Smp P).FreeM α → (WithSample Smp Q).FreeM α
  | .pure x => .pure x
  | .liftBind (.inl i) k => sampleThen i fun b => simulate h (k b)
  | .liftBind (.inr a) k => PFunctor.FreeM.bind (h a) fun b => simulate h (k b)

/-- **Simulation is perfect** when every subroutine has the distribution of the oracle answer it
replaces. -/
theorem evalPMF_simulate {h : (a : P.A) → (WithSample Smp Q).FreeM (P.B a)}
    {O : (a : P.A) → PMF (P.B a)} {O' : (a : Q.A) → PMF (Q.B a)}
    (hO : ∀ a, evalPMF (withSampleOracle Smp O') (h a) = O a) :
    ∀ c : (WithSample Smp P).FreeM α,
      evalPMF (withSampleOracle Smp O') (simulate h c) = evalPMF (withSampleOracle Smp O) c
  | .pure _ => rfl
  | .liftBind (.inl i) k => by
    change (Smp.dist i).bind (fun b => evalPMF _ (simulate h (k b))) =
      (Smp.dist i).bind fun b => evalPMF _ (k b)
    congr 1
    funext b
    exact evalPMF_simulate hO (k b)
  | .liftBind (.inr a) k => by
    change evalPMF _ (PFunctor.FreeM.bind (h a) fun b => simulate h (k b)) =
      (O a).bind fun b => evalPMF _ (k b)
    rw [evalPMF_freeMBind, hO]
    congr 1
    funext b
    exact evalPMF_simulate hO (k b)

/-- **Query cost of a simulation**: `q` queries, each answered by a subroutine of at most `q'`
queries, cost at most `q * q'` queries. -/
theorem oracleBounded_simulate {h : (a : P.A) → (WithSample Smp Q).FreeM (P.B a)} {q' : ℕ}
    (hh : ∀ a, OracleBounded q' (h a)) :
    ∀ {q : ℕ} {c : (WithSample Smp P).FreeM α}, OracleBounded q c →
      OracleBounded (q * q') (simulate h c)
  | q, .pure _, _ => by cases q * q' <;> trivial
  | q, .liftBind (.inl i) k, hc => by
    have hc := (FreeM.costBoundedWith_liftBind_of_free (Q := WithSample Smp P)
      (cont := fun _ _ => True) (costly := Sum.isRight) (a := Sum.inl i) (k := k) rfl q).mp hc
    exact oracleBoundedWith_sampleThen fun b => oracleBounded_simulate hh (hc b)
  | q, .liftBind (.inr a) k, hc => by
    obtain ⟨q₀, rfl⟩ : ∃ q₀, q = q₀ + 1 := by
      cases q with
      | zero => exact absurd hc (FreeM.not_costBoundedWith_zero_of_costly rfl)
      | succ q₀ => exact ⟨q₀, rfl⟩
    have hc := (FreeM.costBoundedWith_liftBind_of_costly (Q := WithSample Smp P)
      (cont := fun _ _ => True) (costly := Sum.isRight) (a := Sum.inr a) (k := k) rfl q₀).mp hc
    rw [show (q₀ + 1) * q' = q' + q₀ * q' by rw [Nat.succ_mul, Nat.add_comm]]
    change OracleBounded _ (PFunctor.FreeM.bind (h a) fun b => simulate h (k b))
    refine FreeM.CostBoundedWith.bind (FreeM.CostBoundedWith.add_right ?_ (hh a))
    exact fun b j hj => FreeM.CostBoundedWith.mono_true hj (oracleBounded_simulate hh (hc b))

/-- **Sampling cost of a simulation**: a computation with at most `q` queries and `s` sampling
steps, whose queries are answered by subroutines of at most `s'` sampling steps, makes at most
`s + q * s'` sampling steps. -/
theorem sampleBounded_simulate {h : (a : P.A) → (WithSample Smp Q).FreeM (P.B a)} {s' : ℕ}
    (hh : ∀ a, SampleBounded s' (h a)) :
    ∀ {q s : ℕ} {c : (WithSample Smp P).FreeM α}, OracleBounded q c → SampleBounded s c →
      SampleBounded (s + q * s') (simulate h c)
  | q, s, .pure _, _, _ => by cases s + q * s' <;> trivial
  | q, s, .liftBind (.inl i) k, hq, hs => by
    have hq := (FreeM.costBoundedWith_liftBind_of_free (Q := WithSample Smp P)
      (cont := fun _ _ => True) (costly := Sum.isRight) (a := Sum.inl i) (k := k) rfl q).mp hq
    obtain ⟨s₀, rfl⟩ : ∃ s₀, s = s₀ + 1 := by
      cases s with
      | zero => exact absurd hs (FreeM.not_costBoundedWith_zero_of_costly rfl)
      | succ s₀ => exact ⟨s₀, rfl⟩
    have hs := (FreeM.costBoundedWith_liftBind_of_costly (Q := WithSample Smp P)
      (cont := fun _ _ => True) (costly := Sum.isLeft) (a := Sum.inl i) (k := k) rfl s₀).mp hs
    rw [show s₀ + 1 + q * s' = (s₀ + q * s') + 1 by omega]
    exact sampleBoundedWith_sampleThen fun b => sampleBounded_simulate hh (hq b) (hs b)
  | q, s, .liftBind (.inr a) k, hq, hs => by
    obtain ⟨q₀, rfl⟩ : ∃ q₀, q = q₀ + 1 := by
      cases q with
      | zero => exact absurd hq (FreeM.not_costBoundedWith_zero_of_costly rfl)
      | succ q₀ => exact ⟨q₀, rfl⟩
    have hq := (FreeM.costBoundedWith_liftBind_of_costly (Q := WithSample Smp P)
      (cont := fun _ _ => True) (costly := Sum.isRight) (a := Sum.inr a) (k := k) rfl q₀).mp hq
    have hs := (FreeM.costBoundedWith_liftBind_of_free (Q := WithSample Smp P)
      (cont := fun _ _ => True) (costly := Sum.isLeft) (a := Sum.inr a) (k := k) rfl s).mp hs
    rw [show s + (q₀ + 1) * s' = s' + (s + q₀ * s') by rw [Nat.succ_mul]; omega]
    change SampleBounded _ (PFunctor.FreeM.bind (h a) fun b => simulate h (k b))
    refine FreeM.CostBoundedWith.bind (FreeM.CostBoundedWith.add_right ?_ (hh a))
    exact fun b j hj =>
      FreeM.CostBoundedWith.mono_true hj (sampleBounded_simulate hh (hq b) (hs b))

end Simulate

/-! ### Monadic adversaries and their games -/

section CPA

variable {M C R : Type u} {K : Type*}

/-- A monadic chosen-plaintext adversary (Katz and Lindell, Definition 3.22) with sampling
operations `Smp`: a computation with the encryption oracle that may sample at any point, and
outputs the two challenge messages and the second stage. The monadic form of `CPAAdversary`. -/
structure MCPAAdversary (Smp : SampleFam.{u}) (M C : Type u) where
  /-- The two stages. -/
  run : (WithSample Smp (OracleSig M C)).FreeM
    ((M × M) × (C → (WithSample Smp (OracleSig M C)).FreeM Bool))

/-- At most `q` encryption queries over both stages, along every path; sampling is free. -/
def MCPAAdversary.OracleBounded (q : ℕ) (A : MCPAAdversary Smp M C) : Prop :=
  OracleBoundedWith (fun out j => ∀ c, Framework.OracleBounded j (out.2 c)) q A.run

/-- At most `s` sampling steps over both stages, along every path. -/
def MCPAAdversary.SampleBounded (s : ℕ) (A : MCPAAdversary Smp M C) : Prop :=
  SampleBoundedWith (fun out j => ∀ c, Framework.SampleBounded j (out.2 c)) s A.run

/-- The monadic CPA experiment with challenge bit `b`: `cpaExp` with the adversary's sampling
answered by `Smp`. -/
noncomputable def mCpaExp (S : SymmEncScheme M K C) (A : MCPAAdversary Smp M C) (b : Bool) :
    PMF Bool :=
  S.gen.bind fun k =>
    (evalPMF (withSampleOracle Smp (S.enc k)) A.run).bind fun out =>
      (S.enc k (pick out.1 b)).bind fun c => evalPMF (withSampleOracle Smp (S.enc k)) (out.2 c)

/-- **`PrivK^cpa`** for monadic adversaries (Katz and Lindell, Definition 3.22). -/
noncomputable def mCpaGame (S : SymmEncScheme M K C) (A : MCPAAdversary Smp M C) : PMF Bool :=
  bitGame (mCpaExp S A)

/-- The monadic CPA advantage. -/
noncomputable def mCpaAdvantage (S : SymmEncScheme M K C) (A : MCPAAdversary Smp M C) : ℝ :=
  guessAdvantage (mCpaGame S A)

/-- A coin adversary as a monadic one: sample the coins once, then run. -/
def MCPAAdversary.ofCoins (A : CPAAdversary M C R) : MCPAAdversary (coinFam A.coins) M C :=
  ⟨sampleThen PUnit.unit fun r =>
    (fun out => (out.1, fun c => embed (out.2 c))) <$> embed (A.run r)⟩

/-- **The CPA `ofCoins` equality**: the monadic experiment of the embedded adversary is the coin
experiment. -/
@[simp] theorem mCpaExp_ofCoins (S : SymmEncScheme M K C) (A : CPAAdversary M C R) (b : Bool) :
    mCpaExp S (MCPAAdversary.ofCoins A) b = cpaExp S A b := by
  simp [mCpaExp, cpaExp, MCPAAdversary.ofCoins, Function.comp_def]

/-- The CPA advantage is unchanged by the embedding. -/
@[simp] theorem mCpaAdvantage_ofCoins (S : SymmEncScheme M K C) (A : CPAAdversary M C R) :
    mCpaAdvantage S (MCPAAdversary.ofCoins A) = cpaAdvantage S A := by
  rw [mCpaAdvantage, mCpaGame, cpaAdvantage, cpaGame, funext (mCpaExp_ofCoins S A)]

/-- The embedding keeps the query bound. -/
theorem MCPAAdversary.oracleBounded_ofCoins {q : ℕ} {A : CPAAdversary M C R}
    (h : A.QueryBounded q) : (MCPAAdversary.ofCoins A).OracleBounded q :=
  oracleBoundedWith_sampleThen fun r => FreeM.CostBoundedWith.map <|
    oracleBoundedWith_embed (fun _ _ hx c => oracleBoundedWith_embed (fun _ _ _ => trivial)
      (hx c)) (h r)

/-- The embedding samples once. -/
theorem MCPAAdversary.sampleBounded_ofCoins (A : CPAAdversary M C R) :
    (MCPAAdversary.ofCoins A).SampleBounded 1 :=
  sampleBoundedWith_sampleThen fun _ => FreeM.CostBoundedWith.map <|
    sampleBoundedWith_embed (fun _ _ => sampleBoundedWith_embed (fun _ => trivial) _) _

end CPA

section CCA

variable {M K C R : Type u} [DecidableEq C]

/-- A monadic chosen-ciphertext adversary (Katz and Lindell, Definition 3.33): the monadic form of
`CCAAdversary`. -/
structure MCCAAdversary (Smp : SampleFam.{u}) (M C : Type u) where
  /-- The two stages. -/
  run : (WithSample Smp (CCASig M C)).FreeM
    ((M × M) × (C → (WithSample Smp (CCASig M C)).FreeM Bool))

/-- At most `q` oracle queries (encryption and decryption) over both stages; sampling is free. -/
def MCCAAdversary.OracleBounded (q : ℕ) (A : MCCAAdversary Smp M C) : Prop :=
  OracleBoundedWith (fun out j => ∀ c, Framework.OracleBounded j (out.2 c)) q A.run

/-- The monadic CCA experiment with challenge bit `b`. -/
noncomputable def mCcaExp (S : SymmEncScheme M K C) (A : MCCAAdversary Smp M C) (b : Bool) :
    PMF Bool :=
  S.gen.bind fun k =>
    (evalPMF (withSampleOracle Smp (ccaOracle S k none)) A.run).bind fun out =>
      (S.enc k (pick out.1 b)).bind fun c =>
        evalPMF (withSampleOracle Smp (ccaOracle S k (some c))) (out.2 c)

/-- **`PrivK^cca`** for monadic adversaries (Katz and Lindell, Definition 3.33). -/
noncomputable def mCcaGame (S : SymmEncScheme M K C) (A : MCCAAdversary Smp M C) : PMF Bool :=
  bitGame (mCcaExp S A)

/-- The monadic CCA advantage. -/
noncomputable def mCcaAdvantage (S : SymmEncScheme M K C) (A : MCCAAdversary Smp M C) : ℝ :=
  guessAdvantage (mCcaGame S A)

/-- A coin CCA adversary as a monadic one: sample the coins once, then run. -/
def MCCAAdversary.ofCoins (A : CCAAdversary M C R) : MCCAAdversary (coinFam A.coins) M C :=
  ⟨sampleThen PUnit.unit fun r =>
    (fun out => (out.1, fun c => embed (out.2 c))) <$> embed (A.run r)⟩

/-- **The CCA `ofCoins` equality.** -/
@[simp] theorem mCcaExp_ofCoins (S : SymmEncScheme M K C) (A : CCAAdversary M C R) (b : Bool) :
    mCcaExp S (MCCAAdversary.ofCoins A) b = ccaExp S A b := by
  simp [mCcaExp, ccaExp, MCCAAdversary.ofCoins, Function.comp_def]

/-- The CCA advantage is unchanged by the embedding. -/
@[simp] theorem mCcaAdvantage_ofCoins (S : SymmEncScheme M K C) (A : CCAAdversary M C R) :
    mCcaAdvantage S (MCCAAdversary.ofCoins A) = ccaAdvantage S A := by
  rw [mCcaAdvantage, mCcaGame, ccaAdvantage, ccaGame, funext (mCcaExp_ofCoins S A)]

end CCA

section PubCCA

variable {M C R : Type u} {PK : Type v} {SK : Type w} [DecidableEq C]

/-- A monadic chosen-ciphertext adversary against a public-key scheme (Katz and Lindell,
Definition 11.8): the monadic form of `PubCCAAdversary`. -/
structure MPubCCAAdversary (Smp : SampleFam.{u}) (M : Type u) (PK : Type v) (C : Type u) where
  /-- The two stages, as a function of the public key. -/
  run : PK → (WithSample Smp (OracleSig C (Option M))).FreeM
    ((M × M) × (C → (WithSample Smp (OracleSig C (Option M))).FreeM Bool))

/-- The monadic public-key CCA experiment with challenge bit `b`. -/
noncomputable def mPubCcaExp (S : PKEScheme M PK SK C) (A : MPubCCAAdversary Smp M PK C)
    (b : Bool) : PMF Bool :=
  S.gen.bind fun kp =>
    (evalPMF (withSampleOracle Smp (pubDecOracle S kp.2 none)) (A.run kp.1)).bind fun out =>
      (S.enc kp.1 (pick out.1 b)).bind fun c =>
        evalPMF (withSampleOracle Smp (pubDecOracle S kp.2 (some c))) (out.2 c)

/-- A coin public-key CCA adversary as a monadic one. -/
def MPubCCAAdversary.ofCoins (A : PubCCAAdversary M PK C R) :
    MPubCCAAdversary (coinFam A.coins) M PK C :=
  ⟨fun pk => sampleThen PUnit.unit fun r =>
    (fun out => (out.1, fun c => embed (out.2 c))) <$> embed (A.run pk r)⟩

/-- **The public-key CCA `ofCoins` equality.** -/
@[simp] theorem mPubCcaExp_ofCoins (S : PKEScheme M PK SK C) (A : PubCCAAdversary M PK C R)
    (b : Bool) : mPubCcaExp S (MPubCCAAdversary.ofCoins A) b = pubCcaExp S A b := by
  simp [mPubCcaExp, pubCcaExp, MPubCCAAdversary.ofCoins, Function.comp_def]

end PubCCA

section MAC

variable {M T R : Type u} {K : Type*}

/-- A monadic forger against a MAC (Katz and Lindell, Definition 4.2): the monadic form of
`MACForger`. -/
structure MMACForger (Smp : SampleFam.{u}) (M T : Type u) where
  /-- The forger. -/
  forge : (WithSample Smp (OracleSig M T)).FreeM (M × T)

/-- At most `q` tagging queries; sampling is free. -/
def MMACForger.OracleBounded (q : ℕ) (A : MMACForger Smp M T) : Prop :=
  Framework.OracleBounded q A.forge

/-- At most `s` sampling steps. -/
def MMACForger.SampleBounded (s : ℕ) (A : MMACForger Smp M T) : Prop :=
  Framework.SampleBounded s A.forge

/-- **`Mac-forge`** for monadic forgers (Katz and Lindell, Definition 4.2). -/
noncomputable def mMacGame [DecidableEq M] (S : MACScheme M K T) (A : MMACForger Smp M T) :
    PMF Bool :=
  S.gen.bind fun k =>
    (mEvalLog Smp (S.tag k) A.forge).map fun p =>
      S.verify k p.1.1 p.1.2 && decide (p.1.1 ∉ p.2.map Prod.fst)

/-- The monadic forgery advantage. -/
noncomputable def mMacAdvantage [DecidableEq M] (S : MACScheme M K T) (A : MMACForger Smp M T) :
    ℝ :=
  winProb (mMacGame S A)

/-- A coin forger as a monadic one: sample the coins once, then run. -/
def MMACForger.ofCoins (A : MACForger M T R) : MMACForger (coinFam A.coins) M T :=
  ⟨sampleThen PUnit.unit fun r => embed (A.forge r)⟩

/-- **The MAC `ofCoins` equality.** -/
@[simp] theorem mMacGame_ofCoins [DecidableEq M] (S : MACScheme M K T) (A : MACForger M T R) :
    mMacGame S (MMACForger.ofCoins A) = macGame S A := by
  simp [mMacGame, macGame, MMACForger.ofCoins, PMF.map_bind]

/-- The forgery advantage is unchanged by the embedding. -/
@[simp] theorem mMacAdvantage_ofCoins [DecidableEq M] (S : MACScheme M K T) (A : MACForger M T R) :
    mMacAdvantage S (MMACForger.ofCoins A) = macAdvantage S A := by
  simp [mMacAdvantage, macAdvantage]

/-- The embedding keeps the query bound. -/
theorem MMACForger.oracleBounded_ofCoins {q : ℕ} {A : MACForger M T R} (h : A.QueryBounded q) :
    (MMACForger.ofCoins A).OracleBounded q :=
  oracleBoundedWith_sampleThen fun r => oracleBoundedWith_embed (fun _ _ _ => trivial) (h r)

/-- The embedding samples once. -/
theorem MMACForger.sampleBounded_ofCoins (A : MACForger M T R) :
    (MMACForger.ofCoins A).SampleBounded 1 :=
  sampleBoundedWith_sampleThen fun _ => sampleBoundedWith_embed (fun _ => trivial) _

end MAC

section Sig

variable {M S R : Type u} {PK : Type v} {SK : Type w} [DecidableEq M]

/-- A monadic forger against a signature scheme (Katz and Lindell, Definition 12.2): the monadic
form of `SigForger`. -/
structure MSigForger (Smp : SampleFam.{u}) (M : Type u) (PK : Type v) (S : Type u) where
  /-- The forger, as a function of the public key. -/
  forge : PK → (WithSample Smp (OracleSig M S)).FreeM (M × S)

/-- **`Sig-forge`** for monadic forgers (Katz and Lindell, Definition 12.2). -/
noncomputable def mSigGame (Sg : SigScheme M PK SK S) (A : MSigForger Smp M PK S) : PMF Bool :=
  Sg.gen.bind fun kp =>
    (mEvalLog Smp (Sg.sign kp.2) (A.forge kp.1)).map fun p =>
      Sg.verify kp.1 p.1.1 p.1.2 && decide (p.1.1 ∉ p.2.map Prod.fst)

/-- A coin signature forger as a monadic one. -/
def MSigForger.ofCoins (A : SigForger M PK S R) : MSigForger (coinFam A.coins) M PK S :=
  ⟨fun pk => sampleThen PUnit.unit fun r => embed (A.forge pk r)⟩

/-- **The signature `ofCoins` equality.** -/
@[simp] theorem mSigGame_ofCoins (Sg : SigScheme M PK SK S) (A : SigForger M PK S R) :
    mSigGame Sg (MSigForger.ofCoins A) = sigGame Sg A := by
  simp [mSigGame, sigGame, MSigForger.ofCoins, PMF.map_bind]

end Sig

end Cslib.Crypto.Framework
