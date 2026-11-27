/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.LazySampling

/-!
# Translating queries, and lazy tables with presampled answers

Two tools for reductions that answer the queries of an adversary themselves, and the facts about
uniform pairs and tapes they use (`uniformOfFintype_map_prod`, `uniformOfFintype_map_fst` and
`uniformOfFintype_map_apply_eq_bind`).

* `OracleComp.reindex f g c` translates the queries of an oracle algorithm `c`: a query `x`
  becomes the query `f x`, and the answer `z` to it is handed to `c` as `g x z`.
  `OracleComp.run_reindex`: run against `O`, it runs `c` against `x ↦ g x (O (f x))`;
  `OracleComp.isQueryBounded_reindex`: it keeps query bounds.
* `OracleComp.runLazy t d n T c` runs `c` against a lazily filled table of answers, started at
  query counter `n` with the table `T`: a recorded query is answered from the table, and a fresh
  query asked when the counter is `m` gets the presampled answer `t m`, which is recorded. This is
  how a reduction keeps a random function consistent without sampling it whole, as in Boneh and
  Shoup's proof of their Theorem 4.10 (`CSLibExt.Crypto.SymmetricKey.GGM`).
  * `OracleComp.map_runLazy` (**presampled answers are lazily sampled answers**): on a uniform
    tape, the run has the output distribution of the lazy random function
    `LazySampling.lazyRF`, as long as the algorithm cannot exhaust the tape.
  * `OracleComp.map_runLazy_empty`: from the empty table, it has the output distribution of the
    algorithm run against a uniformly random function (through `LazySampling.lazyRF_map_fst`).
  * `OracleComp.runLazy_congr` (locality) and `OracleComp.runLazy_comp` (storing tape entries or
    their images) are the bookkeeping lemmas that reductions need.

## References

* D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017,
  Section 4.6 (proof of Theorem 4.10).
-/

@[expose] public section

namespace Cslib.Crypto.Framework

open LazySampling

local notation "U" => Cslib.Probability.PMF.uniformOfFintype

universe u v w

/-! ### Uniform tapes -/

section Tape

variable {α β γ : Type*} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]

/-- **A function of a uniform pair is a function of two independent uniform samples.** Let
$\alpha$ and $\beta$ be finite nonempty sets and $f : \alpha \times \beta \to \gamma$. For a uniform
pair $p \in \alpha \times \beta$, the distribution of $f(p)$ is that of $f(a, b)$ for independent
uniform $a \in \alpha$ and $b \in \beta$. -/
theorem uniformOfFintype_map_prod (f : α × β → γ) :
    (U (α × β)).map f = (U α).bind fun a => (U β).map fun b => f (a, b) := by
  simp only [← PMF.bind_pure_comp]
  exact (uniformOfFintype_bind_bind fun a b => PMF.pure (f (a, b))).symm

/-- **A function of the first entry of a uniform pair.** Let $\alpha$ and $\beta$ be finite
nonempty sets and $f : \alpha \to \gamma$. For a uniform pair $(a, b) \in \alpha \times \beta$, the
distribution of $f(a)$ is that of $f(a)$ for a uniform $a \in \alpha$. -/
theorem uniformOfFintype_map_fst (f : α → γ) :
    (U (α × β)).map (fun p => f p.1) = (U α).map f := by
  rw [uniformOfFintype_map_prod, ← PMF.bind_pure_comp]
  congr 1
  funext a
  exact PMF.map_const (U β) (f a)

variable {Q : ℕ}

/-- Overwriting one entry of a uniform tape with an independent uniform value leaves it uniform. -/
private theorem bind_map_update (j : Fin Q) (f : (Fin Q → α) → γ) :
    ((U α).bind fun a => (U (Fin Q → α)).map fun t => f (Function.update t j a)) =
      (U (Fin Q → α)).map f := by
  let e : α × (Fin Q → α) ≃ (Fin Q → α) × α :=
    { toFun := fun p => (Function.update p.2 j p.1, p.2 j)
      invFun := fun q => (q.1 j, Function.update q.1 j q.2)
      left_inv := fun p => by simp
      right_inv := fun q => by simp }
  rw [← uniformOfFintype_map_fst (β := α) f, ← Cslib.Probability.PMF.uniformOfFintype_map_equiv e,
    PMF.map_comp, uniformOfFintype_map_prod]
  rfl

/-- **An entry of a uniform tape is independent of the rest of the tape.** Let $\alpha$ be a
finite nonempty set, $j \in \{0, \dots, Q - 1\}$ and $F(a, t)$ a function of $a \in \alpha$ and of
a tape $t : \{0, \dots, Q - 1\} \to \alpha$ that does not depend on the entry $t(j)$. For a
uniform tape $t$, the distribution of $F(t(j), t)$ is that of $F(a, t)$ for independent uniform
$a$ and $t$. -/
theorem uniformOfFintype_map_apply_eq_bind (j : Fin Q) (F : α → (Fin Q → α) → γ)
    (hF : ∀ a t b, F a (Function.update t j b) = F a t) :
    (U (Fin Q → α)).map (fun t => F (t j) t) = (U α).bind fun a => (U (Fin Q → α)).map (F a) := by
  rw [← bind_map_update j]
  congr 1
  funext a
  congr 1
  funext t
  rw [Function.update_self, hF]

end Tape

namespace OracleComp

/-! ### Translating queries -/

section Reindex

variable {X : Type u} {Y : Type v} {P Z : Type*} {α : Type w}

/-- **Translating the queries of an oracle algorithm.** Let $c$ be an adaptive oracle algorithm
with queries in $X$, answers in $Y$ and output in $\alpha$, and let $f : X \to P$ and
$g : X \to Z \to Y$. The translated algorithm, with queries in $P$ and answers in $Z$, runs $c$ and
replaces each query $x$ of $c$ by the query $f(x)$; on the answer $z$ it hands $g(x, z)$ to $c$ as
the answer to $x$. So it makes one query for each query of $c$. -/
def reindex (f : X → P) (g : X → Z → Y) : OracleComp X Y α → OracleComp P Z α
  | .pure a => .pure a
  | .liftBind x k => .liftBind (f x) fun z => reindex f g (k (g x z))

/-- **Running a translated algorithm.** Let $c$ be an adaptive oracle algorithm with queries in
$X$ and answers in $Y$, let $f : X \to P$ and $g : X \to Z \to Y$, and let $O : P \to Z$. Running
the algorithm obtained from $c$ by translating its queries along $f$ and its answers along $g$
against $O$ gives the output of $c$ run against the oracle $x \mapsto g(x, O(f(x)))$. -/
theorem run_reindex (f : X → P) (g : X → Z → Y) (O : P → Z) :
    ∀ c : OracleComp X Y α, (reindex f g c).run O = c.run fun x => g x (O (f x))
  | .pure _ => rfl
  | .liftBind x k => run_reindex f g O (k (g x (O (f x))))

/-- **Translating queries keeps query bounds.** If an adaptive oracle algorithm $c$ makes at most
$q$ queries along every path, whatever the answers, so does the algorithm obtained from $c$ by
translating its queries along $f : X \to P$ and its answers along $g : X \to Z \to Y$. -/
theorem isQueryBounded_reindex (f : X → P) (g : X → Z → Y) :
    ∀ {q : ℕ} {c : OracleComp X Y α}, FreeM.IsQueryBounded q c →
      FreeM.IsQueryBounded q (reindex f g c)
  | _, .pure _, _ => trivial
  | 0, .liftBind _ _, hc => hc.elim
  | _ + 1, .liftBind x _, hc => fun z => isQueryBounded_reindex f g (hc (g x z))

end Reindex

/-! ### Lazy tables with presampled answers -/

section Lazy

variable {P : Type u} {α : Type v} {β : Type w} [DecidableEq P] {Q : ℕ}

/-- **Running against a lazy table with presampled answers.** Let $c$ be an adaptive oracle
algorithm with queries in $P$, answers in $\alpha$ and output in $\beta$, let
$t : \{0, \dots, Q - 1\} \to \alpha$ be a tape of answers and let $d \in \beta$ be a default
output. Started at query counter $n$ with a table $T_0$ of recorded answers (a partial function
$P \rightharpoonup \alpha$), the run keeps a current table $T$, at first $T_0$, and answers the
query $p$ asked when the counter is $m$ as follows: if $T$ records an answer $a$ for $p$, the
answer is $a$; otherwise, if $m < Q$, the answer is $t(m)$, and $T$ then records $t(m)$ for $p$;
otherwise the run stops with output $d$. The counter goes up by one at every query. The result is
the output of $c$, or $d$ if the run stops. -/
def runLazy (t : Fin Q → α) (d : β) : ℕ → Table P α → OracleComp P α β → β
  | _, _, .pure b => b
  | n, T, .liftBind p k =>
    match T p with
    | some a => runLazy t d (n + 1) T (k a)
    | none =>
      -- The new table is `Function.update T p (some (t ⟨n, h⟩))` (`runLazy_liftBind_of_none`),
      -- written with `if` so that the run reduces by `decide` also when `P` is a function type.
      if h : n < Q then
        runLazy t d (n + 1) (fun p' => if p' = p then some (t ⟨n, h⟩) else T p') (k (t ⟨n, h⟩))
      else d

theorem runLazy_liftBind_of_some (t : Fin Q → α) (d : β) (n : ℕ) {T : Table P α} {p : P} {a : α}
    (k : α → OracleComp P α β) (hp : T p = some a) :
    runLazy t d n T (.liftBind p k) = runLazy t d (n + 1) T (k a) := by
  simp only [runLazy, hp]

theorem runLazy_liftBind_of_none (t : Fin Q → α) (d : β) {n : ℕ} (hn : n < Q) {T : Table P α}
    {p : P} (k : α → OracleComp P α β) (hp : T p = none) :
    runLazy t d n T (.liftBind p k) =
      runLazy t d (n + 1) (Function.update T p (some (t ⟨n, hn⟩))) (k (t ⟨n, hn⟩)) := by
  have hT : (fun p' => if p' = p then some (t ⟨n, hn⟩) else T p') =
      Function.update T p (some (t ⟨n, hn⟩)) := by
    funext p'
    rw [Function.update_apply]
  simp only [runLazy, hp, hn, dite_true, hT]

/-- **Locality of runs against a lazy table.** Let $t$ and $t'$ be tapes of $Q$ answers that agree
at every position $m' \ge m$. Then for every adaptive oracle algorithm $c$, every counter
$n \ge m$, every table and every default output, the runs of $c$ against the lazy tables with
presampled answers $t$ and $t'$, started at counter $n$ with that table, give the same result. -/
theorem runLazy_congr {t t' : Fin Q → α} (d : β) {m : ℕ} (h : ∀ c : Fin Q, m ≤ c → t c = t' c) :
    ∀ (c : OracleComp P α β) (n : ℕ) (T : Table P α), m ≤ n →
      runLazy t d n T c = runLazy t' d n T c
  | .pure _, _, _, _ => rfl
  | .liftBind p k, n, T, hn => by
    cases hp : T p with
    | some a =>
      rw [runLazy_liftBind_of_some t d n k hp, runLazy_liftBind_of_some t' d n k hp]
      exact runLazy_congr d h (k a) (n + 1) T (by omega)
    | none =>
      by_cases hnQ : n < Q
      · rw [runLazy_liftBind_of_none t d hnQ k hp, runLazy_liftBind_of_none t' d hnQ k hp,
          h ⟨n, hnQ⟩ hn]
        exact runLazy_congr d h _ (n + 1) _ (by omega)
      · simp only [runLazy, hp, hnQ, dite_false]

/-- **Storing tape entries or their images.** Let $g : \gamma \to \alpha$, let
$t : \{0, \dots, Q - 1\} \to \gamma$ be a tape and $T$ a table with values in $\gamma$, and let
$c$ be an adaptive oracle algorithm with queries in $P$ and answers in $\alpha$. Running $c$
against the lazy table with presampled answers $g \circ t$, started with the table that records
$g(a)$ wherever $T$ records $a$, gives the same result as running, against the lazy table with
presampled answers $t$ started with $T$, the algorithm that runs $c$ and hands it $g(z)$ for each
answer $z$, at the same counter and with the same default output. -/
theorem runLazy_comp {γ : Type*} (g : γ → α) (t : Fin Q → γ) (d : β) :
    ∀ (c : OracleComp P α β) (n : ℕ) (T : Table P γ),
      runLazy (fun i => g (t i)) d n (fun p => (T p).map g) c =
        runLazy t d n T (reindex id (fun _ => g) c)
  | .pure _, _, _ => rfl
  | .liftBind p k, n, T => by
    change _ = runLazy t d n T (.liftBind p fun z => reindex id (fun _ => g) (k (g z)))
    cases hp : T p with
    | some a =>
      rw [runLazy_liftBind_of_some _ d n k (T := fun p => (T p).map g) (a := g a) (by simp [hp]),
        runLazy_liftBind_of_some t d n _ hp]
      exact runLazy_comp g t d (k (g a)) (n + 1) T
    | none =>
      by_cases hnQ : n < Q
      · rw [runLazy_liftBind_of_none _ d hnQ k (T := fun p => (T p).map g) (by simp [hp]),
          runLazy_liftBind_of_none t d hnQ _ hp]
        have hT : Function.update (fun p => (T p).map g) p (some (g (t ⟨n, hnQ⟩))) =
            fun p' => (Function.update T p (some (t ⟨n, hnQ⟩)) p').map g := by
          funext p'
          by_cases hp' : p' = p
          · subst hp'
            simp
          · simp [Function.update_of_ne hp']
        rw [hT]
        exact runLazy_comp g t d (k (g (t ⟨n, hnQ⟩))) (n + 1) _
      · simp only [runLazy, hp, hnQ, dite_false, Option.map_none]

variable [Fintype P] [Fintype α] [Nonempty α]

omit [Fintype P] in
/-- **Presampled answers are lazily sampled answers.** Let $\alpha$ be a finite nonempty set and
$c$ an adaptive oracle algorithm with queries in $P$ and answers in $\alpha$ that makes at most
$q$ queries along every path, whatever the answers. Let $n + q \le Q$ and let $T$ be a table.
Running $c$ against the lazy table with a uniformly random tape of $Q$ answers, started at counter
$n$ with the table $T$, has the output distribution of running $c$ against the lazy random
function from $T$, which answers each fresh query with a fresh uniform value in $\alpha$. -/
theorem map_runLazy (d : β) :
    ∀ {q : ℕ} (c : OracleComp P α β) (n : ℕ) (T : Table P α), FreeM.IsQueryBounded q c →
      n + q ≤ Q → (U (Fin Q → α)).map (fun t => runLazy t d n T c) = (lazyRF c T).map Prod.fst
  | _, .pure b, n, T, _, _ => by
    rw [show (fun t : Fin Q → α => runLazy t d n T (.pure b)) = Function.const _ b from rfl,
      PMF.map_const]
    simp [lazyRF, runState, PMF.pure_map]
  | 0, .liftBind _ _, _, _, hc, _ => hc.elim
  | q + 1, .liftBind p k, n, T, hc, hn => by
    have hnQ : n < Q := by omega
    have hlazy : lazyRF (.liftBind p k) T = runState rfStep (.liftBind p k) T := rfl
    cases hp : T p with
    | some a =>
      have h1 : (fun t : Fin Q → α => runLazy t d n T (.liftBind p k)) =
          fun t => runLazy t d (n + 1) T (k a) :=
        funext fun t => runLazy_liftBind_of_some t d n k hp
      rw [h1, map_runLazy d (k a) (n + 1) T (hc a) (by omega), hlazy, rfStep,
        runState_lazyStep_of_some _ k hp]
      rfl
    | none =>
      let F : α → (Fin Q → α) → β := fun a t =>
        runLazy t d (n + 1) (Function.update T p (some a)) (k a)
      have hF : ∀ a t b, F a (Function.update t ⟨n, hnQ⟩ b) = F a t := fun a t b =>
        runLazy_congr d (m := n + 1) (fun c hc => Function.update_of_ne
          (show c ≠ ⟨n, hnQ⟩ from fun h => by rw [h] at hc; simp at hc) b t) (k a) (n + 1) _ le_rfl
      have h1 : (fun t : Fin Q → α => runLazy t d n T (.liftBind p k)) =
          fun t => F (t ⟨n, hnQ⟩) t :=
        funext fun t => runLazy_liftBind_of_none t d hnQ k hp
      rw [h1, uniformOfFintype_map_apply_eq_bind ⟨n, hnQ⟩ F hF, hlazy, rfStep,
        runState_lazyStep_of_none _ k hp, PMF.map_bind]
      congr 1
      funext a
      exact map_runLazy d (k a) (n + 1) _ (hc a) (by omega)

/-- **Presampled answers give a uniformly random function.** Let $P$ be a finite set, $\alpha$ a
finite nonempty set and $c$ an adaptive oracle algorithm with queries in $P$ and answers in
$\alpha$ that makes at most $Q$ queries along every path, whatever the answers. Running $c$ against
the lazy table with a uniformly random tape of $Q$ answers, started at counter $0$ with the empty
table, has the output distribution of running $c$ against a uniformly random function
$P \to \alpha$. -/
theorem map_runLazy_empty (d : β) {c : OracleComp P α β} (hc : FreeM.IsQueryBounded Q c) :
    (U (Fin Q → α)).map (fun t => runLazy t d 0 Table.empty c) =
      (U (P → α)).map fun W => c.run W := by
  rw [map_runLazy d c 0 Table.empty hc (by omega), lazyRF_map_fst]

end Lazy

end OracleComp

end Cslib.Crypto.Framework
