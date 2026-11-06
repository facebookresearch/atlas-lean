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
# Pseudorandom functions: concrete-security reductions for a MAC and for CPA encryption

A keyed function `F : K → X → Y` on finite types is pseudorandom when no efficient distinguisher
tells the oracle `F k` (for a uniform key `k`) from a uniformly random function `X → Y` with more
than a small advantage. This file proves the textbook reductions as **concrete inequalities** for
fixed finite types: the advantage of any adversary against the MAC or the encryption scheme is
bounded by the PRF advantage of an explicit distinguisher built from it, plus an explicit
statistical term. Security parameters, polynomial-time restrictions and negligible functions are
not modelled; the asymptotic statements of Katz and Lindell follow from these bounds but are out
of scope here.

Distinguishers and adversaries are **adaptive oracle algorithms** (`OracleComp`): finite query
trees in CSLib's free monad `PFunctor.FreeM` whose next query may depend on the previous answers,
with random coins drawn up front from a finite type.

* `prfReal F D`, `prfRand D : PMF Bool` are the two worlds of the PRF experiment and
  `prfAdvantage F D` is the difference of their success probabilities.

**The MAC from a PRF** (Katz and Lindell, Construction 4.5 and Theorem 4.6). The tag of `m` is
`F k m`. `macGame F A` is the existential-forgery experiment under an adaptive chosen-message
attack: the forger `A` may query tags, and wins with a valid tag on a message it never queried.
* `macReduction` turns a forger into a distinguisher that runs it, logging its queries, and then
  checks the forgery with one more query; `macGame_eq_prfReal`: with the oracle `F k` it runs the
  forgery experiment exactly.
* `prfRand_macReduction_le`: with a random function, a fresh message's tag is uniform, so the
  forgery succeeds with probability at most `1 / |T|` (`card_macWins_mul_le` counts the winning
  functions).
* `macGame_le`: `Pr[A forges] ≤ prfAdvantage F (macReduction A) + 1 / |T|`.

**CPA encryption from a PRF** (Katz and Lindell, Construction 3.30 and Theorem 3.31). With
messages in an additive group `Y` (bit strings under XOR are one), `encrypt (F k) m r = (r, F k r +
m)` for uniform randomness `r : X`, and `decrypt_encrypt` is correctness.
* `cpaGame q F A` is the indistinguishability experiment under a chosen-plaintext attack. The
  adversary `A` queries the encryption oracle, chooses two messages, sees the encryption of one,
  queries again and guesses which. The encryption randomness of its queries is drawn up front, so
  the oracle answers at most `q` queries; an adversary that asks for more is stopped and guesses
  `false`. `cpaAdvantage q F A = |Pr[A guesses the bit] - 1/2|`.
* `cpaReduction q A` simulates the experiment with its oracle; `cpaGame_eq_prfReal`: with the oracle
  `F k` it is the CPA experiment.
* `prfRand_cpaReduction`: with a random function, the success probability is within `q / (2 |X|)`
  of `1/2`. If the challenge randomness differs from the randomness of all queries, flipping the
  bit and shifting the random function at the challenge point leaves the adversary's view
  unchanged (`cpaGuess_flip`), so exactly half of the cases are wins; the challenge randomness
  repeats one of the `q` query values with probability at most `q / |X|`.
* `cpaAdvantage_le`: `cpaAdvantage q F A ≤ prfAdvantage F (cpaReduction q A) + q / (2 |X|)`, which
  implies Katz and Lindell's bound with `q / |X|`.

The games are `PMF Bool` experiments and the advantages are differences of success
probabilities.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Sections 3.5, 3.6 and 4.3.
-/

@[expose] public section

namespace Cslib.Crypto.PRF

open Finset

universe u v w

/-- **The signature of one oracle.** For types $X$ and $Y$, this is the polynomial functor whose
operations are the queries $x \in X$, each answered by an element of $Y$. -/
abbrev OracleSig (X : Type u) (Y : Type v) : PFunctor.{u, v} := ⟨X, fun _ => Y⟩

/-- **Adaptive oracle algorithms.** For a type $X$ of queries, a type $Y$ of answers and a type
$\alpha$ of outputs, an adaptive deterministic oracle algorithm is an element of CSLib's free
monad over the polynomial functor of one oracle with queries $X$ and answers $Y$. It is built
inductively: it either stops with an output in $\alpha$, or asks a query $x \in X$ and continues
with an algorithm that depends on the answer $y \in Y$. -/
abbrev OracleComp (X : Type u) (Y : Type v) (α : Type w) : Type (max u v w) :=
  (OracleSig X Y).FreeM α

namespace OracleComp

variable {X : Type u} {Y : Type v} {α : Type w}

/-- **The oracle algorithm that stops at once.** For an output $a \in \alpha$, this is the
adaptive oracle algorithm with queries in $X$ and answers in $Y$ that asks no query and stops
with output $a$. -/
abbrev done (a : α) : OracleComp X Y α := .pure a

/-- **Query step.** For a point $x \in X$ and a continuation $k$ assigning an oracle algorithm to
each answer $y \in Y$, the oracle algorithm that first queries $x$ and then continues with
$k(y)$, where $y$ is the answer. -/
abbrev query (x : X) (k : Y → OracleComp X Y α) : OracleComp X Y α := .liftBind x k

/-- **Running an oracle algorithm.** Given a function $O : X \to Y$, the run of an oracle
algorithm with queries in $X$, answers in $Y$ and outputs in $\alpha$ is its output when every
query $x$ is answered by $O(x)$: an algorithm that stops with output $a$ runs to $a$, and one
that queries $x$ and continues with $k(y)$ on answer $y$ runs to the run of $k(O(x))$. -/
def run (O : X → Y) : OracleComp X Y α → α
  | .pure a => a
  | .liftBind x k => run O (k (O x))

/-- **Queries of an oracle algorithm.** For an oracle algorithm $c$ and a function
$O : X \to Y$, the queries of $c$ against $O$ are the list of the points of $X$ that $c$ asks,
in order, when every query $x$ is answered by $O(x)$: the empty list if $c$ stops, and otherwise
the first query $x$ followed by the queries of the continuation on the answer $O(x)$. -/
def queries (O : X → Y) : OracleComp X Y α → List X
  | .pure _ => []
  | .liftBind x k => x :: queries O (k (O x))

/-- **Locality of oracle runs.** Let $c$ be an oracle algorithm and let $O, O' : X \to Y$ agree
at every query of $c$ against $O$. Then $c$ has the same output against $O$ as against $O'$, and
the same list of queries against $O$ as against $O'$. -/
theorem run_congr {O O' : X → Y} :
    ∀ (c : OracleComp X Y α), (∀ x ∈ c.queries O, O x = O' x) →
      c.run O = c.run O' ∧ c.queries O = c.queries O'
  | .pure _, _ => ⟨rfl, rfl⟩
  | .liftBind x k, h => by
    have hx : O x = O' x := h x List.mem_cons_self
    have ih := run_congr (k (O x)) fun z hz => h z (List.mem_cons_of_mem _ hz)
    simp only [run, queries, ← hx]
    exact ⟨ih.1, by rw [ih.2]⟩

/-- **Running a sequential composition.** Let $c$ be an oracle algorithm with outputs in $\alpha$,
let $g$ map each $a \in \alpha$ to an oracle algorithm with outputs in $\beta$, and let
$O : X \to Y$. Running against $O$ the composition that first runs $c$ and then continues with
$g$ applied to its output gives the output of $g(a)$ run against $O$, where $a$ is the output
of $c$ run against $O$. -/
theorem run_bind {β : Type*} (O : X → Y) (g : α → OracleComp X Y β) :
    ∀ c : OracleComp X Y α, run O (PFunctor.FreeM.bind c g) = (g (c.run O)).run O
  | .pure _ => rfl
  | .liftBind x k => run_bind O g (k (O x))

end OracleComp

open OracleComp

private theorem map_uniform_toReal {Ω : Type*} [Fintype Ω] [Nonempty Ω] (g : Ω → Bool) :
    ((Cslib.Probability.PMF.uniformOfFintype Ω).map g true).toReal =
      (∑ ω, if g ω = true then (1 : ℝ) else 0) / Fintype.card Ω := by
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum (fun ω _ => by split_ifs <;> simp)]
  rw [div_eq_mul_inv, sum_mul]
  refine sum_congr rfl fun ω _ => ?_
  by_cases hg : g ω = true <;> simp [hg, eq_comm (a := true)]

/-! ### The PRF experiment -/

section PRFGame

variable {K X Y S : Type*} [Fintype K] [Nonempty K] [Fintype X] [DecidableEq X] [Fintype Y]
  [Nonempty Y] [Fintype S] [Nonempty S]

/-- **Real world of the PRF experiment.** Let $K$, $X$, $Y$ and $S$ be finite sets with $K$, $Y$
and $S$ nonempty, let $F : K \to X \to Y$ be a keyed function and let $D$ be a distinguisher: an
oracle algorithm with coins in $S$ that queries a function $X \to Y$ and outputs a bit. The real
world is the distribution of the output of $D$ with coins $s$ and oracle $F(k, \cdot)$, where the
pair $(k, s)$ is uniform on $K \times S$. -/
noncomputable def prfReal (F : K → X → Y) (D : S → OracleComp X Y Bool) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype (K × S)).map fun ω => (D ω.2).run (F ω.1)

/-- **Random world of the PRF experiment.** Let $X$, $Y$ and $S$ be finite sets with $Y$ and $S$
nonempty, and let $D$ be a distinguisher: an oracle algorithm with coins in $S$ that queries a
function $X \to Y$ and outputs a bit. The random world is the distribution of the output of $D$
with coins $s$ and oracle $f$, where the pair $(f, s)$ is uniform on $(X \to Y) \times S$. -/
noncomputable def prfRand (D : S → OracleComp X Y Bool) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype ((X → Y) × S)).map fun ω => (D ω.2).run ω.1

/-- **PRF advantage.** Let $K$, $X$, $Y$ and $S$ be finite sets with $K$, $Y$ and $S$ nonempty,
let $F : K \to X \to Y$ be a keyed function and let $D$ be a distinguisher: an oracle algorithm
with coins in $S$ that queries a function $X \to Y$ and outputs a bit. The PRF advantage of $D$
against $F$ is the real number $|p_{\mathrm{real}} - p_{\mathrm{rand}}|$, where
$p_{\mathrm{real}}$ is the probability that $D$ outputs $1$ in the real world (uniform coins
$s \in S$, oracle $F(k, \cdot)$ for a uniform key $k \in K$) and $p_{\mathrm{rand}}$ is the
probability that $D$ outputs $1$ in the random world (uniform coins, oracle a uniformly random
function $X \to Y$). -/
noncomputable def prfAdvantage (F : K → X → Y) (D : S → OracleComp X Y Bool) : ℝ :=
  |(prfReal F D true).toReal - (prfRand D true).toReal|

end PRFGame

/-! ### The MAC from a PRF -/

section MAC

variable {K M T R : Type*} [Fintype K] [Nonempty K] [Fintype M] [DecidableEq M] [Fintype T]
  [Nonempty T] [DecidableEq T] [Fintype R] [Nonempty R]

/-- **Winning the forgery game.** A forger $c$, an adaptive oracle algorithm with queries in $M$,
answers in $T$ and output in $M \times T$, wins against the tagging oracle $O \colon M \to T$
when, run with oracle $O$, it outputs a pair $(m, t)$ with $O(m) = t$ and $m$ is not among the
queries it asks in that run. -/
def MacWins (O : M → T) (c : OracleComp M T (M × T)) : Prop :=
  O (c.run O).1 = (c.run O).2 ∧ (c.run O).1 ∉ c.queries O

instance (O : M → T) (c : OracleComp M T (M × T)) : Decidable (MacWins O c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **The MAC forgery experiment.** Let $K$ and $R$ be finite nonempty types, let
$F \colon K \to M \to T$ be a keyed function, and let $A$ be a forger: for coins $r \in R$,
$A(r)$ is an adaptive oracle algorithm with queries in $M$, answers in $T$ and output in
$M \times T$. The existential-forgery experiment under an adaptive chosen-message attack for the
MAC $\mathrm{Mac}_k(m) = F(k, m)$ draws $(k, r)$ uniformly from $K \times R$, runs $A(r)$ with
the tagging oracle $F(k, \cdot)$, and outputs true exactly when $A(r)$ wins against that oracle,
that is, outputs a pair $(m, t)$ with $F(k, m) = t$ where $m$ is not among its queries. -/
noncomputable def macGame (F : K → M → T) (A : R → OracleComp M T (M × T)) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype (K × R)).map fun ω => decide (MacWins (F ω.1) (A ω.2))

/-- **The distinguisher built from a forger.** For a list $L$ of messages in $M$ and a forger $c$,
an adaptive oracle algorithm with queries in $M$, answers in $T$ and output in $M \times T$, the
MAC reduction is the oracle algorithm with the same queries and answers and a Boolean output,
defined by recursion on $c$. If $c$ stops with output $(m, t)$, it queries $m$ and, on answer
$t'$, stops with output true exactly when $t' = t$ and $m \notin L$. If $c$ queries $x$ and
continues with $c_y$ on answer $y$, it queries $x$ and, on answer $y$, continues as the MAC
reduction of $c_y$ with $x$ added to $L$.

Started with the empty list, it runs the forger, logging its queries, then queries the forged
message and accepts when the answer is the forged tag and the message is fresh. -/
def macReduction (log : List M) : OracleComp M T (M × T) → OracleComp M T Bool
  | .pure p => query p.1 fun t => done (decide (t = p.2 ∧ p.1 ∉ log))
  | .liftBind x k => query x fun y => macReduction (x :: log) (k y)

omit [Fintype M] [Fintype T] [Nonempty T] in
theorem run_macReduction (O : M → T) :
    ∀ (log : List M) (c : OracleComp M T (M × T)),
      (macReduction log c).run O =
        decide (O (c.run O).1 = (c.run O).2 ∧ (c.run O).1 ∉ c.queries O ++ log)
  | log, .pure p => by
    simp only [macReduction, run, queries, List.nil_append]
    exact decide_eq_decide.mpr Iff.rfl
  | log, .liftBind x k => by
    rw [macReduction, run, run_macReduction O (x :: log) (k (O x))]
    simp only [run, queries, List.mem_append, List.mem_cons]
    congr 2
    exact propext (by tauto)

omit [Fintype M] [Fintype T] [Nonempty T] in
/-- **The MAC reduction in the real PRF world.** Let $K$ and $R$ be finite nonempty types, let
$F \colon K \to M \to T$ be a keyed function, and let $A$ be a forger: for coins $r \in R$,
$A(r)$ is an adaptive oracle algorithm with queries in $M$, answers in $T$ and output in
$M \times T$. Then the output distribution of the existential-forgery experiment for $F$ and $A$
equals the output distribution of the real world of the PRF experiment for $F$ with the
distinguisher that, on coins $r$, runs the MAC reduction on $A(r)$ starting from the empty query
log. -/
theorem macGame_eq_prfReal (F : K → M → T) (A : R → OracleComp M T (M × T)) :
    macGame F A = prfReal F (fun r => macReduction [] (A r)) := by
  unfold macGame prfReal
  congr 1
  funext ω
  rw [run_macReduction, List.append_nil]
  exact decide_eq_decide.mpr Iff.rfl

omit [Nonempty T] in
/-- **Counting forgeries against a random function.** Let $M$ and $T$ be finite sets and let $c$ be
an adaptive oracle algorithm that queries messages in $M$, receives tags in $T$ and outputs a pair
in $M \times T$. Call a function $f \colon M \to T$ a win for $c$ when the run of $c$ with oracle
$f$ outputs a pair $(m, t)$ with $f(m) = t$ and $m$ not among the messages queried in that run.
If $W$ is the set of functions $M \to T$ that are wins for $c$, then $|W| \cdot |T| \le |T|^{|M|}$.

Changing the tag of the fresh forged message, which the run never queries, gives $|T|$ functions
with the same run, of which exactly one is a win. -/
theorem card_macWins_mul_le (c : OracleComp M T (M × T)) :
    (univ.filter fun f : M → T => MacWins f c).card * Fintype.card T ≤ Fintype.card (M → T) := by
  rw [← card_univ (α := T), ← card_product, ← card_univ (α := M → T)]
  refine card_le_card_of_injOn (fun p => Function.update p.1 (c.run p.1).1 p.2)
    (fun _ _ => mem_coe.mpr (mem_univ _)) ?_
  -- updating at the fresh forged message does not change the run
  have key : ∀ f : M → T, MacWins f c → ∀ t : T,
      c.run (Function.update f (c.run f).1 t) = c.run f := by
    intro f hf t
    refine ((run_congr c fun x hx => ?_).1).symm
    rw [Function.update_of_ne]
    rintro rfl
    exact hf.2 hx
  rintro ⟨f, t⟩ hf ⟨f', t'⟩ hf' heq
  simp only [coe_product, coe_filter, mem_univ, true_and, coe_univ, Set.mem_prod,
    Set.mem_ofPred_eq, Set.mem_univ, and_true] at hf hf' heq
  have hrun : c.run f = c.run f' := by
    rw [← key f hf t, ← key f' hf' t', heq]
  have ht : t = t' := by
    have h1 := congrFun heq (c.run f).1
    rwa [Function.update_self, hrun, Function.update_self] at h1
  subst ht
  have hf_eq : f = Function.update (Function.update f (c.run f).1 t) (c.run f).1 (c.run f).2 := by
    rw [Function.update_idem, ← hf.1, Function.update_eq_self]
  have hf'_eq : f' =
      Function.update (Function.update f' (c.run f').1 t) (c.run f').1 (c.run f').2 := by
    rw [Function.update_idem, ← hf'.1, Function.update_eq_self]
  rw [Prod.mk.injEq]
  refine ⟨?_, rfl⟩
  rw [hf_eq, hf'_eq, heq, hrun]

/-- **Forging against a random function.** Let $M$ and $T$ be finite sets with $T$ nonempty, and
let $A$ be a forger: an oracle algorithm with coins in a finite nonempty set that queries tags
in $T$ of messages in $M$ and outputs a message together with a tag. When the tagging oracle is
a uniformly random function $M \to T$ and the coins are uniform, the MAC reduction built from
$A$ accepts (that is, $A$ outputs the correct tag of a message it never queried) with
probability at most $1/|T|$. -/
theorem prfRand_macReduction_le (A : R → OracleComp M T (M × T)) :
    (prfRand (fun r => macReduction [] (A r)) true).toReal ≤ 1 / Fintype.card T := by
  classical
  rw [prfRand, map_uniform_toReal, Fintype.sum_prod_type, sum_comm]
  have hT : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
  have hF : (0 : ℝ) < Fintype.card (M → T) := by exact_mod_cast Fintype.card_pos
  have hR : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have hcount : ∀ r : R, (∑ f : M → T,
      if (macReduction [] (A r)).run f = true then (1 : ℝ) else 0) ≤
        Fintype.card (M → T) / Fintype.card T := by
    intro r
    rw [le_div_iff₀ hT]
    have h := card_macWins_mul_le (A r)
    simp only [run_macReduction, List.append_nil, decide_eq_true_eq]
    rw [sum_boole]
    exact_mod_cast h
  rw [Fintype.card_prod, Nat.cast_mul, div_le_div_iff₀ (by positivity) hT]
  calc (∑ r : R, ∑ f : M → T, if (macReduction [] (A r)).run f = true then (1 : ℝ) else 0) *
        Fintype.card T
      ≤ (∑ _r : R, (Fintype.card (M → T) : ℝ) / Fintype.card T) * Fintype.card T :=
        mul_le_mul_of_nonneg_right (sum_le_sum fun r _ => hcount r) hT.le
    _ = 1 * (Fintype.card (M → T) * Fintype.card R) := by
        rw [sum_const, card_univ, nsmul_eq_mul]
        field_simp

/-- **The MAC from a PRF, concrete security.** Let $K$, $M$, $T$ and $R$ be finite types with
$K$, $T$ and $R$ nonempty, let $F \colon K \to M \to T$ be a keyed function, and let $A$ be an
adaptive chosen-message forger: for coins $r \in R$, $A(r)$ is an adaptive oracle algorithm
with queries in $M$, answers in $T$ and output in $M \times T$. Then the probability that $A$
wins the existential-forgery experiment for the MAC $\mathrm{Mac}_k(m) = F(k, m)$ is at most
the PRF advantage against $F$ of the distinguisher that, on coins $r$, runs the MAC reduction
on $A(r)$ starting from the empty query log, plus $1 / |T|$.

This is the reduction of Katz and Lindell, Theorem 4.6, stated as a concrete inequality. -/
theorem macGame_le (F : K → M → T) (A : R → OracleComp M T (M × T)) :
    (macGame F A true).toReal ≤
      prfAdvantage F (fun r => macReduction [] (A r)) + 1 / Fintype.card T := by
  rw [macGame_eq_prfReal, prfAdvantage]
  have := prfRand_macReduction_le A
  have := le_abs_self ((prfReal F (fun r => macReduction [] (A r)) true).toReal -
    (prfRand (fun r => macReduction [] (A r)) true).toReal)
  linarith

end MAC

/-! ### CPA encryption from a PRF -/

section CPA

variable {K X Y R : Type*} [Fintype K] [Nonempty K] [Fintype X] [Nonempty X] [DecidableEq X]
  [Fintype Y] [AddCommGroup Y] [Fintype R] [Nonempty R] {q : ℕ}

/-- **Encryption from a keyed function.** Let $Y$ be an additive commutative group of messages
and let $f \colon X \to Y$ be a function (in the scheme, $f = F_k$ for a key $k$). The
encryption of a message $m \in Y$ with randomness $r \in X$ is the pair
$(r, f(r) + m) \in X \times Y$.

This is Construction 3.30 of Katz and Lindell, with XOR replaced by the addition of the
message group. -/
def encrypt (Fk : X → Y) (m : Y) (r : X) : X × Y := (r, Fk r + m)

/-- **Decryption with a keyed function.** For a function $F_k \colon X \to Y$ into an additive
commutative group $Y$, the decryption of a ciphertext $(r, c) \in X \times Y$ is
$\mathrm{Dec}(r, c) = c - F_k(r)$. -/
def decrypt (Fk : X → Y) (c : X × Y) : Y := c.2 - Fk c.1

omit [Fintype X] [Nonempty X] [DecidableEq X] [Fintype Y] in
/-- **Correctness of encryption with a keyed function.** Let $Y$ be an additive commutative group
and $F_k \colon X \to Y$ a function. For every message $m \in Y$ and every randomness $r \in X$,
decrypting the ciphertext $\mathrm{Enc}(m) = (r, F_k(r) + m)$ gives back $m$, that is,
$\mathrm{Dec}(\mathrm{Enc}(m)) = m$ where $\mathrm{Dec}(r, c) = c - F_k(r)$. -/
theorem decrypt_encrypt (Fk : X → Y) (m : Y) (r : X) : decrypt Fk (encrypt Fk m r) = m := by
  simp [decrypt, encrypt]

/-- **Selecting the challenge message by a bit.** Given a pair of messages
$(m_0, m_1) \in Y \times Y$ and a challenge bit $b$, the selected message is $m_1$ when $b$ is
true and $m_0$ when $b$ is false. -/
def pick (m : Y × Y) (b : Bool) : Y := if b then m.2 else m.1

/-- **Running an algorithm against the bounded encryption oracle.** Let $X$ be a set, $Y$ an
abelian group written additively, $f : X \to Y$ a function, $q \in \mathbb{N}$ and
$\rho : \{0, \dots, q - 1\} \to X$ the encryption randomness of the queries. Run from query index
$i \in \mathbb{N}$, an oracle algorithm with messages in $Y$ as queries, answers in $X \times Y$
and outputs in $\beta$ either fails or yields its output together with the next query index: if
it stops with output $a$, the result is $(a, i)$; if it queries a message $m$ and $i < q$, the
oracle answers $(\rho(i), f(\rho(i)) + m)$ and the run continues from index $i + 1$; if it
queries a message and $i \ge q$, the run fails. -/
def runEnc {β : Type*} (f : X → Y) (ρ : Fin q → X) : OracleComp Y (X × Y) β → ℕ → Option (β × ℕ)
  | .pure a, i => some (a, i)
  | .liftBind m k, i =>
    if h : i < q then runEnc f ρ (k (encrypt f m (ρ ⟨i, h⟩))) (i + 1) else none

/-- **CPA adversary.** A CPA adversary with coins in $R$, against an encryption oracle that takes
messages in $Y$ and returns ciphertexts in $X \times Y$, assigns to each $r \in R$ an adaptive
oracle algorithm with access to the encryption oracle that outputs two challenge messages
$(m_0, m_1) \in Y \times Y$ together with a second adaptive oracle algorithm, again with access to
the encryption oracle, which takes the challenge ciphertext in $X \times Y$ and outputs a guess
for the challenge bit. -/
abbrev CPAAdversary (X Y R : Type*) :=
  R → OracleComp Y (X × Y) ((Y × Y) × (X × Y → OracleComp Y (X × Y) Bool))

/-- **The adversary's guess in the CPA experiment.** Let $Y$ be an additive commutative group,
$f \colon X \to Y$ a function, $q$ a natural number, $\rho \colon \{0, \dots, q - 1\} \to X$ the
encryption randomness, $r_s \in X$ the challenge randomness and $b$ a bit. Let $c$ be an oracle
algorithm for the encryption oracle that outputs two messages $(m_0, m_1) \in Y \times Y$ and a
second-phase algorithm. The encryption query with index $i$, counting from $0$ across both
phases, is answered for a message $m$ by $(\rho_i, f(\rho_i) + m)$. Run $c$; when it outputs
$(m_0, m_1)$, run its second phase on the challenge ciphertext $(r_s, f(r_s) + m_b)$, where $m_b$
is $m_1$ if $b$ is true and $m_0$ otherwise. The guess is the output of the second phase. If the
two phases together ask more than $q$ encryption queries, the adversary is stopped and the guess
is false. -/
def cpaGuess (f : X → Y) (ρ : Fin q → X) (rs : X) (b : Bool)
    (c : OracleComp Y (X × Y) ((Y × Y) × (X × Y → OracleComp Y (X × Y) Bool))) : Bool :=
  ((runEnc f ρ c 0).bind fun p =>
    (runEnc f ρ (p.1.2 (encrypt f (pick p.1.1 b) rs)) p.2).map Prod.fst).getD false

variable (q) in
/-- **The CPA experiment.** Let $K$, $X$ and $R$ be nonempty finite sets, $Y$ an additive
commutative group, $q$ a natural number, $F \colon K \to X \to Y$ a keyed function and $A$ a CPA
adversary with coins in $R$. The CPA indistinguishability experiment $\mathrm{PrivK}^{\mathrm{cpa}}$
for the scheme $\mathrm{Enc}_k(m) = (r, F_k(r) + m)$ draws, uniformly and independently, a key
$k \in K$, encryption randomness $\rho \colon \{0, \dots, q - 1\} \to X$ for the encryption
queries, challenge randomness $r_s \in X$, a challenge bit $b$ and coins $r \in R$. It outputs true
exactly when the adversary's guess, with keyed function $F_k$, encryption randomness $\rho$,
challenge randomness $r_s$, challenge bit $b$ and the algorithm that $A$ assigns to $r$, equals $b$.
An adversary that asks more than $q$ encryption queries is stopped and guesses false. -/
noncomputable def cpaGame (F : K → X → Y) (A : CPAAdversary X Y R) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype (K × (Fin q → X) × X × Bool × R)).map fun ω =>
    cpaGuess (F ω.1) ω.2.1 ω.2.2.1 ω.2.2.2.1 (A ω.2.2.2.2) == ω.2.2.2.1

variable (q) in
/-- **CPA advantage.** Let $K$, $X$ and $R$ be nonempty finite sets, $Y$ an additive commutative
group, $q$ a natural number, $F \colon K \to X \to Y$ a keyed function and $A$ a CPA adversary
with coins in $R$. The CPA advantage of $A$ is the real number $|p - 1/2|$, where $p$ is the
probability that the CPA experiment for $F$ and $A$ with at most $q$ encryption queries outputs
true, that is, that $A$ guesses the challenge bit. -/
noncomputable def cpaAdvantage (F : K → X → Y) (A : CPAAdversary X Y R) : ℝ :=
  |(cpaGame q F A true).toReal - 1 / 2|

/-- **Simulating the encryption oracle with a function oracle.** Let $X$ be a set, $Y$ an abelian
group written additively, $q \in \mathbb{N}$ and $\rho : \{0, \dots, q - 1\} \to X$ the
encryption randomness of the queries. Started at query index $i \in \mathbb{N}$, the simulation
turns an oracle algorithm with messages in $Y$ as queries, answers in $X \times Y$ and outputs in
$\beta$ into an oracle algorithm with queries in $X$ and answers in $Y$ that either fails or
outputs the original output together with the next query index: if the original algorithm stops
with output $a$, the simulation stops with $(a, i)$; if it queries a message $m$ and $i < q$, the
simulation queries $\rho(i)$ and, on answer $y$, continues by simulating the original algorithm
on the answer $(\rho(i), y + m)$ from index $i + 1$; if it queries a message and $i \ge q$, the
simulation stops with failure. -/
def simEnc {β : Type*} (ρ : Fin q → X) :
    OracleComp Y (X × Y) β → ℕ → OracleComp X Y (Option (β × ℕ))
  | .pure a, i => done (some (a, i))
  | .liftBind m k, i =>
    if h : i < q then query (ρ ⟨i, h⟩) fun y => simEnc ρ (k (ρ ⟨i, h⟩, y + m)) (i + 1)
    else done none

omit [Fintype X] [Nonempty X] [DecidableEq X] [Fintype Y] in
theorem run_simEnc {β : Type*} (f : X → Y) (ρ : Fin q → X) :
    ∀ (c : OracleComp Y (X × Y) β) (i : ℕ), (simEnc ρ c i).run f = runEnc f ρ c i
  | .pure _, _ => rfl
  | .liftBind m k, i => by
    rw [simEnc, runEnc]
    split_ifs with h
    · exact run_simEnc f ρ _ (i + 1)
    · rfl

variable (q) in
/-- **The PRF distinguisher built from a CPA adversary.** Let $X$ and $R$ be sets, $Y$ an additive
commutative group, $q$ a natural number and $A$ a CPA adversary with coins in $R$ against an
encryption oracle that takes messages in $Y$ and returns ciphertexts in $X \times Y$. With its own
coins $(\rho, r_s, b, r)$, where $\rho \colon \{0, \dots, q - 1\} \to X$, $r_s \in X$, $b$ is a bit
and $r \in R$, and with oracle access to a function $O \colon X \to Y$, the distinguisher runs the
algorithm $A$ assigns to $r$. It answers the encryption query with index $i$, counting from $0$
across both phases, for a message $m$ by querying $O$ at $\rho_i$ and returning
$(\rho_i, O(\rho_i) + m)$. When the first phase outputs messages $(m_0, m_1)$, it queries $O$ at
$r_s$ and gives the second phase the challenge ciphertext $(r_s, O(r_s) + m_b)$, where $m_b$ is
$m_1$ if $b$ is true and $m_0$ otherwise. It outputs true exactly when the adversary's guess
equals $b$, where an adversary that asks more than $q$ encryption queries is stopped and guesses
false. -/
def cpaReduction (A : CPAAdversary X Y R) (s : (Fin q → X) × X × Bool × R) :
    OracleComp X Y Bool :=
  PFunctor.FreeM.bind (simEnc s.1 (A s.2.2.2) 0) fun o =>
    match o with
    | none => done (false == s.2.2.1)
    | some p => query s.2.1 fun y =>
        PFunctor.FreeM.bind (simEnc s.1 (p.1.2 (s.2.1, y + pick p.1.1 s.2.2.1)) p.2) fun o' =>
          done ((o'.map Prod.fst).getD false == s.2.2.1)

omit [Fintype X] [Nonempty X] [DecidableEq X] [Fintype Y]
  [Fintype R] [Nonempty R] in
theorem run_cpaReduction (A : CPAAdversary X Y R) (f : X → Y)
    (s : (Fin q → X) × X × Bool × R) :
    (cpaReduction q A s).run f = (cpaGuess f s.1 s.2.1 s.2.2.1 (A s.2.2.2) == s.2.2.1) := by
  rw [cpaReduction, run_bind, run_simEnc, cpaGuess]
  rcases runEnc f s.1 (A s.2.2.2) 0 with _ | ⟨out, i⟩
  · rfl
  · simp only [run, run_bind, run_simEnc, Option.bind_some, encrypt]

omit [DecidableEq X] [Fintype Y] in
/-- **The CPA reduction is exact with the real oracle.** Let $K$, $X$ and $R$ be nonempty finite
sets, $Y$ an additive commutative group, $q$ a natural number and $F \colon K \to X \to Y$ a keyed
function. For every CPA adversary $A$ with coins in $R$, the CPA experiment for $F$ and $A$ with
at most $q$ encryption queries has the same output distribution as the real world of the PRF
experiment for $F$ run with the distinguisher built from $A$ for $q$ queries: with the oracle $F_k$
for a uniform key $k$, the reduction runs the CPA experiment exactly. -/
theorem cpaGame_eq_prfReal (F : K → X → Y) (A : CPAAdversary X Y R) :
    cpaGame q F A = prfReal F (cpaReduction q A) := by
  unfold cpaGame prfReal
  congr 1
  funext ω
  rw [run_cpaReduction]

omit [Fintype X] [Nonempty X] [DecidableEq X] [Fintype Y] in
/-- **The encryption oracle depends only on the encryption randomness.** Let $Y$ be an additive
commutative group, let $\rho_0, \dots, \rho_{q-1} \in X$ be encryption randomness and let
$f, f' : X \to Y$ satisfy $f(\rho_j) = f'(\rho_j)$ for every $j < q$. Then for every oracle
algorithm $c$ and every natural number $i$, running $c$ against the encryption oracle built from
$f$, with query indices starting at $i$, gives the same result as running it against the one
built from $f'$. Here the encryption oracle built from $f$ answers a query $m$ with index $n < q$
by $(\rho_n, f(\rho_n) + m)$, and the run fails at a query with index $n \ge q$. -/
theorem runEnc_congr {β : Type*} {f f' : X → Y} {ρ : Fin q → X} (h : ∀ j, f (ρ j) = f' (ρ j)) :
    ∀ (c : OracleComp Y (X × Y) β) (i : ℕ), runEnc f ρ c i = runEnc f' ρ c i
  | .pure _, _ => rfl
  | .liftBind m k, i => by
    rw [runEnc, runEnc]
    split_ifs with hi
    · rw [encrypt, encrypt, h]
      exact runEnc_congr h _ (i + 1)
    · rfl

omit [Fintype X] [Nonempty X] [DecidableEq X] [Fintype Y] in
private theorem two_mul_card_filter {Ω : Type*} [Fintype Ω] (g : Ω → Bool) (ψ : Ω → Ω)
    (hψ : Function.Involutive ψ) (hg : ∀ ω, g (ψ ω) = !g ω) :
    2 * (univ.filter fun ω => g ω = true).card = Fintype.card Ω := by
  classical
  have hc : (univ.filter fun ω => g ω = false).card =
      (univ.filter fun ω => g ω = true).card := by
    refine card_nbij' ψ ψ ?_ ?_ (fun ω _ => hψ ω) (fun ω _ => hψ ω) <;>
      · intro ω hω
        simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hω ⊢
        rw [hg, hω]
        rfl
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset Ω)) (fun ω => g ω = true)
  simp_rw [Bool.not_eq_true] at hsplit
  rw [hc, card_univ] at hsplit
  omega

/-- The messages the adversary's first phase outputs against `f` (zero if it is stopped). -/
private def phaseOneMsgs (f : X → Y) (ρ : Fin q → X)
    (c : OracleComp Y (X × Y) ((Y × Y) × (X × Y → OracleComp Y (X × Y) Bool))) : Y × Y :=
  ((runEnc f ρ c 0).map fun p => p.1.1).getD 0

omit [Fintype X] [Nonempty X] [DecidableEq X] [Fintype Y] in
private theorem phaseOneMsgs_congr {f f' : X → Y} {ρ : Fin q → X} (h : ∀ j, f (ρ j) = f' (ρ j))
    (c : OracleComp Y (X × Y) ((Y × Y) × (X × Y → OracleComp Y (X × Y) Bool))) :
    phaseOneMsgs f ρ c = phaseOneMsgs f' ρ c := by
  unfold phaseOneMsgs
  rw [runEnc_congr h]

omit [Fintype X] [Nonempty X] [Fintype Y] in
/-- **The challenge is a one-time pad on fresh randomness**: if the challenge randomness `rs` is
not among the encryption randomness `ρ`, flipping the bit and shifting `f rs` accordingly leaves
the adversary's view, hence its guess, unchanged. -/
private theorem cpaGuess_flip {f : X → Y} {ρ : Fin q → X} {rs : X} (hrs : ∀ j, ρ j ≠ rs)
    (b : Bool) (c : OracleComp Y (X × Y) ((Y × Y) × (X × Y → OracleComp Y (X × Y) Bool))) :
    cpaGuess (Function.update f rs (f rs + pick (phaseOneMsgs f ρ c) b -
      pick (phaseOneMsgs f ρ c) (!b))) ρ rs (!b) c = cpaGuess f ρ rs b c := by
  set f' := Function.update f rs (f rs + pick (phaseOneMsgs f ρ c) b -
    pick (phaseOneMsgs f ρ c) (!b))
  have hagree : ∀ j, f' (ρ j) = f (ρ j) := fun j => Function.update_of_ne (hrs j) _ _
  unfold cpaGuess
  rw [runEnc_congr hagree c 0]
  rcases hrun : runEnc f ρ c 0 with _ | ⟨out, i⟩
  · rfl
  · simp only [Option.bind_some]
    have hm : phaseOneMsgs f ρ c = out.1 := by simp [phaseOneMsgs, hrun]
    have hchal : encrypt f' (pick out.1 (!b)) rs = encrypt f (pick out.1 b) rs := by
      simp only [encrypt, f', Function.update_self, hm]
      congr 1
      abel
    rw [hchal, runEnc_congr hagree]

omit [Fintype X] [Nonempty X] [DecidableEq X] [Fintype Y] in
/-- For fresh challenge randomness, the adversary guesses the bit for exactly half of the pairs
`(f, b)`. -/
private theorem two_mul_card_wins {ρ : Fin q → X} {rs : X} (hrs : ∀ j, ρ j ≠ rs)
    (c : OracleComp Y (X × Y) ((Y × Y) × (X × Y → OracleComp Y (X × Y) Bool)))
    [Fintype (X → Y)] :
    2 * (univ.filter fun fb : (X → Y) × Bool => (cpaGuess fb.1 ρ rs fb.2 c == fb.2) = true).card =
      Fintype.card ((X → Y) × Bool) := by
  classical
  refine two_mul_card_filter _ (fun fb => (Function.update fb.1 rs (fb.1 rs +
    pick (phaseOneMsgs fb.1 ρ c) fb.2 - pick (phaseOneMsgs fb.1 ρ c) (!fb.2)), !fb.2)) ?_ ?_
  · rintro ⟨f, b⟩
    have hagree : ∀ j, Function.update f rs (f rs + pick (phaseOneMsgs f ρ c) b -
        pick (phaseOneMsgs f ρ c) (!b)) (ρ j) = f (ρ j) :=
      fun j => Function.update_of_ne (hrs j) _ _
    have hm : phaseOneMsgs (Function.update f rs (f rs + pick (phaseOneMsgs f ρ c) b -
        pick (phaseOneMsgs f ρ c) (!b))) ρ c = phaseOneMsgs f ρ c :=
      phaseOneMsgs_congr hagree c
    simp only [hm, Function.update_self, Function.update_idem, Bool.not_not]
    rw [show f rs + pick (phaseOneMsgs f ρ c) b - pick (phaseOneMsgs f ρ c) (!b) +
      pick (phaseOneMsgs f ρ c) (!b) - pick (phaseOneMsgs f ρ c) b = f rs by abel,
      Function.update_eq_self]
  · rintro ⟨f, b⟩
    simp only
    rw [cpaGuess_flip hrs b c]
    cases cpaGuess f ρ rs b c <;> cases b <;> rfl

/-- **The CPA reduction against a random function.** Let $X$ be a finite nonempty set, $Y$ a
finite additive commutative group, $q$ a natural number and $A$ a CPA adversary with coins in a
finite nonempty set. Let $p$ be the probability that the CPA reduction built from $A$ (whose
encryption oracle answers at most $q$ queries) outputs $1$, that is, that $A$ guesses the
challenge bit, when its oracle is a uniformly random function $X \to Y$ and its coins are
uniform. Then $|p - 1/2| \le q / (2|X|)$.

The success probability is exactly $1/2$ unless the challenge randomness repeats the randomness
of one of the at most $q$ encryption queries. -/
theorem prfRand_cpaReduction (A : CPAAdversary X Y R) :
    |(prfRand (cpaReduction q A) true).toReal - 1 / 2| ≤ q / (2 * Fintype.card X) := by
  classical
  set N : ℝ := (Fintype.card ((X → Y) × (Fin q → X) × X × Bool × R) : ℝ)
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hX : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hF : (0 : ℝ) < Fintype.card (X → Y) := by exact_mod_cast Fintype.card_pos
  -- the wins for fixed `(ρ, rs, r)`, summed over `(f, b)`
  let W : (Fin q → X) → X → R → ℝ := fun ρ rs r =>
    ∑ fb : (X → Y) × Bool, if (cpaGuess fb.1 ρ rs fb.2 (A r) == fb.2) = true then 1 else 0
  have hW_good : ∀ ρ rs r, (∀ j, ρ j ≠ rs) → W ρ rs r = Fintype.card (X → Y) := by
    intro ρ rs r hrs
    have h := two_mul_card_wins hrs (A r)
    simp only [W, sum_boole, Fintype.card_prod, Fintype.card_bool] at h ⊢
    have : ((univ.filter fun fb : (X → Y) × Bool =>
        (cpaGuess fb.1 ρ rs fb.2 (A r) == fb.2) = true).card : ℝ) =
        Fintype.card (X → Y) := by
      have h' : (univ.filter fun fb : (X → Y) × Bool =>
          (cpaGuess fb.1 ρ rs fb.2 (A r) == fb.2) = true).card = Fintype.card (X → Y) := by
        omega
      exact_mod_cast h'
    exact this
  have hW_bound : ∀ ρ rs r, |W ρ rs r - Fintype.card (X → Y)| ≤ Fintype.card (X → Y) := by
    intro ρ rs r
    have h0 : 0 ≤ W ρ rs r := sum_nonneg fun _ _ => by split_ifs <;> norm_num
    have h1 : W ρ rs r ≤ 2 * Fintype.card (X → Y) := by
      calc W ρ rs r ≤ ∑ _fb : (X → Y) × Bool, (1 : ℝ) :=
            sum_le_sum fun _ _ => by split_ifs <;> norm_num
        _ = 2 * Fintype.card (X → Y) := by
            simp [Fintype.card_prod, Fintype.card_bool, mul_comm]
    rw [abs_le]
    constructor <;> linarith
  -- the success probability as an average of `W`
  have hsum : (prfRand (cpaReduction q A) true).toReal =
      (∑ ρ : Fin q → X, ∑ rs : X, ∑ r : R, W ρ rs r) / N := by
    rw [prfRand, map_uniform_toReal]
    congr 1
    simp only [W, run_cpaReduction]
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type (α₁ := Fin q → X) (α₂ := X × Bool × R),
      Fintype.sum_prod_type (α₁ := X) (α₂ := Bool × R),
      Fintype.sum_prod_type (α₁ := Bool) (α₂ := R),
      Fintype.sum_prod_type (α₁ := X → Y) (α₂ := Bool)]
    rw [sum_comm]
    refine sum_congr rfl fun ρ _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun rs _ => ?_
    exact (sum_congr rfl fun f _ => sum_comm).trans sum_comm
  have hNval : N = Fintype.card (X → Y) * 2 * Fintype.card (Fin q → X) * Fintype.card X *
      Fintype.card R := by
    simp only [N, Fintype.card_prod, Fintype.card_bool]
    push_cast
    ring
  -- the bad event: the challenge randomness repeats one of the `q` query randomness values
  have hbad : (∑ ρ : Fin q → X, ∑ rs : X, ∑ _r : R,
      (if ∀ j, ρ j ≠ rs then (0 : ℝ) else Fintype.card (X → Y))) ≤
      Fintype.card (Fin q → X) * q * Fintype.card R * Fintype.card (X → Y) := by
    have hρ : ∀ ρ : Fin q → X, (∑ rs : X, ∑ _r : R,
        (if ∀ j, ρ j ≠ rs then (0 : ℝ) else Fintype.card (X → Y))) ≤
        q * Fintype.card R * Fintype.card (X → Y) := by
      intro ρ
      simp only [sum_const, card_univ, nsmul_eq_mul]
      have hcount : ((univ.filter fun rs : X => ¬∀ j, ρ j ≠ rs).card : ℝ) ≤ q := by
        have : (univ.filter fun rs : X => ¬∀ j, ρ j ≠ rs) ⊆ univ.image ρ := by
          intro rs hrs
          simp only [mem_filter, mem_univ, true_and, not_forall, not_not] at hrs
          obtain ⟨j, hj⟩ := hrs
          exact mem_image.mpr ⟨j, mem_univ _, hj⟩
        have h1 : (univ.image ρ).card ≤ q := card_image_le.trans (by simp)
        exact_mod_cast (card_le_card this).trans h1
      calc (∑ rs : X, (Fintype.card R : ℝ) *
            (if ∀ j, ρ j ≠ rs then (0 : ℝ) else Fintype.card (X → Y)))
          = Fintype.card R * Fintype.card (X → Y) *
              (univ.filter fun rs : X => ¬∀ j, ρ j ≠ rs).card := by
            simp only [mul_ite, mul_zero]
            rw [sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul]
            ring
        _ ≤ Fintype.card R * Fintype.card (X → Y) * q :=
            mul_le_mul_of_nonneg_left hcount (by positivity)
        _ = q * Fintype.card R * Fintype.card (X → Y) := by ring
    calc _ ≤ ∑ _ρ : Fin q → X, (q : ℝ) * Fintype.card R * Fintype.card (X → Y) :=
          sum_le_sum fun ρ _ => hρ ρ
      _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]; ring
  rw [hsum]
  have hhalf : (1 : ℝ) / 2 = (∑ ρ : Fin q → X, ∑ rs : X, ∑ _r : R,
      (Fintype.card (X → Y) : ℝ)) / N := by
    simp only [sum_const, card_univ, nsmul_eq_mul, hNval]
    field_simp
  rw [hhalf, ← sub_div, abs_div, abs_of_pos hN, div_le_div_iff₀ hN (by positivity)]
  rw [← sum_sub_distrib]
  simp_rw [← sum_sub_distrib]
  calc |∑ ρ : Fin q → X, ∑ rs : X, ∑ r : R, (W ρ rs r - Fintype.card (X → Y))| *
        (2 * Fintype.card X)
      ≤ (∑ ρ : Fin q → X, ∑ rs : X, ∑ _r : R,
          (if ∀ j, ρ j ≠ rs then (0 : ℝ) else Fintype.card (X → Y))) *
          (2 * Fintype.card X) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun ρ _ => ?_)
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun rs _ => ?_)
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun r _ => ?_)
        split_ifs with hrs
        · rw [hW_good ρ rs r hrs, sub_self, abs_zero]
        · exact hW_bound ρ rs r
    _ ≤ (Fintype.card (Fin q → X) * q * Fintype.card R * Fintype.card (X → Y)) *
          (2 * Fintype.card X) := mul_le_mul_of_nonneg_right hbad (by positivity)
    _ = q * N := by rw [hNval]; ring

/-- **CPA encryption from a PRF, concrete security.** Let $K$, $X$ and $R$ be nonempty finite sets,
$Y$ a finite additive commutative group, $q$ a natural number and $F \colon K \to X \to Y$ a keyed
function, used in the scheme $\mathrm{Enc}_k(m) = (r, F_k(r) + m)$ with uniform randomness
$r \in X$. For every CPA adversary $A$ with coins in $R$, the CPA advantage of $A$ in the
experiment whose encryption oracle answers at most $q$ queries is at most the PRF advantage of $F$
against the distinguisher built from $A$ plus $q / (2 |X|)$.

This is the reduction of Katz and Lindell, Theorem 3.31, with the sharper statistical term
$q / (2 |X|)$ in place of $q / |X|$. -/
theorem cpaAdvantage_le (F : K → X → Y) (A : CPAAdversary X Y R) :
    cpaAdvantage q F A ≤ prfAdvantage F (cpaReduction q A) + q / (2 * Fintype.card X) := by
  rw [cpaAdvantage, cpaGame_eq_prfReal, prfAdvantage]
  have h := prfRand_cpaReduction (q := q) A
  calc |(prfReal F (cpaReduction q A) true).toReal - 1 / 2|
      = |((prfReal F (cpaReduction q A) true).toReal -
          (prfRand (cpaReduction q A) true).toReal) +
          ((prfRand (cpaReduction q A) true).toReal - 1 / 2)| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add le_rfl h)

end CPA

end Cslib.Crypto.PRF
