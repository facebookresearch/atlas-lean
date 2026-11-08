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

/-- The polynomial functor of one oracle: an operation is a query `x : X`, answered by `y : Y`. -/
abbrev OracleSig (X : Type u) (Y : Type v) : PFunctor.{u, v} := ⟨X, fun _ => Y⟩

/-- An adaptive deterministic oracle algorithm: a computation in CSLib's free monad over one oracle;
it either stops with an output in `α`, or asks a query in `X` and continues depending on the
answer in `Y`. -/
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

/-- The real world: the distinguisher with uniform coins `s` queries `F k` for a uniform key. -/
noncomputable def prfReal (F : K → X → Y) (D : S → OracleComp X Y Bool) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype (K × S)).map fun ω => (D ω.2).run (F ω.1)

/-- The random world: the distinguisher queries a uniformly random function `X → Y`. -/
noncomputable def prfRand (D : S → OracleComp X Y Bool) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype ((X → Y) × S)).map fun ω => (D ω.2).run ω.1

/-- The PRF advantage `|Pr[D = 1 | F k] - Pr[D = 1 | random function]|`. -/
noncomputable def prfAdvantage (F : K → X → Y) (D : S → OracleComp X Y Bool) : ℝ :=
  |(prfReal F D true).toReal - (prfRand D true).toReal|

end PRFGame

/-! ### The MAC from a PRF -/

section MAC

variable {K M T R : Type*} [Fintype K] [Nonempty K] [Fintype M] [DecidableEq M] [Fintype T]
  [Nonempty T] [DecidableEq T] [Fintype R] [Nonempty R]

/-- The forger, run with tagging oracle `O`, outputs a valid tag on a message it never
queried. -/
def MacWins (O : M → T) (c : OracleComp M T (M × T)) : Prop :=
  O (c.run O).1 = (c.run O).2 ∧ (c.run O).1 ∉ c.queries O

instance (O : M → T) (c : OracleComp M T (M × T)) : Decidable (MacWins O c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The existential-forgery experiment under an adaptive chosen-message attack for the MAC
`Mac_k(m) = F k m`: the key and the forger's coins are uniform. -/
noncomputable def macGame (F : K → M → T) (A : R → OracleComp M T (M × T)) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype (K × R)).map fun ω => decide (MacWins (F ω.1) (A ω.2))

/-- The distinguisher built from a forger: run it, logging its queries, then query the forged
message and accept when the answer is the forged tag and the message is fresh. -/
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
/-- With the oracle `F k`, the reduction runs the forgery experiment exactly. -/
theorem macGame_eq_prfReal (F : K → M → T) (A : R → OracleComp M T (M × T)) :
    macGame F A = prfReal F (fun r => macReduction [] (A r)) := by
  unfold macGame prfReal
  congr 1
  funext ω
  rw [run_macReduction, List.append_nil]
  exact decide_eq_decide.mpr Iff.rfl

omit [Nonempty T] in
/-- **Counting forgeries against a random function**: the functions against which the forger
wins number at most `|T|^|M| / |T|`, since changing the tag of the fresh forged message (which the
run never queries) gives `|T|` functions with the same run, of which exactly one is a win. -/
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

/-- With a random function, the forgery succeeds with probability at most `1 / |T|`. -/
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

/-- **The MAC from a PRF, concrete security** (the reduction of Katz and Lindell, Theorem 4.6):
the forgery probability of any adaptive chosen-message forger is at most the PRF advantage of the
reduction plus `1 / |T|`. -/
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

/-- Encryption with the keyed function `F k` (Katz and Lindell, Construction 3.30, over an
additive group of messages): with randomness `r`, `Enc(m) = (r, F k r + m)`. -/
def encrypt (Fk : X → Y) (m : Y) (r : X) : X × Y := (r, Fk r + m)

/-- Decryption: `Dec(r, c) = c - F k r`. -/
def decrypt (Fk : X → Y) (c : X × Y) : Y := c.2 - Fk c.1

omit [Fintype X] [Nonempty X] [DecidableEq X] [Fintype Y] in
/-- **Correctness**: decryption inverts encryption. -/
theorem decrypt_encrypt (Fk : X → Y) (m : Y) (r : X) : decrypt Fk (encrypt Fk m r) = m := by
  simp [decrypt, encrypt]

/-- The message selected by the challenge bit: `m.2` for `true`, `m.1` for `false`. -/
def pick (m : Y × Y) (b : Bool) : Y := if b then m.2 else m.1

/-- Run an algorithm against the encryption oracle `m ↦ (ρ i, f (ρ i) + m)`, where `ρ i` is the
encryption randomness of the `i`-th query, starting at query index `i`. The oracle answers at
most `q` queries; the run returns `none` if the algorithm asks for more, and otherwise its output
together with the next query index. -/
def runEnc {β : Type*} (f : X → Y) (ρ : Fin q → X) : OracleComp Y (X × Y) β → ℕ → Option (β × ℕ)
  | .pure a, i => some (a, i)
  | .liftBind m k, i =>
    if h : i < q then runEnc f ρ (k (encrypt f m (ρ ⟨i, h⟩))) (i + 1) else none

/-- A CPA adversary with coins `r`: an algorithm with access to the encryption oracle that
outputs two challenge messages together with the algorithm (again with oracle access) it runs on
the challenge ciphertext to guess the challenge bit. -/
abbrev CPAAdversary (X Y R : Type*) :=
  R → OracleComp Y (X × Y) ((Y × Y) × (X × Y → OracleComp Y (X × Y) Bool))

/-- The adversary's guess in the CPA experiment with keyed function `f`, encryption randomness
`ρ` for its oracle queries, challenge randomness `rs` and challenge bit `b`. An adversary that
asks more than `q` encryption queries is stopped and guesses `false`. -/
def cpaGuess (f : X → Y) (ρ : Fin q → X) (rs : X) (b : Bool)
    (c : OracleComp Y (X × Y) ((Y × Y) × (X × Y → OracleComp Y (X × Y) Bool))) : Bool :=
  ((runEnc f ρ c 0).bind fun p =>
    (runEnc f ρ (p.1.2 (encrypt f (pick p.1.1 b) rs)) p.2).map Prod.fst).getD false

variable (q) in
/-- The CPA indistinguishability experiment `PrivK^cpa` for the scheme `Enc_k(m) = (r, F k r + m)`
against adversaries making at most `q` encryption queries: the key `k`, the encryption
randomness of the queries, the challenge randomness, the challenge bit `b` and the coins are
uniform; the game outputs whether the guess equals `b`. -/
noncomputable def cpaGame (F : K → X → Y) (A : CPAAdversary X Y R) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype (K × (Fin q → X) × X × Bool × R)).map fun ω =>
    cpaGuess (F ω.1) ω.2.1 ω.2.2.1 ω.2.2.2.1 (A ω.2.2.2.2) == ω.2.2.2.1

variable (q) in
/-- The CPA advantage `|Pr[A guesses b] - 1/2|`. -/
noncomputable def cpaAdvantage (F : K → X → Y) (A : CPAAdversary X Y R) : ℝ :=
  |(cpaGame q F A true).toReal - 1 / 2|

/-- Simulate the encryption oracle with queries to an oracle for the keyed function. -/
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
/-- The PRF distinguisher built from a CPA adversary: with its own coins `(ρ, rs, b, r)` it runs
the adversary, answering encryption queries and the challenge with its oracle, and outputs
whether the adversary guessed `b`. -/
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
/-- With the oracle `F k`, the reduction runs the CPA experiment exactly. -/
theorem cpaGame_eq_prfReal (F : K → X → Y) (A : CPAAdversary X Y R) :
    cpaGame q F A = prfReal F (cpaReduction q A) := by
  unfold cpaGame prfReal
  congr 1
  funext ω
  rw [run_cpaReduction]

omit [Fintype X] [Nonempty X] [DecidableEq X] [Fintype Y] in
/-- The encryption oracle only evaluates the keyed function at the encryption randomness. -/
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

/-- **The random world**: with a random function, the adversary's success probability is within
`q / (2 |X|)` of `1/2`: it is exactly `1/2` unless the challenge randomness repeats the
randomness of one of the at most `q` encryption queries. -/
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

/-- **CPA encryption from a PRF, concrete security** (the reduction of Katz and Lindell,
Theorem 3.31): in the CPA experiment whose encryption oracle answers at most `q` queries, the
advantage of any adversary is at most the PRF advantage of the reduction plus `q / (2 |X|)`. -/
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
