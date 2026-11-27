/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Classes
import CSLibExt.Computability.Complexity.Host

/-!
# Razborov-Rudich: the natural proofs barrier

A *natural property* is a property of Boolean functions that is constructive (decidable by
polynomial-size circuits given the truth table) and large (holding for at least a
`2 ^ (-c * n)` fraction of all `n`-bit functions). Razborov and Rudich call it *useful*
against `P/poly` when every sequence `f_n ∈ C_n` has superpolynomial circuit size: for every
`k`, `f_n` needs more than `n ^ k` gates for all large `n`. `UsefulAgainstPPoly` uses the
equivalent infinitely-often form: a family that satisfies the property at infinitely many
lengths is not in `P/poly`. (If a `P/poly` family met `C_n` infinitely often, filling the other
lengths with members of `C_n` would give a sequence in `C` that is not superpolynomial almost
everywhere; conversely a sequence in `C` that has circuits of size `n ^ k` at infinitely many
lengths, set to a constant elsewhere, is a `P/poly` family meeting `C` infinitely often.)
Changing a property at finitely many lengths preserves usefulness, so requiring largeness at
every length rather than at all large lengths loses nothing.

The Razborov–Rudich barrier rules out a natural property useful against `P/poly` under the
assumption of a pseudorandom function family in `P/poly` secure against polynomial-size
truth-table distinguishers. At each length, fix a key satisfying the property if one exists.
The resulting family is in `P/poly`: a fixed polynomial-time machine can interpret advice
encoding the key and the circuit. Usefulness then gives a length beyond which no key
satisfies the property. The constructive decider still accepts a random truth table with
probability at least the largeness density, contradicting security.

The keys here have length `n ^ 2`. With only `n` key bits, a distinguisher could compare
its input with all `2 ^ n` keyed truth tables using polynomially many gates in the table
length. It would accept every keyed table and at most a `2 ^ n / 2 ^ (2 ^ n)` fraction of
random tables. Quadratic key length gives superpolynomially many keys in the table length.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.NaturalProofs

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-- **Encoded gates.** An encoded gate of a flat Boolean circuit is a pair $(k, r)$ of a natural
number $k$ (its kind) and a list $r$ of natural numbers (its references), in the shared encoding
of gates as (kind, references) pairs. -/
abbrev NPGate := ℕ × List ℕ

/-- **Evaluation of an encoded circuit.** Given a list of encoded gates $g_0, \dots, g_{m-1}$,
each a (kind, references) pair, and a list of Booleans $a = (a_0, \dots, a_{n-1})$, this is the
list of the values of all $m$ gates, in order: each pair is decoded to a gate of a flat Boolean
circuit on $n$ inputs, and the resulting circuit is evaluated with input $i$ set to $a_i$. An
input pair $(0, [i])$ with $i \ge n$ decodes to the constant false, so it reads as false. -/
def npCircuitEval (C : List NPGate) (assign : List Bool) : List Bool :=
  circuitEval (C.map (acGateOfPair (n := assign.length)))
    (fun i => assign.getD i.val false)

/-- **Truth table.** The truth table of a Boolean function $g$ on $n$ bits is the list of the
$2^n$ values $g(x^{(0)}), g(x^{(1)}), \dots, g(x^{(2^n - 1)})$, where for $i < 2^n$ the input
$x^{(i)}$ has bit $j$ equal to the $j$-th binary digit $\lfloor i / 2^j \rfloor \bmod 2$ of $i$
(bit $0$ being the least significant), for every $j < n$. -/
def truthTable {n : ℕ} (g : (Fin n → Bool) → Bool) : List Bool :=
  List.ofFn (fun i : Fin (2 ^ n) =>
    g (fun j => decide ((i.val / 2 ^ j.val) % 2 = 1)))

/-- **Natural property.** Let $C = (C_n)_{n \in \mathbb{N}}$, where $C_n$ is a set of Boolean
functions on $n$ bits. Then $C$ is natural when it is constructive and large. Constructive: there
are a polynomial $q$ with natural-number coefficients and, for every $n$, a circuit given as a
list of at most $q(2^n)$ encoded gates, such that a Boolean function $g$ on $n$ bits lies in $C_n$
if and only if the evaluation of the circuit on the truth table of $g$ has last gate value true.
Large: there is a natural number $c$ such that $|C_n| \ge 2^{2^n} / 2^{cn}$ for every $n$, that is,
$C_n$ contains at least a $2^{-cn}$ fraction of the $2^{2^n}$ Boolean functions on $n$ bits. -/
def NaturalProperty (C : (n : ℕ) → Set ((Fin n → Bool) → Bool)) : Prop :=
  (∃ (D : (n : ℕ) → List Bool → Bool) (q : Polynomial ℕ),
    (∀ n, ∃ Circ : List NPGate, Circ.length ≤ q.eval (2 ^ n) ∧
      ∀ t, (npCircuitEval Circ t).getLast? = some (D n t)) ∧
    ∀ n g, g ∈ C n ↔ D n (truthTable g) = true) ∧
  ∃ c : ℕ, ∀ n, ((2 ^ (2 ^ n) : ℕ) : ℚ) / (2 : ℚ) ^ (c * n) ≤ (Set.ncard (C n) : ℚ)

/-- **The decision problem of a family of Boolean functions.** For a family
$f = (f_n)_{n \in \mathbb{N}}$, where $f_n$ is a Boolean function on $n$ bits, this is the decision
problem that maps a bitstring $x = x_0 x_1 \cdots x_{n-1}$ of length $n$ to
$f_n(x_0, \dots, x_{n-1})$. -/
def langOfFamily (f : (n : ℕ) → (Fin n → Bool) → Bool) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem :=
  fun x => f x.length (fun i => x.getD i.val false)

/-- **Usefulness against P/poly.** Let $C = (C_n)_{n \in \mathbb{N}}$, where $C_n$ is a set of
Boolean functions on $n$ bits. Then $C$ is useful against P/poly when, for every family
$f = (f_n)_{n \in \mathbb{N}}$ of Boolean functions $f_n$ on $n$ bits such that $f_n \in C_n$ for
infinitely many $n$, the decision problem of $f$ is not in P/poly. Equivalently, if the decision
problem of a family $f$ is in P/poly, then $f_n \in C_n$ for only finitely many $n$. -/
def UsefulAgainstPPoly (C : (n : ℕ) → Set ((Fin n → Bool) → Bool)) : Prop :=
  ∀ f : (n : ℕ) → (Fin n → Bool) → Bool,
    Set.Infinite {n | f n ∈ C n} → langOfFamily f ∉ PPoly

/-- **Keyed function families in P/poly.** Let $F = (F_n)_{n \in \mathbb{N}}$ be a keyed family of
Boolean functions: $F_n(k, x)$ is a Boolean value for every key $k \in \{0,1\}^{n^2}$ and every
input $x \in \{0,1\}^n$. Then $F$ is in P/poly when there is a polynomial $p$ with natural-number
coefficients such that for every $n$ some circuit, given as a list of at most $p(n)$ encoded
gates, computes $F_n$: for all $k$ and $x$, the evaluation of the circuit on the bitstring $kx$ of
length $n^2 + n$ (the bits of $k$ followed by the bits of $x$) has last gate value $F_n(k, x)$. -/
def PRFInPPoly (F : (n : ℕ) → (Fin (n ^ 2) → Bool) → (Fin n → Bool) → Bool) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n, ∃ Circ : List NPGate, Circ.length ≤ p.eval n ∧
    ∀ key input, (npCircuitEval Circ (List.ofFn key ++ List.ofFn input)).getLast? =
      some (F n key input)

/-- **Security of a keyed function family against truth-table distinguishers.** Let
$F = (F_n)_{n \in \mathbb{N}}$ be a keyed family of Boolean functions: $F_n(k, x)$ is a Boolean
value for every key $k \in \{0,1\}^{n^2}$ and every input $x \in \{0,1\}^n$. Write $F_{n,k}$ for the
Boolean function $x \mapsto F_n(k, x)$ on $n$ bits and $T(g)$ for the truth table of a Boolean
function $g$. Then $F$ is secure when the following holds for every polynomial $q$ with
natural-number coefficients and every sequence $(D_n)_{n \in \mathbb{N}}$ of functions from
bitstrings to Booleans such that, for each $n$, some circuit given as a list of at most $q(2^n)$
encoded gates has last gate value $D_n(t)$ on every bitstring $t$: for every natural number $c$
there is a natural number $N$ such that for every $n \ge N$

$$\left| \frac{|\{k \in \{0,1\}^{n^2} : D_n(T(F_{n,k})) = \mathrm{true}\}|}{2^{n^2}} -
\frac{|\{g : D_n(T(g)) = \mathrm{true}\}|}{2^{2^n}} \right| \le \frac{1}{2^{nc}},$$

where $g$ ranges over all $2^{2^n}$ Boolean functions on $n$ bits. That is, a distinguisher
computed by circuits of size polynomial in the truth-table size $2^n$ tells the function
$F_{n,k}$ for a uniformly random key $k$ from a uniformly random Boolean function with advantage
at most $2^{-cn}$ for all large $n$, for every $c$. -/
def PRFSecure (F : (n : ℕ) → (Fin (n ^ 2) → Bool) → (Fin n → Bool) → Bool) : Prop :=
  ∀ (D : (n : ℕ) → List Bool → Bool) (q : Polynomial ℕ),
    (∀ n, ∃ Circ : List NPGate, Circ.length ≤ q.eval (2 ^ n) ∧
      ∀ t, (npCircuitEval Circ t).getLast? = some (D n t)) →
    ∀ c : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |(Set.ncard {k : Fin (n ^ 2) → Bool | D n (truthTable (F n k)) = true} : ℚ) /
          (2 : ℚ) ^ (n ^ 2) -
        (Set.ncard {g : (Fin n → Bool) → Bool | D n (truthTable g) = true} : ℚ) /
          (2 : ℚ) ^ (2 ^ n)| ≤ 1 / (2 : ℚ) ^ (n * c)

/-! ### A fixed polynomial-time interpreter for circuit advice

The advice is a straight-line program. Its data stack initially contains the input bits.
It pushes the key bits, then one value per circuit gate. A scratch stack lets it read a
previous value and restore the data stack. Each three-bit instruction takes one machine step.
-/

open Turing MetaMathlibExt.TM2Program Cslib.Complexity

private inductive Op where
  | left | right | meet | join | zero | one | neg | save

private structure Store where
  acc : Bool
  data : List Bool
  temp : List Bool

private def act : Op → Store → Store
  | .left, ⟨a, d, t⟩ => ⟨a, d.tail, d.headD false :: t⟩
  | .right, ⟨a, d, t⟩ => ⟨a, t.headD false :: d, t.tail⟩
  | .meet, s => { s with acc := s.acc && s.data.headD false }
  | .join, s => { s with acc := s.acc || s.data.headD false }
  | .zero, s => { s with acc := false }
  | .one, s => { s with acc := true }
  | .neg, s => { s with acc := !s.acc }
  | .save, s => { s with data := s.acc :: s.data }

private def execute (ops : List Op) (s : Store) := ops.foldl (flip act) s

private def decode : Bool → Bool → Bool → Op
  | false, false, false => .left
  | false, false, true  => .right
  | false, true,  false => .meet
  | false, true,  true  => .join
  | true,  false, false => .zero
  | true,  false, true  => .one
  | true,  true,  false => .neg
  | true,  true,  true  => .save

private def bits : Op → List Bool
  | .left => [false, false, false]
  | .right => [false, false, true]
  | .meet => [false, true, false]
  | .join => [false, true, true]
  | .zero => [true, false, false]
  | .one => [true, false, true]
  | .neg => [true, true, false]
  | .save => [true, true, true]

private def parse : List Bool → List Op
  | b :: c :: d :: w => decode b c d :: parse w
  | _ => []

private theorem parse_bits (ops : List Op) : parse (ops.flatMap bits) = ops := by
  induction ops with
  | nil => rfl
  | cons o os ih => cases o <;> simp [bits, parse, decode, ih]

private theorem bits_length (ops : List Op) : (ops.flatMap bits).length = 3 * ops.length := by
  induction ops with
  | nil => rfl
  | cons o os ih => cases o <;> simp [bits, ih, Nat.mul_succ]

-- Stack indices are advice, data, and scratch. Running and exit labels both carry the accumulator.
private abbrev Stmt := TM2.Stmt (fun _ : Option Bool => Bool) (Bool × Bool) Bool

private def resumeWith (a : Bool) : Stmt := .goto (fun _ => (false, a))

private def instruction (a : Bool) : Op → Stmt
  | .left => .pop (some false) (fun _ b => b.getD false)
      (.push (some true) id (resumeWith a))
  | .right => .pop (some true) (fun _ b => b.getD false)
      (.push (some false) id (resumeWith a))
  | .meet => .peek (some false) (fun _ b => a && b.getD false) (.goto fun v => (false, v))
  | .join => .peek (some false) (fun _ b => a || b.getD false) (.goto fun v => (false, v))
  | .zero => resumeWith false
  | .one => resumeWith true
  | .neg => resumeWith (!a)
  | .save => .push (some false) (fun _ => a) (resumeWith a)

private def readBit (a : Bool) (next : Bool → Stmt) : Stmt :=
  .peek none (fun _ b => b.isSome) (.branch id
    (.pop none (fun _ b => b.getD false) (.branch id (next true) (next false)))
    (.goto fun _ => (true, a)))

private abbrev machine : Host.Comp where
  K := Option Bool
  Γ _ := Bool
  L := Bool × Bool
  prog
    | (true, _) => .halt
    | (false, a) => readBit a fun b => readBit a fun c => readBit a fun d =>
        instruction a (decode b c d)
  ks := [none, some false, some true]
  ks_nodup := by decide
  mem_ks k := by rcases k with _ | ⟨_ | _⟩ <;> decide

private def tapes (w d t : List Bool) : Option Bool → List Bool
  | none => w
  | some false => d
  | some true => t

private theorem update_advice (w d t u) :
    Function.update (tapes w d t) none u = tapes u d t := by
  funext k
  rcases k with _ | ⟨_ | _⟩ <;> rfl

private theorem update_data (w d t u) :
    Function.update (tapes w d t) (some false) u = tapes w u t := by
  funext k
  rcases k with _ | ⟨_ | _⟩ <;> rfl

private theorem update_temp (w d t u) :
    Function.update (tapes w d t) (some true) u = tapes w d u := by
  funext k
  rcases k with _ | ⟨_ | _⟩ <;> rfl

private theorem instruction_step (o : Op) (w : List Bool) (s : Store) (v : Bool) :
    ∃ v', Run machine.prog 1
      ⟨some (false, s.acc), v, tapes (bits o ++ w) s.data s.temp⟩
      ⟨some (false, (act o s).acc), v', tapes w (act o s).data (act o s).temp⟩ := by
  obtain ⟨a, d, t⟩ := s
  refine ⟨(TM2.stepAux (machine.prog (false, a)) v (tapes (bits o ++ w) d t)).var, Run.single ?_⟩
  cases o <;>
    simp [machine, bits, readBit, instruction, resumeWith, decode, act, TM2.stepAux,
      update_advice, update_data, update_temp, tapes]

private theorem machine_run (w : List Bool) (s : Store) (v : Bool) :
    ∃ v' S', RunLe machine.prog (w.length + 1)
      ⟨some (false, s.acc), v, tapes w s.data s.temp⟩
      ⟨some (true, (execute (parse w) s).acc), v', S'⟩ := by
  match w with
  | [] | [b] | [b, c] =>
    refine ⟨false, tapes [] s.data s.temp, (Run.single ?_).le (by simp)⟩
    try cases b <;> try cases c
    all_goals simp [machine, readBit, TM2.stepAux, update_advice, tapes, parse, execute]
  | b :: c :: d :: w =>
    let o := decode b c d
    obtain ⟨v₁, h₁⟩ := instruction_step o w s v
    have he : bits o = [b, c, d] := by cases b <;> cases c <;> cases d <;> rfl
    rw [he] at h₁
    obtain ⟨v', S', h₂⟩ := machine_run w (act o s) v₁
    exact ⟨v', S', ((h₁.le le_rfl).trans h₂).mono (by simp; omega)⟩

private def answer (x w : List Bool) : Bool := (execute (parse w) ⟨false, x, []⟩).acc

private theorem answer_polyTime : IsPolyTime (fun q : List Bool × List Bool => answer q.1 q.2) := by
  apply Host.isPolyTime_verifier (c := machine) (cX := some false) (cW := none)
    (gX := id) (gW := id) (start := (false, false)) (yes := (true, true)) (no := (true, false))
    answer (Polynomial.X + 1) (by decide) (by decide) rfl rfl
  intro x w
  obtain ⟨v, S, h⟩ := machine_run w ⟨false, x, []⟩ false
  refine ⟨v, S, ?_⟩
  have he : Function.update (Function.update (fun _ => []) (some false) x) none w =
      tapes w x [] := by funext k; rcases k with _ | ⟨_ | _⟩ <;> rfl
  simp only [List.map_id, he, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  rw [show (if answer x w then (true, true) else (true, false)) = (true, answer x w) by
    cases answer x w <;> rfl]
  exact h.mono (by omega)

/-! ### Compiling gates to polynomial-length advice -/

private theorem execute_append (p q : List Op) (s : Store) :
    execute (p ++ q) s = execute q (execute p s) := List.foldl_append

private def combine (disj a b : Bool) := if disj then a || b else a && b

private def inspectBit (disj : Bool) : ℕ → List Op
  | 0 => [if disj then .join else .meet]
  | k + 1 => .left :: inspectBit disj k ++ [.right]

private theorem inspect_length (b : Bool) (k : ℕ) : (inspectBit b k).length = 2 * k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [inspectBit, ih]; omega

private theorem inspect_run (b a : Bool) (d t : List Bool) (k : ℕ) (hk : k < d.length) :
    execute (inspectBit b k) ⟨a, d, t⟩ = ⟨combine b a (d.getD k false), d, t⟩ := by
  induction k generalizing d t with
  | zero => cases d with
    | nil => simp at hk
    | cons x xs => cases b <;> rfl
  | succ k ih =>
    cases d with
    | nil => simp at hk
    | cons x xs =>
      have h : k < xs.length := by simpa using hk
      change execute (inspectBit b k ++ [.right]) ⟨a, xs, x :: t⟩ = _
      rw [execute_append, ih _ _ h]
      rfl

private def setBit (b : Bool) : Op := if b then .one else .zero

private theorem set_run (b : Bool) (s : Store) : act (setBit b) s = { s with acc := b } := by
  cases b <;> rfl

-- Forward and missing references read false. The address m represents all of them.
private def readRef (disj : Bool) (m i : ℕ) : List Op :=
  if i < m then inspectBit disj (m - 1 - i) else if disj then [] else [.zero]

private theorem readRef_run (b a : Bool) (vs x t : List Bool) (i : ℕ) :
    execute (readRef b vs.length i) ⟨a, vs.reverse ++ x, t⟩ =
      ⟨combine b a (vs.getD i false), vs.reverse ++ x, t⟩ := by
  by_cases hi : i < vs.length
  · have hk : vs.length - 1 - i < vs.length := by omega
    simp only [readRef, hi, ↓reduceIte]
    rw [inspect_run _ _ _ _ _ (by simp; omega),
      List.getD_append _ _ _ _ (by simpa using hk), List.getD_reverse _ hk]
    congr 3
    omega
  · simp only [readRef, hi, ↓reduceIte, List.getD_eq_default vs false (Nat.le_of_not_gt hi)]
    cases b <;> cases a <;> rfl

private theorem readRef_length (b : Bool) (m i : ℕ) :
    (readRef b m i).length ≤ 2 * m + 1 := by
  unfold readRef
  split
  · rw [inspect_length]; omega
  · cases b <;> simp

private def aggregate (b : Bool) (r : List ℕ) (f : ℕ → Bool) :=
  if b then r.any f else r.all f

private theorem refs_run (b a : Bool) (vs x t : List Bool) (r : List ℕ) :
    execute (r.flatMap (readRef b vs.length)) ⟨a, vs.reverse ++ x, t⟩ =
      ⟨combine b a (aggregate b r (fun i => vs.getD i false)), vs.reverse ++ x, t⟩ := by
  induction r generalizing a with
  | nil => cases b <;> simp [aggregate, combine, execute]
  | cons i r ih =>
    rw [List.flatMap_cons, execute_append, readRef_run, ih]
    cases b <;> simp [aggregate, combine, Bool.and_assoc, Bool.or_assoc]

private def addresses (m : ℕ) (r : List ℕ) : List ℕ :=
  (r.map (min m)).dedup

private theorem addresses_length (m : ℕ) (r : List ℕ) : (addresses m r).length ≤ m + 1 := by
  unfold addresses
  rw [← List.toFinset_card_of_nodup (List.nodup_dedup _)]
  apply (Finset.card_le_card (t := Finset.range (m + 1)) ?_).trans (by simp)
  intro i hi
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp (List.mem_toFinset.mp hi))
  simp

private theorem aggregate_addresses (b : Bool) (vs : List Bool) (r : List ℕ) :
    aggregate b (addresses vs.length r) (fun i => vs.getD i false) =
      aggregate b r (fun i => vs.getD i false) := by
  have hc (i : ℕ) : vs.getD (min vs.length i) false = vs.getD i false := by
    rcases le_total i vs.length with h | h
    · rw [min_eq_right h]
    · rw [min_eq_left h, List.getD_eq_default _ _ h, List.getD_eq_default _ _ le_rfl]
  simp only [List.getD_eq_getElem?_getD] at hc
  cases b <;> apply Bool.eq_iff_iff.mpr <;>
    simp [aggregate, addresses, List.all_eq_true, List.any_eq_true, hc]

private def manyRefs (b : Bool) (m : ℕ) (r : List ℕ) : List Op :=
  setBit (!b) :: (addresses m r).flatMap (readRef b m)

private theorem manyRefs_run (b a : Bool) (vs x t : List Bool) (r : List ℕ) :
    execute (manyRefs b vs.length r) ⟨a, vs.reverse ++ x, t⟩ =
      ⟨aggregate b r (fun i => vs.getD i false), vs.reverse ++ x, t⟩ := by
  change execute ((addresses vs.length r).flatMap (readRef b vs.length)) (act (setBit (!b)) _) = _
  rw [set_run, refs_run, aggregate_addresses]
  cases b <;> simp [combine]

private theorem flatMap_length_le {α β : Type} {f : α → List β} (l : List α) {k : ℕ}
    (h : ∀ z, (f z).length ≤ k) : (l.flatMap f).length ≤ l.length * k := by
  induction l with
  | nil => simp
  | cons z l ih => simpa [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add (h z) ih

private theorem manyRefs_length (b : Bool) (m : ℕ) (r : List ℕ) :
    (manyRefs b m r).length ≤ (m + 1) * (2 * m + 1) + 1 := by
  apply Nat.succ_le_succ
  exact (flatMap_length_le _ (readRef_length b m)).trans
    (Nat.mul_le_mul_right _ (addresses_length m r))

private def gateOps {n : ℕ} (m : ℕ) : ACGate n → List Op
  | .var i => .one :: inspectBit false (m + i)
  | .const b => [setBit b]
  | .notGate i => .one :: readRef false m i ++ [.neg]
  | .andGate r => manyRefs false m r
  | .orGate r => manyRefs true m r
  | .modGate _ _ => [.zero]

private def supported {n : ℕ} : ACGate n → Prop
  | .modGate _ _ => False
  | _ => True

private theorem decoded_supported (n : ℕ) (g : NPGate) :
    supported (acGateOfPair (n := n) g) := by
  fun_cases acGateOfPair (n := n) g <;> simp_all [supported]

private theorem gateOps_run (vs x t : List Bool) (a : Bool) (g : ACGate x.length)
    (hg : supported g) :
    execute (gateOps vs.length g) ⟨a, vs.reverse ++ x, t⟩ =
      ⟨gateValue vs (fun i => x.getD i.val false) g, vs.reverse ++ x, t⟩ := by
  cases g with
  | var i =>
    change execute (inspectBit false (vs.length + i.val)) ⟨true, vs.reverse ++ x, t⟩ = _
    rw [inspect_run _ _ _ _ _ (by simp),
      List.getD_append_right _ _ _ _ (by simp)]
    simp [combine, gateValue]
  | const b => cases b <;> rfl
  | notGate i =>
    change execute (readRef false vs.length i ++ [.neg]) ⟨true, vs.reverse ++ x, t⟩ = _
    rw [execute_append, readRef_run]
    simp [combine, execute, flip, act, gateValue]
  | andGate r => exact manyRefs_run false a vs x t r
  | orGate r => exact manyRefs_run true a vs x t r
  | modGate m r => exact hg.elim

private def gateBound (n m : ℕ) := (n + m + 1) * (2 * (n + m) + 1) + 3

private theorem gateOps_length {n : ℕ} (m : ℕ) (g : ACGate n) :
    (gateOps m g).length + 1 ≤ gateBound n m := by
  cases g with
  | var i =>
    simp [gateOps, inspect_length, gateBound]
    have := i.isLt
    nlinarith
  | notGate i =>
    have := readRef_length false m i
    simp [gateOps, gateBound]
    nlinarith
  | andGate r =>
    have := manyRefs_length false m r
    simp only [gateOps, gateBound]
    nlinarith
  | orGate r =>
    have := manyRefs_length true m r
    simp only [gateOps, gateBound]
    nlinarith
  | const b | modGate _ _ => simp [gateOps, gateBound]

private def compileFrom {n : ℕ} (m : ℕ) : List (ACGate n) → List Op
  | [] => []
  | g :: gs => gateOps m g ++ .save :: compileFrom (m + 1) gs

private theorem compileFrom_run (x vs : List Bool) (gs : List (ACGate x.length))
    (hg : ∀ g ∈ gs, supported g) :
    let out := gs.foldl (fun v g => v ++ [gateValue v (fun i => x.getD i.val false) g]) vs
    execute (compileFrom vs.length gs) ⟨vs.getLast?.getD false, vs.reverse ++ x, []⟩ =
      ⟨out.getLast?.getD false, out.reverse ++ x, []⟩ := by
  induction gs generalizing vs with
  | nil => rfl
  | cons g gs ih =>
    let z := gateValue vs (fun i => x.getD i.val false) g
    specialize ih (vs ++ [z]) (fun g' h => hg g' (List.mem_cons_of_mem _ h))
    simp only [compileFrom, execute_append, gateOps_run _ _ _ _ _ (hg g (by simp))]
    simpa [List.foldl_cons, z, execute, flip, act] using ih

private theorem compileFrom_length {n : ℕ} (gs : List (ACGate n)) (m : ℕ) :
    (compileFrom m gs).length ≤ gs.length * gateBound n (m + gs.length) := by
  induction gs generalizing m with
  | nil => simp [compileFrom]
  | cons g gs ih =>
    have h := ih (m + 1)
    have he : m + 1 + gs.length = m + (g :: gs).length := by simp; omega
    rw [he] at h
    have hb : gateBound n m ≤ gateBound n (m + (g :: gs).length) := by
      unfold gateBound
      gcongr <;> omega
    have hgate := (gateOps_length m g).trans hb
    simp only [compileFrom, List.length_append, List.length_cons, Nat.succ_mul] at *
    omega

private def keyOps : List Bool → List Op
  | [] => []
  | b :: bs => keyOps bs ++ [setBit b, .save]

private theorem keyOps_run (k x : List Bool) :
    execute (keyOps k) ⟨false, x, []⟩ = ⟨k.headD false, k ++ x, []⟩ := by
  induction k with
  | nil => rfl
  | cons b bs ih =>
    rw [keyOps, execute_append, ih]
    cases b <;> rfl

private theorem keyOps_length (k : List Bool) : (keyOps k).length = 2 * k.length := by
  induction k with
  | nil => rfl
  | cons b bs ih => simp [keyOps, ih]; omega

private def adviceBits (n : ℕ) (key : List Bool) (C : List NPGate) : List Bool :=
  ((keyOps key ++ [Op.zero]) ++ compileFrom 0 (C.map (acGateOfPair (n := key.length + n)))).flatMap
    bits

private theorem answer_advice (key x : List Bool) (C : List NPGate) :
    answer x (adviceBits x.length key C) = (npCircuitEval C (key ++ x)).getLast?.getD false := by
  let input := key ++ x
  have h := compileFrom_run input [] (C.map (acGateOfPair (n := input.length))) (by
    intro g hg
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hg
    exact decoded_supported _ _)
  simp only [answer, adviceBits, parse_bits, execute_append, keyOps_run]
  rw [← List.length_append]
  simpa [input, execute, flip, act, circuitEval, npCircuitEval] using congrArg Store.acc h

private theorem adviceBits_length (n : ℕ) (key : List Bool) (C : List NPGate) :
    (adviceBits n key C).length ≤
      3 * (2 * key.length + 1 + C.length * gateBound (key.length + n) C.length) := by
  have h := compileFrom_length (C.map (acGateOfPair (n := key.length + n))) 0
  simp only [List.length_map, Nat.zero_add] at h
  simp only [adviceBits, bits_length, List.length_append, List.length_singleton, keyOps_length]
  exact
    Nat.mul_le_mul_left 3 (Nat.add_le_add_left h (2 * key.length + 1))

private theorem fixedKey_mem_PPoly
    {F : (n : ℕ) → (Fin (n ^ 2) → Bool) → (Fin n → Bool) → Bool} (hF : PRFInPPoly F)
    (key : (n : ℕ) → Fin (n ^ 2) → Bool) :
    langOfFamily (fun n => F n (key n)) ∈ PPoly := by
  obtain ⟨p, hp⟩ := hF
  choose C hsize hcorrect using hp
  let k : Polynomial ℕ := Polynomial.X ^ 2
  let s := k + Polynomial.X + p
  refine ⟨3 * (2 * k + 1 + p * ((s + 1) * (2 * s + 1) + 3)),
    fun n => adviceBits n (List.ofFn (key n)) (C n), ?_,
    fun q => answer q.1 q.2, answer_polyTime, ?_⟩
  · intro n
    apply (adviceBits_length ..).trans
    simp only [List.length_ofFn, gateBound, s, k, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X]
    gcongr <;> exact hsize n
  · intro x
    let input (i : Fin x.length) := x.getD i.val false
    have he : List.ofFn input = x := by
      apply List.ext_getElem <;> simp [input]
    have h := hcorrect x.length (key x.length) input
    rw [he] at h
    simp only [answer_advice, h, Option.getD_some]
    rfl

/-- **Razborov-Rudich: the natural proofs barrier.** Let $F = (F_n)_{n \in \mathbb{N}}$ be a keyed
family of Boolean functions, where $F_n(k, x)$ is a Boolean value for every key
$k \in \{0,1\}^{n^2}$ and every input $x \in \{0,1\}^n$. If $F$ is in P/poly (computed by circuits
of size polynomial in $n$) and is secure against truth-table distinguishers, then there is no
property $C = (C_n)_{n \in \mathbb{N}}$, with $C_n$ a set of Boolean functions on $n$ bits, that
is both natural and useful against P/poly.

Source: A. A. Razborov and S. Rudich,
"Natural proofs", Journal of Computer and System Sciences 55 (1997), 24-35 (Proceedings of
the Twenty-Sixth Annual ACM Symposium on Theory of Computing, STOC 1994, 18-27). -/
public theorem razborov_rudich_natural_proofs :
    ∀ F : (n : ℕ) → (Fin (n ^ 2) → Bool) → (Fin n → Bool) → Bool,
      PRFInPPoly F → PRFSecure F →
        ¬ ∃ C : (n : ℕ) → Set ((Fin n → Bool) → Bool),
          NaturalProperty C ∧ UsefulAgainstPPoly C := by
  classical
  intro F hF secure ⟨C, ⟨⟨D, q, hq, hD⟩, c, large⟩, useful⟩
  -- Select an accepted key at every length where one exists.
  let key (n : ℕ) : Fin (n ^ 2) → Bool :=
    if h : ∃ k, F n k ∈ C n then h.choose else fun _ => false
  have finite : Set.Finite {n | F n (key n) ∈ C n} := by
    by_contra hi
    exact useful _ hi (fixedKey_mem_PPoly hF key)
  obtain ⟨B, hB⟩ := finite.bddAbove
  obtain ⟨N, hN⟩ := secure D q hq (c + 1)
  let n := max B N + 1
  have hBn : B < n := by dsimp [n]; omega
  have advantage := hN n (by dsimp [n]; omega)
  have empty : {k | D n (truthTable (F n k)) = true} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro k hk
    have hex : ∃ k, F n k ∈ C n := ⟨k, (hD n _).mpr hk⟩
    have hmem : F n (key n) ∈ C n := by simpa [key, hex] using hex.choose_spec
    exact hBn.not_ge (hB hmem)
  have accepts : {g | D n (truthTable g) = true} = C n := by
    ext g
    exact (hD n g).symm
  rw [empty, accepts] at advantage
  simp only [Set.ncard_empty, Nat.cast_zero, zero_div, zero_sub, abs_neg,
    abs_of_nonneg (by positivity : (0 : ℚ) ≤ (C n).ncard / (2 : ℚ) ^ (2 ^ n))] at advantage
  have density := large n
  push_cast at density
  have lower : 1 / (2 : ℚ) ^ (c * n) ≤ (C n).ncard / (2 : ℚ) ^ (2 ^ n) := by
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using density
  apply (not_lt_of_ge (lower.trans advantage))
  apply one_div_lt_one_div_of_lt (by positivity)
  apply pow_lt_pow_right₀ (by norm_num)
  rw [Nat.mul_succ n c, Nat.mul_comm c n]
  omega

end MetaMathlibExt.Complexity.KeyTheorems.NaturalProofs
