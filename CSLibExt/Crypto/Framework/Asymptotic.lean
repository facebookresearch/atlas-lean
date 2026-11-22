/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Games
public import CSLibExt.Computability.Complexity.Classes

/-!
# The asymptotic bridge

The games of `CSLibExt.Crypto.Framework.Games` are **concrete**: fixed finite types, no security
parameter. Katz and Lindell state security **asymptotically** (Definition 3.4 ff.): schemes and
adversaries are families indexed by a security parameter `n`, and a scheme is secure when every
admissible (there: probabilistic polynomial-time) adversary family has negligible advantage. This
file states that shape on top of the concrete games.

* `NegligibleAdv ε`: a real advantage function `ε : ℕ → ℝ` is bounded by a negligible function in
  the sense of the repository's `Cslib.Complexity.Classes.Negligible` (which is `ℚ`-valued, so it
  is reused rather than redefined). `negligibleAdv_zero`, `NegligibleAdv.mono`,
  `NegligibleAdv.add`, `NegligibleAdv.eventually_le`, and `not_negligibleAdv_const` (a positive
  constant is not negligible).
* `AsymptoticallySecure adv Admissible`: every admissible adversary family `A` has
  `NegligibleAdv (fun n => adv n (A n))`. The class of admissible adversaries is a **parameter**.
* `AsymptoticallySecure.of_reduction`: the shape of every asymptotic security proof. A
  reduction mapping admissible adversaries against the scheme to admissible adversaries against
  the assumption, with a concrete bound `adv ≤ adv' + δ` for negligible `δ`, transfers security.
* `PolyQueryBounded`: the one admissible class the framework can define today, adversary families
  whose number of oracle queries is bounded by a polynomial in `n`. The query-bearing notions
  `PolyQueryCPASecure`, `PolyQueryCCASecure`, `PolyQueryMACSecure`, `PolyQuerySigSecure`
  instantiate `AsymptoticallySecure` with it. `PubCPASecure` instead takes the admissible class as
  an argument, because a public-key CPA adversary makes no oracle queries.
* Every instance requires nonempty message types `[∀ n, Nonempty (M n)]` and nonempty adversary
  coin types `[∀ n, Nonempty (R n)]`. Without them there may be no adversaries at all, and the
  security statement holds vacuously: an adversary carries `coins : PMF (R n)`, and there is no
  `PMF` on an empty type; a CPA or CCA adversary must output two messages, and a forger a message.
  With both hypotheses vacuity is ruled out: `exists_polyQueryBounded_cpa`,
  `exists_polyQueryBounded_cca`, `exists_polyQueryBounded_mac` and `exists_polyQueryBounded_sig`
  give an admissible adversary family for each query-bearing notion, and
  `PubCPAAdversary.nonempty` an adversary for `PubCPASecure` (whose admissible class is the
  caller's).
* `invertGame` and `winProb_invertGame`: the inversion experiment of
  `Cslib.Complexity.Classes.invertSucc` is a game in the framework's sense, and
  `IsOneWayFunction.negligibleAdv_invertGame` restates one-wayness
  (`Cslib.Complexity.Classes.IsOneWayFunction`) as negligible advantage of every polynomial-time
  inverter in that game.

**What is deferred.** There is no probabilistic polynomial-time adversary model. `IsPolyTime`
applies to functions `List Bool → List Bool` on bitstring encodings, while adversaries here are
`OracleComp` trees over arbitrary types with a coin distribution; connecting them needs an
encoding of oracle algorithms as machines, which is out of scope for this lane. Consequently:
* `PolyQueryBounded` restricts only the **number of queries**, not computation. Security against
  it is information-theoretic (in the oracle model): it is the right notion for idealized
  constructions (e.g. the PRF constructions instantiated with a truly random function), but a
  computationally secure scheme is in general **not** secure against it. Statements about real
  schemes must pass the intended admissible class (eventually: PPT) as the `Admissible` argument.
  The `PolyQuery` prefix on the instances records this; the unqualified Katz-Lindell names
  `CPASecure`, `CCASecure`, `MACSecure`, `SigSecure` are reserved for the PPT versions.
* The bridge to `IsOneWayFunction` goes in one direction only, for the inversion experiment
  itself: it does not turn an `OracleComp` adversary into a polynomial-time inverter.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Sections 3.1 (Definition 3.4, Proposition 3.6) and 7.1 (Definition 7.1).
* O. Goldreich, *Foundations of Cryptography*, Vol. 1, Cambridge University Press, 2001,
  Section 2.2.
-/

@[expose] public section

namespace Cslib.Crypto.Framework

open Cslib.Complexity.Classes MetaMathlibExt.ComplexityTheory

/-! ### Negligible advantages -/

/-- A real advantage function is **negligible** when it is bounded by a negligible function in
the sense of `Cslib.Complexity.Classes.Negligible` (Katz and Lindell, Definition 3.4). -/
def NegligibleAdv (ε : ℕ → ℝ) : Prop :=
  ∃ e : ℕ → ℚ, Negligible e ∧ ∀ n, ε n ≤ e n

/-- The zero advantage is negligible. -/
theorem negligibleAdv_zero : NegligibleAdv fun _ => 0 :=
  ⟨fun _ => 0, fun _ => ⟨0, fun _ _ => by positivity⟩, fun _ => by simp⟩

/-- A function below a negligible advantage is negligible. -/
theorem NegligibleAdv.mono {ε ε' : ℕ → ℝ} (h : NegligibleAdv ε) (h' : ∀ n, ε' n ≤ ε n) :
    NegligibleAdv ε' :=
  let ⟨e, he, hle⟩ := h
  ⟨e, he, fun n => (h' n).trans (hle n)⟩

/-- A negligible advantage is eventually below `1 / n ^ c` for every `c`. -/
theorem NegligibleAdv.eventually_le {ε : ℕ → ℝ} (h : NegligibleAdv ε) (c : ℕ) :
    ∃ N : ℕ, ∀ n, N ≤ n → ε n ≤ 1 / (n : ℝ) ^ c := by
  obtain ⟨e, he, hle⟩ := h
  obtain ⟨N, hN⟩ := he c
  refine ⟨N, fun n hn => (hle n).trans ?_⟩
  have := (Rat.cast_le (K := ℝ)).mpr (hN n hn)
  simpa using this

/-- The sum of two negligible functions is negligible (Katz and Lindell, Proposition 3.6). -/
theorem negligible_add {e₁ e₂ : ℕ → ℚ} (h₁ : Negligible e₁) (h₂ : Negligible e₂) :
    Negligible (e₁ + e₂) := by
  intro c
  obtain ⟨N₁, hN₁⟩ := h₁ (c + 1)
  obtain ⟨N₂, hN₂⟩ := h₂ (c + 1)
  refine ⟨max (max N₁ N₂) 2, fun n hn => ?_⟩
  have hn₁ : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn₂ : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn2 : (2 : ℚ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
  have hpos : (0 : ℚ) < (n : ℚ) ^ c := by positivity
  calc (e₁ + e₂) n = e₁ n + e₂ n := rfl
    _ ≤ 1 / (n : ℚ) ^ (c + 1) + 1 / (n : ℚ) ^ (c + 1) := add_le_add (hN₁ n hn₁) (hN₂ n hn₂)
    _ = (2 / n) * (1 / (n : ℚ) ^ c) := by rw [pow_succ]; field_simp; ring
    _ ≤ 1 * (1 / (n : ℚ) ^ c) := by
        gcongr
        rw [div_le_one (by linarith)]
        exact hn2
    _ = 1 / (n : ℚ) ^ c := one_mul _

/-- The sum of two negligible advantages is negligible. -/
theorem NegligibleAdv.add {ε₁ ε₂ : ℕ → ℝ} (h₁ : NegligibleAdv ε₁) (h₂ : NegligibleAdv ε₂) :
    NegligibleAdv (ε₁ + ε₂) :=
  let ⟨e₁, he₁, hle₁⟩ := h₁
  let ⟨e₂, he₂, hle₂⟩ := h₂
  ⟨e₁ + e₂, negligible_add he₁ he₂, fun n => by
    simpa using add_le_add (hle₁ n) (hle₂ n)⟩

/-- A positive constant advantage is not negligible. -/
theorem not_negligibleAdv_const {δ : ℝ} (hδ : 0 < δ) : ¬ NegligibleAdv fun _ => δ := by
  intro h
  obtain ⟨N, hN⟩ := h.eventually_le 1
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / δ)
  have hn := hN (max N m + 1) (by omega)
  have hpos : (0 : ℝ) < ((max N m + 1 : ℕ) : ℝ) := by positivity
  have hm' : (m : ℝ) < ((max N m + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : m < max N m + 1)
  rw [pow_one, le_div_iff₀ hpos] at hn
  rw [div_lt_iff₀ hδ] at hm
  nlinarith

/-! ### Asymptotic security -/

/-- **Asymptotic security** against a class of adversary families: every admissible family `A`
(one adversary `A n` per security parameter `n`) has negligible advantage `adv n (A n)`
(Katz and Lindell, the shape of Definitions 3.8, 3.22, 4.2, 11.2, 12.2). The class
`Admissible` is a parameter; see `PolyQueryBounded`. The statement is vacuous when no family is
admissible, in particular when some `Adv n` is empty (for example, adversaries whose coin type or
message type is empty); the instances below rule that out by requiring nonempty message and coin
types (see `exists_polyQueryBounded_cpa` and its siblings). -/
def AsymptoticallySecure {Adv : ℕ → Type*} (adv : (n : ℕ) → Adv n → ℝ)
    (Admissible : ((n : ℕ) → Adv n) → Prop) : Prop :=
  ∀ A, Admissible A → NegligibleAdv fun n => adv n (A n)

/-- **Security by reduction.** If `red` maps every admissible adversary family against the scheme
to an admissible family against the assumption, and the scheme advantage is at most the
assumption advantage of the reduction plus a negligible `δ`, then security of the assumption
implies security of the scheme. -/
theorem AsymptoticallySecure.of_reduction {Adv Bdv : ℕ → Type*} {adv : (n : ℕ) → Adv n → ℝ}
    {bdv : (n : ℕ) → Bdv n → ℝ} {AdmA : ((n : ℕ) → Adv n) → Prop}
    {AdmB : ((n : ℕ) → Bdv n) → Prop} (red : ((n : ℕ) → Adv n) → (n : ℕ) → Bdv n)
    (hred : ∀ A, AdmA A → AdmB (red A)) {δ : ℕ → ℝ} (hδ : NegligibleAdv δ)
    (hbound : ∀ A, AdmA A → ∀ n, adv n (A n) ≤ bdv n (red A n) + δ n)
    (hB : AsymptoticallySecure bdv AdmB) : AsymptoticallySecure adv AdmA := fun A hA =>
  ((hB _ (hred A hA)).add hδ).mono fun n => hbound A hA n

/-- Adversary families whose number of oracle queries is bounded by a polynomial in the
security parameter, for a per-`n` query-bound predicate `bounded n q a`. -/
def PolyQueryBounded {Adv : ℕ → Type*} (bounded : (n : ℕ) → ℕ → Adv n → Prop)
    (A : (n : ℕ) → Adv n) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n, bounded n (p.eval n) (A n)

section Instances

variable {M K C T PK SK S R : ℕ → Type*}

/-- **Polynomial-query CPA security** of a family of private-key schemes: the experiment of
Katz and Lindell, Definition 3.22, against adversary families making polynomially many oracle
queries with unbounded local computation. This is not the PPT notion of Definition 3.22 (see the
module docstring); the name `CPASecure` is reserved for that. The message and coin types must be
nonempty, or there would be no adversaries (`exists_polyQueryBounded_cpa`). -/
@[nolint unusedArguments]
def PolyQueryCPASecure (Sch : (n : ℕ) → SymmEncScheme (M n) (K n) (C n)) (R : ℕ → Type*)
    [∀ n, Nonempty (M n)] [∀ n, Nonempty (R n)] : Prop :=
  AsymptoticallySecure (Adv := fun n => CPAAdversary (M n) (C n) (R n))
    (fun n A => cpaAdvantage (Sch n) A)
    (PolyQueryBounded fun _ q A => A.QueryBounded q)

/-- **Polynomial-query CCA security** of a family of private-key schemes: the experiment of
Katz and Lindell, Definition 3.33, against polynomial-query adversary families. Not the PPT notion;
the name `CCASecure` is reserved for that. The message and coin types must be nonempty
(`exists_polyQueryBounded_cca`). -/
@[nolint unusedArguments]
def PolyQueryCCASecure {M K C : ℕ → Type} [∀ n, DecidableEq (C n)]
    (Sch : (n : ℕ) → SymmEncScheme (M n) (K n) (C n)) (R : ℕ → Type) [∀ n, Nonempty (M n)]
    [∀ n, Nonempty (R n)] : Prop :=
  AsymptoticallySecure (Adv := fun n => CCAAdversary (M n) (C n) (R n))
    (fun n A => ccaAdvantage (Sch n) A)
    (PolyQueryBounded fun _ q A => A.QueryBounded q)

/-- **CPA security** of a family of public-key schemes against all adversary families satisfying
`Admissible` (Katz and Lindell, Definition 11.2). Public-key CPA adversaries make no oracle
queries, so no query-count class applies; pass the intended class explicitly. With an
admissible class that bounds only queries (for example `PolyQueryBounded`), every adversary family
is admissible, so the result is security against unbounded adversaries, not the PPT notion of
Definition 11.2. The message and coin types must be nonempty (`PubCPAAdversary.nonempty`); whether
some family is admissible depends on `Admissible`. -/
@[nolint unusedArguments]
def PubCPASecure (Sch : (n : ℕ) → PKEScheme (M n) (PK n) (SK n) (C n)) (R : ℕ → Type*)
    [∀ n, Nonempty (M n)] [∀ n, Nonempty (R n)]
    (Admissible : ((n : ℕ) → PubCPAAdversary (M n) (PK n) (C n) (R n)) → Prop) : Prop :=
  AsymptoticallySecure (fun n A => pubCpaAdvantage (Sch n) A) Admissible

/-- **Polynomial-query existential unforgeability** of a family of MACs: the experiment of
Katz and Lindell, Definition 4.2, against polynomial-query forger families. Not the PPT notion;
the name `MACSecure` is reserved for that. The message and coin types must be nonempty
(`exists_polyQueryBounded_mac`). -/
@[nolint unusedArguments]
def PolyQueryMACSecure [∀ n, DecidableEq (M n)] (Sch : (n : ℕ) → MACScheme (M n) (K n) (T n))
    (R : ℕ → Type*) [∀ n, Nonempty (M n)] [∀ n, Nonempty (R n)] : Prop :=
  AsymptoticallySecure (Adv := fun n => MACForger (M n) (T n) (R n))
    (fun n A => macAdvantage (Sch n) A)
    (PolyQueryBounded fun _ q A => A.QueryBounded q)

/-- **Polynomial-query existential unforgeability** of a family of signature schemes: the
experiment of Katz and Lindell, Definition 12.2, against polynomial-query forger families. Not the
PPT notion; the name `SigSecure` is reserved for that. The message and coin types must be
nonempty (`exists_polyQueryBounded_sig`). -/
@[nolint unusedArguments]
def PolyQuerySigSecure [∀ n, DecidableEq (M n)]
    (Sch : (n : ℕ) → SigScheme (M n) (PK n) (SK n) (S n)) (R : ℕ → Type*) [∀ n, Nonempty (M n)]
    [∀ n, Nonempty (R n)] : Prop :=
  AsymptoticallySecure (Adv := fun n => SigForger (M n) (PK n) (S n) (R n))
    (fun n A => sigAdvantage (Sch n) A)
    (PolyQueryBounded fun _ q A => A.QueryBounded q)

end Instances

/-! ### Non-vacuity

With a message and a coin value, each adversary type has a member making at most one query (none
for CPA and CCA), so each query-bearing instance has an admissible adversary family. The forgers
obtain their tag or signature from one oracle query, so no tag or signature type needs to be
assumed nonempty. -/

section NonVacuity

universe u

/-- A CPA adversary making no queries: it challenges with `(m, m)` and guesses `true`. -/
theorem CPAAdversary.exists_queryBounded_zero {M C R : Type*} [Nonempty M] [Nonempty R] :
    ∃ A : CPAAdversary M C R, A.QueryBounded 0 := by
  obtain ⟨m⟩ := ‹Nonempty M›
  obtain ⟨r⟩ := ‹Nonempty R›
  exact ⟨⟨PMF.pure r, fun _ => .pure ((m, m), fun _ => .pure true)⟩, fun _ _ => trivial⟩

/-- A CCA adversary making no queries: it challenges with `(m, m)` and guesses `true`. -/
theorem CCAAdversary.exists_queryBounded_zero {M C R : Type u} [Nonempty M] [Nonempty R] :
    ∃ A : CCAAdversary M C R, A.QueryBounded 0 := by
  obtain ⟨m⟩ := ‹Nonempty M›
  obtain ⟨r⟩ := ‹Nonempty R›
  exact ⟨⟨PMF.pure r, fun _ => .pure ((m, m), fun _ => .pure true)⟩, fun _ _ => trivial⟩

/-- A public-key CPA adversary: it challenges with `(m, m)` and guesses `true`. -/
theorem PubCPAAdversary.nonempty {M PK C R : Type*} [Nonempty M] [Nonempty R] :
    Nonempty (PubCPAAdversary M PK C R) := by
  obtain ⟨m⟩ := ‹Nonempty M›
  obtain ⟨r⟩ := ‹Nonempty R›
  exact ⟨⟨PMF.pure r, fun _ _ => (m, m), fun _ _ _ => true⟩⟩

/-- A MAC forger making one query: it asks for the tag of `m` and outputs `m` with that tag. -/
theorem MACForger.exists_queryBounded_one {M T R : Type*} [Nonempty M] [Nonempty R] :
    ∃ A : MACForger M T R, A.QueryBounded 1 := by
  obtain ⟨m⟩ := ‹Nonempty M›
  obtain ⟨r⟩ := ‹Nonempty R›
  exact ⟨⟨PMF.pure r, fun _ => .liftBind m fun t => .pure (m, t)⟩, fun _ _ => trivial⟩

/-- A signature forger making one query: it asks for a signature on `m` and outputs it. -/
theorem SigForger.exists_queryBounded_one {M PK S R : Type*} [Nonempty M] [Nonempty R] :
    ∃ A : SigForger M PK S R, A.QueryBounded 1 := by
  obtain ⟨m⟩ := ‹Nonempty M›
  obtain ⟨r⟩ := ‹Nonempty R›
  exact ⟨⟨PMF.pure r, fun _ _ => .liftBind m fun s => .pure (m, s)⟩, fun _ _ _ => trivial⟩

/-- `PolyQueryCCASecure` is not vacuous: some CCA adversary family is admissible. -/
theorem exists_polyQueryBounded_cca {M C R : ℕ → Type} [∀ n, Nonempty (M n)]
    [∀ n, Nonempty (R n)] :
    ∃ A : (n : ℕ) → CCAAdversary (M n) (C n) (R n),
      PolyQueryBounded (fun _ q A => CCAAdversary.QueryBounded q A) A :=
  ⟨fun _ => Classical.choose CCAAdversary.exists_queryBounded_zero, 0, fun _ => by
    simpa using Classical.choose_spec CCAAdversary.exists_queryBounded_zero⟩

variable {M C T PK S R : ℕ → Type*} [∀ n, Nonempty (M n)] [∀ n, Nonempty (R n)]

/-- `PolyQueryCPASecure` is not vacuous: some CPA adversary family is admissible. -/
theorem exists_polyQueryBounded_cpa :
    ∃ A : (n : ℕ) → CPAAdversary (M n) (C n) (R n),
      PolyQueryBounded (fun _ q A => CPAAdversary.QueryBounded q A) A :=
  ⟨fun _ => Classical.choose CPAAdversary.exists_queryBounded_zero, 0, fun _ => by
    simpa using Classical.choose_spec CPAAdversary.exists_queryBounded_zero⟩

/-- `PolyQueryMACSecure` is not vacuous: some forger family is admissible. -/
theorem exists_polyQueryBounded_mac :
    ∃ A : (n : ℕ) → MACForger (M n) (T n) (R n),
      PolyQueryBounded (fun _ q A => MACForger.QueryBounded q A) A :=
  ⟨fun _ => Classical.choose MACForger.exists_queryBounded_one, 1, fun _ => by
    simpa using Classical.choose_spec MACForger.exists_queryBounded_one⟩

/-- `PolyQuerySigSecure` is not vacuous: some forger family is admissible. -/
theorem exists_polyQueryBounded_sig :
    ∃ A : (n : ℕ) → SigForger (M n) (PK n) (S n) (R n),
      PolyQueryBounded (fun _ q A => SigForger.QueryBounded q A) A :=
  ⟨fun _ => Classical.choose SigForger.exists_queryBounded_one, 1, fun _ => by
    simpa using Classical.choose_spec SigForger.exists_queryBounded_one⟩

end NonVacuity

/-! ### One-way functions -/

/-- The inversion experiment of `Cslib.Complexity.Classes.invertSucc` as a game: `x` and `m`
coins are uniform, and the experiment outputs `1` when the inverter's answer, decoded to `n` bits,
is a preimage of `f n x` (Katz and Lindell, the experiment `Invert`, Definition 7.1, in the
uniform-inverter form of Goldreich, Section 2.2). -/
noncomputable def invertGame (f : (n : ℕ) → (Fin n → Bool) → List Bool)
    (inv : ℕ × List Bool × List Bool → List Bool) (n m : ℕ) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype ((Fin n → Bool) × (Fin m → Bool))).map fun p =>
    decide (f n (fun i => (inv (n, f n p.1, List.ofFn p.2)).getD i.val false) = f n p.1)

/-- The inversion game succeeds with probability exactly `invertSucc`. -/
theorem winProb_invertGame (f : (n : ℕ) → (Fin n → Bool) → List Bool)
    (inv : ℕ × List Bool × List Bool → List Bool) (n m : ℕ) :
    winProb (invertGame f inv n m) = (invertSucc f inv n m : ℝ) := by
  classical
  rw [invertGame, winProb_map_uniform, invertSucc, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  simp only [decide_eq_true_eq, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, Rat.cast_div, Rat.cast_natCast, pow_add]
  push_cast
  rfl

/-- **One-wayness as negligible advantage**: if `f` is a one-way function, every polynomial-time
inverter with polynomially many coins has negligible success probability in `invertGame`. -/
theorem IsOneWayFunction.negligibleAdv_invertGame {f : (n : ℕ) → (Fin n → Bool) → List Bool}
    (hf : IsOneWayFunction f) (q : Polynomial ℕ) (inv : ℕ × List Bool × List Bool → List Bool)
    (hinv : IsPolyTime inv) : NegligibleAdv fun n => winProb (invertGame f inv n (q.eval n)) :=
  ⟨_, hf.2.2 q inv hinv, fun n => (winProb_invertGame f inv n _).le⟩

end Cslib.Crypto.Framework
