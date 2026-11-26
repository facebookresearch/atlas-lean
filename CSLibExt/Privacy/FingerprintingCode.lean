/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Fingerprinting codes and the tracing game

This module defines finite binary fingerprinting codes and the tracing game, in which a coalition
of users combines its codewords into a word that tracing must trace back to a member. A code
(`FingerprintingCode`) is a generator, which draws a codebook (`Codebook`) together with a key that
it shares with tracing, and a tracing algorithm, which maps the key and a word (`Word`) to an
accused user or to `none`, read as ⊥. A coalition sees only its own codewords (`submatrix`), a
pirate strategy (`Pirate`) maps them to a distribution on words, and `tracingGame` samples the
codebook, the key, the pirate's word and the accusation.

`Feasible` is the set F(C_S) of feasible words of Bun, Ullman and Vadhan, `ErrorRobustFeasible`
their relaxed set F_β(C_S) written without division, and `MarkingFeasible` the marking condition
of Tardos; `feasible_iff_markingFeasible` and `errorRobustFeasible_zero_iff` relate the three.
The security predicates bound the error probabilities of the tracing game for nonempty coalitions
of size at most `c`: `IsFingerprintingSecure` and `IsErrorRobustFingerprintingSecure` bound
completeness and soundness separately, after Definitions 3.1, 3.3 and 3.12 of Bun, Ullman and
Vadhan, and `IsFingerprintingSecureCombined` bounds the combined failure of Vadhan's
Definition 5.17 and Tardos's Definition 1.1. Codebook generation from a bias vector
(`bernoulliPMF`, `biasCodebookPMF`, `pmfIID`, `genFromBiasVectorDist`, `genFromIIDBiasDist`) and
linear accusation (`tardosWeight`, `tardosScore`, `TardosAccuses`) follow Tardos's construction.

## Implementation notes

* Coalitions are nonempty and of size at most `c`, as in Tardos's Definition 1.1, while Bun,
  Ullman and Vadhan quantify over every coalition, the empty one included, in Definitions 3.1
  and 3.3, and over coalitions with `n - 1 ≤ |S|` in Definition 3.12. So `IsFingerprintingSecure`
  is weaker than their Definition 3.1, even for `c = n` and equal errors.
* Biases are points of Mathlib's `unitInterval`, and bias distributions are discrete (`PMF`);
  Tardos draws his biases from a continuous distribution.
* The bias generators emit the bias vector as the key. A code whose tracing also reads the
  codebook, as Tardos's does, needs a key that holds the codebook too.

## References

* M. Bun, J. Ullman and S. Vadhan, *Fingerprinting codes and the price of approximate
  differential privacy*, SIAM J. Comput. 47(5):1888–1938, 2018, numbered as in
  arXiv:1311.3158v3: Section 3.1 (the feasible sets F(C_S) and F_β(C_S), Definitions 3.1
  and 3.3) and Section 3.3 (Definition 3.12).
* G. Tardos, *Optimal probabilistic fingerprint codes*, J. ACM 55(2), 2008: Section 1.2
  (Definition 1.1) and Section 2.1 (the construction).
* S. Vadhan, *The complexity of differential privacy*, in Y. Lindell (ed.), *Tutorials on the
  Foundations of Cryptography*, Springer, 2017, 347–450: Section 5.3, Definitions 5.16 and 5.17,
  numbered as in the author's version of 9 August 2016,
  <https://privacytools.seas.harvard.edu/files/privacytools/files/manuscript_2016.pdf>.
-/

@[expose] public section

namespace CSLibExt.Privacy.Fingerprinting

open scoped ENNReal

/-! ### Core types -/

/-- **Binary word.** A word of length $d$ is a string in $\{0, 1\}^d$, given as a function
`Fin d → Bool`, with `true` for $1$. -/
abbrev Word (d : ℕ) : Type := Fin d → Bool

/-- **Codebook.** A codebook for $n$ users of length $d$ is a matrix $C \in \{0, 1\}^{n \times d}$,
given as the function that maps each user $i$ to its codeword, the row $c_i$. -/
abbrev Codebook (n d : ℕ) : Type := Fin n → Word d

/-- **Codewords of a coalition.** For a codebook $C$ and a coalition $S$ of users, $C_S$ is the
family of the codewords $c_i$ of the members $i \in S$, indexed by the members: the part of $C$
that the coalition sees. -/
def submatrix {n d : ℕ} (C : Codebook n d) (S : Finset (Fin n)) :
    {i : Fin n // i ∈ S} → Word d :=
  fun i => C i.1

@[simp]
theorem submatrix_apply {n d : ℕ} (C : Codebook n d) (S : Finset (Fin n))
    (i : {i : Fin n // i ∈ S}) :
    submatrix C S i = C i.1 :=
  rfl

/-- **Pirate strategy.** A pirate strategy of a coalition $S$ maps the codewords $C_S$ of its
members to a probability distribution on words of length $d$. It may be randomized and is
otherwise unrestricted: it need not output a feasible word. -/
abbrev Pirate (n d : ℕ) (S : Finset (Fin n)) : Type :=
  ({i : Fin n // i ∈ S} → Word d) → PMF (Word d)

/-- **Fingerprinting code.** A fingerprinting code for $n$ users of length $d$ with keys in `Key`
is a pair of randomized algorithms: a generator, which draws a codebook $C$ together with a key,
and a tracing algorithm, which maps a key and a word to an accused user $i \in [n]$ or to $\bot$,
no accusation. The key is the state that the generator shares with tracing; tracing receives no
other input from the generator, so a key may hold the codebook itself.

Source: M. Bun, J. Ullman and S. Vadhan, *Fingerprinting codes and the price of approximate
differential privacy*, SIAM J. Comput. 47(5), 2018, arXiv:1311.3158v3, Section 3.1.

Source: S. Vadhan, *The complexity of differential privacy*, in *Tutorials on the Foundations of
Cryptography*, Springer, 2017, Definition 5.16 in the author's version of 9 August 2016. -/
structure FingerprintingCode (n d : ℕ) (Key : Type*) where
  /-- The generator: a distribution on pairs of a codebook and the key it shares with `trace`. -/
  gen : PMF (Codebook n d × Key)
  /-- The tracing algorithm: given a key and a word, a distribution on accusations, `some i` for
  user `i` and `none` for no accusation ($\bot$). -/
  trace : Key → Word d → PMF (Option (Fin n))

/-! ### Feasibility and marking predicates -/

/-- **Feasible word.** A word $w$ is feasible for the coalition $S$ of the codebook $C$,
$w \in F(C_S)$, when each of its bits is the bit of some member of $S$ in the same column: for
every column $j$ there is $i \in S$ with $w_j = c_{ij}$. No word of positive length is feasible
for the empty coalition.

Source: M. Bun, J. Ullman and S. Vadhan, *Fingerprinting codes and the price of approximate
differential privacy*, SIAM J. Comput. 47(5), 2018, arXiv:1311.3158v3, Section 3.1. -/
def Feasible {n d : ℕ} (C : Codebook n d) (S : Finset (Fin n)) (w : Word d) : Prop :=
  ∀ j : Fin d, ∃ i ∈ S, w j = C i j

/-- **Marking condition.** A word $w$ satisfies the marking condition for the coalition $S$ of the
codebook $C$ when it agrees with the coalition on every column on which all members of $S$ agree:
whenever $c_{ij} = b$ for all $i \in S$, then $w_j = b$. For the empty coalition every column
forces both bits, so only the word of length $0$ satisfies it.

Source: G. Tardos, *Optimal probabilistic fingerprint codes*, J. ACM 55(2), 2008,
Definition 1.1. -/
def MarkingFeasible {n d : ℕ} (C : Codebook n d) (S : Finset (Fin n)) (w : Word d) : Prop :=
  ∀ (j : Fin d) (b : Bool), (∀ i ∈ S, C i j = b) → w j = b

/-- **Feasible words are those that satisfy the marking condition.** For every codebook $C$,
coalition $S$ and word $w$, the word $w$ is feasible for $S$, $w \in F(C_S)$, if and only if it
satisfies the marking condition for $S$. -/
theorem feasible_iff_markingFeasible {n d : ℕ}
    (C : Codebook n d) (S : Finset (Fin n)) (w : Word d) :
    Feasible C S w ↔ MarkingFeasible C S w := by
  constructor
  · intro h j b hb
    obtain ⟨i, hi, hw⟩ := h j
    exact hw.trans (hb i hi)
  · intro h j
    by_contra hno
    push Not at hno
    have hall : ∀ i ∈ S, C i j = !w j := by
      intro i hi
      have hne : w j ≠ C i j := hno i hi
      cases hw : w j <;> cases hc : C i j <;> simp_all
    have hcontra := h j (!w j) hall
    cases hw : w j <;> rw [hw] at hcontra <;> simp at hcontra

/-- **β-feasible word.** For a real number $\beta$, a word $w$ of length $d$ is $\beta$-feasible
for the coalition $S$ of the codebook $C$, $w \in F_\beta(C_S)$, when
$(1 - \beta)\, d \le \#\{j : \exists i \in S,\ w_j = c_{ij}\}$: at least a $1 - \beta$ fraction of
its columns are feasible. For $d > 0$ this is the condition
$\Pr_{j \leftarrow [d]}[\exists i \in S,\ w_j = c_{ij}] \ge 1 - \beta$ multiplied by $d$, which the
source states for $\beta \in [0, 1]$; every word is $\beta$-feasible when $d = 0$ or $\beta \ge 1$.

Source: M. Bun, J. Ullman and S. Vadhan, *Fingerprinting codes and the price of approximate
differential privacy*, SIAM J. Comput. 47(5), 2018, arXiv:1311.3158v3, Section 3.1. -/
def ErrorRobustFeasible {n d : ℕ} (β : ℝ) (C : Codebook n d) (S : Finset (Fin n))
    (w : Word d) : Prop :=
  (1 - β) * (d : ℝ) ≤
    ((Finset.univ.filter fun j : Fin d => ∃ i ∈ S, w j = C i j).card : ℝ)

/-- **Zero-error feasibility is feasibility.** A word is $0$-feasible for a coalition,
$w \in F_0(C_S)$, if and only if it is feasible, $w \in F(C_S)$.

Source: M. Bun, J. Ullman and S. Vadhan, *Fingerprinting codes and the price of approximate
differential privacy*, SIAM J. Comput. 47(5), 2018, arXiv:1311.3158v3, Section 3.1. -/
theorem errorRobustFeasible_zero_iff {n d : ℕ}
    (C : Codebook n d) (S : Finset (Fin n)) (w : Word d) :
    ErrorRobustFeasible 0 C S w ↔ Feasible C S w := by
  unfold ErrorRobustFeasible Feasible
  simp only [sub_zero, one_mul, Nat.cast_le]
  constructor
  · intro h j
    have heq : (Finset.univ.filter fun j : Fin d => ∃ i ∈ S, w j = C i j) = Finset.univ :=
      Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _)
        (by simpa [Fintype.card_fin] using h))
    have hj : j ∈ Finset.univ.filter (fun j : Fin d => ∃ i ∈ S, w j = C i j) := by
      rw [heq]; exact Finset.mem_univ j
    exact (Finset.mem_filter.mp hj).2
  · intro h
    have heq : (Finset.univ.filter fun j : Fin d => ∃ i ∈ S, w j = C i j) = Finset.univ :=
      Finset.filter_eq_self.mpr fun j _ => h j
    rw [heq, Finset.card_univ, Fintype.card_fin]

/-! ### Colluder accusation predicates -/

/-- **Accusation of a colluder.** The tracing output $a$ accuses a member of the coalition $S$:
$a$ is `some i` for some $i \in S$. -/
def AccusesGuilty {n : ℕ} (S : Finset (Fin n)) (a : Option (Fin n)) : Prop :=
  ∃ i ∈ S, a = some i

/-- **False accusation.** The tracing output $a$ accuses an innocent user: $a$ is `some i` for
some user $i \notin S$. -/
def FalseAccusation {n : ℕ} (S : Finset (Fin n)) (a : Option (Fin n)) : Prop :=
  ∃ i : Fin n, i ∉ S ∧ a = some i

/-- **No accusation.** The tracing output $a$ is `none`, written $\bot$: tracing accuses
nobody. -/
def NoAccusation {n : ℕ} (a : Option (Fin n)) : Prop :=
  a = none

/-- **Tracing failure.** The tracing output $a$ does not accuse a member of the coalition $S$: it
is $\bot$ or an innocent user. -/
def TracingFailure {n : ℕ} (S : Finset (Fin n)) (a : Option (Fin n)) : Prop :=
  ¬ AccusesGuilty S a

/-! ### Tracing game and security predicates -/

/-- **Tracing game.** The tracing game of a fingerprinting code against a pirate strategy $P$ of
the coalition $S$ draws a codebook $C$ and a key $k$ from the generator, a word $w$ from $P(C_S)$
and an accusation $a$ from tracing on $k$ and $w$, and returns $(C, w, a)$. Its probabilities are
over the coins of the generator, the pirate and tracing. -/
noncomputable def tracingGame {n d : ℕ} {Key : Type*}
    (FC : FingerprintingCode n d Key) (S : Finset (Fin n)) (P : Pirate n d S) :
    PMF (Codebook n d × Word d × Option (Fin n)) :=
  FC.gen.bind fun ck =>
    (P (submatrix ck.1 S)).bind fun w =>
      (FC.trace ck.2 w).map fun a => (ck.1, w, a)

theorem tracingGame_def {n d : ℕ} {Key : Type*}
    (FC : FingerprintingCode n d Key) (S : Finset (Fin n)) (P : Pirate n d S) :
    tracingGame FC S P =
      FC.gen.bind fun ck =>
        (P (submatrix ck.1 S)).bind fun w =>
          (FC.trace ck.2 w).map fun a => (ck.1, w, a) :=
  rfl

/-- **Completeness failure.** The outcomes $(C, w, a)$ of the tracing game in which the word is
feasible for the coalition $S$, $w \in F(C_S)$, and tracing accuses nobody, $a = \bot$. -/
def completenessFailureEvent {n d : ℕ} (S : Finset (Fin n)) :
    Set (Codebook n d × Word d × Option (Fin n)) :=
  {t | Feasible t.1 S t.2.1 ∧ NoAccusation t.2.2}

/-- **Error-robust completeness failure.** The outcomes $(C, w, a)$ of the tracing game in which
the word is $\beta$-feasible for the coalition $S$, $w \in F_\beta(C_S)$, and tracing accuses
nobody, $a = \bot$. -/
def errorRobustCompletenessFailureEvent {n d : ℕ} (β : ℝ) (S : Finset (Fin n)) :
    Set (Codebook n d × Word d × Option (Fin n)) :=
  {t | ErrorRobustFeasible β t.1 S t.2.1 ∧ NoAccusation t.2.2}

/-- **Soundness failure.** The outcomes $(C, w, a)$ of the tracing game in which tracing accuses
a user outside the coalition $S$, $a \in [n] \setminus S$. -/
def soundnessFailureEvent {n d : ℕ} (S : Finset (Fin n)) :
    Set (Codebook n d × Word d × Option (Fin n)) :=
  {t | FalseAccusation S t.2.2}

/-- **Combined tracing failure.** The outcomes $(C, w, a)$ of the tracing game in which the word
is feasible, $w \in F(C_S)$, and tracing does not accuse a member of the coalition $S$: $a$ is
$\bot$ or an innocent user. -/
def combinedFailureEvent {n d : ℕ} (S : Finset (Fin n)) :
    Set (Codebook n d × Word d × Option (Fin n)) :=
  {t | Feasible t.1 S t.2.1 ∧ TracingFailure S t.2.2}

/-- **Completeness error.** The probability of a completeness failure in the tracing game,
$\Pr[w \in F(C_S) \wedge a = \bot]$, as a real number. -/
noncomputable def completenessErrorProb {n d : ℕ} {Key : Type*}
    (FC : FingerprintingCode n d Key) (S : Finset (Fin n)) (P : Pirate n d S) : ℝ :=
  ((tracingGame FC S P).toOuterMeasure (completenessFailureEvent S)).toReal

/-- **Error-robust completeness error.** The probability of an error-robust completeness failure
in the tracing game, $\Pr[w \in F_\beta(C_S) \wedge a = \bot]$, as a real number. -/
noncomputable def errorRobustCompletenessErrorProb {n d : ℕ} {Key : Type*}
    (β : ℝ) (FC : FingerprintingCode n d Key) (S : Finset (Fin n)) (P : Pirate n d S) : ℝ :=
  ((tracingGame FC S P).toOuterMeasure (errorRobustCompletenessFailureEvent β S)).toReal

/-- **Soundness error.** The probability that the tracing game accuses an innocent user,
$\Pr[a \in [n] \setminus S]$, as a real number. -/
noncomputable def soundnessErrorProb {n d : ℕ} {Key : Type*}
    (FC : FingerprintingCode n d Key) (S : Finset (Fin n)) (P : Pirate n d S) : ℝ :=
  ((tracingGame FC S P).toOuterMeasure (soundnessFailureEvent S)).toReal

/-- **Combined tracing error.** The probability of a combined tracing failure in the tracing game,
$\Pr[w \in F(C_S) \wedge a \notin S]$, as a real number, where $a \notin S$ means that $a$ is
$\bot$ or an innocent user. -/
noncomputable def combinedErrorProb {n d : ℕ} {Key : Type*}
    (FC : FingerprintingCode n d Key) (S : Finset (Fin n)) (P : Pirate n d S) : ℝ :=
  ((tracingGame FC S P).toOuterMeasure (combinedFailureEvent S)).toReal

/-- **Fingerprinting security.** A fingerprinting code is secure against coalitions of size at most
$c$ with completeness error $\gamma$ and soundness error $\xi$, two nonnegative real numbers, when
for every nonempty coalition $S$ with $|S| \le c$ and every pirate strategy of $S$ the tracing game
satisfies $\Pr[w \in F(C_S) \wedge a = \bot] \le \gamma$ and $\Pr[a \in [n] \setminus S] \le \xi$.

This is Definition 3.1 of Bun, Ullman and Vadhan with separate errors, as in their
Definition 3.12, for nonempty coalitions of size at most $c$, as in Tardos's Definition 1.1. Their
Definition 3.1 asks for every coalition $S \subseteq [n]$, the empty one included, with
$\gamma = \xi \in (0, 1]$; it implies this predicate for $c = n$ and $\gamma = \xi$, but not
conversely. For one user, the code that always accuses that user meets this predicate with errors
$0$, while against the empty coalition, which sees no codeword, it accuses an innocent user with
probability $1$, so it has security $\xi$ in their sense only for $\xi = 1$. Their
Definition 3.12, for general query families, asks for coalitions with $|S| \ge n - 1$.

Source: M. Bun, J. Ullman and S. Vadhan, *Fingerprinting codes and the price of approximate
differential privacy*, SIAM J. Comput. 47(5), 2018, arXiv:1311.3158v3, Definitions 3.1
and 3.12.

Source: G. Tardos, *Optimal probabilistic fingerprint codes*, J. ACM 55(2), 2008,
Definition 1.1. -/
def IsFingerprintingSecure {n d : ℕ} {Key : Type*}
    (FC : FingerprintingCode n d Key) (c : ℕ) (γ ξ : ℝ) : Prop :=
  0 ≤ γ ∧ 0 ≤ ξ ∧
    ∀ (S : Finset (Fin n)), S.Nonempty → S.card ≤ c → ∀ (P : Pirate n d S),
      completenessErrorProb FC S P ≤ γ ∧ soundnessErrorProb FC S P ≤ ξ

/-- **Error-robust fingerprinting security.** A fingerprinting code is secure against coalitions of
size at most $c$, robustly to a $\beta$ fraction of errors, with completeness error $\gamma$ and
soundness error $\xi$, three nonnegative real numbers, when for every nonempty coalition $S$ with
$|S| \le c$ and every pirate strategy of $S$ the tracing game satisfies
$\Pr[w \in F_\beta(C_S) \wedge a = \bot] \le \gamma$ and $\Pr[a \in [n] \setminus S] \le \xi$.

This is Definition 3.3 of Bun, Ullman and Vadhan with separate errors, for nonempty coalitions of
size at most $c$. Their definition asks for every coalition $S \subseteq [n]$, the empty one
included, with $\gamma = \xi \in [0, 1]$ and $\beta \in [0, 1]$.

Source: M. Bun, J. Ullman and S. Vadhan, *Fingerprinting codes and the price of approximate
differential privacy*, SIAM J. Comput. 47(5), 2018, arXiv:1311.3158v3, Definition 3.3. -/
def IsErrorRobustFingerprintingSecure {n d : ℕ} {Key : Type*}
    (FC : FingerprintingCode n d Key) (c : ℕ) (β γ ξ : ℝ) : Prop :=
  0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ ξ ∧
    ∀ (S : Finset (Fin n)), S.Nonempty → S.card ≤ c → ∀ (P : Pirate n d S),
      errorRobustCompletenessErrorProb β FC S P ≤ γ ∧ soundnessErrorProb FC S P ≤ ξ

/-- **Combined fingerprinting security.** A fingerprinting code is secure against coalitions of
size at most $c$ with combined error $\varepsilon$, a nonnegative real number, when for every
nonempty coalition $S$ with $|S| \le c$ and every pirate strategy of $S$ the tracing game satisfies
$\Pr[w \in F(C_S) \wedge a \notin S] \le \varepsilon$, where $a \notin S$ means that $a$ is $\bot$
or an innocent user.

Vadhan's Definition 5.17 bounds the same event for every coalition by a negligible function of
$n$; here the bound is a fixed $\varepsilon$ and coalitions are nonempty of size at most $c$.
Tardos's Definition 1.1 bounds the probability that tracing accuses nobody or an innocent user,
for pirate strategies whose words satisfy the marking condition.

Source: S. Vadhan, *The complexity of differential privacy*, in *Tutorials on the Foundations of
Cryptography*, Springer, 2017, Definition 5.17 in the author's version of 9 August 2016.

Source: G. Tardos, *Optimal probabilistic fingerprint codes*, J. ACM 55(2), 2008,
Definition 1.1. -/
def IsFingerprintingSecureCombined {n d : ℕ} {Key : Type*}
    (FC : FingerprintingCode n d Key) (c : ℕ) (ε : ℝ) : Prop :=
  0 ≤ ε ∧
    ∀ (S : Finset (Fin n)), S.Nonempty → S.card ≤ c → ∀ (P : Pirate n d S),
      combinedErrorProb FC S P ≤ ε

/-! ### Codebook generation from a bias distribution -/

/-- **Bernoulli mass.** The mass function of the Bernoulli distribution with bias $p \in [0, 1]$
on `Bool`: $p$ at `true` and $1 - p$ at `false`. -/
noncomputable def bernoulliMass (p : unitInterval) (b : Bool) : ℝ≥0∞ :=
  if b then ENNReal.ofReal p else ENNReal.ofReal (unitInterval.symm p)

/-- **Bernoulli distribution.** The Bernoulli distribution with bias $p \in [0, 1]$ as a
probability mass function on `Bool`: `true` with probability $p$ and `false` with probability
$1 - p$. Its measure is Mathlib's `ProbabilityTheory.bernoulliMeasure true false p`. -/
noncomputable def bernoulliPMF (p : unitInterval) : PMF Bool :=
  PMF.ofFintype (bernoulliMass p) (by
    rw [Fintype.sum_bool]
    simp only [bernoulliMass, Bool.false_eq_true, ite_true, ite_false]
    rw [← ENNReal.ofReal_add p.2.1 (unitInterval.symm p).2.1, unitInterval.coe_symm_eq,
      add_sub_cancel, ENNReal.ofReal_one])

theorem bernoulliPMF_apply (p : unitInterval) (b : Bool) :
    bernoulliPMF p b = bernoulliMass p b :=
  rfl

@[simp]
theorem bernoulliPMF_true (p : unitInterval) :
    bernoulliPMF p true = ENNReal.ofReal p :=
  rfl

@[simp]
theorem bernoulliPMF_false (p : unitInterval) :
    bernoulliPMF p false = ENNReal.ofReal (1 - p) :=
  rfl

/-- **Codebook mass for a bias vector.** For a bias vector $p \in [0, 1]^d$, the mass of the
codebook $C$: the product over users $i$ and columns $j$ of $p_j$ when $c_{ij} = 1$ and of
$1 - p_j$ when $c_{ij} = 0$. -/
noncomputable def biasCodebookMass {n d : ℕ} (p : Fin d → unitInterval) (C : Codebook n d) :
    ℝ≥0∞ :=
  ∏ i : Fin n, ∏ j : Fin d, bernoulliMass (p j) (C i j)

/-- **Codebook with independent biased entries.** For a bias vector $p \in [0, 1]^d$, the
distribution on codebooks whose entries are independent with $\Pr[c_{ij} = 1] = p_j$: the second
phase of Tardos's construction, given the biases.

Source: G. Tardos, *Optimal probabilistic fingerprint codes*, J. ACM 55(2), 2008, Section 2.1. -/
noncomputable def biasCodebookPMF {n d : ℕ} (p : Fin d → unitInterval) : PMF (Codebook n d) :=
  PMF.ofFintype (biasCodebookMass p) (by
    simp only [biasCodebookMass]
    rw [← Fintype.prod_sum (fun (_ : Fin n) (row : Word d) =>
      ∏ j : Fin d, bernoulliMass (p j) (row j))]
    apply Finset.prod_eq_one
    intro _ _
    rw [← Fintype.prod_sum (fun (j : Fin d) (b : Bool) => bernoulliMass (p j) b)]
    apply Finset.prod_eq_one
    intro j _
    rw [Fintype.sum_bool]
    simp only [bernoulliMass, Bool.false_eq_true, ite_true, ite_false]
    rw [← ENNReal.ofReal_add (p j).2.1 (unitInterval.symm (p j)).2.1,
      unitInterval.coe_symm_eq, add_sub_cancel, ENNReal.ofReal_one])

@[simp]
theorem biasCodebookPMF_apply {n d : ℕ} (p : Fin d → unitInterval) (C : Codebook n d) :
    biasCodebookPMF p C = ∏ i : Fin n, ∏ j : Fin d, bernoulliMass (p j) (C i j) :=
  rfl

/-- **Independent draws.** The distribution of $d$ independent draws from $\mu$, as a function
`Fin d → α`: one draw from $\mu$ followed by $d - 1$ further independent draws. -/
noncomputable def pmfIID {α : Type*} (μ : PMF α) : (d : ℕ) → PMF (Fin d → α)
  | 0 => PMF.pure Fin.elim0
  | d + 1 => μ.bind fun x => (pmfIID μ d).map fun f => Fin.cons x f

@[simp]
theorem pmfIID_zero {α : Type*} (μ : PMF α) :
    pmfIID μ 0 = PMF.pure Fin.elim0 :=
  rfl

@[simp]
theorem pmfIID_succ {α : Type*} (μ : PMF α) (d : ℕ) :
    pmfIID μ (d + 1) = μ.bind fun x => (pmfIID μ d).map fun f => Fin.cons x f :=
  rfl

/-- **Generation from a bias-vector distribution.** The generator that draws a bias vector $p$
from `biasDist`, then a codebook whose entries are independent with $\Pr[c_{ij} = 1] = p_j$, and
returns the codebook with $p$ as the key. -/
noncomputable def genFromBiasVectorDist {n d : ℕ} (biasDist : PMF (Fin d → unitInterval)) :
    PMF (Codebook n d × (Fin d → unitInterval)) :=
  biasDist.bind fun p => (biasCodebookPMF (n := n) p).map fun C => (C, p)

theorem genFromBiasVectorDist_def {n d : ℕ} (biasDist : PMF (Fin d → unitInterval)) :
    genFromBiasVectorDist (n := n) biasDist =
      biasDist.bind fun p => (biasCodebookPMF (n := n) p).map fun C => (C, p) :=
  rfl

/-- **Generation from independent biases.** The generator that draws the $d$ column biases
independently from $\mu$, then a codebook with these biases, and returns the codebook with the
bias vector as the key: Tardos's construction for a discrete bias distribution $\mu$ on $[0, 1]$.
Tardos draws each bias as $\sin^2 r$ for $r$ uniform on an interval, a continuous distribution,
which a probability mass function cannot express.

Source: G. Tardos, *Optimal probabilistic fingerprint codes*, J. ACM 55(2), 2008, Section 2.1. -/
noncomputable def genFromIIDBiasDist {n d : ℕ} (μ : PMF unitInterval) :
    PMF (Codebook n d × (Fin d → unitInterval)) :=
  genFromBiasVectorDist (pmfIID μ d)

theorem genFromIIDBiasDist_def {n d : ℕ} (μ : PMF unitInterval) :
    genFromIIDBiasDist (n := n) (d := d) μ = genFromBiasVectorDist (pmfIID μ d) :=
  rfl

/-! ### Tardos linear accusation score and predicate -/

/-- **Tardos weight.** Tardos's weight for the bias $p$ and the bit $b$: $\sqrt{(1 - p)/p}$ for
$b = 1$ and $-\sqrt{p/(1 - p)}$ for $b = 0$. For $p \notin (0, 1)$ both weights are $0$, by the
conventions $x / 0 = 0$ and $\sqrt{x} = 0$ for $x < 0$; Tardos's biases lie in $(0, 1)$.

Source: G. Tardos, *Optimal probabilistic fingerprint codes*, J. ACM 55(2), 2008, Section 2.1. -/
noncomputable def tardosWeight (p : ℝ) (b : Bool) : ℝ :=
  if b then Real.sqrt ((1 - p) / p) else -Real.sqrt (p / (1 - p))

@[simp]
theorem tardosWeight_true (p : ℝ) :
    tardosWeight p true = Real.sqrt ((1 - p) / p) :=
  rfl

@[simp]
theorem tardosWeight_false (p : ℝ) :
    tardosWeight p false = -Real.sqrt (p / (1 - p)) :=
  rfl

/-- **Tardos score.** The accusation score of user $i$ on the word $w$ for the bias vector $p$:
$\sum_{j \,:\, w_j = 1} U_{ij}$, where $U_{ij}$ is the Tardos weight of the bias $p_j$ and the
bit $c_{ij}$.

Source: G. Tardos, *Optimal probabilistic fingerprint codes*, J. ACM 55(2), 2008, Section 2.1. -/
noncomputable def tardosScore {n d : ℕ} (p : Fin d → ℝ) (C : Codebook n d)
    (w : Word d) (i : Fin n) : ℝ :=
  ∑ j : Fin d, if w j then tardosWeight (p j) (C i j) else 0

theorem tardosScore_def {n d : ℕ} (p : Fin d → ℝ) (C : Codebook n d)
    (w : Word d) (i : Fin n) :
    tardosScore p C w i = ∑ j : Fin d, if w j then tardosWeight (p j) (C i j) else 0 :=
  rfl

/-- **Tardos accusation.** Tardos's rule accuses user $i$ on the word $w$ when its score for the
bias vector $p$ exceeds the threshold $Z$ strictly. Tardos takes $Z = 20 c k$ for coalitions of
size at most $c$ and error $\varepsilon$, with $k = \lceil \log(1/\varepsilon) \rceil$.

Source: G. Tardos, *Optimal probabilistic fingerprint codes*, J. ACM 55(2), 2008, Section 2.1. -/
def TardosAccuses {n d : ℕ} (p : Fin d → ℝ) (Z : ℝ) (C : Codebook n d)
    (w : Word d) (i : Fin n) : Prop :=
  Z < tardosScore p C w i

theorem tardosAccuses_iff {n d : ℕ} (p : Fin d → ℝ) (Z : ℝ) (C : Codebook n d)
    (w : Word d) (i : Fin n) :
    TardosAccuses p Z C w i ↔ Z < tardosScore p C w i :=
  Iff.rfl

end CSLibExt.Privacy.Fingerprinting
