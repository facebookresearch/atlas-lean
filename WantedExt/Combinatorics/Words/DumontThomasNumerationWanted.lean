/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import MathlibExt.Combinatorics.InfiniteWord.PureMorphicWord

namespace MetaMathlibExt

@[expose] public section

/-- A substitution in the sense of Labbé and Lepšová: a letter map `η : A → A*` (extended to
words by `morphExtend`) whose letter images are all nonempty and which has a growing letter
`a`, i.e. `|ηᵏ(a)| → ∞`. Finiteness of the alphabet is not assumed.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Section 2 (Preliminaries). -/
public def IsSubstitution {A : Type*} (η : A → List A) : Prop :=
  IsNonErasing η ∧
    ∃ a, Filter.Tendsto (fun k => (morphIterate η k [a]).length) Filter.atTop Filter.atTop

/-- A substitution is non-erasing.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Section 2. -/
public theorem IsSubstitution.isNonErasing {A : Type*} {η : A → List A}
    (h : IsSubstitution η) : IsNonErasing η := h.1

/-- A finite sequence `(mᵢ, aᵢ)_{i = 0, …, k}` in `A* × A`, encoded as `s : ℕ → List A × A`
read only at indices `0, …, k`, is admissible with respect to `η` when `m_{i-1} a_{i-1}` is a
prefix of `η(aᵢ)` for `1 ≤ i ≤ k` (here reindexed as `i < k`).

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Definition 3.1 (after Dumont and Thomas). -/
public def IsAdmissibleSequence {A : Type*} (η : A → List A) (s : ℕ → List A × A) (k : ℕ) :
    Prop :=
  ∀ i < k, (s i).1 ++ [(s i).2] <+: η (s (i + 1)).2

/-- An admissible sequence `(mᵢ, aᵢ)_{i = 0, …, k}` is `a`-admissible when moreover
`m_k a_k` is a prefix of `η(a)`.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Definition 3.1. -/
public def IsLetterAdmissibleSequence {A : Type*} (η : A → List A) (a : A)
    (s : ℕ → List A × A) (k : ℕ) : Prop :=
  IsAdmissibleSequence η s k ∧ (s k).1 ++ [(s k).2] <+: η a

/-- Every one-term sequence is admissible (the condition is vacuous for `k = 0`).

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Definition 3.1. -/
public theorem isAdmissibleSequence_zero {A : Type*} (η : A → List A) (s : ℕ → List A × A) :
    IsAdmissibleSequence η s 0 := fun _ hi => absurd hi (Nat.not_lt_zero _)

/-- The deterministic finite automaton with output `𝒜_{η,·}` associated with `η`: states are
letters, digit `i` moves from `b` to the `i`-th letter of `η(b)` (undefined when
`i ≥ |η(b)|`), and `substitutionAutomaton η b w` is the state reached from `b` after reading
the digit word `w`, or `none` when the run is undefined. Every state is final, so a digit word
is accepted from `x` exactly when the result is `some _`. Digits are natural numbers; digits
outside the paper's alphabet `{0, …, max_c |η(c)| - 1}` are never readable, so the accepted
language is unchanged.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Section 2 (the DFAO `𝒜_{η,a}`). -/
public def substitutionAutomaton {A : Type*} (η : A → List A) : A → List ℕ → Option A
  | b, [] => some b
  | b, i :: w => (η b)[i]?.bind fun c => substitutionAutomaton η c w

/-- Reading the empty digit word stays at the starting state.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Section 2. -/
public theorem substitutionAutomaton_nil {A : Type*} (η : A → List A) (b : A) :
    substitutionAutomaton η b [] = some b := rfl

/-- Reading `i ⊙ w` first moves to `η(b)[i]`, then reads `w`.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Section 2. -/
public theorem substitutionAutomaton_cons {A : Type*} (η : A → List A) (b : A) (i : ℕ)
    (w : List ℕ) :
    substitutionAutomaton η b (i :: w) =
      (η b)[i]?.bind fun c => substitutionAutomaton η c w := rfl

/-- For the Fibonacci substitution `0 ↦ 01`, `1 ↦ 0`, the digit word `10` leads from `0` to
`0`, while `11` is rejected.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Section 2 and Proposition 9.2 (Fibonacci substitution). -/
public theorem substitutionAutomaton_fibonacci_small :
    substitutionAutomaton (fun a : Fin 2 => if a = 0 then [0, 1] else [0]) 0 [1, 0] = some 0 ∧
      substitutionAutomaton (fun a : Fin 2 => if a = 0 then [0, 1] else [0]) 0 [1, 1] =
        none := by
  decide

/-- Dumont–Thomas numeration for `ℕ`: let `u = η(u)` be a right-infinite fixed point of a
substitution `η` with growing seed `u₀ = a`. For every `n ≥ 1` there is a unique `k` and a
unique sequence `(mᵢ, aᵢ)_{i = 0, …, k}` that is `a`-admissible with `m_k ≠ ε` and
`u₀ ⋯ u_{n-1} = η^k(m_k) ⋯ η⁰(m₀)`. The fixed-point equation is stated prefixwise:
`η(u₀ ⋯ u_{n-1})` is a prefix of `u` for every `n`. Uniqueness of the sequence is equality at
the indices `0, …, k`.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Theorem 3.2 (Dumont and Thomas, Theorem 1.5). -/
public theorem_wanted dumontThomas_numeration {A : Type*} (η : A → List A)
    (hη : IsSubstitution η) (a : A) (u : ℕ → A)
    (hfix : ∀ n i (hi : i < (morphExtend η ((List.range n).map u)).length),
      (morphExtend η ((List.range n).map u))[i] = u i)
    (hu₀ : u 0 = a)
    (hgrow : Filter.Tendsto (fun k => (morphIterate η k [a]).length) Filter.atTop
      Filter.atTop)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ k s, (IsLetterAdmissibleSequence η a s k ∧ (s k).1 ≠ [] ∧
        (List.range n).map u =
          ((List.range (k + 1)).reverse.map fun j => morphIterate η j (s j).1).flatten) ∧
      ∀ k' s', (IsLetterAdmissibleSequence η a s' k' ∧ (s' k').1 ≠ [] ∧
        (List.range n).map u =
          ((List.range (k' + 1)).reverse.map fun j => morphIterate η j (s' j).1).flatten) →
        k' = k ∧ ∀ i ≤ k, s' i = s i

/-- For an admissible sequence `(mᵢ, aᵢ)_{i = 0, …, k}`,
`∑_{j=0}^{k} |η^j(m_j)| < |η^k(m_k a_k)|`.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Lemma 3.3 (Dumont and Thomas, Lemma 1.1). -/
public theorem_wanted admissibleSequence_weightedLength_lt {A : Type*} (η : A → List A)
    (hη : IsSubstitution η) (s : ℕ → List A × A) (k : ℕ) (hs : IsAdmissibleSequence η s k) :
    ∑ j ∈ Finset.range (k + 1), (morphIterate η j (s j).1).length <
      (morphIterate η k ((s k).1 ++ [(s k).2])).length

/-- Two `b`-admissible sequences of the same length `k + 1` with the same value
`n = ∑_{j=0}^{k} |η^j(m_j)|` coincide termwise.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Lemma 3.4 (Dumont and Thomas, Lemma 1.3). -/
public theorem_wanted letterAdmissibleSequence_eq_of_weightedLength_eq {A : Type*}
    (η : A → List A) (hη : IsSubstitution η) (k : ℕ) (b : A) (s s' : ℕ → List A × A)
    (hs : IsLetterAdmissibleSequence η b s k) (hs' : IsLetterAdmissibleSequence η b s' k)
    (hsum : ∑ j ∈ Finset.range (k + 1), (morphIterate η j (s j).1).length =
      ∑ j ∈ Finset.range (k + 1), (morphIterate η j (s' j).1).length) :
    ∀ i ≤ k, s i = s' i

/-- If `ℓ ≥ 1` and `m` is a proper prefix of `η^ℓ(a)`, then there are `(m', a') ∈ A* × A`
and `m'' ∈ A*` with `m'a'` a prefix of `η(a)`, `m''` a proper prefix of `η^{ℓ-1}(a')`, and
`m = η^{ℓ-1}(m') m''`.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Lemma 3.5 (Dumont and Thomas, Lemma 1.4). -/
public theorem_wanted properPrefix_morphIterate_decomposition {A : Type*} (η : A → List A)
    (hη : IsSubstitution η) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (a : A) (m : List A)
    (hm : m <+: morphIterate η ℓ [a]) (hlt : m.length < (morphIterate η ℓ [a]).length) :
    ∃ (m' : List A) (a' : A) (m'' : List A), m' ++ [a'] <+: η a ∧
      m'' <+: morphIterate η (ℓ - 1) [a'] ∧
      m''.length < (morphIterate η (ℓ - 1) [a']).length ∧
      m = morphIterate η (ℓ - 1) m' ++ m''

/-- If `(mᵢ, aᵢ)_{i = 0, …, k-1}` is `x`-admissible (`k ≥ 1`), then for every `i < k` the
automaton `𝒜_{η,x}` reading `|m_{k-1}| ⊙ ⋯ ⊙ |mᵢ|` from `x` outputs `aᵢ`.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Lemma 3.6. -/
public theorem_wanted substitutionAutomaton_admissibleSequence {A : Type*} (η : A → List A)
    (hη : IsSubstitution η) (k : ℕ) (hk : 1 ≤ k) (x : A) (s : ℕ → List A × A)
    (hs : IsLetterAdmissibleSequence η x s (k - 1)) :
    ∀ i < k,
      substitutionAutomaton η x ((List.range (k - i)).map fun t => (s (k - 1 - t)).1.length) =
        some (s i).2

/-- If the digit word `v_{k-1} v_{k-2} ⋯ v₀` (`k ≥ 1`) is accepted by `𝒜_{η,x}`, then there
is an `x`-admissible sequence `(mᵢ, aᵢ)_{i = 0, …, k-1}` with `|mᵢ| = vᵢ` for all `i < k`.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Lemma 3.8. -/
public theorem_wanted exists_letterAdmissibleSequence_of_accepted {A : Type*}
    (η : A → List A) (hη : IsSubstitution η) (k : ℕ) (hk : 1 ≤ k) (x : A) (v : ℕ → ℕ)
    (hv : (substitutionAutomaton η x ((List.range k).map fun t => v (k - 1 - t))).isSome) :
    ∃ s, IsLetterAdmissibleSequence η x s (k - 1) ∧ ∀ i < k, (s i).1.length = v i

/-- If `p ≥ 1` and `m` is a proper prefix of `η^p(x)`, then there is a unique `x`-admissible
sequence `(mᵢ, aᵢ)_{i = 0, …, p-1}` with `|m| = ∑_{j=0}^{p-1} |η^j(m_j)|` (uniqueness at the
indices `0, …, p-1`); moreover `m = η^{p-1}(m_{p-1}) ⋯ η⁰(m₀)`.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Lemma 3.9. -/
public theorem_wanted existsUnique_letterAdmissibleSequence_of_properPrefix {A : Type*}
    (η : A → List A) (hη : IsSubstitution η) (p : ℕ) (hp : 1 ≤ p) (m : List A) (x : A)
    (hm : m <+: morphIterate η p [x]) (hlt : m.length < (morphIterate η p [x]).length) :
    ∃ s, (IsLetterAdmissibleSequence η x s (p - 1) ∧
        m.length = ∑ j ∈ Finset.range p, (morphIterate η j (s j).1).length) ∧
      (∀ s', IsLetterAdmissibleSequence η x s' (p - 1) →
        m.length = ∑ j ∈ Finset.range p, (morphIterate η j (s' j).1).length →
        ∀ i < p, s' i = s i) ∧
      m = ((List.range p).reverse.map fun j => morphIterate η j (s j).1).flatten

/-- For `p ≥ 1`, the letter of `η^p(x)` at position `ℓ` is the output of `𝒜_{η,x}` on
`tail_{η,p,x}(ℓ)`. The map `tail_{η,p,x}` sends `ℓ` to `|m_{p-1}| ⊙ ⋯ ⊙ |m₀|` for the unique
`x`-admissible sequence of Lemma 3.9 with `ℓ = ∑_{j<p} |η^j(m_j)|`; it is unfolded here by
quantifying over the `x`-admissible sequence itself (by Lemmas 3.3 and 3.9 these sequences
correspond bijectively to the positions `ℓ < |η^p(x)|`, so no range hypothesis is needed).

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Lemma 3.11. -/
public theorem_wanted morphIterate_getElem_eq_substitutionAutomaton_tail {A : Type*}
    (η : A → List A) (hη : IsSubstitution η) (p : ℕ) (hp : 1 ≤ p) (x : A)
    (s : ℕ → List A × A) (hs : IsLetterAdmissibleSequence η x s (p - 1)) :
    (morphIterate η p [x])[∑ j ∈ Finset.range p, (morphIterate η j (s j).1).length]? =
      substitutionAutomaton η x ((List.range p).reverse.map fun j => (s j).1.length)

/-- For `p ≥ 1` and positions `n, n' < |η^p(x)|`: `n = n'` iff
`tail_{η,p,x}(n) = tail_{η,p,x}(n')`, and `n < n'` iff `tail_{η,p,x}(n)` is
lexicographically smaller than `tail_{η,p,x}(n')`. As in Lemma 3.11, positions are given by
their `x`-admissible sequences `s, s'`, with `n = ∑_{j<p} |η^j(m_j)|` and
`tail = |m_{p-1}| ⊙ ⋯ ⊙ |m₀|`; the order on digit words is `List.lt` on `ℕ`.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Lemma 3.12. -/
public theorem_wanted tail_injective_and_strictMono {A : Type*} (η : A → List A)
    (hη : IsSubstitution η) (p : ℕ) (hp : 1 ≤ p) (x : A) (s s' : ℕ → List A × A)
    (hs : IsLetterAdmissibleSequence η x s (p - 1))
    (hs' : IsLetterAdmissibleSequence η x s' (p - 1)) :
    ((∑ j ∈ Finset.range p, (morphIterate η j (s j).1).length =
        ∑ j ∈ Finset.range p, (morphIterate η j (s' j).1).length) ↔
      (List.range p).reverse.map (fun j => (s j).1.length) =
        (List.range p).reverse.map (fun j => (s' j).1.length)) ∧
    ((∑ j ∈ Finset.range p, (morphIterate η j (s j).1).length <
        ∑ j ∈ Finset.range p, (morphIterate η j (s' j).1).length) ↔
      (List.range p).reverse.map (fun j => (s j).1.length) <
        (List.range p).reverse.map (fun j => (s' j).1.length))

/-- Dumont–Thomas numeration for right-infinite periodic points: let `η` be a substitution
with growing letter `a`, `u ∈ Per_{ℤ≥0}(η)` with `u₀ = a`, and `p ≥ 1` a period of `u`. For
every `n ≥ 1` there is a unique `k` with `p ∣ k` and a unique sequence
`(mᵢ, aᵢ)_{i = 0, …, k-1}` that is `a`-admissible with `m_{k-1} ⋯ m_{k-p} ≠ ε` and
`u₀ ⋯ u_{n-1} = η^{k-1}(m_{k-1}) ⋯ η⁰(m₀)`. The periodicity `η^p(u) = u` is stated prefixwise;
sequence uniqueness is equality at the indices `0, …, k-1`.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Theorem 4.1. -/
public theorem_wanted dumontThomas_numeration_rightPeriodic {A : Type*} (η : A → List A)
    (hη : IsSubstitution η) (a : A)
    (hgrow : Filter.Tendsto (fun k => (morphIterate η k [a]).length) Filter.atTop
      Filter.atTop)
    (u : ℕ → A) (hu₀ : u 0 = a) (p : ℕ) (hp : 1 ≤ p)
    (hper : ∀ n i (hi : i < (morphIterate η p ((List.range n).map u)).length),
      (morphIterate η p ((List.range n).map u))[i] = u i)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ k s, (p ∣ k ∧ IsLetterAdmissibleSequence η a s (k - 1) ∧
        ((List.range p).map fun t => (s (k - 1 - t)).1).flatten ≠ [] ∧
        (List.range n).map u =
          ((List.range k).reverse.map fun j => morphIterate η j (s j).1).flatten) ∧
      ∀ k' s', (p ∣ k' ∧ IsLetterAdmissibleSequence η a s' (k' - 1) ∧
        ((List.range p).map fun t => (s' (k' - 1 - t)).1).flatten ≠ [] ∧
        (List.range n).map u =
          ((List.range k').reverse.map fun j => morphIterate η j (s' j).1).flatten) →
        k' = k ∧ ∀ i < k, s' i = s i

/-- Dumont–Thomas numeration for left-infinite periodic points: let `η` be a substitution with
growing letter `b`, `u ∈ Per_{ℤ<0}(η)` with `u₋₁ = b`, and `p ≥ 1` a period of `u`. For every
`n ≤ -2` there is a unique `k` with `p ∣ k` and a unique sequence `(mᵢ, aᵢ)_{i = 0, …, k-1}`
that is `b`-admissible with
`η^{p-1}(m_{k-1}) ⋯ η⁰(m_{k-p}) a_{k-p} ≠ η^p(b)` and
`u_{-|η^k(b)|} ⋯ u_{n-1} = η^{k-1}(m_{k-1}) ⋯ η⁰(m₀)`.
Encoding: the left-infinite word is `v : ℕ → A` with `v j = u_{-1-j}`, periodicity says that
`η^p(u_{-m} ⋯ u_{-1})` is a suffix of `u` for every `m`, and `n = -N` with `N ≥ 2`. The
condition `N ≤ |η^k(b)|` makes explicit that the word `u_{-|η^k(b)|} ⋯ u_{n-1}` is defined
(it excludes the vacuous `k = 0` reading under truncated subtraction).

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Theorem 4.2. -/
public theorem_wanted dumontThomas_numeration_leftPeriodic {A : Type*} (η : A → List A)
    (hη : IsSubstitution η) (b : A)
    (hgrow : Filter.Tendsto (fun k => (morphIterate η k [b]).length) Filter.atTop
      Filter.atTop)
    (v : ℕ → A) (hv₀ : v 0 = b) (p : ℕ) (hp : 1 ≤ p)
    (hper : ∀ m i (hi : i < (morphIterate η p ((List.range m).reverse.map v)).length),
      (morphIterate η p ((List.range m).reverse.map v))[
        (morphIterate η p ((List.range m).reverse.map v)).length - 1 - i]'(by omega) = v i)
    (N : ℕ) (hN : 2 ≤ N) :
    ∃ k s, (p ∣ k ∧ N ≤ (morphIterate η k [b]).length ∧
        IsLetterAdmissibleSequence η b s (k - 1) ∧
        ((List.range p).map fun t => morphIterate η (p - 1 - t) (s (k - 1 - t)).1).flatten ++
          [(s (k - p)).2] ≠ morphIterate η p [b] ∧
        (List.range ((morphIterate η k [b]).length - N)).map
            (fun t => v ((morphIterate η k [b]).length - 1 - t)) =
          ((List.range k).reverse.map fun j => morphIterate η j (s j).1).flatten) ∧
      ∀ k' s', (p ∣ k' ∧ N ≤ (morphIterate η k' [b]).length ∧
        IsLetterAdmissibleSequence η b s' (k' - 1) ∧
        ((List.range p).map fun t => morphIterate η (p - 1 - t) (s' (k' - 1 - t)).1).flatten ++
          [(s' (k' - p)).2] ≠ morphIterate η p [b] ∧
        (List.range ((morphIterate η k' [b]).length - N)).map
            (fun t => v ((morphIterate η k' [b]).length - 1 - t)) =
          ((List.range k').reverse.map fun j => morphIterate η j (s' j).1).flatten) →
        k' = k ∧ ∀ i < k, s' i = s i

/-- A two-sided word `u : ℤ → A` is a periodic point of `η` with period `p ≥ 1` when
`η^p(u) = u`, where `η` acts on `⋯ u₋₂ u₋₁ | u₀ u₁ ⋯` letterwise and keeps the origin
between `η(u₋₁)` and `η(u₀)`. Equivalently (and this is how it is stated here) the right half
satisfies `η^p(u₀ ⋯ u_{n-1})` is a prefix of `u₀ u₁ ⋯` for every `n`, and the left half
satisfies `η^p(u_{-m} ⋯ u₋₁)` is a suffix of `⋯ u₋₂ u₋₁` for every `m`, with the same
encodings as in Theorems 4.1 and 4.2.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Section 2 (periodic points `Per(η)`). -/
public def IsTwoSidedPeriodicPoint {A : Type*} (η : A → List A) (u : ℤ → A) (p : ℕ) : Prop :=
  1 ≤ p ∧
    (∀ n i (hi : i < (morphIterate η p ((List.range n).map fun j : ℕ => u j)).length),
      (morphIterate η p ((List.range n).map fun j : ℕ => u j))[i] = u i) ∧
    ∀ m i (hi : i < (morphIterate η p
        ((List.range m).reverse.map fun j : ℕ => u (-1 - (j : ℤ)))).length),
      (morphIterate η p ((List.range m).reverse.map fun j : ℕ => u (-1 - (j : ℤ))))[
        (morphIterate η p ((List.range m).reverse.map fun j : ℕ => u (-1 - (j : ℤ)))).length -
          1 - i]'(by omega) = u (-1 - (i : ℤ))

/-- A period of a two-sided periodic point is positive.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Section 2. -/
public theorem IsTwoSidedPeriodicPoint.one_le {A : Type*} {η : A → List A} {u : ℤ → A} {p : ℕ}
    (h : IsTwoSidedPeriodicPoint η u p) : 1 ≤ p := h.1

/-- The standing hypothesis of Sections 4–9: `η` is a substitution, `u ∈ Per(η)` is a
two-sided periodic point whose seed letters `u₋₁` and `u₀` are both growing, and `p` is *the*
period of `u` (the least `p ≥ 1` with `η^p(u) = u`).

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Sections 2 and 4 (two-sided periodic point with growing
seed `s = u₋₁|u₀`, and its period). -/
public def IsPeriodicPointWithGrowingSeed {A : Type*} (η : A → List A) (u : ℤ → A) (p : ℕ) :
    Prop :=
  IsSubstitution η ∧ IsLeast {q | IsTwoSidedPeriodicPoint η u q} p ∧
    Filter.Tendsto (fun k => (morphIterate η k [u 0]).length) Filter.atTop Filter.atTop ∧
    Filter.Tendsto (fun k => (morphIterate η k [u (-1)]).length) Filter.atTop Filter.atTop

/-- Under the standing hypothesis, `u` is a two-sided periodic point with period `p`.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Section 4. -/
public theorem IsPeriodicPointWithGrowingSeed.isTwoSidedPeriodicPoint {A : Type*}
    {η : A → List A} {u : ℤ → A} {p : ℕ} (h : IsPeriodicPointWithGrowingSeed η u p) :
    IsTwoSidedPeriodicPoint η u p := h.2.1.1

/-- The Dumont–Thomas complement numeration system `rep_u : ℤ → {0, 1} ⊙ 𝒟*`, as the
relation "`w = rep_u(n)`": `rep_u(0) = 0`, `rep_u(-1) = 1`; for `n ≥ 1`,
`rep_u(n) = 0 ⊙ |m_{k-1}| ⊙ ⋯ ⊙ |m₀|` for the `k` and `u₀`-admissible sequence of
Theorem 4.1 applied to `u|_{ℤ≥0}` with period `p`; for `n ≤ -2`,
`rep_u(n) = 1 ⊙ |m_{k-1}| ⊙ ⋯ ⊙ |m₀|` for the `k` and `u₋₁`-admissible sequence of
Theorem 4.2 applied to `u|_{ℤ<0}` with period `p`. The defining conditions are those of
Theorems 4.1 and 4.2, in the same encoding (`n = N`, resp. `n = -N`, and
`u_{-|η^k(u₋₁)|} ⋯ u_{n-1}` written with integer indices). By the uniqueness parts of those
theorems the relation is functional, and by their existence parts it is total whenever `p` is
a period of `u` and the seed is growing.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Section 4 (definition of Dumont–Thomas complement
numeration systems for `ℤ`). -/
public def IsDumontThomasRep {A : Type*} (η : A → List A) (u : ℤ → A) (p : ℕ) (n : ℤ)
    (w : List ℕ) : Prop :=
  (n = 0 ∧ w = [0]) ∨ (n = -1 ∧ w = [1]) ∨
    (∃ (N k : ℕ) (s : ℕ → List A × A), 1 ≤ N ∧ n = N ∧ p ∣ k ∧
      IsLetterAdmissibleSequence η (u 0) s (k - 1) ∧
      ((List.range p).map fun t => (s (k - 1 - t)).1).flatten ≠ [] ∧
      (List.range N).map (fun j : ℕ => u j) =
        ((List.range k).reverse.map fun j => morphIterate η j (s j).1).flatten ∧
      w = 0 :: (List.range k).reverse.map fun j => (s j).1.length) ∨
    (∃ (N k : ℕ) (s : ℕ → List A × A), 2 ≤ N ∧ n = -N ∧ p ∣ k ∧
      N ≤ (morphIterate η k [u (-1)]).length ∧
      IsLetterAdmissibleSequence η (u (-1)) s (k - 1) ∧
      ((List.range p).map fun t => morphIterate η (p - 1 - t) (s (k - 1 - t)).1).flatten ++
          [(s (k - p)).2] ≠ morphIterate η p [u (-1)] ∧
      (List.range ((morphIterate η k [u (-1)]).length - N)).map
          (fun t : ℕ => u ((t : ℤ) - (morphIterate η k [u (-1)]).length)) =
        ((List.range k).reverse.map fun j => morphIterate η j (s j).1).flatten ∧
      w = 1 :: (List.range k).reverse.map fun j => (s j).1.length)

/-- `rep_u(0) = 0`.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Section 4 (definition of `rep_u`). -/
public theorem isDumontThomasRep_zero {A : Type*} (η : A → List A) (u : ℤ → A) (p : ℕ) :
    IsDumontThomasRep η u p 0 [0] := Or.inl ⟨rfl, rfl⟩

/-- `rep_u(-1) = 1`.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Section 4 (definition of `rep_u`). -/
public theorem isDumontThomasRep_neg_one {A : Type*} (η : A → List A) (u : ℤ → A) (p : ℕ) :
    IsDumontThomasRep η u p (-1) [1] := Or.inr (Or.inl ⟨rfl, rfl⟩)

/-- The automaton `𝒜_{η,s}` for the seed `s = b|a`: from a new initial state `start`, digit
`0` goes to `a` and digit `1` goes to `b`; afterwards it runs `𝒜_{η,·}`
(`substitutionAutomaton`). The result is `none` when the run is undefined or ends in `start`
(the empty word is not accepted, since `start` is not final).

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Section 6 (the automaton `𝒜_{η,s}`). -/
public def seedAutomaton {A : Type*} (η : A → List A) (b a : A) : List ℕ → Option A
  | [] => none
  | 0 :: w => substitutionAutomaton η a w
  | 1 :: w => substitutionAutomaton η b w
  | (_ + 2) :: _ => none

/-- `𝒜_{η,s}(0 ⊙ w) = 𝒜_{η,a}(w)`.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Section 6, Equation (automata relations). -/
public theorem seedAutomaton_zero_cons {A : Type*} (η : A → List A) (b a : A) (w : List ℕ) :
    seedAutomaton η b a (0 :: w) = substitutionAutomaton η a w := rfl

/-- `𝒜_{η,s}(1 ⊙ w) = 𝒜_{η,b}(w)`.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Section 6, Equation (automata relations). -/
public theorem seedAutomaton_one_cons {A : Type*} (η : A → List A) (b a : A) (w : List ℕ) :
    seedAutomaton η b a (1 :: w) = substitutionAutomaton η b w := rfl

/-- The empty word is not accepted by `𝒜_{η,s}`.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Section 6. -/
public theorem seedAutomaton_nil {A : Type*} (η : A → List A) (b a : A) :
    seedAutomaton η b a [] = none := rfl

/-- The digit word that follows the last letter `p` times from `c`: at each step it records
`|η(c)| - 1` and moves to the last letter of `η(c)`. For a substitution this is
`tail_{η,p,c}(|η^p(c)| - 1)`: the last position of `η^p(c)` has the `c`-admissible sequence
with `m_{i} a_{i} = η(a_{i+1})` (`a_p = c`), whose weighted length telescopes to
`|η^p(c)| - 1`, and by Lemma 3.9 that sequence is the one defining `tail`. In particular
`W_max = lastLetterDigits η p u₋₁` (while `W_min = 0^p`).

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Section 7 (the words `W_min` and `W_max`). -/
public def lastLetterDigits {A : Type*} (η : A → List A) : ℕ → A → List ℕ
  | 0, _ => []
  | k + 1, c =>
    match (η c).getLast? with
    | some d => ((η c).length - 1) :: lastLetterDigits η k d
    | none => []

/-- Recurrence for `lastLetterDigits` when `η(c)` ends with `d`.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Section 7. -/
public theorem lastLetterDigits_succ_of_getLast? {A : Type*} (η : A → List A) (k : ℕ) (c d : A)
    (h : (η c).getLast? = some d) :
    lastLetterDigits η (k + 1) c = ((η c).length - 1) :: lastLetterDigits η k d := by
  simp [lastLetterDigits, h]

/-- For the Fibonacci substitution `a ↦ ab`, `b ↦ a` (`a = 0`, `b = 1`) and `p = 2`,
`W_max = tail_{φ,2,b}(|φ²(b)| - 1) = 01`, as computed in the paper.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, proof of Proposition 9.2 (`W_max = 01`). -/
public theorem lastLetterDigits_fibonacci :
    lastLetterDigits (fun a : Fin 2 => if a = 0 then [0, 1] else [0]) 2 1 = [0, 1] := by
  decide

/-- The total order `≺` on `{0, 1} ⊙ 𝒟*`: every word starting with `1` precedes every word
starting with `0`; two words starting with `0` are compared in radix order (shorter first,
then lexicographically); two words starting with `1` are compared in reversed-radix order
(longer first, then lexicographically). Words of `ℕ*` not starting with `0` or `1` are never
related.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Section 8 (definition of the total order `≺`). -/
public def ComplementRadixLT (w w' : List ℕ) : Prop :=
  (w.head? = some 1 ∧ w'.head? = some 0) ∨
    (w.head? = some 0 ∧ w'.head? = some 0 ∧
      (w.length < w'.length ∨ (w.length = w'.length ∧ w < w'))) ∨
    (w.head? = some 1 ∧ w'.head? = some 1 ∧
      (w'.length < w.length ∨ (w.length = w'.length ∧ w < w')))

/-- Small cases from the paper's chain `⋯ ≺ 111 ≺ 10 ≺ 1 ≺ 0 ≺ 00 ≺ 01 ≺ 000`.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Section 8 (example after the definition of `≺`). -/
public theorem complementRadixLT_examples :
    ComplementRadixLT [1, 1, 1] [1, 0] ∧ ComplementRadixLT [1, 0] [1] ∧
      ComplementRadixLT [1] [0] ∧ ComplementRadixLT [0] [0, 0] ∧
      ComplementRadixLT [0, 0] [0, 1] ∧ ComplementRadixLT [0, 1] [0, 0, 0] := by
  simp only [ComplementRadixLT]
  refine ⟨by simp, by simp, by simp, by simp, ?_, by simp⟩
  simp only [List.head?_cons, List.length_cons, List.length_nil]
  exact Or.inr (Or.inl ⟨trivial, trivial, Or.inr ⟨trivial, List.Lex.cons (List.Lex.rel Nat.zero_lt_one)⟩⟩)

/-- The image language `⋃_{ℓ ∈ ℕ} ℒ_{ℓp+1}(𝒜_{η,s}) \ {0 W_min, 1 W_max} 𝒟*`: digit words
accepted by `𝒜_{η,s}` (`s = u₋₁|u₀`) whose length is `ℓp + 1`, which do not start with
`0 ⊙ 0^p` and do not start with `1 ⊙ W_max`.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Lemma 8.3 and Theorem 8.4. -/
public def dumontThomasLanguage {A : Type*} (η : A → List A) (u : ℤ → A) (p : ℕ) :
    Set (List ℕ) :=
  {w | (∃ ℓ : ℕ, w.length = ℓ * p + 1) ∧ (seedAutomaton η (u (-1)) (u 0) w).isSome ∧
    ¬ (0 :: List.replicate p 0) <+: w ∧ ¬ (1 :: lastLetterDigits η p (u (-1))) <+: w}

/-- Membership in the image language unfolds to its four conditions.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Lemma 8.3. -/
public theorem mem_dumontThomasLanguage {A : Type*} (η : A → List A) (u : ℤ → A) (p : ℕ)
    (w : List ℕ) :
    w ∈ dumontThomasLanguage η u p ↔
      (∃ ℓ : ℕ, w.length = ℓ * p + 1) ∧ (seedAutomaton η (u (-1)) (u 0) w).isSome ∧
        ¬ (0 :: List.replicate p 0) <+: w ∧ ¬ (1 :: lastLetterDigits η p (u (-1))) <+: w :=
  Iff.rfl

/-- `u`-quotient and `u`-remainder, case `n ≥ 1`: let `n = N ≥ 1` with the `u₀`-admissible
sequence `(mᵢ, aᵢ)_{i < k}` of `rep_u(n)` (Theorem 4.1 with the period `p`), and let
`q = |η^{k-p-1}(m_{k-1}) ⋯ η⁰(m_p)| ≥ 0` and `r = |η^{p-1}(m_{p-1}) ⋯ η⁰(m₀)|`. Then
`u_n = η^p(u_q)[r]` and `rep_u(n) = rep_u(q) ⊙ tail_{η,p,u_q}(r)`; the latter is stated as
`rep_u(q) = 0 ⊙ |m_{k-1}| ⊙ ⋯ ⊙ |m_p|` together with `(mᵢ, aᵢ)_{i < p}` being
`u_q`-admissible (so, by Lemma 3.9, `|m_{p-1}| ⊙ ⋯ ⊙ |m₀| = tail_{η,p,u_q}(r)`).

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Lemma 4.9 (with the `u`-quotient and `u`-remainder of
Section 4). -/
public theorem_wanted dumontThomasRep_quotient_remainder_pos {A : Type*} (η : A → List A)
    (u : ℤ → A) (p : ℕ) (hu : IsPeriodicPointWithGrowingSeed η u p) (N k : ℕ)
    (s : ℕ → List A × A) (hN : 1 ≤ N) (hk : p ∣ k)
    (hs : IsLetterAdmissibleSequence η (u 0) s (k - 1))
    (htop : ((List.range p).map fun t => (s (k - 1 - t)).1).flatten ≠ [])
    (hpre : (List.range N).map (fun j : ℕ => u j) =
      ((List.range k).reverse.map fun j => morphIterate η j (s j).1).flatten) :
    (morphIterate η p [u (∑ j ∈ Finset.range (k - p), (morphIterate η j (s (j + p)).1).length : ℕ)])[
        ∑ j ∈ Finset.range p, (morphIterate η j (s j).1).length]? = some (u N) ∧
      IsDumontThomasRep η u p
        (∑ j ∈ Finset.range (k - p), (morphIterate η j (s (j + p)).1).length : ℕ)
        (0 :: (List.range (k - p)).reverse.map fun j => (s (j + p)).1.length) ∧
      IsLetterAdmissibleSequence η
        (u (∑ j ∈ Finset.range (k - p), (morphIterate η j (s (j + p)).1).length : ℕ)) s (p - 1)

/-- `u`-quotient and `u`-remainder, case `n ≤ -2`: let `n = -N` (`N ≥ 2`) with the
`u₋₁`-admissible sequence `(mᵢ, aᵢ)_{i < k}` of `rep_u(n)` (Theorem 4.2 with the period
`p`), and let `q = |η^{k-p-1}(m_{k-1}) ⋯ η⁰(m_p)| - |η^{k-p}(u₋₁)| < 0` and
`r = |η^{p-1}(m_{p-1}) ⋯ η⁰(m₀)|`. Then `u_n = η^p(u_q)[r]`,
`rep_u(q) = 1 ⊙ |m_{k-1}| ⊙ ⋯ ⊙ |m_p|`, and `(mᵢ, aᵢ)_{i < p}` is `u_q`-admissible, i.e.
`rep_u(n) = rep_u(q) ⊙ tail_{η,p,u_q}(r)`.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Lemma 4.9 (with the `u`-quotient and `u`-remainder of
Section 4). -/
public theorem_wanted dumontThomasRep_quotient_remainder_neg {A : Type*} (η : A → List A)
    (u : ℤ → A) (p : ℕ) (hu : IsPeriodicPointWithGrowingSeed η u p) (N k : ℕ)
    (s : ℕ → List A × A) (hN : 2 ≤ N) (hk : p ∣ k)
    (hNk : N ≤ (morphIterate η k [u (-1)]).length)
    (hs : IsLetterAdmissibleSequence η (u (-1)) s (k - 1))
    (htop : ((List.range p).map fun t => morphIterate η (p - 1 - t) (s (k - 1 - t)).1).flatten ++
      [(s (k - p)).2] ≠ morphIterate η p [u (-1)])
    (hpre : (List.range ((morphIterate η k [u (-1)]).length - N)).map
        (fun t : ℕ => u ((t : ℤ) - (morphIterate η k [u (-1)]).length)) =
      ((List.range k).reverse.map fun j => morphIterate η j (s j).1).flatten) :
    (morphIterate η p [u ((∑ j ∈ Finset.range (k - p), (morphIterate η j (s (j + p)).1).length : ℕ) -
        ((morphIterate η (k - p) [u (-1)]).length : ℤ))])[
        ∑ j ∈ Finset.range p, (morphIterate η j (s j).1).length]? = some (u (-N)) ∧
      IsDumontThomasRep η u p
        ((∑ j ∈ Finset.range (k - p), (morphIterate η j (s (j + p)).1).length : ℕ) -
          ((morphIterate η (k - p) [u (-1)]).length : ℤ))
        (1 :: (List.range (k - p)).reverse.map fun j => (s (j + p)).1.length) ∧
      IsLetterAdmissibleSequence η
        (u ((∑ j ∈ Finset.range (k - p), (morphIterate η j (s (j + p)).1).length : ℕ) -
          ((morphIterate η (k - p) [u (-1)]).length : ℤ))) s (p - 1)

/-- Two-sided periodic points are automatic in the Dumont–Thomas complement numeration
system: every `n ∈ ℤ` has a representation `rep_u(n)`, and `u_n = 𝒜_{η,s}(rep_u(n))` for the
seed `s = u₋₁|u₀`.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Theorem 6.1. -/
public theorem_wanted seedAutomaton_dumontThomasRep {A : Type*} (η : A → List A) (u : ℤ → A)
    (p : ℕ) (hu : IsPeriodicPointWithGrowingSeed η u p) (n : ℤ) :
    (∃ w, IsDumontThomasRep η u p n w) ∧
      ∀ w, IsDumontThomasRep η u p n w → seedAutomaton η (u (-1)) (u 0) w = some (u n)

/-- `W_min` and `W_max` are neutral words: for `w ∈ ℒ(𝒜_{η,s})` and every `i ≥ 0`,
`𝒜_{η,s}(0 v) = 𝒜_{η,s}(0 (W_min)^i v)` and `𝒜_{η,s}(1 v) = 𝒜_{η,s}(1 (W_max)^i v)`, where
`W_min = 0^p` and `W_max = tail_{η,p,u₋₁}(|η^p(u₋₁)| - 1)` (`lastLetterDigits`).

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Lemma 7.1. -/
public theorem_wanted seedAutomaton_neutral_padding {A : Type*} (η : A → List A) (u : ℤ → A)
    (p : ℕ) (hu : IsPeriodicPointWithGrowingSeed η u p) (v : List ℕ) (i : ℕ) :
    ((seedAutomaton η (u (-1)) (u 0) (0 :: v)).isSome →
        seedAutomaton η (u (-1)) (u 0) (0 :: (List.replicate (i * p) 0 ++ v)) =
          seedAutomaton η (u (-1)) (u 0) (0 :: v)) ∧
      ((seedAutomaton η (u (-1)) (u 0) (1 :: v)).isSome →
        seedAutomaton η (u (-1)) (u 0)
            (1 :: ((List.replicate i (lastLetterDigits η p (u (-1)))).flatten ++ v)) =
          seedAutomaton η (u (-1)) (u 0) (1 :: v))

/-- `rep_u` is increasing for `≺`: if `n < n'` then `rep_u(n) ≺ rep_u(n')`.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Proposition 8.2. -/
public theorem_wanted dumontThomasRep_strictMono {A : Type*} (η : A → List A) (u : ℤ → A)
    (p : ℕ) (hu : IsPeriodicPointWithGrowingSeed η u p) (n n' : ℤ) (w w' : List ℕ)
    (hw : IsDumontThomasRep η u p n w) (hw' : IsDumontThomasRep η u p n' w') (h : n < n') :
    ComplementRadixLT w w'

/-- The image of `rep_u` is `⋃_{ℓ ∈ ℕ} ℒ_{ℓp+1}(𝒜_{η,s}) \ {0 W_min, 1 W_max} 𝒟*`.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Lemma 8.3. -/
public theorem_wanted range_dumontThomasRep {A : Type*} (η : A → List A) (u : ℤ → A) (p : ℕ)
    (hu : IsPeriodicPointWithGrowingSeed η u p) (w : List ℕ) :
    (∃ n, IsDumontThomasRep η u p n w) ↔ w ∈ dumontThomasLanguage η u p

/-- Characterization of `rep_u`: a map `f : ℤ → ℕ*` equals `rep_u` iff it is increasing for
`≺`, its image is `⋃_{ℓ ∈ ℕ} ℒ_{ℓp+1}(𝒜_{η,s}) \ {0 W_min, 1 W_max} 𝒟*`, and `f(0) = 0`.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Theorem 8.4. -/
public theorem_wanted dumontThomasRep_iff_strictMono_range {A : Type*} (η : A → List A)
    (u : ℤ → A) (p : ℕ) (hu : IsPeriodicPointWithGrowingSeed η u p) (f : ℤ → List ℕ) :
    (∀ n, IsDumontThomasRep η u p n (f n)) ↔
      ((∀ n n', n < n' → ComplementRadixLT (f n) (f n')) ∧
        Set.range f = dumontThomasLanguage η u p ∧ f 0 = [0])

/-- The two's complement value of a binary word `w = w_{k-1} ⋯ w₀` (head first):
`val_{2c}(w) = ∑_{i<k} wᵢ 2^i - w_{k-1} 2^k` (`0` for the empty word).

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Section 9.1. -/
public def twosComplementValue (w : List ℕ) : ℤ :=
  (∑ i ∈ Finset.range w.length, (w.reverse.getD i 0 : ℤ) * 2 ^ i) -
    (w.headD 0 : ℤ) * 2 ^ w.length

/-- `val_{2c}(1) = -1`, `val_{2c}(10) = -2`, `val_{2c}(101) = -3`, `val_{2c}(011) = 3`.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Section 9.1 (table of `rep_{2c}`). -/
public theorem twosComplementValue_examples :
    twosComplementValue [1] = -1 ∧ twosComplementValue [1, 0] = -2 ∧
      twosComplementValue [1, 0, 1] = -3 ∧ twosComplementValue [0, 1, 1] = 3 := by
  decide

/-- For a `2`-uniform substitution `ψ` and a two-sided fixed point `β` of `ψ` (period `1`),
`rep_β = rep_{2c}`: `w = rep_β(n)` iff `w` is the two's complement representation of `n`,
i.e. `w ∈ 𝒟⁺ \ (00𝒟* ∪ 11𝒟*)` over `𝒟 = {0, 1}` and `val_{2c}(w) = n`. The substitution and
growing-seed hypotheses are implied by `2`-uniformity, and period `1` is automatically the
least period.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Proposition 9.1. -/
public theorem_wanted dumontThomasRep_uniform_two_iff_twosComplement {A : Type*}
    (ψ : A → List A) (hψ : ∀ c, (ψ c).length = 2) (β : ℤ → A)
    (hβ : IsTwoSidedPeriodicPoint ψ β 1) (n : ℤ) (w : List ℕ) :
    IsDumontThomasRep ψ β 1 n w ↔
      (w ≠ [] ∧ (∀ d ∈ w, d < 2) ∧ ¬ [0, 0] <+: w ∧ ¬ [1, 1] <+: w ∧
        twosComplementValue w = n)

/-- The Fibonacci complement value of `w = w_{k-1} ⋯ w₀` (head first):
`val_{𝓕c}(w) = ∑_{i<k} wᵢ Fᵢ - w_{k-1} F_k` with `F₀ = 1`, `F₁ = 2`, i.e. `Fᵢ = fib (i + 2)`.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Section 9.2. -/
public def fibonacciComplementValue (w : List ℕ) : ℤ :=
  (∑ i ∈ Finset.range w.length, (w.reverse.getD i 0 : ℤ) * (Nat.fib (i + 2) : ℤ)) -
    (w.headD 0 : ℤ) * (Nat.fib (w.length + 2) : ℤ)

/-- `val_{𝓕c}(1) = -1`, `val_{𝓕c}(100) = -2`, `val_{𝓕c}(001) = 1`, `val_{𝓕c}(010) = 2`.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Section 9.2. -/
public theorem fibonacciComplementValue_examples :
    fibonacciComplementValue [1] = -1 ∧ fibonacciComplementValue [1, 0, 0] = -2 ∧
      fibonacciComplementValue [0, 0, 1] = 1 ∧ fibonacciComplementValue [0, 1, 0] = 2 := by
  decide

/-- For the Fibonacci substitution `φ : a ↦ ab, b ↦ a` (`a = 0`, `b = 1`) and its two-sided
periodic point `γ` of period `2` with seed `b|a`, `rep_γ = rep_{𝓕c}`: `w = rep_γ(n)` iff `w`
lies in `L = 𝒟(𝒟𝒟)* \ (𝒟*11𝒟* ∪ 000𝒟* ∪ 101𝒟*)` over `𝒟 = {0, 1}` and
`val_{𝓕c}(w) = n`. Period `2` is automatically the least period here, since `φ(b) = a` does
not end in `b`.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Proposition 9.2. -/
public theorem_wanted dumontThomasRep_fibonacci_iff_fibonacciComplement (γ : ℤ → Fin 2)
    (hγ : IsTwoSidedPeriodicPoint (fun a : Fin 2 => if a = 0 then [0, 1] else [0]) γ 2)
    (hγneg : γ (-1) = 1) (hγ₀ : γ 0 = 0) (n : ℤ) (w : List ℕ) :
    IsDumontThomasRep (fun a : Fin 2 => if a = 0 then [0, 1] else [0]) γ 2 n w ↔
      (w.length % 2 = 1 ∧ (∀ d ∈ w, d < 2) ∧ ¬ [1, 1] <:+: w ∧ ¬ [0, 0, 0] <+: w ∧
        ¬ [1, 0, 1] <+: w ∧ fibonacciComplementValue w = n)

end

end MetaMathlibExt
