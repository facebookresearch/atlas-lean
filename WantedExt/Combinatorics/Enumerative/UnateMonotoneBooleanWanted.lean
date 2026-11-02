/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Order.BooleanFunction.SelfDual

namespace MetaMathlibExt

@[expose] public section

/-! Boolean functions on `n` variables are `(Fin n → Bool) → Bool`; monotone
means Mathlib's `Monotone` for the coordinatewise order with `false ≤ true`.
The paper's variable `x₁` (the top bit of the truth table) is index `0`. -/

/-- **Weight of a Boolean function.** The weight $\mathrm{wt}(f)$ of an $n$-variable Boolean
function $f \colon \{0,1\}^n \to \{0,1\}$ is the number of inputs $x \in \{0,1\}^n$ with
$f(x) = 1$.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Section 2. -/
public def boolFunWeight {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  (Finset.univ.filter fun x => f x = true).card

/-- **Weight of the constant one function.** For every $n$, the constant function $1$ on $n$
variables has weight $2^n$.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Section 2. -/
public theorem boolFunWeight_const_true (n : ℕ) :
    boolFunWeight (fun _ : Fin n → Bool => true) = 2 ^ n := by
  simp [boolFunWeight]

/-- **Boolean functions increasing in a variable.** An $n$-variable Boolean function $f$ is
monotone increasing in the variable $x_i$ if for every input $x$ with $x_i = 0$, changing $x_i$
to $1$ does not decrease the value: $f(x) \le f(x')$, where $x'$ agrees with $x$ except that
$x'_i = 1$.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Section 2. -/
public def IsBoolFunIncreasingIn {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) :
    Prop :=
  ∀ x : Fin n → Bool, x i = false → f x ≤ f (Function.update x i true)

/-- **Boolean functions decreasing in a variable.** An $n$-variable Boolean function $f$ is
monotone decreasing in the variable $x_i$ if for every input $x$ with $x_i = 0$, changing $x_i$
to $1$ does not increase the value: $f(x') \le f(x)$, where $x'$ agrees with $x$ except that
$x'_i = 1$.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Section 2. -/
public def IsBoolFunDecreasingIn {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) :
    Prop :=
  ∀ x : Fin n → Bool, x i = false → f (Function.update x i true) ≤ f x

/-- **Unate Boolean function.** A Boolean function $f$ on $n$ variables, with Boolean values
$0 < 1$, is unate when for each variable $i$ either $f$ is increasing in $x_i$ (changing $x_i$
from $0$ to $1$, with the other variables fixed, never decreases the value of $f$) or $f$ is
decreasing in $x_i$ (that change never increases the value of $f$).

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Section 1. -/
public def IsUnateBoolFun {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ i : Fin n, IsBoolFunIncreasingIn f i ∨ IsBoolFunDecreasingIn f i

/-- **Monotone Boolean functions are unate.** Every Boolean function $f$ on $n$ variables that
is monotone, for the coordinatewise order on $\{0,1\}^n$ with $0 \le 1$, is unate.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Section 1. -/
public theorem isUnateBoolFun_of_monotone {n : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : Monotone f) : IsUnateBoolFun f := by
  intro i
  left
  intro x _
  apply hf
  intro j
  rcases eq_or_ne j i with rfl | h
  · simp
  · simp [Function.update_of_ne h]

/-- **Non-degeneracy in a variable.** An $n$-variable Boolean function $f$ is non-degenerate
on the variable $x_i$ when flipping $x_i$ changes the value of $f$ at some input: there is
$x \in \{0,1\}^n$ with $f(x) \ne f(x')$, where $x'$ is $x$ with its $i$-th coordinate negated.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Section 2. -/
public def IsBoolFunNondegenerateOn {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) :
    Prop :=
  ∃ x : Fin n → Bool, f x ≠ f (Function.update x i (!x i))

/-- **Non-degenerate Boolean functions.** An $n$-variable Boolean function $f$ is non-degenerate
when it is non-degenerate on every variable $x_i$, $1 \le i \le n$: for each $i$ there is an input
$x \in \{0,1\}^n$ with $f(x) \ne f(x')$, where $x'$ is $x$ with its $i$-th coordinate negated.
For $n = 0$ the condition is vacuous, so both $0$-variable (constant) functions are
non-degenerate, matching the paper's convention.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Section 2 and Remark 2. -/
public def IsNondegenerateBoolFun {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ i : Fin n, IsBoolFunNondegenerateOn f i

/-- **A projection is non-degenerate on its own variable.** For every $n$ and every index
$i \in \{1, \ldots, n\}$, the projection $x \mapsto x_i$ on $\{0,1\}^n$ is non-degenerate on
the variable $x_i$.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Section 2. -/
public theorem isBoolFunNondegenerateOn_proj {n : ℕ} (i : Fin n) :
    IsBoolFunNondegenerateOn (fun x : Fin n → Bool => x i) i :=
  ⟨fun _ => false, by simp⟩

/-- **Concatenation of two Boolean functions.** The concatenation $g \,\|\, h$ of two $n$-variable
Boolean functions $g$ and $h$ is the $(n+1)$-variable function whose truth table is that of $g$
followed by that of $h$: its value at $(x_1, x_2, \dots, x_{n+1})$ is $g(x_2, \dots, x_{n+1})$ if
$x_1 = 0$ and $h(x_2, \dots, x_{n+1})$ if $x_1 = 1$. Equivalently,
$(g \,\|\, h)(x) = \bar{x}_1 g(x_2, \dots, x_{n+1}) \oplus x_1 h(x_2, \dots, x_{n+1})$.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Section 2, equation (1). -/
public def boolFunConcat {n : ℕ} (g h : (Fin n → Bool) → Bool) :
    (Fin (n + 1) → Bool) → Bool :=
  fun x => cond (x 0) (h (Fin.tail x)) (g (Fin.tail x))

/-- **Evaluating a concatenation.** For $n$-variable Boolean functions $g$ and $h$, every
$b \in \{0, 1\}$ and every $x \in \{0, 1\}^n$, the concatenation $g \,\|\, h$ takes the value $g(x)$
at the input $(b, x_1, \dots, x_n)$ if $b = 0$ and the value $h(x)$ there if $b = 1$.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Section 2, equation (1). -/
public theorem boolFunConcat_cons {n : ℕ} (g h : (Fin n → Bool) → Bool) (b : Bool)
    (x : Fin n → Bool) : boolFunConcat g h (Fin.cons b x) = cond b (h x) (g x) := by
  simp [boolFunConcat]

/-- **Permutation equivalence of Boolean functions.** An $n$-variable Boolean function $f$ is
permutation-equivalent to $g$ when $g$ is obtained from $f$ by permuting the variables: there
is a permutation $\sigma$ of $\{1, \ldots, n\}$ such that
$g(x_1, \ldots, x_n) = f(x_{\sigma(1)}, \ldots, x_{\sigma(n)})$ for every $x \in \{0,1\}^n$.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Section 2.1. -/
public def IsBoolFunVarPermEquiv {n : ℕ} (f g : (Fin n → Bool) → Bool) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), ∀ x : Fin n → Bool, g x = f (x ∘ σ)

/-- **Permutation equivalence is reflexive.** Every $n$-variable Boolean function is
permutation-equivalent to itself.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Section 2.1. -/
public theorem isBoolFunVarPermEquiv_refl {n : ℕ} (f : (Fin n → Bool) → Bool) :
    IsBoolFunVarPermEquiv f f :=
  ⟨1, fun x => by simp⟩

/-- **NN-equivalence of Boolean functions.** An $n$-variable Boolean function $f$ is
NN-equivalent to $g$ when $g$ is obtained from $f$ by negating some of the inputs and
possibly the output: there are $a \in \{0,1\}^n$ and $c \in \{0,1\}$ such that
$g(x) = f(x \oplus a) \oplus c$ for every $x \in \{0,1\}^n$, where $\oplus$ is exclusive or
(coordinatewise on vectors).

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 13. -/
public def IsBoolFunNNEquiv {n : ℕ} (f g : (Fin n → Bool) → Bool) : Prop :=
  ∃ (a : Fin n → Bool) (c : Bool), ∀ x : Fin n → Bool,
    g x = xor (f fun i => xor (x i) (a i)) c

/-- Every Boolean function is NN-equivalent to itself.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 13. -/
public theorem isBoolFunNNEquiv_refl {n : ℕ} (f : (Fin n → Bool) → Bool) :
    IsBoolFunNNEquiv f f :=
  ⟨fun _ => false, false, fun x => by simp⟩

/-- **NPN-equivalence of Boolean functions.** An $n$-variable Boolean function $f$ is
NPN-equivalent to $g$ when $g$ is obtained from $f$ by permuting the variables, negating some
of the inputs and possibly negating the output: there are a permutation $\sigma$ of
$\{1, \ldots, n\}$, a vector $a \in \{0,1\}^n$ and a bit $c \in \{0,1\}$ such that
$g(x) = f(x_{\sigma(1)} \oplus a_1, \ldots, x_{\sigma(n)} \oplus a_n) \oplus c$ for every
$x \in \{0,1\}^n$, where $\oplus$ is exclusive or.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 14. -/
public def IsBoolFunNPNEquiv {n : ℕ} (f g : (Fin n → Bool) → Bool) : Prop :=
  ∃ (σ : Equiv.Perm (Fin n)) (a : Fin n → Bool) (c : Bool), ∀ x : Fin n → Bool,
    g x = xor (f fun i => xor (x (σ i)) (a i)) c

/-- **NPN-equivalence is reflexive.** Every $n$-variable Boolean function is NPN-equivalent to
itself.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 14. -/
public theorem isBoolFunNPNEquiv_refl {n : ℕ} (f : (Fin n → Bool) → Bool) :
    IsBoolFunNPNEquiv f f :=
  ⟨1, fun _ => false, false, fun x => by simp⟩

/-- **Number of classes of Boolean functions.** Given a relation $R$ and a property $P$ of
$n$-variable Boolean functions, the number of $R$-inequivalent $n$-variable functions with $P$ is
the number of distinct sets $\{g : P(g) \text{ and } R(f, g)\}$ as $f$ ranges over the functions
with $P$. When $R$ is an equivalence relation, this is the number of equivalence classes of $R$
restricted to the functions with $P$. The paper's $[P]_n$ is this count when $R$ is equivalence
under permutation of the variables.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Section 2.1. -/
public noncomputable def boolFunClassCount {n : ℕ}
    (R : ((Fin n → Bool) → Bool) → ((Fin n → Bool) → Bool) → Prop)
    (P : ((Fin n → Bool) → Bool) → Prop) : ℕ :=
  Nat.card {S : Set ((Fin n → Bool) → Bool) // ∃ f, P f ∧ S = {g | P g ∧ R f g}}

/-- **The empty property has no classes.** For every relation $R$ on $n$-variable Boolean
functions, the number of $R$-inequivalent $n$-variable Boolean functions with the property that
holds for no function is $0$.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Section 2.1. -/
public theorem boolFunClassCount_false {n : ℕ}
    (R : ((Fin n → Bool) → Bool) → ((Fin n → Bool) → Bool) → Prop) :
    boolFunClassCount R (fun _ => False) = 0 := by
  rw [boolFunClassCount, Nat.card_eq_zero]
  left
  exact ⟨fun ⟨_, f, hf, _⟩ => hf⟩

/-- **Counting Boolean functions by their non-degenerate restrictions.** Let $P$ be a property
of Boolean functions on any number of variables that is invariant under renaming variables
along injections: for all $m, n$, every injective map $e$ from $\{1, \dots, m\}$ to
$\{1, \dots, n\}$ and every $m$-variable function $g$, the $n$-variable function
$x \mapsto g(x_{e(1)}, \dots, x_{e(m)})$ has $P$ if and only if $g$ has $P$. Write $P_n$ for the
number of $n$-variable Boolean functions with $P$ and $\mathrm{nd}\text{-}P_i$ for the number of
non-degenerate $i$-variable Boolean functions with $P$. Then for every $n \ge 0$,

$$P_n = \sum_{i=0}^{n} \binom{n}{i} \, \mathrm{nd}\text{-}P_i.$$

The invariance hypothesis cannot be dropped: if $P$ holds exactly for the four $1$-variable
functions, then $P_1 = 4$ but the right-hand side is $0 + 2 = 2$.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 1 (`jis-2025-25.3.4-prop-1`). -/
public theorem_wanted card_boolFun_eq_sum_choose_card_nondegenerate
    (P : ∀ n : ℕ, ((Fin n → Bool) → Bool) → Prop)
    (hP : ∀ (m n : ℕ) (e : Fin m ↪ Fin n) (g : (Fin m → Bool) → Bool),
      P n (fun x => g (x ∘ e)) ↔ P m g)
    (n : ℕ) :
    Nat.card {f : (Fin n → Bool) → Bool // P n f}
      = ∑ i ∈ Finset.range (n + 1),
          n.choose i * Nat.card {f : (Fin i → Bool) → Bool // IsNondegenerateBoolFun f ∧ P i f}

/-- **Counting non-degenerate Boolean functions by inclusion–exclusion.** Let $P$ be a property
of Boolean functions on any number of variables that is invariant under renaming variables
along injections: for all $m, n$, every injective map $e$ from $\{1, \dots, m\}$ to
$\{1, \dots, n\}$ and every $m$-variable function $g$, the $n$-variable function
$x \mapsto g(x_{e(1)}, \dots, x_{e(m)})$ has $P$ if and only if $g$ has $P$. Write $P_i$ for the
number of $i$-variable Boolean functions with $P$ and $\mathrm{nd}\text{-}P_n$ for the number of
non-degenerate $n$-variable Boolean functions with $P$. Then for every $n \ge 0$,

$$\mathrm{nd}\text{-}P_n = \sum_{i=0}^{n} (-1)^{n-i} \binom{n}{i} P_i.$$

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 1 (`jis-2025-25.3.4-prop-1`). -/
public theorem_wanted card_nondegenerate_boolFun_eq_alternating_sum
    (P : ∀ n : ℕ, ((Fin n → Bool) → Bool) → Prop)
    (hP : ∀ (m n : ℕ) (e : Fin m ↪ Fin n) (g : (Fin m → Bool) → Bool),
      P n (fun x => g (x ∘ e)) ↔ P m g)
    (n : ℕ) :
    (Nat.card {f : (Fin n → Bool) → Bool // IsNondegenerateBoolFun f ∧ P n f} : ℤ)
      = ∑ i ∈ Finset.range (n + 1),
          (-1) ^ (n - i) * (n.choose i : ℤ) * Nat.card {f : (Fin i → Bool) → Bool // P i f}

/-- **Unate versus monotone Boolean function counts.** For $n \ge 0$, write $U_n$ and $M_n$ for
the numbers of unate and of monotone $n$-variable Boolean functions, $BU_n$ and $BM_n$ for the
numbers of those that are moreover balanced, that is, twice their weight equals $2^n$, and write
the prefix $\mathrm{nd}\text{-}$ for the same counts restricted to non-degenerate functions.
Then $\mathrm{nd}\text{-}U_n = 2^n \, \mathrm{nd}\text{-}M_n$,
$\mathrm{nd}\text{-}BU_n = 2^n \, \mathrm{nd}\text{-}BM_n$, $U_n \le 2^n M_n$ and
$BU_n \le 2^n BM_n$.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 3 (`jis-2025-25.3.4-prop-3`). -/
public theorem_wanted card_unate_boolFun_relations (n : ℕ) :
    Nat.card {f : (Fin n → Bool) → Bool // IsNondegenerateBoolFun f ∧ IsUnateBoolFun f}
        = 2 ^ n * Nat.card {f : (Fin n → Bool) → Bool //
            IsNondegenerateBoolFun f ∧ Monotone f} ∧
      Nat.card {f : (Fin n → Bool) → Bool //
          IsNondegenerateBoolFun f ∧ IsUnateBoolFun f ∧ 2 * boolFunWeight f = 2 ^ n}
        = 2 ^ n * Nat.card {f : (Fin n → Bool) → Bool //
            IsNondegenerateBoolFun f ∧ Monotone f ∧ 2 * boolFunWeight f = 2 ^ n} ∧
      Nat.card {f : (Fin n → Bool) → Bool // IsUnateBoolFun f}
        ≤ 2 ^ n * Nat.card {f : (Fin n → Bool) → Bool // Monotone f} ∧
      Nat.card {f : (Fin n → Bool) → Bool // IsUnateBoolFun f ∧ 2 * boolFunWeight f = 2 ^ n}
        ≤ 2 ^ n * Nat.card {f : (Fin n → Bool) → Bool //
            Monotone f ∧ 2 * boolFunWeight f = 2 ^ n}

/-- **Monotone concatenations of Boolean functions (Bakoev).** Let $g$ and $h$ be Boolean
functions on $n$ variables, and let $g \parallel h$ be their concatenation, the function on
$n + 1$ variables that equals $g$ of the remaining variables when its first variable is $0$ and
$h$ of them when it is $1$. Then $g \parallel h$ is monotone if and only if $g$ and $h$ are both
monotone and $g(x) \le h(x)$ for every $x \in \{0,1\}^n$.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 4 (`jis-2025-25.3.4-prop-4`),
quoting Bakoev. -/
public theorem_wanted monotone_boolFunConcat_iff {n : ℕ} (g h : (Fin n → Bool) → Bool) :
    Monotone (boolFunConcat g h) ↔ Monotone g ∧ Monotone h ∧ g ≤ h

/-- **The dual of a monotone Boolean function is monotone.** If a Boolean function $f$ on $n$
variables is monotone, then so is its dual $f^\star$, defined by $f^\star(x) = \neg f(\bar{x})$,
where $\bar{x}$ is the coordinatewise complement of $x \in \{0,1\}^n$.

In the notation of the source, $f^\star$ is $\overline{f^r}$, where $f^r(x) = f(\bar{x})$ is
the function whose truth table is that of $f$ reversed.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 5 (`jis-2025-25.3.4-prop-5`). -/
public theorem_wanted monotone_booleanFunctionDual {n : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : Monotone f) : Monotone (booleanFunctionDual n f)

/-- **Unateness of a concatenation.** Let $g$ and $h$ be $n$-variable Boolean functions and let
$g \| h$ be their concatenation, the $(n+1)$-variable function equal to $g$ of the remaining
variables when the first variable is $0$ and to $h$ of them when it is $1$. Then $g \| h$ is
unate if and only if $g$ and $h$ are unate, for each variable $x_i$ either both $g$ and $h$
are monotone increasing in $x_i$ or both are monotone decreasing in $x_i$, and $g \le h$
pointwise or $h \le g$ pointwise.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 6 (`jis-2025-25.3.4-prop-6`). -/
public theorem_wanted isUnateBoolFun_boolFunConcat_iff {n : ℕ}
    (g h : (Fin n → Bool) → Bool) :
    IsUnateBoolFun (boolFunConcat g h) ↔
      IsUnateBoolFun g ∧ IsUnateBoolFun h ∧
        (∀ i : Fin n, (IsBoolFunIncreasingIn g i ∧ IsBoolFunIncreasingIn h i) ∨
          (IsBoolFunDecreasingIn g i ∧ IsBoolFunDecreasingIn h i)) ∧
        (g ≤ h ∨ h ≤ g)

/-- **The negation of a unate function is unate.** If an $n$-variable Boolean function $f$ is
unate, then so is its negation $x \mapsto \lnot f(x)$.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 7 (`jis-2025-25.3.4-prop-7`). -/
public theorem_wanted isUnateBoolFun_not {n : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : IsUnateBoolFun f) : IsUnateBoolFun fun x => !f x

/-- **Weight symmetry of monotone Boolean functions.** For all $n \ge 0$ and all $w$ with
$0 \le w \le 2^n$, the number of monotone $n$-variable Boolean functions of weight $w$ equals
the number of monotone $n$-variable Boolean functions of weight $2^n - w$.

The source assumes $n \ge 1$; the case $n = 0$ is included here.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 8 (`jis-2025-25.3.4-prop-8`). -/
public theorem_wanted card_monotone_boolFun_weight_symm (n w : ℕ) (hw : w ≤ 2 ^ n) :
    Nat.card {f : (Fin n → Bool) → Bool // Monotone f ∧ boolFunWeight f = w}
      = Nat.card {f : (Fin n → Bool) → Bool // Monotone f ∧ boolFunWeight f = 2 ^ n - w}

/-- **Weight symmetry of unate Boolean functions.** For all $n \ge 0$ and all $w$ with
$0 \le w \le 2^n$, the number of unate $n$-variable Boolean functions of weight $w$ equals the
number of unate $n$-variable Boolean functions of weight $2^n - w$.

The source assumes $n \ge 1$; the case $n = 0$ is included here.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 9 (`jis-2025-25.3.4-prop-9`). -/
public theorem_wanted card_unate_boolFun_weight_symm (n w : ℕ) (hw : w ≤ 2 ^ n) :
    Nat.card {f : (Fin n → Bool) → Bool // IsUnateBoolFun f ∧ boolFunWeight f = w}
      = Nat.card {f : (Fin n → Bool) → Bool // IsUnateBoolFun f ∧ boolFunWeight f = 2 ^ n - w}

/-- **Permutation classes counted by non-degenerate ones.** Let $(P_n)_{n \ge 0}$ be a family of
properties, $P_n$ a property of $n$-variable Boolean functions, that is invariant under renaming
variables: for all $m$ and $n$, every injection $e$ from $\{1, \dots, m\}$ to $\{1, \dots, n\}$
and every $m$-variable function $g$, the $n$-variable function $x \mapsto g(x \circ e)$ has $P_n$
if and only if $g$ has $P_m$. Write $[P]_n$ for the number of classes of $n$-variable functions
with $P_n$ under permutation of the variables, and $\mathrm{nd}[P]_n$ for the same count over the
non-degenerate $n$-variable functions with $P_n$. Then for every $n$,
$$[P]_n = \sum_{i=0}^{n} \mathrm{nd}[P]_i.$$

The paper assumes only closure under permutations of the variables; the counting argument also
needs invariance under adding or removing dummy variables. Closure under permutations alone is not
enough: if $P_1$ holds for all four $1$-variable functions and $P_n$ holds for none when
$n \ne 1$, then $[P]_1 = 4$ but $\mathrm{nd}[P]_0 + \mathrm{nd}[P]_1 = 0 + 2 = 2$.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 11 (`jis-2025-25.3.4-prop-11`). -/
public theorem_wanted boolFunClassCount_varPerm_eq_sum_nondegenerate
    (P : ∀ n : ℕ, ((Fin n → Bool) → Bool) → Prop)
    (hP : ∀ (m n : ℕ) (e : Fin m ↪ Fin n) (g : (Fin m → Bool) → Bool),
      P n (fun x => g (x ∘ e)) ↔ P m g)
    (n : ℕ) :
    boolFunClassCount IsBoolFunVarPermEquiv (P n)
      = ∑ i ∈ Finset.range (n + 1),
          boolFunClassCount IsBoolFunVarPermEquiv (fun f => IsNondegenerateBoolFun f ∧ P i f)

/-- **Non-degenerate permutation classes as a difference.** Let $(P_n)_{n \ge 0}$ be a family of
properties, $P_n$ a property of $n$-variable Boolean functions, that is invariant under renaming
variables: for all $m$ and $n$, every injection $e$ from $\{1, \dots, m\}$ to $\{1, \dots, n\}$
and every $m$-variable function $g$, the $n$-variable function $x \mapsto g(x \circ e)$ has $P_n$
if and only if $g$ has $P_m$. Write $[P]_n$ for the number of classes of $n$-variable functions
with $P_n$ under permutation of the variables, and $\mathrm{nd}[P]_n$ for the same count over the
non-degenerate $n$-variable functions with $P_n$. Then for every $n$,
$$\mathrm{nd}[P]_{n+1} = [P]_{n+1} - [P]_n,$$
where the subtraction is truncated at $0$; this is the paper's
$\mathrm{nd}[P]_n = [P]_n - [P]_{n-1}$ for $n \ge 1$.

The paper assumes only closure under permutations of the variables, which is not enough; see the
summation form of Proposition 11.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 11 (`jis-2025-25.3.4-prop-11`). -/
public theorem_wanted boolFunClassCount_varPerm_nondegenerate_eq_sub
    (P : ∀ n : ℕ, ((Fin n → Bool) → Bool) → Prop)
    (hP : ∀ (m n : ℕ) (e : Fin m ↪ Fin n) (g : (Fin m → Bool) → Bool),
      P n (fun x => g (x ∘ e)) ↔ P m g)
    (n : ℕ) :
    boolFunClassCount IsBoolFunVarPermEquiv (fun f => IsNondegenerateBoolFun f ∧ P (n + 1) f)
      = boolFunClassCount IsBoolFunVarPermEquiv (P (n + 1))
        - boolFunClassCount IsBoolFunVarPermEquiv (P n)

/-- **Unate versus monotone permutation classes.** Write $[Q]_n$ for the number of classes of
$n$-variable Boolean functions with property $Q$ under permutation of the variables. Let $U$, $M$,
$B$ and $\mathrm{nd}$ be the properties of being unate, monotone (nondecreasing for the
coordinatewise order with $0 < 1$), balanced (true of a function $f$ when $2\,\mathrm{wt}(f) = 2^n$,
where $\mathrm{wt}(f)$ is the weight of $f$) and non-degenerate, and write juxtaposition for
conjunction, so that $BU$ is the property of being balanced and unate. Then for every $n$,
$[\mathrm{nd}\,U]_n \le 2^n [\mathrm{nd}\,M]_n$, $[\mathrm{nd}\,BU]_n \le 2^n [\mathrm{nd}\,BM]_n$,
$[U]_n \le 2^n [M]_n$ and $[BU]_n \le 2^n [BM]_n$.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 12 (`jis-2025-25.3.4-prop-12`). -/
public theorem_wanted boolFunClassCount_varPerm_unate_le (n : ℕ) :
    boolFunClassCount (n := n) IsBoolFunVarPermEquiv
        (fun f => IsNondegenerateBoolFun f ∧ IsUnateBoolFun f)
      ≤ 2 ^ n * boolFunClassCount (n := n) IsBoolFunVarPermEquiv
        (fun f => IsNondegenerateBoolFun f ∧ Monotone f) ∧
    boolFunClassCount (n := n) IsBoolFunVarPermEquiv
        (fun f => IsNondegenerateBoolFun f ∧ IsUnateBoolFun f ∧ 2 * boolFunWeight f = 2 ^ n)
      ≤ 2 ^ n * boolFunClassCount (n := n) IsBoolFunVarPermEquiv
        (fun f => IsNondegenerateBoolFun f ∧ Monotone f ∧ 2 * boolFunWeight f = 2 ^ n) ∧
    boolFunClassCount (n := n) IsBoolFunVarPermEquiv IsUnateBoolFun
      ≤ 2 ^ n * boolFunClassCount (n := n) IsBoolFunVarPermEquiv Monotone ∧
    boolFunClassCount (n := n) IsBoolFunVarPermEquiv
        (fun f => IsUnateBoolFun f ∧ 2 * boolFunWeight f = 2 ^ n)
      ≤ 2 ^ n * boolFunClassCount (n := n) IsBoolFunVarPermEquiv
        (fun f => Monotone f ∧ 2 * boolFunWeight f = 2 ^ n)

/-- **NN-equivalence of monotone Boolean functions.** Let $f$ and $g$ be monotone $n$-variable
Boolean functions. Then $f$ and $g$ are NN-equivalent ($g$ is obtained from $f$ by negating
some inputs and possibly the output) if and only if either $g = f$, or $g(x) = \lnot f(x \oplus a)$
for all $x$, where $a \in \{0,1\}^n$ has $a_i = 1$ exactly for the variables $x_i$ on which $f$
is non-degenerate and $\oplus$ is coordinatewise exclusive or.

This does not mean that every NN-class of monotone functions has two elements: for $n = 1$
and $f(x) = x_1$, the only monotone function NN-equivalent to $f$ is $f$ itself.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 13 (`jis-2025-25.3.4-prop-13`). -/
public theorem_wanted isBoolFunNNEquiv_monotone_iff {n : ℕ}
    {f g : (Fin n → Bool) → Bool} (hf : Monotone f) (hg : Monotone g) :
    IsBoolFunNNEquiv f g ↔
      g = f ∨ ∃ a : Fin n → Bool, (∀ i, a i = true ↔ IsBoolFunNondegenerateOn f i) ∧
        ∀ x : Fin n → Bool, g x = !f fun i => xor (x i) (a i)

/-- **Unate and monotone functions have equally many NN- and NPN-classes.** For every $n$, the
number of NN-inequivalent unate $n$-variable Boolean functions equals the number of
NN-inequivalent monotone ones, and the number of NPN-inequivalent unate $n$-variable Boolean
functions equals the number of NPN-inequivalent monotone ones. Here monotone means nondecreasing
for the coordinatewise order with $0 < 1$.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 14(a) (`jis-2025-25.3.4-prop-14`). -/
public theorem_wanted boolFunClassCount_unate_eq_monotone (n : ℕ) :
    boolFunClassCount (n := n) IsBoolFunNNEquiv IsUnateBoolFun
        = boolFunClassCount (n := n) IsBoolFunNNEquiv Monotone ∧
      boolFunClassCount (n := n) IsBoolFunNPNEquiv IsUnateBoolFun
        = boolFunClassCount (n := n) IsBoolFunNPNEquiv Monotone

/-- **Balanced unate and balanced monotone functions have equally many NN- and NPN-classes.**
For every $n$, call an $n$-variable Boolean function $f$ balanced when $2\,\mathrm{wt}(f) = 2^n$,
where $\mathrm{wt}(f)$ is the weight of $f$. The number of NN-inequivalent balanced unate
$n$-variable Boolean functions equals the number of NN-inequivalent balanced monotone ones, and
the number of NPN-inequivalent balanced unate $n$-variable Boolean functions equals the number of
NPN-inequivalent balanced monotone ones. Here monotone means nondecreasing for the coordinatewise
order with $0 < 1$.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 14(b) (`jis-2025-25.3.4-prop-14`). -/
public theorem_wanted boolFunClassCount_balanced_unate_eq_monotone (n : ℕ) :
    boolFunClassCount (n := n) IsBoolFunNNEquiv
        (fun f => IsUnateBoolFun f ∧ 2 * boolFunWeight f = 2 ^ n)
        = boolFunClassCount (n := n) IsBoolFunNNEquiv
          (fun f => Monotone f ∧ 2 * boolFunWeight f = 2 ^ n) ∧
      boolFunClassCount (n := n) IsBoolFunNPNEquiv
        (fun f => IsUnateBoolFun f ∧ 2 * boolFunWeight f = 2 ^ n)
        = boolFunClassCount (n := n) IsBoolFunNPNEquiv
          (fun f => Monotone f ∧ 2 * boolFunWeight f = 2 ^ n)

end

end MetaMathlibExt
