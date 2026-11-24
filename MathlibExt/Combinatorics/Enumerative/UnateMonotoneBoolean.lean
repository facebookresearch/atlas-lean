/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Bool
import MathlibExt.Combinatorics.Enumerative.SelfDualMonotoneBoolean

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

/-- **The negation of a unate function is unate.** If an $n$-variable Boolean function $f$ is
unate, then so is its negation $x \mapsto \lnot f(x)$.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 7 (`jis-2025-25.3.4-prop-7`). -/
public theorem isUnateBoolFun_not {n : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : IsUnateBoolFun f) : IsUnateBoolFun fun x => !f x := by
  intro i
  rcases hf i with hinc | hdec
  · exact Or.inr fun x hx => compl_le_compl (hinc x hx)
  · exact Or.inl fun x hx => compl_le_compl (hdec x hx)

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

/-- **Monotone concatenations of Boolean functions (Bakoev).** Let $g$ and $h$ be Boolean
functions on $n$ variables, and let $g \parallel h$ be their concatenation, the function on
$n + 1$ variables that equals $g$ of the remaining variables when its first variable is $0$ and
$h$ of them when it is $1$. Then $g \parallel h$ is monotone if and only if $g$ and $h$ are both
monotone and $g(x) \le h(x)$ for every $x \in \{0,1\}^n$.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 4 (`jis-2025-25.3.4-prop-4`),
quoting Bakoev. -/
public theorem monotone_boolFunConcat_iff {n : ℕ} (g h : (Fin n → Bool) → Bool) :
    Monotone (boolFunConcat g h) ↔ Monotone g ∧ Monotone h ∧ g ≤ h := by
  constructor
  · intro hmono
    have compare {a b : Bool} {x y : Fin n → Bool} (hab : a ≤ b) (hxy : x ≤ y) :
        cond a (h x) (g x) ≤ cond b (h y) (g y) := by
      simpa only [boolFunConcat_cons] using
        hmono ((Fin.cons_le_cons (α := fun _ => Bool)).2 ⟨hab, hxy⟩)
    exact ⟨fun _ _ hxy => compare (le_refl false) hxy,
      fun _ _ hxy => compare (le_refl true) hxy,
      fun x => compare (Bool.false_le true) (le_refl x)⟩
  · rintro ⟨hg, hh, hgh⟩ x y hxy
    have htail : Fin.tail x ≤ Fin.tail y := fun i => hxy i.succ
    have hhead := hxy 0
    unfold boolFunConcat
    cases hx : x 0 <;> cases hy : y 0
    · exact hg htail
    · exact (hgh _).trans (hh htail)
    · simp [hx, hy, Bool.le_iff_imp] at hhead
    · exact hh htail

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

/-- **Weight symmetry of monotone Boolean functions.** For all $n \ge 0$ and all $w$ with
$0 \le w \le 2^n$, the number of monotone $n$-variable Boolean functions of weight $w$ equals
the number of monotone $n$-variable Boolean functions of weight $2^n - w$.

The source assumes $n \ge 1$; the case $n = 0$ is included here.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 8 (`jis-2025-25.3.4-prop-8`). -/
public theorem card_monotone_boolFun_weight_symm (n w : ℕ) (hw : w ≤ 2 ^ n) :
    Nat.card {f : (Fin n → Bool) → Bool // Monotone f ∧ boolFunWeight f = w}
      = Nat.card {f : (Fin n → Bool) → Bool // Monotone f ∧ boolFunWeight f = 2 ^ n - w} := by
  have weight (f : (Fin n → Bool) → Bool) : boolFunWeight f = Nat.card {x // f x = true} := by
    simp only [boolFunWeight, Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine Nat.card_congr ((booleanFunctionDual_involutive n).toPerm _ |>.subtypeEquiv fun f => ?_)
  simp only [Function.Involutive.coe_toPerm, monotone_booleanFunctionDual_iff, weight,
    card_true_booleanFunctionDual]
  exact and_congr_right fun _ => (tsub_right_inj (card_true_le_two_pow n f) hw).symm

/-- **Weight symmetry of unate Boolean functions.** For all $n \ge 0$ and all $w$ with
$0 \le w \le 2^n$, the number of unate $n$-variable Boolean functions of weight $w$ equals the
number of unate $n$-variable Boolean functions of weight $2^n - w$.

The source assumes $n \ge 1$; the case $n = 0$ is included here.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 9 (`jis-2025-25.3.4-prop-9`). -/
public theorem card_unate_boolFun_weight_symm (n w : ℕ) (hw : w ≤ 2 ^ n) :
    Nat.card {f : (Fin n → Bool) → Bool // IsUnateBoolFun f ∧ boolFunWeight f = w}
      = Nat.card {f : (Fin n → Bool) → Bool // IsUnateBoolFun f ∧ boolFunWeight f = 2 ^ n - w} := by
  refine Nat.card_congr ((Equiv.piCongrRight fun _ => Equiv.boolNot).subtypeEquiv fun f => ?_)
  apply and_congr
  · change IsUnateBoolFun f ↔ IsUnateBoolFun (fun x => !f x)
    exact ⟨isUnateBoolFun_not, fun h => by simpa using isUnateBoolFun_not h⟩
  · change boolFunWeight f = w ↔ boolFunWeight (fun x => !f x) = 2 ^ n - w
    have hsum : boolFunWeight f + boolFunWeight (fun x => !f x) = 2 ^ n := by
      simpa [boolFunWeight] using
        (Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun x => f x = true))
    omega

end

end MetaMathlibExt
