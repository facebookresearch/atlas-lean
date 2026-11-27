/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Bool
import Mathlib.Logic.Equiv.Fin.Basic
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

/-- **Unateness of a concatenation.** Let $g$ and $h$ be $n$-variable Boolean functions and let
$g \| h$ be their concatenation, the $(n+1)$-variable function equal to $g$ of the remaining
variables when the first variable is $0$ and to $h$ of them when it is $1$. Then $g \| h$ is
unate if and only if $g$ and $h$ are unate, for each variable $x_i$ either both $g$ and $h$
are monotone increasing in $x_i$ or both are monotone decreasing in $x_i$, and $g \le h$
pointwise or $h \le g$ pointwise.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 6 (`jis-2025-25.3.4-prop-6`). -/
public theorem isUnateBoolFun_boolFunConcat_iff {n : ℕ}
    (g h : (Fin n → Bool) → Bool) :
    IsUnateBoolFun (boolFunConcat g h) ↔
      IsUnateBoolFun g ∧ IsUnateBoolFun h ∧
        (∀ i : Fin n, (IsBoolFunIncreasingIn g i ∧ IsBoolFunIncreasingIn h i) ∨
          (IsBoolFunDecreasingIn g i ∧ IsBoolFunDecreasingIn h i)) ∧
        (g ≤ h ∨ h ≤ g) := by
  -- Split the coordinates at zero, then write each input as a head bit and a tail.
  rw [IsUnateBoolFun, Fin.forall_fin_succ]
  simp only [IsBoolFunIncreasingIn, IsBoolFunDecreasingIn, Fin.forall_fin_succ_pi, Bool.forall_bool,
    Fin.cons_zero, Fin.cons_succ, Fin.update_cons_zero, ← Fin.cons_update, boolFunConcat_cons,
    Bool.cond_false, Bool.cond_true, Bool.true_eq_false, false_implies, forall_const, and_true]
  constructor
  · rintro ⟨horder, hdirs⟩
    exact ⟨fun i => (hdirs i).imp And.left And.left, fun i => (hdirs i).imp And.right And.right,
      hdirs, horder⟩
  · rintro ⟨_, _, hdirs, horder⟩
    exact ⟨horder, hdirs⟩

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

namespace isBoolFunNNEquiv_monotone_iff

open Function

/-- Agreement on the non-degenerate coordinates suffices to give the same output. -/
private theorem dependsOn_nondegenerate {n : ℕ} (f : (Fin n → Bool) → Bool) :
    DependsOn f {i | IsBoolFunNondegenerateOn f i} := by
  intro x y hagree
  suffices ∀ s : Finset (Fin n), f (s.piecewise x y) = f y by simpa using this .univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.piecewise_insert, ← ih]
    rcases Bool.eq_or_eq_not (x i) (s.piecewise x y i) with he | he
    · rw [he, update_eq_self]
    · by_contra hdiff
      have hnd : IsBoolFunNondegenerateOn f i := ⟨_, by rwa [← he, ne_comm]⟩
      have heq : x i = s.piecewise x y i := by simpa [hi] using hagree i hnd
      exact Bool.eq_not_iff.mp he heq

/-- On a non-degenerate coordinate, the input and output negation bits must agree. -/
private theorem mask_eq_output {n : ℕ} {f g : (Fin n → Bool) → Bool}
    (hf : Monotone f) (hg : Monotone g) {a : Fin n → Bool} {c : Bool}
    (h : ∀ x, g x = xor (f fun j => xor (x j) (a j)) c)
    (i : Fin n) (hi : IsBoolFunNondegenerateOn f i) : a i = c := by
  obtain ⟨x, hx⟩ := hi
  have hne : f (update x i false) ≠ f (update x i true) := by
    intro he
    apply hx
    calc
      f x = f (update x i (x i)) := by rw [update_eq_self]
      _ = f (update x i (!x i)) := by
        cases x i
        · exact he
        · exact he.symm
  -- The masked endpoints of this edge of the cube are also endpoints of an edge for g.
  let y (j : Fin n) := xor (x j) (a j)
  have edge (b : Bool) : g (update y i b) = xor (f (update x i (xor b (a i)))) c := by
    rw [h]
    congr 2
    funext j
    rcases eq_or_ne j i with rfl | hji
    · simp
    · simp [hji, y]
  have h₁ : f (update x i false) ≤ f (update x i true) := hf (update_le_update_iff'.2 (by decide))
  have h₂ : g (update y i false) ≤ g (update y i true) := hg (update_le_update_iff'.2 (by decide))
  rw [edge, edge] at h₂
  obtain ⟨hfalse, htrue⟩ := Bool.lt_iff.mp (lt_of_le_of_ne h₁ hne)
  cases ha : a i <;> cases c <;> simp [ha, hfalse, htrue, Bool.le_iff_imp] at h₂ ⊢

end isBoolFunNNEquiv_monotone_iff

open isBoolFunNNEquiv_monotone_iff in
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
public theorem isBoolFunNNEquiv_monotone_iff {n : ℕ}
    {f g : (Fin n → Bool) → Bool} (hf : Monotone f) (hg : Monotone g) :
    IsBoolFunNNEquiv f g ↔
      g = f ∨ ∃ a : Fin n → Bool, (∀ i, a i = true ↔ IsBoolFunNondegenerateOn f i) ∧
        ∀ x : Fin n → Bool, g x = !f fun i => xor (x i) (a i) := by
  classical
  constructor
  · rintro ⟨a, c, h⟩
    have ha := mask_eq_output hf hg h
    cases c
    · left
      funext x
      rw [h, Bool.xor_false]
      exact dependsOn_nondegenerate f fun i hi => by simp [ha i hi]
    · right
      refine ⟨fun i => decide (IsBoolFunNondegenerateOn f i), by simp, fun x => ?_⟩
      rw [h, Bool.xor_true]
      apply congrArg Bool.not
      exact dependsOn_nondegenerate f fun i hi => by
        change IsBoolFunNondegenerateOn f i at hi
        simp [hi, ha i hi]
  · rintro (rfl | ⟨a, _, h⟩)
    · exact isBoolFunNNEquiv_refl _
    · exact ⟨a, true, fun x => by simpa using h x⟩

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

namespace boolFunClassCount_varPerm_nondegenerate_eq_sub

open Function

/-- The classes counted by `boolFunClassCount`, as a set of sets. -/
private theorem classCount_eq_ncard {n : ℕ}
    (R : ((Fin n → Bool) → Bool) → ((Fin n → Bool) → Bool) → Prop)
    (P : ((Fin n → Bool) → Bool) → Prop) :
    boolFunClassCount R P = {S | ∃ f, P f ∧ S = {g | P g ∧ R f g}}.ncard :=
  Nat.card_coe_set_eq {S | ∃ f, P f ∧ S = {g | P g ∧ R f g}}

/-- A class only sees the property on the functions related to its representative. -/
private theorem setOf_and_congr {α : Type*} {R : α → α → Prop} {B B' : α → Prop} {f : α}
    (h : ∀ g, R f g → (B g ↔ B' g)) : {g | B g ∧ R f g} = {g | B' g ∧ R f g} :=
  Set.ext fun g => ⟨fun hg => ⟨(h g hg.2).1 hg.1, hg.2⟩, fun hg => ⟨(h g hg.2).2 hg.1, hg.2⟩⟩

/-- Splitting a property along an invariant property `A` adds up the class counts. -/
private theorem classCount_split {n : ℕ}
    {R : ((Fin n → Bool) → Bool) → ((Fin n → Bool) → Bool) → Prop} (hR : ∀ f, R f f)
    {A : ((Fin n → Bool) → Bool) → Prop} (hA : ∀ f g, R f g → (A f ↔ A g))
    (Q : ((Fin n → Bool) → Bool) → Prop) :
    boolFunClassCount R Q =
      boolFunClassCount R (fun f => A f ∧ Q f) + boolFunClassCount R (fun f => ¬ A f ∧ Q f) := by
  simp only [classCount_eq_ncard]
  rw [← Set.ncard_union_eq]
  · congr 1
    ext S
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · rintro ⟨f, hf, rfl⟩
      by_cases hAf : A f
      · refine Or.inl ⟨f, ⟨hAf, hf⟩, setOf_and_congr fun g hg => ?_⟩
        exact ⟨fun hQ => ⟨(hA f g hg).1 hAf, hQ⟩, And.right⟩
      · refine Or.inr ⟨f, ⟨hAf, hf⟩, setOf_and_congr fun g hg => ?_⟩
        exact ⟨fun hQ => ⟨fun hAg => hAf ((hA f g hg).2 hAg), hQ⟩, And.right⟩
    · rintro (⟨f, ⟨hAf, hf⟩, rfl⟩ | ⟨f, ⟨hAf, hf⟩, rfl⟩)
      · refine ⟨f, hf, setOf_and_congr fun g hg => ?_⟩
        exact ⟨And.right, fun hQ => ⟨(hA f g hg).1 hAf, hQ⟩⟩
      · refine ⟨f, hf, setOf_and_congr fun g hg => ?_⟩
        exact ⟨And.right, fun hQ => ⟨fun hAg => hAf ((hA f g hg).2 hAg), hQ⟩⟩
  · rw [Set.disjoint_left]
    rintro S ⟨f, ⟨hAf, hf⟩, rfl⟩ ⟨_, -, heq⟩
    have hmem : f ∈ {g | (A g ∧ Q g) ∧ R f g} := ⟨⟨hAf, hf⟩, hR f⟩
    rw [heq] at hmem
    exact hmem.1.1 hAf

/-- Class counts agree along a map `φ` that reflects the relations and the properties and
meets every class. -/
private theorem classCount_eq_of_map {m k : ℕ}
    {R : ((Fin m → Bool) → Bool) → ((Fin m → Bool) → Bool) → Prop}
    {R' : ((Fin k → Bool) → Bool) → ((Fin k → Bool) → Bool) → Prop}
    (hR : Equivalence R) (hR' : Equivalence R')
    {P : ((Fin m → Bool) → Bool) → Prop} {Q : ((Fin k → Bool) → Bool) → Prop}
    (φ : ((Fin m → Bool) → Bool) → (Fin k → Bool) → Bool)
    (hQP : ∀ g, Q (φ g) ↔ P g) (hRφ : ∀ g₁ g₂, R' (φ g₁) (φ g₂) ↔ R g₁ g₂)
    (hQ : ∀ f f', R' f f' → Q f → Q f') (hφ : ∀ f, Q f → ∃ g, R' f (φ g)) :
    boolFunClassCount R' Q = boolFunClassCount R P := by
  simp only [classCount_eq_ncard]
  -- The class of `g` is sent to the class of `φ g`.
  have himage {g₀ : (Fin m → Bool) → Bool} (hg₀ : P g₀) :
      {f | Q f ∧ ∃ g ∈ {g | P g ∧ R g₀ g}, R' (φ g) f} = {f | Q f ∧ R' (φ g₀) f} := by
    ext f
    simp only [Set.mem_ofPred_eq]
    refine and_congr_right fun _ => ⟨?_, fun hf => ⟨g₀, ⟨hg₀, hR.refl g₀⟩, hf⟩⟩
    rintro ⟨g, ⟨-, hg⟩, hf⟩
    exact hR'.trans ((hRφ g₀ g).2 hg) hf
  -- Related representatives have the same class.
  have hclass {α : Type} {S : α → α → Prop} (hS : Equivalence S) {B : α → Prop} {a b : α}
      (hab : S a b) : {c | B c ∧ S a c} = {c | B c ∧ S b c} :=
    Set.ext fun c => and_congr_right fun _ => ⟨hS.trans (hS.symm hab), hS.trans hab⟩
  symm
  refine Set.ncard_congr (fun S _ => {f | Q f ∧ ∃ g ∈ S, R' (φ g) f}) ?_ ?_ ?_
  · rintro S ⟨g₀, hg₀, rfl⟩
    exact ⟨φ g₀, (hQP g₀).2 hg₀, himage hg₀⟩
  · rintro S T ⟨g₁, hg₁, rfl⟩ ⟨g₂, hg₂, rfl⟩ heq
    simp only [himage hg₁, himage hg₂] at heq
    have hmem : φ g₂ ∈ {f | Q f ∧ R' (φ g₂) f} := ⟨(hQP g₂).2 hg₂, hR'.refl _⟩
    rw [← heq] at hmem
    exact hclass hR ((hRφ g₁ g₂).1 hmem.2)
  · rintro T ⟨f₀, hf₀, rfl⟩
    obtain ⟨g, hg⟩ := hφ f₀ hf₀
    have hPg : P g := (hQP g).1 (hQ f₀ (φ g) hg hf₀)
    exact ⟨_, ⟨g, hPg, rfl⟩, (himage hPg).trans (hclass hR' (hR'.symm hg))⟩

/-- Permutation equivalence is an equivalence relation. -/
private theorem equivalence_isBoolFunVarPermEquiv (n : ℕ) :
    Equivalence (IsBoolFunVarPermEquiv (n := n)) where
  refl := isBoolFunVarPermEquiv_refl
  symm := by
    rintro f g ⟨σ, hσ⟩
    refine ⟨σ⁻¹, fun x => ?_⟩
    rw [hσ]
    congr 1
    funext i
    simp
  trans := by
    rintro f g k ⟨σ, hσ⟩ ⟨τ, hτ⟩
    exact ⟨τ * σ, fun x => by rw [hτ, hσ]; rfl⟩

/-- Permuting the variables preserves non-degeneracy. -/
private theorem isNondegenerateBoolFun_of_isBoolFunVarPermEquiv {n : ℕ}
    {f g : (Fin n → Bool) → Bool} (h : IsBoolFunVarPermEquiv f g)
    (hf : IsNondegenerateBoolFun f) : IsNondegenerateBoolFun g := by
  obtain ⟨σ, hσ⟩ := h
  intro i
  obtain ⟨z, hz⟩ := hf (σ.symm i)
  refine ⟨z ∘ σ.symm, ?_⟩
  rw [hσ, hσ, update_comp_equiv]
  simpa [comp_assoc] using hz

/-- Permuting the variables preserves a property invariant under renaming variables. -/
private theorem iff_of_isBoolFunVarPermEquiv (P : ∀ n : ℕ, ((Fin n → Bool) → Bool) → Prop)
    (hP : ∀ (m n : ℕ) (e : Fin m ↪ Fin n) (g : (Fin m → Bool) → Bool),
      P n (fun x => g (x ∘ e)) ↔ P m g)
    {n : ℕ} {f g : (Fin n → Bool) → Bool} (h : IsBoolFunVarPermEquiv f g) : P n f ↔ P n g := by
  obtain ⟨σ, hσ⟩ := h
  obtain rfl : g = fun x => f (x ∘ σ.toEmbedding) := funext hσ
  exact (hP n n σ.toEmbedding f).symm

/-- A function of the first `n` of `n + 1` variables is degenerate on the last one. -/
private theorem not_isNondegenerateBoolFun_comp_castSucc {n : ℕ}
    (g : (Fin n → Bool) → Bool) :
    ¬ IsNondegenerateBoolFun fun x : Fin (n + 1) → Bool => g (x ∘ Fin.castSuccEmb) := by
  intro h
  obtain ⟨x, hx⟩ := h (Fin.last n)
  apply hx
  dsimp only
  congr 1
  funext i
  simp [Fin.castSucc_ne_last]

/-- Adding a dummy last variable reflects permutation equivalence. -/
private theorem isBoolFunVarPermEquiv_comp_castSucc_iff {n : ℕ}
    (g₁ g₂ : (Fin n → Bool) → Bool) :
    IsBoolFunVarPermEquiv (fun x : Fin (n + 1) → Bool => g₁ (x ∘ Fin.castSuccEmb))
        (fun x => g₂ (x ∘ Fin.castSuccEmb)) ↔ IsBoolFunVarPermEquiv g₁ g₂ := by
  constructor
  · rintro ⟨τ, hτ⟩
    -- Delete the last variable from `τ`: the variable that `τ` sends to the last one is sent
    -- where `τ` sends the last one.
    let e := finSuccEquivLast.permCongr τ
    refine ⟨Equiv.removeNone e, fun y => ?_⟩
    -- Extend `y` by its value at `τ (Fin.last n)`, or by `false` if `τ` fixes the last variable.
    let x : Fin (n + 1) → Bool :=
      Fin.snoc y (Fin.snoc (α := fun _ => Bool) y false (τ (Fin.last n)))
    have hx : x ∘ Fin.castSuccEmb = y := by
      funext i
      simp [x]
    have hxτ : (x ∘ τ) ∘ Fin.castSuccEmb = y ∘ Equiv.removeNone e := by
      funext i
      simp only [comp_apply, Fin.coe_castSuccEmb]
      cases h : finSuccEquivLast (τ (Fin.castSucc i)) with
      | none =>
        have h' := Equiv.removeNone_none (e := e) (x := i) (by simpa [e] using h)
        have hlast : τ (Fin.castSucc i) = Fin.last n := by
          simpa using congrArg finSuccEquivLast.symm h
        simp only [e, Equiv.permCongr_apply, finSuccEquivLast_symm_none] at h'
        have hτlast : τ (Fin.last n) = Fin.castSucc (Equiv.removeNone e i) := by
          simpa using congrArg finSuccEquivLast.symm h'.symm
        rw [hlast]
        simp [x, hτlast]
      | some j =>
        have h' := Equiv.removeNone_some (e := e) (x := i) ⟨j, by simpa [e] using h⟩
        have hj : τ (Fin.castSucc i) = Fin.castSucc j := by
          simpa using congrArg finSuccEquivLast.symm h
        rw [show e (some i) = some j by simpa [e] using h, Option.some_inj] at h'
        rw [hj, h']
        simp [x]
    have := hτ x
    simp only at this
    rwa [hx, hxτ] at this
  · rintro ⟨σ, hσ⟩
    refine ⟨finSuccEquivLast.symm.permCongr (Equiv.optionCongr σ), fun x => ?_⟩
    simp only
    rw [hσ]
    congr 1
    funext i
    simp [Equiv.permCongr_apply]

/-- A degenerate function is a permutation of one that ignores its last variable. -/
private theorem exists_isBoolFunVarPermEquiv_comp_castSucc {n : ℕ}
    {f : (Fin (n + 1) → Bool) → Bool} (hf : ¬ IsNondegenerateBoolFun f) :
    ∃ g : (Fin n → Bool) → Bool,
      IsBoolFunVarPermEquiv f fun x => g (x ∘ Fin.castSuccEmb) := by
  obtain ⟨i, hi⟩ := not_forall.mp hf
  simp only [IsBoolFunNondegenerateOn, not_exists, not_not] at hi
  have hconst (x : Fin (n + 1) → Bool) (b : Bool) : f (update x i b) = f x := by
    rcases Bool.eq_or_eq_not b (x i) with rfl | rfl
    · rw [update_eq_self]
    · exact (hi x).symm
  -- Swap the ignored variable with the last one.
  let τ := Equiv.swap i (Fin.last n)
  refine ⟨fun y => f (Fin.snoc (α := fun _ => Bool) y false ∘ τ), τ, fun x => ?_⟩
  have hsnoc : (Fin.snoc (α := fun _ => Bool) (x ∘ Fin.castSuccEmb) false) =
      update x (Fin.last n) false := by
    funext j
    induction j using Fin.lastCases with
    | last => simp
    | cast j => simp [Fin.castSucc_ne_last]
  simp only
  rw [hsnoc, update_comp_equiv]
  simp [τ, hconst]

/-- The classes in arity `n + 1` split into the old classes and the new non-degenerate ones. -/
private theorem boolFunClassCount_varPerm_succ
    (P : ∀ n : ℕ, ((Fin n → Bool) → Bool) → Prop)
    (hP : ∀ (m n : ℕ) (e : Fin m ↪ Fin n) (g : (Fin m → Bool) → Bool),
      P n (fun x => g (x ∘ e)) ↔ P m g)
    (n : ℕ) :
    boolFunClassCount IsBoolFunVarPermEquiv (P (n + 1))
      = boolFunClassCount IsBoolFunVarPermEquiv (P n)
        + boolFunClassCount IsBoolFunVarPermEquiv
          (fun f => IsNondegenerateBoolFun f ∧ P (n + 1) f) := by
  have hR := equivalence_isBoolFunVarPermEquiv
  -- Non-degeneracy splits the classes of `P (n + 1)` ...
  have hsplit := classCount_split (hR (n + 1)).refl
    (fun f g h => ⟨isNondegenerateBoolFun_of_isBoolFunVarPermEquiv h,
      isNondegenerateBoolFun_of_isBoolFunVarPermEquiv ((hR (n + 1)).symm h)⟩) (P (n + 1))
  -- ... and the degenerate classes are those of `P n`, with a dummy last variable added.
  have hdeg : boolFunClassCount IsBoolFunVarPermEquiv
      (fun f => ¬ IsNondegenerateBoolFun f ∧ P (n + 1) f) =
        boolFunClassCount IsBoolFunVarPermEquiv (P n) := by
    refine classCount_eq_of_map (hR n) (hR (n + 1)) (fun g x => g (x ∘ Fin.castSuccEmb))
      (fun g => ?_) isBoolFunVarPermEquiv_comp_castSucc_iff (fun f f' h hf => ?_)
      (fun f hf => exists_isBoolFunVarPermEquiv_comp_castSucc hf.1)
    · exact ⟨fun h => (hP n (n + 1) Fin.castSuccEmb g).1 h.2,
        fun h => ⟨not_isNondegenerateBoolFun_comp_castSucc g,
          (hP n (n + 1) Fin.castSuccEmb g).2 h⟩⟩
    · exact ⟨fun hnd => hf.1 (isNondegenerateBoolFun_of_isBoolFunVarPermEquiv
        ((hR (n + 1)).symm h) hnd), (iff_of_isBoolFunVarPermEquiv P hP h).1 hf.2⟩
  rw [hdeg] at hsplit
  exact hsplit.trans (Nat.add_comm _ _)

end boolFunClassCount_varPerm_nondegenerate_eq_sub

open boolFunClassCount_varPerm_nondegenerate_eq_sub in
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
public theorem boolFunClassCount_varPerm_nondegenerate_eq_sub
    (P : ∀ n : ℕ, ((Fin n → Bool) → Bool) → Prop)
    (hP : ∀ (m n : ℕ) (e : Fin m ↪ Fin n) (g : (Fin m → Bool) → Bool),
      P n (fun x => g (x ∘ e)) ↔ P m g)
    (n : ℕ) :
    boolFunClassCount IsBoolFunVarPermEquiv (fun f => IsNondegenerateBoolFun f ∧ P (n + 1) f)
      = boolFunClassCount IsBoolFunVarPermEquiv (P (n + 1))
        - boolFunClassCount IsBoolFunVarPermEquiv (P n) := by
  rw [boolFunClassCount_varPerm_succ P hP n, Nat.add_sub_cancel_left]

open boolFunClassCount_varPerm_nondegenerate_eq_sub in
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
public theorem boolFunClassCount_varPerm_eq_sum_nondegenerate
    (P : ∀ n : ℕ, ((Fin n → Bool) → Bool) → Prop)
    (hP : ∀ (m n : ℕ) (e : Fin m ↪ Fin n) (g : (Fin m → Bool) → Bool),
      P n (fun x => g (x ∘ e)) ↔ P m g)
    (n : ℕ) :
    boolFunClassCount IsBoolFunVarPermEquiv (P n)
      = ∑ i ∈ Finset.range (n + 1),
          boolFunClassCount IsBoolFunVarPermEquiv (fun f => IsNondegenerateBoolFun f ∧ P i f) := by
  induction n with
  | zero =>
    have hzero : (fun f : (Fin 0 → Bool) → Bool => IsNondegenerateBoolFun f ∧ P 0 f) = P 0 :=
      funext fun _ => propext ⟨And.right, fun hf => ⟨fun i => Fin.elim0 i, hf⟩⟩
    rw [Finset.sum_range_one, hzero]
  | succ n ih =>
    rw [Finset.sum_range_succ, boolFunClassCount_varPerm_succ P hP n, ih]

namespace boolFunClassCount_varPerm_unate_le

open Function boolFunClassCount_varPerm_nondegenerate_eq_sub

variable {n : ℕ}

private def flip (a x : Fin n → Bool) (i : Fin n) : Bool := xor (x i) (a i)

private theorem flip_flip (a : Fin n → Bool) : Involutive (flip a) := by
  intro x
  funext i
  simp [flip]

private theorem flip_update (a x : Fin n → Bool) (i : Fin n) (b : Bool) :
    flip a (update x i b) = update (flip a x) i (xor b (a i)) := by
  funext j
  by_cases h : j = i <;> simp [flip, h]

/-- Flipping the coordinates that are not increasing makes every edge increasing. -/
private theorem exists_monotone_flip {f : (Fin n → Bool) → Bool} (hf : IsUnateBoolFun f) :
    ∃ a : Fin n → Bool, Monotone (f ∘ flip a) := by
  classical
  let a (i : Fin n) := decide (¬ IsBoolFunIncreasingIn f i)
  refine ⟨a, monotone_of_le_update fun x i hx => ?_⟩
  simp only [comp_apply, flip_update]
  by_cases hi : IsBoolFunIncreasingIn f i
  · simpa [a, hi] using hi (flip a x) (by simp [flip, a, hi, hx])
  · have hy : flip a x i = true := by simp [flip, a, hi, hx]
    have he : update (flip a x) i true = flip a x := by rw [← hy, update_eq_self]
    have hedge := ((hf i).resolve_left hi) (update (flip a x) i false) (by simp)
    rw [update_idem, he] at hedge
    simpa [a, hi] using hedge

private theorem nondegenerate_flip {f : (Fin n → Bool) → Bool} (hf : IsNondegenerateBoolFun f)
    (a : Fin n → Bool) : IsNondegenerateBoolFun (f ∘ flip a) := by
  intro i
  obtain ⟨x, hx⟩ := hf i
  refine ⟨flip a x, ?_⟩
  simp only [comp_apply, flip_update, flip_flip a x]
  simpa [flip] using hx

private theorem weight_flip (f : (Fin n → Bool) → Bool) (a : Fin n → Bool) :
    boolFunWeight (f ∘ flip a) = boolFunWeight f := by
  apply Finset.card_equiv ((flip_flip a).toPerm _)
  intro x
  simp [Involutive.coe_toPerm]

/-- If each function with property `P` can be flipped to one with property `Q`, the flips of
one representative of each `Q`-class cover all the `P`-classes. -/
private theorem classCount_le_of_flip (P Q : ((Fin n → Bool) → Bool) → Prop)
    (h : ∀ f, P f → ∃ a, Q (f ∘ flip a)) :
    boolFunClassCount IsBoolFunVarPermEquiv P ≤
      2 ^ n * boolFunClassCount IsBoolFunVarPermEquiv Q := by
  classical
  let cls (B : ((Fin n → Bool) → Bool) → Prop) f := {g | B g ∧ IsBoolFunVarPermEquiv f g}
  let classes (B : ((Fin n → Bool) → Bool) → Prop) := {S | ∃ f, B f ∧ S = cls B f}
  let rep := invFun (cls Q)
  let cover a S := cls P (rep S ∘ flip a)
  have hcover : classes P ⊆ Set.image2 cover Set.univ (classes Q) := by
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, hg⟩ := h f hf
    let g := f ∘ flip a
    -- Express g as a permutation of the chosen representative, and permute its mask with it.
    have hmem : g ∈ cls Q (rep (cls Q g)) := by
      rw [show cls Q (rep (cls Q g)) = cls Q g from apply_invFun_apply]
      exact ⟨hg, isBoolFunVarPermEquiv_refl g⟩
    obtain ⟨σ, hσ⟩ := hmem.2
    refine ⟨a ∘ σ, Set.mem_univ _, cls Q g, ⟨g, hg, rfl⟩, ?_⟩
    have hrel : IsBoolFunVarPermEquiv (rep (cls Q g) ∘ flip (a ∘ σ)) f := by
      refine ⟨σ, fun x => ?_⟩
      calc
        f x = g (flip a x) := congrArg f (flip_flip a x).symm
        _ = _ := hσ (flip a x)
    have hR := equivalence_isBoolFunVarPermEquiv n
    exact Set.ext fun k => and_congr_right fun _ => ⟨hR.trans (hR.symm hrel), hR.trans hrel⟩
  rw [classCount_eq_ncard, classCount_eq_ncard]
  calc
    (classes P).ncard ≤ (Set.image2 cover Set.univ (classes Q)).ncard := Set.ncard_le_ncard hcover
    _ ≤ (Set.univ : Set (Fin n → Bool)).ncard * (classes Q).ncard :=
      Set.ncard_image2_le Set.finite_univ (Set.toFinite _)
    _ = 2 ^ n * (classes Q).ncard := by simp [Nat.card_eq_fintype_card]

end boolFunClassCount_varPerm_unate_le

open boolFunClassCount_varPerm_unate_le in
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
public theorem boolFunClassCount_varPerm_unate_le (n : ℕ) :
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
        (fun f => Monotone f ∧ 2 * boolFunWeight f = 2 ^ n) := by
  refine ⟨classCount_le_of_flip _ _ ?_, classCount_le_of_flip _ _ ?_,
    classCount_le_of_flip _ _ ?_, classCount_le_of_flip _ _ ?_⟩
  · rintro f ⟨hnd, hu⟩
    obtain ⟨a, hm⟩ := exists_monotone_flip hu
    exact ⟨a, nondegenerate_flip hnd a, hm⟩
  · rintro f ⟨hnd, hu, hb⟩
    obtain ⟨a, hm⟩ := exists_monotone_flip hu
    exact ⟨a, nondegenerate_flip hnd a, hm, by rwa [weight_flip]⟩
  · exact fun _ => exists_monotone_flip
  · rintro f ⟨hu, hb⟩
    obtain ⟨a, hm⟩ := exists_monotone_flip hu
    exact ⟨a, hm, by rwa [weight_flip]⟩

namespace card_unate_boolFun_relations

open Function
open boolFunClassCount_varPerm_unate_le (flip_update exists_monotone_flip)
open boolFunClassCount_varPerm_unate_le renaming
  flip → flipInputs, flip_flip → flipInputs_involutive

variable {n : ℕ}

private theorem unate_flip_of_monotone {g : (Fin n → Bool) → Bool} (hg : Monotone g)
    (a : Fin n → Bool) : IsUnateBoolFun (g ∘ flipInputs a) := by
  intro i
  cases ha : a i
  · left
    intro x hx
    have hy : flipInputs a x i = false := by simp [flipInputs, ha, hx]
    simp only [comp_apply, flip_update, ha, Bool.xor_false]
    apply hg
    calc
      flipInputs a x = update (flipInputs a x) i false := by rw [← hy, update_eq_self]
      _ ≤ update (flipInputs a x) i true := update_le_update_iff'.2 (Bool.false_le true)
  · right
    intro x hx
    have hy : flipInputs a x i = true := by simp [flipInputs, ha, hx]
    simp only [comp_apply, flip_update, ha, Bool.xor_true, Bool.not_true]
    apply hg
    calc
      update (flipInputs a x) i false ≤ update (flipInputs a x) i true :=
        update_le_update_iff'.2 (Bool.false_le true)
      _ = flipInputs a x := by rw [← hy, update_eq_self]

/-- Input flips of monotone functions cover the unate functions. When every input matters,
the mask and the original monotone function are uniquely determined. -/
private theorem count_flips (P : ((Fin n → Bool) → Bool) → Prop)
    (hP : ∀ f a, P f → P (f ∘ flipInputs a)) :
    let unate := Nat.card {f // IsUnateBoolFun (n := n) f ∧ P f}
    let monotone := 2 ^ n * Nat.card {f // Monotone f ∧ P f}
    unate ≤ monotone ∧ ((∀ f, P f → IsNondegenerateBoolFun f) → unate = monotone) := by
  dsimp only
  let toUnate : (Fin n → Bool) × {f // Monotone f ∧ P f} → {f // IsUnateBoolFun f ∧ P f} :=
    fun ⟨a, g⟩ => ⟨g.val ∘ flipInputs a, unate_flip_of_monotone g.prop.1 a, hP _ a g.prop.2⟩
  have hsurj : Surjective toUnate := by
    intro f
    obtain ⟨a, ha⟩ := exists_monotone_flip f.prop.1
    refine ⟨⟨a, ⟨f.val ∘ flipInputs a, ha, hP _ a f.prop.2⟩⟩, Subtype.ext ?_⟩
    funext x
    exact congrArg f.val (flipInputs_involutive a x)
  have hcard : Nat.card ((Fin n → Bool) × {f // Monotone f ∧ P f}) =
      2 ^ n * Nat.card {f // Monotone f ∧ P f} := by
    simp [Nat.card_prod, Nat.card_eq_fintype_card]
  have hle := Nat.card_le_card_of_surjective toUnate hsurj
  rw [hcard] at hle
  refine ⟨hle, fun hnd => le_antisymm hle ?_⟩
  rw [← hcard]
  refine Nat.card_le_card_of_injective toUnate ?_
  rintro ⟨a, g⟩ ⟨b, h⟩ heq
  have hcomp : g.val ∘ flipInputs a = h.val ∘ flipInputs b := congrArg Subtype.val heq
  -- Equal flipped functions relate the monotone functions by the XOR of the two masks.
  have hmask (x : Fin n → Bool) :
      h.val x = xor (g.val (fun i => xor (x i) (xor (b i) (a i)))) false := by
    rw [Bool.xor_false]
    calc
      h.val x = h.val (flipInputs b (flipInputs b x)) :=
        congrArg h.val (flipInputs_involutive b x).symm
      _ = g.val (flipInputs a (flipInputs b x)) := (congrFun hcomp (flipInputs b x)).symm
      _ = _ := congrArg g.val (funext fun i => Bool.xor_assoc (x i) (b i) (a i))
  have hab : a = b := by
    funext i
    have hi := isBoolFunNNEquiv_monotone_iff.mask_eq_output
      g.prop.1 h.prop.1 hmask i (hnd _ g.prop.2 i)
    exact Bool.xor_right_inj.mp (hi.trans (Bool.xor_self (b i)).symm)
  subst b
  exact congrArg (Prod.mk a)
    (Subtype.ext ((flipInputs_involutive a).surjective.injective_comp_right hcomp))

end card_unate_boolFun_relations

open card_unate_boolFun_relations in
open boolFunClassCount_varPerm_unate_le (nondegenerate_flip weight_flip) in
open boolFunClassCount_varPerm_unate_le renaming flip → flipInputs in
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
public theorem card_unate_boolFun_relations (n : ℕ) :
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
            Monotone f ∧ 2 * boolFunWeight f = 2 ^ n} := by
  let balanced (f : (Fin n → Bool) → Bool) : Prop := 2 * boolFunWeight f = 2 ^ n
  have hbalanced (f : (Fin n → Bool) → Bool) (a : Fin n → Bool) (hf : balanced f) :
      balanced (f ∘ flipInputs a) := by simpa only [balanced, weight_flip] using hf
  refine ⟨?_, ?_, ?_, (count_flips balanced hbalanced).1⟩
  · simpa only [and_comm] using
      (count_flips IsNondegenerateBoolFun (fun _ a h => nondegenerate_flip h a)).2 fun _ h => h
  · simpa only [and_left_comm] using
      (count_flips (fun f => IsNondegenerateBoolFun f ∧ balanced f)
        (fun f a h => ⟨nondegenerate_flip h.1 a, hbalanced f a h.2⟩)).2 fun _ h => h.1
  · simpa only [and_true] using (count_flips (fun _ => True) (fun _ _ h => h)).1

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
