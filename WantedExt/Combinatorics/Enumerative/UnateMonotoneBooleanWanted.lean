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

/-- The weight `wt(f)` of an `n`-variable Boolean function: the size of its
support `{x | f x = true}`.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Section 2. -/
public def boolFunWeight {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  (Finset.univ.filter fun x => f x = true).card

/-- The constant function `1` on `n` variables has weight `2 ^ n`.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Section 2. -/
public theorem boolFunWeight_const_true (n : ℕ) :
    boolFunWeight (fun _ : Fin n → Bool => true) = 2 ^ n := by
  simp [boolFunWeight]

/-- `f` is monotone increasing in the variable `i`: setting `x i` from
`false` to `true` never decreases the value.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Section 2. -/
public def IsBoolFunIncreasingIn {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) :
    Prop :=
  ∀ x : Fin n → Bool, x i = false → f x ≤ f (Function.update x i true)

/-- `f` is monotone decreasing in the variable `i`: setting `x i` from
`false` to `true` never increases the value.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Section 2. -/
public def IsBoolFunDecreasingIn {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) :
    Prop :=
  ∀ x : Fin n → Bool, x i = false → f (Function.update x i true) ≤ f x

/-- A unate Boolean function: monotone increasing or monotone decreasing in
each variable.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Section 1. -/
public def IsUnateBoolFun {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ i : Fin n, IsBoolFunIncreasingIn f i ∨ IsBoolFunDecreasingIn f i

/-- Every monotone Boolean function is unate (increasing in every variable).

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

/-- `f` is non-degenerate on the variable `i`: flipping `x i` changes the
value of `f` at some input `x`.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Section 2. -/
public def IsBoolFunNondegenerateOn {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) :
    Prop :=
  ∃ x : Fin n → Bool, f x ≠ f (Function.update x i (!x i))

/-- A non-degenerate Boolean function: non-degenerate on every variable
(vacuous for `n = 0`, matching the paper's convention that the two
`0`-variable functions are non-degenerate).

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Section 2 and Remark 2. -/
public def IsNondegenerateBoolFun {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ i : Fin n, IsBoolFunNondegenerateOn f i

/-- The projection `x ↦ x i` is non-degenerate on `i`.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Section 2. -/
public theorem isBoolFunNondegenerateOn_proj {n : ℕ} (i : Fin n) :
    IsBoolFunNondegenerateOn (fun x : Fin n → Bool => x i) i :=
  ⟨fun _ => false, by simp⟩

/-- The concatenation `f = g || h` of two `n`-variable functions: the
`(n+1)`-variable function whose truth table is that of `g` followed by that
of `h`, i.e. `f(x₁, …, x_{n+1}) = x̄₁ g(x₂, …) ⊕ x₁ h(x₂, …)`; here `x₁` is
the coordinate `0`.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Section 2, equation (1). -/
public def boolFunConcat {n : ℕ} (g h : (Fin n → Bool) → Bool) :
    (Fin (n + 1) → Bool) → Bool :=
  fun x => cond (x 0) (h (Fin.tail x)) (g (Fin.tail x))

/-- Evaluation of `g || h`: the first variable selects `g` (when `false`) or
`h` (when `true`).

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Section 2, equation (1). -/
public theorem boolFunConcat_cons {n : ℕ} (g h : (Fin n → Bool) → Bool) (b : Bool)
    (x : Fin n → Bool) : boolFunConcat g h (Fin.cons b x) = cond b (h x) (g x) := by
  simp [boolFunConcat]

/-- Equivalence of `n`-variable Boolean functions: `g` is obtained from `f`
by a permutation of the variables.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Section 2.1. -/
public def IsBoolFunVarPermEquiv {n : ℕ} (f g : (Fin n → Bool) → Bool) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), ∀ x : Fin n → Bool, g x = f (x ∘ σ)

/-- Every Boolean function is permutation-equivalent to itself.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Section 2.1. -/
public theorem isBoolFunVarPermEquiv_refl {n : ℕ} (f : (Fin n → Bool) → Bool) :
    IsBoolFunVarPermEquiv f f :=
  ⟨1, fun x => by simp⟩

/-- NN-equivalence: `g` is obtained from `f` by negating a subset of the
inputs (the positions where `a i = true`) and possibly the output (`c`).

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

/-- NPN-equivalence: `g` is obtained from `f` by a permutation of the
variables, negation of a subset of the inputs, and possibly negation of the
output.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 14. -/
public def IsBoolFunNPNEquiv {n : ℕ} (f g : (Fin n → Bool) → Bool) : Prop :=
  ∃ (σ : Equiv.Perm (Fin n)) (a : Fin n → Bool) (c : Bool), ∀ x : Fin n → Bool,
    g x = xor (f fun i => xor (x (σ i)) (a i)) c

/-- Every Boolean function is NPN-equivalent to itself.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 14. -/
public theorem isBoolFunNPNEquiv_refl {n : ℕ} (f : (Fin n → Bool) → Bool) :
    IsBoolFunNPNEquiv f f :=
  ⟨1, fun _ => false, false, fun x => by simp⟩

/-- The number of `R`-inequivalent `n`-variable functions with property `P`:
the number of distinct classes `{g | P g ∧ R f g}` over `f` with `P f`
(for an equivalence relation `R`, the number of equivalence classes of the
set `P`). The paper's `[P]_n` is this count for `IsBoolFunVarPermEquiv`.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Section 2.1. -/
public noncomputable def boolFunClassCount {n : ℕ}
    (R : ((Fin n → Bool) → Bool) → ((Fin n → Bool) → Bool) → Prop)
    (P : ((Fin n → Bool) → Bool) → Prop) : ℕ :=
  Nat.card {S : Set ((Fin n → Bool) → Bool) // ∃ f, P f ∧ S = {g | P g ∧ R f g}}

/-- An empty property has no classes.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Section 2.1. -/
public theorem boolFunClassCount_false {n : ℕ}
    (R : ((Fin n → Bool) → Bool) → ((Fin n → Bool) → Bool) → Prop) :
    boolFunClassCount R (fun _ => False) = 0 := by
  rw [boolFunClassCount, Nat.card_eq_zero]
  left
  exact ⟨fun ⟨_, f, hf, _⟩ => hf⟩

/-- Proposition 1: for a property `P` of Boolean functions,
`P_n = ∑_{i=0}^n binom(n, i) nd-P_i`, where `nd-P_i` counts the non-degenerate
`i`-variable functions with `P`.

Deviation: the paper says "every property"; that is false for properties
that depend on the number of variables (if `P` holds exactly for the four
`1`-variable functions, then `P_1 = 4` but the sum is `0 + 2 = 2`). The
hypothesis `hP` (the paper's counting argument, which identifies a function
with its restriction to the variables it depends on) requires `P` to be
invariant under renaming variables along an injection; balanced, monotone,
unate and their intersections satisfy it.

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

/-- Proposition 1, inverse form: `nd-P_n = ∑_{i=0}^n (-1)^{n-i} binom(n, i) P_i`,
under the same renaming-invariance hypothesis as
`card_boolFun_eq_sum_choose_card_nondegenerate`.

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

/-- Proposition 3: `nd-U_n = 2^n nd-M_n`, `nd-BU_n = 2^n nd-BM_n`,
`U_n ≤ 2^n M_n` and `BU_n ≤ 2^n BM_n`, where `U`, `M` count unate and
monotone functions, `B` adds balancedness (`2 wt(f) = 2^n`) and `nd-`
restricts to non-degenerate functions.

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

/-- Proposition 4 (Bakoev): `g || h` is monotone if and only if `g` and `h`
are monotone and `g ≤ h` pointwise.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 4 (`jis-2025-25.3.4-prop-4`),
quoting Bakoev. -/
public theorem_wanted monotone_boolFunConcat_iff {n : ℕ} (g h : (Fin n → Bool) → Bool) :
    Monotone (boolFunConcat g h) ↔ Monotone g ∧ Monotone h ∧ g ≤ h

/-- Proposition 5 (OEIS A003183): if `f` is monotone then so is
`\overline{f^r}`, i.e. `x ↦ ¬ f(x̄)`, the existing `booleanFunctionDual`.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 5 (`jis-2025-25.3.4-prop-5`). -/
public theorem_wanted monotone_booleanFunctionDual {n : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : Monotone f) : Monotone (booleanFunctionDual n f)

/-- Proposition 6: `g || h` is unate if and only if `g` and `h` are unate,
(a) for each variable both are increasing or both are decreasing, and
(b) `g ≤ h` or `h ≤ g`.

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

/-- Proposition 7: the negation of a unate function is unate.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 7 (`jis-2025-25.3.4-prop-7`). -/
public theorem_wanted isUnateBoolFun_not {n : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : IsUnateBoolFun f) : IsUnateBoolFun fun x => !f x

/-- Proposition 8: `M_{n,w} = M_{n,2^n-w}` for `0 ≤ w ≤ 2^n`, where `M_{n,w}`
counts monotone `n`-variable functions of weight `w`. The paper assumes
`n ≥ 1`; the statement also holds for `n = 0` and is stated for all `n`.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 8 (`jis-2025-25.3.4-prop-8`). -/
public theorem_wanted card_monotone_boolFun_weight_symm (n w : ℕ) (hw : w ≤ 2 ^ n) :
    Nat.card {f : (Fin n → Bool) → Bool // Monotone f ∧ boolFunWeight f = w}
      = Nat.card {f : (Fin n → Bool) → Bool // Monotone f ∧ boolFunWeight f = 2 ^ n - w}

/-- Proposition 9: `U_{n,w} = U_{n,2^n-w}` for `0 ≤ w ≤ 2^n`, where `U_{n,w}`
counts unate `n`-variable functions of weight `w`. The paper assumes
`n ≥ 1`; the statement also holds for `n = 0` and is stated for all `n`.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 9 (`jis-2025-25.3.4-prop-9`). -/
public theorem_wanted card_unate_boolFun_weight_symm (n w : ℕ) (hw : w ≤ 2 ^ n) :
    Nat.card {f : (Fin n → Bool) → Bool // IsUnateBoolFun f ∧ boolFunWeight f = w}
      = Nat.card {f : (Fin n → Bool) → Bool // IsUnateBoolFun f ∧ boolFunWeight f = 2 ^ n - w}

/-- Proposition 11: for a property `P` closed under renaming variables,
`[P]_n = ∑_{i=0}^n nd-[P]_i`, where `[P]_n` is the number of classes of
`n`-variable functions with `P` under permutation of variables and `nd-[P]_i`
the same for non-degenerate functions.

Deviation: the paper assumes only closure under permutations of variables;
the counting argument also needs invariance under adding or removing dummy
variables, so `hP` asks for invariance under renaming along any injection.
Closure under permutations alone is not enough: if `P` holds exactly for the
four `1`-variable functions, then `[P]_1 = 4` but the sum is `0 + 2 = 2`.

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

/-- Proposition 11, difference form: `nd-[P]_{n+1} = [P]_{n+1} - [P]_n` (the
paper's `nd-[P]_n = [P]_n - [P]_{n-1}` for `n ≥ 1`), under the same hypothesis
as `boolFunClassCount_varPerm_eq_sum_nondegenerate`.

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

/-- Proposition 12: with `[·]` counting classes under permutation of
variables, `nd-[U]_n ≤ 2^n nd-[M]_n`, `nd-[BU]_n ≤ 2^n nd-[BM]_n`,
`[U]_n ≤ 2^n [M]_n` and `[BU]_n ≤ 2^n [BM]_n`.

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

/-- Proposition 13: two monotone functions `f`, `g` are NN-equivalent if and
only if `g = f` or `g` is obtained from `f` by negating the output and all
variables on which `f` is non-degenerate (the positions `a i = true`).

Omitted: the printed consequence that every NN-class of monotone functions
has exactly two elements is false for self-dual cases: for `n = 1` and
`f x = x₁`, the only monotone function NN-equivalent to `f` is `f` itself.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 13 (`jis-2025-25.3.4-prop-13`). -/
public theorem_wanted isBoolFunNNEquiv_monotone_iff {n : ℕ}
    {f g : (Fin n → Bool) → Bool} (hf : Monotone f) (hg : Monotone g) :
    IsBoolFunNNEquiv f g ↔
      g = f ∨ ∃ a : Fin n → Bool, (∀ i, a i = true ↔ IsBoolFunNondegenerateOn f i) ∧
        ∀ x : Fin n → Bool, g x = !f fun i => xor (x i) (a i)

/-- Proposition 14(a): the numbers of NN-inequivalent (resp. NPN-inequivalent)
`n`-variable unate and monotone functions are equal.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 14(a) (`jis-2025-25.3.4-prop-14`). -/
public theorem_wanted boolFunClassCount_unate_eq_monotone (n : ℕ) :
    boolFunClassCount (n := n) IsBoolFunNNEquiv IsUnateBoolFun
        = boolFunClassCount (n := n) IsBoolFunNNEquiv Monotone ∧
      boolFunClassCount (n := n) IsBoolFunNPNEquiv IsUnateBoolFun
        = boolFunClassCount (n := n) IsBoolFunNPNEquiv Monotone

/-- Proposition 14(b): the numbers of NN-inequivalent (resp. NPN-inequivalent)
`n`-variable balanced unate and balanced monotone functions are equal.

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
