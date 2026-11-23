/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SetFamily.Intersecting
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.Order.Hom.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Order.BooleanFunction.SelfDual
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.IntervalCases

/-!
# Counting self-dual monotone Boolean functions

Results from Bartłomiej Pawelski and Andrzej Szepietowski, *Counting
Self-Dual Monotone Boolean Functions*, Journal of Integer Sequences 28 (2025),
Article 25.6.5 (definitions read from arXiv `2310.12637` and from the journal
TeX source).

`D_n` is the set of monotone `f : (Fin n → Bool) → Bool` with the pointwise
order, `f*` is `booleanFunctionDual n f`, `x | y` and `x & y` are `⊔` and `⊓`,
`Λ_n` is `{f | IsSelfDualMonotone n f}` with `λ_n = Nat.card Λ_n`, and
`d_n = |D_n|`. For `x ≤ y`, `re(x, y) = |{z ∈ D_n | x ≤ z ≤ y}|`; `ℓ(b)` is the
number of inputs where `b` is `true`. Permutations act by
`f ↦ (x ↦ f (x ∘ π))`; `γ(b)` is the size of the class of `b`. The paper's
sums over the class set `R_n` (classes identified with representatives) are
stated for any system of representatives `reps`. A concatenation of `2^k`
elements of `D_n` is the function on `n + k` variables that reads the last `k`
variables as a binary index `∑ yⱼ 2^j` into the word and applies the selected
element to the first `n` variables (`booleanCubeConcat`).

A family `𝒰` of subsets of `X = {1, …, n}` (here `Fin n`) is linked when any
two members meet (`Set.Intersecting`), and a maximal linked system (mls) is a
maximal linked family (`Maximal Set.Intersecting 𝒰`). `Φ(π, Λ_n)` is the set of
`f ∈ Λ_n` fixed by `π`, that is with `(fun x => f (x ∘ π)) = f`.

## Main results

* `monotoneBooleanFunction_orderIso_curry` (Lemma 1): `D_{n+k} ≃o D_n^(B^k)`.
* `booleanFunctionDual_antitone_sup_inf` (Lemma 2) and
  `booleanFunction_perm_monotone_dual_selfDual` (Lemma 5).
* `maximal_intersecting_mem_iff_compl_notMem` (Lemma 3) and
  `maximal_intersecting_of_isUpperSet_of_mem_iff_compl_notMem` (Lemma 4).
* `card_selfDualMonotone_succ` (Theorem 6), `card_selfDualMonotone_succ_le`
  (Corollary 7), `monotoneBooleanFunction_weight_dual` (Lemma 8) and
  `card_selfDualMonotone_succ_eq_add` (Theorem 9).
* `card_selfDualMonotone_add_two` (Theorem 10) and
  `le_card_selfDualMonotone_add_two` (Corollary 11).
* `selfDualMonotone_add_four_iff_concat` (Theorem 12),
  `card_selfDualMonotone_add_four` (Theorem 13) and
  `selfDualMonotone_add_four_iff_concat_of_dual_le` (Theorem 14).
* `selfDualMonotone_not_fixed_of_even_minimalPeriod` (Lemma 15),
  `selfDualMonotone_eight_not_fixed` (Corollary 16) and
  `exists_selfDualMonotone_fixed_of_odd` (Lemma 17).

## Proof outline

* Lemma 1 composes `finAppendOrderIso` (`Fin.appendEquiv` as an order
  isomorphism) with `OrderIso.arrowCongr` and `OrderHom.curry`.
* The binary index `∑ j, if y j then 2 ^ j else 0` of `y : Fin k → Bool` is
  below `2 ^ k` and its `j`-th bit is `y j` (`testBit_sum_ite_two_pow`,
  `sum_ite_testBit_two_pow`). Switching on coordinate `j` adds `2 ^ j`
  (`sum_ite_two_pow_update`) and complementing `y` sends the index `i` to
  `2 ^ k - 1 - i` (`sum_ite_two_pow_compl`).
* `booleanCubeBlock n k F i` fixes the last `k` variables of `F` to the binary
  digits of `i`. By `isSelfDualMonotone_add_iff`, `F` is self-dual and
  monotone iff its blocks are monotone, increase along the edges `i → i + 2^j`
  of the cube (bit `j` of `i` clear), and satisfy
  `block (2 ^ k - 1 - i) = (block i)*`; monotonicity along the edges suffices
  by `monotone_of_le_update`. `isSelfDualMonotone_booleanCubeConcat_iff` is the
  same criterion for a concatenation and `eq_booleanCubeConcat_iff` recovers a
  function from its blocks. Theorems 6, 10, 12 and 14 apply these criteria for
  `k = 1, 2, 4`; for `k = 4` the edge condition is checked on the `32` edges of
  the `4`-cube by case analysis.
* `sum_monotone_eq_sum_reps` turns a sum over `D_n` of a permutation-invariant
  weight into a sum over any system of representatives weighted by class
  sizes; this gives the `reps` forms of Theorems 6, 9 and 10.
* Theorem 13 counts the tuples of Theorem 12 by a bijection with a
  `Finset.sigma`.
* Lemma 15: if every orbit of `π` has even length, alternating along the
  orbits gives `x` with `x ∘ π = xᶜ`, and a self-dual function cannot be fixed
  by `π` (`comp_perm_ne_of_eq_booleanFunctionDual`). Corollary 16 uses the
  vector `x i = decide (Even i)`, checked by `decide` for each of the five
  permutations.
* Lemma 17: for odd `n` the majority function is self-dual, monotone and
  invariant under every permutation.

## Unused hypotheses

The following hypotheses are kept so that the statements match the source,
but the proofs do not use them:
* `Monotone f` and `Monotone g` in Lemma 2, the premise `Monotone f` of the
  second part of Lemma 5, and `Monotone b` in Lemma 8;
* `1 ≤ n` in Theorem 9, so both parts of Theorem 9 also hold for `n = 0`;
* `a|b|c|a*|b*|c* ≤ h` in the first part of Theorem 12, and `h* ≤ h` in the
  first part of Theorem 14, which follow from the other hypotheses.
-/

namespace MetaMathlibExt

open Finset

@[expose] public section

/-! ### Duality and the pointwise order -/

/-- `booleanVectorComplement` is the Boolean-algebra complement on
`Fin n → Bool`. -/
theorem booleanVectorComplement_eq_compl (n : ℕ) (x : Fin n → Bool) :
    booleanVectorComplement n x = xᶜ :=
  rfl

/-- The dual of `f` at `x` is the complement of `f` at `xᶜ`. -/
theorem booleanFunctionDual_apply_eq_compl (n : ℕ)
    (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    booleanFunctionDual n f x = (f xᶜ)ᶜ :=
  rfl

/-- `IsSelfDualMonotone` is `Monotone` together with `f = f*`. -/
theorem isSelfDualMonotone_iff {n : ℕ} {f : (Fin n → Bool) → Bool} :
    IsSelfDualMonotone n f ↔ Monotone f ∧ f = booleanFunctionDual n f :=
  Iff.rfl

/-- Duality of Boolean functions is an involution. -/
theorem booleanFunctionDual_involutive (n : ℕ) :
    Function.Involutive (booleanFunctionDual n) :=
  booleanFunctionDual_dual n

/-- The dual of a monotone Boolean function is monotone.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 5 (`jis-2025-25.3.4-prop-5`).
Proves `Wanted` entry `monotone_booleanFunctionDual`
(`WantedExt/Combinatorics/Enumerative/UnateMonotoneBooleanWanted.lean`). -/
theorem monotone_booleanFunctionDual {n : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : Monotone f) : Monotone (booleanFunctionDual n f) :=
  fun _ _ hxy => compl_le_compl (hf (compl_le_compl hxy))

/-- `f*` is monotone iff `f` is. -/
theorem monotone_booleanFunctionDual_iff {n : ℕ}
    {f : (Fin n → Bool) → Bool} :
    Monotone (booleanFunctionDual n f) ↔ Monotone f :=
  ⟨fun h => booleanFunctionDual_dual n f ▸ monotone_booleanFunctionDual h,
    monotone_booleanFunctionDual⟩

/-- Duality reverses the pointwise order of Boolean functions. -/
theorem antitone_booleanFunctionDual (n : ℕ) :
    Antitone (booleanFunctionDual n) :=
  fun _ _ h x => compl_le_compl (h xᶜ)

/-- `f* ≤ g*` iff `g ≤ f`. -/
theorem booleanFunctionDual_le_booleanFunctionDual_iff {n : ℕ}
    {f g : (Fin n → Bool) → Bool} :
    booleanFunctionDual n f ≤ booleanFunctionDual n g ↔ g ≤ f :=
  ⟨fun h => by simpa using antitone_booleanFunctionDual n h,
    fun h => antitone_booleanFunctionDual n h⟩

/-- `f* ≤ g` iff `g* ≤ f`. -/
theorem booleanFunctionDual_le_comm {n : ℕ} {f g : (Fin n → Bool) → Bool} :
    booleanFunctionDual n f ≤ g ↔ booleanFunctionDual n g ≤ f := by
  rw [← booleanFunctionDual_le_booleanFunctionDual_iff,
    booleanFunctionDual_dual]

/-- `(f ⊔ g)* = f* ⊓ g*`, for all Boolean functions. -/
theorem booleanFunctionDual_sup (n : ℕ) (f g : (Fin n → Bool) → Bool) :
    booleanFunctionDual n (f ⊔ g) =
      booleanFunctionDual n f ⊓ booleanFunctionDual n g :=
  funext fun _ => compl_sup

/-- `(f ⊓ g)* = f* ⊔ g*`, for all Boolean functions. -/
theorem booleanFunctionDual_inf (n : ℕ) (f g : (Fin n → Bool) → Bool) :
    booleanFunctionDual n (f ⊓ g) =
      booleanFunctionDual n f ⊔ booleanFunctionDual n g :=
  funext fun _ => compl_inf

set_option linter.unusedVariables false in
/-- **Lemma 2 (parts 2-4).** For `f, g ∈ D_n`: if `f ≤ g` then `g* ≤ f*`;
`(f | g)* = f* & g*`; `(f & g)* = f* | g*`.

Part 1 (`f** = f`) is `MetaMathlibExt.booleanFunctionDual_dual`, already
proved for every Boolean function, and is not restated.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual
Monotone Boolean Functions*, Journal of Integer Sequences 28 (2025), Article
25.6.5, Lemma 2 (`jis-2025-25.6.5-lem-2`).

Proves `Wanted` entry `booleanFunctionDual_antitone_sup_inf`. -/
theorem booleanFunctionDual_antitone_sup_inf (n : ℕ)
    (f g : (Fin n → Bool) → Bool) (hf : Monotone f) (hg : Monotone g) :
    (f ≤ g → booleanFunctionDual n g ≤ booleanFunctionDual n f) ∧
      booleanFunctionDual n (f ⊔ g) =
        booleanFunctionDual n f ⊓ booleanFunctionDual n g ∧
      booleanFunctionDual n (f ⊓ g) =
        booleanFunctionDual n f ⊔ booleanFunctionDual n g :=
  ⟨fun h => antitone_booleanFunctionDual n h, booleanFunctionDual_sup n f g,
    booleanFunctionDual_inf n f g⟩

/-! ### Relabelling the variables -/

/-- Relabelling the variables of a Boolean function by a permutation `π`,
`f ↦ (x ↦ f (x ∘ π))`, as an order automorphism for the pointwise order. -/
def booleanFunctionPerm (n : ℕ) (π : Equiv.Perm (Fin n)) :
    ((Fin n → Bool) → Bool) ≃o ((Fin n → Bool) → Bool) where
  toFun f x := f (x ∘ π)
  invFun f x := f (x ∘ π.symm)
  left_inv f := funext fun x => by simp [Function.comp_assoc]
  right_inv f := funext fun x => by simp [Function.comp_assoc]
  map_rel_iff' {f g} := by
    refine ⟨fun h x => ?_, fun h x => h (x ∘ π)⟩
    simpa [Function.comp_assoc] using h (x ∘ π.symm)

@[simp]
theorem booleanFunctionPerm_apply (n : ℕ) (π : Equiv.Perm (Fin n))
    (f : (Fin n → Bool) → Bool) :
    booleanFunctionPerm n π f = fun x => f (x ∘ π) :=
  rfl

/-- Relabelling the variables preserves and reflects the pointwise order. -/
theorem comp_perm_le_comp_perm_iff {n : ℕ} {f g : (Fin n → Bool) → Bool}
    (π : Equiv.Perm (Fin n)) :
    ((fun x => f (x ∘ π)) ≤ fun x => g (x ∘ π)) ↔ f ≤ g :=
  (booleanFunctionPerm n π).le_iff_le

/-- Relabelling the variables of a monotone function gives a monotone
function. -/
theorem monotone_comp_perm {n : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : Monotone f) (π : Equiv.Perm (Fin n)) :
    Monotone fun x => f (x ∘ π) :=
  fun _ _ h => hf fun i => h (π i)

/-- `f ∘ π` is monotone iff `f` is. -/
theorem monotone_comp_perm_iff {n : ℕ} {f : (Fin n → Bool) → Bool}
    (π : Equiv.Perm (Fin n)) : (Monotone fun x => f (x ∘ π)) ↔ Monotone f :=
  ⟨fun h => by simpa [Function.comp_assoc] using monotone_comp_perm h π.symm,
    fun h => monotone_comp_perm h π⟩

/-- Relabelling the variables commutes with duality, for every Boolean
function. -/
theorem booleanFunctionDual_comp_perm (n : ℕ) (f : (Fin n → Bool) → Bool)
    (π : Equiv.Perm (Fin n)) :
    (fun x => booleanFunctionDual n f (x ∘ π)) =
      booleanFunctionDual n fun x => f (x ∘ π) :=
  rfl

/-- **Lemma 5.** For every `f : Bⁿ → B` and permutation `π`: `f ∘ π` is
monotone if `f` is; if `f ∈ D_n` then `f* ∘ π = (f ∘ π)*`; if `f ∈ Λ_n` then
every `g ∈ [f]` is in `Λ_n`.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual
Monotone Boolean Functions*, Journal of Integer Sequences 28 (2025), Article
25.6.5, Lemma 5 (`jis-2025-25.6.5-lem-5`).

Proves `Wanted` entry `booleanFunction_perm_monotone_dual_selfDual`. -/
theorem booleanFunction_perm_monotone_dual_selfDual (n : ℕ)
    (f : (Fin n → Bool) → Bool) (π : Equiv.Perm (Fin n)) :
    (Monotone f → Monotone fun x => f (x ∘ π)) ∧
      (Monotone f →
        (fun x => booleanFunctionDual n f (x ∘ π)) =
          booleanFunctionDual n fun x => f (x ∘ π)) ∧
      (IsSelfDualMonotone n f → IsSelfDualMonotone n fun x => f (x ∘ π)) :=
  ⟨fun hf => monotone_comp_perm hf π,
    fun _ => booleanFunctionDual_comp_perm n f π,
    fun hf => ⟨monotone_comp_perm hf.1 π,
      (congrArg (fun g x => g (x ∘ π)) hf.2).trans
        (booleanFunctionDual_comp_perm n f π)⟩⟩

/-- Relabelling the variables does not change the number of `true` values. -/
theorem card_true_comp_perm {n : ℕ} (b : (Fin n → Bool) → Bool)
    (π : Equiv.Perm (Fin n)) :
    Nat.card {x // b (x ∘ π) = true} = Nat.card {x // b x = true} :=
  Nat.card_congr <|
    (Equiv.arrowCongr π.symm (Equiv.refl Bool)).subtypeEquiv fun _ => Iff.rfl

/-! ### Weights -/

/-- `ℓ(b*) = 2ⁿ - ℓ(b)` for every Boolean function `b`. -/
theorem card_true_booleanFunctionDual (n : ℕ) (b : (Fin n → Bool) → Bool) :
    Nat.card {x // booleanFunctionDual n b x = true} =
      2 ^ n - Nat.card {x // b x = true} := by
  have h : Nat.card {x // booleanFunctionDual n b x = true} =
      Nat.card {x // ¬b x = true} :=
    Nat.card_congr <|
      (Function.Involutive.toPerm _ compl_compl).subtypeEquiv fun x => by
        change (b xᶜ)ᶜ = true ↔ ¬b xᶜ = true
        cases b xᶜ <;> decide
  rw [h, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Nat.card_eq_fintype_card]
  simp

/-- `ℓ(b) ≤ 2ⁿ`. -/
theorem card_true_le_two_pow (n : ℕ) (b : (Fin n → Bool) → Bool) :
    Nat.card {x // b x = true} ≤ 2 ^ n := by
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_subtype_le _).trans (by simp)

/-- The weight `ℓ` is monotone for the pointwise order. -/
theorem card_true_mono {n : ℕ} {b c : (Fin n → Bool) → Bool} (h : b ≤ c) :
    Nat.card {x // b x = true} ≤ Nat.card {x // c x = true} :=
  Nat.card_le_card_of_injective
    (Subtype.map id fun x hx => by
      have := h x
      rw [hx] at this
      exact top_le_iff.mp this)
    (Subtype.map_injective _ Function.injective_id)

/-- If `b ≤ c` and `ℓ(c) ≤ ℓ(b)` then `b = c`. -/
theorem eq_of_le_of_card_true_le {n : ℕ} {b c : (Fin n → Bool) → Bool}
    (h : b ≤ c)
    (hc : Nat.card {x // c x = true} ≤ Nat.card {x // b x = true}) :
    b = c := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at hc
  have hsub : univ.filter (fun x => b x = true) ⊆
      univ.filter (fun x => c x = true) := by
    intro x
    simp only [mem_filter, mem_univ, true_and]
    intro hx
    have := h x
    rw [hx] at this
    exact top_le_iff.mp this
  have heq := Finset.eq_of_subset_of_card_le hsub hc
  funext x
  have hx := congrArg (x ∈ ·) heq
  simp only [mem_filter, mem_univ, true_and, eq_iff_iff] at hx
  cases hb : b x <;> cases hcx : c x <;> simp_all

/-- The duality `f ↦ f*` exchanges the monotone functions of weight below
`2^{n-1}` with those of weight above `2^{n-1}`. -/
theorem card_weight_lt_eq_card_weight_gt (n : ℕ) :
    Nat.card {f : (Fin n → Bool) → Bool //
        Monotone f ∧ 2 * Nat.card {x // f x = true} < 2 ^ n} =
      Nat.card {f : (Fin n → Bool) → Bool //
        Monotone f ∧ 2 ^ n < 2 * Nat.card {x // f x = true}} := by
  refine Nat.card_congr ((booleanFunctionDual_involutive n).toPerm _
    |>.subtypeEquiv fun f => ?_)
  have hd := card_true_booleanFunctionDual n f
  have hle := card_true_le_two_pow n f
  simp only [Function.Involutive.coe_toPerm, monotone_booleanFunctionDual_iff,
    hd]
  generalize 2 ^ n = N at hle ⊢
  exact and_congr_right fun _ => by omega

set_option linter.unusedVariables false in
/-- **Lemma 8.** For `b ∈ D_n`: `b ≤ b*` only if `ℓ(b) ≤ 2^{n-1}`; if
`ℓ(b) = 2^{n-1}` and `b ≤ b*` then `b = b*`; if `b` is self-dual then
`ℓ(b) = 2^{n-1}`; `ℓ(b*) = 2ⁿ - ℓ(b)`, hence
`|{f ∈ D_n | ℓ(f) < 2^{n-1}}| = |{f ∈ D_n | ℓ(f) > 2^{n-1}}|`.

Comparisons with `2^{n-1}` are written as comparisons of `2 ℓ` with `2ⁿ` (so
`n = 0` is included).

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual
Monotone Boolean Functions*, Journal of Integer Sequences 28 (2025), Article
25.6.5, Lemma 8 (`jis-2025-25.6.5-lem-8`).

Proves `Wanted` entry `monotoneBooleanFunction_weight_dual`. -/
theorem monotoneBooleanFunction_weight_dual (n : ℕ)
    (b : (Fin n → Bool) → Bool) (hb : Monotone b) :
    (b ≤ booleanFunctionDual n b →
        2 * Nat.card {x // b x = true} ≤ 2 ^ n) ∧
      (2 * Nat.card {x // b x = true} = 2 ^ n →
        b ≤ booleanFunctionDual n b → b = booleanFunctionDual n b) ∧
      (b = booleanFunctionDual n b →
        2 * Nat.card {x // b x = true} = 2 ^ n) ∧
      Nat.card {x // booleanFunctionDual n b x = true} =
        2 ^ n - Nat.card {x // b x = true} ∧
      Nat.card {f : (Fin n → Bool) → Bool //
          Monotone f ∧ 2 * Nat.card {x // f x = true} < 2 ^ n} =
        Nat.card {f : (Fin n → Bool) → Bool //
          Monotone f ∧ 2 ^ n < 2 * Nat.card {x // f x = true}} := by
  have hd := card_true_booleanFunctionDual n b
  have hle := card_true_le_two_pow n b
  refine ⟨fun h => ?_, fun h1 h2 => ?_, fun h => ?_, hd,
    card_weight_lt_eq_card_weight_gt n⟩
  · have := card_true_mono h
    omega
  · exact eq_of_le_of_card_true_le h2 (by omega)
  · have := congrArg (fun f => Nat.card {x // f x = true}) h
    omega

/-! ### Sums over permutation classes -/

open Classical in
/-- A sum over `D_n` of a permutation-invariant weight `w` is the sum over a
system of representatives `reps` of the permutation classes of `D_n`, each
term weighted by the size of its class. -/
theorem sum_monotone_eq_sum_reps {n : ℕ} {M : Type*} [AddCommMonoid M]
    (w : ((Fin n → Bool) → Bool) → M)
    (hw : ∀ b (π : Equiv.Perm (Fin n)), w (fun x => b (x ∘ π)) = w b)
    (reps : Finset ((Fin n → Bool) → Bool)) (hreps : ∀ b ∈ reps, Monotone b)
    (huniq : ∀ f : (Fin n → Bool) → Bool, Monotone f →
      ∃! b, b ∈ reps ∧ ∃ π : Equiv.Perm (Fin n), f = fun x => b (x ∘ π)) :
    ∑ f ∈ univ.filter (fun f : (Fin n → Bool) → Bool => Monotone f), w f =
      ∑ b ∈ reps, Nat.card {g : (Fin n → Bool) → Bool //
        ∃ π : Equiv.Perm (Fin n), g = fun x => b (x ∘ π)} • w b := by
  set cls : ((Fin n → Bool) → Bool) → Finset ((Fin n → Bool) → Bool) :=
    fun b => univ.filter fun g =>
      ∃ π : Equiv.Perm (Fin n), g = fun x => b (x ∘ π) with hcls
  have hS : univ.filter (fun f : (Fin n → Bool) → Bool => Monotone f) =
      reps.biUnion cls := by
    ext f
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, hcls]
    constructor
    · intro hf
      obtain ⟨b, ⟨hb, π, rfl⟩, -⟩ := huniq f hf
      exact ⟨b, hb, π, rfl⟩
    · rintro ⟨b, hb, π, rfl⟩
      exact monotone_comp_perm (hreps b hb) π
  have hdisj : (reps : Set ((Fin n → Bool) → Bool)).PairwiseDisjoint cls := by
    intro b hb b' hb' hne
    refine Finset.disjoint_left.2 fun g hg hg' => hne ?_
    simp only [mem_filter, mem_univ, true_and, hcls] at hg hg'
    obtain ⟨π, rfl⟩ := hg
    exact (huniq _ (monotone_comp_perm (hreps b hb) π)).unique
      ⟨hb, π, rfl⟩ ⟨hb', hg'⟩
  rw [hS, sum_biUnion hdisj]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_congr rfl (g := fun _ => w b), sum_const]
  · rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  · intro g hg
    simp only [mem_filter, mem_univ, true_and, hcls] at hg
    obtain ⟨π, rfl⟩ := hg
    exact hw b π

open Classical in
/-- The number of `f ∈ D_n` with a permutation-invariant property `P` is the
sum of the class sizes of the representatives in `reps` with property `P`. -/
theorem card_monotone_and_eq_sum_reps {n : ℕ}
    (P : ((Fin n → Bool) → Bool) → Prop)
    (hP : ∀ b (π : Equiv.Perm (Fin n)), P (fun x => b (x ∘ π)) ↔ P b)
    (reps : Finset ((Fin n → Bool) → Bool)) (hreps : ∀ b ∈ reps, Monotone b)
    (huniq : ∀ f : (Fin n → Bool) → Bool, Monotone f →
      ∃! b, b ∈ reps ∧ ∃ π : Equiv.Perm (Fin n), f = fun x => b (x ∘ π)) :
    Nat.card {f : (Fin n → Bool) → Bool // Monotone f ∧ P f} =
      ∑ b ∈ reps with P b, Nat.card {g : (Fin n → Bool) → Bool //
        ∃ π : Equiv.Perm (Fin n), g = fun x => b (x ∘ π)} := by
  have h := sum_monotone_eq_sum_reps (fun f => if P f then 1 else 0)
    (fun b π => by simp only [hP]) reps hreps huniq
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero, sum_boole,
    Nat.cast_id] at h
  rw [sum_filter, ← h, filter_filter, Nat.card_eq_fintype_card,
    Fintype.card_subtype]

/-- Splitting a finite subtype according to a second predicate. -/
theorem natCard_subtype_eq_add {α : Type*} [Finite α] (p q : α → Prop) :
    Nat.card {x // p x} =
      Nat.card {x // p x ∧ q x} + Nat.card {x // p x ∧ ¬q x} := by
  classical
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← filter_filter, ← filter_filter, card_filter_add_card_filter_not]

/-! ### Splitting the variables -/

/-- `Fin.append` as an order isomorphism
`(Fin m → α) × (Fin n → α) ≃o (Fin (m + n) → α)`. -/
def finAppendOrderIso (α : Type*) [Preorder α] (m n : ℕ) :
    (Fin m → α) × (Fin n → α) ≃o (Fin (m + n) → α) where
  toEquiv := Fin.appendEquiv m n
  map_rel_iff' {p q} := by
    change Fin.append p.1 p.2 ≤ Fin.append q.1 q.2 ↔ p ≤ q
    constructor
    · intro h
      exact ⟨fun i => by simpa using h (Fin.castAdd n i),
        fun i => by simpa using h (Fin.natAdd m i)⟩
    · rintro ⟨h1, h2⟩ i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa using h1 i
      · simpa using h2 i

@[simp]
theorem finAppendOrderIso_apply (α : Type*) [Preorder α] (m n : ℕ)
    (p : (Fin m → α) × (Fin n → α)) :
    finAppendOrderIso α m n p = Fin.append p.1 p.2 :=
  rfl

/-- `Fin.append` is monotone in both arguments. -/
theorem finAppend_le_finAppend {m n : ℕ} {α : Type*} [Preorder α]
    {x x' : Fin m → α} {y y' : Fin n → α} (hx : x ≤ x') (hy : y ≤ y') :
    Fin.append x y ≤ Fin.append x' y' :=
  (finAppendOrderIso α m n).le_iff_le.2 (Prod.mk_le_mk.2 ⟨hx, hy⟩)

/-- Complement commutes with `Fin.append`. -/
theorem compl_finAppend {m n : ℕ} {α : Type*} [Compl α] (x : Fin m → α)
    (y : Fin n → α) : (Fin.append x y)ᶜ = Fin.append xᶜ yᶜ := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

/-- **Lemma 1.** The poset `D_{n+k}` is isomorphic to the poset `D_n^{B^k}` of
monotone functions from `B^k` to `D_n`.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual
Monotone Boolean Functions*, Journal of Integer Sequences 28 (2025), Article
25.6.5, Lemma 1 (`jis-2025-25.6.5-lem-1`).

Proves `Wanted` entry `monotoneBooleanFunction_orderIso_curry`. -/
theorem monotoneBooleanFunction_orderIso_curry (n k : ℕ) :
    Nonempty (((Fin (n + k) → Bool) →o Bool) ≃o
      ((Fin k → Bool) →o ((Fin n → Bool) →o Bool))) :=
  ⟨(OrderIso.arrowCongr
      ((finAppendOrderIso Bool n k).symm.trans OrderIso.prodComm)
      (OrderIso.refl Bool)).trans OrderHom.curry⟩

/-! ### Binary indices -/

/-- The binary index of `y : Fin k → Bool` through `finFunctionFinEquiv`. -/
theorem sum_ite_two_pow_eq_finFunctionFinEquiv {k : ℕ} (y : Fin k → Bool) :
    (∑ j : Fin k, if y j then 2 ^ (j : ℕ) else 0) =
      (finFunctionFinEquiv (fun j => if y j then (1 : Fin 2) else 0) : ℕ) := by
  rw [finFunctionFinEquiv_apply]
  refine sum_congr rfl fun j _ => ?_
  cases y j <;> simp

/-- The binary index of `y : Fin k → Bool` is below `2 ^ k`. -/
theorem sum_ite_two_pow_lt {k : ℕ} (y : Fin k → Bool) :
    (∑ j : Fin k, if y j then 2 ^ (j : ℕ) else 0) < 2 ^ k := by
  rw [sum_ite_two_pow_eq_finFunctionFinEquiv]
  exact Fin.isLt _

/-- The `j`-th bit of the binary index of `y` is `y j`. -/
theorem testBit_sum_ite_two_pow {k : ℕ} (y : Fin k → Bool) (j : Fin k) :
    (∑ i : Fin k, if y i then 2 ^ (i : ℕ) else 0).testBit j = y j := by
  rw [sum_ite_two_pow_eq_finFunctionFinEquiv, Nat.testBit_eq_decide_div_mod_eq,
    ← finFunctionFinEquiv_symm_apply_val, Equiv.symm_apply_apply]
  cases y j <;> simp

/-- The bits of the binary index of `y` are the values of `y`. -/
theorem fun_testBit_sum_ite_two_pow {k : ℕ} (y : Fin k → Bool) :
    (fun j : Fin k =>
      (∑ i : Fin k, if y i then 2 ^ (i : ℕ) else 0).testBit j) = y :=
  funext (testBit_sum_ite_two_pow y)

/-- Every `i < 2 ^ k` is the binary index of its first `k` bits. -/
theorem sum_ite_testBit_two_pow {k i : ℕ} (hi : i < 2 ^ k) :
    (∑ j : Fin k, if i.testBit j then 2 ^ (j : ℕ) else 0) = i := by
  refine Nat.eq_of_testBit_eq fun m => ?_
  by_cases hm : m < k
  · exact testBit_sum_ite_two_pow (fun j : Fin k => i.testBit j) ⟨m, hm⟩
  · have hk : 2 ^ k ≤ 2 ^ m := Nat.pow_le_pow_right two_pos (not_lt.1 hm)
    rw [Nat.testBit_lt_two_pow ((sum_ite_two_pow_lt _).trans_le hk),
      Nat.testBit_lt_two_pow (hi.trans_le hk)]

/-- Switching on a coordinate `j` that is off adds `2 ^ j` to the binary
index. -/
theorem sum_ite_two_pow_update {k : ℕ} (y : Fin k → Bool) (j : Fin k)
    (hj : y j = false) :
    (∑ i : Fin k, if Function.update y j true i then 2 ^ (i : ℕ) else 0) =
      (∑ i : Fin k, if y i then 2 ^ (i : ℕ) else 0) + 2 ^ (j : ℕ) := by
  rw [Fintype.sum_eq_add_sum_compl j, Fintype.sum_eq_add_sum_compl j]
  simp only [Function.update_self, ite_true, hj, Bool.false_eq_true,
    ite_false, zero_add]
  rw [add_comm]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (by simpa using hi)]

/-- Complementing `y` sends its binary index `i` to `2 ^ k - 1 - i`. -/
theorem sum_ite_two_pow_compl {k : ℕ} (y : Fin k → Bool) :
    (∑ j : Fin k, if yᶜ j then 2 ^ (j : ℕ) else 0) =
      2 ^ k - 1 - ∑ j : Fin k, if y j then 2 ^ (j : ℕ) else 0 := by
  have h : (∑ j : Fin k, if yᶜ j then 2 ^ (j : ℕ) else 0) +
      (∑ j : Fin k, if y j then 2 ^ (j : ℕ) else 0) = 2 ^ k - 1 := by
    rw [← sum_add_distrib]
    have : ∀ j : Fin k, ((if yᶜ j then 2 ^ (j : ℕ) else 0) +
        if y j then 2 ^ (j : ℕ) else 0) = 2 ^ (j : ℕ) := by
      intro j
      rw [Pi.compl_apply]
      cases y j <;> simp
    rw [sum_congr rfl fun j _ => this j,
      Fin.sum_univ_eq_sum_range (fun j => 2 ^ j), Nat.geomSum_eq le_rfl]
    simp
  generalize 2 ^ k = N at h ⊢
  omega

/-- If bit `j < k` of `i < 2 ^ k` is clear, the first `k` bits of `i + 2 ^ j`
are those of `i` with bit `j` set. -/
theorem testBit_add_two_pow_eq_update {k i : ℕ} (hi : i < 2 ^ k) (j : Fin k)
    (hj : i.testBit j = false) :
    (fun m : Fin k => (i + 2 ^ (j : ℕ)).testBit m) =
      Function.update (fun m : Fin k => i.testBit m) j true := by
  have h := sum_ite_two_pow_update (fun m : Fin k => i.testBit m) j hj
  rw [sum_ite_testBit_two_pow hi] at h
  rw [← h, fun_testBit_sum_ite_two_pow]

/-- If bit `j < k` of `i < 2 ^ k` is clear then `i + 2 ^ j < 2 ^ k`. -/
theorem add_two_pow_lt_of_testBit_eq_false {k i : ℕ} (hi : i < 2 ^ k)
    (j : Fin k) (hj : i.testBit j = false) : i + 2 ^ (j : ℕ) < 2 ^ k := by
  have h := sum_ite_two_pow_update (fun m : Fin k => i.testBit m) j hj
  rw [sum_ite_testBit_two_pow hi] at h
  exact h ▸ sum_ite_two_pow_lt _

/-- For `i < 2 ^ k`, the first `k` bits of `2 ^ k - 1 - i` are the complements
of those of `i`. -/
theorem testBit_two_pow_sub_one_sub {k i : ℕ} (hi : i < 2 ^ k) :
    (fun m : Fin k => (2 ^ k - 1 - i).testBit m) =
      (fun m : Fin k => i.testBit m)ᶜ := by
  have h := sum_ite_two_pow_compl (fun m : Fin k => i.testBit m)
  rw [sum_ite_testBit_two_pow hi] at h
  rw [← h, fun_testBit_sum_ite_two_pow]

/-- A function on a finite Boolean cube is monotone as soon as it increases
whenever one coordinate is switched from `false` to `true`. -/
theorem monotone_of_le_update {ι α : Type*} [Finite ι] [DecidableEq ι]
    [Preorder α] {G : (ι → Bool) → α}
    (hG : ∀ y j, y j = false → G y ≤ G (Function.update y j true)) :
    Monotone G := by
  have := Fintype.ofFinite ι
  intro y y' hyy'
  suffices h : ∀ s : Finset ι,
      G y ≤ G (fun j => if j ∈ s then y' j else y j) by
    simpa using h univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    refine ih.trans ?_
    set z : ι → Bool := fun j => if j ∈ s then y' j else y j with hz
    have hins : (fun j => if j ∈ insert a s then y' j else y j) =
        Function.update z a (y' a) := by
      funext j
      by_cases hj : j = a
      · subst hj
        simp
      · simp [hj, hz]
    rw [hins]
    have hza : z a = y a := by simp [hz, ha]
    by_cases h : z a = y' a
    · rw [← h, Function.update_eq_self]
    · have key : ∀ b c : Bool, b ≤ c → b ≠ c → b = false ∧ c = true := by
        decide
      have h1 : z a = false ∧ y' a = true :=
        hza ▸ key _ _ (hyy' a) (hza ▸ h)
      rw [h1.2]
      exact hG z a h1.1

/-! ### Blocks and concatenations -/

/-- The concatenation `W₀ · W₁ ⋯` of Boolean functions on `n` variables, as a
function on `n + k` variables: the last `k` variables give the binary index
`∑ⱼ yⱼ 2^j` into the word `W`, and the selected function is applied to the
first `n` variables (out-of-range indices read `false`).

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual
Monotone Boolean Functions*, Journal of Integer Sequences 28 (2025), Article
25.6.5, the concatenation representation of `D_n^{B^k}` before Theorem 10. -/
public def booleanCubeConcat (n k : ℕ) (W : List ((Fin n → Bool) → Bool)) :
    (Fin (n + k) → Bool) → Bool :=
  fun x => (W.getD (∑ j : Fin k,
      if x (Fin.natAdd n j) then 2 ^ (j : ℕ) else 0) fun _ => false)
    fun i => x (Fin.castAdd k i)

/-- On the all-`false` input the concatenation reads the first word entry at
all-`false`.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual
Monotone Boolean Functions*, Journal of Integer Sequences 28 (2025), Article
25.6.5, the concatenation representation of `D_n^{B^k}` before Theorem 10. -/
public theorem booleanCubeConcat_false (n k : ℕ)
    (W : List ((Fin n → Bool) → Bool)) :
    booleanCubeConcat n k W (fun _ => false) =
      W.getD 0 (fun _ => false) (fun _ => false) := by
  simp [booleanCubeConcat]

/-- The `i`-th block of a Boolean function `F` on `n + k` variables: the
function of the first `n` variables obtained by fixing the last `k` variables
to the first `k` binary digits of `i`. -/
def booleanCubeBlock (n k : ℕ) (F : (Fin (n + k) → Bool) → Bool) (i : ℕ) :
    (Fin n → Bool) → Bool :=
  fun x => F (Fin.append x fun j => i.testBit j)

/-- The block of `F` at the binary index of `y` is `F` with its last `k`
variables fixed to `y`. -/
theorem booleanCubeBlock_sum_ite_two_pow {n k : ℕ}
    (F : (Fin (n + k) → Bool) → Bool) (y : Fin k → Bool) :
    booleanCubeBlock n k F (∑ j : Fin k, if y j then 2 ^ (j : ℕ) else 0) =
      fun x => F (Fin.append x y) := by
  unfold booleanCubeBlock
  rw [fun_testBit_sum_ite_two_pow]

/-- A concatenation evaluated at `Fin.append x y`. -/
theorem booleanCubeConcat_append (n k : ℕ) (W : List ((Fin n → Bool) → Bool))
    (x : Fin n → Bool) (y : Fin k → Bool) :
    booleanCubeConcat n k W (Fin.append x y) =
      W.getD (∑ j : Fin k, if y j then 2 ^ (j : ℕ) else 0) (fun _ => false)
        x := by
  simp only [booleanCubeConcat, Fin.append_left, Fin.append_right]

/-- For `i < 2 ^ k`, the `i`-th block of a concatenation is the `i`-th entry
of the word. -/
theorem booleanCubeBlock_booleanCubeConcat (n k : ℕ)
    (W : List ((Fin n → Bool) → Bool)) {i : ℕ} (hi : i < 2 ^ k) :
    booleanCubeBlock n k (booleanCubeConcat n k W) i =
      W.getD i fun _ => false := by
  funext x
  rw [booleanCubeBlock, booleanCubeConcat_append, sum_ite_testBit_two_pow hi]

/-- A function is the concatenation of a word iff its first `2 ^ k` blocks
are the entries of the word. -/
theorem eq_booleanCubeConcat_iff {n k : ℕ} (F : (Fin (n + k) → Bool) → Bool)
    (W : List ((Fin n → Bool) → Bool)) :
    F = booleanCubeConcat n k W ↔
      ∀ i < 2 ^ k, (W.getD i fun _ => false) = booleanCubeBlock n k F i := by
  constructor
  · rintro rfl i hi
    exact (booleanCubeBlock_booleanCubeConcat n k W hi).symm
  · intro h
    funext z
    rw [← Fin.append_castAdd_natAdd (f := z), booleanCubeConcat_append,
      h _ (sum_ite_two_pow_lt _), booleanCubeBlock_sum_ite_two_pow]

/-- The blocks of a monotone function are monotone. -/
theorem monotone_booleanCubeBlock {n k : ℕ}
    {F : (Fin (n + k) → Bool) → Bool} (hF : Monotone F) (i : ℕ) :
    Monotone (booleanCubeBlock n k F i) :=
  fun _ _ hx => hF (finAppend_le_finAppend hx le_rfl)

/-- For a monotone function, the block at `i` lies below the block at `i'`
whenever the first `k` bits of `i` are among those of `i'`. -/
theorem booleanCubeBlock_le_booleanCubeBlock {n k : ℕ}
    {F : (Fin (n + k) → Bool) → Bool} (hF : Monotone F) {i i' : ℕ}
    (h : ∀ m < k, i.testBit m = true → i'.testBit m = true) :
    booleanCubeBlock n k F i ≤ booleanCubeBlock n k F i' :=
  fun _ => hF (finAppend_le_finAppend le_rfl fun m =>
    Bool.le_iff_imp.2 (h m m.isLt))

/-- **Self-dual monotone functions on `n + k` variables via their blocks.**
`F` is self-dual and monotone iff its first `2 ^ k` blocks are monotone,
increase along the edges `i → i + 2 ^ j` of the cube (bit `j` of `i` clear),
and satisfy `block (2 ^ k - 1 - i) = (block i)*`. -/
theorem isSelfDualMonotone_add_iff {n k : ℕ}
    (F : (Fin (n + k) → Bool) → Bool) :
    IsSelfDualMonotone (n + k) F ↔
      (∀ i < 2 ^ k, Monotone (booleanCubeBlock n k F i)) ∧
      (∀ i < 2 ^ k, ∀ j < k, i.testBit j = false →
        booleanCubeBlock n k F i ≤ booleanCubeBlock n k F (i + 2 ^ j)) ∧
      ∀ i < 2 ^ k, booleanCubeBlock n k F (2 ^ k - 1 - i) =
        booleanFunctionDual n (booleanCubeBlock n k F i) := by
  rw [isSelfDualMonotone_iff]
  constructor
  · rintro ⟨hmono, hdual⟩
    refine ⟨fun i _ => monotone_booleanCubeBlock hmono i, ?_, ?_⟩
    · intro i hi j hj hb x
      unfold booleanCubeBlock
      rw [testBit_add_two_pow_eq_update hi ⟨j, hj⟩ hb]
      refine hmono (finAppend_le_finAppend le_rfl fun m => ?_)
      by_cases hm : m = ⟨j, hj⟩
      · subst hm
        simp
      · rw [Function.update_of_ne hm]
    · intro i hi
      funext x
      unfold booleanCubeBlock
      rw [testBit_two_pow_sub_one_sub hi]
      conv_lhs => rw [hdual]
      rw [booleanFunctionDual_apply_eq_compl,
        booleanFunctionDual_apply_eq_compl, compl_finAppend, compl_compl]
  · rintro ⟨hm, he, hd⟩
    have hH : Monotone fun y : Fin k → Bool =>
        fun x : Fin n → Bool => F (Fin.append x y) := by
      refine monotone_of_le_update fun y j hj => ?_
      rw [← booleanCubeBlock_sum_ite_two_pow,
        ← booleanCubeBlock_sum_ite_two_pow, sum_ite_two_pow_update y j hj]
      exact he _ (sum_ite_two_pow_lt y) j j.isLt
        (by rw [testBit_sum_ite_two_pow, hj])
    have hHy : ∀ y : Fin k → Bool,
        Monotone fun x : Fin n → Bool => F (Fin.append x y) :=
      fun y => booleanCubeBlock_sum_ite_two_pow F y ▸
        hm _ (sum_ite_two_pow_lt y)
    have hHd : ∀ y : Fin k → Bool,
        (fun x : Fin n → Bool => F (Fin.append x yᶜ)) =
          booleanFunctionDual n fun x => F (Fin.append x y) := by
      intro y
      rw [← booleanCubeBlock_sum_ite_two_pow,
        ← booleanCubeBlock_sum_ite_two_pow, sum_ite_two_pow_compl]
      exact hd _ (sum_ite_two_pow_lt y)
    refine ⟨fun z z' hzz' => ?_, funext fun z => ?_⟩
    · rw [← Fin.append_castAdd_natAdd (f := z),
        ← Fin.append_castAdd_natAdd (f := z')]
      exact (hHy _ fun i => hzz' _).trans (hH (fun i => hzz' _) _)
    · rw [← Fin.append_castAdd_natAdd (f := z),
        booleanFunctionDual_apply_eq_compl, compl_finAppend]
      have := congrFun (hHd fun i => z (Fin.natAdd n i))
        (fun i => z (Fin.castAdd k i))ᶜ
      beta_reduce at this
      rw [this, booleanFunctionDual_apply_eq_compl, compl_compl, compl_compl]

/-- **Self-dual monotone concatenations.** The concatenation of a word `W` is
self-dual and monotone iff its first `2 ^ k` entries are monotone, increase
along the edges `i → i + 2 ^ j` of the cube (bit `j` of `i` clear), and satisfy
`W (2 ^ k - 1 - i) = (W i)*`. -/
theorem isSelfDualMonotone_booleanCubeConcat_iff (n k : ℕ)
    (W : List ((Fin n → Bool) → Bool)) :
    IsSelfDualMonotone (n + k) (booleanCubeConcat n k W) ↔
      (∀ i < 2 ^ k, Monotone (W.getD i fun _ => false)) ∧
      (∀ i < 2 ^ k, ∀ j < k, i.testBit j = false →
        (W.getD i fun _ => false) ≤ W.getD (i + 2 ^ j) fun _ => false) ∧
      ∀ i < 2 ^ k, (W.getD (2 ^ k - 1 - i) fun _ => false) =
        booleanFunctionDual n (W.getD i fun _ => false) := by
  rw [isSelfDualMonotone_add_iff]
  refine and_congr (forall₂_congr fun i hi => by
      rw [booleanCubeBlock_booleanCubeConcat _ _ _ hi])
    (and_congr (forall₂_congr fun i hi => forall₂_congr fun j hj =>
      imp_congr_right fun hb => by
        rw [booleanCubeBlock_booleanCubeConcat _ _ _ hi,
          booleanCubeBlock_booleanCubeConcat _ _ _
            (add_two_pow_lt_of_testBit_eq_false hi ⟨j, hj⟩ hb)])
      (forall₂_congr fun i hi => by
        rw [booleanCubeBlock_booleanCubeConcat _ _ _ hi,
          booleanCubeBlock_booleanCubeConcat _ _ _
            (by have := Nat.one_le_two_pow (n := k); omega)]))

/-- For a self-dual monotone `F`, the block at `2 ^ k - 1 - i` is the dual of
the block at `i`. -/
theorem booleanCubeBlock_eq_booleanFunctionDual {n k : ℕ}
    {F : (Fin (n + k) → Bool) → Bool} (hF : IsSelfDualMonotone (n + k) F)
    {i i' : ℕ} (hi : i < 2 ^ k) (hi' : 2 ^ k - 1 - i = i') :
    booleanCubeBlock n k F i' =
      booleanFunctionDual n (booleanCubeBlock n k F i) :=
  hi' ▸ ((isSelfDualMonotone_add_iff F).1 hF).2.2 i hi

/-! ### One and two new variables -/

/-- For monotone `b ≤ b*`, the concatenation `b · b*` is self-dual and
monotone. -/
theorem isSelfDualMonotone_booleanCubeConcat_one {n : ℕ}
    {b : (Fin n → Bool) → Bool} (hb : Monotone b)
    (hbd : b ≤ booleanFunctionDual n b) :
    IsSelfDualMonotone (n + 1)
      (booleanCubeConcat n 1 [b, booleanFunctionDual n b]) := by
  refine (isSelfDualMonotone_booleanCubeConcat_iff n 1 _).2
    ⟨fun i hi => ?_, fun i hi j hj hij => ?_, fun i hi => ?_⟩
  · interval_cases i
    · exact hb
    · exact monotone_booleanFunctionDual hb
  · interval_cases i <;> interval_cases j
    · exact hbd
    · exact absurd hij (by decide)
  · interval_cases i <;> simp

/-- A self-dual monotone `F` on `n + 1` variables is `b · b*` for its block
`b` at `0`, which is monotone with `b ≤ b*`. -/
theorem isSelfDualMonotone_succ_eq_booleanCubeConcat {n : ℕ}
    {F : (Fin (n + 1) → Bool) → Bool} (hF : IsSelfDualMonotone (n + 1) F) :
    Monotone (booleanCubeBlock n 1 F 0) ∧
      booleanCubeBlock n 1 F 0 ≤
        booleanFunctionDual n (booleanCubeBlock n 1 F 0) ∧
      F = booleanCubeConcat n 1 [booleanCubeBlock n 1 F 0,
        booleanFunctionDual n (booleanCubeBlock n 1 F 0)] := by
  have hD : booleanCubeBlock n 1 F 1 =
      booleanFunctionDual n (booleanCubeBlock n 1 F 0) :=
    booleanCubeBlock_eq_booleanFunctionDual hF (i := 0) (by norm_num)
      (by norm_num)
  refine ⟨monotone_booleanCubeBlock hF.1 0,
    hD ▸ booleanCubeBlock_le_booleanCubeBlock hF.1 (by decide),
    (eq_booleanCubeConcat_iff _ _).2 fun i hi => ?_⟩
  interval_cases i
  · rfl
  · exact hD.symm

open Classical in
/-- **Theorem 6.** For `n ≥ 0`, `λ_{n+1} = |{b ∈ D_n | b ≤ b*}|`, and
`λ_{n+1} = ∑_{b ∈ R_n, b ≤ b*} γ(b)`.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual
Monotone Boolean Functions*, Journal of Integer Sequences 28 (2025), Article
25.6.5, Theorem 6 (`jis-2025-25.6.5-thm-6`).

Proves `Wanted` entry `card_selfDualMonotone_succ`. -/
theorem card_selfDualMonotone_succ (n : ℕ) :
    Nat.card {f : (Fin (n + 1) → Bool) → Bool //
        IsSelfDualMonotone (n + 1) f} =
        Nat.card {b : (Fin n → Bool) → Bool //
          Monotone b ∧ b ≤ booleanFunctionDual n b} ∧
      ∀ reps : Finset ((Fin n → Bool) → Bool), (∀ b ∈ reps, Monotone b) →
        (∀ f : (Fin n → Bool) → Bool, Monotone f →
          ∃! b, b ∈ reps ∧ ∃ π : Equiv.Perm (Fin n),
            f = fun x => b (x ∘ π)) →
        Nat.card {f : (Fin (n + 1) → Bool) → Bool //
            IsSelfDualMonotone (n + 1) f} =
          ∑ b ∈ reps with b ≤ booleanFunctionDual n b,
            Nat.card {g : (Fin n → Bool) → Bool //
              ∃ π : Equiv.Perm (Fin n), g = fun x => b (x ∘ π)} := by
  have h : Nat.card {f : (Fin (n + 1) → Bool) → Bool //
        IsSelfDualMonotone (n + 1) f} =
      Nat.card {b : (Fin n → Bool) → Bool //
        Monotone b ∧ b ≤ booleanFunctionDual n b} :=
    Nat.card_congr
      { toFun := fun F => ⟨booleanCubeBlock n 1 F.1 0,
          (isSelfDualMonotone_succ_eq_booleanCubeConcat F.2).1,
          (isSelfDualMonotone_succ_eq_booleanCubeConcat F.2).2.1⟩
        invFun := fun b =>
          ⟨_, isSelfDualMonotone_booleanCubeConcat_one b.2.1 b.2.2⟩
        left_inv := fun F => Subtype.ext
          (isSelfDualMonotone_succ_eq_booleanCubeConcat F.2).2.2.symm
        right_inv := fun b => Subtype.ext
          (booleanCubeBlock_booleanCubeConcat n 1 _ (by norm_num)) }
  refine ⟨h, fun reps hreps huniq => ?_⟩
  rw [h]
  convert card_monotone_and_eq_sum_reps (fun b => b ≤ booleanFunctionDual n b)
    (fun b π =>
      comp_perm_le_comp_perm_iff (f := b) (g := booleanFunctionDual n b) π)
    reps hreps huniq

/-- **Corollary 7.** For `n ≥ 0`, `λ_{n+1} ≤ d_n`.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual
Monotone Boolean Functions*, Journal of Integer Sequences 28 (2025), Article
25.6.5, Corollary 7 (`jis-2025-25.6.5-cor-7`).

Proves `Wanted` entry `card_selfDualMonotone_succ_le`. -/
theorem card_selfDualMonotone_succ_le (n : ℕ) :
    Nat.card {f : (Fin (n + 1) → Bool) → Bool //
        IsSelfDualMonotone (n + 1) f} ≤
      Nat.card {f : (Fin n → Bool) → Bool // Monotone f} := by
  rw [(card_selfDualMonotone_succ n).1]
  exact Nat.card_le_card_of_injective (Subtype.map id fun _ h => h.1)
    (Subtype.map_injective _ Function.injective_id)

set_option linter.unusedVariables false in
open Classical in
/-- **Theorem 9.** For `n ≥ 1`,
`λ_{n+1} = λ_n + ∑_{b ∈ R_n, ℓ(b) < 2^{n-1}, b ≤ b*} γ(b)` and
`λ_{n+1} ≤ λ_n + (d_n - λ_n) / 2 = (d_n + λ_n) / 2`.

Stated for `n ≥ 1` (for `n = 0`, `2^{n-1}` is not an integer); the bound is
stated as `2 λ_{n+1} ≤ d_n + λ_n`; `ℓ(b) < 2^{n-1}` is `2 ℓ(b) < 2ⁿ`.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual
Monotone Boolean Functions*, Journal of Integer Sequences 28 (2025), Article
25.6.5, Theorem 9 (`jis-2025-25.6.5-thm-9`).

Proves `Wanted` entry `card_selfDualMonotone_succ_eq_add`. -/
theorem card_selfDualMonotone_succ_eq_add (n : ℕ) (hn : 1 ≤ n) :
    (∀ reps : Finset ((Fin n → Bool) → Bool), (∀ b ∈ reps, Monotone b) →
        (∀ f : (Fin n → Bool) → Bool, Monotone f →
          ∃! b, b ∈ reps ∧ ∃ π : Equiv.Perm (Fin n),
            f = fun x => b (x ∘ π)) →
        Nat.card {f : (Fin (n + 1) → Bool) → Bool //
            IsSelfDualMonotone (n + 1) f} =
          Nat.card {f : (Fin n → Bool) → Bool // IsSelfDualMonotone n f} +
            ∑ b ∈ reps with
                2 * Nat.card {x // b x = true} < 2 ^ n ∧
                  b ≤ booleanFunctionDual n b,
              Nat.card {g : (Fin n → Bool) → Bool //
                ∃ π : Equiv.Perm (Fin n), g = fun x => b (x ∘ π)}) ∧
      2 * Nat.card {f : (Fin (n + 1) → Bool) → Bool //
          IsSelfDualMonotone (n + 1) f} ≤
        Nat.card {f : (Fin n → Bool) → Bool // Monotone f} +
          Nat.card {f : (Fin n → Bool) → Bool // IsSelfDualMonotone n f} := by
  have hsplit : Nat.card {f : (Fin (n + 1) → Bool) → Bool //
        IsSelfDualMonotone (n + 1) f} =
      Nat.card {f : (Fin n → Bool) → Bool // IsSelfDualMonotone n f} +
        Nat.card {b : (Fin n → Bool) → Bool // Monotone b ∧
          (2 * Nat.card {x // b x = true} < 2 ^ n ∧
            b ≤ booleanFunctionDual n b)} := by
    rw [(card_selfDualMonotone_succ n).1,
      natCard_subtype_eq_add _
        fun b => 2 * Nat.card {x // b x = true} < 2 ^ n, add_comm]
    congr 1
    · refine Nat.card_congr (Equiv.subtypeEquivRight fun b => ?_)
      have hw := monotoneBooleanFunction_weight_dual n b
      refine ⟨fun ⟨⟨hm, hle⟩, hlt⟩ => ⟨hm, (hw hm).2.1
          (by have := (hw hm).1 hle; omega) hle⟩,
        fun ⟨hm, heq⟩ => ⟨⟨hm, heq.le⟩, by have := (hw hm).2.2.1 heq; omega⟩⟩
    · exact Nat.card_congr (Equiv.subtypeEquivRight fun b => by tauto)
  refine ⟨fun reps hreps huniq => ?_, ?_⟩
  · rw [hsplit]
    congr 1
    convert card_monotone_and_eq_sum_reps
      (fun b => 2 * Nat.card {x // b x = true} < 2 ^ n ∧
        b ≤ booleanFunctionDual n b)
      (fun b π => by
        rw [card_true_comp_perm]
        exact and_congr_right fun _ =>
          comp_perm_le_comp_perm_iff (f := b) (g := booleanFunctionDual n b) π)
      reps hreps huniq
  · have hA : Nat.card {b : (Fin n → Bool) → Bool // Monotone b ∧
          (2 * Nat.card {x // b x = true} < 2 ^ n ∧
            b ≤ booleanFunctionDual n b)} ≤
        Nat.card {f : (Fin n → Bool) → Bool //
          Monotone f ∧ 2 * Nat.card {x // f x = true} < 2 ^ n} :=
      Nat.card_le_card_of_injective
        (Subtype.map id fun _ h => ⟨h.1, h.2.1⟩)
        (Subtype.map_injective _ Function.injective_id)
    have hE : Nat.card {f : (Fin n → Bool) → Bool // IsSelfDualMonotone n f} ≤
        Nat.card {f : (Fin n → Bool) → Bool //
          (Monotone f ∧ ¬2 * Nat.card {x // f x = true} < 2 ^ n) ∧
            2 * Nat.card {x // f x = true} = 2 ^ n} :=
      Nat.card_le_card_of_injective (Subtype.map id fun f h => by
        have := (monotoneBooleanFunction_weight_dual n f h.1).2.2.1 h.2
        simp only [id]
        exact ⟨⟨h.1, by omega⟩, this⟩)
        (Subtype.map_injective _ Function.injective_id)
    have hG : Nat.card {f : (Fin n → Bool) → Bool //
          (Monotone f ∧ ¬2 * Nat.card {x // f x = true} < 2 ^ n) ∧
            ¬2 * Nat.card {x // f x = true} = 2 ^ n} =
        Nat.card {f : (Fin n → Bool) → Bool //
          Monotone f ∧ 2 ^ n < 2 * Nat.card {x // f x = true}} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun f => by
        constructor
        · rintro ⟨⟨hm, h1⟩, h2⟩
          exact ⟨hm, by omega⟩
        · rintro ⟨hm, h1⟩
          exact ⟨⟨hm, by omega⟩, by omega⟩)
    have hd := natCard_subtype_eq_add
      (fun f : (Fin n → Bool) → Bool => Monotone f)
      fun f => 2 * Nat.card {x // f x = true} < 2 ^ n
    rw [natCard_subtype_eq_add (fun f : (Fin n → Bool) → Bool =>
      Monotone f ∧ ¬2 * Nat.card {x // f x = true} < 2 ^ n)
      fun f => 2 * Nat.card {x // f x = true} = 2 ^ n, hG] at hd
    have hLG := card_weight_lt_eq_card_weight_gt n
    rw [hsplit, hd]
    omega

/-- For monotone `b, z` with `b | b* ≤ z`, the concatenation `z* · b · b* · z`
is self-dual and monotone. -/
theorem isSelfDualMonotone_booleanCubeConcat_two {n : ℕ}
    {b z : (Fin n → Bool) → Bool} (hb : Monotone b) (hz : Monotone z)
    (h : b ⊔ booleanFunctionDual n b ≤ z) :
    IsSelfDualMonotone (n + 2) (booleanCubeConcat n 2
      [booleanFunctionDual n z, b, booleanFunctionDual n b, z]) := by
  rw [sup_le_iff] at h
  refine (isSelfDualMonotone_booleanCubeConcat_iff n 2 _).2
    ⟨fun i hi => ?_, fun i hi j hj hij => ?_, fun i hi => ?_⟩
  · interval_cases i <;>
      simp only [List.getD_cons_succ, List.getD_cons_zero] <;>
      first | assumption | exact monotone_booleanFunctionDual ‹_›
  · interval_cases i <;> interval_cases j <;>
      first
      | exact absurd hij (by decide)
      | (simp only [Nat.reducePow, Nat.reduceAdd, List.getD_cons_succ,
           List.getD_cons_zero]
         first
         | exact h.1
         | exact h.2
         | exact antitone_booleanFunctionDual n h.1
         | exact booleanFunctionDual_le_comm.1 h.2)
  · interval_cases i <;> simp

/-- A self-dual monotone `F` on `n + 2` variables is `z* · b · b* · z` for its
blocks `b` at `1` and `z` at `3`, which are monotone with `b | b* ≤ z`. -/
theorem isSelfDualMonotone_add_two_eq_booleanCubeConcat {n : ℕ}
    {F : (Fin (n + 2) → Bool) → Bool} (hF : IsSelfDualMonotone (n + 2) F) :
    Monotone (booleanCubeBlock n 2 F 1) ∧
      Monotone (booleanCubeBlock n 2 F 3) ∧
      booleanCubeBlock n 2 F 1 ⊔
          booleanFunctionDual n (booleanCubeBlock n 2 F 1) ≤
        booleanCubeBlock n 2 F 3 ∧
      F = booleanCubeConcat n 2
        [booleanFunctionDual n (booleanCubeBlock n 2 F 3),
          booleanCubeBlock n 2 F 1,
          booleanFunctionDual n (booleanCubeBlock n 2 F 1),
          booleanCubeBlock n 2 F 3] := by
  have hD0 : booleanCubeBlock n 2 F 0 =
      booleanFunctionDual n (booleanCubeBlock n 2 F 3) :=
    booleanCubeBlock_eq_booleanFunctionDual hF (i := 3) (by norm_num)
      (by norm_num)
  have hD2 : booleanCubeBlock n 2 F 2 =
      booleanFunctionDual n (booleanCubeBlock n 2 F 1) :=
    booleanCubeBlock_eq_booleanFunctionDual hF (i := 1) (by norm_num)
      (by norm_num)
  refine ⟨monotone_booleanCubeBlock hF.1 1, monotone_booleanCubeBlock hF.1 3,
    sup_le (booleanCubeBlock_le_booleanCubeBlock hF.1 (by decide))
      (hD2 ▸ booleanCubeBlock_le_booleanCubeBlock hF.1 (by decide)),
    (eq_booleanCubeConcat_iff _ _).2 fun i hi => ?_⟩
  interval_cases i
  · exact hD0.symm
  · rfl
  · exact hD2.symm
  · rfl

open Classical in
/-- `λ_{n+2} = ∑_{b ∈ D_n} re(b | b*, ⊤)`, the first part of Theorem 10. -/
theorem card_selfDualMonotone_add_two_eq_sum (n : ℕ) :
    Nat.card {f : (Fin (n + 2) → Bool) → Bool //
        IsSelfDualMonotone (n + 2) f} =
      ∑ b ∈ Finset.univ.filter (fun b : (Fin n → Bool) → Bool => Monotone b),
        Nat.card {z : (Fin n → Bool) → Bool //
          Monotone z ∧ b ⊔ booleanFunctionDual n b ≤ z} := by
  have e : Nat.card (Σ b : {b : (Fin n → Bool) → Bool // Monotone b},
      {z : (Fin n → Bool) → Bool //
        Monotone z ∧ b.1 ⊔ booleanFunctionDual n b.1 ≤ z}) =
      Nat.card {f : (Fin (n + 2) → Bool) → Bool //
        IsSelfDualMonotone (n + 2) f} := by
    refine Nat.card_congr (Equiv.ofBijective (fun t => ⟨_,
      isSelfDualMonotone_booleanCubeConcat_two t.1.2 t.2.2.1 t.2.2.2⟩)
      ⟨?_, ?_⟩)
    · rintro ⟨⟨b, hb⟩, ⟨z, hz⟩⟩ ⟨⟨b', hb'⟩, ⟨z', hz'⟩⟩ h
      have h' := congrArg Subtype.val h
      have e1 := congrArg (booleanCubeBlock n 2 · 1) h'
      have e3 := congrArg (booleanCubeBlock n 2 · 3) h'
      simp only [
        booleanCubeBlock_booleanCubeConcat n 2 _ (by norm_num : 1 < 2 ^ 2),
        booleanCubeBlock_booleanCubeConcat n 2 _ (by norm_num : 3 < 2 ^ 2),
        List.getD_cons_succ, List.getD_cons_zero] at e1 e3
      subst e1 e3
      rfl
    · rintro ⟨F, hF⟩
      obtain ⟨h1, h3, h13, hFeq⟩ :=
        isSelfDualMonotone_add_two_eq_booleanCubeConcat hF
      exact ⟨⟨⟨_, h1⟩, ⟨_, h3, h13⟩⟩, Subtype.ext hFeq.symm⟩
  rw [← e, Nat.card_sigma]
  exact (Finset.sum_subtype (univ.filter fun b => Monotone b)
    (p := fun b => Monotone b) (fun b => by simp)
    fun b => Nat.card {z : (Fin n → Bool) → Bool //
      Monotone z ∧ b ⊔ booleanFunctionDual n b ≤ z}).symm

/-- `re(b | b*, ⊤)` is invariant under relabelling the variables of `b`. -/
theorem card_monotone_sup_dual_le_comp_perm {n : ℕ}
    (b : (Fin n → Bool) → Bool) (π : Equiv.Perm (Fin n)) :
    Nat.card {z : (Fin n → Bool) → Bool // Monotone z ∧
        (fun x => b (x ∘ π)) ⊔ booleanFunctionDual n (fun x => b (x ∘ π)) ≤
          z} =
      Nat.card {z : (Fin n → Bool) → Bool //
        Monotone z ∧ b ⊔ booleanFunctionDual n b ≤ z} := by
  refine (Nat.card_congr ((booleanFunctionPerm n π).toEquiv.subtypeEquiv
    fun z => ?_)).symm
  rw [← booleanFunctionDual_comp_perm]
  change _ ↔ Monotone (booleanFunctionPerm n π z) ∧
    booleanFunctionPerm n π b ⊔
        booleanFunctionPerm n π (booleanFunctionDual n b) ≤
      booleanFunctionPerm n π z
  rw [← map_sup, OrderIso.le_iff_le, booleanFunctionPerm_apply,
    monotone_comp_perm_iff]

open Classical in
/-- **Theorem 10.** For `n ≥ 0`, `λ_{n+2}` is the number of pairs
`b, d ∈ D_n` with `d ≥ b | b*`: `λ_{n+2} = ∑_{b ∈ D_n} re(b | b*, ⊤)`, and
`λ_{n+2} = ∑_{b ∈ R_n} γ(b) re(b | b*, ⊤)`.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual
Monotone Boolean Functions*, Journal of Integer Sequences 28 (2025), Article
25.6.5, Theorem 10 (`jis-2025-25.6.5-thm-10`).

Proves `Wanted` entry `card_selfDualMonotone_add_two`. -/
theorem card_selfDualMonotone_add_two (n : ℕ) :
    Nat.card {f : (Fin (n + 2) → Bool) → Bool //
        IsSelfDualMonotone (n + 2) f} =
        ∑ b ∈ Finset.univ.filter
            (fun b : (Fin n → Bool) → Bool => Monotone b),
          Nat.card {z : (Fin n → Bool) → Bool //
            Monotone z ∧ b ⊔ booleanFunctionDual n b ≤ z} ∧
      ∀ reps : Finset ((Fin n → Bool) → Bool), (∀ b ∈ reps, Monotone b) →
        (∀ f : (Fin n → Bool) → Bool, Monotone f →
          ∃! b, b ∈ reps ∧ ∃ π : Equiv.Perm (Fin n),
            f = fun x => b (x ∘ π)) →
        Nat.card {f : (Fin (n + 2) → Bool) → Bool //
            IsSelfDualMonotone (n + 2) f} =
          ∑ b ∈ reps, Nat.card {g : (Fin n → Bool) → Bool //
              ∃ π : Equiv.Perm (Fin n), g = fun x => b (x ∘ π)} *
            Nat.card {z : (Fin n → Bool) → Bool //
              Monotone z ∧ b ⊔ booleanFunctionDual n b ≤ z} :=
  ⟨card_selfDualMonotone_add_two_eq_sum n, fun reps hreps huniq => by
    rw [card_selfDualMonotone_add_two_eq_sum n]
    exact sum_monotone_eq_sum_reps _ card_monotone_sup_dual_le_comp_perm reps
      hreps huniq⟩

/-- **Corollary 11.** For `n ≥ 0`, `λ_{n+2} ≥ d_n`.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual
Monotone Boolean Functions*, Journal of Integer Sequences 28 (2025), Article
25.6.5, Corollary 11 (`jis-2025-25.6.5-cor-11`).

Proves `Wanted` entry `le_card_selfDualMonotone_add_two`. -/
theorem le_card_selfDualMonotone_add_two (n : ℕ) :
    Nat.card {f : (Fin n → Bool) → Bool // Monotone f} ≤
      Nat.card {f : (Fin (n + 2) → Bool) → Bool //
        IsSelfDualMonotone (n + 2) f} := by
  classical
  rw [card_selfDualMonotone_add_two_eq_sum, Nat.card_eq_fintype_card,
    Fintype.card_subtype, card_eq_sum_ones]
  refine sum_le_sum fun b _ => ?_
  have : Nonempty {z : (Fin n → Bool) → Bool //
      Monotone z ∧ b ⊔ booleanFunctionDual n b ≤ z} :=
    ⟨⟨⊤, monotone_const, le_top⟩⟩
  exact Nat.card_pos

/-! ### Four new variables -/

/-- The concatenation `h*·g*·f*·a·e*·b·c·d·d*·c*·b*·e·a*·f·g·h` is self-dual
and monotone under the hypotheses of Theorem 12, without the redundant bound
`a|b|c|a*|b*|c* ≤ h`. -/
theorem isSelfDualMonotone_booleanCubeConcat_four {n : ℕ}
    {a b c d e f g h : (Fin n → Bool) → Bool}
    (ha : Monotone a) (hb : Monotone b) (hc : Monotone c) (hd : Monotone d)
    (he : Monotone e) (hf : Monotone f) (hg : Monotone g) (hh : Monotone h)
    (hd₁ : a ⊔ b ⊔ c ≤ d) (hd₂ : d ≤ h)
    (he₁ : a ⊔ booleanFunctionDual n b ⊔ booleanFunctionDual n c ≤ e)
    (he₂ : e ≤ h)
    (hf₁ : b ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n c ≤ f)
    (hf₂ : f ≤ h)
    (hg₁ : c ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n b ≤ g)
    (hg₂ : g ≤ h) :
    IsSelfDualMonotone (n + 4) (booleanCubeConcat n 4
      [booleanFunctionDual n h, booleanFunctionDual n g,
        booleanFunctionDual n f, a, booleanFunctionDual n e, b, c, d,
        booleanFunctionDual n d, booleanFunctionDual n c,
        booleanFunctionDual n b, e, booleanFunctionDual n a, f, g, h]) := by
  simp only [sup_le_iff] at hd₁ he₁ hf₁ hg₁
  obtain ⟨⟨had, hbd⟩, hcd⟩ := hd₁
  obtain ⟨⟨hae, hbe⟩, hce⟩ := he₁
  obtain ⟨⟨hbf, haf⟩, hcf⟩ := hf₁
  obtain ⟨⟨hcg, hag⟩, hbg⟩ := hg₁
  refine (isSelfDualMonotone_booleanCubeConcat_iff n 4 _).2
    ⟨fun i hi => ?_, fun i hi j hj hij => ?_, fun i hi => ?_⟩
  · interval_cases i <;>
      simp only [List.getD_cons_succ, List.getD_cons_zero] <;>
      first | assumption | exact monotone_booleanFunctionDual ‹_›
  · interval_cases i <;> interval_cases j <;>
      first
      | exact absurd hij (by decide)
      | (simp only [Nat.reducePow, Nat.reduceAdd, List.getD_cons_succ,
           List.getD_cons_zero]
         first
         | assumption
         | exact antitone_booleanFunctionDual n ‹_›
         | exact booleanFunctionDual_le_comm.1 ‹_›)
  · interval_cases i <;> simp

/-- **Theorem 12.** For `a, b, c ∈ D_n`, `h ∈ D_n` with `h ≥ a|b|c|a*|b*|c*`,
and `d, e, f, g ∈ D_n` with `a|b|c ≤ d ≤ h`, `a|b*|c* ≤ e ≤ h`,
`b|a*|c* ≤ f ≤ h`, `c|a*|b* ≤ g ≤ h`, the concatenation
`h*·g*·f*·a·e*·b·c·d·d*·c*·b*·e·a*·f·g·h` is a self-dual function in
`D_{n+4}`; and every self-dual function in `D_{n+4}` is of this form.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual
Monotone Boolean Functions*, Journal of Integer Sequences 28 (2025), Article
25.6.5, Theorem 12 (`jis-2025-25.6.5-thm-12`).

Proves `Wanted` entry `selfDualMonotone_add_four_iff_concat`. -/
theorem selfDualMonotone_add_four_iff_concat (n : ℕ) :
    (∀ a b c d e f g h : (Fin n → Bool) → Bool,
      Monotone a → Monotone b → Monotone c → Monotone d → Monotone e →
      Monotone f → Monotone g → Monotone h →
      a ⊔ b ⊔ c ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n b ⊔
        booleanFunctionDual n c ≤ h →
      a ⊔ b ⊔ c ≤ d → d ≤ h →
      a ⊔ booleanFunctionDual n b ⊔ booleanFunctionDual n c ≤ e → e ≤ h →
      b ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n c ≤ f → f ≤ h →
      c ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n b ≤ g → g ≤ h →
      IsSelfDualMonotone (n + 4) (booleanCubeConcat n 4
        [booleanFunctionDual n h, booleanFunctionDual n g,
          booleanFunctionDual n f, a, booleanFunctionDual n e, b, c, d,
          booleanFunctionDual n d, booleanFunctionDual n c,
          booleanFunctionDual n b, e, booleanFunctionDual n a, f, g, h])) ∧
    ∀ F : (Fin (n + 4) → Bool) → Bool, IsSelfDualMonotone (n + 4) F →
      ∃ a b c d e f g h : (Fin n → Bool) → Bool,
        Monotone a ∧ Monotone b ∧ Monotone c ∧ Monotone d ∧ Monotone e ∧
        Monotone f ∧ Monotone g ∧ Monotone h ∧
        a ⊔ b ⊔ c ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n b ⊔
          booleanFunctionDual n c ≤ h ∧
        a ⊔ b ⊔ c ≤ d ∧ d ≤ h ∧
        a ⊔ booleanFunctionDual n b ⊔ booleanFunctionDual n c ≤ e ∧ e ≤ h ∧
        b ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n c ≤ f ∧ f ≤ h ∧
        c ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n b ≤ g ∧ g ≤ h ∧
        F = booleanCubeConcat n 4
          [booleanFunctionDual n h, booleanFunctionDual n g,
            booleanFunctionDual n f, a, booleanFunctionDual n e, b, c, d,
            booleanFunctionDual n d, booleanFunctionDual n c,
            booleanFunctionDual n b, e, booleanFunctionDual n a, f, g, h] := by
  refine ⟨fun a b c d e f g h ha hb hc hd he hf hg hh _ hd₁ hd₂ he₁ he₂ hf₁
    hf₂ hg₁ hg₂ => isSelfDualMonotone_booleanCubeConcat_four ha hb hc hd he
      hf hg hh hd₁ hd₂ he₁ he₂ hf₁ hf₂ hg₁ hg₂, fun F hF => ?_⟩
  set B := booleanCubeBlock n 4 F with hB
  have hle : ∀ {i i' : ℕ},
      (∀ m < 4, i.testBit m = true → i'.testBit m = true) → B i ≤ B i' :=
    fun h => booleanCubeBlock_le_booleanCubeBlock hF.1 h
  have hD : ∀ {i i' : ℕ}, i < 2 ^ 4 → 2 ^ 4 - 1 - i = i' →
      B i' = booleanFunctionDual n (B i) :=
    fun hi h => booleanCubeBlock_eq_booleanFunctionDual hF hi h
  have h0 : B 0 = booleanFunctionDual n (B 15) := hD (by norm_num) (by norm_num)
  have h1 : B 1 = booleanFunctionDual n (B 14) := hD (by norm_num) (by norm_num)
  have h2 : B 2 = booleanFunctionDual n (B 13) := hD (by norm_num) (by norm_num)
  have h4 : B 4 = booleanFunctionDual n (B 11) := hD (by norm_num) (by norm_num)
  have h8 : B 8 = booleanFunctionDual n (B 7) := hD (by norm_num) (by norm_num)
  have h9 : B 9 = booleanFunctionDual n (B 6) := hD (by norm_num) (by norm_num)
  have h10 : B 10 = booleanFunctionDual n (B 5) :=
    hD (by norm_num) (by norm_num)
  have h12 : B 12 = booleanFunctionDual n (B 3) :=
    hD (by norm_num) (by norm_num)
  have hm := monotone_booleanCubeBlock hF.1 (k := 4)
  refine ⟨B 3, B 5, B 6, B 7, B 11, B 13, B 14, B 15, hm 3, hm 5, hm 6, hm 7,
    hm 11, hm 13, hm 14, hm 15, ?_, ?_, hle (by decide), ?_, hle (by decide),
    ?_, hle (by decide), ?_, hle (by decide),
    (eq_booleanCubeConcat_iff _ _).2 fun i hi => ?_⟩
  · rw [← h12, ← h10, ← h9]
    exact sup_le (sup_le (sup_le (sup_le (sup_le (hle (by decide))
      (hle (by decide))) (hle (by decide))) (hle (by decide)))
      (hle (by decide))) (hle (by decide))
  · exact sup_le (sup_le (hle (by decide)) (hle (by decide))) (hle (by decide))
  · rw [← h10, ← h9]
    exact sup_le (sup_le (hle (by decide)) (hle (by decide))) (hle (by decide))
  · rw [← h12, ← h9]
    exact sup_le (sup_le (hle (by decide)) (hle (by decide))) (hle (by decide))
  · rw [← h12, ← h10]
    exact sup_le (sup_le (hle (by decide)) (hle (by decide))) (hle (by decide))
  · interval_cases i <;>
      simp only [List.getD_cons_succ, List.getD_cons_zero] <;>
      first
        | rfl | exact h0.symm | exact h1.symm | exact h2.symm | exact h4.symm
        | exact h8.symm | exact h9.symm | exact h10.symm | exact h12.symm

/-- The blocks of `h*·g*·f*·a·e*·b·c·d·d*·c*·b*·e·a*·f·g·h` at the indices of
`a, b, c, d, e, f, g, h`. -/
private theorem booleanCubeBlock_booleanCubeConcat_four (n : ℕ)
    (a b c d e f g h : (Fin n → Bool) → Bool) :
    let F := booleanCubeConcat n 4
      [booleanFunctionDual n h, booleanFunctionDual n g,
        booleanFunctionDual n f, a, booleanFunctionDual n e, b, c, d,
        booleanFunctionDual n d, booleanFunctionDual n c,
        booleanFunctionDual n b, e, booleanFunctionDual n a, f, g, h]
    booleanCubeBlock n 4 F 3 = a ∧ booleanCubeBlock n 4 F 5 = b ∧
      booleanCubeBlock n 4 F 6 = c ∧ booleanCubeBlock n 4 F 7 = d ∧
      booleanCubeBlock n 4 F 11 = e ∧ booleanCubeBlock n 4 F 13 = f ∧
      booleanCubeBlock n 4 F 14 = g ∧ booleanCubeBlock n 4 F 15 = h := by
  intro F
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact (booleanCubeBlock_booleanCubeConcat n 4 _ (by norm_num)).trans rfl

open Classical in
/-- **Theorem 13.** `λ_{n+4} = ∑_{a,b,c ∈ D_n} ∑_{h ∈ D_n, h ≥ a|b|c|a*|b*|c*}
re(a|b|c, h) re(a|b*|c*, h) re(b|a*|c*, h) re(c|a*|b*, h)`.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual
Monotone Boolean Functions*, Journal of Integer Sequences 28 (2025), Article
25.6.5, Theorem 13 (`jis-2025-25.6.5-thm-13`).

Proves `Wanted` entry `card_selfDualMonotone_add_four`. -/
theorem card_selfDualMonotone_add_four (n : ℕ) :
    Nat.card {F : (Fin (n + 4) → Bool) → Bool //
        IsSelfDualMonotone (n + 4) F} =
      ∑ a ∈ Finset.univ.filter (fun b : (Fin n → Bool) → Bool => Monotone b),
      ∑ b ∈ Finset.univ.filter (fun b : (Fin n → Bool) → Bool => Monotone b),
      ∑ c ∈ Finset.univ.filter (fun b : (Fin n → Bool) → Bool => Monotone b),
      ∑ h ∈ Finset.univ.filter (fun h : (Fin n → Bool) → Bool => Monotone h ∧
          a ⊔ b ⊔ c ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n b ⊔
            booleanFunctionDual n c ≤ h),
        Nat.card {z : (Fin n → Bool) → Bool //
          Monotone z ∧ a ⊔ b ⊔ c ≤ z ∧ z ≤ h} *
        Nat.card {z : (Fin n → Bool) → Bool // Monotone z ∧
          a ⊔ booleanFunctionDual n b ⊔ booleanFunctionDual n c ≤ z ∧
            z ≤ h} *
        Nat.card {z : (Fin n → Bool) → Bool // Monotone z ∧
          b ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n c ≤ z ∧
            z ≤ h} *
        Nat.card {z : (Fin n → Bool) → Bool // Monotone z ∧
          c ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n b ≤ z ∧
            z ≤ h} := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, ← card_product,
    ← card_sigma]
  have hB := booleanCubeBlock_booleanCubeConcat_four n
  refine card_nbij'
    (fun F => ⟨booleanCubeBlock n 4 F 3, booleanCubeBlock n 4 F 5,
      booleanCubeBlock n 4 F 6, booleanCubeBlock n 4 F 15,
      ((booleanCubeBlock n 4 F 7, booleanCubeBlock n 4 F 11),
        booleanCubeBlock n 4 F 13), booleanCubeBlock n 4 F 14⟩)
    (fun t => booleanCubeConcat n 4
      [booleanFunctionDual n t.2.2.2.1, booleanFunctionDual n t.2.2.2.2.2,
        booleanFunctionDual n t.2.2.2.2.1.2, t.1,
        booleanFunctionDual n t.2.2.2.2.1.1.2, t.2.1, t.2.2.1,
        t.2.2.2.2.1.1.1, booleanFunctionDual n t.2.2.2.2.1.1.1,
        booleanFunctionDual n t.2.2.1, booleanFunctionDual n t.2.1,
        t.2.2.2.2.1.1.2, booleanFunctionDual n t.1, t.2.2.2.2.1.2,
        t.2.2.2.2.2, t.2.2.2.1]) ?_ ?_ ?_ ?_
  · intro F hF
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hF
    obtain ⟨a, b, c, d, e, f, g, h, ha, hb, hc, hd, he, hf, hg, hh, hH, hd₁,
      hd₂, he₁, he₂, hf₁, hf₂, hg₁, hg₂, rfl⟩ :=
      (selfDualMonotone_add_four_iff_concat n).2 F hF
    obtain ⟨h3, h5, h6, h7, h11, h13, h14, h15⟩ := hB a b c d e f g h
    simp only [h3, h5, h6, h7, h11, h13, h14, h15, mem_coe, mem_sigma,
      mem_product, mem_filter, mem_univ, true_and]
    exact ⟨ha, hb, hc, ⟨hh, hH⟩, ⟨⟨⟨hd, hd₁, hd₂⟩, he, he₁, he₂⟩, hf, hf₁,
      hf₂⟩, hg, hg₁, hg₂⟩
  · rintro ⟨a, b, c, h, ⟨⟨d, e⟩, f⟩, g⟩ ht
    simp only [mem_coe, mem_sigma, mem_product, mem_filter, mem_univ,
      true_and, coe_filter, Set.mem_ofPred_eq] at ht ⊢
    obtain ⟨ha, hb, hc, ⟨hh, hH⟩, ⟨⟨⟨hd, hd₁, hd₂⟩, he, he₁, he₂⟩, hf, hf₁,
      hf₂⟩, hg, hg₁, hg₂⟩ := ht
    exact (selfDualMonotone_add_four_iff_concat n).1 a b c d e f g h ha hb hc
      hd he hf hg hh hH hd₁ hd₂ he₁ he₂ hf₁ hf₂ hg₁ hg₂
  · intro F hF
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hF
    obtain ⟨a, b, c, d, e, f, g, h, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, rfl⟩ := (selfDualMonotone_add_four_iff_concat n).2 F hF
    obtain ⟨h3, h5, h6, h7, h11, h13, h14, h15⟩ := hB a b c d e f g h
    simp only [h3, h5, h6, h7, h11, h13, h14, h15]
  · rintro ⟨a, b, c, h, ⟨⟨d, e⟩, f⟩, g⟩ -
    obtain ⟨h3, h5, h6, h7, h11, h13, h14, h15⟩ := hB a b c d e f g h
    simp only [h3, h5, h6, h7, h11, h13, h14, h15]

/-- **Theorem 14.** For `h ∈ D_n` with `h ≥ h*`, `a, b, c ∈ D_n` with
`h* ≤ a, b, c ≤ h`, and `d, e, f, g ∈ D_n` with `a|b|c ≤ d ≤ h`,
`a|b*|c* ≤ e ≤ h`, `b|a*|c* ≤ f ≤ h`, `c|a*|b* ≤ g ≤ h`, the concatenation
`h*·g*·f*·a·e*·b·c·d·d*·c*·b*·e·a*·f·g·h` is a self-dual function in
`D_{n+4}`; and every self-dual function in `D_{n+4}` is of this form.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual
Monotone Boolean Functions*, Journal of Integer Sequences 28 (2025), Article
25.6.5, Theorem 14 (`jis-2025-25.6.5-thm-14`).

Proves `Wanted` entry `selfDualMonotone_add_four_iff_concat_of_dual_le`. -/
theorem selfDualMonotone_add_four_iff_concat_of_dual_le (n : ℕ) :
    (∀ a b c d e f g h : (Fin n → Bool) → Bool,
      Monotone a → Monotone b → Monotone c → Monotone d → Monotone e →
      Monotone f → Monotone g → Monotone h →
      booleanFunctionDual n h ≤ h →
      booleanFunctionDual n h ≤ a → a ≤ h → booleanFunctionDual n h ≤ b →
      b ≤ h → booleanFunctionDual n h ≤ c → c ≤ h →
      a ⊔ b ⊔ c ≤ d → d ≤ h →
      a ⊔ booleanFunctionDual n b ⊔ booleanFunctionDual n c ≤ e → e ≤ h →
      b ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n c ≤ f → f ≤ h →
      c ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n b ≤ g → g ≤ h →
      IsSelfDualMonotone (n + 4) (booleanCubeConcat n 4
        [booleanFunctionDual n h, booleanFunctionDual n g,
          booleanFunctionDual n f, a, booleanFunctionDual n e, b, c, d,
          booleanFunctionDual n d, booleanFunctionDual n c,
          booleanFunctionDual n b, e, booleanFunctionDual n a, f, g, h])) ∧
    ∀ F : (Fin (n + 4) → Bool) → Bool, IsSelfDualMonotone (n + 4) F →
      ∃ a b c d e f g h : (Fin n → Bool) → Bool,
        Monotone a ∧ Monotone b ∧ Monotone c ∧ Monotone d ∧ Monotone e ∧
        Monotone f ∧ Monotone g ∧ Monotone h ∧
        booleanFunctionDual n h ≤ h ∧
        booleanFunctionDual n h ≤ a ∧ a ≤ h ∧ booleanFunctionDual n h ≤ b ∧
        b ≤ h ∧ booleanFunctionDual n h ≤ c ∧ c ≤ h ∧
        a ⊔ b ⊔ c ≤ d ∧ d ≤ h ∧
        a ⊔ booleanFunctionDual n b ⊔ booleanFunctionDual n c ≤ e ∧ e ≤ h ∧
        b ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n c ≤ f ∧ f ≤ h ∧
        c ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n b ≤ g ∧ g ≤ h ∧
        F = booleanCubeConcat n 4
          [booleanFunctionDual n h, booleanFunctionDual n g,
            booleanFunctionDual n f, a, booleanFunctionDual n e, b, c, d,
            booleanFunctionDual n d, booleanFunctionDual n c,
            booleanFunctionDual n b, e, booleanFunctionDual n a, f, g, h] := by
  refine ⟨fun a b c d e f g h ha hb hc hd he hf hg hh _ hha hah hhb hbh hhc
    hch hd₁ hd₂ he₁ he₂ hf₁ hf₂ hg₁ hg₂ =>
      (selfDualMonotone_add_four_iff_concat n).1 a b c d e f g h ha hb hc hd
        he hf hg hh ?_ hd₁ hd₂ he₁ he₂ hf₁ hf₂ hg₁ hg₂, fun F hF => ?_⟩
  · exact sup_le (sup_le (sup_le (sup_le (sup_le hah hbh) hch)
      (booleanFunctionDual_le_comm.1 hha)) (booleanFunctionDual_le_comm.1 hhb))
      (booleanFunctionDual_le_comm.1 hhc)
  · obtain ⟨a, b, c, d, e, f, g, h, ha, hb, hc, hd, he, hf, hg, hh, hH, hd₁,
      hd₂, he₁, he₂, hf₁, hf₂, hg₁, hg₂, hF⟩ :=
      (selfDualMonotone_add_four_iff_concat n).2 F hF
    simp only [sup_le_iff] at hH
    obtain ⟨⟨⟨⟨⟨hah, hbh⟩, hch⟩, hdah⟩, hdbh⟩, hdch⟩ := hH
    exact ⟨a, b, c, d, e, f, g, h, ha, hb, hc, hd, he, hf, hg, hh,
      (booleanFunctionDual_le_comm.1 hdah).trans hah,
      booleanFunctionDual_le_comm.1 hdah, hah,
      booleanFunctionDual_le_comm.1 hdbh, hbh,
      booleanFunctionDual_le_comm.1 hdch, hch,
      hd₁, hd₂, he₁, he₂, hf₁, hf₂, hg₁, hg₂, hF⟩

/-! ### Maximal linked systems -/

/-- **Lemma 3 (L2).** For `n ≥ 1`, if `𝒰 ⊆ 𝒫(X)` is a maximal linked system
then for every `A ⊆ X` exactly one of `A` and `Aᶜ` lies in `𝒰`.

Part (L1), that a maximal linked system is an upset, is Mathlib's
`Set.Intersecting.isUpperSet` and is not restated. The hypothesis `n ≥ 1` is
needed: for `n = 0` the empty family is the mls and contains neither `∅` nor
`∅ᶜ = ∅`.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual
Monotone Boolean Functions*, Journal of Integer Sequences 28 (2025), Article
25.6.5, Lemma 3 (`jis-2025-25.6.5-lem-3`).

Proves `Wanted` entry `maximal_intersecting_mem_iff_compl_notMem`. -/
theorem maximal_intersecting_mem_iff_compl_notMem {n : ℕ} (hn : 1 ≤ n)
    {U : Set (Finset (Fin n))} (hU : Maximal Set.Intersecting U)
    (A : Finset (Fin n)) :
    A ∈ U ↔ Aᶜ ∉ U := by
  have hmax : ∀ t : Set (Finset (Fin n)), t.Intersecting → U ⊆ t → U = t :=
    fun t ht hUt => le_antisymm hUt (hU.2 ht hUt)
  have hup : IsUpperSet U := hU.1.isUpperSet hmax
  refine ⟨hU.1.compl_notMem, fun hA => ?_⟩
  by_contra hAU
  have hbot : A ≠ ⊥ := by
    rintro rfl
    have hne : (⊤ : Finset (Fin n)) ≠ ⊥ := by
      rw [Finset.top_eq_univ, Finset.bot_eq_empty]
      exact (univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 hn)).ne_empty
    have hins : (insert (⊤ : Finset (Fin n)) U).Intersecting :=
      hU.1.insert hne fun b hb hdisj => hU.1.ne_bot hb (top_disjoint.1 hdisj)
    exact hA (by simpa using (hmax _ hins (Set.subset_insert _ _)).symm ▸
      Set.mem_insert (⊤ : Finset (Fin n)) U)
  have hins : (insert A U).Intersecting :=
    hU.1.insert hbot fun b hb hdisj => hA (hup hdisj.symm.le_compl_right hb)
  exact hAU ((hmax _ hins (Set.subset_insert _ _)).symm ▸ Set.mem_insert A U)

/-- **Lemma 4.** If a family `𝒰 ⊆ 𝒫(X)` is an upset (L1) and for every
`A ⊆ X` exactly one of `A` and `Aᶜ` lies in `𝒰` (L2), then `𝒰` is a maximal
linked system.

The paper's hypothesis `n ≥ 1` is dropped: for `n = 0`, `∅ᶜ = ∅` and (L2)
cannot hold.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual
Monotone Boolean Functions*, Journal of Integer Sequences 28 (2025), Article
25.6.5, Lemma 4 (`jis-2025-25.6.5-lem-4`).

Proves `Wanted` entry
`maximal_intersecting_of_isUpperSet_of_mem_iff_compl_notMem`. -/
theorem maximal_intersecting_of_isUpperSet_of_mem_iff_compl_notMem {n : ℕ}
    {U : Set (Finset (Fin n))} (h₁ : IsUpperSet U)
    (h₂ : ∀ A : Finset (Fin n), A ∈ U ↔ Aᶜ ∉ U) :
    Maximal Set.Intersecting U := by
  have hint : U.Intersecting := fun A hA B hB hdisj =>
    (h₂ A).1 hA (h₁ hdisj.le_compl_left hB)
  refine ⟨hint, fun t ht hUt A hA => ?_⟩
  by_contra hAU
  exact ht.compl_notMem hA (hUt (not_not.1 (mt (h₂ A).2 hAU)))

/-! ### Permutations fixing self-dual functions -/

/-- If `x ∘ π = xᶜ` for some input `x`, then no self-dual Boolean function is
fixed by relabelling its variables by `π`. -/
theorem comp_perm_ne_of_eq_booleanFunctionDual {n : ℕ}
    {π : Equiv.Perm (Fin n)} {x : Fin n → Bool} (hx : x ∘ π = xᶜ)
    {f : (Fin n → Bool) → Bool} (hf : f = booleanFunctionDual n f) :
    (fun x => f (x ∘ π)) ≠ f := by
  intro h
  have h1 : f (x ∘ π) = f x := congrFun h x
  rw [hx] at h1
  have h2 : f x = (f xᶜ)ᶜ := congrFun hf x
  rw [h1] at h2
  revert h2
  cases f x <;> decide

/-- If every orbit of a permutation `π` of a finite type has even length,
there is `x` with `x ∘ π = xᶜ`: alternate the values of `x` along each
orbit. -/
theorem exists_comp_eq_compl_of_even_minimalPeriod {α : Type*} [Finite α]
    (π : Equiv.Perm α) (hπ : ∀ i, Even (Function.minimalPeriod π i)) :
    ∃ x : α → Bool, x ∘ π = xᶜ := by
  classical
  let r : α → α := fun i =>
    (Quotient.mk (Equiv.Perm.SameCycle.setoid π) i).out
  have hr : ∀ i, π.SameCycle (r i) i := fun i =>
    Quotient.mk_out (s := Equiv.Perm.SameCycle.setoid π) i
  have hrπ : ∀ i, r (π i) = r i := fun i =>
    congrArg Quotient.out (Quotient.sound (Equiv.Perm.sameCycle_apply_left.2
      (Equiv.Perm.SameCycle.refl π i)))
  have key : ∀ i a b, (π ^ a) (r i) = (π ^ b) (r i) → a ≤ b →
      (Even a ↔ Even b) := by
    intro i a b hab hle
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [pow_add, Equiv.Perm.mul_apply] at hab
    have hd : Function.IsPeriodicPt π d (r i) := by
      change (⇑π)^[d] (r i) = r i
      rw [Equiv.Perm.iterate_eq_pow]
      exact ((π ^ a).injective hab).symm
    have hev : Even d := even_iff_two_dvd.2
      ((hπ (r i)).two_dvd.trans hd.minimalPeriod_dvd)
    rw [Nat.even_add]
    exact ⟨fun h => ⟨fun _ => hev, fun _ => h⟩, fun h => h.2 hev⟩
  have key' : ∀ i a b, (π ^ a) (r i) = (π ^ b) (r i) → (Even a ↔ Even b) :=
    fun i a b h => (le_total a b).elim (key i a b h)
      fun hba => (key i b a h.symm hba).symm
  let x : α → Bool := fun i => decide (∃ m, Even m ∧ (π ^ m) (r i) = i)
  have hx : ∀ i m, (π ^ m) (r i) = i → x i = decide (Even m) := by
    intro i m hm
    simp only [x, decide_eq_decide]
    exact ⟨fun ⟨m', he, h'⟩ => (key' i m' m (h'.trans hm.symm)).1 he,
      fun he => ⟨m, he, hm⟩⟩
  refine ⟨x, funext fun i => ?_⟩
  obtain ⟨m, hm⟩ := (hr i).exists_nat_pow_eq
  have h1 : (π ^ (m + 1)) (r (π i)) = π i := by
    rw [hrπ, pow_succ', Equiv.Perm.mul_apply, hm]
  rw [Function.comp_apply, hx _ _ h1, Pi.compl_apply, hx _ _ hm]
  simp only [Nat.even_add_one, decide_not]
  rfl

/-- **Lemma 15.** If `π`, acting on `{1, …, n}`, is a product of disjoint
cycles of even length (every point has even orbit length under `π`), then
`Φ(π, Λ_n) = ∅`: no self-dual monotone function is fixed by `π`.

The paper's hypothesis that `n` is even is dropped: it follows from the cycle
condition.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual
Monotone Boolean Functions*, Journal of Integer Sequences 28 (2025), Article
25.6.5, Lemma 15 (`jis-2025-25.6.5-lem-15`).

Proves `Wanted` entry `selfDualMonotone_not_fixed_of_even_minimalPeriod`. -/
theorem selfDualMonotone_not_fixed_of_even_minimalPeriod {n : ℕ}
    (π : Equiv.Perm (Fin n)) (hπ : ∀ i, Even (Function.minimalPeriod π i))
    (f : (Fin n → Bool) → Bool) (hf : IsSelfDualMonotone n f) :
    (fun x => f (x ∘ π)) ≠ f :=
  have ⟨_, hx⟩ := exists_comp_eq_compl_of_even_minimalPeriod π hπ
  comp_perm_ne_of_eq_booleanFunctionDual hx hf.2

/-- **Corollary 16.** `Φ(π, Λ_8) = ∅` for `π` each of `(12345678)`,
`(12)(345678)`, `(1234)(5678)`, `(12)(34)(5678)` and `(12)(34)(56)(78)`.

Points `1, …, 8` are `0, …, 7` in `Fin 8`.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual
Monotone Boolean Functions*, Journal of Integer Sequences 28 (2025), Article
25.6.5, Corollary 16 (`jis-2025-25.6.5-cor-16`).

Proves `Wanted` entry `selfDualMonotone_eight_not_fixed`. -/
theorem selfDualMonotone_eight_not_fixed (π : Equiv.Perm (Fin 8))
    (hπ : π = c[0, 1, 2, 3, 4, 5, 6, 7] ∨ π = c[0, 1] * c[2, 3, 4, 5, 6, 7] ∨
      π = c[0, 1, 2, 3] * c[4, 5, 6, 7] ∨
      π = c[0, 1] * c[2, 3] * c[4, 5, 6, 7] ∨
      π = c[0, 1] * c[2, 3] * c[4, 5] * c[6, 7])
    (f : (Fin 8 → Bool) → Bool) (hf : IsSelfDualMonotone 8 f) :
    (fun x => f (x ∘ π)) ≠ f := by
  refine comp_perm_ne_of_eq_booleanFunctionDual
    (x := fun i => decide (Even (i : ℕ))) ?_ hf.2
  rcases hπ with rfl | rfl | rfl | rfl | rfl <;> decide

/-- **Lemma 17.** For odd `n` and every `π ∈ S_n`, `Φ(π, Λ_n) ≠ ∅`.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual
Monotone Boolean Functions*, Journal of Integer Sequences 28 (2025), Article
25.6.5, Lemma 17 (`jis-2025-25.6.5-lem-17`).

Proves `Wanted` entry `exists_selfDualMonotone_fixed_of_odd`. -/
theorem exists_selfDualMonotone_fixed_of_odd {n : ℕ} (hn : Odd n)
    (π : Equiv.Perm (Fin n)) :
    ∃ f : (Fin n → Bool) → Bool,
      IsSelfDualMonotone n f ∧ (fun x => f (x ∘ π)) = f := by
  refine ⟨fun x => decide (n < 2 * (univ.filter fun i => x i = true).card),
    ⟨?_, ?_⟩, ?_⟩
  · intro x y hxy
    have : (univ.filter fun i => x i = true).card ≤
        (univ.filter fun i => y i = true).card := by
      refine card_le_card fun i => ?_
      simp only [mem_filter, mem_univ, true_and]
      intro hi
      have := hxy i
      rw [hi] at this
      exact top_le_iff.mp this
    simp only [Bool.le_iff_imp, decide_eq_true_eq]
    omega
  · funext x
    have hc : (univ.filter fun i => xᶜ i = true).card =
        n - (univ.filter fun i => x i = true).card := by
      have : (univ.filter fun i => xᶜ i = true) =
          (univ.filter fun i => x i = true)ᶜ := by
        ext i
        simp
      rw [this, card_compl, Fintype.card_fin]
    have hle : (univ.filter fun i => x i = true).card ≤ n :=
      (card_le_univ _).trans (by simp)
    rw [booleanFunctionDual_apply_eq_compl, hc]
    obtain ⟨k, rfl⟩ := hn
    by_cases h : 2 * k + 1 < 2 * (univ.filter fun i => x i = true).card
    · simp only [h, decide_true]
      symm
      simp only [Bool.compl_eq_bnot, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_false_iff_not, not_lt]
      omega
    · simp only [h, decide_false]
      symm
      simp only [Bool.compl_eq_bnot, Bool.not_eq_eq_eq_not, Bool.not_false,
        decide_eq_true_eq]
      omega
  · funext x
    have : (univ.filter fun i => (x ∘ π) i = true).card =
        (univ.filter fun i => x i = true).card := by
      rw [card_filter, card_filter]
      exact Equiv.sum_comp π (fun i => if x i = true then 1 else 0)
    change decide (n < 2 * (univ.filter fun i => (x ∘ π) i = true).card) = _
    rw [this]

end

end MetaMathlibExt
