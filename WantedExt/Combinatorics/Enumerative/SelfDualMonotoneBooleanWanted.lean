/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SetFamily.Intersecting
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.Order.Hom.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Order.BooleanFunction.SelfDual

/-!
# Counting self-dual monotone Boolean functions

Statements from Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone
Boolean Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5 (definitions read
from arXiv `2310.12637` and from the journal TeX source).

`D_n` is the set of monotone `f : (Fin n → Bool) → Bool` with the pointwise order, `f*` is
`booleanFunctionDual n f`, `x | y` and `x & y` are `⊔` and `⊓`, `Λ_n` is
`{f | IsSelfDualMonotone n f}` with `λ_n = Nat.card Λ_n`, and `d_n = |D_n|`. For `x ≤ y`,
`re(x, y) = |{z ∈ D_n | x ≤ z ≤ y}|`; `ℓ(b)` is the number of inputs where `b` is `true`.
Permutations act by `f ↦ (x ↦ f (x ∘ π))`; `γ(b)` is the size of the class of `b`. The
paper's sums over the class set `R_n` (classes identified with representatives) are stated for
any system of representatives `reps`. A concatenation of `2^k` elements of `D_n` is the
function on `n + k` variables that reads the last `k` variables as a binary index `∑ yⱼ 2^j`
into the word and applies the selected element to the first `n` variables.

A family `𝒰` of subsets of `X = {1, …, n}` (here `Fin n`) is linked when any two members meet
(`Set.Intersecting`), and a maximal linked system (mls) is a maximal linked family
(`Maximal Set.Intersecting 𝒰`). `Φ(π, Λ_n)` is the set of `f ∈ Λ_n` fixed by `π`, that is
with `(fun x => f (x ∘ π)) = f`.
-/

namespace MetaMathlibExt

open scoped Classical

@[expose] public section

/-- The concatenation `W₀ · W₁ ⋯` of Boolean functions on `n` variables, as a function on
`n + k` variables: the last `k` variables give the binary index `∑ⱼ yⱼ 2^j` into the word `W`,
and the selected function is applied to the first `n` variables (out-of-range indices read
`false`).

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, the concatenation
representation of `D_n^{B^k}` before Theorem 10. -/
public def booleanCubeConcat (n k : ℕ) (W : List ((Fin n → Bool) → Bool)) :
    (Fin (n + k) → Bool) → Bool :=
  fun x => (W.getD (∑ j : Fin k, if x (Fin.natAdd n j) then 2 ^ (j : ℕ) else 0) fun _ => false)
    fun i => x (Fin.castAdd k i)

/-- On the all-`false` input the concatenation reads the first word entry at all-`false`.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, the concatenation
representation of `D_n^{B^k}` before Theorem 10. -/
public theorem booleanCubeConcat_false (n k : ℕ) (W : List ((Fin n → Bool) → Bool)) :
    booleanCubeConcat n k W (fun _ => false) = W.getD 0 (fun _ => false) (fun _ => false) := by
  simp [booleanCubeConcat]

/-- **Lemma 1.** The poset `D_{n+k}` is isomorphic to the poset `D_n^{B^k}` of monotone
functions from `B^k` to `D_n`.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Lemma 1
(`jis-2025-25.6.5-lem-1`). -/
public theorem_wanted monotoneBooleanFunction_orderIso_curry (n k : ℕ) :
    Nonempty (((Fin (n + k) → Bool) →o Bool) ≃o
      ((Fin k → Bool) →o ((Fin n → Bool) →o Bool)))

/-- **Lemma 2 (parts 2-4).** For `f, g ∈ D_n`: if `f ≤ g` then `g* ≤ f*`;
`(f | g)* = f* & g*`; `(f & g)* = f* | g*`.

Part 1 (`f** = f`) is `MetaMathlibExt.booleanFunctionDual_dual`, already proved for every
Boolean function, and is not restated.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Lemma 2
(`jis-2025-25.6.5-lem-2`). -/
public theorem_wanted booleanFunctionDual_antitone_sup_inf (n : ℕ)
    (f g : (Fin n → Bool) → Bool) (hf : Monotone f) (hg : Monotone g) :
    (f ≤ g → booleanFunctionDual n g ≤ booleanFunctionDual n f) ∧
      booleanFunctionDual n (f ⊔ g) = booleanFunctionDual n f ⊓ booleanFunctionDual n g ∧
      booleanFunctionDual n (f ⊓ g) = booleanFunctionDual n f ⊔ booleanFunctionDual n g

/-- **Lemma 5.** For every `f : Bⁿ → B` and permutation `π`: `f ∘ π` is monotone if `f` is;
if `f ∈ D_n` then `f* ∘ π = (f ∘ π)*`; if `f ∈ Λ_n` then every `g ∈ [f]` is in `Λ_n`.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Lemma 5
(`jis-2025-25.6.5-lem-5`). -/
public theorem_wanted booleanFunction_perm_monotone_dual_selfDual (n : ℕ)
    (f : (Fin n → Bool) → Bool) (π : Equiv.Perm (Fin n)) :
    (Monotone f → Monotone fun x => f (x ∘ π)) ∧
      (Monotone f →
        (fun x => booleanFunctionDual n f (x ∘ π)) = booleanFunctionDual n fun x => f (x ∘ π)) ∧
      (IsSelfDualMonotone n f → IsSelfDualMonotone n fun x => f (x ∘ π))

/-- **Theorem 6.** For `n ≥ 0`, `λ_{n+1} = |{b ∈ D_n | b ≤ b*}|`, and
`λ_{n+1} = ∑_{b ∈ R_n, b ≤ b*} γ(b)`.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Theorem 6
(`jis-2025-25.6.5-thm-6`). -/
public theorem_wanted card_selfDualMonotone_succ (n : ℕ) :
    Nat.card {f : (Fin (n + 1) → Bool) → Bool // IsSelfDualMonotone (n + 1) f} =
        Nat.card {b : (Fin n → Bool) → Bool // Monotone b ∧ b ≤ booleanFunctionDual n b} ∧
      ∀ reps : Finset ((Fin n → Bool) → Bool), (∀ b ∈ reps, Monotone b) →
        (∀ f : (Fin n → Bool) → Bool, Monotone f →
          ∃! b, b ∈ reps ∧ ∃ π : Equiv.Perm (Fin n), f = fun x => b (x ∘ π)) →
        Nat.card {f : (Fin (n + 1) → Bool) → Bool // IsSelfDualMonotone (n + 1) f} =
          ∑ b ∈ reps with b ≤ booleanFunctionDual n b,
            Nat.card {g : (Fin n → Bool) → Bool //
              ∃ π : Equiv.Perm (Fin n), g = fun x => b (x ∘ π)}

/-- **Corollary 7.** For `n ≥ 0`, `λ_{n+1} ≤ d_n`.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Corollary 7
(`jis-2025-25.6.5-cor-7`). -/
public theorem_wanted card_selfDualMonotone_succ_le (n : ℕ) :
    Nat.card {f : (Fin (n + 1) → Bool) → Bool // IsSelfDualMonotone (n + 1) f} ≤
      Nat.card {f : (Fin n → Bool) → Bool // Monotone f}

/-- **Lemma 8.** For `b ∈ D_n`: `b ≤ b*` only if `ℓ(b) ≤ 2^{n-1}`; if `ℓ(b) = 2^{n-1}` and
`b ≤ b*` then `b = b*`; if `b` is self-dual then `ℓ(b) = 2^{n-1}`; `ℓ(b*) = 2ⁿ - ℓ(b)`, hence
`|{f ∈ D_n | ℓ(f) < 2^{n-1}}| = |{f ∈ D_n | ℓ(f) > 2^{n-1}}|`.

Comparisons with `2^{n-1}` are written as comparisons of `2 ℓ` with `2ⁿ` (so `n = 0` is
included).

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Lemma 8
(`jis-2025-25.6.5-lem-8`). -/
public theorem_wanted monotoneBooleanFunction_weight_dual (n : ℕ) (b : (Fin n → Bool) → Bool)
    (hb : Monotone b) :
    (b ≤ booleanFunctionDual n b → 2 * Nat.card {x // b x = true} ≤ 2 ^ n) ∧
      (2 * Nat.card {x // b x = true} = 2 ^ n → b ≤ booleanFunctionDual n b →
        b = booleanFunctionDual n b) ∧
      (b = booleanFunctionDual n b → 2 * Nat.card {x // b x = true} = 2 ^ n) ∧
      Nat.card {x // booleanFunctionDual n b x = true} = 2 ^ n - Nat.card {x // b x = true} ∧
      Nat.card {f : (Fin n → Bool) → Bool // Monotone f ∧ 2 * Nat.card {x // f x = true} < 2 ^ n} =
        Nat.card {f : (Fin n → Bool) → Bool //
          Monotone f ∧ 2 ^ n < 2 * Nat.card {x // f x = true}}

/-- **Theorem 9.** For `n ≥ 1`,
`λ_{n+1} = λ_n + ∑_{b ∈ R_n, ℓ(b) < 2^{n-1}, b ≤ b*} γ(b)` and
`λ_{n+1} ≤ λ_n + (d_n - λ_n) / 2 = (d_n + λ_n) / 2`.

Stated for `n ≥ 1` (for `n = 0`, `2^{n-1}` is not an integer); the bound is stated as
`2 λ_{n+1} ≤ d_n + λ_n`; `ℓ(b) < 2^{n-1}` is `2 ℓ(b) < 2ⁿ`.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Theorem 9
(`jis-2025-25.6.5-thm-9`). -/
public theorem_wanted card_selfDualMonotone_succ_eq_add (n : ℕ) (hn : 1 ≤ n) :
    (∀ reps : Finset ((Fin n → Bool) → Bool), (∀ b ∈ reps, Monotone b) →
        (∀ f : (Fin n → Bool) → Bool, Monotone f →
          ∃! b, b ∈ reps ∧ ∃ π : Equiv.Perm (Fin n), f = fun x => b (x ∘ π)) →
        Nat.card {f : (Fin (n + 1) → Bool) → Bool // IsSelfDualMonotone (n + 1) f} =
          Nat.card {f : (Fin n → Bool) → Bool // IsSelfDualMonotone n f} +
            ∑ b ∈ reps with
                2 * Nat.card {x // b x = true} < 2 ^ n ∧ b ≤ booleanFunctionDual n b,
              Nat.card {g : (Fin n → Bool) → Bool //
                ∃ π : Equiv.Perm (Fin n), g = fun x => b (x ∘ π)}) ∧
      2 * Nat.card {f : (Fin (n + 1) → Bool) → Bool // IsSelfDualMonotone (n + 1) f} ≤
        Nat.card {f : (Fin n → Bool) → Bool // Monotone f} +
          Nat.card {f : (Fin n → Bool) → Bool // IsSelfDualMonotone n f}

/-- **Theorem 10.** For `n ≥ 0`, `λ_{n+2}` is the number of pairs `b, d ∈ D_n` with
`d ≥ b | b*`: `λ_{n+2} = ∑_{b ∈ D_n} re(b | b*, ⊤)`, and
`λ_{n+2} = ∑_{b ∈ R_n} γ(b) re(b | b*, ⊤)`.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Theorem 10
(`jis-2025-25.6.5-thm-10`). -/
public theorem_wanted card_selfDualMonotone_add_two (n : ℕ) :
    Nat.card {f : (Fin (n + 2) → Bool) → Bool // IsSelfDualMonotone (n + 2) f} =
        ∑ b ∈ Finset.univ.filter (fun b : (Fin n → Bool) → Bool => Monotone b),
          Nat.card {z : (Fin n → Bool) → Bool // Monotone z ∧ b ⊔ booleanFunctionDual n b ≤ z} ∧
      ∀ reps : Finset ((Fin n → Bool) → Bool), (∀ b ∈ reps, Monotone b) →
        (∀ f : (Fin n → Bool) → Bool, Monotone f →
          ∃! b, b ∈ reps ∧ ∃ π : Equiv.Perm (Fin n), f = fun x => b (x ∘ π)) →
        Nat.card {f : (Fin (n + 2) → Bool) → Bool // IsSelfDualMonotone (n + 2) f} =
          ∑ b ∈ reps, Nat.card {g : (Fin n → Bool) → Bool //
              ∃ π : Equiv.Perm (Fin n), g = fun x => b (x ∘ π)} *
            Nat.card {z : (Fin n → Bool) → Bool // Monotone z ∧ b ⊔ booleanFunctionDual n b ≤ z}

/-- **Corollary 11.** For `n ≥ 0`, `λ_{n+2} ≥ d_n`.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Corollary 11
(`jis-2025-25.6.5-cor-11`). -/
public theorem_wanted le_card_selfDualMonotone_add_two (n : ℕ) :
    Nat.card {f : (Fin n → Bool) → Bool // Monotone f} ≤
      Nat.card {f : (Fin (n + 2) → Bool) → Bool // IsSelfDualMonotone (n + 2) f}

/-- **Theorem 12.** For `a, b, c ∈ D_n`, `h ∈ D_n` with `h ≥ a|b|c|a*|b*|c*`, and
`d, e, f, g ∈ D_n` with `a|b|c ≤ d ≤ h`, `a|b*|c* ≤ e ≤ h`, `b|a*|c* ≤ f ≤ h`,
`c|a*|b* ≤ g ≤ h`, the concatenation
`h*·g*·f*·a·e*·b·c·d·d*·c*·b*·e·a*·f·g·h` is a self-dual function in `D_{n+4}`; and every
self-dual function in `D_{n+4}` is of this form.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Theorem 12
(`jis-2025-25.6.5-thm-12`). -/
public theorem_wanted selfDualMonotone_add_four_iff_concat (n : ℕ) :
    (∀ a b c d e f g h : (Fin n → Bool) → Bool,
      Monotone a → Monotone b → Monotone c → Monotone d → Monotone e → Monotone f →
      Monotone g → Monotone h →
      a ⊔ b ⊔ c ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n b ⊔
        booleanFunctionDual n c ≤ h →
      a ⊔ b ⊔ c ≤ d → d ≤ h →
      a ⊔ booleanFunctionDual n b ⊔ booleanFunctionDual n c ≤ e → e ≤ h →
      b ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n c ≤ f → f ≤ h →
      c ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n b ≤ g → g ≤ h →
      IsSelfDualMonotone (n + 4) (booleanCubeConcat n 4
        [booleanFunctionDual n h, booleanFunctionDual n g, booleanFunctionDual n f, a,
          booleanFunctionDual n e, b, c, d, booleanFunctionDual n d, booleanFunctionDual n c,
          booleanFunctionDual n b, e, booleanFunctionDual n a, f, g, h])) ∧
    ∀ F : (Fin (n + 4) → Bool) → Bool, IsSelfDualMonotone (n + 4) F →
      ∃ a b c d e f g h : (Fin n → Bool) → Bool,
        Monotone a ∧ Monotone b ∧ Monotone c ∧ Monotone d ∧ Monotone e ∧ Monotone f ∧
        Monotone g ∧ Monotone h ∧
        a ⊔ b ⊔ c ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n b ⊔
          booleanFunctionDual n c ≤ h ∧
        a ⊔ b ⊔ c ≤ d ∧ d ≤ h ∧
        a ⊔ booleanFunctionDual n b ⊔ booleanFunctionDual n c ≤ e ∧ e ≤ h ∧
        b ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n c ≤ f ∧ f ≤ h ∧
        c ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n b ≤ g ∧ g ≤ h ∧
        F = booleanCubeConcat n 4
          [booleanFunctionDual n h, booleanFunctionDual n g, booleanFunctionDual n f, a,
            booleanFunctionDual n e, b, c, d, booleanFunctionDual n d, booleanFunctionDual n c,
            booleanFunctionDual n b, e, booleanFunctionDual n a, f, g, h]

/-- **Theorem 13.** `λ_{n+4} = ∑_{a,b,c ∈ D_n} ∑_{h ∈ D_n, h ≥ a|b|c|a*|b*|c*}
re(a|b|c, h) re(a|b*|c*, h) re(b|a*|c*, h) re(c|a*|b*, h)`.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Theorem 13
(`jis-2025-25.6.5-thm-13`). -/
public theorem_wanted card_selfDualMonotone_add_four (n : ℕ) :
    Nat.card {F : (Fin (n + 4) → Bool) → Bool // IsSelfDualMonotone (n + 4) F} =
      ∑ a ∈ Finset.univ.filter (fun b : (Fin n → Bool) → Bool => Monotone b),
      ∑ b ∈ Finset.univ.filter (fun b : (Fin n → Bool) → Bool => Monotone b),
      ∑ c ∈ Finset.univ.filter (fun b : (Fin n → Bool) → Bool => Monotone b),
      ∑ h ∈ Finset.univ.filter (fun h : (Fin n → Bool) → Bool => Monotone h ∧
          a ⊔ b ⊔ c ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n b ⊔
            booleanFunctionDual n c ≤ h),
        Nat.card {z : (Fin n → Bool) → Bool // Monotone z ∧ a ⊔ b ⊔ c ≤ z ∧ z ≤ h} *
        Nat.card {z : (Fin n → Bool) → Bool // Monotone z ∧
          a ⊔ booleanFunctionDual n b ⊔ booleanFunctionDual n c ≤ z ∧ z ≤ h} *
        Nat.card {z : (Fin n → Bool) → Bool // Monotone z ∧
          b ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n c ≤ z ∧ z ≤ h} *
        Nat.card {z : (Fin n → Bool) → Bool // Monotone z ∧
          c ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n b ≤ z ∧ z ≤ h}

/-- **Theorem 14.** For `h ∈ D_n` with `h ≥ h*`, `a, b, c ∈ D_n` with `h* ≤ a, b, c ≤ h`, and
`d, e, f, g ∈ D_n` with `a|b|c ≤ d ≤ h`, `a|b*|c* ≤ e ≤ h`, `b|a*|c* ≤ f ≤ h`,
`c|a*|b* ≤ g ≤ h`, the concatenation `h*·g*·f*·a·e*·b·c·d·d*·c*·b*·e·a*·f·g·h` is a
self-dual function in `D_{n+4}`; and every self-dual function in `D_{n+4}` is of this form.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Theorem 14
(`jis-2025-25.6.5-thm-14`). -/
public theorem_wanted selfDualMonotone_add_four_iff_concat_of_dual_le (n : ℕ) :
    (∀ a b c d e f g h : (Fin n → Bool) → Bool,
      Monotone a → Monotone b → Monotone c → Monotone d → Monotone e → Monotone f →
      Monotone g → Monotone h →
      booleanFunctionDual n h ≤ h →
      booleanFunctionDual n h ≤ a → a ≤ h → booleanFunctionDual n h ≤ b → b ≤ h →
      booleanFunctionDual n h ≤ c → c ≤ h →
      a ⊔ b ⊔ c ≤ d → d ≤ h →
      a ⊔ booleanFunctionDual n b ⊔ booleanFunctionDual n c ≤ e → e ≤ h →
      b ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n c ≤ f → f ≤ h →
      c ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n b ≤ g → g ≤ h →
      IsSelfDualMonotone (n + 4) (booleanCubeConcat n 4
        [booleanFunctionDual n h, booleanFunctionDual n g, booleanFunctionDual n f, a,
          booleanFunctionDual n e, b, c, d, booleanFunctionDual n d, booleanFunctionDual n c,
          booleanFunctionDual n b, e, booleanFunctionDual n a, f, g, h])) ∧
    ∀ F : (Fin (n + 4) → Bool) → Bool, IsSelfDualMonotone (n + 4) F →
      ∃ a b c d e f g h : (Fin n → Bool) → Bool,
        Monotone a ∧ Monotone b ∧ Monotone c ∧ Monotone d ∧ Monotone e ∧ Monotone f ∧
        Monotone g ∧ Monotone h ∧
        booleanFunctionDual n h ≤ h ∧
        booleanFunctionDual n h ≤ a ∧ a ≤ h ∧ booleanFunctionDual n h ≤ b ∧ b ≤ h ∧
        booleanFunctionDual n h ≤ c ∧ c ≤ h ∧
        a ⊔ b ⊔ c ≤ d ∧ d ≤ h ∧
        a ⊔ booleanFunctionDual n b ⊔ booleanFunctionDual n c ≤ e ∧ e ≤ h ∧
        b ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n c ≤ f ∧ f ≤ h ∧
        c ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n b ≤ g ∧ g ≤ h ∧
        F = booleanCubeConcat n 4
          [booleanFunctionDual n h, booleanFunctionDual n g, booleanFunctionDual n f, a,
            booleanFunctionDual n e, b, c, d, booleanFunctionDual n d, booleanFunctionDual n c,
            booleanFunctionDual n b, e, booleanFunctionDual n a, f, g, h]

/-- **Lemma 3 (L2).** For `n ≥ 1`, if `𝒰 ⊆ 𝒫(X)` is a maximal linked system then for every
`A ⊆ X` exactly one of `A` and `Aᶜ` lies in `𝒰`.

Part (L1), that a maximal linked system is an upset, is Mathlib's
`Set.Intersecting.isUpperSet` and is not restated. The hypothesis `n ≥ 1` is needed: for
`n = 0` the empty family is the mls and contains neither `∅` nor `∅ᶜ = ∅`.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Lemma 3
(`jis-2025-25.6.5-lem-3`). -/
public theorem_wanted maximal_intersecting_mem_iff_compl_notMem {n : ℕ} (hn : 1 ≤ n)
    {U : Set (Finset (Fin n))} (hU : Maximal Set.Intersecting U) (A : Finset (Fin n)) :
    A ∈ U ↔ Aᶜ ∉ U

/-- **Lemma 4.** If a family `𝒰 ⊆ 𝒫(X)` is an upset (L1) and for every `A ⊆ X` exactly one of
`A` and `Aᶜ` lies in `𝒰` (L2), then `𝒰` is a maximal linked system.

The paper's hypothesis `n ≥ 1` is dropped: for `n = 0`, `∅ᶜ = ∅` and (L2) cannot hold.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Lemma 4
(`jis-2025-25.6.5-lem-4`). -/
public theorem_wanted maximal_intersecting_of_isUpperSet_of_mem_iff_compl_notMem {n : ℕ}
    {U : Set (Finset (Fin n))} (h₁ : IsUpperSet U) (h₂ : ∀ A : Finset (Fin n), A ∈ U ↔ Aᶜ ∉ U) :
    Maximal Set.Intersecting U

/-- **Lemma 15.** If `π`, acting on `{1, …, n}`, is a product of disjoint cycles of even
length (every point has even orbit length under `π`), then `Φ(π, Λ_n) = ∅`: no self-dual
monotone function is fixed by `π`.

The paper's hypothesis that `n` is even is dropped: it follows from the cycle condition.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Lemma 15
(`jis-2025-25.6.5-lem-15`). -/
public theorem_wanted selfDualMonotone_not_fixed_of_even_minimalPeriod {n : ℕ}
    (π : Equiv.Perm (Fin n)) (hπ : ∀ i, Even (Function.minimalPeriod π i))
    (f : (Fin n → Bool) → Bool) (hf : IsSelfDualMonotone n f) :
    (fun x => f (x ∘ π)) ≠ f

/-- **Corollary 16.** `Φ(π, Λ_8) = ∅` for `π` each of `(12345678)`, `(12)(345678)`,
`(1234)(5678)`, `(12)(34)(5678)` and `(12)(34)(56)(78)`.

Points `1, …, 8` are `0, …, 7` in `Fin 8`.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Corollary 16
(`jis-2025-25.6.5-cor-16`). -/
public theorem_wanted selfDualMonotone_eight_not_fixed (π : Equiv.Perm (Fin 8))
    (hπ : π = c[0, 1, 2, 3, 4, 5, 6, 7] ∨ π = c[0, 1] * c[2, 3, 4, 5, 6, 7] ∨
      π = c[0, 1, 2, 3] * c[4, 5, 6, 7] ∨ π = c[0, 1] * c[2, 3] * c[4, 5, 6, 7] ∨
      π = c[0, 1] * c[2, 3] * c[4, 5] * c[6, 7])
    (f : (Fin 8 → Bool) → Bool) (hf : IsSelfDualMonotone 8 f) :
    (fun x => f (x ∘ π)) ≠ f

/-- **Lemma 17.** For odd `n` and every `π ∈ S_n`, `Φ(π, Λ_n) ≠ ∅`.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Lemma 17
(`jis-2025-25.6.5-lem-17`). -/
public theorem_wanted exists_selfDualMonotone_fixed_of_odd {n : ℕ} (hn : Odd n)
    (π : Equiv.Perm (Fin n)) :
    ∃ f : (Fin n → Bool) → Bool, IsSelfDualMonotone n f ∧ (fun x => f (x ∘ π)) = f

end

end MetaMathlibExt
