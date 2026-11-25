/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Notation

/-!
# The first meta-automatic sequence

The defining recurrence pairs each even-indexed value with its Boolean complement.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The meta-automatic sequence $\mathcal{M}_1$.** The sequence
$\mathcal{M}_1 : \mathbb{N} \to \{0, 1\}$ (OEIS A392736) is defined by $\mathcal{M}_1(0) = 0$,
$\mathcal{M}_1(1) = 1$, the recurrences $\mathcal{M}_1(4n) = \mathcal{M}_1(n)$ and
$\mathcal{M}_1(4n+1) = 1 - \mathcal{M}_1(n)$ for every $n \ge 1$, and the recurrences
$\mathcal{M}_1(4n+2) = \mathcal{M}_1(2n + 1 - \mathcal{M}_1(n))$ and
$\mathcal{M}_1(4n+3) = 1 - \mathcal{M}_1(2n + 1 - \mathcal{M}_1(n))$ for every $n \ge 0$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 3 (definition of `ℳ₁`). -/
public def metaAutomaticOne : ℕ → Bool
  | 0 => false
  | 1 => true
  | n + 2 =>
    match (n + 2) % 4 with
    | 0 => metaAutomaticOne ((n + 2) / 4)
    | 1 => !metaAutomaticOne ((n + 2) / 4)
    | 2 => if metaAutomaticOne ((n + 2) / 4) then metaAutomaticOne (2 * ((n + 2) / 4))
        else metaAutomaticOne (2 * ((n + 2) / 4) + 1)
    | _ => !(if metaAutomaticOne ((n + 2) / 4) then metaAutomaticOne (2 * ((n + 2) / 4))
        else metaAutomaticOne (2 * ((n + 2) / 4) + 1))
termination_by n => n
decreasing_by all_goals omega

/-- **Recurrences of the meta-automatic sequence $\mathcal{M}_1$.** Reading the values of the
meta-automatic sequence $\mathcal{M}_1$ as $0$ and $1$, for every $n \ge 1$ we have
$\mathcal{M}_1(4n) = \mathcal{M}_1(n)$ and $\mathcal{M}_1(4n+1) = 1 - \mathcal{M}_1(n)$, and for
every $n \in \mathbb{N}$ we have $\mathcal{M}_1(4n+2) = \mathcal{M}_1(2n + 1 - \mathcal{M}_1(n))$
and $\mathcal{M}_1(4n+3) = 1 - \mathcal{M}_1(2n + 1 - \mathcal{M}_1(n))$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 3, equations (6) and (7). -/
public theorem metaAutomaticOne_rec (n : ℕ) :
    (1 ≤ n → metaAutomaticOne (4 * n) = metaAutomaticOne n) ∧
      (1 ≤ n → metaAutomaticOne (4 * n + 1) = !metaAutomaticOne n) ∧
      metaAutomaticOne (4 * n + 2) =
        metaAutomaticOne (2 * n + 1 - (metaAutomaticOne n).toNat) ∧
      metaAutomaticOne (4 * n + 3) =
        !metaAutomaticOne (2 * n + 1 - (metaAutomaticOne n).toNat) := by
  refine ⟨fun hn => ?_, fun hn => ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ : ∃ k, 4 * n = k + 2 := ⟨4 * n - 2, by omega⟩
    rw [hk, metaAutomaticOne]
    simp only [show (k + 2) % 4 = 0 by omega, show (k + 2) / 4 = n by omega]
  · obtain ⟨k, hk⟩ : ∃ k, 4 * n + 1 = k + 2 := ⟨4 * n - 1, by omega⟩
    rw [hk, metaAutomaticOne]
    simp only [show (k + 2) % 4 = 1 by omega, show (k + 2) / 4 = n by omega]
  · rw [show 4 * n + 2 = 4 * n + 2 from rfl, metaAutomaticOne]
    simp only [show (4 * n + 2) % 4 = 2 by omega, show (4 * n + 2) / 4 = n by omega]
    cases metaAutomaticOne n <;> simp
  · rw [show 4 * n + 3 = (4 * n + 1) + 2 by omega, metaAutomaticOne]
    simp only [show (4 * n + 1 + 2) % 4 = 3 by omega, show (4 * n + 1 + 2) / 4 = n by omega]
    cases metaAutomaticOne n <;> simp

/-- **The meta-automatic sequence $\mathcal{M}_1$ is balanced.** Reading the values of the
meta-automatic sequence $\mathcal{M}_1$ as $0$ and $1$, we have
$\mathcal{M}_1(2n) + \mathcal{M}_1(2n+1) = 1$ for every $n \in \mathbb{N}$.

The paper's lemma also asserts that $\mathcal{M}_1$ is well defined; here that is part of the
definition of $\mathcal{M}_1$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Lemma 10 (`jis-2026-26.4.1-lem-10`). -/
public theorem metaAutomaticOne_balanced (n : ℕ) :
    (metaAutomaticOne (2 * n)).toNat + (metaAutomaticOne (2 * n + 1)).toNat = 1 := by
  have complement (b : Bool) : b.toNat + (!b).toNat = 1 := by cases b <;> rfl
  by_cases hn : n = 0
  · simp [hn, metaAutomaticOne]
  obtain ⟨k, hk⟩ : ∃ k, 2 * n = 4 * k ∨ 2 * n = 4 * k + 2 := ⟨n / 2, by omega⟩
  obtain ⟨h₀, h₁, h₂, h₃⟩ := metaAutomaticOne_rec k
  rcases hk with hk | hk
  · rw [hk, h₀ (by omega), h₁ (by omega)]
    exact complement _
  · rw [hk, h₂, h₃]
    exact complement _

end

end MetaMathlibExt
