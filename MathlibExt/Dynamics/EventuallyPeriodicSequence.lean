/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.WLOG

namespace MetaMathlibExt

@[expose] public section

/-- **Eventually periodic sequences.** A sequence $u : \mathbb{N} \to \alpha$ with values in a
type $\alpha$ is eventually periodic if there are natural numbers $p > 0$ (a period) and $n_0$
(a preperiod) such that $u(n + p) = u(n)$ for every natural number $n \ge n_0$.

Source: concept `jis_sem_2c65b9e5cf5a27c75318c558`; source statements
`jis_2541b4a8b30e59c04cfc2cab`, `jis_6271663997522001b37d9cd0`,
`jis_7be4cb01363efa6d047e19af`, `jis_9f6420ee91649658b50a752a`, clause `definition`. -/
def IsEventuallyPeriodic {α : Type _} (u : ℕ → α) : Prop :=
  ∃ p n₀ : ℕ, 0 < p ∧ ∀ n : ℕ, n₀ ≤ n → u (n + p) = u n

/-- **Explicit period and preperiod give eventual periodicity.** Let $\alpha$ be a type and
$u : \mathbb{N} \to \alpha$ a sequence. If there are natural numbers $p > 0$ and $n_0$ such that
$u(n + p) = u(n)$ for every natural number $n \ge n_0$, then $u$ is eventually periodic.

Source: concept `jis_sem_2c65b9e5cf5a27c75318c558`; source statements
`jis_2541b4a8b30e59c04cfc2cab`, `jis_6271663997522001b37d9cd0`,
`jis_7be4cb01363efa6d047e19af`, `jis_9f6420ee91649658b50a752a`, clause `witness_api`. -/
theorem IsEventuallyPeriodic.of_witness {α : Type _} {u : ℕ → α} {p n₀ : ℕ}
    (hp : 0 < p) (h : ∀ n : ℕ, n₀ ≤ n → u (n + p) = u n) :
    IsEventuallyPeriodic u :=
  ⟨p, n₀, hp, h⟩

/-- **Period and preperiod of an eventually periodic sequence.** Let $\alpha$ be a type. If a
sequence $u : \mathbb{N} \to \alpha$ is eventually periodic, then there are natural numbers
$p > 0$ and $n_0$ such that $u(n + p) = u(n)$ for every natural number $n \ge n_0$.

Source: concept `jis_sem_2c65b9e5cf5a27c75318c558`; source statements
`jis_2541b4a8b30e59c04cfc2cab`, `jis_6271663997522001b37d9cd0`,
`jis_7be4cb01363efa6d047e19af`, `jis_9f6420ee91649658b50a752a`, clause `witness_api`. -/
theorem IsEventuallyPeriodic.witness_spec {α : Type _} {u : ℕ → α}
    (h : IsEventuallyPeriodic u) :
    ∃ p n₀ : ℕ, 0 < p ∧ ∀ n : ℕ, n₀ ≤ n → u (n + p) = u n :=
  h

/-- **Periodic sequences are eventually periodic.** Let $\alpha$ be a type, let
$u : \mathbb{N} \to \alpha$ be a sequence and let $p > 0$ be a natural number with
$u(n + p) = u(n)$ for every $n \in \mathbb{N}$. Then $u$ is eventually periodic.

Source: concept `jis_sem_2c65b9e5cf5a27c75318c558`; source statements
`jis_2541b4a8b30e59c04cfc2cab`, `jis_6271663997522001b37d9cd0`,
`jis_7be4cb01363efa6d047e19af`, `jis_9f6420ee91649658b50a752a`,
clause `periodic_special_case`. -/
theorem IsEventuallyPeriodic.of_periodic {α : Type _} {u : ℕ → α} {p : ℕ}
    (hp : 0 < p) (h : ∀ n : ℕ, u (n + p) = u n) : IsEventuallyPeriodic u :=
  ⟨p, 0, hp, fun n _ => h n⟩

/-- **Ultimately periodic sequences.** Let $\alpha$ be a type. A sequence
$u : \mathbb{N} \to \alpha$ is called ultimately periodic exactly when it is eventually periodic;
the two terms name the same notion.

Source: concept `jis_sem_2c65b9e5cf5a27c75318c558`; source statements
`jis_2541b4a8b30e59c04cfc2cab`, `jis_6271663997522001b37d9cd0`,
`jis_7be4cb01363efa6d047e19af`, `jis_9f6420ee91649658b50a752a`, clause `alias`. -/
abbrev IsUltimatelyPeriodic {α : Type _} (u : ℕ → α) : Prop :=
  IsEventuallyPeriodic u

/-- **Orbits in a finite set are eventually periodic.** Let $S$ be a finite set, $F : S \to S$ a
map and $r : \mathbb{N} \to S$ a sequence with $r(n + 1) = F(r(n))$ for every $n \in \mathbb{N}$.
Then $r$ is eventually periodic. -/
theorem IsEventuallyPeriodic.of_finite_orbit {S : Type*} [Finite S] (F : S → S) (r : ℕ → S)
    (h : ∀ n, r (n + 1) = F (r n)) : IsEventuallyPeriodic r := by
  obtain ⟨x, y, hne, hxy⟩ := Finite.exists_ne_map_eq_of_infinite r
  wlog hlt : x < y generalizing x y
  · exact this y x hne.symm hxy.symm (by omega)
  refine ⟨y - x, x, by omega, fun n hn => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction d with
  | zero => simpa [Nat.add_sub_cancel' hlt.le] using hxy.symm
  | succ d ih =>
    rw [show x + (d + 1) + (y - x) = x + d + (y - x) + 1 by omega, ← Nat.add_assoc, h, h,
      ih (by omega)]

end

end MetaMathlibExt
