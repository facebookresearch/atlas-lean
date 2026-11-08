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

/-- Eventually periodic sequence (concept `jis_sem_2c65b9e5cf5a27c75318c558`;
source statements `jis_2541b4a8b30e59c04cfc2cab`, `jis_6271663997522001b37d9cd0`,
`jis_7be4cb01363efa6d047e19af`, `jis_9f6420ee91649658b50a752a`, clause `definition`):
a sequence `u : ℕ → α` admitting a positive period `p` and a preperiod `n₀`
with `u (n + p) = u n` for every `n ≥ n₀`. -/
def IsEventuallyPeriodic {α : Type _} (u : ℕ → α) : Prop :=
  ∃ p n₀ : ℕ, 0 < p ∧ ∀ n : ℕ, n₀ ≤ n → u (n + p) = u n

/-- Constructor for eventual periodicity (concept `jis_sem_2c65b9e5cf5a27c75318c558`;
source statements `jis_2541b4a8b30e59c04cfc2cab`, `jis_6271663997522001b37d9cd0`,
`jis_7be4cb01363efa6d047e19af`, `jis_9f6420ee91649658b50a752a`, clause `witness_api`):
explicit period and preperiod witnesses give eventual periodicity. -/
theorem IsEventuallyPeriodic.of_witness {α : Type _} {u : ℕ → α} {p n₀ : ℕ}
    (hp : 0 < p) (h : ∀ n : ℕ, n₀ ≤ n → u (n + p) = u n) :
    IsEventuallyPeriodic u :=
  ⟨p, n₀, hp, h⟩

/-- Eliminator for eventual periodicity (concept `jis_sem_2c65b9e5cf5a27c75318c558`;
source statements `jis_2541b4a8b30e59c04cfc2cab`, `jis_6271663997522001b37d9cd0`,
`jis_7be4cb01363efa6d047e19af`, `jis_9f6420ee91649658b50a752a`, clause `witness_api`):
the defining condition with explicit period and preperiod witnesses. -/
theorem IsEventuallyPeriodic.witness_spec {α : Type _} {u : ℕ → α}
    (h : IsEventuallyPeriodic u) :
    ∃ p n₀ : ℕ, 0 < p ∧ ∀ n : ℕ, n₀ ≤ n → u (n + p) = u n :=
  h

/-- A purely periodic sequence is eventually periodic with preperiod zero
(concept `jis_sem_2c65b9e5cf5a27c75318c558`;
source statements `jis_2541b4a8b30e59c04cfc2cab`, `jis_6271663997522001b37d9cd0`,
`jis_7be4cb01363efa6d047e19af`, `jis_9f6420ee91649658b50a752a`,
clause `periodic_special_case`). -/
theorem IsEventuallyPeriodic.of_periodic {α : Type _} {u : ℕ → α} {p : ℕ}
    (hp : 0 < p) (h : ∀ n : ℕ, u (n + p) = u n) : IsEventuallyPeriodic u :=
  ⟨p, 0, hp, fun n _ => h n⟩

/-- Ultimately periodic is terminology for the same concept (concept
`jis_sem_2c65b9e5cf5a27c75318c558`;
source statements `jis_2541b4a8b30e59c04cfc2cab`, `jis_6271663997522001b37d9cd0`,
`jis_7be4cb01363efa6d047e19af`, `jis_9f6420ee91649658b50a752a`, clause `alias`):
recorded here as an abbreviation so its semantics are not duplicated. -/
abbrev IsUltimatelyPeriodic {α : Type _} (u : ℕ → α) : Prop :=
  IsEventuallyPeriodic u

/-- An orbit `r (n + 1) = F (r n)` of a map on a finite type is eventually periodic. -/
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
