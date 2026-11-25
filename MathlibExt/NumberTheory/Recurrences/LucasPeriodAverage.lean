/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LucasSequence
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Ring

/-!
# Sums of second-order recurrences over Lucas periods

For a positive modulus coprime to $Q$, the recurrence step permutes pairs of residues.
When the Lucas initial pair returns, every initial pair returns. If the modulus is also
coprime to $P-Q-1$, telescoping shows that it divides the sum over any whole number of periods.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Period of a Lucas sequence modulo $m$.** For a Lucas sequence $U = U(P, Q)$ and a natural
number $m$, the least period $\pi_U(m)$ of $U$ modulo $m$ is the minimal period of the pair
$(0, 1)$ under the map $(x, y) \mapsto (y, P y - Q x)$ on pairs of residues modulo $m$, that is,
the least $r > 0$ with $U_r \equiv 0 \pmod m$ and $U_{r+1} \equiv 1 \pmod m$, and $0$ if there
is no such $r$.

For $m > 0$, $\pi_U(m) = 0$ exactly when $U$ is not purely periodic modulo $m$, that is, when
$\gcd(m, Q) > 1$. For $m = 0$ the residues are integers and the congruences are equalities; this
value has no meaning in the paper (for the Fibonacci sequence it is $0$).

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Section 1, equation
(1.11). -/
noncomputable def lucasUPeriod (params : LucasSequenceParams) (m : ℕ) : ℕ :=
  Function.minimalPeriod
    (fun x : ZMod m × ZMod m => (x.2, (params.p : ZMod m) * x.2 - (params.q : ZMod m) * x.1))
    (0, 1)

namespace secondOrder_sum_dvd_of_period_dvd

variable {R : Type*} [CommRing R]

private def step (p q : R) (x : R × R) : R × R := (x.2, p * x.2 - q * x.1)

/-- A return of the Lucas initial pair gives a return for any solution of the recurrence. -/
private theorem return_pair {p q : R} {r : ℕ}
    (hr : Function.IsPeriodicPt (step p q) r (0, 1))
    (w : ℕ → R) (hw : ∀ k, w (k + 2) = p * w (k + 1) - q * w k) :
    (w r, w (r + 1)) = (w 0, w 1) := by
  -- This linear change of initial values sends (0, 1) to the initial pair of w.
  let g (x : R × R) := (w 0 * x.2 + (w 1 - p * w 0) * x.1, w 1 * x.2 - q * w 0 * x.1)
  have comm : Function.Commute g (step p q) := by
    intro x
    apply Prod.ext <;> dsimp [g, step] <;> ring
  have hreturn := hr.map comm
  have hseed : g (0, 1) = (w 0, w 1) := by simp [g]
  rw [hseed] at hreturn
  have orbit (k : ℕ) : (step p q)^[k] (w 0, w 1) = (w k, w (k + 1)) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      exact Prod.ext rfl (hw k).symm
  exact (orbit r).symm.trans hreturn

private theorem mul_sum {p q : R} (w : ℕ → R)
    (hw : ∀ k, w (k + 2) = p * w (k + 1) - q * w k) (r : ℕ) :
    (p - q - 1) * ∑ i ∈ Finset.Icc 1 r, w i = w (r + 1) - w 1 - q * (w r - w 0) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 r), mul_add, ih, hw r]
    ring

end secondOrder_sum_dvd_of_period_dvd

-- The source assumes the factor is nonzero. Coprimality already suffices for cancellation.
set_option linter.unusedVariables false in
open secondOrder_sum_dvd_of_period_dvd in
/-- **Sums of a second-order recurrence over whole periods.** Let $P, Q$ be integers with $Q \ne 0$,
let $U = U(P, Q)$ be their Lucas sequence, write $a = P$ and $b = -Q$, and suppose
$a + b - 1 \ne 0$. Let $n > 0$ be coprime to $b(a + b - 1)$, and let $\pi_U(n)$ be the period of
$U$ modulo $n$: the least $r > 0$ with $U_r \equiv 0$ and $U_{r+1} \equiv 1 \pmod n$, or $0$ if
there is none. Then $\pi_U(n) > 0$, and for every $r \ge 0$ divisible by $\pi_U(n)$ and every
integer sequence $w$ with $w_{k+2} = a w_{k+1} + b w_k$ for all $k \ge 0$, $n$ divides
$w_1 + \dots + w_r$.

Part (ii) of the corollary is false as printed and is omitted: for $(a, b) = (-6, 7)$, so that
$a + b - 1 = 0$, the number $n = 3$ is coprime to $7 \cdot (-8)$ and $\pi_U(3) = 2$, but
$U_1 + U_2 = 1 - 6 = -5$.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Corollary 2.2
(`integers-2024-A36-cor-2-2`). -/
theorem secondOrder_sum_dvd_of_period_dvd (params : LucasSequenceParams)
    (hab : params.p - params.q - 1 ≠ 0) (n : ℕ) (hn : 0 < n)
    (hcop : IsCoprime (n : ℤ) (params.q * (params.p - params.q - 1))) :
    0 < lucasUPeriod params n ∧
    ∀ r, lucasUPeriod params n ∣ r → ∀ w : ℕ → ℤ,
      (∀ k, w (k + 2) = params.p * w (k + 1) - params.q * w k) →
      (n : ℤ) ∣ ∑ i ∈ Finset.Icc 1 r, w i := by
  have : NeZero n := ⟨hn.ne'⟩
  have hq : IsUnit (params.q : ZMod n) := by
    simpa [ZMod.natCast_self, isCoprime_zero_left] using
      hcop.of_mul_right_left.intCast (R := ZMod n)
  have hinj : Function.Injective (step (params.p : ZMod n) (params.q : ZMod n)) := by
    intro x y h
    have h₂ : x.2 = y.2 := congrArg Prod.fst h
    have h₁ := congrArg Prod.snd h
    dsimp [step] at h₁
    rw [h₂] at h₁
    exact Prod.ext (hq.mul_left_cancel (sub_right_inj.mp h₁)) h₂
  refine ⟨Function.minimalPeriod_pos_of_mem_periodicPts (hinj.mem_periodicPts (0, 1)), ?_⟩
  intro r hr w hw
  let v (k : ℕ) : ZMod n := w k
  have hv (k : ℕ) : v (k + 2) = params.p * v (k + 1) - params.q * v k := by
    simp [v, hw k]
  have hperiod := Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr hr
  obtain ⟨h₀, h₁⟩ := Prod.mk.inj (return_pair hperiod v hv)
  apply hcop.of_mul_right_right.dvd_of_dvd_mul_left
  rw [mul_sum w hw]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp
  push_cast
  change v (r + 1) - v 1 - params.q * (v r - v 0) = 0
  simp [h₀, h₁]

end

end MetaMathlibExt
