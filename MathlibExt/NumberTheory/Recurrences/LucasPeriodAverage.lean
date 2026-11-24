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
# Periods and sums of second-order recurrences

For a positive modulus coprime to $Q$, the recurrence step permutes pairs of residues.
The full Lucas period preserves every solution, and the restricted period multiplies every
solution by the same Lucas term. If the modulus is also coprime to $P-Q-1$, telescoping shows
that it divides the sum over any whole number of periods.
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

/-- **Restricted period of a Lucas sequence modulo $m$.** For a Lucas sequence $U = U(P, Q)$ and
a natural number $m$, the least restricted period $\rho_U(m)$ of $U$ modulo $m$ is the least
$s > 0$ such that $m \mid U_s$ and $U_{s+1}$ is coprime to $m$, and $0$ if there is no such $s$.

In the paper's terms, $U_{s+1} \equiv M \pmod m$ for a multiplier $M$ coprime to $m$; for
$s = \rho_U(m)$ this $U_{s+1}$ is the multiplier $M_U(m)$.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Section 1, equations
(1.10) and (1.12). -/
noncomputable def lucasURestrictedPeriod (params : LucasSequenceParams) (m : ℕ) : ℕ :=
  sInf {s : ℕ | 0 < s ∧ (m : ℤ) ∣ lucasU params s ∧ IsCoprime (lucasU params (s + 1)) (m : ℤ)}

namespace lucasUPeriod_isPeriod_of_secondOrder

variable {R : Type*} [CommRing R]

private def step (p q : R) (x : R × R) : R × R := (x.2, p * x.2 - q * x.1)

private theorem iterate_pair {p q : R} (w : ℕ → R)
    (hw : ∀ k, w (k + 2) = p * w (k + 1) - q * w k) (r : ℕ) :
    (step p q)^[r] (w 0, w 1) = (w r, w (r + 1)) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih]
    exact Prod.ext rfl (hw r).symm

/-- If the Lucas pair returns up to a scalar, so does every initial pair. -/
private theorem scaled_pair {p q c : R} {r : ℕ} (hr : (step p q)^[r] (0, 1) = (0, c))
    (w : ℕ → R) (hw : ∀ k, w (k + 2) = p * w (k + 1) - q * w k) :
    (w r, w (r + 1)) = (c * w 0, c * w 1) := by
  -- This linear change of initial values sends (0, 1) to the initial pair of w.
  let g (x : R × R) := (w 0 * x.2 + (w 1 - p * w 0) * x.1, w 1 * x.2 - q * w 0 * x.1)
  have comm : Function.Commute g (step p q) := by
    intro x
    apply Prod.ext <;> dsimp [g, step] <;> ring
  have h := comm.iterate_right r (0, 1)
  rw [hr, show g (0, 1) = (w 0, w 1) by simp [g], iterate_pair w hw] at h
  simpa [g, mul_comm] using h.symm

private theorem period_pos (params : LucasSequenceParams) (m : ℕ) (hm : 0 < m)
    (hmb : IsCoprime (m : ℤ) params.q) : 0 < lucasUPeriod params m := by
  have : NeZero m := ⟨hm.ne'⟩
  have hq : IsUnit (params.q : ZMod m) := by
    simpa [ZMod.natCast_self, isCoprime_zero_left] using hmb.intCast (R := ZMod m)
  have hinj : Function.Injective (step (params.p : ZMod m) (params.q : ZMod m)) := by
    intro x y h
    have h₂ : x.2 = y.2 := congrArg Prod.fst h
    have h₁ := congrArg Prod.snd h
    dsimp [step] at h₁
    rw [h₂] at h₁
    exact Prod.ext (hq.mul_left_cancel (sub_right_inj.mp h₁)) h₂
  exact Function.minimalPeriod_pos_of_mem_periodicPts (hinj.mem_periodicPts (0, 1))

end lucasUPeriod_isPeriod_of_secondOrder

open lucasUPeriod_isPeriod_of_secondOrder in
/-- **Periods of second-order recurrences modulo $m$.** Let $U$ be the Lucas sequence with
integer parameters $P$ and $Q \neq 0$, let $m$ be a positive integer with $\gcd(m, Q) = 1$, and
write $\pi(m)$ and $\rho(m)$ for the period and the restricted period of $U$ modulo $m$. Then
$\pi(m) > 0$ and $\rho(m) > 0$, and every integer sequence $w$ with
$w_{k+2} = P w_{k+1} - Q w_k$ for all $k$ satisfies $w_{n + \pi(m)} \equiv w_n \pmod m$ and
$w_{n + \rho(m)} \equiv U_{\rho(m) + 1} w_n \pmod m$ for every natural number $n$.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 1.1
(`integers-2024-A36-thm-1-1`). -/
theorem lucasUPeriod_isPeriod_of_secondOrder (params : LucasSequenceParams)
    (m : ℕ) (hm : 0 < m) (hmb : IsCoprime (m : ℤ) params.q) (w : ℕ → ℤ)
    (hw : ∀ k, w (k + 2) = params.p * w (k + 1) - params.q * w k) :
    0 < lucasUPeriod params m ∧ 0 < lucasURestrictedPeriod params m ∧
    (∀ n, w (n + lucasUPeriod params m) ≡ w n [ZMOD m]) ∧
    (∀ n, w (n + lucasURestrictedPeriod params m) ≡
      lucasU params (lucasURestrictedPeriod params m + 1) * w n [ZMOD m]) := by
  let π := lucasUPeriod params m
  let ρ := lucasURestrictedPeriod params m
  let u (k : ℕ) : ZMod m := lucasU params k
  let f := step (params.p : ZMod m) (params.q : ZMod m)
  have orbit (k : ℕ) : f^[k] (0, 1) = (u k, u (k + 1)) := by
    have hu (j : ℕ) : u (j + 2) = params.p * u (j + 1) - params.q * u j := by
      simp [u, lucasU_add_two]
    simpa [u, lucasU, f] using iterate_pair u hu k
  have hπ : f^[π] (0, 1) = (0, 1) := Function.iterate_minimalPeriod
  have hπpos := period_pos params m hm hmb
  obtain ⟨hu₀, hu₁⟩ := Prod.mk.inj ((orbit π).symm.trans hπ)
  -- The full period witnesses nonemptiness in the definition of the restricted period.
  have hcop : IsCoprime (lucasU params (π + 1)) (m : ℤ) := by
    have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (lucasU params (π + 1)) m).mp
      (by simpa [u] using hu₁.symm)
    simpa using IsCoprime.add_one_left_of_dvd hd
  have hmem : π ∈ {s : ℕ | 0 < s ∧ (m : ℤ) ∣ lucasU params s ∧
      IsCoprime (lucasU params (s + 1)) (m : ℤ)} :=
    ⟨hπpos, (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp hu₀, hcop⟩
  obtain ⟨hρpos, hρdvd, -⟩ := Nat.sInf_mem ⟨π, hmem⟩
  have shift (r : ℕ) (c : ZMod m) (hr : f^[r] (0, 1) = (0, c)) (n : ℕ) :
      (w (n + r) : ZMod m) = c * w n := by
    let v (k : ℕ) : ZMod m := w (n + k)
    have hv (k : ℕ) : v (k + 2) = params.p * v (k + 1) - params.q * v k := by
      simp [v, ← Nat.add_assoc, hw]
    exact congrArg Prod.fst (scaled_pair hr v hv)
  refine ⟨hπpos, hρpos, fun n => ?_, fun n => ?_⟩
  · exact (ZMod.intCast_eq_intCast_iff _ _ m).mp (by simpa using shift π 1 hπ n)
  · have hρ : f^[ρ] (0, 1) = (0, u (ρ + 1)) := by
      rw [orbit, show u ρ = 0 from (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mpr hρdvd]
    exact (ZMod.intCast_eq_intCast_iff _ _ m).mp (by simpa [u] using shift ρ _ hρ n)

namespace secondOrder_sum_dvd_of_period_dvd

variable {R : Type*} [CommRing R]

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
open secondOrder_sum_dvd_of_period_dvd lucasUPeriod_isPeriod_of_secondOrder in
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
  refine ⟨period_pos params n hn hcop.of_mul_right_left, ?_⟩
  intro r hr w hw
  let v (k : ℕ) : ZMod n := w k
  have hv (k : ℕ) : v (k + 2) = params.p * v (k + 1) - params.q * v k := by
    simp [v, hw k]
  have hperiod := Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr hr
  have hreturn : (v r, v (r + 1)) = (v 0, v 1) := by
    simpa using scaled_pair (c := 1) hperiod v hv
  obtain ⟨h₀, h₁⟩ := Prod.mk.inj hreturn
  apply hcop.of_mul_right_right.dvd_of_dvd_mul_left
  rw [mul_sum w hw]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp
  push_cast
  change v (r + 1) - v 1 - params.q * (v r - v 0) = 0
  simp [h₀, h₁]

end

end MetaMathlibExt
