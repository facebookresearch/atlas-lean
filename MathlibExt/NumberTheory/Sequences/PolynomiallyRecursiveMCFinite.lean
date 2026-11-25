/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PRecursiveSequence
public import Mathlib.Algebra.MvPolynomial.Eval
import MathlibExt.Dynamics.EventuallyPeriodicSequence
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace MetaMathlibExt

/-- **MC-finite sequences.** An integer sequence $s$ is MC-finite if for every natural number
$m > 0$ it eventually satisfies, modulo $m$, a linear recurrence with constant integer
coefficients: there are natural numbers $p > 0$ and $q > 0$ and integers $c_0, \dots, c_{p-1}$
such that $s(n + p) \equiv \sum_{i=0}^{p-1} c_i\, s(n + i) \pmod{m}$ for all $n \ge q$.

Source: Filmus, Fischer, Makowsky, and Rakita, "MC-Finiteness of Restricted Set Partition
Functions," Journal of Integer Sequences 26 (2023), Article 23.7.4, lines 281–286. -/
def IsMCFinite (s : ℕ → ℤ) : Prop :=
  ∀ m : ℕ, 0 < m →
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
      ∃ c : Fin p → ℤ, ∀ n : ℕ, q ≤ n →
        (s (n + p) - ∑ i : Fin p, c i * s (n + i.val)) % (↑m : ℤ) = 0

theorem isMCFinite_iff (s : ℕ → ℤ) :
    IsMCFinite s ↔ ∀ m : ℕ, 0 < m →
      ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
        ∃ c : Fin p → ℤ, ∀ n : ℕ, q ≤ n →
          (s (n + p) - ∑ i : Fin p, c i * s (n + i.val)) % (↑m : ℤ) = 0 :=
  Iff.rfl

/-- Eventual periodicity mod `m` yields the MC-finiteness recurrence,
with `c 0 = 1` and all other coefficients `0`. -/
private theorem mc_finite_of_zmod_periodic (s : ℕ → ℤ) (m : ℕ)
    (hper : IsEventuallyPeriodic fun n => ((s n : ℤ) : ZMod m)) :
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ ∃ c : Fin p → ℤ, ∀ n : ℕ, q ≤ n →
      (s (n + p) - ∑ i : Fin p, c i * s (n + i.val)) % (↑m : ℤ) = 0 := by
  obtain ⟨p, q, hp, hper⟩ := hper
  refine ⟨p, q + 1, hp, by omega, (fun i => if i.val = 0 then 1 else 0), ?_⟩
  intro n hn
  have hterm : ∀ i : Fin p, (if i.val = 0 then (1 : ℤ) else 0) * s (n + i.val)
      = (if (⟨0, hp⟩ : Fin p) = i then s (n + i.val) else 0) := by
    intro i
    by_cases hi : i.val = 0
    · have hfin : (⟨0, hp⟩ : Fin p) = i := Fin.ext hi.symm
      simp [hi, hfin]
    · have hfin : (⟨0, hp⟩ : Fin p) ≠ i := by
        intro hcon
        apply hi
        exact (congrArg Fin.val hcon).symm
      simp [hi, hfin]
  have hsup : (∑ i : Fin p, (if i.val = 0 then (1 : ℤ) else 0) * s (n + i.val))
      = s n := by
    simp_rw [hterm, Fintype.sum_ite_eq]
    show s (n + 0) = s n
    rw [Nat.add_zero]
  simp only []
  rw [hsup]
  have hcast : (↑(s (n + p) - s n) : ZMod m) = 0 := by
    rw [Int.cast_sub, sub_eq_zero]
    exact hper n (by omega)
  have hdvd : (↑m : ℤ) ∣ (s (n + p) - s n) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
  exact Int.emod_eq_zero_of_dvd hdvd

/-- **Polynomial recursions give MC-finite sequences.** Let $u_0, \dots, u_k$ be integer sequences
and let $P_0, \dots, P_k$ be polynomials with integer coefficients in $k + 2$ variables such that
$u_i(n+1) = P_i(u_0(n), \dots, u_k(n), n)$ for every $i \le k$ and every $n \ge 0$. Then the
sequence $u_0$ is MC-finite. -/
theorem isMCFinite_of_mvPolynomial_recursion {k : ℕ} (u : Fin (k + 1) → ℕ → ℤ)
    (P : Fin (k + 1) → MvPolynomial (Fin (k + 1) ⊕ Unit) ℤ)
    (hrec : ∀ i : Fin (k + 1), ∀ n : ℕ,
      u i (n + 1) = MvPolynomial.eval
        (Sum.elim (fun j : Fin (k + 1) => u j n) (fun _ : Unit => (↑n : ℤ))) (P i)) :
    IsMCFinite (u 0) := by
  intro m hm
  have : NeZero m := ⟨by omega⟩
  set φ : ℤ →+* ZMod m := Int.castRingHom (ZMod m)
  obtain ⟨p, q0, hp, hper0⟩ :=
    IsEventuallyPeriodic.of_finite_orbit
      (fun a : (Fin (k + 1) → ZMod m) × ZMod m =>
        ((fun i => MvPolynomial.eval (Sum.elim a.1 (fun _ => a.2)) ((P i).map φ)),
          a.2 + 1))
      (fun n : ℕ => ((fun j => φ (u j n)), φ (↑n : ℤ)))
      (by
        intro n
        refine Prod.ext ?_ ?_
        · funext i
          simp only []
          rw [hrec i n, MvPolynomial.map_eval]
          have hfun : (φ ∘ Sum.elim (fun j => u j n) (fun _ : Unit => (↑n : ℤ)))
              = Sum.elim (fun j => φ (u j n)) (fun _ : Unit => φ (↑n : ℤ)) := by
            funext x
            cases x with
            | inl j => rfl
            | inr _ => rfl
          rw [hfun]
        · simp only []
          rw [map_natCast, Nat.cast_add_one, map_natCast])
  refine mc_finite_of_zmod_periodic (u 0) m ⟨p, q0, hp, fun n hn => ?_⟩
  have h2 := hper0 n hn
  have h3 : φ (u (0 : Fin (k + 1)) (n + p)) = φ (u (0 : Fin (k + 1)) n) :=
    congrFun (congrArg Prod.fst h2) 0
  exact h3

/-- **P-recursive sequences with leading coefficient 1 are MC-finite.** Let $s$ be an integer
sequence that is P-recursive of order $k$ with coefficient polynomials $Q_0, \dots, Q_k$ with
integer coefficients, that is, $Q_0(n)\, s_n = \sum_{i=1}^{k} Q_i(n)\, s_{n-i}$ for every $n \ge k$.
If $Q_0 = 1$, then $s$ is MC-finite. -/
theorem IsPRecursiveSequence.isMCFinite {k : ℕ} {Q : Fin (k + 1) → Polynomial ℤ} {s : ℕ → ℤ}
    (hs : IsPRecursiveSequence k Q s) (hQ : Q 0 = 1) : IsMCFinite s := by
  intro m hm
  have hrec : ∀ n : ℕ, k ≤ n →
      s n = ∑ i : Fin k, (Q i.succ).eval (↑n : ℤ) * s (n - (i.val + 1)) := by
    intro n hn
    have h := hs n hn
    rwa [hQ, Polynomial.eval_one, one_mul] at h
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 : ∀ n, s n = 0 := fun n => by simpa using hrec n (Nat.zero_le n)
    exact mc_finite_of_zmod_periodic s m (.of_periodic one_pos fun n => by rw [h0, h0])
  have : NeZero m := ⟨by omega⟩
  set φ : ℤ →+* ZMod m := Int.castRingHom (ZMod m)
  obtain ⟨p, q0, hp, hper0⟩ :=
    IsEventuallyPeriodic.of_finite_orbit
      (fun a : (Fin k → ZMod m) × ZMod m =>
        ((fun i : Fin k =>
          if h : i.val + 1 < k then a.1 ⟨i.val + 1, h⟩
          else ∑ j : Fin k, ((Q j.succ).map φ).eval (a.2 + φ (↑k : ℤ))
            * a.1 ⟨k - 1 - j.val, by have hj := j.isLt; omega⟩),
        a.2 + 1))
      (fun n : ℕ => ((fun i : Fin k => φ (s (n + i.val))), φ (↑n : ℤ)))
      (by
        intro n
        have hceφ : ∀ j : Fin k, φ ((Q j.succ).eval (↑(n + k) : ℤ))
            = ((Q j.succ).map φ).eval (φ (↑n : ℤ) + φ (↑k : ℤ)) := by
          intro j
          have h1 := Polynomial.hom_eval₂ (Q j.succ) (RingHom.id ℤ) φ
            (↑(n + k) : ℤ)
          rw [RingHom.comp_id, Polynomial.eval₂_eq_eval_map φ] at h1
          have eφ : φ ((↑(n + k) : ℕ) : ℤ) = φ (↑n : ℤ) + φ (↑k : ℤ) := by
            rw [Nat.cast_add, map_add]
          rw [eφ] at h1
          exact h1
        have hce : ∀ j : Fin k, (↑((Q j.succ).eval (↑(n + k) : ℤ)) : ZMod m)
            = ((Q j.succ).map φ).eval (φ (↑n : ℤ) + φ (↑k : ℤ)) :=
          fun j => hceφ j
        have hse : ∀ j : Fin k, (↑(s (n + k - (j.val + 1))) : ZMod m)
            = φ (s (n + (k - 1 - j.val))) := by
          intro j
          have hj := j.isLt
          have e : n + k - (j.val + 1) = n + (k - 1 - j.val) := by omega
          have hcast : ∀ a : ℤ, (↑a : ZMod m) = φ a := fun a => rfl
          rw [e, hcast]
        have hterm : ∀ j : Fin k,
            (↑((Q j.succ).eval (↑(n + k) : ℤ)) : ZMod m)
              * (↑(s (n + k - (j.val + 1))) : ZMod m)
            = ((Q j.succ).map φ).eval (φ (↑n : ℤ) + φ (↑k : ℤ))
              * φ (s (n + (k - 1 - j.val))) := by
          intro j
          rw [hce j, hse j]
        have hsum : (↑(∑ i : Fin k, (Q i.succ).eval (↑(n + k) : ℤ)
            * s (n + k - (i.val + 1))) : ZMod m)
            = ∑ j : Fin k, ((Q j.succ).map φ).eval (φ (↑n : ℤ) + φ (↑k : ℤ))
              * φ (s (n + (k - 1 - j.val))) := by
          rw [Int.cast_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Int.cast_mul]
          exact hterm j
        refine Prod.ext ?_ ?_
        · funext i
          simp only []
          by_cases hi : i.val + 1 < k
          · rw [dite_eq_left hi]
            show φ (s (n + 1 + i.val)) = φ (s (n + (i.val + 1)))
            rw [show n + 1 + i.val = n + (i.val + 1) from by omega]
          · rw [dite_eq_right hi]
            have hi2 := i.isLt
            have eN : n + 1 + i.val = n + k := by omega
            have hkn : k ≤ n + k := by omega
            rw [eN, hrec (n + k) hkn]
            exact hsum
        · simp only []
          rw [map_natCast, Nat.cast_add_one, map_natCast])
  refine mc_finite_of_zmod_periodic s m ⟨p, q0, hp, fun n hn => ?_⟩
  have h2 := hper0 n hn
  have h3 : φ (s (n + p)) = φ (s n) :=
    congrFun (congrArg Prod.fst h2) ⟨0, hk⟩
  exact h3

/--
**Polynomially recursive integer sequences are MC-finite.** Call an integer sequence $s$
MC-finite if for every natural number $m > 0$ there are natural numbers $p > 0$ and $q > 0$ and
integers $c_0, \dots, c_{p-1}$ such that $m$ divides $s(n + p) - \sum_{i=0}^{p-1} c_i\, s(n + i)$
for all $n \ge q$. Every integer sequence $s$ has the following two properties.

(1) If there are $k \ge 0$, integer sequences $u_0, \dots, u_k$ with $s = u_0$, and polynomials
$P_0, \dots, P_k$ with integer coefficients in $k + 2$ variables such that
$u_i(n+1) = P_i(u_0(n), \dots, u_k(n), n)$ for all $i \le k$ and all $n \ge 0$, then $s$ is
MC-finite.

(2) Holonomic case: if there are $k > 0$ and polynomials $P_1, \dots, P_k$ with integer
coefficients such that $P_1 \ne 0$, $P_k \ne 0$ and $s(n) = \sum_{i=1}^{k} P_i(n)\, s(n - i)$ for
all $n \ge k$, then $s$ is MC-finite.

Source: Yuval Filmus, Eldar Fischer, and Johann A. Makowsky, with Vsevolod
Rakita, "MC-Finiteness of Restricted Set Partition Functions," Journal of
Integer Sequences 26 (2023), Article 23.7.4, Theorem (label th:MC),
lines 422–427, with the MC-finite definition at lines 281–286 and the
holonomic/PRS definitions at lines 387–412,
<https://cs.uwaterloo.ca/journals/JIS/VOL26/Makowsky/makowsky16.tex>.
It follows from `isMCFinite_of_mvPolynomial_recursion` and
`IsPRecursiveSequence.isMCFinite`; in the holonomic premise the conditions `0 < k`,
`P 1 ≠ 0` and `P k ≠ 0` are unused and keep the source's shape.
Proves `Wanted` entry `polynomially_recursive_MC_finite`.
-/
theorem polynomially_recursive_MC_finite
    (s : ℕ → ℤ) :
    ((∃ k : ℕ, ∃ u : Fin (k + 1) → ℕ → ℤ,
        ∃ P : Fin (k + 1) → MvPolynomial (Fin (k + 1) ⊕ Unit) ℤ,
        s = u 0 ∧
        ∀ i : Fin (k + 1), ∀ n : ℕ,
          u i (n + 1) = MvPolynomial.eval
            (Sum.elim (fun j : Fin (k + 1) => u j n) (fun _ : Unit => (↑n : ℤ))) (P i)) →
      ∀ m : ℕ, 0 < m →
        ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
          ∃ c : Fin p → ℤ, ∀ n : ℕ, q ≤ n →
            (s (n + p) - ∑ i : Fin p, c i * s (n + i.val)) % (↑m : ℤ) = 0) ∧
    ((∃ k : ℕ, ∃ P : ℕ → Polynomial ℤ,
        0 < k ∧ P 1 ≠ 0 ∧ P k ≠ 0 ∧
        ∀ n : ℕ, k ≤ n →
          s n = ∑ i : Fin k, (P (i.val + 1)).eval (↑n : ℤ) * s (n - (i.val + 1))) →
      ∀ m : ℕ, 0 < m →
        ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
          ∃ c : Fin p → ℤ, ∀ n : ℕ, q ≤ n →
            (s (n + p) - ∑ i : Fin p, c i * s (n + i.val)) % (↑m : ℤ) = 0) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨k, u, P, rfl, hrec⟩
    exact isMCFinite_of_mvPolynomial_recursion u P hrec
  · rintro ⟨k, P, -, -, -, hrec⟩
    refine IsPRecursiveSequence.isMCFinite
      (Q := Fin.cons 1 fun i : Fin k => P (i.val + 1)) ?_ (by simp)
    intro n hn
    simpa using hrec n hn

end MetaMathlibExt
