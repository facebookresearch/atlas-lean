/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Zeta

/-!
# A totient-weighted divisor sum identity

If $f$ and $g$ are functions from the positive integers to $\mathbb{Q}$ with
$g(n) = \sum_{d \mid n} f(d)$ for every $n \ge 1$, then for every $k \ge 1$
$$\sum_{d \mid k} \frac{k}{d} \, f(d) = \sum_{d \mid k} \varphi\left(\frac{k}{d}\right) g(d).$$
This is Lemma 4.3 of the arXiv text of Darij Grinberg and Peter Mao, *Necklaces over a Group
with Identity Product* (arXiv:2405.08937v4), published in the Journal of Integer Sequences 29
(2026), Article 26.4.6.

The proof follows theirs. In terms of Dirichlet convolution the hypothesis says
$g = \zeta * f$, and Gauss's identity $\sum_{d \mid n} \varphi(d) = n$ (`Nat.sum_totient`) says
$\varphi * \zeta = \mathrm{id}$, so $\varphi * g = (\varphi * \zeta) * f = \mathrm{id} * f$. We run
this argument with Mathlib's `ArithmeticFunction`, after replacing $f$ and $g$ by the functions
that agree with them on positive integers and vanish at $0$.

## Main statements

* `MetaMathlibExt.sum_div_mul_eq_sum_totient_mul`: the identity above, for `f g : ℕ → ℚ`, whose
  values at `0` play no role.
-/

namespace MetaMathlibExt

-- The hypothesis `hk` of the source's statement is kept for fidelity: for `k = 0` both sides are
-- empty sums, so the proof does not use it.
set_option linter.unusedVariables false in
/-- **Totient-weighted divisor sum identity.** Let $f$ and $g$ be functions from the natural
numbers to the rational numbers such that $g(k) = \sum_{d \mid k} f(d)$ for every positive
integer $k$, where sums over $d \mid k$ run over the positive divisors $d$ of $k$. Then for
every positive integer $k$,
$$\sum_{d \mid k} \frac{k}{d} \, f(d) = \sum_{d \mid k} \varphi\left(\frac{k}{d}\right) g(d),$$
where $\varphi$ is Euler's totient function.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Lemma 9
(`jis-2026-26.4.6-lem-9`). -/
public theorem sum_div_mul_eq_sum_totient_mul (f g : ℕ → ℚ)
    (hfg : ∀ k, 0 < k → g k = ∑ d ∈ k.divisors, f d) (k : ℕ) (hk : 0 < k) :
    ∑ d ∈ k.divisors, ((k / d : ℕ) : ℚ) * f d =
      ∑ d ∈ k.divisors, (Nat.totient (k / d) : ℚ) * g d := by
  -- `f`, `g` and `φ` as arithmetic functions, that is, changed to vanish at `0`
  let F : ArithmeticFunction ℚ := ⟨fun n => if n = 0 then 0 else f n, ite_eq_left rfl⟩
  let G : ArithmeticFunction ℚ := ⟨fun n => if n = 0 then 0 else g n, ite_eq_left rfl⟩
  let T : ArithmeticFunction ℕ := ⟨Nat.totient, Nat.totient_zero⟩
  have hF (n : ℕ) (hn : n ≠ 0) : F n = f n := ite_eq_right hn
  have hG (n : ℕ) (hn : n ≠ 0) : G n = g n := ite_eq_right hn
  -- Gauss's identity `∑ d ∣ n, φ d = n`, that is, `φ * ζ = id`
  have hT : T * ArithmeticFunction.zeta = ArithmeticFunction.id := by
    ext n
    rw [ArithmeticFunction.mul_zeta_apply, ArithmeticFunction.id_apply]
    exact Nat.sum_totient n
  -- the hypothesis `hfg`, that is, `g = ζ * f`
  have hGF : G = (ArithmeticFunction.zeta : ArithmeticFunction ℚ) * F := by
    ext n
    rw [ArithmeticFunction.coe_zeta_mul_apply]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [hG n hn.ne', hfg n hn]
      exact Finset.sum_congr rfl fun d hd => (hF d (Nat.pos_of_mem_divisors hd).ne').symm
  -- hence `id * f = (φ * ζ) * f = φ * g`
  have key : ((ArithmeticFunction.id : ArithmeticFunction ℕ) : ArithmeticFunction ℚ) * F =
      (T : ArithmeticFunction ℚ) * G := by
    rw [hGF, ← mul_assoc, ← ArithmeticFunction.natCoe_mul, hT]
  -- evaluate both convolutions at `k`, as sums over the divisors `d` of `k`
  have hk' := congrArg (fun H : ArithmeticFunction ℚ => H k) key
  simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.id_apply] at hk'
  rw [Nat.sum_divisorsAntidiagonal' (fun a b => (a : ℚ) * F b),
    Nat.sum_divisorsAntidiagonal' (fun a b => (T a : ℚ) * G b)] at hk'
  calc ∑ d ∈ k.divisors, ((k / d : ℕ) : ℚ) * f d
      = ∑ d ∈ k.divisors, ((k / d : ℕ) : ℚ) * F d :=
        Finset.sum_congr rfl fun d hd => by rw [hF d (Nat.pos_of_mem_divisors hd).ne']
    _ = ∑ d ∈ k.divisors, (T (k / d) : ℚ) * G d := hk'
    _ = ∑ d ∈ k.divisors, (Nat.totient (k / d) : ℚ) * g d :=
        Finset.sum_congr rfl fun d hd => by rw [hG d (Nat.pos_of_mem_divisors hd).ne']; rfl

end MetaMathlibExt
