/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.NumberTheory.Multiplicity

/-!
# Powers of three dividing a cube plus one

Tripling the exponent in `2 ^ k + 1` increases the multiplicity of three by at most one.
-/

namespace MetaMathlibExt

/-- **Bounding the power of $3$ dividing $2^{3k} + 1$.** For all natural numbers $m$ and $k$, if
$3^{m+1}$ does not divide $2^k + 1$, then $3^{m+2}$ does not divide $2^{3k} + 1$.

For odd $k$, where $3$ divides $2^k + 1$, this says: if $3^m$ does not divide $(2^k + 1)/3$,
then $3^{m+1}$ does not divide $(2^{3k} + 1)/3$. For even $k$ the conclusion holds since $3$
does not divide $2^{3k} + 1$.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Lemma 3
(`integers-2026-A107-lem-3`). -/
public theorem three_pow_not_dvd_two_pow_add_one_cube (m k : ℕ)
    (h : ¬ 3 ^ (m + 1) ∣ 2 ^ k + 1) : ¬ 3 ^ (m + 2) ∣ 2 ^ (3 * k) + 1 := by
  intro hd
  apply h
  have h₃ : 3 ∣ 2 ^ (3 * k) + 1 := (dvd_pow_self 3 (by omega : m + 2 ≠ 0)).trans hd
  rw [pow_mul] at h₃
  have hcong : 2 ^ 3 ≡ 2 [MOD 3] := by decide
  have hbase : 3 ∣ 2 ^ k + 1 :=
    (((hcong.pow k).add_right 1).dvd_iff dvd_rfl).mp h₃
  have hval := Nat.multiplicity_pow_add_pow (by decide : Odd 3) hbase
    (fun hdvd => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hdvd))
    (by decide : Odd 3)
  rw [one_pow, Nat.Prime.multiplicity_self] at hval
  rw [Nat.mul_comm 3 k, pow_mul, multiplicity_dvd_iff_le (by positivity)] at hd
  rw [multiplicity_dvd_iff_le (by positivity)]
  omega

end MetaMathlibExt
