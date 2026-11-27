/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TwoComplexity

/-!
# Adding a small multiple to a multiple of the square

For `l > 1`, adding `a ≤ l - 1` copies of `l` to a positive multiple of `l²` increases
its `l`-complexity by exactly `a`.

Reference: Pengcheng Zhang, "The 2-Complexity of Even Positive Integers",
*INTEGERS* 24 (2024), Article A109, Proposition 2.
-/

set_option autoImplicit false

namespace MathlibExt.NumberTheory.TwoComplexityWanted

private theorem build_multiple (l m : ℕ) (hm : 0 < m) : CanBuild l m (m * l) := by
  induction m, hm using Nat.le_induction with
  | base => simpa using (CanBuild.base (l := l))
  | succ m _ ih => simpa only [Nat.add_mul, one_mul] using ih.add CanBuild.base

private theorem build_add_copies {l k n : ℕ} (h : CanBuild l k n) (a : ℕ) :
    CanBuild l (k + a) (n + a * l) := by
  induction a with
  | zero => simpa using h
  | succ a ih =>
    simpa only [Nat.add_mul, one_mul, Nat.add_assoc] using ih.add CanBuild.base

private theorem build_dvd {l k n : ℕ} (h : CanBuild l k n) : l ∣ n := by
  induction h with
  | base => exact dvd_refl l
  | add _ _ ihx ihy => exact dvd_add ihx ihy
  | mul _ _ ihx _ => exact dvd_mul_of_dvd_left ihx _

private theorem build_split {l k n : ℕ} (h : CanBuild l k n) :
    ∃ j c d : ℕ, k = j + c ∧ n = d + c * l ∧ l ^ 2 ∣ d ∧
      ((j = 0 ∧ d = 0) ∨ CanBuild l j d) := by
  induction h with
  | base => exact ⟨0, 1, 0, by simp, by simp, dvd_zero _, Or.inl ⟨rfl, rfl⟩⟩
  | @add kx ky x y hx hy ihx ihy =>
    obtain ⟨jx, cx, dx, hkx, hnx, hdx, hbx⟩ := ihx
    obtain ⟨jy, cy, dy, hky, hny, hdy, hby⟩ := ihy
    refine ⟨jx + jy, cx + cy, dx + dy, by omega, ?_, dvd_add hdx hdy, ?_⟩
    · rw [hnx, hny, Nat.add_mul]
      omega
    · rcases hbx with ⟨rfl, rfl⟩ | hbx <;> rcases hby with ⟨rfl, rfl⟩ | hby
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr (by simpa using hby)
      · exact Or.inr (by simpa using hbx)
      · exact Or.inr (hbx.add hby)
  | @mul kx ky x y hx hy _ _ =>
    exact ⟨kx + ky, 0, x * y, by simp, by simp,
      by simpa only [pow_two] using mul_dvd_mul (build_dvd hx) (build_dvd hy),
      Or.inr (hx.mul hy)⟩

private theorem build_remove_copies {l k n b a : ℕ} (h : CanBuild l k n)
    (hl : 1 < l) (hn : n = b + a * l) (hb : l ^ 2 ∣ b) (hb0 : 1 ≤ b)
    (ha : a ≤ l - 1) : ∃ j, CanBuild l j b ∧ j + a = k := by
  obtain ⟨j, c, d, hk, hd, hdvd, hbuild⟩ := build_split h
  obtain ⟨t, ht⟩ := hb
  obtain ⟨u, hu⟩ := hdvd
  have hcoef : (l * t + a) * l = (l * u + c) * l := by
    rw [hn] at hd
    rw [ht, hu, pow_two] at hd
    nlinarith only [hd]
  have he := Nat.eq_of_mul_eq_mul_right (by omega : 0 < l) hcoef
  have ha' : a < l := by omega
  have hmod : a = c % l := by
    have he' := congrArg (fun x => x % l) he
    simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt ha'] using he'
  have hac : a ≤ c := by rw [hmod]; exact Nat.mod_le c l
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hac
  have hb' : b = d + r * l := by
    rw [hn, hr, Nat.add_mul] at hd
    omega
  rcases hbuild with ⟨hj, hd0⟩ | hbuild
  · have hr0 : 0 < r := by
      rw [hd0, zero_add] at hb'
      nlinarith only [hb', hb0]
    refine ⟨r, ?_, by omega⟩
    simpa only [hb', hd0, zero_add] using build_multiple l r hr0
  · refine ⟨j + r, ?_, by omega⟩
    simpa only [hb'] using build_add_copies hbuild r

/-- **Adding a small multiple of $l$ to a multiple of $l^2$.** Write $\|n\|_l$ for the
$l$-complexity of $n$. Let $l > 1$, let $b \ge 1$ be a multiple of $l^2$, let $a$ be a natural
number with $a \le l - 1$, and let $n = b + a l$. Then $\|n\|_l = \|b\|_l + a$.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Proposition 2. -/
public theorem complexityL_decomp (l n b a : ℕ) (hl : 1 < l)
    (hn : n = b + a * l) (hb : l ^ 2 ∣ b) (hb0 : 1 ≤ b)
    (ha : a ≤ l - 1) :
    complexityL l n = complexityL l b + a
    := by
  have hbl : l ∣ b := dvd_trans (dvd_pow_self l (by decide : 2 ≠ 0)) hb
  obtain ⟨m, hm⟩ := hbl
  have hm0 : 0 < m := by nlinarith only [hm, hb0]
  have hbbuild : ∃ k, CanBuild l k b :=
    ⟨m, by simpa only [hm, Nat.mul_comm] using build_multiple l m hm0⟩
  have hnbuild := build_add_copies (complexityL_spec hbbuild) a
  rw [← hn] at hnbuild
  apply Nat.le_antisymm (complexityL_min_le hnbuild)
  obtain ⟨j, hj, hjk⟩ := build_remove_copies (complexityL_spec ⟨_, hnbuild⟩)
    hl hn hb hb0 ha
  have := complexityL_min_le hj
  omega

end MathlibExt.NumberTheory.TwoComplexityWanted
