/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

attribute [local instance] Classical.decEq

@[expose] public section

namespace WeierstrassCurve.Affine

/-!
# Supersingular elliptic curves

This file defines supersingularity over an algebraic closure of `ZMod p` through trivial geometric
`p`-torsion and relates it to trivial geometric `p ^ r`-torsion for every positive `r`.
-/

/-- An elliptic curve over an algebraic closure of `ZMod p` is supersingular when every geometric
point killed by `p` is zero.

This is the `r = 1` form of the equivalent torsion condition in arXiv:2308.11539v1,
`main.tex`, lines 164–170.
-/
def IsSupersingular {p : ℕ} [Fact p.Prime]
    (W : WeierstrassCurve.Affine (AlgebraicClosure (ZMod p))) [W.IsElliptic] : Prop :=
  ∀ P : W.Point, p • P = 0 → P = 0

theorem IsSupersingular.iff_pow_torsion {p : ℕ} [Fact p.Prime]
    (W : WeierstrassCurve.Affine (AlgebraicClosure (ZMod p))) [W.IsElliptic] :
    W.IsSupersingular ↔
      ∀ r : ℕ, 0 < r → ∀ P : W.Point, (p ^ r) • P = 0 → P = 0 := by
  constructor
  · intro h
    have aux : ∀ (n : ℕ) (P : W.Point), (p ^ (n + 1)) • P = 0 → P = 0 := by
      intro n
      induction n with
      | zero =>
        intro P hP
        exact h P (by simpa using hP)
      | succ n ih =>
        intro P hP
        have hP2 : p ^ (n + 1) • (p • P) = 0 := by
          rw [← mul_nsmul]
          simpa [pow_succ'] using hP
        exact h P (ih (p • P) hP2)
    intro r hr P hP
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
    exact aux n P hP
  · intro h P hP
    exact h 1 (by omega) P (by simpa using hP)

/-- **Supersingularity from trivial prime-power torsion.** Let $p$ be a prime and let $E$ be an
elliptic curve over an algebraic closure $\overline{\mathbb{F}}_p$ of $\mathbb{Z}/p\mathbb{Z}$. If
for every integer $r \ge 1$ the only point $P \in E(\overline{\mathbb{F}}_p)$ with $p^r P = 0$ is
$P = 0$, then $E$ is supersingular. -/
theorem IsSupersingular.of_pow_torsion {p : ℕ} [Fact p.Prime]
    (W : WeierstrassCurve.Affine (AlgebraicClosure (ZMod p))) [W.IsElliptic]
    (h : ∀ r : ℕ, 0 < r → ∀ P : W.Point, (p ^ r) • P = 0 → P = 0) :
    W.IsSupersingular :=
  (IsSupersingular.iff_pow_torsion W).mpr h

/-- **Supersingular curves have trivial prime-power torsion.** Let $p$ be a prime and let $E$ be a
supersingular elliptic curve over an algebraic closure $\overline{\mathbb{F}}_p$ of
$\mathbb{Z}/p\mathbb{Z}$. Then for every integer $r \ge 1$, every point
$P \in E(\overline{\mathbb{F}}_p)$ with $p^r P = 0$ is $P = 0$. -/
theorem IsSupersingular.pow_torsion {p : ℕ} [Fact p.Prime]
    (W : WeierstrassCurve.Affine (AlgebraicClosure (ZMod p))) [W.IsElliptic]
    (h : W.IsSupersingular) {r : ℕ} (hr : 0 < r)
    {P : W.Point} (hP : (p ^ r) • P = 0) : P = 0 :=
  (IsSupersingular.iff_pow_torsion W).mp h r hr P hP

end WeierstrassCurve.Affine
