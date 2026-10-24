/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Algebra.Star.BigOperators

@[expose] public section

open scoped BigOperators

namespace MathlibExt.Analysis.Fourier.FiniteAbelianDFTWanted

/-!
# Discrete Fourier transform on a finite abelian group

The Fourier transform of a complex-valued function on a finite abelian group,
as a function on the dual group, with Fourier inversion, the Plancherel
formula, and the shift (modulation) law.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "Fourier transform for finite abelian groups" (reference-only), and
section "Fourier transform", entry "discrete Fourier transform on a finite
abelian group" (empty); A. Terras, Fourier Analysis on Finite Groups and
Applications, Ch. 2–3 (Fourier transform on finite abelian groups).
-/

/--
**Discrete Fourier transform on a finite abelian group.** Let $G$ be a finite abelian group and
$f : G \to \mathbb{C}$. The discrete Fourier transform of $f$ is the function on the additive
characters $\psi$ of $G$ with values in $\mathbb{C}$ (maps with $\psi(0) = 1$ and
$\psi(a + b) = \psi(a)\psi(b)$) given by $\hat f(\psi) = \sum_{x \in G} \psi(x) f(x)$.

No complex conjugate is applied to the character.
-/
def dftFun {G : Type*} [AddCommGroup G] [Fintype G] (f : G → ℂ) :
    AddChar G ℂ → ℂ :=
  fun ψ => ∑ x : G, ψ x * f x

private theorem dft_orthogonality {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (x y : G) :
    (∑ ψ : AddChar G ℂ, star (ψ x) * ψ y) =
      if y = x then (Fintype.card G : ℂ) else 0 := by
  classical
  calc
    (∑ ψ : AddChar G ℂ, star (ψ x) * ψ y) = ∑ ψ : AddChar G ℂ, ψ (-x + y) := by
      apply Finset.sum_congr rfl
      intro ψ _
      rw [AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj, starRingEnd_apply]
    _ = if -x + y = 0 then (Fintype.card G : ℂ) else 0 :=
      AddChar.sum_apply_eq_ite (-x + y)
    _ = if y = x then (Fintype.card G : ℂ) else 0 := by
      simp only [neg_add_eq_zero, eq_comm]

private theorem dft_inversion_sum {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) (x : G) :
    (∑ ψ : AddChar G ℂ, star (ψ x) * dftFun f ψ) = (Fintype.card G : ℂ) * f x := by
  classical
  calc
    (∑ ψ : AddChar G ℂ, star (ψ x) * dftFun f ψ) =
        ∑ ψ : AddChar G ℂ, ∑ y : G, star (ψ x) * (ψ y * f y) := by
      simp only [dftFun, Finset.mul_sum]
    _ = ∑ y : G, ∑ ψ : AddChar G ℂ, star (ψ x) * (ψ y * f y) := by
      rw [Finset.sum_comm]
    _ = ∑ y : G, (∑ ψ : AddChar G ℂ, star (ψ x) * ψ y) * f y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_mul]
      simp only [mul_assoc]
    _ = ∑ y : G, (if y = x then (Fintype.card G : ℂ) else 0) * f y := by
      simp_rw [dft_orthogonality]
    _ = (Fintype.card G : ℂ) * f x := by
      simp

private theorem dft_star_dftFun {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) (ψ : AddChar G ℂ) :
    (∑ x : G, star (f x) * star (ψ x)) = star (dftFun f ψ) := by
  rw [dftFun, star_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [star_mul']
  exact mul_comm _ _

/--
**Fourier inversion on a finite abelian group.** Let $G$ be a finite abelian group with $|G|$
elements, let $f : G \to \mathbb{C}$, and write $\hat f(\psi) = \sum_{y \in G} \psi(y) f(y)$ for
the discrete Fourier transform of $f$ at an additive character $\psi$ of $G$ with values in
$\mathbb{C}$. Then for every $x \in G$,
$f(x) = \frac{1}{|G|} \sum_{\psi} \overline{\psi(x)} \, \hat f(\psi)$, where $\psi$ runs over
all additive characters of $G$ with values in $\mathbb{C}$.

Proof: expand the transform and collapse the inner sum with the orthogonality of characters.
This is the Fourier inversion formula (4.4) of K. Conrad, Characters of finite abelian groups,
Section 4, https://kconrad.math.uconn.edu/blurbs/grouptheory/charthy.pdf, up to reindexing
$\psi \mapsto \psi^{-1}$ (Conrad conjugates the character in the transform rather than in the
inversion sum).

Proves `Wanted` entry `dft_inversion`.

Sources: `undergrad.yaml`, section "Fourier transform", entry "discrete
Fourier transform on a finite abelian group"; A. Terras, Fourier Analysis on
Finite Groups and Applications, Ch. 2, Fourier inversion theorem.
-/
public theorem dft_inversion {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) (x : G) :
    f x = ((Fintype.card G : ℂ))⁻¹ *
      ∑ ψ : AddChar G ℂ, star (ψ x) * dftFun f ψ := by
  rw [dft_inversion_sum]
  exact (inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (f x)).symm

/--
**Plancherel formula on a finite abelian group.** Let $G$ be a finite abelian group with $|G|$
elements, let $f, g : G \to \mathbb{C}$, and write $\hat h(\psi) = \sum_{x \in G} \psi(x) h(x)$
for the discrete Fourier transform of $h : G \to \mathbb{C}$ at an additive character $\psi$ of
$G$ with values in $\mathbb{C}$. Then $\sum_{x \in G} \overline{f(x)} \, g(x)$ equals
$\frac{1}{|G|} \sum_{\psi} \overline{\hat f(\psi)} \, \hat g(\psi)$, where $\psi$ runs over all
additive characters of $G$ with values in $\mathbb{C}$.

Proof: apply Fourier inversion to $g$, exchange the finite sums, and identify the conjugated
inner sum with $\overline{\hat f(\psi)}$. K. Conrad, Characters of finite abelian groups,
Section 4, proves the same identity by checking it on characters.

Proves `Wanted` entry `dft_plancherel`.

Sources: `undergrad.yaml`, section "Fourier transform", entry "discrete
Fourier transform on a finite abelian group"; A. Terras, Fourier Analysis on
Finite Groups and Applications, Ch. 2, Plancherel formula.
-/
public theorem dft_plancherel {G : Type*} [AddCommGroup G] [Fintype G]
    (f g : G → ℂ) :
    (∑ x : G, star (f x) * g x) = ((Fintype.card G : ℂ))⁻¹ *
      ∑ ψ : AddChar G ℂ, star (dftFun f ψ) * dftFun g ψ := by
  classical
  calc
    (∑ x : G, star (f x) * g x) =
        ∑ x : G, star (f x) * ((Fintype.card G : ℂ)⁻¹ *
          ∑ ψ : AddChar G ℂ, star (ψ x) * dftFun g ψ) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [dft_inversion g x]
    _ = ∑ x : G, (Fintype.card G : ℂ)⁻¹ *
        ∑ ψ : AddChar G ℂ, star (f x) * (star (ψ x) * dftFun g ψ) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← mul_assoc, mul_comm (star (f x)), mul_assoc, Finset.mul_sum]
    _ = (Fintype.card G : ℂ)⁻¹ *
        ∑ x : G, ∑ ψ : AddChar G ℂ,
          star (f x) * (star (ψ x) * dftFun g ψ) := by
      rw [Finset.mul_sum]
    _ = (Fintype.card G : ℂ)⁻¹ *
        ∑ ψ : AddChar G ℂ, ∑ x : G,
          star (f x) * (star (ψ x) * dftFun g ψ) := by
      rw [Finset.sum_comm]
    _ = (Fintype.card G : ℂ)⁻¹ *
        ∑ ψ : AddChar G ℂ, (∑ x : G, star (f x) * star (ψ x)) * dftFun g ψ := by
      congr 1
      apply Finset.sum_congr rfl
      intro ψ _
      rw [Finset.sum_mul]
      simp only [mul_assoc]
    _ = (Fintype.card G : ℂ)⁻¹ *
        ∑ ψ : AddChar G ℂ, star (dftFun f ψ) * dftFun g ψ := by
      simp_rw [dft_star_dftFun]

/--
**Translation modulates the discrete Fourier transform.** Let $G$ be a finite abelian group,
$f : G \to \mathbb{C}$, $t \in G$, and $\psi$ an additive character of $G$ with values in
$\mathbb{C}$, and write $\hat h(\psi) = \sum_{x \in G} \psi(x) h(x)$ for the discrete Fourier
transform of $h : G \to \mathbb{C}$. If $g(x) = f(x - t)$ for all $x \in G$, then
$\hat g(\psi) = \psi(t) \hat f(\psi)$.

Proof: reindex the finite sum by $x \mapsto x + t$ and use $\psi(x + t) = \psi(x) \psi(t)$.

Proves `Wanted` entry `dftFun_translate`.

Sources: `undergrad.yaml`, section "Fourier transform", entry "discrete
Fourier transform on a finite abelian group"; A. Terras, Fourier Analysis on
Finite Groups and Applications, Ch. 2 (translation and modulation).
-/
public theorem dftFun_translate {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) (t : G) (ψ : AddChar G ℂ) :
    dftFun (fun x => f (x - t)) ψ = ψ t * dftFun f ψ := by
  classical
  calc
    dftFun (fun x => f (x - t)) ψ = ∑ x : G, ψ x * f (x - t) := rfl
    _ = ∑ x : G, ψ (x + t) * f x := by
      symm
      apply Fintype.sum_equiv (Equiv.addRight t)
      intro x
      simp
    _ = ∑ x : G, (ψ x * ψ t) * f x := by
      simp_rw [AddChar.map_add_eq_mul]
    _ = ψ t * ∑ x : G, ψ x * f x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = ψ t * dftFun f ψ := rfl

end MathlibExt.Analysis.Fourier.FiniteAbelianDFTWanted
