/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Zsqrtd.Basic
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity
public import MathlibExt.NumberTheory.ZsqrtdNormFactorization

/-!
# Gaussian prime basics

Units, norm-primality, and small primes in the Gaussian integers `ℤ[i]`.
-/

local notation "ℤ[i]" => GaussianInt

namespace GaussianInt

@[expose] public section

/-- **Units of the Gaussian integers.** A Gaussian integer $x \in \mathbb{Z}[i]$ is a unit if
and only if $x$ is one of $1$, $-1$, $i$ and $-i$. -/
public theorem gaussianInt_isUnit_iff (x : ℤ[i]) :
    IsUnit x ↔ x = 1 ∨ x = -1 ∨ x = ⟨0, 1⟩ ∨ x = ⟨0, -1⟩ := by
  rw [← Zsqrtd.norm_eq_one_iff]
  constructor
  · intro h
    have hnorm : Zsqrtd.norm x = 1 := by
      have hnn := GaussianInt.norm_nonneg x
      have hcast : ((Zsqrtd.norm x).natAbs : ℤ) = Zsqrtd.norm x :=
        Int.natAbs_of_nonneg hnn
      omega
    cases x with
    | mk r i =>
      have h2 : r * r - -1 * i * i = 1 := hnorm
      have hsum : r * r + i * i = 1 := by linear_combination h2
      have hr : r * r = 0 ∨ r * r = 1 := by
        have g1 : 0 ≤ r * r := mul_self_nonneg r
        have g2 : 0 ≤ i * i := mul_self_nonneg i
        omega
      have hi : i * i = 0 ∨ i * i = 1 := by
        have g1 : 0 ≤ r * r := mul_self_nonneg r
        have g2 : 0 ≤ i * i := mul_self_nonneg i
        omega
      rcases hr with hr | hr <;> rcases hi with hi | hi
      · exfalso; omega
      · rw [mul_self_eq_zero] at hr
        rw [mul_self_eq_one_iff] at hi
        subst hr
        rcases hi with rfl | rfl
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
      · rw [mul_self_eq_one_iff] at hr
        rw [mul_self_eq_zero] at hi
        subst hi
        rcases hr with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · exfalso; omega
  · rintro (rfl | rfl | rfl | rfl) <;> decide

/-- **Gaussian integers of prime norm are prime.** Let $\pi = a + bi \in \mathbb{Z}[i]$ and
let $N(\pi) = a^2 + b^2$ be its norm. If the absolute value of $N(\pi)$ is a prime number,
then $\pi$ is a prime element of $\mathbb{Z}[i]$. -/
public theorem gaussianInt_prime_of_natAbs_norm_prime {π : ℤ[i]}
    (h : (Zsqrtd.norm π).natAbs.Prime) : Prime π :=
  Zsqrtd.prime_of_natAbs_norm_prime h

/-- **1 + i is a Gaussian prime.** The Gaussian integer $1 + i$ is a prime element of
$\mathbb{Z}[i]$; its norm is $2$. -/
public theorem gaussianInt_prime_one_add_I : Prime (⟨1, 1⟩ : ℤ[i]) :=
  gaussianInt_prime_of_natAbs_norm_prime (by decide)

/-- **Factorization of 2 in the Gaussian integers.** In $\mathbb{Z}[i]$ we have
$2 = -i \cdot (1 + i)^2$, where $-i$ is a unit with inverse $i$. -/
public theorem gaussianInt_two_eq : (2 : ℤ[i])
    = (⟨⟨0, -1⟩, ⟨0, 1⟩, by decide, by decide⟩ : ℤ[i]ˣ) * ⟨1, 1⟩ ^ 2 := by
  decide

/-- **Enumeration of the Gaussian units.** The map $u$ on $\{0, 1, 2, 3\}$ with $u_0 = 1$,
$u_1 = -1$, $u_2 = i$ and $u_3 = -i$ in $\mathbb{Z}[i]$, listing the four units of
$\mathbb{Z}[i]$. -/
public def unitVal : Fin 4 → ℤ[i] := fun i =>
  if i = 0 then 1 else if i = 1 then -1 else if i = 2 then ⟨0, 1⟩
    else ⟨0, -1⟩

/-- **The four Gaussian units are distinct.** Let $u_0 = 1$, $u_1 = -1$, $u_2 = i$ and
$u_3 = -i$ in $\mathbb{Z}[i]$. For $j, k \in \{0, 1, 2, 3\}$, if $u_j = u_k$ then $j = k$. -/
public theorem unitVal_inj : Function.Injective unitVal := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

/-- **The enumeration of the Gaussian units is complete.** Let $u_0 = 1$, $u_1 = -1$, $u_2 = i$
and $u_3 = -i$. Every unit $u$ of $\mathbb{Z}[i]$ equals $u_j$ for some $j \in \{0, 1, 2, 3\}$. -/
public theorem unitVal_complete (u : ℤ[i]) (hu : IsUnit u) :
    ∃ i, unitVal i = u := by
  rcases (gaussianInt_isUnit_iff u).mp hu with rfl | rfl | rfl | rfl
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨2, by decide⟩
  · exact ⟨3, by decide⟩

/-- **Inverses of the Gaussian units.** The map $v$ on $\{0, 1, 2, 3\}$ with $v_0 = 1$,
$v_1 = -1$, $v_2 = -i$ and $v_3 = i$ in $\mathbb{Z}[i]$, listing the inverses of the units
$1$, $-1$, $i$ and $-i$ in that order. -/
public def unitValInv : Fin 4 → ℤ[i] := fun i =>
  if i = 0 then 1 else if i = 1 then -1 else if i = 2 then ⟨0, -1⟩
    else ⟨0, 1⟩

/-- **Each Gaussian unit times its listed inverse is one.** Let $u_0 = 1$, $u_1 = -1$,
$u_2 = i$, $u_3 = -i$ and $v_0 = 1$, $v_1 = -1$, $v_2 = -i$, $v_3 = i$ in $\mathbb{Z}[i]$.
Then $u_j v_j = 1$ for every $j \in \{0, 1, 2, 3\}$. -/
public theorem unitVal_mul_unitValInv (i : Fin 4) :
    unitVal i * unitValInv i = 1 := by
  fin_cases i <;> decide

end

end GaussianInt
