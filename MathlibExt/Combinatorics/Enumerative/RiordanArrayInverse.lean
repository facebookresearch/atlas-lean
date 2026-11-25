/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-! # Riordan array inverse -/

/-- **Inverse of a Riordan array from its A- and Z-sequences (one-sided form).** Let $K$ be a
field, let $g, f, A, Z, \bar f$ be formal power series over $K$, and let $d_{00} \in K$ with
$d_{00} \ne 0$. Suppose that $g(0) = d_{00}$, $f(0) = 0$, $A(0) \ne 0$, $\bar f(0) = 0$,
$f(\bar f(x)) = x$, $f(x) = x\, A(f(x))$ and $g(x) = d_{00} \bigl(1 - x\, Z(f(x))\bigr)^{-1}$.
Then
$$\left(\frac{1}{g(\bar f(x))},\ \bar f(x)\right) =
\left(\frac{A(x) - x\, Z(x)}{d_{00}\, A(x)},\ \frac{x}{A(x)}\right).$$

Here $A$ and $Z$ are the generating functions of the A- and Z-sequences of the Riordan array
$(g, f)$, and the pair on the left is its inverse. Only $f(\bar f(x)) = x$ is assumed, not also
$\bar f(f(x)) = x$. -/
theorem riordan_array_inverse_via_a_and_z_sequences_general
    {K : Type*} [Field K]
    (g f A Z fInv : PowerSeries K)
    (d₀₀ : K)
    (hd₀₀ : PowerSeries.constantCoeff g = d₀₀)
    (hd₀₀_ne : d₀₀ ≠ 0)
    (hf₀ : PowerSeries.constantCoeff f = 0)
    (hA₀ : PowerSeries.constantCoeff A ≠ 0)
    (hfInv₀ : PowerSeries.constantCoeff fInv = 0)
    (hA : f = (PowerSeries.X : PowerSeries K) * PowerSeries.subst f A)
    (hcomp_left : PowerSeries.subst fInv f = (PowerSeries.X : PowerSeries K))
    (hZ : g = PowerSeries.C (R := K) d₀₀ *
      ((1 - PowerSeries.X * PowerSeries.subst f Z : PowerSeries K)⁻¹)) :
    (((PowerSeries.subst fInv g)⁻¹, fInv) : PowerSeries K × PowerSeries K) =
      ((A - PowerSeries.X * Z) *
        ((PowerSeries.C (R := K) d₀₀ * A : PowerSeries K)⁻¹),
        (PowerSeries.X : PowerSeries K) * A⁻¹) := by
  have hfSubst : PowerSeries.HasSubst f :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hf₀
  have hfInvSubst : PowerSeries.HasSubst fInv :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hfInv₀
  have hX_eq : (PowerSeries.X : PowerSeries K) = fInv * A := by
    have e1 : PowerSeries.subst fInv f = PowerSeries.X := hcomp_left
    rw [hA, PowerSeries.subst_mul hfInvSubst, PowerSeries.subst_X hfInvSubst,
      PowerSeries.subst_comp_subst_apply hfSubst hfInvSubst, hcomp_left,
      PowerSeries.X_subst] at e1
    exact e1.symm
  have hfInv_eq : fInv = PowerSeries.X * A⁻¹ := by
    have hAinv : A * A⁻¹ = 1 := PowerSeries.mul_inv_cancel _ hA₀
    calc fInv = fInv * 1 := (mul_one _).symm
      _ = fInv * (A * A⁻¹) := by rw [hAinv]
      _ = (fInv * A) * A⁻¹ := by ring
      _ = PowerSeries.X * A⁻¹ := by rw [← hX_eq]
  have hW_ne : PowerSeries.constantCoeff
      (1 - PowerSeries.X * PowerSeries.subst f Z : PowerSeries K) ≠ 0 := by
    have hX0 : PowerSeries.constantCoeff (PowerSeries.X : PowerSeries K) = 0 :=
      PowerSeries.constantCoeff_X
    simp [hX0]
  have hCdA_ne : PowerSeries.constantCoeff
      (PowerSeries.C (R := K) d₀₀ * A : PowerSeries K) ≠ 0 := by
    have h1 : PowerSeries.constantCoeff
        (PowerSeries.C (R := K) d₀₀ * A : PowerSeries K)
        = d₀₀ * PowerSeries.constantCoeff A := by
      simp [PowerSeries.constantCoeff_C]
    rw [h1]
    exact mul_ne_zero hd₀₀_ne hA₀
  have hS_ne : PowerSeries.constantCoeff (PowerSeries.subst fInv g) ≠ 0 := by
    have h : MvPowerSeries.constantCoeff fInv = 0 := hfInv₀
    have hS := PowerSeries.constantCoeff_subst_of_constantCoeff_zero h g
    have hS2 : MvPowerSeries.constantCoeff (PowerSeries.subst fInv g) = d₀₀ := by
      simpa [hd₀₀] using hS
    have hS3 : PowerSeries.constantCoeff (PowerSeries.subst fInv g) = d₀₀ := hS2
    rw [hS3]
    exact hd₀₀_ne
  have hW_inv : (1 - PowerSeries.X * PowerSeries.subst f Z : PowerSeries K)⁻¹
      * (1 - PowerSeries.X * PowerSeries.subst f Z) = 1 :=
    PowerSeries.inv_mul_cancel _ hW_ne
  have hgW : g * (1 - PowerSeries.X * PowerSeries.subst f Z : PowerSeries K)
      = PowerSeries.C (R := K) d₀₀ := by
    rw [hZ, mul_assoc, hW_inv, mul_one]
  have hsubstW : PowerSeries.subst fInv
      (1 - PowerSeries.X * PowerSeries.subst f Z : PowerSeries K)
      = 1 - fInv * Z := by
    have h1 : PowerSeries.subst fInv (1 : PowerSeries K) = 1 := by
      have hC1 : (PowerSeries.C (R := K) 1) = 1 := map_one _
      rw [← hC1, PowerSeries.subst_C]
      exact map_one _
    rw [PowerSeries.subst_sub hfInvSubst, h1, PowerSeries.subst_mul hfInvSubst,
      PowerSeries.subst_X hfInvSubst,
      PowerSeries.subst_comp_subst_apply hfSubst hfInvSubst, hcomp_left,
      PowerSeries.X_subst]
  have hSU0 : PowerSeries.subst fInv g *
      PowerSeries.subst fInv
        (1 - PowerSeries.X * PowerSeries.subst f Z : PowerSeries K)
      = PowerSeries.C (R := K) d₀₀ := by
    have hsubst_gW : PowerSeries.subst fInv
        (g * (1 - PowerSeries.X * PowerSeries.subst f Z : PowerSeries K))
        = PowerSeries.subst fInv (PowerSeries.C (R := K) d₀₀) := by
      rw [hgW]
    rw [PowerSeries.subst_mul hfInvSubst, PowerSeries.subst_C] at hsubst_gW
    exact hsubst_gW
  have hSU : PowerSeries.subst fInv g * (1 - fInv * Z)
      = PowerSeries.C (R := K) d₀₀ := by
    rw [← hsubstW]
    exact hSU0
  have hU_eq : (1 - PowerSeries.X * A⁻¹ * Z : PowerSeries K)
      = (A - PowerSeries.X * Z) * A⁻¹ := by
    rw [sub_mul, PowerSeries.mul_inv_cancel _ hA₀]
    ring
  have hSU2 : PowerSeries.subst fInv g * ((A - PowerSeries.X * Z) * A⁻¹)
      = PowerSeries.C (R := K) d₀₀ := by
    rw [← hU_eq, ← hfInv_eq]
    exact hSU
  have hSA : PowerSeries.subst fInv g * (A - PowerSeries.X * Z)
      = PowerSeries.C (R := K) d₀₀ * A := by
    have h := congrArg (· * A) hSU2
    rwa [mul_assoc (PowerSeries.subst fInv g) ((A - PowerSeries.X * Z) * A⁻¹) A,
      mul_assoc (A - PowerSeries.X * Z) A⁻¹ A,
      PowerSeries.inv_mul_cancel _ hA₀, mul_one] at h
  have hfirst : (PowerSeries.subst fInv g)⁻¹
      = (A - PowerSeries.X * Z) *
        ((PowerSeries.C (R := K) d₀₀ * A : PowerSeries K)⁻¹) := by
    rw [PowerSeries.inv_eq_iff_mul_eq_one hS_ne]
    have hCdA : (PowerSeries.C (R := K) d₀₀ * A)
        * (PowerSeries.C (R := K) d₀₀ * A)⁻¹ = 1 :=
      PowerSeries.mul_inv_cancel _ hCdA_ne
    calc (A - PowerSeries.X * Z) * ((PowerSeries.C (R := K) d₀₀ * A)⁻¹)
          * PowerSeries.subst fInv g
        = ((A - PowerSeries.X * Z) * PowerSeries.subst fInv g)
          * (PowerSeries.C (R := K) d₀₀ * A)⁻¹ := by ring
      _ = (PowerSeries.subst fInv g * (A - PowerSeries.X * Z))
          * (PowerSeries.C (R := K) d₀₀ * A)⁻¹ := by
          rw [mul_comm (A - PowerSeries.X * Z) (PowerSeries.subst fInv g)]
      _ = (PowerSeries.C (R := K) d₀₀ * A)
          * (PowerSeries.C (R := K) d₀₀ * A)⁻¹ := by rw [hSA]
      _ = 1 := hCdA
  exact Prod.ext hfirst hfInv_eq

set_option linter.unusedVariables false in
/-- **Inverse of a Riordan array from its A- and Z-sequences.** Let $K$ be a field, let
$g, f, A, Z, \bar f$ be formal power series over $K$, and let $d_{00} \in K$ with $d_{00} \ne 0$.
Suppose that $g(0) = d_{00}$, $f(0) = 0$, $A(0) \ne 0$ and $\bar f(0) = 0$; that
$f(\bar f(x)) = x$ and $\bar f(f(x)) = x$, so that $\bar f$ is the compositional inverse of $f$;
that $f(x) = x\, A(f(x))$, so that $A$ is the generating function of the A-sequence; and that
$g(x) = d_{00} \bigl(1 - x\, Z(f(x))\bigr)^{-1}$, so that $Z$ is the generating function of the
Z-sequence. Then
$$\left(\frac{1}{g(\bar f(x))},\ \bar f(x)\right) =
\left(\frac{A(x) - x\, Z(x)}{d_{00}\, A(x)},\ \frac{x}{A(x)}\right).$$

The pair on the left is the inverse of the Riordan array $(g, f)$. The hypothesis
$\bar f(f(x)) = x$ is not needed for the conclusion; it is kept to match the source.

Proves `Wanted` entry `riordan_array_inverse_via_a_and_z_sequences`.

Source: Paul Barry and Aoife Hennessy, "Meixner-Type Results for Riordan Arrays and
Associated Integer Sequences," Journal of Integer Sequences 13 (2010), Article 10.9.4,
Lemma (label `Lemma`), lines 280-283,
<https://cs.uwaterloo.ca/journals/JIS/VOL13/Barry5/barry96s.tex>.
The paper attributes this formula to Luzon.
-/
theorem riordan_array_inverse_via_a_and_z_sequences
  {K : Type*} [Field K]
  (g f A Z fInv : PowerSeries K)
  (d₀₀ : K)
  (hd₀₀ : PowerSeries.constantCoeff g = d₀₀)
  (hd₀₀_ne : d₀₀ ≠ 0)
  (hf₀ : PowerSeries.constantCoeff f = 0)
  (hA₀ : PowerSeries.constantCoeff A ≠ 0)
  (hfInv₀ : PowerSeries.constantCoeff fInv = 0)
  (hA : f = (PowerSeries.X : PowerSeries K) * PowerSeries.subst f A)
  (hcomp_left : PowerSeries.subst fInv f = (PowerSeries.X : PowerSeries K))
  (hcomp_right : PowerSeries.subst f fInv = (PowerSeries.X : PowerSeries K))
  (hZ : g = PowerSeries.C (R := K) d₀₀ *
    ((1 - PowerSeries.X * PowerSeries.subst f Z : PowerSeries K)⁻¹)) :
  (((PowerSeries.subst fInv g)⁻¹, fInv) : PowerSeries K × PowerSeries K) =
    ((A - PowerSeries.X * Z) *
      ((PowerSeries.C (R := K) d₀₀ * A : PowerSeries K)⁻¹),
      (PowerSeries.X : PowerSeries K) * A⁻¹) := by
  exact riordan_array_inverse_via_a_and_z_sequences_general g f A Z fInv d₀₀ hd₀₀ hd₀₀_ne hf₀ hA₀
    hfInv₀ hA hcomp_left hZ

end MetaMathlibExt
