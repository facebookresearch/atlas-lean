/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

section
namespace MetaMathlibExt

/-- **Peart–Woodson triple factorization of Riordan arrays.** Let $b$ be an integer, let
$\varepsilon$, $\delta$ and $\lambda$ be real numbers, and let $g$ and $f$ be formal power series
over $\mathbb{R}$ with $g(0) = 1$ and $f(0) = 0$. Write $r_{n,k}$ for the coefficient of $x^n$
in $g f^k$, and suppose that for all natural numbers $n$ and $k$

$$r_{n+1,0} = (b + \varepsilon)\, r_{n,0} + (\lambda + \delta)\, r_{n,1},$$

$$r_{n+1,k+1} = r_{n,k} + b\, r_{n,k+1} + \lambda\, r_{n,k+2},$$

that is, the Riordan array $(g, f)$ has dot diagram
$[b + \varepsilon, \lambda + \delta; 1, b, \lambda]$. With the Riordan product
$(p_1, p_2) \ast (q_1, q_2) = (p_1 \cdot q_1(p_2),\, q_2(p_2))$, let
$P_b = \bigl(1/(1 - bx),\, x/(1 - bx)\bigr)$ and
$C_\lambda = \bigl(c(\lambda x^2),\, x\, c(\lambda x^2)\bigr)$, where
$c(x) = \sum_{m \ge 0} C_m x^m$ is the generating function of the Catalan numbers $C_m$, and let
$F_{\varepsilon,\delta} = \bigl(1/(1 - \varepsilon x - \delta x^2),\, x\bigr)$. Then
$(g, f) = (P_b \ast C_\lambda) \ast F_{\varepsilon,\delta}$.

Source: Cameron and Nkwanta, Riordan multiplication at lines 113–117 and the dot-diagram
recursions at lines 124–138.

Proves `Wanted` entry `triple_factorization_of_dot_diagram`.

Source: Naiomi T. Cameron and Asamoah Nkwanta, *On Some (Pseudo) Involutions
in the Riordan Group*, Journal of Integer Sequences 8 (2005), Article 05.3.7,
Triple Factorization theorem due to Peart and Woodson, line 339, reused in
the proof at line 373,
<https://cs.uwaterloo.ca/journals/JIS/VOL8/Cameron/cameron46.tex>.
-/
theorem triple_factorization_of_dot_diagram
    (b : ℤ) (ε δ lam : ℝ) (g f : PowerSeries ℝ)
    (hg : PowerSeries.constantCoeff g = 1)
    (hf : PowerSeries.constantCoeff f = 0) :
    let coeff := fun (p : PowerSeries ℝ) (n : ℕ) => PowerSeries.coeff n p
    let entry := fun (n k : ℕ) => coeff (g * f ^ k) n
    let hasDot :=
      (∀ n : ℕ, entry (n + 1) 0 = ((b : ℝ) + ε) * entry n 0 + (lam + δ) * entry n 1) ∧
      (∀ n k : ℕ, entry (n + 1) (k + 1) =
        entry n k + (b : ℝ) * entry n (k + 1) + lam * entry n (k + 2))
    let compose := fun (p q : PowerSeries ℝ) => PowerSeries.subst q p
    let mul := fun (p q : PowerSeries ℝ × PowerSeries ℝ) =>
      (p.1 * compose q.1 p.2, compose q.2 p.2)
    let X : PowerSeries ℝ := PowerSeries.X
    let cat : PowerSeries ℝ := PowerSeries.mk fun n => (catalan n : ℝ)
    let catLam := compose cat (PowerSeries.C lam * X ^ 2)
    let Pb : PowerSeries ℝ × PowerSeries ℝ :=
      ((1 - PowerSeries.C (b : ℝ) * X)⁻¹,
       X * (1 - PowerSeries.C (b : ℝ) * X)⁻¹)
    let CLam : PowerSeries ℝ × PowerSeries ℝ := (catLam, X * catLam)
    let Fεδ : PowerSeries ℝ × PowerSeries ℝ :=
      ((1 - PowerSeries.C ε * X - PowerSeries.C δ * X ^ 2)⁻¹, X)
    hasDot → (g, f) = mul (mul Pb CLam) Fεδ := by
  change ((∀ n : ℕ, PowerSeries.coeff (n + 1) (g * f ^ 0)
      = ((b : ℝ) + ε) * PowerSeries.coeff n (g * f ^ 0)
        + (lam + δ) * PowerSeries.coeff n (g * f ^ 1))
    ∧ (∀ n k : ℕ, PowerSeries.coeff (n + 1) (g * f ^ (k + 1))
      = PowerSeries.coeff n (g * f ^ k)
        + (b : ℝ) * PowerSeries.coeff n (g * f ^ (k + 1))
        + lam * PowerSeries.coeff n (g * f ^ (k + 2))))
    → (g, f) = (((1 - PowerSeries.C (b : ℝ) * PowerSeries.X)⁻¹
        * PowerSeries.subst (PowerSeries.X * (1 - PowerSeries.C (b : ℝ) * PowerSeries.X)⁻¹)
          (PowerSeries.subst (PowerSeries.C lam * PowerSeries.X ^ 2)
            (PowerSeries.mk fun n => (catalan n : ℝ))))
        * PowerSeries.subst
          (PowerSeries.subst (PowerSeries.X * (1 - PowerSeries.C (b : ℝ) * PowerSeries.X)⁻¹)
            (PowerSeries.X * PowerSeries.subst (PowerSeries.C lam * PowerSeries.X ^ 2)
              (PowerSeries.mk fun n => (catalan n : ℝ))))
          ((1 - PowerSeries.C ε * PowerSeries.X - PowerSeries.C δ * PowerSeries.X ^ 2)⁻¹),
      PowerSeries.subst
        (PowerSeries.subst (PowerSeries.X * (1 - PowerSeries.C (b : ℝ) * PowerSeries.X)⁻¹)
          (PowerSeries.X * PowerSeries.subst (PowerSeries.C lam * PowerSeries.X ^ 2)
            (PowerSeries.mk fun n => (catalan n : ℝ))))
        PowerSeries.X)
  intro h
  obtain ⟨hcol0, hcol⟩ := h
  -- Clean versions of the column recursions.
  have hcol0' : ∀ n : ℕ, PowerSeries.coeff (n + 1) g
      = ((b : ℝ) + ε) * PowerSeries.coeff n g
        + (lam + δ) * PowerSeries.coeff n (g * f) := by
    intro n
    have e := hcol0 n
    rwa [pow_zero, mul_one, pow_one] at e
  have hcol1 : ∀ n : ℕ, PowerSeries.coeff (n + 1) (g * f)
      = PowerSeries.coeff n g + (b : ℝ) * PowerSeries.coeff n (g * f)
        + lam * PowerSeries.coeff n (g * f ^ 2) := by
    intro n
    have e := hcol n 0
    rw [show (0 : ℕ) + 1 = 1 from rfl, show (0 : ℕ) + 2 = 2 from rfl,
      pow_zero, mul_one, pow_one] at e
    exact e
  -- Auxiliary coefficient facts.
  have hX0 : ∀ p : PowerSeries ℝ,
      PowerSeries.coeff 0 (PowerSeries.X * p) = 0 := by
    intro p
    rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
    simp [PowerSeries.coeff_X]
  have hcf0 : PowerSeries.coeff 0 (g * f) = 0 := by
    rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton,
      PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hg, hf, mul_zero]
  have hg0 : PowerSeries.coeff 0 g = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hg]
  have h10 : PowerSeries.coeff 0 (1 : PowerSeries ℝ) = 1 := by simp
  have h1s : ∀ n : ℕ, PowerSeries.coeff (n + 1) (1 : PowerSeries ℝ) = 0 := by
    intro n; simp
  -- Column generating-function equations.
  have hG1 : g * f = PowerSeries.X * g
      + PowerSeries.X * (PowerSeries.C (b : ℝ) * (g * f))
      + PowerSeries.X * (PowerSeries.C lam * (g * f ^ 2)) := by
    apply PowerSeries.ext
    intro n
    cases n with
    | zero =>
      simp only [map_add, hX0, hcf0, add_zero]
    | succ n =>
      rw [map_add, map_add,
        PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
      exact hcol1 n
  have hG0 : g = 1 + PowerSeries.X * (PowerSeries.C ((b : ℝ) + ε) * g)
      + PowerSeries.X * (PowerSeries.C (lam + δ) * (g * f)) := by
    apply PowerSeries.ext
    intro n
    cases n with
    | zero =>
      rw [map_add, map_add, hX0, hX0, hg0, h10,
        add_zero, add_zero]
    | succ n =>
      rw [map_add, map_add,
        PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
        h1s, zero_add]
      exact hcol0' n
  -- Functional equations for f and g.
  have hgU : IsUnit g := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hg]
    exact isUnit_one
  have hE2 : f = PowerSeries.X + PowerSeries.C (b : ℝ) * PowerSeries.X * f
      + PowerSeries.C lam * PowerSeries.X * f ^ 2 := by
    have h0 : g * (f - PowerSeries.X - PowerSeries.C (b : ℝ) * PowerSeries.X * f
        - PowerSeries.C lam * PowerSeries.X * f ^ 2) = 0 := by
      linear_combination hG1
    have h1 := (hgU.mul_right_eq_zero).mp h0
    linear_combination h1
  have hE1 : g * (1 - PowerSeries.C ((b : ℝ) + ε) * PowerSeries.X
      - PowerSeries.C (lam + δ) * PowerSeries.X * f) = 1 := by
    linear_combination hG0
  -- Catalan generating-function identity over ℝ.
  set catR : PowerSeries ℝ := PowerSeries.mk fun n => (catalan n : ℝ) with hcatRdef
  have hmap : PowerSeries.map (Nat.castRingHom ℝ) PowerSeries.catalanSeries = catR := by
    rw [hcatRdef]
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.catalanSeries_coeff, PowerSeries.coeff_mk]
    simp
  have hcat : catR = catR ^ 2 * PowerSeries.X + 1 := by
    have h2 := congrArg (PowerSeries.map (Nat.castRingHom ℝ))
      PowerSeries.catalanSeries_sq_mul_X_add_one
    rw [map_add, map_mul, map_pow, map_one, PowerSeries.map_X] at h2
    rw [← hmap]
    exact h2.symm
  -- Abbreviations for the pieces of the three factors.
  set U : PowerSeries ℝ := (1 - PowerSeries.C (b : ℝ) * PowerSeries.X)⁻¹ with hUdef
  set V : PowerSeries ℝ
      := (1 - PowerSeries.C ε * PowerSeries.X - PowerSeries.C δ * PowerSeries.X ^ 2)⁻¹ with hVdef
  set Q : PowerSeries ℝ := PowerSeries.C lam * PowerSeries.X ^ 2 with hQdef
  set catLam : PowerSeries ℝ := PowerSeries.subst Q catR with hcatLamdef
  set P2 : PowerSeries ℝ := PowerSeries.X * U with hP2def
  set S : PowerSeries ℝ := PowerSeries.subst P2 catLam with hSdef
  set F : PowerSeries ℝ := PowerSeries.subst P2 (PowerSeries.X * catLam) with hFdef
  set W : PowerSeries ℝ := PowerSeries.subst F V with hWdef
  -- The two geometric-series inverses.
  have hcU : PowerSeries.constantCoeff (1 - PowerSeries.C (b : ℝ) * PowerSeries.X) = 1 := by
    simp
  have hU : U * (1 - PowerSeries.C (b : ℝ) * PowerSeries.X) = 1 := by
    rw [hUdef]
    exact PowerSeries.inv_mul_cancel _ (by rw [hcU]; exact one_ne_zero)
  have hcV : PowerSeries.constantCoeff
      (1 - PowerSeries.C ε * PowerSeries.X - PowerSeries.C δ * PowerSeries.X ^ 2) = 1 := by
    simp
  have hV : V * (1 - PowerSeries.C ε * PowerSeries.X
      - PowerSeries.C δ * PowerSeries.X ^ 2) = 1 := by
    rw [hVdef]
    exact PowerSeries.inv_mul_cancel _ (by rw [hcV]; exact one_ne_zero)
  -- Substitution side conditions.
  have hXsub : PowerSeries.HasSubst (PowerSeries.X : PowerSeries ℝ) :=
    PowerSeries.HasSubst.of_constantCoeff_zero PowerSeries.constantCoeff_X
  have hX2sub : PowerSeries.HasSubst (PowerSeries.X ^ 2 : PowerSeries ℝ) := by
    rw [pow_two]
    exact PowerSeries.HasSubst.mul_left hXsub
  have hQsub : PowerSeries.HasSubst Q := hX2sub.mul_right
  have hP2sub : PowerSeries.HasSubst P2 := PowerSeries.HasSubst.mul_left hXsub
  -- Catalan equation pushed through the substitutions.
  have hcatLam : catLam = catLam ^ 2 * Q + 1 := by
    have h := congrArg (⇑(PowerSeries.substAlgHom hQsub)) hcat
    simp only [map_add, map_mul, map_pow, map_one, PowerSeries.substAlgHom_X] at h
    simp only [PowerSeries.coe_substAlgHom] at h
    exact h
  have hClam : (⇑(PowerSeries.substAlgHom hP2sub)) (PowerSeries.C lam)
      = PowerSeries.C lam := by
    rw [PowerSeries.C_eq_algebraMap, AlgHom.commutes, ← PowerSeries.C_eq_algebraMap]
  have hS : S = S ^ 2 * (PowerSeries.C lam * (PowerSeries.X * U) ^ 2) + 1 := by
    have h := congrArg (⇑(PowerSeries.substAlgHom hP2sub)) hcatLam
    rw [hQdef] at h
    simp only [map_add, map_mul, map_pow, map_one, PowerSeries.substAlgHom_X, hClam] at h
    simp only [PowerSeries.coe_substAlgHom, hP2def] at h
    exact h
  have hFPS : F = P2 * S := by
    rw [hFdef, hSdef, PowerSeries.subst_mul hP2sub, PowerSeries.subst_X hP2sub]
  have hFX : F = PowerSeries.X * (U * S) := by
    rw [hFPS, hP2def, mul_assoc]
  -- The middle factor's second component satisfies the same equation as f.
  have hUS : U * S = 1 + PowerSeries.C (b : ℝ) * PowerSeries.X * (U * S)
      + PowerSeries.C lam * PowerSeries.X ^ 2 * U ^ 2 * S ^ 2 := by
    linear_combination S * hU + hS
  have hF : F = PowerSeries.X + PowerSeries.C (b : ℝ) * PowerSeries.X * F
      + PowerSeries.C lam * PowerSeries.X * F ^ 2 := by
    rw [hFX]
    linear_combination PowerSeries.X * hUS
  have hFc : PowerSeries.constantCoeff F = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hFX]
    exact hX0 _
  have hFsub : PowerSeries.HasSubst F :=
    PowerSeries.HasSubst.of_constantCoeff_zero hFc
  -- The last factor's first component, substituted at F, is the expected inverse.
  have hCeps : (⇑(PowerSeries.substAlgHom hFsub)) (PowerSeries.C ε)
      = PowerSeries.C ε := by
    rw [PowerSeries.C_eq_algebraMap, AlgHom.commutes, ← PowerSeries.C_eq_algebraMap]
  have hCdel : (⇑(PowerSeries.substAlgHom hFsub)) (PowerSeries.C δ)
      = PowerSeries.C δ := by
    rw [PowerSeries.C_eq_algebraMap, AlgHom.commutes, ← PowerSeries.C_eq_algebraMap]
  have hW : W * (1 - PowerSeries.C ε * F - PowerSeries.C δ * F ^ 2) = 1 := by
    have h := congrArg (⇑(PowerSeries.substAlgHom hFsub)) hV
    simp only [map_mul, map_pow, map_sub, map_one, PowerSeries.substAlgHom_X,
      hCeps, hCdel] at h
    simp only [PowerSeries.coe_substAlgHom] at h
    exact h
  -- The full first component satisfies the same equation as g.
  have hCadd2 : PowerSeries.C (lam + δ)
      = PowerSeries.C lam + PowerSeries.C δ := by
    rw [map_add]
  have stepA : U * S * (1 - PowerSeries.C ((b : ℝ) + ε) * PowerSeries.X
      - PowerSeries.C (lam + δ) * PowerSeries.X ^ 2 * U * S)
      = S * (U * (1 - PowerSeries.C (b : ℝ) * PowerSeries.X))
        - PowerSeries.C ε * PowerSeries.X * U * S
        - PowerSeries.C (lam + δ) * PowerSeries.X ^ 2 * U ^ 2 * S ^ 2 := by
    rw [map_add, map_add]
    ring
  rw [hU, mul_one] at stepA
  have stepB : U * S * (1 - PowerSeries.C ((b : ℝ) + ε) * PowerSeries.X
      - PowerSeries.C (lam + δ) * PowerSeries.X ^ 2 * U * S)
      = 1 - PowerSeries.C ε * PowerSeries.X * U * S
        - PowerSeries.C δ * PowerSeries.X ^ 2 * U ^ 2 * S ^ 2 := by
    linear_combination stepA + hS
      - (PowerSeries.X ^ 2 * U ^ 2 * S ^ 2) * hCadd2
  have hG : U * S * W * (1 - PowerSeries.C ((b : ℝ) + ε) * PowerSeries.X
      - PowerSeries.C (lam + δ) * PowerSeries.X * F) = 1 := by
    have e1 : U * S * W * (1 - PowerSeries.C ((b : ℝ) + ε) * PowerSeries.X
        - PowerSeries.C (lam + δ) * PowerSeries.X * F)
        = W * (U * S * (1 - PowerSeries.C ((b : ℝ) + ε) * PowerSeries.X
          - PowerSeries.C (lam + δ) * PowerSeries.X ^ 2 * U * S)) := by
      rw [hFX]; ring
    rw [e1, stepB]
    rw [hFX] at hW
    linear_combination hW
  -- Uniqueness: f then g coincide with the two components.
  have hU2 : IsUnit (1 - PowerSeries.X * (PowerSeries.C (b : ℝ)
      + PowerSeries.C lam * (f + F))) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have hc : PowerSeries.constantCoeff (1 - PowerSeries.X * (PowerSeries.C (b : ℝ)
        + PowerSeries.C lam * (f + F))) = 1 := by
      simp
    rw [hc]
    exact isUnit_one
  have key : (f - F) * (1 - PowerSeries.X * (PowerSeries.C (b : ℝ)
      + PowerSeries.C lam * (f + F))) = 0 := by
    linear_combination hE2 - hF
  have hfeq : f = F := by
    rw [mul_comm] at key
    have hsub := (hU2.mul_right_eq_zero).mp key
    exact sub_eq_zero.mp hsub
  have hgeq : g = U * S * W := by
    have hW1 : (1 - PowerSeries.C ((b : ℝ) + ε) * PowerSeries.X
        - PowerSeries.C (lam + δ) * PowerSeries.X * f)
        = (1 - PowerSeries.C ((b : ℝ) + ε) * PowerSeries.X
          - PowerSeries.C (lam + δ) * PowerSeries.X * F) := by
      rw [hfeq]
    rw [hW1] at hE1
    have hU1 : IsUnit (1 - PowerSeries.C ((b : ℝ) + ε) * PowerSeries.X
        - PowerSeries.C (lam + δ) * PowerSeries.X * F) :=
      ⟨⟨_, _, by rw [mul_comm _ (U * S * W)]; exact hG, hG⟩, rfl⟩
    exact hU1.mul_right_cancel (by rw [hE1, hG])
  have hFX2 : PowerSeries.subst F PowerSeries.X = F :=
    PowerSeries.subst_X (R := ℝ) (τ := Unit) (S := ℝ) (a := F) hFsub
  rw [hgeq, hfeq, hFX2]

end MetaMathlibExt

end
