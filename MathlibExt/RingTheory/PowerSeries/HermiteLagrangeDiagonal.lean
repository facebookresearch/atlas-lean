/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

open PowerSeries

/- Chain of helper lemmas proving the Lagrange–Bürmann diagonal identity from scratch
(no such lemma exists in Mathlib as of Lean 4.34.0 / this Mathlib snapshot). -/
namespace MetaMathlibExt.LagrangeInversionAux

/-- The formal derivative commutes with coefficient-wise ring homomorphisms. -/
private theorem map_derivative {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (g : R⟦X⟧) :
    map f (derivative g) = derivative (map f g) := by
  ext n
  simp only [coeff_map, coeff_derivative, map_mul, map_add, map_natCast, map_one]

/-- Fundamental Lagrange relation, multiplied through by `N`: this holds in every
commutative ring since it only uses `derivative_pow` and the coefficient formulas. -/
private theorem base_mul (R : Type*) [CommRing R] (φ : PowerSeries R) (M : ℕ) :
    ((M + 1 : ℕ) : R) * coeff (M + 1) (φ ^ M * (φ - X * derivative φ)) = 0 := by
  have key : ((M + 1 : ℕ) : PowerSeries R) * (φ ^ M * (φ - X * derivative φ))
      = ((M + 1 : ℕ) : PowerSeries R) * φ ^ (M + 1) - X * derivative (φ ^ (M + 1)) := by
    rw [derivative_pow, Nat.add_sub_cancel]
    ring
  have hc : ((M + 1 : ℕ) : R) * coeff (M + 1) (φ ^ M * (φ - X * derivative φ))
      = coeff (M + 1) (((M + 1 : ℕ) : PowerSeries R) * (φ ^ M * (φ - X * derivative φ))) := by
    rw [show ((M + 1 : ℕ) : PowerSeries R) = C ((M + 1 : ℕ) : R) from
      (map_natCast (C : R →+* PowerSeries R) (M + 1)).symm, coeff_C_mul]
  rw [hc, key, map_sub,
    show ((M + 1 : ℕ) : PowerSeries R) = C ((M + 1 : ℕ) : R) from
      (map_natCast (C : R →+* PowerSeries R) (M + 1)).symm, coeff_C_mul,
    coeff_succ_X_mul, coeff_derivative]
  push_cast
  ring

/-- Fundamental Lagrange relation over an arbitrary commutative ring, obtained from
`base_mul` by transporting the identity through the torsion-free universal ring
`MvPolynomial ℕ ℤ`, where the nonzero factor `N` can be cancelled. -/
private theorem base (R : Type*) [CommRing R] (φ : PowerSeries R) (M : ℕ) :
    coeff (M + 1) (φ ^ M * (φ - X * derivative φ)) = 0 := by
  set 𝕌 := MvPolynomial ℕ ℤ with h𝕌
  set Φ : 𝕌⟦X⟧ := mk fun i => MvPolynomial.X i with hΦdef
  set ev : 𝕌 →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) (fun i => coeff i φ) with hev
  have hΦ : map ev Φ = φ := by
    ext n
    rw [coeff_map, hΦdef, coeff_mk, hev, MvPolynomial.eval₂Hom_X']
  have hbase𝕌 : coeff (M + 1) (Φ ^ M * (Φ - X * derivative Φ)) = 0 := by
    have h := base_mul 𝕌 Φ M
    have hne : ((M + 1 : ℕ) : 𝕌) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero M
    exact (mul_eq_zero.mp h).resolve_left hne
  have hexpr : φ ^ M * (φ - X * derivative φ) = map ev (Φ ^ M * (Φ - X * derivative Φ)) := by
    simp only [map_mul, map_pow, map_sub, map_derivative, hΦ, PowerSeries.map_X]
  rw [hexpr, coeff_map, hbase𝕌, map_zero]

/-- The `0`-th coefficient of a substitution `F.subst w` (with `w` having zero constant
term) is the `0`-th coefficient of `F`. -/
private theorem need0 {R : Type*} [CommRing R] (w : PowerSeries R)
    (hw0 : PowerSeries.constantCoeff w = 0) (F : PowerSeries R) :
    coeff 0 (F.subst w) = coeff 0 F := by
  have hs : HasSubst w := HasSubst.of_constantCoeff_zero' hw0
  rw [coeff_subst' hs F 0]
  rw [finsum_eq_single _ 0 (fun d hd => by
    rw [coeff_zero_eq_constantCoeff, map_pow, hw0, zero_pow hd, smul_zero])]
  simp [coeff_zero_eq_constantCoeff]

/-- Splitting a substitution using the reversion equation `w = X * φ(w)`:
`F(w) = F(0) + X · (φ · F₁)(w)`, where `F₁` is the shift of `F`. -/
private theorem hFsub {R : Type*} [CommRing R] (φ w : PowerSeries R)
    (hw0 : PowerSeries.constantCoeff w = 0) (hw : w = X * φ.subst w) (F : PowerSeries R) :
    F.subst w = C (coeff 0 F) + X * ((φ * (mk fun i => coeff (i + 1) F)).subst w) := by
  have hs : HasSubst w := HasSubst.of_constantCoeff_zero' hw0
  set F₁ : PowerSeries R := mk fun i => coeff (i + 1) F with hF₁
  have hsplit : F = C (coeff 0 F) + X * F₁ := by
    ext n
    cases n with
    | zero => simp [hF₁]
    | succ m => simp [hF₁, coeff_succ_C, coeff_succ_X_mul, coeff_mk]
  have hww : w * (F₁.subst w) = X * ((φ * F₁).subst w) := by
    rw [subst_mul hs, ← mul_assoc, ← hw]
  conv_lhs => rw [hsplit]
  rw [subst_add hs, subst_mul hs, subst_X hs, subst_C, hww, ← C_apply]

/-- One reversion step: `coeff (N+1) (F(w)) = coeff N ((φ · F₁)(w))`. -/
private theorem hrec {R : Type*} [CommRing R] (φ w : PowerSeries R)
    (hw0 : PowerSeries.constantCoeff w = 0) (hw : w = X * φ.subst w) (N : ℕ) (F : PowerSeries R) :
    coeff (N + 1) (F.subst w)
      = coeff N ((φ * (mk fun i => coeff (i + 1) F)).subst w) := by
  rw [hFsub φ w hw0 hw F, map_add, coeff_succ_C, coeff_succ_X_mul, zero_add]

/-- Core coefficient identity relating a substitution `F(w)` to coefficients of `F · φ^·`. -/
private theorem needS {R : Type*} [CommRing R] (φ w : PowerSeries R)
    (hw0 : PowerSeries.constantCoeff w = 0) (hw : w = X * φ.subst w) :
    ∀ (N : ℕ) (F : PowerSeries R),
      coeff (N + 1) (F.subst w) + coeff N (F * derivative φ * φ ^ N)
        = coeff (N + 1) (F * φ ^ (N + 1)) := by
  intro N
  induction N with
  | zero =>
    intro F
    set c₀ := coeff 0 F with hc₀
    set F₁ : PowerSeries R := mk fun i => coeff (i + 1) F with hF₁
    have hsplit : F = C c₀ + X * F₁ := by
      ext n; cases n with
      | zero => simp [hc₀]
      | succ m => simp [hF₁, coeff_succ_C, coeff_succ_X_mul, coeff_mk]
    rw [hrec φ w hw0 hw 0 F, ← hF₁, need0 w hw0 (φ * F₁)]
    have hmul0 :
        X * (φ * F₁) + X * (F * derivative φ * φ ^ 0)
          + C c₀ * (φ ^ 0 * (φ - X * derivative φ))
        = F * φ ^ (0 + 1) + X * (X * (F₁ * derivative φ)) := by
      conv_lhs => rw [hsplit]
      conv_rhs => rw [hsplit]
      ring
    have h2 := congrArg (coeff (0 + 1)) hmul0
    simp only [map_add, coeff_succ_X_mul, coeff_zero_X_mul, coeff_C_mul,
      base R φ 0, mul_zero, add_zero] at h2
    linear_combination h2
  | succ k ih =>
    intro F
    set c₀ := coeff 0 F with hc₀
    set F₁ : PowerSeries R := mk fun i => coeff (i + 1) F with hF₁
    have hsplit : F = C c₀ + X * F₁ := by
      ext n; cases n with
      | zero => simp [hc₀]
      | succ m => simp [hF₁, coeff_succ_C, coeff_succ_X_mul, coeff_mk]
    have hih := ih (φ * F₁)
    rw [hrec φ w hw0 hw (k + 1) F, ← hF₁]
    have hmul :
        X * (φ * F₁ * φ ^ (k + 1)) + X * (F * derivative φ * φ ^ (k + 1))
          + C c₀ * (φ ^ (k + 1) * (φ - X * derivative φ))
        = F * φ ^ (k + 1 + 1)
          + X * (X * (φ * F₁ * derivative φ * φ ^ k)) := by
      conv_lhs => rw [hsplit]
      conv_rhs => rw [hsplit]
      ring
    have h2 := congrArg (coeff (k + 1 + 1)) hmul
    simp only [map_add, coeff_succ_X_mul, coeff_C_mul, base R φ (k + 1),
      mul_zero, add_zero] at h2
    linear_combination h2 + hih

/-- The diagonal Lagrange–Bürmann identity, proved by induction on the coefficient index:
any `H` solving `(1 - X·φ'(w))·H = F(w)` has `coeff N H = coeff N (F · φ^N)`. -/
private theorem main {R : Type*} [CommRing R] (φ w : PowerSeries R)
    (hw0 : PowerSeries.constantCoeff w = 0) (hw : w = X * φ.subst w) :
    ∀ (N : ℕ) (F H : PowerSeries R),
      (1 - X * ((derivative φ).subst w)) * H = F.subst w →
      coeff N H = coeff N (F * φ ^ N) := by
  intro N
  induction N with
  | zero =>
    intro F H heq
    rw [pow_zero, mul_one]
    have h0 := congrArg (coeff 0) heq
    rw [need0 w hw0 F] at h0
    rwa [coeff_zero_eq_constantCoeff, map_mul, map_sub, map_one, map_mul,
      constantCoeff_X, zero_mul, sub_zero, one_mul, ← coeff_zero_eq_constantCoeff] at h0
  | succ N ih =>
    intro F H heq
    have hs : HasSubst w := HasSubst.of_constantCoeff_zero' hw0
    have key : coeff (N + 1) H
        = coeff (N + 1) (F.subst w) + coeff N (((derivative φ).subst w) * H) := by
      have h := congrArg (coeff (N + 1)) heq
      have hexp : (1 - X * ((derivative φ).subst w)) * H
          = H - X * (((derivative φ).subst w) * H) := by ring
      rw [hexp, map_sub, coeff_succ_X_mul] at h
      linear_combination h
    have heq' : (1 - X * ((derivative φ).subst w)) * (((derivative φ).subst w) * H)
        = (F * derivative φ).subst w := by
      calc (1 - X * ((derivative φ).subst w)) * (((derivative φ).subst w) * H)
          = ((derivative φ).subst w) * ((1 - X * ((derivative φ).subst w)) * H) := by ring
        _ = ((derivative φ).subst w) * (F.subst w) := by rw [heq]
        _ = (F * derivative φ).subst w := by rw [subst_mul hs]; ring
    have hih := ih (F * derivative φ) (((derivative φ).subst w) * H) heq'
    rw [key, hih]
    have hneed := needS φ w hw0 hw N F
    linear_combination hneed

end MetaMathlibExt.LagrangeInversionAux

section
namespace MetaMathlibExt.LagrangeInversion

/-- **Hermite's diagonal form of Lagrange inversion without side conditions.** Let $R$ be a
commutative ring, let $F$, $\varphi$, $w$ and $G$ be formal power series over $R$, and write
$[X^n]H$ for the coefficient of $X^n$ in a power series $H$. Write $\varphi'$ for the formal
derivative of $\varphi$, and $\varphi(w)$, $\varphi'(w)$, $F(w)$ for the substitution of $w$ into
$\varphi$, $\varphi'$, $F$. If $w = X\,\varphi(w)$ and $(1 - X\,\varphi'(w))\,G = F(w)$, then
$[X^n](F\varphi^n) = [X^n]G$ for every natural number $n$.

The constant term of $w$ vanishes automatically, and $\varphi$ may have zero constant term. -/
theorem coeff_mul_pow_eq_coeff_of_eq_X_mul_subst {R : Type*} [CommRing R] (n : ℕ)
    {F phi w G : PowerSeries R} (hw : w = PowerSeries.X * phi.subst w)
    (hG : (1 - PowerSeries.X * (PowerSeries.derivative phi).subst w) * G = F.subst w) :
    (PowerSeries.coeff n) (F * phi ^ n) = (PowerSeries.coeff n) G := by
  have hw0 : PowerSeries.constantCoeff w = 0 := by
    rw [hw, map_mul, PowerSeries.constantCoeff_X, zero_mul]
  exact (MetaMathlibExt.LagrangeInversionAux.main phi w hw0 hw n F G hG).symm

set_option linter.unusedVariables false in
/-- **Hermite's diagonal form of Lagrange inversion.** Let $R$ be a commutative ring, let $F$,
$\varphi$, $w$ and $G$ be formal power series over $R$, and write $[X^n]H$ for the coefficient
of $X^n$ in a power series $H$. Write $\varphi'$ for the formal derivative of $\varphi$, and
$\varphi(w)$, $\varphi'(w)$, $F(w)$ for the substitution of $w$ into $\varphi$, $\varphi'$, $F$.
Suppose that $w$ has constant term $0$, that $\varphi$ has nonzero constant term, that
$w = X\,\varphi(w)$, and that $(1 - X\,\varphi'(w))\,G = F(w)$. Then
$[X^n](F\varphi^n) = [X^n]G$ for every natural number $n$.

In contrast to the derivative-coefficient form of the Lagrange–Bürmann formula, the derivative
here is absorbed into the defining equation for $G$.

Proves `Wanted` entry `hermite_lagrange_diagonal_formula`. The source's hypotheses `hw0` and
`_hphi` are not needed; see `coeff_mul_pow_eq_coeff_of_eq_X_mul_subst`.

Reference: Bakir Farhi, "Some Applications of the Lagrange Inversion Formula
for the k-Fibonacci Numbers", Journal of Integer Sequences 27 (2024),
Hermite corollary and derivation lines 205-240.
Source: https://cs.uwaterloo.ca/journals/JIS/VOL27/Farhi/farhi35.tex
Complete-source SHA-256:
  ade74bb31bb7d561d2e57515f2125656c2c0a2482237711179e3589bb4b26f27
Normalized statement lines 205-210 SHA-256:
  6e89d7158aae443fa6bf9907f922bc8b116a023093496193a6d016f01de94f7b
Normalized lines 205-240 SHA-256:
  06cba9424deb1a7b852172a86dbc1088947b1225aad87d0577386d59fa3aed58
-/
theorem hermite_lagrange_diagonal_formula
  (n : ℕ) (R : Type*) [CommRing R] (F phi w : PowerSeries R)
  (hw0 : PowerSeries.constantCoeff w = 0)
  (hphi : PowerSeries.coeff 0 phi ≠ 0)
  (hw : w = PowerSeries.X * phi.subst w)
  (G : PowerSeries R)
  (hG : (1 - PowerSeries.X * (PowerSeries.derivative phi).subst w) * G = F.subst w) :
  (PowerSeries.coeff n) (F * phi ^ n) = (PowerSeries.coeff n) G := by
  exact (MetaMathlibExt.LagrangeInversionAux.main phi w hw0 hw n F G hG).symm

end MetaMathlibExt.LagrangeInversion
