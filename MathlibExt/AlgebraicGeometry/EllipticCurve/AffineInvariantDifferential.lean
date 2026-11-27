/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Kaehler.QuotientMvPolynomial
public import MathlibExt.AlgebraicGeometry.EllipticCurve.VariableChangePolynomial
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Tactic.LinearCombination

/-!
# The invariant differential of an affine Weierstrass curve

Let `W` be a Weierstrass curve over a field `F` with `Δ_W ≠ 0`, and let
`A_W = F[x, y] / (f_W)` with `f_W = y² + a₁ x y + a₃ y - x³ - a₂ x² - a₄ x - a₆`, written here
as a quotient of `MvPolynomial (Fin 2) F` with `x = X 0` and `y = X 1`. With
`P_W = 2y + a₁ x + a₃` and `Q_W = 3x² + 2a₂ x + a₄ - a₁ y`, there is a unique `ω_W ∈ Ω¹_{A_W/F}`
with `P_W ω_W = dx` and `Q_W ω_W = dy`, and `Ω¹_{A_W/F}` is free of rank one with basis `ω_W`
(`WeierstrassCurve.invariantDifferential_spec`). Under a variable change `C = (u, r, s, t)`, the
substitution `x = u² x' + r`, `y = u³ y' + u² s x' + t` induces an isomorphism `A_W ≅ A_{C • W}`
that carries `ω_W` to `u⁻¹ ω_{C • W}` (`WeierstrassCurve.invariantDifferential_variableChange`).

The proofs use the presentation of the differentials of a hypersurface
(`MvPolynomial.kaehlerDifferential_planeCurve`) and, transported from Mathlib's coordinate ring
`F[X][Y] / (f_W)`, the identities of
`WeierstrassCurve.Affine.evalEval_polynomial_variableChange`,
`WeierstrassCurve.Affine.evalEval_partials_variableChange` and
`WeierstrassCurve.Affine.CoordinateRing.exists_mul_add_mul_eq_one_of_Δ_ne_zero`.
-/

@[expose] public section

open MvPolynomial KaehlerDifferential
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- The Weierstrass polynomial `f_W = y² + a₁ x y + a₃ y - x³ - a₂ x² - a₄ x - a₆` in
`F[x, y]`, with `x = X 0` and `y = X 1`. -/
noncomputable def mvPolynomial : MvPolynomial (Fin 2) F :=
  X 1 ^ 2 + C W.a₁ * X 0 * X 1 + C W.a₃ * X 1 -
    (X 0 ^ 3 + C W.a₂ * X 0 ^ 2 + C W.a₄ * X 0 + C W.a₆)

/-- `P_W = 2y + a₁ x + a₃ = ∂f_W/∂y` in `F[x, y]`, with `x = X 0` and `y = X 1`. -/
noncomputable def mvPolynomialP : MvPolynomial (Fin 2) F :=
  2 * X 1 + C W.a₁ * X 0 + C W.a₃

/-- `Q_W = 3x² + 2a₂ x + a₄ - a₁ y = -∂f_W/∂x` in `F[x, y]`, with `x = X 0` and `y = X 1`. -/
noncomputable def mvPolynomialQ : MvPolynomial (Fin 2) F :=
  3 * X 0 ^ 2 + 2 * C W.a₂ * X 0 + C W.a₄ - C W.a₁ * X 1

/-- The affine coordinate ring `F[x, y] / (f_W)` of `W`. -/
abbrev MvCoordinateRing : Type _ := MvPolynomial (Fin 2) F ⧸ Ideal.span {W.mvPolynomial}

/-- The class in `F[x, y] / (f_W)` of a polynomial. -/
noncomputable abbrev mvMk : MvPolynomial (Fin 2) F →ₐ[F] W.MvCoordinateRing :=
  Ideal.Quotient.mkₐ F _

theorem pderiv_zero_mvPolynomial : pderiv 0 W.mvPolynomial = -W.mvPolynomialQ := by
  simp [mvPolynomial, mvPolynomialQ, pderiv_X]
  ring

theorem pderiv_one_mvPolynomial : pderiv 1 W.mvPolynomial = W.mvPolynomialP := by
  simp [mvPolynomial, mvPolynomialP, pderiv_X]

/-- The ring homomorphism `F[X][Y] → F[x, y] / (f_W)`, `X ↦ x̄`, `Y ↦ ȳ`. -/
noncomputable def toMvCoordinateRing : F[X][Y] →+* W.MvCoordinateRing :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (W.mvMk.toRingHom.comp C) (W.mvMk (X 0))) (W.mvMk (X 1))

@[simp] theorem toMvCoordinateRing_CC (a : F) :
    W.toMvCoordinateRing (Polynomial.C (Polynomial.C a)) = W.mvMk (C a) := by
  simp [toMvCoordinateRing]
  rfl

@[simp] theorem toMvCoordinateRing_CX :
    W.toMvCoordinateRing (Polynomial.C Polynomial.X) = W.mvMk (X 0) := by
  simp [toMvCoordinateRing]

@[simp] theorem toMvCoordinateRing_Y : W.toMvCoordinateRing Y = W.mvMk (X 1) := by
  simp [toMvCoordinateRing]

theorem toMvCoordinateRing_polynomial :
    W.toMvCoordinateRing W.toAffine.polynomial = 0 := by
  have : W.mvMk W.mvPolynomial = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  rw [← this]
  change _ = W.mvMk (X 1 ^ 2 + C W.a₁ * X 0 * X 1 + C W.a₃ * X 1 -
    (X 0 ^ 3 + C W.a₂ * X 0 ^ 2 + C W.a₄ * X 0 + C W.a₆))
  rw [Affine.polynomial]
  simp only [map_add, map_sub, map_mul, map_pow, toMvCoordinateRing_CC, toMvCoordinateRing_CX,
    toMvCoordinateRing_Y]
  ring

theorem toMvCoordinateRing_polynomialY :
    W.toMvCoordinateRing W.toAffine.polynomialY = W.mvMk W.mvPolynomialP := by
  rw [Affine.polynomialY, mvPolynomialP]
  simp only [map_add, map_mul, map_ofNat, toMvCoordinateRing_CC,
    toMvCoordinateRing_CX, toMvCoordinateRing_Y]
  ring

theorem toMvCoordinateRing_neg_polynomialX :
    W.toMvCoordinateRing (-W.toAffine.polynomialX) = W.mvMk W.mvPolynomialQ := by
  rw [Affine.polynomialX, mvPolynomialQ]
  simp only [map_neg, map_add, map_sub, map_mul, map_pow, map_ofNat, toMvCoordinateRing_CC,
    toMvCoordinateRing_CX, toMvCoordinateRing_Y]
  ring

/-- **$P_W$ and $Q_W$ generate the unit ideal of $F[x, y]/(f_W)$** when $\Delta_W \ne 0$:
there are $p, q$ with $p P_W + q Q_W = 1$. This is
`WeierstrassCurve.Affine.CoordinateRing.exists_mul_add_mul_eq_one_of_Δ_ne_zero`, carried from
Mathlib's coordinate ring `F[X][Y] / (f_W)` along the map `X ↦ x̄`, `Y ↦ ȳ`. -/
theorem exists_mul_add_mul_eq_one_of_Δ_ne_zero (hΔ : W.Δ ≠ 0) :
    ∃ p q : W.MvCoordinateRing, p * W.mvMk W.mvPolynomialP + q * W.mvMk W.mvPolynomialQ = 1 := by
  obtain ⟨p, q, h⟩ := Affine.CoordinateRing.exists_mul_add_mul_eq_one_of_Δ_ne_zero W hΔ
  let ψ : W.toAffine.CoordinateRing →+* W.MvCoordinateRing :=
    AdjoinRoot.lift (Polynomial.eval₂RingHom (W.mvMk.toRingHom.comp C) (W.mvMk (X 0)))
      (W.mvMk (X 1)) (W.toMvCoordinateRing_polynomial)
  refine ⟨ψ p, ψ q, ?_⟩
  have := congrArg ψ h
  rw [map_add, map_mul, map_mul, map_one] at this
  rw [← this]
  congr 2
  · exact ((AdjoinRoot.lift_mk _ _).trans W.toMvCoordinateRing_polynomialY).symm
  · exact ((AdjoinRoot.lift_mk _ _).trans W.toMvCoordinateRing_neg_polynomialX).symm

/-- The `A_W`-linear map `A_W² → A_W`, `(b₁, b₂) ↦ b₁ P_W + b₂ Q_W`. -/
noncomputable def pairingPQ :
    (Fin 2 → W.MvCoordinateRing) →ₗ[W.MvCoordinateRing] W.MvCoordinateRing :=
  Fintype.linearCombination W.MvCoordinateRing ![W.mvMk W.mvPolynomialP, W.mvMk W.mvPolynomialQ]

theorem pairingPQ_apply (b : Fin 2 → W.MvCoordinateRing) :
    W.pairingPQ b = b 0 * W.mvMk W.mvPolynomialP + b 1 * W.mvMk W.mvPolynomialQ := by
  simp [pairingPQ, Fintype.linearCombination_apply, Fin.sum_univ_two]

theorem ker_kaehlerCoordinates_le_ker_pairingPQ :
    LinearMap.ker (kaehlerCoordinates F W.mvPolynomial) ≤ LinearMap.ker W.pairingPQ := by
  rw [(kaehlerDifferential_planeCurve F W.mvPolynomial).2, Submodule.span_le,
    Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker, pairingPQ_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pderiv_zero_mvPolynomial,
    pderiv_one_mvPolynomial, map_neg]
  change -(W.mvMk W.mvPolynomialQ) * W.mvMk W.mvPolynomialP +
    W.mvMk W.mvPolynomialP * W.mvMk W.mvPolynomialQ = 0
  ring

/-- The `A_W`-linear map `Ω¹_{A_W/F} → A_W` with `dx ↦ P_W` and `dy ↦ Q_W`, induced by
`(b₁, b₂) ↦ b₁ P_W + b₂ Q_W` through the presentation of `Ω¹_{A_W/F}`. -/
noncomputable def kaehlerToCoordinateRing :
    KaehlerDifferential F W.MvCoordinateRing →ₗ[W.MvCoordinateRing] W.MvCoordinateRing :=
  ((LinearMap.ker (kaehlerCoordinates F W.mvPolynomial)).liftQ W.pairingPQ
      W.ker_kaehlerCoordinates_le_ker_pairingPQ).comp
    ((kaehlerCoordinates F W.mvPolynomial).quotKerEquivOfSurjective
      (quotientSpanSingleton_kaehler_surjective F W.mvPolynomial)).symm.toLinearMap

theorem kaehlerToCoordinateRing_kaehlerCoordinates (b : Fin 2 → W.MvCoordinateRing) :
    W.kaehlerToCoordinateRing (kaehlerCoordinates F W.mvPolynomial b) = W.pairingPQ b := by
  rw [kaehlerToCoordinateRing, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ← LinearMap.quotKerEquivOfSurjective_apply_mk _
      (quotientSpanSingleton_kaehler_surjective F W.mvPolynomial),
    LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]

theorem kaehlerToCoordinateRing_D_X_zero :
    W.kaehlerToCoordinateRing (D F _ (W.mvMk (X 0))) = W.mvMk W.mvPolynomialP := by
  have : kaehlerCoordinates F W.mvPolynomial (Pi.single 0 1) = D F _ (W.mvMk (X 0)) := by
    rw [kaehlerCoordinates, Fintype.linearCombination_apply_single]
    exact one_smul W.MvCoordinateRing (D F W.MvCoordinateRing (W.mvMk (X 0)))
  rw [← this, kaehlerToCoordinateRing_kaehlerCoordinates, pairingPQ_apply]
  simp

theorem kaehlerToCoordinateRing_D_X_one :
    W.kaehlerToCoordinateRing (D F _ (W.mvMk (X 1))) = W.mvMk W.mvPolynomialQ := by
  have : kaehlerCoordinates F W.mvPolynomial (Pi.single 1 1) = D F _ (W.mvMk (X 1)) := by
    rw [kaehlerCoordinates, Fintype.linearCombination_apply_single]
    exact one_smul W.MvCoordinateRing (D F W.MvCoordinateRing (W.mvMk (X 1)))
  rw [← this, kaehlerToCoordinateRing_kaehlerCoordinates, pairingPQ_apply]
  simp

theorem kaehlerToCoordinateRing_bijective (hΔ : W.Δ ≠ 0) :
    Function.Bijective W.kaehlerToCoordinateRing := by
  obtain ⟨p, q, hpq⟩ := W.exists_mul_add_mul_eq_one_of_Δ_ne_zero hΔ
  have hsurj := quotientSpanSingleton_kaehler_surjective F W.mvPolynomial
  refine ⟨?_, fun b ↦ ⟨kaehlerCoordinates F W.mvPolynomial ![b * p, b * q], ?_⟩⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro w hw
    obtain ⟨v, rfl⟩ := hsurj w
    rw [LinearMap.mem_ker, kaehlerToCoordinateRing_kaehlerCoordinates, pairingPQ_apply] at hw
    -- `v = c (-Q, P)` with `c = v₁ p - v₀ q`, so `v` lies in the kernel of the presentation.
    have hv : v = (v 1 * p - v 0 * q) •
        (fun i ↦ Ideal.Quotient.mk (Ideal.span {W.mvPolynomial}) (pderiv i W.mvPolynomial)) := by
      funext i
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, pderiv_zero_mvPolynomial, map_neg,
          smul_eq_mul]
        change v 0 = (v 1 * p - v 0 * q) * -(W.mvMk W.mvPolynomialQ)
        linear_combination (-v 0) * hpq + p * hw
      · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, pderiv_one_mvPolynomial,
          smul_eq_mul]
        change v 1 = (v 1 * p - v 0 * q) * W.mvMk W.mvPolynomialP
        linear_combination (-v 1) * hpq + q * hw
    have : v ∈ LinearMap.ker (kaehlerCoordinates F W.mvPolynomial) := by
      rw [(kaehlerDifferential_planeCurve F W.mvPolynomial).2, hv]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      funext i
      fin_cases i <;> rfl
    rw [Submodule.mem_bot, ← LinearMap.mem_ker.mp this]
  · rw [kaehlerToCoordinateRing_kaehlerCoordinates, pairingPQ_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination b * hpq

/-- The isomorphism `Ω¹_{A_W/F} ≅ A_W` with `dx ↦ P_W` and `dy ↦ Q_W`, for `Δ_W ≠ 0`. -/
noncomputable def kaehlerEquiv (hΔ : W.Δ ≠ 0) :
    KaehlerDifferential F W.MvCoordinateRing ≃ₗ[W.MvCoordinateRing] W.MvCoordinateRing :=
  LinearEquiv.ofBijective W.kaehlerToCoordinateRing (W.kaehlerToCoordinateRing_bijective hΔ)

/-- **The invariant differential** `ω_W ∈ Ω¹_{A_W/F}` of a Weierstrass curve with `Δ_W ≠ 0`:
the element sent to `1` by the isomorphism `Ω¹_{A_W/F} ≅ A_W` with `dx ↦ P_W`, `dy ↦ Q_W`. -/
noncomputable def invariantDifferential (hΔ : W.Δ ≠ 0) : KaehlerDifferential F W.MvCoordinateRing :=
  (W.kaehlerEquiv hΔ).symm 1

/-- **The invariant differential generates the differentials of the affine Weierstrass curve.**
Let $F$ be a field and $W$ a Weierstrass curve over $F$ with coefficients
$a_1, a_2, a_3, a_4, a_6$ and discriminant $\Delta_W \ne 0$, and let
$A_W = F[x, y] / (y^2 + a_1 x y + a_3 y - x^3 - a_2 x^2 - a_4 x - a_6)$. Then there is a unique
$\omega_W \in \Omega^1_{A_W/F}$ with $(2y + a_1 x + a_3)\,\omega_W = dx$ and
$(3x^2 + 2a_2 x + a_4 - a_1 y)\,\omega_W = dy$, namely `WeierstrassCurve.invariantDifferential`,
and $\Omega^1_{A_W/F}$ is a free $A_W$-module of rank one with basis $\omega_W$.

Here $A_W$ is `MvPolynomial (Fin 2) F` modulo the Weierstrass polynomial, with $x$ = `X 0` and
$y$ = `X 1`.

Source: P. Deligne, "Preuve des conjectures de Tate et de Shafarevitch [d'après G. Faltings]",
Séminaire Bourbaki, exposé 616, Astérisque 121–122 (1985), 25–41, Exemple 1.4, p. 28 (the form
$dx/F_y = -dy/F_x$); J. S. Milne, *Elliptic Curves*, 2nd ed., World Scientific, 2021, Chapter V,
§6, p. 211 (the case $y^2 = x^3 + ax + b$ over $\mathbb{C}$). The algebraic statement is proved
here. -/
theorem invariantDifferential_spec (hΔ : W.Δ ≠ 0) :
    (W.mvMk W.mvPolynomialP • W.invariantDifferential hΔ = D F _ (W.mvMk (X 0)) ∧
      W.mvMk W.mvPolynomialQ • W.invariantDifferential hΔ = D F _ (W.mvMk (X 1))) ∧
    (∀ η : KaehlerDifferential F W.MvCoordinateRing,
      W.mvMk W.mvPolynomialP • η = D F _ (W.mvMk (X 0)) →
      W.mvMk W.mvPolynomialQ • η = D F _ (W.mvMk (X 1)) → η = W.invariantDifferential hΔ) ∧
    ∃ b : Module.Basis (Fin 1) W.MvCoordinateRing (KaehlerDifferential F W.MvCoordinateRing),
      b 0 = W.invariantDifferential hΔ := by
  set e := W.kaehlerEquiv hΔ
  have he : ∀ w, e w = W.kaehlerToCoordinateRing w := fun _ ↦ rfl
  refine ⟨⟨e.injective ?_, e.injective ?_⟩, fun η h₁ h₂ ↦ e.injective ?_, ?_⟩
  · rw [map_smul, invariantDifferential, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one, he,
      kaehlerToCoordinateRing_D_X_zero]
  · rw [map_smul, invariantDifferential, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one, he,
      kaehlerToCoordinateRing_D_X_one]
  · obtain ⟨p, q, hpq⟩ := W.exists_mul_add_mul_eq_one_of_Δ_ne_zero hΔ
    have e₁ := congrArg e h₁
    have e₂ := congrArg e h₂
    rw [map_smul, smul_eq_mul, he, he, kaehlerToCoordinateRing_D_X_zero] at e₁
    rw [map_smul, smul_eq_mul, he, he, kaehlerToCoordinateRing_D_X_one] at e₂
    rw [invariantDifferential, LinearEquiv.apply_symm_apply, he]
    linear_combination p * e₁ + q * e₂ + (1 - W.kaehlerToCoordinateRing η) * hpq
  · exact ⟨(Module.Basis.singleton (Fin 1) W.MvCoordinateRing).map e.symm, by
      simp only [Module.Basis.map_apply, Module.Basis.singleton_apply]
      rfl⟩

/-! ### The pushforward of differentials along an algebra homomorphism -/

/-- The `F`-linear map `Ω¹_{A/F} → Ω¹_{B/F}`, `a • d a' ↦ f a • d (f a')`, of an `F`-algebra
homomorphism `f : A → B`: `KaehlerDifferential.map` for the `A`-algebra structure of `B` given by
`f`. -/
noncomputable def kaehlerMapAlgHom {A B : Type*} [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] (f : A →ₐ[F] B) :
    KaehlerDifferential F A →ₗ[F] KaehlerDifferential F B :=
  letI := f.toRingHom.toAlgebra
  haveI : IsScalarTower F A B := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  { toFun := KaehlerDifferential.map F F A B
    map_add' := map_add _
    map_smul' := fun c w ↦ by
      rw [← algebraMap_smul A c w, LinearMap.map_smul, RingHom.id_apply, algebraMap_smul,
        ← IsScalarTower.algebraMap_smul B c, algebraMap_smul] }

theorem kaehlerMapAlgHom_D {A B : Type*} [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] (f : A →ₐ[F] B) (a : A) :
    kaehlerMapAlgHom f (D F A a) = D F B (f a) := by
  let _ := f.toRingHom.toAlgebra
  have : IsScalarTower F A B := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  exact KaehlerDifferential.map_D F F A B a

theorem kaehlerMapAlgHom_smul {A B : Type*} [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] (f : A →ₐ[F] B) (a : A) (w : KaehlerDifferential F A) :
    kaehlerMapAlgHom f (a • w) = f a • kaehlerMapAlgHom f w := by
  let _ := f.toRingHom.toAlgebra
  have : IsScalarTower F A B := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  exact LinearMap.map_smul (KaehlerDifferential.map F F A B) a w

/-! ### Variable changes -/

section VariableChange

variable (C : VariableChange F)

theorem variableChange_Δ_ne_zero (hΔ : W.Δ ≠ 0) : (C • W).Δ ≠ 0 := by
  rw [variableChange_Δ]
  exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) hΔ

/-- The substitution `x ↦ u² x' + r`, `y ↦ u³ y' + u² s x' + t` of a variable change
`C = (u, r, s, t)`, as an `F`-algebra endomorphism of `F[x, y]`. -/
noncomputable def variableChangeSubst : MvPolynomial (Fin 2) F →ₐ[F] MvPolynomial (Fin 2) F :=
  aeval ![MvPolynomial.C ((C.u : F) ^ 2) * X 0 + MvPolynomial.C C.r,
    MvPolynomial.C ((C.u : F) ^ 3) * X 1 + MvPolynomial.C ((C.u : F) ^ 2 * C.s) * X 0 +
      MvPolynomial.C C.t]

/-- The inverse substitution `x' ↦ u⁻² (x - r)`, `y' ↦ u⁻³ (y - s (x - r) - t)`. -/
noncomputable def variableChangeSubstInv :
    MvPolynomial (Fin 2) F →ₐ[F] MvPolynomial (Fin 2) F :=
  aeval ![MvPolynomial.C (((C.u⁻¹ : Fˣ) : F) ^ 2) * (X 0 - MvPolynomial.C C.r),
    MvPolynomial.C (((C.u⁻¹ : Fˣ) : F) ^ 3) *
      (X 1 - MvPolynomial.C C.s * (X 0 - MvPolynomial.C C.r) - MvPolynomial.C C.t)]

private theorem C_u_mul_C_u_inv :
    MvPolynomial.C (C.u : F) * MvPolynomial.C ((C.u⁻¹ : Fˣ) : F) =
      (1 : MvPolynomial (Fin 2) F) := by
  rw [← map_mul, Units.mul_inv, map_one]

theorem variableChangeSubst_comp_inv :
    (variableChangeSubst C).comp (variableChangeSubstInv C) = AlgHom.id F _ := by
  have hab := C_u_mul_C_u_inv C
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
    simp only [variableChangeSubst, variableChangeSubstInv, AlgHom.comp_apply, aeval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, map_mul, map_sub, map_pow, aeval_C,
      MvPolynomial.algebraMap_eq, AlgHom.id_apply, Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · linear_combination (MvPolynomial.C (C.u : F) * MvPolynomial.C ((C.u⁻¹ : Fˣ) : F) + 1) *
      X 0 * hab
  · linear_combination (MvPolynomial.C (C.u : F) ^ 2 * MvPolynomial.C ((C.u⁻¹ : Fˣ) : F) ^ 2 +
      MvPolynomial.C (C.u : F) * MvPolynomial.C ((C.u⁻¹ : Fˣ) : F) + 1) * X 1 * hab

theorem variableChangeSubstInv_comp :
    (variableChangeSubstInv C).comp (variableChangeSubst C) = AlgHom.id F _ := by
  have hab := C_u_mul_C_u_inv C
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
    simp only [variableChangeSubst, variableChangeSubstInv, AlgHom.comp_apply, aeval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, map_mul, map_add, map_pow, aeval_C,
      MvPolynomial.algebraMap_eq, AlgHom.id_apply, Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · linear_combination (MvPolynomial.C (C.u : F) * MvPolynomial.C ((C.u⁻¹ : Fˣ) : F) + 1) *
      (X 0 - MvPolynomial.C C.r) * hab
  · linear_combination ((MvPolynomial.C (C.u : F) ^ 2 * MvPolynomial.C ((C.u⁻¹ : Fˣ) : F) ^ 2 +
      MvPolynomial.C (C.u : F) * MvPolynomial.C ((C.u⁻¹ : Fˣ) : F) + 1) *
        (X 1 - MvPolynomial.C C.s * (X 0 - MvPolynomial.C C.r) - MvPolynomial.C C.t) +
      (MvPolynomial.C (C.u : F) * MvPolynomial.C ((C.u⁻¹ : Fˣ) : F) + 1) * MvPolynomial.C C.s *
        (X 0 - MvPolynomial.C C.r)) * hab

/-- The ring homomorphism `F[X][Y] → F[x, y]`, `X ↦ x`, `Y ↦ y`. -/
noncomputable def bivariateToMvPolynomial : F[X][Y] →+* MvPolynomial (Fin 2) F :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom MvPolynomial.C (X 0)) (X 1)

@[simp] theorem bivariateToMvPolynomial_CC (a : F) :
    bivariateToMvPolynomial (Polynomial.C (Polynomial.C a)) = MvPolynomial.C a := by
  simp [bivariateToMvPolynomial]

@[simp] theorem bivariateToMvPolynomial_CX :
    bivariateToMvPolynomial (Polynomial.C (Polynomial.X : Polynomial F)) =
      (X 0 : MvPolynomial (Fin 2) F) := by
  simp [bivariateToMvPolynomial]

@[simp] theorem bivariateToMvPolynomial_Y :
    bivariateToMvPolynomial (Y : F[X][Y]) = (X 1 : MvPolynomial (Fin 2) F) := by
  simp [bivariateToMvPolynomial]

/-- **The Weierstrass polynomial after a variable change**, in `F[x, y]`:
`f_W(u² x + r, u³ y + u² s x + t) = u⁶ f_{C • W}(x, y)`. This is
`WeierstrassCurve.Affine.evalEval_polynomial_variableChange`, carried from `F[X][Y]` to
`F[x, y]`. -/
theorem variableChangeSubst_mvPolynomial :
    variableChangeSubst C W.mvPolynomial =
      MvPolynomial.C ((C.u : F) ^ 6) * (C • W).mvPolynomial := by
  have h := congrArg bivariateToMvPolynomial (Affine.evalEval_polynomial_variableChange W C)
  rw [Affine.evalEval_polynomial, Affine.polynomial] at h
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, RingHom.coe_comp, Function.comp_apply,
    map_add, map_sub, map_mul, map_pow, bivariateToMvPolynomial_CC, bivariateToMvPolynomial_CX,
    bivariateToMvPolynomial_Y] at h
  simp only [variableChangeSubst, mvPolynomial, map_add, map_sub, map_mul, map_pow, aeval_X,
    aeval_C, MvPolynomial.algebraMap_eq, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination h

/-- **The partial derivatives after a variable change**, in `F[x, y]`: `P_W` and `Q_W` become
`u³ P_{C • W}` and `u⁴ Q_{C • W} + s u³ P_{C • W}`. This is
`WeierstrassCurve.Affine.evalEval_partials_variableChange`, carried from `F[X][Y]` to
`F[x, y]`. -/
theorem variableChangeSubst_mvPolynomialP_Q :
    variableChangeSubst C W.mvPolynomialP =
        MvPolynomial.C ((C.u : F) ^ 3) * (C • W).mvPolynomialP ∧
      variableChangeSubst C W.mvPolynomialQ =
        MvPolynomial.C ((C.u : F) ^ 4) * (C • W).mvPolynomialQ +
          MvPolynomial.C (C.s * (C.u : F) ^ 3) * (C • W).mvPolynomialP := by
  obtain ⟨h₁, h₂⟩ := Affine.evalEval_partials_variableChange W C
  replace h₁ := congrArg bivariateToMvPolynomial h₁
  replace h₂ := congrArg bivariateToMvPolynomial h₂
  rw [Affine.evalEval_polynomialY, Affine.polynomialY] at h₁
  rw [Polynomial.evalEval_neg, Affine.evalEval_polynomialX, Affine.polynomialX,
    Affine.polynomialY] at h₂
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, RingHom.coe_comp, Function.comp_apply,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, bivariateToMvPolynomial_CC,
    bivariateToMvPolynomial_CX, bivariateToMvPolynomial_Y] at h₁ h₂
  constructor
  · simp only [variableChangeSubst, mvPolynomialP, map_add, map_mul, map_pow, map_ofNat,
      aeval_X, aeval_C, MvPolynomial.algebraMap_eq, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination h₁
  · simp only [variableChangeSubst, mvPolynomialQ, mvPolynomialP, map_add, map_sub, map_mul,
      map_pow, map_ofNat, aeval_X, aeval_C, MvPolynomial.algebraMap_eq, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    linear_combination h₂

/-- The substitution of a variable change as an `F`-algebra automorphism of `F[x, y]`. -/
noncomputable def variableChangeSubstEquiv :
    MvPolynomial (Fin 2) F ≃ₐ[F] MvPolynomial (Fin 2) F :=
  AlgEquiv.ofAlgHom (variableChangeSubst C) (variableChangeSubstInv C)
    (variableChangeSubst_comp_inv C) (variableChangeSubstInv_comp C)

theorem span_mvPolynomial_variableChange :
    Ideal.span {(C • W).mvPolynomial} =
      (Ideal.span {W.mvPolynomial}).map (variableChangeSubstEquiv C) := by
  rw [Ideal.map_span, Set.image_singleton]
  change _ = Ideal.span {variableChangeSubst C W.mvPolynomial}
  rw [variableChangeSubst_mvPolynomial, Ideal.span_singleton_mul_left_unit]
  have h := (Units.isUnit (C.u ^ 6)).map (MvPolynomial.C : F →+* MvPolynomial (Fin 2) F)
  rwa [Units.val_pow_eq_pow_val] at h

/-- The isomorphism `A_W ≅ A_{C • W}` induced by the substitution of a variable change. -/
noncomputable def variableChangeEquiv : W.MvCoordinateRing ≃ₐ[F] (C • W).MvCoordinateRing :=
  Ideal.quotientEquivAlg _ _ (variableChangeSubstEquiv C) (W.span_mvPolynomial_variableChange C)

theorem variableChangeEquiv_mvMk (p : MvPolynomial (Fin 2) F) :
    W.variableChangeEquiv C (W.mvMk p) = (C • W).mvMk (variableChangeSubst C p) :=
  Ideal.quotientEquivAlg_mk _ _ _ p

theorem mvMk_C (c : F) : W.mvMk (MvPolynomial.C c) = algebraMap F W.MvCoordinateRing c := by
  rw [← MvPolynomial.algebraMap_eq]
  exact (Ideal.Quotient.mkₐ F _).commutes c

/-- **The invariant differential under a variable change.** Let $F$ be a field, $W$ a Weierstrass
curve over $F$ with $\Delta_W \ne 0$, $C = (u, r, s, t)$ a variable change and $W' = C \cdot W$,
and let $A_W = F[x, y]/(f_W)$ and $A_{W'} = F[x, y]/(f_{W'})$. Then:

1. the $F$-algebra homomorphism $\varphi : F[x, y] \to F[x, y]$ with
   $\varphi(x) = u^2 x + r$ and $\varphi(y) = u^3 y + u^2 s x + t$ induces an isomorphism
   $\bar\varphi : A_W \to A_{W'}$ (`WeierstrassCurve.variableChangeEquiv`), with
   $\bar\varphi(\bar g) = \overline{\varphi(g)}$;
2. the map $\varphi_* : \Omega^1_{A_W/F} \to \Omega^1_{A_{W'}/F}$ with
   $\varphi_*(a \, db) = \bar\varphi(a) \, d\bar\varphi(b)$ (`WeierstrassCurve.kaehlerMapAlgHom`)
   sends $\omega_W$ to $u^{-1} \omega_{W'}$, where $\omega_W$ and $\omega_{W'}$ are the invariant
   differentials (`WeierstrassCurve.invariantDifferential`).

Source: B. Conrad, "Minimal models for elliptic curves", notes, version of 21 November 2015,
p. 6 ("the standard transformation laws for discriminants and invariant differentials");
J. S. Milne, *Elliptic Curves*, 2nd ed., World Scientific, 2021, Chapter II, Theorem 2.4(b),
p. 52, for the variable change and the coefficients of $W'$. The transformation law is proved
here. -/
theorem invariantDifferential_variableChange (hΔ : W.Δ ≠ 0) :
    (∀ p, W.variableChangeEquiv C (W.mvMk p) = (C • W).mvMk (variableChangeSubst C p)) ∧
    kaehlerMapAlgHom (W.variableChangeEquiv C).toAlgHom (W.invariantDifferential hΔ) =
      ((C.u⁻¹ : Fˣ) : F) • (C • W).invariantDifferential (W.variableChange_Δ_ne_zero C hΔ) := by
  refine ⟨W.variableChangeEquiv_mvMk C, ?_⟩
  set e := W.variableChangeEquiv C
  set z := kaehlerMapAlgHom e.toAlgHom (W.invariantDifferential hΔ)
  obtain ⟨⟨h₁, h₂⟩, -, -⟩ := W.invariantDifferential_spec hΔ
  obtain ⟨-, huniq, -⟩ := (C • W).invariantDifferential_spec (W.variableChange_Δ_ne_zero C hΔ)
  obtain ⟨hP, hQ⟩ := variableChangeSubst_mvPolynomialP_Q W C
  have he : ∀ p, e.toAlgHom (W.mvMk p) = (C • W).mvMk (variableChangeSubst C p) :=
    W.variableChangeEquiv_mvMk C
  have H₁ := congrArg (kaehlerMapAlgHom e.toAlgHom) h₁
  have H₂ := congrArg (kaehlerMapAlgHom e.toAlgHom) h₂
  rw [kaehlerMapAlgHom_smul, kaehlerMapAlgHom_D, he, he, hP] at H₁
  rw [kaehlerMapAlgHom_smul, kaehlerMapAlgHom_D, he, he, hQ] at H₂
  simp only [variableChangeSubst, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one] at H₁ H₂
  simp only [map_add, map_mul, map_pow, mvMk_C, Derivation.leibniz, Derivation.leibniz_pow,
    Derivation.map_algebraMap, smul_zero, add_zero] at H₁ H₂
  set a := algebraMap F (C • W).MvCoordinateRing (C.u : F)
  set b := algebraMap F (C • W).MvCoordinateRing ((C.u⁻¹ : Fˣ) : F)
  have hab : a * b = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  set P := (C • W).mvMk (C • W).mvPolynomialP
  set Q := (C • W).mvMk (C • W).mvPolynomialQ
  set dx := D F (C • W).MvCoordinateRing ((C • W).mvMk (X 0))
  set dy := D F (C • W).MvCoordinateRing ((C • W).mvMk (X 1))
  have G₁ : P • (a • z) = dx := by
    linear_combination (norm := module) b ^ 2 • H₁ + hab • ((a * b + 1) • (dx - (a * P) • z))
  have G₂ : Q • (a • z) = dy := by
    linear_combination (norm := module) b ^ 3 • H₂ -
      (algebraMap F (C • W).MvCoordinateRing C.s * a ^ 2 * b ^ 3) • G₁ +
      hab • ((a ^ 2 * b ^ 2 + a * b + 1) • (dy - (a * Q) • z))
  have hη := huniq (a • z) G₁ G₂
  rw [← hη, ← algebraMap_smul (C • W).MvCoordinateRing]
  change z = b • a • z
  linear_combination (norm := module) -(hab • z)

end VariableChange

end WeierstrassCurve
