/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.ProjectiveSchemeZeroSection
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.Tactic.LinearCombination

/-!
# Variable changes of the projective Weierstrass curve

Let `W` be a Weierstrass curve over a commutative ring `R` and let `C = (u, r, s, t)` be a variable
change, with `u ∈ Rˣ` and `r, s, t ∈ R`. The substitution
`X ↦ u² X + r Z`, `Y ↦ u³ Y + u² s X + t Z`, `Z ↦ Z` of `R[X, Y, Z]`
(`WeierstrassCurve.projectiveSubst`) carries the homogeneous Weierstrass polynomial `F_W` to
`u⁶ F_{C • W}` (`WeierstrassCurve.projectiveSubst_polynomial`). Hence it induces a graded
isomorphism of homogeneous coordinate rings `S_W ≃ S_{C • W}`, whose inverse is induced by `C⁻¹`
(`WeierstrassCurve.homogeneousVariableChangeEquiv`,
`WeierstrassCurve.projectiveGradedVariableChange`,
`WeierstrassCurve.projectiveGradedVariableChangeInv`), and, through the functoriality of `Proj`,
an isomorphism of projective Weierstrass curves `Proj S_{C • W} ≅ Proj S_W`
(`WeierstrassCurve.projectiveSchemeVariableChangeIso`). This isomorphism lies over `Spec R`,
carries the zero section `[0 : 1 : 0]` of `C • W` to that of `W`, and restricts on the affine
charts `Z ≠ 0` to the affine variable change `A_W → A_{C • W}`, `x ↦ u² x' + r`,
`y ↦ u³ y' + u² s x' + t` (`WeierstrassCurve.affineVariableChange`).

## Main definitions and results

* `WeierstrassCurve.projectiveSubst_polynomial`: `F_W(u² X + r Z, u³ Y + u² s X + t Z, Z) =
  u⁶ F_{C • W}(X, Y, Z)`.
* `WeierstrassCurve.homogeneousVariableChangeEquiv`: the `R`-algebra isomorphism
  `S_W ≃ S_{C • W}`.
* `WeierstrassCurve.projectiveGradedVariableChange`: the graded ring map `S_W → S_{C • W}`, with
  graded inverse `WeierstrassCurve.projectiveGradedVariableChangeInv`.
* `WeierstrassCurve.projectiveSchemeVariableChangeIso`: the isomorphism
  `(C • W).ProjectiveScheme ≅ W.ProjectiveScheme`, with
  `WeierstrassCurve.projectiveSchemeVariableChangeIso_hom_projectiveSchemeToSpec`,
  `WeierstrassCurve.zeroSection_comp_projectiveSchemeVariableChangeIso_hom` and
  `WeierstrassCurve.affineChart_comp_projectiveSchemeVariableChangeIso_hom`.

## References

* J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
  <https://jmilne.org/math/Books/EC2.pdf>, Chapter II, Theorem 2.4(b), p. 52: the isomorphism
  `(x : y : z) ↦ (u² x + r z : u³ y + s u² x + t z : z)` between the curves of the two
  Weierstrass equations.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

private lemma u_mul_a₁ (W : WeierstrassCurve R) (C : VariableChange R) :
    (C.u : R) * (C • W).a₁ = W.a₁ + 2 * C.s := by
  rw [variableChange_a₁, ← mul_assoc, Units.mul_inv, one_mul]

private lemma u_mul_a₂ (W : WeierstrassCurve R) (C : VariableChange R) :
    (C.u : R) ^ 2 * (C • W).a₂ = W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2 := by
  rw [variableChange_a₂, ← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]

private lemma u_mul_a₃ (W : WeierstrassCurve R) (C : VariableChange R) :
    (C.u : R) ^ 3 * (C • W).a₃ = W.a₃ + C.r * W.a₁ + 2 * C.t := by
  rw [variableChange_a₃, ← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]

private lemma u_mul_a₄ (W : WeierstrassCurve R) (C : VariableChange R) :
    (C.u : R) ^ 4 * (C • W).a₄ = W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ -
      (C.t + C.r * C.s) * W.a₁ + 3 * C.r ^ 2 - 2 * C.s * C.t := by
  rw [variableChange_a₄, ← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]

private lemma u_mul_a₆ (W : WeierstrassCurve R) (C : VariableChange R) :
    (C.u : R) ^ 6 * (C • W).a₆ = W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 -
      C.t * W.a₃ - C.t ^ 2 - C.r * C.t * W.a₁ := by
  rw [variableChange_a₆, ← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]

/-- The substitution `X ↦ u² X + r Z`, `Y ↦ u³ Y + u² s X + t Z`, `Z ↦ Z` of `R[X, Y, Z]`
attached to a variable change `C = (u, r, s, t)`. -/
noncomputable def projectiveSubst (C : VariableChange R) :
    MvPolynomial (Fin 3) R →ₐ[R] MvPolynomial (Fin 3) R :=
  aeval ![MvPolynomial.C ((C.u : R) ^ 2) * X 0 + MvPolynomial.C C.r * X 2,
    MvPolynomial.C ((C.u : R) ^ 3) * X 1 + MvPolynomial.C ((C.u : R) ^ 2 * C.s) * X 0 +
      MvPolynomial.C C.t * X 2, X 2]

/-- The substitution sends `X` to `u² X + r Z`. -/
@[simp]
theorem projectiveSubst_X_zero (C : VariableChange R) :
    projectiveSubst C (X 0) = MvPolynomial.C ((C.u : R) ^ 2) * X 0 + MvPolynomial.C C.r * X 2 := by
  simp [projectiveSubst]

/-- The substitution sends `Y` to `u³ Y + u² s X + t Z`. -/
@[simp]
theorem projectiveSubst_X_one (C : VariableChange R) :
    projectiveSubst C (X 1) = MvPolynomial.C ((C.u : R) ^ 3) * X 1 +
      MvPolynomial.C ((C.u : R) ^ 2 * C.s) * X 0 + MvPolynomial.C C.t * X 2 := by
  simp [projectiveSubst]

/-- The substitution fixes `Z`. -/
@[simp]
theorem projectiveSubst_X_two (C : VariableChange R) : projectiveSubst C (X 2) = X 2 := by
  simp [projectiveSubst]

/-- The substitution fixes constants. -/
@[simp]
theorem projectiveSubst_C (C : VariableChange R) (a : R) :
    projectiveSubst C (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [projectiveSubst, MvPolynomial.algebraMap_eq]

/-- **The homogeneous Weierstrass polynomial after a variable change.** Let `W` be a
Weierstrass curve over a commutative ring `R`, with homogeneous Weierstrass polynomial
`F_W = Y² Z + a₁ X Y Z + a₃ Y Z² - X³ - a₂ X² Z - a₄ X Z² - a₆ Z³` in `R[X, Y, Z]`
(`WeierstrassCurve.Projective.polynomial`, variables `X, Y, Z = 0, 1, 2`), and let
`C = (u, r, s, t)` be a variable change. Then, in `R[X, Y, Z]`,
`F_W(u² X + r Z, u³ Y + u² s X + t Z, Z) = u⁶ F_{C • W}(X, Y, Z)`.

Source: J. S. Milne, *Elliptic Curves*, 2nd ed., author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter II, Theorem 2.4(b), p. 52: the map
`(x : y : z) ↦ (u² x + r z : u³ y + s u² x + t z : z)` between the curves of the two equations;
the identity follows by expansion, over any commutative ring (the field hypothesis of the source
is not used). -/
theorem projectiveSubst_polynomial (W : WeierstrassCurve R) (C : VariableChange R) :
    projectiveSubst C W.toProjective.polynomial =
      MvPolynomial.C ((C.u : R) ^ 6) * (C • W).toProjective.polynomial := by
  have h₁ := congrArg (MvPolynomial.C (σ := Fin 3)) (u_mul_a₁ W C)
  have h₂ := congrArg (MvPolynomial.C (σ := Fin 3)) (u_mul_a₂ W C)
  have h₃ := congrArg (MvPolynomial.C (σ := Fin 3)) (u_mul_a₃ W C)
  have h₄ := congrArg (MvPolynomial.C (σ := Fin 3)) (u_mul_a₄ W C)
  have h₆ := congrArg (MvPolynomial.C (σ := Fin 3)) (u_mul_a₆ W C)
  simp only [map_mul, map_add, map_sub, map_pow, map_ofNat] at h₁ h₂ h₃ h₄ h₆
  simp only [Projective.polynomial, toProjective, map_add, map_sub, map_mul, map_pow,
    projectiveSubst_X_zero, projectiveSubst_X_one, projectiveSubst_X_two, projectiveSubst_C]
  linear_combination (-(MvPolynomial.C (C.u : R) ^ 5) * X 0 * X 1 * X 2) * h₁ +
    (MvPolynomial.C (C.u : R) ^ 4 * X 0 ^ 2 * X 2) * h₂ +
    (-(MvPolynomial.C (C.u : R) ^ 3) * X 1 * X 2 ^ 2) * h₃ +
    (MvPolynomial.C (C.u : R) ^ 2 * X 0 * X 2 ^ 2) * h₄ + X 2 ^ 3 * h₆

/-- Substituting with `C` and then with `C⁻¹` is the identity of `R[X, Y, Z]`. -/
theorem projectiveSubst_inv_comp (C : VariableChange R) :
    (projectiveSubst C⁻¹).comp (projectiveSubst C) = AlgHom.id R _ := by
  have hv : (MvPolynomial.C (C.u : R) : MvPolynomial (Fin 3) R) *
      MvPolynomial.C ((C.u⁻¹ : Rˣ) : R) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  refine MvPolynomial.algHom_ext fun i => ?_
  fin_cases i <;> simp [VariableChange.inv_def]
  · linear_combination
      (MvPolynomial.C (C.u : R) * MvPolynomial.C ((C.u⁻¹ : Rˣ) : R) + 1) *
        (X 0 - MvPolynomial.C C.r * X 2) * hv
  · linear_combination (((MvPolynomial.C (C.u : R) * MvPolynomial.C ((C.u⁻¹ : Rˣ) : R)) ^ 2 +
      MvPolynomial.C (C.u : R) * MvPolynomial.C ((C.u⁻¹ : Rˣ) : R) + 1) *
        (X 1 - MvPolynomial.C C.t * X 2) -
      MvPolynomial.C C.s * (MvPolynomial.C (C.u : R) * MvPolynomial.C ((C.u⁻¹ : Rˣ) : R)) ^ 2 *
        (X 0 - MvPolynomial.C C.r * X 2)) * hv

/-- Substituting with `C⁻¹` and then with `C` is the identity of `R[X, Y, Z]`. -/
theorem projectiveSubst_comp_inv (C : VariableChange R) :
    (projectiveSubst C).comp (projectiveSubst C⁻¹) = AlgHom.id R _ := by
  have hv : (MvPolynomial.C (C.u : R) : MvPolynomial (Fin 3) R) *
      MvPolynomial.C ((C.u⁻¹ : Rˣ) : R) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  refine MvPolynomial.algHom_ext fun i => ?_
  fin_cases i <;> simp [VariableChange.inv_def]
  · linear_combination
      (MvPolynomial.C (C.u : R) * MvPolynomial.C ((C.u⁻¹ : Rˣ) : R) + 1) * X 0 * hv
  · linear_combination ((MvPolynomial.C (C.u : R) * MvPolynomial.C ((C.u⁻¹ : Rˣ) : R)) ^ 2 +
      MvPolynomial.C (C.u : R) * MvPolynomial.C ((C.u⁻¹ : Rˣ) : R) + 1) * X 1 * hv

/-- The substitution preserves homogeneity and degree. -/
theorem projectiveSubst_isHomogeneous (C : VariableChange R) {n : ℕ}
    {p : MvPolynomial (Fin 3) R} (hp : p.IsHomogeneous n) :
    (projectiveSubst C p).IsHomogeneous n := by
  have := hp.eval₂ (algebraMap R (MvPolynomial (Fin 3) R))
    ![MvPolynomial.C ((C.u : R) ^ 2) * X 0 + MvPolynomial.C C.r * X 2,
      MvPolynomial.C ((C.u : R) ^ 3) * X 1 + MvPolynomial.C ((C.u : R) ^ 2 * C.s) * X 0 +
        MvPolynomial.C C.t * X 2, X 2] (n := 1) (fun r => isHomogeneous_C _ r) (fun i => by
      fin_cases i
      · exact (isHomogeneous_C_mul_X _ _).add (isHomogeneous_C_mul_X _ _)
      · exact ((isHomogeneous_C_mul_X _ _).add (isHomogeneous_C_mul_X _ _)).add
          (isHomogeneous_C_mul_X _ _)
      · exact isHomogeneous_X _ _)
  simpa [projectiveSubst, aeval_def] using this

/-- The `R`-algebra map `S_W → S_{W'}` induced by the substitution of a variable change `C` with
`C • W = W'`. -/
noncomputable def homogeneousVariableChangeAux (C : VariableChange R) {W W' : WeierstrassCurve R}
    (h : C • W = W') : W.HomogeneousCoordinateRing →ₐ[R] W'.HomogeneousCoordinateRing :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ R _).comp (projectiveSubst C)) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    subst h
    have hF : Ideal.Quotient.mk (Ideal.span {(C • W).toProjective.polynomial})
        (C • W).toProjective.polynomial = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    simp [projectiveSubst_polynomial, hF])

/-- The map `S_W → S_{W'}` sends the class of `p` to the class of its substitution. -/
theorem homogeneousVariableChangeAux_mk (C : VariableChange R) {W W' : WeierstrassCurve R}
    (h : C • W = W') (p : MvPolynomial (Fin 3) R) :
    homogeneousVariableChangeAux C h (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (projectiveSubst C p) :=
  rfl

/-- The map induced by `C⁻¹` is a left inverse of the map induced by `C`. -/
theorem homogeneousVariableChangeAux_comp (C : VariableChange R) {W W' : WeierstrassCurve R}
    (h : C • W = W') (h' : C⁻¹ • W' = W) :
    (homogeneousVariableChangeAux C⁻¹ h').comp (homogeneousVariableChangeAux C h) =
      AlgHom.id R _ := by
  refine Ideal.Quotient.algHom_ext R (MvPolynomial.algHom_ext fun i => ?_)
  change Ideal.Quotient.mk _ (projectiveSubst C⁻¹ (projectiveSubst C (X i))) =
    Ideal.Quotient.mk _ (X i)
  rw [← AlgHom.comp_apply, projectiveSubst_inv_comp, AlgHom.id_apply]

/-- The map induced by `C⁻¹` is a right inverse of the map induced by `C`. -/
theorem homogeneousVariableChangeAux_comp' (C : VariableChange R) {W W' : WeierstrassCurve R}
    (h : C • W = W') (h' : C⁻¹ • W' = W) :
    (homogeneousVariableChangeAux C h).comp (homogeneousVariableChangeAux C⁻¹ h') =
      AlgHom.id R _ := by
  refine Ideal.Quotient.algHom_ext R (MvPolynomial.algHom_ext fun i => ?_)
  change Ideal.Quotient.mk _ (projectiveSubst C (projectiveSubst C⁻¹ (X i))) =
    Ideal.Quotient.mk _ (X i)
  rw [← AlgHom.comp_apply, projectiveSubst_comp_inv, AlgHom.id_apply]

/-- The map `S_W → S_{W'}` induced by a variable change preserves degrees. -/
theorem homogeneousVariableChangeAux_mem (C : VariableChange R) {W W' : WeierstrassCurve R}
    (h : C • W = W') {n : ℕ} {x : W.HomogeneousCoordinateRing} (hx : x ∈ W.projectiveGrading n) :
    homogeneousVariableChangeAux C h x ∈ W'.projectiveGrading n := by
  obtain ⟨p, hp, rfl⟩ := hx
  exact W'.mk_mem_projectiveGrading
    (projectiveSubst_isHomogeneous C ((mem_homogeneousSubmodule _ _).mp hp))

variable (W : WeierstrassCurve R)

/-- **The homogeneous coordinate rings of `W` and `C • W`.** For a Weierstrass curve `W` over a
commutative ring `R` and a variable change `C = (u, r, s, t)`, this is the `R`-algebra
isomorphism `S_W = R[X, Y, Z] / (F_W) ≃ S_{C • W} = R[X, Y, Z] / (F_{C • W})` sending the class
of `p(X, Y, Z)` to the class of `p(u² X + r Z, u³ Y + u² s X + t Z, Z)`; its inverse is the map
induced in the same way by `C⁻¹`, using `C⁻¹ • (C • W) = W`. It preserves degrees
(`WeierstrassCurve.homogeneousVariableChangeAux_mem`). -/
noncomputable def homogeneousVariableChangeEquiv (C : VariableChange R) :
    W.HomogeneousCoordinateRing ≃ₐ[R] (C • W).HomogeneousCoordinateRing :=
  AlgEquiv.ofAlgHom (homogeneousVariableChangeAux C rfl)
    (homogeneousVariableChangeAux C⁻¹ (inv_smul_smul C W))
    (homogeneousVariableChangeAux_comp' C rfl _) (homogeneousVariableChangeAux_comp C rfl _)

/-- **The graded ring map `S_W → S_{C • W}` of a variable change.** The ring map underlying
`WeierstrassCurve.homogeneousVariableChangeEquiv`, as a map of graded rings for the gradings by
total degree. -/
noncomputable def projectiveGradedVariableChange (C : VariableChange R) :
    W.projectiveGrading →+*ᵍ (C • W).projectiveGrading :=
  ⟨(homogeneousVariableChangeAux C rfl).toRingHom,
    fun hx => homogeneousVariableChangeAux_mem C rfl hx⟩

/-- The graded ring map `S_{C • W} → S_W` induced by `C⁻¹`, the inverse of
`WeierstrassCurve.projectiveGradedVariableChange`. -/
noncomputable def projectiveGradedVariableChangeInv (C : VariableChange R) :
    (C • W).projectiveGrading →+*ᵍ W.projectiveGrading :=
  ⟨(homogeneousVariableChangeAux C⁻¹ (inv_smul_smul C W)).toRingHom,
    fun hx => homogeneousVariableChangeAux_mem C⁻¹ _ hx⟩

/-- `S_{C • W} → S_W → S_{C • W}` is the identity. -/
theorem projectiveGradedVariableChange_comp_inv (C : VariableChange R) :
    (W.projectiveGradedVariableChange C).comp (W.projectiveGradedVariableChangeInv C) =
      GradedRingHom.id _ := by
  refine GradedRingHom.ext fun x => ?_
  rw [GradedRingHom.comp_apply, GradedRingHom.id_apply]
  change homogeneousVariableChangeAux C rfl
    (homogeneousVariableChangeAux C⁻¹ (inv_smul_smul C W) x) = x
  rw [← AlgHom.comp_apply, homogeneousVariableChangeAux_comp', AlgHom.id_apply]

/-- `S_W → S_{C • W} → S_W` is the identity. -/
theorem projectiveGradedVariableChangeInv_comp (C : VariableChange R) :
    (W.projectiveGradedVariableChangeInv C).comp (W.projectiveGradedVariableChange C) =
      GradedRingHom.id _ := by
  refine GradedRingHom.ext fun x => ?_
  rw [GradedRingHom.comp_apply, GradedRingHom.id_apply]
  change homogeneousVariableChangeAux C⁻¹ (inv_smul_smul C W)
    (homogeneousVariableChangeAux C rfl x) = x
  rw [← AlgHom.comp_apply, homogeneousVariableChangeAux_comp, AlgHom.id_apply]

/-- If `f : S_W → S_{W'}` and `g : S_{W'} → S_W` are graded and `f ∘ g = id`, then the irrelevant
ideal of `S_{W'}` is contained in the ideal generated by the image of that of `S_W`. -/
private theorem irrelevant_le_map_of_comp {W' : WeierstrassCurve R}
    (f : W.projectiveGrading →+*ᵍ W'.projectiveGrading)
    (g : W'.projectiveGrading →+*ᵍ W.projectiveGrading) (hfg : f.comp g = GradedRingHom.id _) :
    HomogeneousIdeal.irrelevant W'.projectiveGrading ≤
      (HomogeneousIdeal.irrelevant W.projectiveGrading).map f := by
  change (HomogeneousIdeal.irrelevant W'.projectiveGrading).toIdeal ≤
    ((HomogeneousIdeal.irrelevant W.projectiveGrading).map f).toIdeal
  refine W'.irrelevant_le_span_coordinates.trans (Ideal.span_le.mpr ?_)
  rintro _ ⟨i, rfl⟩
  have h1 : f (g (W'.projectiveCoordinate i)) = W'.projectiveCoordinate i := by
    rw [← GradedRingHom.comp_apply, hfg, GradedRingHom.id_apply]
  rw [HomogeneousIdeal.toIdeal_map, ← h1]
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos
    (g.map_mem (W'.projectiveCoordinate_mem i)))

/-- The irrelevant ideal of `S_{C • W}` is contained in the ideal generated by the image of the
irrelevant ideal of `S_W`: the hypothesis of `AlgebraicGeometry.Proj.map`. -/
theorem irrelevant_le_map_projectiveGradedVariableChange (C : VariableChange R) :
    HomogeneousIdeal.irrelevant (C • W).projectiveGrading ≤
      (HomogeneousIdeal.irrelevant W.projectiveGrading).map (W.projectiveGradedVariableChange C) :=
  irrelevant_le_map_of_comp W _ _ (W.projectiveGradedVariableChange_comp_inv C)

/-- The irrelevant ideal of `S_W` is contained in the ideal generated by the image of the
irrelevant ideal of `S_{C • W}` under the inverse map. -/
theorem irrelevant_le_map_projectiveGradedVariableChangeInv (C : VariableChange R) :
    HomogeneousIdeal.irrelevant W.projectiveGrading ≤
      (HomogeneousIdeal.irrelevant (C • W).projectiveGrading).map
        (W.projectiveGradedVariableChangeInv C) :=
  irrelevant_le_map_of_comp (C • W) _ _ (W.projectiveGradedVariableChangeInv_comp C)

private theorem proj_map_eq_id {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    {𝒜 : ℕ → σ} [GradedRing 𝒜] (f : 𝒜 →+*ᵍ 𝒜) (hf) (h : f = GradedRingHom.id 𝒜) :
    Proj.map f hf = 𝟙 (Proj 𝒜) := by
  subst h
  exact Proj.map_id

/-- **The isomorphism of projective Weierstrass curves given by a variable change.** Let `W` be
a Weierstrass curve over a commutative ring `R` and `C = (u, r, s, t)` a variable change. This is
the isomorphism of schemes `Proj S_{C • W} ≅ Proj S_W` whose morphism is
`AlgebraicGeometry.Proj.map` of the graded ring map `S_W → S_{C • W}`,
`X ↦ u² X + r Z`, `Y ↦ u³ Y + u² s X + t Z`, `Z ↦ Z`
(`WeierstrassCurve.projectiveGradedVariableChange`), and whose inverse is `Proj.map` of the map
induced by `C⁻¹`; on points it is `(x : y : z) ↦ (u² x + r z : u³ y + s u² x + t z : z)`. It
lies over `Spec R` (`projectiveSchemeVariableChangeIso_hom_projectiveSchemeToSpec`), matches the
zero sections (`zeroSection_comp_projectiveSchemeVariableChangeIso_hom`) and restricts on the
affine charts to the affine variable change
(`affineChart_comp_projectiveSchemeVariableChangeIso_hom`).

Source: J. S. Milne, *Elliptic Curves*, 2nd ed., author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter II, Theorem 2.4(b), p. 52 (the map, there over a
field for curves with nonzero discriminant; neither hypothesis is used here). The converse part of
the source (every isomorphism fixing `O` has this form) is not proved here. -/
noncomputable def projectiveSchemeVariableChangeIso (C : VariableChange R) :
    (C • W).ProjectiveScheme ≅ W.ProjectiveScheme where
  hom := Proj.map (W.projectiveGradedVariableChange C)
    (W.irrelevant_le_map_projectiveGradedVariableChange C)
  inv := Proj.map (W.projectiveGradedVariableChangeInv C)
    (W.irrelevant_le_map_projectiveGradedVariableChangeInv C)
  hom_inv_id := by
    rw [← Proj.map_comp]
    exact proj_map_eq_id _ _ (W.projectiveGradedVariableChange_comp_inv C)
  inv_hom_id := by
    rw [← Proj.map_comp]
    exact proj_map_eq_id _ _ (W.projectiveGradedVariableChangeInv_comp C)

end WeierstrassCurve

section AwayLift

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜] {T : Type u} [CommRing T]

/-- The ring map `A_(s) → T` induced by a ring map `ρ : A → T` with `ρ s` a unit. -/
private noncomputable def awayLiftAux (ρ : A →+* T) (s : A) (hs : IsUnit (ρ s)) : Away 𝒜 s →+* T :=
  (IsLocalization.Away.lift s hs).comp (algebraMap (Away 𝒜 s) (Localization.Away s))

private lemma awayLiftAux_mk_mul (ρ : A →+* T) {s : A} (hs : IsUnit (ρ s)) {d : ℕ} (hd : s ∈ 𝒜 d)
    (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    ρ s ^ n * awayLiftAux 𝒜 ρ s hs (Away.mk 𝒜 hd n a ha) = ρ a := by
  rw [awayLiftAux, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.Away.lift]
  have := (IsLocalization.lift_mk'_spec (M := Submonoid.powers s) (S := Localization.Away s)
    (g := ρ) (fun y => ?_) a _ ⟨s ^ n, n, rfl⟩).mp rfl
  · rw [this, map_pow]
  · obtain ⟨_, k, rfl⟩ := y
    simpa using hs.pow k

private lemma awayLiftAux_algebraMap (ρ : A →+* T) {s : A} (hs : IsUnit (ρ s)) (c : 𝒜 0) :
    awayLiftAux 𝒜 ρ s hs (algebraMap (𝒜 0) (Away 𝒜 s) c) = ρ c := by
  rw [awayLiftAux, RingHom.comp_apply]
  exact IsLocalization.Away.lift_eq s hs (c : A)

private lemma awayLiftAux_congr {ρ ρ' : A →+* T} (h : ρ = ρ') (s : A) (hs : IsUnit (ρ s))
    (hs' : IsUnit (ρ' s)) : awayLiftAux 𝒜 ρ s hs = awayLiftAux 𝒜 ρ' s hs' := by
  subst h
  rfl

private lemma awayLiftAux_comp_awayMap (ρ : A →+* T) {f g x : A} {d e : ℕ} (hf : f ∈ 𝒜 d)
    (hg : g ∈ 𝒜 e) (hx : x = f * g) (hux : IsUnit (ρ x)) (huf : IsUnit (ρ f)) :
    (awayLiftAux 𝒜 ρ x hux).comp (awayMap 𝒜 hg hx) = awayLiftAux 𝒜 ρ f huf := by
  refine RingHom.ext fun y => ?_
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hf y
  rw [RingHom.comp_apply, awayMap_mk]
  refine (hux.pow n).mul_left_cancel ?_
  rw [awayLiftAux_mk_mul]
  have h2 := awayLiftAux_mk_mul 𝒜 ρ huf hf n a ha
  simp only [hx, map_mul, map_pow, mul_pow]
  rw [← h2]
  ring

private lemma awayLiftAux_comp_awayMap' {B τ : Type u} [CommRing B] [SetLike τ B]
    [AddSubgroupClass τ B] {ℬ : ℕ → τ} [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ) (ρ : B →+* T)
    {s : A} {d : ℕ} (hs : s ∈ 𝒜 d) (hu : IsUnit (ρ (f s))) :
    (awayLiftAux ℬ ρ (f s) hu).comp (Away.map f s) =
      awayLiftAux 𝒜 (ρ.comp (f : A →+* B)) s hu := by
  refine RingHom.ext fun y => ?_
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hs y
  rw [RingHom.comp_apply, Away.map_mk]
  refine (hu.pow n).mul_left_cancel ?_
  rw [awayLiftAux_mk_mul]
  have h2 := awayLiftAux_mk_mul 𝒜 (ρ.comp (f : A →+* B)) hu hs n a ha
  simpa using h2.symm

private lemma comp_awayLiftAux {T' : Type u} [CommRing T'] (φ : T →+* T') (ρ : A →+* T) {s : A}
    {d : ℕ} (hd : s ∈ 𝒜 d) (hu : IsUnit (ρ s)) :
    φ.comp (awayLiftAux 𝒜 ρ s hu) = awayLiftAux 𝒜 (φ.comp ρ) s (hu.map φ) := by
  refine RingHom.ext fun y => ?_
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hd y
  refine ((hu.map φ).pow n).mul_left_cancel ?_
  have h1 := awayLiftAux_mk_mul 𝒜 (φ.comp ρ) (hu.map φ) hd n a ha
  have h2 := congrArg φ (awayLiftAux_mk_mul 𝒜 ρ hu hd n a ha)
  simp only [RingHom.comp_apply, map_mul, map_pow] at h1 h2 ⊢
  rw [h1, h2]

private lemma fromZeroRingHom_eq_mk {s : A} {d : ℕ} (hs : s ∈ 𝒜 d) (c : 𝒜 0) :
    fromZeroRingHom 𝒜 (Submonoid.powers s) c = Away.mk 𝒜 hs 0 c (by simp) := by
  apply val_injective
  rw [Away.val_mk]
  simp only [pow_zero]
  rfl

private lemma specMap_awayLiftAux_awayι (ρ : A →+* T) {s s' : A} {i j : ℕ} (hs : s ∈ 𝒜 i)
    (hs' : s' ∈ 𝒜 j) (hi : 0 < i) (hj : 0 < j) (hu : IsUnit (ρ s)) (hu' : IsUnit (ρ s')) :
    Spec.map (CommRingCat.ofHom (awayLiftAux 𝒜 ρ s hu)) ≫ Proj.awayι 𝒜 s hs hi =
      Spec.map (CommRingCat.ofHom (awayLiftAux 𝒜 ρ s' hu')) ≫ Proj.awayι 𝒜 s' hs' hj := by
  have hx : IsUnit (ρ (s * s')) := by rw [map_mul]; exact hu.mul hu'
  rw [← awayLiftAux_comp_awayMap 𝒜 ρ hs hs' rfl hx hu,
    ← awayLiftAux_comp_awayMap 𝒜 ρ hs' hs (mul_comm s s') hx hu', CommRingCat.ofHom_comp,
    CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
    Proj.SpecMap_awayMap_awayι, Proj.SpecMap_awayMap_awayι]
  congr 1

end AwayLift

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Evaluation `S_W → R` at the point `[0 : 1 : 0]`. -/
private noncomputable def evalZeroSectionAux : W.HomogeneousCoordinateRing →+* R :=
  Ideal.Quotient.lift _ (aeval ![(0 : R), 1, 0]).toRingHom (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [Projective.polynomial])

private theorem specMap_awayLiftAux_eq_zeroSection (ρ : W.HomogeneousCoordinateRing →+* R)
    (h0 : ρ (W.projectiveCoordinate 0) = 0) (h2 : ρ (W.projectiveCoordinate 2) = 0)
    (hY : IsUnit (ρ (W.projectiveCoordinate 1))) (hR : ∀ r, ρ (algebraMap R _ r) = r) :
    Spec.map (CommRingCat.ofHom (awayLiftAux W.projectiveGrading ρ _ hY)) ≫
      Proj.awayι W.projectiveGrading _ (W.projectiveCoordinate_mem 1) Nat.one_pos =
        W.zeroSection := by
  set L := awayLiftAux W.projectiveGrading ρ _ hY
  have key : L.comp W.awayYRingEquiv.symm.toRingHom = W.evalAtInfinity.toRingHom := by
    refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_))
    · change L (W.awayYRingEquiv.symm (algebraMap R _ r)) = W.evalAtInfinity (algebraMap R _ r)
      rw [AlgHom.commutes, ← W.awayYRingEquiv_algebraMap r, RingEquiv.symm_apply_apply,
        awayLiftAux_algebraMap]
      exact hR r
    · fin_cases i
      · change L (W.awayYRingEquiv.symm W.zAtInfinity) = W.evalAtInfinity W.zAtInfinity
        rw [awayYRingEquiv_symm_zAtInfinity, zAtInfinity, evalAtInfinity_mk]
        refine (hY.pow 1).mul_left_cancel ?_
        rw [xOverY, awayLiftAux_mk_mul, h0]
        simp
      · change L (W.awayYRingEquiv.symm W.wAtInfinity) = W.evalAtInfinity W.wAtInfinity
        rw [awayYRingEquiv_symm_wAtInfinity, evalAtInfinity_wAtInfinity]
        refine (hY.pow 1).mul_left_cancel ?_
        rw [zOverY, awayLiftAux_mk_mul, h2]
        simp
  have hL : L = W.evalAtInfinity.toRingHom.comp W.awayYRingEquiv.toRingHom := by
    rw [← key, RingHom.comp_assoc]
    ext x
    simp
  rw [zeroSection, chartAtInfinity, ← Category.assoc, ← Spec.map_comp, hL,
    CommRingCat.ofHom_comp]
  rfl

/-- The morphism of `projectiveSchemeVariableChangeIso` is `Proj.map` of the graded ring map. -/
theorem projectiveSchemeVariableChangeIso_hom (C : VariableChange R) :
    (W.projectiveSchemeVariableChangeIso C).hom = Proj.map (W.projectiveGradedVariableChange C)
      (W.irrelevant_le_map_projectiveGradedVariableChange C) :=
  rfl

private theorem evalZeroSectionAux_mk (p : MvPolynomial (Fin 3) R) :
    W.evalZeroSectionAux (Ideal.Quotient.mk _ p) = aeval ![(0 : R), 1, 0] p :=
  rfl

/-- The graded map sends the class of `p` to the class of its substitution. -/
theorem projectiveGradedVariableChange_mk (C : VariableChange R) (p : MvPolynomial (Fin 3) R) :
    W.projectiveGradedVariableChange C (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (projectiveSubst C p) :=
  rfl

/-- The graded map is the identity on constants. -/
theorem projectiveGradedVariableChange_algebraMap (C : VariableChange R) (r : R) :
    W.projectiveGradedVariableChange C (algebraMap R _ r) = algebraMap R _ r :=
  (homogeneousVariableChangeAux C rfl).commutes r

/-- **The variable change isomorphism preserves the zero section.** Let `W` be a Weierstrass
curve over a commutative ring `R` and `C` a variable change. The composite of the zero section
`O = [0 : 1 : 0]` of `C • W` with `projectiveSchemeVariableChangeIso W C` is the zero section
of `W`.

Source: J. S. Milne, *Elliptic Curves*, 2nd ed., author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter II, Theorem 2.4(b), p. 52 (the isomorphism sends
`O` to `O`). -/
theorem zeroSection_comp_projectiveSchemeVariableChangeIso_hom (C : VariableChange R) :
    (C • W).zeroSection ≫ (W.projectiveSchemeVariableChangeIso C).hom = W.zeroSection := by
  have hu' : IsUnit ((C • W).evalZeroSectionAux ((C • W).projectiveCoordinate 1)) := by
    rw [projectiveCoordinate, evalZeroSectionAux_mk]
    simp
  have hu : IsUnit ((C • W).evalZeroSectionAux
      (W.projectiveGradedVariableChange C (W.projectiveCoordinate 1))) := by
    rw [projectiveCoordinate, projectiveGradedVariableChange_mk, evalZeroSectionAux_mk]
    simp
  have h0 : (C • W).evalZeroSectionAux ((C • W).projectiveCoordinate 0) = 0 := by
    rw [projectiveCoordinate, evalZeroSectionAux_mk]
    simp
  have h2 : (C • W).evalZeroSectionAux ((C • W).projectiveCoordinate 2) = 0 := by
    rw [projectiveCoordinate, evalZeroSectionAux_mk]
    simp
  have hR : ∀ r, (C • W).evalZeroSectionAux (algebraMap R _ r) = r := fun r => by
    rw [show algebraMap R (C • W).HomogeneousCoordinateRing r =
      Ideal.Quotient.mk _ (MvPolynomial.C r) from rfl, evalZeroSectionAux_mk]
    simp
  have h0' : ((C • W).evalZeroSectionAux.comp (W.projectiveGradedVariableChange C :
      W.HomogeneousCoordinateRing →+* _)) (W.projectiveCoordinate 0) = 0 := by
    rw [RingHom.comp_apply]
    change (C • W).evalZeroSectionAux (W.projectiveGradedVariableChange C _) = _
    rw [projectiveCoordinate, projectiveGradedVariableChange_mk, evalZeroSectionAux_mk]
    simp
  have h2' : ((C • W).evalZeroSectionAux.comp (W.projectiveGradedVariableChange C :
      W.HomogeneousCoordinateRing →+* _)) (W.projectiveCoordinate 2) = 0 := by
    rw [RingHom.comp_apply]
    change (C • W).evalZeroSectionAux (W.projectiveGradedVariableChange C _) = _
    rw [projectiveCoordinate, projectiveGradedVariableChange_mk, evalZeroSectionAux_mk]
    simp
  have hR' : ∀ r, ((C • W).evalZeroSectionAux.comp (W.projectiveGradedVariableChange C :
      W.HomogeneousCoordinateRing →+* _)) (algebraMap R _ r) = r := fun r => by
    rw [RingHom.comp_apply]
    change (C • W).evalZeroSectionAux (W.projectiveGradedVariableChange C _) = _
    rw [projectiveGradedVariableChange_algebraMap, hR]
  rw [← (C • W).specMap_awayLiftAux_eq_zeroSection _ h0 h2 hu' hR]
  have hmem : W.projectiveGradedVariableChange C (W.projectiveCoordinate 1) ∈
      (C • W).projectiveGrading 1 :=
    (W.projectiveGradedVariableChange C).map_mem (W.projectiveCoordinate_mem 1)
  rw [specMap_awayLiftAux_awayι _ _ _ hmem _ Nat.one_pos hu' hu]
  rw [projectiveSchemeVariableChangeIso_hom, Category.assoc, Proj.awayι_comp_map,
    ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    awayLiftAux_comp_awayMap' _ _ _ (W.projectiveCoordinate_mem 1) hu]
  exact W.specMap_awayLiftAux_eq_zeroSection _ h0' h2' hu hR'

/-- **The variable change isomorphism lies over `Spec R`.** Let `W` be a Weierstrass curve over
a commutative ring `R` and `C` a variable change. The composite of
`projectiveSchemeVariableChangeIso W C : Proj S_{C • W} ≅ Proj S_W` with the structure morphism
`Proj S_W → Spec R` is the structure morphism `Proj S_{C • W} → Spec R`. -/
theorem projectiveSchemeVariableChangeIso_hom_projectiveSchemeToSpec (C : VariableChange R) :
    (W.projectiveSchemeVariableChangeIso C).hom ≫ W.projectiveSchemeToSpec =
      (C • W).projectiveSchemeToSpec := by
  refine (Proj.mapAffineOpenCover _
    (W.irrelevant_le_map_projectiveGradedVariableChange C)).openCover.hom_ext _ _ fun s => ?_
  obtain ⟨i, x, hx⟩ := s
  have hfx : W.projectiveGradedVariableChange C x ∈ (C • W).projectiveGrading i :=
    (W.projectiveGradedVariableChange C).map_mem hx
  have key : Proj.awayι (C • W).projectiveGrading _ hfx i.pos ≫
      Proj.map (W.projectiveGradedVariableChange C)
        (W.irrelevant_le_map_projectiveGradedVariableChange C) ≫ W.projectiveSchemeToSpec =
      Proj.awayι (C • W).projectiveGrading _ hfx i.pos ≫ (C • W).projectiveSchemeToSpec := by
    rw [Proj.awayι_comp_map_assoc _ _ _ _ hx, projectiveSchemeToSpec, projectiveSchemeToSpec,
      Proj.awayι_toSpecZero_assoc, Proj.awayι_toSpecZero_assoc,
      ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [fromZeroRingHom_eq_mk _ hx, fromZeroRingHom_eq_mk _ hfx, Away.map_mk]
    simp only [Away.val_mk, SetLike.GradeZero.coe_algebraMap,
      projectiveGradedVariableChange_algebraMap]
  exact key

/-- **The affine Weierstrass polynomial after a variable change, over a commutative ring.** Let
`W` be a Weierstrass curve over a commutative ring `R` and `C = (u, r, s, t)` a variable change.
In the affine coordinate ring `A_{C • W}`, with coordinates `x', y'`, the Weierstrass polynomial
of `W` vanishes at `(u² x' + r, u³ y' + u² s x' + t)`. -/
theorem affineVariableChange_eval (C : VariableChange R) :
    Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap R (C • W).toAffine.CoordinateRing)
        (algebraMap R _ ((C.u : R) ^ 2) * (C • W).affineX + algebraMap R _ C.r))
      (algebraMap R _ ((C.u : R) ^ 3) * (C • W).affineY +
        algebraMap R _ ((C.u : R) ^ 2 * C.s) * (C • W).affineX + algebraMap R _ C.t)
      W.toAffine.polynomial = 0 := by
  set A := algebraMap R (C • W).toAffine.CoordinateRing
  have h₁ := congrArg A (u_mul_a₁ W C)
  have h₂ := congrArg A (u_mul_a₂ W C)
  have h₃ := congrArg A (u_mul_a₃ W C)
  have h₄ := congrArg A (u_mul_a₄ W C)
  have h₆ := congrArg A (u_mul_a₆ W C)
  simp only [map_mul, map_add, map_sub, map_pow, map_ofNat] at h₁ h₂ h₃ h₄ h₆
  have hrel := (C • W).relation_affine
  simp only [Affine.polynomial, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.coe_eval₂RingHom,
    map_mul, map_pow, map_add, toAffine]
  linear_combination A (C.u : R) ^ 6 * hrel +
    (-(A (C.u : R) ^ 5) * (C • W).affineX * (C • W).affineY) * h₁ +
    (A (C.u : R) ^ 4 * (C • W).affineX ^ 2) * h₂ + (-(A (C.u : R) ^ 3) * (C • W).affineY) * h₃ +
    (A (C.u : R) ^ 2 * (C • W).affineX) * h₄ + h₆

/-- **The affine variable change.** Let `W` be a Weierstrass curve over a commutative ring `R`
and `C = (u, r, s, t)` a variable change. This is the ring map `A_W → A_{C • W}` of affine
coordinate rings sending `x` to `u² x' + r` and `y` to `u³ y' + u² s x' + t` (and the identity on
`R`), obtained by `AdjoinRoot.lift` from `WeierstrassCurve.affineVariableChange_eval`. -/
noncomputable def affineVariableChange (C : VariableChange R) :
    W.toAffine.CoordinateRing →+* (C • W).toAffine.CoordinateRing :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (algebraMap R (C • W).toAffine.CoordinateRing)
      (algebraMap R _ ((C.u : R) ^ 2) * (C • W).affineX + algebraMap R _ C.r))
    (algebraMap R _ ((C.u : R) ^ 3) * (C • W).affineY +
      algebraMap R _ ((C.u : R) ^ 2 * C.s) * (C • W).affineX + algebraMap R _ C.t)
    (W.affineVariableChange_eval C)

/-- The affine variable change sends `x` to `u² x' + r`. -/
theorem affineVariableChange_affineX (C : VariableChange R) :
    W.affineVariableChange C W.affineX =
      algebraMap R _ ((C.u : R) ^ 2) * (C • W).affineX + algebraMap R _ C.r := by
  simp [affineVariableChange, affineX]

/-- The affine variable change sends `y` to `u³ y' + u² s x' + t`. -/
theorem affineVariableChange_affineY (C : VariableChange R) :
    W.affineVariableChange C W.affineY =
      algebraMap R _ ((C.u : R) ^ 3) * (C • W).affineY +
        algebraMap R _ ((C.u : R) ^ 2 * C.s) * (C • W).affineX + algebraMap R _ C.t := by
  simp [affineVariableChange, affineY]

/-- The affine variable change is the identity on `R`. -/
theorem affineVariableChange_algebraMap (C : VariableChange R) (r : R) :
    W.affineVariableChange C (algebraMap R _ r) = algebraMap R _ r := by
  rw [show algebraMap R W.toAffine.CoordinateRing r =
    AdjoinRoot.of W.toAffine.polynomial (Polynomial.C r) from rfl]
  simp [affineVariableChange]

/-- **The variable change isomorphism on the affine charts.** Let `W` be a Weierstrass curve
over a commutative ring `R` and `C = (u, r, s, t)` a variable change. The composite of the affine
chart `Spec A_{C • W} → Proj S_{C • W}` (image `D₊(Z)`) with
`projectiveSchemeVariableChangeIso W C` is `Spec` of the affine variable change
`A_W → A_{C • W}`, `x ↦ u² x' + r`, `y ↦ u³ y' + u² s x' + t`, followed by the affine chart
`Spec A_W → Proj S_W`.

Source: J. S. Milne, *Elliptic Curves*, 2nd ed., author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter II, Theorem 2.4(b), p. 52. -/
theorem affineChart_comp_projectiveSchemeVariableChangeIso_hom (C : VariableChange R) :
    (C • W).affineChart ≫ (W.projectiveSchemeVariableChangeIso C).hom =
      Spec.map (CommRingCat.ofHom (W.affineVariableChange C)) ≫ W.affineChart := by
  have hZ : IsUnit (W.dehomogenizeZ (W.projectiveCoordinate 2)) := by
    rw [dehomogenizeZ_coordinate_two]; exact isUnit_one
  have hZ' : IsUnit ((C • W).dehomogenizeZ ((C • W).projectiveCoordinate 2)) := by
    rw [dehomogenizeZ_coordinate_two]; exact isUnit_one
  have hfZ : IsUnit ((C • W).dehomogenizeZ
      (W.projectiveGradedVariableChange C (W.projectiveCoordinate 2))) := by
    rw [projectiveCoordinate, projectiveGradedVariableChange_mk, dehomogenizeZ_mk]
    simp
  have hmem : W.projectiveGradedVariableChange C (W.projectiveCoordinate 2) ∈
      (C • W).projectiveGrading 1 :=
    (W.projectiveGradedVariableChange C).map_mem (W.projectiveCoordinate_mem 2)
  have e : W.awayZToAffine = awayLiftAux W.projectiveGrading W.dehomogenizeZ _ hZ := rfl
  have e' : (C • W).awayZToAffine =
      awayLiftAux (C • W).projectiveGrading (C • W).dehomogenizeZ _ hZ' := rfl
  have hρ : (C • W).dehomogenizeZ.comp (W.projectiveGradedVariableChange C :
      W.HomogeneousCoordinateRing →+* _) = (W.affineVariableChange C).comp W.dehomogenizeZ := by
    refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_))
    · change (C • W).dehomogenizeZ (W.projectiveGradedVariableChange C
        (Ideal.Quotient.mk _ (MvPolynomial.C r))) =
          W.affineVariableChange C (W.dehomogenizeZ (Ideal.Quotient.mk _ (MvPolynomial.C r)))
      rw [projectiveGradedVariableChange_mk, dehomogenizeZ_mk, dehomogenizeZ_mk]
      simp [affineVariableChange_algebraMap]
    · change (C • W).dehomogenizeZ (W.projectiveGradedVariableChange C
        (Ideal.Quotient.mk _ (X i))) =
          W.affineVariableChange C (W.dehomogenizeZ (Ideal.Quotient.mk _ (X i)))
      rw [projectiveGradedVariableChange_mk, dehomogenizeZ_mk, dehomogenizeZ_mk]
      fin_cases i
      · simp [affineVariableChange_affineX]
      · simp [affineVariableChange_affineY]
      · simp
  rw [affineChart, affineChart]
  rw [e, e']
  rw [specMap_awayLiftAux_awayι _ _ _ hmem one_pos one_pos hZ' hfZ]
  rw [projectiveSchemeVariableChangeIso_hom, Category.assoc,
    Proj.awayι_comp_map _ _ _ _ (W.projectiveCoordinate_mem 2),
    ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [awayLiftAux_comp_awayMap' _ _ _ (W.projectiveCoordinate_mem 2) hfZ, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    comp_awayLiftAux _ _ _ (W.projectiveCoordinate_mem 2) hZ]
  rw [awayLiftAux_congr _ hρ (W.projectiveCoordinate 2) hfZ (hZ.map (W.affineVariableChange C))]

end WeierstrassCurve
