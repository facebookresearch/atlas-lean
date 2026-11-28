/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.WeierstrassModel
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Tests for integral Weierstrass models

Well-typedness and field projections of planar and abstract integral Weierstrass models over the
`p`-adic integers, for the curve `y² + y = x³ - x` over `ℚ_[p]` (discriminant `37`), and the
categories of models.
-/

@[expose] public section

namespace WeierstrassCurve.WeierstrassModelTest

open AlgebraicGeometry CategoryTheory Limits

variable (p : ℕ) [Fact p.Prime]

/-- The integral Weierstrass equation `y² + y = x³ - x` over `ℤ_[p]`. -/
noncomputable abbrev W : WeierstrassCurve ℤ_[p] := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := -1, a₆ := 0 }

/-- The curve `y² + y = x³ - x` over `ℚ_[p]`. -/
noncomputable abbrev E : WeierstrassCurve ℚ_[p] := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := -1, a₆ := 0 }

/-- Its discriminant is `37`. -/
theorem E_Δ : (E p).Δ = 37 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  norm_num

instance : (E p).IsElliptic := ⟨by rw [E_Δ, isUnit_iff_ne_zero]; norm_num⟩

/-- The generic fibre equation of `W` is `E`. -/
example : (W p).baseChange ℚ_[p] = E p := by
  ext <;> simp [WeierstrassCurve.baseChange, WeierstrassCurve.map]

/-- The base change of the zero section of `W` is a section of the generic fibre. -/
example : baseChangeSection (W p).projectiveSchemeToSpec (W p).zeroSection
    (W p).zeroSection_projectiveSchemeToSpec (Spec.map (CommRingCat.ofHom (algebraMap ℤ_[p] ℚ_[p])))
      ≫ pullback.snd _ _ = 𝟙 _ := by
  simp

/-- A planar model of `E` with equation `W` is built from a `ℚ_[p]`-isomorphism `W_K ≅ E`
carrying `[0 : 1 : 0]` to the identity. -/
noncomputable example
    (i : pullback (W p).projectiveSchemeToSpec
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ_[p] ℚ_[p]))) ≅ (E p).ProjectiveScheme)
    (h₁ : i.hom ≫ (E p).projectiveSchemeToSpec = pullback.snd _ _)
    (h₂ : baseChangeSection (W p).projectiveSchemeToSpec (W p).zeroSection
      (W p).zeroSection_projectiveSchemeToSpec
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ_[p] ℚ_[p]))) ≫ i.hom = (E p).zeroSection) :
    (E p).PlanarWeierstrassModel ℤ_[p] :=
  ⟨W p, i, h₁, h₂⟩

section Planar

variable {p} (M M' : (E p).PlanarWeierstrassModel ℤ_[p])

example : M.i.hom ≫ (E p).projectiveSchemeToSpec = pullback.snd _ _ :=
  M.i_hom_projectiveSchemeToSpec

example (φ : M ⟶ M') : φ.hom ≫ M'.W.projectiveSchemeToSpec = M.W.projectiveSchemeToSpec :=
  φ.hom_projectiveSchemeToSpec

example : (𝟙 M : M ⟶ M).hom = 𝟙 M.W.ProjectiveScheme := rfl

example (φ : M ⟶ M') : 𝟙 M ≫ φ = φ := Category.id_comp φ

end Planar

section Abstract

variable {p} (M M' M'' : (E p).WeierstrassModel ℤ_[p])

example : IsProper M.f := inferInstance

example : Flat M.f := inferInstance

example : LocallyOfFinitePresentation M.f := inferInstance

example (x : M.𝒲) : IsIntegrallyClosed (M.𝒲.presheaf.stalk x) := (M.normal x).2

example : M.ε ≫ M.f = 𝟙 _ := M.ε_f

example : baseChangeSection M.f M.ε M.ε_f
    (Spec.map (CommRingCat.ofHom (algebraMap ℤ_[p] ℚ_[p]))) ≫ M.i.hom = (E p).zeroSection :=
  M.ε_i_hom

example : topologicalKrullDim (pullback M.f
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ℤ_[p]))) : Scheme) = 1 :=
  M.topologicalKrullDim_specialFibre

example : GeometricallyIrreducible
    (pullback.snd M.f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ℤ_[p])))) :=
  M.geometricallyIrreducible_specialFibre

noncomputable example : M.𝒲.Opens := M.smoothLocus

example (φ : M ⟶ M') (ψ : M' ⟶ M'') : (φ ≫ ψ).hom = φ.hom ≫ ψ.hom := rfl

example (φ : M ⟶ M') : φ ≫ 𝟙 M' = φ := Category.comp_id φ

end Abstract

#check @baseChangeSection
#check @baseChangeSection_fst
#check @baseChangeSection_snd
#check @baseChangeMap
#check @baseChangeMap_fst
#check @baseChangeMap_snd
#check @baseChangeMap_id
#check @baseChangeMap_comp
#check @WeierstrassCurve.PlanarWeierstrassModel
#check @WeierstrassCurve.PlanarWeierstrassModel.Hom
#check @WeierstrassCurve.PlanarWeierstrassModel.id_hom
#check @WeierstrassCurve.PlanarWeierstrassModel.comp_hom
#check @WeierstrassCurve.WeierstrassModel
#check @WeierstrassCurve.WeierstrassModel.smoothLocus
#check @WeierstrassCurve.WeierstrassModel.Hom
#check @WeierstrassCurve.WeierstrassModel.id_hom
#check @WeierstrassCurve.WeierstrassModel.comp_hom

end WeierstrassCurve.WeierstrassModelTest
