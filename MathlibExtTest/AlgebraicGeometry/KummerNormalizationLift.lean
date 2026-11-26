/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.KummerNormalizationLift

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

universe u v

-- Consumer with the original binders.
example {X : Scheme.{u}} [IsIntegral X]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (k : ℕ) (g : X.functionField)
    (V : X.Opens) (hV : IsAffineOpen V) (hVne : Nonempty V)
    (hk : IsUnit ((k : ℕ) : Γ(X, V)))
    (u : Γ(X, V)) (hu : IsUnit u) (h : X.functionField) (hh : h ≠ 0)
    (hval : ∀ (x : X) (hx : x ∈ V),
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ V x hx u) =
        g / h ^ k) :
    let A' := AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)
    let f₀ := Spec.map (CommRingCat.ofHom (algebraMap X.functionField A')) ≫
      X.fromSpecStalk (genericPoint X)
    let π := f₀.fromNormalization
    let Y := f₀.normalization
    ∀ T : Γ(Y, π ⁻¹ᵁ V),
      f₀.toNormalization.app (π ⁻¹ᵁ V) T =
        (Spec (CommRingCat.of A')).presheaf.map (homOfLE le_top).op
          ((Scheme.ΓSpecIso (CommRingCat.of A')).inv
            (algebraMap X.functionField A' h⁻¹ * AdjoinRoot.root _)) →
      ∀ (Z : Scheme.{u}) (z : Z ⟶ X), z ⁻¹ᵁ V = ⊤ →
        ∀ τ : Γ(Z, ⊤), Z.presheaf.map (homOfLE le_top).op τ ^ k = z.app V u →
          ∃! s : Z ⟶ Y, s ≫ π = z ∧
            s.app (π ⁻¹ᵁ V) T = Z.presheaf.map (homOfLE le_top).op τ :=
  AlgebraicGeometry.existsUnique_lift_fromNormalization_kummer_of_isAffineOpen hnorm k g V hV
    hVne hk u hu h hh hval

-- Higher-universe consumer.
example {X : Scheme.{v}} [IsIntegral X]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (k : ℕ) (g : X.functionField)
    (V : X.Opens) (hV : IsAffineOpen V) (hVne : Nonempty V)
    (hk : IsUnit ((k : ℕ) : Γ(X, V)))
    (u : Γ(X, V)) (hu : IsUnit u) (h : X.functionField) (hh : h ≠ 0)
    (hval : ∀ (x : X) (hx : x ∈ V),
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ V x hx u) =
        g / h ^ k) :
    let A' := AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)
    let f₀ := Spec.map (CommRingCat.ofHom (algebraMap X.functionField A')) ≫
      X.fromSpecStalk (genericPoint X)
    let π := f₀.fromNormalization
    let Y := f₀.normalization
    ∀ T : Γ(Y, π ⁻¹ᵁ V),
      f₀.toNormalization.app (π ⁻¹ᵁ V) T =
        (Spec (CommRingCat.of A')).presheaf.map (homOfLE le_top).op
          ((Scheme.ΓSpecIso (CommRingCat.of A')).inv
            (algebraMap X.functionField A' h⁻¹ * AdjoinRoot.root _)) →
      ∀ (Z : Scheme.{v}) (z : Z ⟶ X), z ⁻¹ᵁ V = ⊤ →
        ∀ τ : Γ(Z, ⊤), Z.presheaf.map (homOfLE le_top).op τ ^ k = z.app V u →
          ∃! s : Z ⟶ Y, s ≫ π = z ∧
            s.app (π ⁻¹ᵁ V) T = Z.presheaf.map (homOfLE le_top).op τ :=
  AlgebraicGeometry.existsUnique_lift_fromNormalization_kummer_of_isAffineOpen hnorm k g V hV
    hVne hk u hu h hh hval
