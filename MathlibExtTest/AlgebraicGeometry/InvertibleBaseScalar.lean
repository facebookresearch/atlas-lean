/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.InvertibleBaseScalar

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules (existsUnique_isBaseScalar_of_isLineBundle_of_bijective)
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.SchemeModuleLinear (baseScalar)

universe u v

/-- The source's `baseSection`, restated (with `SourceIsBaseScalar` below) only to check that the
theorem gives the source's statement: the image of `c : R` in `Γ(X, U)` along `f`. -/
private noncomputable def sourceBaseSection {X : Scheme.{u}} {R : Type u} [CommRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) (c : R) (U : X.Opens) : Γ(X, U) :=
  X.presheaf.map (homOfLE (le_top (a := U))).op
    (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c))

/-- The source's `IsBaseScalar`: `σ` multiplies every section by `sourceBaseSection f c`. -/
private def SourceIsBaseScalar {X : Scheme.{u}} {R : Type u} [CommRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) {M : X.Modules} (σ : M ⟶ M) (c : R) : Prop :=
  ∀ (U : X.Opens) (s : Γ(M, U)), σ.app U s = sourceBaseSection f c U • s

/-- The source's predicate is the action of `baseScalar R (Over.mk f) c`. -/
private theorem sourceIsBaseScalar_iff {X : Scheme.{u}} {R : Type u} [CommRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) {M : X.Modules} (σ : M ⟶ M) (c : R) :
    SourceIsBaseScalar f σ c ↔ (baseScalar R (Over.mk f) c).asHom.app M = σ := by
  constructor
  · intro h
    ext U x
    exact (h U.unop x).symm
  · rintro rfl U s
    rfl

/-- The source's statement, with its binders and definitions and the invertibility hypothesis
stated as `CoherentCurveLinearSeries.IsLineBundle`, follows from the theorem. -/
private theorem exactSource
    {X : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    (hH0 : Function.Bijective fun c : R =>
      f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c))
    {M : X.Modules} (hM : IsLineBundle M) (σ : M ⟶ M) :
    ∃! c : R, SourceIsBaseScalar f σ c :=
  (existsUnique_congr fun c => sourceIsBaseScalar_iff f σ c).2
    (existsUnique_isBaseScalar_of_isLineBundle_of_bijective f hH0 hM σ)

/-- The same statement one universe higher. -/
private theorem exactSourceHigher
    {X : Scheme.{v}} {R : Type v} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    (hH0 : Function.Bijective fun c : R =>
      f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c))
    {M : X.Modules} (hM : IsLineBundle M) (σ : M ⟶ M) :
    ∃! c : R, SourceIsBaseScalar f σ c :=
  (existsUnique_congr fun c => sourceIsBaseScalar_iff f σ c).2
    (existsUnique_isBaseScalar_of_isLineBundle_of_bijective f hH0 hM σ)

-- Every endomorphism of a line bundle is multiplication by a unique global section.
example {X : Scheme.{u}} {M : X.Modules} (hM : IsLineBundle M) (g : M ⟶ M) :
    ∃! s : Γ(X, ⊤), ∀ (U : X.Opens) (x : Γ(M, U)),
      g.app U x = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s • x :=
  hM.existsUnique_app_eq_smul g

/-- A concrete instance: over `Spec ℤ` itself, where the map from `ℤ` to the global sections is
bijective, twice the identity of the structure sheaf is the action of the base scalar `2`, and by
the theorem of no other integer. -/
example (c : ℤ) :
    (baseScalar ℤ (Over.mk (𝟙 (Spec (.of ℤ)))) c).asHom.app (structureModule (Spec (.of ℤ))) =
      𝟙 (structureModule (Spec (.of ℤ))) + 𝟙 _ ↔ c = 2 := by
  have hbij : Function.Bijective fun c : ℤ =>
      Scheme.Hom.appTop (𝟙 (Spec (.of ℤ))) ((Scheme.ΓSpecIso (.of ℤ)).inv c) := by
    rw [Scheme.Hom.id_appTop]
    exact ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv
  have h2 : (baseScalar ℤ (Over.mk (𝟙 (Spec (.of ℤ)))) 2).asHom.app
      (structureModule (Spec (.of ℤ))) = 𝟙 (structureModule (Spec (.of ℤ))) + 𝟙 _ :=
    (sourceIsBaseScalar_iff _ _ _).1 fun U s => by
      simp only [sourceBaseSection]
      rw [map_ofNat, map_ofNat, map_ofNat, two_smul]
      rfl
  obtain ⟨_, -, huniq⟩ := existsUnique_isBaseScalar_of_isLineBundle_of_bijective _ hbij
    (isLineBundle_structureModule _) (𝟙 (structureModule (Spec (.of ℤ))) + 𝟙 _)
  exact ⟨fun hc => (huniq c hc).trans (huniq 2 h2).symm, fun hc => hc ▸ h2⟩

/-- Boundary: the injectivity half of the bijectivity hypothesis cannot be
dropped. The cast `ℤ → ZMod 2` is surjective but not injective. Along the
induced `Spec (ZMod 2) ⟶ Spec ℤ`, the structure sheaf is a line bundle, and its
identity is the action of both base scalars `1` and `3`, so the base scalar
is not unique. -/
example :
    let f : Spec (.of (ZMod 2)) ⟶ Spec (.of ℤ) :=
      Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod 2)))
    (Function.Surjective fun c : ℤ => f.appTop ((Scheme.ΓSpecIso (.of ℤ)).inv c)) ∧
      IsLineBundle (structureModule (Spec (.of (ZMod 2)))) ∧
      ¬ ∃! c : ℤ, (baseScalar ℤ (Over.mk f) c).asHom.app
        (structureModule (Spec (.of (ZMod 2)))) = 𝟙 (structureModule (Spec (.of (ZMod 2)))) := by
  intro f
  have key (c : ℤ) : f.appTop ((Scheme.ΓSpecIso (.of ℤ)).inv c) =
      (Scheme.ΓSpecIso (.of (ZMod 2))).inv (c : ZMod 2) := by
    simp [f]
  refine ⟨fun s => ?_, isLineBundle_structureModule _, ?_⟩
  · obtain ⟨c, hc⟩ := ZMod.intCast_surjective (n := 2) ((Scheme.ΓSpecIso (.of (ZMod 2))).hom s)
    exact ⟨c, by simp only [key, hc, Iso.hom_inv_id_apply]⟩
  · rintro ⟨c, -, huniq⟩
    have h1 : SourceIsBaseScalar f (𝟙 (structureModule _)) 1 := fun U s => by
      simp [sourceBaseSection]
    have h31 : f.appTop ((Scheme.ΓSpecIso (.of ℤ)).inv 3) =
        f.appTop ((Scheme.ΓSpecIso (.of ℤ)).inv 1) := by
      rw [key, key, show ((3 : ℤ) : ZMod 2) = ((1 : ℤ) : ZMod 2) by decide]
    have h3 : SourceIsBaseScalar f (𝟙 (structureModule _)) 3 := fun U s => by
      have hb : sourceBaseSection f 3 U = sourceBaseSection f 1 U := by
        unfold sourceBaseSection
        rw [h31]
      rw [hb]
      exact h1 U s
    have h13 : (3 : ℤ) = 1 := (huniq 3 ((sourceIsBaseScalar_iff _ _ _).1 h3)).trans
      (huniq 1 ((sourceIsBaseScalar_iff _ _ _).1 h1)).symm
    omega
