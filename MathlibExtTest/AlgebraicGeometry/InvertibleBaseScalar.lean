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
  AlgebraicGeometry.DescentCharacter
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

universe u v

/-- Consumer with the original binders, the invertibility hypothesis stated as
`CoherentCurveLinearSeries.IsLineBundle`. -/
private theorem exactSource
    {X : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    (hH0 : Function.Bijective fun c : R =>
      f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c))
    {M : X.Modules} (hM : IsLineBundle M) (σ : M ⟶ M) :
    ∃! c : R, IsBaseScalar f σ c :=
  existsUnique_isBaseScalar_of_isLineBundle_of_bijective f hH0 hM σ

/-- The same statement one universe higher. -/
private theorem exactSourceHigher
    {X : Scheme.{v}} {R : Type v} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    (hH0 : Function.Bijective fun c : R =>
      f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c))
    {M : X.Modules} (hM : IsLineBundle M) (σ : M ⟶ M) :
    ∃! c : R, IsBaseScalar f σ c :=
  existsUnique_isBaseScalar_of_isLineBundle_of_bijective f hH0 hM σ

-- Every endomorphism of a line bundle is multiplication by a unique global section.
example {X : Scheme.{u}} {M : X.Modules} (hM : IsLineBundle M) (g : M ⟶ M) :
    ∃! s : Γ(X, ⊤), ∀ (U : X.Opens) (x : Γ(M, U)),
      g.app U x = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s • x :=
  hM.existsUnique_app_eq_smul g

/-- Boundary: the injectivity half of the bijectivity hypothesis cannot be
dropped. The cast `ℤ → ZMod 2` is surjective but not injective. Along the
induced `Spec (ZMod 2) ⟶ Spec ℤ`, the structure sheaf is a line bundle, and its
identity is multiplication by both base scalars `1` and `3`, so the base scalar
is not unique. -/
example :
    let f : Spec (.of (ZMod 2)) ⟶ Spec (.of ℤ) :=
      Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod 2)))
    (Function.Surjective fun c : ℤ => f.appTop ((Scheme.ΓSpecIso (.of ℤ)).inv c)) ∧
      IsLineBundle (structureModule (Spec (.of (ZMod 2)))) ∧
      ¬ ∃! c : ℤ, IsBaseScalar f (𝟙 (structureModule _)) c := by
  intro f
  have key (c : ℤ) : f.appTop ((Scheme.ΓSpecIso (.of ℤ)).inv c) =
      (Scheme.ΓSpecIso (.of (ZMod 2))).inv (c : ZMod 2) := by
    simp [f]
  refine ⟨fun s => ?_, isLineBundle_structureModule _, ?_⟩
  · obtain ⟨c, hc⟩ := ZMod.intCast_surjective (n := 2) ((Scheme.ΓSpecIso (.of (ZMod 2))).hom s)
    exact ⟨c, by simp only [key, hc, Iso.hom_inv_id_apply]⟩
  · rintro ⟨c, -, huniq⟩
    have h1 : IsBaseScalar f (𝟙 (structureModule _)) 1 := fun U s => by
      simp [baseSection]
    have h31 : f.appTop ((Scheme.ΓSpecIso (.of ℤ)).inv 3) =
        f.appTop ((Scheme.ΓSpecIso (.of ℤ)).inv 1) := by
      rw [key, key, show ((3 : ℤ) : ZMod 2) = ((1 : ℤ) : ZMod 2) by decide]
    have h3 : IsBaseScalar f (𝟙 (structureModule _)) 3 := fun U s => by
      have hb : baseSection f 3 U = baseSection f 1 U := by
        unfold baseSection
        rw [h31]
      rw [hb]
      exact h1 U s
    have h13 : (3 : ℤ) = 1 := (huniq 3 h3).trans (huniq 1 h1).symm
    omega
