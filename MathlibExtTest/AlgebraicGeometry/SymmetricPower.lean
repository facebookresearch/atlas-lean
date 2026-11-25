/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.SymmetricPower

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicCurve

/-- Unfolding: the permutation action fixes the quotient morphism, and the
quotient morphism is finite and surjective. -/
example {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) (r : ℕ)
    (P : SymmetricPowerPackage c r) (σ : Equiv.Perm (Fin r)) :
    (finFibrePow.permAct c r σ).asIso.hom ≫ P.π = P.π ∧ IsFinite P.π ∧ Surjective P.π ∧
      IsProper P.csym ∧ SmoothOfRelativeDimension r P.csym :=
  ⟨P.permAct_comp_π σ, P.isFinite_π, P.surjective_π, P.proper, P.smooth⟩

/-- Characterization: two points of the fibre power have the same image in
the symmetric power exactly when a permutation of the factors takes one
to the other. -/
example {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) (r : ℕ)
    (P : SymmetricPowerPackage c r) (x x' : ↥(finFibrePow c r)) :
    P.π.base x = P.π.base x' ↔
      ∃ σ : Equiv.Perm (Fin r), (finFibrePow.permAct c r σ).asIso.hom.base x = x' :=
  P.π_apply_eq_iff x x'

/-- The permutation action is a group action by automorphisms: the product
of two permutations acts as the composite of the two automorphisms. -/
example {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) (r : ℕ)
    (σ τ : Equiv.Perm (Fin r)) :
    finFibrePow.permAct c r (σ * τ) =
      finFibrePow.permAct c r σ * finFibrePow.permAct c r τ :=
  map_mul _ _ _

/-- The zeroth fibre power of `Spec k` over itself is `Spec k` itself. -/
noncomputable def fibrePowZeroIso (k : Type u) [Field k] :
    finFibrePow (𝟙 (Spec (CommRingCat.of k))) 0 ≅ Spec (CommRingCat.of k) where
  hom := finFibrePow.toBase _ _
  inv := WidePullback.lift (𝟙 _) (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
  hom_inv_id := by
    apply WidePullback.hom_ext
    · intro j
      exact Fin.elim0 j
    · simp [finFibrePow.toBase]
  inv_hom_id := by
    simp [finFibrePow.toBase]

/-- Congruence for `Scheme.Hom.appLE` in the morphism argument.  Rewriting
the morphism directly in a goal whose `appLE` proof term mentions it fails
with "motive is not type correct"; rewriting the whole `appLE` term with
this lemma avoids that. -/
private lemma appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h; rfl

/-- Nontrivial instance: the zeroth symmetric power of `Spec k` over itself,
with the identity as quotient morphism. Every field of the package is
instantiated. -/
noncomputable def symPowZeroOfSpec (k : Type u) [Field k] :
    SymmetricPowerPackage (𝟙 (Spec (CommRingCat.of k))) 0 where
  Csym := finFibrePow (𝟙 (Spec (CommRingCat.of k))) 0
  csym := finFibrePow.toBase (𝟙 (Spec (CommRingCat.of k))) 0
  π := 𝟙 _
  π_comp_csym := Category.id_comp _
  permAct_comp_π := by
    intro σ
    have hσ : σ = 1 := Subsingleton.elim σ 1
    rw [hσ, map_one]
    rfl
  isFinite_π := by infer_instance
  surjective_π := by infer_instance
  π_apply_eq_iff := by
    intro x x'
    constructor
    · intro h
      refine ⟨1, ?_⟩
      simpa using h
    · rintro ⟨σ, hσ⟩
      have hσ1 : σ = 1 := Subsingleton.elim σ 1
      subst hσ1
      simpa using hσ
  app_injective := by
    intro V
    exact Function.injective_id
  range_app := by
    intro V
    ext s
    simp only [Set.mem_range]
    constructor
    · rintro ⟨s, rfl⟩
      intro σ
      have hσ : σ = 1 := Subsingleton.elim σ 1
      subst hσ
      have h1 : (finFibrePow.permAct (𝟙 (Spec (CommRingCat.of k))) 0
          (1 : Equiv.Perm (Fin 0))).asIso.hom = 𝟙 _ := by
        rw [map_one]; rfl
      rw [appLE_congr_hom h1]
      have happ : ∀ e : ((𝟙 (finFibrePow (𝟙 (Spec (CommRingCat.of k))) 0)) ⁻¹ᵁ V) ≤
          (𝟙 (finFibrePow (𝟙 (Spec (CommRingCat.of k))) 0)) ⁻¹ᵁ
            ((𝟙 (finFibrePow (𝟙 (Spec (CommRingCat.of k))) 0)) ⁻¹ᵁ V),
          Scheme.Hom.appLE (𝟙 (finFibrePow (𝟙 (Spec (CommRingCat.of k))) 0))
            ((𝟙 (finFibrePow (𝟙 (Spec (CommRingCat.of k))) 0)) ⁻¹ᵁ V)
            ((𝟙 (finFibrePow (𝟙 (Spec (CommRingCat.of k))) 0)) ⁻¹ᵁ V) e
            = 𝟙 Γ(finFibrePow (𝟙 (Spec (CommRingCat.of k))) 0,
                (𝟙 (finFibrePow (𝟙 (Spec (CommRingCat.of k))) 0)) ⁻¹ᵁ V) := by
        intro e
        ext t
        rw [Scheme.Hom.appLE]
        change (CommRingCat.Hom.hom
          ((finFibrePow (𝟙 (Spec (CommRingCat.of k))) 0).presheaf.map
            (homOfLE e).op)) t = t
        have h1e : (homOfLE e).op = eqToHom (congrArg Opposite.op
            (Scheme.Hom.id_preimage
              ((𝟙 (finFibrePow (𝟙 (Spec (CommRingCat.of k))) 0)) ⁻¹ᵁ V))) :=
          Subsingleton.elim _ _
        rw [h1e, CategoryTheory.eqToHom_map]
        rfl
      rw [happ]
      apply ConcreteCategory.id_apply
    · intro _
      exact ⟨s, rfl⟩
  exists_affine_chart := by
    intro U _hU
    refine ⟨⊤, ?_, ?_⟩
    · haveI : IsIso (fibrePowZeroIso k).hom := (fibrePowZeroIso k).isIso_hom
      haveI : IsAffine (finFibrePow (𝟙 (Spec (CommRingCat.of k))) 0) :=
        IsAffine.of_isIso (fibrePowZeroIso k).hom
      exact isAffineOpen_top _
    · simp
  integral := by
    haveI : IsIso (fibrePowZeroIso k).inv := (fibrePowZeroIso k).isIso_inv
    exact IsIntegral.of_isIso (fibrePowZeroIso k).inv
  proper := by
    haveI : IsIso (finFibrePow.toBase (𝟙 (Spec (CommRingCat.of k))) 0) :=
      (fibrePowZeroIso k).isIso_hom
    infer_instance
  smooth := by
    haveI : IsIso (finFibrePow.toBase (𝟙 (Spec (CommRingCat.of k))) 0) :=
      (fibrePowZeroIso k).isIso_hom
    haveI : IsOpenImmersion (finFibrePow.toBase (𝟙 (Spec (CommRingCat.of k))) 0) :=
      MorphismProperty.of_isIso @IsOpenImmersion _
    infer_instance

end AlgebraicCurve
