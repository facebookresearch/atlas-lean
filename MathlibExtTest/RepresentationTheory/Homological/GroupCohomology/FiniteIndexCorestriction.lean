/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.FiniteIndexCorestriction

@[expose] public section

open CategoryTheory groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]

-- The unit followed by the norm is multiplication by the index.
example (H : Subgroup G) [H.FiniteIndex] [DecidableRel (QuotientGroup.rightRel H)]
    (A : Rep.{u} k G) :
    (Rep.resCoindAdjunction k H.subtype).unit.app A ≫ (Rep.coindResAdjunction k H).counit.app A =
      H.index • 𝟙 A :=
  Rep.resCoindUnit_comp_coindResCounit H A

-- Restriction through Shapiro's lemma, for any subgroup.
example (H : Subgroup G) (A : Rep.{u} k G) (n : ℕ) :
    map H.subtype (𝟙 (Rep.res H.subtype A)) n =
      map (MonoidHom.id G) ((Rep.resCoindAdjunction k H.subtype).unit.app A) n ≫
        (coindIso (Rep.res H.subtype A) n).hom :=
  map_subtype_eq_map_unit_comp_coindIso A n

-- Shapiro's isomorphism on cochains: `x ↦ (h ↦ x(h)(1))`.
example (H : Subgroup G) (B : Rep.{u} k H) (n : ℕ) (x : (Fin n → G) → Rep.coind H.subtype B)
    (h : Fin n → H) :
    ((coindCochainsMap B).f n).hom x h = (x (H.subtype ∘ h)).1 1 :=
  coindCochainsMap_f_apply B n x h

-- Corestriction is natural, and `cor ∘ res` is multiplication by the index.
example (H : Subgroup G) [H.FiniteIndex] [DecidableRel (QuotientGroup.rightRel H)]
    {A A' : Rep.{u} k G} (f : A ⟶ A') (n : ℕ) :
    map (MonoidHom.id H) ((Rep.resFunctor H.subtype).map f) n ≫ cor H A' n =
      cor H A n ≫ map (MonoidHom.id G) f n :=
  cor_naturality f n

example (H : Subgroup G) [H.FiniteIndex] [DecidableRel (QuotientGroup.rightRel H)]
    (A : Rep.{u} k G) (n : ℕ) (x : groupCohomology A n) :
    (cor H A n).hom ((map H.subtype (𝟙 (Rep.res H.subtype A)) n).hom x) = H.index • x := by
  have := congrArg (fun φ => φ.hom x) (map_subtype_comp_cor H A n)
  simpa using this

-- For a finite group, `|G|` kills positive-degree cohomology.
example [Finite G] (A : Rep.{u} k G) (x : groupCohomology A 2) : Nat.card G • x = 0 :=
  card_smul_apply_eq_zero A 1 x

-- Over `ℚ`, positive-degree cohomology of a finite group vanishes.
example {G : Type} [Group G] [Finite G] (A : Rep ℚ G) (n : ℕ) :
    Limits.IsZero (groupCohomology A (n + 1)) := by
  refine isZero_of_bijective_card_smul A ?_ n
  have hG : (Nat.card G : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  refine ⟨fun a b hab => ?_, fun b => ⟨(Nat.card G : ℚ)⁻¹ • b, ?_⟩⟩
  · simp only [← Nat.cast_smul_eq_nsmul ℚ] at hab
    exact smul_right_injective _ hG hab
  · simp only [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ hG, one_smul]
