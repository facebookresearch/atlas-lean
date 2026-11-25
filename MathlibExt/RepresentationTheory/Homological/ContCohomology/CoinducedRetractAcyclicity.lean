/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Homological.ContCohomology.CoinducedAcyclicity
public import MathlibExt.RepresentationTheory.Homological.ContCohomology.CoefficientFunctor

/-!
# Acyclicity from a retraction of a coinduced coefficient

A coefficient retraction `Y.coind₁ ⟶ Y` makes positive-degree continuous
cohomology of `Y` a retract of the vanishing cohomology of `Y.coind₁`.  We
also construct such a retraction after restricting a coinduced coefficient
along a continuous group homomorphism, provided a continuous left-equivariant
coordinate on the ambient group is given.

This file does not construct an equivariant coordinate for an open or closed
subgroup and makes no Shapiro, Hochschild--Serre, residue, or norm-residue
claim.

## Main declarations

* `ContinuousCohomology.isZero_succ_of_coinduced_retract`
* `ContinuousCohomology.restrictedCoinducedRetraction`
* `ContinuousCohomology.restrictedCoinducedRetraction_apply`
* `ContinuousCohomology.restrictedCoinducedIota_comp_retraction`
* `ContinuousCohomology.isZero_restrict_coind₁_succ_of_retraction`
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits ContRepresentation

universe u v z w

namespace ContinuousCohomology

private theorem isZero_of_retract
    {C : Type*} [Category C] [HasZeroMorphisms C]
    {A B : C} (i : A ⟶ B) (r : B ⟶ A)
    (hir : i ≫ r = 𝟙 A) (hB : IsZero B) : IsZero A := by
  refine ⟨fun Z ↦ ⟨⟨⟨0⟩, fun f ↦ ?_⟩⟩,
    fun Z ↦ ⟨⟨⟨0⟩, fun f ↦ ?_⟩⟩⟩
  · calc
      f = (𝟙 A) ≫ f := (Category.id_comp f).symm
      _ = (i ≫ r) ≫ f := by rw [hir]
      _ = i ≫ (r ≫ f) := Category.assoc _ _ _
      _ = i ≫ 0 := by rw [hB.eq_of_src (r ≫ f) 0]
      _ = 0 := comp_zero
  · calc
      f = f ≫ 𝟙 A := (Category.comp_id f).symm
      _ = f ≫ (i ≫ r) := by rw [hir]
      _ = (f ≫ i) ≫ r := (Category.assoc _ _ _).symm
      _ = 0 ≫ r := by rw [hB.eq_of_tgt (f ≫ i) 0]
      _ = 0 := zero_comp

/-- Positive continuous cohomology vanishes when the coefficient is a
retract of its compact-open coinduction through the constant inclusion. -/
theorem isZero_succ_of_coinduced_retract
    {k : Type u} {H : Type z}
    [Ring k] [TopologicalSpace k]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H]
    (Y : TopRep.{max z w, u, z} k H)
    (s : Y.coind₁ ⟶ Y)
    (hs : TopRep.coind₁ι.app Y ≫ s = 𝟙 Y)
    (n : ℕ) : IsZero (continuousCohomology (n + 1) Y) := by
  let C := homogeneousCochainsFunctor.{u, z, w} (k := k) (G := H)
  let iH := HomologicalComplex.homologyMap
    (C.map (TopRep.coind₁ι.app Y)) (n + 1)
  let rH := HomologicalComplex.homologyMap (C.map s) (n + 1)
  apply isZero_of_retract iH rH
  · dsimp only [iH, rH]
    rw [← HomologicalComplex.homologyMap_comp]
    change HomologicalComplex.homologyMap
      (C.map (TopRep.coind₁ι.app Y) ≫ C.map s) (n + 1) = _
    rw [← C.map_comp, hs]
    change HomologicalComplex.homologyMap (C.map (𝟙 Y)) (n + 1) =
      𝟙 ((C.obj Y).homology (n + 1))
    rw [C.map_id, HomologicalComplex.homologyMap_id]
  · exact isZero_coind₁_succ Y n

section Restricted

variable {k : Type u} {G : Type v} {H : Type z}
variable [Ring k] [TopologicalSpace k]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [LocallyCompactSpace G] [LocallyCompactSpace H]

private abbrev restrictedCoinducedCoefficient
    (phi : H →ₜ* G)
    (X : TopRep.{max z w, u, v} k G) :
    TopRep.{max z (max v w), u, z} k H :=
  TopRep.res.{u, v, z, max z (max v w)} phi.toMonoidHom X.coind₁

/-- A continuous left-equivariant coordinate on the `H`-orbits of `G`
produces a retraction of the coinduced coefficient after restriction. -/
def restrictedCoinducedRetraction
    (phi : H →ₜ* G)
    (X : TopRep.{max z w, u, v} k G)
    (r : C(G, H))
    (hr : ∀ h g, r (phi h * g) = h * r g) :
    (TopRep.res.{u, v, z, max z (max v w)}
        phi.toMonoidHom X.coind₁).coind₁ ⟶
      TopRep.res.{u, v, z, max z (max v w)}
        phi.toMonoidHom X.coind₁ :=
  TopRep.ofHom
    { toFun := fun F ↦
        ⟨fun g ↦ F (r g) g,
          continuous_eval.comp
            ((F.continuous.comp r.continuous).prodMk continuous_id)⟩
      map_add' := by
        intro F K
        ext g
        rfl
      map_smul' := by
        intro a F
        ext g
        rfl
      cont := by
        apply ContinuousMap.continuous_of_continuous_uncurry
        have h₁ : Continuous (fun p : C(H, C(G, X)) × G ↦ p.1 (r p.2)) :=
          continuous_eval.comp
            (continuous_fst.prodMk (r.continuous.comp continuous_snd))
        exact continuous_eval.comp (h₁.prodMk continuous_snd)
      isIntertwining' := by
        intro h
        ext F g
        change X.ρ (phi h)
            (F (h⁻¹ * r g) ((phi h)⁻¹ * g)) =
          X.ρ (phi h)
            (F (r ((phi h)⁻¹ * g)) ((phi h)⁻¹ * g))
        rw [← map_inv]
        rw [hr] }

/-- The restricted-coinduced retraction evaluates at the coordinate and the
ambient group variable. -/
@[simp]
theorem restrictedCoinducedRetraction_apply
    (phi : H →ₜ* G)
    (X : TopRep.{max z w, u, v} k G)
    (r : C(G, H))
    (hr : ∀ h g, r (phi h * g) = h * r g)
    (F : C(H, C(G, X))) (g : G) :
    (restrictedCoinducedRetraction.{u, v, z, w} phi X r hr).hom F g =
      F (r g) g :=
  rfl

/-- The constant-function inclusion followed by the restricted-coinduced
retraction is the identity. -/
@[reassoc (attr := simp)]
theorem restrictedCoinducedIota_comp_retraction
    (phi : H →ₜ* G)
    (X : TopRep.{max z w, u, v} k G)
    (r : C(G, H))
    (hr : ∀ h g, r (phi h * g) = h * r g) :
    TopRep.ofHom (X.ρ.coind₁.restrict (phi : H →* G)).coind₁ι ≫
        restrictedCoinducedRetraction.{u, v, z, w} phi X r hr =
      𝟙 (TopRep.res.{u, v, z, max z (max v w)}
        phi.toMonoidHom X.coind₁) := by
  ext F g
  rfl

/-- A continuous left-equivariant coordinate makes positive continuous
cohomology of a restricted coinduced coefficient vanish. -/
theorem isZero_restrict_coind₁_succ_of_retraction
    (phi : H →ₜ* G)
    (X : TopRep.{max z w, u, v} k G)
    (r : C(G, H))
    (hr : ∀ h g, r (phi h * g) = h * r g)
    (n : ℕ) :
    IsZero (continuousCohomology.{u, z, max v w} (n + 1)
      (TopRep.res.{u, v, z, max z (max v w)}
        phi.toMonoidHom X.coind₁)) :=
  isZero_succ_of_coinduced_retract.{u, z, max v w}
    (restrictedCoinducedCoefficient.{u, v, z, w} phi X)
    (restrictedCoinducedRetraction.{u, v, z, w} phi X r hr)
    (restrictedCoinducedIota_comp_retraction.{u, v, z, w} phi X r hr) n

end Restricted

end ContinuousCohomology

end
