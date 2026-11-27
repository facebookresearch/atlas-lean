/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NeronModelUniqueness

/-!
# Group law on a Néron model

Let `N` be a Néron model over `R` of a group object `A` over `Spec K`. The unit, multiplication
and inverse of `A` extend uniquely to the model, because `N.model`, `N.model ⊗ N.model` and
`Spec R` are smooth over `R` and taking generic fibres is a bijection on morphisms out of smooth
`R`-schemes; the group axioms hold because they hold on generic fibres.

* `NeronModel.grpObj`: the group object structure on `N.model`;
* `NeronModel.isMonHom_genericIso_grpObj`: its generic fibre is identified with `A` as a group;
* `NeronModel.eq_grpObj_of_isMonHom`: it is the only group object structure with that property;
* `NeronModel.isCommMonObj_grpObj`: it is commutative when `A` is;
* `NeronModel.groupStructure`, `NeronModel.groupStructure_unique`: for commutative `A`, the
  resulting `NeronModel.GroupStructure`, and its uniqueness.

Reference: S. Lichtenstein, *Néron models*, seminar notes, Stanford, 2011,
http://math.stanford.edu/~conrad/mordellsem/Notes/L11.pdf: Proposition 1.4.2 (iii), p. 5.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NeronModels

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.SemistableModels
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped MonObj

universe u

variable {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
  {A : Over (Spec (.of K))}

/-- The cartesian product of two smooth schemes over `Spec R` is smooth over `Spec R`. -/
instance smooth_tensorObj_hom (X Y : Over (trait R)) [Smooth X.hom] [Smooth Y.hom] :
    Smooth (X ⊗ Y).hom := by
  change Smooth (pullback.fst X.hom Y.hom ≫ X.hom); infer_instance

/-- The terminal scheme over `Spec R` is smooth over `Spec R`. -/
instance smooth_tensorUnit_hom : Smooth (𝟙_ (Over (trait R))).hom := by
  change Smooth (𝟙 _); infer_instance

namespace NeronModel

variable (N : NeronModel R K A)

/-- The unique extension to `N.model` of a morphism between generic fibres with smooth source:
the inverse of taking generic fibres (`NeronModel.bijective_map`). -/
def pre {T : Over (trait R)} [Smooth T.hom]
    (f : (genericFunctor R K).obj T ⟶ (genericFunctor R K).obj N.model) : T ⟶ N.model :=
  Function.surjInv (N.bijective_map T).2 f

/-- The generic fibre of `NeronModel.pre f` is `f`. -/
@[simp] theorem map_pre {T : Over (trait R)} [Smooth T.hom]
    (f : (genericFunctor R K).obj T ⟶ (genericFunctor R K).obj N.model) :
    (genericFunctor R K).map (N.pre f) = f :=
  Function.surjInv_eq (N.bijective_map T).2 f

/-- Morphisms from a smooth scheme into `N.model` with equal generic fibres are equal. -/
theorem map_injective {T : Over (trait R)} [Smooth T.hom] {f g : T ⟶ N.model}
    (h : (genericFunctor R K).map f = (genericFunctor R K).map g) : f = g :=
  (N.bijective_map T).1 h

variable [GrpObj A]

/-- **Group law on a Néron model.** The group object structure on `N.model` whose unit,
multiplication and inverse are the unique extensions of those of `A`, transported to the generic
fibre of `N.model` through `N.genericIso` (Lichtenstein, *Néron models*, Proposition 1.4.2 (iii),
p. 5). -/
abbrev grpObj : GrpObj N.model :=
  letI : GrpObj ((genericFunctor R K).obj N.model) := GrpObj.ofIso N.genericIso.symm
  { one := N.pre
      (Functor.OplaxMonoidal.η (genericFunctor R K) ≫ η[(genericFunctor R K).obj N.model])
    mul := N.pre (δ (genericFunctor R K) N.model N.model ≫ μ[(genericFunctor R K).obj N.model])
    one_mul := N.map_injective <| by simp [← δ_natural_left_assoc]
    mul_one := N.map_injective <| by simp [← δ_natural_right_assoc]
    mul_assoc := N.map_injective <| by simp [← δ_natural_left_assoc, ← δ_natural_right_assoc]
    inv := N.pre ι[(genericFunctor R K).obj N.model]
    left_inv := N.map_injective <| by simp [Functor.OplaxMonoidal.η_of_cartesianMonoidalCategory]
    right_inv := N.map_injective <| by simp [Functor.OplaxMonoidal.η_of_cartesianMonoidalCategory] }

/-- The generic fibre of the multiplication of `NeronModel.grpObj` is the multiplication of `A`,
through `N.genericIso`. -/
theorem map_mul_grpObj :
    (genericFunctor R K).map (@MonObj.mul _ _ _ N.model N.grpObj.toMonObj) =
      Functor.OplaxMonoidal.δ (genericFunctor R K) N.model N.model ≫
        (N.genericIso.hom ⊗ₘ N.genericIso.hom) ≫ μ[A] ≫ N.genericIso.inv := by
  refine (N.map_pre _).trans ?_
  simp [MonObj.ofIso_mul]

/-- With `NeronModel.grpObj`, the identification `N.genericIso` of the generic fibre of
`N.model` with `A` is a homomorphism of group objects: the group law of `N.model` extends that of
`A`. -/
theorem isMonHom_genericIso_grpObj :
    letI := N.grpObj
    IsMonHom N.genericIso.hom :=
  letI := N.grpObj
  ⟨by
        change (Functor.LaxMonoidal.ε (genericFunctor R K) ≫ (genericFunctor R K).map
          (N.pre (Functor.OplaxMonoidal.η (genericFunctor R K) ≫ _))) ≫ _ = _
        simp [MonObj.ofIso_one], by
        change (Functor.LaxMonoidal.μ (genericFunctor R K) _ _ ≫ (genericFunctor R K).map
          (N.pre (Functor.OplaxMonoidal.δ (genericFunctor R K) _ _ ≫ _))) ≫ _ = _
        simp [MonObj.ofIso_mul]⟩

/-- Under a group object structure `g` on `N.model` for which `N.genericIso` is a homomorphism,
the generic fibre of the multiplication is the multiplication of `A`. -/
theorem map_mul_of_isMonHom (g : GrpObj N.model)
    (hg : letI := g; IsMonHom N.genericIso.hom) :
    Functor.LaxMonoidal.μ (genericFunctor R K) N.model N.model ≫
      (genericFunctor R K).map (@MonObj.mul _ _ _ N.model g.toMonObj) =
      (N.genericIso.hom ⊗ₘ N.genericIso.hom) ≫ μ[A] ≫ N.genericIso.inv := by
  have h := @IsMonHom.mul_hom _ _ _ _ _ _ _ N.genericIso.hom hg
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

/-- **Uniqueness of the group law.** `NeronModel.grpObj` is the only group object structure on
`N.model` for which `N.genericIso` is a homomorphism of group objects (Lichtenstein, *Néron
models*, Proposition 1.4.2 (iii), p. 5). -/
theorem eq_grpObj_of_isMonHom (g : GrpObj N.model)
    (hg : letI := g; IsMonHom N.genericIso.hom) : g = N.grpObj := by
  refine GrpObj.ext _ _ (MonObj.ext _ _ (N.map_injective ?_))
  rw [← cancel_epi (Functor.LaxMonoidal.μ (genericFunctor R K) N.model N.model)]
  exact (N.map_mul_of_isMonHom g hg).trans
    (N.map_mul_of_isMonHom N.grpObj N.isMonHom_genericIso_grpObj).symm

variable [IsCommMonObj A]

/-- If `A` is commutative, so is the group law `NeronModel.grpObj` on `N.model`
(Lichtenstein, *Néron models*, Proposition 1.4.2 (iii), p. 5). -/
theorem isCommMonObj_grpObj :
    letI := N.grpObj
    IsCommMonObj N.model :=
  letI := N.grpObj
  ⟨N.map_injective <| by
      rw [Functor.map_comp, map_mul_grpObj]
      simp only [Functor.map_braiding, Category.assoc, Functor.Monoidal.μ_δ_assoc]
      rw [← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm_assoc]⟩

/-- For commutative `A`, the commutative group law of `NeronModel.grpObj` packaged as a
`NeronModel.GroupStructure`: a commutative group object structure on `N.model` whose generic
fibre identification with `A` is a homomorphism. -/
@[instance_reducible]
def groupStructure : N.GroupStructure :=
  letI := N.grpObj
  { commutative := N.isCommMonObj_grpObj
    compatible := N.isMonHom_genericIso_grpObj }

omit [IsCommMonObj A] in
/-- Any two `NeronModel.GroupStructure`s on `N` have the same group law
(Lichtenstein, *Néron models*, Proposition 1.4.2 (iii), p. 5). -/
theorem groupStructure_unique (g₁ g₂ : N.GroupStructure) : g₁.toGrpObj = g₂.toGrpObj :=
  (N.eq_grpObj_of_isMonHom _ g₁.compatible).trans
    (N.eq_grpObj_of_isMonHom _ g₂.compatible).symm

end NeronModel

end MathlibExt.AlgebraicGeometry.NeronModels
