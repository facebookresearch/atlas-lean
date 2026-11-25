/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AbelianSchemes
public import MathlibExt.AlgebraicGeometry.SemistableModels

/-!
# Néron interfaces over a general trait

The generic and special fibres use the actual SemistableModels pullback
functors. A Néron model is an actual smooth separated locally finite-type
scheme with an identified generic fibre and unique extension from every
smooth test scheme. Finite type is additional actual quasi-compactness.

The Hom equivalence, functorial extension maps and residue-field reduction
are completed constructions from the defining mapping property. Group
extension, abelian-variety existence and the good-reduction mapping property
remain independent Wanted requests on these actual objects.

`PadicNeronModels` specializes these models to `ℤ_p ⊂ ℚ_p`.

Reference: Conrad, *Néron models, Tamagawa factors, and Tate-Shafarevich
groups*, Theorem 1.1 and Remark 1.3, pp. 2–3: existence over any Dedekind
scheme; §2, property 1 and Example 2.1, pp. 3–4: group extension and good
reduction. https://math.stanford.edu/~conrad/BSDseminar/Notes/L3.pdf
Bosch–Lütkebohmert–Raynaud, *Néron Models*, §§1.1–1.3 and §4.4,
https://doi.org/10.1007/978-3-642-51438-8.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.NeronModels

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.SemistableModels

universe u

variable (R : Type u) [CommRing R] (K : Type u) [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The exact extension property for a fixed integral scheme and its actual
generic fibre, including all smooth test schemes. -/
def HasMappingProperty (M : Over (trait R)) : Prop :=
  ∀ (Y : Over (trait R)) [Smooth Y.hom]
    (f : (genericFunctor R K).obj Y ⟶ (genericFunctor R K).obj M),
    ∃! e : Y ⟶ M, (genericFunctor R K).map e = f

/-- A general locally finite-type Néron model of a specified generic scheme. -/
structure NeronModel (A : Over (Spec (.of K))) where
  /-- The integral model, a scheme over the trait. -/
  model : Over (trait R)
  [smooth : Smooth model.hom]
  [separated : IsSeparated model.hom]
  [locallyFiniteType : LocallyOfFiniteType model.hom]
  /-- The generic fibre of the model is identified with `A`. -/
  genericIso : (genericFunctor R K).obj model ≅ A
  /-- Every generic map from a smooth test scheme has a unique extension. -/
  mappingProperty : ∀ (Y : Over (trait R)) [Smooth Y.hom]
    (f : (genericFunctor R K).obj Y ⟶ A),
    ∃! e : Y ⟶ model, (genericFunctor R K).map e ≫ genericIso.hom = f

attribute [instance] NeronModel.smooth NeronModel.separated
  NeronModel.locallyFiniteType

/-- Finite-type Néron models retain actual quasi-compactness. -/
structure FiniteTypeNeronModel (A : Over (Spec (.of K)))
    extends NeronModel R K A where
  [quasiCompact : QuasiCompact model.hom]

attribute [instance] FiniteTypeNeronModel.quasiCompact

namespace NeronModel

variable {R K} {A : Over (Spec (.of K))} (N : NeronModel R K A)

/-- Unique extension is exactly inverse to the fixed generic restriction. -/
def homEquiv (Y : Over (trait R)) [Smooth Y.hom] :
    (Y ⟶ N.model) ≃ ((genericFunctor R K).obj Y ⟶ A) where
  toFun e := (genericFunctor R K).map e ≫ N.genericIso.hom
  invFun f := Classical.choose (N.mappingProperty Y f)
  left_inv e :=
    ((Classical.choose_spec (N.mappingProperty Y
      ((genericFunctor R K).map e ≫ N.genericIso.hom))).2 e rfl).symm
  right_inv f := (Classical.choose_spec (N.mappingProperty Y f)).1

theorem extend_generic (Y : Over (trait R)) [Smooth Y.hom]
    (f : (genericFunctor R K).obj Y ⟶ A) :
    (genericFunctor R K).map ((N.homEquiv Y).symm f) ≫ N.genericIso.hom = f :=
  (N.homEquiv Y).apply_symm_apply f

variable {B C : Over (Spec (.of K))}

/-- Every generic scheme morphism extends between actual Néron models. -/
def map (M : NeronModel R K A) (N : NeronModel R K B) (f : A ⟶ B) :
    M.model ⟶ N.model :=
  (N.homEquiv M.model).symm (M.genericIso.hom ≫ f)

theorem map_generic (M : NeronModel R K A) (N : NeronModel R K B) (f : A ⟶ B) :
    (genericFunctor R K).map (map M N f) ≫ N.genericIso.hom =
      M.genericIso.hom ≫ f :=
  (N.homEquiv M.model).apply_symm_apply _

theorem map_id (M : NeronModel R K A) : map M M (𝟙 A) = 𝟙 M.model := by
  apply (M.homEquiv M.model).injective
  change (genericFunctor R K).map (map M M (𝟙 A)) ≫ M.genericIso.hom =
    (genericFunctor R K).map (𝟙 M.model) ≫ M.genericIso.hom
  rw [map_generic, (genericFunctor R K).map_id]
  simp

theorem map_comp (M : NeronModel R K A) (N : NeronModel R K B)
    (O : NeronModel R K C) (f : A ⟶ B) (g : B ⟶ C) :
    map M O (f ≫ g) = map M N f ≫ map N O g := by
  apply (O.homEquiv M.model).injective
  change (genericFunctor R K).map (map M O (f ≫ g)) ≫ O.genericIso.hom =
    (genericFunctor R K).map (map M N f ≫ map N O g) ≫ O.genericIso.hom
  rw [map_generic, CategoryTheory.Functor.map_comp, Category.assoc, map_generic]
  simpa only [Category.assoc] using
    (congrArg (fun a ↦ a ≫ g) (map_generic M N f)).symm

variable [GrpObj A] [IsCommMonObj A]

/-- An actual integral group law with its generic normalization. The maps
are morphisms of the model scheme; the generic comparison is a group map. -/
class GroupStructure extends GrpObj N.model where
  [commutative : IsCommMonObj N.model]
  compatible : IsMonHom N.genericIso.hom

attribute [instance] GroupStructure.commutative

end NeronModel

/-- Completed packaging for a fixed smooth separated model satisfying the
actual mapping property. The geometric mapping-property proof is separate. -/
def ofMappingProperty (M : Over (trait R)) [Smooth M.hom]
    [IsSeparated M.hom] [LocallyOfFiniteType M.hom]
    (h : HasMappingProperty R K M) :
    NeronModel R K ((genericFunctor R K).obj M) where
  model := M
  genericIso := Iso.refl _
  mappingProperty Y _ f := by simpa using h Y f

section BaseChange

variable (R' : Type u) [CommRing R'] (K' : Type u) [Field K']
  [Algebra R' K'] [IsFractionRing R' K']
  (φ : trait R' ⟶ trait R) (ψ : Spec (.of K') ⟶ Spec (.of K))
  (sq : ψ ≫ genericInclusion R K = genericInclusion R' K' ≫ φ)

/-- The generic comparison is assembled from actual pullback composition
and the prescribed actual base/coefficient square. -/
def genericBaseChangeIso (M : Over (trait R)) :
    (genericFunctor R' K').obj ((Over.pullback φ).obj M) ≅
      (Over.pullback ψ).obj ((genericFunctor R K).obj M) :=
  ((Over.pullbackComp (genericInclusion R' K') φ).app M).symm ≪≫
    eqToIso (congrArg (fun f ↦ (Over.pullback f).obj M) sq.symm) ≪≫
      (Over.pullbackComp ψ (genericInclusion R K)).app M

variable {A : Over (Spec (.of K))}

instance baseChangeSmooth (M : NeronModel R K A) :
    Smooth ((Over.pullback φ).obj M.model).hom :=
  inferInstanceAs (Smooth (pullback.snd M.model.hom φ))

/-- The actual base-change morphism between models is the unique extension
of the normalized generic comparison. It need not be an isomorphism under
ramified base change. -/
def baseChangeMap (M : NeronModel R K A)
    (N : NeronModel R' K' ((Over.pullback ψ).obj A)) :
    (Over.pullback φ).obj M.model ⟶ N.model :=
  (N.homEquiv ((Over.pullback φ).obj M.model)).symm
    ((genericBaseChangeIso R K R' K' φ ψ sq M.model).hom ≫
      (Over.pullback ψ).map M.genericIso.hom)

theorem baseChangeMap_generic (M : NeronModel R K A)
    (N : NeronModel R' K' ((Over.pullback ψ).obj A)) :
    (genericFunctor R' K').map (baseChangeMap R K R' K' φ ψ sq M N) ≫
      N.genericIso.hom =
    (genericBaseChangeIso R K R' K' φ ψ sq M.model).hom ≫
      (Over.pullback ψ).map M.genericIso.hom :=
  (N.homEquiv ((Over.pullback φ).obj M.model)).apply_symm_apply _

end BaseChange

section Reduction

variable [IsLocalRing R]

/-- Actual integral scheme-valued points. -/
abbrev IntegralPoint (M : Over (trait R)) :=
  {q : trait R ⟶ M.left // q ≫ M.hom = 𝟙 _}

/-- Actual residue-field points of the scheme-theoretic special fibre. -/
abbrev SpecialPoint (M : Over (trait R)) :=
  {q : specialBase R ⟶ ((specialFunctor R).obj M).left //
    q ≫ ((specialFunctor R).obj M).hom = 𝟙 _}

/-- Reduction is induced by the actual residue quotient and pullback square. -/
def reducePoint (M : Over (trait R)) (q : IntegralPoint R M) :
    SpecialPoint R M :=
  ⟨pullback.lift (specialInclusion R ≫ q.1) (𝟙 _) (by
      simp [Category.assoc, q.2]),
    pullback.lift_snd _ _ _⟩

end Reduction

end MathlibExt.AlgebraicGeometry.NeronModels
