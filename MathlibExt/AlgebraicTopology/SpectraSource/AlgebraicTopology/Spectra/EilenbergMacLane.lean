/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/Spectra/EilenbergMacLane.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.SimplicialSet.Pointed.ReducedFree
public import MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.Spectra.SymmetricSpectrum
public import MathlibExt.AlgebraicTopology.SpectraSource.CategoryTheory.Monoidal.Mod.Algebra

/-!
# The Eilenberg–MacLane symmetric spectra `HR` and `HM`

For a commutative ring `R`, the Eilenberg–MacLane symmetric spectrum `HR` has as `n`-th level the
reduced free module `R~[Sⁿ]` on the simplicial sphere `Sⁿ = (S¹)^∧n`, with `Σ_n` permuting the
sphere coordinates. It is the composite of the sphere symmetric sequence `n ↦ Sⁿ` with the lax
braided functor `R~[-]`, so it is a commutative monoid for the Day convolution product
(`SymmetricSequence.eilenbergMacLane R`): its multiplication
`R~[S^p] ∧ R~[S^q] ⟶ R~[S^(p+q)]` is the bilinear extension of the concatenation of sphere
coordinates, `[x] ∧ [y] ↦ [x ∧ y]`, and its unit is the generator of the non-basepoint simplex
of `S⁰`.

Sending each simplex of `Sⁿ` to its generator is a morphism of commutative monoids from the sphere
symmetric sequence to `HR` (`SymmetricSequence.sphereToEilenbergMacLane R`). Restricting scalars
along it makes `HR` a symmetric spectrum (`SymmetricSpectrum.eilenbergMacLane R`). Its structure
maps `S^p ∧ R~[S^q] ⟶ R~[S^(p+q)]` send `x ∧ Σ aᵢ yᵢ` to `Σ aᵢ (x ∧ yᵢ)`
(`SymmetricSpectrum.eilenbergMacLane_dayStructureMap_app_smashMk`). The multiplication of `HR`
descends to the smash product over the sphere, making `HR` a commutative ring spectrum, a
commutative monoid object of symmetric spectra (`Mod.monObjComapRegular`,
`Mod.isCommMonObjComapRegular`).

For an `R`-module `M`, the Eilenberg–MacLane spectrum `HM` has as `n`-th level the reduced free
module `M~[Sⁿ] = R~[Sⁿ] ⊗_R M` with coefficients in `M`, with `Σ_n` permuting the sphere
coordinates. It is a module over the commutative monoid `HR` of symmetric sequences
(`SymmetricSequence.eilenbergMacLaneModule R M`), with structure maps
`R~[S^p] ∧ M~[S^q] ⟶ M~[S^(p+q)]` the bilinear extension of `[x] ∧ ([y] ⊗ m) ↦ [x ∧ y] ⊗ m`.
A linear map `M ⟶ N` induces a morphism of `HR`-modules `HM ⟶ HN`, functorially. Restricting
scalars along the unit `S ⟶ HR` makes `HM` a symmetric spectrum
(`SymmetricSpectrum.eilenbergMacLaneModule R M`), functorial in `M`, with structure maps
`S^p ∧ M~[S^q] ⟶ M~[S^(p+q)]` sending `x ∧ Σ yᵢ ⊗ mᵢ` to `Σ (x ∧ yᵢ) ⊗ mᵢ`. The action of the
ring spectrum `HR` on `HM` through the smash product over the sphere is not constructed here.

## Main definitions

* `SymmetricSequence.eilenbergMacLane R`: the commutative monoid `n ↦ R~[Sⁿ]` of symmetric
  sequences.
* `SymmetricSequence.sphereToEilenbergMacLane R`: the unit morphism of monoids `S ⟶ HR`.
* `SymmetricSpectrum.eilenbergMacLane R`: the Eilenberg–MacLane symmetric spectrum `HR`, a
  commutative ring spectrum.
* `SymmetricSequence.eilenbergMacLaneModule R M`: the `HR`-module `n ↦ M~[Sⁿ]` of an `R`-module
  `M`, and `SymmetricSequence.eilenbergMacLaneModuleMap R g`: the morphism `HM ⟶ HN` induced by a
  linear map `g`.
* `SymmetricSpectrum.eilenbergMacLaneModule R M`: the Eilenberg–MacLane symmetric spectrum `HM`,
  and `SymmetricSpectrum.eilenbergMacLaneModuleMap R g`: the map `HM ⟶ HN` induced by a linear
  map `g`.

## Main statements

* `SymmetricSpectrum.eilenbergMacLane_dayStructureMap`: the structure maps of `HR` are the
  generator map followed by the multiplication of `HR`.
* `SymmetricSpectrum.eilenbergMacLane_dayStructureMap_app_smashMk`: the structure maps on
  simplices.
* `SymmetricSpectrum.tensorπ_eilenbergMacLane_mul_hom`,
  `SymmetricSpectrum.eilenbergMacLane_one_hom`: the multiplication and unit of the ring spectrum
  `HR`.
* `SymmetricSequence.eilenbergMacLaneModule_dayStructureMap_app_smashMk`,
  `SymmetricSpectrum.eilenbergMacLaneModule_dayStructureMap_app_smashMk`: the structure maps of
  `HM`, as an `HR`-module and as a symmetric spectrum, on simplices.
* `SymmetricSequence.eilenbergMacLaneModuleMap_id`,
  `SymmetricSequence.eilenbergMacLaneModuleMap_comp`,
  `SymmetricSpectrum.eilenbergMacLaneModuleMap_id`,
  `SymmetricSpectrum.eilenbergMacLaneModuleMap_comp`: functoriality of `HM` in `M`.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 1.
* S. Schwede, *Symmetric spectra*, book project, Chapter I.
-/

public section

open CategoryTheory MonoidalCategory

namespace MathlibExt.SpectraSource

open scoped DayFunctor

noncomputable section

variable (R : Type) [CommRing R]

namespace SymmetricSequence

/-- The Eilenberg–MacLane symmetric sequence `n ↦ R~[Sⁿ]` of reduced free `R`-modules on the
simplicial spheres, with `Σ_n` permuting the sphere coordinates. The bilinear extension of the
concatenation of coordinates `[x] ∧ [y] ↦ [x ∧ y]` makes it a commutative monoid for the Day
convolution product, through the instances `DayFunctor.monObj` and `DayFunctor.isCommMonObj`. -/
-- An abbreviation, so that the instances for lax braided functors apply to it.
abbrev eilenbergMacLane : SymmetricSequence.{0} :=
  .mk (PointedSSet.smashPowFunctor PointedSSet.circle ⋙ PointedSSet.reducedFree R)

/- The Eilenberg–MacLane symmetric sequence is a commutative monoid. -/
example : IsCommMonObj (eilenbergMacLane R) := inferInstance

/-- The unit morphism `S ⟶ HR` from the sphere symmetric sequence, sending each simplex of `Sⁿ` to
its generator in `R~[Sⁿ]`. It is a morphism of monoids, through the instance
`DayFunctor.isMonHom`. -/
def sphereToEilenbergMacLane : sphere ⟶ eilenbergMacLane R :=
  .mk ((PointedSSet.smashPowFunctor PointedSSet.circle).rightUnitor.inv ≫
    Functor.whiskerLeft _ (PointedSSet.toReducedFree R))

@[simp]
lemma sphereToEilenbergMacLane_natTrans_app (k : FiniteBijection) :
    (sphereToEilenbergMacLane R).natTrans.app k =
      PointedSSet.reducedFreeι R (PointedSSet.circle.smashPow (Fin k.len)) := by
  simp [sphereToEilenbergMacLane]

/-- The generator maps `Sⁿ ⟶ R~[Sⁿ]` form a monoidal natural transformation. -/
instance : NatTrans.IsMonoidal (sphereToEilenbergMacLane R).natTrans :=
  inferInstanceAs (NatTrans.IsMonoidal
    ((PointedSSet.smashPowFunctor PointedSSet.circle).rightUnitor.inv ≫
      Functor.whiskerLeft _ (PointedSSet.toReducedFree R)))

/- The unit `S ⟶ HR` is a morphism of monoids. -/
example : IsMonHom (sphereToEilenbergMacLane R) := inferInstance

end SymmetricSequence

namespace SymmetricSpectrum

/-- The Eilenberg–MacLane symmetric spectrum `HR`: the commutative monoid `n ↦ R~[Sⁿ]` of
symmetric sequences, regarded as a module over the sphere by restricting scalars along the unit
`S ⟶ HR`. It is a commutative ring spectrum, a commutative monoid for the smash product over the
sphere, through the instances `Mod.monObjComapRegular` and `Mod.isCommMonObjComapRegular`. -/
-- An abbreviation, so that the monoid instances for `Mod.comapRegular` apply to it.
abbrev eilenbergMacLane : SymmetricSpectrum :=
  Mod.comapRegular (SymmetricSequence.sphereToEilenbergMacLane R)

/- The Eilenberg–MacLane spectrum is a commutative ring spectrum. -/
example : IsCommMonObj (eilenbergMacLane R) := inferInstance

/-- On representatives in `HR ⊗ HR`, the multiplication `HR ∧_S HR ⟶ HR` of the ring spectrum `HR`
is the multiplication of the symmetric sequence `n ↦ R~[Sⁿ]`. -/
lemma tensorπ_eilenbergMacLane_mul_hom :
    Mod.tensorπ _ _ ≫ (MonObj.mul : eilenbergMacLane R ⊗ eilenbergMacLane R ⟶ _).hom =
      (MonObj.mul : SymmetricSequence.eilenbergMacLane R ⊗ SymmetricSequence.eilenbergMacLane R ⟶
        _) :=
  Mod.tensorπ_comapRegular_mul_hom _

/-- The unit `S ⟶ HR` of the ring spectrum `HR` is the generator map
`SymmetricSequence.sphereToEilenbergMacLane R`. -/
lemma eilenbergMacLane_one_hom :
    (MonObj.one : 𝟙_ SymmetricSpectrum ⟶ eilenbergMacLane R).hom =
      SymmetricSequence.sphereToEilenbergMacLane R :=
  (rfl)

lemma eilenbergMacLane_eq_comap : eilenbergMacLane R =
    (Mod.comap (SymmetricSequence.sphereToEilenbergMacLane R)).obj
      (Mod.regular (SymmetricSequence.eilenbergMacLane R)) :=
  (rfl)

lemma eilenbergMacLane_X : (eilenbergMacLane R).X = SymmetricSequence.eilenbergMacLane R :=
  (rfl)

/-- The sphere acts on `HR` through the unit `S ⟶ HR` followed by the multiplication of `HR`. -/
lemma eilenbergMacLane_smul :
    ModObj.smul (M := SymmetricSequence.sphere) (X := (eilenbergMacLane R).X) =
      SymmetricSequence.sphereToEilenbergMacLane R ▷ SymmetricSequence.eilenbergMacLane R ≫
        MonObj.mul :=
  (rfl)

/-- The structure maps `S^p ∧ R~[S^q] ⟶ R~[S^(p+q)]` of `HR` are the generator map on the sphere
factor followed by the multiplication of `HR`. -/
lemma eilenbergMacLane_dayStructureMap (p q : FiniteBijection) :
    (eilenbergMacLane R).dayStructureMap p q =
      PointedSSet.reducedFreeι R _ ▷ _ ≫
        Functor.LaxMonoidal.μ (PointedSSet.smashPowFunctor PointedSSet.circle ⋙
          PointedSSet.reducedFree R) p q := by
  rw [Mod.dayStructureMap_def, eilenbergMacLane_smul, DayFunctor.comp_natTrans,
    NatTrans.comp_app]
  -- The Day convolution unit is that of `(eilenbergMacLane R).X`, which is the symmetric
  -- sequence `SymmetricSequence.eilenbergMacLane R` only up to unfolding, so the rewrite is
  -- applied by unification.
  refine (DayFunctor.η_app_comp_whiskerRight_natTrans_app_assoc
    (SymmetricSequence.sphereToEilenbergMacLane R) (SymmetricSequence.eilenbergMacLane R) p q
    _).trans ?_
  rw [DayFunctor.η_app_comp_mul_natTrans_app,
    SymmetricSequence.sphereToEilenbergMacLane_natTrans_app]

/-- The structure map `S^p ∧ R~[S^q] ⟶ R~[S^(p+q)]` of `HR` sends `x ∧ Σ aᵢ yᵢ` to
`Σ aᵢ (x ∧ yᵢ)`, where `x ∧ yᵢ ∈ S^(p+q)` concatenates the sphere coordinates. -/
@[simp]
lemma eilenbergMacLane_dayStructureMap_app_smashMk {p q : FiniteBijection}
    {n : SimplexCategoryᵒᵖ} (x : (PointedSSet.circle.smashPow (Fin p.len)).right.obj n)
    (v : ((PointedSSet.reducedFree R).obj
      (PointedSSet.circle.smashPow (Fin q.len))).right.obj n) :
    ((eilenbergMacLane R).dayStructureMap p q).right.app n (PointedSSet.smashMk x v) =
      ReducedFreeModule.map R (fun y ↦ (Functor.LaxMonoidal.μ
        (PointedSSet.smashPowFunctor PointedSSet.circle) p q).right.app n
          (PointedSSet.smashMk x y)) (by simp) v := by
  rw [eilenbergMacLane_dayStructureMap, Functor.LaxMonoidal.comp_μ, PointedSSet.reducedFree_μ,
    ← Category.assoc, PointedSSet.comp_right_app_apply, PointedSSet.reducedFree_map_app]
  simp

end SymmetricSpectrum

section Module

variable (M : Type) [AddCommGroup M] [Module R M]

namespace SymmetricSequence

/-- The Eilenberg–MacLane symmetric sequence `n ↦ M~[Sⁿ] = R~[Sⁿ] ⊗_R M` of an `R`-module `M`,
with `Σ_n` permuting the sphere coordinates, as a module over the commutative monoid `HR`. Its
structure maps `R~[S^p] ∧ M~[S^q] ⟶ M~[S^(p+q)]` are the bilinear extension of
`[x] ∧ ([y] ⊗ m) ↦ [x ∧ y] ⊗ m`, concatenating sphere coordinates
(`SymmetricSequence.eilenbergMacLaneModule_dayStructureMap_app_smashMk`). -/
-- An abbreviation, so that the levels of `HM` are the reduced free modules `M~[Sⁿ]`.
abbrev eilenbergMacLaneModule : Mod SymmetricSequence.{0} (eilenbergMacLane R) :=
  Mod.dayMk (.mk (PointedSSet.smashPowFunctor PointedSSet.circle ⋙
      PointedSSet.reducedFreeTensor R M))
    (PointedSSet.reducedFreeTensorCompAct R M _)
    (PointedSSet.reducedFreeTensorCompAct_unit _) (PointedSSet.reducedFreeTensorCompAct_assoc _)

/-- The structure maps `R~[S^p] ∧ M~[S^q] ⟶ M~[S^(p+q)]` of the `HR`-module `HM` are the action
of reduced free `R`-modules followed by the concatenation of sphere coordinates. -/
lemma eilenbergMacLaneModule_dayStructureMap (p q : FiniteBijection) :
    (eilenbergMacLaneModule R M).dayStructureMap p q =
      PointedSSet.reducedFreeTensorAct R M _ _ ≫ (PointedSSet.reducedFreeTensor R M).map
        (Functor.LaxMonoidal.μ (PointedSSet.smashPowFunctor PointedSSet.circle) p q) :=
  (Mod.dayStructureMap_dayMk _ _ _ _ p q).trans (PointedSSet.reducedFreeTensorCompAct_app _ p q)

/-- The structure map `R~[S^p] ∧ M~[S^q] ⟶ M~[S^(p+q)]` of `HM` sends `v ∧ Σ yᵢ ⊗ mᵢ` to
`Σ (v ∧ yᵢ) ⊗ mᵢ`, where `x ∧ y ∈ S^(p+q)` concatenates the sphere coordinates. -/
lemma eilenbergMacLaneModule_dayStructureMap_app_smashMk {p q : FiniteBijection}
    {n : SimplexCategoryᵒᵖ} (v : ((PointedSSet.reducedFree R).obj
      (PointedSSet.circle.smashPow (Fin p.len))).right.obj n)
    (t : ((PointedSSet.reducedFreeTensor R M).obj
      (PointedSSet.circle.smashPow (Fin q.len))).right.obj n) :
    ((eilenbergMacLaneModule R M).dayStructureMap p q).right.app n (PointedSSet.smashMk v t) =
      LinearMap.rTensor M (ReducedFreeModule.map₂ R (fun x y ↦ (Functor.LaxMonoidal.μ
        (PointedSSet.smashPowFunctor PointedSSet.circle) p q).right.app n
          (PointedSSet.smashMk x y)) (by simp) (by simp) v) t := by
  rw [Mod.dayStructureMap_dayMk, PointedSSet.reducedFreeTensorCompAct_app_app_smashMk]

variable {M} {N P : Type} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- The morphism of `HR`-modules `HM ⟶ HN` induced by a linear map `g : M →ₗ[R] N`, applying `g`
to the coefficients in every level. -/
def eilenbergMacLaneModuleMap (g : M →ₗ[R] N) :
    eilenbergMacLaneModule R M ⟶ eilenbergMacLaneModule R N :=
  Mod.dayHomMk (.mk (Functor.whiskerLeft _ (PointedSSet.reducedFreeTensorMap R g))) fun p q ↦ by
    rw [Mod.dayStructureMap_dayMk, Mod.dayStructureMap_dayMk]
    exact PointedSSet.reducedFreeTensorCompAct_app_comp_reducedFreeTensorMap_app _ g p q

@[simp]
lemma eilenbergMacLaneModuleMap_hom_natTrans_app (g : M →ₗ[R] N) (k : FiniteBijection) :
    (eilenbergMacLaneModuleMap R g).hom.natTrans.app k =
      (PointedSSet.reducedFreeTensorMap R g).app (PointedSSet.circle.smashPow (Fin k.len)) := by
  simp [eilenbergMacLaneModuleMap]

@[simp]
lemma eilenbergMacLaneModuleMap_id :
    eilenbergMacLaneModuleMap R (LinearMap.id : M →ₗ[R] M) = 𝟙 _ := by
  apply Mod.Hom.ext
  apply DayFunctor.hom_ext
  ext k : 2
  simp

lemma eilenbergMacLaneModuleMap_comp (g : M →ₗ[R] N) (h : N →ₗ[R] P) :
    eilenbergMacLaneModuleMap R (h ∘ₗ g) =
      eilenbergMacLaneModuleMap R g ≫ eilenbergMacLaneModuleMap R h := by
  apply Mod.Hom.ext
  apply DayFunctor.hom_ext
  ext k : 2
  simp [PointedSSet.reducedFreeTensorMap_comp]

end SymmetricSequence

namespace SymmetricSpectrum

/-- The Eilenberg–MacLane symmetric spectrum `HM` of an `R`-module `M`: the `HR`-module
`n ↦ M~[Sⁿ]` of symmetric sequences, regarded as a symmetric spectrum by restricting scalars along
the unit `S ⟶ HR`. -/
-- Written as a structure with an explicit underlying object, exposed and implicitly reducible, so
-- that its levels are those of the symmetric sequence `n ↦ M~[Sⁿ]`.
@[expose, implicit_reducible]
def eilenbergMacLaneModule : SymmetricSpectrum :=
  letI := (SymmetricSequence.eilenbergMacLaneModule R M).mod
  letI := Mod.scalarRestriction (SymmetricSequence.sphereToEilenbergMacLane R)
    (SymmetricSequence.eilenbergMacLaneModule R M).X
  ⟨(SymmetricSequence.eilenbergMacLaneModule R M).X⟩

/-- `HM` is the restriction of scalars of the `HR`-module `n ↦ M~[Sⁿ]` along the unit `S ⟶ HR`. -/
lemma eilenbergMacLaneModule_eq : eilenbergMacLaneModule R M =
    (Mod.comap (SymmetricSequence.sphereToEilenbergMacLane R)).obj
      (SymmetricSequence.eilenbergMacLaneModule R M) :=
  (rfl)

/-- The structure maps `S^p ∧ M~[S^q] ⟶ M~[S^(p+q)]` of `HM` are the generator map on the sphere
factor followed by the action of reduced free `R`-modules and the concatenation of sphere
coordinates. -/
lemma eilenbergMacLaneModule_dayStructureMap (p q : FiniteBijection) :
    (eilenbergMacLaneModule R M).dayStructureMap p q =
      PointedSSet.reducedFreeι R ((PointedSSet.smashPowFunctor PointedSSet.circle).obj p) ▷
          (PointedSSet.reducedFreeTensor R M).obj
            ((PointedSSet.smashPowFunctor PointedSSet.circle).obj q) ≫
        (PointedSSet.reducedFreeTensorCompAct R M
          (PointedSSet.smashPowFunctor PointedSSet.circle)).app (p, q) := by
  refine (Mod.dayStructureMap_comap (SymmetricSequence.sphereToEilenbergMacLane R)
    (SymmetricSequence.eilenbergMacLaneModule R M) p q).trans ?_
  rw [SymmetricSequence.sphereToEilenbergMacLane_natTrans_app, Mod.dayStructureMap_dayMk]
  -- The two sides differ only in how the levels of the spheres and of `M~[S^q]` are written.
  rfl

/-- The structure map `S^p ∧ M~[S^q] ⟶ M~[S^(p+q)]` of `HM` sends `x ∧ Σ yᵢ ⊗ mᵢ` to
`Σ (x ∧ yᵢ) ⊗ mᵢ`, where `x ∧ yᵢ ∈ S^(p+q)` concatenates the sphere coordinates. -/
@[simp]
lemma eilenbergMacLaneModule_dayStructureMap_app_smashMk {p q : FiniteBijection}
    {n : SimplexCategoryᵒᵖ} (x : (PointedSSet.circle.smashPow (Fin p.len)).right.obj n)
    (t : ((PointedSSet.reducedFreeTensor R M).obj
      (PointedSSet.circle.smashPow (Fin q.len))).right.obj n) :
    ((eilenbergMacLaneModule R M).dayStructureMap p q).right.app n (PointedSSet.smashMk x t) =
      LinearMap.rTensor M (ReducedFreeModule.map R (fun y ↦ (Functor.LaxMonoidal.μ
        (PointedSSet.smashPowFunctor PointedSSet.circle) p q).right.app n
          (PointedSSet.smashMk x y)) (by simp)) t := by
  rw [eilenbergMacLaneModule_dayStructureMap,
    PointedSSet.reducedFreeι_whiskerRight_comp_reducedFreeTensorCompAct_app_app_smashMk
      (PointedSSet.smashPowFunctor PointedSSet.circle) p q]

variable {M} {N P : Type} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- The map of symmetric spectra `HM ⟶ HN` induced by a linear map `g : M →ₗ[R] N`, applying `g`
to the coefficients in every level: the morphism of `HR`-modules
`SymmetricSequence.eilenbergMacLaneModuleMap R g` after restricting scalars to the sphere. -/
def eilenbergMacLaneModuleMap (g : M →ₗ[R] N) :
    eilenbergMacLaneModule R M ⟶ eilenbergMacLaneModule R N :=
  (Mod.comap (SymmetricSequence.sphereToEilenbergMacLane R)).map
    (SymmetricSequence.eilenbergMacLaneModuleMap R g)

@[simp]
lemma eilenbergMacLaneModuleMap_hom (g : M →ₗ[R] N) :
    (eilenbergMacLaneModuleMap R g).hom = (SymmetricSequence.eilenbergMacLaneModuleMap R g).hom :=
  (rfl)

@[simp]
lemma eilenbergMacLaneModuleMap_id :
    eilenbergMacLaneModuleMap R (LinearMap.id : M →ₗ[R] M) = 𝟙 _ := by
  ext : 1
  -- The identity of `HM` is that of the `HR`-module `n ↦ M~[Sⁿ]` after unfolding the restriction
  -- of scalars.
  rw [eilenbergMacLaneModuleMap_hom, SymmetricSequence.eilenbergMacLaneModuleMap_id]
  rfl

lemma eilenbergMacLaneModuleMap_comp (g : M →ₗ[R] N) (h : N →ₗ[R] P) :
    eilenbergMacLaneModuleMap R (h ∘ₗ g) =
      eilenbergMacLaneModuleMap R g ≫ eilenbergMacLaneModuleMap R h := by
  ext : 1
  simp [SymmetricSequence.eilenbergMacLaneModuleMap_comp]

end SymmetricSpectrum

end Module

end

end MathlibExt.SpectraSource
