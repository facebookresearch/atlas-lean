/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferArbitraryIndependence

/-!
# Corestriction along injective group homomorphisms

Let `k` be a commutative ring, `f : H →* G` injective, and `A` a representation of `G`. The
equivalence `e : H ≃* f.range` identifies restriction along `f` with restriction to its range.
It gives a cohomology isomorphism `I_n : H^n(H,f^*A) ≅ H^n(f.range,Res A)` whose forward map
is pullback along `e⁻¹` with the identity coefficient comparison.

If `f.range` has finite index, composing `I_n.hom` with Schreier corestriction defines `cor_f
: H^n(H,f^*A) → H^n(G,A)`. Its composite with restriction along `f` multiplies by
`[G:f.range]`, and it is natural in `A`. Equal presentations of a subgroup have compatible
coefficient and cohomology comparisons in every degree.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace groupCohomology

universe u

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

/-- Let `G` be a group, `k` a commutative ring, `J,K ≤ G`, `h : J = K`, and `A : Rep k G`. For
`e=MulEquiv.subgroupCongr h : J ≃* K`, the isomorphism `subgroupCongrResIso h A :
(e⁻¹)^*(Res_J A) ≅ Res_K A` has underlying linear map the identity on `A`. -/
noncomputable def subgroupCongrResIso
    {J K : Subgroup G} (h : J = K) (A : Rep k G) :
    Rep.res (MulEquiv.subgroupCongr h).symm.toMonoidHom
        (Rep.res J.subtype A) ≅
      Rep.res K.subtype A := by
  subst K
  exact Iso.refl _

@[simp]
theorem subgroupCongrResIso_hom_apply
    {J K : Subgroup G} (h : J = K) (A : Rep k G) (x : A) :
    (subgroupCongrResIso h A).hom x = x := by
  subst K
  rfl

@[simp]
theorem subgroupCongrResIso_hom_toLinearMap
    {J K : Subgroup G} (h : J = K) (A : Rep k G) :
    (subgroupCongrResIso h A).hom.hom.toLinearMap = LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact subgroupCongrResIso_hom_apply h A x

/-- Let `G` be a group, `k` a commutative ring, `J,K ≤ G` both finite index, `h : J = K`, `A : Rep
k G`, and `n : ℕ`. For `e=MulEquiv.subgroupCongr h` and `γ=(subgroupCongrResIso h A).hom`,
`map e.symm γ n ≫ schreierCorestriction K A n = schreierCorestriction J A n`, as maps
`H^n(J,Res_J A) → H^n(G,A)`. -/
theorem schreierCorestriction_subgroupCongr
    {J K : Subgroup G} (h : J = K)
    [J.FiniteIndex] [K.FiniteIndex] (A : Rep k G) (n : ℕ) :
    groupCohomology.map
        (MulEquiv.subgroupCongr h).symm.toMonoidHom
        (subgroupCongrResIso h A).hom n ≫
      schreierCorestriction K A n =
        schreierCorestriction J A n := by
  subst K
  have hgroup :
      (MulEquiv.subgroupCongr (rfl : J = J)).symm.toMonoidHom =
        MonoidHom.id J := by
    ext x
    rfl
  have hcoeff :
      (subgroupCongrResIso (rfl : J = J) A).hom.hom.toLinearMap =
        ((𝟙 (Rep.res J.subtype A) :
          Rep.res J.subtype A ⟶ Rep.res J.subtype A).hom.toLinearMap) := by
    ext x
    rfl
  rw [groupCohomology.map_congr hgroup hcoeff n,
    groupCohomology.map_id, Category.id_comp]

/-- Let `k` be a commutative ring, `f : H →* G` an injective group homomorphism, and `A : Rep k
G`. Put `e=MonoidHom.ofInjective hf : H ≃* f.range` and `i=f.range.subtype`. The isomorphism
`injectiveRangeResIso f hf A : (e⁻¹)^*(f^*A) ≅ i^*A` has underlying linear map the identity on
`A`, since `f(e⁻¹(g)) = g` for `g ∈ f.range`. -/
noncomputable def injectiveRangeResIso
    (f : H →* G) (hf : Function.Injective f) (A : Rep k G) :
    Rep.res (MonoidHom.ofInjective hf).symm.toMonoidHom
        (Rep.res f A) ≅
      Rep.res f.range.subtype A :=
  Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl k A) (fun g => by
    apply LinearMap.ext
    intro x
    change A.ρ (f ((MonoidHom.ofInjective hf).symm g)) x =
      A.ρ (g : G) x
    rw [MonoidHom.apply_ofInjective_symm]))

@[simp]
theorem injectiveRangeResIso_hom_apply
    (f : H →* G) (hf : Function.Injective f) (A : Rep k G) (x : A) :
    (injectiveRangeResIso f hf A).hom x = x :=
  rfl

@[simp]
theorem injectiveRangeResIso_hom_toLinearMap
    (f : H →* G) (hf : Function.Injective f) (A : Rep k G) :
    (injectiveRangeResIso f hf A).hom.hom.toLinearMap = LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact injectiveRangeResIso_hom_apply f hf A x

/-- Let `k` be a commutative ring, `f : H →* G` injective, `A : Rep k G`, and `n : ℕ`. The
isomorphism `injectiveRangeCohomologyIso f hf A n : H^n(H,f^*A) ≅ H^n(f.range,Res A)` is
induced by `e=MonoidHom.ofInjective hf : H ≃* f.range` and the identity linear coefficient
equivalence. Its forward morphism is `map e.symm (injectiveRangeResIso f hf A).hom n`. -/
noncomputable def injectiveRangeCohomologyIso
    (f : H →* G) (hf : Function.Injective f) (A : Rep k G) (n : ℕ) :
    groupCohomology (Rep.res f A) n ≅
      groupCohomology (Rep.res f.range.subtype A) n :=
  groupCohomology.mapIso (MonoidHom.ofInjective hf)
    (LinearEquiv.refl k A)
    (fun h => by
      apply LinearMap.ext
      intro x
      change A.ρ (f h) x = A.ρ ((MonoidHom.ofInjective hf h : f.range) : G) x
      rfl) n

/-- Let `k` be a commutative ring, `f : H →* G` injective, `A : Rep k G`, and `n : ℕ`. For
`I=injectiveRangeCohomologyIso f hf A n`, `map f (𝟙 (f^*A)) n ≫ I.hom = map f.range.subtype (𝟙
(Res A)) n`. Both sides are restriction maps from `H^n(G,A)` to `H^n(f.range,Res A)`. -/
theorem restriction_comp_injectiveRangeCohomologyIso_hom
    (f : H →* G) (hf : Function.Injective f) (A : Rep k G) (n : ℕ) :
    groupCohomology.map f (𝟙 (Rep.res f A)) n ≫
        (injectiveRangeCohomologyIso f hf A n).hom =
      groupCohomology.map f.range.subtype
        (𝟙 (Rep.res f.range.subtype A)) n := by
  unfold injectiveRangeCohomologyIso
  change groupCohomology.map f (𝟙 (Rep.res f A)) n ≫
      groupCohomology.map
        (MonoidHom.ofInjective hf).symm.toMonoidHom
        (injectiveRangeResIso f hf A).hom n = _
  rw [← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · ext x
    exact MonoidHom.apply_ofInjective_symm hf x
  · apply LinearMap.ext
    intro x
    rfl

/-- Let `k` be a commutative ring, `f : H →* G` injective, `A : Rep k G`, and `n : ℕ`. For
`I=injectiveRangeCohomologyIso f hf A n`, `map f.range.subtype (𝟙 (Res A)) n ≫ I.inv = map f
(𝟙 (f^*A)) n`, as maps `H^n(G,A) → H^n(H,f^*A)`. -/
theorem restriction_comp_injectiveRangeCohomologyIso_inv
    (f : H →* G) (hf : Function.Injective f) (A : Rep k G) (n : ℕ) :
    groupCohomology.map f.range.subtype
        (𝟙 (Rep.res f.range.subtype A)) n ≫
      (injectiveRangeCohomologyIso f hf A n).inv =
        groupCohomology.map f (𝟙 (Rep.res f A)) n := by
  apply (cancel_mono (injectiveRangeCohomologyIso f hf A n).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (restriction_comp_injectiveRangeCohomologyIso_hom
    f hf A n).symm

/-- Let `G` be a group, `k` a commutative ring, `J,K ≤ G`, `h : J = K`, `A : Rep k G`, and `n :
ℕ`. The canonical isomorphism `subgroupCongrCohomologyIso h A n : H^n(J,Res_J A) ≅ H^n(K,Res_K
A)` has forward map `map (MulEquiv.subgroupCongr h).symm (subgroupCongrResIso h A).hom n`. -/
noncomputable def subgroupCongrCohomologyIso
    {J K : Subgroup G} (h : J = K) (A : Rep k G) (n : ℕ) :
    groupCohomology (Rep.res J.subtype A) n ≅
      groupCohomology (Rep.res K.subtype A) n := by
  subst K
  exact Iso.refl _

@[simp]
theorem subgroupCongrCohomologyIso_hom
    {J K : Subgroup G} (h : J = K) (A : Rep k G) (n : ℕ) :
    (subgroupCongrCohomologyIso h A n).hom =
      groupCohomology.map
        (MulEquiv.subgroupCongr h).symm.toMonoidHom
        (subgroupCongrResIso h A).hom n := by
  subst K
  have hgroup :
      (MulEquiv.subgroupCongr (rfl : J = J)).symm.toMonoidHom =
        MonoidHom.id J := by
    ext x
    rfl
  have hcoeff :
      (subgroupCongrResIso (rfl : J = J) A).hom.hom.toLinearMap =
        ((𝟙 (Rep.res J.subtype A) :
          Rep.res J.subtype A ⟶ Rep.res J.subtype A).hom.toLinearMap) := by
    ext x
    rfl
  rw [groupCohomology.map_congr hgroup hcoeff n,
    groupCohomology.map_id]
  rfl

/-- Let `G` be a group, `k` a commutative ring, `J,K ≤ G`, `h : J = K`, `A : Rep k G`, and `n :
ℕ`. The restrictions satisfy `res_J^n ≫ (subgroupCongrCohomologyIso h A n).hom = res_K^n` as
maps `H^n(G,A) → H^n(K,Res_K A)`, with identity coefficient morphisms for both inclusions. -/
theorem restriction_comp_subgroupCongrCohomologyIso_hom
    {J K : Subgroup G} (h : J = K) (A : Rep k G) (n : ℕ) :
    groupCohomology.map J.subtype
        (𝟙 (Rep.res J.subtype A)) n ≫
      (subgroupCongrCohomologyIso h A n).hom =
        groupCohomology.map K.subtype
          (𝟙 (Rep.res K.subtype A)) n := by
  subst K
  change groupCohomology.map J.subtype
      (𝟙 (Rep.res J.subtype A)) n ≫ 𝟙 _ = _
  rw [Category.comp_id]

/-- Let `k` be a commutative ring, `f : H →* G` injective, and `φ : A → B` a morphism of
representations. Put `e=MonoidHom.ofInjective hf`, `i=f.range.subtype`, and
`Γ_A=(injectiveRangeResIso f hf A).hom`. The coefficient morphisms satisfy `Γ_A ≫ i^*(φ) =
(e⁻¹)^*(f^*(φ)) ≫ Γ_B`, from `(e⁻¹)^*(f^*A)` to `i^*B`. -/
theorem injectiveRangeResIso_naturality
    (f : H →* G) (hf : Function.Injective f)
    {A B : Rep k G} (phi : A ⟶ B) :
    (injectiveRangeResIso f hf A).hom ≫
        (Rep.resFunctor f.range.subtype).map phi =
      (Rep.resFunctor
          (MonoidHom.ofInjective hf).symm.toMonoidHom).map
          ((Rep.resFunctor f).map phi) ≫
        (injectiveRangeResIso f hf B).hom := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  rfl

/-- Let `k` be a commutative ring, `f : H →* G` injective with finite-index range, `A : Rep k G`,
and `n : ℕ`. The morphism `schreierCorestrictionOfInjective f hf A n : H^n(H,f^*A) → H^n(G,A)`
is `map e.symm Γ n ≫ schreierCorestriction f.range A n`, where `e=MonoidHom.ofInjective hf : H
≃* f.range` and `Γ=(injectiveRangeResIso f hf A).hom`. -/
noncomputable def schreierCorestrictionOfInjective
    (f : H →* G) (hf : Function.Injective f)
    [f.range.FiniteIndex] (A : Rep k G) (n : ℕ) :
    groupCohomology (Rep.res f A) n ⟶ groupCohomology A n :=
  groupCohomology.map
      (MonoidHom.ofInjective hf).symm.toMonoidHom
      (injectiveRangeResIso f hf A).hom n ≫
    schreierCorestriction f.range A n

/-- Let `k` be a commutative ring, `f : H →* G` injective with finite-index range, `A : Rep k G`,
and `n : ℕ`. Restriction followed by corestriction satisfies `map f (𝟙 (f^*A)) n ≫
schreierCorestrictionOfInjective f hf A n = f.range.index • 𝟙 (H^n(G,A))`. Thus the composite
multiplies every class by `[G:f.range]`. -/
theorem schreierCorestrictionOfInjective_restriction
    (f : H →* G) (hf : Function.Injective f)
    [f.range.FiniteIndex] (A : Rep k G) (n : ℕ) :
    groupCohomology.map f (𝟙 (Rep.res f A)) n ≫
        schreierCorestrictionOfInjective f hf A n =
      f.range.index • 𝟙 (groupCohomology A n) := by
  let e := MonoidHom.ofInjective hf
  let leftCoeff :
      Rep.res (f.comp e.symm.toMonoidHom) A ⟶
        Rep.res f.range.subtype A :=
    (Rep.resFunctor e.symm.toMonoidHom).map (𝟙 (Rep.res f A)) ≫
      (injectiveRangeResIso f hf A).hom
  let rightCoeff :
      Rep.res f.range.subtype A ⟶ Rep.res f.range.subtype A := 𝟙 _
  unfold schreierCorestrictionOfInjective
  rw [← Category.assoc, ← groupCohomology.map_comp]
  have hgroup :
      f.comp e.symm.toMonoidHom = f.range.subtype := by
    ext x
    exact MonoidHom.apply_ofInjective_symm hf x
  have hcoeff : leftCoeff.hom.toLinearMap =
      rightCoeff.hom.toLinearMap := by
    apply LinearMap.ext
    intro x
    rfl
  change groupCohomology.map (f.comp e.symm.toMonoidHom)
      leftCoeff n ≫ schreierCorestriction f.range A n = _
  rw [groupCohomology.map_congr hgroup hcoeff n]
  exact schreierCorestriction_restriction (H := f.range) A n

/-- Let `k` be a commutative ring, `f : H →* G` injective with finite-index range, `φ : A → B` a
morphism of `G`-representations, and `n : ℕ`. Then `cor_f^A ≫ map (id G) φ n = map (id H)
((Rep.resFunctor f).map φ) n ≫ cor_f^B`, where `cor_f` denotes
`schreierCorestrictionOfInjective f hf` in degree `n`. Both maps run from `H^n(H,f^*A)` to
`H^n(G,B)`. -/
theorem schreierCorestrictionOfInjective_naturality
    (f : H →* G) (hf : Function.Injective f)
    [f.range.FiniteIndex] {A B : Rep k G} (phi : A ⟶ B) (n : ℕ) :
    schreierCorestrictionOfInjective f hf A n ≫
        groupCohomology.map (MonoidHom.id G) phi n =
      groupCohomology.map (MonoidHom.id H)
          ((Rep.resFunctor f).map phi) n ≫
        schreierCorestrictionOfInjective f hf B n := by
  let e := MonoidHom.ofInjective hf
  let rangeMapA := groupCohomology.map e.symm.toMonoidHom
    (injectiveRangeResIso f hf A).hom n
  let rangeMapB := groupCohomology.map e.symm.toMonoidHom
    (injectiveRangeResIso f hf B).hom n
  let rangePhi := (Rep.resFunctor f.range.subtype).map phi
  let sourcePhi := (Rep.resFunctor f).map phi
  have hmap : rangeMapA ≫
      groupCohomology.map (MonoidHom.id f.range) rangePhi n =
    groupCohomology.map (MonoidHom.id H) sourcePhi n ≫
      rangeMapB := by
    dsimp only [rangeMapA, rangeMapB, rangePhi, sourcePhi, e]
    rw [← groupCohomology.map_comp, ← groupCohomology.map_comp]
    apply groupCohomology.map_congr rfl
    exact congrArg (fun q => q.hom.toLinearMap)
      (injectiveRangeResIso_naturality f hf phi)
  unfold schreierCorestrictionOfInjective
  calc
    (rangeMapA ≫ schreierCorestriction f.range A n) ≫
          groupCohomology.map (MonoidHom.id G) phi n =
        rangeMapA ≫
          (schreierCorestriction f.range A n ≫
            groupCohomology.map (MonoidHom.id G) phi n) :=
      Category.assoc _ _ _
    _ = rangeMapA ≫
          (groupCohomology.map (MonoidHom.id f.range) rangePhi n ≫
            schreierCorestriction f.range B n) := by
      rw [schreierCorestriction_naturality]
    _ = (rangeMapA ≫
          groupCohomology.map (MonoidHom.id f.range) rangePhi n) ≫
            schreierCorestriction f.range B n :=
      (Category.assoc _ _ _).symm
    _ = (groupCohomology.map (MonoidHom.id H) sourcePhi n ≫
          rangeMapB) ≫ schreierCorestriction f.range B n := by
      rw [hmap]
    _ = groupCohomology.map (MonoidHom.id H) sourcePhi n ≫
        (rangeMapB ≫ schreierCorestriction f.range B n) :=
      Category.assoc _ _ _

end groupCohomology
