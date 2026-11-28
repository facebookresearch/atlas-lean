/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Mathlib/RepresentationTheory/Homological/Resolution.lean` (Mathlib):
Copyright (c) 2022 Amelia Livingston. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Amelia Livingston
-/

module

public import Mathlib.RepresentationTheory.FiniteIndex
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro

/-!
# Corestriction for subgroups of finite index

Let `k` be a commutative ring, `G` a group, `H ≤ G` a subgroup and `A` a `k`-linear
`G`-representation. This file makes Shapiro's isomorphism
`groupCohomology.coindIso B n : Hⁿ(G, Coind_H^G B) ≅ Hⁿ(H, B)` explicit on inhomogeneous
cochains and uses it to define the corestriction for subgroups of finite index.

## Main results

* `CategoryTheory.ProjectiveResolution.isoExt_inv_comp_isoExt_hom`: for two projective
  resolutions `P`, `Q` of `X` and a chain map `φ : Q ⟶ P` over `𝟙 X`, the comparison
  `Hⁿ(Hom(P, Y)) ≅ Extⁿ(X, Y) ≅ Hⁿ(Hom(Q, Y))` is the map induced by `φ`.
* `groupCohomology.coindIso_hom_eq`: Shapiro's isomorphism is induced by the cochain map
  `x ↦ (h ↦ x(h)(1))`.
* `Rep.resCoindUnit_comp_coindResCounit`: for `H` of finite index, the unit
  `A ⟶ Coind_H^G(Res_H A)` followed by the counit `Coind_H^G(Res_H A) ⟶ A` is `(G : H) • 𝟙 A`.
* `groupCohomology.map_subtype_eq_map_unit_comp_coindIso`: restriction is the map induced by the
  unit followed by Shapiro's isomorphism.
* `groupCohomology.cor`: the corestriction `Hⁿ(H, Res_H A) ⟶ Hⁿ(G, A)`, natural in `A`
  (`groupCohomology.cor_naturality`).
* `groupCohomology.map_subtype_comp_cor`: corestriction after restriction is multiplication by
  the index.
* `groupCohomology.card_smul_eq_zero`: for finite `G`, `|G|` kills `Hⁿ(G, A)` for `n ≥ 1`.
* `groupCohomology.isZero_of_bijective_card_smul`: for finite `G`, if multiplication by `|G|` is
  bijective on `A`, then `Hⁿ(G, A) = 0` for `n ≥ 1`.

## Scope

The corestriction is defined for an abstract group `G` and a subgroup `H` of finite index, with
the counit of `Rep.coindResAdjunction` (which takes a `DecidableRel (QuotientGroup.rightRel H)`
instance; `groupCohomology.map_subtype_comp_cor` holds for every such instance). Not proved here:
that `groupCohomology.cor` is the norm `A^H → A^G` in degree `0`; its independence of the
decidability instance; any statement on Tate cohomology or profinite groups; and the form of
NSW (1.6.2) whose hypothesis is that multiplication by each prime dividing `|G|` is bijective
(here the hypothesis is that multiplication by `|G|` is bijective, and only degrees `n ≥ 1` of
ordinary cohomology are covered).

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic
  edition 2.3: Chapter I, §5, 4. Corestriction, p. 47; Corollary (1.5.7), p. 51;
  Proposition (1.6.2), p. 60; the maps `i`, `ν` and Proposition (1.6.5), pp. 63–64.
* J. S. Milne, *Class Field Theory*, version 4.03: Chapter II, Example 1.29, Proposition 1.30
  and Corollary 1.31, p. 70.
-/

@[expose] public section

universe u

open CategoryTheory Opposite Finsupp

namespace CategoryTheory.ProjectiveResolution

variable {R : Type*} [Ring R] {C : Type*} [Category C] [Abelian C] [Linear R C]
  [EnoughProjectives C]

/-- The cochain map `Hom(P, Y) ⟶ Hom(Q, Y)` given by precomposition with a chain map
`φ : Q ⟶ P`. -/
noncomputable abbrev linearYonedaObjMap {Q P : ChainComplex C ℕ} (φ : Q ⟶ P) (Y : C) :
    P.linearYonedaObj R Y ⟶ Q.linearYonedaObj R Y :=
  (HomologicalComplex.unopFunctor _ _).map
    ((((linearYoneda R C).obj Y).rightOp.mapHomologicalComplex _).map φ).op

/-- Let `P` and `Q` be projective resolutions of `X` and `φ : Q ⟶ P` a chain map lifting
`𝟙 X` in degree `0`. Then the composite `Hⁿ(Hom(P, Y)) ≅ Extⁿ(X, Y) ≅ Hⁿ(Hom(Q, Y))` of the
isomorphisms `ProjectiveResolution.isoExt` is the map induced on cohomology by precomposition
with `φ`. -/
@[reassoc]
theorem isoExt_inv_comp_isoExt_hom {X : C} (P Q : ProjectiveResolution X)
    (φ : Q.complex ⟶ P.complex) (hφ : φ.f 0 ≫ P.π.f 0 = Q.π.f 0) (n : ℕ) (Y : C) :
    (P.isoExt (R := R) n Y).inv ≫ (Q.isoExt n Y).hom =
      HomologicalComplex.homologyMap (linearYonedaObjMap (R := R) φ Y) n := by
  set F := ((linearYoneda R C).obj Y).rightOp
  have h := ProjectiveResolution.isoLeftDerivedObj_hom_naturality (𝟙 X) Q P φ
    (by erw [Category.comp_id]; exact hφ) F n
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  have h2 := HomologicalComplex.homologyOp_hom_naturality (linearYonedaObjMap (R := R) φ Y) n
  apply Quiver.Hom.op_inj
  change (HomologicalComplex.homologyOp (Q.complex.linearYonedaObj R Y) n).inv ≫
    (Q.isoLeftDerivedObj F n).inv ≫ (P.isoLeftDerivedObj F n).hom ≫
    (HomologicalComplex.homologyOp (P.complex.linearYonedaObj R Y) n).hom = _
  have h' : (Q.isoLeftDerivedObj F n).inv ≫ (P.isoLeftDerivedObj F n).hom =
      HomologicalComplex.homologyMap ((HomologicalComplex.opFunctor (ModuleCat R)
        (ComplexShape.up ℕ)).map (linearYonedaObjMap (R := R) φ Y).op) n := by
    rw [h, Iso.inv_hom_id_assoc]
    rfl
  erw [reassoc_of% h', h2, Iso.inv_hom_id_assoc]

end CategoryTheory.ProjectiveResolution

namespace Rep

variable {k : Type u} [CommRing k]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The inverse of `Rep.diagonalSuccIsoFree k G m` sends the basis element `g·(f₀, ..., fₘ₋₁)`
to `(g, g f₀, g f₀ f₁, ..., g f₀ ⋯ fₘ₋₁)`. -/
lemma diagonalSuccIsoFree_inv_hom_single {G : Type u} [Group G] (m : ℕ) (f : Fin m → G) (g : G)
    (r : k) : (diagonalSuccIsoFree k G m).inv.hom (single f (MonoidAlgebra.single g r)) =
      MonoidAlgebra.single (g • Fin.partialProd f) r := by
  simp only [diagonalSuccIsoFree, diagonalSuccIsoTensorTrivial, Iso.trans_inv, Rep.hom_comp,
    Representation.IntertwiningMap.comp_apply]
  have step1 : (Hom.hom (leftRegularTensorTrivialIsoFree k G (Fin m → G)).inv)
      (single f (.single g r)) = .single g 1 ⊗ₜ[k] .single f r :=
    Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single f g r
  rw [step1]
  simp only [mkIso_inv, Representation.linearizeOfMulActionIso, Representation.Equiv.mk_symm,
    LinearEquiv.refl_symm, ConcreteCategory.hom_ofHom, Action.tensorObj_V, Action.trivial_V,
    Functor.mapIso_inv, tensor_V, tensor_ρ, Iso.symm_inv, Functor.Monoidal.μIso_hom, μ_hom,
    MonoidalCategory.tensorIso_inv, Representation.linearizeTrivialIso, hom_tensorHom,
    Representation.IntertwiningMap.tensor_apply, Representation.Equiv.coe_toIntertwiningMap,
    Representation.Equiv.mk_apply, LinearEquiv.refl_apply]
  have key₁ := Representation.linearizeMap_single (k := k)
    (Action.diagonalSuccIsoTensorTrivial G m).inv (g, f) ((1 : k) * r)
  have key₂ := Representation.LinearizeMonoidal.μ_apply_single_single (k := k)
    (X := Action.leftRegular G) (Y := Action.trivial G (Fin m → G)) g f 1 r
  exact ((congrArg (fun z => (Representation.linearizeMap
    (Action.diagonalSuccIsoTensorTrivial G m).inv) z) key₂).trans key₁).trans (by simp)

/-- The augmentation of the bar resolution sends `r • g·()` in degree `0` to `r`. -/
lemma barResolution_π_f_zero_single {G : Type u} [Group G] (x : Fin 0 → G) (g : G) (r : k) :
    ((barResolution k G).π.f 0).hom (single x (MonoidAlgebra.single g r)) = r := by
  change ((diagonalSuccIsoFree k G 0).inv ≫ standardComplex.ε k G).hom
    (single x (MonoidAlgebra.single g r)) = r
  rw [Rep.hom_comp, Representation.IntertwiningMap.comp_apply, diagonalSuccIsoFree_inv_hom_single]
  simp [standardComplex.ε]

namespace barComplex

variable {G : Type u} [Group G] (H : Subgroup G)

/-- In degree `n`, the `H`-equivariant map from the bar complex of `H` to the restriction of the
bar complex of `G`, sending the basis element `(h₁, ..., hₙ)` to `(h₁, ..., hₙ)`. -/
noncomputable def subgroupMap (n : ℕ) :
    free k H (Fin n → H) ⟶ res H.subtype (free k G (Fin n → G)) :=
  freeLift k H _ fun h => single (H.subtype ∘ h) (MonoidAlgebra.single 1 1)

/-- `subgroupMap H n` sends `r • x·(h₁, ..., hₙ)` to `r • x·(h₁, ..., hₙ)`, read in `G`. -/
lemma subgroupMap_single (n : ℕ) (h : Fin n → H) (x : H) (r : k) :
    (subgroupMap (k := k) H n).hom (single h (MonoidAlgebra.single x r)) =
      single (H.subtype ∘ h) (MonoidAlgebra.single (x : G) r) := by
  simp [subgroupMap]

/-- The chain map from the bar complex of a subgroup `H ≤ G` to the restriction to `H` of the bar
complex of `G`, induced by the inclusion `H → G`. -/
noncomputable def subgroupComparison :
    barComplex k H ⟶ ((resFunctor H.subtype).mapHomologicalComplex _).obj (barComplex k G) where
  f n := subgroupMap H n
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    refine free_ext _ _ _ _ _ fun h => ?_
    simp only [Functor.mapHomologicalComplex_obj_d, ChainComplex.of_d, Rep.hom_comp,
      Representation.IntertwiningMap.comp_apply]
    rw [d_single (k := k)]
    simp only [map_add, map_sum]
    erw [subgroupMap_single, d_single (k := k), subgroupMap_single]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    erw [subgroupMap_single]
    congr 1
    exact (Fin.comp_contractNth _ _ (fun _ _ => rfl) j h).symm

/-- The comparison map `subgroupComparison` lies over the identity of the trivial
representation `k`. -/
lemma subgroupComparison_f_zero :
    (subgroupComparison (k := k) H).f 0 ≫
      (((resFunctor H.subtype).mapProjectiveResolution (barResolution k G)).π.f 0) =
      (barResolution k H).π.f 0 := by
  refine free_ext _ _ _ _ _ fun h => ?_
  simp only [ChainComplex.single₀_obj_zero, Functor.mapHomologicalComplex_obj_X,
    subgroupComparison, Functor.mapProjectiveResolution_π, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    ChainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv, Category.comp_id]
  change ((barResolution k G).π.f 0).hom ((subgroupMap H 0).hom
    (single h (MonoidAlgebra.single 1 1))) = _
  rw [subgroupMap_single, barResolution_π_f_zero_single]
  exact (barResolution_π_f_zero_single h 1 1).symm

end barComplex

variable {G : Type u} [Group G] (H : Subgroup G) [H.FiniteIndex]
  [DecidableRel (QuotientGroup.rightRel H)]

/-- Let `H ≤ G` have finite index. The unit `A ⟶ Coind_H^G(Res_H A)`, `a ↦ (g ↦ g a)`, of the
adjunction `Res_H ⊣ Coind_H^G` followed by the counit `Coind_H^G(Res_H A) ⟶ A`,
`x ↦ ∑_{σ ∈ G/H} σ x(σ⁻¹)`, of the adjunction `Coind_H^G ⊣ Res_H` is multiplication by the
index `(G : H)`. -/
theorem resCoindUnit_comp_coindResCounit (A : Rep.{u} k G) :
    (resCoindAdjunction k H.subtype).unit.app A ≫ (coindResAdjunction k H).counit.app A =
      H.index • 𝟙 A := by
  ext a
  simp only [Functor.id_obj, Functor.comp_obj, coindFunctor_obj, Adjunction.mkOfHomEquiv_unit_app,
    LinearEquiv.coe_toEquiv, coindResAdjunction_counit_app, indResAdjunction, indResHomEquiv,
    res_obj_ρ, Adjunction.mkOfHomEquiv_counit_app, indFunctor_obj, LinearEquiv.coe_symm_toEquiv,
    LinearEquiv.symm_mk, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.coe_mk, hom_id,
    Representation.IntertwiningMap.toLinearMap_id, LinearMap.comp_id, hom_comp,
    ConcreteCategory.hom_ofHom, Representation.IntertwiningMap.comp_toLinearMap,
    indCoindIso_inv_hom_toLinearMap, Representation.Equiv.mk, LinearEquiv.toLinearMap_ofLinearMap,
    LinearEquiv.invFun_eq_symm, LinearEquiv.symm_ofLinearMap, LinearEquiv.coe_ofLinearMap,
    LinearMap.coe_comp, Representation.IntertwiningMap.coe_toLinearMap, Function.comp_apply]
  rw [coindToInd_apply, map_sum]
  rw [Finset.sum_congr rfl (g := fun _ => a)]
  · have hc : Nat.card (_root_.Quotient (QuotientGroup.rightRel H)) = H.index := by
      rw [Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H),
        ← Subgroup.index_eq_card]
    simp [Fintype.card_eq_nat_card, hc]
    rfl
  · intro q _
    induction q using Quotient.inductionOn with | h g => ?_
    simp only [Quotient.liftOn_mk]
    simp only [Functor.id_obj, LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
      Representation.Coinvariants.lift_mk, TensorProduct.lift.tmul, LinearEquiv.coe_coe,
      MonoidAlgebra.coeffLinearEquiv_apply, MonoidAlgebra.coeff_single, lift_apply, zero_smul,
      sum_single_index, one_smul]
    change (A.ρ g⁻¹) (A.ρ g a) = a
    simp

end Rep

namespace groupCohomology

open Rep Rep.barComplex

variable {k G : Type u} [CommRing k] [Group G] {H : Subgroup G}

/-- The cochain map `C^•(G, Coind_H^G B) ⟶ C^•(H, B)` sending a cochain `x` to
`(h₁, ..., hₙ) ↦ x(h₁, ..., hₙ)(1)`; it induces Shapiro's isomorphism
(`groupCohomology.coindIso_hom_eq`). -/
noncomputable def coindCochainsMap (B : Rep.{u} k H) :
    inhomogeneousCochains (coind H.subtype B) ⟶ inhomogeneousCochains B :=
  (inhomogeneousCochainsIso (coind H.subtype B)).hom ≫
    (linearYonedaObjResProjectiveResolutionIso (barResolution k G) B).inv ≫
    ProjectiveResolution.linearYonedaObjMap (subgroupComparison H) B ≫
    (inhomogeneousCochainsIso B).inv

/-- On an `n`-cochain `x`, `coindCochainsMap B` evaluates `x(h₁, ..., hₙ) ∈ Coind_H^G B` at
`1`. -/
lemma coindCochainsMap_f_apply (B : Rep.{u} k H) (n : ℕ)
    (x : (Fin n → G) → coind H.subtype B) (h : Fin n → H) :
    ((coindCochainsMap B).f n).hom x h = (x (H.subtype ∘ h)).1 1 := by
  change ((resCoindHomEquiv.{u} H.subtype ((barResolution k G).complex.X n) B).symm
    (freeLift k G (coind H.subtype B) x)).hom
      ((subgroupMap H n).hom (single h (MonoidAlgebra.single 1 1))) = _
  rw [subgroupMap_single]
  change ((freeLift k G (coind H.subtype B) x).hom
    (single (H.subtype ∘ h) (MonoidAlgebra.single 1 1))).1 1 = _
  simp

/-- Shapiro's isomorphism `Hⁿ(G, Coind_H^G B) ≅ Hⁿ(H, B)` of Mathlib is the map induced on
cohomology by the cochain map `coindCochainsMap B`, `x ↦ (h ↦ x(h)(1))`. -/
theorem coindIso_hom_eq (B : Rep.{u} k H) (n : ℕ) :
    (coindIso B n).hom = HomologicalComplex.homologyMap (coindCochainsMap B) n := by
  simp only [coindIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, groupCohomologyIso,
    groupCohomologyIsoExt, Iso.trans_inv, Iso.symm_inv]
  have hq : (isoOfQuasiIsoAt (HomotopyEquiv.ofIso (inhomogeneousCochainsIso B)).hom n).inv =
      HomologicalComplex.homologyMap (inhomogeneousCochainsIso B).inv n := by
    rw [← cancel_epi (isoOfQuasiIsoAt (HomotopyEquiv.ofIso (inhomogeneousCochainsIso B)).hom n).hom,
      Iso.hom_inv_id, isoOfQuasiIsoAt_hom, ← HomologicalComplex.homologyMap_comp]
    simp [HomotopyEquiv.ofIso]
  have hL := ProjectiveResolution.isoExt_inv_comp_isoExt_hom (R := k)
    ((resFunctor H.subtype).mapProjectiveResolution (barResolution k G)) (barResolution k H)
    (subgroupComparison (k := k) H) (subgroupComparison_f_zero H) n B
  rw [hq, barResolution.extIso]
  erw [reassoc_of% hL]
  simp only [HomologicalComplex.homologyFunctor_map]
  have e : (inhomogeneousCochainsIso (coind H.subtype B) ≪≫
      (linearYonedaObjResProjectiveResolutionIso (barResolution k G) B).symm).hom ≫
      ProjectiveResolution.linearYonedaObjMap (subgroupComparison H) B ≫
      (inhomogeneousCochainsIso B).inv = coindCochainsMap B := rfl
  rw [← e, HomologicalComplex.homologyMap_comp]
  congr 1
  exact (HomologicalComplex.homologyMap_comp _ _ _).symm

/-- Restriction through Shapiro's lemma: for a subgroup `H ≤ G` and a `G`-representation `A`,
the restriction `Hⁿ(G, A) ⟶ Hⁿ(H, Res_H A)` (`groupCohomology.map H.subtype (𝟙 _) n`) is the map
induced by the unit `A ⟶ Coind_H^G(Res_H A)`, `a ↦ (g ↦ g a)`, of `Res_H ⊣ Coind_H^G`,
followed by Shapiro's isomorphism `groupCohomology.coindIso (Res_H A) n`. Holds for every
`n` and every subgroup `H`. -/
theorem map_subtype_eq_map_unit_comp_coindIso (A : Rep.{u} k G) (n : ℕ) :
    map H.subtype (𝟙 (res H.subtype A)) n =
      map (MonoidHom.id G) ((resCoindAdjunction k H.subtype).unit.app A) n ≫
        (coindIso (res H.subtype A) n).hom := by
  rw [coindIso_hom_eq, map, map, ← HomologicalComplex.homologyMap_comp]
  congr 1
  ext m x h
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    cochainsMap_f_hom]
  erw [coindCochainsMap_f_apply]
  simp only [Rep.hom_id, res_obj_ρ, Representation.IntertwiningMap.toLinearMap_id,
    Subgroup.coe_subtype, LinearMap.compLeft_apply, LinearMap.id_coe, Function.comp_apply,
    LinearMap.funLeft_apply, id_eq, Functor.comp_obj, coindFunctor_obj,
    Adjunction.mkOfHomEquiv_unit_app, LinearEquiv.coe_toEquiv, MonoidHom.coe_id,
    CompTriple.comp_eq, Representation.IntertwiningMap.coe_toLinearMap]
  symm
  change (A.ρ 1) (x (Subtype.val ∘ h)) = _
  simp

/-- Shapiro's isomorphism is natural in the `H`-representation `B`. -/
theorem coindIso_hom_naturality {B B' : Rep.{u} k H} (f : B ⟶ B') (n : ℕ) :
    map (MonoidHom.id G) (coindMap H.subtype f) n ≫ (coindIso B' n).hom =
      (coindIso B n).hom ≫ map (MonoidHom.id H) f n := by
  rw [coindIso_hom_eq, coindIso_hom_eq, map, map, ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp]
  congr 1
  ext m x h
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    cochainsMap_f_hom]
  erw [coindCochainsMap_f_apply]
  change _ = f.hom (((coindCochainsMap B).f m).hom x h)
  erw [coindCochainsMap_f_apply]
  rfl

/-- The map induced on `Hⁿ(G, -)` by `m • 𝟙 A` is multiplication by `m`. -/
theorem map_id_nsmul (A : Rep.{u} k G) (m n : ℕ) :
    map (MonoidHom.id G) (m • 𝟙 A) n = m • 𝟙 (groupCohomology A n) := by
  change (HomologicalComplex.homologyFunctor _ _ n).map ((cochainsFunctor k G).map (m • 𝟙 A)) = _
  rw [Functor.map_nsmul, Functor.map_nsmul]
  erw [CategoryTheory.Functor.map_id]
  rfl

variable [H.FiniteIndex] [DecidableRel (QuotientGroup.rightRel H)]

variable (H) in
/-- The corestriction `Hⁿ(H, Res_H A) ⟶ Hⁿ(G, A)` for a subgroup `H ≤ G` of finite index: the
inverse of Shapiro's isomorphism `Hⁿ(G, Coind_H^G(Res_H A)) ≅ Hⁿ(H, Res_H A)` followed by the
map induced by the counit `Coind_H^G(Res_H A) ⟶ A`, `x ↦ ∑_{σ ∈ G/H} σ x(σ⁻¹)`, of
`Coind_H^G ⊣ Res_H` (`Rep.coindResAdjunction`). It is a morphism of `k`-modules, hence
`k`-linear. -/
noncomputable def cor (A : Rep.{u} k G) (n : ℕ) :
    groupCohomology (res H.subtype A) n ⟶ groupCohomology A n :=
  (coindIso (res H.subtype A) n).inv ≫
    map (MonoidHom.id G) ((coindResAdjunction k H).counit.app A) n

/-- The corestriction is natural in the `G`-representation `A`. -/
theorem cor_naturality {A A' : Rep.{u} k G} (f : A ⟶ A') (n : ℕ) :
    map (MonoidHom.id H) ((resFunctor H.subtype).map f) n ≫ cor H A' n =
      cor H A n ≫ map (MonoidHom.id G) f n := by
  have hn := coindIso_hom_naturality (G := G) ((resFunctor H.subtype).map f) n
  have hn' : map (MonoidHom.id H) ((resFunctor H.subtype).map f) n ≫
      (coindIso (res H.subtype A') n).inv = (coindIso (res H.subtype A) n).inv ≫
        map (MonoidHom.id G) (coindMap H.subtype ((resFunctor H.subtype).map f)) n := by
    rw [Iso.eq_inv_comp, ← reassoc_of% hn, Iso.hom_inv_id, Category.comp_id]
  simp only [cor]
  rw [reassoc_of% hn', Category.assoc, ← map_id_comp, ← map_id_comp]
  congr 2
  exact (coindResAdjunction k H).counit_naturality f

variable (H) in
/-- Corestriction after restriction is multiplication by the index: for a subgroup `H ≤ G` of
finite index and every `n`, `cor ∘ res = (G : H) • 𝟙` on `Hⁿ(G, A)`. -/
theorem map_subtype_comp_cor (A : Rep.{u} k G) (n : ℕ) :
    map H.subtype (𝟙 (res H.subtype A)) n ≫ cor H A n = H.index • 𝟙 (groupCohomology A n) := by
  rw [map_subtype_eq_map_unit_comp_coindIso, cor, Category.assoc, Iso.hom_inv_id_assoc,
    ← map_id_comp, Rep.resCoindUnit_comp_coindResCounit, map_id_nsmul]

omit [H.FiniteIndex] [DecidableRel (QuotientGroup.rightRel H)]

/-- For a finite group `G`, multiplication by `|G|` is zero on `Hⁿ⁺¹(G, A)`. -/
theorem card_smul_eq_zero [Finite G] (A : Rep.{u} k G) (n : ℕ) :
    Nat.card G • 𝟙 (groupCohomology A (n + 1)) = 0 := by
  classical
  rw [← Subgroup.index_bot, ← map_subtype_comp_cor (⊥ : Subgroup G),
    (isZero_groupCohomology_succ_of_subsingleton (G := ↥(⊥ : Subgroup G))
      (Rep.res (⊥ : Subgroup G).subtype A) n).eq_zero_of_tgt
      (map (⊥ : Subgroup G).subtype (𝟙 _) (n + 1)), Limits.zero_comp]

/-- For a finite group `G`, every class in `Hⁿ⁺¹(G, A)` is killed by `|G|`. -/
theorem card_smul_apply_eq_zero [Finite G] (A : Rep.{u} k G) (n : ℕ)
    (x : groupCohomology A (n + 1)) : Nat.card G • x = 0 := by
  have := congrArg (fun f => f.hom x) (card_smul_eq_zero A n)
  simpa using this

/-- For a finite group `G`, if multiplication by `|G|` is bijective on `A`, then
`Hⁿ⁺¹(G, A) = 0`. -/
theorem isZero_of_bijective_card_smul [Finite G] (A : Rep.{u} k G)
    (h : Function.Bijective (fun a : A => Nat.card G • a)) (n : ℕ) :
    Limits.IsZero (groupCohomology A (n + 1)) := by
  have : IsIso (Nat.card G • 𝟙 A) := (ConcreteCategory.isIso_iff_bijective _).mpr h
  have hi : IsIso (Nat.card G • 𝟙 (groupCohomology A (n + 1))) := by
    rw [← map_id_nsmul]
    change IsIso ((functor k G (n + 1)).map _)
    infer_instance
  rw [card_smul_eq_zero] at hi
  have e := @IsIso.hom_inv_id _ _ _ _ _ hi
  rw [Limits.zero_comp] at e
  exact (Limits.IsZero.iff_id_eq_zero _).2 e.symm

end groupCohomology
