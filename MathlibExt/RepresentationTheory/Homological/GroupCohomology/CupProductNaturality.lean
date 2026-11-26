/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupProduct
public import MathlibExt.RepresentationTheory.Rep.ResTensor

/-!
# Coefficient naturality of arbitrary-degree group-cohomology cups

The Alexander--Whitney cup pairing is natural in both coefficient
representations.  This file proves naturality first for the comparison
between inhomogeneous and bar cochains, then for bar and inhomogeneous cup
pairings, and finally for the induced cup on group cohomology.

## Main declarations

* `groupCohomology.inhomogeneousCochainsIso_hom_naturality`
* `groupCohomology.inhomogeneousCochainsIso_inv_naturality`
* `groupCohomology.barCochainCupPairing_naturality`
* `groupCohomology.inhomogeneousCupPairing_naturality`
* `groupCohomology.cup_naturality`
* `groupCohomology.inhomogeneousCupPairing_naturality_of_hom`
* `groupCohomology.cup_naturality_of_hom`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Opposite
open HomologicalComplex

universe u

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G]

@[simp]
private lemma moduleHom_comp_apply {A B C : ModuleCat k}
    (a : A ⟶ B) (b : B ⟶ C) (x : A) :
    (a ≫ b).hom x = b.hom (a.hom x) :=
  rfl

private lemma cochainsMap_id_apply
    {A B : Rep k G} (f : A ⟶ B) (n : ℕ)
    (phi : (Fin n → G) → A) (x : Fin n → G) :
    ((cochainsMap (MonoidHom.id G) f).f n).hom phi x = f.hom (phi x) :=
  rfl

private lemma cochainsMap_restricted_apply
    {G H : Type u} [Group G] [Group H] {A : Rep k H} {B : Rep k G}
    (f : G →* H) (phi : Rep.res f A ⟶ B) (n : ℕ)
    (a : (Fin n → H) → A) (g : Fin n → G) :
    ((cochainsMap f phi).f n).hom a g = phi.hom (a (fun i => f (g i))) :=
  rfl

private lemma coefficientTensorMap_tmul {A B C D : ModuleCat k}
    (f : A ⟶ B) (g : C ⟶ D) (a : A) (b : C) :
    (f ⊗ₘ g).hom (a ⊗ₜ[k] b) = f.hom a ⊗ₜ[k] g.hom b :=
  rfl

private lemma coefficientMap_apply_basis
    {A B : Rep k G} (f : A ⟶ B) (n : ℕ)
    (phi : Rep.free k G (Fin n → G) ⟶ A) (x : Fin n → G) :
    (((((linearHomCochainComplexBifunctor k (Rep k G)).map f).app
      (op (Rep.barComplex k G))).f n).hom phi).hom
        (Finsupp.single x (MonoidAlgebra.single 1 1)) =
      f.hom (phi.hom (Finsupp.single x (MonoidAlgebra.single 1 1))) :=
  rfl

/-- The comparison from inhomogeneous cochains to bar linear-Yoneda
cochains is natural in the coefficient representation. -/
theorem inhomogeneousCochainsIso_hom_naturality
    {A B : Rep k G} (f : A ⟶ B) :
    cochainsMap (MonoidHom.id G) f ≫ (inhomogeneousCochainsIso B).hom =
      (inhomogeneousCochainsIso A).hom ≫
        (((linearHomCochainComplexBifunctor k (Rep k G)).map f).app
          (op (Rep.barComplex k G))) := by
  set_option backward.isDefEq.respectTransparency false in
  ext n phi
  apply Rep.free_ext
  intro x
  simp only [HomologicalComplex.comp_f]
  rw [moduleHom_comp_apply, moduleHom_comp_apply]
  have hIsoB :
      (((inhomogeneousCochainsIso B).hom.f n).hom
        (((cochainsMap (MonoidHom.id G) f).f n).hom phi)).hom
          (Finsupp.single x (MonoidAlgebra.single 1 1)) =
        ((cochainsMap (MonoidHom.id G) f).f n).hom phi x := by
    simpa using inhomogeneousCochainsIso_hom_apply_single_single G k B n
      (((cochainsMap (MonoidHom.id G) f).f n).hom phi) x 1 1
  rw [hIsoB, cochainsMap_id_apply]
  let phiBar : Rep.free k G (Fin n → G) ⟶ A :=
    ((inhomogeneousCochainsIso A).hom.f n).hom phi
  have hIso : phiBar.hom
      (Finsupp.single x (MonoidAlgebra.single 1 1)) = phi x := by
    simpa using (inhomogeneousCochainsIso_hom_apply_single_single
      G k A n phi x 1 1)
  have hCoeff := coefficientMap_apply_basis f n phiBar x
  exact (congrArg f.hom hIso.symm).trans hCoeff.symm

/-- Inverse orientation of coefficient naturality for the inhomogeneous/bar
comparison. -/
theorem inhomogeneousCochainsIso_inv_naturality
    {A B : Rep k G} (f : A ⟶ B) :
    (inhomogeneousCochainsIso A).inv ≫
        cochainsMap (MonoidHom.id G) f =
      (((linearHomCochainComplexBifunctor k (Rep k G)).map f).app
          (op (Rep.barComplex k G))) ≫
        (inhomogeneousCochainsIso B).inv := by
  set_option backward.isDefEq.respectTransparency false in
  rw [← cancel_mono (inhomogeneousCochainsIso B).hom]
  simp only [Category.assoc]
  rw [inhomogeneousCochainsIso_hom_naturality f]
  simp

/-- Coefficient naturality of the arbitrary-degree bar cup pairing. -/
theorem barCochainCupPairing_naturality
    {A B A' B' : Rep k G} (f : A ⟶ A') (g : B ⟶ B')
    (p q : ℕ) :
    (barCochainCupPairing G k A B).pair p q ≫
        (((linearHomCochainComplexBifunctor k (Rep k G)).map (f ⊗ₘ g)).app
          (op (Rep.barComplex k G))).f (p + q) =
      (((((linearHomCochainComplexBifunctor k (Rep k G)).map f).app
          (op (Rep.barComplex k G))).f p) ⊗ₘ
        ((((linearHomCochainComplexBifunctor k (Rep k G)).map g).app
          (op (Rep.barComplex k G))).f q)) ≫
        (barCochainCupPairing G k A' B').pair p q := by
  apply linearYonedaCochainGradedPairing_coefficient_naturality
  simp

/-- Coefficient naturality of the arbitrary-degree inhomogeneous cup
pairing. -/
theorem inhomogeneousCupPairing_naturality
    {A B A' B' : Rep k G} (f : A ⟶ A') (g : B ⟶ B')
    (p q : ℕ) :
    (inhomogeneousCupPairing G k A B).pair p q ≫
        (cochainsMap (MonoidHom.id G) (f ⊗ₘ g)).f (p + q) =
      ((cochainsMap (MonoidHom.id G) f).f p ⊗ₘ
        (cochainsMap (MonoidHom.id G) g).f q) ≫
        (inhomogeneousCupPairing G k A' B').pair p q := by
  set_option backward.isDefEq.respectTransparency false in
  rw [inhomogeneousCupPairing, inhomogeneousCupPairing]
  simp only [HomologicalComplex.CochainGradedPairing.whisker_pair]
  have hout :
      (inhomogeneousCochainsIso (A ⊗ B)).inv.f (p + q) ≫
          (cochainsMap (MonoidHom.id G) (f ⊗ₘ g)).f (p + q) =
        ((((linearHomCochainComplexBifunctor k (Rep k G)).map
          (f ⊗ₘ g)).app (op (Rep.barComplex k G))).f (p + q)) ≫
          (inhomogeneousCochainsIso (A' ⊗ B')).inv.f (p + q) := by
    simpa only [HomologicalComplex.comp_f] using congrArg
      (fun h => h.f (p + q))
      (inhomogeneousCochainsIso_inv_naturality (f ⊗ₘ g))
  have hA :
      (cochainsMap (MonoidHom.id G) f).f p ≫
          (inhomogeneousCochainsIso A').hom.f p =
        (inhomogeneousCochainsIso A).hom.f p ≫
          (((linearHomCochainComplexBifunctor k (Rep k G)).map f).app
            (op (Rep.barComplex k G))).f p := by
    simpa only [HomologicalComplex.comp_f] using congrArg (fun h => h.f p)
      (inhomogeneousCochainsIso_hom_naturality f)
  have hB :
      (cochainsMap (MonoidHom.id G) g).f q ≫
          (inhomogeneousCochainsIso B').hom.f q =
        (inhomogeneousCochainsIso B).hom.f q ≫
          (((linearHomCochainComplexBifunctor k (Rep k G)).map g).app
            (op (Rep.barComplex k G))).f q := by
    simpa only [HomologicalComplex.comp_f] using congrArg (fun h => h.f q)
      (inhomogeneousCochainsIso_hom_naturality g)
  simp only [Category.assoc]
  rw [hout]
  rw [← Category.assoc ((barCochainCupPairing G k A B).pair p q)]
  rw [barCochainCupPairing_naturality f g p q]
  let barF := (((linearHomCochainComplexBifunctor k (Rep k G)).map f).app
    (op (Rep.barComplex k G))).f p
  let barG := (((linearHomCochainComplexBifunctor k (Rep k G)).map g).app
    (op (Rep.barComplex k G))).f q
  let coF := (cochainsMap (MonoidHom.id G) f).f p
  let coG := (cochainsMap (MonoidHom.id G) g).f q
  let isoA := (inhomogeneousCochainsIso A).hom.f p
  let isoB := (inhomogeneousCochainsIso B).hom.f q
  let isoA' := (inhomogeneousCochainsIso A').hom.f p
  let isoB' := (inhomogeneousCochainsIso B').hom.f q
  have hTensorNat :
      (isoA ⊗ₘ isoB) ≫ (barF ⊗ₘ barG) =
        (coF ⊗ₘ coG) ≫ (isoA' ⊗ₘ isoB') := by
    dsimp only [barF, barG, coF, coG, isoA, isoB, isoA', isoB']
    rw [MonoidalCategory.tensorHom_comp_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom, hA, hB]
  simpa only [Category.assoc] using congrArg
    (fun h => h ≫ (barCochainCupPairing G k A' B').pair p q ≫
      (inhomogeneousCochainsIso (A' ⊗ B')).inv.f (p + q)) hTensorNat

/-- Coefficient naturality of the arbitrary-degree cup product on group
cohomology. -/
theorem cup_naturality
    {A B A' B' : Rep k G} (f : A ⟶ A') (g : B ⟶ B')
    (p q : ℕ) :
    cup G k A B p q ≫
        map (MonoidHom.id G) (f ⊗ₘ g) (p + q) =
      (map (MonoidHom.id G) f p ⊗ₘ
        map (MonoidHom.id G) g q) ≫ cup G k A' B' p q := by
  symm
  apply HomologicalComplex.CochainGradedPairing.pairHomology_naturality
    (inhomogeneousCupPairing G k A B)
    (inhomogeneousCupPairing G k A' B')
    (cochainsMap (MonoidHom.id G) f)
    (cochainsMap (MonoidHom.id G) g)
    (cochainsMap (MonoidHom.id G) (f ⊗ₘ g))
  intro i j
  exact inhomogeneousCupPairing_naturality f g i j

/-- A monoid homomorphism commutes with every finite partial product. -/
theorem map_partialProd {G H : Type u} [Group G] [Group H]
    (f : G →* H) {n : ℕ} (x : Fin n → G) (i : Fin (n + 1)) :
    f (Fin.partialProd x i) =
      Fin.partialProd (fun j => f (x j)) i := by
  simp [Fin.partialProd, List.ofFn_comp', map_list_prod]

set_option backward.isDefEq.respectTransparency false in
/-- Joint group-and-coefficient naturality of the arbitrary-degree
inhomogeneous cup pairing. -/
theorem inhomogeneousCupPairing_naturality_of_hom
    {G H : Type u} [Group G] [Group H]
    {A B : Rep k H} {A' B' : Rep k G}
    (f : G →* H) (phi : Rep.res f A ⟶ A') (psi : Rep.res f B ⟶ B')
    (p q : ℕ) :
    (inhomogeneousCupPairing H k A B).pair p q ≫
        (cochainsMap f
          ((Rep.resTensorIso f A B).inv ≫ (phi ⊗ₘ psi))).f (p + q) =
      ((cochainsMap f phi).f p ⊗ₘ (cochainsMap f psi).f q) ≫
        (inhomogeneousCupPairing G k A' B').pair p q := by
  have hcoef (a : A) (b : B) :
      ((Rep.resTensorIso f A B).inv ≫ (phi ⊗ₘ psi)).hom (a ⊗ₜ[k] b) =
        phi.hom a ⊗ₜ[k] psi.hom b := by
    rfl
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
      apply inhomogeneousCochains.ext
      intro g
      rw [moduleHom_comp_apply, moduleHom_comp_apply,
        coefficientTensorMap_tmul, cochainsMap_restricted_apply]
      rw [inhomogeneousCupPairing_apply, inhomogeneousCupPairing_apply]
      rw [hcoef]
      simp only [cochainsMap_restricted_apply]
      congr 1
      rw [← map_partialProd]
      simpa using Rep.hom_comm_apply psi
        (Fin.partialProd g (Fin.natAdd p (0 : Fin (q + 1))))
        (y (fun i => f (g (Fin.natAdd p i))))
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-- Joint group-and-coefficient naturality of the arbitrary-degree cup on
group cohomology. -/
theorem cup_naturality_of_hom
    {G H : Type u} [Group G] [Group H]
    {A B : Rep k H} {A' B' : Rep k G}
    (f : G →* H) (phi : Rep.res f A ⟶ A') (psi : Rep.res f B ⟶ B')
    (p q : ℕ) :
    cup H k A B p q ≫
        map f ((Rep.resTensorIso f A B).inv ≫ (phi ⊗ₘ psi)) (p + q) =
      (map f phi p ⊗ₘ map f psi q) ≫ cup G k A' B' p q := by
  symm
  apply HomologicalComplex.CochainGradedPairing.pairHomology_naturality
    (inhomogeneousCupPairing H k A B)
    (inhomogeneousCupPairing G k A' B')
    (cochainsMap f phi)
    (cochainsMap f psi)
    (cochainsMap f ((Rep.resTensorIso f A B).inv ≫ (phi ⊗ₘ psi)))
  intro i j
  exact inhomogeneousCupPairing_naturality_of_hom f phi psi i j

end groupCohomology
