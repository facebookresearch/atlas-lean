/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Algebra.Homology.CochainGradedPairingHomologyLaws
public import MathlibExt.Algebra.Homology.HomologyDegreeTransport
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupProductNaturality
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.Homology

/-!
# Target-normalized cups with left degree one

This file packages the arbitrary cup with a degree-one left input and
normalizes its output degree from `1 + q` to `q + 1`.  It also records joint
group-and-coefficient naturality and the formula on cycle representatives.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- The arbitrary cup with left degree one, with its target degree
normalized from `1 + q` to `q + 1`. -/
noncomputable def cupOneAny
    (A B : Rep k G) (q : ℕ) :
    groupCohomology A 1 ⊗ groupCohomology B q ⟶
      groupCohomology (A ⊗ B) (q + 1) :=
  cup G k A B 1 q ≫
    ((inhomogeneousCochains (A ⊗ B)).homologyIsoOfEq
      (Nat.one_add q)).hom

/-- Cup on the left by a fixed degree-one class, followed by an arbitrary
coefficient pairing. -/
noncomputable def cupOneClassMap
    {A B C : Rep k G} (x : groupCohomology A 1)
    (mu : A ⊗ B ⟶ C) (q : ℕ) :
    groupCohomology B q ⟶ groupCohomology C (q + 1) :=
  ModuleCat.ofHom
      ((TensorProduct.mk k
        (groupCohomology A 1) (groupCohomology B q)) x) ≫
    cupOneAny A B q ≫
    map (MonoidHom.id G) mu (q + 1)

@[simp]
theorem cupOneClassMap_apply
    {A B C : Rep k G} (x : groupCohomology A 1)
    (mu : A ⊗ B ⟶ C) (q : ℕ) (y : groupCohomology B q) :
    (cupOneClassMap x mu q).hom y =
      (map (MonoidHom.id G) mu (q + 1)).hom
        ((cupOneAny A B q).hom (x ⊗ₜ[k] y)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Joint group-and-coefficient naturality of the target-normalized
`(1,q)` cup. -/
theorem cupOneAny_naturality_of_hom
    {J : Type u} [Group J]
    {A B : Rep k G} {A' B' : Rep k J}
    (f : J →* G) (phi : Rep.res f A ⟶ A')
    (psi : Rep.res f B ⟶ B') (q : ℕ) :
    cupOneAny A B q ≫
        map f ((Rep.resTensorIso f A B).inv ≫ (phi ⊗ₘ psi)) (q + 1) =
      (map f phi 1 ⊗ₘ map f psi q) ≫ cupOneAny A' B' q := by
  let coeff := (Rep.resTensorIso f A B).inv ≫ (phi ⊗ₘ psi)
  have hcast := HomologicalComplex.homologyIsoOfEq_hom_naturality
    (cochainsMap f coeff) (Nat.one_add q)
  unfold cupOneAny
  rw [Category.assoc]
  rw [← hcast]
  rw [← Category.assoc]
  rw [cup_naturality_of_hom f phi psi 1 q]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Coefficient naturality of the target-normalized `(1,q)` cup. -/
theorem cupOneAny_naturality
    {A B A' B' : Rep k G} (phi : A ⟶ A') (psi : B ⟶ B')
    (q : ℕ) :
    cupOneAny A B q ≫
        map (MonoidHom.id G) (phi ⊗ₘ psi) (q + 1) =
      (map (MonoidHom.id G) phi 1 ⊗ₘ
        map (MonoidHom.id G) psi q) ≫ cupOneAny A' B' q := by
  let coeff := (Rep.resTensorIso (MonoidHom.id G) A B).inv ≫
    (phi ⊗ₘ psi)
  have hmap : map (MonoidHom.id G) coeff (q + 1) =
      map (MonoidHom.id G) (phi ⊗ₘ psi) (q + 1) := by
    apply map_congr rfl
    rfl
  rw [← hmap]
  exact cupOneAny_naturality_of_hom
    (f := MonoidHom.id G) phi psi q

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Simultaneous coefficient naturality of cup on the left by a fixed
degree-one class. -/
theorem cupOneClassMap_naturality
    {A B C A' B' C' : Rep k G}
    (x : groupCohomology A 1)
    (mu : A ⊗ B ⟶ C) (mu' : A' ⊗ B' ⟶ C')
    (phi : A ⟶ A') (psi : B ⟶ B') (omega : C ⟶ C')
    (hmu : (phi ⊗ₘ psi) ≫ mu' = mu ≫ omega)
    (q : ℕ) :
    cupOneClassMap x mu q ≫
        map (MonoidHom.id G) omega (q + 1) =
      map (MonoidHom.id G) psi q ≫
        cupOneClassMap
          ((map (MonoidHom.id G) phi 1).hom x) mu' q := by
  let i := ModuleCat.ofHom
    ((TensorProduct.mk k
      (groupCohomology A 1) (groupCohomology B q)) x)
  let i' := ModuleCat.ofHom
    ((TensorProduct.mk k
      (groupCohomology A' 1) (groupCohomology B' q))
        ((map (MonoidHom.id G) phi 1).hom x))
  let hphi := map (MonoidHom.id G) phi 1
  let hpsi := map (MonoidHom.id G) psi q
  have hi : i ≫ (hphi ⊗ₘ hpsi) = hpsi ≫ i' := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    rfl
  change (i ≫ cupOneAny A B q ≫ map (MonoidHom.id G) mu (q + 1)) ≫
      map (MonoidHom.id G) omega (q + 1) =
    hpsi ≫
      (i' ≫ cupOneAny A' B' q ≫
        map (MonoidHom.id G) mu' (q + 1))
  calc
    (i ≫ cupOneAny A B q ≫ map (MonoidHom.id G) mu (q + 1)) ≫
          map (MonoidHom.id G) omega (q + 1) =
      i ≫ cupOneAny A B q ≫
        map (MonoidHom.id G) (mu ≫ omega) (q + 1) := by
          rw [Category.assoc, Category.assoc, ← map_id_comp]
    _ = i ≫ cupOneAny A B q ≫
        map (MonoidHom.id G) ((phi ⊗ₘ psi) ≫ mu') (q + 1) := by
          rw [hmu]
    _ = i ≫ cupOneAny A B q ≫
        (map (MonoidHom.id G) (phi ⊗ₘ psi) (q + 1) ≫
          map (MonoidHom.id G) mu' (q + 1)) := by
            rw [map_id_comp]
    _ = i ≫
        ((map (MonoidHom.id G) phi 1 ⊗ₘ
          map (MonoidHom.id G) psi q) ≫ cupOneAny A' B' q) ≫
        map (MonoidHom.id G) mu' (q + 1) := by
          rw [← cupOneAny_naturality phi psi q]
          simp only [Category.assoc]
    _ = (i ≫ (hphi ⊗ₘ hpsi)) ≫ cupOneAny A' B' q ≫
        map (MonoidHom.id G) mu' (q + 1) := by
          rfl
    _ = (hpsi ≫ i') ≫ cupOneAny A' B' q ≫
        map (MonoidHom.id G) mu' (q + 1) := by rw [hi]
    _ = hpsi ≫
        (i' ≫ cupOneAny A' B' q ≫
          map (MonoidHom.id G) mu' (q + 1)) := by
            simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Mapping the tensor-unit coefficient of a fixed left class through
`phi` turns the left-unitor cup into the cup valued in `A' ⊗ B`. -/
theorem cupOneClassMap_leftUnitor_naturality
    {A' B : Rep k G}
    (x : groupCohomology (𝟙_ (Rep k G)) 1)
    (phi : 𝟙_ (Rep k G) ⟶ A') (q : ℕ) :
    cupOneClassMap x (λ_ B).hom q ≫
        map (MonoidHom.id G)
          ((λ_ B).inv ≫ (phi ⊗ₘ 𝟙 B)) (q + 1) =
      cupOneClassMap
        ((map (MonoidHom.id G) phi 1).hom x)
        (𝟙 (A' ⊗ B)) q := by
  have hmu : (phi ⊗ₘ 𝟙 B) ≫ 𝟙 (A' ⊗ B) =
      (λ_ B).hom ≫ ((λ_ B).inv ≫ (phi ⊗ₘ 𝟙 B)) := by
    simp
  have h := cupOneClassMap_naturality
    x (λ_ B).hom (𝟙 (A' ⊗ B)) phi (𝟙 B)
      ((λ_ B).inv ≫ (phi ⊗ₘ 𝟙 B)) hmu q
  rw [map_id, Category.id_comp] at h
  exact h

set_option backward.isDefEq.respectTransparency.types false in
/-- In bidegree `(1,1)`, target normalization is the identity. -/
theorem cupOneAny_one_eq (A B : Rep k G) :
    cupOneAny A B 1 = cup G k A B 1 1 := by
  unfold cupOneAny
  rw [show Nat.one_add 1 = (rfl : 1 + 1 = 1 + 1) from
    Subsingleton.elim _ _]
  change cup G k A B 1 1 ≫ 𝟙 _ = _
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Representative formula for the target-normalized `(1,q)` cup. -/
theorem cupOneAny_π_apply
    (A B : Rep k G) (q : ℕ)
    (x : cocycles A 1) (y : cocycles B q) :
    cupOneAny A B q
        (π A 1 x ⊗ₜ[k] π B q y) =
      π (A ⊗ B) (q + 1)
        (((inhomogeneousCochains (A ⊗ B)).cyclesIsoOfEq
          (Nat.one_add q)).hom.hom
          (((inhomogeneousCupPairing G k A B).pairCycles 1 q).hom
            (x ⊗ₜ[k] y))) := by
  rw [cupOneAny]
  change (((cup G k A B 1 q ≫
      ((inhomogeneousCochains (A ⊗ B)).homologyIsoOfEq
        (Nat.one_add q)).hom).hom)
      (π A 1 x ⊗ₜ[k] π B q y) = _)
  unfold cup
  change (((inhomogeneousCochains (A ⊗ B)).homologyIsoOfEq
      (Nat.one_add q)).hom.hom
        (((inhomogeneousCupPairing G k A B).pairHomology 1 q).hom
          (((inhomogeneousCochains A).homologyπ 1).hom x ⊗ₜ[k]
            ((inhomogeneousCochains B).homologyπ q).hom y))) = _
  rw [HomologicalComplex.CochainGradedPairing.pairHomology_π_apply]
  have h := ConcreteCategory.congr_hom
    ((inhomogeneousCochains (A ⊗ B)
      ).homologyπ_comp_homologyIsoOfEq_hom (Nat.one_add q))
    (((inhomogeneousCupPairing G k A B).pairCycles 1 q).hom
      (x ⊗ₜ[k] y))
  change _ = ((inhomogeneousCochains (A ⊗ B)).homologyπ (q + 1)).hom
    (((inhomogeneousCochains (A ⊗ B)).cyclesIsoOfEq
      (Nat.one_add q)).hom.hom
      (((inhomogeneousCupPairing G k A B).pairCycles 1 q).hom
        (x ⊗ₜ[k] y)))
  simpa only [ConcreteCategory.comp_apply] using h

end groupCohomology
