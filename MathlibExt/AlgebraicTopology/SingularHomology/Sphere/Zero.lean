/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.CategoryTheory.Preadditive.SignedDiagonal
public import MathlibExt.Topology.Sphere.StandardCover
public import MathlibExt.AlgebraicTopology.SingularHomology.Reduced

/-!
# Degree-zero singular homology of the zero-sphere

This file provides the ordinary and reduced degree-zero singular homology of
the zero-sphere `S⁰` with the identifications `H₀(S⁰; R) ≅ R ⊕ R` and
`H̃₀(S⁰; R) ≅ R`, orientation normalization, and the antipodal action laws.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicTopology

namespace AlgebraicTopology

universe w u v

section Ordinary

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]
  [HasCoproducts.{0} C] [Preadditive C] [CategoryWithHomology C]

attribute [local instance] HasBinaryBiproducts.of_hasBinaryCoproducts

/-- Reindexes the `S⁰` zeroth-homotopy coproduct along `sphereZeroPi0Equiv`, with `Bool`
  orientation inherited from that equivalence. -/
noncomputable def sphereZeroPi0CoproductIso (R : C) :
    (∐ fun _ : ZerothHomotopy ↥(TopCat.sphere.{w} 0) => R) ≅ (∐ fun _ : Bool => R) :=
  Sigma.whiskerEquiv sphereZeroPi0Equiv.{w} (fun _ => Iso.refl R)

/-- Identifies ordinary degree-zero singular homology of `S⁰` with `R ⊞ R` by the general
  H₀ coproduct iso, the preceding reindexing, and the Bool-coproduct biproduct iso; it
  does not state the reduced-H₀ orientation. -/
noncomputable def sphereZeroH0Iso (R : C) :
    ((singularHomologyFunctor.{w, v, u} C 0).obj R).obj (TopCat.sphere.{w} 0) ≅ R ⊞ R :=
  (TopCat.sphere.{w} 0).singularHomology₀Iso R ≪≫
    sphereZeroPi0CoproductIso.{w} R ≪≫
    boolCoproductIsoBiprod R

omit [HasCoproducts.{w} C] [CategoryWithHomology C] in
private lemma boolCoproductIsoBiprod_hom_comp_fold (R : C) :
    (boolCoproductIsoBiprod (C := C) R).hom ≫ biprodFold R =
      Sigma.desc (fun _ : Bool => 𝟙 R) := by
  apply Sigma.hom_ext
  intro b
  cases b <;>
    simp only [boolCoproductIsoBiprod, biprodFold, ← Category.assoc,
      Sigma.ι_comp_desc, biprod.inl_desc, biprod.inr_desc]

omit [Preadditive C] [CategoryWithHomology C] in
private lemma sphereZeroPi0CoproductIso_hom_comp_desc (R : C) :
    (sphereZeroPi0CoproductIso.{w} (C := C) R).hom ≫ Sigma.desc (fun _ : Bool => 𝟙 R) =
      Sigma.desc (fun _ : ZerothHomotopy ↥(TopCat.sphere.{w} 0) => 𝟙 R) := by
  apply Sigma.hom_ext
  intro q
  dsimp only [sphereZeroPi0CoproductIso, Sigma.whiskerEquiv, Iso.symm]
  rw [← Category.assoc, Sigma.ι_comp_map']
  simp only [Iso.refl_inv, Category.id_comp, Sigma.ι_comp_desc]

@[reassoc]
theorem sphereZeroH0Iso_hom_comp_biprodFold (R : C) :
    (sphereZeroH0Iso.{w} (C := C) R).hom ≫ biprodFold R =
      (TopCat.sphere.{w} 0).singularHomology₀ε R := by
  unfold sphereZeroH0Iso
  simp only [Iso.trans_hom, Category.assoc]
  rw [boolCoproductIsoBiprod_hom_comp_fold, sphereZeroPi0CoproductIso_hom_comp_desc]
  exact TopCat.singularHomology₀Iso_sigma_desc_id (TopCat.sphere.{w} 0) R

private lemma sphereZeroPi0Equiv_mk_north :
    sphereZeroPi0Equiv.{w}
        (ZerothHomotopy.mk (ULift.up.{w, 0} (northPt 0))) = true := by
  calc sphereZeroPi0Equiv.{w}
        (ZerothHomotopy.mk (ULift.up.{w, 0} (northPt 0)))
      = sphereOneEquivBool (northPt 0) := rfl
    _ = true := sphereOneEquivBool_northPt

private lemma sphereZeroPi0Equiv_mk_south :
    sphereZeroPi0Equiv.{w}
        (ZerothHomotopy.mk (ULift.up.{w, 0} (southPt 0))) = false := by
  calc sphereZeroPi0Equiv.{w}
        (ZerothHomotopy.mk (ULift.up.{w, 0} (southPt 0)))
      = sphereOneEquivBool (southPt 0) := rfl
    _ = false := sphereOneEquivBool_southPt

private lemma sphereZeroPi0Equiv_mk_eq_homeoBool (x : ↥(TopCat.sphere.{w} 0)) :
    sphereZeroPi0Equiv.{w} (ZerothHomotopy.mk x) = sphereZeroHomeoBool.{w} x := by
  by_cases hx : sphereZeroHomeoBool.{w} x = true
  · have hx_eq : x = ULift.up (northPt 0) := by
      have : sphereZeroHomeoBool.{w} x =
          sphereZeroHomeoBool.{w} (ULift.up.{w, 0} (northPt 0)) := by
        rw [hx, sphereZeroHomeoBool_northPt]
      exact sphereZeroHomeoBool.{w}.injective this
    rw [hx_eq, sphereZeroPi0Equiv_mk_north, sphereZeroHomeoBool_northPt]
  · have hx_false : sphereZeroHomeoBool.{w} x = false := by
      cases hb : sphereZeroHomeoBool.{w} x <;> simp_all
    have hx_eq : x = ULift.up (southPt 0) := by
      have : sphereZeroHomeoBool.{w} x =
          sphereZeroHomeoBool.{w} (ULift.up.{w, 0} (southPt 0)) := by
        rw [hx_false, sphereZeroHomeoBool_southPt]
      exact sphereZeroHomeoBool.{w}.injective this
    rw [hx_eq, sphereZeroPi0Equiv_mk_south, sphereZeroHomeoBool_southPt]

lemma sphereZeroPi0Equiv_zerothHomotopyMap_antipodal
    (q : ZerothHomotopy ↥(TopCat.sphere.{w} 0)) :
    sphereZeroPi0Equiv.{w} (TopCat.zerothHomotopyMap (sphereAntipodalMap.{w} 0) q) =
      !(sphereZeroPi0Equiv.{w} q) := by
  induction q using ZerothHomotopy.rec with
  | mk x =>
    rw [TopCat.zerothHomotopyMap_mk, sphereZeroPi0Equiv_mk_eq_homeoBool,
      sphereZeroPi0Equiv_mk_eq_homeoBool, sphereZeroHomeoBool_antipodalMap]

private noncomputable abbrev antipodalCoproductMap (R : C) :
    (∐ fun _ : ZerothHomotopy ↥(TopCat.sphere.{w} 0) => R) ⟶
      (∐ fun _ : ZerothHomotopy ↥(TopCat.sphere.{w} 0) => R) :=
  Sigma.map' (TopCat.zerothHomotopyMap (sphereAntipodalMap.{w} 0)) (fun _ => 𝟙 R)

omit [HasCoproducts.{0} C] [Preadditive C] [CategoryWithHomology C] in
private theorem zerothCoproductFunctor_map_eq (R : C) :
    (TopCat.zerothHomotopyCoproductFunctor.{w, v, u} (C := C) R).map
        (sphereAntipodalMap.{w} 0) =
      antipodalCoproductMap.{w} R :=
  rfl

omit [Preadditive C] [CategoryWithHomology C] in
private theorem sphereZeroPi0CoproductIso_inv_comp_zerothMap_comp_hom (R : C) :
    (sphereZeroPi0CoproductIso.{w} (C := C) R).inv ≫
      antipodalCoproductMap.{w} R ≫
      (sphereZeroPi0CoproductIso.{w} R).hom =
      Sigma.map' (fun b : Bool => !b) (fun _ => 𝟙 R) := by
  apply Sigma.hom_ext
  intro b
  simp only [← Category.assoc, sphereZeroPi0CoproductIso, Sigma.whiskerEquiv,
    antipodalCoproductMap, Iso.refl_inv, Iso.refl_hom, eqToHom_refl, Category.id_comp,
    Category.comp_id, Sigma.ι_comp_map']
  have h_eq : sphereZeroPi0Equiv.{w} (TopCat.zerothHomotopyMap (sphereAntipodalMap.{w} 0)
      (sphereZeroPi0Equiv.{w}.symm b)) = !b := by
    calc sphereZeroPi0Equiv.{w} (TopCat.zerothHomotopyMap (sphereAntipodalMap.{w} 0)
          (sphereZeroPi0Equiv.{w}.symm b))
        = !(sphereZeroPi0Equiv.{w} (sphereZeroPi0Equiv.{w}.symm b)) := by
          rw [sphereZeroPi0Equiv_zerothHomotopyMap_antipodal]
      _ = !b := by rw [Equiv.apply_symm_apply]
  rw [h_eq]

omit [HasCoproducts.{w} C] [CategoryWithHomology C] in
private theorem bool_not_coprod_braiding (R : C) :
    (boolCoproductIsoBiprod (C := C) R).inv ≫
      Sigma.map' (fun b : Bool => !b) (fun _ => 𝟙 R) ≫
      (boolCoproductIsoBiprod R).hom =
      (biprod.braiding R R).hom := by
  apply biprod.hom_ext'
  · simp only [← Category.assoc, boolCoproductIsoBiprod, Sigma.ι_comp_desc,
      Sigma.ι_comp_map', biprod.inl_desc, Category.id_comp]
    apply biprod.hom_ext <;> simp [biprod.braiding]
  · simp only [← Category.assoc, boolCoproductIsoBiprod, Sigma.ι_comp_desc,
      Sigma.ι_comp_map', biprod.inr_desc, Category.id_comp]
    apply biprod.hom_ext <;> simp [biprod.braiding]

@[reassoc]
theorem sphereZeroH0Iso_inv_comp_antipodal_comp_hom (R : C) :
    (sphereZeroH0Iso.{w} (C := C) R).inv ≫
      ((singularHomologyFunctor.{w, v, u} C 0).obj R).map (sphereAntipodalMap.{w} 0) ≫
      (sphereZeroH0Iso.{w} R).hom =
      (biprod.braiding R R).hom := by
  have h_nat : ((singularHomologyFunctor.{w, v, u} C 0).obj R).map (sphereAntipodalMap.{w} 0) ≫
      ((TopCat.sphere.{w} 0).singularHomology₀Iso R).hom =
      ((TopCat.sphere.{w} 0).singularHomology₀Iso R).hom ≫
        antipodalCoproductMap.{w} R := by
    have h0 := TopCat.singularHomologyMap_comp_singularHomology₀Iso_hom
      (sphereAntipodalMap.{w} (0 : ℕ)) (R := R)
    change ((singularHomologyFunctor.{w, v, u} C 0).obj R).map (sphereAntipodalMap.{w} 0) ≫
        ((TopCat.sphere.{w} 0).singularHomology₀Iso R).hom =
        ((TopCat.sphere.{w} 0).singularHomology₀Iso R).hom ≫
          (TopCat.zerothHomotopyCoproductFunctor.{w, v, u} R).map
            (sphereAntipodalMap.{w} 0) at h0
    rw [zerothCoproductFunctor_map_eq] at h0
    exact h0
  have h_alpha : (sphereZeroH0Iso.{w} (C := C) R).inv ≫
      ((singularHomologyFunctor.{w, v, u} C 0).obj R).map (sphereAntipodalMap.{w} 0) ≫
      (sphereZeroH0Iso.{w} R).hom =
      (boolCoproductIsoBiprod R).inv ≫
        (sphereZeroPi0CoproductIso.{w} R).inv ≫
        ((TopCat.sphere.{w} 0).singularHomology₀Iso R).inv ≫
        ((singularHomologyFunctor.{w, v, u} C 0).obj R).map (sphereAntipodalMap.{w} 0) ≫
        ((TopCat.sphere.{w} 0).singularHomology₀Iso R).hom ≫
        (sphereZeroPi0CoproductIso.{w} R).hom ≫
        (boolCoproductIsoBiprod R).hom := by
    unfold sphereZeroH0Iso
    simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]
  have h_mid : (boolCoproductIsoBiprod R).inv ≫
        (sphereZeroPi0CoproductIso.{w} R).inv ≫
        ((TopCat.sphere.{w} 0).singularHomology₀Iso R).inv ≫
        ((singularHomologyFunctor.{w, v, u} C 0).obj R).map (sphereAntipodalMap.{w} 0) ≫
        ((TopCat.sphere.{w} 0).singularHomology₀Iso R).hom ≫
        (sphereZeroPi0CoproductIso.{w} R).hom ≫
        (boolCoproductIsoBiprod R).hom =
      (boolCoproductIsoBiprod R).inv ≫
        (sphereZeroPi0CoproductIso.{w} R).inv ≫
        antipodalCoproductMap.{w} R ≫
        (sphereZeroPi0CoproductIso.{w} R).hom ≫
        (boolCoproductIsoBiprod R).hom := by
    calc (boolCoproductIsoBiprod R).inv ≫
          (sphereZeroPi0CoproductIso.{w} R).inv ≫
          ((TopCat.sphere.{w} 0).singularHomology₀Iso R).inv ≫
          ((singularHomologyFunctor.{w, v, u} C 0).obj R).map (sphereAntipodalMap.{w} 0) ≫
          ((TopCat.sphere.{w} 0).singularHomology₀Iso R).hom ≫
          (sphereZeroPi0CoproductIso.{w} R).hom ≫
          (boolCoproductIsoBiprod R).hom
        = (boolCoproductIsoBiprod R).inv ≫
          (sphereZeroPi0CoproductIso.{w} R).inv ≫
          (((TopCat.sphere.{w} 0).singularHomology₀Iso R).inv ≫
            ((singularHomologyFunctor.{w, v, u} C 0).obj R).map (sphereAntipodalMap.{w} 0) ≫
            ((TopCat.sphere.{w} 0).singularHomology₀Iso R).hom) ≫
          (sphereZeroPi0CoproductIso.{w} R).hom ≫
          (boolCoproductIsoBiprod R).hom := by simp only [Category.assoc]
      _ = (boolCoproductIsoBiprod R).inv ≫
          (sphereZeroPi0CoproductIso.{w} R).inv ≫
          ((((TopCat.sphere.{w} 0).singularHomology₀Iso R).inv ≫
            ((TopCat.sphere.{w} 0).singularHomology₀Iso R).hom) ≫
            antipodalCoproductMap.{w} R) ≫
          (sphereZeroPi0CoproductIso.{w} R).hom ≫
          (boolCoproductIsoBiprod R).hom := by
          rw [← Category.assoc, ← Category.assoc, h_nat]
          simp only [Category.assoc]
      _ = (boolCoproductIsoBiprod R).inv ≫
          (sphereZeroPi0CoproductIso.{w} R).inv ≫
          antipodalCoproductMap.{w} R ≫
          (sphereZeroPi0CoproductIso.{w} R).hom ≫
          (boolCoproductIsoBiprod R).hom := by
          simp only [Iso.inv_hom_id, Category.id_comp]
  calc (sphereZeroH0Iso.{w} (C := C) R).inv ≫
        ((singularHomologyFunctor.{w, v, u} C 0).obj R).map (sphereAntipodalMap.{w} 0) ≫
        (sphereZeroH0Iso.{w} R).hom
      = (boolCoproductIsoBiprod R).inv ≫
          (sphereZeroPi0CoproductIso.{w} R).inv ≫
          antipodalCoproductMap.{w} R ≫
          (sphereZeroPi0CoproductIso.{w} R).hom ≫
          (boolCoproductIsoBiprod R).hom := by rw [h_alpha, h_mid]
    _ = (boolCoproductIsoBiprod R).inv ≫
          ((sphereZeroPi0CoproductIso.{w} R).inv ≫
            antipodalCoproductMap.{w} R ≫
            (sphereZeroPi0CoproductIso.{w} R).hom) ≫
          (boolCoproductIsoBiprod R).hom := by simp only [Category.assoc]
    _ = (boolCoproductIsoBiprod R).inv ≫
          Sigma.map' (fun b : Bool => !b) (fun _ => 𝟙 R) ≫
          (boolCoproductIsoBiprod R).hom := by
        rw [sphereZeroPi0CoproductIso_inv_comp_zerothMap_comp_hom]
    _ = (biprod.braiding R R).hom := by rw [bool_not_coprod_braiding]

@[reassoc]
theorem sphereZeroH0Iso_hom_comp_braiding (R : C) :
    ((singularHomologyFunctor.{w, v, u} C 0).obj R).map (sphereAntipodalMap.{w} 0) ≫
      (sphereZeroH0Iso.{w} R).hom =
      (sphereZeroH0Iso.{w} R).hom ≫ (biprod.braiding R R).hom := by
  have h := sphereZeroH0Iso_inv_comp_antipodal_comp_hom.{w} (C := C) R
  calc ((singularHomologyFunctor.{w, v, u} C 0).obj R).map
          (sphereAntipodalMap.{w} 0) ≫ (sphereZeroH0Iso.{w} R).hom
      = (sphereZeroH0Iso.{w} R).hom ≫ (sphereZeroH0Iso.{w} R).inv ≫
        ((singularHomologyFunctor.{w, v, u} C 0).obj R).map (sphereAntipodalMap.{w} 0) ≫
        (sphereZeroH0Iso.{w} R).hom := by
        rw [← Category.assoc, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    _ = (sphereZeroH0Iso.{w} R).hom ≫ (biprod.braiding R R).hom := by rw [h]

@[reassoc]
theorem singularHomologyMap_sphereAntipodal_comp_sphereZeroH0Iso_hom (R : C) :
    ((singularHomologyFunctor.{w, v, u} C 0).obj R).map (sphereAntipodalMap.{w} 0) ≫
      (sphereZeroH0Iso.{w} (C := C) R).hom =
      (sphereZeroH0Iso.{w} R).hom ≫ (biprod.braiding R R).hom :=
  sphereZeroH0Iso_hom_comp_braiding.{w} R

end Ordinary

section Reduced

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
  [HasCoproducts.{0} C]

attribute [local instance] HasBinaryBiproducts.of_hasBinaryCoproducts

/-! ### Canonical generic reduced H₀(S⁰) -/

/-- Canonical iso `H̃₀(S⁰; R) ≅ ker (R⊕R → R)` built from `H̃₀ ≅ ker ε` and
`ker.mapIso` along `H₀(S⁰) ≅ R⊕R`. -/
noncomputable def sphereZeroReducedH0KernelIso (R : C) :
    reducedSingularHomology.{w, v, u} C R 0 (TopCat.sphere.{w} 0) ≅ kernel (biprodFold R) :=
  (reducedSingularHomologyZeroCanonicalKernelIso.{w, v, u} C R (TopCat.sphere.{w} 0)) ≪≫
    kernel.mapIso (f := (TopCat.sphere.{w} 0).singularHomology₀ε R) (biprodFold R)
      (sphereZeroH0Iso.{w} (C := C) R) (Iso.refl R)
      (by
        calc (TopCat.sphere.{w} 0).singularHomology₀ε R ≫ (Iso.refl R).hom
            = (TopCat.sphere.{w} 0).singularHomology₀ε R := by simp
          _ = (sphereZeroH0Iso.{w} R).hom ≫ biprodFold R := by
              rw [← sphereZeroH0Iso_hom_comp_biprodFold])

@[reassoc (attr := simp)]
theorem sphereZeroReducedH0KernelIso_hom_ι (R : C) :
    (sphereZeroReducedH0KernelIso.{w} (C := C) R).hom ≫ kernel.ι (biprodFold R) =
      (reducedSingularHomologyι.{w, v, u} C R 0).app (TopCat.sphere.{w} 0) ≫
        (sphereZeroH0Iso.{w} (C := C) R).hom := by
  simp [sphereZeroReducedH0KernelIso]

/-- Generic canonical `H̃₀(S⁰; R) ≅ R` via the signed diagonal kernel iso.
The final negation fixes the orientation convention: the accepted generator
of `H̃₀(S⁰; R)` is `[north] - [south]`, matching the interval-first cross
product (`∂[I] = [1] - [0]` with `0 ↦ south`, `1 ↦ north`) and the
half-space boundary model equations. -/
noncomputable def sphereZeroReducedH0Iso (R : C) :
    reducedSingularHomology.{w, v, u} C R 0 (TopCat.sphere.{w} 0) ≅ R :=
  sphereZeroReducedH0KernelIso.{w} (C := C) R ≪≫
    (biprodSignedDiagonalKernelIso R).symm ≪≫
    ⟨-𝟙 R, -𝟙 R, by simp, by simp⟩

@[reassoc (attr := simp)]
theorem sphereZeroReducedH0Iso_inv_comp_ι_comp_sphereZeroH0Iso_hom (R : C) :
    (sphereZeroReducedH0Iso.{w} (C := C) R).inv ≫
      (reducedSingularHomologyι.{w, v, u} C R 0).app (TopCat.sphere.{w} 0) ≫
      (sphereZeroH0Iso.{w} (C := C) R).hom =
      -biprodSignedDiagonal (C := C) R := by
  have h_inv : (sphereZeroReducedH0Iso.{w} (C := C) R).inv =
      (-𝟙 R) ≫ (biprodSignedDiagonalKernelIso (C := C) R).hom ≫
        (sphereZeroReducedH0KernelIso.{w} (C := C) R).inv := by
    simp only [sphereZeroReducedH0Iso, Iso.trans_inv, Iso.symm_inv,
      Category.assoc]
  calc (sphereZeroReducedH0Iso.{w} (C := C) R).inv ≫
        (reducedSingularHomologyι.{w, v, u} C R 0).app (TopCat.sphere.{w} 0) ≫
        (sphereZeroH0Iso.{w} (C := C) R).hom
      = (-𝟙 R) ≫ (biprodSignedDiagonalKernelIso R).hom ≫
        (sphereZeroReducedH0KernelIso.{w} R).inv ≫
        (reducedSingularHomologyι.{w, v, u} C R 0).app (TopCat.sphere.{w} 0) ≫
        (sphereZeroH0Iso.{w} R).hom := by simp only [h_inv, Category.assoc]
    _ = (-𝟙 R) ≫ (biprodSignedDiagonalKernelIso R).hom ≫
        (sphereZeroReducedH0KernelIso.{w} R).inv ≫
        ((sphereZeroReducedH0KernelIso.{w} R).hom ≫ kernel.ι (biprodFold R)) := by
          rw [sphereZeroReducedH0KernelIso_hom_ι]
    _ = (-𝟙 R) ≫ (biprodSignedDiagonalKernelIso R).hom ≫
        kernel.ι (biprodFold R) := by
          simp only [Iso.inv_hom_id_assoc]
    _ = (-𝟙 R) ≫ biprodSignedDiagonal R := by
          rw [biprodSignedDiagonalKernelIso_hom_ι]
    _ = -biprodSignedDiagonal R := by
          rw [Preadditive.neg_comp, Category.id_comp]

theorem sphereZeroReducedH0Iso_inv_ι_orientation (R : C) :
    (sphereZeroReducedH0Iso.{w} (C := C) R).inv ≫
      (reducedSingularHomologyι.{w, v, u} C R 0).app (TopCat.sphere.{w} 0) ≫
      (sphereZeroH0Iso.{w} (C := C) R).hom =
      -biprodSignedDiagonal (C := C) R :=
  sphereZeroReducedH0Iso_inv_comp_ι_comp_sphereZeroH0Iso_hom.{w} R

/-! ### Reduced antipodal action is -1 -/

@[reassoc]
theorem sphereZeroReducedH0Iso_inv_comp_reducedAntipodal_comp_hom (R : C) :
    (sphereZeroReducedH0Iso.{w} (C := C) R).inv ≫
      (reducedSingularHomologyFunctor.{w, v, u} C R 0).map (sphereAntipodalMap.{w} 0) ≫
      (sphereZeroReducedH0Iso.{w} (C := C) R).hom = -𝟙 R := by
  let F := (reducedSingularHomologyFunctor.{w, v, u} C R 0).map (sphereAntipodalMap.{w} 0)
  let G := ((singularHomologyFunctor.{w, v, u} C 0).obj R).map (sphereAntipodalMap.{w} 0)
  let p := sphereZeroH0Iso.{w} (C := C) R
  let ι := (reducedSingularHomologyι.{w, v, u} C R 0).app (TopCat.sphere.{w} 0)
  let sd := biprodSignedDiagonal (C := C) R
  let isoRed := sphereZeroReducedH0Iso.{w} (C := C) R
  have h_sd_eq : sd = (biprodSignedDiagonalKernelIso (C := C) R).hom ≫
      kernel.ι (biprodFold R) := by rw [biprodSignedDiagonalKernelIso_hom_ι]
  have : Mono sd := by
    rw [h_sd_eq]
    infer_instance
  have hNat : F ≫ ι = ι ≫ G :=
    (reducedSingularHomologyι.{w, v, u} C R 0).naturality (sphereAntipodalMap.{w} 0)
  have hGp : G ≫ p.hom = p.hom ≫ (biprod.braiding R R).hom :=
    singularHomologyMap_sphereAntipodal_comp_sphereZeroH0Iso_hom.{w} (C := C) R
  have h_orient : isoRed.inv ≫ ι ≫ p.hom = -sd :=
    sphereZeroReducedH0Iso_inv_comp_ι_comp_sphereZeroH0Iso_hom.{w} R
  have h_hom_sd : isoRed.hom ≫ sd = -(ι ≫ p.hom) := by
    calc isoRed.hom ≫ sd
        = isoRed.hom ≫ (-(isoRed.inv ≫ ι ≫ p.hom)) := by
          rw [h_orient, neg_neg]
      _ = -(isoRed.hom ≫ (isoRed.inv ≫ ι ≫ p.hom)) := by
          rw [Preadditive.comp_neg]
      _ = -((isoRed.hom ≫ isoRed.inv) ≫ ι ≫ p.hom) := by
          simp only [Category.assoc]
      _ = -(ι ≫ p.hom) := by
          simp only [Iso.hom_inv_id, Category.id_comp]
  apply (cancel_mono sd).mp
  calc (isoRed.inv ≫ F ≫ isoRed.hom) ≫ sd
      = isoRed.inv ≫ F ≫ (isoRed.hom ≫ sd) := by simp only [Category.assoc]
    _ = isoRed.inv ≫ F ≫ (-(ι ≫ p.hom)) := by rw [h_hom_sd]
    _ = -(isoRed.inv ≫ F ≫ (ι ≫ p.hom)) := by
        rw [Preadditive.comp_neg, Preadditive.comp_neg]
    _ = -(isoRed.inv ≫ (F ≫ ι) ≫ p.hom) := by simp only [Category.assoc]
    _ = -(isoRed.inv ≫ (ι ≫ G) ≫ p.hom) := by rw [hNat]
    _ = -(isoRed.inv ≫ ι ≫ (G ≫ p.hom)) := by simp only [Category.assoc]
    _ = -(isoRed.inv ≫ ι ≫ (p.hom ≫ (biprod.braiding R R).hom)) := by rw [hGp]
    _ = -((isoRed.inv ≫ ι ≫ p.hom) ≫ (biprod.braiding R R).hom) := by
        simp only [Category.assoc]
    _ = -((-sd) ≫ (biprod.braiding R R).hom) := by rw [h_orient]
    _ = -(-(sd ≫ (biprod.braiding R R).hom)) := by rw [Preadditive.neg_comp]
    _ = sd ≫ (biprod.braiding R R).hom := by rw [neg_neg]
    _ = -sd := by rw [biprodSignedDiagonal_comp_braiding]
    _ = (-𝟙 R) ≫ sd := by simp

@[reassoc (attr := simp)]
theorem reducedSingularHomologyMap_sphereAntipodal_comp_sphereZeroReducedH0Iso_hom (R : C) :
    (reducedSingularHomologyFunctor.{w, v, u} C R 0).map (sphereAntipodalMap.{w} 0) ≫
      (sphereZeroReducedH0Iso.{w} (C := C) R).hom =
      (sphereZeroReducedH0Iso.{w} (C := C) R).hom ≫ (-𝟙 R) := by
  have h_conj :=
    sphereZeroReducedH0Iso_inv_comp_reducedAntipodal_comp_hom.{w} (C := C) R
  calc (reducedSingularHomologyFunctor.{w, v, u} C R 0).map (sphereAntipodalMap.{w} 0) ≫
        (sphereZeroReducedH0Iso.{w} R).hom
      = (sphereZeroReducedH0Iso.{w} R).hom ≫ (sphereZeroReducedH0Iso.{w} R).inv ≫
        (reducedSingularHomologyFunctor.{w, v, u} C R 0).map (sphereAntipodalMap.{w} 0) ≫
        (sphereZeroReducedH0Iso.{w} R).hom := by
          simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    _ = (sphereZeroReducedH0Iso.{w} R).hom ≫ (-𝟙 R) := by rw [h_conj]

end Reduced

end AlgebraicTopology
