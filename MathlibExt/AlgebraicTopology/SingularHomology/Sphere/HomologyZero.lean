/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.AlgebraicTopology.SingularHomology.Sphere.Zero
public import MathlibExt.AlgebraicTopology.SingularHomology.ReducedCoefficientFunctor

/-!
# Coefficient naturality of reduced zero-sphere homology

The canonical oriented identification `H̃₀(S⁰; R) ≅ R` is natural in the
coefficient object.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicTopology

variable {C : Type u} [Category.{v} C] [HasCoproducts.{0} C] [Abelian C]

private theorem sphereZeroH0Iso_hom_naturality_coefficient
    {R S : C} (a : R ⟶ S) :
    ((singularHomologyFunctor C 0).map a).app (TopCat.sphere.{0} 0) ≫
        (sphereZeroH0Iso (C := C) S).hom =
      (sphereZeroH0Iso (C := C) R).hom ≫ biprod.map a a := by
  unfold sphereZeroH0Iso
  simp only [Iso.trans_hom]
  rw [← Category.assoc, TopCat.singularHomology₀Iso_hom_naturality_coefficient,
    Category.assoc]
  have hbool : Limits.Sigma.map (fun _ : Bool => a) ≫
        (boolCoproductIsoBiprod S).hom =
      (boolCoproductIsoBiprod R).hom ≫ biprod.map a a := by
    apply Sigma.hom_ext
    intro b
    cases b <;> simp [boolCoproductIsoBiprod]
  have h_tail :
      Limits.Sigma.map (fun _ : ZerothHomotopy ↥(TopCat.sphere.{0} 0) => a) ≫
          (sphereZeroPi0CoproductIso (C := C) S).hom ≫
          (boolCoproductIsoBiprod S).hom =
        (sphereZeroPi0CoproductIso (C := C) R).hom ≫
          (boolCoproductIsoBiprod R).hom ≫ biprod.map a a := by
    dsimp only [sphereZeroPi0CoproductIso, Sigma.whiskerEquiv]
    rw [← Category.assoc, Sigma.map_comp_map']
    simp only [Iso.refl_inv, Category.comp_id]
    have hfactor : Sigma.map' sphereZeroPi0Equiv (fun _ => a) =
        Sigma.map' sphereZeroPi0Equiv (fun _ => 𝟙 R) ≫
          Limits.Sigma.map (fun _ : Bool => a) := by
      rw [Sigma.map'_comp_map]
      simp
    rw [hfactor, Category.assoc, hbool]
  simpa only [Category.assoc] using congrArg
    (fun k => ((TopCat.sphere.{0} 0).singularHomology₀Iso R).hom ≫ k) h_tail

/-- The oriented reduced degree-zero homology identification of the zero-sphere
is natural in the coefficient object. -/
theorem sphereZeroReducedH0Iso_hom_naturality_coefficient
    {R S : C} (a : R ⟶ S) :
    ((reducedSingularHomologyCoefficientFunctor C 0).map a).app
          (TopCat.sphere.{0} 0) ≫
        (sphereZeroReducedH0Iso (C := C) S).hom =
      (sphereZeroReducedH0Iso (C := C) R).hom ≫ a := by
  change (reducedSingularHomologyCoefficientMap C 0 a).app (TopCat.sphere.{0} 0) ≫
        (sphereZeroReducedH0Iso (C := C) S).hom =
      (sphereZeroReducedH0Iso (C := C) R).hom ≫ a
  let eR := sphereZeroReducedH0Iso (C := C) R
  let eS := sphereZeroReducedH0Iso (C := C) S
  let ιR := (reducedSingularHomologyι C R 0).app (TopCat.sphere.{0} 0)
  let ιS := (reducedSingularHomologyι C S 0).app (TopCat.sphere.{0} 0)
  let pR := sphereZeroH0Iso (C := C) R
  let pS := sphereZeroH0Iso (C := C) S
  let rα := (reducedSingularHomologyCoefficientMap C 0 a).app (TopCat.sphere.{0} 0)
  let hα := ((singularHomologyFunctor C 0).map a).app (TopCat.sphere.{0} 0)
  let _ : Mono ιS := by
    dsimp [ιS]
    rw [← reducedSingularHomologyObjIso_hom_ι]
    infer_instance
  have hrι : rα ≫ ιS = ιR ≫ hα := by
    exact congr_app (reducedSingularHomologyCoefficientMap_comp_ι C 0 a)
      (TopCat.sphere.{0} 0)
  have hp : hα ≫ pS.hom = pR.hom ≫ biprod.map a a :=
    sphereZeroH0Iso_hom_naturality_coefficient a
  have hsd : a ≫ biprodSignedDiagonal (C := C) S =
      biprodSignedDiagonal (C := C) R ≫ biprod.map a a := by
    apply biprod.hom_ext <;> simp [biprodSignedDiagonal]
  have hinv : a ≫ eS.inv = eR.inv ≫ rα := by
    apply (cancel_mono ιS).mp
    apply (cancel_mono pS.hom).mp
    have hlhs : (a ≫ eS.inv) ≫ ιS ≫ pS.hom =
        a ≫ (-biprodSignedDiagonal (C := C) S) := by
      simpa only [Category.assoc] using congrArg (fun q => a ≫ q)
        (sphereZeroReducedH0Iso_inv_comp_ι_comp_sphereZeroH0Iso_hom (C := C) S)
    have hrhs : (eR.inv ≫ rα) ≫ ιS ≫ pS.hom =
        (-biprodSignedDiagonal (C := C) R) ≫ biprod.map a a := by
      calc
        (eR.inv ≫ rα) ≫ ιS ≫ pS.hom = eR.inv ≫ (rα ≫ ιS) ≫ pS.hom := by
          simp only [Category.assoc]
        _ = eR.inv ≫ (ιR ≫ hα) ≫ pS.hom := by rw [hrι]
        _ = eR.inv ≫ ιR ≫ (hα ≫ pS.hom) := by simp only [Category.assoc]
        _ = eR.inv ≫ ιR ≫ (pR.hom ≫ biprod.map a a) := by rw [hp]
        _ = (eR.inv ≫ ιR ≫ pR.hom) ≫ biprod.map a a := by
          simp only [Category.assoc]
        _ = (-biprodSignedDiagonal (C := C) R) ≫ biprod.map a a := by
          rw [sphereZeroReducedH0Iso_inv_comp_ι_comp_sphereZeroH0Iso_hom]
    calc
      ((a ≫ eS.inv) ≫ ιS) ≫ pS.hom =
          a ≫ (-biprodSignedDiagonal (C := C) S) := by
        simpa only [Category.assoc] using hlhs
      _ = (-biprodSignedDiagonal (C := C) R) ≫ biprod.map a a := by
        rw [Preadditive.comp_neg, hsd, Preadditive.neg_comp]
      _ = ((eR.inv ≫ rα) ≫ ιS) ≫ pS.hom := by
        simpa only [Category.assoc] using hrhs.symm
  apply (cancel_epi eR.inv).mp
  simp only [← Category.assoc]
  change (eR.inv ≫ rα) ≫ eS.hom = (eR.inv ≫ eR.hom) ≫ a
  rw [← hinv]
  simp

/-- Reduced degree-zero homology of the zero-sphere is naturally isomorphic
to the coefficient object. -/
noncomputable def sphereZeroReducedH0CoefficientNatIso :
    reducedSingularHomologyCoefficientFunctor C 0 ⋙
        (evaluation TopCat.{0} C).obj (TopCat.sphere.{0} 0) ≅
      (𝟭 C : C ⥤ C) :=
  NatIso.ofComponents
    (fun R => sphereZeroReducedH0Iso (C := C) R)
    (fun {_ _} a => sphereZeroReducedH0Iso_hom_naturality_coefficient a)

end AlgebraicTopology
