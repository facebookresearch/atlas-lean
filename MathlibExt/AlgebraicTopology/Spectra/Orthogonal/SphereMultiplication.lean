/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.DimensionPowerAdd

/-!
# Full ordered multiplication of the original sphere coefficients

The entire original symmetric smash-power multiplication maps to the original
Orth sphere multiplication. The proof uses the actual source dimension add
map and the original strong monoidal coefficient tensor comparison.
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory MonoidalCategory
open CategoryTheory.MonoidalCategory.TensorPower
open scoped MonoidalClosed

namespace CategoryTheory.Spectra

attribute [local instance] OrthogonalIndex.category OrthogonalIndex.monoidalCategory
attribute [local instance] OrthogonalIndex.enrichedOrdinaryCategory
attribute [local instance] OrthogonalIndex.symmetricCategory

/-- The complete original sphere splitting preserves ordered addition of degrees. -/
theorem originalOrthogonalSpherePowerIso_mul (m n : ℕ) :
    (originalOrthogonalSpherePowerIso.{u, v} (m + n)).hom ≫
        (tensorPowObj_add (PointedCGWH.orthogonalSphere.{u, v} 1) m n).hom =
      (PointedCGWH.orthogonalSphereTensorIso.{u, v} m n).hom ≫
        ((originalOrthogonalSpherePowerIso.{u, v} m).hom ⊗ₘ
          (originalOrthogonalSpherePowerIso.{u, v} n).hom) := by
  let _ := originalOrthogonalSphereMonoidal.{u, v}
  let G := originalOrthogonalSphereOrdinary.{u, v}
  let pm : OrthogonalIndex := tensorPowObj (1 : OrthogonalIndex) m
  let pn : OrthogonalIndex := tensorPowObj (1 : OrthogonalIndex) n
  let ps : OrthogonalIndex := tensorPowObj (1 : OrthogonalIndex) (m + n)
  let dm : pm = m := orthogonalDimensionPower.{v, u} m
  let dn : pn = n := orthogonalDimensionPower.{v, u} n
  let ds : ps = m + n := orthogonalDimensionPower.{v, u} (m + n)
  let dmn : m + n = pm + pn := congrArg₂ (fun a b : OrthogonalIndex => a + b) dm.symm dn.symm
  let cm : G.obj m ⟶ G.obj pm := eqToHom (congrArg G.obj dm.symm)
  let cn : G.obj n ⟶ G.obj pn := eqToHom (congrArg G.obj dn.symm)
  let cs : G.obj (m + n) ⟶ G.obj ps := eqToHom (congrArg G.obj ds.symm)
  let cmn : G.obj (m + n) ⟶ G.obj (pm + pn) := eqToHom (congrArg G.obj dmn)
  let fm := (mapTensorPowObjIso G (1 : OrthogonalIndex) m).hom
  let fn := (mapTensorPowObjIso G (1 : OrthogonalIndex) n).hom
  let fs := (mapTensorPowObjIso G (1 : OrthogonalIndex) (m + n)).hom
  let add := (tensorPowObj_add (G.obj 1) m n).hom
  have h := mapTensorPowObjIso_hom_add G (1 : OrthogonalIndex) m n
  have hSource := orthogonalDimensionPower_addMap.{u, v} m n
  have hMap : G.map (tensorPowObj_add (1 : OrthogonalIndex) m n).hom =
      eqToHom (congrArg G.obj (ds.trans dmn)) := by
    rw [hSource]
    exact eqToHom_map G _
  have h0 : fs ≫ add = eqToHom (congrArg G.obj (ds.trans dmn)) ≫
      (Functor.Monoidal.μIso G pm pn).inv ≫ (fm ⊗ₘ fn) := by
    exact h.trans (congrArg (fun z => z ≫ (Functor.Monoidal.μIso G pm pn).inv ≫
      (fm ⊗ₘ fn)) hMap)
  have hCast : cs ≫ eqToHom (congrArg G.obj (ds.trans dmn)) = cmn := by
    rw [eqToHom_trans]
  have transport {a b c d : OrthogonalIndex} (ha : a = b) (hc : c = d) :
      eqToHom (congrArg G.obj (congrArg₂ (fun a c : OrthogonalIndex => a + c) ha hc).symm) ≫
        (Functor.Monoidal.μIso G a c).inv =
      (Functor.Monoidal.μIso G b d).inv ≫
        (eqToHom (congrArg G.obj ha.symm) ⊗ₘ eqToHom (congrArg G.obj hc.symm)) := by
    cases ha
    cases hc
    simp
  have hTensor : cmn ≫ (Functor.Monoidal.μIso G pm pn).inv =
      (PointedCGWH.orthogonalSphereTensorIso.{u, v} m n).hom ≫ (cm ⊗ₘ cn) := by
    have ht := transport dm dn
    have hmu : (Functor.Monoidal.μIso G m n).inv =
        (PointedCGWH.orthogonalSphereTensorIso.{u, v} m n).hom :=
      congrArg Iso.inv (originalOrthogonalSphereMonoidal_muIso.{u, v} m n)
    rw [hmu] at ht
    exact ht
  have h1 := congrArg (fun z => cs ≫ z) h0
  have h2 : (cs ≫ fs) ≫ add =
      (PointedCGWH.orthogonalSphereTensorIso.{u, v} m n).hom ≫
        ((cm ≫ fm) ⊗ₘ (cn ≫ fn)) := by
    rw [Category.assoc]
    have hCast' := congrArg (fun z => z ≫ (Functor.Monoidal.μIso G pm pn).inv ≫
      (fm ⊗ₘ fn)) hCast
    have hTensor' := congrArg (fun z => z ≫ (fm ⊗ₘ fn)) hTensor
    have hFuse := tensorHom_comp_tensorHom cm cn fm fn
    exact h1.trans ((Category.assoc cs _ _).symm.trans
      (hCast'.trans ((Category.assoc cmn _ _).symm.trans
        (hTensor'.trans ((Category.assoc _ _ _).trans
          (congrArg (fun z => (PointedCGWH.orthogonalSphereTensorIso.{u, v} m n).hom ≫ z)
            hFuse))))))
  have hm : cm ≫ fm = (originalOrthogonalSpherePowerIso.{u, v} m).hom := by
    exact congrArg Iso.hom (originalSphereMonoidalPowerIso_eq.{u, v} m)
  have hn : cn ≫ fn = (originalOrthogonalSpherePowerIso.{u, v} n).hom := by
    exact congrArg Iso.hom (originalSphereMonoidalPowerIso_eq.{u, v} n)
  have hs : cs ≫ fs = (originalOrthogonalSpherePowerIso.{u, v} (m + n)).hom := by
    exact congrArg Iso.hom (originalSphereMonoidalPowerIso_eq.{u, v} (m + n))
  have hL := congrArg (fun z => z ≫ add) hs
  have hR := congrArg (fun z => (PointedCGWH.orthogonalSphereTensorIso.{u, v} m n).hom ≫ z)
    (congrArg₂ (fun a b => a ⊗ₘ b) hm hn)
  exact hL.symm.trans (h2.trans hR)

/-- The complete original symmetric multiplication maps to the original Orth multiplication. -/
theorem originalSpherePowerComparisonIso_multiplication (m n : ℕ) :
    (tensorPowObj_add PointedCGWH.sphereOne.{u, v} m n).inv ≫
        (originalSpherePowerComparisonIso.{u, v} (m + n)).hom =
      ((originalSpherePowerComparisonIso.{u, v} m).hom ⊗ₘ
        (originalSpherePowerComparisonIso.{u, v} n).hom) ≫
        (PointedCGWH.orthogonalSphereTensorIso.{u, v} m n).inv := by
  let c := orthogonalOneSphereIsoSphereOne.{u, v}.inv
  let fm := tensorPowMap c m
  let fn := tensorPowMap c n
  let fs := tensorPowMap c (m + n)
  let pm := originalOrthogonalSpherePowerIso.{u, v} m
  let pn := originalOrthogonalSpherePowerIso.{u, v} n
  let ps := originalOrthogonalSpherePowerIso.{u, v} (m + n)
  have hSeed := tensorPowObj_add_naturality c m n
  have hOrth := originalOrthogonalSpherePowerIso_mul.{u, v} m n
  apply (cancel_mono (PointedCGWH.orthogonalSphereTensorIso.{u, v} m n).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_epi (tensorPowObj_add PointedCGWH.sphereOne.{u, v} m n).hom).1
  simp only [Iso.hom_inv_id_assoc]
  have hInverse : ps.inv ≫ (PointedCGWH.orthogonalSphereTensorIso.{u, v} m n).hom =
      (tensorPowObj_add (PointedCGWH.orthogonalSphere.{u, v} 1) m n).hom ≫
        (pm.inv ⊗ₘ pn.inv) := by
    apply (cancel_epi ps.hom).1
    simp only [Iso.hom_inv_id_assoc]
    have hFull := congrArg (fun z => z ≫ (pm.inv ⊗ₘ pn.inv)) hOrth
    have hCancel : ((pm.hom ⊗ₘ pn.hom) ≫ (pm.inv ⊗ₘ pn.inv)) = 𝟙 _ := by
      rw [tensorHom_comp_tensorHom, Iso.hom_inv_id, Iso.hom_inv_id, id_tensorHom_id]
    have hc := (Category.assoc _ _ _).trans
      ((congrArg (fun z => (PointedCGWH.orthogonalSphereTensorIso.{u, v} m n).hom ≫ z)
        hCancel).trans (Category.comp_id _))
    exact hc.symm.trans ((hFull.symm.trans (Category.assoc _ _ _)))
  have hs : (originalSpherePowerComparisonIso.{u, v} (m + n)).hom = fs ≫ ps.inv := rfl
  have hm : (originalSpherePowerComparisonIso.{u, v} m).hom = fm ≫ pm.inv := rfl
  have hn : (originalSpherePowerComparisonIso.{u, v} n).hom = fn ≫ pn.inv := rfl
  have hFusion := tensorHom_comp_tensorHom fm fn pm.inv pn.inv
  have hSeed' := congrArg (fun z => z ≫ (pm.inv ⊗ₘ pn.inv)) hSeed
  have hWhole : (fs ≫ ps.inv) ≫ (PointedCGWH.orthogonalSphereTensorIso.{u, v} m n).hom =
      (tensorPowObj_add PointedCGWH.sphereOne.{u, v} m n).hom ≫
        ((fm ≫ pm.inv) ⊗ₘ (fn ≫ pn.inv)) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => fs ≫ z) hInverse).trans
        ((Category.assoc _ _ _).symm.trans
          (hSeed'.trans ((Category.assoc _ _ _).trans
            (congrArg (fun z => (tensorPowObj_add PointedCGWH.sphereOne.{u, v} m n).hom ≫ z)
              hFusion)))))
  exact (congrArg (fun z => z ≫ (PointedCGWH.orthogonalSphereTensorIso.{u, v} m n).hom) hs).trans
    (hWhole.trans (congrArg (fun z => (tensorPowObj_add PointedCGWH.sphereOne.{u, v} m n).hom ≫ z)
      (congrArg₂ (fun a b => a ⊗ₘ b) hm hn).symm))

end CategoryTheory.Spectra
