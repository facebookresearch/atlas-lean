/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SphereMonoidal
public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SpherePowerComparison
public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SphereMonoidalCharacteristics

/-!
# The original sphere splitting and the standard monoidal power comparison

The source tensor powers of the actual one-dimensional representation have
their literal finite dimensions. The standard monoidal power comparison uses
the original Orth sphere epsilon and mu, and agrees with the original ordered
representation-sphere splitting.
-/

@[expose] public section

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

/-- The source tensor powers of dimension one are their actual original dimensions. -/
theorem orthogonalDimensionPower (n : ℕ) :
    tensorPowObj (1 : OrthogonalIndex) n = n := by
  induction n with
  | zero => rfl
  | succ n h =>
      change tensorPowObj (1 : OrthogonalIndex) n + 1 = n + 1
      rw [h]

/-- The standard monoidal power comparison, with the actual source dimension restored. -/
def originalSphereMonoidalPowerIso (n : ℕ) :
    PointedCGWH.orthogonalSphere.{u, v} n ≅
      tensorPowObj (PointedCGWH.orthogonalSphere.{u, v} 1) n := by
  letI := originalOrthogonalSphereMonoidal.{u, v}
  exact eqToIso (congrArg originalOrthogonalSphereOrdinary.{u, v}.obj
    (orthogonalDimensionPower.{v, u} n).symm) ≪≫
      mapTensorPowObjIso originalOrthogonalSphereOrdinary.{u, v} (1 : OrthogonalIndex) n

/-- At dimension zero the standard comparison is the original sphere-zero splitting. -/
theorem originalSphereMonoidalPowerIso_zero :
    originalSphereMonoidalPowerIso.{u, v} 0 = PointedCGWH.orthogonalSphereZeroIso.{u, v} := by
  let _ := originalOrthogonalSphereMonoidal.{u, v}
  unfold originalSphereMonoidalPowerIso
  apply Iso.ext
  simp only [mapTensorPowObjIso_zero, originalOrthogonalSphereMonoidal_epsilonIso]
  change 𝟙 _ ≫ PointedCGWH.orthogonalSphereZeroIso.{u, v}.hom = _
  rw [Category.id_comp]

/-- At each successor the standard comparison uses the original ordered sphere splitting. -/
theorem originalSphereMonoidalPowerIso_succ (n : ℕ) :
    originalSphereMonoidalPowerIso.{u, v} (n + 1) =
      PointedCGWH.orthogonalSphereTensorIso.{u, v} n 1 ≪≫
        tensorIso (originalSphereMonoidalPowerIso.{u, v} n) (Iso.refl _) := by
  let _ := originalOrthogonalSphereMonoidal.{u, v}
  let G := originalOrthogonalSphereOrdinary.{u, v}
  let d : tensorPowObj (1 : OrthogonalIndex) n = n := orthogonalDimensionPower.{v, u} n
  have generalTransport {a b : OrthogonalIndex} (h : a = b) :
      eqToHom (congrArg G.obj (congrArg (fun a : OrthogonalIndex => a + 1) h).symm) ≫
      (Functor.Monoidal.μIso G a 1).inv =
        (Functor.Monoidal.μIso G b 1).inv ≫ eqToHom (congrArg G.obj h.symm) ▷ G.obj 1 := by
    cases h
    simp
  have hTransport : eqToHom (congrArg G.obj (congrArg (fun a : OrthogonalIndex => a + 1) d).symm) ≫
      (Functor.Monoidal.μIso G (tensorPowObj (1 : OrthogonalIndex) n) 1).inv =
        (Functor.Monoidal.μIso G n 1).inv ≫ eqToHom (congrArg G.obj d.symm) ▷ G.obj 1 := by
    exact generalTransport d
  apply Iso.ext
  change eqToHom (congrArg G.obj (orthogonalDimensionPower.{v, u} (n + 1)).symm) ≫
      (mapTensorPowObjIso G (1 : OrthogonalIndex) (n + 1)).hom =
    (PointedCGWH.orthogonalSphereTensorIso.{u, v} n 1).hom ≫
      ((eqToHom (congrArg G.obj d.symm) ≫
        (mapTensorPowObjIso G (1 : OrthogonalIndex) n).hom) ⊗ₘ 𝟙 (G.obj 1))
  rw [mapTensorPowObjIso_succ]
  simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom]
  let c : G.obj (n + 1) ⟶ G.obj (tensorPowObj (1 : OrthogonalIndex) n + 1) :=
    eqToHom (congrArg G.obj (congrArg (fun a : OrthogonalIndex => a + 1) d).symm)
  let p : G.obj (tensorPowObj (1 : OrthogonalIndex) n) ⟶
      tensorPowObj (G.obj 1) n := (mapTensorPowObjIso G (1 : OrthogonalIndex) n).hom
  change c ≫ (Functor.Monoidal.μIso G (tensorPowObj (1 : OrthogonalIndex) n) 1).inv ≫
      (p ⊗ₘ 𝟙 (G.obj 1)) =
    (PointedCGWH.orthogonalSphereTensorIso.{u, v} n 1).hom ≫
      ((eqToHom (congrArg G.obj d.symm) ≫ p) ⊗ₘ 𝟙 (G.obj 1))
  have h := congrArg (fun k : G.obj (n + 1) ⟶
    G.obj (tensorPowObj (1 : OrthogonalIndex) n) ⊗ G.obj 1 =>
      k ≫ (p ⊗ₘ 𝟙 (G.obj 1))) hTransport
  have hmu : (Functor.Monoidal.μIso G n 1).inv =
      (PointedCGWH.orthogonalSphereTensorIso.{u, v} n 1).hom :=
    congrArg Iso.inv (originalOrthogonalSphereMonoidal_muIso.{u, v} n 1)
  have hFuse : (eqToHom (congrArg G.obj d.symm) ▷ G.obj 1) ≫
      (p ⊗ₘ 𝟙 (G.obj 1)) = (eqToHom (congrArg G.obj d.symm) ≫ p) ⊗ₘ 𝟙 (G.obj 1) := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp]
  exact (Category.assoc _ _ _).symm.trans
    (h.trans ((Category.assoc _ _ _).trans
      ((congrArg (fun k => k ≫ _) hmu).trans
        (congrArg (fun k => (PointedCGWH.orthogonalSphereTensorIso.{u, v} n 1).hom ≫ k) hFuse))))

/-- The standard monoidal power map is exactly the original ordered representation splitting. -/
theorem originalSphereMonoidalPowerIso_eq (n : ℕ) :
    originalSphereMonoidalPowerIso.{u, v} n = originalOrthogonalSpherePowerIso.{u, v} n := by
  induction n with
  | zero => exact originalSphereMonoidalPowerIso_zero
  | succ n h =>
      rw [originalSphereMonoidalPowerIso_succ, h]
      rfl

end CategoryTheory.Spectra
