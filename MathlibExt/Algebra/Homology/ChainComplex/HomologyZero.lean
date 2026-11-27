/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The degree-zero homology class map as a cokernel

For a nonnegative chain complex, the degree-zero class map is a cokernel
of the degree-one differential. It is the opcycles projection followed by
the degree-zero homology isomorphism, and the comparison is natural.
Only zero morphisms and the specified degree-zero homology are required.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

section Homology

variable (K : ChainComplex C ℕ) [K.HasHomology 0]

/-- The degree-zero class of a chain, using native opcycles and homology. -/
def homologyZeroClass : K.X 0 ⟶ K.homology 0 :=
  K.pOpcycles 0 ≫ K.isoHomologyι₀.inv

@[reassoc (attr := simp)]
theorem d_comp_homologyZeroClass : K.d 1 0 ≫ homologyZeroClass K = 0 := by
  change K.d 1 0 ≫ (K.pOpcycles 0 ≫ K.isoHomologyι₀.inv) = 0
  rw [← Category.assoc, K.d_pOpcycles, zero_comp]

/-- The degree-zero homology class as a cokernel cofork of `d₁`. -/
def homologyZeroCofork : CokernelCofork (K.d 1 0) :=
  CokernelCofork.ofπ (homologyZeroClass K) (d_comp_homologyZeroClass K)

@[simp]
theorem homologyZeroCofork_π : (homologyZeroCofork K).π = homologyZeroClass K :=
  rfl

/-- The native degree-zero class earns the cokernel universal property. -/
def homologyZeroCoforkIsColimit : IsColimit (homologyZeroCofork K) := by
  let c : CokernelCofork (K.d 1 0) :=
    CokernelCofork.ofπ (K.pOpcycles 0) (K.d_pOpcycles 1 0)
  have hc : IsColimit c := by
    have hprev : (ComplexShape.down ℕ).prev 0 = 1 := by simp
    exact CokernelCofork.isColimitOfIsColimitOfIff'
      (K.sc 0).opcyclesIsCokernel (K.d 1 0) (fun {W} φ => by
        change K.d ((ComplexShape.down ℕ).prev 0) 0 ≫ φ = 0 ↔ K.d 1 0 ≫ φ = 0
        rw [hprev])
  let e : c ≅ homologyZeroCofork K :=
    Cofork.ext K.isoHomologyι₀.symm (by rfl)
  exact IsColimit.ofIsoColimit hc e

variable [HasCokernel (K.d 1 0)]

/-- Native degree-zero homology is the native cokernel of the differential. -/
def homologyZeroIsoCokernel : K.homology 0 ≅ cokernel (K.d 1 0) :=
  IsColimit.coconePointUniqueUpToIso
    (s := homologyZeroCofork K)
    (t := CokernelCofork.ofπ (cokernel.π (K.d 1 0)) (cokernel.condition (K.d 1 0)))
    (homologyZeroCoforkIsColimit K)
    (cokernelIsCokernel (K.d 1 0))

@[reassoc (attr := simp)]
theorem homologyZeroIsoCokernel_class :
    homologyZeroClass K ≫ (homologyZeroIsoCokernel K).hom = cokernel.π (K.d 1 0) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (s := homologyZeroCofork K)
    (t := CokernelCofork.ofπ (cokernel.π (K.d 1 0)) (cokernel.condition (K.d 1 0)))
    (homologyZeroCoforkIsColimit K)
    (cokernelIsCokernel (K.d 1 0)) WalkingParallelPair.one

end Homology

section Naturality

variable {K L : ChainComplex C ℕ} [K.HasHomology 0] [L.HasHomology 0]

/-- Actual chain maps preserve the native degree-zero homology class. -/
@[reassoc]
theorem homologyZeroClass_naturality (φ : K ⟶ L) :
    homologyZeroClass K ≫ HomologicalComplex.homologyMap φ 0 =
      φ.f 0 ≫ homologyZeroClass L := by
  have hi : K.isoHomologyι₀.inv ≫ HomologicalComplex.homologyMap φ 0 =
      HomologicalComplex.opcyclesMap φ 0 ≫ L.isoHomologyι₀.inv :=
    ChainComplex.isoHomologyι₀_inv_naturality φ
  have hp : K.pOpcycles 0 ≫ HomologicalComplex.opcyclesMap φ 0 =
      φ.f 0 ≫ L.pOpcycles 0 :=
    HomologicalComplex.p_opcyclesMap φ 0
  change (K.pOpcycles 0 ≫ K.isoHomologyι₀.inv) ≫
      HomologicalComplex.homologyMap φ 0 =
    φ.f 0 ≫ (L.pOpcycles 0 ≫ L.isoHomologyι₀.inv)
  calc
    _ = K.pOpcycles 0 ≫
        (K.isoHomologyι₀.inv ≫ HomologicalComplex.homologyMap φ 0) :=
      Category.assoc _ _ _
    _ = K.pOpcycles 0 ≫
        (HomologicalComplex.opcyclesMap φ 0 ≫ L.isoHomologyι₀.inv) :=
      congrArg (fun f : K.opcycles 0 ⟶ L.homology 0 => K.pOpcycles 0 ≫ f) hi
    _ = (K.pOpcycles 0 ≫ HomologicalComplex.opcyclesMap φ 0) ≫
        L.isoHomologyι₀.inv := (Category.assoc _ _ _).symm
    _ = (φ.f 0 ≫ L.pOpcycles 0) ≫ L.isoHomologyι₀.inv :=
      congrArg (fun f : K.X 0 ⟶ L.opcycles 0 => f ≫ L.isoHomologyι₀.inv) hp
    _ = _ := Category.assoc _ _ _

variable [HasCokernel (K.d 1 0)] [HasCokernel (L.d 1 0)]

/-- The comparison is natural for the maps of cokernels. -/
@[reassoc]
theorem homologyZeroIsoCokernel_naturality (φ : K ⟶ L) :
    HomologicalComplex.homologyMap φ 0 ≫ (homologyZeroIsoCokernel L).hom =
      (homologyZeroIsoCokernel K).hom ≫
        cokernel.map (K.d 1 0) (L.d 1 0) (φ.f 1) (φ.f 0) (φ.comm 1 0).symm := by
  have hp : cokernel.π (K.d 1 0) ≫
        cokernel.map (K.d 1 0) (L.d 1 0) (φ.f 1) (φ.f 0) (φ.comm 1 0).symm =
      φ.f 0 ≫ cokernel.π (L.d 1 0) :=
    cokernel.π_desc (K.d 1 0) (φ.f 0 ≫ cokernel.π (L.d 1 0)) (by
      rw [← Category.assoc, ← φ.comm 1 0, Category.assoc, cokernel.condition, comp_zero])
  apply Cofork.IsColimit.hom_ext (homologyZeroCoforkIsColimit K)
  change homologyZeroClass K ≫
      (HomologicalComplex.homologyMap φ 0 ≫ (homologyZeroIsoCokernel L).hom) =
    homologyZeroClass K ≫ ((homologyZeroIsoCokernel K).hom ≫
      cokernel.map (K.d 1 0) (L.d 1 0) (φ.f 1) (φ.f 0) (φ.comm 1 0).symm)
  calc
    _ = (homologyZeroClass K ≫ HomologicalComplex.homologyMap φ 0) ≫
        (homologyZeroIsoCokernel L).hom := (Category.assoc _ _ _).symm
    _ = (φ.f 0 ≫ homologyZeroClass L) ≫ (homologyZeroIsoCokernel L).hom :=
      congrArg (fun f : K.X 0 ⟶ L.homology 0 =>
        f ≫ (homologyZeroIsoCokernel L).hom) (homologyZeroClass_naturality φ)
    _ = φ.f 0 ≫ cokernel.π (L.d 1 0) := by
      rw [Category.assoc, homologyZeroIsoCokernel_class]
    _ = cokernel.π (K.d 1 0) ≫
        cokernel.map (K.d 1 0) (L.d 1 0) (φ.f 1) (φ.f 0) (φ.comm 1 0).symm := hp.symm
    _ = _ := by rw [← Category.assoc, homologyZeroIsoCokernel_class]

end Naturality

end ChainComplex
