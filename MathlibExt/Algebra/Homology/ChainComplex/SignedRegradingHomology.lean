/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.CategoryTheory.Linear.Basic

/-!
# Signed chain-to-cochain regrading with the literal homology coordinate

At cochain degree k the object is C_(d-k), and the differential is multiplied
by (-1)^(k+1). The homology coordinate is induced by a short-complex isomorphism
whose middle component is identity, not by a degree-rescaling chain isomorphism.
The cycle-inclusion and cycle-to-quotient equations express preservation of
the same categorical representative in every integer degree.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ChainComplex

universe v u

variable {A : Type u} [Category.{v} A]

section Preadditive

variable [Preadditive A]

/-- Regrade a chain complex by d-k, with the target-degree sign on its differential. -/
def signedRegrading (C : ChainComplex A ℤ) (d : ℤ) : CochainComplex A ℤ where
  X k := C.X (d - k)
  d k l := l.negOnePow • C.d (d - k) (d - l)
  shape k l hkl := by
    have h : ¬ (ComplexShape.down ℤ).Rel (d - k) (d - l) := by
      intro h
      apply hkl
      change k + 1 = l
      change (d - l) + 1 = d - k at h
      omega
    rw [C.shape _ _ h, smul_zero]
  d_comp_d' k l m _hkl _hlm := by
    rw [Linear.units_smul_comp, Linear.comp_units_smul,
      C.d_comp_d, smul_zero, smul_zero]

@[simp]
theorem signedRegrading_X (C : ChainComplex A ℤ) (d k : ℤ) :
    (signedRegrading C d).X k = C.X (d - k) := rfl

@[simp]
theorem signedRegrading_d (C : ChainComplex A ℤ) (d k l : ℤ) :
    (signedRegrading C d).d k l = l.negOnePow • C.d (d - k) (d - l) := rfl

/-- An actual chain map has its original reindexed components in the signed complex. -/
def signedRegradingMap {C C' : ChainComplex A ℤ} (f : C ⟶ C') (d : ℤ) :
    signedRegrading C d ⟶ signedRegrading C' d where
  f k := f.f (d - k)
  comm' k l _hkl := by
    change f.f (d - k) ≫ (l.negOnePow • C'.d (d - k) (d - l)) =
      (l.negOnePow • C.d (d - k) (d - l)) ≫ f.f (d - l)
    rw [Linear.comp_units_smul, Linear.units_smul_comp, f.comm]

@[simp]
theorem signedRegradingMap_f {C C' : ChainComplex A ℤ} (f : C ⟶ C') (d k : ℤ) :
    (signedRegradingMap f d).f k = f.f (d - k) := rfl

/-- Signed regrading is functorial on every integer-indexed chain complex. -/
def signedRegradingFunctor (d : ℤ) : ChainComplex A ℤ ⥤ CochainComplex A ℤ where
  obj C := signedRegrading C d
  map f := signedRegradingMap f d
  map_id C := by
    apply HomologicalComplex.Hom.ext
    funext k
    rfl
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext k
    rfl

/-- The incoming sign, identity middle component and outgoing sign at degree k. -/
def signedRegradingShortComplexIso (C : ChainComplex A ℤ) (d k : ℤ) :
    (signedRegrading C d).sc' (k - 1) k (k + 1) ≅
      C.sc' (d - (k - 1)) (d - k) (d - (k + 1)) :=
  ShortComplex.isoMk
    (k.negOnePow • Iso.refl (C.X (d - (k - 1))))
    (Iso.refl (C.X (d - k)))
    ((k + 1).negOnePow • Iso.refl (C.X (d - (k + 1))))
    (by
      change (k.negOnePow • 𝟙 _) ≫ C.d (d - (k - 1)) (d - k) =
        (k.negOnePow • C.d (d - (k - 1)) (d - k)) ≫ 𝟙 _
      rw [Linear.units_smul_comp, Category.id_comp, Category.comp_id])
    (by
      change (𝟙 _) ≫ C.d (d - k) (d - (k + 1)) =
        ((k + 1).negOnePow • C.d (d - k) (d - (k + 1))) ≫
          ((k + 1).negOnePow • 𝟙 _)
      rw [Category.id_comp, Linear.units_smul_comp, Linear.comp_units_smul,
        Category.comp_id, smul_smul, Int.units_mul_self, one_smul])

@[simp]
theorem signedRegradingShortComplexIso_hom_τ₁ (C : ChainComplex A ℤ) (d k : ℤ) :
    (signedRegradingShortComplexIso C d k).hom.τ₁ =
      k.negOnePow • 𝟙 (C.X (d - (k - 1))) := rfl

@[simp]
theorem signedRegradingShortComplexIso_hom_τ₂ (C : ChainComplex A ℤ) (d k : ℤ) :
    (signedRegradingShortComplexIso C d k).hom.τ₂ = 𝟙 (C.X (d - k)) := rfl

@[simp]
theorem signedRegradingShortComplexIso_hom_τ₃ (C : ChainComplex A ℤ) (d k : ℤ) :
    (signedRegradingShortComplexIso C d k).hom.τ₃ =
      (k + 1).negOnePow • 𝟙 (C.X (d - (k + 1))) := rfl

@[simp]
theorem signedRegradingShortComplexIso_inv_τ₁ (C : ChainComplex A ℤ) (d k : ℤ) :
    (signedRegradingShortComplexIso C d k).inv.τ₁ =
      k.negOnePow • 𝟙 (C.X (d - (k - 1))) := by
  change (k.negOnePow)⁻¹ • (𝟙 (C.X (d - (k - 1)))) =
    k.negOnePow • (𝟙 (C.X (d - (k - 1))))
  rw [Int.units_inv_eq_self]

@[simp]
theorem signedRegradingShortComplexIso_inv_τ₂ (C : ChainComplex A ℤ) (d k : ℤ) :
    (signedRegradingShortComplexIso C d k).inv.τ₂ = 𝟙 (C.X (d - k)) := rfl

@[simp]
theorem signedRegradingShortComplexIso_inv_τ₃ (C : ChainComplex A ℤ) (d k : ℤ) :
    (signedRegradingShortComplexIso C d k).inv.τ₃ =
      (k + 1).negOnePow • 𝟙 (C.X (d - (k + 1))) := by
  change ((k + 1).negOnePow)⁻¹ • (𝟙 (C.X (d - (k + 1)))) =
    (k + 1).negOnePow • (𝟙 (C.X (d - (k + 1))))
  rw [Int.units_inv_eq_self]

/-- The three actual short-complex component squares are natural in chain maps. -/
theorem signedRegradingShortComplexIso_naturality
    {C C' : ChainComplex A ℤ} (f : C ⟶ C') (d k : ℤ) :
    (shortComplexFunctor' A (ComplexShape.up ℤ) (k - 1) k (k + 1)).map
        (signedRegradingMap f d) ≫ (signedRegradingShortComplexIso C' d k).hom =
      (signedRegradingShortComplexIso C d k).hom ≫
        (shortComplexFunctor' A (ComplexShape.down ℤ)
          (d - (k - 1)) (d - k) (d - (k + 1))).map f := by
  apply ShortComplex.hom_ext
  · change f.f (d - (k - 1)) ≫ (k.negOnePow • 𝟙 _) =
      (k.negOnePow • 𝟙 _) ≫ f.f (d - (k - 1))
    rw [Linear.comp_units_smul, Linear.units_smul_comp, Category.comp_id, Category.id_comp]
  · change f.f (d - k) ≫ 𝟙 _ = 𝟙 _ ≫ f.f (d - k)
    rw [Category.comp_id, Category.id_comp]
  · change f.f (d - (k + 1)) ≫ ((k + 1).negOnePow • 𝟙 _) =
      ((k + 1).negOnePow • 𝟙 _) ≫ f.f (d - (k + 1))
    rw [Linear.comp_units_smul, Linear.units_smul_comp, Category.comp_id, Category.id_comp]

private theorem up_prev (k : ℤ) : (ComplexShape.up ℤ).prev k = k - 1 :=
  (ComplexShape.up ℤ).prev_eq' (by change (k - 1) + 1 = k; omega)

private theorem up_next (k : ℤ) : (ComplexShape.up ℤ).next k = k + 1 :=
  (ComplexShape.up ℤ).next_eq' (by change k + 1 = k + 1; rfl)

private theorem down_regraded_prev (d k : ℤ) :
    (ComplexShape.down ℤ).prev (d - k) = d - (k - 1) :=
  (ComplexShape.down ℤ).prev_eq' (by change (d - k) + 1 = d - (k - 1); omega)

private theorem down_regraded_next (d k : ℤ) :
    (ComplexShape.down ℤ).next (d - k) = d - (k + 1) :=
  (ComplexShape.down ℤ).next_eq' (by change (d - (k + 1)) + 1 = d - k; omega)

private def nativeShortComplexIso (C : ChainComplex A ℤ) (d k : ℤ) :
    (signedRegrading C d).sc k ≅ C.sc (d - k) :=
  (signedRegrading C d).isoSc' (k - 1) k (k + 1) (up_prev k) (up_next k) ≪≫
    signedRegradingShortComplexIso C d k ≪≫
      (C.isoSc' (d - (k - 1)) (d - k) (d - (k + 1))
        (down_regraded_prev d k) (down_regraded_next d k)).symm

private theorem nativeShortComplexIso_hom_τ₂ (C : ChainComplex A ℤ) (d k : ℤ) :
    (nativeShortComplexIso C d k).hom.τ₂ = 𝟙 (C.X (d - k)) := by
  change (𝟙 (C.X (d - k))) ≫ (𝟙 (C.X (d - k))) ≫
    (𝟙 (C.X (d - k))) = 𝟙 (C.X (d - k))
  rw [Category.id_comp, Category.id_comp]

private theorem nativeShortComplexIso_inv_τ₂ (C : ChainComplex A ℤ) (d k : ℤ) :
    (nativeShortComplexIso C d k).inv.τ₂ = 𝟙 (C.X (d - k)) := by
  change ((𝟙 (C.X (d - k))) ≫ (𝟙 (C.X (d - k)))) ≫
    (𝟙 (C.X (d - k))) = 𝟙 (C.X (d - k))
  rw [Category.id_comp, Category.id_comp]

private theorem nativeShortComplexIso_naturality
    {C C' : ChainComplex A ℤ} (f : C ⟶ C') (d k : ℤ) :
    (shortComplexFunctor A (ComplexShape.up ℤ) k).map (signedRegradingMap f d) ≫
        (nativeShortComplexIso C' d k).hom =
      (nativeShortComplexIso C d k).hom ≫
        (shortComplexFunctor A (ComplexShape.down ℤ) (d - k)).map f := by
  let uC := (signedRegrading C d).isoSc' (k - 1) k (k + 1) (up_prev k) (up_next k)
  let uC' := (signedRegrading C' d).isoSc' (k - 1) k (k + 1) (up_prev k) (up_next k)
  let vC := C.isoSc' (d - (k - 1)) (d - k) (d - (k + 1))
    (down_regraded_prev d k) (down_regraded_next d k)
  let vC' := C'.isoSc' (d - (k - 1)) (d - k) (d - (k + 1))
    (down_regraded_prev d k) (down_regraded_next d k)
  let gD := (shortComplexFunctor A (ComplexShape.up ℤ) k).map (signedRegradingMap f d)
  let gD' := (shortComplexFunctor' A (ComplexShape.up ℤ) (k - 1) k (k + 1)).map
    (signedRegradingMap f d)
  let gC' := (shortComplexFunctor' A (ComplexShape.down ℤ)
    (d - (k - 1)) (d - k) (d - (k + 1))).map f
  let gC := (shortComplexFunctor A (ComplexShape.down ℤ) (d - k)).map f
  have hu : gD ≫ uC'.hom = uC.hom ≫ gD' :=
    (natIsoSc' A (ComplexShape.up ℤ) (k - 1) k (k + 1)
      (up_prev k) (up_next k)).hom.naturality (signedRegradingMap f d)
  have hv : gC' ≫ vC'.inv = vC.inv ≫ gC :=
    (natIsoSc' A (ComplexShape.down ℤ)
      (d - (k - 1)) (d - k) (d - (k + 1))
      (down_regraded_prev d k) (down_regraded_next d k)).inv.naturality f
  have hs : gD' ≫ (signedRegradingShortComplexIso C' d k).hom =
      (signedRegradingShortComplexIso C d k).hom ≫ gC' :=
    signedRegradingShortComplexIso_naturality f d k
  dsimp only [nativeShortComplexIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  change gD ≫ (uC'.hom ≫ (signedRegradingShortComplexIso C' d k).hom ≫ vC'.inv) =
    uC.hom ≫ (signedRegradingShortComplexIso C d k).hom ≫ vC.inv ≫ gC
  calc
    _ = uC.hom ≫ gD' ≫ (signedRegradingShortComplexIso C' d k).hom ≫ vC'.inv := by
      simpa only [Category.assoc] using
        congrArg (fun g => g ≫ (signedRegradingShortComplexIso C' d k).hom ≫ vC'.inv) hu
    _ = uC.hom ≫ (signedRegradingShortComplexIso C d k).hom ≫ gC' ≫ vC'.inv := by
      simpa only [Category.assoc] using congrArg (fun g => uC.hom ≫ g ≫ vC'.inv) hs
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun g => uC.hom ≫ (signedRegradingShortComplexIso C d k).hom ≫ g) hv

end Preadditive

section Homology

variable [Abelian A]

/-- The canonical signed-regrading homology isomorphism with identity middle component. -/
def signedRegradingHomologyIso (C : ChainComplex A ℤ) (d k : ℤ) :
    (signedRegrading C d).homology k ≅ C.homology (d - k) :=
  ShortComplex.homologyMapIso
    ((signedRegrading C d).isoSc' (k - 1) k (k + 1)
      ((ComplexShape.up ℤ).prev_eq' (by change (k - 1) + 1 = k; omega))
      ((ComplexShape.up ℤ).next_eq' (by rfl)) ≪≫
      signedRegradingShortComplexIso C d k ≪≫
        (C.isoSc' (d - (k - 1)) (d - k) (d - (k + 1))
          ((ComplexShape.down ℤ).prev_eq'
            (by change (d - k) + 1 = d - (k - 1); omega))
          ((ComplexShape.down ℤ).next_eq'
            (by change (d - (k + 1)) + 1 = d - k; omega))).symm)

/-- The corresponding actual cycle coordinate, before passing to the quotient. -/
def signedRegradingCyclesIso (C : ChainComplex A ℤ) (d k : ℤ) :
    (signedRegrading C d).cycles k ≅ C.cycles (d - k) :=
  ShortComplex.cyclesMapIso
    ((signedRegrading C d).isoSc' (k - 1) k (k + 1)
      ((ComplexShape.up ℤ).prev_eq' (by change (k - 1) + 1 = k; omega))
      ((ComplexShape.up ℤ).next_eq' (by rfl)) ≪≫
      signedRegradingShortComplexIso C d k ≪≫
        (C.isoSc' (d - (k - 1)) (d - k) (d - (k + 1))
          ((ComplexShape.down ℤ).prev_eq'
            (by change (d - k) + 1 = d - (k - 1); omega))
          ((ComplexShape.down ℤ).next_eq'
            (by change (d - (k + 1)) + 1 = d - k; omega))).symm)

/-- The cycle comparison keeps the literal middle-object representative. -/
@[reassoc]
theorem signedRegradingCyclesIso_hom_iCycles (C : ChainComplex A ℤ) (d k : ℤ) :
    (signedRegradingCyclesIso C d k).hom ≫ C.iCycles (d - k) =
      (signedRegrading C d).iCycles k := by
  change ShortComplex.cyclesMap (nativeShortComplexIso C d k).hom ≫
      (C.sc (d - k)).iCycles = ((signedRegrading C d).sc k).iCycles
  rw [ShortComplex.cyclesMap_i, nativeShortComplexIso_hom_τ₂]
  change ((signedRegrading C d).iCycles k :
      (signedRegrading C d).cycles k ⟶ C.X (d - k)) ≫ 𝟙 (C.X (d - k)) =
    (signedRegrading C d).iCycles k
  exact Category.comp_id
    ((signedRegrading C d).iCycles k :
      (signedRegrading C d).cycles k ⟶ C.X (d - k))

/-- The inverse cycle comparison also keeps the literal representative. -/
@[reassoc]
theorem signedRegradingCyclesIso_inv_iCycles (C : ChainComplex A ℤ) (d k : ℤ) :
    (signedRegradingCyclesIso C d k).inv ≫ (signedRegrading C d).iCycles k =
      C.iCycles (d - k) := by
  change ShortComplex.cyclesMap (nativeShortComplexIso C d k).inv ≫
      ((signedRegrading C d).sc k).iCycles = (C.sc (d - k)).iCycles
  rw [ShortComplex.cyclesMap_i, nativeShortComplexIso_inv_τ₂]
  change C.iCycles (d - k) ≫ 𝟙 (C.X (d - k)) = C.iCycles (d - k)
  exact Category.comp_id (C.iCycles (d - k))

/-- Passing the same cycles to homology gives the exact categorical quotient square. -/
@[reassoc]
theorem signedRegradingHomologyIso_hom_quotient (C : ChainComplex A ℤ) (d k : ℤ) :
    (signedRegrading C d).homologyπ k ≫ (signedRegradingHomologyIso C d k).hom =
      (signedRegradingCyclesIso C d k).hom ≫ C.homologyπ (d - k) :=
  ShortComplex.homologyπ_naturality (nativeShortComplexIso C d k).hom

/-- The reverse quotient square is induced by the actual inverse short-complex map. -/
@[reassoc]
theorem signedRegradingHomologyIso_inv_quotient (C : ChainComplex A ℤ) (d k : ℤ) :
    C.homologyπ (d - k) ≫ (signedRegradingHomologyIso C d k).inv =
      (signedRegradingCyclesIso C d k).inv ≫ (signedRegrading C d).homologyπ k :=
  ShortComplex.homologyπ_naturality (nativeShortComplexIso C d k).inv

/-- Naturality of the same-representative homology coordinate in actual chain maps. -/
@[reassoc]
theorem signedRegradingHomologyIso_naturality
    {C C' : ChainComplex A ℤ} (f : C ⟶ C') (d k : ℤ) :
    homologyMap (signedRegradingMap f d) k ≫ (signedRegradingHomologyIso C' d k).hom =
      (signedRegradingHomologyIso C d k).hom ≫ homologyMap f (d - k) := by
  change ShortComplex.homologyMap
      ((shortComplexFunctor A (ComplexShape.up ℤ) k).map (signedRegradingMap f d)) ≫
      ShortComplex.homologyMap (nativeShortComplexIso C' d k).hom =
    ShortComplex.homologyMap (nativeShortComplexIso C d k).hom ≫
      ShortComplex.homologyMap ((shortComplexFunctor A (ComplexShape.down ℤ) (d - k)).map f)
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp,
    nativeShortComplexIso_naturality]

/-- Naturality already holds before the cycles quotient. -/
@[reassoc]
theorem signedRegradingCyclesIso_naturality
    {C C' : ChainComplex A ℤ} (f : C ⟶ C') (d k : ℤ) :
    cyclesMap (signedRegradingMap f d) k ≫ (signedRegradingCyclesIso C' d k).hom =
      (signedRegradingCyclesIso C d k).hom ≫ cyclesMap f (d - k) := by
  change ShortComplex.cyclesMap
      ((shortComplexFunctor A (ComplexShape.up ℤ) k).map (signedRegradingMap f d)) ≫
      ShortComplex.cyclesMap (nativeShortComplexIso C' d k).hom =
    ShortComplex.cyclesMap (nativeShortComplexIso C d k).hom ≫
      ShortComplex.cyclesMap ((shortComplexFunctor A (ComplexShape.down ℤ) (d - k)).map f)
  rw [← ShortComplex.cyclesMap_comp, ← ShortComplex.cyclesMap_comp,
    nativeShortComplexIso_naturality]

end Homology

end ChainComplex
