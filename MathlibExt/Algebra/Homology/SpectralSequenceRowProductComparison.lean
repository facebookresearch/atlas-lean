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

public import MathlibExt.Algebra.Homology.SpectralSequencePairing
public import MathlibExt.Algebra.Homology.SpectralObject.StepClassToPage
public import MathlibExt.AlgebraicTopology.AtiyahHirzebruch.SkeletalFirstPageRowsNaturality

/-!
# Products on actual first-page rows and their homology

The row cycle kernels retain the original first-page inclusions. Their
homology uses the original row cokernels and the canonical comparison with
the native second page. Products are induced from the original interval
pairing and descend through those actual cycle and homology maps.

All row and cochain degrees are integers. A comparison of coefficient rows
uses genuine cochain isomorphisms, including their differential equations.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u v

namespace CategoryTheory.SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (S : SpectralSequence C
  (fun r => ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) 1)

/-- Row objects are the original objects at their native bidegrees. -/
theorem firstPageRow_X (q p : ℤ) :
    (S.firstPageRow q).X p = (S.page 1).X (p, q) := rfl

/-- Row differentials are the original native first-page differentials. -/
theorem firstPageRow_d (q p p' : ℤ) :
    (S.firstPageRow q).d p p' = (S.page 1).d (p, q) (p', q) := rfl

/-- The inverse of the original landed row-cycle comparison retains the cycle inclusion. -/
@[reassoc]
theorem firstPageRowCyclesIso_inv_i (p q : ℤ) :
    (S.firstPageRowCyclesIso p q).inv ≫ (S.firstPageRow q).iCycles p =
      (S.page 1).iCycles (p, q) := by
  apply (cancel_epi (S.firstPageRowCyclesIso p q).hom).mp
  rw [Iso.hom_inv_id_assoc]
  exact (S.firstPageRowCyclesIso_hom_i p q).symm

/-- The inverse of the original landed cycle comparison retains the homology projection. -/
@[reassoc]
theorem firstPageRowCyclesIso_inv_π (p q : ℤ) :
    (S.firstPageRowCyclesIso p q).inv ≫ (S.firstPageRow q).homologyπ p ≫
        (S.firstPageRowHomologyIso p q).hom =
      (S.page 1).homologyπ (p, q) := by
  apply (cancel_epi (S.firstPageRowCyclesIso p q).hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  exact S.firstPageRowCyclesIso_homologyπ p q

variable {S}
variable {T : SpectralSequence C
  (fun r => ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) 1}

/-- The native second-page comparison induced by a genuine cochain row
isomorphism. The row isomorphism includes its actual differential compatibility. -/
def firstPageRowSecondPageIsoOfIso (q r : ℤ)
    (i : S.firstPageRow q ≅ T.firstPageRow r) (p : ℤ) :
    (S.page 2).X (p, q) ≅ (T.page 2).X (p, r) :=
  (S.firstPageRowSecondPageIso p q).symm ≪≫
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) p).mapIso i ≪≫
      T.firstPageRowSecondPageIso p r

/-- The comparison uses the original row-to-second-page maps and the actual
homology map of the row isomorphism. -/
@[reassoc]
theorem firstPageRowSecondPageIsoOfIso_homology (q r : ℤ)
    (i : S.firstPageRow q ≅ T.firstPageRow r) (p : ℤ) :
    (S.firstPageRowSecondPageIso p q).hom ≫
        (firstPageRowSecondPageIsoOfIso q r i p).hom =
      HomologicalComplex.homologyMap i.hom p ≫ (T.firstPageRowSecondPageIso p r).hom := by
  simp [firstPageRowSecondPageIsoOfIso, HomologicalComplex.homologyFunctor]

end CategoryTheory.SpectralSequence

namespace CategoryTheory.Abelian.SpectralObject.IntervalPairing

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [∀ A : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight A)]
variable {X Y Z : SpectralObject C EInt} (P : IntervalPairing X Y Z)

/-- The original native first-page product on the two integer rows. Its
total-degree Leibniz sign is determined by the first row degree `p + q`. -/
abbrev firstPageRowPair (q q' p p' : ℤ) :
    ((X.skeletalSpectralSequence).firstPageRow q).X p ⊗
      ((Y.skeletalSpectralSequence).firstPageRow q').X p' ⟶
        ((Z.skeletalSpectralSequence).firstPageRow (q + q')).X (p + p') :=
  P.pagePair 1 le_rfl (p, q) (p', q')

/-- The actual product on row cycle kernels induced by the original
native first-page cycle product. -/
def firstPageRowCyclesPair (q q' p p' : ℤ) :
    ((X.skeletalSpectralSequence).firstPageRow q).cycles p ⊗
      ((Y.skeletalSpectralSequence).firstPageRow q').cycles p' ⟶
        ((Z.skeletalSpectralSequence).firstPageRow (q + q')).cycles (p + p') :=
  (((X.skeletalSpectralSequence).firstPageRowCyclesIso p q).hom ⊗ₘ
    ((Y.skeletalSpectralSequence).firstPageRowCyclesIso p' q').hom) ≫
      P.pageCyclesPair 1 le_rfl (p, q) (p', q') ≫
        ((Z.skeletalSpectralSequence).firstPageRowCyclesIso (p + p') (q + q')).inv

/-- The row cycle product retains both original cycle inclusions. -/
@[reassoc]
theorem firstPageRowCyclesPair_i (q q' p p' : ℤ) :
    P.firstPageRowCyclesPair q q' p p' ≫
        ((Z.skeletalSpectralSequence).firstPageRow (q + q')).iCycles (p + p') =
      (((X.skeletalSpectralSequence).firstPageRow q).iCycles p ⊗ₘ
        ((Y.skeletalSpectralSequence).firstPageRow q').iCycles p') ≫
          P.firstPageRowPair q q' p p' := by
  change P.firstPageRowCyclesPair q q' p p' ≫
      (((Z.skeletalSpectralSequence).firstPageRow (q + q')).iCycles (p + p') :
        ((Z.skeletalSpectralSequence).firstPageRow (q + q')).cycles (p + p') ⟶
          ((Z.skeletalSpectralSequence).page 1).X (p + p', q + q')) =
    ((((X.skeletalSpectralSequence).firstPageRow q).iCycles p :
        ((X.skeletalSpectralSequence).firstPageRow q).cycles p ⟶
          ((X.skeletalSpectralSequence).page 1).X (p, q)) ⊗ₘ
      (((Y.skeletalSpectralSequence).firstPageRow q').iCycles p' :
        ((Y.skeletalSpectralSequence).firstPageRow q').cycles p' ⟶
          ((Y.skeletalSpectralSequence).page 1).X (p', q'))) ≫
      P.pagePair 1 le_rfl (p, q) (p', q')
  dsimp only [firstPageRowCyclesPair]
  simp only [Category.assoc,
    (Z.skeletalSpectralSequence).firstPageRowCyclesIso_inv_i (p + p') (q + q')]
  let eX := ((X.skeletalSpectralSequence).firstPageRowCyclesIso p q).hom
  let eY := ((Y.skeletalSpectralSequence).firstPageRowCyclesIso p' q').hom
  let jX := ((X.skeletalSpectralSequence).page 1).iCycles (p, q)
  let jY := ((Y.skeletalSpectralSequence).page 1).iCycles (p', q')
  let pair := P.pagePair 1 le_rfl (p, q) (p', q')
  exact (congrArg (fun f => (eX ⊗ₘ eY) ≫ f)
    (P.pageCyclesPair_i 1 le_rfl (p, q) (p', q'))).trans
      ((Category.assoc (eX ⊗ₘ eY) (jX ⊗ₘ jY) pair).symm.trans
        ((congrArg (fun f => f ≫ pair)
          (tensorHom_comp_tensorHom eX eY jX jY)).trans
            (congrArg (fun f => f ≫ pair)
              (congrArg₂ (fun f g => f ⊗ₘ g)
                ((X.skeletalSpectralSequence).firstPageRowCyclesIso_hom_i p q)
                ((Y.skeletalSpectralSequence).firstPageRowCyclesIso_hom_i p' q')))))

/-- The native page-homology product expressed in the actual row homology
objects. Its quotient formula will identify it with row cokernel descent. -/
def firstPageRowNativeHomologyPair (q q' p p' : ℤ) :
    ((X.skeletalSpectralSequence).firstPageRow q).homology p ⊗
      ((Y.skeletalSpectralSequence).firstPageRow q').homology p' ⟶
        ((Z.skeletalSpectralSequence).firstPageRow (q + q')).homology (p + p') :=
  (((X.skeletalSpectralSequence).firstPageRowHomologyIso p q).hom ⊗ₘ
    ((Y.skeletalSpectralSequence).firstPageRowHomologyIso p' q').hom) ≫
      P.pageHomologyPair 1 le_rfl (p, q) (p', q') ≫
        ((Z.skeletalSpectralSequence).firstPageRowHomologyIso (p + p') (q + q')).inv

/-- The actual row homology projections retain the original native cycle
product and its homology projection. -/
@[reassoc]
theorem firstPageRowNativeHomologyPair_π (q q' p p' : ℤ) :
    (((X.skeletalSpectralSequence).firstPageRow q).homologyπ p ⊗ₘ
      ((Y.skeletalSpectralSequence).firstPageRow q').homologyπ p') ≫
        P.firstPageRowNativeHomologyPair q q' p p' =
      P.firstPageRowCyclesPair q q' p p' ≫
        ((Z.skeletalSpectralSequence).firstPageRow (q + q')).homologyπ (p + p') := by
  apply (cancel_mono
    ((Z.skeletalSpectralSequence).firstPageRowHomologyIso (p + p') (q + q')).hom).mp
  dsimp only [firstPageRowNativeHomologyPair, firstPageRowCyclesPair]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    SpectralSequence.firstPageRowCyclesIso_inv_π]
  rw [← Category.assoc, tensorHom_comp_tensorHom,
    (X.skeletalSpectralSequence).firstPageRowCyclesIso_homologyπ,
    (Y.skeletalSpectralSequence).firstPageRowCyclesIso_homologyπ]
  rw [← tensorHom_comp_tensorHom_assoc, P.pageHomologyPair_π]
  rfl

/-- Both actual row boundaries vanish after the row cycle product and its
actual homology projection. -/
theorem firstPageRowCyclesPair_boundaries_zero (q q' p p' : ℤ) :
    coprod.desc
      (((X.skeletalSpectralSequence).firstPageRow q).toCycles (p - 1) p ▷
        ((Y.skeletalSpectralSequence).firstPageRow q').cycles p')
      (((X.skeletalSpectralSequence).firstPageRow q).cycles p ◁
        ((Y.skeletalSpectralSequence).firstPageRow q').toCycles (p' - 1) p') ≫
      (P.firstPageRowCyclesPair q q' p p' ≫
        ((Z.skeletalSpectralSequence).firstPageRow (q + q')).homologyπ (p + p')) = 0 := by
  rw [← P.firstPageRowNativeHomologyPair_π q q' p p']
  apply coprod.hom_ext
  · simp [tensorHom_def, ← comp_whiskerRight_assoc]
  · simp [tensorHom_def', ← whiskerLeft_comp_assoc]

/-- The product descended through the original row cycle and boundary
cokernels, with no tensor-homology isomorphism assumed. -/
def firstPageRowHomologyPair (q q' p p' : ℤ) :
    ((X.skeletalSpectralSequence).firstPageRow q).homology p ⊗
      ((Y.skeletalSpectralSequence).firstPageRow q').homology p' ⟶
        ((Z.skeletalSpectralSequence).firstPageRow (q + q')).homology (p + p') :=
  HomologicalComplex.tensorHomologyDesc
    ((X.skeletalSpectralSequence).firstPageRow q) (p - 1) p
      (by apply (ComplexShape.up ℤ).prev_eq'; change p - 1 + 1 = p; omega)
    ((Y.skeletalSpectralSequence).firstPageRow q') (p' - 1) p'
      (by apply (ComplexShape.up ℤ).prev_eq'; change p' - 1 + 1 = p'; omega)
    (P.firstPageRowCyclesPair q q' p p' ≫
      ((Z.skeletalSpectralSequence).firstPageRow (q + q')).homologyπ (p + p'))
    (by exact P.firstPageRowCyclesPair_boundaries_zero q q' p p')

/-- The row product's quotient formula uses the actual homology projections. -/
@[reassoc]
theorem firstPageRowHomologyPair_π (q q' p p' : ℤ) :
    (((X.skeletalSpectralSequence).firstPageRow q).homologyπ p ⊗ₘ
      ((Y.skeletalSpectralSequence).firstPageRow q').homologyπ p') ≫
        P.firstPageRowHomologyPair q q' p p' =
      P.firstPageRowCyclesPair q q' p p' ≫
        ((Z.skeletalSpectralSequence).firstPageRow (q + q')).homologyπ (p + p') := by
  apply HomologicalComplex.tensor_homologyπ_comp_tensorHomologyDesc

/-- Row cokernel descent agrees with the actual native homology product. -/
theorem firstPageRowHomologyPair_eq_native (q q' p p' : ℤ) :
    P.firstPageRowHomologyPair q q' p p' = P.firstPageRowNativeHomologyPair q q' p p' := by
  apply HomologicalComplex.tensor_homologyπ_hom_ext
    ((X.skeletalSpectralSequence).firstPageRow q) (p - 1) p
      (by apply (ComplexShape.up ℤ).prev_eq'; change p - 1 + 1 = p; omega)
    ((Y.skeletalSpectralSequence).firstPageRow q') (p' - 1) p'
      (by apply (ComplexShape.up ℤ).prev_eq'; change p' - 1 + 1 = p'; omega)
  rw [P.firstPageRowHomologyPair_π, P.firstPageRowNativeHomologyPair_π]

/-- The original row-to-second-page isomorphisms carry the actual descended
row product to the original native second-page product. -/
@[reassoc]
theorem firstPageRowHomologyPair_secondPage (q q' p p' : ℤ) :
    P.firstPageRowHomologyPair q q' p p' ≫
        ((Z.skeletalSpectralSequence).firstPageRowSecondPageIso (p + p') (q + q')).hom =
      (((X.skeletalSpectralSequence).firstPageRowSecondPageIso p q).hom ⊗ₘ
        ((Y.skeletalSpectralSequence).firstPageRowSecondPageIso p' q').hom) ≫
          P.pagePair 2 (by omega) (p, q) (p', q') := by
  rw [P.firstPageRowHomologyPair_eq_native]
  dsimp only [firstPageRowNativeHomologyPair, SpectralSequence.firstPageRowSecondPageIso,
    Iso.trans_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  let eX := ((X.skeletalSpectralSequence).firstPageRowHomologyIso p q).hom
  let eY := ((Y.skeletalSpectralSequence).firstPageRowHomologyIso p' q').hom
  let sX := ((X.skeletalSpectralSequence).iso 1 2 (p, q) rfl le_rfl).hom
  let sY := ((Y.skeletalSpectralSequence).iso 1 2 (p', q') rfl le_rfl).hom
  let pair := P.pagePair 2 (by omega) (p, q) (p', q')
  exact (congrArg (fun f => (eX ⊗ₘ eY) ≫ f)
    (P.pagePair_successor 1 le_rfl (p, q) (p', q'))).trans
      ((Category.assoc (eX ⊗ₘ eY) (sX ⊗ₘ sY) pair).symm.trans
        (congrArg (fun f => f ≫ pair) (tensorHom_comp_tensorHom eX eY sX sY)))

section Comparison

variable {Xr Yr Zr : SpectralObject C EInt} (Q : IntervalPairing Xr Yr Zr)
variable (q q' : ℤ)
variable
  (iX : (X.skeletalSpectralSequence).firstPageRow q ≅
    (Xr.skeletalSpectralSequence).firstPageRow 0)
  (iY : (Y.skeletalSpectralSequence).firstPageRow q' ≅
    (Yr.skeletalSpectralSequence).firstPageRow 0)
  (iZ : (Z.skeletalSpectralSequence).firstPageRow (q + q') ≅
    (Zr.skeletalSpectralSequence).firstPageRow 0)
  (hpair : ∀ p p' : ℤ,
    P.firstPageRowPair q q' p p' ≫ iZ.hom.f (p + p') =
      ((q * p').negOnePow : ℤ) •
        ((iX.hom.f p ⊗ₘ iY.hom.f p') ≫ Q.firstPageRowPair 0 0 p p'))

include hpair

/-- A proved signed first-page component square induces the same square
on the actual row cycle kernels. -/
@[reassoc]
theorem firstPageRowCyclesPair_naturality (p p' : ℤ) :
    P.firstPageRowCyclesPair q q' p p' ≫
        HomologicalComplex.cyclesMap iZ.hom (p + p') =
      ((q * p').negOnePow : ℤ) •
        ((HomologicalComplex.cyclesMap iX.hom p ⊗ₘ
          HomologicalComplex.cyclesMap iY.hom p') ≫ Q.firstPageRowCyclesPair 0 0 p p') := by
  apply (cancel_mono
    (((Zr.skeletalSpectralSequence).firstPageRow 0).iCycles (p + p'))).mp
  rw [Category.assoc, HomologicalComplex.cyclesMap_i,
    ← Category.assoc, P.firstPageRowCyclesPair_i, Category.assoc, hpair]
  have hQ : Q.firstPageRowCyclesPair 0 0 p p' ≫
      ((Zr.skeletalSpectralSequence).firstPageRow 0).iCycles (p + p') =
    (((Xr.skeletalSpectralSequence).firstPageRow 0).iCycles p ⊗ₘ
      ((Yr.skeletalSpectralSequence).firstPageRow 0).iCycles p') ≫
        Q.firstPageRowPair 0 0 p p' := Q.firstPageRowCyclesPair_i 0 0 p p'
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc]
  rw [hQ]
  conv_rhs =>
    rw [← Category.assoc, tensorHom_comp_tensorHom,
      HomologicalComplex.cyclesMap_i, HomologicalComplex.cyclesMap_i]
  conv_lhs => rw [← Category.assoc, tensorHom_comp_tensorHom]

/-- The signed component square descends through the actual row homology
cokernels. Its only product premise concerns the original first page. -/
@[reassoc]
theorem firstPageRowHomologyPair_naturality (p p' : ℤ) :
    P.firstPageRowHomologyPair q q' p p' ≫
        HomologicalComplex.homologyMap iZ.hom (p + p') =
      ((q * p').negOnePow : ℤ) •
        ((HomologicalComplex.homologyMap iX.hom p ⊗ₘ
          HomologicalComplex.homologyMap iY.hom p') ≫ Q.firstPageRowHomologyPair 0 0 p p') := by
  apply HomologicalComplex.tensor_homologyπ_hom_ext
    ((X.skeletalSpectralSequence).firstPageRow q) (p - 1) p
      (by apply (ComplexShape.up ℤ).prev_eq'; change p - 1 + 1 = p; omega)
    ((Y.skeletalSpectralSequence).firstPageRow q') (p' - 1) p'
      (by apply (ComplexShape.up ℤ).prev_eq'; change p' - 1 + 1 = p'; omega)
  rw [← Category.assoc, P.firstPageRowHomologyPair_π, Category.assoc,
    HomologicalComplex.homologyπ_naturality,
    ← Category.assoc, P.firstPageRowCyclesPair_naturality Q q q' iX iY iZ hpair]
  have hQ :
      (((Xr.skeletalSpectralSequence).firstPageRow 0).homologyπ p ⊗ₘ
        ((Yr.skeletalSpectralSequence).firstPageRow 0).homologyπ p') ≫
          Q.firstPageRowHomologyPair 0 0 p p' =
      Q.firstPageRowCyclesPair 0 0 p p' ≫
        ((Zr.skeletalSpectralSequence).firstPageRow 0).homologyπ (p + p') :=
    Q.firstPageRowHomologyPair_π 0 0 p p'
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc]
  apply congrArg (fun f => ((q * p').negOnePow : ℤ) • f)
  conv_rhs =>
    rw [← Category.assoc, tensorHom_comp_tensorHom,
      HomologicalComplex.homologyπ_naturality, HomologicalComplex.homologyπ_naturality,
      ← tensorHom_comp_tensorHom_assoc, hQ]

/-- The original native second-page products commute with the comparisons
induced by a proved signed E1 row square. Both interval pairings remain
independent inputs, and the Koszul factor uses the original coefficient degree. -/
@[reassoc]
theorem firstPageRowProductComparison_secondPage (p p' : ℤ) :
    P.pagePair 2 (by omega) (p, q) (p', q') ≫
        (SpectralSequence.firstPageRowSecondPageIsoOfIso (q + q') 0 iZ (p + p')).hom =
      ((q * p').negOnePow : ℤ) •
        (((SpectralSequence.firstPageRowSecondPageIsoOfIso q 0 iX p).hom ⊗ₘ
          (SpectralSequence.firstPageRowSecondPageIsoOfIso q' 0 iY p').hom) ≫
            Q.pagePair 2 (by omega) (p, 0) (p', 0)) := by
  apply (cancel_epi
    (((X.skeletalSpectralSequence).firstPageRowSecondPageIso p q).hom ⊗ₘ
      ((Y.skeletalSpectralSequence).firstPageRowSecondPageIso p' q').hom)).mp
  rw [← Category.assoc, ← P.firstPageRowHomologyPair_secondPage,
    Category.assoc, SpectralSequence.firstPageRowSecondPageIsoOfIso_homology,
    ← Category.assoc, P.firstPageRowHomologyPair_naturality Q q q' iX iY iZ hpair]
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc]
  apply congrArg (fun f => ((q * p').negOnePow : ℤ) • f)
  conv_rhs =>
    rw [← Category.assoc, tensorHom_comp_tensorHom,
      SpectralSequence.firstPageRowSecondPageIsoOfIso_homology,
      SpectralSequence.firstPageRowSecondPageIsoOfIso_homology,
      ← tensorHom_comp_tensorHom_assoc]
  have hQ : Q.firstPageRowHomologyPair 0 0 p p' ≫
      ((Zr.skeletalSpectralSequence).firstPageRowSecondPageIso (p + p') 0).hom =
    (((Xr.skeletalSpectralSequence).firstPageRowSecondPageIso p 0).hom ⊗ₘ
      ((Yr.skeletalSpectralSequence).firstPageRowSecondPageIso p' 0).hom) ≫
        Q.pagePair 2 (by omega) (p, 0) (p', 0) :=
    Q.firstPageRowHomologyPair_secondPage 0 0 p p'
  rw [← hQ]

end Comparison

end CategoryTheory.Abelian.SpectralObject.IntervalPairing
