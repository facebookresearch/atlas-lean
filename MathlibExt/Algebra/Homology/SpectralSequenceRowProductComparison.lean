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
# First-page row products and second-page comparisons

The product on first-page bidegrees induces maps on integer row cycles and on their homology
quotients. The row cycle inclusions and homology projections agree with those of the page, so
the descended row product is the native page homology product and is identified with the E₂
product.

For supplied cochain isomorphisms from rows q,q′ and q+q′ to row-zero models, a product
comparison with sign (−1)^{q p′} descends to cycle and homology products and then to E₂. All
row and horizontal degrees remain arbitrary integers.
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

/-- The object in an integer first-page row.

Its degree-p object is E₁^{p,q}. -/
theorem firstPageRow_X (q p : ℤ) :
    (S.firstPageRow q).X p = (S.page 1).X (p, q) := rfl

/-- The differential of an integer first-page row.

Its differential is the existing page differential between (p,q) and (p′,q). -/
theorem firstPageRow_d (q p p' : ℤ) :
    (S.firstPageRow q).d p p' = (S.page 1).d (p, q) (p', q) := rfl

/-- The inverse row cycle comparison preserves inclusion.

The inverse page-to-row cycle map followed by row inclusion equals page cycle inclusion. -/
@[reassoc]
theorem firstPageRowCyclesIso_inv_i (p q : ℤ) :
    (S.firstPageRowCyclesIso p q).inv ≫ (S.firstPageRow q).iCycles p =
      (S.page 1).iCycles (p, q) := by
  apply (cancel_epi (S.firstPageRowCyclesIso p q).hom).mp
  rw [Iso.hom_inv_id_assoc]
  exact (S.firstPageRowCyclesIso_hom_i p q).symm

/-- The inverse row cycle comparison preserves projection.

The inverse cycle comparison, row homology projection and row homology chart recover the page
projection. -/
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

/-- The second-page comparison of two isomorphic row complexes.

A cochain isomorphism between row q of S and row r of T induces E₂^{p,q}(S) ≅ E₂^{p,r}(T). -/
def firstPageRowSecondPageIsoOfIso (q r : ℤ)
    (i : S.firstPageRow q ≅ T.firstPageRow r) (p : ℤ) :
    (S.page 2).X (p, q) ≅ (T.page 2).X (p, r) :=
  (S.firstPageRowSecondPageIso p q).symm ≪≫
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) p).mapIso i ≪≫
      T.firstPageRowSecondPageIso p r

/-- The row-isomorphism E₂ comparison is its homology map.

The row-to-E₂ charts commute with homology of the supplied cochain isomorphism. -/
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

/-- The raw first-page product on two integer rows.

Pair row q in horizontal degree p with row q′ in degree p′ to obtain row q+q′ in degree p+p′. -/
abbrev firstPageRowPair (q q' p p' : ℤ) :
    ((X.skeletalSpectralSequence).firstPageRow q).X p ⊗
      ((Y.skeletalSpectralSequence).firstPageRow q').X p' ⟶
        ((Z.skeletalSpectralSequence).firstPageRow (q + q')).X (p + p') :=
  P.pagePair 1 le_rfl (p, q) (p', q')

/-- The first-page row product on cycle objects.

Use the row-to-page cycle comparisons, the page cycle product and the output inverse row
comparison. -/
def firstPageRowCyclesPair (q q' p p' : ℤ) :
    ((X.skeletalSpectralSequence).firstPageRow q).cycles p ⊗
      ((Y.skeletalSpectralSequence).firstPageRow q').cycles p' ⟶
        ((Z.skeletalSpectralSequence).firstPageRow (q + q')).cycles (p + p') :=
  (((X.skeletalSpectralSequence).firstPageRowCyclesIso p q).hom ⊗ₘ
    ((Y.skeletalSpectralSequence).firstPageRowCyclesIso p' q').hom) ≫
      P.pageCyclesPair 1 le_rfl (p, q) (p', q') ≫
        ((Z.skeletalSpectralSequence).firstPageRowCyclesIso (p + p') (q + q')).inv

/-- The row cycle product preserves inclusion.

The output row inclusion equals the tensor of input inclusions followed by the raw row
product. -/
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

/-- The row homology product transported from page homology.

Use row homology comparisons to transport the page-1 homology product back to row homology. -/
def firstPageRowNativeHomologyPair (q q' p p' : ℤ) :
    ((X.skeletalSpectralSequence).firstPageRow q).homology p ⊗
      ((Y.skeletalSpectralSequence).firstPageRow q').homology p' ⟶
        ((Z.skeletalSpectralSequence).firstPageRow (q + q')).homology (p + p') :=
  (((X.skeletalSpectralSequence).firstPageRowHomologyIso p q).hom ⊗ₘ
    ((Y.skeletalSpectralSequence).firstPageRowHomologyIso p' q').hom) ≫
      P.pageHomologyPair 1 le_rfl (p, q) (p', q') ≫
        ((Z.skeletalSpectralSequence).firstPageRowHomologyIso (p + p') (q + q')).inv

/-- The transported row homology product preserves projection.

The tensor of row homology projections followed by the product equals the row cycle product
followed by output projection. -/
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

/-- Row boundary products vanish after homology projection.

Both incoming row-boundary sources paired with cycles are killed by the output projection. -/
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

/-- The row homology product obtained by cokernel descent.

Descend the row cycle product through its two boundary cokernels. -/
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

/-- The descended row homology product preserves projections.

The tensor of input projections followed by the descended product equals the cycle product
followed by output projection. -/
@[reassoc]
theorem firstPageRowHomologyPair_π (q q' p p' : ℤ) :
    (((X.skeletalSpectralSequence).firstPageRow q).homologyπ p ⊗ₘ
      ((Y.skeletalSpectralSequence).firstPageRow q').homologyπ p') ≫
        P.firstPageRowHomologyPair q q' p p' =
      P.firstPageRowCyclesPair q q' p p' ≫
        ((Z.skeletalSpectralSequence).firstPageRow (q + q')).homologyπ (p + p') := by
  apply HomologicalComplex.tensor_homologyπ_comp_tensorHomologyDesc

/-- The two row homology product constructions agree.

Cokernel descent gives the same product as transport from native page homology. -/
theorem firstPageRowHomologyPair_eq_native (q q' p p' : ℤ) :
    P.firstPageRowHomologyPair q q' p p' = P.firstPageRowNativeHomologyPair q q' p p' := by
  apply HomologicalComplex.tensor_homologyπ_hom_ext
    ((X.skeletalSpectralSequence).firstPageRow q) (p - 1) p
      (by apply (ComplexShape.up ℤ).prev_eq'; change p - 1 + 1 = p; omega)
    ((Y.skeletalSpectralSequence).firstPageRow q') (p' - 1) p'
      (by apply (ComplexShape.up ℤ).prev_eq'; change p' - 1 + 1 = p'; omega)
  rw [P.firstPageRowHomologyPair_π, P.firstPageRowNativeHomologyPair_π]

/-- The row homology product agrees with the second-page product.

The row-to-E₂ isomorphisms carry the row homology product to pagePair at r=2. -/
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

/-- The signed row comparison preserves cycle products.

Under the given cochain row isomorphisms and product square, cycle products transform with
sign (−1)^{q p′}. -/
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

/-- The signed row comparison preserves homology products.

The induced homology maps carry the product with the same normalization sign (−1)^{q p′}. -/
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

/-- The signed row product comparison on the second page.

The E₂ maps induced by the row isomorphisms intertwine the page products with sign (−1)^{q
p′}. -/
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
