/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Embedding.ExtendHomologyFunctor

/-!
# Zero extension from natural to integer chain degrees

The embedding n ↦ (n : ℤ) extends nonnegative chain complexes by zero in
negative degrees. Cycles, opcycles and homology in nonnegative degrees
are naturally identified with those of the original complex.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace ComplexShape

set_option backward.defeqAttrib.useBackward true in
/-- The embedding from `down ℕ` to `down ℤ` sending `n ↦ (n : ℤ)`.

This is the `down`-to-`down` analogue of Mathlib's `embeddingDownNat`,
which deliberately lands in `ComplexShape.up ℤ` via `n ↦ -n`. -/
def embeddingDownNatToInt : Embedding (down ℕ) (down ℤ) :=
  Embedding.mk' _ _ (fun n => (n : ℤ))
    (fun _ _ h => by simpa using h)
    (by dsimp; omega)

set_option backward.isDefEq.respectTransparency false in
instance : embeddingDownNatToInt.IsRelIff := by
  dsimp [embeddingDownNatToInt]
  infer_instance

instance : embeddingDownNatToInt.IsTruncLE where
  mem_prev {i j} h := by
    change (j : ℤ) + 1 = i at h
    have hi : (0 : ℤ) ≤ i := by
      have hj : (0 : ℤ) ≤ j := Int.natCast_nonneg j
      omega
    refine ⟨i.toNat, ?_⟩
    change (i.toNat : ℤ) = i
    exact Int.toNat_of_nonneg hi

/-- An integer index is outside the image of `embeddingDownNatToInt`
exactly when it is negative. -/
lemma notMem_range_embeddingDownNatToInt_iff (z : ℤ) :
    (∀ n : ℕ, embeddingDownNatToInt.f n ≠ z) ↔ z < 0 := by
  constructor
  · intro h
    by_contra hz
    apply h z.toNat
    change (z.toNat : ℤ) = z
    exact Int.toNat_of_nonneg (by omega)
  · intro hz n
    change (n : ℤ) ≠ z
    omega

end ComplexShape

section ExtendFunctor

variable (C : Type*) [Category C] [HasZeroObject C] [HasZeroMorphisms C]

/-- Zero-extension functor from `ChainComplex C ℕ` to `ChainComplex C ℤ`
obtained by extending along `ComplexShape.embeddingDownNatToInt`.

This is a thin wrapper around `ComplexShape.Embedding.extendFunctor`. -/
noncomputable def ComplexShape.embeddingDownNatToIntExtendFunctor :
    ChainComplex C ℕ ⥤ ChainComplex C ℤ :=
  ComplexShape.embeddingDownNatToInt.extendFunctor C

end ExtendFunctor

section Homology

/-- Cycles functor isomorphism for the `down ℕ → down ℤ` embedding. -/
noncomputable def HomologicalComplex.cyclesFunctorExtendDownNatToIntIso
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
    [CategoryWithHomology C] (n : ℕ) :
    ComplexShape.embeddingDownNatToInt.extendFunctor C ⋙
      cyclesFunctor C (ComplexShape.down ℤ) (n : ℤ) ≅
      cyclesFunctor C (ComplexShape.down ℕ) n :=
  HomologicalComplex.extendCyclesFunctorIso
    ComplexShape.embeddingDownNatToInt n (n : ℤ) rfl

/-- Opcycles functor isomorphism for the `down ℕ → down ℤ` embedding. -/
noncomputable def HomologicalComplex.opcyclesFunctorExtendDownNatToIntIso
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
    [CategoryWithHomology C] (n : ℕ) :
    ComplexShape.embeddingDownNatToInt.extendFunctor C ⋙
      opcyclesFunctor C (ComplexShape.down ℤ) (n : ℤ) ≅
      opcyclesFunctor C (ComplexShape.down ℕ) n :=
  HomologicalComplex.extendOpcyclesFunctorIso
    ComplexShape.embeddingDownNatToInt n (n : ℤ) rfl

/-- Homology functor isomorphism for the `down ℕ → down ℤ` embedding. -/
noncomputable def HomologicalComplex.homologyFunctorExtendDownNatToIntIso
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
    [CategoryWithHomology C] (n : ℕ) :
    ComplexShape.embeddingDownNatToInt.extendFunctor C ⋙
      homologyFunctor C (ComplexShape.down ℤ) (n : ℤ) ≅
      homologyFunctor C (ComplexShape.down ℕ) n :=
  HomologicalComplex.extendHomologyFunctorIso
    ComplexShape.embeddingDownNatToInt n (n : ℤ) rfl

section CycleComparisons

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]

/-- Canonical cycles isomorphism for zero-extension at a nonnegative degree. -/
noncomputable def HomologicalComplex.cyclesIsoExtendDownNatToInt
    (K : ChainComplex C ℕ) (n : ℕ)
    [K.HasHomology n]
    [(K.extend ComplexShape.embeddingDownNatToInt).HasHomology (n : ℤ)] :
    (K.extend ComplexShape.embeddingDownNatToInt).cycles (n : ℤ) ≅
      K.cycles n :=
  K.extendCyclesIso ComplexShape.embeddingDownNatToInt rfl

/-- Canonical opcycles isomorphism for zero-extension at a nonnegative degree. -/
noncomputable def HomologicalComplex.opcyclesIsoExtendDownNatToInt
    (K : ChainComplex C ℕ) (n : ℕ)
    [K.HasHomology n]
    [(K.extend ComplexShape.embeddingDownNatToInt).HasHomology (n : ℤ)] :
    (K.extend ComplexShape.embeddingDownNatToInt).opcycles (n : ℤ) ≅
      K.opcycles n :=
  K.extendOpcyclesIso ComplexShape.embeddingDownNatToInt rfl

/-- Naturality of the cycles isomorphism with respect to a chain map. -/
@[reassoc]
lemma HomologicalComplex.cyclesIso_extendDownNatToInt_naturality
    {K L : ChainComplex C ℕ} (φ : K ⟶ L) (n : ℕ)
    [K.HasHomology n] [L.HasHomology n]
    [(K.extend ComplexShape.embeddingDownNatToInt).HasHomology (n : ℤ)]
    [(L.extend ComplexShape.embeddingDownNatToInt).HasHomology (n : ℤ)] :
    cyclesMap (extendMap φ ComplexShape.embeddingDownNatToInt) (n : ℤ) ≫
        (cyclesIsoExtendDownNatToInt L n).hom =
      (cyclesIsoExtendDownNatToInt K n).hom ≫ cyclesMap φ n :=
  extendCyclesIso_hom_naturality φ ComplexShape.embeddingDownNatToInt rfl

/-- Naturality of the opcycles isomorphism with respect to a chain map. -/
@[reassoc]
lemma HomologicalComplex.opcyclesIso_extendDownNatToInt_naturality
    {K L : ChainComplex C ℕ} (φ : K ⟶ L) (n : ℕ)
    [K.HasHomology n] [L.HasHomology n]
    [(K.extend ComplexShape.embeddingDownNatToInt).HasHomology (n : ℤ)]
    [(L.extend ComplexShape.embeddingDownNatToInt).HasHomology (n : ℤ)] :
    opcyclesMap (extendMap φ ComplexShape.embeddingDownNatToInt) (n : ℤ) ≫
        (opcyclesIsoExtendDownNatToInt L n).hom =
      (opcyclesIsoExtendDownNatToInt K n).hom ≫ opcyclesMap φ n :=
  extendOpcyclesIso_hom_naturality φ ComplexShape.embeddingDownNatToInt rfl

end CycleComparisons

variable {C : Type*} [Category C] [Abelian C]

/-- Canonical homology isomorphism for the zero-extension at a
nonnegative degree `n : ℕ`. -/
noncomputable def homologyIsoExtendDownNatToInt
    (K : ChainComplex C ℕ) (n : ℕ)
    [K.HasHomology n]
    [(K.extend ComplexShape.embeddingDownNatToInt).HasHomology (n : ℤ)] :
    ((K.extend ComplexShape.embeddingDownNatToInt).homology (n : ℤ) ≅ K.homology n) :=
  (HomologicalComplex.homologyFunctorExtendDownNatToIntIso (C := C) n).app K

@[deprecated homologyIsoExtendDownNatToInt (since := "2026-10-21"),
  nolint defsWithUnderscore]
alias homologyIso_extendDownNatToInt := homologyIsoExtendDownNatToInt

/-- Naturality of the homology isomorphism with respect to a chain map. -/
lemma homologyIso_extendDownNatToInt_naturality
    {K L : ChainComplex C ℕ} (φ : K ⟶ L) (n : ℕ)
    [K.HasHomology n] [L.HasHomology n]
    [(K.extend ComplexShape.embeddingDownNatToInt).HasHomology (n : ℤ)]
    [(L.extend ComplexShape.embeddingDownNatToInt).HasHomology (n : ℤ)] :
    HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNatToInt) (n : ℤ) ≫
        (HomologicalComplex.extendHomologyIso
          ComplexShape.embeddingDownNatToInt (K := L) (j := n) (j' := (n : ℤ)) rfl).hom =
      (HomologicalComplex.extendHomologyIso
          ComplexShape.embeddingDownNatToInt (K := K) (j := n) (j' := (n : ℤ)) rfl).hom ≫
        HomologicalComplex.homologyMap φ n := by
  exact (HomologicalComplex.homologyFunctorExtendDownNatToIntIso
    (C := C) n).hom.naturality φ

/-- Inverse naturality of the homology isomorphism with respect to a chain
map. -/
@[reassoc]
lemma homologyIso_extendDownNatToInt_inv_naturality
    {K L : ChainComplex C ℕ} (φ : K ⟶ L) (n : ℕ)
    [K.HasHomology n] [L.HasHomology n]
    [(K.extend ComplexShape.embeddingDownNatToInt).HasHomology (n : ℤ)]
    [(L.extend ComplexShape.embeddingDownNatToInt).HasHomology (n : ℤ)] :
    HomologicalComplex.homologyMap φ n ≫
        (homologyIsoExtendDownNatToInt L n).inv =
      (homologyIsoExtendDownNatToInt K n).inv ≫
        HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap φ
            ComplexShape.embeddingDownNatToInt) (n : ℤ) :=
  (HomologicalComplex.homologyFunctorExtendDownNatToIntIso
    (C := C) n).inv.naturality φ

/-- The extended complex has zero homology in every negative degree. -/
lemma isZero_homology_extendDownNatToInt_neg
    (K : ChainComplex C ℕ) (z : ℤ) (hz : z < 0)
    [(K.extend ComplexShape.embeddingDownNatToInt).HasHomology z] :
    IsZero ((K.extend ComplexShape.embeddingDownNatToInt).homology z) :=
  HomologicalComplex.isZero_homology_extend_of_notMem_range K
    ComplexShape.embeddingDownNatToInt z
    ((ComplexShape.notMem_range_embeddingDownNatToInt_iff z).mpr hz)

/-- Preservation and reflection of `QuasiIso` by the zero-extension. -/
lemma quasiIso_extendDownNatToInt_iff
    {K L : ChainComplex C ℕ} (φ : K ⟶ L)
    [∀ n : ℕ, K.HasHomology n] [∀ n : ℕ, L.HasHomology n] :
    QuasiIso (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNatToInt) ↔
      QuasiIso φ :=
  HomologicalComplex.quasiIso_extendMap_iff φ ComplexShape.embeddingDownNatToInt

end Homology
