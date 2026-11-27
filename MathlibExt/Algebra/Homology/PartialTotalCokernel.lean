/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import MathlibExt.Algebra.Homology.Embedding.DownNatToIntShiftInvNaturality
public import MathlibExt.Algebra.Homology.PartialTotalFunctor
public import MathlibExt.Algebra.Homology.ShortComplex.CokernelSequence
public import MathlibExt.CategoryTheory.NatTrans.PointwiseArrow

/-!
# Cokernels of partial-total inclusions

This file gives generator lemmas for the cokernel of an arbitrary
first-quadrant partial-total inclusion. The shifted extensionality theorem is
the common mechanism behind the mixed and cyclic Connes-tail comparisons.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace HomologicalComplex₂

section Functoriality

variable {A : Type u} [Category.{v} A] [Preadditive A]
  [HasZeroObject A] [HasFiniteCoproducts A]
  [HasCokernels (ChainComplex A ℕ)]

/-- The canonical partial-total inclusion/cokernel presentation, functorial in
the bicomplex. -/
noncomputable abbrev partialTotalCokernelShortComplexFunctor (p : ℕ) :
    HomologicalComplex₂ A (ComplexShape.down ℕ) (ComplexShape.down ℕ) ⥤
      ShortComplex (ChainComplex A ℕ) :=
  (partialTotalInclusionNatTrans (C := A) p).arrow ⋙
    ShortComplex.cokernelSequenceFunctor

/-- The canonical inclusion/cokernel presentation of a partial-total stage. -/
noncomputable abbrev partialTotalCokernelShortComplex
    (K : HomologicalComplex₂ A (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (p : ℕ) :
    ShortComplex (ChainComplex A ℕ) :=
  ShortComplex.mk (K.partialTotalι p)
    (cokernel.π (K.partialTotalι p))
    (cokernel.condition (K.partialTotalι p))

theorem partialTotalCokernelShortComplexFunctor_obj (p : ℕ)
    (K : HomologicalComplex₂ A (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    (partialTotalCokernelShortComplexFunctor (A := A) p).obj K =
      K.partialTotalCokernelShortComplex p :=
  rfl

/-- A bicomplex morphism induces a morphism of its partial-total cokernel
presentations. -/
noncomputable abbrev partialTotalCokernelShortComplexMap
    {K L : HomologicalComplex₂ A (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)} (φ : K ⟶ L) (p : ℕ) :
    K.partialTotalCokernelShortComplex p ⟶
      L.partialTotalCokernelShortComplex p :=
  (partialTotalCokernelShortComplexFunctor (A := A) p).map φ

@[simp]
theorem partialTotalCokernelShortComplexFunctor_map
    {K L : HomologicalComplex₂ A (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)} (φ : K ⟶ L) (p : ℕ) :
    (partialTotalCokernelShortComplexFunctor (A := A) p).map φ =
      partialTotalCokernelShortComplexMap φ p :=
  rfl

/-- At a fixed filtration stage, the quotient of the full total by the
partial total is functorial in the bicomplex. -/
noncomputable abbrev partialTotalCokernelFunctor (p : ℕ) :
    HomologicalComplex₂ A (ComplexShape.down ℕ) (ComplexShape.down ℕ) ⥤
      ChainComplex A ℕ :=
  partialTotalCokernelShortComplexFunctor (A := A) p ⋙ ShortComplex.π₃

/-- The map of cokernels induced by a morphism of first-quadrant
bicomplexes. -/
noncomputable abbrev partialTotalCokernelMap
    {K L : HomologicalComplex₂ A (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)} (φ : K ⟶ L) (p : ℕ) :
    cokernel (K.partialTotalι p) ⟶ cokernel (L.partialTotalι p) :=
  (partialTotalCokernelFunctor (A := A) p).map φ

/-- The degreewise cokernel projections form a natural transformation from
the full total functor to the partial-total cokernel functor. -/
noncomputable abbrev partialTotalCokernelπ (p : ℕ) :
    HomologicalComplex₂.totalFunctor A (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) (ComplexShape.down ℕ) ⟶
      partialTotalCokernelFunctor (A := A) p :=
  Functor.whiskerLeft
    ((partialTotalInclusionNatTrans (C := A) p).arrow)
    (Limits.coker.π (ChainComplex A ℕ))

/-- The cokernel projections are natural in bicomplex morphisms. -/
@[reassoc]
theorem partialTotalCokernel_π_naturality
    {K L : HomologicalComplex₂ A (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)} (φ : K ⟶ L) (p : ℕ) :
    cokernel.π (K.partialTotalι p) ≫ partialTotalCokernelMap φ p =
      HomologicalComplex₂.total.map φ (ComplexShape.down ℕ) ≫
        cokernel.π (L.partialTotalι p) :=
  ((partialTotalCokernelπ (A := A) p).naturality φ).symm

/-- The cokernel map induced by the identity bicomplex map is the identity. -/
theorem partialTotalCokernelMap_id
    (K : HomologicalComplex₂ A (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (p : ℕ) :
    partialTotalCokernelMap (𝟙 K) p = 𝟙 _ :=
  (partialTotalCokernelFunctor (A := A) p).map_id K

/-- Partial-total cokernel maps compose with bicomplex maps. -/
@[reassoc]
theorem partialTotalCokernelMap_comp
    {K L M : HomologicalComplex₂ A (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)} (φ : K ⟶ L) (ψ : L ⟶ M) (p : ℕ) :
    partialTotalCokernelMap (φ ≫ ψ) p =
      partialTotalCokernelMap φ p ≫ partialTotalCokernelMap ψ p :=
  (partialTotalCokernelFunctor (A := A) p).map_comp φ ψ

theorem partialTotalCokernelFunctor_obj (p : ℕ)
    (K : HomologicalComplex₂ A (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    (partialTotalCokernelFunctor (A := A) p).obj K =
      cokernel (K.partialTotalι p) :=
  rfl

@[simp]
theorem partialTotalCokernelFunctor_map
    {K L : HomologicalComplex₂ A (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)} (φ : K ⟶ L) (p : ℕ) :
    (partialTotalCokernelFunctor (A := A) p).map φ =
      partialTotalCokernelMap φ p :=
  rfl

theorem partialTotalCokernelπ_app (p : ℕ)
    (K : HomologicalComplex₂ A (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    (partialTotalCokernelπ (A := A) p).app K =
      cokernel.π (K.partialTotalι p) :=
  rfl

theorem partialTotalCokernelShortComplexMap_id
    (K : HomologicalComplex₂ A (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (p : ℕ) :
    partialTotalCokernelShortComplexMap (𝟙 K) p = 𝟙 _ :=
  (partialTotalCokernelShortComplexFunctor (A := A) p).map_id K

@[reassoc]
theorem partialTotalCokernelShortComplexMap_comp
    {K L M : HomologicalComplex₂ A (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)} (φ : K ⟶ L) (ψ : L ⟶ M) (p : ℕ) :
    partialTotalCokernelShortComplexMap (φ ≫ ψ) p =
      partialTotalCokernelShortComplexMap φ p ≫
        partialTotalCokernelShortComplexMap ψ p :=
  (partialTotalCokernelShortComplexFunctor (A := A) p).map_comp φ ψ

end Functoriality

section Exactness

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The canonical partial-total inclusion/cokernel presentation is short
exact. -/
theorem partialTotalCokernelShortExact
    (K : HomologicalComplex₂ A (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (p : ℕ) :
    (K.partialTotalCokernelShortComplex p).ShortExact := by
  let _ : Mono (Arrow.mk (K.partialTotalι p)).hom := by
    change Mono (K.partialTotalι p)
    infer_instance
  exact ShortComplex.cokernelSequence_shortExact
    (Arrow.mk (K.partialTotalι p))

end Exactness

section Generators

variable {A : Type u} [Category.{v} A] [Preadditive A]
  [HasZeroObject A] [HasFiniteCoproducts A]
  [HasCokernels (ChainComplex A ℕ)]

/-- A generator in a retained column maps to zero in the cokernel of the
partial-total inclusion. -/
@[reassoc (attr := simp)]
theorem ιTotal_cokernel_partialTotalι_π_eq_zero
    (K : HomologicalComplex₂ A (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (p i j n : ℕ) (hi : i < p + 1)
    (hn : i + j = n) :
    K.ιTotal (ComplexShape.down ℕ) i j n hn ≫
      (cokernel.π (K.partialTotalι p)).f n = 0 := by
  let i' : Fin (p + 1) := ⟨i, hi⟩
  have hfactor := K.partialTotalComponent_comp_partialTotalι
    p i' j n hn
  change K.partialTotalComponent p i' j n hn ≫
      (K.partialTotalι p).f n =
    K.ιTotal (ComplexShape.down ℕ) i j n hn at hfactor
  have hπ : (K.partialTotalι p).f n ≫
      (cokernel.π (K.partialTotalι p)).f n = 0 := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
      HomologicalComplex.congr_hom
        (cokernel.condition (K.partialTotalι p)) n
  rw [← hfactor]
  simp only [Category.assoc, hπ, comp_zero]

/-- A total-complex cell followed by the partial-total cokernel projection
and a chosen shifted-extension coordinate. -/
noncomputable def partialTotalCokernelGenerator
    (K : HomologicalComplex₂ A (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (p : ℕ) (b : ℤ)
    (i j n : ℕ) (hn : i + j = n) (z : ℤ)
    (hz : (ComplexShape.embeddingDownNatToIntShift b).f n = z) :
    (K.X i).X j ⟶
      ((cokernel (K.partialTotalι p)).extend
        (ComplexShape.embeddingDownNatToIntShift b)).X z :=
  K.ιTotal (ComplexShape.down ℕ) i j n hn ≫
    (cokernel.π (K.partialTotalι p)).f n ≫
    ((cokernel (K.partialTotalι p)).extendXIso
      (ComplexShape.embeddingDownNatToIntShift b) hz).inv

/-- At the native shifted degree, the cokernel generator uses the canonical
shifted-extension coordinate. -/
@[reassoc]
theorem partialTotalCokernelGenerator_native
    (K : HomologicalComplex₂ A (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (p : ℕ) (b : ℤ)
    (i j n : ℕ) (hn : i + j = n) :
    K.partialTotalCokernelGenerator p b i j n hn
        (b + (n : ℤ)) (by
          rw [ComplexShape.embeddingDownNatToIntShift_f]) =
      K.ιTotal (ComplexShape.down ℕ) i j n hn ≫
        (cokernel.π (K.partialTotalι p)).f n ≫
        (HomologicalComplex.extendDownNatToIntShiftXIso
          (cokernel (K.partialTotalι p)) b n).inv :=
  rfl

/-- Reindexing a partial-total cokernel generator transports its composites
without changing the underlying cell map. -/
theorem partialTotalCokernelGenerator_comp_heq
    (K : HomologicalComplex₂ A (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (p : ℕ) (b : ℤ) (i j : ℕ)
    {n n' : ℕ} (hn : i + j = n) (hn' : i + j = n')
    {z z' : ℤ}
    (hz : (ComplexShape.embeddingDownNatToIntShift b).f n = z)
    (hz' : (ComplexShape.embeddingDownNatToIntShift b).f n' = z')
    (hnn : n = n') (hzz : z = z') {L : ChainComplex A ℤ}
    (α : (cokernel (K.partialTotalι p)).extend
      (ComplexShape.embeddingDownNatToIntShift b) ⟶ L) :
    HEq (K.partialTotalCokernelGenerator p b i j n hn z hz ≫ α.f z)
      (K.partialTotalCokernelGenerator p b i j n' hn' z' hz' ≫
        α.f z') := by
  cases hnn
  cases hzz
  rfl

/-- Every generator from a retained column vanishes in the shifted
partial-total cokernel. -/
@[simp, reassoc]
theorem partialTotalCokernelGenerator_eq_zero
    (K : HomologicalComplex₂ A (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (p : ℕ) (b : ℤ)
    (i j n : ℕ) (hi : i < p + 1) (hn : i + j = n)
    (z : ℤ) (hz : (ComplexShape.embeddingDownNatToIntShift b).f n = z) :
    K.partialTotalCokernelGenerator p b i j n hn z hz = 0 := by
  unfold partialTotalCokernelGenerator
  rw [← Category.assoc,
    K.ιTotal_cokernel_partialTotalι_π_eq_zero p i j n hi hn,
    zero_comp]

/-- Partial-total cokernel generators are natural in bicomplex morphisms. -/
@[reassoc]
theorem partialTotalCokernelGenerator_naturality
    {K L : HomologicalComplex₂ A (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)} (φ : K ⟶ L) (p : ℕ) (b : ℤ)
    (i j n : ℕ) (hn : i + j = n) (z : ℤ)
    (hz : (ComplexShape.embeddingDownNatToIntShift b).f n = z) :
    K.partialTotalCokernelGenerator p b i j n hn z hz ≫
        (HomologicalComplex.extendMap (partialTotalCokernelMap φ p)
          (ComplexShape.embeddingDownNatToIntShift b)).f z =
      (φ.f i).f j ≫
        L.partialTotalCokernelGenerator p b i j n hn z hz := by
  unfold partialTotalCokernelGenerator
  simp only [Category.assoc]
  rw [HomologicalComplex.extendXIso_inv_naturality]
  have hπ := HomologicalComplex.congr_hom
    (partialTotalCokernel_π_naturality φ p) n
  simp only [HomologicalComplex.comp_f] at hπ
  have hι := HomologicalComplex₂.ιTotal_map
    (K := K) (L := L) (φ := φ) (c₁₂ := ComplexShape.down ℕ)
    i j n hn
  calc
    K.ιTotal (ComplexShape.down ℕ) i j n hn ≫
          (cokernel.π (K.partialTotalι p)).f n ≫
          (partialTotalCokernelMap φ p).f n ≫
          (HomologicalComplex.extendXIso
            (cokernel (L.partialTotalι p))
            (ComplexShape.embeddingDownNatToIntShift b) hz).inv =
        K.ιTotal (ComplexShape.down ℕ) i j n hn ≫
          (((cokernel.π (K.partialTotalι p)).f n ≫
            (partialTotalCokernelMap φ p).f n) ≫
            (HomologicalComplex.extendXIso
              (cokernel (L.partialTotalι p))
              (ComplexShape.embeddingDownNatToIntShift b) hz).inv) := by
      simp only [Category.assoc]
    _ = K.ιTotal (ComplexShape.down ℕ) i j n hn ≫
          (((HomologicalComplex₂.total.map φ
              (ComplexShape.down ℕ)).f n ≫
            (cokernel.π (L.partialTotalι p)).f n) ≫
            (HomologicalComplex.extendXIso
              (cokernel (L.partialTotalι p))
              (ComplexShape.embeddingDownNatToIntShift b) hz).inv) := by
      rw [hπ]
    _ = (K.ιTotal (ComplexShape.down ℕ) i j n hn ≫
            (HomologicalComplex₂.total.map φ
              (ComplexShape.down ℕ)).f n) ≫
          (cokernel.π (L.partialTotalι p)).f n ≫
          (HomologicalComplex.extendXIso
            (cokernel (L.partialTotalι p))
            (ComplexShape.embeddingDownNatToIntShift b) hz).inv := by
      simp only [Category.assoc]
    _ = ((φ.f i).f j ≫
          L.ιTotal (ComplexShape.down ℕ) i j n hn) ≫
          (cokernel.π (L.partialTotalι p)).f n ≫
          (HomologicalComplex.extendXIso
            (cokernel (L.partialTotalι p))
            (ComplexShape.embeddingDownNatToIntShift b) hz).inv := by
      rw [hι]
    _ = (φ.f i).f j ≫
          L.ιTotal (ComplexShape.down ℕ) i j n hn ≫
          (cokernel.π (L.partialTotalι p)).f n ≫
          (HomologicalComplex.extendXIso
            (cokernel (L.partialTotalι p))
            (ComplexShape.embeddingDownNatToIntShift b) hz).inv := by
      simp only [Category.assoc]

end Generators

section Extensionality

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Maps out of a shifted cokernel of a partial-total inclusion are equal
when they agree after every total-complex generator, the degreewise cokernel
projection, and the canonical shifted-extension coordinate. -/
theorem partialTotalCokernel_extend_hom_ext
    (K : HomologicalComplex₂ A (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (p : ℕ) (b : ℤ)
    {L : ChainComplex A ℤ}
    {α β : (cokernel (K.partialTotalι p)).extend
      (ComplexShape.embeddingDownNatToIntShift b) ⟶ L}
    (h : ∀ (i j n : ℕ) (hn : i + j = n),
      K.ιTotal (ComplexShape.down ℕ) i j n hn ≫
          (cokernel.π (K.partialTotalι p)).f n ≫
          (HomologicalComplex.extendDownNatToIntShiftXIso
            (cokernel (K.partialTotalι p)) b n).inv ≫
          α.f (b + (n : ℤ)) =
        K.ιTotal (ComplexShape.down ℕ) i j n hn ≫
          (cokernel.π (K.partialTotalι p)).f n ≫
          (HomologicalComplex.extendDownNatToIntShiftXIso
            (cokernel (K.partialTotalι p)) b n).inv ≫
          β.f (b + (n : ℤ))) :
    α = β := by
  apply HomologicalComplex.hom_ext
  intro z
  by_cases hz : z < b
  · exact (HomologicalComplex.isZero_extendDownNatToIntShift_X_lt
      (cokernel (K.partialTotalι p)) b z hz).eq_of_src _ _
  · let n := (z - b).toNat
    have hn : b + (n : ℤ) = z := by
      dsimp only [n]
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    rw [← hn]
    apply (cancel_epi
      (HomologicalComplex.extendDownNatToIntShiftXIso
        (cokernel (K.partialTotalι p)) b n).inv).1
    apply (cancel_epi ((cokernel.π (K.partialTotalι p)).f n)).1
    apply HomologicalComplex₂.total.hom_ext
    intro i j hij
    simpa only [Category.assoc] using h i j n hij

/-- Maps out of a shifted partial-total cokernel are determined by the
generators in the omitted columns; retained-column generators are killed by
the cokernel relation. -/
theorem partialTotalCokernel_extend_hom_ext_of_tail
    (K : HomologicalComplex₂ A (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (p : ℕ) (b : ℤ)
    {L : ChainComplex A ℤ}
    {α β : (cokernel (K.partialTotalι p)).extend
      (ComplexShape.embeddingDownNatToIntShift b) ⟶ L}
    (h : ∀ (i j n : ℕ) (hn : i + j = n), p + 1 ≤ i →
      K.partialTotalCokernelGenerator p b i j n hn
          (b + (n : ℤ)) (by
            rw [ComplexShape.embeddingDownNatToIntShift_f]) ≫
          α.f (b + (n : ℤ)) =
        K.partialTotalCokernelGenerator p b i j n hn
          (b + (n : ℤ)) (by
            rw [ComplexShape.embeddingDownNatToIntShift_f]) ≫
          β.f (b + (n : ℤ))) :
    α = β := by
  apply K.partialTotalCokernel_extend_hom_ext p b
  intro i j n hn
  rw [← K.partialTotalCokernelGenerator_native_assoc,
    ← K.partialTotalCokernelGenerator_native_assoc]
  by_cases hi : i < p + 1
  · rw [K.partialTotalCokernelGenerator_eq_zero p b i j n hi hn,
      zero_comp, zero_comp]
  · exact h i j n hn (by omega)

end Extensionality

end HomologicalComplex₂
