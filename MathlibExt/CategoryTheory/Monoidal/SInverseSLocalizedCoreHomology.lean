/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Homology.FirstQuadrantStageZeroRepresentative
import MathlibExt.Algebra.Homology.Embedding.ExtendHomologyFunctor
import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageSections
import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageCompleteBoundary
import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationFiniteComparison
import MathlibExt.Algebra.Homology.PartialTotalEdgeMaps
import MathlibExt.CategoryTheory.Monoidal.SInverseSGroupCompletionSpectralSequence
public import MathlibExt.CategoryTheory.Monoidal.SInverseSSwapCoreComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanVerticalHomology
import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleUnit
import MathlibExt.CategoryTheory.Monoidal.SInverseSFiberHomologyModuleComparison
import MathlibExt.Algebra.Homology.FirstQuadrantFiltrationNaturality
import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationModuleAbutment
import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationComma
import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationFiberCoreTransport
import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationFilteredHomotopy
import MathlibExt.Algebra.Homology.FirstQuadrantBottomRelativeNaturality
import MathlibExt.Algebra.Homology.SpectralObject.MonoidAction
import MathlibExt.CategoryTheory.CategoryHomology.InitialGenerator
import MathlibExt.CategoryTheory.Monoidal.SInverseSLocalizedSpectralSequence
import MathlibExt.Algebra.Homology.FirstQuadrantAbutmentImage
import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondPageLinearComparison
import MathlibExt.Algebra.Homology.SpectralObject.ZeroColumnEdge
import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationModulePages
import MathlibExt.CategoryTheory.Monoidal.SInverseSActualLocalizedSecondPage
import MathlibExt.CategoryTheory.Monoidal.SInverseSActualLocalizedSecondPageConsequences
public import MathlibExt.CategoryTheory.Monoidal.SInverseSActualLocalizedZeroColumnEdge
import MathlibExt.CategoryTheory.Monoidal.SInverseSLocalizedInitialCoefficientGenerator
import MathlibExt.Algebra.Category.ModuleCat.LocalizationUnit
public import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationAbutmentLocalization

/-!
# Localized whole-core homology and canonical fraction generators

For a small additive category, the original localized Bousfield--Kan zero-column
edge identifies raw localized core homology with the homology of the nerve of
additive `S⁻¹S`. The canonical comparison retains the coefficient zero-column
iso, the literal signed-total localization comparison, and the original abutment.

The negative unit is induced by the negative core inclusion. Its fraction law
uses first-coordinate translation to invert the original second translation.
After coordinate swap, the positive law uses second-coordinate translation.
The unit and fraction laws cover every degree, the whole core module, and every
skeleton-monomial denominator, including the explicit formulas on skeleton classes.
-/

noncomputable section

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits ZeroObject Opposite
open scoped Simplicial

universe uD vD uA vA uC

namespace HomologicalComplex₂

private theorem embedding_eq_of_f_eq
    {I J : Type*} {c : ComplexShape I} {c' : ComplexShape J}
    (e e' : ComplexShape.Embedding c c') (h : e.f = e'.f) : e = e' := by
  cases e
  cases e'
  cases h
  rfl

private theorem zero_column_embedding_eq :
    ComplexShape.embeddingUpIntLE (-(0 : ℤ)) =
      ComplexShape.embeddingDownNat := by
  apply embedding_eq_of_f_eq
  funext n
  simp

variable {D : Type uD} [Category.{vD} D] [Abelian D]

private def zero_direct_column_iso
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    horizontalDirectColumnCochain K 0 ≅
      (K.X 0).extend ComplexShape.embeddingDownNat :=
  horizontalDirectColumnUntwistIso K 0 ≪≫
    eqToIso (congrArg (fun e => (K.X 0).extend e) zero_column_embedding_eq)

private def zero_finite_inclusion_component
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (t : ℕ) : (K.X 0).X t ⟶ (horizontalFilteredTotalComplex K 0).X t :=
  horizontalFilteredTopInclusionComplex K 0 t ≫
    eqToHom (congrArg (fun d => (horizontalFilteredTotalComplex K 0).X d)
      (Nat.zero_add t))

private theorem chain_map_component_cast
    {A B : ChainComplex D ℕ} (f : A ⟶ B)
    (i j : ℕ) (h : i = j) :
    eqToHom (congrArg A.X h) ≫ f.f j =
      f.f i ≫ eqToHom (congrArg B.X h) := by
  cases h
  simp

private theorem total_inclusion_target_cast
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (p q n n' : ℕ) (h : p + q = n) (h' : n = n') :
    K.ιTotal (ComplexShape.down ℕ) p q n h ≫
        eqToHom (congrArg (K.total (ComplexShape.down ℕ)).X h') =
      K.ιTotal (ComplexShape.down ℕ) p q n' (h.trans h') := by
  cases h'
  simp

private theorem zero_finite_inclusion_component_to_total
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (t : ℕ) :
    zero_finite_inclusion_component K t ≫
        (horizontalFilteredTotalComplexToTotal K 0).f t =
      K.ιTotal (ComplexShape.down ℕ) 0 t t (Nat.zero_add t) := by
  have h : horizontalFilteredTopInclusionComplex K 0 t ≫
      (horizontalFilteredTotalComplexToTotal K 0).f (0 + t) =
      K.ιTotal (ComplexShape.down ℕ) 0 t (0 + t) rfl := by
    exact horizontalFilteredTotalι_toTotal K 0 (0 + t)
      (horizontalFilteredTopIndex 0 t)
  calc
    _ = horizontalFilteredTopInclusionComplex K 0 t ≫
        (eqToHom (congrArg (horizontalFilteredTotalComplex K 0).X
          (Nat.zero_add t)) ≫ (horizontalFilteredTotalComplexToTotal K 0).f t) := by
      rw [zero_finite_inclusion_component, Category.assoc]
    _ = (horizontalFilteredTopInclusionComplex K 0 t ≫
        (horizontalFilteredTotalComplexToTotal K 0).f (0 + t)) ≫
        eqToHom (congrArg (K.total (ComplexShape.down ℕ)).X (Nat.zero_add t)) := by
      rw [chain_map_component_cast (horizontalFilteredTotalComplexToTotal K 0)
        (0 + t) t (Nat.zero_add t), Category.assoc]
    _ = K.ιTotal (ComplexShape.down ℕ) 0 t (0 + t) rfl ≫
        eqToHom (congrArg (K.total (ComplexShape.down ℕ)).X (Nat.zero_add t)) := by
      rw [h]
    _ = _ := total_inclusion_target_cast K 0 t (0 + t) t rfl (Nat.zero_add t)

private def zero_finite_inclusion
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    K.X 0 ⟶ horizontalFilteredTotalComplex K 0 where
  f := zero_finite_inclusion_component K
  comm' i j hij := by
    apply (cancel_mono ((horizontalFilteredTotalComplexToTotal K 0).f j)).1
    rw [Category.assoc,
      ← (horizontalFilteredTotalComplexToTotal K 0).comm,
      ← Category.assoc, zero_finite_inclusion_component_to_total,
      Category.assoc, zero_finite_inclusion_component_to_total]
    rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
      K.ι_D₁, K.ι_D₂]
    rw [K.d₁_eq_zero (ComplexShape.down ℕ) 0 i j (by simp)]
    rw [K.d₂_eq (ComplexShape.down ℕ) 0 hij j (by simp)]
    simp

private def zero_complete_inclusion
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    K.X 0 ⟶ horizontalCompleteFilteredTotalComplex K ((0 : ℤ) : EInt) :=
  zero_finite_inclusion K ≫
    (horizontalCompleteFilteredTotalComplexFiniteIso K (0 : ℤ) (le_refl 0)).inv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem zero_finite_top_projection_inverse
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (t : ℕ) :
    zero_finite_inclusion_component K t ≫
        eqToHom (congrArg (fun d => (horizontalFilteredTotalComplex K 0).X d)
          (Nat.zero_add t).symm) ≫ horizontalFilteredTopProjection K 0 t =
      𝟙 ((K.X 0).X t) := by
  let e := eqToIso (congrArg
    (fun d => (horizontalFilteredTotalComplex K 0).X d) (Nat.zero_add t))
  dsimp only [zero_finite_inclusion_component]
  change (horizontalFilteredTopInclusionComplex K 0 t ≫ e.hom) ≫ e.inv ≫
    horizontalFilteredTopProjection K 0 t = _
  calc
    _ = horizontalFilteredTopInclusionComplex K 0 t ≫ (e.hom ≫ e.inv) ≫
        horizontalFilteredTopProjection K 0 t := by simp only [Category.assoc]
    _ = horizontalFilteredTopInclusionComplex K 0 t ≫
        horizontalFilteredTopProjection K 0 t := by rw [e.hom_inv_id]; simp
    _ = _ := by
      change horizontalFilteredTopInclusion K 0 t ≫
        horizontalFilteredTopProjection K 0 t = _
      exact (horizontalFilteredTopProjectionZeroIso K t).inv_hom_id

private theorem zero_untwist_component
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (i : ℤ) :
    (horizontalDirectColumnUntwistIso K 0).hom.f i = 𝟙 _ := by
  dsimp [horizontalDirectColumnUntwistIso, horizontalDirectColumnUntwistXIso]
  simp
  rfl

private theorem extendXIso_inv_transport
    (A : ChainComplex D ℕ)
    (e e' : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ))
    (h : e = e') (t : ℕ) (i : ℤ) (hi : e.f t = i) (hi' : e'.f t = i) :
    (A.extendXIso e hi).inv ≫
        (eqToIso (congrArg (fun e => A.extend e) h)).hom.f i =
      (A.extendXIso e' hi').inv := by
  cases h
  simp

private theorem extendXIso_inv_comp_hom
    (A : ChainComplex D ℕ)
    (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ))
    (a b : ℕ) (hab : a = b) (i : ℤ) (ha : e.f a = i) (hb : e.f b = i) :
    (A.extendXIso e ha).inv ≫ (A.extendXIso e hb).hom =
      eqToHom (congrArg A.X hab) := by
  cases hab
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem zero_finite_projection_supported
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (t : ℕ) :
    (HomologicalComplex.extendMap (zero_finite_inclusion K)
        ComplexShape.embeddingDownNat).f (-(0 : ℤ) - (t : ℤ)) ≫
      (horizontalNaturalDirectColumnProjectionMap K 0).f (-(0 : ℤ) - (t : ℤ)) ≫
        (zero_direct_column_iso K).hom.f (-(0 : ℤ) - (t : ℤ)) = 𝟙 _ := by
  let i : ℤ := -(0 : ℤ) - (t : ℤ)
  let F := horizontalFilteredTotalComplex K 0
  have hd : ComplexShape.embeddingDownNat.f t = i := by
    simp [i, ComplexShape.embeddingDownNat_f]
  have hs : ComplexShape.embeddingDownNat.f (0 + t) = i := by
    simp [i, ComplexShape.embeddingDownNat_f]
  have hu : (ComplexShape.embeddingUpIntLE (-(0 : ℤ))).f t = i := by
    simp [i]
  have htransport :
      ((K.X 0).extendXIso (ComplexShape.embeddingUpIntLE (-(0 : ℤ))) hu).inv ≫
          (zero_direct_column_iso K).hom.f i =
        ((K.X 0).extendXIso ComplexShape.embeddingDownNat hd).inv := by
    dsimp only [zero_direct_column_iso, Iso.trans_hom, HomologicalComplex.comp_f]
    rw [zero_untwist_component]
    simp only [Category.id_comp]
    exact extendXIso_inv_transport (K.X 0) _ _ zero_column_embedding_eq t _ hu hd
  have hcast : (F.extendXIso ComplexShape.embeddingDownNat hd).inv ≫
        (F.extendXIso ComplexShape.embeddingDownNat hs).hom =
      eqToHom (congrArg F.X (Nat.zero_add t).symm) :=
    extendXIso_inv_comp_hom F _ t (0 + t) (Nat.zero_add t).symm i hd hs
  change (HomologicalComplex.extendMap (zero_finite_inclusion K)
      ComplexShape.embeddingDownNat).f i ≫
    horizontalNaturalDirectColumnProjection K 0 i ≫
      (zero_direct_column_iso K).hom.f i = _
  have hp : horizontalNaturalDirectColumnProjection K 0 i =
      horizontalNaturalDirectColumnProjectionComponent K 0 t := by
    dsimp only [i]
    exact horizontalNaturalDirectColumnProjection_eq_component K 0 t
  rw [hp]
  rw [HomologicalComplex.extendMap_f _ _ hd]
  dsimp only [zero_finite_inclusion, horizontalNaturalDirectColumnProjectionComponent,
    horizontalDirectColumnCochainXIso]
  simp only [Category.assoc]
  change ((K.X 0).extendXIso ComplexShape.embeddingDownNat hd).hom ≫
      zero_finite_inclusion_component K t ≫
      (F.extendXIso ComplexShape.embeddingDownNat hd).inv ≫
      (F.extendXIso ComplexShape.embeddingDownNat hs).hom ≫
      horizontalFilteredTopProjection K 0 t ≫
      ((K.X 0).extendXIso (ComplexShape.embeddingUpIntLE (-(0 : ℤ))) hu).inv ≫
      (zero_direct_column_iso K).hom.f i = _
  have hleft : zero_finite_inclusion_component K t ≫
        (F.extendXIso ComplexShape.embeddingDownNat hd).inv ≫
        (F.extendXIso ComplexShape.embeddingDownNat hs).hom ≫
        horizontalFilteredTopProjection K 0 t = 𝟙 _ := by
    calc
      _ = zero_finite_inclusion_component K t ≫
          ((F.extendXIso ComplexShape.embeddingDownNat hd).inv ≫
            (F.extendXIso ComplexShape.embeddingDownNat hs).hom) ≫
          horizontalFilteredTopProjection K 0 t := by simp only [Category.assoc]
      _ = _ := by rw [hcast]; exact zero_finite_top_projection_inverse K t
  calc
    _ = ((K.X 0).extendXIso ComplexShape.embeddingDownNat hd).hom ≫
        (zero_finite_inclusion_component K t ≫
          (F.extendXIso ComplexShape.embeddingDownNat hd).inv ≫
          (F.extendXIso ComplexShape.embeddingDownNat hs).hom ≫
          horizontalFilteredTopProjection K 0 t) ≫
        (((K.X 0).extendXIso (ComplexShape.embeddingUpIntLE (-(0 : ℤ))) hu).inv ≫
          (zero_direct_column_iso K).hom.f i) := by simp only [Category.assoc]
    _ = _ := by rw [hleft, htransport]; simp [i]

private theorem zero_finite_projection_chain_inverse
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    HomologicalComplex.extendMap (zero_finite_inclusion K)
        ComplexShape.embeddingDownNat ≫
      horizontalNaturalDirectColumnProjectionMap K 0 ≫
        (zero_direct_column_iso K).hom = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext i
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
  by_cases hi : i ≤ 0
  · obtain ⟨t, ht⟩ : ∃ t : ℕ, i = -(0 : ℤ) - (t : ℤ) :=
      ⟨(-i).toNat, by rw [Int.toNat_of_nonneg (by omega)]; omega⟩
    subst i
    exact zero_finite_projection_supported K t
  · apply ((K.X 0).isZero_extend_X ComplexShape.embeddingDownNat i
      (fun t ht => by simp only [ComplexShape.embeddingDownNat_f] at ht; omega)).eq_of_src

private theorem zero_complete_projection_chain_inverse
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    HomologicalComplex.extendMap (zero_complete_inclusion K)
        ComplexShape.embeddingDownNat ≫
      horizontalCompleteDirectColumnProjectionMap K 0 ≫
        (zero_direct_column_iso K).hom = 𝟙 _ := by
  rw [horizontalCompleteDirectColumnProjectionMap_eq_finite]
  let c := horizontalCompleteFilteredTotalComplexFiniteIso K (0 : ℤ) (le_refl 0)
  have h : HomologicalComplex.extendMap (zero_complete_inclusion K)
        ComplexShape.embeddingDownNat ≫
      HomologicalComplex.extendMap c.hom ComplexShape.embeddingDownNat =
    HomologicalComplex.extendMap (zero_finite_inclusion K)
      ComplexShape.embeddingDownNat := by
    rw [← HomologicalComplex.extendMap_comp]
    simp only [zero_complete_inclusion, c, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  calc
    _ = (HomologicalComplex.extendMap (zero_complete_inclusion K)
          ComplexShape.embeddingDownNat ≫
        HomologicalComplex.extendMap c.hom ComplexShape.embeddingDownNat) ≫
      horizontalNaturalDirectColumnProjectionMap K 0 ≫
        (zero_direct_column_iso K).hom := by
          simp only [Category.assoc, c]
          rfl
    _ = _ := by rw [h]; exact zero_finite_projection_chain_inverse K

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem zero_direct_column_homology_transport
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (q : ℕ) :
    let n : ℤ := -(q : ℤ)
    let m : ℤ := -((0 : ℕ) : ℤ) - (q : ℤ)
    let hDegree : n = m := by simp [n, m]
    eqToHom (congrArg
        (fun j => (horizontalDirectColumnCochain K 0).homology j) hDegree) ≫
      (horizontalDirectColumnHomologyIso K 0 q).hom =
        HomologicalComplex.homologyMap (zero_direct_column_iso K).hom n ≫
          ((K.X 0).extendHomologyIso ComplexShape.embeddingDownNat
            (by simp [n, ComplexShape.embeddingDownNat_f])).hom := by
  dsimp only
  let n : ℤ := -(q : ℤ)
  let m : ℤ := -((0 : ℕ) : ℤ) - (q : ℤ)
  let hDegree : n = m := by simp [n, m]
  let A := K.X 0
  let u := (horizontalDirectColumnUntwistIso K 0).hom
  let z := eqToIso (congrArg (fun e => A.extend e) zero_column_embedding_eq)
  have hn : ComplexShape.embeddingDownNat.f q = n := by
    simp [n, ComplexShape.embeddingDownNat_f]
  have hm : (ComplexShape.embeddingUpIntLE (-(0 : ℤ))).f q = m := by
    simp [m]
  have hcast := (HomologicalComplex.homologyIsoOfEq_hom_naturality
    u hDegree).symm
  simp only [HomologicalComplex.homologyIsoOfEq_hom] at hcast
  have hext :
      eqToHom (congrArg (fun j => (A.extend
          (ComplexShape.embeddingUpIntLE (-(0 : ℤ)))).homology j)
            hDegree) ≫
          (A.extendHomologyIso
            (ComplexShape.embeddingUpIntLE (-(0 : ℤ))) hm).hom =
        HomologicalComplex.homologyMap z.hom n ≫
          (A.extendHomologyIso ComplexShape.embeddingDownNat hn).hom := by
    simpa only [HomologicalComplex.homologyIsoOfEq_hom, z] using
      (HomologicalComplex.homologyIsoOfEq_hom_extendHomologyIso_hom_of_embedding_eq
        A (ComplexShape.embeddingUpIntLE (-(0 : ℤ)))
          ComplexShape.embeddingDownNat zero_column_embedding_eq
          q n m hn hm hDegree)
  change eqToHom (congrArg
      (fun j => (horizontalDirectColumnCochain K 0).homology j) hDegree) ≫
      (HomologicalComplex.homologyMap u m ≫
        (A.extendHomologyIso (ComplexShape.embeddingUpIntLE (-(0 : ℤ))) hm).hom) =
    HomologicalComplex.homologyMap (u ≫ z.hom) n ≫
      (A.extendHomologyIso ComplexShape.embeddingDownNat hn).hom
  calc
    _ = (eqToHom (congrArg
          (fun j => (horizontalDirectColumnCochain K 0).homology j) hDegree) ≫
          HomologicalComplex.homologyMap u m) ≫
        (A.extendHomologyIso (ComplexShape.embeddingUpIntLE (-(0 : ℤ))) hm).hom := by
      simp only [Category.assoc]
    _ = HomologicalComplex.homologyMap u n ≫
        (eqToHom (congrArg (fun j => (A.extend
          (ComplexShape.embeddingUpIntLE (-(0 : ℤ)))).homology j) hDegree) ≫
          (A.extendHomologyIso (ComplexShape.embeddingUpIntLE (-(0 : ℤ))) hm).hom) := by
      rw [hcast]
      simp only [Category.assoc]
    _ = HomologicalComplex.homologyMap u n ≫
        (HomologicalComplex.homologyMap z.hom n ≫
          (A.extendHomologyIso ComplexShape.embeddingDownNat hn).hom) := by rw [hext]
    _ = _ := by rw [HomologicalComplex.homologyMap_comp]; simp only [Category.assoc]

private def zero_complete_projection_homology
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (q : ℕ) :
    (horizontalCompleteFilteredTotalComplex K ((0 : ℤ) : EInt)).homology q ⟶
      (K.X 0).homology q :=
  let F := horizontalCompleteFilteredTotalComplex K ((0 : ℤ) : EInt)
  let n : ℤ := -(q : ℤ)
  let m : ℤ := -((0 : ℕ) : ℤ) - (q : ℤ)
  let hDegree : n = m := by simp [n, m]
  (F.extendHomologyIso ComplexShape.embeddingDownNat
      (by simp [n, ComplexShape.embeddingDownNat_f])).inv ≫
    HomologicalComplex.homologyMap (horizontalCompleteDirectColumnProjectionMap K 0) n ≫
    eqToHom (congrArg (fun j => (horizontalDirectColumnCochain K 0).homology j) hDegree) ≫
    (horizontalDirectColumnHomologyIso K 0 q).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem zero_complete_inclusion_homology_projection
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (q : ℕ) :
    HomologicalComplex.homologyMap (zero_complete_inclusion K) q ≫
      zero_complete_projection_homology K q = 𝟙 _ := by
  let F := horizontalCompleteFilteredTotalComplex K ((0 : ℤ) : EInt)
  let n : ℤ := -(q : ℤ)
  let m : ℤ := -((0 : ℕ) : ℤ) - (q : ℤ)
  let hDegree : n = m := by simp [n, m]
  have hn : ComplexShape.embeddingDownNat.f q = n := by
    simp [n, ComplexShape.embeddingDownNat_f]
  let eA := (K.X 0).extendHomologyIso ComplexShape.embeddingDownNat hn
  let eF := F.extendHomologyIso ComplexShape.embeddingDownNat hn
  let s := HomologicalComplex.extendMap (zero_complete_inclusion K)
    ComplexShape.embeddingDownNat
  let u := horizontalCompleteDirectColumnProjectionMap K 0
  let cast := eqToHom (congrArg
    (fun j => (horizontalDirectColumnCochain K 0).homology j) hDegree)
  let c := (horizontalDirectColumnHomologyIso K 0 q).hom
  have hnat := HomologicalComplex.extendHomologyIso_inv_naturality
    (zero_complete_inclusion K) ComplexShape.embeddingDownNat hn
  have hcol := zero_direct_column_homology_transport K q
  change (HomologicalComplex.homologyMap (zero_complete_inclusion K) q) ≫
    (eF.inv ≫ HomologicalComplex.homologyMap u n ≫ cast ≫ c) = _
  calc
    _ = (HomologicalComplex.homologyMap (zero_complete_inclusion K) q ≫ eF.inv) ≫
        (HomologicalComplex.homologyMap u n ≫ cast ≫ c) := by simp only [Category.assoc]
    _ = (eA.inv ≫ HomologicalComplex.homologyMap s n) ≫
        (HomologicalComplex.homologyMap u n ≫ cast ≫ c) := by rw [hnat]
    _ = eA.inv ≫ HomologicalComplex.homologyMap s n ≫
        HomologicalComplex.homologyMap u n ≫ (cast ≫ c) := by simp only [Category.assoc]
    _ = eA.inv ≫ HomologicalComplex.homologyMap s n ≫
        HomologicalComplex.homologyMap u n ≫
        HomologicalComplex.homologyMap (zero_direct_column_iso K).hom n ≫ eA.hom := by
      rw [hcol]
    _ = eA.inv ≫ HomologicalComplex.homologyMap
        (s ≫ u ≫ (zero_direct_column_iso K).hom) n ≫ eA.hom := by
      simp only [HomologicalComplex.homologyMap_comp, Category.assoc]
    _ = _ := by
      rw [zero_complete_projection_chain_inverse, HomologicalComplex.homologyMap_id]
      simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem zero_complete_inclusion_native_representative
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (hneg : ∀ (n a : ℤ), a < 0 →
      IsZero (((horizontalCompleteFiltrationSpectralObject K).H n).obj
        (CategoryTheory.ComposableArrows.mk₁
          (homOfLE (bot_le : (⊥ : EInt) ≤ (a : EInt))))))
    (q : ℕ) :
    HomologicalComplex.homologyMap (zero_complete_inclusion K) q ≫
      (horizontalBottomRelativeHomologyStageIso K ((0 : ℤ) : EInt) q).inv ≫
      (horizontalCompleteFiltrationSpectralObject K).nativeZeroColumnStageZeroRepresentative
        hneg q ≫ (horizontalSecondPageVerticalHorizontalHomologyIso K 0 q).hom =
      (K.verticalHomologyComplex q).pOpcycles 0 ≫
        (ChainComplex.isoHomologyι₀ (K.verticalHomologyComplex q)).inv := by
  have h := horizontalSecondPageZeroColumnStageRepresentative K hneg q
  dsimp only at h
  change (horizontalBottomRelativeHomologyStageIso K ((0 : ℤ) : EInt) q).inv ≫
      (horizontalCompleteFiltrationSpectralObject K).nativeZeroColumnStageZeroRepresentative
        hneg q ≫ (horizontalSecondPageVerticalHorizontalHomologyIso K 0 q).hom =
    zero_complete_projection_homology K q ≫ (K.verticalHomologyComplex q).pOpcycles 0 ≫
      (ChainComplex.isoHomologyι₀ (K.verticalHomologyComplex q)).inv at h
  calc
    _ = HomologicalComplex.homologyMap (zero_complete_inclusion K) q ≫
        ((horizontalBottomRelativeHomologyStageIso K ((0 : ℤ) : EInt) q).inv ≫
          (horizontalCompleteFiltrationSpectralObject K).nativeZeroColumnStageZeroRepresentative
            hneg q ≫ (horizontalSecondPageVerticalHorizontalHomologyIso K 0 q).hom) := by
      rfl
    _ = HomologicalComplex.homologyMap (zero_complete_inclusion K) q ≫
        (zero_complete_projection_homology K q ≫ (K.verticalHomologyComplex q).pOpcycles 0 ≫
          (ChainComplex.isoHomologyι₀ (K.verticalHomologyComplex q)).inv) := by rw [h]
    _ = (HomologicalComplex.homologyMap (zero_complete_inclusion K) q ≫
        zero_complete_projection_homology K q) ≫ (K.verticalHomologyComplex q).pOpcycles 0 ≫
          (ChainComplex.isoHomologyι₀ (K.verticalHomologyComplex q)).inv := by
      simp only [Category.assoc]
    _ = _ := by rw [zero_complete_inclusion_homology_projection]; simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem zero_complete_inclusion_to_total
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    zero_complete_inclusion K ≫
        horizontalCompleteFilteredTotalToTotal K ((0 : ℤ) : EInt) =
      K.partialTotalZeroRowToTotal := by
  let c := horizontalCompleteFilteredTotalComplexFiniteIso K (0 : ℤ) (le_refl 0)
  have h : c.hom ≫ horizontalFilteredTotalComplexToTotal K 0 =
      horizontalCompleteFilteredTotalToTotal K ((0 : ℤ) : EInt) :=
    horizontalCompleteFilteredTotalComplexFiniteIso_hom_toTotal K (0 : ℤ) (le_refl 0)
  rw [← h]
  change (zero_finite_inclusion K ≫ c.inv) ≫
    (c.hom ≫ horizontalFilteredTotalComplexToTotal K 0) = _
  calc
    _ = zero_finite_inclusion K ≫ (c.inv ≫ c.hom) ≫
        horizontalFilteredTotalComplexToTotal K 0 := by simp only [Category.assoc]
    _ = zero_finite_inclusion K ≫ horizontalFilteredTotalComplexToTotal K 0 := by
      rw [c.inv_hom_id]
      simp
    _ = _ := by
      apply HomologicalComplex.Hom.ext
      funext t
      change zero_finite_inclusion_component K t ≫
          (horizontalFilteredTotalComplexToTotal K 0).f t =
        K.ιTotal (ComplexShape.down ℕ) 0 t t (Nat.zero_add t)
      exact zero_finite_inclusion_component_to_total K t

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem zero_finite_inclusion_naturality
    {K L : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ)}
    (f : K ⟶ L) :
    f.f 0 ≫ zero_finite_inclusion L =
      zero_finite_inclusion K ≫ horizontalFilteredTotalComplexMapOfBicomplex f 0 := by
  apply HomologicalComplex.Hom.ext
  funext t
  change (f.f 0).f t ≫ zero_finite_inclusion_component L t =
    zero_finite_inclusion_component K t ≫
      (horizontalFilteredTotalComplexMapOfBicomplex f 0).f t
  have htop : horizontalFilteredTopInclusionComplex K 0 t ≫
        (horizontalFilteredTotalComplexMapOfBicomplex f 0).f (0 + t) =
      (f.f 0).f t ≫ horizontalFilteredTopInclusionComplex L 0 t :=
    horizontalFilteredTotalι_mapOfBicomplex f 0 (0 + t)
      (horizontalFilteredTopIndex 0 t)
  symm
  calc
    _ = horizontalFilteredTopInclusionComplex K 0 t ≫
        ((horizontalFilteredTotalComplexMapOfBicomplex f 0).f (0 + t) ≫
          eqToHom (congrArg (horizontalFilteredTotalComplex L 0).X (Nat.zero_add t))) := by
      rw [zero_finite_inclusion_component, Category.assoc,
        chain_map_component_cast (horizontalFilteredTotalComplexMapOfBicomplex f 0)
          (0 + t) t (Nat.zero_add t)]
    _ = ((f.f 0).f t ≫ horizontalFilteredTopInclusionComplex L 0 t) ≫
        eqToHom (congrArg (horizontalFilteredTotalComplex L 0).X (Nat.zero_add t)) := by
      rw [← Category.assoc, htop]
    _ = _ := by rw [zero_finite_inclusion_component, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem zero_complete_inclusion_naturality
    {K L : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ)}
    (f : K ⟶ L) :
    f.f 0 ≫ zero_complete_inclusion L =
      zero_complete_inclusion K ≫
        horizontalCompleteFilteredTotalComplexMapOfBicomplex f ((0 : ℤ) : EInt) := by
  let cK := horizontalCompleteFilteredTotalComplexFiniteIso K (0 : ℤ) (le_refl 0)
  let cL := horizontalCompleteFilteredTotalComplexFiniteIso L (0 : ℤ) (le_refl 0)
  let ffin := horizontalFilteredTotalComplexMapOfBicomplex f 0
  let fcomp := horizontalCompleteFilteredTotalComplexMapOfBicomplex f ((0 : ℤ) : EInt)
  have hnat : cK.hom ≫ ffin = fcomp ≫ cL.hom :=
    horizontalCompleteFilteredTotalComplexFiniteIso_naturality f (0 : ℤ) (le_refl 0)
  have hinv : ffin ≫ cL.inv = cK.inv ≫ fcomp := by
    calc
      _ = cK.inv ≫ (cK.hom ≫ ffin) ≫ cL.inv := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = cK.inv ≫ (fcomp ≫ cL.hom) ≫ cL.inv := by rw [hnat]
      _ = cK.inv ≫ fcomp ≫ (cL.hom ≫ cL.inv) := by simp only [Category.assoc]
      _ = _ := by rw [cL.hom_inv_id, Category.comp_id]
  change f.f 0 ≫ (zero_finite_inclusion L ≫ cL.inv) =
    (zero_finite_inclusion K ≫ cK.inv) ≫ fcomp
  calc
    _ = (f.f 0 ≫ zero_finite_inclusion L) ≫ cL.inv := by rw [Category.assoc]
    _ = (zero_finite_inclusion K ≫ ffin) ≫ cL.inv := by
      rw [zero_finite_inclusion_naturality]
    _ = zero_finite_inclusion K ≫ (ffin ≫ cL.inv) := by rw [Category.assoc]
    _ = _ := by rw [hinv, Category.assoc]

end HomologicalComplex₂


namespace CategoryTheory.SInverseS

private abbrev zeroSimplexMap (n : ℕ) : ⦋n⦌ ⟶ ⦋0⦌ :=
  SimplexCategory.const ⦋n⦌ ⦋0⦌ 0

private theorem zeroSimplexMap_zero : zeroSimplexMap 0 = 𝟙 ⦋0⦌ := by
  ext j
  simp [zeroSimplexMap, SimplexCategory.const]

private theorem zeroSimplexMap_succ (n : ℕ) :
    zeroSimplexMap (n + 1) =
      SimplexCategory.σ (0 : Fin (n + 1)) ≫ zeroSimplexMap n := by
  ext j
  rfl

section Shuffle

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
  (B : SimplicialObject (SimplicialObject A))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem diagonal_cast_cancel {m n : ℕ} (h : m = n) :
    AlgebraicTopology.Bisimplicial.map B
        (eqToHom (congrArg SimplexCategory.mk h))
        (eqToHom (congrArg SimplexCategory.mk h)) ≫
      eqToHom (congrArg (fun k =>
        (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X k) h) =
      𝟙 ((AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X n) := by
  rw [AlgebraicTopology.Bisimplicial.map_eqToHom B h h]
  subst n
  change 𝟙 ((B.obj (op ⦋m⦌)).obj (op ⦋m⦌)) ≫
      𝟙 ((B.obj (op ⦋m⦌)).obj (op ⦋m⦌)) = _
  exact Category.id_comp _

variable [HasCountableCoproducts A]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem zeroRow_shuffle_component (n : ℕ) :
    (AlgebraicTopology.bisimplicialAlternatingBicomplex A B).ιTotal
        (ComplexShape.down ℕ) 0 n n (Nat.zero_add n) ≫
      (AlgebraicTopology.BisimplicialEilenbergZilber.alternatingMap B).f n =
        (B.map (zeroSimplexMap n).op).app (op ⦋n⦌) := by
  let _ : Unique (AlgebraicTopology.EilenbergZilber.Shuffle 0 n) :=
    { default := AlgebraicTopology.EilenbergZilber.Shuffle.leftUnitShuffle n
      uniq := fun s => AlgebraicTopology.EilenbergZilber.Shuffle.eq_leftUnitShuffle s }
  rw [AlgebraicTopology.BisimplicialEilenbergZilber.alternatingMap_f,
    AlgebraicTopology.BisimplicialEilenbergZilber.totalι_comp_component,
    AlgebraicTopology.BisimplicialEilenbergZilber.shuffleBidegree, Fintype.sum_unique,
    AlgebraicTopology.EilenbergZilber.Shuffle.eq_leftUnitShuffle
      (default : AlgebraicTopology.EilenbergZilber.Shuffle 0 n)]
  simp only [AlgebraicTopology.BisimplicialEilenbergZilber.shuffleSummand,
    AlgebraicTopology.EilenbergZilber.Shuffle.leftUnitShuffle_sign, one_smul,
    AlgebraicTopology.BisimplicialEilenbergZilber.shuffleMap,
    AlgebraicTopology.EilenbergZilber.Shuffle.leftUnitShuffle_leftHom,
    AlgebraicTopology.EilenbergZilber.Shuffle.leftUnitShuffle_rightHom]
  let c : ⦋0 + n⦌ ⟶ ⦋n⦌ := eqToHom (congrArg SimplexCategory.mk (Nat.zero_add n))
  have hp :
      AlgebraicTopology.Bisimplicial.map B (zeroSimplexMap n) (𝟙 ⦋n⦌) ≫
        AlgebraicTopology.Bisimplicial.map B c c =
      AlgebraicTopology.Bisimplicial.map B (c ≫ zeroSimplexMap n) c := by
    simpa only [Category.comp_id] using
      AlgebraicTopology.Bisimplicial.map_comp B (zeroSimplexMap n) (𝟙 ⦋n⦌) c c
  change AlgebraicTopology.Bisimplicial.map B (c ≫ zeroSimplexMap n) c ≫
      eqToHom (congrArg (fun k =>
        (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X k)
        (Nat.zero_add n)) = _
  rw [← hp, Category.assoc, diagonal_cast_cancel B (Nat.zero_add n)]
  change AlgebraicTopology.Bisimplicial.map B (zeroSimplexMap n) (𝟙 ⦋n⦌) ≫
      𝟙 ((B.obj (op ⦋n⦌)).obj (op ⦋n⦌)) = _
  rw [Category.comp_id]
  simp only [AlgebraicTopology.Bisimplicial.map, op_id, Functor.map_id, Category.comp_id]

end Shuffle

section ConstantBase

variable {J : Type uC} [Category.{uC} J]

private abbrev constantBaseIndex (i : J) (n : ℕ) :
    StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n :=
  ⟨SrepBridge.constChain i n, PUnit.unit⟩

private theorem constantBaseIndex_degZero (i : J) (n : ℕ) :
    StrictOrdinaryWeightedBar.wDegZeroIdx (CategoryBar.replUnit J) n
        (constantBaseIndex i n) = constantBaseIndex i (n + 1) := by
  have hchain :
      SrepBridge.srepDupFirst (SrepBridge.constChain i n) =
        SrepBridge.constChain i (n + 1) := by
    apply Functor.hext
    · intro x
      rcases x with ⟨a, ha⟩
      obtain _ | a := a <;> rfl
    · intro x y f
      rcases x with ⟨a, ha⟩
      rcases y with ⟨b, hb⟩
      obtain _ | a := a
      · obtain _ | b := b
        · apply heq_of_eq
          change 𝟙 i = 𝟙 i
          rfl
        · obtain _ | b := b
          · apply heq_of_eq
            change 𝟙 i = 𝟙 i
            rfl
          · apply heq_of_eq
            change (𝟙 i) ≫ 𝟙 i = 𝟙 i
            exact Category.id_comp _
      · obtain _ | b := b
        · exfalso
          have hle : a + 1 ≤ 0 := leOfHom f
          omega
        · apply heq_of_eq
          simp [SrepBridge.srepDupFirst, SrepBridge.constChain,
            ComposableArrows.Precomp.map]
  refine Sigma.ext hchain ?_
  change HEq PUnit.unit PUnit.unit
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem constantBase_outerMap (D : J ⥤ SSet.{uC}) (i : J) (n : ℕ) :
    StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D 0
        (constantBaseIndex i 0) ≫
      (StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D).map
        (zeroSimplexMap n).op =
      StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n
        (constantBaseIndex i n) := by
  induction n with
  | zero =>
    rw [zeroSimplexMap_zero, op_id, Functor.map_id]
    change _ ≫ 𝟙 (StrictOrdinaryWeightedBar.wbarObj (CategoryBar.replUnit J) D 0) = _
    exact Category.comp_id _
  | succ n ih =>
    rw [zeroSimplexMap_succ, op_comp, Functor.map_comp, ← Category.assoc, ih,
      StrictOrdinaryWeightedBar.wbarSimplicial_map_σ,
      StrictOrdinaryWeightedBar.wbarσ_zero,
      StrictOrdinaryWeightedBar.wbarDegZero_ι]
    change 𝟙 (D.obj i) ≫ _ = _
    rw [Category.id_comp]
    have hTransport (a b : StrictOrdinaryWeightedBar.WIdx J
        (CategoryBar.replUnit J) (n + 1)) (h : a = b) :
        HEq (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D (n + 1) a)
          (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D (n + 1) b) := by
      cases h
      rfl
    exact eq_of_heq (hTransport _ _ (constantBaseIndex_degZero i n))

end ConstantBase

section RowDiagonal

variable {J : Type uC} [Category.{uC} J] (D : J ⥤ SSet.{uC}) (R : AddCommGrpCat.{uC})

private theorem rowIso_hom_f (n : ℕ) :
    (eqToIso (SSet.bkAlternatingBicomplex_X_eq_chainComplex R D 0).symm).hom.f n =
      𝟙 (((StrictOrdinaryWeightedBar.wbarObj (CategoryBar.replUnit J) D 0).chainComplex R).X n) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem diagonalIso_hom_f (n : ℕ) :
    (SSet.bkDiagonalAlternatingComplexIso AddCommGrpCat.{uC} R D).hom.f n =
      𝟙 (((SSet.bkLinearizedBisimplicial AddCommGrpCat.{uC} R D).obj
        (op ⦋n⦌)).obj (op ⦋n⦌)) := by
  unfold SSet.bkDiagonalAlternatingComplexIso
  rw [Functor.mapIso_hom, AlgebraicTopology.alternatingFaceMapComplex_map_f]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem row_shuffle_diagonal_generator (i : J) (n : ℕ) (y : (D.obj i) _⦋n⦌) :
    (D.obj i).ιChainComplex y ≫
      (SSet.chainComplexMap
        (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D 0
          (constantBaseIndex i 0)) R).f n ≫
      (eqToIso (SSet.bkAlternatingBicomplex_X_eq_chainComplex R D 0).symm).hom.f n ≫
      (SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R D).partialTotalZeroRowToTotal.f n ≫
      (AlgebraicTopology.BisimplicialEilenbergZilber.alternatingMap
        (SSet.bkLinearizedBisimplicial AddCommGrpCat.{uC} R D)).f n ≫
      (SSet.bkDiagonalAlternatingComplexIso AddCommGrpCat.{uC} R D).hom.f n =
    (SSet.bkHocolim D).ιChainComplex
      ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n
        (constantBaseIndex i n)).app (op ⦋n⦌) y) := by
  let B := SSet.bkLinearizedBisimplicial AddCommGrpCat.{uC} R D
  let K := SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R D
  let U := StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D
  let P₀ := StrictOrdinaryWeightedBar.wbarObj (CategoryBar.replUnit J) D 0
  let Pn := StrictOrdinaryWeightedBar.wbarObj (CategoryBar.replUnit J) D n
  let incl : D.obj i ⟶ P₀ := StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D 0
    (constantBaseIndex i 0)
  let incln : D.obj i ⟶ Pn := StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n
    (constantBaseIndex i n)
  let u := incl.app (op ⦋n⦌) y
  let v : (SSet.bkHocolim D) _⦋n⦌ := incln.app (op ⦋n⦌) y
  let z : (SSet.bkHocolim D) _⦋n⦌ := (U.map (zeroSimplexMap n).op).app (op ⦋n⦌) u
  let t : (P₀.chainComplex R).X n ⟶ (K.total (ComplexShape.down ℕ)).X n :=
    K.partialTotalZeroRowToTotal.f n
  let sh : (K.total (ComplexShape.down ℕ)).X n ⟶
      (B.obj (op ⦋n⦌)).obj (op ⦋n⦌) :=
    (AlgebraicTopology.BisimplicialEilenbergZilber.alternatingMap B).f n
  let d : ((SSet.bkHocolim D).chainComplex R).X n ⟶
      ((SSet.bkHocolim D).chainComplex R).X n :=
    (SSet.bkDiagonalAlternatingComplexIso AddCommGrpCat.{uC} R D).hom.f n
  have hShuffle : t ≫ sh =
        (B.map (zeroSimplexMap n).op).app (op ⦋n⦌) :=
    zeroRow_shuffle_component B n
  have hLinear : P₀.ιChainComplex u ≫ (B.map (zeroSimplexMap n).op).app (op ⦋n⦌) =
      Pn.ιChainComplex ((U.map (zeroSimplexMap n).op).app (op ⦋n⦌) u) := by
    change P₀.ιChainComplex u ≫
        (SSet.chainComplexMap (U.map (zeroSimplexMap n).op) R).f n = _
    exact SSet.ι_chainComplexMap_f (X := P₀) (Y := Pn)
      (f := U.map (zeroSimplexMap n).op) (R := R) u
  have hConst : (U.map (zeroSimplexMap n).op).app (op ⦋n⦌) u = v :=
    congrArg (fun f : D.obj i ⟶ Pn => f.app (op ⦋n⦌) y)
      (constantBase_outerMap D i n)
  have hLinear' : P₀.ιChainComplex u ≫ (B.map (zeroSimplexMap n).op).app (op ⦋n⦌) =
      (SSet.bkHocolim D).ιChainComplex z := hLinear
  have hd : d = 𝟙 (((SSet.bkHocolim D).chainComplex R).X n) :=
    diagonalIso_hom_f D R n
  change (D.obj i).ιChainComplex y ≫ (SSet.chainComplexMap incl R).f n ≫
      (eqToIso (SSet.bkAlternatingBicomplex_X_eq_chainComplex R D 0).symm).hom.f n ≫
      t ≫ sh ≫ d = (SSet.bkHocolim D).ιChainComplex v
  rw [SSet.ι_chainComplexMap_f_assoc, rowIso_hom_f]
  change P₀.ιChainComplex u ≫ 𝟙 (P₀.chainComplex R).X n ≫
      t ≫ sh ≫ d = (SSet.bkHocolim D).ιChainComplex v
  have hId : P₀.ιChainComplex u ≫ 𝟙 ((P₀.chainComplex R).X n) ≫ t ≫ sh ≫ d =
      P₀.ιChainComplex u ≫ t ≫ sh ≫ d :=
    (P₀.ιChainComplex u) ≫= Category.id_comp (t ≫ sh ≫ d)
  refine hId.trans ?_
  calc
    _ = P₀.ιChainComplex u ≫
        (t ≫ sh) ≫ d := by
      simp only [Category.assoc]
    _ = P₀.ιChainComplex u ≫ (B.map (zeroSimplexMap n).op).app (op ⦋n⦌) ≫ d := by
      rw [hShuffle]
    _ = (SSet.bkHocolim D).ιChainComplex z ≫ d := by
      simpa only [Category.assoc] using hLinear' =≫ d
    _ = (SSet.bkHocolim D).ιChainComplex z ≫
        𝟙 (((SSet.bkHocolim D).chainComplex R).X n) :=
      (SSet.bkHocolim D).ιChainComplex z ≫= hd
    _ = (SSet.bkHocolim D).ιChainComplex z := Category.comp_id _
    _ = _ := congrArg (fun w : (SSet.bkHocolim D) _⦋n⦌ =>
      (SSet.bkHocolim D).ιChainComplex w) hConst

end RowDiagonal

private theorem original_cancel_inverse_middle
    {D₀ : Type*} [Category* D₀] {X₀ X₁ X₂ X₃ X₄ X₅ Y₀ : D₀}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (e : Y₀ ≅ X₂)
    (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) (f : X₄ ⟶ X₅) :
    a ≫ b ≫ e.inv ≫ e.hom ≫ c ≫ d ≫ f = a ≫ b ≫ c ≫ d ≫ f := by
  simp only [Iso.inv_hom_id_assoc]

section ForgetCoefficientClass

open CategoryHomology

variable {J A : Type uC} [Category.{uC} J] [CommRing A]


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_forget_homology_projection (S : ShortComplex (ModuleCat.{uC} A)) :
    (S.map (forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).homologyπ ≫ (S.mapHomologyIso (forget₂
      (ModuleCat.{uC} A) AddCommGrpCat.{uC})).hom =
      (S.mapCyclesIso (forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).hom ≫ ((forget₂
        (ModuleCat.{uC} A) AddCommGrpCat.{uC})).map S.homologyπ := by
  let h := S.homologyData.left
  rw [h.mapHomologyIso_eq (forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC}), h.mapCyclesIso_eq
    (forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc, (h.map (forget₂ (ModuleCat.{uC} A)
    AddCommGrpCat.{uC})).homologyπ_comp_homologyIso_hom]
  change ((h.map (forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).cyclesIso.hom ≫ ((forget₂
    (ModuleCat.{uC} A) AddCommGrpCat.{uC})).map h.π) ≫
      ((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).map h.homologyIso.inv =
    ((h.map (forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).cyclesIso.hom ≫ ((forget₂
      (ModuleCat.{uC} A) AddCommGrpCat.{uC})).map h.cyclesIso.inv) ≫ ((forget₂ (ModuleCat.{uC} A)
      AddCommGrpCat.{uC})).map S.homologyπ
  simp only [Category.assoc, ← ((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).map_comp]
  rw [h.π_comp_homologyIso_inv]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_forget_zero_projection (K : ChainComplex (ModuleCat.{uC} A) ℕ) :
    ((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).map (ChainComplex.homologyZeroClass K) ≫
        ((HomologicalComplex.mapHomologyFunctorIso 0 (forget₂ (ModuleCat.{uC} A)
          AddCommGrpCat.{uC})).app K).inv =
      ChainComplex.homologyZeroClass ((((forget₂ (ModuleCat.{uC} A)
        AddCommGrpCat.{uC})).mapHomologicalComplex (ComplexShape.down ℕ)).obj K) := by
  let KU := (((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj K
  let e := (HomologicalComplex.mapHomologyFunctorIso 0 (forget₂ (ModuleCat.{uC} A)
    AddCommGrpCat.{uC})).app K
  let c := (K.sc 0).mapCyclesIso (forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})
  have hp : KU.homologyπ 0 ≫ e.hom = c.hom ≫ ((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).map
    (K.homologyπ 0) :=
    original_forget_homology_projection (K.sc 0)
  have hpi : ((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).map (K.homologyπ 0) ≫ e.inv = c.inv ≫
    KU.homologyπ 0 := by
    apply (cancel_epi c.hom).1
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← hp,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hi : c.inv ≫ KU.iCycles 0 = ((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).map (K.iCycles
    0) := by
    apply (cancel_epi c.hom).1
    rw [Iso.hom_inv_id_assoc]
    exact (ShortComplex.mapCyclesIso_hom_iCycles (S := K.sc 0) (forget₂ (ModuleCat.{uC} A)
      AddCommGrpCat.{uC})).symm
  let l := K.liftCycles (𝟙 (K.X 0)) 0 (by simp) (by simp)
  let lU := KU.liftCycles (𝟙 (KU.X 0)) 0 (by simp) (by simp)
  have hl : ((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).map l ≫ c.inv = lU := by
    apply (cancel_mono (KU.iCycles 0)).1
    rw [Category.assoc, hi, ← ((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).map_comp]
    simp only [l, lU, HomologicalComplex.liftCycles_i, Functor.map_id]
    rfl
  have hq : ChainComplex.homologyZeroClass K = l ≫ K.homologyπ 0 := by
    simpa only [Category.id_comp] using
      comp_homologyZeroProjection_eq_class K (𝟙 (K.X 0))
  have hqU : ChainComplex.homologyZeroClass KU = lU ≫ KU.homologyπ 0 := by
    simpa only [Category.id_comp] using
      comp_homologyZeroProjection_eq_class KU (𝟙 (KU.X 0))
  change ((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).map (ChainComplex.homologyZeroClass K) ≫
    e.inv = ChainComplex.homologyZeroClass KU
  rw [hq, Functor.map_comp, Category.assoc, hpi, ← Category.assoc, hl, hqU]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_forget_bar_component (M : J ⥤ ModuleCat.{uC} A) :
    (coefficientBarComplexForgetIso M).hom.f 0 = (coefficientBarForgetObjIso M 0).hom := by
  unfold coefficientBarComplexForgetIso
  rw [Iso.trans_hom, HomologicalComplex.comp_f,
    Functor.mapIso_hom, AlgebraicTopology.alternatingFaceMapComplex_map_f]
  change (𝟙 _ ≫ (coefficientBarForgetSimplicialIso M).hom.app (op ⦋0⦌)) = _
  rw [Category.id_comp]
  unfold coefficientBarForgetSimplicialIso
  rw [Iso.trans_hom, NatTrans.comp_app, Functor.mapIso_hom,
    SimplicialObject.Data.toSimplicialObject_mapObjIso_hom_app_mk,
    SimplicialObject.Data.toSimplicialFunctor_map_app_mk]
  change 𝟙 (((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).obj (coefficientBarObj M 0)) ≫
    (coefficientBarForgetObjIso M 0).hom = _
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_forget_normalized_factorization (M : J ⥤ ModuleCat.{uC} A) :
    (homologyWithCoefficientsForgetIso M 0).hom =
      ((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).map (coefficientHomologyZeroComparison
        M).hom ≫
        ((HomologicalComplex.mapHomologyFunctorIso 0 (forget₂ (ModuleCat.{uC} A)
          AddCommGrpCat.{uC})).app (coefficientBarComplex M)).inv ≫
          HomologicalComplex.homologyMap (coefficientBarComplexForgetIso M).hom 0 ≫
            (coefficientHomologyZeroComparison (M ⋙ (forget₂ (ModuleCat.{uC} A)
              AddCommGrpCat.{uC}))).inv := by
  let ν := AlgebraicTopology.inclusionOfMooreComplexMap (coefficientBarSimplicial M)
  have h := (HomologicalComplex.mapHomologyFunctorIso 0 (forget₂ (ModuleCat.{uC} A)
    AddCommGrpCat.{uC})).inv.naturality ν
  change ((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).map (coefficientHomologyZeroComparison
    M).hom ≫
      ((HomologicalComplex.mapHomologyFunctorIso 0 (forget₂ (ModuleCat.{uC} A)
        AddCommGrpCat.{uC})).app (coefficientBarComplex M)).inv =
    ((HomologicalComplex.mapHomologyFunctorIso 0 (forget₂ (ModuleCat.{uC} A)
      AddCommGrpCat.{uC})).app (normalizedCoefficientBarComplex M)).inv ≫
      HomologicalComplex.homologyMap
        ((((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).mapHomologicalComplex (ComplexShape.down
          ℕ)).map ν) 0 at h
  change ((HomologicalComplex.mapHomologyFunctorIso 0 (forget₂ (ModuleCat.{uC} A)
    AddCommGrpCat.{uC})).app
      (normalizedCoefficientBarComplex M)).inv ≫
    HomologicalComplex.homologyMap
      (((((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).mapHomologicalComplex (ComplexShape.down
        ℕ)).map ν) ≫
        (coefficientBarComplexForgetIso M).hom ≫
          AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex
            (coefficientBarSimplicial (M ⋙ (forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})))) 0 = _
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  change _ = ((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).map
    (coefficientHomologyZeroComparison M).hom ≫
    ((HomologicalComplex.mapHomologyFunctorIso 0 (forget₂ (ModuleCat.{uC} A)
      AddCommGrpCat.{uC})).app (coefficientBarComplex M)).inv ≫
      HomologicalComplex.homologyMap (coefficientBarComplexForgetIso M).hom 0 ≫
        HomologicalComplex.homologyMap
          (AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex
            (coefficientBarSimplicial (M ⋙ (forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})))) 0
  rw [← Category.assoc, ← Category.assoc, ← h]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_coefficient_class_forget (M : J ⥤ ModuleCat.{uC} A) (i : J) :
    ((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).map (coefficientHomologyClass M i) ≫
      (homologyWithCoefficientsForgetIso M 0).hom =
      coefficientHomologyClass (M ⋙ (forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})) i := by
  let K := coefficientBarComplex M
  let c := coefficientBarComplexForgetIso M
  let KU := (((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj K
  let K' := coefficientBarComplex (M ⋙ (forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC}))
  let ιM : M.obj i ⟶ K.X 0 := coefficientBarι M (ComposableArrows.mk₀ i)
  let ιN : (M ⋙ (forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).obj i ⟶ K'.X 0 := coefficientBarι
    (M ⋙ (forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})) (ComposableArrows.mk₀ i)
  let e := coefficientHomologyZeroComparison M
  let e' := coefficientHomologyZeroComparison (M ⋙ (forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC}))
  let η := (HomologicalComplex.mapHomologyFunctorIso 0 (forget₂ (ModuleCat.{uC} A)
    AddCommGrpCat.{uC})).app K
  let Hc := HomologicalComplex.homologyMap c.hom 0
  have hq : ((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).map (ChainComplex.homologyZeroClass K)
    ≫ η.inv =
      ChainComplex.homologyZeroClass KU :=
    original_forget_zero_projection K
  have hc : ChainComplex.homologyZeroClass KU ≫ Hc =
      c.hom.f 0 ≫ ChainComplex.homologyZeroClass K' :=
    ChainComplex.homologyZeroClass_naturality c.hom
  have hι : ((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).map ιM ≫ c.hom.f 0 = ιN := by
    rw [original_forget_bar_component]
    exact map_coefficientBarι_comp_coefficientBarForgetObjIso_hom M (ComposableArrows.mk₀ i)
  have hf : (homologyWithCoefficientsForgetIso M 0).hom =
      ((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).map e.hom ≫ η.inv ≫ Hc ≫ e'.inv :=
        original_forget_normalized_factorization M
  change ((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).map (ιM ≫ ChainComplex.homologyZeroClass
    K ≫ e.inv) ≫
      (homologyWithCoefficientsForgetIso M 0).hom =
    ιN ≫ ChainComplex.homologyZeroClass K' ≫ e'.inv
  calc
    _ = ((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).map ιM ≫ ((forget₂ (ModuleCat.{uC} A)
      AddCommGrpCat.{uC})).map (ChainComplex.homologyZeroClass K) ≫
        ((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).map e.inv ≫ ((forget₂ (ModuleCat.{uC} A)
          AddCommGrpCat.{uC})).map e.hom ≫ η.inv ≫ Hc ≫ e'.inv := by
      rw [hf]
      simp only [Functor.map_comp, Category.assoc]
    _ = ((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).map ιM ≫ ((forget₂ (ModuleCat.{uC} A)
      AddCommGrpCat.{uC})).map (ChainComplex.homologyZeroClass K) ≫ η.inv ≫ Hc ≫ e'.inv := by
      exact original_cancel_inverse_middle (((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).map
        ιM) (((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).map (ChainComplex.homologyZeroClass
        K))
        (((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).mapIso e) η.inv Hc e'.inv
    _ = ((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).map ιM ≫ ChainComplex.homologyZeroClass KU
      ≫ Hc ≫ e'.inv := by
      simpa only [Category.assoc] using
        congrArg (fun f => ((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).map ιM ≫ f ≫ Hc ≫
          e'.inv) hq
    _ = ((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).map ιM ≫ c.hom.f 0 ≫
      ChainComplex.homologyZeroClass K' ≫ e'.inv := by
      simpa only [Category.assoc] using
        congrArg (fun f => ((forget₂ (ModuleCat.{uC} A) AddCommGrpCat.{uC})).map ιM ≫ f ≫ e'.inv) hc
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ ChainComplex.homologyZeroClass K' ≫ e'.inv) hι

end ForgetCoefficientClass

section OriginalRow

variable (C : Type uC) [Category.{uC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] (R : AddCommGrpCat.{uC})

local notation "proj" => translationProjection (C := C)
local notation "commaD" => SSet.rightCommaNerveDiagram proj
local notation "jcomma" => coreToTranslationFiber (Core.mk (0 : C)) ⋙
  Functor.IsCofibered.fiberToCostructuredArrow (0 : Translation C)
local notation "j" => nerveMap jcomma
local notation "rowIso" => eqToIso
  (Eq.symm (SSet.bkAlternatingBicomplex_X_eq_chainComplex R commaD 0))
local notation "rowIncl" => StrictOrdinaryWeightedBar.wbarIncl
  (CategoryBar.replUnit (Translation C)) commaD 0
  (constantBaseIndex (0 : Translation C) 0)
local notation "jrow" => SSet.chainComplexMap (j ≫ rowIncl) R ≫ Iso.hom rowIso
local notation "sourceMap" => SSet.chainComplexMap (SSet.rightCommaTotalToSource proj) R

private theorem coreCommaProjection :
    (jcomma) ⋙ SSet.rightCommaProjectionFunctor proj (0 : Translation C) =
      negativeCoreInclusion (C := C) := by
  apply Functor.hext
  · intro X
    rfl
  · intro X Y f
    rfl

private theorem coreCommaNerveProjection :
    (j) ≫ nerveMap (SSet.rightCommaProjectionFunctor proj (0 : Translation C)) =
      nerveMap (negativeCoreInclusion (C := C)) := by
  rw [← coreCommaProjection C]
  ext a x
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_row_chain :
    (jrow) ≫ ((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
      (translationProjection (C := C))))).partialTotalZeroRowToTotal ≫
      ((AlgebraicTopology.BisimplicialEilenbergZilber.alternatingMap (SSet.bkLinearizedBisimplicial
      AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))) ≫
      ((SSet.bkDiagonalAlternatingComplexIso AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
        (translationProjection (C := C))))).hom ≫ (sourceMap) =
      SSet.chainComplexMap (nerveMap (negativeCoreInclusion (C := C))) R := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply SSet.chainComplex_hom_ext
  intro x
  let P₀ := StrictOrdinaryWeightedBar.wbarObj (CategoryBar.replUnit (Translation C)) commaD 0
  let incl0 : (commaD).obj (0 : Translation C) ⟶ P₀ := rowIncl
  let y := (j).app (op ⦋n⦌) x
  let pn := constantBaseIndex (0 : Translation C) n
  let yn := (StrictOrdinaryWeightedBar.wbarIncl
    (CategoryBar.replUnit (Translation C)) commaD n pn).app (op ⦋n⦌) y
  have hDiag := row_shuffle_diagonal_generator commaD R (0 : Translation C) n y
  have hAug : (SSet.rightCommaTotalToSource proj).app (op ⦋n⦌) yn =
      (nerveMap (SSet.rightCommaProjectionFunctor proj (0 : Translation C))).app
        (op ⦋n⦌) y :=
    congrArg (fun f => f y) (SSet.rightCommaTotalToSource_app_mk_ι proj n pn)
  have hCore :
      (nerveMap (SSet.rightCommaProjectionFunctor proj (0 : Translation C))).app
          (op ⦋n⦌) y =
        (nerveMap (negativeCoreInclusion (C := C))).app (op ⦋n⦌) x :=
    congrArg (fun f : nerve (Core C) ⟶ nerve (Pair C) => f.app (op ⦋n⦌) x)
      (coreCommaNerveProjection C)
  simp only [HomologicalComplex.comp_f, Category.assoc]
  rw [SSet.ι_chainComplexMap_f_assoc]
  conv_rhs => rw [SSet.ι_chainComplexMap_f]
  have hIncl := SSet.ι_chainComplexMap_f (X := (commaD).obj (0 : Translation C))
    (Y := P₀) (f := incl0) (R := R) y
  change P₀.ιChainComplex (incl0.app (op ⦋n⦌) y) ≫ (rowIso).hom.f n ≫
      ((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
        (translationProjection (C := C))))).partialTotalZeroRowToTotal.f n ≫
        ((AlgebraicTopology.BisimplicialEilenbergZilber.alternatingMap
        (SSet.bkLinearizedBisimplicial AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
        (translationProjection (C := C)))))).f n ≫
      ((SSet.bkDiagonalAlternatingComplexIso AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
        (translationProjection (C := C))))).hom.f n ≫ (sourceMap).f n = _
  rw [← hIncl]
  calc
    _ = (SSet.bkHocolim commaD).ιChainComplex yn ≫ (sourceMap).f n := by
      have h := hDiag =≫ (sourceMap).f n
      rw [Category.assoc, Category.assoc, Category.assoc,
        Category.assoc, Category.assoc] at h
      exact h
    _ = (nerve (Pair C)).ιChainComplex
        ((SSet.rightCommaTotalToSource proj).app (op ⦋n⦌) yn) :=
      SSet.ι_chainComplexMap_f (X := SSet.bkHocolim commaD)
        (Y := nerve (Pair C)) (f := SSet.rightCommaTotalToSource proj) (R := R) yn
    _ = _ := by rw [hAug, hCore]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_abutment_hom (q : ℕ) :
    (translationBKAbutmentHomologyIso C R q).hom =
      HomologicalComplex.homologyMap (((AlgebraicTopology.BisimplicialEilenbergZilber.alternatingMap
        (SSet.bkLinearizedBisimplicial AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
        (translationProjection (C := C)))))) ≫ ((SSet.bkDiagonalAlternatingComplexIso
        AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram (translationProjection (C := C))))).hom ≫
        (sourceMap)) q := by
  unfold translationBKAbutmentHomologyIso SSet.rightCommaBKTotalSourceHomologyIso_addCommGrp
  simp only [Iso.trans_hom, Iso.symm_hom, HomotopyEquiv.toHomologyIso,
    isoOfQuasiIsoAt, asIso_hom,
    SSet.bkDiagonalTotalHomotopyEquiv, HomotopyEquiv.trans,
    HomotopyEquiv.ofIso, AlgebraicTopology.BisimplicialNormalization.homotopyEquiv,
    Iso.symm_inv, HomologicalComplex.homologyMap_comp, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_row_homology (q : ℕ) :
    HomologicalComplex.homologyMap ((jrow) ≫ ((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R
      (SSet.rightCommaNerveDiagram (translationProjection (C := C))))).partialTotalZeroRowToTotal) q
      ≫
        (translationBKAbutmentHomologyIso C R q).hom =
      SSet.homologyMap (nerveMap (negativeCoreInclusion (C := C))) R q := by
  rw [original_abutment_hom, ← HomologicalComplex.homologyMap_comp]
  change HomologicalComplex.homologyMap
      ((jrow) ≫ ((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
        (translationProjection (C := C))))).partialTotalZeroRowToTotal ≫
        ((AlgebraicTopology.BisimplicialEilenbergZilber.alternatingMap
        (SSet.bkLinearizedBisimplicial AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
        (translationProjection (C := C)))))) ≫
        ((SSet.bkDiagonalAlternatingComplexIso AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
          (translationProjection (C := C))))).hom ≫ (sourceMap)) q = _
  rw [original_row_chain]

private theorem original_row_homology_module (q : ℕ) :
    (coreTranslationHomologyModuleAddCommGrpIso C R q).hom ≫
      HomologicalComplex.homologyMap ((jrow) ≫ ((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R
        (SSet.rightCommaNerveDiagram (translationProjection (C := C))))).partialTotalZeroRowToTotal)
        q ≫
        (translationBKAbutmentHomologyIso C R q).hom =
      (coreTranslationHomologyModuleAddCommGrpIso C R q).hom ≫
        SSet.homologyMap (nerveMap (negativeCoreInclusion (C := C))) R q := by
  exact congrArg (fun f => (coreTranslationHomologyModuleAddCommGrpIso C R q).hom ≫ f)
    (original_row_homology C R q)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_row_stage_homology (q : ℕ) :
    HomologicalComplex.homologyMap
        ((jrow) ≫ HomologicalComplex₂.zero_complete_inclusion ((SSet.bkAlternatingBicomplex
          AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))) q ≫
      HomologicalComplex.homologyMap
        (HomologicalComplex₂.horizontalCompleteFilteredTotalToTotal ((SSet.bkAlternatingBicomplex
          AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))
          ((0 : ℤ) : EInt)) q ≫
      (translationBKAbutmentHomologyIso C R q).hom =
        SSet.homologyMap (nerveMap (negativeCoreInclusion (C := C))) R q := by
  calc
    _ = HomologicalComplex.homologyMap
        ((jrow) ≫ (HomologicalComplex₂.zero_complete_inclusion ((SSet.bkAlternatingBicomplex
          AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram (translationProjection (C := C))))) ≫
          HomologicalComplex₂.horizontalCompleteFilteredTotalToTotal ((SSet.bkAlternatingBicomplex
            AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))
            ((0 : ℤ) : EInt))) q ≫
        (translationBKAbutmentHomologyIso C R q).hom := by
      simp only [HomologicalComplex.homologyMap_comp, Category.assoc]
    _ = HomologicalComplex.homologyMap
        ((jrow) ≫ ((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
          (translationProjection (C := C))))).partialTotalZeroRowToTotal) q ≫
        (translationBKAbutmentHomologyIso C R q).hom := by
      rw [HomologicalComplex₂.zero_complete_inclusion_to_total]
    _ = _ := original_row_homology C R q

private theorem original_row_stage_homology_module (q : ℕ) :
    (coreTranslationHomologyModuleAddCommGrpIso C R q).hom ≫
      HomologicalComplex.homologyMap
        ((jrow) ≫ HomologicalComplex₂.zero_complete_inclusion ((SSet.bkAlternatingBicomplex
          AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))) q ≫
      HomologicalComplex.homologyMap
        (HomologicalComplex₂.horizontalCompleteFilteredTotalToTotal ((SSet.bkAlternatingBicomplex
          AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))
          ((0 : ℤ) : EInt)) q ≫
      (translationBKAbutmentHomologyIso C R q).hom =
    (coreTranslationHomologyModuleAddCommGrpIso C R q).hom ≫
      SSet.homologyMap (nerveMap (negativeCoreInclusion (C := C))) R q := by
  exact congrArg (fun f => (coreTranslationHomologyModuleAddCommGrpIso C R q).hom ≫ f)
    (original_row_stage_homology C R q)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def original_core_stage_raw (q : ℕ) :
    (forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC}).obj
        (coreTranslationHomologyModuleCat C R q) ⟶
      (forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC}).obj
        ((secondTranslationBKModuleSpectralObject (C := C) R).stableIntervalStep
          (-(q : ℤ)) ((0 : ℤ) : EInt)) :=
  (coreTranslationHomologyModuleAddCommGrpIso C R q).hom ≫
    HomologicalComplex.homologyMap (jrow) q ≫
    HomologicalComplex.homologyMap (HomologicalComplex₂.zero_complete_inclusion
      ((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
      (translationProjection (C := C)))))) q ≫
    (HomologicalComplex₂.horizontalBottomRelativeHomologyStageIso ((SSet.bkAlternatingBicomplex
      AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))
      ((0 : ℤ) : EInt) q).inv ≫
    (CategoryTheory.Abelian.SpectralObject.monoidModuleIntervalForgetIso
      (HomologicalComplex₂.horizontalCompleteFiltrationSpectralObject ((SSet.bkAlternatingBicomplex
        AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram (translationProjection (C := C))))))
      (secondTranslationBKSpectralAction (C := C) R) (-(q : ℤ))
      (CategoryTheory.ComposableArrows.mk₁
        (HomologicalComplex₂.horizontalBottomToStageMap ((0 : ℤ) : EInt)))).inv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem second_translation_fiber_comma (W : C) (B : Translation C) :
    secondTranslationFiberFunctor W B ⋙
        Functor.IsCofibered.fiberToCostructuredArrow B =
      Functor.IsCofibered.fiberToCostructuredArrow B ⋙
        secondTranslationCostructuredMap W B := by
  let i := Functor.IsCofibered.fiberToCostructuredArrow
    (p := translationProjection (C := C)) B
  have hobj (X : (translationProjection (C := C)).Fiber B) :
      (secondTranslationFiberFunctor W B ⋙ i).obj X =
        (i ⋙ secondTranslationCostructuredMap W B).obj X := by
    have hleft : ((secondTranslationFiberFunctor W B ⋙ i).obj X).left =
        ((i ⋙ secondTranslationCostructuredMap W B).obj X).left := by rfl
    apply CostructuredArrow.obj_ext _ _ hleft
    simp [i, Functor.comp_obj, secondTranslationFiberFunctor,
      Functor.IsCofibered.fiberToCostructuredArrow,
      secondTranslationCostructuredMap_obj_hom]
  have hom_heq : ∀ {X Y X' Y' :
        CostructuredArrow (translationProjection (C := C)) B},
      X = X' → Y = Y' → ∀ (f : X ⟶ Y) (g : X' ⟶ Y'),
        HEq f.left g.left → HEq f g := by
    intro X Y X' Y' hX hY f g hfg
    cases hX
    cases hY
    exact heq_of_eq (CostructuredArrow.hom_ext f g (eq_of_heq hfg))
  refine Functor.hext hobj ?_
  intro X Y f
  apply hom_heq (hobj X) (hobj Y)
  apply heq_of_eq
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem core_second_translation_comma (W : C) :
    coreLeftTranslationFunctor W ⋙ (jcomma) =
      (jcomma) ⋙ secondTranslationCostructuredMap W (0 : Translation C) := by
  have h := coreSecondTranslationFiberFunctor_eq (Core.mk W) (Core.mk (0 : C))
  calc
    _ = (coreLeftTranslationFunctor W ⋙ coreToTranslationFiber (Core.mk (0 : C))) ⋙
        Functor.IsCofibered.fiberToCostructuredArrow (0 : Translation C) := by rfl
    _ = (coreToTranslationFiber (Core.mk (0 : C)) ⋙
          secondTranslationFiberFunctor W (0 : Translation C)) ⋙
        Functor.IsCofibered.fiberToCostructuredArrow (0 : Translation C) := by
      rw [← h]
      rfl
    _ = coreToTranslationFiber (Core.mk (0 : C)) ⋙
        (secondTranslationFiberFunctor W (0 : Translation C) ⋙
          Functor.IsCofibered.fiberToCostructuredArrow (0 : Translation C)) := by rfl
    _ = coreToTranslationFiber (Core.mk (0 : C)) ⋙
        (Functor.IsCofibered.fiberToCostructuredArrow (0 : Translation C) ⋙
          secondTranslationCostructuredMap W (0 : Translation C)) := by
      rw [second_translation_fiber_comma]
    _ = _ := by rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_row_bicomplex_map (W : C) :
    SSet.chainComplexMap
        (StrictOrdinaryWeightedBar.wbarMapF 0
          (secondTranslationRightCommaNerveDiagramNatTrans W)) R ≫
      (rowIso).hom =
    (rowIso).hom ≫ (secondTranslationBKBicomplexMap R W).f 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, rowIso_hom_f, Category.comp_id, Category.id_comp]
  change (SSet.chainComplexMap
      (StrictOrdinaryWeightedBar.wbarMapF 0
        (secondTranslationRightCommaNerveDiagramNatTrans W)) R).f n =
    (SSet.chainComplexMap
      ((StrictOrdinaryWeightedBar.wbarSimplicialMapF
        (CategoryBar.replUnit (Translation C))
        (secondTranslationRightCommaNerveDiagramNatTrans W)).app (op ⦋0⦌)) R).f n
  rw [StrictOrdinaryWeightedBar.wbarSimplicialMapF_app_mk]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_row_second_translation (W : C) :
    SSet.chainComplexMap (nerveMap (coreLeftTranslationFunctor W)) R ≫ (jrow) =
      (jrow) ≫ (secondTranslationBKBicomplexMap R W).f 0 := by
  let τ := secondTranslationRightCommaNerveDiagramNatTrans W
  let wmap : StrictOrdinaryWeightedBar.wbarObj
      (CategoryBar.replUnit (Translation C)) (commaD) 0 ⟶
      StrictOrdinaryWeightedBar.wbarObj
        (CategoryBar.replUnit (Translation C)) (commaD) 0 :=
    StrictOrdinaryWeightedBar.wbarMapF 0 τ
  have hnerve : nerveMap (coreLeftTranslationFunctor W) ≫ (j) =
      (j) ≫ τ.app (0 : Translation C) := by
    dsimp only [τ]
    rw [secondTranslationRightCommaNerveDiagramNatTrans_app,
      nerveMap_comp, nerveMap_comp, core_second_translation_comma]
  have hbar : (rowIncl) ≫ wmap = τ.app (0 : Translation C) ≫ (rowIncl) :=
    StrictOrdinaryWeightedBar.wbarMapF_ι 0 τ
      (constantBaseIndex (0 : Translation C) 0)
  have hsimp : nerveMap (coreLeftTranslationFunctor W) ≫ ((j) ≫ (rowIncl)) =
      ((j) ≫ (rowIncl)) ≫ wmap := by
    calc
      _ = (j) ≫ (τ.app (0 : Translation C) ≫ (rowIncl)) := by
        rw [← Category.assoc, hnerve, Category.assoc]
      _ = (j) ≫ ((rowIncl) ≫ wmap) := by rw [← hbar]
      _ = _ := by rw [Category.assoc]
  let hColimits : HasColimitsOfSize.{uC, uC} AddCommGrpCat.{uC} := inferInstance
  let : HasCoproducts.{uC} AddCommGrpCat.{uC} :=
    fun J => hColimits.has_colimits_of_shape (Discrete J)
  let F : SSet.{uC} ⥤ ChainComplex AddCommGrpCat.{uC} ℕ :=
    (SSet.chainComplexFunctor.{uC} AddCommGrpCat.{uC}).obj R
  have hchain : SSet.chainComplexMap (nerveMap (coreLeftTranslationFunctor W)) R ≫
        SSet.chainComplexMap ((j) ≫ (rowIncl)) R =
      SSet.chainComplexMap ((j) ≫ (rowIncl)) R ≫ SSet.chainComplexMap wmap R := by
    change F.map (nerveMap (coreLeftTranslationFunctor W)) ≫ F.map ((j) ≫ (rowIncl)) =
      F.map ((j) ≫ (rowIncl)) ≫ F.map wmap
    rw [← F.map_comp, ← F.map_comp, hsimp]
  change SSet.chainComplexMap (nerveMap (coreLeftTranslationFunctor W)) R ≫
      (SSet.chainComplexMap ((j) ≫ (rowIncl)) R ≫ (rowIso).hom) =
    (SSet.chainComplexMap ((j) ≫ (rowIncl)) R ≫ (rowIso).hom) ≫
      (secondTranslationBKBicomplexMap R W).f 0
  calc
    _ = (SSet.chainComplexMap (nerveMap (coreLeftTranslationFunctor W)) R ≫
        SSet.chainComplexMap ((j) ≫ (rowIncl)) R) ≫ (rowIso).hom := by
      rw [Category.assoc]
    _ = (SSet.chainComplexMap ((j) ≫ (rowIncl)) R ≫ SSet.chainComplexMap wmap R) ≫
        (rowIso).hom := by rw [hchain]
    _ = SSet.chainComplexMap ((j) ≫ (rowIncl)) R ≫
        ((rowIso).hom ≫ (secondTranslationBKBicomplexMap R W).f 0) := by
      rw [Category.assoc, original_row_bicomplex_map]
    _ = _ := by rw [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_core_stage_homology_naturality (W : C) (q : ℕ) :
    SSet.homologyMap (nerveMap (coreLeftTranslationFunctor W)) R q ≫
      HomologicalComplex.homologyMap (jrow) q ≫
      HomologicalComplex.homologyMap (HomologicalComplex₂.zero_complete_inclusion
        ((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
        (translationProjection (C := C)))))) q =
    HomologicalComplex.homologyMap (jrow) q ≫
      HomologicalComplex.homologyMap (HomologicalComplex₂.zero_complete_inclusion
        ((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
        (translationProjection (C := C)))))) q ≫
      HomologicalComplex.homologyMap
        (HomologicalComplex₂.horizontalCompleteFilteredTotalComplexMapOfBicomplex
          (secondTranslationBKBicomplexMap R W) ((0 : ℤ) : EInt)) q := by
  have hrow : HomologicalComplex.homologyMap
        (SSet.chainComplexMap (nerveMap (coreLeftTranslationFunctor W)) R) q ≫
      HomologicalComplex.homologyMap (jrow) q =
    HomologicalComplex.homologyMap (jrow) q ≫
      HomologicalComplex.homologyMap ((secondTranslationBKBicomplexMap R W).f 0) q := by
    simpa only [← HomologicalComplex.homologyMap_comp] using
      congrArg (fun f => HomologicalComplex.homologyMap f q)
        (original_row_second_translation C R W)
  have hstage :
      HomologicalComplex.homologyMap ((secondTranslationBKBicomplexMap R W).f 0) q ≫
        HomologicalComplex.homologyMap (HomologicalComplex₂.zero_complete_inclusion
          ((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
          (translationProjection (C := C)))))) q =
      HomologicalComplex.homologyMap (HomologicalComplex₂.zero_complete_inclusion
        ((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
        (translationProjection (C := C)))))) q ≫
        HomologicalComplex.homologyMap
          (HomologicalComplex₂.horizontalCompleteFilteredTotalComplexMapOfBicomplex
            (secondTranslationBKBicomplexMap R W) ((0 : ℤ) : EInt)) q := by
    simpa only [← HomologicalComplex.homologyMap_comp] using
      congrArg (fun f => HomologicalComplex.homologyMap f q)
        (HomologicalComplex₂.zero_complete_inclusion_naturality
          (secondTranslationBKBicomplexMap R W))
  change HomologicalComplex.homologyMap
      (SSet.chainComplexMap (nerveMap (coreLeftTranslationFunctor W)) R) q ≫
      HomologicalComplex.homologyMap (jrow) q ≫
      HomologicalComplex.homologyMap (HomologicalComplex₂.zero_complete_inclusion
        ((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
        (translationProjection (C := C)))))) q = _
  calc
    _ = (HomologicalComplex.homologyMap
          (SSet.chainComplexMap (nerveMap (coreLeftTranslationFunctor W)) R) q ≫
        HomologicalComplex.homologyMap (jrow) q) ≫
        HomologicalComplex.homologyMap (HomologicalComplex₂.zero_complete_inclusion
          ((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
          (translationProjection (C := C)))))) q := by
      simp only [Category.assoc]
    _ = (HomologicalComplex.homologyMap (jrow) q ≫
        HomologicalComplex.homologyMap ((secondTranslationBKBicomplexMap R W).f 0) q) ≫
        HomologicalComplex.homologyMap (HomologicalComplex₂.zero_complete_inclusion
          ((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
          (translationProjection (C := C)))))) q := by
      rw [hrow]
    _ = _ := by
      rw [Category.assoc, hstage]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_stage_bottom_inv_naturality (W : C) (q : ℕ) :
    HomologicalComplex.homologyMap
        (HomologicalComplex₂.horizontalCompleteFilteredTotalComplexMapOfBicomplex
          (secondTranslationBKBicomplexMap R W) ((0 : ℤ) : EInt)) q ≫
      (HomologicalComplex₂.horizontalBottomRelativeHomologyStageIso ((SSet.bkAlternatingBicomplex
        AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))
        ((0 : ℤ) : EInt) q).inv =
    (HomologicalComplex₂.horizontalBottomRelativeHomologyStageIso ((SSet.bkAlternatingBicomplex
      AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))
      ((0 : ℤ) : EInt) q).inv ≫
      ((HomologicalComplex₂.horizontalCompleteFiltrationSpectralObjectMap
        (secondTranslationBKBicomplexMap R W)).hom (-(q : ℤ))).app
        (CategoryTheory.ComposableArrows.mk₁
          (HomologicalComplex₂.horizontalBottomToStageMap ((0 : ℤ) : EInt))) := by
  let b := HomologicalComplex₂.horizontalBottomRelativeHomologyStageIso
    ((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
    (translationProjection (C := C)))))
    ((0 : ℤ) : EInt) q
  let f := HomologicalComplex.homologyMap
    (HomologicalComplex₂.horizontalCompleteFilteredTotalComplexMapOfBicomplex
      (secondTranslationBKBicomplexMap R W) ((0 : ℤ) : EInt)) q
  let α := ((HomologicalComplex₂.horizontalCompleteFiltrationSpectralObjectMap
    (secondTranslationBKBicomplexMap R W)).hom (-(q : ℤ))).app
      (CategoryTheory.ComposableArrows.mk₁
        (HomologicalComplex₂.horizontalBottomToStageMap ((0 : ℤ) : EInt)))
  have h : α ≫ b.hom = b.hom ≫ f :=
    HomologicalComplex₂.horizontalBottomRelativeHomologyStageIso_naturality_of_bicomplex
      (secondTranslationBKBicomplexMap R W) ((0 : ℤ) : EInt) q
  change f ≫ b.inv = b.inv ≫ α
  calc
    _ = b.inv ≫ (b.hom ≫ f) ≫ b.inv := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = b.inv ≫ (α ≫ b.hom) ≫ b.inv := by rw [← h]
    _ = b.inv ≫ α ≫ (b.hom ≫ b.inv) := by simp only [Category.assoc]
    _ = _ := by rw [b.hom_inv_id, Category.comp_id]

local notation "stageY" => secondTranslationBKModuleSpectralObject (C := C) R
local notation "stageI" => CategoryTheory.ComposableArrows.mk₁
  (HomologicalComplex₂.horizontalBottomToStageMap ((0 : ℤ) : EInt))

private def original_core_stage_interval_raw (q : ℕ) :
    ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).obj
      (coreTranslationHomologyModuleCat C R q) ⟶
      ((HomologicalComplex₂.horizontalCompleteFiltrationSpectralObject ((SSet.bkAlternatingBicomplex
        AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram (translationProjection (C :=
        C))))))).stableIntervalStep (-(q : ℤ)) ((0 : ℤ) : EInt) :=
  (coreTranslationHomologyModuleAddCommGrpIso C R q).hom ≫
    HomologicalComplex.homologyMap (jrow) q ≫
    HomologicalComplex.homologyMap (HomologicalComplex₂.zero_complete_inclusion
      ((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
      (translationProjection (C := C)))))) q ≫
    (HomologicalComplex₂.horizontalBottomRelativeHomologyStageIso ((SSet.bkAlternatingBicomplex
      AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))
      ((0 : ℤ) : EInt) q).inv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_core_stage_interval_naturality (W : C) (q : ℕ) :
    ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map
      (coreTranslationCoefficientMap C R q (toSkeleton W)) ≫
      original_core_stage_interval_raw C R q =
    original_core_stage_interval_raw C R q ≫
      ((HomologicalComplex₂.horizontalCompleteFiltrationSpectralObjectMap
        (secondTranslationBKBicomplexMap R W)).hom (-(q : ℤ))).app (stageI) := by
  let ε := coreTranslationHomologyModuleAddCommGrpIso C R q
  let jh := HomologicalComplex.homologyMap (jrow) q
  let sh := HomologicalComplex.homologyMap
    (HomologicalComplex₂.zero_complete_inclusion ((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R
      (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))) q
  let b := HomologicalComplex₂.horizontalBottomRelativeHomologyStageIso
    ((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
    (translationProjection (C := C)))))
    ((0 : ℤ) : EInt) q
  let c := SSet.homologyMap (nerveMap (coreLeftTranslationFunctor W)) R q
  let f := HomologicalComplex.homologyMap
    (HomologicalComplex₂.horizontalCompleteFilteredTotalComplexMapOfBicomplex
      (secondTranslationBKBicomplexMap R W) ((0 : ℤ) : EInt)) q
  let α := ((HomologicalComplex₂.horizontalCompleteFiltrationSpectralObjectMap
    (secondTranslationBKBicomplexMap R W)).hom (-(q : ℤ))).app (stageI)
  let μ := ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map
    (coreTranslationCoefficientMap C R q (toSkeleton W))
  have hsource : μ ≫ ε.hom = ε.hom ≫ c := by
    have h := coreTranslationCoefficientMap_comp_moduleIso_hom C R q (toSkeleton W)
    rw [coreTranslationHomologyMap_toSkeleton] at h
    exact h
  have hnat : c ≫ jh ≫ sh = jh ≫ sh ≫ f :=
    original_core_stage_homology_naturality C R W q
  have hb : f ≫ b.inv = b.inv ≫ α := original_stage_bottom_inv_naturality C R W q
  change μ ≫ (ε.hom ≫ jh ≫ sh ≫ b.inv) = (ε.hom ≫ jh ≫ sh ≫ b.inv) ≫ α
  calc
    _ = (μ ≫ ε.hom) ≫ jh ≫ sh ≫ b.inv := by simp only [Category.assoc]
    _ = (ε.hom ≫ c) ≫ jh ≫ sh ≫ b.inv := by rw [hsource]
    _ = ε.hom ≫ (c ≫ jh ≫ sh) ≫ b.inv := by simp only [Category.assoc]
    _ = ε.hom ≫ (jh ≫ sh ≫ f) ≫ b.inv := by rw [hnat]
    _ = ε.hom ≫ jh ≫ sh ≫ (f ≫ b.inv) := by simp only [Category.assoc]
    _ = ε.hom ≫ jh ≫ sh ≫ (b.inv ≫ α) := by rw [hb]
    _ = _ := by simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_core_stage_raw_comp_forget (q : ℕ) :
    original_core_stage_raw C R q ≫
      (((HomologicalComplex₂.horizontalCompleteFiltrationSpectralObject
        ((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
        (translationProjection (C := C))))))).monoidModuleIntervalForgetIso
        (secondTranslationBKSpectralAction (C := C) R)
        (-(q : ℤ)) (stageI)).hom =
      original_core_stage_interval_raw C R q := by
  simp only [original_core_stage_raw, original_core_stage_interval_raw, Category.assoc]
  rw [Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_core_stage_target_generator (W : C) (q : ℕ)
    (y : (stageY).stableIntervalStep (-(q : ℤ)) ((0 : ℤ) : EInt)) :
    (((HomologicalComplex₂.horizontalCompleteFiltrationSpectralObject ((SSet.bkAlternatingBicomplex
      AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram (translationProjection (C :=
      C))))))).monoidModuleIntervalForgetIso (secondTranslationBKSpectralAction (C := C) R)
      (-(q : ℤ)) (stageI)).hom
        (MonoidAlgebra.single (Multiplicative.ofAdd (toSkeleton W)) (1 : ℤ) • y) =
      ((HomologicalComplex₂.horizontalCompleteFiltrationSpectralObjectMap
        (secondTranslationBKBicomplexMap R W)).hom (-(q : ℤ))).app (stageI)
        ((((HomologicalComplex₂.horizontalCompleteFiltrationSpectralObject
          ((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
          (translationProjection (C := C))))))).monoidModuleIntervalForgetIso
          (secondTranslationBKSpectralAction (C := C) R)
          (-(q : ℤ)) (stageI)).hom y) := by
  let E := ((HomologicalComplex₂.horizontalCompleteFiltrationSpectralObject
    ((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
    (translationProjection (C := C)))))))
  let ρ := secondTranslationBKSpectralAction (C := C) R
  let n : ℤ := -(q : ℤ)
  let I : ComposableArrows EInt 1 := (stageI)
  let m := Multiplicative.ofAdd (toSkeleton W)
  let P := E.intervalRepresentation ρ n I
  let Φ := E.monoidModuleIntervalForgetIso ρ n I
  let γ : (E.H n).obj I ⟶ (E.H n).obj I :=
    ((HomologicalComplex₂.horizontalCompleteFiltrationSpectralObjectMap
      (secondTranslationBKBicomplexMap R W)).hom n).app I
  have hmap : ((ρ m).asHom.hom n).app I = γ :=
    congrArg (fun e : End E => (e.asHom.hom n).app I)
      (secondTranslationBKSpectralAction_toSkeleton_map (C := C) R W)
  let x : P.asModule := (show E.monoidModuleInterval ρ n I from y)
  have hΦ (z : P.asModule) : Φ.hom z = P.asModuleEquiv z :=
    E.monoidModuleIntervalForgetIso_hom_apply ρ n I z
  have hP (z : (E.H n).obj I) :
      P m z = ((ρ m).asHom.hom n).app I z :=
    Action.intRepresentation_apply (Multiplicative (Skeleton C))
      (E.intervalAction ρ n I) m z
  have hgen := Representation.asModuleEquiv_map_smul P
    (MonoidAlgebra.single m (1 : ℤ)) x
  rw [Representation.asAlgebraHom_single_one] at hgen
  have hgen' := hgen.trans (hP (P.asModuleEquiv x))
  rw [hmap] at hgen'
  change Φ.hom (MonoidAlgebra.single m (1 : ℤ) • x) = γ (Φ.hom x)
  calc
    _ = P.asModuleEquiv (MonoidAlgebra.single m (1 : ℤ) • x) := hΦ _
    _ = γ (P.asModuleEquiv x) := hgen'
    _ = γ (Φ.hom x) := congrArg (fun z => γ z) (hΦ x).symm

private abbrev original_stage_underlying_module (q : ℕ) :
    Module (coreTranslationRing C)
      (((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).obj
        ((stageY).stableIntervalStep (-(q : ℤ)) ((0 : ℤ) : EInt))) := by
  change Module (coreTranslationRing C)
    ((stageY).stableIntervalStep (-(q : ℤ)) ((0 : ℤ) : EInt))
  infer_instance

attribute [local instance] original_stage_underlying_module

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_core_stage_monomial (W : C) (q : ℕ)
    (x : coreTranslationHomologyModuleCat C R q) :
    (original_core_stage_raw C R q).hom
        (MonoidAlgebra.single (Multiplicative.ofAdd (toSkeleton W)) (1 : ℤ) • x) =
      MonoidAlgebra.single (Multiplicative.ofAdd (toSkeleton W)) (1 : ℤ) •
        (original_core_stage_raw C R q).hom x := by
  let e := ((HomologicalComplex₂.horizontalCompleteFiltrationSpectralObject
    ((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
    (translationProjection (C := C))))))).monoidModuleIntervalForgetIso
    (secondTranslationBKSpectralAction (C := C) R)
    (-(q : ℤ)) (stageI)
  let f := original_core_stage_interval_raw C R q
  let g := (original_core_stage_raw C R q).hom
  let m := Multiplicative.ofAdd (toSkeleton W)
  let α := ((HomologicalComplex₂.horizontalCompleteFiltrationSpectralObjectMap
    (secondTranslationBKBicomplexMap R W)).hom (-(q : ℤ))).app (stageI)
  have hg (z : coreTranslationHomologyModuleCat C R q) : e.hom (g z) = f.hom z := by
    exact congrArg (fun k : ((forget₂ (ModuleCat.{uC} (coreTranslationRing C))
      AddCommGrpCat.{uC})).obj (coreTranslationHomologyModuleCat C R q) ⟶
      ((HomologicalComplex₂.horizontalCompleteFiltrationSpectralObject ((SSet.bkAlternatingBicomplex
        AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram (translationProjection (C :=
        C))))))).stableIntervalStep (-(q : ℤ)) ((0 : ℤ) : EInt) => k.hom z)
      (original_core_stage_raw_comp_forget C R q)
  have hμ : (((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map
    (coreTranslationCoefficientMap C R q (toSkeleton W))).hom x =
      MonoidAlgebra.single m (1 : ℤ) • x := by
    change MonoidAlgebra.of ℤ (Multiplicative (Skeleton C)) m • x = _
    rw [MonoidAlgebra.of_apply]
  have hnat : f.hom (MonoidAlgebra.single m (1 : ℤ) • x) = α (f.hom x) := by
    have h := congrArg (fun k : ((forget₂ (ModuleCat.{uC} (coreTranslationRing C))
      AddCommGrpCat.{uC})).obj (coreTranslationHomologyModuleCat C R q) ⟶
      ((HomologicalComplex₂.horizontalCompleteFiltrationSpectralObject ((SSet.bkAlternatingBicomplex
        AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram (translationProjection (C :=
        C))))))).stableIntervalStep (-(q : ℤ)) ((0 : ℤ) : EInt) => k.hom x)
      (original_core_stage_interval_naturality C R W q)
    change f.hom ((((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map
        (coreTranslationCoefficientMap C R q (toSkeleton W))).hom x) = α (f.hom x) at h
    rw [hμ] at h
    exact h
  suffices h : e.hom (g (MonoidAlgebra.single m (1 : ℤ) • x)) =
      e.hom (MonoidAlgebra.single m (1 : ℤ) • g x) by
    have hi := congrArg (fun y => e.inv y) h
    simpa only [Iso.hom_inv_id_apply] using hi
  calc
    _ = f.hom (MonoidAlgebra.single m (1 : ℤ) • x) := hg _
    _ = α (f.hom x) := hnat
    _ = α (e.hom (g x)) := by rw [hg]
    _ = _ := (original_core_stage_target_generator C R W q (g x)).symm

private theorem original_core_stage_single_one (q : ℕ)
    (m : Multiplicative (Skeleton C)) (x : coreTranslationHomologyModuleCat C R q) :
    (original_core_stage_raw C R q).hom (MonoidAlgebra.single m (1 : ℤ) • x) =
      MonoidAlgebra.single m (1 : ℤ) • (original_core_stage_raw C R q).hom x := by
  let W := (fromSkeleton C).obj m.toAdd
  have hm : Multiplicative.ofAdd (toSkeleton W) = m := by
    rw [show toSkeleton W = m.toAdd from toSkeleton_fromSkeleton_obj m.toAdd]
    rfl
  simpa only [hm] using original_core_stage_monomial C R W q x

private theorem original_core_stage_single_integer (q : ℕ)
    (m : Multiplicative (Skeleton C)) (z : ℤ) (x : coreTranslationHomologyModuleCat C R q) :
    (original_core_stage_raw C R q).hom (MonoidAlgebra.single m z • x) =
      MonoidAlgebra.single m z • (original_core_stage_raw C R q).hom x := by
  let g := (original_core_stage_raw C R q).hom
  have hc : MonoidAlgebra.single m z =
      z • (MonoidAlgebra.single m (1 : ℤ) : coreTranslationRing C) := by
    rw [MonoidAlgebra.smul_single]
    simp
  calc
    _ = g (z • (MonoidAlgebra.single m (1 : ℤ) • x)) := by rw [hc, smul_assoc]
    _ = z • g (MonoidAlgebra.single m (1 : ℤ) • x) := g.map_zsmul _ _
    _ = z • (MonoidAlgebra.single m (1 : ℤ) • g x) := by
      rw [original_core_stage_single_one]
    _ = (z • (MonoidAlgebra.single m (1 : ℤ) : coreTranslationRing C)) • g x := by
      rw [smul_assoc]
    _ = _ := by rw [← hc]

private theorem original_core_stage_smul (q : ℕ) (a : coreTranslationRing C)
    (x : coreTranslationHomologyModuleCat C R q) :
    (original_core_stage_raw C R q).hom (a • x) =
      a • (original_core_stage_raw C R q).hom x := by
  classical
  conv_lhs => rw [← MonoidAlgebra.sum_coeff_single a]
  conv_rhs => rw [← MonoidAlgebra.sum_coeff_single a]
  simp only [Finsupp.sum, Finset.sum_smul, map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  exact original_core_stage_single_integer C R q m (a.coeff m) x

private def original_core_stage_linear (q : ℕ) :
    coreTranslationHomologyModuleCat C R q ⟶
      (stageY).stableIntervalStep (-(q : ℤ)) ((0 : ℤ) : EInt) :=
  ModuleCat.ofHom
    { toFun := (original_core_stage_raw C R q).hom
      map_add' := (original_core_stage_raw C R q).hom.map_add
      map_smul' := original_core_stage_smul C R q }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_core_stage_linear_forget (q : ℕ) :
    ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map
      (original_core_stage_linear C R q) ≫
      (((HomologicalComplex₂.horizontalCompleteFiltrationSpectralObject
        ((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
        (translationProjection (C := C))))))).monoidModuleIntervalForgetIso
        (secondTranslationBKSpectralAction (C := C) R)
        (-(q : ℤ)) (stageI)).hom =
    (coreTranslationHomologyModuleAddCommGrpIso C R q).hom ≫
      HomologicalComplex.homologyMap (jrow) q ≫
      HomologicalComplex.homologyMap (HomologicalComplex₂.zero_complete_inclusion
        ((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
        (translationProjection (C := C)))))) q ≫
      (HomologicalComplex₂.horizontalBottomRelativeHomologyStageIso ((SSet.bkAlternatingBicomplex
        AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))
        ((0 : ℤ) : EInt) q).inv := by
  change original_core_stage_raw C R q ≫
    (((HomologicalComplex₂.horizontalCompleteFiltrationSpectralObject ((SSet.bkAlternatingBicomplex
      AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram (translationProjection (C :=
      C))))))).monoidModuleIntervalForgetIso (secondTranslationBKSpectralAction (C := C) R)
      (-(q : ℤ)) (stageI)).hom = _
  exact original_core_stage_raw_comp_forget C R q

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_vertical_coefficient_component (q : ℕ) :
    (Functor.IsCofibered.cofiberedVerticalHomologyComplexIso (p := proj) R q).hom.f 0 =
      (SSet.bkAlternatingVerticalHomologyIso R commaD 0 q).hom ≫
        (CategoryHomology.terminalWeightCoefficientBarDegreeIso
          ((commaD) ⋙ SSet.homologyFunctor R q) 0).hom ≫
          CategoryHomology.coefficientBarMap
            (Functor.IsCofibered.costructuredFiberHomologyNatIso
              (p := proj) AddCommGrpCat.{uC} R q).hom 0 := by
  let ω := Functor.IsCofibered.costructuredFiberHomologyNatIso
    (p := proj) AddCommGrpCat.{uC} R q
  have hm : ((AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{uC}).map
      (CategoryHomology.coefficientBarSimplicialMap ω.hom)).f 0 =
        CategoryHomology.coefficientBarMap ω.hom 0 := by
    rw [AlgebraicTopology.alternatingFaceMapComplex_map_f]
    exact SimplicialObject.Data.toSimplicialNatTrans_app_mk
      (CategoryHomology.coefficientBarDataMap ω.hom) 0
  unfold Functor.IsCofibered.cofiberedVerticalHomologyComplexIso
    SSet.bkVerticalHomologyCoefficientBarComplexIso
    Functor.IsCofibered.commaFiberCoefficientBarComplexIso
  simp only [Iso.trans_hom, HomologicalComplex.comp_f, Functor.mapIso_hom]
  change ((SSet.bkAlternatingVerticalHomologyIso R commaD 0 q).hom ≫
      (CategoryHomology.terminalWeightCoefficientBarDegreeIso
        ((commaD) ⋙ SSet.homologyFunctor R q) 0).hom) ≫
        ((AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{uC}).map
          (CategoryHomology.coefficientBarSimplicialMap ω.hom)).f 0 = _
  rw [hm]
  exact Category.assoc _ _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_weighted_fiber_summand (q : ℕ) :
    (Functor.IsCofibered.costructuredFiberHomologyIso
        (p := proj) AddCommGrpCat.{uC} (0 : Translation C) R q).inv ≫
      HomologicalComplex.homologyMap
        (SSet.chainComplexMap (rowIncl) R ≫ (rowIso).hom) q ≫
        (Functor.IsCofibered.cofiberedVerticalHomologyComplexIso (p := proj) R q).hom.f 0 =
      CategoryHomology.coefficientBarι
        (Functor.IsCofibered.fiberHomologyFunctor (p := proj) AddCommGrpCat.{uC} R q)
        (ComposableArrows.mk₀ (0 : Translation C)) := by
  let Cq := Functor.IsCofibered.costructuredHomologyFunctor (p := proj) AddCommGrpCat.{uC} R q
  let N := Functor.IsCofibered.fiberHomologyFunctor (p := proj) AddCommGrpCat.{uC} R q
  let ω := Functor.IsCofibered.costructuredFiberHomologyNatIso (p := proj) AddCommGrpCat.{uC} R q
  let γ := Functor.IsCofibered.costructuredFiberHomologyIso
    (p := proj) AddCommGrpCat.{uC} (0 : Translation C) R q
  let χ := Functor.IsCofibered.cofiberedVerticalHomologyComplexIso (p := proj) R q
  let T := CategoryHomology.terminalWeightCoefficientBarDegreeIso Cq 0
  let p₀ := constantBaseIndex (0 : Translation C) 0
  let t := HomologicalComplex.homologyMap
    (SSet.chainComplexMap (rowIncl) R ≫ (rowIso).hom) q
  let ιN := CategoryHomology.coefficientBarι N (ComposableArrows.mk₀ (0 : Translation C))
  have hr : SSet.chainComplexMap (rowIncl) R ≫ (rowIso).hom =
      SSet.chainComplexMap (rowIncl) R := by
    change SSet.chainComplexMap (rowIncl) R ≫ 𝟙 _ = _
    exact Category.comp_id _
  have ht : t = SSet.homologyMap (rowIncl) R q :=
    congrArg (fun f => HomologicalComplex.homologyMap f q) hr
  have hχ : χ.hom.f 0 = (SSet.bkAlternatingVerticalHomologyIso R commaD 0 q).hom ≫
      T.hom ≫ CategoryHomology.coefficientBarMap ω.hom 0 :=
    original_vertical_coefficient_component C R q
  have hs : SSet.homologyMap (rowIncl) R q ≫
      (SSet.bkAlternatingVerticalHomologyIso R commaD 0 q).hom =
        StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit (Translation C)) Cq 0 p₀ := by
    exact SSet.homologyMap_ι_comp_homologySigmaIso_hom
      (fun x : StrictOrdinaryWeightedBar.WIdx (Translation C)
        (CategoryBar.replUnit (Translation C)) 0 => (commaD).obj x.1.left) R q p₀
  have hT : StrictOrdinaryWeightedBar.wbarIncl
      (CategoryBar.replUnit (Translation C)) Cq 0 p₀ ≫ T.hom =
        CategoryHomology.coefficientBarι Cq (ComposableArrows.mk₀ (0 : Translation C)) :=
    CategoryHomology.wbarIncl_terminalWeightCoefficientBarDegreeIso_hom Cq 0 p₀
  have h : t ≫ χ.hom.f 0 = γ.hom ≫ ιN := by
    calc
      _ = SSet.homologyMap (rowIncl) R q ≫
          (SSet.bkAlternatingVerticalHomologyIso R commaD 0 q).hom ≫
          T.hom ≫ CategoryHomology.coefficientBarMap ω.hom 0 := by rw [ht, hχ]
      _ = StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit (Translation C)) Cq 0 p₀ ≫
          T.hom ≫ CategoryHomology.coefficientBarMap ω.hom 0 := by
        simpa only [Category.assoc] using hs =≫ (T.hom ≫ CategoryHomology.coefficientBarMap ω.hom 0)
      _ = CategoryHomology.coefficientBarι Cq (ComposableArrows.mk₀ (0 : Translation C)) ≫
          CategoryHomology.coefficientBarMap ω.hom 0 := by
        simpa only [Category.assoc] using hT =≫ CategoryHomology.coefficientBarMap ω.hom 0
      _ = _ := by
        exact CategoryHomology.coefficientBarι_map ω.hom (ComposableArrows.mk₀ (0 : Translation C))
  change γ.inv ≫ t ≫ χ.hom.f 0 = ιN
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
    congrArg (fun f => γ.inv ≫ f) h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_fiber_class_vertical_quotient (q : ℕ) :
    CategoryHomology.coefficientHomologyClass
        (Functor.IsCofibered.fiberHomologyFunctor (p := proj) AddCommGrpCat.{uC} R q)
        (0 : Translation C) ≫
      (Functor.IsCofibered.cofiberedVerticalHorizontalHomologyIso (p := proj) R 0 q).inv =
    (Functor.IsCofibered.costructuredFiberHomologyIso
        (p := proj) AddCommGrpCat.{uC} (0 : Translation C) R q).inv ≫
      HomologicalComplex.homologyMap (SSet.chainComplexMap (rowIncl) R ≫ (rowIso).hom) q ≫
        ChainComplex.homologyZeroClass (((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R
          (SSet.rightCommaNerveDiagram (translationProjection (C := C))))).verticalHomologyComplex
          q) := by
  let N := Functor.IsCofibered.fiberHomologyFunctor (p := proj) AddCommGrpCat.{uC} R q
  let V := ((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
    (translationProjection (C := C))))).verticalHomologyComplex q
  let χ := Functor.IsCofibered.cofiberedVerticalHomologyComplexIso (p := proj) R q
  let φ := Functor.IsCofibered.cofiberedVerticalHorizontalHomologyIso (p := proj) R 0 q
  let γ := Functor.IsCofibered.costructuredFiberHomologyIso
    (p := proj) AddCommGrpCat.{uC} (0 : Translation C) R q
  let ιN := CategoryHomology.coefficientBarι N (ComposableArrows.mk₀ (0 : Translation C))
  let t := HomologicalComplex.homologyMap (SSet.chainComplexMap (rowIncl) R ≫ (rowIso).hom) q
  let e := CategoryHomology.coefficientHomologyZeroComparison N
  have hc : χ.hom.f 0 ≫ χ.inv.f 0 = 𝟙 _ := by
    have h := congrArg (fun f : V ⟶ V => f.f 0) χ.hom_inv_id
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using h
  have hw : γ.inv ≫ t ≫ χ.hom.f 0 = ιN := original_weighted_fiber_summand C R q
  have hι : ιN ≫ χ.inv.f 0 = γ.inv ≫ t := by
    have h := congrArg (fun f => f ≫ χ.inv.f 0) hw
    calc
      _ = (γ.inv ≫ t ≫ χ.hom.f 0) ≫ χ.inv.f 0 := h.symm
      _ = γ.inv ≫ ((t ≫ χ.hom.f 0) ≫ χ.inv.f 0) := Category.assoc _ _ _
      _ = γ.inv ≫ t ≫ (χ.hom.f 0 ≫ χ.inv.f 0) :=
        γ.inv ≫= Category.assoc _ _ _
      _ = γ.inv ≫ t ≫ 𝟙 _ := γ.inv ≫= t ≫= hc
      _ = γ.inv ≫ t := γ.inv ≫= Category.comp_id _
  have hf : φ.inv = e.hom ≫ HomologicalComplex.homologyMap χ.inv 0 := by rfl
  have hclass : CategoryHomology.coefficientHomologyClass N (0 : Translation C) ≫ e.hom =
      ιN ≫ ChainComplex.homologyZeroClass (CategoryHomology.coefficientBarComplex N) :=
    CategoryHomology.coefficientHomologyClass_comp_coefficientHomologyZeroComparison_hom
      N (0 : Translation C)
  have hp := ChainComplex.homologyZeroClass_naturality χ.inv
  change CategoryHomology.coefficientHomologyClass N (0 : Translation C) ≫ φ.inv =
    γ.inv ≫ t ≫ ChainComplex.homologyZeroClass V
  calc
    _ = (CategoryHomology.coefficientHomologyClass N (0 : Translation C) ≫ e.hom) ≫
        HomologicalComplex.homologyMap χ.inv 0 := by rw [hf, Category.assoc]
    _ = ιN ≫ ChainComplex.homologyZeroClass (CategoryHomology.coefficientBarComplex N) ≫
        HomologicalComplex.homologyMap χ.inv 0 := by rw [hclass, Category.assoc]
    _ = ιN ≫ χ.inv.f 0 ≫ ChainComplex.homologyZeroClass V := by
      simpa only [Category.assoc] using congrArg (fun f => ιN ≫ f) hp
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ ChainComplex.homologyZeroClass V) hι

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_core_fiber_weighted_homology (q : ℕ) :
    (coreTranslationFiberHomologyIso C (0 : Translation C) R q).hom ≫
      (Functor.IsCofibered.costructuredFiberHomologyIso
        (p := proj) AddCommGrpCat.{uC} (0 : Translation C) R q).inv ≫
        HomologicalComplex.homologyMap
          (SSet.chainComplexMap (rowIncl) R ≫ (rowIso).hom) q =
      HomologicalComplex.homologyMap (jrow) q := by
  let i := coreToTranslationFiber (Core.mk (0 : C))
  let c := Functor.IsCofibered.fiberToCostructuredArrow
    (p := proj) (0 : Translation C)
  let hColimits : HasColimitsOfSize.{uC, uC} AddCommGrpCat.{uC} := inferInstance
  let : HasCoproducts.{uC} AddCommGrpCat.{uC} :=
    fun J => hColimits.has_colimits_of_shape (Discrete J)
  let T : SSet.{uC} ⥤ ChainComplex AddCommGrpCat.{uC} ℕ :=
    (SSet.chainComplexFunctor.{uC} AddCommGrpCat.{uC}).obj R
  have hn : nerveMap i ≫ nerveMap c = (j) := by
    ext a x
    rfl
  have hF : SSet.chainComplexMap (j) R =
      SSet.chainComplexMap (nerveMap i) R ≫ SSet.chainComplexMap (nerveMap c) R := by
    change T.map (j) = T.map (nerveMap i) ≫ T.map (nerveMap c)
    rw [← hn]
    exact T.map_comp _ _
  have hr : (jrow) = SSet.chainComplexMap (nerveMap i) R ≫
      SSet.chainComplexMap (nerveMap c) R ≫
      SSet.chainComplexMap (rowIncl) R ≫ (rowIso).hom := by
    change T.map ((j) ≫ (rowIncl)) ≫ (rowIso).hom =
      T.map (nerveMap i) ≫ T.map (nerveMap c) ≫ T.map (rowIncl) ≫ (rowIso).hom
    calc
      _ = (T.map (j) ≫ T.map (rowIncl)) ≫ (rowIso).hom :=
        (T.map_comp (j) (rowIncl)) =≫ (rowIso).hom
      _ = ((T.map (nerveMap i) ≫ T.map (nerveMap c)) ≫ T.map (rowIncl)) ≫
          (rowIso).hom := (hF =≫ T.map (rowIncl)) =≫ (rowIso).hom
      _ = _ := by simp only [Category.assoc]
  have hH := congrArg (fun f => HomologicalComplex.homologyMap f q) hr
  change HomologicalComplex.homologyMap (SSet.chainComplexMap (nerveMap i) R) q ≫
    HomologicalComplex.homologyMap (SSet.chainComplexMap (nerveMap c) R) q ≫
      HomologicalComplex.homologyMap (SSet.chainComplexMap (rowIncl) R ≫ (rowIso).hom) q = _
  simpa only [HomologicalComplex.homologyMap_comp, Category.assoc] using hH.symm

/-- The same original right-comma BK bicomplex, with its value category fixed. -/
private abbrev cachedOriginalRowBicomplex :
    HomologicalComplex₂ AddCommGrpCat.{uC} (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R
    (SSet.rightCommaNerveDiagram (translationProjection (C := C)))

/-- The original module coefficient functor at the given whole-core degree. -/
private abbrev cachedOriginalRowCoefficientFunctor (q : ℕ) :
    Translation C ⥤ ModuleCat.{uC} (coreTranslationRing C) :=
  coreTranslationCoefficientFunctor C R q

/-- The actual strict-fiber coefficient functor of the original projection. -/
private abbrev cachedOriginalRowFiberFunctor (q : ℕ) :
    Translation C ⥤ AddCommGrpCat.{uC} :=
  Functor.IsCofibered.fiberHomologyFunctor
    (p := translationProjection (C := C)) AddCommGrpCat.{uC} R q

/-- The original module-forgetting comparison at degree zero. -/
private abbrev cachedOriginalRowForgetIso (q : ℕ) :
    (forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC}).obj
        (CategoryHomology.homologyWithCoefficients
          (cachedOriginalRowCoefficientFunctor C R q) 0) ≅
      CategoryHomology.homologyWithCoefficients
        (cachedOriginalRowCoefficientFunctor C R q ⋙
          forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC}) 0 :=
  homologyWithCoefficientsForgetIso (cachedOriginalRowCoefficientFunctor C R q) 0

/-- The same objectwise core/fiber comparison, with both coefficient functors fixed. -/
private abbrev cachedOriginalRowFiberNatIso (q : ℕ) :
    cachedOriginalRowCoefficientFunctor C R q ⋙
        forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC} ≅
      cachedOriginalRowFiberFunctor C R q :=
  coreTranslationCoefficientFiberNatIso C R q

/-- The original kappa Iso, with its module-forgetting source and native page fixed. -/
private abbrev cachedOriginalRowKappaIso (q : ℕ) :
    (forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC}).obj
        (CategoryHomology.homologyWithCoefficients
          (cachedOriginalRowCoefficientFunctor C R q) 0) ≅
      ((translationBKHomologySpectralSequence C R).page 2).X (0, q) :=
  coreTranslationActionSecondPageIso C R 0 q

/-- The original signed second-page comparison for that same bicomplex. -/
private abbrev cachedOriginalRowEtaIso (q : ℕ) :
    ((translationBKHomologySpectralSequence C R).page 2).X (0, q) ≅
      ((cachedOriginalRowBicomplex C R).verticalHomologyComplex q).homology 0 :=
  HomologicalComplex₂.horizontalSecondPageVerticalHorizontalHomologyIso
    (cachedOriginalRowBicomplex C R) 0 q

/-- The original strict-fiber Iso uses the original named cofibered dictionary. -/
private abbrev cachedOriginalRowPhiIso (q : ℕ) :
    ((cachedOriginalRowBicomplex C R).verticalHomologyComplex q).homology 0 ≅
      CategoryHomology.homologyWithCoefficients (cachedOriginalRowFiberFunctor C R q) 0 :=
  @Functor.IsCofibered.cofiberedVerticalHorizontalHomologyIso.{uC, uC}
    (Translation C) (Pair C)
    (inferInstanceAs (Category.{uC} (Translation C)))
    (inferInstanceAs (Category.{uC} (Pair C)))
    (translationProjection (C := C))
    (translationProjection_isCofibered (C := C)) R 0 q

private theorem original_kappa_eta (q : ℕ) :
    (cachedOriginalRowKappaIso C R q).hom ≫ (cachedOriginalRowEtaIso C R q).hom =
    (cachedOriginalRowForgetIso C R q).hom ≫
      (CategoryHomology.homologyWithCoefficientsFunctor
        (C := Translation C) (A := AddCommGrpCat.{uC}) 0).map
          (cachedOriginalRowFiberNatIso C R q).hom ≫
      (cachedOriginalRowPhiIso C R q).inv := by
  let F : Translation C ⥤ ModuleCat.{uC} (coreTranslationRing C) :=
    cachedOriginalRowCoefficientFunctor C R q
  let N : Translation C ⥤ AddCommGrpCat.{uC} := cachedOriginalRowFiberFunctor C R q
  let H : (Translation C ⥤ AddCommGrpCat.{uC}) ⥤ AddCommGrpCat.{uC} :=
    CategoryHomology.homologyWithCoefficientsFunctor
      (C := Translation C) (A := AddCommGrpCat.{uC}) 0
  let η : ((translationBKHomologySpectralSequence C R).page 2).X (0, q) ≅
      ((cachedOriginalRowBicomplex C R).verticalHomologyComplex q).homology 0 :=
    cachedOriginalRowEtaIso C R q
  let φ : ((cachedOriginalRowBicomplex C R).verticalHomologyComplex q).homology 0 ≅
      CategoryHomology.homologyWithCoefficients N 0 := cachedOriginalRowPhiIso C R q
  let ψ : (forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC}).obj
        (CategoryHomology.homologyWithCoefficients F 0) ≅
      CategoryHomology.homologyWithCoefficients
        (F ⋙ forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC}) 0 :=
    cachedOriginalRowForgetIso C R q
  let α : F ⋙ forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC} ≅ N :=
    cachedOriginalRowFiberNatIso C R q
  let Hα : CategoryHomology.homologyWithCoefficients
        (F ⋙ forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC}) 0 ⟶
      CategoryHomology.homologyWithCoefficients N 0 := H.map α.hom
  have hκ : (cachedOriginalRowKappaIso C R q).hom =
      (ψ.hom ≫ Hα) ≫ (φ.inv ≫ η.inv) := by rfl
  rw [hκ]
  change ((ψ.hom ≫ Hα) ≫ (φ.inv ≫ η.inv)) ≫ η.hom = ψ.hom ≫ Hα ≫ φ.inv
  calc
    _ = (ψ.hom ≫ Hα) ≫ ((φ.inv ≫ η.inv) ≫ η.hom) := Category.assoc _ _ _
    _ = (ψ.hom ≫ Hα) ≫ (φ.inv ≫ (η.inv ≫ η.hom)) :=
      (ψ.hom ≫ Hα) ≫= Category.assoc _ _ _
    _ = (ψ.hom ≫ Hα) ≫ (φ.inv ≫ 𝟙 _) := (ψ.hom ≫ Hα) ≫= φ.inv ≫= η.inv_hom_id
    _ = (ψ.hom ≫ Hα) ≫ φ.inv := (ψ.hom ≫ Hα) ≫= Category.comp_id _
    _ = _ := Category.assoc _ _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_core_class_kappa (q : ℕ) :
    ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map
      (CategoryHomology.coefficientHomologyClass
        (coreTranslationCoefficientFunctor C R q) (0 : Translation C)) ≫
      (coreTranslationActionSecondPageIso C R 0 q).hom ≫
        (HomologicalComplex₂.horizontalSecondPageVerticalHorizontalHomologyIso
          ((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
          (translationProjection (C := C))))) 0 q).hom =
    (coreTranslationHomologyModuleAddCommGrpIso C R q).hom ≫
      HomologicalComplex.homologyMap (jrow) q ≫
        ChainComplex.homologyZeroClass (((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R
          (SSet.rightCommaNerveDiagram (translationProjection (C := C))))).verticalHomologyComplex
          q) := by
  let F := coreTranslationCoefficientFunctor C R q
  let N := Functor.IsCofibered.fiberHomologyFunctor (p := proj) AddCommGrpCat.{uC} R q
  let α := coreTranslationCoefficientFiberNatIso C R q
  let ψ := homologyWithCoefficientsForgetIso F 0
  let φ := Functor.IsCofibered.cofiberedVerticalHorizontalHomologyIso (p := proj) R 0 q
  let ε := coreTranslationHomologyModuleAddCommGrpIso C R q
  let eCore := coreTranslationFiberHomologyIso C (0 : Translation C) R q
  let γ := Functor.IsCofibered.costructuredFiberHomologyIso
    (p := proj) AddCommGrpCat.{uC} (0 : Translation C) R q
  let t := HomologicalComplex.homologyMap (SSet.chainComplexMap (rowIncl) R ≫ (rowIso).hom) q
  let qV := ChainComplex.homologyZeroClass (((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R
    (SSet.rightCommaNerveDiagram (translationProjection (C := C))))).verticalHomologyComplex q)
  let Hα := (CategoryHomology.homologyWithCoefficientsFunctor 0).map α.hom
  have hf : ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map
    (CategoryHomology.coefficientHomologyClass F (0 : Translation C)) ≫
      ψ.hom = CategoryHomology.coefficientHomologyClass (F ⋙ (forget₂ (ModuleCat.{uC}
        (coreTranslationRing C)) AddCommGrpCat.{uC})) (0 : Translation C) :=
    original_coefficient_class_forget F (0 : Translation C)
  have hn : CategoryHomology.coefficientHomologyClass (F ⋙ (forget₂ (ModuleCat.{uC}
    (coreTranslationRing C)) AddCommGrpCat.{uC})) (0 : Translation C) ≫
      Hα = α.hom.app (0 : Translation C) ≫
        CategoryHomology.coefficientHomologyClass N (0 : Translation C) :=
    CategoryHomology.coefficientHomologyClass_naturality α.hom (0 : Translation C)
  have ha : α.hom.app (0 : Translation C) = ε.hom ≫ eCore.hom :=
    coreTranslationCoefficientFiberIsoApp_hom C R q (0 : Translation C)
  have hφ : CategoryHomology.coefficientHomologyClass N (0 : Translation C) ≫ φ.inv =
      γ.inv ≫ t ≫ qV := original_fiber_class_vertical_quotient C R q
  have hj : eCore.hom ≫ γ.inv ≫ t = HomologicalComplex.homologyMap (jrow) q :=
    original_core_fiber_weighted_homology C R q
  calc
    _ = ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map
      (CategoryHomology.coefficientHomologyClass F (0 : Translation C)) ≫
        ψ.hom ≫ Hα ≫ φ.inv :=
      ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map
        (CategoryHomology.coefficientHomologyClass F (0 : Translation C)) ≫=
        original_kappa_eta C R q
    _ = CategoryHomology.coefficientHomologyClass (F ⋙ (forget₂ (ModuleCat.{uC} (coreTranslationRing
      C)) AddCommGrpCat.{uC})) (0 : Translation C) ≫
        Hα ≫ φ.inv := by
      simpa only [Category.assoc] using hf =≫ (Hα ≫ φ.inv)
    _ = α.hom.app (0 : Translation C) ≫
        CategoryHomology.coefficientHomologyClass N (0 : Translation C) ≫ φ.inv := by
      simpa only [Category.assoc] using hn =≫ φ.inv
    _ = ε.hom ≫ eCore.hom ≫ γ.inv ≫ t ≫ qV := by
      rw [ha, Category.assoc, hφ]
    _ = _ := by
      simpa only [Category.assoc] using ε.hom ≫= hj =≫ qV

end OriginalRow


end CategoryTheory.SInverseS



/-! Accepted native representative-forgetting blocks, integrated in this unit. -/

open CategoryTheory.Abelian ComposableArrows

namespace CategoryTheory.Abelian.SpectralObject

universe u v w t

variable {M : Type w} [Monoid M] {ι : Type t} [Category.{v} ι]

private theorem intervalForget_hom_eqToHom
    (X : SpectralObject AddCommGrpCat.{u} ι) (σ : M →* End X)
    (n : ℤ) (I : ComposableArrows ι 1) :
    (X.monoidModuleIntervalForgetIso σ n I).hom =
      eqToHom (congrArg (fun Z : SpectralObject AddCommGrpCat.{u} ι =>
        (Z.H n).obj I) (X.forgetMonoidModule_monoidModule σ)) := by
  cases X
  ext x
  rw [monoidModuleIntervalForgetIso_hom_apply]
  rfl

variable (Y : SpectralObject (ModuleCat.{u} (MonoidAlgebra ℤ M)) ι)

private def recoveredIntervalIso (X : SpectralObject AddCommGrpCat.{u} ι)
    (hX : forgetMonoidModule Y = X) (n : ℤ) (I : ComposableArrows ι 1) :
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).obj
        ((Y.H n).obj I) ≅ (X.H n).obj I :=
  eqToIso (congrArg (fun Z : SpectralObject AddCommGrpCat.{u} ι =>
    (Z.H n).obj I) hX)

private theorem recoveredIntervalIso_self_hom (n : ℤ) (I : ComposableArrows ι 1) :
    (recoveredIntervalIso Y (forgetMonoidModule Y) rfl n I).hom =
      𝟙 ((forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).obj
        ((Y.H n).obj I)) := by
  rfl

private def recoveredCyclesIso (X : SpectralObject AddCommGrpCat.{u} ι)
    (hX : forgetMonoidModule Y = X)
    {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n : ℤ) :
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).obj
        (Y.cycles f g n) ≅ X.cycles f g n :=
  Y.forgetMonoidModuleCyclesIso f g n ≪≫
    eqToIso (congrArg (fun Z : SpectralObject AddCommGrpCat.{u} ι =>
      Z.cycles f g n) hX)

private def recoveredEIso (X : SpectralObject AddCommGrpCat.{u} ι)
    (hX : forgetMonoidModule Y = X)
    {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).obj
        (Y.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) ≅
      X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ :=
  Y.forgetMonoidModuleEIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≪≫
    eqToIso (congrArg (fun Z : SpectralObject AddCommGrpCat.{u} ι =>
      Z.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) hX)

private theorem forgetToCycles {i j k : ι}
    (f : i ⟶ j) (g : j ⟶ k) (fg : i ⟶ k) (hfg : f ≫ g = fg) (n : ℤ) :
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).map
        (Y.toCycles f g fg hfg n) ≫
      (Y.forgetMonoidModuleCyclesIso f g n).hom =
    (forgetMonoidModule Y).toCycles f g fg hfg n := by
  let U := forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}
  apply (cancel_mono ((forgetMonoidModule Y).iCycles f g n)).1
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => U.map (Y.toCycles f g fg hfg n) ≫ a)
      (Y.forgetMonoidModuleCyclesIso_hom_iCycles f g n)).trans
      ((U.map_comp (Y.toCycles f g fg hfg n) (Y.iCycles f g n)).symm.trans
        ((congrArg U.map (Y.toCycles_i f g fg hfg n)).trans
          ((forgetMonoidModule Y).toCycles_i f g fg hfg n).symm)))

private theorem recoveredToCycles (X : SpectralObject AddCommGrpCat.{u} ι)
    (hX : forgetMonoidModule Y = X) {i j k : ι}
    (f : i ⟶ j) (g : j ⟶ k) (fg : i ⟶ k) (hfg : f ≫ g = fg) (n : ℤ) :
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).map
        (Y.toCycles f g fg hfg n) ≫ (recoveredCyclesIso Y X hX f g n).hom =
      (recoveredIntervalIso Y X hX n (mk₁ fg)).hom ≫ X.toCycles f g fg hfg n := by
  subst X
  simp only [recoveredCyclesIso, Iso.trans_hom, eqToIso.hom, eqToHom_refl,
    recoveredIntervalIso_self_hom, Category.comp_id]
  exact (forgetToCycles Y f g fg hfg n).trans
    (Category.id_comp ((forgetMonoidModule Y).toCycles f g fg hfg n)).symm

private theorem recoveredEIso_pi (X : SpectralObject AddCommGrpCat.{u} ι)
    (hX : forgetMonoidModule Y = X)
    {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).map
        (Y.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) ≫
      (recoveredEIso Y X hX f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom =
    (recoveredCyclesIso Y X hX f₁ f₂ n₁).hom ≫
      X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ := by
  subst X
  simpa only [recoveredEIso, recoveredCyclesIso, Iso.trans_hom,
    eqToIso.hom, eqToHom_refl, Category.comp_id] using
    Y.forgetMonoidModuleEIso_πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂

private theorem recoveredEIso_map (X : SpectralObject AddCommGrpCat.{u} ι)
    (hX : forgetMonoidModule Y = X)
    {i₀ i₁ i₂ i₃ j₀ j₁ j₂ j₃ : ι}
    (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (g₁ : j₀ ⟶ j₁) (g₂ : j₁ ⟶ j₂) (g₃ : j₂ ⟶ j₃)
    (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ g₁ g₂ g₃)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).map
        (Y.map f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ hn₁ hn₂) ≫
      (recoveredEIso Y X hX g₁ g₂ g₃ n₀ n₁ n₂ hn₁ hn₂).hom =
    (recoveredEIso Y X hX f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom ≫
      X.map f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ hn₁ hn₂ := by
  subst X
  simpa only [recoveredEIso, Iso.trans_hom, eqToIso.hom,
    eqToHom_refl, Category.comp_id] using
    Y.forgetMonoidModuleEIso_map f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ hn₁ hn₂

private theorem recoveredCokernel_g (X : SpectralObject AddCommGrpCat.{u} ι)
    (hX : forgetMonoidModule Y = X)
    {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).map
        (Y.cokernelSequenceE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂).g ≫
      (recoveredEIso Y X hX f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom =
    (recoveredIntervalIso Y X hX n₁ (mk₁ f₁₂)).hom ≫
      (X.cokernelSequenceE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂).g := by
  dsimp only [cokernelSequenceE]
  rw [Functor.map_comp, Category.assoc]
  erw [recoveredEIso_pi Y X hX f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂]
  rw [← Category.assoc]
  erw [recoveredToCycles Y X hX f₁ f₂ f₁₂ h₁₂ n₁]
  exact Category.assoc _ _ _

private theorem zeroColumnLower_le : ((-2 : ℤ) : EInt) ≤ ((-1 : ℤ) : EInt) :=
  WithBotTop.coe_monotone (by omega)

private theorem zeroColumnMiddle_le : ((-1 : ℤ) : EInt) ≤ ((0 : ℤ) : EInt) :=
  WithBotTop.coe_monotone (by omega)

private theorem zeroColumnUpper_le : ((0 : ℤ) : EInt) ≤ ((1 : ℤ) : EInt) :=
  WithBotTop.coe_monotone (by omega)

private abbrev zeroColumnLowerArrow := homOfLE zeroColumnLower_le
private abbrev zeroColumnMiddleArrow := homOfLE zeroColumnMiddle_le
private abbrev zeroColumnUpperArrow := homOfLE zeroColumnUpper_le
private abbrev zeroColumnBottomArrow :=
  homOfLE (bot_le : (⊥ : EInt) ≤ ((-1 : ℤ) : EInt))
private abbrev zeroColumnBottomToZero :=
  homOfLE (bot_le : (⊥ : EInt) ≤ ((0 : ℤ) : EInt))

section NativeWindow

variable {D : Type uD} [Category.{vD} D] [Abelian D]
  (X : SpectralObject D EInt)

private abbrev nativePageWindow (q : ℕ) : D :=
  X.E zeroColumnLowerArrow zeroColumnMiddleArrow zeroColumnUpperArrow
    (-(q : ℤ) - 1) (-(q : ℤ)) (-(q : ℤ) + 1) (by omega) rfl

private abbrev nativeBottomWindow (q : ℕ) : D :=
  X.E zeroColumnBottomArrow zeroColumnMiddleArrow zeroColumnUpperArrow
    (-(q : ℤ) - 1) (-(q : ℤ)) (-(q : ℤ) + 1) (by omega) rfl

private def nativeProjection (q : ℕ) :
    X.stableIntervalStep (-(q : ℤ)) ((0 : ℤ) : EInt) ⟶ nativeBottomWindow X q :=
  (X.cokernelSequenceE zeroColumnBottomArrow zeroColumnMiddleArrow
    zeroColumnUpperArrow zeroColumnBottomToZero (Subsingleton.elim _ _)
    (-(q : ℤ) - 1) (-(q : ℤ)) (-(q : ℤ) + 1) (by omega) rfl).g

private def nativeOuterLeftIso
    (hneg : ∀ (n a : ℤ), a < 0 → IsZero ((X.H n).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (a : EInt)))))) (q : ℕ) :
    nativeBottomWindow X q ≅ nativePageWindow X q :=
  X.isoMapFourδ₁Toδ₀' (⊥ : EInt) ((-2 : ℤ) : EInt) ((-1 : ℤ) : EInt)
    ((0 : ℤ) : EInt) ((1 : ℤ) : EInt)
    bot_le zeroColumnLower_le zeroColumnMiddle_le zeroColumnUpper_le
    (-(q : ℤ) - 1) (-(q : ℤ)) (-(q : ℤ) + 1)
    (hneg (-(q : ℤ) + 1) (-2) (by omega)) (by omega) rfl

variable [X.HasSpectralSequence coreE₁FirstQuadrantHomological]

private def nativePresentation (q : ℕ) :
    ((X.spectralSequence coreE₁FirstQuadrantHomological).page
      (2 : ℤ) (by omega)).X (0, q) ≅ nativePageWindow X q :=
  X.spectralSequencePageXIso coreE₁FirstQuadrantHomological (2 : ℤ) (by omega) (0, q)
    ((-2 : ℤ) : EInt) ((-1 : ℤ) : EInt) ((0 : ℤ) : EInt) ((1 : ℤ) : EInt)
    (by simp [coreE₁FirstQuadrantHomological])
    (by simp [coreE₁FirstQuadrantHomological])
    (by simp [coreE₁FirstQuadrantHomological])
    (by simp [coreE₁FirstQuadrantHomological])
    (-(q : ℤ) - 1) (-(q : ℤ)) (-(q : ℤ) + 1)
    (by simp [coreE₁FirstQuadrantHomological]) (by omega) rfl

private theorem nativeRepresentative_presented
    (hneg : ∀ (n a : ℤ), a < 0 → IsZero ((X.H n).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (a : EInt)))))) (q : ℕ) :
    X.nativeZeroColumnStageZeroRepresentative hneg q ≫ (nativePresentation X q).hom =
      nativeProjection X q ≫ (nativeOuterLeftIso X hneg q).hom := by
  exact X.nativeZeroColumnStageZeroRepresentative_comp_pageXIso_hom hneg q

end NativeWindow

end CategoryTheory.Abelian.SpectralObject

namespace CategoryTheory.SInverseS

open HomologicalComplex₂

variable {C : Type uC} [Category.{uC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] (R : AddCommGrpCat.{uC})

local notation "Y" => secondTranslationBKModuleSpectralObject (C := C) R
local notation "A" => MonoidAlgebra ℤ (Multiplicative (Skeleton C))

private def nativeIntervalForgetIso (n : ℤ) (I : ComposableArrows EInt 1) :
    ((forget₂ (ModuleCat.{uC} (MonoidAlgebra ℤ (Multiplicative (Skeleton C))))
      AddCommGrpCat.{uC})).obj (((Y).H n).obj I) ≅ (((horizontalCompleteFiltrationSpectralObject
      (SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
      (translationProjection (C := C)))))).H n).obj I :=
  ((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R
    (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).monoidModuleIntervalForgetIso
    (secondTranslationBKSpectralAction (C := C) R) n I

private theorem nativeIntervalForgetIso_hom (n : ℤ) (I : ComposableArrows EInt 1) :
    (nativeIntervalForgetIso (C := C) R n I).hom =
      eqToHom (congrArg (fun Z : SpectralObject AddCommGrpCat.{uC} EInt =>
        (Z.H n).obj I) (secondTranslationBKModuleSpectralObject_forget (C := C) R)) :=
  SpectralObject.intervalForget_hom_eqToHom ((horizontalCompleteFiltrationSpectralObject
    (SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
    (translationProjection (C := C))))))
    (secondTranslationBKSpectralAction (C := C) R) n I

private theorem nativeNegativeSupportE (n a : ℤ) (ha : a < 0) :
    IsZero ((((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex
      AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).H
      n).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (a : EInt))))) :=
  horizontalCompleteFiltrationSpectralObject_H_isZero_of_obj_isZero (SSet.bkAlternatingBicomplex
    AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram (translationProjection (C := C))))
    bot_le (horizontalCompleteFiltrationCochainDiagram_obj_isZero_bot (SSet.bkAlternatingBicomplex
      AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))
    (horizontalCompleteFiltrationCochainDiagram_obj_isZero_of_neg (SSet.bkAlternatingBicomplex
      AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) a ha) n

private theorem nativeNegativeSupportY (n a : ℤ) (ha : a < 0) :
    IsZero (((Y).H n).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (a : EInt))))) := by
  let I : ComposableArrows EInt 1 := mk₁ (homOfLE
    (bot_le : (⊥ : EInt) ≤ (a : EInt)))
  have h : IsZero (((forget₂ (ModuleCat.{uC} (MonoidAlgebra ℤ (Multiplicative (Skeleton C))))
    AddCommGrpCat.{uC})).obj (((Y).H n).obj I)) :=
    (nativeIntervalForgetIso (C := C) R n I).isZero_iff.mpr
      (nativeNegativeSupportE (C := C) R n a ha)
  rw [IsZero.iff_id_eq_zero] at h ⊢
  apply ((forget₂ (ModuleCat.{uC} (MonoidAlgebra ℤ (Multiplicative (Skeleton C))))
    AddCommGrpCat.{uC})).map_injective
  simpa only [Functor.map_id, Functor.map_zero] using h

private def nativePageComponentForgetIso (q : ℕ) :
    ((forget₂ (ModuleCat.{uC} (MonoidAlgebra ℤ (Multiplicative (Skeleton C))))
      AddCommGrpCat.{uC})).obj ((((Y).spectralSequence
      SpectralObject.coreE₁FirstQuadrantHomological).page
      (2 : ℤ) (by omega)).X (0, q)) ≅
    ((((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R
      (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).spectralSequence
      SpectralObject.coreE₁FirstQuadrantHomological).page
      (2 : ℤ) (by omega)).X (0, q) :=
  (HomologicalComplex.eval AddCommGrpCat.{uC}
    (ComplexShape.spectralSequenceNat ⟨-2, 1⟩) (0, q)).mapIso
    (secondTranslationBKModulePageForgetIso (C := C) R (2 : ℤ) (by omega))

private def nativeWindowForgetIso (q : ℕ) :
    ((forget₂ (ModuleCat.{uC} (MonoidAlgebra ℤ (Multiplicative (Skeleton C))))
      AddCommGrpCat.{uC})).obj (SpectralObject.nativePageWindow (Y) q) ≅
      SpectralObject.nativePageWindow ((horizontalCompleteFiltrationSpectralObject
        (SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
        (translationProjection (C := C)))))) q :=
  SpectralObject.recoveredEIso (Y) ((horizontalCompleteFiltrationSpectralObject
    (SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
    (translationProjection (C := C))))))
    (secondTranslationBKModuleSpectralObject_forget (C := C) R)
    SpectralObject.zeroColumnLowerArrow SpectralObject.zeroColumnMiddleArrow
    SpectralObject.zeroColumnUpperArrow
    (-(q : ℤ) - 1) (-(q : ℤ)) (-(q : ℤ) + 1) (by omega) rfl

private def nativeBottomForgetIso (q : ℕ) :
    ((forget₂ (ModuleCat.{uC} (MonoidAlgebra ℤ (Multiplicative (Skeleton C))))
      AddCommGrpCat.{uC})).obj (SpectralObject.nativeBottomWindow (Y) q) ≅
      SpectralObject.nativeBottomWindow ((horizontalCompleteFiltrationSpectralObject
        (SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
        (translationProjection (C := C)))))) q :=
  SpectralObject.recoveredEIso (Y) ((horizontalCompleteFiltrationSpectralObject
    (SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
    (translationProjection (C := C))))))
    (secondTranslationBKModuleSpectralObject_forget (C := C) R)
    SpectralObject.zeroColumnBottomArrow SpectralObject.zeroColumnMiddleArrow
    SpectralObject.zeroColumnUpperArrow
    (-(q : ℤ) - 1) (-(q : ℤ)) (-(q : ℤ) + 1) (by omega) rfl

private theorem nativeProjection_forget (q : ℕ) :
    ((forget₂ (ModuleCat.{uC} (MonoidAlgebra ℤ (Multiplicative (Skeleton C))))
      AddCommGrpCat.{uC})).map (SpectralObject.nativeProjection (Y) q) ≫
      (nativeBottomForgetIso (C := C) R q).hom =
    (nativeIntervalForgetIso (C := C) R (-(q : ℤ))
      (mk₁ SpectralObject.zeroColumnBottomToZero)).hom ≫
      SpectralObject.nativeProjection ((horizontalCompleteFiltrationSpectralObject
        (SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
        (translationProjection (C := C)))))) q := by
  have h := SpectralObject.recoveredCokernel_g (Y) ((horizontalCompleteFiltrationSpectralObject
    (SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
    (translationProjection (C := C))))))
    (secondTranslationBKModuleSpectralObject_forget (C := C) R)
    SpectralObject.zeroColumnBottomArrow SpectralObject.zeroColumnMiddleArrow
    SpectralObject.zeroColumnUpperArrow SpectralObject.zeroColumnBottomToZero
    (Subsingleton.elim _ _) (-(q : ℤ) - 1) (-(q : ℤ)) (-(q : ℤ) + 1) (by omega) rfl
  dsimp only [SpectralObject.nativeProjection, nativeBottomForgetIso]
  rw [nativeIntervalForgetIso_hom]
  exact h

private theorem nativeOuterLeft_forget (q : ℕ) :
    ((forget₂ (ModuleCat.{uC} (MonoidAlgebra ℤ (Multiplicative (Skeleton C))))
      AddCommGrpCat.{uC})).map (SpectralObject.nativeOuterLeftIso (Y)
        (nativeNegativeSupportY (C := C) R) q).hom ≫
      (nativeWindowForgetIso (C := C) R q).hom =
    (nativeBottomForgetIso (C := C) R q).hom ≫
      (SpectralObject.nativeOuterLeftIso ((horizontalCompleteFiltrationSpectralObject
        (SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
        (translationProjection (C := C))))))
        (nativeNegativeSupportE (C := C) R) q).hom := by
  have h := SpectralObject.recoveredEIso_map (Y) ((horizontalCompleteFiltrationSpectralObject
    (SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
    (translationProjection (C := C))))))
    (secondTranslationBKModuleSpectralObject_forget (C := C) R)
    SpectralObject.zeroColumnBottomArrow SpectralObject.zeroColumnMiddleArrow
    SpectralObject.zeroColumnUpperArrow
    SpectralObject.zeroColumnLowerArrow SpectralObject.zeroColumnMiddleArrow
    SpectralObject.zeroColumnUpperArrow
    (fourδ₁Toδ₀' (⊥ : EInt) ((-2 : ℤ) : EInt) ((-1 : ℤ) : EInt)
      ((0 : ℤ) : EInt) ((1 : ℤ) : EInt)
      bot_le SpectralObject.zeroColumnLower_le SpectralObject.zeroColumnMiddle_le
      SpectralObject.zeroColumnUpper_le)
    (-(q : ℤ) - 1) (-(q : ℤ)) (-(q : ℤ) + 1) (by omega) rfl
  simpa only [SpectralObject.nativeOuterLeftIso, nativeBottomForgetIso,
    nativeWindowForgetIso, SpectralObject.isoMapFourδ₁Toδ₀'_hom,
    SpectralObject.mapFourδ₁Toδ₀', SpectralObject.zeroColumnBottomArrow,
    SpectralObject.zeroColumnLowerArrow, SpectralObject.zeroColumnMiddleArrow,
    SpectralObject.zeroColumnUpperArrow] using h

private theorem nativePageForget_presented_at (q : ℕ)
    (i₀ i₁ i₂ i₃ : EInt)
    (h₀ : i₀ = SpectralObject.coreE₁FirstQuadrantHomological.i₀ 2 (0, q) (by omega))
    (h₁ : i₁ = SpectralObject.coreE₁FirstQuadrantHomological.i₁ (0, q))
    (h₂ : i₂ = SpectralObject.coreE₁FirstQuadrantHomological.i₂ (0, q))
    (h₃ : i₃ = SpectralObject.coreE₁FirstQuadrantHomological.i₃ 2 (0, q) (by omega))
    (n₀ n₁ n₂ : ℤ)
    (h : n₁ = SpectralObject.coreE₁FirstQuadrantHomological.deg (0, q))
    (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    let recipe := SpectralObject.coreE₁FirstQuadrantHomological
    let f₁ := homOfLE (recipe.le₀₁' 2 (by omega) (0, q) h₀ h₁)
    let f₂ := homOfLE (recipe.le₁₂' (0, q) h₁ h₂)
    let f₃ := homOfLE (recipe.le₂₃' 2 (by omega) (0, q) h₂ h₃)
    let eY := (Y).spectralSequencePageXIso recipe 2 (by omega) (0, q)
      i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂
    let eE := ((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex
      AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram (translationProjection (C :=
      C)))))).spectralSequencePageXIso recipe 2 (by omega) (0, q)
      i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂
    let recovery := congrArg
      (fun Z : SpectralObject AddCommGrpCat.{uC} EInt =>
        Z.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂)
      (secondTranslationBKModuleSpectralObject_forget (C := C) R)
    (nativePageComponentForgetIso (C := C) R q).hom ≫ eE.hom =
      ((forget₂ (ModuleCat.{uC} (MonoidAlgebra ℤ (Multiplicative (Skeleton C))))
        AddCommGrpCat.{uC})).map eY.hom ≫
        ((Y).forgetMonoidModuleEIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom ≫ eqToHom recovery := by
  have hn₀ : n₀ = n₁ - 1 := by omega
  have hn₂' : n₂ = n₁ + 1 := by omega
  subst i₀ i₁ i₂ i₃ n₀ n₂ n₁
  exact secondTranslationBKModulePageForgetIso_presented (C := C) R
    (2 : ℤ) (by omega) (0, q)

private theorem nativePageForget_presented (q : ℕ) :
    (nativePageComponentForgetIso (C := C) R q).hom ≫
      (SpectralObject.nativePresentation ((horizontalCompleteFiltrationSpectralObject
        (SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
        (translationProjection (C := C)))))) q).hom =
    ((forget₂ (ModuleCat.{uC} (MonoidAlgebra ℤ (Multiplicative (Skeleton C))))
      AddCommGrpCat.{uC})).map (SpectralObject.nativePresentation (Y) q).hom ≫
      (nativeWindowForgetIso (C := C) R q).hom := by
  exact nativePageForget_presented_at (C := C) R q
    ((-2 : ℤ) : EInt) ((-1 : ℤ) : EInt) ((0 : ℤ) : EInt) ((1 : ℤ) : EInt)
    (by simp [SpectralObject.coreE₁FirstQuadrantHomological])
    (by simp [SpectralObject.coreE₁FirstQuadrantHomological])
    (by simp [SpectralObject.coreE₁FirstQuadrantHomological])
    (by simp [SpectralObject.coreE₁FirstQuadrantHomological])
    (-(q : ℤ) - 1) (-(q : ℤ)) (-(q : ℤ) + 1)
    (by simp [SpectralObject.coreE₁FirstQuadrantHomological]) (by omega) rfl

private theorem nativeRepresentative_forget (q : ℕ) :
    ((forget₂ (ModuleCat.{uC} (MonoidAlgebra ℤ (Multiplicative (Skeleton C))))
      AddCommGrpCat.{uC})).map ((Y).nativeZeroColumnStageZeroRepresentative
        (nativeNegativeSupportY (C := C) R) q) ≫
      (nativePageComponentForgetIso (C := C) R q).hom =
    (nativeIntervalForgetIso (C := C) R (-(q : ℤ))
      (mk₁ SpectralObject.zeroColumnBottomToZero)).hom ≫
      ((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R
        (SSet.rightCommaNerveDiagram (translationProjection (C :=
        C)))))).nativeZeroColumnStageZeroRepresentative
        (nativeNegativeSupportE (C := C) R) q := by
  apply (cancel_mono (SpectralObject.nativePresentation ((horizontalCompleteFiltrationSpectralObject
    (SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
    (translationProjection (C := C)))))) q).hom).1
  rw [Category.assoc, nativePageForget_presented, ← Category.assoc,
    ← Functor.map_comp, SpectralObject.nativeRepresentative_presented]
  rw [Functor.map_comp, Category.assoc, nativeOuterLeft_forget,
    ← Category.assoc, nativeProjection_forget]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => (nativeIntervalForgetIso (C := C) R (-(q : ℤ))
        (mk₁ SpectralObject.zeroColumnBottomToZero)).hom ≫ a)
      (SpectralObject.nativeRepresentative_presented ((horizontalCompleteFiltrationSpectralObject
        (SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
        (translationProjection (C := C))))))
        (nativeNegativeSupportE (C := C) R) q).symm).trans
      (Category.assoc _ _ _).symm)

end CategoryTheory.SInverseS

namespace CategoryTheory.SInverseS

section OriginalNativeTarget

variable (C : Type uC) [Category.{uC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] (R : AddCommGrpCat.{uC})

local notation "targetProj" => translationProjection (C := C)
local notation "targetD" => SSet.rightCommaNerveDiagram targetProj
local notation "targetY" => secondTranslationBKModuleSpectralObject (C := C) R
local notation "targetComma" => coreToTranslationFiber (Core.mk (0 : C)) ⋙
  Functor.IsCofibered.fiberToCostructuredArrow (0 : Translation C)
local notation "targetIncl" => StrictOrdinaryWeightedBar.wbarIncl
  (CategoryBar.replUnit (Translation C)) targetD 0 (constantBaseIndex (0 : Translation C) 0)
local notation "targetRowIso" => eqToIso
  (Eq.symm (SSet.bkAlternatingBicomplex_X_eq_chainComplex R targetD 0))
local notation "targetRow" => SSet.chainComplexMap (nerveMap targetComma ≫ targetIncl) R ≫
  Iso.hom targetRowIso

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_core_native_generator (q : ℕ) :
    CategoryHomology.coefficientHomologyClass
        (coreTranslationCoefficientFunctor C R q) (0 : Translation C) ≫
      (secondTranslationBKModuleSecondPageCoefficientIso (C := C) R 0 q).inv =
    original_core_stage_linear C R q ≫
      (targetY).nativeZeroColumnStageZeroRepresentative
        (nativeNegativeSupportY (C := C) R) q := by
  let g := CategoryHomology.coefficientHomologyClass
    (coreTranslationCoefficientFunctor C R q) (0 : Translation C)
  let Γ := secondTranslationBKModuleSecondPageCoefficientIso (C := C) R 0 q
  let a := original_core_stage_linear C R q
  let ρY := (targetY).nativeZeroColumnStageZeroRepresentative
    (nativeNegativeSupportY (C := C) R) q
  let ρE := ((HomologicalComplex₂.horizontalCompleteFiltrationSpectralObject
    (SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
    (translationProjection (C := C)))))).nativeZeroColumnStageZeroRepresentative
    (nativeNegativeSupportE (C := C) R) q
  let e₂ := nativePageComponentForgetIso (C := C) R q
  let η := HomologicalComplex₂.horizontalSecondPageVerticalHorizontalHomologyIso
    ((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
    (translationProjection (C := C))))) 0 q
  let κ := coreTranslationActionSecondPageIso C R 0 q
  let ε := coreTranslationHomologyModuleAddCommGrpIso C R q
  let s₀ := HomologicalComplex₂.zero_complete_inclusion ((SSet.bkAlternatingBicomplex
    AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))
  let b := HomologicalComplex₂.horizontalBottomRelativeHomologyStageIso
    ((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
    (translationProjection (C := C)))))
    ((0 : ℤ) : EInt) q
  let eI := ((HomologicalComplex₂.horizontalCompleteFiltrationSpectralObject
    (SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
    (translationProjection (C := C)))))).monoidModuleIntervalForgetIso
    (secondTranslationBKSpectralAction (C := C) R) (-(q : ℤ))
    (mk₁ (HomologicalComplex₂.horizontalBottomToStageMap ((0 : ℤ) : EInt)))
  let qV := ChainComplex.homologyZeroClass (((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R
    (SSet.rightCommaNerveDiagram (translationProjection (C := C))))).verticalHomologyComplex q)
  have hΓ : ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map Γ.inv =
    κ.hom ≫ e₂.inv :=
    secondTranslationBKModuleSecondPageCoefficientIso_inv_forget (C := C) R 0 q
  have hcore : ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map (g ≫
    Γ.inv) ≫ e₂.hom ≫ η.hom =
      ε.hom ≫ HomologicalComplex.homologyMap (targetRow) q ≫ qV := by
    calc
      _ = ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map g ≫ κ.hom ≫
        e₂.inv ≫ e₂.hom ≫ η.hom := by
        rw [Functor.map_comp, hΓ]
        simp only [Category.assoc]
      _ = ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map g ≫ κ.hom ≫
        η.hom := by
        simpa only [Category.assoc] using
          (((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map g ≫ κ.hom) ≫=
            e₂.inv_hom_id_assoc η.hom
      _ = _ := original_core_class_kappa C R q
  have hbottom : SpectralObject.zeroColumnBottomToZero =
      HomologicalComplex₂.horizontalBottomToStageMap ((0 : ℤ) : EInt) :=
    Subsingleton.elim _ _
  have hrep : ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map ρY ≫
    e₂.hom = eI.hom ≫ ρE := by
    have h := nativeRepresentative_forget (C := C) R q
    change ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map ρY ≫ e₂.hom =
      (((HomologicalComplex₂.horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex
        AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram (translationProjection (C :=
        C)))))).monoidModuleIntervalForgetIso
        (secondTranslationBKSpectralAction (C := C) R) (-(q : ℤ))
        (mk₁ SpectralObject.zeroColumnBottomToZero)).hom ≫ ρE at h
    simpa only [hbottom] using h
  have hb : ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map a ≫ eI.hom =
    ε.hom ≫
      HomologicalComplex.homologyMap (targetRow) q ≫
      HomologicalComplex.homologyMap s₀ q ≫ b.inv :=
    original_core_stage_linear_forget C R q
  have hr : HomologicalComplex.homologyMap s₀ q ≫ b.inv ≫ ρE ≫ η.hom = qV :=
    HomologicalComplex₂.zero_complete_inclusion_native_representative ((SSet.bkAlternatingBicomplex
      AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))
      (nativeNegativeSupportE (C := C) R) q
  have hstage : ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map (a ≫ ρY)
    ≫ e₂.hom ≫ η.hom =
      ε.hom ≫ HomologicalComplex.homologyMap (targetRow) q ≫ qV := by
    calc
      _ = ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map a ≫ (((forget₂
        (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map ρY ≫ e₂.hom) ≫ η.hom := by
        simp only [Functor.map_comp, Category.assoc]
      _ = ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map a ≫ (eI.hom ≫
        ρE) ≫ η.hom := by rw [hrep]
      _ = (((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map a ≫ eI.hom) ≫
        ρE ≫ η.hom :=
        ((Category.assoc (((forget₂ (ModuleCat.{uC} (coreTranslationRing C))
          AddCommGrpCat.{uC})).map a) eI.hom ρE).symm) =≫ η.hom
      _ = ε.hom ≫ HomologicalComplex.homologyMap (targetRow) q ≫
          HomologicalComplex.homologyMap s₀ q ≫ b.inv ≫ ρE ≫ η.hom := by
        rw [hb]
        simp only [Category.assoc]
      _ = _ := by
        simpa only [Category.assoc] using
          (ε.hom ≫ HomologicalComplex.homologyMap (targetRow) q) ≫= hr
  have hmap : ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map (g ≫
    Γ.inv) = ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map (a ≫ ρY)
    := by
    apply (cancel_mono (e₂.hom ≫ η.hom)).1
    exact hcore.trans hstage.symm
  change g ≫ Γ.inv = a ≫ ρY
  exact ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map_injective hmap

end OriginalNativeTarget

section OriginalLocalizedAttachment

variable (C : Type uC) [Category.{uC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] (R : AddCommGrpCat.{uC})

local notation "attachT" => coreTranslationDenominators C
local notation "attachL" => ModuleCat.localizedModuleFunctor attachT
local notation "attachY" => secondTranslationBKModuleSpectralObject (C := C) R
local notation "attachLY" => secondTranslationBKLocalizedModuleSpectralObject (C := C) R
local notation "attachRow" => SSet.chainComplexMap
  (nerveMap (coreToTranslationFiber (Core.mk (0 : C)) ⋙
    Functor.IsCofibered.fiberToCostructuredArrow (0 : Translation C)) ≫
    StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit (Translation C))
      (SSet.rightCommaNerveDiagram (translationProjection (C := C))) 0
      (constantBaseIndex (0 : Translation C) 0)) R ≫
  Iso.hom (eqToIso (Eq.symm (SSet.bkAlternatingBicomplex_X_eq_chainComplex R
    (SSet.rightCommaNerveDiagram (translationProjection (C := C))) 0)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_localized_toCycles
    {i j k : EInt} (f : i ⟶ j) (g : j ⟶ k) (fg : i ⟶ k)
    (hfg : f ≫ g = fg) (n : ℤ) :
    (attachL).map ((attachY).toCycles f g fg hfg n) ≫
      ((attachL).mapSpectralObjectCyclesIso (attachY) f g n).hom =
      (attachLY).toCycles f g fg hfg n := by
  apply (cancel_mono ((attachLY).iCycles f g n)).1
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => (attachL).map ((attachY).toCycles f g fg hfg n) ≫ a)
      ((attachL).mapSpectralObjectCyclesIso_hom_iCycles (attachY) f g n)).trans
      (((attachL).map_comp ((attachY).toCycles f g fg hfg n) ((attachY).iCycles f g n)).symm.trans
        ((congrArg (attachL).map ((attachY).toCycles_i f g fg hfg n)).trans
          ((attachLY).toCycles_i f g fg hfg n).symm)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_localized_cokernel_g
    {i j k l : EInt} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (attachL).map ((attachY).cokernelSequenceE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂).g ≫
      ((attachL).mapSpectralObjectEIso (attachY) f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom =
      ((attachLY).cokernelSequenceE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂).g := by
  dsimp only [SpectralObject.cokernelSequenceE]
  rw [Functor.map_comp, Category.assoc]
  erw [(attachL).mapSpectralObjectEIso_πE (attachY) f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂]
  rw [← Category.assoc]
  erw [original_localized_toCycles C R f₁ f₂ f₁₂ h₁₂ n₁]
  exact Category.assoc _ _ _

private theorem original_localized_negative_support (n a : ℤ) (ha : a < 0) :
    IsZero (((attachLY).H n).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (a : EInt))))) := by
  change IsZero ((attachL).obj (((attachY).H n).obj
    (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (a : EInt))))))
  exact (attachL).map_isZero (nativeNegativeSupportY (C := C) R n a ha)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_localized_representative (q : ℕ) :
    (attachL).map ((attachY).nativeZeroColumnStageZeroRepresentative
        (nativeNegativeSupportY (C := C) R) q) ≫
      ((secondTranslationBKLocalizedModuleSpectralSequenceIso (C := C) R).hom.hom 2
        (by omega)).f (0,q) =
    (attachLY).nativeZeroColumnStageZeroRepresentative
      (original_localized_negative_support C R) q := by
  let pY := SpectralObject.nativePresentation (attachY) q
  let pL := SpectralObject.nativePresentation (attachLY) q
  let lY := SpectralObject.nativeOuterLeftIso (attachY) (nativeNegativeSupportY (C := C) R) q
  let lL := SpectralObject.nativeOuterLeftIso (attachLY) (original_localized_negative_support C R) q
  let gY := SpectralObject.nativeProjection (attachY) q
  let gL := SpectralObject.nativeProjection (attachLY) q
  let ρY := (attachY).nativeZeroColumnStageZeroRepresentative
    (nativeNegativeSupportY (C := C) R) q
  let ρL := (attachLY).nativeZeroColumnStageZeroRepresentative
    (original_localized_negative_support C R) q
  let eB := (attachL).mapSpectralObjectEIso (attachY)
    SpectralObject.zeroColumnBottomArrow SpectralObject.zeroColumnMiddleArrow
    SpectralObject.zeroColumnUpperArrow
    (-(q : ℤ) - 1) (-(q : ℤ)) (-(q : ℤ) + 1) (by omega) rfl
  let eW := (attachL).mapSpectralObjectEIso (attachY)
    SpectralObject.zeroColumnLowerArrow SpectralObject.zeroColumnMiddleArrow
    SpectralObject.zeroColumnUpperArrow
    (-(q : ℤ) - 1) (-(q : ℤ)) (-(q : ℤ) + 1) (by omega) rfl
  let a₂ := ((secondTranslationBKLocalizedModuleSpectralSequenceIso (C := C) R).hom.hom
    2 (by omega)).f (0,q)
  have hp : a₂ ≫ pL.hom = (attachL).map pY.hom ≫ eW.hom := by
    have h := (attachL).mapSpectralObjectSpectralSequencePageIso_presented (attachY)
      SpectralObject.coreE₁FirstQuadrantHomological 2 (by omega) (0,q)
      ((-2 : ℤ) : EInt) ((-1 : ℤ) : EInt) ((0 : ℤ) : EInt) ((1 : ℤ) : EInt)
      (by simp [SpectralObject.coreE₁FirstQuadrantHomological])
      (by simp [SpectralObject.coreE₁FirstQuadrantHomological])
      (by simp [SpectralObject.coreE₁FirstQuadrantHomological])
      (by simp [SpectralObject.coreE₁FirstQuadrantHomological])
      (-(q : ℤ) - 1) (-(q : ℤ)) (-(q : ℤ) + 1)
      (by simp [SpectralObject.coreE₁FirstQuadrantHomological]) (by omega) rfl
    have ha : a₂ = ((attachL).mapSpectralObjectSpectralSequencePageIso (attachY)
        SpectralObject.coreE₁FirstQuadrantHomological 2 (by omega)).hom.f (0,q) :=
      congrArg (fun f => f.f (0,q))
        (secondTranslationBKLocalizedModuleSpectralSequenceIso_hom_hom (C := C) R 2 (by omega))
    change ((attachL).mapSpectralObjectSpectralSequencePageIso (attachY)
        SpectralObject.coreE₁FirstQuadrantHomological 2 (by omega)).hom.f (0,q) ≫ pL.hom =
      (attachL).map pY.hom ≫ eW.hom at h
    exact (congrArg (fun f => f ≫ pL.hom) ha).trans h
  have hl : (attachL).map lY.hom ≫ eW.hom = eB.hom ≫ lL.hom := by
    have h := (attachL).mapSpectralObjectEIso_map (attachY)
      SpectralObject.zeroColumnBottomArrow SpectralObject.zeroColumnMiddleArrow
      SpectralObject.zeroColumnUpperArrow
      SpectralObject.zeroColumnLowerArrow SpectralObject.zeroColumnMiddleArrow
      SpectralObject.zeroColumnUpperArrow
      (fourδ₁Toδ₀' (⊥ : EInt) ((-2 : ℤ) : EInt) ((-1 : ℤ) : EInt)
        ((0 : ℤ) : EInt) ((1 : ℤ) : EInt)
        bot_le SpectralObject.zeroColumnLower_le SpectralObject.zeroColumnMiddle_le
        SpectralObject.zeroColumnUpper_le)
      (-(q : ℤ) - 1) (-(q : ℤ)) (-(q : ℤ) + 1) (by omega) rfl
    dsimp only [lY, lL, SpectralObject.nativeOuterLeftIso]
    simp only [SpectralObject.isoMapFourδ₁Toδ₀'_hom, SpectralObject.mapFourδ₁Toδ₀']
    exact h
  have hg : (attachL).map gY ≫ eB.hom = gL := by
    exact original_localized_cokernel_g C R
      SpectralObject.zeroColumnBottomArrow SpectralObject.zeroColumnMiddleArrow
      SpectralObject.zeroColumnUpperArrow SpectralObject.zeroColumnBottomToZero
      (Subsingleton.elim _ _) (-(q : ℤ) - 1) (-(q : ℤ)) (-(q : ℤ) + 1) (by omega) rfl
  have hY : ρY ≫ pY.hom = gY ≫ lY.hom :=
    SpectralObject.nativeRepresentative_presented (attachY) (nativeNegativeSupportY (C := C) R) q
  have hL : ρL ≫ pL.hom = gL ≫ lL.hom :=
    SpectralObject.nativeRepresentative_presented (attachLY)
      (original_localized_negative_support C R) q
  change (attachL).map ρY ≫ a₂ = ρL
  apply (cancel_mono pL.hom).1
  calc
    _ = (attachL).map ρY ≫ (a₂ ≫ pL.hom) := Category.assoc _ _ _
    _ = (attachL).map ρY ≫ ((attachL).map pY.hom ≫ eW.hom) :=
      (attachL).map ρY ≫= hp
    _ = (attachL).map (ρY ≫ pY.hom) ≫ eW.hom := by
      rw [Functor.map_comp, Category.assoc]
    _ = (attachL).map (gY ≫ lY.hom) ≫ eW.hom :=
      congrArg (fun f => (attachL).map f ≫ eW.hom) hY
    _ = (attachL).map gY ≫ (attachL).map lY.hom ≫ eW.hom := by
      rw [Functor.map_comp, Category.assoc]
    _ = (attachL).map gY ≫ eB.hom ≫ lL.hom :=
      (attachL).map gY ≫= hl
    _ = gL ≫ lL.hom := by
      simpa only [Category.assoc] using hg =≫ lL.hom
    _ = _ := hL.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_localized_edge_stage (q : ℕ) :
    (attachLY).nativeZeroColumnStageZeroRepresentative
        (original_localized_negative_support C R) q ≫
      secondTranslationBKLocalizedModuleZeroColumnEdge (C := C) R q =
    (attachL).map
      ((secondTranslationBKStageModuleIso (C := C) R q ((0 : ℤ) : EInt)).hom ≫
        secondTranslationBKStageToTotalModuleMap (C := C) R q ((0 : ℤ) : EInt)) := by
  have h := secondTranslationBKLocalizedModuleZeroColumnEdge_representation (C := C) R q
  change (attachLY).nativeZeroColumnStageZeroRepresentative
      (original_localized_negative_support C R) q ≫
        secondTranslationBKLocalizedModuleZeroColumnEdge (C := C) R q =
    (secondTranslationBKLocalizedStageModuleIso (C := C) R q ((0 : ℤ) : EInt)).hom ≫
      (attachL).map
        (secondTranslationBKStageToTotalModuleMap (C := C) R q ((0 : ℤ) : EInt)) at h
  rw [secondTranslationBKLocalizedStageModuleIso_hom] at h
  simpa only [Functor.map_comp] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_core_localized_box (q : ℕ) :
    (coreTranslationCoefficientLocalizationIsoApp C R q (0 : Translation C)).hom ≫
      (secondTranslationBKLocalizedModuleSecondPageZeroIso (C := C) R q).inv ≫
        secondTranslationBKLocalizedModuleZeroColumnEdge (C := C) R q =
    (attachL).map
      (original_core_stage_linear C R q ≫
        (secondTranslationBKStageModuleIso (C := C) R q ((0 : ℤ) : EInt)).hom ≫
          secondTranslationBKStageToTotalModuleMap (C := C) R q ((0 : ℤ) : EInt)) := by
  let g := CategoryHomology.coefficientHomologyClass
    (coreTranslationCoefficientFunctor C R q) (0 : Translation C)
  let Γ := secondTranslationBKModuleSecondPageCoefficientIso (C := C) R 0 q
  let ζ := localizedCoreTranslationActionCoefficientRefinementZeroIso C R q
  let Xi := coreTranslationCoefficientLocalizationIsoApp C R q (0 : Translation C)
  let Phi := secondTranslationBKLocalizedModuleSecondPageCoefficientIso (C := C) R 0 q
  let Z := secondTranslationBKLocalizedModuleSecondPageZeroIso (C := C) R q
  let β := secondTranslationBKLocalizedModuleZeroColumnEdge (C := C) R q
  let a := original_core_stage_linear C R q
  let t := (secondTranslationBKStageModuleIso (C := C) R q ((0 : ℤ) : EInt)).hom ≫
    secondTranslationBKStageToTotalModuleMap (C := C) R q ((0 : ℤ) : EInt)
  let a₂ := ((secondTranslationBKLocalizedModuleSpectralSequenceIso (C := C) R).hom.hom
    2 (by omega)).f (0,q)
  let ρY := (attachY).nativeZeroColumnStageZeroRepresentative
    (nativeNegativeSupportY (C := C) R) q
  let ρL := (attachLY).nativeZeroColumnStageZeroRepresentative
    (original_localized_negative_support C R) q
  have hi : (attachL).map g ≫ ζ.hom = Xi.hom :=
    localizedCoreTranslationActionCoefficientRefinementZeroIso_initial_generator C R q
  have hZ : Z.inv = ζ.inv ≫ Phi.inv :=
    secondTranslationBKLocalizedModuleSecondPageZeroIso_inv (C := C) R q
  have hPhi : Phi.inv = (attachL).map Γ.inv ≫ a₂ :=
    secondTranslationBKLocalizedModuleSecondPageCoefficientIso_inv (C := C) R 0 q
  have hTarget : g ≫ Γ.inv = a ≫ ρY := original_core_native_generator C R q
  have hρ : (attachL).map ρY ≫ a₂ = ρL := original_localized_representative C R q
  have he : ρL ≫ β = (attachL).map t := original_localized_edge_stage C R q
  change Xi.hom ≫ Z.inv ≫ β = (attachL).map (a ≫ t)
  calc
    _ = (attachL).map g ≫ ζ.hom ≫ ζ.inv ≫ Phi.inv ≫ β := by
      rw [← hi, hZ]
      simp only [Category.assoc]
    _ = (attachL).map g ≫ Phi.inv ≫ β := by
      exact (attachL).map g ≫= ζ.hom_inv_id_assoc (Phi.inv ≫ β)
    _ = (attachL).map (g ≫ Γ.inv) ≫ a₂ ≫ β := by
      rw [hPhi, Functor.map_comp]
      simp only [Category.assoc]
    _ = (attachL).map (a ≫ ρY) ≫ a₂ ≫ β :=
      congrArg (fun f => (attachL).map f ≫ a₂ ≫ β) hTarget
    _ = (attachL).map a ≫ ((attachL).map ρY ≫ a₂) ≫ β := by
      simp only [Functor.map_comp, Category.assoc]
    _ = (attachL).map a ≫ ρL ≫ β := by
      exact ((attachL).map a ≫= hρ) =≫ β
    _ = (attachL).map a ≫ (attachL).map t := (attachL).map a ≫= he
    _ = _ := ((attachL).map_comp a t).symm

private def original_core_source_unit (q : ℕ) :
    ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).obj
      (coreTranslationHomologyModuleCat C R q) ⟶
      ((forget₂ (ModuleCat.{uC} (Localization (coreTranslationDenominators C)))
        AddCommGrpCat.{uC})).obj (localizedCoreTranslationHomologyModuleCat C R q) :=
  ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map
    ((ModuleCat.localizedModuleFunctorUnit attachT).app
    (coreTranslationHomologyModuleCat C R q)) ≫
      ((forget₂ (ModuleCat.{uC} (Localization (coreTranslationDenominators C)))
        AddCommGrpCat.{uC})).map (coreTranslationCoefficientLocalizationIsoApp C R q (0 :
        Translation C)).hom

private def original_negative_attachment (q : ℕ) :
    ((forget₂ (ModuleCat.{uC} (Localization (coreTranslationDenominators C)))
      AddCommGrpCat.{uC})).obj (localizedCoreTranslationHomologyModuleCat C R q) ⟶
      (nerve (Pair C)).homology R q :=
  ((forget₂ (ModuleCat.{uC} (Localization (coreTranslationDenominators C))) AddCommGrpCat.{uC})).map
    ((secondTranslationBKLocalizedModuleSecondPageZeroIso (C := C) R q).inv ≫
      secondTranslationBKLocalizedModuleZeroColumnEdge (C := C) R q) ≫
    (secondTranslationBKTotalHomologyLocalizationUnderlyingIso C R q).hom ≫
      (translationBKAbutmentHomologyIso C R q).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_core_source_unit_apply (q : ℕ)
    (x : coreTranslationHomologyModuleCat C R q) :
    (original_core_source_unit C R q).hom x =
      LocalizedModule.mk x (1 : coreTranslationDenominators C) := by
  let M := coreTranslationHomologyModuleCat C R q
  let Xi := coreTranslationCoefficientLocalizationIsoApp C R q (0 : Translation C)
  have heval := congrArg (fun f => f x)
    (coreTranslationCoefficientLocalizationLinearEquiv_comp_mk C R q)
  have hunit := ModuleCat.localizedModuleFunctorUnit_app_apply attachT M x
  have hmap := congrArg (fun y => (((forget₂ (ModuleCat.{uC} (Localization
    (coreTranslationDenominators C))) AddCommGrpCat.{uC})).map Xi.hom).hom y) hunit
  have hXi : (((forget₂ (ModuleCat.{uC} (Localization (coreTranslationDenominators C)))
    AddCommGrpCat.{uC})).map Xi.hom).hom (M.localizedModuleMkLinearMap attachT x) =
      LocalizedModule.mk x (1 : coreTranslationDenominators C) := heval
  exact hmap.trans hXi

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_stage_total_negative (q : ℕ) :
    ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map
        (original_core_stage_linear C R q ≫
          (secondTranslationBKStageModuleIso (C := C) R q ((0 : ℤ) : EInt)).hom ≫
            secondTranslationBKStageToTotalModuleMap (C := C) R q ((0 : ℤ) : EInt)) ≫
      (translationBKAbutmentHomologyIso C R q).hom =
    (coreTranslationHomologyModuleAddCommGrpIso C R q).hom ≫
      SSet.homologyMap (nerveMap (negativeCoreInclusion (C := C))) R q := by
  let a := original_core_stage_linear C R q
  let cS := secondTranslationBKStageModuleIso (C := C) R q ((0 : ℤ) : EInt)
  let sT := secondTranslationBKStageToTotalModuleMap (C := C) R q ((0 : ℤ) : EInt)
  let b := HomologicalComplex₂.horizontalBottomRelativeHomologyStageIso
    ((SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
    (translationProjection (C := C)))))
    ((0 : ℤ) : EInt) q
  let eI := ((HomologicalComplex₂.horizontalCompleteFiltrationSpectralObject
    (SSet.bkAlternatingBicomplex AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram
    (translationProjection (C := C)))))).monoidModuleIntervalForgetIso
    (secondTranslationBKSpectralAction (C := C) R) (-(q : ℤ))
    (mk₁ (HomologicalComplex₂.horizontalBottomToStageMap ((0 : ℤ) : EInt)))
  let s₀ := HomologicalComplex₂.zero_complete_inclusion ((SSet.bkAlternatingBicomplex
    AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))
  let ε := coreTranslationHomologyModuleAddCommGrpIso C R q
  let h := translationBKAbutmentHomologyIso C R q
  let u := HomologicalComplex.homologyMap
    (HomologicalComplex₂.horizontalCompleteFilteredTotalToTotal ((SSet.bkAlternatingBicomplex
      AddCommGrpCat.{uC} R (SSet.rightCommaNerveDiagram (translationProjection (C := C))))) ((0 : ℤ)
      : EInt)) q
  have hc : ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map cS.hom =
    eI.hom ≫ b.hom := by
    apply ConcreteCategory.hom_ext
    intro x
    change cS.hom x = b.hom (eI.hom x)
    rw [secondTranslationBKStageModuleIso_hom_apply,
      SpectralObject.monoidModuleIntervalForgetIso_hom_apply]
  have hs : ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map sT = u := by
    apply ConcreteCategory.hom_ext
    intro x
    change sT x = u.hom x
    exact secondTranslationBKStageToTotalModuleMap_apply (C := C) R q ((0 : ℤ) : EInt) x
  have hb : ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map a ≫ eI.hom =
    ε.hom ≫
      HomologicalComplex.homologyMap (attachRow) q ≫
        HomologicalComplex.homologyMap s₀ q ≫ b.inv :=
    original_core_stage_linear_forget C R q
  change ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map (a ≫ cS.hom ≫
    sT) ≫ h.hom = _
  calc
    _ = ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map a ≫ eI.hom ≫
      b.hom ≫ u ≫ h.hom := by
      rw [Functor.map_comp, Functor.map_comp, hc, hs]
      simp only [Category.assoc]
    _ = ε.hom ≫ HomologicalComplex.homologyMap (attachRow) q ≫
        HomologicalComplex.homologyMap s₀ q ≫ b.inv ≫ b.hom ≫ u ≫ h.hom := by
      simpa only [Category.assoc] using hb =≫ (b.hom ≫ u ≫ h.hom)
    _ = ε.hom ≫ HomologicalComplex.homologyMap (attachRow) q ≫
        HomologicalComplex.homologyMap s₀ q ≫ u ≫ h.hom := by
      simpa only [Category.assoc] using
        (ε.hom ≫ HomologicalComplex.homologyMap (attachRow) q ≫
          HomologicalComplex.homologyMap s₀ q) ≫= b.inv_hom_id_assoc (u ≫ h.hom)
    _ = _ := by
      simpa only [HomologicalComplex.homologyMap_comp, Category.assoc] using
        original_row_stage_homology_module C R q

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_core_unit_negative_map (q : ℕ) :
    original_core_source_unit C R q ≫ original_negative_attachment C R q =
    (coreTranslationHomologyModuleAddCommGrpIso C R q).hom ≫
      SSet.homologyMap (nerveMap (negativeCoreInclusion (C := C))) R q := by
  let V := coreTranslationHomologyModuleCat C R q
  let N := secondTranslationBKTotalHomologyModule (C := C) R q
  let f : V ⟶ N := original_core_stage_linear C R q ≫
    (secondTranslationBKStageModuleIso (C := C) R q ((0 : ℤ) : EInt)).hom ≫
      secondTranslationBKStageToTotalModuleMap (C := C) R q ((0 : ℤ) : EInt)
  let ηV := (ModuleCat.localizedModuleFunctorUnit attachT).app V
  let ηN := (ModuleCat.localizedModuleFunctorUnit attachT).app N
  let Xi := coreTranslationCoefficientLocalizationIsoApp C R q (0 : Translation C)
  let τ := (secondTranslationBKLocalizedModuleSecondPageZeroIso (C := C) R q).inv ≫
    secondTranslationBKLocalizedModuleZeroColumnEdge (C := C) R q
  let lambdaIso := secondTranslationBKTotalHomologyLocalizationUnderlyingIso C R q
  let h := translationBKAbutmentHomologyIso C R q
  have hbox : Xi.hom ≫ τ = (attachL).map f := original_core_localized_box C R q
  have hunit : ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map ηV ≫
    ((forget₂ (ModuleCat.{uC} (Localization (coreTranslationDenominators C)))
    AddCommGrpCat.{uC})).map ((attachL).map f) =
      ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map f ≫ ((forget₂
        (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map ηN := by
    have hn := ModuleCat.localizedModuleFunctorUnit_naturality attachT f
    have hu := congrArg ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map
      hn
    simpa only [Functor.map_comp, ModuleCat.forget₂_map_restrictScalars] using hu.symm
  have hLambda : ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map ηN ≫
    lambdaIso.hom = 𝟙 _ :=
    secondTranslationBKTotalHomologyLocalizationUnderlyingIso_unit_hom C R q
  change (((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map ηV ≫ ((forget₂
    (ModuleCat.{uC} (Localization (coreTranslationDenominators C))) AddCommGrpCat.{uC})).map Xi.hom)
    ≫
    (((forget₂ (ModuleCat.{uC} (Localization (coreTranslationDenominators C)))
      AddCommGrpCat.{uC})).map τ ≫ lambdaIso.hom ≫ h.hom) = _
  calc
    _ = ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map ηV ≫ ((forget₂
      (ModuleCat.{uC} (Localization (coreTranslationDenominators C))) AddCommGrpCat.{uC})).map
      (Xi.hom ≫ τ) ≫ lambdaIso.hom ≫ h.hom := by
      simp only [Functor.map_comp, Category.assoc]
    _ = ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map ηV ≫ ((forget₂
      (ModuleCat.{uC} (Localization (coreTranslationDenominators C))) AddCommGrpCat.{uC})).map
      ((attachL).map f) ≫ lambdaIso.hom ≫ h.hom := by
      rw [hbox]
    _ = ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map f ≫ ((forget₂
      (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map ηN ≫ lambdaIso.hom ≫ h.hom
      := by
      simpa only [Category.assoc] using hunit =≫ (lambdaIso.hom ≫ h.hom)
    _ = ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map f ≫ h.hom := by
      calc
        _ = ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map f ≫
          ((((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map ηN ≫
          lambdaIso.hom) ≫ h.hom) :=
          ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map f ≫=
            (Category.assoc (((forget₂ (ModuleCat.{uC} (coreTranslationRing C))
              AddCommGrpCat.{uC})).map ηN) lambdaIso.hom h.hom).symm
        _ = ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map f ≫ (𝟙 _ ≫
          h.hom) :=
          ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map f ≫= (hLambda
            =≫ h.hom)
        _ = _ := ((forget₂ (ModuleCat.{uC} (coreTranslationRing C)) AddCommGrpCat.{uC})).map f ≫=
          Category.id_comp h.hom
    _ = _ := original_stage_total_negative C R q

open scoped BigOperators

private def original_denominator_monomial (d : coreTranslationDenominators C) :
    Multiplicative (Skeleton C) :=
  Classical.choose (MonoidHom.mem_mrange.mp d.property)

private theorem original_denominator_monomial_spec (d : coreTranslationDenominators C) :
    MonoidAlgebra.of ℤ (Multiplicative (Skeleton C))
        (original_denominator_monomial C d) = (d : coreTranslationRing C) :=
  Classical.choose_spec (MonoidHom.mem_mrange.mp d.property)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_total_localization_map_smul (q : ℕ) (r : coreTranslationRing C)
    (y : (attachL).obj (secondTranslationBKTotalHomologyModule (C := C) R q)) :
    (secondTranslationBKTotalHomologyLocalizationUnderlyingIso C R q).hom
        ((algebraMap (coreTranslationRing C) (Localization attachT) r) • y) =
      @SMul.smul (coreTranslationRing C)
        (secondTranslationBKTotalHomologyModule (C := C) R q) inferInstance r
          ((secondTranslationBKTotalHomologyLocalizationUnderlyingIso C R q).hom y) := by
  let N := secondTranslationBKTotalHomologyModule (C := C) R q
  let eLocal := ModuleCat.localizedModuleLinearEquivOfBijectiveSmul attachT N
    (secondTranslationBKTotalHomologyModule_denominator_bijective C R q)
  let yLocal : N.localizedModule attachT := y
  have hLocal : eLocal ((algebraMap (coreTranslationRing C) (Localization attachT) r) • yLocal) =
      r • eLocal yLocal := by
    rw [IsScalarTower.algebraMap_smul]
    exact eLocal.map_smul r yLocal
  exact hLocal

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_total_monomial_translation (q : ℕ)
    (m : Multiplicative (Skeleton C)) (k : ℤ)
    (x : secondTranslationBKTotalHomologyModule (C := C) R q) :
    (translationBKAbutmentHomologyIso C R q).hom (MonoidAlgebra.single m k • x) =
      k • pairSecondTranslationHomologyMap C R q m.toAdd.out
        ((translationBKAbutmentHomologyIso C R q).hom x) := by
  let W := m.toAdd.out
  have hm : Multiplicative.ofAdd (toSkeleton W) = m :=
    congrArg Multiplicative.ofAdd (toSkeleton_fromSkeleton_obj m.toAdd)
  have hmono : MonoidAlgebra.single m k • x =
      k • HomologicalComplex.homologyMap (secondTranslationBKTotalComplexMap R W) q x := by
    rw [← hm]
    exact secondTranslationBKTotalHomologyModule_single_apply (C := C) R q W k x
  have hs := congrArg (fun f => f x) (secondTranslationBKAbutmentHomologySquare C R W q)
  change (translationBKAbutmentHomologyIso C R q).hom
      (HomologicalComplex.homologyMap (secondTranslationBKTotalComplexMap R W) q x) =
    pairSecondTranslationHomologyMap C R q W
      ((translationBKAbutmentHomologyIso C R q).hom x) at hs
  rw [hmono, map_zsmul, hs]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_negative_attachment_smul (q : ℕ) (r : coreTranslationRing C)
    (z : localizedCoreTranslationHomologyModuleCat C R q) :
    (original_negative_attachment C R q)
        ((algebraMap (coreTranslationRing C) (Localization attachT) r) • z) =
      (translationBKAbutmentHomologyIso C R q).hom
        (@SMul.smul (coreTranslationRing C)
          (secondTranslationBKTotalHomologyModule (C := C) R q) inferInstance r
          ((secondTranslationBKTotalHomologyLocalizationUnderlyingIso C R q).hom
          (((secondTranslationBKLocalizedModuleSecondPageZeroIso (C := C) R q).inv ≫
            secondTranslationBKLocalizedModuleZeroColumnEdge (C := C) R q) z))) := by
  let τ := (secondTranslationBKLocalizedModuleSecondPageZeroIso (C := C) R q).inv ≫
    secondTranslationBKLocalizedModuleZeroColumnEdge (C := C) R q
  change (translationBKAbutmentHomologyIso C R q).hom
      ((secondTranslationBKTotalHomologyLocalizationUnderlyingIso C R q).hom
        (τ.hom ((algebraMap (coreTranslationRing C) (Localization attachT) r) • z))) = _
  rw [τ.hom.map_smul, original_total_localization_map_smul C R q r]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_negative_single_translation (q : ℕ)
    (m : Multiplicative (Skeleton C)) (k : ℤ)
    (z : localizedCoreTranslationHomologyModuleCat C R q) :
    (original_negative_attachment C R q)
        ((algebraMap (coreTranslationRing C) (Localization attachT)
          (MonoidAlgebra.single m k)) • z) =
      k • pairSecondTranslationHomologyMap C R q m.toAdd.out
        ((original_negative_attachment C R q) z) := by
  let τ := (secondTranslationBKLocalizedModuleSecondPageZeroIso (C := C) R q).inv ≫
    secondTranslationBKLocalizedModuleZeroColumnEdge (C := C) R q
  let x : secondTranslationBKTotalHomologyModule (C := C) R q :=
    (secondTranslationBKTotalHomologyLocalizationUnderlyingIso C R q).hom (τ z)
  have hs := original_negative_attachment_smul C R q (MonoidAlgebra.single m k) z
  have hx := original_total_monomial_translation C R q m k x
  exact hs.trans hx

private theorem original_raw_fraction_cancel (q : ℕ) (d : coreTranslationDenominators C)
    (x : coreTranslationHomologyModuleCat C R q) :
    (algebraMap (coreTranslationRing C) (Localization attachT) (d : coreTranslationRing C)) •
        LocalizedModule.mk x d = LocalizedModule.mk x (1 : coreTranslationDenominators C) := by
  rw [IsScalarTower.algebraMap_smul, LocalizedModule.smul'_mk]
  simpa only [Submonoid.smul_def] using LocalizedModule.mk_cancel d x

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_negative_integral_translation (q : ℕ) (r : coreTranslationRing C)
    (z : localizedCoreTranslationHomologyModuleCat C R q) :
    (original_negative_attachment C R q)
        ((algebraMap (coreTranslationRing C) (Localization attachT) r) • z) =
      ∑ m ∈ r.coeff.support, (r.coeff m) •
        pairSecondTranslationHomologyMap C R q m.toAdd.out
          ((original_negative_attachment C R q) z) := by
  classical
  have hsum : r = r.coeff.sum MonoidAlgebra.single :=
    (MonoidAlgebra.sum_coeff_single r).symm
  have hlin : (algebraMap (coreTranslationRing C) (Localization attachT) r) • z =
      ∑ m ∈ r.coeff.support,
        (algebraMap (coreTranslationRing C) (Localization attachT)
          (MonoidAlgebra.single m (r.coeff m))) • z := by
    calc
      _ = (algebraMap (coreTranslationRing C) (Localization attachT)
          (r.coeff.sum MonoidAlgebra.single)) • z :=
        congrArg (fun a => (algebraMap (coreTranslationRing C) (Localization attachT) a) • z) hsum
      _ = _ := by simp only [Finsupp.sum, map_sum, Finset.sum_smul]
  rw [hlin, map_sum]
  apply Finset.sum_congr rfl
  intro m _
  exact original_negative_single_translation C R q m (r.coeff m) z

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_negative_denominator_translation (q : ℕ)
    (d : coreTranslationDenominators C)
    (z : localizedCoreTranslationHomologyModuleCat C R q) :
    (original_negative_attachment C R q)
        ((algebraMap (coreTranslationRing C) (Localization attachT)
          (d : coreTranslationRing C)) • z) =
      pairSecondTranslationHomologyMap C R q (original_denominator_monomial C d).toAdd.out
        ((original_negative_attachment C R q) z) := by
  have hr : MonoidAlgebra.single (original_denominator_monomial C d) (1 : ℤ) =
      (d : coreTranslationRing C) := by
    simpa only [MonoidAlgebra.of_apply] using original_denominator_monomial_spec C d
  simpa only [hr, one_zsmul] using
    original_negative_single_translation C R q (original_denominator_monomial C d) 1 z

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_negative_unit_apply (q : ℕ)
    (x : coreTranslationHomologyModuleCat C R q) :
    (original_negative_attachment C R q)
        (LocalizedModule.mk x (1 : coreTranslationDenominators C)) =
      SSet.homologyMap (nerveMap (negativeCoreInclusion (C := C))) R q
        ((coreTranslationHomologyModuleAddCommGrpIso C R q).hom x) := by
  have h := congrArg (fun f => f x) (original_core_unit_negative_map C R q)
  change (original_negative_attachment C R q)
      ((original_core_source_unit C R q).hom x) =
    SSet.homologyMap (nerveMap (negativeCoreInclusion (C := C))) R q
      ((coreTranslationHomologyModuleAddCommGrpIso C R q).hom x) at h
  rw [original_core_source_unit_apply C R q x] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_negative_fraction_apply (q : ℕ)
    (d : coreTranslationDenominators C) (x : coreTranslationHomologyModuleCat C R q) :
    (original_negative_attachment C R q) (LocalizedModule.mk x d) =
      (pairTranslationHomologyIsoOfObject C R q
        (original_denominator_monomial C d).toAdd.out).hom
        (SSet.homologyMap (nerveMap (negativeCoreInclusion (C := C))) R q
          ((coreTranslationHomologyModuleAddCommGrpIso C R q).hom x)) := by
  let J := pairTranslationHomologyIsoOfObject C R q
    (original_denominator_monomial C d).toAdd.out
  have ht := original_negative_denominator_translation C R q d (LocalizedModule.mk x d)
  rw [original_raw_fraction_cancel C R q d x, original_negative_unit_apply C R q x] at ht
  have hInv : J.inv ((original_negative_attachment C R q) (LocalizedModule.mk x d)) =
      SSet.homologyMap (nerveMap (negativeCoreInclusion (C := C))) R q
        ((coreTranslationHomologyModuleAddCommGrpIso C R q).hom x) := ht.symm
  have hi := congrArg
    (fun f => f ((original_negative_attachment C R q) (LocalizedModule.mk x d))) J.inv_hom_id
  change J.hom (J.inv ((original_negative_attachment C R q) (LocalizedModule.mk x d))) =
    (original_negative_attachment C R q) (LocalizedModule.mk x d) at hi
  calc
    _ = J.hom (J.inv ((original_negative_attachment C R q) (LocalizedModule.mk x d))) := hi.symm
    _ = _ := congrArg (fun z => J.hom z) hInv

private def original_positive_attachment (q : ℕ) :
    ((forget₂ (ModuleCat.{uC} (Localization (coreTranslationDenominators C)))
      AddCommGrpCat.{uC})).obj (localizedCoreTranslationHomologyModuleCat C R q) ⟶
      (nerve (Pair C)).homology R q :=
  original_negative_attachment C R q ≫ (swapHomologyIso (C := C) R q).hom

private theorem original_swap_inverse_conjugacy (q : ℕ) (W : C) :
    (pairTranslationHomologyIsoOfObject C R q W).hom ≫
        (swapHomologyIso (C := C) R q).hom =
      (swapHomologyIso (C := C) R q).hom ≫
        (pairTranslationHomologyIsoOfObject C R q W).inv := by
  let J := pairTranslationHomologyIsoOfObject C R q W
  let σ := swapHomologyIso (C := C) R q
  have h := swapHomologyIso_intertwines (C := C) R q W
  change J.inv ≫ σ.hom = σ.hom ≫ J.hom at h
  have hi := congrArg (fun f => J.hom ≫ f ≫ J.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
    using hi.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_positive_fraction_apply (q : ℕ)
    (d : coreTranslationDenominators C) (x : coreTranslationHomologyModuleCat C R q) :
    (original_positive_attachment C R q) (LocalizedModule.mk x d) =
      (pairTranslationHomologyIsoOfObject C R q
        (original_denominator_monomial C d).toAdd.out).inv
        (SSet.homologyMap (nerveMap (coreInclusion (C := C))) R q
          ((coreTranslationHomologyModuleAddCommGrpIso C R q).hom x)) := by
  let J := pairTranslationHomologyIsoOfObject C R q
    (original_denominator_monomial C d).toAdd.out
  let σ := swapHomologyIso (C := C) R q
  let jMinus := SSet.homologyMap (nerveMap (negativeCoreInclusion (C := C))) R q
  let jPlus := SSet.homologyMap (nerveMap (coreInclusion (C := C))) R q
  let ε := coreTranslationHomologyModuleAddCommGrpIso C R q
  have hs := congrArg (fun f => f (jMinus (ε.hom x)))
    (original_swap_inverse_conjugacy C R q (original_denominator_monomial C d).toAdd.out)
  change σ.hom (J.hom (jMinus (ε.hom x))) = J.inv (σ.hom (jMinus (ε.hom x))) at hs
  have hc := congrArg (fun f => f (ε.hom x)) (negativeCoreHomology_comp_swap (C := C) R q)
  change σ.hom (jMinus (ε.hom x)) = jPlus (ε.hom x) at hc
  change σ.hom ((original_negative_attachment C R q) (LocalizedModule.mk x d)) =
    J.inv (jPlus (ε.hom x))
  rw [original_negative_fraction_apply C R q d x]
  exact hs.trans (congrArg (fun z => J.inv z) hc)

private theorem original_denominator_monomial_of_skeleton (s : Skeleton C) :
    original_denominator_monomial C (coreTranslationDenominator C s) =
      Multiplicative.ofAdd s := by
  apply MonoidAlgebra.of_injective (R := ℤ) (M := Multiplicative (Skeleton C))
  exact original_denominator_monomial_spec C (coreTranslationDenominator C s)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_negative_skeleton_fraction_apply (q : ℕ) (s : Skeleton C)
    (x : coreTranslationHomologyModuleCat C R q) :
    (original_negative_attachment C R q)
        (LocalizedModule.mk x (coreTranslationDenominator C s)) =
      (pairTranslationHomologyIso C R q s).hom
        (SSet.homologyMap (nerveMap (negativeCoreInclusion (C := C))) R q
          ((coreTranslationHomologyModuleAddCommGrpIso C R q).hom x)) := by
  change _ = (pairTranslationHomologyIsoOfObject C R q s.out).hom _
  simpa only [original_denominator_monomial_of_skeleton, toAdd_ofAdd] using
    original_negative_fraction_apply C R q (coreTranslationDenominator C s) x

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_positive_skeleton_fraction_apply (q : ℕ) (s : Skeleton C)
    (x : coreTranslationHomologyModuleCat C R q) :
    (original_positive_attachment C R q)
        (LocalizedModule.mk x (coreTranslationDenominator C s)) =
      (pairTranslationHomologyIso C R q s).inv
        (SSet.homologyMap (nerveMap (coreInclusion (C := C))) R q
          ((coreTranslationHomologyModuleAddCommGrpIso C R q).hom x)) := by
  change _ = (pairTranslationHomologyIsoOfObject C R q s.out).inv _
  simpa only [original_denominator_monomial_of_skeleton, toAdd_ofAdd] using
    original_positive_fraction_apply C R q (coreTranslationDenominator C s) x

private theorem original_negative_attachment_isIso (q : ℕ) :
    IsIso (original_negative_attachment C R q) := by
  let Z := secondTranslationBKLocalizedModuleSecondPageZeroIso (C := C) R q
  let β := secondTranslationBKLocalizedModuleZeroColumnEdge (C := C) R q
  let τ := Z.inv ≫ β
  have hB : IsIso β := secondTranslationBKLocalizedModuleZeroColumnEdge_isIso (C := C) R q
  let : IsIso τ := IsIso.comp_isIso' Z.isIso_inv hB
  have ht : IsIso (((forget₂ (ModuleCat.{uC} (Localization (coreTranslationDenominators C)))
    AddCommGrpCat.{uC})).map τ) := by infer_instance
  change IsIso (((forget₂ (ModuleCat.{uC} (Localization (coreTranslationDenominators C)))
    AddCommGrpCat.{uC})).map τ ≫
    (secondTranslationBKTotalHomologyLocalizationUnderlyingIso C R q).hom ≫
      (translationBKAbutmentHomologyIso C R q).hom)
  exact IsIso.comp_isIso' ht (IsIso.comp_isIso'
    (secondTranslationBKTotalHomologyLocalizationUnderlyingIso C R q).isIso_hom
    (translationBKAbutmentHomologyIso C R q).isIso_hom)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem original_core_fraction_swap_characteristic (q : ℕ) :
    let thetaMinus : ((forget₂ (ModuleCat.{uC} (Localization (coreTranslationDenominators C)))
      AddCommGrpCat.{uC})).obj (localizedCoreTranslationHomologyModuleCat C R q) ⟶
        (nerve (Pair C)).homology R q :=
      ((forget₂ (ModuleCat.{uC} (Localization (coreTranslationDenominators C)))
        AddCommGrpCat.{uC})).map
        ((secondTranslationBKLocalizedModuleSecondPageZeroIso (C := C) R q).inv ≫
          secondTranslationBKLocalizedModuleZeroColumnEdge (C := C) R q) ≫
        (secondTranslationBKTotalHomologyLocalizationUnderlyingIso C R q).hom ≫
          (translationBKAbutmentHomologyIso C R q).hom
    let thetaPlus := thetaMinus ≫ (swapHomologyIso (C := C) R q).hom
    IsIso thetaMinus ∧
      (∀ x : coreTranslationHomologyModule C R q,
        thetaMinus (LocalizedModule.mk x (1 : coreTranslationDenominators C)) =
          SSet.homologyMap (nerveMap (negativeCoreInclusion (C := C))) R q
            ((coreTranslationHomologyModuleAddCommGrpIso C R q).hom x)) ∧
      (∀ (d : coreTranslationDenominators C) (x : coreTranslationHomologyModule C R q),
        let m := Classical.choose (MonoidHom.mem_mrange.mp d.property)
        let J := pairTranslationHomologyIsoOfObject C R q m.toAdd.out
        thetaMinus (LocalizedModule.mk x d) =
            J.hom (SSet.homologyMap (nerveMap (negativeCoreInclusion (C := C))) R q
              ((coreTranslationHomologyModuleAddCommGrpIso C R q).hom x)) ∧
          thetaPlus (LocalizedModule.mk x d) =
            J.inv (SSet.homologyMap (nerveMap (coreInclusion (C := C))) R q
              ((coreTranslationHomologyModuleAddCommGrpIso C R q).hom x))) := by
  refine ⟨original_negative_attachment_isIso C R q, ?_, ?_⟩
  · intro x
    exact original_negative_unit_apply C R q x
  · intro d x
    exact ⟨original_negative_fraction_apply C R q d x,
      original_positive_fraction_apply C R q d x⟩

end OriginalLocalizedAttachment

public section

variable {C : Type uC} [Category.{uC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- The canonical original localized zero-column comparison from whole-core
homology to the homology of additive `S⁻¹S`. -/
def secondTranslationBKLocalizedCoreHomologyIso (R : AddCommGrpCat.{uC}) (q : ℕ) :
    (forget₂ (ModuleCat.{uC} (Localization (coreTranslationDenominators C))) AddCommGrpCat.{uC}).obj
        (localizedCoreTranslationHomologyModuleCat C R q) ≅
      (nerve (Pair C)).homology R q := by
  let U := forget₂ (ModuleCat.{uC} (Localization (coreTranslationDenominators C)))
    AddCommGrpCat.{uC}
  let Z := secondTranslationBKLocalizedModuleSecondPageZeroIso (C := C) R q
  let β := secondTranslationBKLocalizedModuleZeroColumnEdge (C := C) R q
  let : IsIso β := secondTranslationBKLocalizedModuleZeroColumnEdge_isIso (C := C) R q
  exact U.mapIso Z.symm ≪≫ U.mapIso (asIso β) ≪≫
    secondTranslationBKTotalHomologyLocalizationUnderlyingIso C R q ≪≫
      translationBKAbutmentHomologyIso C R q

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical negative comparison retains the original edge map and sends
every whole-core fraction to first translation of its negative core class. -/
theorem secondTranslationBKLocalizedCoreHomologyIso_characteristic
    (R : AddCommGrpCat.{uC}) (q : ℕ) :
    let U := forget₂ (ModuleCat.{uC} (Localization (coreTranslationDenominators C)))
      AddCommGrpCat.{uC}
    let Z := secondTranslationBKLocalizedModuleSecondPageZeroIso (C := C) R q
    let β := secondTranslationBKLocalizedModuleZeroColumnEdge (C := C) R q
    let lambdaIso := secondTranslationBKTotalHomologyLocalizationUnderlyingIso C R q
    let h := translationBKAbutmentHomologyIso C R q
    let E := secondTranslationBKLocalizedCoreHomologyIso (C := C) R q
    let ε := coreTranslationHomologyModuleAddCommGrpIso C R q
    let jMinus := SSet.homologyMap (nerveMap (negativeCoreInclusion (C := C))) R q
    E.hom = U.map (Z.inv ≫ β) ≫ lambdaIso.hom ≫ h.hom ∧
      (∀ x : coreTranslationHomologyModule C R q,
        E.hom (LocalizedModule.mk x (1 : coreTranslationDenominators C)) = jMinus (ε.hom x)) ∧
      (∀ (d : coreTranslationDenominators C) (x : coreTranslationHomologyModule C R q),
        let m := Classical.choose (MonoidHom.mem_mrange.mp d.property)
        let J := pairTranslationHomologyIsoOfObject C R q m.toAdd.out
        E.hom (LocalizedModule.mk x d) = J.hom (jMinus (ε.hom x))) ∧
      (∀ (s : Skeleton C) (x : coreTranslationHomologyModule C R q),
        E.hom (LocalizedModule.mk x (coreTranslationDenominator C s)) =
          (pairTranslationHomologyIso C R q s).hom (jMinus (ε.hom x))) := by
  dsimp only
  have hE : (secondTranslationBKLocalizedCoreHomologyIso (C := C) R q).hom =
      original_negative_attachment C R q := by
    simp only [secondTranslationBKLocalizedCoreHomologyIso, Functor.mapIso_hom,
      Iso.trans_hom, Iso.symm_hom, asIso_hom, original_negative_attachment,
      Functor.map_comp, Category.assoc]
  refine ⟨hE, ?_, ?_, ?_⟩
  · intro x
    exact (congrArg
      (fun f => f (LocalizedModule.mk x (1 : coreTranslationDenominators C))) hE).trans
      (original_negative_unit_apply C R q x)
  · intro d x
    exact (congrArg (fun f => f (LocalizedModule.mk x d)) hE).trans
      (original_negative_fraction_apply C R q d x)
  · intro s x
    exact (congrArg (fun f => f (LocalizedModule.mk x (coreTranslationDenominator C s))) hE).trans
      (original_negative_skeleton_fraction_apply C R q s x)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Original coordinate swap carries the canonical negative comparison to the
positive core map, with second translation as the inverse fraction operator. -/
theorem secondTranslationBKLocalizedCoreHomologyIso_swap_characteristic
    (R : AddCommGrpCat.{uC}) (q : ℕ) :
    let E := secondTranslationBKLocalizedCoreHomologyIso (C := C) R q
    let σ := swapHomologyIso (C := C) R q
    let Eplus := E ≪≫ σ
    let ε := coreTranslationHomologyModuleAddCommGrpIso C R q
    let jPlus := SSet.homologyMap (nerveMap (coreInclusion (C := C))) R q
    Eplus.hom = E.hom ≫ σ.hom ∧
      (∀ x : coreTranslationHomologyModule C R q,
        Eplus.hom (LocalizedModule.mk x (1 : coreTranslationDenominators C)) = jPlus (ε.hom x)) ∧
      (∀ (d : coreTranslationDenominators C) (x : coreTranslationHomologyModule C R q),
        let m := Classical.choose (MonoidHom.mem_mrange.mp d.property)
        let J := pairTranslationHomologyIsoOfObject C R q m.toAdd.out
        Eplus.hom (LocalizedModule.mk x d) = J.inv (jPlus (ε.hom x))) ∧
      (∀ (s : Skeleton C) (x : coreTranslationHomologyModule C R q),
        Eplus.hom (LocalizedModule.mk x (coreTranslationDenominator C s)) =
          (pairTranslationHomologyIso C R q s).inv (jPlus (ε.hom x))) := by
  dsimp only
  let E := secondTranslationBKLocalizedCoreHomologyIso (C := C) R q
  let σ := swapHomologyIso (C := C) R q
  have hMinus : E.hom = original_negative_attachment C R q :=
    (secondTranslationBKLocalizedCoreHomologyIso_characteristic (C := C) R q).1
  have hPlus : (E ≪≫ σ).hom = original_positive_attachment C R q := hMinus =≫ σ.hom
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro x
    let ε := coreTranslationHomologyModuleAddCommGrpIso C R q
    let jMinus := SSet.homologyMap (nerveMap (negativeCoreInclusion (C := C))) R q
    let jPlus := SSet.homologyMap (nerveMap (coreInclusion (C := C))) R q
    have hc := congrArg (fun f => f (ε.hom x)) (negativeCoreHomology_comp_swap (C := C) R q)
    change σ.hom (jMinus (ε.hom x)) = jPlus (ε.hom x) at hc
    have hu := original_negative_unit_apply C R q x
    calc
      _ = (original_positive_attachment C R q)
          (LocalizedModule.mk x (1 : coreTranslationDenominators C)) :=
        congrArg
          (fun f => f (LocalizedModule.mk x (1 : coreTranslationDenominators C))) hPlus
      _ = σ.hom (jMinus (ε.hom x)) := congrArg (fun z => σ.hom z) hu
      _ = _ := hc
  · intro d x
    exact (congrArg (fun f => f (LocalizedModule.mk x d)) hPlus).trans
      (original_positive_fraction_apply C R q d x)
  · intro s x
    exact (congrArg
      (fun f => f (LocalizedModule.mk x (coreTranslationDenominator C s))) hPlus).trans
      (original_positive_skeleton_fraction_apply C R q s x)

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original localized edge comparison preserves the full integral
monoid-algebra action through the actual second translations. -/
theorem secondTranslationBKLocalizedCoreHomologyIso_integral_equivariance
    (R : AddCommGrpCat.{uC}) (q : ℕ) (r : coreTranslationRing C)
    (z : localizedCoreTranslationHomologyModuleCat C R q) :
    (secondTranslationBKLocalizedCoreHomologyIso (C := C) R q).hom
        ((algebraMap (coreTranslationRing C)
          (Localization (coreTranslationDenominators C)) r) • z) =
      ∑ m ∈ r.coeff.support, (r.coeff m) •
        pairSecondTranslationHomologyMap C R q m.toAdd.out
          ((secondTranslationBKLocalizedCoreHomologyIso (C := C) R q).hom z) := by
  have hE : (secondTranslationBKLocalizedCoreHomologyIso (C := C) R q).hom =
      original_negative_attachment C R q :=
    (secondTranslationBKLocalizedCoreHomologyIso_characteristic (C := C) R q).1
  simpa only [hE] using original_negative_integral_translation C R q r z

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Coordinate swap turns the canonical comparison into the positive core map
and preserves every integral monoid-algebra scalar by actual first translation. -/
theorem secondTranslationBKLocalizedCoreHomologyIso_swap_integral_equivariance
    (R : AddCommGrpCat.{uC}) (q : ℕ) (r : coreTranslationRing C)
    (z : localizedCoreTranslationHomologyModuleCat C R q) :
    (secondTranslationBKLocalizedCoreHomologyIso (C := C) R q ≪≫
        swapHomologyIso (C := C) R q).hom
        ((algebraMap (coreTranslationRing C)
          (Localization (coreTranslationDenominators C)) r) • z) =
      ∑ m ∈ r.coeff.support, (r.coeff m) •
        SSet.homologyMap (nerveMap (translateFirstFunctor m.toAdd.out)) R q
          ((secondTranslationBKLocalizedCoreHomologyIso (C := C) R q ≪≫
            swapHomologyIso (C := C) R q).hom z) := by
  change (swapHomologyIso (C := C) R q).hom
      ((secondTranslationBKLocalizedCoreHomologyIso (C := C) R q).hom
        ((algebraMap (coreTranslationRing C)
          (Localization (coreTranslationDenominators C)) r) • z)) = _
  rw [secondTranslationBKLocalizedCoreHomologyIso_integral_equivariance]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro m _
  apply congrArg (fun x => (r.coeff m) • x)
  exact ConcreteCategory.congr_hom
    (swapHomologyIso_intertwines (C := C) R q m.toAdd.out)
    ((secondTranslationBKLocalizedCoreHomologyIso (C := C) R q).hom z)

/-- Categorical group completion identifies whole localized core homology with
pair homology in every degree. The canonical positive core comparison retains
all integral scalars, the core unit and every original denominator fraction. -/
theorem groupCompletionHomology (R : AddCommGrpCat.{uC}) (q : ℕ) :
    let E := secondTranslationBKLocalizedCoreHomologyIso (C := C) R q ≪≫
      swapHomologyIso (C := C) R q
    let ε := coreTranslationHomologyModuleAddCommGrpIso C R q
    let j := SSet.homologyMap (nerveMap (coreInclusion (C := C))) R q
    IsIso E.hom ∧
      (∀ (r : coreTranslationRing C) (z : localizedCoreTranslationHomologyModuleCat C R q),
        E.hom ((algebraMap (coreTranslationRing C)
            (Localization (coreTranslationDenominators C)) r) • z) =
          ∑ m ∈ r.coeff.support, (r.coeff m) •
            SSet.homologyMap (nerveMap (translateFirstFunctor m.toAdd.out)) R q (E.hom z)) ∧
      (∀ x : coreTranslationHomologyModule C R q,
        E.hom (LocalizedModule.mk x (1 : coreTranslationDenominators C)) = j (ε.hom x)) ∧
      (∀ (d : coreTranslationDenominators C) (x : coreTranslationHomologyModule C R q),
        let m := Classical.choose (MonoidHom.mem_mrange.mp d.property)
        let J := pairTranslationHomologyIsoOfObject C R q m.toAdd.out
        E.hom (LocalizedModule.mk x d) = J.inv (j (ε.hom x))) ∧
      (∀ (s : Skeleton C) (x : coreTranslationHomologyModule C R q),
        E.hom (LocalizedModule.mk x (coreTranslationDenominator C s)) =
          (pairTranslationHomologyIso C R q s).inv (j (ε.hom x))) := by
  dsimp only
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · exact secondTranslationBKLocalizedCoreHomologyIso_swap_integral_equivariance R q
  · exact (secondTranslationBKLocalizedCoreHomologyIso_swap_characteristic
      (C := C) R q).2.1
  · exact (secondTranslationBKLocalizedCoreHomologyIso_swap_characteristic
      (C := C) R q).2.2.1
  · exact (secondTranslationBKLocalizedCoreHomologyIso_swap_characteristic
      (C := C) R q).2.2.2

end

end CategoryTheory.SInverseS


end
