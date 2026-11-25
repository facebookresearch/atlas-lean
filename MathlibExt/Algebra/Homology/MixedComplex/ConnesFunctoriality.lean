/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.MixedComplex.ConnesTail
public import MathlibExt.Algebra.Homology.MixedComplex.Comparison
public import MathlibExt.Algebra.Homology.Embedding.ExtendHomologyFunctor

/-!
# Functoriality of the Connes construction and SBI maps

A morphism of mixed complexes induces maps of their Connes bicomplexes,
totals and first columns. These maps commute with the tail and periodicity
comparisons and induce compatible morphisms of SBI diagrams. The resulting
comparison is natural in the mixed-complex morphism.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂

universe u v

namespace MixedComplex

section CharacterizedModels

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {M N P : MixedComplex C}

omit [Preadditive C] in
private theorem indexMap_naturality {X Y : ℕ → C}
    (φ : ∀ n, X n ⟶ Y n) {i j : ℕ} (h : i = j) :
    eqToHom (congrArg X h) ≫ φ j = φ i ≫ eqToHom (congrArg Y h) := by
  subst j
  simp

namespace ConnesDoubleData

/-- The supported-cell formula of a characterized vertical differential. -/
theorem vertical_eq (D : ConnesDoubleData M) (p q : ℕ) (h : p ≤ q) :
    (D.K.X p).d (q + 1) q =
      (D.objIso p (q + 1) (by omega)).hom ≫
        eqToHom (congrArg (mixedObject M) (by omega : q + 1 - p = q - p + 1)) ≫
        (((-1 : ℤ) ^ p) • mixedDifferential M (q - p)) ≫ (D.objIso p q h).inv := by
  apply (cancel_mono (D.objIso p q h).hom).1
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using
    (D.vertical_spec p q h (by omega)).symm

/-- The supported-cell formula of a characterized horizontal differential. -/
theorem horizontal_eq (D : ConnesDoubleData M) (p q : ℕ) (h : p + 1 ≤ q) :
    (D.K.d (p + 1) p).f q =
      (D.objIso (p + 1) q h).hom ≫ M.B (q - (p + 1)) ≫
        eqToHom (congrArg (mixedObject M) (by omega : q - (p + 1) + 1 = q - p)) ≫
        (D.objIso p q (by omega)).inv := by
  apply (cancel_mono (D.objIso p q (by omega)).hom).1
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using
    (D.horizontal_spec p q h (by omega)).symm

/-- A mixed map in the original coordinates of two characterized models. -/
def mapComponent (D : ConnesDoubleData M) (E : ConnesDoubleData N)
    (f : M ⟶ N) (p q : ℕ) : (D.K.X p).X q ⟶ (E.K.X p).X q :=
  if h : p ≤ q then
    (D.objIso p q h).hom ≫ f.underlying.f (q - p) ≫ (E.objIso p q h).inv
  else 0

/-- Each supported component is the corresponding underlying degree map. -/
theorem mapComponent_spec (D : ConnesDoubleData M) (E : ConnesDoubleData N)
    (f : M ⟶ N) (p q : ℕ) (h : p ≤ q) :
    (D.objIso p q h).hom ≫ f.underlying.f (q - p) =
      mapComponent D E f p q ≫ (E.objIso p q h).hom := by
  simp only [mapComponent, dite_eq_left h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The component map commutes with the signed original vertical differential. -/
theorem mapComponent_vertical (D : ConnesDoubleData M) (E : ConnesDoubleData N)
    (f : M ⟶ N) (p q : ℕ) :
    mapComponent D E f p (q + 1) ≫ (E.K.X p).d (q + 1) q =
      (D.K.X p).d (q + 1) q ≫ mapComponent D E f p q := by
  by_cases h : p ≤ q
  · have hu : p ≤ q + 1 := by omega
    let iM := eqToHom (congrArg (mixedObject M) (by omega : q + 1 - p = q - p + 1))
    let iN := eqToHom (congrArg (mixedObject N) (by omega : q + 1 - p = q - p + 1))
    have hi : iM ≫ f.underlying.f (q - p + 1) =
        f.underlying.f (q + 1 - p) ≫ iN :=
      indexMap_naturality f.underlying.f (by omega : q + 1 - p = q - p + 1)
    have hc : f.underlying.f (q - p + 1) ≫
          (((-1 : ℤ) ^ p) • mixedDifferential N (q - p)) =
        (((-1 : ℤ) ^ p) • mixedDifferential M (q - p)) ≫ f.underlying.f (q - p) := by
      simp only [mixedDifferential, Preadditive.comp_zsmul, Preadditive.zsmul_comp]
      exact congrArg (fun a => ((-1 : ℤ) ^ p) • a)
        (f.underlying.comm (q - p + 1) (q - p))
    have hm : f.underlying.f (q + 1 - p) ≫ iN ≫
          (((-1 : ℤ) ^ p) • mixedDifferential N (q - p)) =
        iM ≫ (((-1 : ℤ) ^ p) • mixedDifferential M (q - p)) ≫
          f.underlying.f (q - p) := by
      calc
        _ = (iM ≫ f.underlying.f (q - p + 1)) ≫
            (((-1 : ℤ) ^ p) • mixedDifferential N (q - p)) := by
          rw [← Category.assoc, ← hi]
        _ = iM ≫ (f.underlying.f (q - p + 1) ≫
            (((-1 : ℤ) ^ p) • mixedDifferential N (q - p))) := Category.assoc _ _ _
        _ = _ := by rw [hc]
    rw [vertical_eq E p q h, vertical_eq D p q h]
    simp only [mapComponent, dite_eq_left h, dite_eq_left hu, Category.assoc, Iso.inv_hom_id_assoc]
    simpa only [Category.assoc] using congrArg (fun a =>
      (D.objIso p (q + 1) hu).hom ≫ a ≫ (E.objIso p q h).inv) hm
  · exact (E.isZero p q (by omega)).eq_of_tgt _ _

/-- The component map commutes with the original mixed-operator horizontal differential. -/
theorem mapComponent_horizontal (D : ConnesDoubleData M) (E : ConnesDoubleData N)
    (f : M ⟶ N) (p q : ℕ) :
    mapComponent D E f (p + 1) q ≫ (E.K.d (p + 1) p).f q =
      (D.K.d (p + 1) p).f q ≫ mapComponent D E f p q := by
  by_cases h : p + 1 ≤ q
  · have hl : p ≤ q := by omega
    let iM := eqToHom (congrArg (mixedObject M) (by omega : q - (p + 1) + 1 = q - p))
    let iN := eqToHom (congrArg (mixedObject N) (by omega : q - (p + 1) + 1 = q - p))
    have hi : iM ≫ f.underlying.f (q - p) =
        f.underlying.f (q - (p + 1) + 1) ≫ iN :=
      indexMap_naturality f.underlying.f (by omega : q - (p + 1) + 1 = q - p)
    have hm : f.underlying.f (q - (p + 1)) ≫ N.B (q - (p + 1)) ≫ iN =
        M.B (q - (p + 1)) ≫ iM ≫ f.underlying.f (q - p) := by
      rw [← Category.assoc, f.comm_B]
      simp only [Category.assoc]
      rw [← hi]
    rw [horizontal_eq E p q h, horizontal_eq D p q h]
    simp only [mapComponent, dite_eq_left h, dite_eq_left hl, Category.assoc, Iso.inv_hom_id_assoc]
    simpa only [Category.assoc] using congrArg (fun a =>
      (D.objIso (p + 1) q h).hom ≫ a ≫ (E.objIso p q hl).inv) hm
  · exact (D.isZero (p + 1) q (by omega)).eq_of_src _ _

/-- The bicomplex morphism between two component-characterized Connes models. -/
def map (D : ConnesDoubleData M) (E : ConnesDoubleData N) (f : M ⟶ N) : D.K ⟶ E.K :=
  HomologicalComplex₂.homMk (fun x => mapComponent D E f x.1 x.2)
    (by
      intro p p' q hp
      change p' + 1 = p at hp
      subst p
      exact mapComponent_horizontal D E f p' q)
    (by
      intro p q q' hq
      change q' + 1 = q at hq
      subst q
      exact mapComponent_vertical D E f p q')

/-- The constructed model morphism has its exact original cell component. -/
@[simp]
theorem map_f_f (D : ConnesDoubleData M) (E : ConnesDoubleData N)
    (f : M ⟶ N) (p q : ℕ) : ((map D E f).f p).f q = mapComponent D E f p q := rfl

/-- The supported original-cell naturality of the constructed model morphism. -/
theorem map_spec (D : ConnesDoubleData M) (E : ConnesDoubleData N)
    (f : M ⟶ N) (p q : ℕ) (h : p ≤ q) :
    (D.objIso p q h).hom ≫ f.underlying.f (q - p) =
      ((map D E f).f p).f q ≫ (E.objIso p q h).hom :=
  mapComponent_spec D E f p q h


/-- Identity acts as the identity on every characterized cell. -/
theorem map_id (D : ConnesDoubleData M) : map D D (𝟙 M) = 𝟙 D.K := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply HomologicalComplex.Hom.ext
  funext q
  by_cases h : p ≤ q
  · simp only [map_f_f, mapComponent, dite_eq_left h, MixedComplex.id_underlying,
      HomologicalComplex.id_f, Category.id_comp, Iso.hom_inv_id]
  · exact (D.isZero p q (by omega)).eq_of_src _ _

/-- Composition follows the original underlying mixed maps, in every characterized model. -/
theorem map_comp (D : ConnesDoubleData M) (E : ConnesDoubleData N)
    (F : ConnesDoubleData P) (f : M ⟶ N) (g : N ⟶ P) :
    map D E f ≫ map E F g = map D F (f ≫ g) := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply HomologicalComplex.Hom.ext
  funext q
  by_cases h : p ≤ q
  · simp only [HomologicalComplex.comp_f, map_f_f, mapComponent, dite_eq_left h,
      MixedComplex.comp_underlying, Category.assoc, Iso.inv_hom_id_assoc]
  · exact (D.isZero p q (by omega)).eq_of_src _ _

/-- A characterized morphism is unique once its original supported-cell formula is fixed. -/
theorem map_eq_of_spec (D : ConnesDoubleData M) (E : ConnesDoubleData N)
    (f : M ⟶ N) (g : D.K ⟶ E.K)
    (hg : ∀ p q (h : p ≤ q),
      (D.objIso p q h).hom ≫ f.underlying.f (q - p) =
        ((g.f p).f q) ≫ (E.objIso p q h).hom) : g = map D E f := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply HomologicalComplex.Hom.ext
  funext q
  by_cases h : p ≤ q
  · apply (cancel_mono (E.objIso p q h).hom).1
    exact (hg p q h).symm.trans (map_spec D E f p q h)
  · exact (D.isZero p q (by omega)).eq_of_src _ _

end ConnesDoubleData

end CharacterizedModels

section CharacterizedPresentations

variable {C : Type u} [Category.{v} C] [Abelian C]
  {M N P : MixedComplex C}

namespace GenericMixedCyclicData

/-- The induced morphism of the native column/total/cokernel short complexes. -/
def automaticShortMap (D : GenericMixedCyclicData M) (E : GenericMixedCyclicData N)
    (f : M ⟶ N) : genericMixedConnesShortComplex D.model ⟶
      genericMixedConnesShortComplex E.model :=
  partialTotalCokernelShortComplexMap (D.model.map E.model f) 0

/-- The original column comparisons are natural in the component-derived model map. -/
theorem automatic_columnMap_naturality
    (D : GenericMixedCyclicData M) (E : GenericMixedCyclicData N) (f : M ⟶ N) :
    f.underlying ≫ E.columnMap = D.columnMap ≫ (automaticShortMap D E f).τ₁ := by
  apply HomologicalComplex.Hom.ext
  funext q
  let aD : (D.model.K.X 0).X q ≅ M.underlying.X q :=
    D.model.objIso 0 q (Nat.zero_le q)
  let aE : (E.model.K.X 0).X q ≅ N.underlying.X q :=
    E.model.objIso 0 q (Nat.zero_le q)
  let iD := D.model.K.partialTotalComponent 0 (0 : Fin 1) q q (Nat.zero_add q)
  let iE := E.model.K.partialTotalComponent 0 (0 : Fin 1) q q (Nat.zero_add q)
  let g := D.model.K.partialTotalHom (D.model.map E.model f) 0
  have hD : D.columnMap.f q = aD.inv ≫ iD := D.columnMap_spec q
  have hE : E.columnMap.f q = aE.inv ≫ iE := E.columnMap_spec q
  have hi : iD ≫ g.f q = ((D.model.map E.model f).f 0).f q ≫ iE :=
    D.model.K.partialTotalComponent_naturality (D.model.map E.model f)
      0 (0 : Fin 1) q q (Nat.zero_add q)
  have hc : ((D.model.map E.model f).f 0).f q =
      aD.hom ≫ f.underlying.f q ≫ aE.inv := by
    simp only [ConnesDoubleData.map_f_f, ConnesDoubleData.mapComponent,
      dite_eq_left (Nat.zero_le q), Nat.sub_zero, aD, aE]
  have h : D.columnMap.f q ≫ g.f q = f.underlying.f q ≫ E.columnMap.f q := by
    calc
      _ = aD.inv ≫ (iD ≫ g.f q) :=
        (congrArg (fun a => a ≫ g.f q) hD).trans (Category.assoc _ _ _)
      _ = aD.inv ≫ (((D.model.map E.model f).f 0).f q ≫ iE) :=
        congrArg (fun a => aD.inv ≫ a) hi
      _ = aD.inv ≫ ((aD.hom ≫ f.underlying.f q ≫ aE.inv) ≫ iE) :=
        congrArg (fun a => aD.inv ≫ (a ≫ iE)) hc
      _ = f.underlying.f q ≫ (aE.inv ≫ iE) := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = _ := congrArg (fun a => f.underlying.f q ≫ a) hE.symm
  exact h.symm

private theorem automatic_tailSource_naturality
    (D : GenericMixedCyclicData M) (E : GenericMixedCyclicData N) (f : M ⟶ N)
    (p q : ℕ) :
    genericMixedTailSourceComponent D.model p q ≫
        (extendMap (partialTotalCokernelMap (D.model.map E.model f) 0)
          (ComplexShape.embeddingDownNatToIntShift 0)).f
            (2 + ((p + q : ℕ) : ℤ)) =
      ((D.model.map E.model f).f (p + 1)).f (q + 1) ≫
        genericMixedTailSourceComponent E.model p q := by
  simpa only [genericMixedTailSourceComponent] using
    D.model.K.partialTotalCokernelGenerator_naturality (D.model.map E.model f)
      0 0 (p + 1) (q + 1) (p + q + 2) (by omega)
      (2 + ((p + q : ℕ) : ℤ)) (by
        rw [ComplexShape.embeddingDownNatToIntShift_f]
        push_cast
        omega)

private theorem automatic_tailCell_naturality
    (D : GenericMixedCyclicData M) (E : GenericMixedCyclicData N) (f : M ⟶ N)
    (p q : ℕ) (h : p ≤ q) :
    (genericMixedTailCellIso D.model p q h).hom ≫ ((D.model.map E.model f).f p).f q =
      ((D.model.map E.model f).f (p + 1)).f (q + 1) ≫
        (genericMixedTailCellIso E.model p q h).hom := by
  have hd : q + 1 - (p + 1) = q - p := by omega
  have hspec₀ := D.model.map_spec E.model f p q h
  have hspec₁ := D.model.map_spec E.model f (p + 1) (q + 1) (by omega)
  have ht := indexMap_naturality (φ := f.underlying.f) hd
  have hu : (D.model.objIso (p + 1) (q + 1) (by omega)).hom ≫
      eqToHom (congrArg (mixedObject M) hd) ≫ f.underlying.f (q - p) =
    ((D.model.map E.model f).f (p + 1)).f (q + 1) ≫
      (E.model.objIso (p + 1) (q + 1) (by omega)).hom ≫
        eqToHom (congrArg (mixedObject N) hd) := by
    calc
      _ = (D.model.objIso (p + 1) (q + 1) (by omega)).hom ≫
          (f.underlying.f (q + 1 - (p + 1)) ≫
            eqToHom (congrArg (mixedObject N) hd)) := by
        rw [ht]
      _ = ((D.model.objIso (p + 1) (q + 1) (by omega)).hom ≫
          f.underlying.f (q + 1 - (p + 1))) ≫
            eqToHom (congrArg (mixedObject N) hd) := (Category.assoc _ _ _).symm
      _ = _ := by rw [hspec₁, Category.assoc]
  apply (cancel_mono (E.model.objIso p q h).hom).1
  simp only [genericMixedTailCellIso, Iso.trans_hom, Iso.symm_hom,
    eqToIso.hom, Category.assoc]
  rw [← hspec₀]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  simpa only [Category.assoc, Category.comp_id] using hu

private theorem automatic_tailTarget_naturality
    (D : GenericMixedCyclicData M) (E : GenericMixedCyclicData N) (f : M ⟶ N)
    (p q : ℕ) (h : p ≤ q) :
    genericMixedTailTargetComponent D.model p q h ≫
        (extendMap (total.map (D.model.map E.model f) (ComplexShape.down ℕ))
          (ComplexShape.embeddingDownNatToIntShift 2)).f
            (2 + ((p + q : ℕ) : ℤ)) =
      ((D.model.map E.model f).f (p + 1)).f (q + 1) ≫
        genericMixedTailTargetComponent E.model p q h := by
  have hi := HomologicalComplex₂.ιTotal_map (K := D.model.K) (L := E.model.K)
    (φ := D.model.map E.model f) (c₁₂ := ComplexShape.down ℕ) p q (p + q) rfl
  have he := HomologicalComplex.extendDownNatToIntShiftXIso_inv_naturality
    (total.map (D.model.map E.model f) (ComplexShape.down ℕ)) 2 (p + q)
  have hc := automatic_tailCell_naturality D E f p q h
  simp only [genericMixedTailTargetComponent_eq, Category.assoc]
  rw [he]
  conv_lhs =>
    rhs
    rw [← Category.assoc, hi, Category.assoc]
  rw [← Category.assoc, hc, Category.assoc]

/-- The specified integer tail maps are natural; their square is derived from native generators. -/
theorem automatic_tailMap_naturality
    (D : GenericMixedCyclicData M) (E : GenericMixedCyclicData N) (f : M ⟶ N) :
    extendMap (automaticShortMap D E f).τ₃ (ComplexShape.embeddingDownNatToIntShift 0) ≫
        E.tailMap =
      D.tailMap ≫ extendMap (automaticShortMap D E f).τ₂
        (ComplexShape.embeddingDownNatToIntShift 2) := by
  let α := extendMap (automaticShortMap D E f).τ₃
    (ComplexShape.embeddingDownNatToIntShift 0) ≫ E.tailMap
  let β := D.tailMap ≫ extendMap (automaticShortMap D E f).τ₂
    (ComplexShape.embeddingDownNatToIntShift 2)
  change α = β
  apply D.model.K.partialTotalCokernel_extend_hom_ext_of_tail 0 0
  intro i j n hn hi
  cases i with
  | zero => omega
  | succ p =>
      cases j with
      | zero => exact (D.model.isZero (p + 1) 0 (by omega)).eq_of_src _ _
      | succ q =>
          by_cases hpq : p ≤ q
          · have hn' : (p + 1) + (q + 1) = p + q + 2 := by omega
            have hnn : n = p + q + 2 := by omega
            have hz : (ComplexShape.embeddingDownNatToIntShift 0).f n =
                0 + (n : ℤ) := by
              rw [ComplexShape.embeddingDownNatToIntShift_f]
            have hz' : (ComplexShape.embeddingDownNatToIntShift 0).f (p + q + 2) =
                2 + ((p + q : ℕ) : ℤ) := by
              rw [ComplexShape.embeddingDownNatToIntShift_f]
              push_cast
              omega
            have hzz : (0 : ℤ) + (n : ℤ) = 2 + ((p + q : ℕ) : ℤ) := by
              rw [hnn]
              push_cast
              omega
            have hsource := automatic_tailSource_naturality D E f p q
            have htarget := automatic_tailTarget_naturality D E f p q hpq
            have hD := D.tailMap_spec p q hpq
            have hE := E.tailMap_spec p q hpq
            have hc : genericMixedTailSourceComponent D.model p q ≫
                  α.f (2 + ((p + q : ℕ) : ℤ)) =
                genericMixedTailSourceComponent D.model p q ≫
                  β.f (2 + ((p + q : ℕ) : ℤ)) := by
              change genericMixedTailSourceComponent D.model p q ≫
                  (extendMap (partialTotalCokernelMap (D.model.map E.model f) 0)
                    (ComplexShape.embeddingDownNatToIntShift 0) ≫ E.tailMap).f
                      (2 + ((p + q : ℕ) : ℤ)) =
                genericMixedTailSourceComponent D.model p q ≫
                  (D.tailMap ≫ extendMap
                    (total.map (D.model.map E.model f) (ComplexShape.down ℕ))
                    (ComplexShape.embeddingDownNatToIntShift 2)).f
                      (2 + ((p + q : ℕ) : ℤ))
              simp only [HomologicalComplex.comp_f]
              calc
                _ = ((D.model.map E.model f).f (p + 1)).f (q + 1) ≫
                    (genericMixedTailSourceComponent E.model p q ≫ E.tailMap.f
                      (2 + ((p + q : ℕ) : ℤ))) := by
                  rw [← Category.assoc, hsource, Category.assoc]
                _ = ((D.model.map E.model f).f (p + 1)).f (q + 1) ≫
                    genericMixedTailTargetComponent E.model p q hpq := by rw [hE]
                _ = _ := by rw [← htarget, ← hD, Category.assoc]
            unfold genericMixedTailSourceComponent at hc
            convert hc using 1
            · rw [hzz]
            · exact D.model.K.partialTotalCokernelGenerator_comp_heq 0 0
                (p + 1) (q + 1) hn hn' hz hz' hnn hzz α
            · exact D.model.K.partialTotalCokernelGenerator_comp_heq 0 0
                (p + 1) (q + 1) hn hn' hz hz' hnn hzz β
          · exact (D.model.isZero (p + 1) (q + 1) (by omega)).eq_of_src _ _

/-- A plain mixed morphism constructs comparison maps for arbitrary genuinely characterized models. -/
def automaticMap (D : GenericMixedCyclicData M) (E : GenericMixedCyclicData N)
    (f : M ⟶ N) : GenericMixedCyclicMap D E f where
  shortMap := automaticShortMap D E f
  columnMap_naturality := automatic_columnMap_naturality D E f
  tailMap_naturality := automatic_tailMap_naturality D E f

/-- Constructed arbitrary-model maps preserve identities. -/
theorem automaticMap_id (D : GenericMixedCyclicData M) :
    automaticMap D D (𝟙 M) = GenericMixedCyclicMap.id D := by
  apply GenericMixedCyclicMap.ext
  change partialTotalCokernelShortComplexMap (D.model.map D.model (𝟙 M)) 0 = 𝟙 _
  rw [ConnesDoubleData.map_id, partialTotalCokernelShortComplexMap_id]

/-- Constructed arbitrary-model maps preserve composition. -/
theorem automaticMap_comp
    (D : GenericMixedCyclicData M) (E : GenericMixedCyclicData N) (F : GenericMixedCyclicData P)
    (f : M ⟶ N) (g : N ⟶ P) :
    automaticMap D F (f ≫ g) = GenericMixedCyclicMap.comp (automaticMap D E f) (automaticMap E F g) := by
  apply GenericMixedCyclicMap.ext
  change partialTotalCokernelShortComplexMap (D.model.map F.model (f ≫ g)) 0 =
    partialTotalCokernelShortComplexMap (D.model.map E.model f) 0 ≫
      partialTotalCokernelShortComplexMap (E.model.map F.model g) 0
  rw [← ConnesDoubleData.map_comp, partialTotalCokernelShortComplexMap_comp]

end GenericMixedCyclicData

end CharacterizedPresentations

section Coordinates

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  {M N : MixedComplex C}

/-- The bicomplex map has the original mixed-degree component. -/
theorem connesBicomplexMap_coordinates (f : M ⟶ N)
    (p n q : ℕ) (hn : n + p = q) :
    ((M.connesBicomplexMap f).f p).f q =
      (ChainComplex.mixedColumnIso M.underlying p n q hn).hom ≫
        f.underlying.f n ≫ (ChainComplex.mixedColumnIso N.underlying p n q hn).inv := by
  have h := congrArg (fun g : M.connesBicomplex.X p ⟶ N.connesBicomplex.X p => g.f q)
    (connesBicomplexMap_f M f p)
  exact h.trans (ChainComplex.mixedColumnMap_f_eq f.underlying p n q hn)

variable [M.connesBicomplex.HasTotal (ComplexShape.down ℕ)]
  [N.connesBicomplex.HasTotal (ComplexShape.down ℕ)]

/-- Totalization keeps each original mixed summand and its coefficient map. -/
theorem connesSummandι_naturality (f : M ⟶ N)
    (p n q j : ℕ) (hn : n + p = q) (hj : p + q = j) :
    M.connesSummandι p n q j hn hj ≫
        (total.map (M.connesBicomplexMap f) (ComplexShape.down ℕ)).f j =
      f.underlying.f n ≫ N.connesSummandι p n q j hn hj := by
  let eM : (M.connesBicomplex.X p).X q ≅ M.underlying.X n :=
    ChainComplex.mixedColumnIso M.underlying p n q hn
  let eN : (N.connesBicomplex.X p).X q ≅ N.underlying.X n :=
    ChainComplex.mixedColumnIso N.underlying p n q hn
  let iM := M.connesBicomplex.ιTotal (ComplexShape.down ℕ) p q j hj
  let iN := N.connesBicomplex.ιTotal (ComplexShape.down ℕ) p q j hj
  let t := total.map (M.connesBicomplexMap f) (ComplexShape.down ℕ)
  have hcell : ((M.connesBicomplexMap f).f p).f q =
      eM.hom ≫ f.underlying.f n ≫ eN.inv := connesBicomplexMap_coordinates f p n q hn
  have ht : iM ≫ t.f j = ((M.connesBicomplexMap f).f p).f q ≫ iN :=
    HomologicalComplex₂.ιTotal_map (K := M.connesBicomplex) (L := N.connesBicomplex)
      (φ := M.connesBicomplexMap f) (c₁₂ := ComplexShape.down ℕ) p q j hj
  have hm : M.connesSummandι p n q j hn hj = eM.inv ≫ iM := rfl
  have hN : N.connesSummandι p n q j hn hj = eN.inv ≫ iN := rfl
  calc
    _ = eM.inv ≫ (iM ≫ t.f j) :=
      (congrArg (fun a => a ≫ t.f j) hm).trans (Category.assoc _ _ _)
    _ = eM.inv ≫ (((M.connesBicomplexMap f).f p).f q ≫ iN) := congrArg (fun a => eM.inv ≫ a) ht
    _ = eM.inv ≫ ((eM.hom ≫ f.underlying.f n ≫ eN.inv) ≫ iN) :=
      congrArg (fun a => eM.inv ≫ (a ≫ iN)) hcell
    _ = f.underlying.f n ≫ (eN.inv ≫ iN) := by simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = _ := congrArg (fun a => f.underlying.f n ≫ a) hN.symm

/-- Periodicity is natural in the total map, in every native degree. -/
theorem connesPeriodicityF_naturality (f : M ⟶ N) (j : ℕ) :
    (total.map (M.connesBicomplexMap f) (ComplexShape.down ℕ)).f j ≫ N.connesPeriodicityF j =
      M.connesPeriodicityF j ≫
        (extendMap (total.map (M.connesBicomplexMap f) (ComplexShape.down ℕ))
          (ComplexShape.embeddingDown'Add (1 : ℕ) 2)).f j := by
  let t : M.connesTotal ⟶ N.connesTotal :=
    total.map (M.connesBicomplexMap f) (ComplexShape.down ℕ)
  let e : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    ComplexShape.embeddingDown'Add (1 : ℕ) 2
  let pM : M.connesTotal.X j ⟶ (M.connesTotal.extend e).X j := M.connesPeriodicityF j
  let pN : N.connesTotal.X j ⟶ (N.connesTotal.extend e).X j := N.connesPeriodicityF j
  let s : (M.connesTotal.extend e).X j ⟶ (N.connesTotal.extend e).X j := (extendMap t e).f j
  have hmain : t.f j ≫ pN = pM ≫ s := by
    apply HomologicalComplex₂.total.hom_ext (K := M.connesBicomplex) (c₁₂ := ComplexShape.down ℕ)
    intro p q hj
    have hsum : p + q = j := hj
    by_cases hpq : p ≤ q
    · let n := q - p
      have hn : n + p = q := Nat.sub_add_cancel hpq
      let a : (M.connesBicomplex.X p).X q ≅ M.underlying.X n :=
        ChainComplex.mixedColumnIso M.underlying p n q hn
      let i := M.connesBicomplex.ιTotal (ComplexShape.down ℕ) p q j hj
      let m : M.underlying.X n ⟶ M.connesTotal.X j := M.connesSummandι p n q j hn hj
      let mN : N.underlying.X n ⟶ N.connesTotal.X j := N.connesSummandι p n q j hn hj
      have hs : a.inv ≫ i = m := rfl
      have ht : m ≫ t.f j = f.underlying.f n ≫ mN :=
        connesSummandι_naturality f p n q j hn hj
      apply (cancel_epi a.inv).1
      have hleft : a.inv ≫ (i ≫ (t.f j ≫ pN)) = m ≫ (t.f j ≫ pN) :=
        (Category.assoc a.inv i (t.f j ≫ pN)).symm.trans
          (congrArg (fun b => b ≫ (t.f j ≫ pN)) hs)
      have hright : a.inv ≫ (i ≫ (pM ≫ s)) = m ≫ (pM ≫ s) :=
        (Category.assoc a.inv i (pM ≫ s)).symm.trans
          (congrArg (fun b => b ≫ (pM ≫ s)) hs)
      have hmiddle : m ≫ (t.f j ≫ pN) = m ≫ (pM ≫ s) := by
        cases p with
        | zero =>
          have hM : m ≫ pM = 0 := M.connesSummandι_periodicityF_zero n q j hn hj
          have hN : mN ≫ pN = 0 := N.connesSummandι_periodicityF_zero n q j hn hj
          have hL : m ≫ (t.f j ≫ pN) = 0 :=
            (Category.assoc m (t.f j) pN).symm.trans
              ((congrArg (fun b => b ≫ pN) ht).trans
                ((Category.assoc (f.underlying.f n) mN pN).trans
                  ((congrArg (fun b => f.underlying.f n ≫ b) hN).trans comp_zero)))
          have hR : m ≫ (pM ≫ s) = 0 :=
            (Category.assoc m pM s).symm.trans
              ((congrArg (fun b => b ≫ s) hM).trans zero_comp)
          exact hL.trans hR.symm
        | succ p =>
          let k := j - 2
          have hk : k + 2 = j := by dsimp only [k]; omega
          have hn' : n + p = q - 1 := by omega
          have hj' : p + (q - 1) = k := by dsimp only [k]; omega
          let bM : (M.connesTotal.extend e).X j ≅ M.connesTotal.X k :=
            M.connesTotal.extendXIso e hk
          let bN : (N.connesTotal.extend e).X j ≅ N.connesTotal.X k :=
            N.connesTotal.extendXIso e hk
          let lowerM : M.underlying.X n ⟶ M.connesTotal.X k :=
            M.connesSummandι p n (q - 1) k hn' hj'
          let lowerN : N.underlying.X n ⟶ N.connesTotal.X k :=
            N.connesSummandι p n (q - 1) k hn' hj'
          have hext : s ≫ bN.hom = bM.hom ≫ t.f k := by
            have h : s = bM.hom ≫ t.f k ≫ bN.inv := extendMap_f t e hk
            exact (congrArg (fun a => a ≫ bN.hom) h).trans
              ((Category.assoc bM.hom (t.f k ≫ bN.inv) bN.hom).trans
                ((congrArg (fun a => bM.hom ≫ a)
                  (Category.assoc (t.f k) bN.inv bN.hom)).trans
                  ((congrArg (fun a => bM.hom ≫ (t.f k ≫ a)) bN.inv_hom_id).trans
                    (congrArg (fun a => bM.hom ≫ a) (Category.comp_id (t.f k))))))
          have hM : m ≫ pM ≫ bM.hom = lowerM :=
            M.connesSummandι_periodicityF p n q j k hn hj hk
          have hN : mN ≫ pN ≫ bN.hom = lowerN :=
            N.connesSummandι_periodicityF p n q j k hn hj hk
          have ht' : lowerM ≫ t.f k = f.underlying.f n ≫ lowerN :=
            connesSummandι_naturality f p n (q - 1) k hn' hj'
          apply (cancel_mono bN.hom).1
          have hL : (m ≫ (t.f j ≫ pN)) ≫ bN.hom = f.underlying.f n ≫ lowerN := by
            exact (congrArg (fun a => a ≫ bN.hom) (Category.assoc m (t.f j) pN).symm).trans
              ((congrArg (fun a => (a ≫ pN) ≫ bN.hom) ht).trans
                ((Category.assoc (f.underlying.f n ≫ mN) pN bN.hom).trans
                  ((Category.assoc (f.underlying.f n) mN (pN ≫ bN.hom)).trans
                    (congrArg (fun a => f.underlying.f n ≫ a) hN))))
          have hR : (m ≫ (pM ≫ s)) ≫ bN.hom = f.underlying.f n ≫ lowerN := by
            exact (Category.assoc m (pM ≫ s) bN.hom).trans
              ((congrArg (fun a => m ≫ a) (Category.assoc pM s bN.hom)).trans
                ((congrArg (fun a => m ≫ (pM ≫ a)) hext).trans
                  ((congrArg (fun a => m ≫ a) (Category.assoc pM bM.hom (t.f k)).symm).trans
                    ((Category.assoc m (pM ≫ bM.hom) (t.f k)).symm.trans
                      ((congrArg (fun a => a ≫ t.f k) hM).trans ht')))))
          exact hL.trans hR.symm
      exact hleft.trans (hmiddle.trans hright.symm)
    · exact (M.connesBicomplex_isZero_cell p q (by omega)).eq_of_src _ _
  exact hmain

/-- The existing periodicity chain maps have the same map square. -/
theorem connesPeriodicity_naturality (f : M ⟶ N) :
    total.map (M.connesBicomplexMap f) (ComplexShape.down ℕ) ≫ N.connesPeriodicity =
      M.connesPeriodicity ≫
        extendMap (total.map (M.connesBicomplexMap f) (ComplexShape.down ℕ))
          (ComplexShape.embeddingDown'Add (1 : ℕ) 2) := by
  apply HomologicalComplex.hom_ext
  intro j
  exact connesPeriodicityF_naturality f j

omit [M.connesBicomplex.HasTotal (ComplexShape.down ℕ)]
  [N.connesBicomplex.HasTotal (ComplexShape.down ℕ)] in
/-- The arbitrary-model constructor specializes to the existing actual mixed bicomplex map. -/
theorem ConnesDoubleData.map_connesDoubleData (f : M ⟶ N) :
    M.connesDoubleData.map N.connesDoubleData f = M.connesBicomplexMap f := by
  symm
  apply ConnesDoubleData.map_eq_of_spec M.connesDoubleData N.connesDoubleData f
    (M.connesBicomplexMap f)
  intro p q h
  let eM : (M.connesBicomplex.X p).X q ≅ M.underlying.X (q - p) :=
    M.connesDoubleData.objIso p q h
  let eN : (N.connesBicomplex.X p).X q ≅ N.underlying.X (q - p) :=
    N.connesDoubleData.objIso p q h
  have hn : q - p + p = q := Nat.sub_add_cancel h
  have hc : ((M.connesBicomplexMap f).f p).f q =
      eM.hom ≫ f.underlying.f (q - p) ≫ eN.inv :=
    connesBicomplexMap_coordinates f p (q - p) q hn
  have hx : (eM.hom ≫ f.underlying.f (q - p) ≫ eN.inv) ≫ eN.hom =
      ((M.connesBicomplexMap f).f p).f q ≫ eN.hom :=
    congrArg (fun a : (M.connesBicomplex.X p).X q ⟶ (N.connesBicomplex.X p).X q =>
      a ≫ eN.hom) hc.symm
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hx
  exact hx

end Coordinates

section Presentations

variable {C : Type u} [Category.{v} C] [Abelian C] {M N P : MixedComplex C}

/-- The original first-column comparison is natural in a plain mixed map. -/
theorem connesFirstColumnMap_naturality (f : M ⟶ N) :
    f.underlying ≫ N.connesFirstColumnMap =
      M.connesFirstColumnMap ≫ M.connesBicomplex.partialTotalHom (M.connesBicomplexMap f) 0 := by
  have h := GenericMixedCyclicData.automatic_columnMap_naturality
    M.connesCyclicData N.connesCyclicData f
  change f.underlying ≫ N.connesFirstColumnMap =
    M.connesFirstColumnMap ≫ M.connesBicomplex.partialTotalHom
      (M.connesDoubleData.map N.connesDoubleData f) 0 at h
  rw [ConnesDoubleData.map_connesDoubleData] at h
  exact h

/-- The ordinary inclusion commutes with the constructed total map. -/
theorem connesOrdinaryInclusion_naturality (f : M ⟶ N) :
    f.underlying ≫ N.connesOrdinaryInclusion =
      M.connesOrdinaryInclusion ≫ (connesTotalFunctor (C := C)).map f := by
  let φ := M.connesBicomplexMap f
  have hcolumn := connesFirstColumnMap_naturality f
  have hi : M.connesBicomplex.partialTotalHom φ 0 ≫ N.connesBicomplex.partialTotalι 0 =
      M.connesBicomplex.partialTotalι 0 ≫ total.map φ (ComplexShape.down ℕ) :=
    (partialTotalInclusionNatTrans (C := C) 0).naturality φ
  calc
    _ = (f.underlying ≫ N.connesFirstColumnMap) ≫ N.connesBicomplex.partialTotalι 0 :=
      (Category.assoc _ _ _).symm
    _ = (M.connesFirstColumnMap ≫ M.connesBicomplex.partialTotalHom φ 0) ≫
        N.connesBicomplex.partialTotalι 0 := congrArg (fun b => b ≫ N.connesBicomplex.partialTotalι 0) hcolumn
    _ = M.connesFirstColumnMap ≫ (M.connesBicomplex.partialTotalι 0 ≫
        total.map φ (ComplexShape.down ℕ)) :=
      (Category.assoc _ _ _).trans (congrArg (fun b => M.connesFirstColumnMap ≫ b) hi)
    _ = _ := (Category.assoc _ _ _).symm

/-- A genuinely nonzero underlying mixed map remains nonzero on the total. -/
theorem connesTotalMap_ne_zero (f : M ⟶ N) (hf : f.underlying ≠ 0) :
    (connesTotalFunctor (C := C)).map f ≠ 0 := by
  intro hzero
  let : Mono N.connesOrdinaryInclusion := by
    change Mono (N.connesFirstColumnMap ≫ N.connesBicomplex.partialTotalι 0)
    infer_instance
  have h := connesOrdinaryInclusion_naturality f
  have he : f.underlying ≫ N.connesOrdinaryInclusion = 0 :=
    h.trans ((congrArg (fun b => M.connesOrdinaryInclusion ≫ b) hzero).trans (comp_zero))
  apply hf
  apply (cancel_mono N.connesOrdinaryInclusion).1
  exact he.trans ((zero_comp).symm)

/-- Native cokernel descent carries periodicity naturality to the tail map. -/
theorem connesTailNatMap_naturality (f : M ⟶ N) :
    partialTotalCokernelMap (M.connesBicomplexMap f) 0 ≫ N.connesTailNatMap =
      M.connesTailNatMap ≫ extendMap ((connesTotalFunctor (C := C)).map f)
        (ComplexShape.embeddingDown'Add (1 : ℕ) 2) := by
  let e : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    ComplexShape.embeddingDown'Add (1 : ℕ) 2
  let t : M.connesTotal ⟶ N.connesTotal := (connesTotalFunctor (C := C)).map f
  let q : cokernel (M.connesBicomplex.partialTotalι 0) ⟶
      cokernel (N.connesBicomplex.partialTotalι 0) :=
    partialTotalCokernelMap (M.connesBicomplexMap f) 0
  let πM : M.connesTotal ⟶ cokernel (M.connesBicomplex.partialTotalι 0) :=
    cokernel.π (M.connesBicomplex.partialTotalι 0)
  let πN : N.connesTotal ⟶ cokernel (N.connesBicomplex.partialTotalι 0) :=
    cokernel.π (N.connesBicomplex.partialTotalι 0)
  let rM : cokernel (M.connesBicomplex.partialTotalι 0) ⟶ M.connesTotal.extend e :=
    M.connesTailNatMap
  let rN : cokernel (N.connesBicomplex.partialTotalι 0) ⟶ N.connesTotal.extend e :=
    N.connesTailNatMap
  let pM : M.connesTotal ⟶ M.connesTotal.extend e := M.connesPeriodicity
  let pN : N.connesTotal ⟶ N.connesTotal.extend e := N.connesPeriodicity
  let s : M.connesTotal.extend e ⟶ N.connesTotal.extend e := extendMap t e
  have hπ : πM ≫ q = t ≫ πN := partialTotalCokernel_π_naturality (M.connesBicomplexMap f) 0
  have hM : πM ≫ rM = pM := M.cokernelπ_connesTailNatMap
  have hN : πN ≫ rN = pN := N.cokernelπ_connesTailNatMap
  have hperiod : t ≫ pN = pM ≫ s := connesPeriodicity_naturality f
  have hn : q ≫ rN = rM ≫ s := by
    apply (cancel_epi πM).1
    have hleft : πM ≫ (q ≫ rN) = t ≫ pN :=
      (Category.assoc πM q rN).symm.trans
        ((congrArg (fun a => a ≫ rN) hπ).trans
          ((Category.assoc t πN rN).trans (congrArg (fun a => t ≫ a) hN)))
    have hright : πM ≫ (rM ≫ s) = pM ≫ s :=
      (Category.assoc πM rM s).symm.trans (congrArg (fun a => a ≫ s) hM)
    exact hleft.trans (hperiod.trans hright.symm)
  exact hn

/-- The existing Nat-indexed cancellation is natural, without an IsIso input. -/
theorem connesTailNatIso_naturality (f : M ⟶ N) :
    partialTotalCokernelMap (M.connesBicomplexMap f) 0 ≫ N.connesTailNatIso.hom =
      M.connesTailNatIso.hom ≫ extendMap ((connesTotalFunctor (C := C)).map f)
        (ComplexShape.embeddingDown'Add (1 : ℕ) 2) :=
  connesTailNatMap_naturality f

/-- The same square is transported to the native integer SBI degrees. -/
theorem connesTailIso_naturality (f : M ⟶ N) :
    extendMap (partialTotalCokernelMap (M.connesBicomplexMap f) 0)
        (ComplexShape.embeddingDownNatToIntShift 0) ≫ N.connesTailIso.hom =
      M.connesTailIso.hom ≫ extendMap ((connesTotalFunctor (C := C)).map f)
        (ComplexShape.embeddingDownNatToIntShift 2) := by
  have h := GenericMixedCyclicData.automatic_tailMap_naturality
    M.connesCyclicData N.connesCyclicData f
  change extendMap (partialTotalCokernelMap
      (M.connesDoubleData.map N.connesDoubleData f) 0)
      (ComplexShape.embeddingDownNatToIntShift 0) ≫ N.connesTailIso.hom =
    M.connesTailIso.hom ≫ extendMap
      (total.map (M.connesDoubleData.map N.connesDoubleData f) (ComplexShape.down ℕ))
      (ComplexShape.embeddingDownNatToIntShift 2) at h
  rw [ConnesDoubleData.map_connesDoubleData] at h
  exact h

/-- A plain mixed-complex morphism supplies all canonical presentation squares. -/
def connesCyclicMap (f : M ⟶ N) : GenericMixedCyclicMap M.connesCyclicData N.connesCyclicData f :=
  GenericMixedCyclicData.automaticMap M.connesCyclicData N.connesCyclicData f

theorem connesCyclicMap_id (M : MixedComplex C) :
    connesCyclicMap (𝟙 M) = GenericMixedCyclicMap.id M.connesCyclicData :=
  GenericMixedCyclicData.automaticMap_id M.connesCyclicData

theorem connesCyclicMap_comp (f : M ⟶ N) (g : N ⟶ P) :
    connesCyclicMap (f ≫ g) = GenericMixedCyclicMap.comp (connesCyclicMap f) (connesCyclicMap g) :=
  GenericMixedCyclicData.automaticMap_comp M.connesCyclicData N.connesCyclicData P.connesCyclicData f g

/-- The Connes presentations form a functor on plain mixed-complex maps. -/
def connesSBIPresentationFunctor : MixedComplex C ⥤ ConnesSBIPresentation (A := C) where
  obj M := M.connesSBIPresentation
  map f := (connesCyclicMap f).toConnesSBIPresentationHom
  map_id M := by
    exact (congrArg (fun F => F.toConnesSBIPresentationHom) (connesCyclicMap_id M)).trans
      (GenericMixedCyclicMap.toConnesSBIPresentationHom_id M.connesCyclicData)
  map_comp f g := by
    exact (congrArg (fun F => F.toConnesSBIPresentationHom) (connesCyclicMap_comp f g)).trans
      (GenericMixedCyclicMap.toConnesSBIPresentationHom_comp (connesCyclicMap f) (connesCyclicMap g))

/-- The Connes construction defines a functor from mixed complexes to SBI diagrams. -/
def connesSBIDiagramFunctor : MixedComplex C ⥤ NatSBIDiagram (A := C) :=
  connesSBIPresentationFunctor ⋙ ConnesSBIPresentation.sbiDiagramFunctor

/-- The induced cyclic map is homology of the existing actual total map. -/
theorem connesCyclicMap_hcMap (f : M ⟶ N) (n : ℕ) :
    (connesCyclicMap f).hcMap n = (connesHomologyFunctor (C := C) n).map f := by
  change HomologicalComplex.homologyMap
      (total.map (M.connesDoubleData.map N.connesDoubleData f) (ComplexShape.down ℕ)) n =
    (connesHomologyFunctor (C := C) n).map f
  rw [ConnesDoubleData.map_connesDoubleData]
  rfl

/-- The canonical mixed adapter transfers the native quasi-isomorphism equivalence. -/
theorem quasiIso_connesTotalMap_iff (f : M ⟶ N) :
    QuasiIso f.underlying ↔ QuasiIso ((connesTotalFunctor (C := C)).map f) := by
  have h := (connesCyclicMap f).toConnesSBIPresentationHom.quasiIso_ordinaryMap_iff_shortMap_τ₂
  change QuasiIso f.underlying ↔
      QuasiIso (total.map (M.connesDoubleData.map N.connesDoubleData f) (ComplexShape.down ℕ)) at h
  rw [ConnesDoubleData.map_connesDoubleData] at h
  exact h

/-- The underlying complex and column-zero functor are naturally isomorphic. -/
def connesFirstColumnNatIso :
    MixedComplex.underlyingFunctor C ≅
      connesBicomplexFunctor ⋙ HomologicalComplex₂.partialTotalStageFunctor (C := C) 0 :=
  NatIso.ofComponents (fun M => M.connesFirstColumnIso.symm) (by
    intro M N f
    exact connesFirstColumnMap_naturality f)

/-- The degree-two periodicity maps form a natural transformation. -/
def connesPeriodicityNatTrans : connesTotalFunctor (C := C) ⟶
    connesTotalFunctor (C := C) ⋙
      (ComplexShape.embeddingDown'Add (1 : ℕ) 2).extendFunctor C where
  app M := M.connesPeriodicity
  naturality _ _ f := connesPeriodicity_naturality f

/-- Native tail cancellation is a natural isomorphism of actual cokernel and shifted-total functors. -/
def connesTailNatIsoFamily :
    connesBicomplexFunctor ⋙ partialTotalCokernelFunctor (A := C) 0 ≅
      connesTotalFunctor (C := C) ⋙
        (ComplexShape.embeddingDown'Add (1 : ℕ) 2).extendFunctor C :=
  NatIso.ofComponents (fun M => M.connesTailNatIso) (by
    intro M N f
    exact connesTailNatIso_naturality f)

/-- The same natural cancellation retains the literal integer SBI offsets. -/
def connesTailIsoFamily :
    (connesBicomplexFunctor ⋙ partialTotalCokernelFunctor (A := C) 0) ⋙
        (ComplexShape.embeddingDownNatToIntShift 0).extendFunctor C ≅
      connesTotalFunctor (C := C) ⋙
        (ComplexShape.embeddingDownNatToIntShift 2).extendFunctor C :=
  NatIso.ofComponents (fun M => M.connesTailIso) (by
    intro M N f
    exact connesTailIso_naturality f)

/-- Actual Connes totalization faithfully retains the original mixed morphism. -/
instance connesTotalFunctor_faithful : (connesTotalFunctor (C := C)).Faithful where
  map_injective {M N} {f g} h := by
    apply MixedComplex.Hom.ext
    let : Mono N.connesOrdinaryInclusion := by
      change Mono (N.connesFirstColumnMap ≫ N.connesBicomplex.partialTotalι 0)
      infer_instance
    apply (cancel_mono N.connesOrdinaryInclusion).1
    exact (connesOrdinaryInclusion_naturality f).trans
      ((congrArg (fun a => M.connesOrdinaryInclusion ≫ a) h).trans
        (connesOrdinaryInclusion_naturality g).symm)

/-- The presentation functor is faithful on plain mixed morphisms. -/
instance connesSBIPresentationFunctor_faithful :
    (connesSBIPresentationFunctor (C := C)).Faithful where
  map_injective {M N} {f g} h := by
    apply MixedComplex.Hom.ext
    exact congrArg (fun F : M.connesSBIPresentation ⟶ N.connesSBIPresentation =>
      F.ordinaryMap) h

end Presentations

end MixedComplex
