/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.MixedComplex.Connes
public import MathlibExt.Algebra.Homology.PartialTotalCokernel

/-!
# Comparison of cyclic homology of mixed complexes

Comparisons of Connes bicomplexes and their totals induce compatible
maps of SBI diagrams. The `ConnesSBIPresentation` comparison theorem
gives the corresponding five-lemma criterion for cyclic homology.
-/

@[expose] public section

namespace MixedComplex

open CategoryTheory Limits

universe w u

variable {A : Type u} [Category.{w} A] [Abelian A]
variable {M M' : MixedComplex A}
variable {D : GenericMixedCyclicData M} {D' : GenericMixedCyclicData M'}

/-- The canonical identification between adjacent diagonal cells used by the
two-column tail translation. -/
noncomputable def genericMixedTailCellIso
    (K : ConnesDoubleData M) (p q : ℕ) (h : p ≤ q) :
    (K.K.X (p + 1)).X (q + 1) ≅ (K.K.X p).X q :=
  K.objIso (p + 1) (q + 1) (by omega) ≪≫
    eqToIso (congrArg (mixedObject M)
      (by omega : q + 1 - (p + 1) = q - p)) ≪≫
    (K.objIso p q h).symm

/-- The target coordinate of the tail translation is the adjacent-cell
identification followed by the total generator and the shifted-extension
coordinate. -/
theorem genericMixedTailTargetComponent_eq
    (K : ConnesDoubleData M) (p q : ℕ) (h : p ≤ q) :
    genericMixedTailTargetComponent K p q h =
      (genericMixedTailCellIso K p q h).hom ≫
        K.K.ιTotal (ComplexShape.down ℕ) p q (p + q) rfl ≫
        (HomologicalComplex.extendDownNatToIntShiftXIso
          (genericMixedConnesTotal K) 2 (p + q)).inv := by
  dsimp only [genericMixedTailTargetComponent,
    genericMixedTailCellIso, Iso.trans_hom, Iso.symm_hom]
  simp only [eqToIso.hom, Category.assoc]

/-- Maps out of the shift-zero Connes tail are equal when they agree after
every full-total generator, the degreewise cokernel projection, and the
canonical shift-zero coordinate. -/
theorem genericMixedConnesTail_extend_hom_ext
    (K : ConnesDoubleData M)
    {L : ChainComplex A ℤ}
    {α β : (genericMixedConnesTail K).extend
      (ComplexShape.embeddingDownNatToIntShift 0) ⟶ L}
    (h : ∀ (i j n : ℕ) (hn : i + j = n),
      K.K.ιTotal (ComplexShape.down ℕ) i j n hn ≫
          (cokernel.π (genericMixedFirstColumnι K)).f n ≫
          (HomologicalComplex.extendDownNatToIntShiftXIso
            (genericMixedConnesTail K) 0 n).inv ≫
          α.f ((0 : ℤ) + (n : ℤ)) =
        K.K.ιTotal (ComplexShape.down ℕ) i j n hn ≫
          (cokernel.π (genericMixedFirstColumnι K)).f n ≫
          (HomologicalComplex.extendDownNatToIntShiftXIso
            (genericMixedConnesTail K) 0 n).inv ≫
          β.f ((0 : ℤ) + (n : ℤ))) :
    α = β :=
  HomologicalComplex₂.partialTotalCokernel_extend_hom_ext K.K 0 0 h

/-- Chain-level comparison data inducing a morphism of generic mixed-complex
SBI presentations. -/
structure GenericMixedCyclicMap (D : GenericMixedCyclicData M)
    (D' : GenericMixedCyclicData M') (f : M ⟶ M') where
  /-- The map between the column/total/tail short complexes. -/
  shortMap : genericMixedConnesShortComplex D.model ⟶
    genericMixedConnesShortComplex D'.model
  /-- Naturality of the comparisons with the first columns. -/
  columnMap_naturality :
    f.underlying ≫ D'.columnMap = D.columnMap ≫ shortMap.τ₁
  /-- Naturality of the two chain-level tail translations. -/
  tailMap_naturality :
    HomologicalComplex.extendMap shortMap.τ₃
          (ComplexShape.embeddingDownNatToIntShift 0) ≫ D'.tailMap =
      D.tailMap ≫ HomologicalComplex.extendMap shortMap.τ₂
        (ComplexShape.embeddingDownNatToIntShift 2)

namespace GenericMixedCyclicMap

/-- Two mixed-cyclic comparison maps over the same mixed-complex morphism are
equal when their short-complex maps agree. -/
@[ext]
theorem ext {f : M ⟶ M'} (F G : GenericMixedCyclicMap D D' f)
    (h : F.shortMap = G.shortMap) : F = G := by
  cases F
  cases G
  cases h
  rfl

/-- Identity comparison map. -/
noncomputable def id (D : GenericMixedCyclicData M) :
    GenericMixedCyclicMap D D (𝟙 M) where
  shortMap := 𝟙 _
  columnMap_naturality := by simp
  tailMap_naturality := by simp

/-- Composition of mixed-cyclic comparison maps. -/
noncomputable def comp {M'' : MixedComplex A}
    {D'' : GenericMixedCyclicData M''}
    {f : M ⟶ M'} {g : M' ⟶ M''}
    (F : GenericMixedCyclicMap D D' f)
    (G : GenericMixedCyclicMap D' D'' g) :
    GenericMixedCyclicMap D D'' (f ≫ g) where
  shortMap := F.shortMap ≫ G.shortMap
  columnMap_naturality := by
    simp only [MixedComplex.comp_underlying, Category.assoc,
      ShortComplex.comp_τ₁]
    rw [G.columnMap_naturality, ← Category.assoc,
      F.columnMap_naturality, Category.assoc]
  tailMap_naturality := by
    simp only [ShortComplex.comp_τ₃, ShortComplex.comp_τ₂,
      HomologicalComplex.extendMap_comp, Category.assoc]
    rw [G.tailMap_naturality, ← Category.assoc,
      F.tailMap_naturality, Category.assoc]

@[simp]
theorem id_shortMap (D : GenericMixedCyclicData M) :
    (id D).shortMap = 𝟙 _ :=
  rfl

@[simp]
theorem comp_shortMap {M'' : MixedComplex A}
    {D'' : GenericMixedCyclicData M''} {f : M ⟶ M'} {g : M' ⟶ M''}
    (F : GenericMixedCyclicMap D D' f)
    (G : GenericMixedCyclicMap D' D'' g) :
    (comp F G).shortMap = F.shortMap ≫ G.shortMap :=
  rfl

/-- Forget the mixed-complex model characterizations and retain the
general presentation morphism. -/
noncomputable abbrev toConnesSBIPresentationHom {f : M ⟶ M'}
    (F : GenericMixedCyclicMap D D' f) :
    D.toConnesSBIPresentation ⟶ D'.toConnesSBIPresentation where
  ordinaryMap := f.underlying
  shortMap := F.shortMap
  ordinaryComparison_naturality := F.columnMap_naturality
  tailIso_naturality := by
    simpa only [GenericMixedCyclicData.toConnesSBIPresentation,
      asIso_hom] using F.tailMap_naturality

@[simp]
theorem toConnesSBIPresentationHom_id (D : GenericMixedCyclicData M) :
    (id D).toConnesSBIPresentationHom = 𝟙 D.toConnesSBIPresentation := by
  apply ConnesSBIPresentation.hom_ext <;> simp

@[simp]
theorem toConnesSBIPresentationHom_comp
    {M'' : MixedComplex A} {D'' : GenericMixedCyclicData M''}
    {f : M ⟶ M'} {g : M' ⟶ M''}
    (F : GenericMixedCyclicMap D D' f)
    (G : GenericMixedCyclicMap D' D'' g) :
    (comp F G).toConnesSBIPresentationHom =
      F.toConnesSBIPresentationHom ≫ G.toConnesSBIPresentationHom := by
  apply ConnesSBIPresentation.hom_ext <;> simp

/-- Map induced on homology of the underlying mixed complex. -/
noncomputable abbrev hMap {f : M ⟶ M'}
    (F : GenericMixedCyclicMap D D' f) (n : ℕ) :
    genericMixedHomology M n ⟶ genericMixedHomology M' n :=
  F.toConnesSBIPresentationHom.hMap n

/-- Compatibility spelling for the map on underlying homology. -/
noncomputable abbrev hhMap {f : M ⟶ M'}
    (F : GenericMixedCyclicMap D D' f) (n : ℕ) :
    genericMixedHomology M n ⟶ genericMixedHomology M' n :=
  F.hMap n

/-- Map induced on cyclic homology. -/
noncomputable abbrev hcMap {f : M ⟶ M'}
    (F : GenericMixedCyclicMap D D' f) (n : ℕ) : D.HC n ⟶ D'.HC n :=
  F.toConnesSBIPresentationHom.hcMap n

/-- The model-specific comparison induces a morphism of homology-level SBI
diagrams. -/
noncomputable abbrev toSBIHom {f : M ⟶ M'}
    (F : GenericMixedCyclicMap D D' f) : D.sbiDiagram ⟶ D'.sbiDiagram :=
  F.toConnesSBIPresentationHom.toSBIHom

@[simp]
theorem id_hMap (D : GenericMixedCyclicData M) (n : ℕ) :
    (id D).hMap n = 𝟙 _ := by
  simp only [hMap, toConnesSBIPresentationHom_id,
    ConnesSBIPresentation.Hom.id_hMap]

@[simp]
theorem id_hcMap (D : GenericMixedCyclicData M) (n : ℕ) :
    (id D).hcMap n = 𝟙 _ := by
  simp only [hcMap, toConnesSBIPresentationHom_id,
    ConnesSBIPresentation.Hom.id_hcMap]

@[simp]
theorem comp_hMap {M'' : MixedComplex A}
    {D'' : GenericMixedCyclicData M''} {f : M ⟶ M'} {g : M' ⟶ M''}
    (F : GenericMixedCyclicMap D D' f)
    (G : GenericMixedCyclicMap D' D'' g) (n : ℕ) :
    (comp F G).hMap n = F.hMap n ≫ G.hMap n := by
  simp only [hMap, toConnesSBIPresentationHom_comp,
    ConnesSBIPresentation.Hom.comp_hMap]

@[simp]
theorem comp_hcMap {M'' : MixedComplex A}
    {D'' : GenericMixedCyclicData M''} {f : M ⟶ M'} {g : M' ⟶ M''}
    (F : GenericMixedCyclicMap D D' f)
    (G : GenericMixedCyclicMap D' D'' g) (n : ℕ) :
    (comp F G).hcMap n = F.hcMap n ≫ G.hcMap n := by
  simp only [hcMap, toConnesSBIPresentationHom_comp,
    ConnesSBIPresentation.Hom.comp_hcMap]

@[simp]
theorem toSBIHom_id (D : GenericMixedCyclicData M) :
    (id D).toSBIHom = 𝟙 D.sbiDiagram := by
  simp only [toSBIHom, toConnesSBIPresentationHom_id,
    ConnesSBIPresentation.Hom.toSBIHom_id]

@[simp]
theorem toSBIHom_comp {M'' : MixedComplex A}
    {D'' : GenericMixedCyclicData M''} {f : M ⟶ M'} {g : M' ⟶ M''}
    (F : GenericMixedCyclicMap D D' f)
    (G : GenericMixedCyclicMap D' D'' g) :
    (comp F G).toSBIHom = F.toSBIHom ≫ G.toSBIHom := by
  simp only [toSBIHom, toConnesSBIPresentationHom_comp,
    ConnesSBIPresentation.Hom.toSBIHom_comp]

/-- A homology isomorphism through degree `n` induces a cyclic-homology
isomorphism in degree `n`. -/
theorem isIso_hcMap_of_isIso_homologyMap_le {f : M ⟶ M'}
    (F : GenericMixedCyclicMap D D' f) (n : ℕ)
    (h : ∀ m : ℕ, m ≤ n →
      IsIso (HomologicalComplex.homologyMap f.underlying m)) :
    IsIso (F.hcMap n) :=
  F.toConnesSBIPresentationHom.isIso_hcMap_of_isIso_hMap_le n h

/-- An isomorphism on all underlying homology groups induces isomorphisms on
all cyclic-homology maps. -/
theorem isIso_hcMap_of_isIso_homologyMap {f : M ⟶ M'}
    (F : GenericMixedCyclicMap D D' f)
    (h : ∀ n : ℕ, IsIso (HomologicalComplex.homologyMap f.underlying n))
    (n : ℕ) : IsIso (F.hcMap n) :=
  F.toConnesSBIPresentationHom.isIso_hcMap_of_isIso_hMap h n

/-- A quasi-isomorphism of underlying mixed-complex chain complexes induces a
quasi-isomorphism on the total complexes. -/
theorem quasiIso_shortMap_τ₂ {f : M ⟶ M'}
    (F : GenericMixedCyclicMap D D' f) [QuasiIso f.underlying] :
    QuasiIso F.shortMap.τ₂ :=
  F.toConnesSBIPresentationHom.quasiIso_shortMap_τ₂

/-- A quasi-isomorphism of underlying mixed-complex chain complexes induces
isomorphisms on all cyclic-homology maps. -/
theorem isIso_hcMap {f : M ⟶ M'} (F : GenericMixedCyclicMap D D' f)
    [QuasiIso f.underlying] (n : ℕ) : IsIso (F.hcMap n) := by
  apply F.isIso_hcMap_of_isIso_homologyMap
  intro m
  infer_instance

end GenericMixedCyclicMap

end MixedComplex
