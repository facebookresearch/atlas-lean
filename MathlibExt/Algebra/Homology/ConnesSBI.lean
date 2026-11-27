/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.QuasiIso
public import MathlibExt.Algebra.Homology.Embedding.DownNatToIntShiftInvNaturality
public import MathlibExt.Algebra.Homology.HomologyDegreeTransport
public import MathlibExt.Algebra.Homology.QuasiIsoNaturality
public import MathlibExt.Algebra.Homology.SBISequence

/-!
# Chain-level presentations of connective SBI sequences

`ConnesSBIPresentation` packages the chain-level input common to Connes constructions:
a short exact sequence, a quasi-isomorphic model for its first term, and an
even translation identifying the third term with the second.  It derives the
SBI diagram, its exactness and connective boundary conditions.

The construction is independent of mixed complexes, cyclic objects, and a
chosen bicomplex model.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w u

namespace CategoryTheory

open Limits

variable {A : Type u} [Category.{w} A] [Abelian A]
/-- A chain-level presentation of a connective SBI sequence. -/
structure ConnesSBIPresentation where
  /-- The preferred chain complex computing ordinary homology. -/
  ordinary : ChainComplex A ℕ
  /-- The short exact sequence which produces the long exact sequence. -/
  shortComplex : ShortComplex (ChainComplex A ℕ)
  /-- Exactness, monicity, and epicity of the chain-level short complex. -/
  shortExact : shortComplex.ShortExact
  /-- Comparison from the preferred ordinary-homology model to the first
  term of the short complex. -/
  ordinaryComparison : ordinary ⟶ shortComplex.X₁
  [ordinaryComparisonQuasiIso : QuasiIso ordinaryComparison]
  /-- Even translation from the third term to the second term. -/
  tailIso :
    shortComplex.X₃.extend (ComplexShape.embeddingDownNatToIntShift 0) ≅
      shortComplex.X₂.extend (ComplexShape.embeddingDownNatToIntShift 2)

namespace ConnesSBIPresentation

/-- Cyclic-type homology associated to a chain-level SBI presentation. -/
noncomputable abbrev HC (D : ConnesSBIPresentation (A := A)) (n : ℕ) : A :=
  D.shortComplex.X₂.homology n

/-- Homology comparison induced by the first-term quasi-isomorphism. -/
noncomputable def hIso (D : ConnesSBIPresentation (A := A)) (n : ℕ) :
    D.ordinary.homology n ≅ D.shortComplex.X₁.homology n := by
  let _ := D.ordinaryComparisonQuasiIso
  exact isoOfQuasiIsoAt D.ordinaryComparison n

/-- Homology comparison induced by the even translation. -/
noncomputable def tailHomologyIso (D : ConnesSBIPresentation (A := A)) (n : ℕ) :
    D.shortComplex.X₃.homology (n + 2) ≅ D.HC n := by
  let Q := D.shortComplex.X₃
  let T := D.shortComplex.X₂
  let Qz := Q.extend (ComplexShape.embeddingDownNatToIntShift 0)
  let Tz := T.extend (ComplexShape.embeddingDownNatToIntShift 2)
  let d₁ : ℤ := 0 + ((n + 2 : ℕ) : ℤ)
  let d₂ : ℤ := 2 + (n : ℤ)
  let eQ : Q.homology (n + 2) ≅ Qz.homology d₁ :=
    (HomologicalComplex.homologyIsoExtendDownNatToIntShift Q 0
      (n + 2)).symm
  let eMap : Qz.homology d₁ ≅ Tz.homology d₁ :=
    HomologicalComplex.homologyMapIso D.tailIso d₁
  let eDeg : Tz.homology d₁ ≅ Tz.homology d₂ :=
    HomologicalComplex.homologyIsoOfEq Tz (by
      dsimp only [d₁, d₂]
      omega)
  let eT : Tz.homology d₂ ≅ T.homology n :=
    HomologicalComplex.homologyIsoExtendDownNatToIntShift T 2 n
  exact eQ ≪≫ eMap ≪≫ eDeg ≪≫ eT

/-- Inclusion in the SBI diagram. -/
noncomputable def I (D : ConnesSBIPresentation (A := A)) (n : ℕ) :
    D.ordinary.homology n ⟶ D.HC n :=
  (D.hIso n).hom ≫ HomologicalComplex.homologyMap D.shortComplex.f n

/-- Periodicity in the SBI diagram. -/
noncomputable def S (D : ConnesSBIPresentation (A := A)) (n : ℕ) :
    D.HC (n + 2) ⟶ D.HC n :=
  HomologicalComplex.homologyMap D.shortComplex.g (n + 2) ≫
    (D.tailHomologyIso n).hom

/-- Connecting map in the SBI diagram. -/
noncomputable def B (D : ConnesSBIPresentation (A := A)) (n : ℕ) :
    D.HC n ⟶ D.ordinary.homology (n + 1) :=
  (D.tailHomologyIso n).inv ≫
    D.shortExact.δ (n + 2) (n + 1) (by simp) ≫
    (D.hIso (n + 1)).inv

@[reassoc (attr := simp)]
theorem S_comp_B (D : ConnesSBIPresentation (A := A)) (n : ℕ) :
    D.S n ≫ D.B n = 0 := by
  simp only [S, B, Category.assoc]
  rw [Iso.hom_inv_id_assoc]
  simpa only [zero_comp] using
    D.shortExact.comp_δ_assoc (n + 2) (n + 1) (by simp)
      (D.hIso (n + 1)).inv

@[reassoc (attr := simp)]
theorem B_comp_I (D : ConnesSBIPresentation (A := A)) (n : ℕ) :
    D.B n ≫ D.I (n + 1) = 0 := by
  simp only [B, I, Category.assoc]
  rw [Iso.inv_hom_id_assoc]
  rw [D.shortExact.δ_comp]
  simp

@[reassoc (attr := simp)]
theorem I_comp_S (D : ConnesSBIPresentation (A := A)) (n : ℕ) :
    D.I (n + 2) ≫ D.S n = 0 := by
  have hfg : HomologicalComplex.homologyMap D.shortComplex.f (n + 2) ≫
      HomologicalComplex.homologyMap D.shortComplex.g (n + 2) = 0 := by
    rw [← HomologicalComplex.homologyMap_comp, D.shortComplex.zero,
      HomologicalComplex.homologyMap_zero]
  simp only [I, S, Category.assoc]
  rw [← Category.assoc
    (HomologicalComplex.homologyMap D.shortComplex.f (n + 2))
    (HomologicalComplex.homologyMap D.shortComplex.g (n + 2))
    (D.tailHomologyIso n).hom]
  rw [hfg, zero_comp, comp_zero]

/-- Exactness at the `HC n` term. -/
theorem exact_SB (D : ConnesSBIPresentation (A := A)) (n : ℕ) :
    (ShortComplex.mk (D.S n) (D.B n) (D.S_comp_B n)).Exact := by
  let N : ShortComplex A :=
    ShortComplex.mk
      (HomologicalComplex.homologyMap D.shortComplex.g (n + 2))
      (D.shortExact.δ (n + 2) (n + 1) (by simp))
      (D.shortExact.comp_δ (n + 2) (n + 1) (by simp))
  let R : ShortComplex A :=
    ShortComplex.mk (D.S n) (D.B n) (D.S_comp_B n)
  let e : N ≅ R := ShortComplex.isoMk (Iso.refl _)
    (D.tailHomologyIso n) (D.hIso (n + 1)).symm
    (by simp [N, R, S]) (by simp [N, R, B])
  exact ShortComplex.exact_of_iso e
    (D.shortExact.homology_exact₃ (n + 2) (n + 1) (by simp))

/-- Exactness at the `H (n + 1)` term. -/
theorem exact_BI (D : ConnesSBIPresentation (A := A)) (n : ℕ) :
    (ShortComplex.mk (D.B n) (D.I (n + 1)) (D.B_comp_I n)).Exact := by
  let N : ShortComplex A :=
    ShortComplex.mk
      (D.shortExact.δ (n + 2) (n + 1) (by simp))
      (HomologicalComplex.homologyMap D.shortComplex.f (n + 1))
      (D.shortExact.δ_comp (n + 2) (n + 1) (by simp))
  let R : ShortComplex A :=
    ShortComplex.mk (D.B n) (D.I (n + 1)) (D.B_comp_I n)
  let e : N ≅ R := ShortComplex.isoMk (D.tailHomologyIso n)
    (D.hIso (n + 1)).symm (Iso.refl _)
    (by simp [N, R, B]) (by simp [N, R, I])
  exact ShortComplex.exact_of_iso e
    (D.shortExact.homology_exact₁ (n + 2) (n + 1) (by simp))

/-- Exactness at the `HC (n + 2)` term. -/
theorem exact_IS (D : ConnesSBIPresentation (A := A)) (n : ℕ) :
    (ShortComplex.mk (D.I (n + 2)) (D.S n) (D.I_comp_S n)).Exact := by
  let N : ShortComplex A :=
    ShortComplex.mk
      (HomologicalComplex.homologyMap D.shortComplex.f (n + 2))
      (HomologicalComplex.homologyMap D.shortComplex.g (n + 2))
      (by
        rw [← HomologicalComplex.homologyMap_comp, D.shortComplex.zero]
        simp)
  let R : ShortComplex A :=
    ShortComplex.mk (D.I (n + 2)) (D.S n) (D.I_comp_S n)
  let e : N ≅ R := ShortComplex.isoMk (D.hIso (n + 2)).symm
    (Iso.refl _) (D.tailHomologyIso n)
    (by simp [N, R, I]) (by simp [N, R, S])
  exact ShortComplex.exact_of_iso e (D.shortExact.homology_exact₂ (n + 2))

/-- The homology-level SBI diagram derived from chain-level data. -/
noncomputable abbrev sbiDiagram (D : ConnesSBIPresentation (A := A)) :
    NatSBIDiagram (A := A) where
  H := fun n => D.ordinary.homology n
  HC := D.HC
  I := D.I
  S := D.S
  B := D.B
  S_comp_B := D.S_comp_B
  B_comp_I := D.B_comp_I
  I_comp_S := D.I_comp_S

/-- Exactness of the derived SBI diagram. -/
theorem sbiDiagram_exact (D : ConnesSBIPresentation (A := A)) :
    D.sbiDiagram.Exact where
  exact_SB := D.exact_SB
  exact_BI := D.exact_BI
  exact_IS := D.exact_IS

/-- Homology of the third term vanishes in degrees zero and one. -/
theorem isZero_tailHomology_of_lt_two (D : ConnesSBIPresentation (A := A))
    (n : ℕ) (hn : n < 2) : IsZero (D.shortComplex.X₃.homology n) := by
  let Q := D.shortComplex.X₃
  let T := D.shortComplex.X₂
  let Qz := Q.extend (ComplexShape.embeddingDownNatToIntShift 0)
  let Tz := T.extend (ComplexShape.embeddingDownNatToIntShift 2)
  have hTz : IsZero (Tz.homology (n : ℤ)) := by
    dsimp only [Tz]
    exact HomologicalComplex.isZero_homology_extendDownNatToIntShift_lt
      T 2 (n : ℤ) (by omega)
  have hQz : IsZero (Qz.homology (n : ℤ)) :=
    IsZero.of_iso hTz
      (HomologicalComplex.homologyMapIso D.tailIso (n : ℤ))
  have hQz' : IsZero (Qz.homology ((0 : ℤ) + (n : ℤ))) := by
    simpa only [zero_add] using hQz
  exact IsZero.of_iso hQz'
    (HomologicalComplex.homologyIsoExtendDownNatToIntShift Q 0 n).symm

/-- The degree-zero inclusion of the derived SBI diagram is an isomorphism. -/
theorem isIso_I_zero (D : ConnesSBIPresentation (A := A)) : IsIso (D.I 0) := by
  let f := D.shortComplex.f
  let g := D.shortComplex.g
  let hf := HomologicalComplex.homologyMap f 0
  have hQ0 : IsZero (D.shortComplex.X₃.homology 0) :=
    D.isZero_tailHomology_of_lt_two 0 (by omega)
  have hQ1 : IsZero (D.shortComplex.X₃.homology 1) :=
    D.isZero_tailHomology_of_lt_two 1 (by omega)
  have hExact₂ := D.shortExact.homology_exact₂ 0
  have hg0 : HomologicalComplex.homologyMap g 0 = 0 := hQ0.eq_of_tgt _ _
  let _ : Epi hf := (hExact₂.epi_f_iff).2 hg0
  have hExact₁ := D.shortExact.homology_exact₁ 1 0 (by simp)
  have hδ0 : D.shortExact.δ 1 0 (by simp) = 0 := hQ1.eq_of_src _ _
  let _ : Mono hf := (hExact₁.mono_g_iff).2 hδ0
  let _ : IsIso hf := isIso_of_mono_of_epi hf
  dsimp only [I]
  infer_instance

/-- The degree-one inclusion of the derived SBI diagram is an epimorphism. -/
theorem epi_I_one (D : ConnesSBIPresentation (A := A)) : Epi (D.I 1) := by
  let f := D.shortComplex.f
  let g := D.shortComplex.g
  let hf := HomologicalComplex.homologyMap f 1
  have hQ1 : IsZero (D.shortComplex.X₃.homology 1) :=
    D.isZero_tailHomology_of_lt_two 1 (by omega)
  have hExact₂ := D.shortExact.homology_exact₂ 1
  have hg1 : HomologicalComplex.homologyMap g 1 = 0 := hQ1.eq_of_tgt _ _
  let _ : Epi hf := (hExact₂.epi_f_iff).2 hg1
  dsimp only [I]
  infer_instance

/-- Connective boundary conditions of the derived SBI diagram. -/
theorem sbiDiagram_connectiveBoundary
    (D : ConnesSBIPresentation (A := A)) :
    D.sbiDiagram.ConnectiveBoundary where
  isIso_I_zero := D.isIso_I_zero
  epi_I_one := D.epi_I_one

/-- A chain-level morphism between two SBI presentations. -/
structure Hom (D : ConnesSBIPresentation (A := A)) (D' : ConnesSBIPresentation (A := A)) where
  /-- Map between the preferred ordinary-homology complexes. -/
  ordinaryMap : D.ordinary ⟶ D'.ordinary
  /-- Map of the underlying short exact sequences. -/
  shortMap : D.shortComplex ⟶ D'.shortComplex
  /-- Naturality of the preferred first-term comparisons. -/
  ordinaryComparison_naturality :
    ordinaryMap ≫ D'.ordinaryComparison = D.ordinaryComparison ≫ shortMap.τ₁
  /-- Naturality of the even translations. -/
  tailIso_naturality :
    HomologicalComplex.extendMap shortMap.τ₃
          (ComplexShape.embeddingDownNatToIntShift 0) ≫ D'.tailIso.hom =
      D.tailIso.hom ≫ HomologicalComplex.extendMap shortMap.τ₂
        (ComplexShape.embeddingDownNatToIntShift 2)

attribute [reassoc] Hom.ordinaryComparison_naturality Hom.tailIso_naturality

namespace Hom

/-- Two presentation morphisms are equal when their ordinary and short-complex
maps agree. -/
theorem ext {D : ConnesSBIPresentation (A := A)} {D' : ConnesSBIPresentation (A := A)}
    (F G : D.Hom D') (hOrdinary : F.ordinaryMap = G.ordinaryMap)
    (hShort : F.shortMap = G.shortMap) : F = G := by
  cases F
  cases G
  cases hOrdinary
  cases hShort
  rfl

/-- Identity morphism of a chain-level SBI presentation. -/
def id (D : ConnesSBIPresentation (A := A)) : D.Hom D where
  ordinaryMap := 𝟙 _
  shortMap := 𝟙 _
  ordinaryComparison_naturality := by simp
  tailIso_naturality := by simp

/-- Composition of chain-level SBI presentation morphisms. -/
def comp
    {D : ConnesSBIPresentation (A := A)} {D' : ConnesSBIPresentation (A := A)}
    {D'' : ConnesSBIPresentation (A := A)}
    (F : D.Hom D') (G : D'.Hom D'') :
    D.Hom D'' where
  ordinaryMap := F.ordinaryMap ≫ G.ordinaryMap
  shortMap := F.shortMap ≫ G.shortMap
  ordinaryComparison_naturality := by
    rw [Category.assoc, G.ordinaryComparison_naturality,
      ← Category.assoc, F.ordinaryComparison_naturality, Category.assoc,
      ShortComplex.comp_τ₁]
  tailIso_naturality := by
    simp only [ShortComplex.comp_τ₃, ShortComplex.comp_τ₂,
      HomologicalComplex.extendMap_comp, Category.assoc]
    rw [G.tailIso_naturality, ← Category.assoc,
      F.tailIso_naturality, Category.assoc]

end Hom

instance : Category.{w} (ConnesSBIPresentation (A := A)) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp F := by
    apply Hom.ext
    · simp only [Hom.comp, Hom.id, Category.id_comp]
    · simp only [Hom.comp, Hom.id, Category.id_comp]
  comp_id F := by
    apply Hom.ext
    · simp only [Hom.comp, Hom.id, Category.comp_id]
    · simp only [Hom.comp, Hom.id, Category.comp_id]
  assoc F G K := by
    apply Hom.ext
    · simp only [Hom.comp, Category.assoc]
    · simp only [Hom.comp, Category.assoc]

/-- Two presentation morphisms are equal when their ordinary and short-complex
maps agree. -/
@[ext]
theorem hom_ext {D D' : ConnesSBIPresentation (A := A)} (F G : D ⟶ D')
    (hOrdinary : F.ordinaryMap = G.ordinaryMap)
    (hShort : F.shortMap = G.shortMap) : F = G :=
  Hom.ext F G hOrdinary hShort

@[simp]
theorem id_ordinaryMap (D : ConnesSBIPresentation (A := A)) :
    (𝟙 D : D ⟶ D).ordinaryMap = 𝟙 _ :=
  rfl

@[simp]
theorem id_shortMap (D : ConnesSBIPresentation (A := A)) :
    (𝟙 D : D ⟶ D).shortMap = 𝟙 _ :=
  rfl

@[simp, reassoc]
theorem comp_ordinaryMap
    {D : ConnesSBIPresentation (A := A)} {D' : ConnesSBIPresentation (A := A)}
    {D'' : ConnesSBIPresentation (A := A)} (F : D ⟶ D') (G : D' ⟶ D'') :
    (F ≫ G).ordinaryMap = F.ordinaryMap ≫ G.ordinaryMap :=
  rfl

@[simp, reassoc]
theorem comp_shortMap
    {D : ConnesSBIPresentation (A := A)} {D' : ConnesSBIPresentation (A := A)}
    {D'' : ConnesSBIPresentation (A := A)} (F : D ⟶ D') (G : D' ⟶ D'') :
    (F ≫ G).shortMap = F.shortMap ≫ G.shortMap :=
  rfl

/-- Forget a presentation to its preferred ordinary complex. -/
@[simps, implicit_reducible]
def ordinaryFunctor : ConnesSBIPresentation (A := A) ⥤ ChainComplex A ℕ where
  obj D := D.ordinary
  map F := F.ordinaryMap

/-- Forget a presentation to its short exact sequence. -/
@[simps, implicit_reducible]
def shortComplexFunctor :
    ConnesSBIPresentation (A := A) ⥤ ShortComplex (ChainComplex A ℕ) where
  obj D := D.shortComplex
  map F := F.shortMap

/-- The preferred ordinary complex comparison, functorially in chain-level
SBI presentations. -/
@[simps]
def ordinaryComparisonNatTrans :
    ordinaryFunctor (A := A) ⟶
      shortComplexFunctor (A := A) ⋙ ShortComplex.π₁ where
  app D := D.ordinaryComparison
  naturality {_D _D'} F := F.ordinaryComparison_naturality

namespace Hom

/-- Map on ordinary homology. -/
noncomputable def hMap {D D' : ConnesSBIPresentation (A := A)}
    (F : D ⟶ D') (n : ℕ) :
    D.ordinary.homology n ⟶ D'.ordinary.homology n :=
  HomologicalComplex.homologyMap F.ordinaryMap n

/-- Map on cyclic-type homology. -/
noncomputable def hcMap {D D' : ConnesSBIPresentation (A := A)}
    (F : D ⟶ D') (n : ℕ) : D.HC n ⟶ D'.HC n :=
  HomologicalComplex.homologyMap F.shortMap.τ₂ n

@[simp]
theorem id_hMap (D : ConnesSBIPresentation (A := A)) (n : ℕ) :
    (𝟙 D : D ⟶ D).hMap n = 𝟙 _ := by
  simp only [hMap, id_ordinaryMap, HomologicalComplex.homologyMap_id]

@[simp]
theorem id_hcMap (D : ConnesSBIPresentation (A := A)) (n : ℕ) :
    (𝟙 D : D ⟶ D).hcMap n = 𝟙 _ := by
  simp only [hcMap, id_shortMap, ShortComplex.id_τ₂,
    HomologicalComplex.homologyMap_id]

@[simp]
theorem comp_hMap {D D' D'' : ConnesSBIPresentation (A := A)}
    (F : D ⟶ D') (G : D' ⟶ D'') (n : ℕ) :
    (F ≫ G).hMap n = F.hMap n ≫ G.hMap n := by
  simp only [hMap, comp_ordinaryMap, HomologicalComplex.homologyMap_comp]

@[simp]
theorem comp_hcMap {D D' D'' : ConnesSBIPresentation (A := A)}
    (F : D ⟶ D') (G : D' ⟶ D'') (n : ℕ) :
    (F ≫ G).hcMap n = F.hcMap n ≫ G.hcMap n := by
  simp only [hcMap, comp_shortMap, ShortComplex.comp_τ₂,
    HomologicalComplex.homologyMap_comp]

@[reassoc]
theorem hIso_hom_naturality
    {D D' : ConnesSBIPresentation (A := A)}
    (F : D ⟶ D') (n : ℕ) :
    F.hMap n ≫ (D'.hIso n).hom =
      (D.hIso n).hom ≫ HomologicalComplex.homologyMap F.shortMap.τ₁ n := by
  let _ : QuasiIso D.ordinaryComparison := D.ordinaryComparisonQuasiIso
  let _ : QuasiIso D'.ordinaryComparison := D'.ordinaryComparisonQuasiIso
  simpa only [hMap, hIso] using
    HomologicalComplex.isoOfQuasiIsoAt_naturality
      D.ordinaryComparison D'.ordinaryComparison F.ordinaryMap F.shortMap.τ₁ n
        F.ordinaryComparison_naturality

@[reassoc]
theorem tailHomologyIso_hom_naturality
    {D D' : ConnesSBIPresentation (A := A)}
    (F : D ⟶ D') (n : ℕ) :
    HomologicalComplex.homologyMap F.shortMap.τ₃ (n + 2) ≫
        (D'.tailHomologyIso n).hom =
      (D.tailHomologyIso n).hom ≫ F.hcMap n := by
  let Q := D.shortComplex.X₃
  let Q' := D'.shortComplex.X₃
  let T := D.shortComplex.X₂
  let T' := D'.shortComplex.X₂
  let Qz := Q.extend (ComplexShape.embeddingDownNatToIntShift 0)
  let Qz' := Q'.extend (ComplexShape.embeddingDownNatToIntShift 0)
  let Tz := T.extend (ComplexShape.embeddingDownNatToIntShift 2)
  let Tz' := T'.extend (ComplexShape.embeddingDownNatToIntShift 2)
  let d₁ : ℤ := 0 + ((n + 2 : ℕ) : ℤ)
  let d₂ : ℤ := 2 + (n : ℤ)
  let eQ :=
    (HomologicalComplex.homologyIsoExtendDownNatToIntShift Q 0 (n + 2)).symm
  let eQ' :=
    (HomologicalComplex.homologyIsoExtendDownNatToIntShift Q' 0 (n + 2)).symm
  let eT : Tz.homology d₂ ≅ T.homology n :=
    HomologicalComplex.homologyIsoExtendDownNatToIntShift T 2 n
  let eT' : Tz'.homology d₂ ≅ T'.homology n :=
    HomologicalComplex.homologyIsoExtendDownNatToIntShift T' 2 n
  have hd : d₁ = d₂ := by
    dsimp only [d₁, d₂]
    omega
  let eDeg : Tz.homology d₁ ≅ Tz.homology d₂ :=
    HomologicalComplex.homologyIsoOfEq Tz hd
  let eDeg' : Tz'.homology d₁ ≅ Tz'.homology d₂ :=
    HomologicalComplex.homologyIsoOfEq Tz' hd
  have hQ :
      HomologicalComplex.homologyMap F.shortMap.τ₃ (n + 2) ≫ eQ'.hom =
        eQ.hom ≫ HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap F.shortMap.τ₃
            (ComplexShape.embeddingDownNatToIntShift 0)) d₁ := by
    simpa only [Q, Q', Qz, Qz', d₁, eQ, eQ', Iso.symm_hom] using
      (HomologicalComplex.homologyIso_extendDownNatToIntShift_inv_naturality
        F.shortMap.τ₃ 0 (n + 2)).symm
  have hTail :
      HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap F.shortMap.τ₃
            (ComplexShape.embeddingDownNatToIntShift 0)) d₁ ≫
          HomologicalComplex.homologyMap D'.tailIso.hom d₁ =
        HomologicalComplex.homologyMap D.tailIso.hom d₁ ≫
          HomologicalComplex.homologyMap
            (HomologicalComplex.extendMap F.shortMap.τ₂
              (ComplexShape.embeddingDownNatToIntShift 2)) d₁ := by
    rw [← HomologicalComplex.homologyMap_comp,
      F.tailIso_naturality, HomologicalComplex.homologyMap_comp]
  have hDeg :
      HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap F.shortMap.τ₂
            (ComplexShape.embeddingDownNatToIntShift 2)) d₁ ≫ eDeg'.hom =
        eDeg.hom ≫ HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap F.shortMap.τ₂
            (ComplexShape.embeddingDownNatToIntShift 2)) d₂ := by
    simpa only [eDeg, eDeg'] using
      HomologicalComplex.homologyIsoOfEq_hom_naturality
        (HomologicalComplex.extendMap F.shortMap.τ₂
          (ComplexShape.embeddingDownNatToIntShift 2)) hd
  have hT := HomologicalComplex.homologyIso_extendDownNatToIntShift_naturality
    F.shortMap.τ₂ 2 n
  dsimp only [tailHomologyIso, hcMap]
  simp only [Iso.trans_hom, HomologicalComplex.homologyMapIso_hom,
    Category.assoc]
  dsimp only [d₂] at hDeg hT ⊢
  rw [reassoc_of% hQ, reassoc_of% hTail, reassoc_of% hDeg, hT]

private theorem first_naturality
    {D : ConnesSBIPresentation (A := A)} {D' : ConnesSBIPresentation (A := A)}
    (F : D ⟶ D') (n : ℕ) :
    HomologicalComplex.homologyMap F.shortMap.τ₁ n ≫
        HomologicalComplex.homologyMap D'.shortComplex.f n =
      HomologicalComplex.homologyMap D.shortComplex.f n ≫
        HomologicalComplex.homologyMap F.shortMap.τ₂ n := by
  rw [← HomologicalComplex.homologyMap_comp,
    F.shortMap.comm₁₂, HomologicalComplex.homologyMap_comp]

private theorem third_naturality
    {D : ConnesSBIPresentation (A := A)} {D' : ConnesSBIPresentation (A := A)}
    (F : D ⟶ D') (n : ℕ) :
    HomologicalComplex.homologyMap F.shortMap.τ₂ n ≫
        HomologicalComplex.homologyMap D'.shortComplex.g n =
      HomologicalComplex.homologyMap D.shortComplex.g n ≫
        HomologicalComplex.homologyMap F.shortMap.τ₃ n := by
  rw [← HomologicalComplex.homologyMap_comp,
    F.shortMap.comm₂₃, HomologicalComplex.homologyMap_comp]

@[reassoc]
theorem hIso_inv_naturality
    {D D' : ConnesSBIPresentation (A := A)}
    (F : D ⟶ D') (n : ℕ) :
    (D.hIso n).inv ≫ F.hMap n =
      HomologicalComplex.homologyMap F.shortMap.τ₁ n ≫ (D'.hIso n).inv := by
  let _ : QuasiIso D.ordinaryComparison := D.ordinaryComparisonQuasiIso
  let _ : QuasiIso D'.ordinaryComparison := D'.ordinaryComparisonQuasiIso
  simpa only [hMap, hIso] using
    HomologicalComplex.isoOfQuasiIsoAt_inv_naturality
      D.ordinaryComparison D'.ordinaryComparison F.ordinaryMap F.shortMap.τ₁ n
        F.ordinaryComparison_naturality

@[reassoc]
theorem tailHomologyIso_inv_naturality
    {D D' : ConnesSBIPresentation (A := A)}
    (F : D ⟶ D') (n : ℕ) :
    (D.tailHomologyIso n).inv ≫
        HomologicalComplex.homologyMap F.shortMap.τ₃ (n + 2) =
      F.hcMap n ≫ (D'.tailHomologyIso n).inv := by
  apply (cancel_mono (D'.tailHomologyIso n).hom).1
  calc
    ((D.tailHomologyIso n).inv ≫
        HomologicalComplex.homologyMap F.shortMap.τ₃ (n + 2)) ≫
          (D'.tailHomologyIso n).hom =
      (D.tailHomologyIso n).inv ≫
        (HomologicalComplex.homologyMap F.shortMap.τ₃ (n + 2) ≫
          (D'.tailHomologyIso n).hom) := Category.assoc _ _ _
    _ = (D.tailHomologyIso n).inv ≫
        ((D.tailHomologyIso n).hom ≫ F.hcMap n) := by
          rw [F.tailHomologyIso_hom_naturality]
    _ = F.hcMap n := by simp
    _ = (F.hcMap n ≫ (D'.tailHomologyIso n).inv) ≫
        (D'.tailHomologyIso n).hom := by simp

/-- The chain-level morphism induces a morphism of homology-level SBI
diagrams. -/
noncomputable def toSBIHom
    {D : ConnesSBIPresentation (A := A)} {D' : ConnesSBIPresentation (A := A)}
    (F : D ⟶ D') : D.sbiDiagram ⟶ D'.sbiDiagram where
  hMap n := F.hMap n
  hcMap n := F.hcMap n
  I_naturality n := by
    have hH := F.hIso_hom_naturality n
    dsimp only [hMap] at hH
    dsimp only [I, hMap, hcMap]
    simp only [Category.assoc]
    rw [← F.first_naturality n]
    simp only [← Category.assoc]
    rw [← hH]
  S_naturality n := by
    have hTail := F.tailHomologyIso_hom_naturality n
    dsimp only [hcMap] at hTail
    dsimp only [S, hcMap]
    simp only [Category.assoc]
    rw [← hTail]
    simp only [← Category.assoc]
    rw [← F.third_naturality (n + 2)]
  B_naturality n := by
    have hH := F.hIso_inv_naturality (n + 1)
    dsimp only [hMap] at hH
    have hTail := F.tailHomologyIso_inv_naturality n
    dsimp only [hcMap] at hTail
    dsimp only [B, hMap, hcMap]
    have hδ := HomologicalComplex.HomologySequence.δ_naturality
      F.shortMap D.shortExact D'.shortExact
      (n + 2) (n + 1) (by simp)
    simp only [Category.assoc]
    rw [hH, reassoc_of% hδ, reassoc_of% hTail]

@[simp]
theorem toSBIHom_id (D : ConnesSBIPresentation (A := A)) :
    (𝟙 D : D ⟶ D).toSBIHom = 𝟙 D.sbiDiagram := by
  apply NatSBIDiagram.hom_ext <;> intro n
  · simp only [toSBIHom, id_hMap,
      NatSBIDiagram.id_hMap]
  · simp only [toSBIHom, id_hcMap, NatSBIDiagram.id_hcMap]

@[simp]
theorem toSBIHom_comp {D D' D'' : ConnesSBIPresentation (A := A)}
    (F : D ⟶ D') (G : D' ⟶ D'') :
    (F ≫ G).toSBIHom = F.toSBIHom ≫ G.toSBIHom := by
  apply NatSBIDiagram.hom_ext <;> intro n
  · simp only [toSBIHom, comp_hMap,
      NatSBIDiagram.comp_hMap]
  · simp only [toSBIHom, comp_hcMap, NatSBIDiagram.comp_hcMap]

end Hom

/-- The homology-level SBI diagram of a chain-level presentation, functorially
in presentation morphisms. -/
@[simps, implicit_reducible]
def sbiDiagramFunctor :
    ConnesSBIPresentation (A := A) ⥤ NatSBIDiagram (A := A) where
  obj D := D.sbiDiagram
  map F := Hom.toSBIHom F
  map_id D := Hom.toSBIHom_id D
  map_comp F G := Hom.toSBIHom_comp F G

namespace Hom

/-- Bounded general SBI comparison.  Ordinary-homology isomorphisms
are needed only through the requested degree. -/
theorem isIso_hcMap_of_isIso_hMap_le
    {D : ConnesSBIPresentation (A := A)} {D' : ConnesSBIPresentation (A := A)}
    (F : D ⟶ D') (n : ℕ)
    (h : ∀ m : ℕ, m ≤ n → IsIso (F.hMap m)) :
    IsIso (F.hcMap n) := by
  have h' : ∀ m : ℕ, m ≤ n → IsIso (F.toSBIHom.hMap m) := by
    intro m hm
    simpa only [toSBIHom, hMap] using h m hm
  have hresult := F.toSBIHom.isIso_hcMap_of_isIso_hMap_le
    D.sbiDiagram_exact D'.sbiDiagram_exact
      D.sbiDiagram_connectiveBoundary D'.sbiDiagram_connectiveBoundary n h'
  simpa only [toSBIHom, hcMap] using hresult

/-- The general SBI comparison theorem. -/
theorem isIso_hcMap_of_isIso_hMap
    {D : ConnesSBIPresentation (A := A)} {D' : ConnesSBIPresentation (A := A)}
    (F : D ⟶ D')
    (h : ∀ n : ℕ, IsIso (F.hMap n))
    (n : ℕ) : IsIso (F.hcMap n) :=
  F.isIso_hcMap_of_isIso_hMap_le n (fun m _ => h m)

/-- A quasi-isomorphism on the preferred ordinary complexes induces a
quasi-isomorphism on the middle terms of the short exact sequences. -/
theorem quasiIso_shortMap_τ₂
    {D : ConnesSBIPresentation (A := A)} {D' : ConnesSBIPresentation (A := A)}
    (F : D ⟶ D') [QuasiIso F.ordinaryMap] : QuasiIso F.shortMap.τ₂ where
  quasiIsoAt n := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact F.isIso_hcMap_of_isIso_hMap (fun m => by
      dsimp only [hMap]
      infer_instance) n

end Hom

end ConnesSBIPresentation

end CategoryTheory

namespace CategoryTheory.ConnesSBIPresentation.Hom

variable {A : Type u} [Category.{w} A] [Abelian A]

/-- The preferred ordinary map is invertible in degree n when the HC maps
through degree n+1 are invertible. -/
theorem isIso_hMap_of_isIso_hcMap_le
    {D D' : ConnesSBIPresentation (A := A)} (F : D ⟶ D') (n : ℕ)
    (h : ∀ m : ℕ, m ≤ n + 1 → IsIso (F.hcMap m)) : IsIso (F.hMap n) := by
  have h' : ∀ m : ℕ, m ≤ n + 1 → IsIso (F.toSBIHom.hcMap m) := by
    intro m hm
    simpa only [toSBIHom, hcMap] using h m hm
  have hresult := F.toSBIHom.isIso_hMap_of_isIso_hcMap_le
    D.sbiDiagram_exact D'.sbiDiagram_exact
      D.sbiDiagram_connectiveBoundary D'.sbiDiagram_connectiveBoundary n h'
  simpa only [toSBIHom, hMap] using hresult

/-- Isomorphisms on the cyclic maps in every nonnegative degree imply
isomorphisms on the preferred ordinary maps. -/
theorem isIso_hMap_of_isIso_hcMap
    {D D' : ConnesSBIPresentation (A := A)} (F : D ⟶ D')
    (h : ∀ n : ℕ, IsIso (F.hcMap n)) (n : ℕ) : IsIso (F.hMap n) :=
  F.isIso_hMap_of_isIso_hcMap_le n (fun m _ => h m)

/-- The chain-level preferred ordinary map is a quasi-isomorphism when
the middle map is a quasi-isomorphism. -/
theorem quasiIso_ordinaryMap
    {D D' : ConnesSBIPresentation (A := A)} (F : D ⟶ D')
    [QuasiIso F.shortMap.τ₂] : QuasiIso F.ordinaryMap where
  quasiIsoAt n := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact F.isIso_hMap_of_isIso_hcMap (fun m => by
      dsimp only [hcMap]
      infer_instance) n

/-- The constructed connective SBI presentations detect the same actual
quasi-isomorphisms on ordinary and middle complexes. -/
theorem quasiIso_ordinaryMap_iff_shortMap_τ₂
    {D D' : ConnesSBIPresentation (A := A)} (F : D ⟶ D') :
    QuasiIso F.ordinaryMap ↔ QuasiIso F.shortMap.τ₂ := by
  constructor
  · intro h
    letI : QuasiIso F.ordinaryMap := h
    exact F.quasiIso_shortMap_τ₂
  · intro h
    letI : QuasiIso F.shortMap.τ₂ := h
    exact F.quasiIso_ordinaryMap

end CategoryTheory.ConnesSBIPresentation.Hom

namespace CategoryTheory.ConnesSBIPresentation

open Limits HomologicalComplex

universe uA wA

variable {A : Type uA} [Category.{wA} A] [Abelian A]

/-- The same original tail Iso computes the original cycle objects, using
native extension and degree-transport cycles coordinates. -/
noncomputable def tailCyclesComparison (D : ConnesSBIPresentation (A := A)) (n : ℕ) :
    D.shortComplex.X₃.cycles (n + 2) ⟶ D.shortComplex.X₂.cycles n := by
  let Q : ChainComplex A ℕ := D.shortComplex.X₃
  let T : ChainComplex A ℕ := D.shortComplex.X₂
  let Tz : ChainComplex A ℤ := T.extend (ComplexShape.embeddingDownNatToIntShift 2)
  let d₁ : ℤ := 0 + ((n + 2 : ℕ) : ℤ)
  let d₂ : ℤ := 2 + (n : ℤ)
  let h : d₁ = d₂ := by dsimp only [d₁, d₂]; omega
  exact (cyclesIsoExtendDownNatToIntShift Q 0 (n + 2)).inv ≫
    cyclesMap D.tailIso.hom d₁ ≫ (cyclesIsoOfEq Tz h).hom ≫
      (cyclesIsoExtendDownNatToIntShift T 2 n).hom

/-- The cycle comparison retains precisely the original chain tail component
and its original degree/extension coordinate maps. -/
@[reassoc]
theorem tailCyclesComparison_iCycles (D : ConnesSBIPresentation (A := A)) (n : ℕ) :
    D.tailCyclesComparison n ≫ D.shortComplex.X₂.iCycles n =
      D.shortComplex.X₃.iCycles (n + 2) ≫
        (D.shortComplex.X₃.extendXIso (ComplexShape.embeddingDownNatToIntShift 0) rfl).inv ≫
          D.tailIso.hom.f (0 + ((n + 2 : ℕ) : ℤ)) ≫
            ((D.shortComplex.X₂.extend (ComplexShape.embeddingDownNatToIntShift 2)).XIsoOfEq
              (by omega : (0 : ℤ) + ((n + 2 : ℕ) : ℤ) = 2 + (n : ℤ))).hom ≫
                (extendDownNatToIntShiftXIso D.shortComplex.X₂ 2 n).hom := by
  let Q : ChainComplex A ℕ := D.shortComplex.X₃
  let T : ChainComplex A ℕ := D.shortComplex.X₂
  let Qz : ChainComplex A ℤ := Q.extend (ComplexShape.embeddingDownNatToIntShift 0)
  let Tz : ChainComplex A ℤ := T.extend (ComplexShape.embeddingDownNatToIntShift 2)
  let d₁ : ℤ := 0 + ((n + 2 : ℕ) : ℤ)
  let d₂ : ℤ := 2 + (n : ℤ)
  let h : d₁ = d₂ := by dsimp only [d₁, d₂]; omega
  let cQ : Qz.cycles d₁ ≅ Q.cycles (n + 2) :=
    cyclesIsoExtendDownNatToIntShift Q 0 (n + 2)
  let cD : Tz.cycles d₁ ≅ Tz.cycles d₂ := cyclesIsoOfEq Tz h
  let cT : Tz.cycles d₂ ≅ T.cycles n := cyclesIsoExtendDownNatToIntShift T 2 n
  let eQ : Qz.X d₁ ≅ Q.X (n + 2) :=
    Q.extendXIso (ComplexShape.embeddingDownNatToIntShift 0)
      (rfl : (ComplexShape.embeddingDownNatToIntShift 0).f (n + 2) = d₁)
  let eD : Tz.X d₁ ≅ Tz.X d₂ := Tz.XIsoOfEq h
  let eT : Tz.X d₂ ≅ T.X n := extendDownNatToIntShiftXIso T 2 n
  let f : Qz ⟶ Tz := D.tailIso.hom
  have hQ : cQ.inv ≫ Qz.iCycles d₁ = Q.iCycles (n + 2) ≫ eQ.inv := by
    change (Q.extendCyclesIso (ComplexShape.embeddingDownNatToIntShift 0) rfl).inv ≫
      Qz.iCycles d₁ = Q.iCycles (n + 2) ≫
        (Q.extendXIso (ComplexShape.embeddingDownNatToIntShift 0) rfl).inv
    exact Q.extendCyclesIso_inv_iCycles (ComplexShape.embeddingDownNatToIntShift 0) rfl
  have hT : cT.hom ≫ T.iCycles n = Tz.iCycles d₂ ≫ eT.hom := by
    change (T.extendCyclesIso (ComplexShape.embeddingDownNatToIntShift 2) rfl).hom ≫
      T.iCycles n = Tz.iCycles d₂ ≫
        (T.extendXIso (ComplexShape.embeddingDownNatToIntShift 2) rfl).hom
    exact T.extendCyclesIso_hom_iCycles (ComplexShape.embeddingDownNatToIntShift 2) rfl
  have hD : cD.hom ≫ Tz.iCycles d₂ = Tz.iCycles d₁ ≫ eD.hom :=
    cyclesIsoOfEq_hom_iCycles Tz h
  have hMap : cyclesMap f d₁ ≫ Tz.iCycles d₁ = Qz.iCycles d₁ ≫ f.f d₁ :=
    cyclesMap_i f d₁
  change (cQ.inv ≫ cyclesMap f d₁ ≫ cD.hom ≫ cT.hom) ≫ T.iCycles n =
    Q.iCycles (n + 2) ≫ eQ.inv ≫ f.f d₁ ≫ eD.hom ≫ eT.hom
  calc
    _ = cQ.inv ≫ cyclesMap f d₁ ≫ cD.hom ≫ (cT.hom ≫ T.iCycles n) := by
      simp only [Category.assoc]
    _ = cQ.inv ≫ cyclesMap f d₁ ≫ cD.hom ≫ (Tz.iCycles d₂ ≫ eT.hom) := by rw [hT]
    _ = cQ.inv ≫ cyclesMap f d₁ ≫ (cD.hom ≫ Tz.iCycles d₂) ≫ eT.hom := by
      simp only [Category.assoc]
    _ = cQ.inv ≫ cyclesMap f d₁ ≫ (Tz.iCycles d₁ ≫ eD.hom) ≫ eT.hom := by rw [hD]
    _ = cQ.inv ≫ (cyclesMap f d₁ ≫ Tz.iCycles d₁) ≫ eD.hom ≫ eT.hom := by
      simp only [Category.assoc]
    _ = cQ.inv ≫ (Qz.iCycles d₁ ≫ f.f d₁) ≫ eD.hom ≫ eT.hom := by rw [hMap]
    _ = (cQ.inv ≫ Qz.iCycles d₁) ≫ f.f d₁ ≫ eD.hom ≫ eT.hom := by
      simp only [Category.assoc]
    _ = (Q.iCycles (n + 2) ≫ eQ.inv) ≫ f.f d₁ ≫ eD.hom ≫ eT.hom := by rw [hQ]
    _ = _ := by simp only [Category.assoc]

/-- The homology map of the original tail Iso retains the same actual cycle
comparison, rather than supplying a separate desired homology result. -/
@[reassoc]
theorem homologyπ_tailHomologyIso_hom (D : ConnesSBIPresentation (A := A)) (n : ℕ) :
    D.shortComplex.X₃.homologyπ (n + 2) ≫ (D.tailHomologyIso n).hom =
      D.tailCyclesComparison n ≫ D.shortComplex.X₂.homologyπ n := by
  let Q : ChainComplex A ℕ := D.shortComplex.X₃
  let T : ChainComplex A ℕ := D.shortComplex.X₂
  let Qz : ChainComplex A ℤ := Q.extend (ComplexShape.embeddingDownNatToIntShift 0)
  let Tz : ChainComplex A ℤ := T.extend (ComplexShape.embeddingDownNatToIntShift 2)
  let d₁ : ℤ := 0 + ((n + 2 : ℕ) : ℤ)
  let d₂ : ℤ := 2 + (n : ℤ)
  let h : d₁ = d₂ := by dsimp only [d₁, d₂]; omega
  have hQ : Q.homologyπ (n + 2) ≫ (homologyIsoExtendDownNatToIntShift Q 0 (n + 2)).inv =
      (cyclesIsoExtendDownNatToIntShift Q 0 (n + 2)).inv ≫ Qz.homologyπ d₁ := by
    change Q.homologyπ (n + 2) ≫
      (Q.extendHomologyIso (ComplexShape.embeddingDownNatToIntShift 0) rfl).inv =
        (Q.extendCyclesIso (ComplexShape.embeddingDownNatToIntShift 0) rfl).inv ≫ Qz.homologyπ d₁
    exact Q.homologyπ_extendHomologyIso_inv (ComplexShape.embeddingDownNatToIntShift 0) rfl
  have hT : Tz.homologyπ d₂ ≫ (homologyIsoExtendDownNatToIntShift T 2 n).hom =
      (cyclesIsoExtendDownNatToIntShift T 2 n).hom ≫ T.homologyπ n := by
    change Tz.homologyπ d₂ ≫
      (T.extendHomologyIso (ComplexShape.embeddingDownNatToIntShift 2) rfl).hom =
        (T.extendCyclesIso (ComplexShape.embeddingDownNatToIntShift 2) rfl).hom ≫ T.homologyπ n
    exact T.homologyπ_extendHomologyIso_hom (ComplexShape.embeddingDownNatToIntShift 2) rfl
  have hD : Tz.homologyπ d₁ ≫ (homologyIsoOfEq Tz h).hom =
      (cyclesIsoOfEq Tz h).hom ≫ Tz.homologyπ d₂ := homologyπ_comp_homologyIsoOfEq_hom Tz h
  have hMap : Qz.homologyπ d₁ ≫ homologyMap D.tailIso.hom d₁ =
      cyclesMap D.tailIso.hom d₁ ≫ Tz.homologyπ d₁ := homologyπ_naturality D.tailIso.hom d₁
  simp only [tailCyclesComparison, Category.assoc]
  change Q.homologyπ (n + 2) ≫
      (homologyIsoExtendDownNatToIntShift Q 0 (n + 2)).inv ≫
        homologyMap D.tailIso.hom d₁ ≫ (homologyIsoOfEq Tz h).hom ≫
          (homologyIsoExtendDownNatToIntShift T 2 n).hom =
    (cyclesIsoExtendDownNatToIntShift Q 0 (n + 2)).inv ≫
      cyclesMap D.tailIso.hom d₁ ≫ (cyclesIsoOfEq Tz h).hom ≫
        (cyclesIsoExtendDownNatToIntShift T 2 n).hom ≫ T.homologyπ n
  rw [reassoc_of% hQ, reassoc_of% hMap, reassoc_of% hD, hT]

end CategoryTheory.ConnesSBIPresentation
