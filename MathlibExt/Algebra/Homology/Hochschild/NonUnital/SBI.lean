/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Cyclic
public import MathlibExt.Algebra.Homology.PartialTotalCokernel
public import MathlibExt.Algebra.Homology.PartialTotalCoordinates
public import MathlibExt.Algebra.Homology.PartialTotalEvenTail
public import MathlibExt.Algebra.Homology.ConnesSBI
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Embedding.Restriction
public import Mathlib.Algebra.Homology.Embedding.Extend

/-!
# The two-column cyclic SBI presentation

The Hochschild term in this presentation is
the total of the first two cyclic bicomplex
columns, CC(A){2}. Its inclusion, cokernel
and period-two tail comparison give an
SBI presentation for nonunital algebra maps.
Comparison with the b complex requires a
left unit. The relative-unitization cokernel
Hochschild model is a separate definition.

Reference: Loday, Cyclic Homology, §§1.4.1,
1.4.5 and Theorem 2.2.1.
-/

@[expose] public section
noncomputable section

open CategoryTheory Category Limits HomologicalComplex HomologicalComplex₂
open ModuleCat.Algebra.Hochschild.NonUnital
open scoped TensorProduct

universe u v

namespace ModuleCat.Algebra.Hochschild

theorem cyclicColumn_two_parity (p : ℕ) : Even (p + 2) ↔ Even p := by
  rw [show p + 2 = (p + 1) + 1 by omega, Nat.even_add_one, Nat.even_add_one,
    not_not]

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- The literal native total of the first two raw cyclic columns. -/
abbrev cyclicFirstTwoColumns : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  (cyclicBicomplex k A).partialTotal 1

/-- The raw cyclic-total quotient by the first two columns. -/
abbrev cyclicTwoColumnTail : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  cokernel ((cyclicBicomplex k A).partialTotalι 1)

/-- The chain-level inclusion/cokernel sequence whose homology gives raw SBI. -/
abbrev cyclicTwoColumnSequence : ShortComplex (ChainComplex (ModuleCat.{max u v} k) ℕ) :=
  (cyclicBicomplex k A).partialTotalCokernelShortComplex 1

/-- Its middle complex is the original cyclic total. -/
lemma cyclicTwoColumnSequence_X₂ :
    (cyclicTwoColumnSequence k A).X₂ = cyclicTotal k A := rfl

/-- Its first term retains both raw columns. -/
lemma cyclicTwoColumnSequence_X₁ :
    (cyclicTwoColumnSequence k A).X₁ = cyclicFirstTwoColumns k A := rfl

/-- The third term is the quotient, rather than a chosen comparison object. -/
lemma cyclicTwoColumnSequence_X₃ :
    (cyclicTwoColumnSequence k A).X₃ = cyclicTwoColumnTail k A := rfl

/-- Short exactness is the native partial-total inclusion/cokernel theorem. -/
theorem cyclicTwoColumnSequence_shortExact :
    (cyclicTwoColumnSequence k A).ShortExact :=
  (cyclicBicomplex k A).partialTotalCokernelShortExact 1

/-- Canonical coordinate of either retained raw column, including the odd column. -/
def cyclicFirstTwoColumnCell (p : Fin 2) (q n : ℕ) (h : p.val + q = n) :
    ModuleCat.Algebra.Hochschild.NonUnital.chainLevel k A A q ⟶ (cyclicFirstTwoColumns k A).X n :=
  (cyclicBicomplex k A).partialTotalComponent 1 p q n h

/-- The retained cell includes as its full-total coprojection. -/
@[reassoc]
theorem cyclicFirstTwoColumnCell_inclusion (p : Fin 2) (q n : ℕ)
    (h : p.val + q = n) :
    cyclicFirstTwoColumnCell k A p q n h ≫
        (cyclicTwoColumnSequence k A).f.f n =
      (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) p.val q n h :=
  (cyclicBicomplex k A).partialTotalComponent_comp_partialTotalι 1 p q n h

/-- Both retained columns vanish under the quotient projection. -/
@[reassoc]
theorem cyclicTwoColumnProjection_retained (p : Fin 2) (q n : ℕ)
    (h : p.val + q = n) :
    (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) p.val q n h ≫
        (cyclicTwoColumnSequence k A).g.f n = 0 :=
  (cyclicBicomplex k A).ιTotal_cokernel_partialTotalι_π_eq_zero
    1 p.val q n p.isLt h

/-- The period-two column comparison has identity maps on original tensor levels. -/
def cyclicColumnPeriodTwoIso (p : ℕ) : cyclicColumn k A (p + 2) ≅ cyclicColumn k A p :=
  HomologicalComplex.Hom.isoOfComponents (fun q => Iso.refl (ModuleCat.Algebra.Hochschild.NonUnital.chainLevel k A A q))
    (fun i j _ => by
      change (𝟙 _) ≫
          (if Even p then (bComplex k A).d i j else (bPrimeComplex k A).d i j) =
        (if Even (p + 2) then (bComplex k A).d i j else (bPrimeComplex k A).d i j) ≫
          (𝟙 _)
      simp only [Category.id_comp, Category.comp_id, cyclicColumn_two_parity])

/-- The forward period-two coordinate is the original identity tensor map. -/
lemma cyclicColumnPeriodTwoIso_hom_f (p q : ℕ) :
    (cyclicColumnPeriodTwoIso k A p).hom.f q = 𝟙 (ModuleCat.Algebra.Hochschild.NonUnital.chainLevel k A A q) := rfl

/-- The inverse period-two coordinate is the same original identity tensor map. -/
lemma cyclicColumnPeriodTwoIso_inv_f (p q : ℕ) :
    (cyclicColumnPeriodTwoIso k A p).inv.f q = 𝟙 (ModuleCat.Algebra.Hochschild.NonUnital.chainLevel k A A q) := rfl

/-- Native restriction drops two outer columns without introducing a parallel bicomplex. -/
def cyclicOuterTailTwoIso :
    (cyclicBicomplex k A).restriction (_root_.partialTotalOuterEmbedding 2) ≅
      cyclicBicomplex k A :=
  HomologicalComplex.Hom.isoOfComponents (fun p => cyclicColumnPeriodTwoIso k A p)
    (fun i j hij => by
      have hi : j + 1 = i := hij
      subst i
      apply HomologicalComplex.hom_ext
      intro q
      let R := cyclicBicomplex k A
      let L := R.restriction (_root_.partialTotalOuterEmbedding 2)
      let X : ModuleCat.{max u v} k := NonUnital.chainLevel k A A q
      let a : X ⟶ X := (cyclicColumnPeriodTwoIso k A (j + 1)).hom.f q
      let c : X ⟶ X := (cyclicColumnPeriodTwoIso k A j).hom.f q
      let d : X ⟶ X := (R.d (j + 1) j).f q
      let d' : X ⟶ X := (L.d (j + 1) j).f q
      have ha : a = 𝟙 X := cyclicColumnPeriodTwoIso_hom_f k A (j + 1) q
      have hc : c = 𝟙 X := cyclicColumnPeriodTwoIso_hom_f k A j q
      have hd : d = if Even j then 𝟙 X - cyclicMap k A q else normMap k A q :=
        cyclicBicomplex_horizontal k A j q
      have hd' : d' = if Even (j + 2) then 𝟙 X - cyclicMap k A q else normMap k A q := by
        change ((cyclicBicomplex k A).d ((j + 2) + 1) (j + 2)).f q = _
        exact cyclicBicomplex_horizontal k A (j + 2) q
      have hdd : d = d' := by
        rw [hd, hd']
        simp only [cyclicColumn_two_parity]
      change a ≫ d = d' ≫ c
      exact (congrArg (fun f : X ⟶ X => f ≫ d) ha).trans
        ((Category.id_comp d).trans (hdd.trans
          ((Category.comp_id d').symm.trans
            (congrArg (fun f : X ⟶ X => d' ≫ f) hc.symm)))))

/-- The period-two bicomplex map preserves every literal tensor cell. -/
lemma cyclicOuterTailTwoIso_hom_f_f (p q : ℕ) :
    ((cyclicOuterTailTwoIso k A).hom.f p).f q = 𝟙 (ModuleCat.Algebra.Hochschild.NonUnital.chainLevel k A A q) := rfl

/-- Its inverse preserves those same literal tensor cells. -/
lemma cyclicOuterTailTwoIso_inv_f_f (p q : ℕ) :
    ((cyclicOuterTailTwoIso k A).inv.f p).f q = 𝟙 (ModuleCat.Algebra.Hochschild.NonUnital.chainLevel k A A q) := rfl

section Maps

variable {k A} {B : Type v} [NonUnitalRing B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- The original nonunital map acts on all three chain-level terms. -/
def cyclicTwoColumnSequenceMap (f : A →ₙₐ[k] B) :
    cyclicTwoColumnSequence k A ⟶ cyclicTwoColumnSequence k B :=
  partialTotalCokernelShortComplexMap (cyclicBicomplexHom f) 1

/-- The first component is the native partial-total map, retaining both columns. -/
lemma cyclicTwoColumnSequenceMap_τ₁ (f : A →ₙₐ[k] B) :
    (cyclicTwoColumnSequenceMap f).τ₁ =
      (cyclicBicomplex k A).partialTotalHom (cyclicBicomplexHom f) 1 := rfl

/-- The middle component is the original cyclic-total map. -/
lemma cyclicTwoColumnSequenceMap_τ₂ (f : A →ₙₐ[k] B) :
    (cyclicTwoColumnSequenceMap f).τ₂ =
      HomologicalComplex₂.total.map (cyclicBicomplexHom f) (ComplexShape.down ℕ) := rfl

/-- The third component is the cokernel map. -/
lemma cyclicTwoColumnSequenceMap_τ₃ (f : A →ₙₐ[k] B) :
    (cyclicTwoColumnSequenceMap f).τ₃ =
      partialTotalCokernelMap (cyclicBicomplexHom f) 1 := rfl

/-- The two-column map acts by the original tensor map on each retained cell. -/
@[reassoc]
theorem cyclicFirstTwoColumnCell_naturality (f : A →ₙₐ[k] B)
    (p : Fin 2) (q n : ℕ) (h : p.val + q = n) :
    cyclicFirstTwoColumnCell k A p q n h ≫
        (cyclicTwoColumnSequenceMap f).τ₁.f n =
      ModuleCat.ofHom (TensorPower.consLevelMap (f : A →ₗ[k] B) q) ≫
        cyclicFirstTwoColumnCell k B p q n h := by
  rw [cyclicTwoColumnSequenceMap_τ₁]
  exact ((cyclicBicomplex k A).partialTotalComponent_naturality
    (cyclicBicomplexHom f) 1 p q n h).trans
      (congrArg (fun m => m ≫ cyclicFirstTwoColumnCell k B p q n h)
        (cyclicBicomplexHom_f_f f p.val q))

/-- Naturality of the raw inclusion. -/
@[reassoc]
theorem cyclicTwoColumnInclusion_naturality (f : A →ₙₐ[k] B) :
    (cyclicTwoColumnSequenceMap f).τ₁ ≫ (cyclicTwoColumnSequence k B).f =
      (cyclicTwoColumnSequence k A).f ≫ (cyclicTwoColumnSequenceMap f).τ₂ :=
  (cyclicTwoColumnSequenceMap f).comm₁₂

/-- Naturality of the raw quotient projection. -/
@[reassoc]
theorem cyclicTwoColumnProjection_naturality (f : A →ₙₐ[k] B) :
    (cyclicTwoColumnSequenceMap f).τ₂ ≫ (cyclicTwoColumnSequence k B).g =
      (cyclicTwoColumnSequence k A).g ≫ (cyclicTwoColumnSequenceMap f).τ₃ :=
  (cyclicTwoColumnSequenceMap f).comm₂₃

/-- The original nonunital identity induces the identity on the entire sequence. -/
lemma cyclicTwoColumnSequenceMap_id :
    cyclicTwoColumnSequenceMap (NonUnitalAlgHom.id k A) =
      𝟙 (cyclicTwoColumnSequence k A) := by
  rw [cyclicTwoColumnSequenceMap, cyclicBicomplexHom_id]
  exact partialTotalCokernelShortComplexMap_id (cyclicBicomplex k A) 1

variable {D : Type v} [NonUnitalRing D] [Module k D]
  [IsScalarTower k D D] [SMulCommClass k D D]

/-- The whole chain-level sequence map composes in the original nonunital-map order. -/
lemma cyclicTwoColumnSequenceMap_comp (f : A →ₙₐ[k] B) (g : B →ₙₐ[k] D) :
    cyclicTwoColumnSequenceMap (g.comp f) =
      cyclicTwoColumnSequenceMap f ≫ cyclicTwoColumnSequenceMap g := by
  rw [cyclicTwoColumnSequenceMap, cyclicBicomplexHom_comp]
  exact partialTotalCokernelShortComplexMap_comp (cyclicBicomplexHom f)
    (cyclicBicomplexHom g) 1

/-- The canonical outer period-two comparison commutes with the nonunital map. -/
@[reassoc]
theorem cyclicOuterTailTwoIso_naturality (f : A →ₙₐ[k] B) :
    HomologicalComplex.restrictionMap (cyclicBicomplexHom f)
        (_root_.partialTotalOuterEmbedding 2) ≫ (cyclicOuterTailTwoIso k B).hom =
      (cyclicOuterTailTwoIso k A).hom ≫ cyclicBicomplexHom f := by
  apply HomologicalComplex.hom_ext
  intro p
  apply HomologicalComplex.hom_ext
  intro q
  let X : ModuleCat.{max u v} k := NonUnital.chainLevel k A A q
  let Y : ModuleCat.{max u v} k := NonUnital.chainLevel k B B q
  let a : X ⟶ Y := ((cyclicBicomplexHom f).f (p + 2)).f q
  let b : X ⟶ Y := ((cyclicBicomplexHom f).f p).f q
  let eA : X ⟶ X := ((cyclicOuterTailTwoIso k A).hom.f p).f q
  let eB : Y ⟶ Y := ((cyclicOuterTailTwoIso k B).hom.f p).f q
  have ha : a = ModuleCat.ofHom (TensorPower.consLevelMap (f : A →ₗ[k] B) q) :=
    cyclicBicomplexHom_f_f f (p + 2) q
  have hb : b = ModuleCat.ofHom (TensorPower.consLevelMap (f : A →ₗ[k] B) q) :=
    cyclicBicomplexHom_f_f f p q
  have heA : eA = 𝟙 X := cyclicOuterTailTwoIso_hom_f_f k A p q
  have heB : eB = 𝟙 Y := cyclicOuterTailTwoIso_hom_f_f k B p q
  change a ≫ eB = eA ≫ b
  exact (congrArg (fun e : Y ⟶ Y => a ≫ e) heB).trans
    ((Category.comp_id a).trans ((ha.trans hb.symm).trans
      ((Category.id_comp b).symm.trans (congrArg (fun e : X ⟶ X => e ≫ b) heA.symm))))

end Maps

end ModuleCat.Algebra.Hochschild

namespace ModuleCat.Algebra.Hochschild

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- The quotient by two raw columns is the original cyclic total zero-extended
by two Nat degrees. Its maps retain the native total sign and the original period map. -/
def cyclicTwoColumnTailNatIso :
    cyclicTwoColumnTail k A ≅
      (cyclicTotal k A).extend (_root_.partialTotalOuterEmbedding 2) :=
  firstTwoColumnCokernelTailIso (cyclicBicomplex k A) ≪≫
    ((_root_.partialTotalOuterEmbedding 2).extendFunctor
      (ModuleCat.{max u v} k)).mapIso
        ((totalFunctor (ModuleCat.{max u v} k) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ) (ComplexShape.down ℕ)).mapIso (cyclicOuterTailTwoIso k A))

/-- The tail complex has no terms before the two-column offset. -/
theorem isZero_cyclicTwoColumnTail_X (n : ℕ) (hn : n < 2) :
    IsZero ((cyclicTwoColumnTail k A).X n) := by
  let e := _root_.partialTotalOuterEmbedding 2
  have hZero : IsZero (((cyclicTotal k A).extend e).X n) :=
    (cyclicTotal k A).isZero_extend_X e n (by
      intro i hi
      change i + 2 = n at hi
      omega)
  exact hZero.of_iso
    ((HomologicalComplex.eval (ModuleCat.{max u v} k) (ComplexShape.down ℕ) n).mapIso
      (cyclicTwoColumnTailNatIso k A))

/-- The computed tail comparison in the integer degrees used by the native SBI engine. -/
def cyclicTwoColumnTailIso :
    (cyclicTwoColumnTail k A).extend (ComplexShape.embeddingDownNatToIntShift 0) ≅
      (cyclicTotal k A).extend (ComplexShape.embeddingDownNatToIntShift 2) :=
  ((ComplexShape.embeddingDownNatToIntShift 0).extendFunctor
      (ModuleCat.{max u v} k)).mapIso (cyclicTwoColumnTailNatIso k A) ≪≫
    HomologicalComplex.extendNatAddIntIso (cyclicTotal k A) 2

/-- The raw cyclic bicomplex supplies the chain-level SBI presentation.
The ordinary term is the total of the first two columns, with no unitality premise. -/
def cyclicConnesSBIPresentation :
    CategoryTheory.ConnesSBIPresentation (A := ModuleCat.{max u v} k) where
  ordinary := cyclicFirstTwoColumns k A
  shortComplex := cyclicTwoColumnSequence k A
  shortExact := cyclicTwoColumnSequence_shortExact k A
  ordinaryComparison := 𝟙 (cyclicFirstTwoColumns k A)
  ordinaryComparisonQuasiIso := inferInstance
  tailIso := cyclicTwoColumnTailIso k A

/-- The homology of the first two raw columns, the `CC(A){2}` HH
presentation specified in Loday 2.2.1 (printed p. 61 / PDF page 76). -/
abbrev cyclicRawHochschildHomology (n : ℕ) : ModuleCat.{max u v} k :=
  (cyclicFirstTwoColumns k A).homology n

/-- The inclusion of the raw Hochschild term into cyclic homology. -/
abbrev cyclicSBIInclusion (n : ℕ) :
    cyclicRawHochschildHomology k A n ⟶ cyclicHomology k A n :=
  (cyclicConnesSBIPresentation k A).I n

/-- Periodicity is the original quotient map followed by the computed two-column translation. -/
abbrev cyclicSBIPeriodicity (n : ℕ) : cyclicHomology k A (n + 2) ⟶ cyclicHomology k A n :=
  (cyclicConnesSBIPresentation k A).S n

/-- The LES connecting morphism of the raw two-column sequence. -/
abbrev cyclicSBIConnecting (n : ℕ) :
    cyclicHomology k A n ⟶ cyclicRawHochschildHomology k A (n + 1) :=
  (cyclicConnesSBIPresentation k A).B n

theorem cyclicConnes_hIso_hom (n : ℕ) :
    ((cyclicConnesSBIPresentation k A).hIso n).hom =
      𝟙 (cyclicRawHochschildHomology k A n) := by
  have hDef : ((cyclicConnesSBIPresentation k A).hIso n).hom =
      HomologicalComplex.homologyMap (𝟙 (cyclicFirstTwoColumns k A)) n := rfl
  exact hDef.trans (HomologicalComplex.homologyMap_id (cyclicFirstTwoColumns k A) n)

theorem cyclicConnes_hIso_inv (n : ℕ) :
    ((cyclicConnesSBIPresentation k A).hIso n).inv =
      𝟙 (cyclicRawHochschildHomology k A n) := by
  let X : ModuleCat.{max u v} k := cyclicRawHochschildHomology k A n
  let E : X ≅ X := (cyclicConnesSBIPresentation k A).hIso n
  have hE : E.hom = 𝟙 X := cyclicConnes_hIso_hom k A n
  apply (cancel_mono E.hom).1
  exact E.inv_hom_id.trans ((Category.id_comp E.hom).trans hE).symm

/-- The raw SBI inclusion is the homology map of the original two-column inclusion. -/
theorem cyclicSBIInclusion_eq_homologyMap (n : ℕ) :
    cyclicSBIInclusion k A n =
      HomologicalComplex.homologyMap (cyclicTwoColumnSequence k A).f n := by
  let X : ModuleCat.{max u v} k := cyclicRawHochschildHomology k A n
  let E : X ≅ X := (cyclicConnesSBIPresentation k A).hIso n
  let f : X ⟶ cyclicHomology k A n := HomologicalComplex.homologyMap (cyclicTwoColumnSequence k A).f n
  have hE : E.hom = 𝟙 X := cyclicConnes_hIso_hom k A n
  change E.hom ≫ f = f
  exact (congrArg (fun e : X ⟶ X => e ≫ f) hE).trans (Category.id_comp f)

/-- The raw connecting map retains the LES boundary and translated inverse. -/
theorem cyclicSBIConnecting_eq_δ (n : ℕ) :
    cyclicSBIConnecting k A n =
      ((cyclicConnesSBIPresentation k A).tailHomologyIso n).inv ≫
        (cyclicTwoColumnSequence_shortExact k A).δ (n + 2) (n + 1) (by simp) := by
  let X : ModuleCat.{max u v} k := cyclicRawHochschildHomology k A (n + 1)
  let E : X ≅ X := (cyclicConnesSBIPresentation k A).hIso (n + 1)
  let f : cyclicHomology k A n ⟶ X :=
    ((cyclicConnesSBIPresentation k A).tailHomologyIso n).inv ≫
      (cyclicTwoColumnSequence_shortExact k A).δ (n + 2) (n + 1) (by simp)
  have hE : E.inv = 𝟙 X := cyclicConnes_hIso_inv k A (n + 1)
  change f ≫ E.inv = f
  exact (congrArg (fun e : X ⟶ X => f ≫ e) hE).trans (Category.comp_id f)

/-- The SBI diagram computed from the raw cyclic bicomplex. -/
abbrev cyclicSBIDiagram : CategoryTheory.NatSBIDiagram (A := ModuleCat.{max u v} k) :=
  (cyclicConnesSBIPresentation k A).sbiDiagram

/-- Exactness of every term follows from the native LES of the short exact sequence. -/
theorem cyclicSBIDiagram_exact : (cyclicSBIDiagram k A).Exact :=
  (cyclicConnesSBIPresentation k A).sbiDiagram_exact

/-- The low-degree boundary conditions use the vanishing of the quotient tail. -/
theorem cyclicSBIDiagram_connectiveBoundary : (cyclicSBIDiagram k A).ConnectiveBoundary :=
  (cyclicConnesSBIPresentation k A).sbiDiagram_connectiveBoundary

/-- The degree-zero raw Hochschild inclusion is an isomorphism. -/
theorem cyclicSBIInclusion_isIso_zero : IsIso (cyclicSBIInclusion k A 0) :=
  (cyclicConnesSBIPresentation k A).isIso_I_zero

/-- The degree-one raw Hochschild inclusion is epic, without a unitality premise. -/
theorem cyclicSBIInclusion_epi_one : Epi (cyclicSBIInclusion k A 1) :=
  (cyclicConnesSBIPresentation k A).epi_I_one

section PresentationMaps

variable {k A} {B : Type v} [NonUnitalRing B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- The Nat-tail quotient comparison commutes with original nonunital algebra maps. -/
@[reassoc]
theorem cyclicTwoColumnTailNatIso_hom_naturality (f : A →ₙₐ[k] B) :
    partialTotalCokernelMap (cyclicBicomplexHom f) 1 ≫ (cyclicTwoColumnTailNatIso k B).hom =
      (cyclicTwoColumnTailNatIso k A).hom ≫
        HomologicalComplex.extendMap
          (total.map (cyclicBicomplexHom f) (ComplexShape.down ℕ))
          (_root_.partialTotalOuterEmbedding 2) := by
  let C := ModuleCat.{max u v} k
  let R : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) := cyclicBicomplex k A
  let T : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) := cyclicBicomplex k B
  let F : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) ⥤ ChainComplex C ℕ :=
    totalFunctor C (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
  let e : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) := _root_.partialTotalOuterEmbedding 2
  let ψ : R ⟶ T := cyclicBicomplexHom f
  let ψTail : R.restriction e ⟶ T.restriction e := HomologicalComplex.restrictionMap ψ e
  let aA : cyclicTwoColumnTail k A ≅ (F.obj (R.restriction e)).extend e := firstTwoColumnCokernelTailIso R
  let aB : cyclicTwoColumnTail k B ≅ (F.obj (T.restriction e)).extend e := firstTwoColumnCokernelTailIso T
  let pA : F.obj (R.restriction e) ≅ cyclicTotal k A := F.mapIso (cyclicOuterTailTwoIso k A)
  let pB : F.obj (T.restriction e) ≅ cyclicTotal k B := F.mapIso (cyclicOuterTailTwoIso k B)
  let bA : (F.obj (R.restriction e)).extend e ≅ (cyclicTotal k A).extend e := (e.extendFunctor C).mapIso pA
  let bB : (F.obj (T.restriction e)).extend e ≅ (cyclicTotal k B).extend e := (e.extendFunctor C).mapIso pB
  have ha : partialTotalCokernelMap ψ 1 ≫ aB.hom =
      aA.hom ≫ HomologicalComplex.extendMap (F.map ψTail) e :=
    firstTwoColumnCokernelTailIso_hom_naturality ψ
  have hp : F.map ψTail ≫ pB.hom = pA.hom ≫ F.map ψ := by
    change F.map ψTail ≫ F.map (cyclicOuterTailTwoIso k B).hom =
      F.map (cyclicOuterTailTwoIso k A).hom ≫ F.map ψ
    erw [← F.map_comp, cyclicOuterTailTwoIso_naturality, F.map_comp]
  have hb : HomologicalComplex.extendMap (F.map ψTail) e ≫ bB.hom =
      bA.hom ≫ HomologicalComplex.extendMap (F.map ψ) e := by
    change HomologicalComplex.extendMap (F.map ψTail) e ≫
        HomologicalComplex.extendMap pB.hom e =
      HomologicalComplex.extendMap pA.hom e ≫ HomologicalComplex.extendMap (F.map ψ) e
    erw [← HomologicalComplex.extendMap_comp, hp, HomologicalComplex.extendMap_comp]
    rfl
  change partialTotalCokernelMap ψ 1 ≫ (aB.hom ≫ bB.hom) =
    (aA.hom ≫ bA.hom) ≫ HomologicalComplex.extendMap (F.map ψ) e
  have hFirst : partialTotalCokernelMap ψ 1 ≫ (aB.hom ≫ bB.hom) =
      (aA.hom ≫ HomologicalComplex.extendMap (F.map ψTail) e) ≫ bB.hom :=
    (Category.assoc (partialTotalCokernelMap ψ 1) aB.hom bB.hom).symm.trans
      (congrArg (fun g : cyclicTwoColumnTail k A ⟶ (F.obj (T.restriction e)).extend e =>
        g ≫ bB.hom) ha)
  have hSecond : (aA.hom ≫ HomologicalComplex.extendMap (F.map ψTail) e) ≫ bB.hom =
      aA.hom ≫ (bA.hom ≫ HomologicalComplex.extendMap (F.map ψ) e) :=
    (Category.assoc aA.hom (HomologicalComplex.extendMap (F.map ψTail) e) bB.hom).trans
      (congrArg (fun g : (F.obj (R.restriction e)).extend e ⟶ (cyclicTotal k B).extend e =>
        aA.hom ≫ g) hb)
  exact hFirst.trans (hSecond.trans
    (Category.assoc aA.hom bA.hom (HomologicalComplex.extendMap (F.map ψ) e)).symm)

/-- The computed integer tail comparison retains original algebra-map naturality. -/
@[reassoc]
theorem cyclicTwoColumnTailIso_hom_naturality (f : A →ₙₐ[k] B) :
    HomologicalComplex.extendMap (partialTotalCokernelMap (cyclicBicomplexHom f) 1)
        (ComplexShape.embeddingDownNatToIntShift 0) ≫ (cyclicTwoColumnTailIso k B).hom =
      (cyclicTwoColumnTailIso k A).hom ≫
        HomologicalComplex.extendMap
          (total.map (cyclicBicomplexHom f) (ComplexShape.down ℕ))
          (ComplexShape.embeddingDownNatToIntShift 2) := by
  let C := ModuleCat.{max u v} k
  let e₀ : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℤ) := ComplexShape.embeddingDownNatToIntShift 0
  let e₂ : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℤ) := ComplexShape.embeddingDownNatToIntShift 2
  let e : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) := _root_.partialTotalOuterEmbedding 2
  let ψ : cyclicTotal k A ⟶ cyclicTotal k B := total.map (cyclicBicomplexHom f) (ComplexShape.down ℕ)
  let q : cyclicTwoColumnTail k A ⟶ cyclicTwoColumnTail k B := partialTotalCokernelMap (cyclicBicomplexHom f) 1
  let aA : (cyclicTwoColumnTail k A).extend e₀ ≅ ((cyclicTotal k A).extend e).extend e₀ :=
    (e₀.extendFunctor C).mapIso (cyclicTwoColumnTailNatIso k A)
  let aB : (cyclicTwoColumnTail k B).extend e₀ ≅ ((cyclicTotal k B).extend e).extend e₀ :=
    (e₀.extendFunctor C).mapIso (cyclicTwoColumnTailNatIso k B)
  let bA : ((cyclicTotal k A).extend e).extend e₀ ≅ (cyclicTotal k A).extend e₂ :=
    HomologicalComplex.extendNatAddIntIso (cyclicTotal k A) 2
  let bB : ((cyclicTotal k B).extend e).extend e₀ ≅ (cyclicTotal k B).extend e₂ :=
    HomologicalComplex.extendNatAddIntIso (cyclicTotal k B) 2
  have ha : HomologicalComplex.extendMap q e₀ ≫ aB.hom =
      aA.hom ≫ HomologicalComplex.extendMap (HomologicalComplex.extendMap ψ e) e₀ := by
    change HomologicalComplex.extendMap q e₀ ≫
        HomologicalComplex.extendMap (cyclicTwoColumnTailNatIso k B).hom e₀ =
      HomologicalComplex.extendMap (cyclicTwoColumnTailNatIso k A).hom e₀ ≫
        HomologicalComplex.extendMap (HomologicalComplex.extendMap ψ e) e₀
    erw [← HomologicalComplex.extendMap_comp, cyclicTwoColumnTailNatIso_hom_naturality,
      HomologicalComplex.extendMap_comp]
  have hb : HomologicalComplex.extendMap (HomologicalComplex.extendMap ψ e) e₀ ≫
      bB.hom = bA.hom ≫ HomologicalComplex.extendMap ψ e₂ :=
    HomologicalComplex.extendNatAddIntIso_hom_naturality ψ 2
  change HomologicalComplex.extendMap q e₀ ≫ (aB.hom ≫ bB.hom) =
    (aA.hom ≫ bA.hom) ≫ HomologicalComplex.extendMap ψ e₂
  calc
    HomologicalComplex.extendMap q e₀ ≫ (aB.hom ≫ bB.hom) =
        (HomologicalComplex.extendMap q e₀ ≫ aB.hom) ≫ bB.hom := (Category.assoc _ _ _).symm
    _ = (aA.hom ≫ HomologicalComplex.extendMap (HomologicalComplex.extendMap ψ e) e₀) ≫
          bB.hom := by rw [ha]
    _ = aA.hom ≫ (HomologicalComplex.extendMap (HomologicalComplex.extendMap ψ e) e₀ ≫
          bB.hom) := Category.assoc _ _ _
    _ = aA.hom ≫ (bA.hom ≫ HomologicalComplex.extendMap ψ e₂) := by rw [hb]
    _ = (aA.hom ≫ bA.hom) ≫ HomologicalComplex.extendMap ψ e₂ :=
      (Category.assoc _ _ _).symm

/-- Original nonunital algebra maps induce morphisms of the computed SBI presentations. -/
def cyclicConnesSBIPresentationMap (f : A →ₙₐ[k] B) :
    cyclicConnesSBIPresentation k A ⟶ cyclicConnesSBIPresentation k B where
  ordinaryMap := (cyclicTwoColumnSequenceMap f).τ₁
  shortMap := cyclicTwoColumnSequenceMap f
  ordinaryComparison_naturality := by
    change (cyclicTwoColumnSequenceMap f).τ₁ ≫ 𝟙 _ = 𝟙 _ ≫ (cyclicTwoColumnSequenceMap f).τ₁
    rw [Category.comp_id, Category.id_comp]
  tailIso_naturality := by
    change HomologicalComplex.extendMap (partialTotalCokernelMap (cyclicBicomplexHom f) 1)
        (ComplexShape.embeddingDownNatToIntShift 0) ≫ (cyclicTwoColumnTailIso k B).hom =
      (cyclicTwoColumnTailIso k A).hom ≫ HomologicalComplex.extendMap
        (total.map (cyclicBicomplexHom f) (ComplexShape.down ℕ))
        (ComplexShape.embeddingDownNatToIntShift 2)
    exact cyclicTwoColumnTailIso_hom_naturality f

/-- The underlying short-complex map is the original two-column/cokernel map. -/
lemma cyclicConnesSBIPresentationMap_shortMap (f : A →ₙₐ[k] B) :
    (cyclicConnesSBIPresentationMap f).shortMap = cyclicTwoColumnSequenceMap f := rfl

/-- The ordinary map retains both original raw columns. -/
lemma cyclicConnesSBIPresentationMap_ordinaryMap (f : A →ₙₐ[k] B) :
    (cyclicConnesSBIPresentationMap f).ordinaryMap = (cyclicTwoColumnSequenceMap f).τ₁ := rfl

/-- The computed presentation map preserves the original identity. -/
lemma cyclicConnesSBIPresentationMap_id :
    cyclicConnesSBIPresentationMap (NonUnitalAlgHom.id k A) =
      𝟙 (cyclicConnesSBIPresentation k A) := by
  apply CategoryTheory.ConnesSBIPresentation.hom_ext
  · change (cyclicTwoColumnSequenceMap (NonUnitalAlgHom.id k A)).τ₁ = 𝟙 _
    rw [cyclicTwoColumnSequenceMap_id, ShortComplex.id_τ₁]
  · exact cyclicTwoColumnSequenceMap_id (k := k) (A := A)

variable {D : Type v} [NonUnitalRing D] [Module k D]
  [IsScalarTower k D D] [SMulCommClass k D D]

/-- Composition is the original nonunital-map composition on the entire presentation. -/
lemma cyclicConnesSBIPresentationMap_comp (f : A →ₙₐ[k] B) (g : B →ₙₐ[k] D) :
    cyclicConnesSBIPresentationMap (g.comp f) =
      cyclicConnesSBIPresentationMap f ≫ cyclicConnesSBIPresentationMap g := by
  apply CategoryTheory.ConnesSBIPresentation.hom_ext
  · change (cyclicTwoColumnSequenceMap (g.comp f)).τ₁ =
      (cyclicTwoColumnSequenceMap f).τ₁ ≫ (cyclicTwoColumnSequenceMap g).τ₁
    rw [cyclicTwoColumnSequenceMap_comp, ShortComplex.comp_τ₁]
  · exact cyclicTwoColumnSequenceMap_comp f g

/-- The source map induces the native morphism of exact SBI diagrams. -/
def cyclicSBIDiagramMap (f : A →ₙₐ[k] B) : cyclicSBIDiagram k A ⟶ cyclicSBIDiagram k B :=
  (cyclicConnesSBIPresentationMap f).toSBIHom

/-- The ordinary homology action is that of the original retained two-column map. -/
lemma cyclicSBIDiagramMap_hMap (f : A →ₙₐ[k] B) (n : ℕ) :
    (cyclicSBIDiagramMap f).hMap n =
      HomologicalComplex.homologyMap (cyclicTwoColumnSequenceMap f).τ₁ n := rfl

/-- The cyclic homology action is the total map of the original cyclic bicomplex. -/
lemma cyclicSBIDiagramMap_hcMap (f : A →ₙₐ[k] B) (n : ℕ) :
    (cyclicSBIDiagramMap f).hcMap n = cyclicHomologyMap f n := rfl

/-- The SBI-diagram map preserves the original identity algebra map. -/
lemma cyclicSBIDiagramMap_id :
    cyclicSBIDiagramMap (NonUnitalAlgHom.id k A) = 𝟙 (cyclicSBIDiagram k A) := by
  rw [cyclicSBIDiagramMap, cyclicConnesSBIPresentationMap_id]
  exact CategoryTheory.ConnesSBIPresentation.Hom.toSBIHom_id (cyclicConnesSBIPresentation k A)

/-- Actual diagram maps compose in the same order as the original nonunital maps. -/
lemma cyclicSBIDiagramMap_comp (f : A →ₙₐ[k] B) (g : B →ₙₐ[k] D) :
    cyclicSBIDiagramMap (g.comp f) = cyclicSBIDiagramMap f ≫ cyclicSBIDiagramMap g := by
  rw [cyclicSBIDiagramMap, cyclicConnesSBIPresentationMap_comp]
  exact CategoryTheory.ConnesSBIPresentation.Hom.toSBIHom_comp
    (cyclicConnesSBIPresentationMap f) (cyclicConnesSBIPresentationMap g)

/-- Inclusion is natural in the original algebra map. -/
@[reassoc]
theorem cyclicSBIInclusion_naturality (f : A →ₙₐ[k] B) (n : ℕ) :
    (cyclicSBIDiagramMap f).hMap n ≫ cyclicSBIInclusion k B n =
      cyclicSBIInclusion k A n ≫ cyclicHomologyMap f n :=
  (cyclicSBIDiagramMap f).I_naturality n |>.symm

/-- Periodicity is natural in the original algebra map. -/
@[reassoc]
theorem cyclicSBIPeriodicity_naturality (f : A →ₙₐ[k] B) (n : ℕ) :
    cyclicHomologyMap f (n + 2) ≫ cyclicSBIPeriodicity k B n =
      cyclicSBIPeriodicity k A n ≫ cyclicHomologyMap f n :=
  (cyclicSBIDiagramMap f).S_naturality n |>.symm

/-- The native LES connecting morphism is natural in the original algebra map. -/
@[reassoc]
theorem cyclicSBIConnecting_naturality (f : A →ₙₐ[k] B) (n : ℕ) :
    cyclicHomologyMap f n ≫ cyclicSBIConnecting k B n =
      cyclicSBIConnecting k A n ≫ (cyclicSBIDiagramMap f).hMap (n + 1) :=
  (cyclicSBIDiagramMap f).B_naturality n |>.symm

/-- A quasi-isomorphism of the first-two-column complexes induces a quasi-isomorphism
of the original cyclic totals, by the native SBI comparison theorem. -/
theorem cyclicTotalHom_quasiIso_of_firstTwo (f : A →ₙₐ[k] B)
    [QuasiIso (cyclicTwoColumnSequenceMap f).τ₁] : QuasiIso (cyclicTotalHom f) := by
  let F := cyclicConnesSBIPresentationMap f
  letI : QuasiIso F.ordinaryMap := by
    change QuasiIso (cyclicTwoColumnSequenceMap f).τ₁
    infer_instance
  change QuasiIso F.shortMap.τ₂
  exact F.quasiIso_shortMap_τ₂

end PresentationMaps

end ModuleCat.Algebra.Hochschild


namespace ModuleCat.Algebra.Hochschild

section ReverseComparison

variable {k : Type u} [CommRing k] {A B : Type v}
  [NonUnitalRing A] [NonUnitalRing B] [Module k A] [Module k B]
  [IsScalarTower k A A] [SMulCommClass k A A]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- The cyclic-total quasi-isomorphism detects the HH map in the source's
`CC(A){2}` presentation, for the original nonunital algebra map. -/
theorem cyclicFirstTwoMap_quasiIso_of_cyclicTotalHom (f : A →ₙₐ[k] B)
    [QuasiIso (cyclicTotalHom f)] : QuasiIso (cyclicTwoColumnSequenceMap f).τ₁ := by
  let F := cyclicConnesSBIPresentationMap f
  letI : QuasiIso F.shortMap.τ₂ := by
    change QuasiIso (cyclicTotalHom f)
    infer_instance
  change QuasiIso F.ordinaryMap
  exact F.quasiIso_ordinaryMap

/-- Chain-level reformulation of Loday, Corollary 2.2.3 using the source's
`CC(A){2}` HH presentation from 2.2.1 (printed p. 61 / PDF page 76).
The first-two-column and cyclic-total maps have equivalent
quasi-isomorphism tests; the printed homology criterion includes
"and conversely" (printed p. 62 / PDF page 77). -/
theorem cyclicFirstTwoMap_quasiIso_iff_cyclicTotalHom (f : A →ₙₐ[k] B) :
    QuasiIso (cyclicTwoColumnSequenceMap f).τ₁ ↔ QuasiIso (cyclicTotalHom f) := by
  change QuasiIso (cyclicConnesSBIPresentationMap f).ordinaryMap ↔
    QuasiIso (cyclicConnesSBIPresentationMap f).shortMap.τ₂
  exact (cyclicConnesSBIPresentationMap f).quasiIso_ordinaryMap_iff_shortMap_τ₂

/-- Loday, Corollary 2.2.3 on the source's `CC(A){2}` HH presentation
(2.2.1, printed p. 61 / PDF page 76) and the original cyclic-total homology.
The algebra map is general: the print says "which need not preserve the
unit if any" and includes "and conversely" (printed p. 62 / PDF page 77). -/
theorem cyclicRawHochschildMap_isIso_iff_cyclicHomologyMap (f : A →ₙₐ[k] B) :
    (∀ n : ℕ, IsIso (HomologicalComplex.homologyMap (cyclicTwoColumnSequenceMap f).τ₁ n)) ↔
      ∀ n : ℕ, IsIso (cyclicHomologyMap f n) := by
  let h : cyclicFirstTwoColumns k A ⟶ cyclicFirstTwoColumns k B := (cyclicTwoColumnSequenceMap f).τ₁
  let c : cyclicTotal k A ⟶ cyclicTotal k B := cyclicTotalHom f
  have hh : QuasiIso h ↔ ∀ n : ℕ, IsIso (HomologicalComplex.homologyMap h n) :=
    (_root_.quasiIso_iff h).trans
      (forall_congr' (fun n => _root_.quasiIsoAt_iff_isIso_homologyMap h n))
  have hc : QuasiIso c ↔ ∀ n : ℕ, IsIso (HomologicalComplex.homologyMap c n) :=
    (_root_.quasiIso_iff c).trans
      (forall_congr' (fun n => _root_.quasiIsoAt_iff_isIso_homologyMap c n))
  change (∀ n : ℕ, IsIso (HomologicalComplex.homologyMap h n)) ↔
    ∀ n : ℕ, IsIso (HomologicalComplex.homologyMap c n)
  exact hh.symm.trans ((cyclicFirstTwoMap_quasiIso_iff_cyclicTotalHom f).trans hc)

end ReverseComparison

end ModuleCat.Algebra.Hochschild
