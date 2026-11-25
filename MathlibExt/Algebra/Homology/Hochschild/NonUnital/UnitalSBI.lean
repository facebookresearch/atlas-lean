/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.SBI
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.ConnesBoundary
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Maps
public import MathlibExt.Algebra.Homology.ChainComplex.DegreewiseSplit
public import MathlibExt.Algebra.Homology.PartialTotalZero
public import MathlibExt.Algebra.Homology.PartialTotalSignedRowHomology
public import MathlibExt.Algebra.Homology.TotalComplexFirstColumn
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# The b-complex comparison with two cyclic columns

The first-column inclusion is defined for
nonunital algebras. A left unit contracts
b′, giving a homotopy equivalence between
the b complex and the first-two-column total.
The comparison is natural for nonunital
algebra maps without requiring them to
preserve chosen units or contractions.

Reference: Loday, Cyclic Homology, Remark 2.2.2.
-/

@[expose] public section
noncomputable section

open CategoryTheory Category Limits HomologicalComplex HomologicalComplex₂
open ModuleCat.Algebra.Hochschild.NonUnital
open scoped TensorProduct ZeroObject

universe u v

namespace ModuleCat.Algebra.Hochschild

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- The original zero cyclic column is the regular b-complex. -/
def cyclicColumnZeroIso : (cyclicBicomplex k A).X 0 ≅ bComplex k A :=
  eqToIso (cyclicColumn_even k A 0 ⟨0, rfl⟩)

/-- The zero-column comparison preserves every original tensor level. -/
@[simp]
theorem cyclicColumnZeroIso_hom_f (n : ℕ) :
    (cyclicColumnZeroIso k A).hom.f n = 𝟙 (NonUnital.chainLevel k A A n) := by
  let h : (cyclicBicomplex k A).X 0 = bComplex k A := cyclicColumn_even k A 0 ⟨0, rfl⟩
  change (eqToHom h).f n = 𝟙 (NonUnital.chainLevel k A A n)
  rw [HomologicalComplex.eqToHom_f]
  let X : ModuleCat.{max u v} k := NonUnital.chainLevel k A A n
  have hX : X = X := congrArg
    (fun K : ChainComplex (ModuleCat.{max u v} k) ℕ => K.X n) h
  change eqToHom hX = 𝟙 X
  exact eqToHom_refl X hX

/-- Its inverse also preserves every original tensor level. -/
@[simp]
theorem cyclicColumnZeroIso_inv_f (n : ℕ) :
    (cyclicColumnZeroIso k A).inv.f n = 𝟙 (NonUnital.chainLevel k A A n) := by
  let h : (cyclicBicomplex k A).X 0 = bComplex k A := cyclicColumn_even k A 0 ⟨0, rfl⟩
  change (eqToHom h.symm).f n = 𝟙 (NonUnital.chainLevel k A A n)
  rw [HomologicalComplex.eqToHom_f]
  let X : ModuleCat.{max u v} k := NonUnital.chainLevel k A A n
  have hX : X = X := congrArg
    (fun K : ChainComplex (ModuleCat.{max u v} k) ℕ => K.X n) h.symm
  change eqToHom hX = 𝟙 X
  exact eqToHom_refl X hX

/-- The native zero-stage projection computes the original b-complex. -/
def cyclicZeroPartialIso : (cyclicBicomplex k A).partialTotal 0 ≅ bComplex k A := by
  let K := cyclicBicomplex k A
  have hS : K.partialTotalZeroShortComplex.ShortExact := K.partialTotalZeroShortExact
  have hZero : IsZero K.partialTotalZeroShortComplex.X₁ := by
    change IsZero (0 : ChainComplex (ModuleCat.{max u v} k) ℕ)
    exact isZero_zero _
  letI : IsIso (K.partialTotalRowQuotient 0) := by
    change IsIso K.partialTotalZeroShortComplex.g
    exact hS.isIso_g_iff.2 hZero
  exact ((asIso (K.partialTotalRowQuotient 0)) ≪≫ K.totalRowZeroIso) ≪≫
    cyclicColumnZeroIso k A

/-- The zero-stage forward arrow is the row projection and the native coordinates. -/
theorem cyclicZeroPartialIso_hom :
    (cyclicZeroPartialIso k A).hom =
      ((cyclicBicomplex k A).partialTotalRowQuotient 0 ≫
        (cyclicBicomplex k A).totalRowZeroIso.hom) ≫
          (cyclicColumnZeroIso k A).hom := rfl

/-- The zero-stage inverse is the first-column cell inclusion. -/
theorem cyclicZeroPartialIso_inv_f (n : ℕ) :
    (cyclicZeroPartialIso k A).inv.f n =
      (cyclicBicomplex k A).partialTotalComponent 0 ⟨0, by omega⟩ n n (Nat.zero_add n) := by
  let K := cyclicBicomplex k A
  let E := cyclicZeroPartialIso k A
  let i := K.partialTotalComponent 0 ⟨0, by omega⟩ n n (Nat.zero_add n)
  letI : IsIso (E.hom.f n) :=
    ((HomologicalComplex.eval (ModuleCat.{max u v} k) (ComplexShape.down ℕ) n).mapIso E).isIso_hom
  apply (cancel_mono (E.hom.f n)).1
  have hInv : E.inv.f n ≫ E.hom.f n = 𝟙 ((bComplex k A).X n) := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
      HomologicalComplex.congr_hom E.inv_hom_id n
  have hComponent : E.hom.f n =
      ((K.partialTotalRowQuotient 0).f n ≫
        (K.totalRowXIso 0 n n (Nat.zero_add n)).hom) ≫
          𝟙 (NonUnital.chainLevel k A A n) := by
    change (cyclicZeroPartialIso k A).hom.f n = _
    rw [cyclicZeroPartialIso_hom, HomologicalComplex.comp_f,
      HomologicalComplex.comp_f, totalRowZeroIso_hom_f, cyclicColumnZeroIso_hom_f]
  have hCell : i ≫ E.hom.f n = 𝟙 (NonUnital.chainLevel k A A n) := by
    erw [hComponent, Category.comp_id, ← Category.assoc]
    erw [K.partialTotalComponent_comp_partialTotalRowQuotient 0 n n (Nat.zero_add n),
      Iso.inv_hom_id]
    rfl
  exact hInv.trans hCell.symm

/-- The original b-complex includes as the first column of the first two raw columns. -/
def cyclicBToFirstTwo : bComplex k A ⟶ cyclicFirstTwoColumns k A :=
  (cyclicZeroPartialIso k A).inv ≫
    ((cyclicBicomplex k A).partialTotalSuccShortComplex 0).f

/-- The comparison uses exactly the original zero-column tensor cell. -/
theorem cyclicBToFirstTwo_f (n : ℕ) :
    (cyclicBToFirstTwo k A).f n =
      cyclicFirstTwoColumnCell k A ⟨0, by omega⟩ n n (Nat.zero_add n) := by
  change (cyclicZeroPartialIso k A).inv.f n ≫
      ((cyclicBicomplex k A).partialTotalMap (Nat.le_succ 0)).f n = _
  rw [cyclicZeroPartialIso_inv_f]
  exact (cyclicBicomplex k A).partialTotalComponent_partialTotalMap
    (Nat.le_succ 0) ⟨0, by omega⟩ n n (Nat.zero_add n)

/-- Composing with the raw SBI inclusion is the canonical native first-column total map. -/
theorem cyclicBToFirstTwo_comp_inclusion :
    cyclicBToFirstTwo k A ≫ (cyclicTwoColumnSequence k A).f =
      (cyclicColumnZeroIso k A).inv ≫
        firstColumnTotalInclusion (cyclicBicomplex k A) := by
  apply HomologicalComplex.hom_ext
  intro n
  change (cyclicBToFirstTwo k A).f n ≫ (cyclicTwoColumnSequence k A).f.f n =
    (cyclicColumnZeroIso k A).inv.f n ≫ (firstColumnTotalInclusion (cyclicBicomplex k A)).f n
  erw [cyclicBToFirstTwo_f, cyclicFirstTwoColumnCell_inclusion, cyclicColumnZeroIso_inv_f,
    firstColumnTotalInclusion_f, Category.id_comp]

section ActualMaps

variable {k A} {B : Type v} [NonUnitalRing B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- Original algebra maps act through the regular coefficient Hochschild map. -/
def cyclicBComplexHom (f : A →ₙₐ[k] B) : bComplex k A ⟶ bComplex k B :=
  NonUnital.complexMap
    (NonUnitalAlgHom.lmul k A) (regularRight (k := k) (A := A))
    (fun a b m => by
      simpa only [MulOpposite.op_unop] using regular_commute (k := k) (A := A) a b.unop m)
    (NonUnitalAlgHom.lmul k B) (regularRight (k := k) (A := B))
    (fun a b m => by
      simpa only [MulOpposite.op_unop] using regular_commute (k := k) (A := B) a b.unop m)
    f (f : A →ₗ[k] B)
    (fun a m => by change f (a * m) = f a * f m; exact f.map_mul a m)
    (fun a m => by change f (m * a) = f m * f a; exact f.map_mul m a)

/-- The original b-map preserves both the coefficient and every tensor factor. -/
theorem cyclicBComplexHom_f (f : A →ₙₐ[k] B) (n : ℕ) :
    (cyclicBComplexHom f).f n =
      ModuleCat.ofHom (TensorPower.consLevelMap (f : A →ₗ[k] B) n) := rfl

/-- The identity algebra map gives the identity b-map. -/
theorem cyclicBComplexHom_id :
    cyclicBComplexHom (NonUnitalAlgHom.id k A) = 𝟙 (bComplex k A) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [cyclicBComplexHom_f]
  change ModuleCat.ofHom (TensorPower.consLevelMap (LinearMap.id : A →ₗ[k] A) n) = _
  rw [TensorPower.consLevelMap_id]
  rfl

variable {D : Type v} [NonUnitalRing D] [Module k D]
  [IsScalarTower k D D] [SMulCommClass k D D]

/-- Composition retains the original nonunital-map order on the b-complex. -/
theorem cyclicBComplexHom_comp (f : A →ₙₐ[k] B) (g : B →ₙₐ[k] D) :
    cyclicBComplexHom (g.comp f) = cyclicBComplexHom f ≫ cyclicBComplexHom g := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, cyclicBComplexHom_f, cyclicBComplexHom_f,
    cyclicBComplexHom_f]
  apply ModuleCat.hom_ext
  change TensorPower.consLevelMap ((g : B →ₗ[k] D).comp (f : A →ₗ[k] B)) n =
    (TensorPower.consLevelMap (g : B →ₗ[k] D) n).comp
      (TensorPower.consLevelMap (f : A →ₗ[k] B) n)
  exact (TensorPower.consLevelMap_comp (f : A →ₗ[k] B) (g : B →ₗ[k] D) n).symm

/-- The comparison is natural without any unit-preservation hypothesis. -/
@[reassoc]
theorem cyclicBToFirstTwo_naturality (f : A →ₙₐ[k] B) :
    cyclicBComplexHom f ≫ cyclicBToFirstTwo k B =
      cyclicBToFirstTwo k A ≫ (cyclicTwoColumnSequenceMap f).τ₁ := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, cyclicBComplexHom_f,
    cyclicBToFirstTwo_f, cyclicBToFirstTwo_f]
  exact (cyclicFirstTwoColumnCell_naturality f ⟨0, by omega⟩ n n (Nat.zero_add n)).symm

end ActualMaps

/-- An left unit contracts the signed, shifted quotient of the first successor step. -/
def cyclicFirstSuccessorContractionOfLeftUnit (e : A) (hLeft : ∀ a : A, e * a = a) :
    Homotopy (𝟙 ((cyclicBicomplex k A).partialTotalSuccShortComplex 0).X₃) 0 := by
  let K := cyclicBicomplex k A
  let E : K.signedRow 1 ≅ bPrimeComplex k A :=
    (K.signedRowIso 1) ≪≫ eqToIso (cyclicColumn_odd k A 1 (by decide))
  let H := ((bPrimeContractionOfLeftUnit k A e hLeft).compLeft E.hom).compRight E.inv
  have hId : (E.hom ≫ 𝟙 (bPrimeComplex k A)) ≫ E.inv = 𝟙 (K.signedRow 1) := by
    rw [Category.comp_id, E.hom_inv_id]
  have hZero : (E.hom ≫ (0 : bPrimeComplex k A ⟶ bPrimeComplex k A)) ≫ E.inv = 0 := by
    rw [comp_zero, zero_comp]
  let H' : Homotopy (𝟙 (K.signedRow 1)) 0 :=
    (Homotopy.ofEq hId.symm).trans (H.trans (Homotopy.ofEq hZero))
  change Homotopy (𝟙 ((K.signedRow 1).extend (_root_.partialTotalOuterEmbedding 1))) 0
  simpa only [HomologicalComplex.extendMap_id, HomologicalComplex.extendMap_zero] using
    H'.extend (_root_.partialTotalOuterEmbedding 1)

/-- A left unit earns a homotopy equivalence whose forward arrow is the original inclusion. -/
def cyclicBToFirstTwoHomotopyEquivOfLeftUnit (e : A) (hLeft : ∀ a : A, e * a = a) :
    HomotopyEquiv (bComplex k A) (cyclicFirstTwoColumns k A) :=
  (HomotopyEquiv.ofIso ((cyclicZeroPartialIso k A).symm)).trans
    (ChainComplex.homotopyEquivOfDegreewiseSplit
      ((cyclicBicomplex k A).partialTotalSuccShortComplex 0)
      (fun n => (cyclicBicomplex k A).partialTotalSuccDegreeSplitting 0 n)
      (cyclicFirstSuccessorContractionOfLeftUnit k A e hLeft))

/-- The homotopy equivalence has the unit-independent canonical forward map. -/
theorem cyclicBToFirstTwoHomotopyEquivOfLeftUnit_hom
    (e : A) (hLeft : ∀ a : A, e * a = a) :
    (cyclicBToFirstTwoHomotopyEquivOfLeftUnit k A e hLeft).hom =
      cyclicBToFirstTwo k A := by
  change (cyclicZeroPartialIso k A).inv ≫
      (ChainComplex.homotopyEquivOfDegreewiseSplit
        ((cyclicBicomplex k A).partialTotalSuccShortComplex 0)
        (fun n => (cyclicBicomplex k A).partialTotalSuccDegreeSplitting 0 n)
        (cyclicFirstSuccessorContractionOfLeftUnit k A e hLeft)).hom =
    (cyclicZeroPartialIso k A).inv ≫
      ((cyclicBicomplex k A).partialTotalSuccShortComplex 0).f
  exact congrArg (fun f => (cyclicZeroPartialIso k A).inv ≫ f)
    (ChainComplex.homotopyEquivOfDegreewiseSplit_hom _ _ _)

/-- Existence of an left unit makes the original comparison a quasi-isomorphism. -/
theorem cyclicBToFirstTwo_quasiIso (hUnit : ∃ e : A, ∀ a : A, e * a = a) :
    QuasiIso (cyclicBToFirstTwo k A) := by
  rcases hUnit with ⟨e, hLeft⟩
  rw [← cyclicBToFirstTwoHomotopyEquivOfLeftUnit_hom k A e hLeft]
  infer_instance

/-- The homology comparison is computed from the first-column quasi-isomorphism. -/
def cyclicBToFirstTwoHomologyIso (hUnit : ∃ e : A, ∀ a : A, e * a = a) (n : ℕ) :
    (bComplex k A).homology n ≅ cyclicRawHochschildHomology k A n := by
  letI : QuasiIso (cyclicBToFirstTwo k A) := cyclicBToFirstTwo_quasiIso k A hUnit
  exact isoOfQuasiIsoAt (cyclicBToFirstTwo k A) n

/-- The canonical forward homology arrow is the comparison's native homology map. -/
theorem cyclicBToFirstTwoHomologyIso_hom
    (hUnit : ∃ e : A, ∀ a : A, e * a = a) (n : ℕ) :
    (cyclicBToFirstTwoHomologyIso k A hUnit n).hom =
      HomologicalComplex.homologyMap (cyclicBToFirstTwo k A) n := rfl

section HomologyNaturality

variable {k A} {B : Type v} [NonUnitalRing B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- Original maps commute with the homology comparison for any two left-unit witnesses. -/
@[reassoc]
theorem cyclicBToFirstTwoHomologyIso_hom_naturality
    (f : A →ₙₐ[k] B) (hA : ∃ e : A, ∀ a : A, e * a = a)
    (hB : ∃ e : B, ∀ b : B, e * b = b) (n : ℕ) :
    HomologicalComplex.homologyMap (cyclicBComplexHom f) n ≫
        (cyclicBToFirstTwoHomologyIso k B hB n).hom =
      (cyclicBToFirstTwoHomologyIso k A hA n).hom ≫
        HomologicalComplex.homologyMap (cyclicTwoColumnSequenceMap f).τ₁ n := by
  have h := congrArg
    (fun g : bComplex k A ⟶ cyclicFirstTwoColumns k B =>
      HomologicalComplex.homologyMap g n) (cyclicBToFirstTwo_naturality f)
  simpa only [HomologicalComplex.homologyMap_comp,
    cyclicBToFirstTwoHomologyIso_hom] using h

/-- The inverse is natural because the canonical forward arrow is natural and invertible. -/
@[reassoc]
theorem cyclicBToFirstTwoHomologyIso_inv_naturality
    (f : A →ₙₐ[k] B) (hA : ∃ e : A, ∀ a : A, e * a = a)
    (hB : ∃ e : B, ∀ b : B, e * b = b) (n : ℕ) :
    HomologicalComplex.homologyMap (cyclicTwoColumnSequenceMap f).τ₁ n ≫
        (cyclicBToFirstTwoHomologyIso k B hB n).inv =
      (cyclicBToFirstTwoHomologyIso k A hA n).inv ≫
        HomologicalComplex.homologyMap (cyclicBComplexHom f) n := by
  let X : ModuleCat.{max u v} k := (bComplex k A).homology n
  let Y : ModuleCat.{max u v} k := (bComplex k B).homology n
  let P : ModuleCat.{max u v} k := cyclicRawHochschildHomology k A n
  let Q : ModuleCat.{max u v} k := cyclicRawHochschildHomology k B n
  let eA : X ≅ P := cyclicBToFirstTwoHomologyIso k A hA n
  let eB : Y ≅ Q := cyclicBToFirstTwoHomologyIso k B hB n
  let a : X ⟶ Y := HomologicalComplex.homologyMap (cyclicBComplexHom f) n
  let b : P ⟶ Q := HomologicalComplex.homologyMap (cyclicTwoColumnSequenceMap f).τ₁ n
  have h : a ≫ eB.hom = eA.hom ≫ b := cyclicBToFirstTwoHomologyIso_hom_naturality f hA hB n
  change b ≫ eB.inv = eA.inv ≫ a
  apply (cancel_mono eB.hom).1
  calc
    _ = b := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = (eA.inv ≫ eA.hom) ≫ b :=
      ((congrArg (fun a : P ⟶ P => a ≫ b) eA.inv_hom_id).trans (Category.id_comp b)).symm
    _ = eA.inv ≫ (eA.hom ≫ b) := Category.assoc _ _ _
    _ = eA.inv ≫ (a ≫ eB.hom) :=
      congrArg (fun f : X ⟶ Q => eA.inv ≫ f) h.symm
    _ = (eA.inv ≫ a) ≫ eB.hom := (Category.assoc _ _ _).symm

end HomologyNaturality

/-- The raw SBI engine with the b-complex as its ordinary model. -/
def cyclicBConnesSBIPresentation (hUnit : ∃ e : A, ∀ a : A, e * a = a) :
    ConnesSBIPresentation (A := ModuleCat.{max u v} k) where
  ordinary := bComplex k A
  shortComplex := cyclicTwoColumnSequence k A
  shortExact := cyclicTwoColumnSequence_shortExact k A
  ordinaryComparison := cyclicBToFirstTwo k A
  ordinaryComparisonQuasiIso := cyclicBToFirstTwo_quasiIso k A hUnit
  tailIso := (cyclicConnesSBIPresentation k A).tailIso

/-- The chain-level ordinary comparison stays the original unit-independent first-column map. -/
theorem cyclicBConnesSBIPresentation_ordinaryComparison
    (hUnit : ∃ e : A, ∀ a : A, e * a = a) :
    (cyclicBConnesSBIPresentation k A hUnit).ordinaryComparison =
      cyclicBToFirstTwo k A := rfl

/-- A unital algebra supplies the printed comparison without any additional comparison data. -/
theorem cyclicBToFirstTwo_quasiIso_of_unital
    (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A] :
    QuasiIso (cyclicBToFirstTwo k A) :=
  cyclicBToFirstTwo_quasiIso k A ⟨1, one_mul⟩

end ModuleCat.Algebra.Hochschild

namespace ModuleCat.Algebra.Hochschild

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- The ordinary-model homology coordinate is the canonical comparison isomorphism. -/
theorem cyclicBConnesSBIPresentation_hIso
    (hUnit : ∃ e : A, ∀ a : A, e * a = a) (n : ℕ) :
    (cyclicBConnesSBIPresentation k A hUnit).hIso n =
      cyclicBToFirstTwoHomologyIso k A hUnit n := rfl

/-- The ordinary-model presentation gives the connective SBI diagram. -/
abbrev cyclicBSBIDiagram (hUnit : ∃ e : A, ∀ a : A, e * a = a) :
    NatSBIDiagram (A := ModuleCat.{max u v} k) :=
  (cyclicBConnesSBIPresentation k A hUnit).sbiDiagram

/-- Inclusion from original b-homology into the original cyclic homology. -/
abbrev cyclicBSBIInclusion (hUnit : ∃ e : A, ∀ a : A, e * a = a) (n : ℕ) :
    (bComplex k A).homology n ⟶ cyclicHomology k A n :=
  (cyclicBConnesSBIPresentation k A hUnit).I n

/-- The native SBI boundary with its target computed by the original b-complex. -/
abbrev cyclicBSBIConnecting (hUnit : ∃ e : A, ∀ a : A, e * a = a) (n : ℕ) :
    cyclicHomology k A n ⟶ (bComplex k A).homology (n + 1) :=
  (cyclicBConnesSBIPresentation k A hUnit).B n

/-- The ordinary-model inclusion is induced by the native first-column chain map. -/
theorem cyclicBSBIInclusion_eq_firstColumn_homologyMap
    (hUnit : ∃ e : A, ∀ a : A, e * a = a) (n : ℕ) :
    cyclicBSBIInclusion k A hUnit n =
      HomologicalComplex.homologyMap
        ((cyclicColumnZeroIso k A).inv ≫ firstColumnTotalInclusion (cyclicBicomplex k A)) n := by
  let P : ChainComplex (ModuleCat.{max u v} k) ℕ := bComplex k A
  let Q : ChainComplex (ModuleCat.{max u v} k) ℕ := cyclicFirstTwoColumns k A
  let T : ChainComplex (ModuleCat.{max u v} k) ℕ := cyclicTotal k A
  let q : P ⟶ Q := cyclicBToFirstTwo k A
  let i : Q ⟶ T := (cyclicTwoColumnSequence k A).f
  let j : P ⟶ T := (cyclicColumnZeroIso k A).inv ≫ firstColumnTotalInclusion (cyclicBicomplex k A)
  let e : P.homology n ≅ Q.homology n := (cyclicBConnesSBIPresentation k A hUnit).hIso n
  have he : e.hom = HomologicalComplex.homologyMap q n :=
    cyclicBToFirstTwoHomologyIso_hom k A hUnit n
  have hq : q ≫ i = j := cyclicBToFirstTwo_comp_inclusion k A
  change e.hom ≫ HomologicalComplex.homologyMap i n = HomologicalComplex.homologyMap j n
  exact (congrArg (fun a : P.homology n ⟶ Q.homology n =>
    a ≫ HomologicalComplex.homologyMap i n) he).trans
      ((HomologicalComplex.homologyMap_comp q i n).symm.trans
        (congrArg (fun a : P ⟶ T => HomologicalComplex.homologyMap a n) hq))

/-- The connecting map is the original raw boundary followed by the inverse coordinate. -/
theorem cyclicBSBIConnecting_eq_raw
    (hUnit : ∃ e : A, ∀ a : A, e * a = a) (n : ℕ) :
    cyclicBSBIConnecting k A hUnit n =
      cyclicSBIConnecting k A n ≫ (cyclicBToFirstTwoHomologyIso k A hUnit (n + 1)).inv := by
  change (((cyclicBConnesSBIPresentation k A hUnit).tailHomologyIso n).inv ≫
      (cyclicTwoColumnSequence_shortExact k A).δ (n + 2) (n + 1) (by simp)) ≫
        ((cyclicBConnesSBIPresentation k A hUnit).hIso (n + 1)).inv = _
  rw [cyclicBConnesSBIPresentation_hIso, cyclicSBIConnecting_eq_δ]
  rfl

/-- Changing the ordinary model preserves the even-tail periodicity map. -/
theorem cyclicBConnesSBIPresentation_S
    (hUnit : ∃ e : A, ∀ a : A, e * a = a) (n : ℕ) :
    (cyclicBConnesSBIPresentation k A hUnit).S n = cyclicSBIPeriodicity k A n := rfl

/-- Native homology exactness supplies all three kinds of SBI exactness at the original objects. -/
theorem cyclicBSBIDiagram_exact (hUnit : ∃ e : A, ∀ a : A, e * a = a) :
    (cyclicBSBIDiagram k A hUnit).Exact :=
  (cyclicBConnesSBIPresentation k A hUnit).sbiDiagram_exact

/-- The ordinary model retains the connective degree-zero and degree-one conclusions. -/
theorem cyclicBSBIDiagram_connectiveBoundary (hUnit : ∃ e : A, ∀ a : A, e * a = a) :
    (cyclicBSBIDiagram k A hUnit).ConnectiveBoundary :=
  (cyclicBConnesSBIPresentation k A hUnit).sbiDiagram_connectiveBoundary

/-- Original b-homology maps isomorphically to cyclic homology in degree zero. -/
theorem cyclicBSBIInclusion_isIso_zero (hUnit : ∃ e : A, ∀ a : A, e * a = a) :
    IsIso (cyclicBSBIInclusion k A hUnit 0) :=
  (cyclicBConnesSBIPresentation k A hUnit).isIso_I_zero

/-- Every original cyclic degree-one class lifts through the b-homology inclusion. -/
theorem cyclicBSBIInclusion_epi_one (hUnit : ∃ e : A, ∀ a : A, e * a = a) :
    Epi (cyclicBSBIInclusion k A hUnit 1) :=
  (cyclicBConnesSBIPresentation k A hUnit).epi_I_one

section PresentationMaps

variable {k A} {B : Type v} [NonUnitalRing B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- Actual original maps induce SBI presentation maps between any two left-unital endpoints. -/
def cyclicBConnesSBIPresentationMap (f : A →ₙₐ[k] B)
    (hA : ∃ e : A, ∀ a : A, e * a = a) (hB : ∃ e : B, ∀ b : B, e * b = b) :
    cyclicBConnesSBIPresentation k A hA ⟶ cyclicBConnesSBIPresentation k B hB where
  ordinaryMap := cyclicBComplexHom f
  shortMap := cyclicTwoColumnSequenceMap f
  ordinaryComparison_naturality := cyclicBToFirstTwo_naturality f
  tailIso_naturality := (cyclicConnesSBIPresentationMap f).tailIso_naturality

/-- The ordinary component is the original regular Hochschild map. -/
theorem cyclicBConnesSBIPresentationMap_ordinaryMap (f : A →ₙₐ[k] B)
    (hA : ∃ e : A, ∀ a : A, e * a = a) (hB : ∃ e : B, ∀ b : B, e * b = b) :
    (cyclicBConnesSBIPresentationMap f hA hB).ordinaryMap = cyclicBComplexHom f := rfl

/-- The raw short-complex component retains both original columns and the quotient. -/
theorem cyclicBConnesSBIPresentationMap_shortMap (f : A →ₙₐ[k] B)
    (hA : ∃ e : A, ∀ a : A, e * a = a) (hB : ∃ e : B, ∀ b : B, e * b = b) :
    (cyclicBConnesSBIPresentationMap f hA hB).shortMap = cyclicTwoColumnSequenceMap f := rfl

/-- The presentation map preserves the original identity. -/
theorem cyclicBConnesSBIPresentationMap_id (hA : ∃ e : A, ∀ a : A, e * a = a) :
    cyclicBConnesSBIPresentationMap (NonUnitalAlgHom.id k A) hA hA =
      𝟙 (cyclicBConnesSBIPresentation k A hA) := by
  apply CategoryTheory.ConnesSBIPresentation.hom_ext
  · exact cyclicBComplexHom_id
  · exact cyclicTwoColumnSequenceMap_id

variable {D : Type v} [NonUnitalRing D] [Module k D]
  [IsScalarTower k D D] [SMulCommClass k D D]

/-- Composition uses the original maps, without a compatibility premise on unit choices. -/
theorem cyclicBConnesSBIPresentationMap_comp (f : A →ₙₐ[k] B) (g : B →ₙₐ[k] D)
    (hA : ∃ e : A, ∀ a : A, e * a = a) (hB : ∃ e : B, ∀ b : B, e * b = b)
    (hD : ∃ e : D, ∀ d : D, e * d = d) :
    cyclicBConnesSBIPresentationMap (g.comp f) hA hD =
      cyclicBConnesSBIPresentationMap f hA hB ≫ cyclicBConnesSBIPresentationMap g hB hD := by
  apply CategoryTheory.ConnesSBIPresentation.hom_ext
  · exact cyclicBComplexHom_comp f g
  · exact cyclicTwoColumnSequenceMap_comp f g

/-- Native SBI functoriality gives the whole homology diagram map. -/
def cyclicBSBIDiagramMap (f : A →ₙₐ[k] B)
    (hA : ∃ e : A, ∀ a : A, e * a = a) (hB : ∃ e : B, ∀ b : B, e * b = b) :
    cyclicBSBIDiagram k A hA ⟶ cyclicBSBIDiagram k B hB :=
  (cyclicBConnesSBIPresentationMap f hA hB).toSBIHom

/-- The HH component is native homology of the original b-map. -/
theorem cyclicBSBIDiagramMap_hMap (f : A →ₙₐ[k] B)
    (hA : ∃ e : A, ∀ a : A, e * a = a) (hB : ∃ e : B, ∀ b : B, e * b = b) (n : ℕ) :
    (cyclicBSBIDiagramMap f hA hB).hMap n =
      HomologicalComplex.homologyMap (cyclicBComplexHom f) n := rfl

/-- The HC component is the cyclic-homology map. -/
theorem cyclicBSBIDiagramMap_hcMap (f : A →ₙₐ[k] B)
    (hA : ∃ e : A, ∀ a : A, e * a = a) (hB : ∃ e : B, ∀ b : B, e * b = b) (n : ℕ) :
    (cyclicBSBIDiagramMap f hA hB).hcMap n = cyclicHomologyMap f n := rfl

/-- The native diagram map preserves identities on the ordinary and cyclic models. -/
theorem cyclicBSBIDiagramMap_id (hA : ∃ e : A, ∀ a : A, e * a = a) :
    cyclicBSBIDiagramMap (NonUnitalAlgHom.id k A) hA hA = 𝟙 (cyclicBSBIDiagram k A hA) := by
  rw [cyclicBSBIDiagramMap, cyclicBConnesSBIPresentationMap_id]
  exact CategoryTheory.ConnesSBIPresentation.Hom.toSBIHom_id _

/-- The native whole-diagram map composes in the same original-map order. -/
theorem cyclicBSBIDiagramMap_comp (f : A →ₙₐ[k] B) (g : B →ₙₐ[k] D)
    (hA : ∃ e : A, ∀ a : A, e * a = a) (hB : ∃ e : B, ∀ b : B, e * b = b)
    (hD : ∃ e : D, ∀ d : D, e * d = d) :
    cyclicBSBIDiagramMap (g.comp f) hA hD =
      cyclicBSBIDiagramMap f hA hB ≫ cyclicBSBIDiagramMap g hB hD := by
  rw [cyclicBSBIDiagramMap, cyclicBConnesSBIPresentationMap_comp f g hA hB hD]
  exact CategoryTheory.ConnesSBIPresentation.Hom.toSBIHom_comp _ _

/-- Inclusion is natural under arbitrary original nonunital maps between the left-unital models. -/
@[reassoc]
theorem cyclicBSBIInclusion_naturality (f : A →ₙₐ[k] B)
    (hA : ∃ e : A, ∀ a : A, e * a = a) (hB : ∃ e : B, ∀ b : B, e * b = b) (n : ℕ) :
    HomologicalComplex.homologyMap (cyclicBComplexHom f) n ≫ cyclicBSBIInclusion k B hB n =
      cyclicBSBIInclusion k A hA n ≫ cyclicHomologyMap f n :=
  (cyclicBSBIDiagramMap f hA hB).I_naturality n |>.symm

/-- The boundary square uses the same original b and cyclic homology actions. -/
@[reassoc]
theorem cyclicBSBIConnecting_naturality (f : A →ₙₐ[k] B)
    (hA : ∃ e : A, ∀ a : A, e * a = a) (hB : ∃ e : B, ∀ b : B, e * b = b) (n : ℕ) :
    cyclicHomologyMap f n ≫ cyclicBSBIConnecting k B hB n =
      cyclicBSBIConnecting k A hA n ≫
        HomologicalComplex.homologyMap (cyclicBComplexHom f) (n + 1) :=
  (cyclicBSBIDiagramMap f hA hB).B_naturality n |>.symm

/-- For left-unital endpoints, the original ordinary Hochschild and cyclic-total
maps have equivalent quasi-isomorphism tests. The algebra map need not preserve
the endpoint units. -/
theorem cyclicBComplexHom_quasiIso_iff_cyclicTotalHom (f : A →ₙₐ[k] B)
    (hA : ∃ e : A, ∀ a : A, e * a = a) (hB : ∃ e : B, ∀ b : B, e * b = b) :
    QuasiIso (cyclicBComplexHom f) ↔ QuasiIso (cyclicTotalHom f) := by
  change QuasiIso (cyclicBConnesSBIPresentationMap f hA hB).ordinaryMap ↔
    QuasiIso (cyclicBConnesSBIPresentationMap f hA hB).shortMap.τ₂
  exact (cyclicBConnesSBIPresentationMap f hA hB).quasiIso_ordinaryMap_iff_shortMap_τ₂

/-- The original ordinary Hochschild homology maps are all isomorphisms if and
only if the original cyclic homology maps are all isomorphisms, for left-unital
endpoints and any original nonunital algebra map. -/
theorem cyclicBHochschildMap_isIso_iff_cyclicHomologyMap (f : A →ₙₐ[k] B)
    (hA : ∃ e : A, ∀ a : A, e * a = a) (hB : ∃ e : B, ∀ b : B, e * b = b) :
    (∀ n : ℕ, IsIso (HomologicalComplex.homologyMap (cyclicBComplexHom f) n)) ↔
      ∀ n : ℕ, IsIso (cyclicHomologyMap f n) := by
  let h : bComplex k A ⟶ bComplex k B := cyclicBComplexHom f
  let c : cyclicTotal k A ⟶ cyclicTotal k B := cyclicTotalHom f
  have hh : QuasiIso h ↔ ∀ n : ℕ, IsIso (HomologicalComplex.homologyMap h n) :=
    (_root_.quasiIso_iff h).trans
      (forall_congr' (fun n => _root_.quasiIsoAt_iff_isIso_homologyMap h n))
  have hc : QuasiIso c ↔ ∀ n : ℕ, IsIso (HomologicalComplex.homologyMap c n) :=
    (_root_.quasiIso_iff c).trans
      (forall_congr' (fun n => _root_.quasiIsoAt_iff_isIso_homologyMap c n))
  change (∀ n : ℕ, IsIso (HomologicalComplex.homologyMap h n)) ↔
    ∀ n : ℕ, IsIso (HomologicalComplex.homologyMap c n)
  exact hh.symm.trans ((cyclicBComplexHom_quasiIso_iff_cyclicTotalHom f hA hB).trans hc)

end PresentationMaps

end ModuleCat.Algebra.Hochschild
