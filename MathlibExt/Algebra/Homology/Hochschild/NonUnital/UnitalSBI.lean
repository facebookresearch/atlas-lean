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
# Left units and the Hochschild model of SBI

Let `k` be a commutative ring and `A` a nonunital ring with a compatible `k`-module structure.
The regular `b`-complex is cyclic column zero, and its first-column inclusion into
`CC^{(2)}(A)` is defined for every such algebra.

If an element `e ∈ A` satisfies `e*a = a` for all `a`, insertion of `e` contracts the `b′`
column. The inclusion `b(A) → CC^{(2)}(A)` is then a chain homotopy equivalence, giving an SBI
presentation with ordinary homology `H_n(b(A))`. Its inclusion and connecting maps are `I_n :
H_n(b) → HC_n` and `B_n : HC_n → H_(n+1)(b)`, with the period-two cyclic map unchanged. All
homology comparisons and SBI maps are natural for nonunital algebra homomorphisms between
algebras possessing left units. For a unital algebra, take `e = 1`.

Reference: Loday, *Cyclic Homology*, Remark 2.2.2.
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

/-- The zeroth cyclic column as the regular Hochschild complex.

For a nonunital ground algebra, cyclic column zero is isomorphic to the regular `b`-complex. -/
def cyclicColumnZeroIso : (cyclicBicomplex k A).X 0 ≅ bComplex k A :=
  eqToIso (cyclicColumn_even k A 0 ⟨0, rfl⟩)

/-- The forward tensor formula for cyclic column zero.

The forward comparison from cyclic column zero to the `b`-complex is the identity on every
tensor level. -/
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

/-- The inverse tensor formula for cyclic column zero.

The inverse comparison from the `b`-complex to cyclic column zero is the identity on every
tensor level. -/
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

/-- The zero-stage cyclic total as the Hochschild complex.

The partial cyclic total retaining only column zero is isomorphic to the `b`-complex, through
its row projection and column-zero coordinates. -/
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

/-- The forward map of the zero-stage Hochschild comparison.

The forward comparison is the zero-stage row projection followed by the total-row and column-
zero isomorphisms. -/
theorem cyclicZeroPartialIso_hom :
    (cyclicZeroPartialIso k A).hom =
      ((cyclicBicomplex k A).partialTotalRowQuotient 0 ≫
        (cyclicBicomplex k A).totalRowZeroIso.hom) ≫
          (cyclicColumnZeroIso k A).hom := rfl

/-- The cell inclusion for the inverse zero-stage comparison.

In degree `n`, the inverse comparison from the `b`-complex is the cell inclusion in bidegree
`(0,n)` of the zero-stage total. -/
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

/-- The Hochschild inclusion into the first two cyclic columns.

The `b`-complex includes as column zero in `CC^{(2)}(A)`, the total of cyclic columns zero and
one. -/
def cyclicBToFirstTwo : bComplex k A ⟶ cyclicFirstTwoColumns k A :=
  (cyclicZeroPartialIso k A).inv ≫
    ((cyclicBicomplex k A).partialTotalSuccShortComplex 0).f

/-- The tensor cell formula for the Hochschild two-column inclusion.

In degree `n`, the comparison is the bidegree `(0,n)` cell inclusion into the first-two-column
total. -/
theorem cyclicBToFirstTwo_f (n : ℕ) :
    (cyclicBToFirstTwo k A).f n =
      cyclicFirstTwoColumnCell k A ⟨0, by omega⟩ n n (Nat.zero_add n) := by
  change (cyclicZeroPartialIso k A).inv.f n ≫
      ((cyclicBicomplex k A).partialTotalMap (Nat.le_succ 0)).f n = _
  rw [cyclicZeroPartialIso_inv_f]
  exact (cyclicBicomplex k A).partialTotalComponent_partialTotalMap
    (Nat.le_succ 0) ⟨0, by omega⟩ n n (Nat.zero_add n)

/-- The full cyclic-total map of the Hochschild inclusion.

Composing the `b`-complex inclusion into `CC^{(2)}(A)` with inclusion into `CC(A)` gives the
first-column total inclusion through column-zero coordinates. -/
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

/-- The regular Hochschild map of a nonunital algebra homomorphism.

For `f : A → B`, the induced `b`-complex map applies `f` to the regular coefficient and to
every algebra tensor factor. -/
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

/-- The tensor component of a regular Hochschild algebra map.

The degree-`n` component applies the underlying ground-linear map `f` to all `n+1` tensor
entries. -/
theorem cyclicBComplexHom_f (f : A →ₙₐ[k] B) (n : ℕ) :
    (cyclicBComplexHom f).f n =
      ModuleCat.ofHom (TensorPower.consLevelMap (f : A →ₗ[k] B) n) := rfl

/-- The identity regular Hochschild map.

The identity nonunital algebra homomorphism induces the identity on the regular `b`-complex. -/
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

/-- Composition of regular Hochschild algebra maps.

For composable nonunital algebra homomorphisms, their regular `b`-complex maps compose in the
same order. -/
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

/-- Naturality of the Hochschild inclusion into two cyclic columns.

For any nonunital algebra map, its `b`-complex map and retained-column map commute with the
first-column inclusion. -/
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

/-- The odd-column quotient contraction from a left unit.

If `e*a = a` for every `a ∈ A`, the `b′` contraction transports to a contraction of the
signed, degree-shifted quotient in the first partial-total successor sequence. -/
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

/-- The Hochschild-to-two-column homotopy equivalence from a left unit.

A left unit `e ∈ A` contracts the odd-column quotient and gives a chain homotopy equivalence
from the `b`-complex to `CC^{(2)}(A)`. -/
def cyclicBToFirstTwoHomotopyEquivOfLeftUnit (e : A) (hLeft : ∀ a : A, e * a = a) :
    HomotopyEquiv (bComplex k A) (cyclicFirstTwoColumns k A) :=
  (HomotopyEquiv.ofIso ((cyclicZeroPartialIso k A).symm)).trans
    (ChainComplex.homotopyEquivOfDegreewiseSplit
      ((cyclicBicomplex k A).partialTotalSuccShortComplex 0)
      (fun n => (cyclicBicomplex k A).partialTotalSuccDegreeSplitting 0 n)
      (cyclicFirstSuccessorContractionOfLeftUnit k A e hLeft))

/-- The forward map of the left-unit two-column equivalence.

The forward homotopy-equivalence map is the first-column inclusion, independently of which
left unit is used for the contraction. -/
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

/-- The first-column quasi-isomorphism for a left-unital algebra.

If `A` has an element `e` with `e*a = a` for all `a`, the inclusion of the `b`-complex into
`CC^{(2)}(A)` is a quasi-isomorphism. -/
theorem cyclicBToFirstTwo_quasiIso (hUnit : ∃ e : A, ∀ a : A, e * a = a) :
    QuasiIso (cyclicBToFirstTwo k A) := by
  rcases hUnit with ⟨e, hLeft⟩
  rw [← cyclicBToFirstTwoHomotopyEquivOfLeftUnit_hom k A e hLeft]
  infer_instance

/-- The homology comparison from a left unit.

If `A` has a left unit, the first-column inclusion gives `H_n(b(A)) ≅ H_n(CC^{(2)}(A))` for
every `n ∈ ℕ`. -/
def cyclicBToFirstTwoHomologyIso (hUnit : ∃ e : A, ∀ a : A, e * a = a) (n : ℕ) :
    (bComplex k A).homology n ≅ cyclicRawHochschildHomology k A n := by
  letI : QuasiIso (cyclicBToFirstTwo k A) := cyclicBToFirstTwo_quasiIso k A hUnit
  exact isoOfQuasiIsoAt (cyclicBToFirstTwo k A) n

/-- The forward homology map of the left-unit comparison.

The forward comparison equals the homology map induced by the first-column inclusion `b(A) →
CC^{(2)}(A)`. -/
theorem cyclicBToFirstTwoHomologyIso_hom
    (hUnit : ∃ e : A, ∀ a : A, e * a = a) (n : ℕ) :
    (cyclicBToFirstTwoHomologyIso k A hUnit n).hom =
      HomologicalComplex.homologyMap (cyclicBToFirstTwo k A) n := rfl

section HomologyNaturality

variable {k A} {B : Type v} [NonUnitalRing B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- Naturality of the forward left-unit homology comparison.

For a nonunital map between two algebras with left units, the regular Hochschild map and two-
column homology map commute with the forward comparison, for any witnesses of left-unit
existence. -/
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

/-- Naturality of the inverse left-unit homology comparison.

The inverse isomorphisms `H_n(CC^{(2)}) → H_n(b)` commute with maps between algebras with left
units, for any left-unit witnesses. -/
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

/-- The SBI presentation with the regular Hochschild complex.

If `A` has a left unit, use the first-column quasi-isomorphism to take `b(A)` as the ordinary
complex in the two-column Connes SBI presentation. -/
def cyclicBConnesSBIPresentation (hUnit : ∃ e : A, ∀ a : A, e * a = a) :
    ConnesSBIPresentation (A := ModuleCat.{max u v} k) where
  ordinary := bComplex k A
  shortComplex := cyclicTwoColumnSequence k A
  shortExact := cyclicTwoColumnSequence_shortExact k A
  ordinaryComparison := cyclicBToFirstTwo k A
  ordinaryComparisonQuasiIso := cyclicBToFirstTwo_quasiIso k A hUnit
  tailIso := (cyclicConnesSBIPresentation k A).tailIso

/-- The ordinary chain comparison of the left-unit SBI presentation.

The comparison from the ordinary `b`-complex to the retained two-column total is the first-
column inclusion. -/
theorem cyclicBConnesSBIPresentation_ordinaryComparison
    (hUnit : ∃ e : A, ∀ a : A, e * a = a) :
    (cyclicBConnesSBIPresentation k A hUnit).ordinaryComparison =
      cyclicBToFirstTwo k A := rfl

/-- The two-column Hochschild quasi-isomorphism for a unital algebra.

For a unital `k`-algebra `A`, its unit `1` makes the first-column inclusion `b(A) →
CC^{(2)}(A)` a quasi-isomorphism. -/
theorem cyclicBToFirstTwo_quasiIso_of_unital
    (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A] :
    QuasiIso (cyclicBToFirstTwo k A) :=
  cyclicBToFirstTwo_quasiIso k A ⟨1, one_mul⟩

end ModuleCat.Algebra.Hochschild

namespace ModuleCat.Algebra.Hochschild

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- The ordinary homology isomorphism in the left-unit SBI presentation.

Its ordinary homology coordinate is the isomorphism induced by the first-column inclusion from
`b(A)` to `CC^{(2)}(A)`. -/
theorem cyclicBConnesSBIPresentation_hIso
    (hUnit : ∃ e : A, ∀ a : A, e * a = a) (n : ℕ) :
    (cyclicBConnesSBIPresentation k A hUnit).hIso n =
      cyclicBToFirstTwoHomologyIso k A hUnit n := rfl

/-- The connective SBI diagram for a left-unital Hochschild model.

For an algebra with a left unit, this is the SBI diagram whose ordinary term is `H_n(b(A))`
and whose cyclic term is `HC_n(A)`. -/
abbrev cyclicBSBIDiagram (hUnit : ∃ e : A, ∀ a : A, e * a = a) :
    NatSBIDiagram (A := ModuleCat.{max u v} k) :=
  (cyclicBConnesSBIPresentation k A hUnit).sbiDiagram

/-- The Hochschild homology inclusion for a left-unital algebra.

The `b`-complex SBI presentation gives `I_n : H_n(b(A)) → HC_n(A)`. -/
abbrev cyclicBSBIInclusion (hUnit : ∃ e : A, ∀ a : A, e * a = a) (n : ℕ) :
    (bComplex k A).homology n ⟶ cyclicHomology k A n :=
  (cyclicBConnesSBIPresentation k A hUnit).I n

/-- The SBI boundary into left-unital Hochschild homology.

The connecting morphism, followed by the inverse two-column comparison, gives `B_n : HC_n(A) →
H_(n+1)(b(A))`. -/
abbrev cyclicBSBIConnecting (hUnit : ∃ e : A, ∀ a : A, e * a = a) (n : ℕ) :
    cyclicHomology k A n ⟶ (bComplex k A).homology (n + 1) :=
  (cyclicBConnesSBIPresentation k A hUnit).B n

/-- The left-unital SBI inclusion as a first-column homology map.

The map `I_n` equals the homology map of the first-column inclusion from the regular
`b`-complex into the full cyclic total. -/
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

/-- The left-unital boundary through the two-column homology coordinate.

The `b`-complex connecting map is the two-column SBI boundary followed by the inverse homology
comparison in degree `n+1`. -/
theorem cyclicBSBIConnecting_eq_raw
    (hUnit : ∃ e : A, ∀ a : A, e * a = a) (n : ℕ) :
    cyclicBSBIConnecting k A hUnit n =
      cyclicSBIConnecting k A n ≫ (cyclicBToFirstTwoHomologyIso k A hUnit (n + 1)).inv := by
  change (((cyclicBConnesSBIPresentation k A hUnit).tailHomologyIso n).inv ≫
      (cyclicTwoColumnSequence_shortExact k A).δ (n + 2) (n + 1) (by simp)) ≫
        ((cyclicBConnesSBIPresentation k A hUnit).hIso (n + 1)).inv = _
  rw [cyclicBConnesSBIPresentation_hIso, cyclicSBIConnecting_eq_δ]
  rfl

/-- The periodicity map of the left-unit SBI presentation.

Replacing the two-column ordinary term by the `b`-complex retains the period-two map `S_n :
HC_(n+2)(A) → HC_n(A)`. -/
theorem cyclicBConnesSBIPresentation_S
    (hUnit : ∃ e : A, ∀ a : A, e * a = a) (n : ℕ) :
    (cyclicBConnesSBIPresentation k A hUnit).S n = cyclicSBIPeriodicity k A n := rfl

/-- Exactness of the left-unital Hochschild SBI diagram.

For an algebra with a left unit, the regular Hochschild and cyclic homology terms form an
exact connective SBI diagram. -/
theorem cyclicBSBIDiagram_exact (hUnit : ∃ e : A, ∀ a : A, e * a = a) :
    (cyclicBSBIDiagram k A hUnit).Exact :=
  (cyclicBConnesSBIPresentation k A hUnit).sbiDiagram_exact

/-- The low-degree conditions of the left-unital SBI diagram.

The left-unit ordinary model satisfies the connective boundary conditions inherited from the
cyclic tail's vanishing in degrees below two. -/
theorem cyclicBSBIDiagram_connectiveBoundary (hUnit : ∃ e : A, ∀ a : A, e * a = a) :
    (cyclicBSBIDiagram k A hUnit).ConnectiveBoundary :=
  (cyclicBConnesSBIPresentation k A hUnit).sbiDiagram_connectiveBoundary

/-- The degree-zero Hochschild-to-cyclic isomorphism from a left unit.

If `A` has a left unit, the inclusion `H_0(b(A)) → HC_0(A)` is an isomorphism. -/
theorem cyclicBSBIInclusion_isIso_zero (hUnit : ∃ e : A, ∀ a : A, e * a = a) :
    IsIso (cyclicBSBIInclusion k A hUnit 0) :=
  (cyclicBConnesSBIPresentation k A hUnit).isIso_I_zero

/-- The degree-one Hochschild-to-cyclic epimorphism from a left unit.

If `A` has a left unit, the inclusion `H_1(b(A)) → HC_1(A)` is epic. -/
theorem cyclicBSBIInclusion_epi_one (hUnit : ∃ e : A, ∀ a : A, e * a = a) :
    Epi (cyclicBSBIInclusion k A hUnit 1) :=
  (cyclicBConnesSBIPresentation k A hUnit).epi_I_one

section PresentationMaps

variable {k A} {B : Type v} [NonUnitalRing B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- The left-unit SBI presentation map of an algebra homomorphism.

A nonunital ground-algebra map between algebras with left units induces a presentation map
using its regular Hochschild map, two-column short-complex map, and tail comparison. -/
def cyclicBConnesSBIPresentationMap (f : A →ₙₐ[k] B)
    (hA : ∃ e : A, ∀ a : A, e * a = a) (hB : ∃ e : B, ∀ b : B, e * b = b) :
    cyclicBConnesSBIPresentation k A hA ⟶ cyclicBConnesSBIPresentation k B hB where
  ordinaryMap := cyclicBComplexHom f
  shortMap := cyclicTwoColumnSequenceMap f
  ordinaryComparison_naturality := cyclicBToFirstTwo_naturality f
  tailIso_naturality := (cyclicConnesSBIPresentationMap f).tailIso_naturality

/-- The ordinary component of a left-unit presentation map.

The ordinary component is the regular `b`-complex map induced by the algebra homomorphism. -/
theorem cyclicBConnesSBIPresentationMap_ordinaryMap (f : A →ₙₐ[k] B)
    (hA : ∃ e : A, ∀ a : A, e * a = a) (hB : ∃ e : B, ∀ b : B, e * b = b) :
    (cyclicBConnesSBIPresentationMap f hA hB).ordinaryMap = cyclicBComplexHom f := rfl

/-- The short-complex component of a left-unit presentation map.

The short-complex component is the induced map on retained two columns, full cyclic total, and
cokernel tail. -/
theorem cyclicBConnesSBIPresentationMap_shortMap (f : A →ₙₐ[k] B)
    (hA : ∃ e : A, ∀ a : A, e * a = a) (hB : ∃ e : B, ∀ b : B, e * b = b) :
    (cyclicBConnesSBIPresentationMap f hA hB).shortMap = cyclicTwoColumnSequenceMap f := rfl

/-- The identity map of a left-unit SBI presentation.

For any witness of a left unit, the identity algebra homomorphism induces the identity on the
associated presentation. -/
theorem cyclicBConnesSBIPresentationMap_id (hA : ∃ e : A, ∀ a : A, e * a = a) :
    cyclicBConnesSBIPresentationMap (NonUnitalAlgHom.id k A) hA hA =
      𝟙 (cyclicBConnesSBIPresentation k A hA) := by
  apply CategoryTheory.ConnesSBIPresentation.hom_ext
  · exact cyclicBComplexHom_id
  · exact cyclicTwoColumnSequenceMap_id

variable {D : Type v} [NonUnitalRing D] [Module k D]
  [IsScalarTower k D D] [SMulCommClass k D D]

/-- Composition of left-unit SBI presentation maps.

For composable nonunital maps between algebras with left units, the induced presentation maps
compose, with the given endpoint left-unit witnesses. -/
theorem cyclicBConnesSBIPresentationMap_comp (f : A →ₙₐ[k] B) (g : B →ₙₐ[k] D)
    (hA : ∃ e : A, ∀ a : A, e * a = a) (hB : ∃ e : B, ∀ b : B, e * b = b)
    (hD : ∃ e : D, ∀ d : D, e * d = d) :
    cyclicBConnesSBIPresentationMap (g.comp f) hA hD =
      cyclicBConnesSBIPresentationMap f hA hB ≫ cyclicBConnesSBIPresentationMap g hB hD := by
  apply CategoryTheory.ConnesSBIPresentation.hom_ext
  · exact cyclicBComplexHom_comp f g
  · exact cyclicTwoColumnSequenceMap_comp f g

/-- The SBI homology diagram map between left-unital algebras.

A nonunital algebra map and witnesses of left units at both endpoints induce a morphism of
their regular Hochschild and cyclic SBI diagrams. -/
def cyclicBSBIDiagramMap (f : A →ₙₐ[k] B)
    (hA : ∃ e : A, ∀ a : A, e * a = a) (hB : ∃ e : B, ∀ b : B, e * b = b) :
    cyclicBSBIDiagram k A hA ⟶ cyclicBSBIDiagram k B hB :=
  (cyclicBConnesSBIPresentationMap f hA hB).toSBIHom

/-- The Hochschild component of a left-unit SBI homology map.

The ordinary degree-`n` component is the homology map of the regular `b`-complex algebra map. -/
theorem cyclicBSBIDiagramMap_hMap (f : A →ₙₐ[k] B)
    (hA : ∃ e : A, ∀ a : A, e * a = a) (hB : ∃ e : B, ∀ b : B, e * b = b) (n : ℕ) :
    (cyclicBSBIDiagramMap f hA hB).hMap n =
      HomologicalComplex.homologyMap (cyclicBComplexHom f) n := rfl

/-- The cyclic component of a left-unit SBI homology map.

The cyclic degree-`n` component is the cyclic-homology map induced by the algebra
homomorphism. -/
theorem cyclicBSBIDiagramMap_hcMap (f : A →ₙₐ[k] B)
    (hA : ∃ e : A, ∀ a : A, e * a = a) (hB : ∃ e : B, ∀ b : B, e * b = b) (n : ℕ) :
    (cyclicBSBIDiagramMap f hA hB).hcMap n = cyclicHomologyMap f n := rfl

/-- The identity map of a left-unit SBI homology diagram.

The identity algebra homomorphism induces the identity on the regular Hochschild and cyclic
homology diagram. -/
theorem cyclicBSBIDiagramMap_id (hA : ∃ e : A, ∀ a : A, e * a = a) :
    cyclicBSBIDiagramMap (NonUnitalAlgHom.id k A) hA hA = 𝟙 (cyclicBSBIDiagram k A hA) := by
  rw [cyclicBSBIDiagramMap, cyclicBConnesSBIPresentationMap_id]
  exact CategoryTheory.ConnesSBIPresentation.Hom.toSBIHom_id _

/-- Composition of left-unit SBI homology diagram maps.

The diagram map induced by a composite nonunital algebra homomorphism is the composite of the
two diagram maps. -/
theorem cyclicBSBIDiagramMap_comp (f : A →ₙₐ[k] B) (g : B →ₙₐ[k] D)
    (hA : ∃ e : A, ∀ a : A, e * a = a) (hB : ∃ e : B, ∀ b : B, e * b = b)
    (hD : ∃ e : D, ∀ d : D, e * d = d) :
    cyclicBSBIDiagramMap (g.comp f) hA hD =
      cyclicBSBIDiagramMap f hA hB ≫ cyclicBSBIDiagramMap g hB hD := by
  rw [cyclicBSBIDiagramMap, cyclicBConnesSBIPresentationMap_comp f g hA hB hD]
  exact CategoryTheory.ConnesSBIPresentation.Hom.toSBIHom_comp _ _

/-- Naturality of the left-unital Hochschild-to-cyclic inclusion.

For maps between algebras with left units, the regular Hochschild and cyclic homology maps
commute with `I_n : H_n(b) → HC_n`. -/
@[reassoc]
theorem cyclicBSBIInclusion_naturality (f : A →ₙₐ[k] B)
    (hA : ∃ e : A, ∀ a : A, e * a = a) (hB : ∃ e : B, ∀ b : B, e * b = b) (n : ℕ) :
    HomologicalComplex.homologyMap (cyclicBComplexHom f) n ≫ cyclicBSBIInclusion k B hB n =
      cyclicBSBIInclusion k A hA n ≫ cyclicHomologyMap f n :=
  (cyclicBSBIDiagramMap f hA hB).I_naturality n |>.symm

/-- Naturality of the left-unital SBI connecting map.

For maps between algebras with left units, the cyclic map in degree `n` and regular Hochschild
map in degree `n+1` commute with `B_n`. -/
@[reassoc]
theorem cyclicBSBIConnecting_naturality (f : A →ₙₐ[k] B)
    (hA : ∃ e : A, ∀ a : A, e * a = a) (hB : ∃ e : B, ∀ b : B, e * b = b) (n : ℕ) :
    cyclicHomologyMap f n ≫ cyclicBSBIConnecting k B hB n =
      cyclicBSBIConnecting k A hA n ≫
        HomologicalComplex.homologyMap (cyclicBComplexHom f) (n + 1) :=
  (cyclicBSBIDiagramMap f hA hB).B_naturality n |>.symm

/-- The equivalence of Hochschild and cyclic quasi-isomorphisms with left units.

For a nonunital algebra map between algebras with left units, the regular `b`-complex map is a
quasi-isomorphism if and only if its full cyclic-total map is a quasi-isomorphism. -/
theorem cyclicBComplexHom_quasiIso_iff_cyclicTotalHom (f : A →ₙₐ[k] B)
    (hA : ∃ e : A, ∀ a : A, e * a = a) (hB : ∃ e : B, ∀ b : B, e * b = b) :
    QuasiIso (cyclicBComplexHom f) ↔ QuasiIso (cyclicTotalHom f) := by
  change QuasiIso (cyclicBConnesSBIPresentationMap f hA hB).ordinaryMap ↔
    QuasiIso (cyclicBConnesSBIPresentationMap f hA hB).shortMap.τ₂
  exact (cyclicBConnesSBIPresentationMap f hA hB).quasiIso_ordinaryMap_iff_shortMap_τ₂

/-- The equivalence of Hochschild and cyclic homology isomorphisms with left units.

For a nonunital map between algebras with left units, all regular Hochschild homology maps are
isomorphisms if and only if all cyclic homology maps are isomorphisms. -/
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
