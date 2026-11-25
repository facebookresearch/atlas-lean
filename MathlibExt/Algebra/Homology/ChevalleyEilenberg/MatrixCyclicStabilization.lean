/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import MathlibExt.Algebra.Homology.ChainComplex.PositiveTailFunctor
public import MathlibExt.Algebra.Homology.HomologicalComplex.ColimitDifferential
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.MatrixCyclicChainMap

/-!
# Stabilized matrix trace maps

The directed colimit of finite matrix Chevalley–Eilenberg complexes has zero boundary from
degree one to zero, so positive-tail homology identifies with homology in the next degree.

Over a commutative rational algebra, the finite matrix trace chain maps descend to this
colimit and induce compatible Connes and cyclic homology maps, determined by their
finite-stage restrictions.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v

namespace ChevalleyEilenberg

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]

/-- The colimit of the finite matrix CE diagram. -/
abbrev stableMatrixCEComplex : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  colimit (matrixComplexFunctor k A)

/-- The positive tail of the colimit, with the negative CE differential. -/
abbrev stableMatrixPositiveTail : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  ChainComplex.positiveTail (stableMatrixCEComplex k A)

/-- The positive tail of the finite-matrix colimit complex with its differential negated. -/
abbrev stableMatrixPrintedPositiveTail : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  ChainComplex.positiveTail (HomologicalComplex.negateDifferentials (stableMatrixCEComplex k A))

/-- The degree-one vanishing differential remains zero in the colimit. -/
theorem stableMatrixCEComplex_d_one_zero : (stableMatrixCEComplex k A).d 1 0 = 0 :=
  HomologicalComplex.colimit_d_eq_zero (matrixComplexFunctor k A) 1 0
    (fun m => matrixComplex_d_one_zero k A m)

/-- The canonical homology comparison between the colimit tail and the shifted full colimit. -/
def stableMatrixPositiveTailHomologyIso (n : ℕ) :
    (stableMatrixPositiveTail k A).homology n ≅ (stableMatrixCEComplex k A).homology (n + 1) :=
  ChainComplex.positiveTailHomologyIso (stableMatrixCEComplex k A)
    (stableMatrixCEComplex_d_one_zero k A) n

section Rational

variable [Algebra ℚ k]

/-- The finite-matrix trace cocone for the positive tail of the canonical Chevalley–Eilenberg
complex. -/
def matrixCyclicWeibelCocone : Cocone
    (matrixComplexFunctor k A ⋙ ChainComplex.positiveTailFunctor (ModuleCat.{max u v} k)) where
  pt := ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k A
  ι :=
    { app := matrixCyclicWeibelChainMap k A
      naturality m n h := by
        change matrixPositiveTailMap k A (leOfHom h) ≫ matrixCyclicWeibelChainMap k A n =
          matrixCyclicWeibelChainMap k A m ≫ 𝟙 _
        exact (matrixCyclicWeibelChainMap_zeroCorner k A (leOfHom h)).trans (Category.comp_id _).symm }

/-- The finite-matrix trace cocone for the positive bracket differential. -/
def matrixCyclicPrintedCocone : Cocone
    (matrixComplexFunctor k A ⋙ ChainComplex.negatedPositiveTailFunctor (ModuleCat.{max u v} k)) where
  pt := ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k A
  ι :=
    { app := matrixCyclicChainMap k A
      naturality m n h := by
        change matrixCyclicPrintedZeroCorner k A (leOfHom h) ≫ matrixCyclicChainMap k A n =
          matrixCyclicChainMap k A m ≫ 𝟙 _
        exact (matrixCyclicChainMap_zeroCorner k A (leOfHom h)).trans (Category.comp_id _).symm }

/-- The colimit trace chain map from the positive tail of the canonical matrix Chevalley–Eilenberg
complex. -/
def stableMatrixCyclicWeibelChainMap : stableMatrixPositiveTail k A ⟶
    ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k A :=
  (isColimitOfPreserves (ChainComplex.positiveTailFunctor (ModuleCat.{max u v} k))
    (colimit.isColimit (matrixComplexFunctor k A))).desc (matrixCyclicWeibelCocone k A)

/-- The colimit trace chain map for the positive bracket differential. -/
def stableMatrixCyclicChainMap : stableMatrixPrintedPositiveTail k A ⟶
    ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k A :=
  (isColimitOfPreserves (ChainComplex.negatedPositiveTailFunctor (ModuleCat.{max u v} k))
    (colimit.isColimit (matrixComplexFunctor k A))).desc (matrixCyclicPrintedCocone k A)

/-- The stabilized cyclic trace chain map agrees with each finite matrix trace after the
finite-stage inclusion. -/
@[reassoc]
theorem stableMatrixCyclicWeibelChainMap_ι (m : ℕ) :
    ChainComplex.positiveTailMap (colimit.ι (matrixComplexFunctor k A) m) ≫
        stableMatrixCyclicWeibelChainMap k A = matrixCyclicWeibelChainMap k A m :=
  (isColimitOfPreserves (ChainComplex.positiveTailFunctor (ModuleCat.{max u v} k))
    (colimit.isColimit (matrixComplexFunctor k A))).fac (matrixCyclicWeibelCocone k A) m

/-- The descended printed-positive map retains every finite theta-trace specialization. -/
@[reassoc]
theorem stableMatrixCyclicChainMap_ι (m : ℕ) :
    ChainComplex.positiveTailMap
        (HomologicalComplex.negateMap (colimit.ι (matrixComplexFunctor k A) m)) ≫
      stableMatrixCyclicChainMap k A = matrixCyclicChainMap k A m :=
  (isColimitOfPreserves (ChainComplex.negatedPositiveTailFunctor (ModuleCat.{max u v} k))
    (colimit.isColimit (matrixComplexFunctor k A))).fac (matrixCyclicPrintedCocone k A) m

/-- The shifted homology map from the colimit CE complex to Connes homology. -/
def stableMatrixCyclicConnesHomologyMap (n : ℕ) :
    (stableMatrixCEComplex k A).homology (n + 1) ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.connesHomology k A n :=
  (stableMatrixPositiveTailHomologyIso k A n).inv ≫
    HomologicalComplex.homologyMap (stableMatrixCyclicWeibelChainMap k A) n

/-- The map from homology of the matrix colimit complex in degree n + 1 to cyclic homology in
degree n. -/
def stableMatrixCyclicHomologyMap (n : ℕ) :
    (stableMatrixCEComplex k A).homology (n + 1) ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.cyclicHomology k A n :=
  stableMatrixCyclicConnesHomologyMap k A n ≫
    (ModuleCat.Algebra.Hochschild.NonUnital.cyclicToConnesHomologyIso k A n).inv

/-- The colimit HC lift factors through the rational Connes comparison. -/
@[reassoc]
theorem stableMatrixCyclicHomologyMap_comp_connes (n : ℕ) :
    stableMatrixCyclicHomologyMap k A n ≫
      ModuleCat.Algebra.Hochschild.NonUnital.cyclicToConnesHomology k A n =
        stableMatrixCyclicConnesHomologyMap k A n := by
  rw [stableMatrixCyclicHomologyMap, Category.assoc,
    ← ModuleCat.Algebra.Hochschild.NonUnital.cyclicToConnesHomologyIso_hom,
    Iso.inv_hom_id, Category.comp_id]

/-- The homology map of every canonical finite inclusion gives the finite lambda-to-HC map. -/
theorem stableMatrixCyclicHomologyMap_ι (m n : ℕ) :
    HomologicalComplex.homologyMap (colimit.ι (matrixComplexFunctor k A) m) (n + 1) ≫
        stableMatrixCyclicHomologyMap k A n = matrixCyclicHomologyMap k A m n := by
  let eM := matrixPositiveTailHomologyIso k A m n
  let eS := stableMatrixPositiveTailHomologyIso k A n
  let h0 : matrixHomology k A m (n + 1) ⟶ (stableMatrixCEComplex k A).homology (n + 1) :=
    HomologicalComplex.homologyMap (colimit.ι (matrixComplexFunctor k A) m) (n + 1)
  let ht : (matrixPositiveTail k A m).homology n ⟶ (stableMatrixPositiveTail k A).homology n :=
    HomologicalComplex.homologyMap
      (ChainComplex.positiveTailMap (colimit.ι (matrixComplexFunctor k A) m)) n
  let fM : (matrixPositiveTail k A m).homology n ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.connesHomology k A n :=
    HomologicalComplex.homologyMap (matrixCyclicWeibelChainMap k A m) n
  let fS : (stableMatrixPositiveTail k A).homology n ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.connesHomology k A n :=
    HomologicalComplex.homologyMap (stableMatrixCyclicWeibelChainMap k A) n
  have he : ht ≫ eS.hom = eM.hom ≫ h0 :=
    ChainComplex.positiveTailHomologyIso_naturality (colimit.ι (matrixComplexFunctor k A) m)
      (matrixComplex_d_one_zero k A m) (stableMatrixCEComplex_d_one_zero k A) n
  have heInv : h0 ≫ eS.inv = eM.inv ≫ ht := by
    apply (cancel_mono eS.hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
      he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hm : ht ≫ fS = fM := by
    have hmap := congrArg (fun f => HomologicalComplex.homologyMap f n)
      (stableMatrixCyclicWeibelChainMap_ι k A m)
    simp only [HomologicalComplex.homologyMap_comp] at hmap
    exact hmap
  have hn : h0 ≫ (eS.inv ≫ fS) = eM.inv ≫ fM := by
    calc
      _ = (h0 ≫ eS.inv) ≫ fS := (Category.assoc _ _ _).symm
      _ = (eM.inv ≫ ht) ≫ fS := congrArg (fun f => f ≫ fS) heInv
      _ = eM.inv ≫ (ht ≫ fS) := Category.assoc _ _ _
      _ = _ := congrArg (fun f => eM.inv ≫ f) hm
  let c := (ModuleCat.Algebra.Hochschild.NonUnital.cyclicToConnesHomologyIso k A n).inv
  change h0 ≫ ((eS.inv ≫ fS) ≫ c) = (eM.inv ≫ fM) ≫ c
  exact (Category.assoc h0 (eS.inv ≫ fS) c).symm.trans (congrArg (fun f => f ≫ c) hn)

end Rational

end ChevalleyEilenberg
