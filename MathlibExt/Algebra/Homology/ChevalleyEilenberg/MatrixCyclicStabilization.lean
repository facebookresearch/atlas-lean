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
# Cyclic trace maps on the directed matrix CE colimit

Let `k` be a commutative ring and `A` a unital `k`-algebra. Take the directed colimit of
finite matrix CE complexes under top-left zero extension. Its differential from degree one to
zero vanishes, so positive-tail homology in degree `n` identifies with full-colimit homology
in degree `n+1`.

Over rational ground scalars, the compatible finite trace maps give cocones for the canonical
positive tail and for its negated-differential convention. Their colimit descents map to the
cyclic quotient complex. The induced quotient and cyclic homology maps are characterized by
their restrictions along the finite-stage inclusions.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v

namespace ChevalleyEilenberg

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]

/-- The directed colimit of finite matrix CE complexes.

Take the colimit of the natural-number size functor with top-left zero-extension maps. -/
abbrev stableMatrixCEComplex : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  colimit (matrixComplexFunctor k A)

/-- The canonical positive tail of the matrix CE colimit.

Restrict the colimit CE complex to positive exterior degrees, retaining its canonical
differential. -/
abbrev stableMatrixPositiveTail : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  ChainComplex.positiveTail (stableMatrixCEComplex k A)

/-- The negated-differential positive tail of the matrix CE colimit.

Negate the colimit differential and restrict to positive exterior degrees. -/
abbrev stableMatrixPrintedPositiveTail : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  ChainComplex.positiveTail (HomologicalComplex.negateDifferentials (stableMatrixCEComplex k A))

/-- Vanishing of the degree-one differential in the matrix CE colimit.

The finite-stage zero degree-one differentials induce a zero differential from degree one to
zero in the colimit. -/
theorem stableMatrixCEComplex_d_one_zero : (stableMatrixCEComplex k A).d 1 0 = 0 :=
  HomologicalComplex.colimit_d_eq_zero (matrixComplexFunctor k A) 1 0
    (fun m => matrixComplex_d_one_zero k A m)

/-- The positive-tail homology comparison for the matrix CE colimit.

The zero degree-one boundary gives `H_n(tail C) ≅ H_(n+1)(C)` for the full matrix CE colimit. -/
def stableMatrixPositiveTailHomologyIso (n : ℕ) :
    (stableMatrixPositiveTail k A).homology n ≅ (stableMatrixCEComplex k A).homology (n + 1) :=
  ChainComplex.positiveTailHomologyIso (stableMatrixCEComplex k A)
    (stableMatrixCEComplex_d_one_zero k A) n

section Rational

variable [Algebra ℚ k]

/-- The finite trace cocone on canonical positive matrix CE tails.

The degree-signed finite matrix trace maps form a cocone with target the cyclic quotient
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

/-- The finite trace cocone on positive-bracket matrix CE tails.

The tail-alternating finite trace maps form a cocone after differential negation, with target
the cyclic quotient complex. -/
def matrixCyclicPrintedCocone : Cocone
    (matrixComplexFunctor k A ⋙ ChainComplex.negatedPositiveTailFunctor (ModuleCat.{max u v} k)) where
  pt := ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k A
  ι :=
    { app := matrixCyclicChainMap k A
      naturality m n h := by
        change matrixCyclicPrintedZeroCorner k A (leOfHom h) ≫ matrixCyclicChainMap k A n =
          matrixCyclicChainMap k A m ≫ 𝟙 _
        exact (matrixCyclicChainMap_zeroCorner k A (leOfHom h)).trans (Category.comp_id _).symm }

/-- The colimit cyclic trace from the canonical positive matrix tail.

Descend the compatible degree-signed finite trace maps to the positive tail of the matrix CE
colimit. -/
def stableMatrixCyclicWeibelChainMap : stableMatrixPositiveTail k A ⟶
    ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k A :=
  (isColimitOfPreserves (ChainComplex.positiveTailFunctor (ModuleCat.{max u v} k))
    (colimit.isColimit (matrixComplexFunctor k A))).desc (matrixCyclicWeibelCocone k A)

/-- The colimit cyclic trace from the positive-bracket matrix tail.

Descend the compatible finite tail-alternating trace maps to the negated-differential positive
tail of the colimit. -/
def stableMatrixCyclicChainMap : stableMatrixPrintedPositiveTail k A ⟶
    ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k A :=
  (isColimitOfPreserves (ChainComplex.negatedPositiveTailFunctor (ModuleCat.{max u v} k))
    (colimit.isColimit (matrixComplexFunctor k A))).desc (matrixCyclicPrintedCocone k A)

/-- The finite-stage restriction of canonical colimit cyclic trace.

The positive-tail finite-stage inclusion followed by the colimit trace is the finite degree-
signed matrix trace. -/
@[reassoc]
theorem stableMatrixCyclicWeibelChainMap_ι (m : ℕ) :
    ChainComplex.positiveTailMap (colimit.ι (matrixComplexFunctor k A) m) ≫
        stableMatrixCyclicWeibelChainMap k A = matrixCyclicWeibelChainMap k A m :=
  (isColimitOfPreserves (ChainComplex.positiveTailFunctor (ModuleCat.{max u v} k))
    (colimit.isColimit (matrixComplexFunctor k A))).fac (matrixCyclicWeibelCocone k A) m

/-- The finite-stage restriction of positive-bracket colimit cyclic trace.

The negated-differential finite-stage tail inclusion followed by the colimit trace is the
finite tail-alternating trace. -/
@[reassoc]
theorem stableMatrixCyclicChainMap_ι (m : ℕ) :
    ChainComplex.positiveTailMap
        (HomologicalComplex.negateMap (colimit.ι (matrixComplexFunctor k A) m)) ≫
      stableMatrixCyclicChainMap k A = matrixCyclicChainMap k A m :=
  (isColimitOfPreserves (ChainComplex.negatedPositiveTailFunctor (ModuleCat.{max u v} k))
    (colimit.isColimit (matrixComplexFunctor k A))).fac (matrixCyclicPrintedCocone k A) m

/-- The matrix-colimit CE map into cyclic quotient homology.

The full-colimit-to-tail homology comparison and the colimit trace give a map from full degree
`n+1` to quotient homology degree `n`. -/
def stableMatrixCyclicConnesHomologyMap (n : ℕ) :
    (stableMatrixCEComplex k A).homology (n + 1) ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.connesHomology k A n :=
  (stableMatrixPositiveTailHomologyIso k A n).inv ≫
    HomologicalComplex.homologyMap (stableMatrixCyclicWeibelChainMap k A) n

/-- The matrix-colimit CE map into cyclic homology.

Follow the quotient homology map by the inverse rational cyclic-to-quotient comparison. -/
def stableMatrixCyclicHomologyMap (n : ℕ) :
    (stableMatrixCEComplex k A).homology (n + 1) ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.cyclicHomology k A n :=
  stableMatrixCyclicConnesHomologyMap k A n ≫
    (ModuleCat.Algebra.Hochschild.NonUnital.cyclicToConnesHomologyIso k A n).inv

/-- The quotient factorization of the matrix-colimit cyclic homology map.

Composing the cyclic homology map with the cyclic-to-quotient comparison gives the colimit
trace map to quotient homology. -/
@[reassoc]
theorem stableMatrixCyclicHomologyMap_comp_connes (n : ℕ) :
    stableMatrixCyclicHomologyMap k A n ≫
      ModuleCat.Algebra.Hochschild.NonUnital.cyclicToConnesHomology k A n =
        stableMatrixCyclicConnesHomologyMap k A n := by
  rw [stableMatrixCyclicHomologyMap, Category.assoc,
    ← ModuleCat.Algebra.Hochschild.NonUnital.cyclicToConnesHomologyIso_hom,
    Iso.inv_hom_id, Category.comp_id]

/-- The finite-stage homology restriction of matrix-colimit cyclic trace.

The finite-stage CE homology inclusion followed by the colimit cyclic homology map equals the
finite matrix cyclic homology map. -/
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
