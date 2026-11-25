/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.MatrixCyclicStabilization

/-!
# Coefficient naturality of stabilized matrix trace maps

Algebra homomorphisms act on the directed colimit of finite matrix Chevalley–Eilenberg
complexes. Over a commutative rational algebra, the stabilized trace chain maps commute with
these coefficient maps.

The resulting Connes and cyclic homology maps inherit the same naturality.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v

namespace ChevalleyEilenberg

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]
  {B : Type v} [Ring B] [Algebra k B]

/-- The coefficient map on the colimit of finite matrix CE complexes. -/
def stableMatrixCoefficientMap (f : A →ₐ[k] B) :
    stableMatrixCEComplex k A ⟶ stableMatrixCEComplex k B :=
  colimMap (matrixCoefficientNatTrans k A f)

/-- The colimit coefficient map retains the coefficient map at every finite matrix stage. -/
@[reassoc]
theorem stableMatrixCoefficientMap_ι (f : A →ₐ[k] B) (m : ℕ) :
    colimit.ι (matrixComplexFunctor k A) m ≫ stableMatrixCoefficientMap k A f =
      matrixCoefficientMap k A f m ≫ colimit.ι (matrixComplexFunctor k B) m :=
  ι_colimMap (matrixCoefficientNatTrans k A f) m

section Rational

variable [Algebra ℚ k]

/-- The stabilized cyclic trace chain map is natural in algebra homomorphisms of coefficients. -/
theorem stableMatrixCyclicWeibelChainMap_naturality (f : A →ₐ[k] B) :
    ChainComplex.positiveTailMap (stableMatrixCoefficientMap k A f) ≫
        stableMatrixCyclicWeibelChainMap k B =
      stableMatrixCyclicWeibelChainMap k A ≫
        ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHom f.toNonUnitalAlgHom := by
  let F := ChainComplex.positiveTailFunctor (ModuleCat.{max u v} k)
  let hc := isColimitOfPreserves F (colimit.isColimit (matrixComplexFunctor k A))
  apply hc.hom_ext
  intro m
  let a : matrixComplex k A m ⟶ stableMatrixCEComplex k A := colimit.ι (matrixComplexFunctor k A) m
  let b : matrixComplex k B m ⟶ stableMatrixCEComplex k B := colimit.ι (matrixComplexFunctor k B) m
  let q := matrixCoefficientMap k A f m
  let c := ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHom f.toNonUnitalAlgHom
  let wA : F.obj (stableMatrixCEComplex k A) ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k A := stableMatrixCyclicWeibelChainMap k A
  let wB : F.obj (stableMatrixCEComplex k B) ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k B := stableMatrixCyclicWeibelChainMap k B
  let lA : F.obj (matrixComplex k A m) ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k A := matrixCyclicWeibelChainMap k A m
  let lB : F.obj (matrixComplex k B m) ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k B := matrixCyclicWeibelChainMap k B m
  have hi : a ≫ stableMatrixCoefficientMap k A f = q ≫ b := stableMatrixCoefficientMap_ι k A f m
  have hF : F.map a ≫ F.map (stableMatrixCoefficientMap k A f) = F.map q ≫ F.map b :=
    (F.map_comp a (stableMatrixCoefficientMap k A f)).symm.trans
      ((congrArg F.map hi).trans (F.map_comp q b))
  have hA : F.map a ≫ wA = lA := stableMatrixCyclicWeibelChainMap_ι k A m
  have hB : F.map b ≫ wB = lB := stableMatrixCyclicWeibelChainMap_ι k B m
  have hN : F.map q ≫ lB = lA ≫ c := matrixCyclicWeibelChainMap_naturality k A f m
  change F.map a ≫ (F.map (stableMatrixCoefficientMap k A f) ≫ wB) = F.map a ≫ (wA ≫ c)
  calc
    _ = (F.map a ≫ F.map (stableMatrixCoefficientMap k A f)) ≫ wB := (Category.assoc _ _ _).symm
    _ = (F.map q ≫ F.map b) ≫ wB :=
      congrArg (fun g : F.obj (matrixComplex k A m) ⟶ F.obj (stableMatrixCEComplex k B) => g ≫ wB) hF
    _ = F.map q ≫ (F.map b ≫ wB) := Category.assoc _ _ _
    _ = F.map q ≫ lB := congrArg (fun g => F.map q ≫ g) hB
    _ = lA ≫ c := hN
    _ = _ := (congrArg (fun g => g ≫ c) hA.symm).trans (Category.assoc _ _ _)

/-- Printed-positive colimit theta traces preserve the same coefficient square. -/
theorem stableMatrixCyclicChainMap_naturality (f : A →ₐ[k] B) :
    ChainComplex.positiveTailMap (HomologicalComplex.negateMap (stableMatrixCoefficientMap k A f)) ≫
        stableMatrixCyclicChainMap k B =
      stableMatrixCyclicChainMap k A ≫
        ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHom f.toNonUnitalAlgHom := by
  let F := ChainComplex.negatedPositiveTailFunctor (ModuleCat.{max u v} k)
  let hc := isColimitOfPreserves F (colimit.isColimit (matrixComplexFunctor k A))
  apply hc.hom_ext
  intro m
  let a : matrixComplex k A m ⟶ stableMatrixCEComplex k A := colimit.ι (matrixComplexFunctor k A) m
  let b : matrixComplex k B m ⟶ stableMatrixCEComplex k B := colimit.ι (matrixComplexFunctor k B) m
  let q := matrixCoefficientMap k A f m
  let c := ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHom f.toNonUnitalAlgHom
  let wA : F.obj (stableMatrixCEComplex k A) ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k A := stableMatrixCyclicChainMap k A
  let wB : F.obj (stableMatrixCEComplex k B) ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k B := stableMatrixCyclicChainMap k B
  let lA : F.obj (matrixComplex k A m) ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k A := matrixCyclicChainMap k A m
  let lB : F.obj (matrixComplex k B m) ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k B := matrixCyclicChainMap k B m
  have hi : a ≫ stableMatrixCoefficientMap k A f = q ≫ b := stableMatrixCoefficientMap_ι k A f m
  have hF : F.map a ≫ F.map (stableMatrixCoefficientMap k A f) = F.map q ≫ F.map b :=
    (F.map_comp a (stableMatrixCoefficientMap k A f)).symm.trans
      ((congrArg F.map hi).trans (F.map_comp q b))
  have hA : F.map a ≫ wA = lA := stableMatrixCyclicChainMap_ι k A m
  have hB : F.map b ≫ wB = lB := stableMatrixCyclicChainMap_ι k B m
  have hN : F.map q ≫ lB = lA ≫ c := matrixCyclicChainMap_naturality k A f m
  change F.map a ≫ (F.map (stableMatrixCoefficientMap k A f) ≫ wB) = F.map a ≫ (wA ≫ c)
  calc
    _ = (F.map a ≫ F.map (stableMatrixCoefficientMap k A f)) ≫ wB := (Category.assoc _ _ _).symm
    _ = (F.map q ≫ F.map b) ≫ wB :=
      congrArg (fun g : F.obj (matrixComplex k A m) ⟶ F.obj (stableMatrixCEComplex k B) => g ≫ wB) hF
    _ = F.map q ≫ (F.map b ≫ wB) := Category.assoc _ _ _
    _ = F.map q ≫ lB := congrArg (fun g => F.map q ≫ g) hB
    _ = lA ≫ c := hN
    _ = _ := (congrArg (fun g => g ≫ c) hA.symm).trans (Category.assoc _ _ _)

/-- The shifted colimit CE homology-to-Connes map retains coefficient naturality. -/
theorem stableMatrixCyclicConnesHomologyMap_naturality (f : A →ₐ[k] B) (n : ℕ) :
    HomologicalComplex.homologyMap (stableMatrixCoefficientMap k A f) (n + 1) ≫
        stableMatrixCyclicConnesHomologyMap k B n =
      stableMatrixCyclicConnesHomologyMap k A n ≫
        ModuleCat.Algebra.Hochschild.NonUnital.connesHomologyMap f.toNonUnitalAlgHom n := by
  let g := stableMatrixCoefficientMap k A f
  let eA := stableMatrixPositiveTailHomologyIso k A n
  let eB := stableMatrixPositiveTailHomologyIso k B n
  let h0 : (stableMatrixCEComplex k A).homology (n + 1) ⟶
      (stableMatrixCEComplex k B).homology (n + 1) := HomologicalComplex.homologyMap g (n + 1)
  let ht : (stableMatrixPositiveTail k A).homology n ⟶ (stableMatrixPositiveTail k B).homology n :=
    HomologicalComplex.homologyMap (ChainComplex.positiveTailMap g) n
  let fA : (stableMatrixPositiveTail k A).homology n ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.connesHomology k A n :=
    HomologicalComplex.homologyMap (stableMatrixCyclicWeibelChainMap k A) n
  let fB : (stableMatrixPositiveTail k B).homology n ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.connesHomology k B n :=
    HomologicalComplex.homologyMap (stableMatrixCyclicWeibelChainMap k B) n
  let c := ModuleCat.Algebra.Hochschild.NonUnital.connesHomologyMap f.toNonUnitalAlgHom n
  have he : ht ≫ eB.hom = eA.hom ≫ h0 :=
    ChainComplex.positiveTailHomologyIso_naturality g
      (stableMatrixCEComplex_d_one_zero k A) (stableMatrixCEComplex_d_one_zero k B) n
  have heInv : h0 ≫ eB.inv = eA.inv ≫ ht := by
    apply (cancel_mono eB.hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
      he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hm : ht ≫ fB = fA ≫ c := by
    have hmap := congrArg (fun h => HomologicalComplex.homologyMap h n)
      (stableMatrixCyclicWeibelChainMap_naturality k A f)
    simp only [HomologicalComplex.homologyMap_comp] at hmap
    exact hmap
  change h0 ≫ (eB.inv ≫ fB) = (eA.inv ≫ fA) ≫ c
  calc
    _ = (h0 ≫ eB.inv) ≫ fB := (Category.assoc _ _ _).symm
    _ = (eA.inv ≫ ht) ≫ fB := congrArg (fun h => h ≫ fB) heInv
    _ = eA.inv ≫ (ht ≫ fB) := Category.assoc _ _ _
    _ = eA.inv ≫ (fA ≫ c) := congrArg (fun h => eA.inv ≫ h) hm
    _ = _ := (Category.assoc _ _ _).symm

/-- The descended rational HC map preserves the coefficient algebra maps. -/
theorem stableMatrixCyclicHomologyMap_naturality (f : A →ₐ[k] B) (n : ℕ) :
    HomologicalComplex.homologyMap (stableMatrixCoefficientMap k A f) (n + 1) ≫
        stableMatrixCyclicHomologyMap k B n =
      stableMatrixCyclicHomologyMap k A n ≫
        ModuleCat.Algebra.Hochschild.NonUnital.cyclicHomologyMap f.toNonUnitalAlgHom n := by
  rw [stableMatrixCyclicHomologyMap, stableMatrixCyclicHomologyMap, ← Category.assoc,
    stableMatrixCyclicConnesHomologyMap_naturality, Category.assoc,
    ModuleCat.Algebra.Hochschild.NonUnital.cyclicToConnesHomologyIso_inv_naturality,
    ← Category.assoc]

end Rational

end ChevalleyEilenberg
