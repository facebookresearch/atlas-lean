/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CyclicBoundary
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.MatrixCyclicDegreeMap
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.ConnesComparison

/-!
# Finite matrix cyclic trace chain maps

For a unital algebra over a commutative rational algebra, normalized exterior
antisymmetrization followed by generalized matrix trace gives chain maps to the Connes
complex. The two differential conventions differ by the degree sign `(-1)^n`.

The induced homology maps lift through the cyclic-to-Connes comparison. Zero extension and
algebra homomorphisms preserve the finite matrix trace formulas.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace ChevalleyEilenberg

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  (A : Type v) [Ring A] [Algebra k A]

local notation "Cλ" => ModuleCat.Algebra.Hochschild.NonUnital.connesComplex

/-- The finite-matrix exterior-to-Connes chain map for the positive bracket convention. -/
def matrixCyclicChainMap (r : ℕ) :
    cyclicPrintedSource k (Matrix (Fin r) (Fin r) A) ⟶ Cλ k A :=
  cyclicExteriorChainMap k (Matrix (Fin r) (Fin r) A) ≫
    ModuleCat.Algebra.Hochschild.Matrix.connesTrace k A r

/-- The finite-matrix cyclic trace chain map from the positive tail of the canonical
Chevalley–Eilenberg complex. -/
def matrixCyclicWeibelChainMap (r : ℕ) : matrixPositiveTail k A r ⟶ Cλ k A :=
  cyclicExteriorWeibelChainMap k (Matrix (Fin r) (Fin r) A) ≫
    ModuleCat.Algebra.Hochschild.Matrix.connesTrace k A r

/-- The chain-map component is exactly the positive-convention degree map. -/
theorem matrixCyclicChainMap_f (r n : ℕ) :
    ((matrixCyclicChainMap k A r).f n).hom = matrixCyclicDegreeMap k A r n := rfl

/-- The component in degree n is `(-1)^n` times the normalized tail trace. -/
theorem matrixCyclicWeibelChainMap_f (r n : ℕ) :
    ((matrixCyclicWeibelChainMap k A r).f n).hom = matrixCyclicWeibelDegreeMap k A r n := by
  have hc : (((matrixCyclicWeibelChainMap k A r).f n).hom :
      (⋀[k]^(n + 1) (Matrix (Fin r) (Fin r) A)) →ₗ[k] ((Cλ k A).X n)) =
      ((ModuleCat.Algebra.Hochschild.Matrix.connesTrace k A r).f n).hom.comp
        ((cyclicExteriorWeibelChainMap k (Matrix (Fin r) (Fin r) A)).f n).hom := rfl
  have hf : (((cyclicExteriorWeibelChainMap k (Matrix (Fin r) (Fin r) A)).f n).hom :
      (⋀[k]^(n + 1) (Matrix (Fin r) (Fin r) A)) →ₗ[k]
        ((Cλ k (Matrix (Fin r) (Fin r) A)).X n)) =
      cyclicExteriorWeibel k (Matrix (Fin r) (Fin r) A) n :=
    cyclicExteriorWeibelChainMap_f k (Matrix (Fin r) (Fin r) A) n
  have hs : ((ModuleCat.Algebra.Hochschild.Matrix.connesTrace k A r).f n).hom.comp
      (cyclicExteriorWeibel k (Matrix (Fin r) (Fin r) A) n) =
      matrixCyclicWeibelDegreeMap k A r n := by
    rw [cyclicExteriorWeibel, LinearMap.comp_smul]
    rfl
  exact hc.trans ((congrArg
    (fun g => ((ModuleCat.Algebra.Hochschild.Matrix.connesTrace k A r).f n).hom.comp g) hf).trans hs)

/-- Top-left zero extension on the exterior complex with the positive bracket differential. -/
def matrixCyclicPrintedZeroCorner {r s : ℕ} (h : r ≤ s) :
    cyclicPrintedSource k (Matrix (Fin r) (Fin r) A) ⟶
      cyclicPrintedSource k (Matrix (Fin s) (Fin s) A) :=
  ChainComplex.positiveTailMap (HomologicalComplex.negateMap (matrixZeroCornerMap k A h))

/-- Positive-convention chain maps are stable under every finite zero corner. -/
theorem matrixCyclicChainMap_zeroCorner {r s : ℕ} (h : r ≤ s) :
    matrixCyclicPrintedZeroCorner k A h ≫ matrixCyclicChainMap k A s = matrixCyclicChainMap k A r := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  change (matrixCyclicDegreeMap k A s n).comp
    (exteriorPower.map (n + 1) (Matrix.zeroExtendLinear (k := k) (A := A) h)) =
      matrixCyclicDegreeMap k A r n
  exact matrixCyclicDegreeMap_zeroCorner k A h n

/-- Top-left zero extension commutes with the finite matrix cyclic trace chain maps. -/
theorem matrixCyclicWeibelChainMap_zeroCorner {r s : ℕ} (h : r ≤ s) :
    matrixPositiveTailMap k A h ≫ matrixCyclicWeibelChainMap k A s = matrixCyclicWeibelChainMap k A r := by
  apply HomologicalComplex.hom_ext
  intro n
  have hs : (((matrixPositiveTailMap k A h).f n).hom :
      (⋀[k]^(n + 1) (Matrix (Fin r) (Fin r) A)) →ₗ[k]
        (⋀[k]^(n + 1) (Matrix (Fin s) (Fin s) A))) =
      exteriorPower.map (n + 1) (Matrix.zeroExtendLinear (k := k) (A := A) h) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro a
    change ((matrixPositiveTailMap k A h).f n).hom (exteriorPower.ιMulti k (n + 1) a) =
      exteriorPower.map (n + 1) (Matrix.zeroExtendLinear (k := k) (A := A) h)
        (exteriorPower.ιMulti k (n + 1) a)
    rw [matrixPositiveTailMap_pure, exteriorPower.map_apply_ιMulti]
    have hfun : (fun i => Matrix.zeroExtend h (a i)) =
        (Matrix.zeroExtendLinear (k := k) (A := A) h) ∘ a := by
      funext i
      exact (Matrix.zeroExtendLinear_apply (k := k) h (a i)).symm
    exact congrArg (exteriorPower.ιMulti k (n + 1)) hfun
  apply ModuleCat.hom_ext
  rw [HomologicalComplex.comp_f, ModuleCat.hom_comp,
    matrixCyclicWeibelChainMap_f, matrixCyclicWeibelChainMap_f, hs]
  exact matrixCyclicWeibelDegreeMap_zeroCorner k A h n

section Coefficients

variable {B : Type v} [Ring B] [Algebra k B]

/-- The positive-convention matrix map induced by the coefficient algebra map. -/
def matrixCyclicPrintedCoefficientMap (f : A →ₐ[k] B) (r : ℕ) :
    cyclicPrintedSource k (Matrix (Fin r) (Fin r) A) ⟶
      cyclicPrintedSource k (Matrix (Fin r) (Fin r) B) :=
  ChainComplex.positiveTailMap (HomologicalComplex.negateMap (matrixCoefficientMap k A f r))

/-- The positive-convention whole matrix chain family is natural in the coefficient map. -/
theorem matrixCyclicChainMap_naturality (f : A →ₐ[k] B) (r : ℕ) :
    matrixCyclicPrintedCoefficientMap k A f r ≫ matrixCyclicChainMap k B r =
      matrixCyclicChainMap k A r ≫
        ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHom f.toNonUnitalAlgHom := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  change (matrixCyclicDegreeMap k B r n).comp
      (exteriorPower.map (n + 1) (f.mapMatrix (m := Fin r)).toLinearMap) =
    (((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHom f.toNonUnitalAlgHom).f n).hom).comp
      (matrixCyclicDegreeMap k A r n)
  exact (matrixCyclicDegreeMap_natural k A f r n).symm

/-- The whole matrix lambda family is natural under every coefficient algebra map. -/
theorem matrixCyclicWeibelChainMap_naturality (f : A →ₐ[k] B) (r : ℕ) :
    ChainComplex.positiveTailMap (matrixCoefficientMap k A f r) ≫ matrixCyclicWeibelChainMap k B r =
      matrixCyclicWeibelChainMap k A r ≫
        ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHom f.toNonUnitalAlgHom := by
  apply HomologicalComplex.hom_ext
  intro n
  have hs : (((ChainComplex.positiveTailMap (matrixCoefficientMap k A f r)).f n).hom :
      (⋀[k]^(n + 1) (Matrix (Fin r) (Fin r) A)) →ₗ[k]
        (⋀[k]^(n + 1) (Matrix (Fin r) (Fin r) B))) =
      exteriorPower.map (n + 1) (f.mapMatrix (m := Fin r)).toLinearMap := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro a
    change ((matrixCoefficientMap k A f r).f (n + 1)).hom
        (exteriorPower.ιMulti k (n + 1) a) =
      exteriorPower.map (n + 1) (f.mapMatrix (m := Fin r)).toLinearMap
        (exteriorPower.ιMulti k (n + 1) a)
    rw [matrixCoefficientMap_pure, exteriorPower.map_apply_ιMulti]
    rfl
  have hn : (matrixCyclicWeibelDegreeMap k B r n).comp
      (exteriorPower.map (n + 1) (f.mapMatrix (m := Fin r)).toLinearMap) =
      (((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHom f.toNonUnitalAlgHom).f n).hom).comp
        (matrixCyclicWeibelDegreeMap k A r n) := by
    rw [matrixCyclicWeibelDegreeMap, matrixCyclicWeibelDegreeMap,
      LinearMap.comp_smul, LinearMap.smul_comp]
    exact congrArg (fun g => (-1 : k) ^ n • g) (matrixCyclicDegreeMap_natural k A f r n).symm
  apply ModuleCat.hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ModuleCat.hom_comp,
    ModuleCat.hom_comp, matrixCyclicWeibelChainMap_f, matrixCyclicWeibelChainMap_f, hs]
  exact hn

end Coefficients

/-- The map from finite-matrix CE homology to Connes quotient homology. -/
def matrixCyclicConnesHomologyMap (r n : ℕ) :
    matrixHomology k A r (n + 1) ⟶ ModuleCat.Algebra.Hochschild.NonUnital.connesHomology k A n :=
  (matrixPositiveTailHomologyIso k A r n).inv ≫
    HomologicalComplex.homologyMap (matrixCyclicWeibelChainMap k A r) n

/-- The HC lift through the rational first-column comparison. -/
def matrixCyclicHomologyMap (r n : ℕ) :
    matrixHomology k A r (n + 1) ⟶ ModuleCat.Algebra.Hochschild.NonUnital.cyclicHomology k A n :=
  matrixCyclicConnesHomologyMap k A r n ≫
    (ModuleCat.Algebra.Hochschild.NonUnital.cyclicToConnesHomologyIso k A n).inv

/-- Composing the finite matrix cyclic-homology map with the cyclic-to-Connes comparison gives the
trace map on Connes homology. -/
@[reassoc]
theorem matrixCyclicHomologyMap_comp_connes (r n : ℕ) :
    matrixCyclicHomologyMap k A r n ≫
      ModuleCat.Algebra.Hochschild.NonUnital.cyclicToConnesHomology k A n =
        matrixCyclicConnesHomologyMap k A r n := by
  rw [matrixCyclicHomologyMap, Category.assoc, ←
    ModuleCat.Algebra.Hochschild.NonUnital.cyclicToConnesHomologyIso_hom,
    Iso.inv_hom_id, Category.comp_id]

/-- Every finite zero corner preserves the lambda-to-HC map. -/
theorem matrixCyclicHomologyMap_zeroCorner {r s : ℕ} (h : r ≤ s) (n : ℕ) :
    matrixZeroCornerHomologyMap k A h (n + 1) ≫ matrixCyclicHomologyMap k A s n =
      matrixCyclicHomologyMap k A r n := by
  let eR := matrixPositiveTailHomologyIso k A r n
  let eS := matrixPositiveTailHomologyIso k A s n
  let h0 : matrixHomology k A r (n + 1) ⟶ matrixHomology k A s (n + 1) :=
    matrixZeroCornerHomologyMap k A h (n + 1)
  let ht : (matrixPositiveTail k A r).homology n ⟶ (matrixPositiveTail k A s).homology n :=
    HomologicalComplex.homologyMap (matrixPositiveTailMap k A h) n
  let fR : (matrixPositiveTail k A r).homology n ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.connesHomology k A n :=
    HomologicalComplex.homologyMap (matrixCyclicWeibelChainMap k A r) n
  let fS : (matrixPositiveTail k A s).homology n ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.connesHomology k A n :=
    HomologicalComplex.homologyMap (matrixCyclicWeibelChainMap k A s) n
  have he : ht ≫ eS.hom = eR.hom ≫ h0 := matrixPositiveTailHomologyIso_naturality k A h n
  have heInv : h0 ≫ eS.inv = eR.inv ≫ ht := by
    apply (cancel_mono eS.hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
      he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hm : ht ≫ fS = fR := by
    have hmap := congrArg (fun f => HomologicalComplex.homologyMap f n)
      (matrixCyclicWeibelChainMap_zeroCorner k A h)
    simp only [HomologicalComplex.homologyMap_comp] at hmap
    exact hmap
  have hn : h0 ≫ (eS.inv ≫ fS) = eR.inv ≫ fR := by
    calc
      _ = (h0 ≫ eS.inv) ≫ fS := (Category.assoc _ _ _).symm
      _ = (eR.inv ≫ ht) ≫ fS := congrArg (fun f => f ≫ fS) heInv
      _ = eR.inv ≫ (ht ≫ fS) := Category.assoc _ _ _
      _ = _ := congrArg (fun f => eR.inv ≫ f) hm
  let c := (ModuleCat.Algebra.Hochschild.NonUnital.cyclicToConnesHomologyIso k A n).inv
  change h0 ≫ ((eS.inv ≫ fS) ≫ c) = (eR.inv ≫ fR) ≫ c
  exact (Category.assoc h0 (eS.inv ≫ fS) c).symm.trans (congrArg (fun f => f ≫ c) hn)

section HomologyNaturality

variable {B : Type v} [Ring B] [Algebra k B]

/-- The finite matrix homology-to-Connes map is natural under the algebra map. -/
theorem matrixCyclicConnesHomologyMap_naturality (f : A →ₐ[k] B) (r n : ℕ) :
    HomologicalComplex.homologyMap (matrixCoefficientMap k A f r) (n + 1) ≫
        matrixCyclicConnesHomologyMap k B r n =
      matrixCyclicConnesHomologyMap k A r n ≫
        ModuleCat.Algebra.Hochschild.NonUnital.connesHomologyMap f.toNonUnitalAlgHom n := by
  let g := matrixCoefficientMap k A f r
  let eA := matrixPositiveTailHomologyIso k A r n
  let eB := matrixPositiveTailHomologyIso k B r n
  let h0 : matrixHomology k A r (n + 1) ⟶ matrixHomology k B r (n + 1) :=
    HomologicalComplex.homologyMap g (n + 1)
  let ht : (matrixPositiveTail k A r).homology n ⟶ (matrixPositiveTail k B r).homology n :=
    HomologicalComplex.homologyMap (ChainComplex.positiveTailMap g) n
  let fA : (matrixPositiveTail k A r).homology n ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.connesHomology k A n :=
    HomologicalComplex.homologyMap (matrixCyclicWeibelChainMap k A r) n
  let fB : (matrixPositiveTail k B r).homology n ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.connesHomology k B n :=
    HomologicalComplex.homologyMap (matrixCyclicWeibelChainMap k B r) n
  let c : ModuleCat.Algebra.Hochschild.NonUnital.connesHomology k A n ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.connesHomology k B n :=
    ModuleCat.Algebra.Hochschild.NonUnital.connesHomologyMap f.toNonUnitalAlgHom n
  have he : ht ≫ eB.hom = eA.hom ≫ h0 :=
    ChainComplex.positiveTailHomologyIso_naturality g
      (matrixComplex_d_one_zero k A r) (matrixComplex_d_one_zero k B r) n
  have heInv : h0 ≫ eB.inv = eA.inv ≫ ht := by
    apply (cancel_mono eB.hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
      he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hm : ht ≫ fB = fA ≫ c := by
    have hmap := congrArg (fun h => HomologicalComplex.homologyMap h n)
      (matrixCyclicWeibelChainMap_naturality k A f r)
    simp only [HomologicalComplex.homologyMap_comp] at hmap
    exact hmap
  change h0 ≫ (eB.inv ≫ fB) = (eA.inv ≫ fA) ≫ c
  calc
    _ = (h0 ≫ eB.inv) ≫ fB := (Category.assoc _ _ _).symm
    _ = (eA.inv ≫ ht) ≫ fB := congrArg (fun f => f ≫ fB) heInv
    _ = eA.inv ≫ (ht ≫ fB) := Category.assoc _ _ _
    _ = eA.inv ≫ (fA ≫ c) := congrArg (fun f => eA.inv ≫ f) hm
    _ = _ := (Category.assoc _ _ _).symm

/-- The HC lift is natural in the coefficient algebra map. -/
theorem matrixCyclicHomologyMap_naturality (f : A →ₐ[k] B) (r n : ℕ) :
    HomologicalComplex.homologyMap (matrixCoefficientMap k A f r) (n + 1) ≫
        matrixCyclicHomologyMap k B r n =
      matrixCyclicHomologyMap k A r n ≫
        ModuleCat.Algebra.Hochschild.NonUnital.cyclicHomologyMap f.toNonUnitalAlgHom n := by
  rw [matrixCyclicHomologyMap, matrixCyclicHomologyMap, ← Category.assoc,
    matrixCyclicConnesHomologyMap_naturality, Category.assoc,
    ModuleCat.Algebra.Hochschild.NonUnital.cyclicToConnesHomologyIso_inv_naturality,
    ← Category.assoc]

end HomologyNaturality

end ChevalleyEilenberg

end
