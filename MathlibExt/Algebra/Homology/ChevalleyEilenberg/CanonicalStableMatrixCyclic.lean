/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CanonicalStableMatrixComparison
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.MatrixCyclicStabilizationNaturality

/-!
# Stable matrix Lie homology maps to cyclic homology

For a unital algebra A over a commutative rational algebra k, the stabilized matrix trace
induces a map from Chevalley–Eilenberg homology of the stable matrix Lie algebra in degree n +
1 to cyclic homology of A in degree n.

Its restriction along every finite matrix inclusion is the corresponding finite matrix
homology map.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v

namespace ChevalleyEilenberg

variable (k : Type u) [CommRing k] [Algebra ℚ k] (A : Type v) [Ring A] [Algebra k A]

/-- The stabilized trace map from stable matrix Lie homology in degree n + 1 to cyclic homology in
degree n. -/
def canonicalStableMatrixCyclicHomologyMap (n : ℕ) :
    (canonicalStableMatrixCEComplex k A).homology (n + 1) ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.cyclicHomology k A n :=
  HomologicalComplex.homologyMap (canonicalStableMatrixCEIso k A).inv (n + 1) ≫
    stableMatrixCyclicHomologyMap k A n

/-- Every finite lambda-to-HC map is retained by the canonical stable model. -/
theorem canonicalStableMatrixCyclicHomologyMap_finite (m n : ℕ) :
    HomologicalComplex.homologyMap (canonicalStableMatrixCEInclusion k A m) (n + 1) ≫
        canonicalStableMatrixCyclicHomologyMap k A n = matrixCyclicHomologyMap k A m n := by
  let e := canonicalStableMatrixCEIso k A
  let a : matrixComplex k A m ⟶ stableMatrixCEComplex k A :=
    colimit.ι (matrixComplexFunctor k A) m
  have ha : a ≫ e.hom = canonicalStableMatrixCEInclusion k A m :=
    colimitToCanonicalStableMatrixCE_ι k A m
  have h : canonicalStableMatrixCEInclusion k A m ≫ e.inv = a := by
    calc
      _ = (a ≫ e.hom) ≫ e.inv :=
        congrArg (fun f : matrixComplex k A m ⟶ canonicalStableMatrixCEComplex k A => f ≫ e.inv) ha.symm
      _ = a ≫ (e.hom ≫ e.inv) := Category.assoc a e.hom e.inv
      _ = a := (congrArg (fun f => a ≫ f) e.hom_inv_id).trans (Category.comp_id a)
  have hm := congrArg (fun f => HomologicalComplex.homologyMap f (n + 1)) h
  simp only [HomologicalComplex.homologyMap_comp] at hm
  let c := stableMatrixCyclicHomologyMap k A n
  have hH : HomologicalComplex.homologyMap (canonicalStableMatrixCEInclusion k A m) (n + 1) ≫
      (HomologicalComplex.homologyMap e.inv (n + 1) ≫ c) = matrixCyclicHomologyMap k A m n := by
    calc
      _ = (HomologicalComplex.homologyMap (canonicalStableMatrixCEInclusion k A m) (n + 1) ≫
          HomologicalComplex.homologyMap e.inv (n + 1)) ≫ c := (Category.assoc _ _ _).symm
      _ = HomologicalComplex.homologyMap a (n + 1) ≫ c := congrArg (fun f => f ≫ c) hm
      _ = _ := stableMatrixCyclicHomologyMap_ι k A m n
  exact hH

end ChevalleyEilenberg
