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
# The stable matrix Lie-to-cyclic homology map

Let k be a commutative ℚ-algebra and A an associative unital k-algebra.
The finite matrix trace maps stabilize to a morphism
Θ_n : H_(n+1)(C_*(Mat_∞(A))) → HC_n(A).
The CE complex is identified with the directed colimit of its finite
matrix complexes, and Θ_n restricts to the finite matrix homology map
at every size m ≥ 0.

The construction passes through the positive-tail CE trace into
Cλ(A), the Connes quotient by the signed cyclic relation 1−t.
The equality d₁ = 0 identifies positive-tail homology in degree n
with CE homology in degree n+1, and the inverse rational isomorphism
HC_n(A) ≅ H_n(Cλ(A)) gives the cyclic-homology target.
The chain category is ModuleCat^max(u,v)(k), with independent ring
and algebra worlds.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v

namespace ChevalleyEilenberg

variable (k : Type u) [CommRing k] [Algebra ℚ k] (A : Type v) [Ring A] [Algebra k A]

/-- For a commutative ℚ-algebra k, an associative unital
k-algebra A and n ≥ 0, the stabilized matrix trace defines
H_(n+1)(C_*(Mat_∞(A))) → HC_n(A).
It uses the finite-to-stable CE isomorphism, the positive-tail
Connes trace and the inverse rational Connes homology comparison. -/
def canonicalStableMatrixCyclicHomologyMap (n : ℕ) :
    (canonicalStableMatrixCEComplex k A).homology (n + 1) ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.cyclicHomology k A n :=
  HomologicalComplex.homologyMap (canonicalStableMatrixCEIso k A).inv (n + 1) ≫
    stableMatrixCyclicHomologyMap k A n

/-- For a commutative ℚ-algebra k, an associative unital
k-algebra A and m,n ≥ 0, the stable trace map Θ_n satisfies
Θ_n ∘ H_(n+1)(C_*(i_m)) = Θ_(m,n).
Here i_m : Mat_m(A) → Mat_∞(A), and Θ_(m,n) is the finite matrix
Lie-to-cyclic homology map in degrees n+1 and n. -/
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
