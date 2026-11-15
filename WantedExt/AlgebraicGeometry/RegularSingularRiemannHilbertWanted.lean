/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RegularSingularConnections

/-!
# Regular singular Riemann--Hilbert on the punctured projective line

This is the algebraic connection/local-system correspondence, including
regularity at infinity. Omitting that condition would admit irregular
connections and make algebraic fullness false.

Source: Deligne, *Équations différentielles à points singuliers réguliers*,
Lecture Notes in Mathematics 163 (1970), Chapter II §5.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RegularSingularRiemannHilbertWanted

open CategoryTheory
open MathlibExt.AlgebraicGeometry.RegularSingularConnections
open MathlibExt.AlgebraicGeometry.ConstructibleComplexes

/-- Actual holomorphic solutions form a finite-rank complex local system
where all actual matrix coefficient denominators are nonzero. -/
public theorem_wanted solutions_local_system (S : Finset ℂ) (r : ℕ)
    (A : Matrix (Fin r) (Fin r) RationalFunctions) (hA : PolesWithin S A) :
    IsFiniteRankLocalSystem ℂ (puncturedLine S) (solutionSheaf S A)

/-- The actual solution sheaf resolves the actual analytic connection
de Rham complex. Its degree-zero comparison sends every solution to the
same holomorphic vector function. The shift `[1]` gives the curve perverse
normalization used in the Riemann--Hilbert correspondence. -/
public def_wanted analytic_deRham_comparison (S : Finset ℂ) (r : ℕ)
    (A : Matrix (Fin r) (Fin r) RationalFunctions) (hA : PolesWithin S A)
    (D : AnalyticConnectionDeRhamData S r A) :
    {η : (HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj
        (solutionSheaf S A) ⟶ analyticDeRhamComplex D //
      QuasiIso η ∧
        ∀ (U : TopologicalSpace.Opens (puncturedLine S)) (v : solutionSections S A U)
          (z : ℂ), z ∈ ambientOpen S U → ∀ i : Fin r,
          (D.functionSections U
            (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
              (solutionSheaf S A)).inv ≫ η.f 0).hom.app (.op U)
                ((solutionUnit S A).app (.op U) v))).1 z i = v.1 z i}

/-- Every map of solution local systems algebraizes uniquely to the actual
horizontal rational gauge matrix, with no new poles on the open line. -/
public theorem_wanted regular_singular_full_faithful
    (δ : RationalDerivative) (S : Finset ℂ) (r s : ℕ)
    (A : Matrix (Fin r) (Fin r) RationalFunctions)
    (B : Matrix (Fin s) (Fin s) RationalFunctions)
    (hA : PolesWithin S A) (hB : PolesWithin S B)
    (hAreg : ∀ a, RegularSingularAt δ A a)
    (hBreg : ∀ a, RegularSingularAt δ B a)
    (hAinf : RegularSingularAtInfinity δ A)
    (hBinf : RegularSingularAtInfinity δ B)
    (φ : solutionSheaf S A ⟶ solutionSheaf S B) :
    ∃! G : Matrix (Fin s) (Fin r) RationalFunctions,
      PolesWithin S G ∧ HorizontalMatrix δ A B G ∧ InducedByMatrix S A B φ G

/-- Every rank-r complex local system on the actual punctured line comes
from a rational matrix connection regular singular at all boundary points,
including infinity. The open coordinate ring is a localization of ℂ[t],
so its finite projective bundles are free and a matrix presentation exists. -/
public theorem_wanted regular_singular_essentially_surjective
    (δ : RationalDerivative) (S : Finset ℂ) (r : ℕ)
    (L : TopCat.Sheaf (ModuleCat.{0} ℂ) (puncturedLine S))
    (hL : IsFiniteRankLocalSystem ℂ (puncturedLine S) L)
    (hrank : ∀ z : puncturedLine S,
      Module.finrank ℂ (L.presheaf.stalk z) = r) :
    ∃ A : Matrix (Fin r) (Fin r) RationalFunctions,
      PolesWithin S A ∧ (∀ a, RegularSingularAt δ A a) ∧
        RegularSingularAtInfinity δ A ∧ Nonempty (solutionSheaf S A ≅ L)

end WantedExt.AlgebraicGeometry.RegularSingularRiemannHilbertWanted
