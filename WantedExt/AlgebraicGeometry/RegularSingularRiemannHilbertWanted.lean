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

/-- Actual holomorphic solutions form a complex local system of rank `r` (every stalk has
dimension `r`) where all actual matrix coefficient denominators are nonzero. -/
public theorem_wanted solutions_local_system (S : Finset ℂ) (r : ℕ)
    (A : Matrix (Fin r) (Fin r) RationalFunctions) (hA : PolesWithin S A) :
    IsFiniteRankLocalSystem ℂ (puncturedLine S) (solutionSheaf S A hA) ∧
      ∀ z : puncturedLine S, Module.finrank ℂ ((solutionSheaf S A hA).presheaf.stalk z) = r

/-- The analytic connection de Rham data of a rational matrix connection on the punctured line:
the sheaves of holomorphic vector functions and of holomorphic vector one-forms (trivialized by
`dz`), with their restrictions, and the connection operator `f ↦ f' - A f`. Any two such data are
canonically isomorphic, since the structure pins every section and the differential. -/
public def_wanted analytic_connection_deRham_data (S : Finset ℂ) (r : ℕ)
    (A : Matrix (Fin r) (Fin r) RationalFunctions) (hA : PolesWithin S A) :
  AnalyticConnectionDeRhamData S r A hA

/-- Let $S \subset \mathbb{C}$ be finite and $A$ an $r \times r$ matrix of rational functions with
poles in $S$ (`hA`). Then there is a quasi-isomorphism $\eta$ from the sheaf of holomorphic
solutions of $f' = Af$ on $\mathbb{C} \setminus S$ (`solutionSheaf`), placed in degree $0$, to the
analytic de Rham complex $\mathcal{O}^r \to \Omega^r$, $f \mapsto f' - Af$, of the de Rham data
`analytic_connection_deRham_data` (unshifted, in degrees $0$ and $1$; its shift by $[1]$ is the
perverse normalization on a curve), such that in degree $0$, $\eta$ sends every solution on an
open $U$ to the same function, viewed as a holomorphic vector function on $U$. -/
public def_wanted analytic_deRham_comparison (S : Finset ℂ) (r : ℕ)
    (A : Matrix (Fin r) (Fin r) RationalFunctions) (hA : PolesWithin S A) :
    {η : (HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj
        (solutionSheaf S A hA) ⟶
          analyticDeRhamComplex (❰analytic_connection_deRham_data❱ S r A hA) //
      QuasiIso η ∧
        ∀ (U : TopologicalSpace.Opens (puncturedLine S)) (v : solutionSections S A hA U)
          (z : ℂ), z ∈ ambientOpen S U → ∀ i : Fin r,
          ((❰analytic_connection_deRham_data❱ S r A hA).functionSections U
            (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
              (solutionSheaf S A hA)).inv ≫ η.f 0).hom.app (.op U)
                ((solutionUnit S A hA).app (.op U) v))).1 z i = v.1 z i}

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
    (φ : solutionSheaf S A hA ⟶ solutionSheaf S B hB) :
    ∃! G : Matrix (Fin s) (Fin r) RationalFunctions,
      ∃ hG : PolesWithin S G, HorizontalMatrix δ A B G ∧ InducedByMatrix S A B hA hB φ G hG

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
    ∃ A : Matrix (Fin r) (Fin r) RationalFunctions, ∃ hA : PolesWithin S A,
      (∀ a, RegularSingularAt δ A a) ∧
        RegularSingularAtInfinity δ A ∧ Nonempty (solutionSheaf S A hA ≅ L)

end WantedExt.AlgebraicGeometry.RegularSingularRiemannHilbertWanted
