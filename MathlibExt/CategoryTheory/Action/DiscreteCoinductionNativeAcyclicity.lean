/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import MathlibExt.CategoryTheory.Action.DiscreteCoinductionCoresolution
public import MathlibExt.RepresentationTheory.Homological.ContCohomology.CoinducedAcyclicity
public import MathlibExt.RepresentationTheory.Homological.ContCohomology.CoefficientFunctor

/-!
# Positive continuous cohomology vanishes on coinduction terms

Let G be a compact, locally compact, totally disconnected topological group in universe g, with
discrete continuous abelian coefficients in W=max(g,w). The comparison from diagonal action
coinduction to continuous representation coinduction identifies their homogeneous cochain
complexes.

For every coefficient action A, every positive continuous cohomology object of J(TA) is zero in
topological ℤ-modules. The same vanishing holds for all positive monad powers T^{p+1}A and for
every term of the cosimplicial monad coresolution, whose degree-p coefficient is T^{p+1}A. Both
p and the cohomological degree range over all nonnegative integers before taking their
successors.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe g w
namespace CategoryTheory.DiscreteAbelianAction
variable (G : Type g) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] [LocallyCompactSpace G]

/-- Let G be a compact, locally compact, totally disconnected topological group in universe g, with
discrete continuous abelian coefficients in W=max(g,w). Write J for the associated continuous
ℤ-representation and T for diagonal coinduction. For A and n≥0, the continuous cohomology object
H_cont^{n+1}(G,J(TA)) is a zero object of topological ℤ-modules in universe W. The coinduction
comparison J(TA)≅C(JA) transports the positive-degree vanishing for the continuous homogeneous
resolution. -/
theorem coind_native_isZero_succ (A : DiscreteAbelianAction.{g, max g w} G) (n : ℕ) :
    IsZero (continuousCohomology.{0, g, w} (n + 1) (toTopRep.obj (coind.{g, w}.obj A))) := by
  let F := ContinuousCohomology.homogeneousCochainsFunctor.{0, g, w} (k := ℤ) (G := G) ⋙
    HomologicalComplex.homologyFunctor (TopModuleCat.{max g w} ℤ) (ComplexShape.up ℕ) (n + 1)
  let e := F.mapIso (coindToTopRepIso.{g, w} G A)
  have hz := ContinuousCohomology.isZero_coind₁_succ.{0, g, w} (toTopRep.obj A) n
  exact IsZero.of_iso hz e

/-- Let G be a compact, locally compact, totally disconnected topological group in universe g, with
discrete continuous abelian coefficients in W=max(g,w). Write J for the associated continuous
ℤ-representation and T for diagonal coinduction. For a coefficient action A and all p,n≥0,
H_cont^{n+1}(G,J(T^{p+1}A)) is a zero topological ℤ-module. Reassociation realizes T^{p+1}A as
one coinduction of T^p A, so the statement includes every positive power and every positive
cohomological degree. -/
theorem coindPower_native_isZero_succ (A : DiscreteAbelianAction.{g, max g w} G)
    (p n : ℕ) :
    IsZero (continuousCohomology.{0, g, w} (n + 1)
      (toTopRep.obj ((Monad.monadPow (coindMonad.{g, w} G) (p + 1)).obj A))) := by
  let B := (Monad.monadPow (coindMonad.{g, w} G) p).obj A
  let F := ContinuousCohomology.homogeneousCochainsFunctor.{0, g, w} (k := ℤ) (G := G) ⋙
    HomologicalComplex.homologyFunctor (TopModuleCat.{max g w} ℤ) (ComplexShape.up ℕ) (n + 1)
  let e := F.mapIso (toTopRep.mapIso
    (eqToIso (Monad.monadPow_succ_obj_eq (coindMonad.{g, w} G) p A)))
  exact IsZero.of_iso (coind_native_isZero_succ.{g, w} G B n) e

/-- Let G be a compact, locally compact, totally disconnected topological group in universe g, with
discrete continuous abelian coefficients in W=max(g,w). Write J for the associated continuous
ℤ-representation and T for diagonal coinduction. Let K_A be the cosimplicial monad coresolution.
For all p,n≥0, H_cont^{n+1}(G,J(K_A^p)) is a zero topological ℤ-module. The degree-p coefficient
comparison K_A^p≅T^{p+1}A identifies it with a positive coinduction power. -/
theorem coindCoresolution_native_isZero_succ (A : DiscreteAbelianAction.{g, max g w} G)
    (p n : ℕ) :
    IsZero (continuousCohomology.{0, g, w} (n + 1)
      (toTopRep.obj ((Monad.coresolution (coindMonad.{g, w} G) A).obj
          (SimplexCategory.mk p)))) := by
  let F := ContinuousCohomology.homogeneousCochainsFunctor.{0, g, w} (k := ℤ) (G := G) ⋙
    HomologicalComplex.homologyFunctor (TopModuleCat.{max g w} ℤ) (ComplexShape.up ℕ) (n + 1)
  let e := F.mapIso (toTopRep.mapIso (Monad.coresolutionObjIso (coindMonad.{g, w} G) A p))
  exact IsZero.of_iso (coindPower_native_isZero_succ.{g, w} G A p n) e

end CategoryTheory.DiscreteAbelianAction
