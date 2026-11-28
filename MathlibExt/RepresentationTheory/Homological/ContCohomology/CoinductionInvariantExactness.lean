/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import
  MathlibExt.RepresentationTheory.Homological.ContCohomology.CoinductionInvariantEvaluation

/-!
# Exact coefficient sequences after invariant coinduction

Let R be a ring with a topology and G a topological group.
The functor taking G-invariants of compact-open coinduction, then
forgetting topology, takes values in R-modules.

For a discrete coefficient with jointly continuous G-action, identity
evaluation identifies this module with its underlying R-module.
Thus a sequence of three such coefficients which is short exact after
forgetting to algebraic representations remains short exact after
invariant coinduction, as a sequence in ModuleCat R.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe r g w
namespace ContinuousCohomology
variable {R : Type r} [Ring R] [TopologicalSpace R]
variable {G : Type g} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Let R be a ring equipped with a topology and G a topological
group. A coefficient X is a topological R-module with a G-representation
by continuous R-linear maps. Scalar, group and carrier universes are independent.
The functor X ↦ C(G,X)^G, followed by forgetting the subspace
topology, takes values in R-modules. It uses the diagonal coinduced
action and identity-evaluation invariant submodule. -/
abbrev coindInvariantModuleFunctor :
    TopRep.{max g w, r, g} R G ⥤ ModuleCat.{max g w} R :=
  TopRep.coind₁Functor R G ⋙ TopRep.invariantsFunctor R G ⋙
    forget₂ (TopModuleCat.{max g w} R) (ModuleCat.{max g w} R)

/-- Let R be a ring equipped with a topology and G a topological
group. A coefficient X is a topological R-module with a G-representation
by continuous R-linear maps. Scalar, group and carrier universes are independent.
For discrete X with jointly continuous G-action, evaluation at 1
gives the R-module isomorphism between invariant coinduction and
the underlying R-module of X. -/
def coindInvariantModuleIso (X : TopRep.{max g w, r, g} R G) [DiscreteTopology X]
    (hX : ((TopRep.toActionTopModFunc (k := R) (G := G)).obj X).IsContinuous) :
    coindInvariantModuleFunctor.obj X ≅
      (forget₂ (Rep.{max g w} R G) (ModuleCat.{max g w} R)).obj
        ((TopRep.forgetToRep (k := R) (G := G)).obj X) :=
  { hom := ModuleCat.ofHom (coindInvariantEquiv X hX).toLinearMap
    inv := ModuleCat.ofHom (coindInvariantEquiv X hX).symm.toLinearMap
    hom_inv_id := by ext c; exact (coindInvariantEquiv X hX).symm_apply_apply c
    inv_hom_id := by ext x; exact (coindInvariantEquiv X hX).apply_symm_apply x }

/-- Let R be a ring equipped with a topology and G a topological
group. A coefficient X is a topological R-module with a G-representation
by continuous R-linear maps. Scalar, group and carrier universes are independent.
Let X₁ → X₂ → X₃ be a short complex of three discrete coefficients
whose G-actions are jointly continuous. If the sequence is short exact
after forgetting topology to algebraic representations, its invariant
coinduction sequence is short exact in ModuleCat R. -/
theorem coindInvariant_shortExact
    (S : ShortComplex (TopRep.{max g w, r, g} R G))
    [DiscreteTopology S.X₁] [DiscreteTopology S.X₂] [DiscreteTopology S.X₃]
    (h₁ : ((TopRep.toActionTopModFunc (k := R) (G := G)).obj S.X₁).IsContinuous)
    (h₂ : ((TopRep.toActionTopModFunc (k := R) (G := G)).obj S.X₂).IsContinuous)
    (h₃ : ((TopRep.toActionTopModFunc (k := R) (G := G)).obj S.X₃).IsContinuous)
    (hS : (S.map (TopRep.forgetToRep (k := R) (G := G))).ShortExact) :
    (S.map (coindInvariantModuleFunctor (R := R) (G := G))).ShortExact := by
  let U := (S.map (TopRep.forgetToRep (k := R) (G := G))).map
    (forget₂ (Rep.{max g w} R G) (ModuleCat.{max g w} R))
  let T := S.map (coindInvariantModuleFunctor (R := R) (G := G))
  let e : T ≅ U := ShortComplex.isoMk
    (coindInvariantModuleIso S.X₁ h₁) (coindInvariantModuleIso S.X₂ h₂)
    (coindInvariantModuleIso S.X₃ h₃)
    (by ext c; rfl) (by ext c; rfl)
  let : Mono (S.map (TopRep.forgetToRep (k := R) (G := G))).f := hS.mono_f
  let : Epi (S.map (TopRep.forgetToRep (k := R) (G := G))).g := hS.epi_g
  have hU : U.ShortExact := hS.map
    (forget₂ (Rep.{max g w} R G) (ModuleCat.{max g w} R))
  exact ShortComplex.shortExact_of_iso e.symm hU

end ContinuousCohomology
