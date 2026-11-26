/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import MathlibExt.CategoryTheory.Action.DiscreteAbelianShortExact
public import MathlibExt.RepresentationTheory.Homological.ContCohomology.DiscreteCoinductionExactness

/-!
# Continuous coinduction preserves short exact coefficient rows

Let G be a compact, totally disconnected topological group in universe g, and let the discrete
continuous abelian coefficient groups lie in W=max(g,w). Diagonal coinduction C sends A to the
continuous function group C(G,A), with action (h•F)(g)=h•F(h⁻¹g), and sends coefficient
morphisms to pointwise postcomposition.

This functor is additive. If a short complex is short exact after forgetting the action, its
coinduced row remains short exact on the underlying abelian groups. The same row is therefore
short exact in the category of discrete continuous actions.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe g w
namespace CategoryTheory.DiscreteAbelianAction
variable {G : Type g} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- Let G be a compact, totally disconnected topological group in universe g and let discrete
continuous abelian coefficients lie in W=max(g,w). For diagonal coinduction C and parallel
equivariant additive maps f,h:A→B, C(f+h)=C(f)+C(h). On a continuous coefficient function F:G→A,
each side has value f(F(g))+h(F(g)) at g. -/
instance coind_additive : (coind.{g, w} (G := G)).Additive where
  map_add := by
    intro A B f h
    apply (forget G).map_injective
    ext c
    rfl

/-- Let G be a compact, totally disconnected topological group in universe g and let discrete
continuous abelian coefficients lie in W=max(g,w). Let U forget the action and C be diagonal
continuous coinduction. If S=(A --a→ B --b→ D) is a short complex with U(S) short exact, then
U(CS) is short exact. Its arrows are pointwise postcomposition with a and b; the first is
injective, its image is the second map's kernel, and the second is surjective. -/
theorem coind_forget_shortExact
    (S : ShortComplex (DiscreteAbelianAction.{g, max g w} G))
    (hS : (S.map (forget.{g, max g w} G)).ShortExact) :
    ((S.map coind.{g, w}).map (forget.{g, max g w} G)).ShortExact := by
  let T := S.map (forget.{g, max g w} G)
  let U := (S.map coind.{g, w}).map (forget.{g, max g w} G)
  have hf : Function.Injective (homToAdd S.f) := (AddCommGrpCat.mono_iff_injective T.f).mp hS.mono_f
  have hq : Function.Surjective (homToAdd S.g) := (AddCommGrpCat.epi_iff_surjective T.g).mp hS.epi_g
  have hex : ∀ y : underlying S.X₂, homToAdd S.g y = 0 → ∃ x : underlying S.X₁,
      homToAdd S.f x = y :=
    T.ab_exact_iff.mp hS.exact
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · apply U.ab_exact_iff.mpr
    intro c hc
    exact ContinuousCohomology.coindOneMap_lift_kernel.{0, g, w}
      (toTopRep.map S.f) (toTopRep.map S.g) hex c hc
  · apply (AddCommGrpCat.mono_iff_injective U.f).mpr
    exact ContinuousCohomology.coindOneMap_injective.{0, g, w} (toTopRep.map S.f) hf
  · apply (AddCommGrpCat.epi_iff_surjective U.g).mpr
    exact ContinuousCohomology.coindOneMap_surjective.{0, g, w} (toTopRep.map S.g) hq

/-- Let G be a compact, totally disconnected topological group in universe g and let discrete
continuous abelian coefficients lie in W=max(g,w). For a short complex S of discrete continuous
actions whose underlying abelian-group row U(S) is short exact, the coinduced short complex CS
is short exact in the action category. Its pointwise coefficient arrows satisfy the
action-category kernel and cokernel universal properties, and are respectively mono and epi. -/
theorem coind_shortExact_of_forget
    (S : ShortComplex (DiscreteAbelianAction.{g, max g w} G))
    (hS : (S.map (forget.{g, max g w} G)).ShortExact) : (S.map coind.{g, w}).ShortExact :=
  shortExact_of_forget_shortExact.{g, max g w} (G := G) (S.map coind.{g, w})
    (coind_forget_shortExact.{g, w} (G := G) S hS)

end CategoryTheory.DiscreteAbelianAction
