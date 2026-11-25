/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import MathlibExt.RepresentationTheory.Continuous.ContinuousActionBridge
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory

/-!
# Exactness of actual continuous coinduction on discrete coefficients

A set-theoretic section into a discrete coefficient is continuous on its
discrete source. Composing this section with an actual continuous function
gives the required continuous lift. The same construction lifts kernel
functions. The resulting sequence is genuinely short exact after forgetting
coefficient topology; no abelian structure on topological modules is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe r g w

namespace ContinuousCohomology

variable {R : Type r} [Ring R] [TopologicalSpace R]
variable {G : Type g} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Every surjective coefficient arrow lifts actual continuous functions through its discrete
target. -/
theorem coindOneMap_surjective {X Y : TopRep.{max g w, r, g} R G}
    [DiscreteTopology Y] (f : X ⟶ Y) (hf : Function.Surjective f.hom) :
    Function.Surjective ((TopRep.coind₁Functor R G).map f).hom := by
  classical
  let s : Y → X := fun y => Classical.choose (hf y)
  intro c
  let b : C(G, X) := ⟨fun t => s (c t),
    (continuous_of_discreteTopology (f := s)).comp c.continuous⟩
  refine ⟨b, ?_⟩
  apply ContinuousMap.ext
  intro t
  exact Classical.choose_spec (hf (c t))

/-- The actual continuous-function map retains injectivity of its original coefficient arrow. -/
theorem coindOneMap_injective {X Y : TopRep.{max g w, r, g} R G}
    (f : X ⟶ Y) (hf : Function.Injective f.hom) :
    Function.Injective ((TopRep.coind₁Functor R G).map f).hom := by
  intro c d h
  apply ContinuousMap.ext
  intro t
  apply hf
  exact congrArg (fun q : C(G, Y) => q t) h

/-- Every actual coinduced kernel function lifts continuously through an exact coefficient pair. -/
theorem coindOneMap_lift_kernel {X Y Z : TopRep.{max g w, r, g} R G}
    [DiscreteTopology Y] (f : X ⟶ Y) (q : Y ⟶ Z)
    (hex : ∀ y : Y, q.hom y = 0 → ∃ x : X, f.hom x = y)
    (c : Y.coind₁) (hc : ((TopRep.coind₁Functor R G).map q).hom c = 0) :
    ∃ b : X.coind₁, ((TopRep.coind₁Functor R G).map f).hom b = c := by
  classical
  let s : Y → X := fun y => if h : q.hom y = 0 then Classical.choose (hex y h) else 0
  have hs (y : Y) (hy : q.hom y = 0) : f.hom (s y) = y := by
    simp only [s, dite_eq_left hy]
    exact Classical.choose_spec (hex y hy)
  let b : C(G, X) := ⟨fun t => s (c t),
    (continuous_of_discreteTopology (f := s)).comp c.continuous⟩
  refine ⟨b, ?_⟩
  apply ContinuousMap.ext
  intro t
  apply hs
  exact congrArg (fun d : C(G, Z) => d t) hc

/-- Actual coinduction preserves real short-exact discrete coefficient sequences. -/
theorem coindOne_forget_shortExact
    (S : ShortComplex (TopRep.{max g w, r, g} R G))
    [DiscreteTopology S.X₂] [DiscreteTopology S.X₃]
    (hS : (S.map (TopRep.forgetToRep (k := R) (G := G))).ShortExact) :
    ((S.map (TopRep.coind₁Functor R G)).map
      (TopRep.forgetToRep (k := R) (G := G))).ShortExact := by
  let T := S.map (TopRep.forgetToRep (k := R) (G := G))
  let U := (S.map (TopRep.coind₁Functor R G)).map
    (TopRep.forgetToRep (k := R) (G := G))
  have hf : Function.Injective S.f.hom := (Rep.mono_iff_injective T.f).mp hS.mono_f
  have hq : Function.Surjective S.g.hom := (Rep.epi_iff_surjective T.g).mp hS.epi_g
  have hex : ∀ y : S.X₂, S.g.hom y = 0 → ∃ x : S.X₁, S.f.hom x = y :=
    (T.map (forget₂ (Rep.{max g w} R G) (ModuleCat.{max g w} R))).moduleCat_exact_iff.mp
      (hS.exact.map (forget₂ (Rep.{max g w} R G) (ModuleCat.{max g w} R)))
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · apply (U.exact_map_iff_of_faithful
      (forget₂ (Rep.{max g w} R G) (ModuleCat.{max g w} R))).mp
    apply (U.map (forget₂ (Rep.{max g w} R G) (ModuleCat.{max g w} R))).moduleCat_exact_iff.mpr
    intro c hc
    exact coindOneMap_lift_kernel S.f S.g hex c hc
  · apply (Rep.mono_iff_injective U.f).mpr
    exact coindOneMap_injective S.f hf
  · apply (Rep.epi_iff_surjective U.g).mpr
    exact coindOneMap_surjective S.g hq

end ContinuousCohomology
