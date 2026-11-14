/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import MathlibExt.AlgebraicGeometry.NearbyCycleProperMaps

@[expose] public noncomputable section

/-!
# Global rational nearby and vanishing cycles

Authors: Pierre Deligne; Alexandru Dimca; David B. Massey;
Mark de Cataldo, Luca Migliorini.

Sources:
* Massey, *Notes on Perverse Sheaves and Vanishing Cycles*, the section
  on nearby and vanishing cycles: traditional definitions, the Milnor
  triangle, perverse preservation and proper direct image (pp. 25--35).
  https://arxiv.org/abs/math/9908107v14
* Dimca, *Sheaves in Topology*, §4.2.
* de Cataldo--Migliorini, *The decomposition theorem, perverse sheaves
  and the topology of algebraic maps*, §5.5, Theorem 5.5.3.
  https://arxiv.org/abs/0712.0349

The actual functors use the exponential pullback cover, the adjunction
specialization map and its functorial cochain cone. We use unshifted
Rψ and Rφ = Cone(i* → Rψ), so both Rψ[-1] and Rφ[-1] are perverse exact.
The monodromy is induced by the positive integral deck generator.
No quasi-unipotence claim is made for arbitrary rational local systems.
Generic K-injective resolutions, derived Kan functors and the Axiom
strict-local fiber/map theory are already covered toolbox inputs.
-/

namespace WantedExt.AlgebraicGeometry.NearbyCycles

open CategoryTheory CategoryTheory.Functor
open _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.ComplexAnalytification
open _root_.MathlibExt.AlgebraicGeometry.PerverseSheaves
open _root_.MathlibExt.AlgebraicGeometry.NearbyCycleGeometry
open _root_.MathlibExt.AlgebraicGeometry.NearbyCycleComplexes
open _root_.MathlibExt.AlgebraicGeometry.NearbyCycleMonodromy
open _root_.MathlibExt.AlgebraicGeometry.NearbyCycleProperMaps

attribute [local instance] HasDerivedCategory.standard

/-- Choose a resolver with the extra deck compatibility needed by the
functorial cone enhancement. Generic K-injective resolution existence is
already covered; an arbitrary resolver is not required to carry this
strict cochain comparison. -/
public def_wanted deckCompatibleResolver
    (X : ComplexScheme) [IsComplexVariety X] (s : Γ(X.left, ⊤)) :
    DeckCompatibleCycleResolution X s

/-- Algebraic constructibility and boundedness of the actual global
nearby and vanishing functors. -/
public theorem_wanted boundedConstructibleCycles
    (X : ComplexScheme) [IsComplexVariety X] (s : Γ(X.left, ⊤)) (A : ZeroFiber X s)
    (R : FunctorialResolution (exponentialCover X s))
    (K : QDerived (space X)) (hK : boundedConstructible X K) :
    boundedConstructible A.Z ((nearbyFunctor A R).obj K) ∧
      boundedConstructible A.Z ((vanishingFunctor A R).obj K)

/-- Both shifted actual cycle functors preserve the two halves of the
characterized middle perverse t-structure in every degree. -/
public theorem_wanted perverseCyclesExact
    (X : ComplexScheme) [IsComplexVariety X] (s : Γ(X.left, ⊤)) (A : ZeroFiber X s)
    [PerverseSheafTheory X] [PerverseSheafTheory A.Z]
    (R : FunctorialResolution (exponentialCover X s))
    (K : (boundedConstructible X).FullSubcategory) :
    ∃ hψ : boundedConstructible A.Z
        (((nearbyFunctor A R).obj K.obj)⟦(-1 : ℤ)⟧),
    ∃ hφ : boundedConstructible A.Z
        (((vanishingFunctor A R).obj K.obj)⟦(-1 : ℤ)⟧),
    ∀ m : ℤ,
      ((perverseTStructure X).le m K →
        (perverseTStructure A.Z).le m ⟨_, hψ⟩) ∧
      ((perverseTStructure X).ge m K →
        (perverseTStructure A.Z).ge m ⟨_, hψ⟩) ∧
      ((perverseTStructure X).le m K →
        (perverseTStructure A.Z).le m ⟨_, hφ⟩) ∧
      ((perverseTStructure X).ge m K →
        (perverseTStructure A.Z).ge m ⟨_, hφ⟩)

/-- The proper direct-image comparison of the actual global cycle
triangles, with the zero/cover base-change maps and both deck monodromies
fixed by the completed core definitions. -/
public def_wanted properCycleFunctoriality
    (X Y : ComplexScheme) [IsComplexVariety X] [IsComplexVariety Y]
    (s : Γ(X.left, ⊤)) (t : Γ(Y.left, ⊤))
    (A : ZeroFiber X s) (B : ZeroFiber Y t)
    (G : FunctionMorphism A B) [IsProper G.g.left] [DiagramDerivedData G]
    (R₁ : FunctorialResolution (exponentialCover X s))
    (R₂ : FunctorialResolution (exponentialCover Y t))
    (E₁ : DeckResolutionComparison R₁ (deckIso X s 1))
    (E₂ : DeckResolutionComparison R₂ (deckIso Y t 1)) :
    CanonicalProperCycleComparison G R₁ R₂ E₁ E₂
      (specializationDeckCompatibility A R₁ E₁)
      (specializationDeckCompatibility B R₂ E₂)

end WantedExt.AlgebraicGeometry.NearbyCycles

