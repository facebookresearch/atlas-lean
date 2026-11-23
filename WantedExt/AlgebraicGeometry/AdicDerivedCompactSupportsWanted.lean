/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AdicDerivedCompactSupports

@[expose] public noncomputable section

/-!
# Constructions for derived compact supports over the continuous coefficient ring

For sheaves of modules over the continuous coefficient ring `E_X` on small pro-étale sites:

* the module categories have enough injectives (they are Grothendieck abelian; Mathlib proves this
  for small sites, and the small pro-étale site is essentially small);
* derived extension by zero along an open immersion is left adjoint to derived restriction, and
  derived inverse image is left adjoint to derived direct image, with the expected units;
* direct images compose along a refinement of compactifications, compatibly with the pasting of
  base changes; global sections of a direct image are global sections; derived global sections of a
  derived direct image are the derived functor of the composite (Stacks 0D6E);
* open base change: for a refinement of compactifications (a Cartesian square of open immersions
  over a proper map), the exchange map `j_{d!} K ⟶ r^* j_{c!} K` is an isomorphism.

References: Stacks Project, Tags 07A6, 0D6E and 09AH; Bhatt--Scholze, *The pro-étale topology for
schemes*, §6.1.
-/

namespace WantedExt.AlgebraicGeometry.AdicDerivedCompactSupportsWanted

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AdicRingedSiteOperations
open MathlibExt.AlgebraicGeometry.AdicDerivedCompactSupports

attribute [local instance] HasDerivedCategory.standard

/-- Enough injectives for every scheme. -/
public theorem_wanted moduleInjectives (E : Type) [CommRing E] [TopologicalSpace E]
    [IsTopologicalRing E] : ModuleInjectives E

/-- The derived adjunction for extension by zero along an open immersion. -/
public def_wanted openDerivedAdjunction (E : Type) [CommRing E] [TopologicalSpace E]
    [IsTopologicalRing E] {X Y : Scheme} (j : X ⟶ Y) [IsOpenImmersion j]
    [(pushforward E j).IsRightAdjoint] [(pullback E j).IsRightAdjoint] [ModuleInjectives E]
    [PreservesFiniteLimits (extensionByZero E j)] [PreservesFiniteLimits (pullback E j)] :
    OpenDerivedAdjunction E j

/-- The derived adjunction between inverse and direct image. -/
public def_wanted imageDerivedAdjunction (E : Type) [CommRing E] [TopologicalSpace E]
    [IsTopologicalRing E] {X Y : Scheme} (f : X ⟶ Y) [(pushforward E f).IsRightAdjoint]
    [PreservesFiniteLimits (pullback E f)] [ModuleInjectives E] :
    ImageDerivedAdjunction E f

/-- Composition of direct images along a refinement, compatible with the pasting of base
changes. -/
public def_wanted ringedRefinementPasting (E : Type) [CommRing E] [TopologicalSpace E]
    [IsTopologicalRing E] {X S : Scheme} {f : X ⟶ S} {c d : Compactification f}
    (r : Refinement c d) : RingedRefinementPasting E r

/-- Global sections of a direct image are global sections. -/
public def_wanted sectionsPushforwardNormalization (E : Type) [CommRing E] [TopologicalSpace E]
    [IsTopologicalRing E] {X Y : Scheme} (p : X ⟶ Y) [ModuleInjectives E] :
    SectionsPushforwardNormalization E p

/-- Derived global sections of a derived direct image. -/
public def_wanted sectionsDerivedNormalization (E : Type) [CommRing E] [TopologicalSpace E]
    [IsTopologicalRing E] {X Y : Scheme} (p : X ⟶ Y) [ModuleInjectives E]
    [SectionsPushforwardNormalization E p] : SectionsDerivedNormalization E p

/-- Open base change along a refinement of compactifications. -/
public theorem_wanted refinementExchange (E : Type) [CommRing E] [TopologicalSpace E]
    [IsTopologicalRing E] {X S : Scheme} {f : X ⟶ S} {c d : Compactification f}
    (r : Refinement c d) [(pushforward E c.openMap).IsRightAdjoint]
    [(pushforward E d.openMap).IsRightAdjoint] [(pushforward E r.map).IsRightAdjoint]
    [RingedRefinementPasting E r] [ModuleInjectives E]
    [PreservesFiniteLimits (pullback E c.openMap)] [PreservesFiniteLimits (pullback E d.openMap)]
    [PreservesFiniteLimits (pullback E r.map)] [(pullback E c.openMap).IsRightAdjoint]
    [(pullback E d.openMap).IsRightAdjoint] [PreservesFiniteLimits (extensionByZero E c.openMap)]
    [PreservesFiniteLimits (extensionByZero E d.openMap)] [OpenDerivedAdjunction E c.openMap]
    [OpenDerivedAdjunction E d.openMap] : RefinementExchange E r

end WantedExt.AlgebraicGeometry.AdicDerivedCompactSupportsWanted
