/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: @toskua, Codex
-/

module

public import MathlibExt.Algebra.Homology.HomologicalComplex.EndpointCofreeAdjunction
public import MathlibExt.CategoryTheory.Functor.EnoughInjectives

/-!
# Injective cofree complexes and covers

Let C have zero morphisms, a zero object and binary biproducts. Cofree maps
K → D(I) are determined by their first coefficients Kᵢ → Iᵢ. If those coefficients
are monomorphisms, the resulting complex map is a monomorphism.

When C also has finite limits, injective coefficient objects give an injective
cofree complex. If C has enough injectives, the degreewise injective presentations
and the cofree adjunction give enough injectives for complexes of any shape.
The source index and the object and morphism universes are independent.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Classical ZeroObject

universe u v w

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C]
  [HasZeroMorphisms C] [HasZeroObject C] [HasBinaryBiproducts C]
variable {ι : Type w} {c : ComplexShape ι}

/-- For C with finite limits, any complex shape c and a family of
injective objects Iᵢ, the complex D(I) is injective in the category
of c-shaped complexes. Its term at an endpoint has zero second summand. -/
theorem endpointCofree_injective (c : ComplexShape ι) [HasFiniteLimits C]
    (I : ι → C) [∀ i, Injective (I i)] :
    Injective (endpointCofree c I) := by
  let e := piEquivalenceFunctorDiscrete ι C
  have hD : Injective (e.functor.obj I) :=
    injective_discrete_of_obj (e.functor.obj I) (fun i => by
      change Injective (I i.as)
      infer_instance)
  have hI : Injective (I : GradedObject ι C) := (e.map_injective_iff I).1 hD
  exact (endpointCofreeAdjunction C c).map_injective I hI

/-- For a c-shaped complex K and a family of monomorphisms
aᵢ : Kᵢ → Iᵢ, the cofree morphism K → D(I) is a
monomorphism of complexes of the same shape. -/
theorem endpointCofreeHom_mono (K : HomologicalComplex C c) (I : ι → C)
    (a : ∀ i, K.X i ⟶ I i) [∀ i, Mono (a i)] :
    Mono (endpointCofreeHom K I a) := by
  apply HomologicalComplex.mono_of_mono_f
  intro i
  exact mono_of_mono_fac (endpointCofreeHom_fst K I a i)

/-- If C has enough injectives, a complex K of any
shape has a cofree morphism into D(I), where Iᵢ is the chosen injective
object containing Kᵢ and the first coefficient is the chosen
monomorphism Kᵢ → Iᵢ. -/
def endpointCofreeCover (K : HomologicalComplex C c) [EnoughInjectives C] :
    K ⟶ endpointCofree c (fun i => Injective.under (K.X i)) :=
  endpointCofreeHom K _ (fun i => Injective.ι (K.X i))

/-- For a complex K in C with enough injectives,
the cofree cover followed by the first projection in degree i is
the chosen inclusion of Kᵢ into its injective object. -/
@[reassoc (attr := simp)]
theorem endpointCofreeCover_fst (K : HomologicalComplex C c) [EnoughInjectives C] (i : ι) :
    (endpointCofreeCover K).f i ≫
        endpointCofreeProjection c (fun j => Injective.under (K.X j)) i =
      Injective.ι (K.X i) :=
  endpointCofreeHom_fst _ _ _ _

/-- If C has zero morphisms, a zero object, binary biproducts, finite limits and enough
injectives, then the category
of complexes in C of any shape c has enough injectives. Each complex
embeds in the cofree complex formed from its degreewise injective
objects, including at indices with no outgoing edge. -/
theorem enoughInjectives_of_endpointCofree (c : ComplexShape ι) [HasFiniteLimits C]
    [EnoughInjectives C] :
    EnoughInjectives (HomologicalComplex C c) := by
  letI : EnoughInjectives (Discrete ι ⥤ C) := enoughInjectives_discrete ι
  letI : EnoughInjectives (GradedObject ι C) :=
    EnoughInjectives.of_equivalence (piEquivalenceFunctorDiscrete ι C).functor
  exact EnoughInjectives.of_adjunction (endpointCofreeAdjunction C c)

/-- For C with zero morphisms, a zero object, binary biproducts, finite limits and enough
injectives, and any complex
shape c, cofree covers provide the enough-injectives structure on
the category of c-shaped complexes. The index, object and morphism
universes are independent. -/
instance instEnoughInjectivesEndpointCofree [HasFiniteLimits C] [EnoughInjectives C] :
    EnoughInjectives (HomologicalComplex C c) :=
  enoughInjectives_of_endpointCofree c

end HomologicalComplex
