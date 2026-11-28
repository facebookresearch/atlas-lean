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
# Cofree complexes with endpoint terms

Let C be an abelian category, c a complex shape on an arbitrary index type ι,
and I : ι → C a family of objects. Put Eᵢ = I(c.next i) when c has an outgoing
edge at i, and Eᵢ = 0 otherwise. The cofree complex D(I) has terms
D(I)ᵢ = Iᵢ ⊕ Eᵢ. Along an edge i → j, its differential projects onto Eᵢ,
identifies that object with Iⱼ and includes it as the first summand of D(I)ⱼ.
Successive differentials compose to zero.

For any c-shaped complex K, morphisms K → D(I) correspond bijectively to
arbitrary families aᵢ : Kᵢ → Iᵢ. The first component is aᵢ, and the second
component along i → j is dᵏᵢⱼ followed by aⱼ. At an index without an outgoing
edge the second component is zero.

Injective objects Iᵢ give an injective complex D(I), and monic first
components give a monic complex morphism. Thus enough injectives in C imply
enough injectives in the category of c-shaped complexes. Each term uses only
a binary biproduct; the index and both category universes are independent.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Classical ZeroObject

universe u v w

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} {c : ComplexShape ι}

/-- For an abelian category C, any complex shape c and a family of
injective objects Iᵢ, the complex D(I) is injective in the category
of c-shaped complexes. Its term at an endpoint has zero second summand. -/
theorem endpointCofree_injective (I : ι → C) [∀ i, Injective (I i)] :
    Injective (endpointCofree (c := c) I) := by
  let e := piEquivalenceFunctorDiscrete ι C
  have hD : Injective (e.functor.obj I) :=
    injective_discrete_of_obj (e.functor.obj I) (fun i => by
      change Injective (I i.as)
      infer_instance)
  have hI : Injective (I : GradedObject ι C) := (e.map_injective_iff I).1 hD
  exact (endpointCofreeAdjunction C c).map_injective I hI

/-- For a complex K in an abelian category and a family of monomorphisms
aᵢ : Kᵢ → Iᵢ, the prescribed cofree morphism K → D(I) is a
monomorphism of complexes of the same shape. -/
theorem endpointCofreeHom_mono (K : HomologicalComplex C c) (I : ι → C)
    (a : ∀ i, K.X i ⟶ I i) [∀ i, Mono (a i)] :
    Mono (endpointCofreeHom K I a) := by
  apply HomologicalComplex.mono_of_mono_f
  intro i
  exact mono_of_mono_fac (endpointCofreeHom_fst K I a i)

/-- If an abelian category C has enough injectives, a complex K of any
shape has a cofree morphism into D(I), where Iᵢ is the chosen injective
object containing Kᵢ and the first coefficient is the chosen
monomorphism Kᵢ → Iᵢ. -/
def endpointCofreeCover (K : HomologicalComplex C c) [EnoughInjectives C] :
    K ⟶ endpointCofree (c := c) (fun i => Injective.under (K.X i)) :=
  endpointCofreeHom K _ (fun i => Injective.ι (K.X i))

/-- For a complex K in an abelian category with enough injectives,
the cofree cover followed by the first projection in degree i is
the chosen inclusion of Kᵢ into its injective object. -/
@[reassoc (attr := simp)]
theorem endpointCofreeCover_fst (K : HomologicalComplex C c) [EnoughInjectives C] (i : ι) :
    (endpointCofreeCover K).f i ≫
        endpointCofreeProjection (c := c) (fun j => Injective.under (K.X j)) i =
      Injective.ι (K.X i) :=
  endpointCofreeHom_fst _ _ _ _

/-- If C is an abelian category with enough injectives, then the category
of complexes in C of any shape c has enough injectives. Each complex
embeds in the cofree complex formed from its degreewise injective
objects, including at indices with no outgoing edge. -/
theorem enoughInjectives_of_endpointCofree [EnoughInjectives C] :
    EnoughInjectives (HomologicalComplex C c) := by
  letI : EnoughInjectives (Discrete ι ⥤ C) := enoughInjectives_discrete ι
  letI : EnoughInjectives (GradedObject ι C) :=
    EnoughInjectives.of_equivalence (piEquivalenceFunctorDiscrete ι C).functor
  exact EnoughInjectives.of_adjunction (endpointCofreeAdjunction C c)

/-- For an abelian category C with enough injectives and any complex
shape c, cofree covers provide the enough-injectives structure on
the category of c-shaped complexes. The index, object and morphism
universes are independent. -/
instance instEnoughInjectivesEndpointCofree [EnoughInjectives C] :
    EnoughInjectives (HomologicalComplex C c) :=
  enoughInjectives_of_endpointCofree

end HomologicalComplex
