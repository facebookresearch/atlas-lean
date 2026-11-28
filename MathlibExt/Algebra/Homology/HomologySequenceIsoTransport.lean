/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Connecting maps under isomorphisms of short exact complex sequences

Let C be an abelian category, c any complex shape, and S a short exact
sequence of complexes of shape c. An isomorphism e:S ≅ T makes T short
exact and induces cohomology isomorphisms on its first and third terms.

For a relation c.Rel(i,j), the connecting map δ_S:Hᵢ(S₃) → Hⱼ(S₁)
transforms into
Hⱼ(e₁) ∘ δ_S ∘ Hᵢ(e₃)⁻¹:Hᵢ(T₃) → Hⱼ(T₁).
This is the connecting map of T, and it satisfies the corresponding
naturality square with the forward component maps of e. The shape and
category universes are arbitrary.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace CategoryTheory.ShortComplex.ShortExact

variable {C I : Type*} [Category* C] [Abelian C] {c : ComplexShape I}
  {S T : ShortComplex (HomologicalComplex C c)}

/-- Let C be abelian, c a complex shape, S a short exact sequence of
complexes and e:S ≅ T an isomorphism of short complexes. For c.Rel(i,j),
the connecting map transported to T is
Hⱼ(e₁) ∘ δ_S ∘ Hᵢ(e₃)⁻¹:Hᵢ(T₃) → Hⱼ(T₁),
where e₁ and e₃ are the first and third component isomorphisms. -/
def connectingIsoTransport (hS : S.ShortExact) (e : S ≅ T)
    (i j : I) (hij : c.Rel i j) : T.X₃.homology i ⟶ T.X₁.homology j :=
  ((HomologicalComplex.homologyFunctor C c i).mapIso
    ((ShortComplex.π₃ : ShortComplex (HomologicalComplex C c) ⥤
        HomologicalComplex C c).mapIso e)).inv ≫
      hS.δ i j hij ≫
        ((HomologicalComplex.homologyFunctor C c j).mapIso
          ((ShortComplex.π₁ : ShortComplex (HomologicalComplex C c) ⥤
        HomologicalComplex C c).mapIso e)).hom

/-- Let C be abelian, S a short exact sequence of complexes of shape c,
and e:S ≅ T an isomorphism of short complexes. For c.Rel(i,j),
the map Hⱼ(e₁) ∘ δ_S ∘ Hᵢ(e₃)⁻¹ equals the connecting map δ_T
of the short exact sequence T obtained through e. -/
theorem connectingIsoTransport_eq (hS : S.ShortExact) (e : S ≅ T)
    (i j : I) (hij : c.Rel i j) :
    connectingIsoTransport hS e i j hij = (ShortComplex.shortExact_of_iso e hS).δ i j hij := by
  let e₃ := (HomologicalComplex.homologyFunctor C c i).mapIso
    ((ShortComplex.π₃ : ShortComplex (HomologicalComplex C c) ⥤ HomologicalComplex C c).mapIso e)
  change e₃.inv ≫ (hS.δ i j hij ≫ HomologicalComplex.homologyMap e.hom.τ₁ j) = _
  apply (Iso.inv_comp_eq e₃).2
  exact HomologicalComplex.HomologySequence.δ_naturality e.hom hS
    (ShortComplex.shortExact_of_iso e hS) i j hij

/-- In an abelian category C, let S be a short exact sequence of complexes
of shape c and e:S ≅ T an isomorphism of short complexes.
For c.Rel(i,j), the forward component maps satisfy
Hⱼ(e₁) ∘ δ_S = δ_transport ∘ Hᵢ(e₃), where
δ_transport=Hⱼ(e₁) ∘ δ_S ∘ Hᵢ(e₃)⁻¹ is the connecting map on T. -/
@[reassoc]
theorem connectingIsoTransport_naturality (hS : S.ShortExact) (e : S ≅ T)
    (i j : I) (hij : c.Rel i j) :
    hS.δ i j hij ≫ HomologicalComplex.homologyMap e.hom.τ₁ j =
      HomologicalComplex.homologyMap e.hom.τ₃ i ≫ connectingIsoTransport hS e i j hij := by
  rw [connectingIsoTransport_eq]
  exact HomologicalComplex.HomologySequence.δ_naturality e.hom hS
    (ShortComplex.shortExact_of_iso e hS) i j hij

end CategoryTheory.ShortComplex.ShortExact
