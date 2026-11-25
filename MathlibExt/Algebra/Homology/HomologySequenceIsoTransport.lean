/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Native connecting maps under isomorphisms of exact complex sequences

The original short exact sequence provides its native connecting map. An
isomorphism of the sequence supplies the component homology isomorphisms.
Native isomorphism transport earns exactness of the target sequence, and
native connecting-map naturality identifies its connecting map with this
computed conjugation. All complex shapes and category universes are retained.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace CategoryTheory.ShortComplex.ShortExact

variable {C I : Type*} [Category* C] [Abelian C] {c : ComplexShape I}
  {S T : ShortComplex (HomologicalComplex C c)}

/-- The original native connecting map transported by the actual sequence isomorphism. -/
def connectingIsoTransport (hS : S.ShortExact) (e : S ≅ T)
    (i j : I) (hij : c.Rel i j) : T.X₃.homology i ⟶ T.X₁.homology j :=
  ((HomologicalComplex.homologyFunctor C c i).mapIso
    ((ShortComplex.π₃ : ShortComplex (HomologicalComplex C c) ⥤ HomologicalComplex C c).mapIso e)).inv ≫
      hS.δ i j hij ≫
        ((HomologicalComplex.homologyFunctor C c j).mapIso
          ((ShortComplex.π₁ : ShortComplex (HomologicalComplex C c) ⥤ HomologicalComplex C c).mapIso e)).hom

/-- The transported value is the native connecting map of the earned target short exact sequence. -/
theorem connectingIsoTransport_eq (hS : S.ShortExact) (e : S ≅ T)
    (i j : I) (hij : c.Rel i j) :
    connectingIsoTransport hS e i j hij = (ShortComplex.shortExact_of_iso e hS).δ i j hij := by
  let e₃ := (HomologicalComplex.homologyFunctor C c i).mapIso
    ((ShortComplex.π₃ : ShortComplex (HomologicalComplex C c) ⥤ HomologicalComplex C c).mapIso e)
  change e₃.inv ≫ (hS.δ i j hij ≫ HomologicalComplex.homologyMap e.hom.τ₁ j) = _
  apply (Iso.inv_comp_eq e₃).2
  exact HomologicalComplex.HomologySequence.δ_naturality e.hom hS
    (ShortComplex.shortExact_of_iso e hS) i j hij

/-- The forward component maps give the original native connecting-map square. -/
@[reassoc]
theorem connectingIsoTransport_naturality (hS : S.ShortExact) (e : S ≅ T)
    (i j : I) (hij : c.Rel i j) :
    hS.δ i j hij ≫ HomologicalComplex.homologyMap e.hom.τ₁ j =
      HomologicalComplex.homologyMap e.hom.τ₃ i ≫ connectingIsoTransport hS e i j hij := by
  rw [connectingIsoTransport_eq]
  exact HomologicalComplex.HomologySequence.δ_naturality e.hom hS
    (ShortComplex.shortExact_of_iso e hS) i j hij

end CategoryTheory.ShortComplex.ShortExact
