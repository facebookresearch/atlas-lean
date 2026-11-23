/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopPair.Coproduct
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

@[expose] public section

/-! # Coproduct colimits for `TopPair`

This module lifts the explicit `TopPair` coproduct `sigma` to categorical
colimit instances. The direct `HasCoproduct P` instance is operational;
the shape-wide `HasCoproductsOfShape` instance is derived via transport
along `Discrete.natIsoFunctor` for generic machinery.
-/

open CategoryTheory Limits

universe x w v u

namespace TopPair

variable {ι : Type v} (P : ι → TopPair.{max v u})

/-- Direct coproduct instance via the explicit `sigma` cofan. -/
noncomputable instance : HasCoproduct P :=
  HasColimit.mk ⟨_, sigmaCofanIsColimit P⟩

/-- Canonical iso `∐ P ≅ sigma P`, oriented as `TopCat.sigmaIsoSigma`. -/
noncomputable def sigmaIsoSigma : ∐ P ≅ sigma P :=
  (colimit.isColimit _).coconePointUniqueUpToIso (sigmaCofanIsColimit P)

/-- Leg of `∐ P` equals the explicit leg via `sigmaIsoSigma`. -/
@[reassoc (attr := simp)]
theorem sigmaIsoSigma_hom_ι (i : ι) :
    Sigma.ι P i ≫ (sigmaIsoSigma P).hom = sigmaι P i :=
  colimit.comp_coconePointUniqueUpToIso_hom (sigmaCofanIsColimit P) ⟨i⟩

/-- Explicit sigma comparison for a functor on topological pairs that
preserves the selected coproduct. -/
noncomputable def mapSigmaIso
    {C : Type w} [Category.{x} C]
    (F : TopPair.{max v u} ⥤ C)
    [HasCoproduct (fun i => F.obj (P i))]
    [PreservesColimit (Discrete.functor P) F] :
    (∐ fun i => F.obj (P i)) ≅ F.obj (sigma P) :=
  (PreservesCoproduct.iso F P).symm ≪≫ F.mapIso (sigmaIsoSigma P)

/-- The explicit mapped sigma comparison agrees with mapped explicit
injections. -/
@[reassoc (attr := simp)]
theorem mapSigmaIso_hom_ι
    {C : Type w} [Category.{x} C]
    (F : TopPair.{max v u} ⥤ C)
    [HasCoproduct (fun i => F.obj (P i))]
    [PreservesColimit (Discrete.functor P) F] (i : ι) :
    Sigma.ι (fun i => F.obj (P i)) i ≫ (mapSigmaIso P F).hom =
      F.map (sigmaι P i) := by
  rw [mapSigmaIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc]
  change (Sigma.ι _ i ≫ (PreservesCoproduct.iso F P).inv) ≫
      F.map (sigmaIsoSigma P).hom = _
  rw [PreservesCoproduct.inv_hom, Limits.ι_comp_sigmaComparison]
  rw [← F.map_comp, sigmaIsoSigma_hom_ι]

/-- Shape-wide coproducts from the direct family instance via `natIsoFunctor`. -/
noncomputable instance (priority := 100) : HasCoproductsOfShape ι TopPair.{max v u} where
  has_colimit _ := hasColimit_of_iso Discrete.natIsoFunctor

end TopPair
