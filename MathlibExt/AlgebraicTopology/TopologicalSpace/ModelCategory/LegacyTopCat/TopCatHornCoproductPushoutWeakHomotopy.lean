/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.TopCatHornCoproductSDR

/-!
# Pushout legs of coproducts of realized horn inclusions

For a `Type u` family of positive-dimensional horns, the categorical coproduct map
`Limits.Sigma.map hornSDRIncl` is `Arrow`-isomorphic to the bundled inclusion
`TopCat.ofHom hornSDRCopIncl` via `TopCat.hornSDR_arrow_iso`; transport the pushout
along that iso with `Arrow.leftFunc.mapIso`, `Arrow.rightFunc.mapIso`, and
`IsPushout.of_iso`, then apply `TopCat.hornSDR_pushout_inr_mem`. Hence every pushout
of such a coproduct is a weak homotopy equivalence. No transfinite composition,
further closure, or model structure is claimed.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace TopCat

variable {J : Type u} {n : J → ℕ} {k : ∀ j, Fin (n j + 1)}
  {hn : ∀ j, 0 < n j}

include hn
/-- Pushout legs of horn coproducts are weak homotopy equivalences. -/
theorem hornCoproduct_pushout_inr_mem_weakHomotopyEquivalences
    {Y P : TopCat.{u}}
    {f : (∐ fun j => hornSDRDomain J n k j) ⟶ Y}
    {g : (∐ fun j => hornSDRSimplex J n j) ⟶ P} {j : Y ⟶ P}
    (h : IsPushout
      (Limits.Sigma.map (fun j => hornSDRIncl J n k j)) f g j) :
    weakHomotopyEquivalences j := by
  let e := TopCat.hornSDR_arrow_iso J n k
  let eL : (∐ fun j => hornSDRDomain J n k j) ≅ _ := Arrow.leftFunc.mapIso e
  let eR : (∐ fun j => hornSDRSimplex J n j) ≅ _ := Arrow.rightFunc.mapIso e
  have commf : Limits.Sigma.map (fun j => hornSDRIncl J n k j) ≫ eR.hom =
      eL.hom ≫ TopCat.ofHom (hornSDRCopIncl J n k) := (e.hom.w).symm
  have commg : f ≫ (Iso.refl Y).hom = eL.hom ≫ (eL.inv ≫ f) := by simp
  have comminl : g ≫ (Iso.refl P).hom = eR.hom ≫ (eR.inv ≫ g) := by simp
  have comminr : j ≫ (Iso.refl P).hom = (Iso.refl Y).hom ≫ j := by simp
  have h' : IsPushout (TopCat.ofHom (hornSDRCopIncl J n k)) (eL.inv ≫ f)
      (eR.inv ≫ g) j :=
    h.of_iso eL eR (Iso.refl Y) (Iso.refl P) commf commg comminl comminr
  exact TopCat.hornSDR_pushout_inr_mem J n k hn h'

end TopCat
