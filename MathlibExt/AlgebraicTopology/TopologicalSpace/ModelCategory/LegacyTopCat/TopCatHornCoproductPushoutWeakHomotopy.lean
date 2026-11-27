/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.TopCatHornCoproductSDR

/-!
# Pushout of a positive-dimensional horn coproduct

For a family of positive-dimensional realized horn inclusions, the categorical
coproduct map identifies with the bundled inclusion of their disjoint unions.
Every pushout of that coproduct has a weak homotopy-equivalence opposite leg.
The family index and the topological carriers lie in the same specified universe.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace TopCat

variable {J : Type u} {n : J → ℕ} {k : ∀ j, Fin (n j + 1)}
  {hn : ∀ j, 0 < n j}

include hn
/--
Given a positive-dimensional horn family and a pushout of its categorical
coproduct inclusion, the opposite pushout leg is a weak homotopy equivalence.
-/
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
