/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSetBaseCoherence
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Original coefficient pullback chains under an actual simplicial Iso

The original base map reindexes each simplex coproduct and transports its
actual coefficient object. A simplicial Iso gives an equivalence of these
indexing types; the stock coproduct equivalence produces the inverse in
every degree. This identifies the SAME original chain map, not just its
source and target carriers.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CategoryHomology
open scoped Simplicial

universe uR uX

namespace SSet

variable {R : Type uR} [CommRing R] {X Y : SSet.{uX}}

/-- An actual simplicial isomorphism makes the original coefficient
pullback chain map invertible in every degree. -/
public theorem localCoefficientPullbackChainMap_f_isIso_of_isIso
    (f : X ⟶ Y) [IsIso f] (L : SSet.LocalSystem R Y) (n : ℕ) :
    IsIso ((localCoefficientPullbackChainMap f L).f n) := by
  let e : X _⦋n⦌ ≃ Y _⦋n⦌ :=
    Equiv.ofBijective (f.app (op ⦋n⦌)) ((isIso_iff_bijective _).mp inferInstance)
  let F := localCoefficientFamily (L.pullback f) n
  let G := localCoefficientFamily L n
  let w : ∀ σ : X _⦋n⦌, G (e σ) ≅ F σ :=
    fun σ => (eqToIso (localCoefficientPullbackFamilyEq f L σ)).symm
  let E : (∐ F) ≅ (∐ G) := Sigma.whiskerEquiv e w
  let eX : (localCoefficientChainComplex (L.pullback f)).X n ≅ (∐ F) :=
    eqToIso (localCoefficientChainComplex_X (L.pullback f) n)
  let eY : (localCoefficientChainComplex L).X n ≅ (∐ G) :=
    eqToIso (localCoefficientChainComplex_X L n)
  let m : (∐ F) ⟶ (∐ G) :=
    eX.inv ≫ (localCoefficientPullbackChainMap f L).f n ≫ eY.hom
  have he : m = E.hom := by
    apply Sigma.hom_ext
    intro σ
    have hMap : (Sigma.ι F σ ≫ eX.inv) ≫
        (localCoefficientPullbackChainMap f L).f n ≫ eY.hom =
        eqToHom (localCoefficientPullbackFamilyEq f L σ) ≫ Sigma.ι G (e σ) :=
      localCoefficientι_pullbackChainMap_conjugate f L n σ
    have hE : Sigma.ι F σ ≫ E.hom =
        eqToHom (localCoefficientPullbackFamilyEq f L σ) ≫ Sigma.ι G (e σ) := by
      dsimp only [E, Sigma.whiskerEquiv]
      rw [Sigma.ι_comp_map']
      rfl
    have hStart : Sigma.ι F σ ≫ m = (Sigma.ι F σ ≫ eX.inv) ≫
        (localCoefficientPullbackChainMap f L).f n ≫ eY.hom := by
      simp only [m, Category.assoc]
    exact hStart.trans (hMap.trans hE.symm)
  have hE : IsIso E.hom := E.isIso_hom
  let : IsIso m := he.symm ▸ hE
  let : IsIso eX.hom := eX.isIso_hom
  let : IsIso eY.inv := eY.isIso_inv
  have hm : eX.hom ≫ m ≫ eY.inv = (localCoefficientPullbackChainMap f L).f n := by
    calc
      eX.hom ≫ m ≫ eY.inv = (eX.hom ≫ eX.inv) ≫
          (localCoefficientPullbackChainMap f L).f n ≫ (eY.hom ≫ eY.inv) := by
        simp only [m, Category.assoc]
      _ = _ := by rw [eX.hom_inv_id, eY.hom_inv_id, Category.id_comp, Category.comp_id]
  exact hm ▸ (inferInstance : IsIso (eX.hom ≫ m ≫ eY.inv))

/-- The SAME whole original coefficient chain map is an isomorphism for
an actual simplicial isomorphism. -/
public theorem localCoefficientPullbackChainMap_isIso_of_isIso
    (f : X ⟶ Y) [IsIso f] (L : SSet.LocalSystem R Y) :
    IsIso (localCoefficientPullbackChainMap f L) := by
  let (n : ℕ) : IsIso ((localCoefficientPullbackChainMap f L).f n) :=
    localCoefficientPullbackChainMap_f_isIso_of_isIso f L n
  exact HomologicalComplex.Hom.isIso_of_components _

section OverBase

variable {Z : SSet.{uX}}

/-- For an ACTUAL isomorphism over a fixed coefficient base, the original
over-base chain map is an Iso. Both coefficient comparison and base-map
inverses are derived from the same original systems and simplex maps. -/
public theorem localCoefficientChainMapOver_isIso
    (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) (a : X ⟶ Z)
    (ha : a = f ≫ g) (L : SSet.LocalSystem R Z) :
    IsIso (localCoefficientChainMapOver f g a ha L) := by
  let E := (LocalSystem.pullbackCongrIso ha L) ≪≫
    (LocalSystem.pullbackCompIso f g L)
  let e := (localCoefficientChainComplexFunctor (R := R) (X := X)).mapIso E
  have he : e.hom = localCoefficientChainMap E.hom := by rfl
  let : IsIso (localCoefficientChainMap E.hom) :=
    he ▸ (inferInstance : IsIso e.hom)
  let : IsIso (localCoefficientPullbackChainMap f (L.pullback g)) :=
    localCoefficientPullbackChainMap_isIso_of_isIso f (L.pullback g)
  unfold localCoefficientChainMapOver
  infer_instance

end OverBase

end SSet

end
