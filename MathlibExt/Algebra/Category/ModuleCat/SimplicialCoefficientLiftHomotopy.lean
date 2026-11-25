/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- SOURCE-ONLY the original fixed coefficient prism under native output lift; Native has not been run.
module

public import MathlibExt.Algebra.Category.ModuleCat.SimplicialCoefficientLift
public import MathlibExt.AlgebraicTopology.DoldKan.AdditiveNormalizationHomotopy

/-!
# Native coefficient lift preserves the actual fixed normalized prism

The same original simplicial homotopy is acted on by both native tensor
functors. The actual tensor functor isomorphism and canonical additive
normalization homotopy comparison return its components to output lift
of the original coefficient homotopy. No desired compatibility is input.
-/

@[expose] public section
noncomputable section

open CategoryTheory AlgebraicTopology

universe u v s h

namespace ModuleCat.SimplicialCoefficientLift

variable (R : Type u) [CommRing R]

/-- Native tensoring before normalization retains the same fixed original
prism under coefficient and output lifts, in every shifted degree. -/
@[reassoc]
theorem normalizedIso_homotopy (M : ModuleCat.{s} R)
    {X Y : SimplicialObject (ModuleCat.{v} R)} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) (n m : ℕ) :
    (H.whiskerRight ((tensorBifunctorAt.{u, max s h, v} R).obj
        ((uliftFunctor.{h, s} R).obj M))).toNormalizedChainHomotopy.hom n m ≫
      (normalizedIso.{u, v, s, h} R M Y).hom.f m =
    (normalizedIso.{u, v, s, h} R M X).hom.f n ≫
      (uliftFunctor.{h, max v s} R).map
        ((H.whiskerRight ((tensorBifunctorAt.{u, s, v} R).obj M)).toNormalizedChainHomotopy.hom n m) := by
  let T := (tensorBifunctorAt.{u, s, v} R).obj M
  let T' := (tensorBifunctorAt.{u, max s h, v} R).obj ((uliftFunctor.{h, s} R).obj M)
  let U := uliftFunctor.{h, max v s} R
  let N := normalizedMooreComplex (ModuleCat.{max v s h} R)
  let t := tensorFunctorIso.{u, v, s, h} R M
  let sx := (N.map (Functor.whiskerLeft X t.hom)).f n
  let sy := (N.map (Functor.whiskerLeft Y t.hom)).f m
  let ex := ((HomologicalComplex.eval _ (ComplexShape.down ℕ) n).mapIso
    (((NormalizedQuotient.mooreCompMapIso U).app (X ⋙ T))))
  let ey := ((HomologicalComplex.eval _ (ComplexShape.down ℕ) m).mapIso
    (((NormalizedQuotient.mooreCompMapIso U).app (Y ⋙ T))))
  let hT := (H.whiskerRight T').toNormalizedChainHomotopy.hom n m
  let hTU := (H.whiskerRight (T ⋙ U)).toNormalizedChainHomotopy.hom n m
  let h0 := (H.whiskerRight T).toNormalizedChainHomotopy.hom n m
  have ht : hT ≫ sy = sx ≫ hTU := by
    have hn := SimplicialObject.Homotopy.normalizedFamilyHom_naturality
      (𝟭 (ModuleCat.{v} R ⥤ ModuleCat.{max v s h} R)) H t.hom n m
    change hT ≫ sy = sx ≫ hTU at hn
    exact hn
  have hu : U.map h0 ≫ ey.hom = ex.hom ≫ hTU := by
    have hn := NormalizedQuotient.mooreCompMapIso_homotopy U (H.whiskerRight T) n m
    change U.map h0 ≫ ey.hom = ex.hom ≫ hTU at hn
    exact hn
  have hi : hTU ≫ ey.inv = ex.inv ≫ U.map h0 := by
    calc
      hTU ≫ ey.inv = ex.inv ≫ (ex.hom ≫ hTU) ≫ ey.inv := by
        simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      _ = ex.inv ≫ (U.map h0 ≫ ey.hom) ≫ ey.inv := congrArg (fun z => ex.inv ≫ z ≫ ey.inv) hu.symm
      _ = ex.inv ≫ U.map h0 := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change hT ≫ (sy ≫ ey.inv) = (sx ≫ ex.inv) ≫ U.map h0
  calc
    hT ≫ (sy ≫ ey.inv) = (hT ≫ sy) ≫ ey.inv := (Category.assoc _ _ _).symm
    _ = (sx ≫ hTU) ≫ ey.inv := congrArg (fun z => z ≫ ey.inv) ht
    _ = sx ≫ (hTU ≫ ey.inv) := Category.assoc _ _ _
    _ = sx ≫ (ex.inv ≫ U.map h0) := congrArg (fun z => sx ≫ z) hi
    _ = _ := (Category.assoc _ _ _).symm

end ModuleCat.SimplicialCoefficientLift

end
