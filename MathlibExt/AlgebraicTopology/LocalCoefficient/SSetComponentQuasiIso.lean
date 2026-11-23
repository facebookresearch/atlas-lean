/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSetComponentBaseCoherence
public import MathlibExt.Algebra.Homology.QuasiIsoColimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Quasi-isomorphism assembly through actual component coefficient cofans

The original component coefficient map squares and actual coefficient
cofan colimits assemble componentwise quasi-isomorphisms into the SAME
original ambient pullback chain map. The component indexing is changed by
the ACTUAL bijection mapπ₀ f. Exact coproduct homology preservation is an
explicit structural category assumption, not a coefficient flatness claim.
An application to weak maps must derive the component hypotheses first.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe uR uX

namespace SSet

variable {R : Type uR} [CommRing R] {X Y : SSet.{uX}}

private noncomputable def isColimitLiteralLocalCoefficientComponentCofan
    (Z : SSet.{uX}) (M : SSet.LocalSystem R Z) :
    IsColimit (Cofan.mk (localCoefficientChainComplex M)
      (localCoefficientComponentInclusion Z M)) := by
  let s := Cofan.mk (localCoefficientChainComplex M)
    (localCoefficientComponentInclusion Z M)
  have hd : Sigma.desc s.inj = localCoefficientComponentCoproductMap Z M := by
    apply Sigma.hom_ext
    intro c
    exact (Sigma.ι_comp_desc (localCoefficientComponentInclusion Z M) c).trans
      (localCoefficientComponentCoproductMap_ι Z M c).symm
  have hIso : IsIso (localCoefficientComponentCoproductMap Z M) :=
    localCoefficientComponentCoproductMap_isIso Z M
  letI : IsIso (Sigma.desc s.inj) := hd.symm ▸ hIso
  exact Cofan.isColimitOfIsIsoSigmaDesc s

/-- The actual coefficient pullback map is a quasi-isomorphism when its
ACTUAL component maps are, with the original component-index bijection.
The theorem uses existing colimit homology comparison and exact original
map squares; it is an assembly step, not an assumed excision endpoint. -/
public theorem localCoefficientPullbackChainMap_quasiIso_of_components
    (f : X ⟶ Y) (L : SSet.LocalSystem R Y)
    (hπ : Function.Bijective (mapπ₀ f))
    [(colim (J := Discrete (π₀ X)) (C := ModuleCat.{max uR uX} R)).PreservesHomology]
    (hcomp : ∀ c : π₀ X, QuasiIso (localCoefficientComponentBaseMap f c L)) :
    QuasiIso (localCoefficientPullbackChainMap f L) := by
  let K : Discrete (π₀ X) ⥤ ChainComplex (ModuleCat.{max uR uX} R) ℕ :=
    Discrete.functor (fun c => localCoefficientComponentComplex X (L.pullback f) c)
  let T : Discrete (π₀ X) ⥤ ChainComplex (ModuleCat.{max uR uX} R) ℕ :=
    Discrete.functor (fun c => localCoefficientComponentComplex Y L (mapπ₀ f c))
  let τ : K ⟶ T := Discrete.natTrans
    (fun c : Discrete (π₀ X) => localCoefficientComponentBaseMap f c.as L)
  let s : Cocone K := Cofan.mk (localCoefficientChainComplex (L.pullback f))
    (localCoefficientComponentInclusion X (L.pullback f))
  let t : Cocone T := Cofan.mk (localCoefficientChainComplex L)
    (fun c => localCoefficientComponentInclusion Y L (mapπ₀ f c))
  have hs : IsColimit s := isColimitLiteralLocalCoefficientComponentCofan X (L.pullback f)
  let e : π₀ X ≃ π₀ Y := Equiv.ofBijective (mapπ₀ f) hπ
  let ty := Cofan.mk (localCoefficientChainComplex L) (localCoefficientComponentInclusion Y L)
  have hty : IsColimit ty := isColimitLiteralLocalCoefficientComponentCofan Y L
  have ht : IsColimit t :=
    (Cofan.isColimitEquivOfEquiv e ty) hty
  have hτ (c : Discrete (π₀ X)) :
      τ.app c = localCoefficientComponentBaseMap f c.as L := rfl
  have hSquare (c : Discrete (π₀ X)) :
      s.ι.app c ≫ localCoefficientPullbackChainMap f L = τ.app c ≫ t.ι.app c := by
    change localCoefficientComponentInclusion X (L.pullback f) c.as ≫
        localCoefficientPullbackChainMap f L =
      localCoefficientComponentBaseMap f c.as L ≫
        localCoefficientComponentInclusion Y L (mapπ₀ f c.as)
    exact (localCoefficientComponentBaseMap_comp f c.as L).symm
  have hQI (c : Discrete (π₀ X)) : QuasiIso (τ.app c) := (hτ c).symm ▸ hcomp c.as
  exact HomologicalComplex.quasiIso_of_isColimit_of_objectwise τ s t hs ht
    (localCoefficientPullbackChainMap f L) hSquare hQI

section IntegerCoefficients

/-- Exactness of the ACTUAL integer-module component coproduct is derived
through the existing exact forgetful functor and the stock additive-group
coproduct theorem. This does not invoke a scalar-lifted module facade or
assume tensor flatness. -/
private theorem integerComponentColim_preservesHomology (X : SSet.{uX}) :
    (colim (J := Discrete (π₀ X)) (C := ModuleCat.{uX} ℤ)).PreservesHomology := by
  let U : ModuleCat.{uX} ℤ ⥤ AddCommGrpCat.{uX} :=
    forget₂ (ModuleCat.{uX} ℤ) AddCommGrpCat.{uX}
  let : HasExactColimitsOfShape (Discrete (π₀ X)) (ModuleCat.{uX} ℤ) :=
    HasExactColimitsOfShape.domain_of_functor (Discrete (π₀ X)) U
  infer_instance

/-- The original literal-integer coefficient map is assembled through
its ACTUAL component maps, with exact component coproduct homology derived
internally. The final weak-map application must derive those component
quasi-isomorphisms, rather than supply the desired ambient conclusion. -/
public theorem localCoefficientPullbackChainMap_integer_quasiIso_of_components
    {X Y : SSet.{uX}} (f : X ⟶ Y) (L : SSet.LocalSystem ℤ Y)
    (hπ : Function.Bijective (mapπ₀ f))
    (hcomp : ∀ c : π₀ X, QuasiIso (localCoefficientComponentBaseMap f c L)) :
    QuasiIso (localCoefficientPullbackChainMap f L) := by
  let : (colim (J := Discrete (π₀ X)) (C := ModuleCat.{uX} ℤ)).PreservesHomology :=
    integerComponentColim_preservesHomology X
  exact localCoefficientPullbackChainMap_quasiIso_of_components f L hπ hcomp

end IntegerCoefficients

end SSet

end
