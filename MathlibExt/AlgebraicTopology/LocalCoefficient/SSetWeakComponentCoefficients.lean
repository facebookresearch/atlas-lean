/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.HomotopyFiberAcyclicity
public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSetComponentQuasiIso
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.ComponentRealizationWeakEquivalence
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverCore
public import Mathlib.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic

/-!
# Original local-coefficient maps on arbitrary simplicial components

The existing regular-cover/projective-stalk comparison is applied to the
actual restricted map. Connectedness of its target fundamental groupoid is
derived from the existing component, with no ambient Kan assumption.

The original pullback-composition Isos and whole inclusion squares identify
the component coefficient maps. The actual literal integer-module component
coproduct then assembles the same original ambient pullback chain map.
No coefficient flatness, component quasi-isomorphism, or excision witness is
an input to the final weak-map theorem.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Simplicial

universe u

namespace SSet

/-- A vertex in an actual connected simplicial set has a genuine
fundamental-groupoid arrow to every object, without a Kan premise. -/
public theorem fundamentalGroupoid_nonempty_hom_of_isConnected
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌)
    (z : FundamentalGroupoid X) : Nonempty (FundamentalGroupoid.mk x ⟶ z) := by
  obtain ⟨y, rfl⟩ := FundamentalGroupoid.mk_surjective z
  obtain ⟨v⟩ := KanComplex.nativeCover_vertexFiber_nonempty (X := X) (x := x) y
  exact ⟨KanComplex.nativeCoverVertexPathEquiv (X := X) (x := x) y v⟩

/-- The original over-base coefficient map is a quasi-isomorphism when
its actual connected target map is weak. All source-system transport is
the existing pullback congruence/composition transport. -/
public theorem localCoefficientChainMapOver_quasiIso_of_weak
    {X Y Z : SSet.{u}} (f : X ⟶ Y) (hf : realizationWeakEquivalences f)
    (g : Y ⟶ Z) (a : X ⟶ Z) (ha : a = f ≫ g)
    (y : Y _⦋0⦌)
    (hconn : ∀ z : FundamentalGroupoid Y, Nonempty (FundamentalGroupoid.mk y ⟶ z))
    (L : SSet.LocalSystem ℤ Z) :
    QuasiIso (localCoefficientChainMapOver f g a ha L) := by
  let E := (LocalSystem.pullbackCongrIso ha L) ≪≫ (LocalSystem.pullbackCompIso f g L)
  let e := (localCoefficientChainComplexFunctor (R := ℤ) (X := X)).mapIso E
  let : IsIso (localCoefficientChainMap E.hom) := by
    change IsIso e.hom
    infer_instance
  let : QuasiIso (localCoefficientPullbackChainMap f (L.pullback g)) :=
    realizationWeakEquivalences.quasiIso_localCoefficientPullbackChainMap
      f hf y hconn (L.pullback g)
  unfold localCoefficientChainMapOver
  infer_instance

/-- Every original component coefficient map is a quasi-isomorphism,
derived from the original weak map rather than supplied to the assembly. -/
public theorem localCoefficientComponentBaseMap_quasiIso_of_weak
    {X Y : SSet.{u}} (f : X ⟶ Y) (hf : realizationWeakEquivalences f)
    (c : π₀ X) (L : SSet.LocalSystem ℤ Y) :
    QuasiIso (localCoefficientComponentBaseMap f c L) := by
  let K : SSet.{u} := π₀.component c
  let T : SSet.{u} := π₀.component (mapπ₀ f c)
  let m : K ⟶ T := componentBaseMap f c
  let iX : K ⟶ X := (π₀.component c).ι
  let iY : T ⟶ Y := (π₀.component (mapπ₀ f c)).ι
  have hm : realizationWeakEquivalences m := realizationWeakEquivalences_componentBaseMap f hf c
  obtain ⟨v, hv⟩ := (mapπ₀ f c).mk_surjective
  let y : T _⦋0⦌ := ⟨v, by simpa [π₀.component] using hv⟩
  have hconn (z : FundamentalGroupoid T) : Nonempty (FundamentalGroupoid.mk y ⟶ z) :=
    fundamentalGroupoid_nonempty_hom_of_isConnected T y z
  let q := localCoefficientComponentBaseMapOver f c L
  let : QuasiIso q := localCoefficientChainMapOver_quasiIso_of_weak
    m hm iY (iX ≫ f) (componentBaseMap_ι f c).symm y hconn L
  let E := LocalSystem.pullbackCompIso iX f L
  let e := (localCoefficientChainComplexFunctor (R := ℤ) (X := K)).mapIso E
  let : IsIso (localCoefficientChainMap E.inv) := by
    change IsIso e.inv
    infer_instance
  change QuasiIso (localCoefficientChainMap E.inv ≫ q)
  infer_instance

/-- A weak simplicial map induces the ACTUAL original coefficient-chain
quasi-isomorphism for every target integer local system and arbitrary
ambient components. Exactness of its actual component coproduct is derived
internally; neither endpoint is assumed Kan or connected. -/
public theorem realizationWeakEquivalences.quasiIso_localCoefficientPullbackChainMap_allComponents
    {X Y : SSet.{u}} (f : X ⟶ Y) (hf : realizationWeakEquivalences f)
    (L : SSet.LocalSystem ℤ Y) : QuasiIso (localCoefficientPullbackChainMap f L) := by
  exact localCoefficientPullbackChainMap_integer_quasiIso_of_components f L
    hf.bijective_mapπ₀ (fun c => localCoefficientComponentBaseMap_quasiIso_of_weak f hf c L)

/-- The actual over-base map is a quasi-isomorphism for a weak original
map on arbitrary components. The entire source coefficient transport is
the existing congruence/composition Iso; no connected target is required. -/
public theorem localCoefficientChainMapOver_quasiIso_of_weak_allComponents
    {X Y Z : SSet.{u}} (f : X ⟶ Y) (hf : realizationWeakEquivalences f)
    (g : Y ⟶ Z) (a : X ⟶ Z) (ha : a = f ≫ g)
    (L : SSet.LocalSystem ℤ Z) : QuasiIso (localCoefficientChainMapOver f g a ha L) := by
  let E := (LocalSystem.pullbackCongrIso ha L) ≪≫ LocalSystem.pullbackCompIso f g L
  let e := (localCoefficientChainComplexFunctor (R := ℤ) (X := X)).mapIso E
  let : IsIso (localCoefficientChainMap E.hom) := by
    change IsIso e.hom
    infer_instance
  let : QuasiIso (localCoefficientPullbackChainMap f (L.pullback g)) :=
    realizationWeakEquivalences.quasiIso_localCoefficientPullbackChainMap_allComponents f hf _
  unfold localCoefficientChainMapOver
  infer_instance

/-- An actual base-pullback quasi-isomorphism transports to the original
over-base coefficient map through the forced source Iso. -/
public theorem localCoefficientChainMapOver_quasiIso_of_pullback
    {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (a : X ⟶ Z) (ha : a = f ≫ g)
    (L : SSet.LocalSystem ℤ Z)
    (hf : QuasiIso (localCoefficientPullbackChainMap f (L.pullback g))) :
    QuasiIso (localCoefficientChainMapOver f g a ha L) := by
  let E := (LocalSystem.pullbackCongrIso ha L) ≪≫ LocalSystem.pullbackCompIso f g L
  let e := (localCoefficientChainComplexFunctor (R := ℤ) (X := X)).mapIso E
  let : IsIso (localCoefficientChainMap E.hom) := by
    change IsIso e.hom
    infer_instance
  let : QuasiIso (localCoefficientPullbackChainMap f (L.pullback g)) := hf
  unfold localCoefficientChainMapOver
  infer_instance

end SSet

end
