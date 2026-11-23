/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.RealizedInterval
public import MathlibExt.AlgebraicTopology.SimplicialSet.IntervalEndpointsAnodyne
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHRealizationCofibrations
public import Mathlib.AlgebraicTopology.ModelCategory.Cylinder

/-!
# The actual native interval cylinder

The original interval faces are native trivial cofibrations by the SAME
face/horn calculation and realization adjunction. Its whole boundary is a
cofibration. Tensoring with an actual cofibrant object gives the literal
native cylinder, with no given cylinder or contraction witness.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen CGWH.modelCategory

universe u v

namespace CGWH

/-- Both ORIGINAL interval endpoints are genuine native trivial cofibrations. -/
private theorem nativeIntervalEndpoint_mem_trivialCofibrations_computed (ε : Fin 2) :
    trivialCofibrations CGWH.{u, v} (nativeIntervalEndpoint.{u, v} ε) := by
  have he : nativeIntervalEndpoint.{u, v} ε =
      nativeZeroTensorUnitIso.{u, v}.inv ≫ SSet.toCGWH.{u, v}.map (SSet.stdSimplex.δ ε.rev) := by
    calc
      nativeIntervalEndpoint.{u, v} ε =
          nativeIntervalBoundaryEndpoint.{u, v} ε ≫ nativeIntervalBoundary.{u, v} :=
        (nativeIntervalBoundaryEndpoint_comp.{u, v} ε).symm
      _ = nativeZeroTensorUnitIso.{u, v}.inv ≫
          SSet.toCGWH.{u, v}.map (SSet.stdSimplex.δ ε.rev) := by
        change (nativeZeroTensorUnitIso.{u, v}.inv ≫
          SSet.toCGWH.{u, v}.map (SSet.boundary.ι ε.rev)) ≫
          SSet.toCGWH.{u, v}.map ((SSet.boundary.{v} 1).ι) = _
        rw [Category.assoc, ← Functor.map_comp, SSet.boundary.ι_ι]
  rw [he]
  let f : (Δ[0] : SSet.{v}) ⟶ Δ[1] := SSet.stdSimplex.δ ε.rev
  have hf : trivialCofibrations SSet.{v} f := by
    rw [← SSet.anodyneExtensions_eq_trivialCofibrations]
    exact SSet.anodyneExtensions_stdSimplex_endpoint ε.rev
  have hm := CGWH.modelCategory.toCGWH_map_mem_trivialCofibrations f hf
  exact (trivialCofibrations CGWH.{u, v}).comp_mem _ _
    ((trivialCofibrations CGWH.{u, v}).of_isIso nativeZeroTensorUnitIso.{u, v}.inv) hm

/-- Both actual original endpoint maps have the proved native trivial-cofibration property. -/
public theorem nativeIntervalEndpoint_mem_trivialCofibrations (ε : Fin 2) :
    trivialCofibrations CGWH.{u, v} (nativeIntervalEndpoint.{u, v} ε) :=
  nativeIntervalEndpoint_mem_trivialCofibrations_computed.{u, v} ε

/-- The original boundary inclusion is a native cofibration, through its
actual simplicial subcomplex mono and the SAME realization adjunction. -/
public theorem nativeIntervalBoundary_cofibration :
    Cofibration (nativeIntervalBoundary.{u, v}) := by
  let f : (∂Δ[1] : SSet.{v}) ⟶ Δ[1] := (SSet.boundary.{v} 1).ι
  letI : Cofibration f := (SSet.modelCategoryQuillen.cofibration_iff f).mpr inferInstance
  exact CGWH.modelCategory.toCGWH_map_cofibration f

/-- The original endpoint inclusion into an object's actual native cylinder. -/
public abbrev nativeIntervalCylinderEndpoint (A : CGWH.{u, v}) (ε : Fin 2) :
    A ⟶ A ⊗ nativeInterval.{u, v} :=
  (ρ_ A).inv ≫ A ◁ nativeIntervalEndpoint.{u, v} ε

/-- Its cylinder projection is the original identity at BOTH ends. -/
@[reassoc]
public theorem nativeIntervalCylinderEndpoint_fst (A : CGWH.{u, v}) (ε : Fin 2) :
    nativeIntervalCylinderEndpoint A ε ≫
        CartesianMonoidalCategory.fst A nativeInterval.{u, v} = 𝟙 A := by
  rw [Category.assoc, CartesianMonoidalCategory.whiskerLeft_fst,
    CartesianMonoidalCategory.rightUnitor_inv_fst]

/-- The second coordinate is the SAME original endpoint, after the
original unique map to the native tensor unit. -/
@[reassoc]
public theorem nativeIntervalCylinderEndpoint_snd (A : CGWH.{u, v}) (ε : Fin 2) :
    nativeIntervalCylinderEndpoint A ε ≫ CartesianMonoidalCategory.snd A nativeInterval.{u, v} =
      CartesianMonoidalCategory.toUnit A ≫ nativeIntervalEndpoint.{u, v} ε := by
  rw [Category.assoc, CartesianMonoidalCategory.whiskerLeft_snd,
    ← Category.assoc, CartesianMonoidalCategory.rightUnitor_inv_snd]

/-- The complete native endpoint point is its original tensor pairing. -/
public theorem nativeIntervalCylinderEndpoint_apply (A : CGWH.{u, v}) (ε : Fin 2) (a : A) :
    nativeIntervalCylinderEndpoint A ε a =
      tensorMk a (nativeIntervalEndpoint.{u, v} ε (CartesianMonoidalCategory.toUnit A a)) := by
  apply (tensorEquivProd A nativeInterval.{u, v}).injective
  rw [tensorEquivProd_tensorMk]
  apply Prod.ext
  · rw [tensorEquivProd_apply_fst]
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
      ConcreteCategory.congr_hom (nativeIntervalCylinderEndpoint_fst A ε) a
  · rw [tensorEquivProd_apply_snd]
    simpa only [ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom (nativeIntervalCylinderEndpoint_snd A ε) a

/-- The complete endpoint inclusion is natural in the original native
object map, at BOTH original interval endpoints. -/
@[reassoc]
public theorem nativeIntervalCylinderEndpoint_natural
    {A B : CGWH.{u, v}} (i : A ⟶ B) (ε : Fin 2) :
    i ≫ nativeIntervalCylinderEndpoint B ε =
      nativeIntervalCylinderEndpoint A ε ≫ (i ▷ nativeInterval.{u, v}) := by
  have hLeft : (i ≫ nativeIntervalCylinderEndpoint B ε) ≫
      CartesianMonoidalCategory.fst B nativeInterval.{u, v} = i := by
    calc
      _ = i ≫ (nativeIntervalCylinderEndpoint B ε ≫
          CartesianMonoidalCategory.fst B nativeInterval.{u, v}) := Category.assoc _ _ _
      _ = i ≫ 𝟙 B := congrArg (fun f : B ⟶ B => i ≫ f)
        (nativeIntervalCylinderEndpoint_fst B ε)
      _ = i := Category.comp_id i
  have hRight : (nativeIntervalCylinderEndpoint A ε ≫ (i ▷ nativeInterval.{u, v})) ≫
      CartesianMonoidalCategory.fst B nativeInterval.{u, v} = i := by
    calc
      _ = nativeIntervalCylinderEndpoint A ε ≫
          ((i ▷ nativeInterval.{u, v}) ≫
            CartesianMonoidalCategory.fst B nativeInterval.{u, v}) := Category.assoc _ _ _
      _ = nativeIntervalCylinderEndpoint A ε ≫
          (CartesianMonoidalCategory.fst A nativeInterval.{u, v} ≫ i) :=
        congrArg (fun f : A ⊗ nativeInterval.{u, v} ⟶ B =>
          nativeIntervalCylinderEndpoint A ε ≫ f)
          (CartesianMonoidalCategory.whiskerRight_fst i nativeInterval.{u, v})
      _ = (nativeIntervalCylinderEndpoint A ε ≫
          CartesianMonoidalCategory.fst A nativeInterval.{u, v}) ≫ i :=
        (Category.assoc _ _ _).symm
      _ = 𝟙 A ≫ i := congrArg (fun f : A ⟶ A => f ≫ i)
        (nativeIntervalCylinderEndpoint_fst A ε)
      _ = i := Category.id_comp i
  apply CartesianMonoidalCategory.hom_ext
  · exact hLeft.trans hRight.symm
  · rw [Category.assoc, nativeIntervalCylinderEndpoint_snd, Category.assoc,
      CartesianMonoidalCategory.whiskerRight_snd, ← Category.assoc,
      nativeIntervalCylinderEndpoint_snd]
    exact congrArg (fun f => f ≫ nativeIntervalEndpoint.{u, v} ε)
      (CartesianMonoidalCategory.toUnit_unique _ _)

/-- The actual native cylinder projection is weak, derived from its
original trivial-cofibration endpoint and original section equation. -/
public theorem nativeIntervalProjection_weakEquivalence
    (A : CGWH.{u, v}) [IsCofibrant A] :
    WeakEquivalence (CartesianMonoidalCategory.fst A nativeInterval.{u, v}) := by
  have hInitial : cofibrations CGWH.{u, v} (initial.to A) :=
    (cofibration_iff _).mp (inferInstance : Cofibration (initial.to A))
  have hPush : trivialCofibrations CGWH.{u, v}
      ((Arrow.mk (initial.to A) □ Arrow.mk (nativeIntervalEndpoint.{u, v} 0)).hom) :=
    IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_right
      (C := CGWH.{u, v}) (initial.to A) (nativeIntervalEndpoint.{u, v} 0)
      hInitial (nativeIntervalEndpoint_mem_trivialCofibrations.{u, v} 0)
  let e := MonoidalCategory.Arrow.PushoutProduct.isInitialIso'
    (Arrow.mk (nativeIntervalEndpoint.{u, v} 0)) initialIsInitial (W := A)
  have hθ : trivialCofibrations CGWH.{u, v} (A ◁ nativeIntervalEndpoint.{u, v} 0) :=
    ((trivialCofibrations CGWH.{u, v}).arrow_iso_iff e).mp hPush
  letI : WeakEquivalence (A ◁ nativeIntervalEndpoint.{u, v} 0) :=
    (weakEquivalence_iff _).mpr hθ.2
  letI : WeakEquivalence (nativeIntervalCylinderEndpoint A 0) := inferInstance
  exact weakEquivalence_of_precomp_of_fac (nativeIntervalCylinderEndpoint_fst A 0)

/-- The actual original interval supplies its LITERAL cylinder data.
The carrier remains A tensor the original interval, so a whole original
source square can be supplied directly, with no hidden carrier transport. -/
public abbrev nativeIntervalCylinder (A : CGWH.{u, v}) [IsCofibrant A] : Cylinder A where
  I := A ⊗ nativeInterval.{u, v}
  i₀ := nativeIntervalCylinderEndpoint A 0
  i₁ := nativeIntervalCylinderEndpoint A 1
  π := CartesianMonoidalCategory.fst A nativeInterval.{u, v}
  i₀_π := nativeIntervalCylinderEndpoint_fst A 0
  i₁_π := nativeIntervalCylinderEndpoint_fst A 1
  weakEquivalence_π := nativeIntervalProjection_weakEquivalence A

end CGWH

end
