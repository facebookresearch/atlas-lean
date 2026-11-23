/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Realization.ContinuousWhitehead

/-!
# Consumers of continuous Whitehead for realized simplicial sets

These tests use the native Δ[0] cylinder, distinguish its two endpoints,
check the model-to-continuous homotopy bridge, and retain the given map
as the forward map of the Whitehead equivalence.
-/

universe k

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped Simplicial MonoidalCategory SSet.modelCategoryQuillen TopCat.modelCategory

namespace CanonicalContinuousWhiteheadConsumers

private abbrev K : SSet.{k} := (Δ[0] : SSet.{k})
private abbrev L : SSet.{k} := (Δ[1] : SSet.{k})
private def P : Cylinder (SSet.toTop.obj (K.{k} : SSet.{k})) :=
  SSet.RealizationCWUpgrade.realizedStandardCylinder.{k} K.{k}

private def intervalCoordinate :
    (P.{k} : Cylinder (SSet.toTop.obj K.{k})).I ⟶ TopCat.I.{k} :=
  SSet.toTop.map (CartesianMonoidalCategory.snd K.{k} L.{k}) ≫
    SSet.stdSimplex.toTopObjIsoI.{k}.hom

private theorem coordinate_zero :
    ((P.{k}).i₀ : SSet.toTop.obj K.{k} ⟶ (P.{k}).I) ≫ intervalCoordinate.{k} =
      TopCat.const (X := SSet.toTop.obj K.{k}) (0 : TopCat.I.{k}) := by
  let a : K.{k} ⟶ K.{k} ⊗ L.{k} := SSet.ι₀
  let b : K.{k} ⊗ L.{k} ⟶ L.{k} := CartesianMonoidalCategory.snd K.{k} L.{k}
  let e : SSet.toTop.obj L.{k} ≅ TopCat.I.{k} := SSet.stdSimplex.toTopObjIsoI.{k}
  have hPrism : a ≫ b = SSet.stdSimplex.δ (1 : Fin 2) :=
    (SSet.ι₀_snd K.{k}).trans SSet.stdSimplex.δ_one_eq_const.symm
  have hMap : SSet.toTop.map a ≫ (SSet.toTop.map b ≫ e.hom) =
      SSet.toTop.map (SSet.stdSimplex.δ (1 : Fin 2)) ≫ e.hom :=
    (Category.assoc (SSet.toTop.map a) (SSet.toTop.map b) e.hom).symm.trans
      (congrArg (fun f : SSet.toTop.obj K.{k} ⟶ SSet.toTop.obj L.{k} => f ≫ e.hom)
        ((SSet.toTop.map_comp a b).symm.trans
          (congrArg (fun f : K.{k} ⟶ L.{k} => SSet.toTop.map f) hPrism)))
  apply TopCat.ext
  intro z
  have hz : z = (default : SSet.toTop.obj K.{k}) := Subsingleton.elim _ _
  have hInterval : e.hom (SSet.toTop.map (SSet.stdSimplex.δ (1 : Fin 2))
        (default : SSet.toTop.obj K.{k})) =
      (0 : TopCat.I.{k}) :=
    (congrArg (fun x : SSet.toTop.obj L.{k} => e.hom x) SSet.toTopObjIsoI_inv_zero.{k}.symm).trans
      (ConcreteCategory.congr_hom e.inv_hom_id (0 : TopCat.I.{k}))
  exact (ConcreteCategory.congr_hom hMap z).trans
    ((congrArg (fun x : SSet.toTop.obj K.{k} =>
        e.hom (SSet.toTop.map (SSet.stdSimplex.δ (1 : Fin 2)) x)) hz).trans hInterval)

private theorem coordinate_one :
    ((P.{k}).i₁ : SSet.toTop.obj K.{k} ⟶ (P.{k}).I) ≫ intervalCoordinate.{k} =
      TopCat.const (X := SSet.toTop.obj K.{k}) (1 : TopCat.I.{k}) := by
  let a : K.{k} ⟶ K.{k} ⊗ L.{k} := SSet.ι₁
  let b : K.{k} ⊗ L.{k} ⟶ L.{k} := CartesianMonoidalCategory.snd K.{k} L.{k}
  let e : SSet.toTop.obj L.{k} ≅ TopCat.I.{k} := SSet.stdSimplex.toTopObjIsoI.{k}
  have hPrism : a ≫ b = SSet.stdSimplex.δ (0 : Fin 2) :=
    (SSet.ι₁_snd K.{k}).trans SSet.stdSimplex.δ_zero_eq_const.symm
  have hMap : SSet.toTop.map a ≫ (SSet.toTop.map b ≫ e.hom) =
      SSet.toTop.map (SSet.stdSimplex.δ (0 : Fin 2)) ≫ e.hom :=
    (Category.assoc (SSet.toTop.map a) (SSet.toTop.map b) e.hom).symm.trans
      (congrArg (fun f : SSet.toTop.obj K.{k} ⟶ SSet.toTop.obj L.{k} => f ≫ e.hom)
        ((SSet.toTop.map_comp a b).symm.trans
          (congrArg (fun f : K.{k} ⟶ L.{k} => SSet.toTop.map f) hPrism)))
  apply TopCat.ext
  intro z
  have hz : z = (default : SSet.toTop.obj K.{k}) := Subsingleton.elim _ _
  have hInterval : e.hom (SSet.toTop.map (SSet.stdSimplex.δ (0 : Fin 2))
        (default : SSet.toTop.obj K.{k})) =
      (1 : TopCat.I.{k}) :=
    (congrArg (fun x : SSet.toTop.obj L.{k} => e.hom x) SSet.toTopObjIsoI_inv_one.{k}.symm).trans
      (ConcreteCategory.congr_hom e.inv_hom_id (1 : TopCat.I.{k}))
  exact (ConcreteCategory.congr_hom hMap z).trans
    ((congrArg (fun x : SSet.toTop.obj K.{k} =>
        e.hom (SSet.toTop.map (SSet.stdSimplex.δ (0 : Fin 2)) x)) hz).trans hInterval)

private theorem native_endpoints_distinct :
    (P.{k}).i₀ (default : SSet.toTop.obj K.{k}) ≠
      (P.{k}).i₁ (default : SSet.toTop.obj K.{k}) := by
  have h₀ : intervalCoordinate.{k} ((P.{k}).i₀ (default : SSet.toTop.obj K.{k})) = 0 :=
    ConcreteCategory.congr_hom coordinate_zero.{k} (default : SSet.toTop.obj K.{k})
  have h₁ : intervalCoordinate.{k} ((P.{k}).i₁ (default : SSet.toTop.obj K.{k})) = 1 :=
    ConcreteCategory.congr_hom coordinate_one.{k} (default : SSet.toTop.obj K.{k})
  intro h
  have hI : (0 : TopCat.I.{k}) = 1 :=
    h₀.symm.trans ((congrArg intervalCoordinate.{k} h).trans h₁)
  have hReal : (0 : ℝ) = 1 :=
    congrArg (fun t : TopCat.I.{k} => (TopCat.I.homeomorph t : ℝ)) hI
  exact (zero_ne_one : (0 : ℝ) ≠ 1) hReal

/-!
Case 1: the actual Δ[0] cylinder has distinct native endpoint points.
This catches collapsing the endpoint coproduct, rather than merely checking
the IsGood field of a reconstructed cylinder record.
-/
theorem cylinder_endpoints_distinct :
    let K₀ : SSet.{k} := Δ[0]
    let Q : Cylinder (SSet.toTop.obj K₀) :=
      SSet.RealizationCWUpgrade.realizedStandardCylinder.{k} K₀
    Q.i₀ (default : SSet.toTop.obj K₀) ≠ Q.i₁ (default : SSet.toTop.obj K₀) := by
  exact native_endpoints_distinct.{k}

/-!
Case 2: the public continuous-cylinder bridge maps the actual two ends to
different interval values in their correct order. Both endpoint equations
are derived from the original simplicial projections and interval Iso.
-/
theorem continuous_cylinder_endpoint_order :
    let K₀ : SSet.{k} := Δ[0]
    let h : SSet.toTop.obj (K₀ ⊗ (Δ[1] : SSet.{k})) ⟶ TopCat.I.{k} :=
      SSet.toTop.map (CartesianMonoidalCategory.snd K₀ (Δ[1] : SSet.{k})) ≫
        SSet.stdSimplex.toTopObjIsoI.{k}.hom
    ∃ (h₀ : SSet.toTop.map (SSet.ι₀ : K₀ ⟶ K₀ ⊗ (Δ[1] : SSet.{k})) ≫ h =
          TopCat.const (X := SSet.toTop.obj K₀) (0 : TopCat.I.{k}))
      (h₁ : SSet.toTop.map (SSet.ι₁ : K₀ ⟶ K₀ ⊗ (Δ[1] : SSet.{k})) ≫ h =
          TopCat.const (X := SSet.toTop.obj K₀) (1 : TopCat.I.{k})),
      let H := SSet.RealizationCWUpgrade.continuousHomotopyOfCylinderMap.{k} h h₀ h₁
      H (0, (default : SSet.toTop.obj K₀)) = 0 ∧
        H (1, (default : SSet.toTop.obj K₀)) = 1 ∧
        H (0, (default : SSet.toTop.obj K₀)) ≠ H (1, (default : SSet.toTop.obj K₀)) := by
  refine ⟨coordinate_zero.{k}, coordinate_one.{k}, ?_⟩
  let H : TopCat.Homotopy
      (TopCat.const (X := SSet.toTop.obj K.{k}) (0 : TopCat.I.{k}))
      (TopCat.const (X := SSet.toTop.obj K.{k}) (1 : TopCat.I.{k})) :=
    SSet.RealizationCWUpgrade.continuousHomotopyOfCylinderMap.{k}
    intervalCoordinate.{k} coordinate_zero.{k} coordinate_one.{k}
  let x₀ : SSet.toTop.obj K.{k} := default
  have h₀ : H (0, x₀) = (0 : TopCat.I.{k}) := H.map_zero_left x₀
  have h₁ : H (1, x₀) = (1 : TopCat.I.{k}) := H.map_one_left x₀
  refine ⟨h₀, h₁, ?_⟩
  intro heq
  have hI : (0 : TopCat.I.{k}) = 1 := h₀.symm.trans (heq.trans h₁)
  have hReal : (0 : ℝ) = 1 :=
    congrArg (fun t : TopCat.I.{k} => (TopCat.I.homeomorph t : ℝ)) hI
  exact (zero_ne_one : (0 : ℝ) ≠ 1) hReal

/-!
Case 3: a model left homotopy built on that very cylinder is interpreted
as a genuine continuous homotopy. Fibrancy is derived by the public adapter.
-/
theorem model_relation_continuous_endpoints :
    let K₀ : SSet.{k} := Δ[0]
    let f : SSet.toTop.obj K₀ ⟶ TopCat.I.{k} := TopCat.const 0
    let g : SSet.toTop.obj K₀ ⟶ TopCat.I.{k} := TopCat.const 1
    ∃ rel : LeftHomotopyRel f g,
      let H := @SSet.RealizationCWUpgrade.continuousHomotopyOfLeftHomotopy.{k}
        K₀ TopCat.I.{k}
        (SSet.RealizationCWUpgrade.allTopCatObjectsFibrant.{k} TopCat.I.{k}) f g rel
      H (0, (default : SSet.toTop.obj K₀)) = 0 ∧
        H (1, (default : SSet.toTop.obj K₀)) = 1 := by
  let f : SSet.toTop.obj K.{k} ⟶ TopCat.I.{k} := TopCat.const 0
  let g : SSet.toTop.obj K.{k} ⟶ TopCat.I.{k} := TopCat.const 1
  let raw : (P.{k}).LeftHomotopy f g :=
    { h := intervalCoordinate.{k}
      h₀ := coordinate_zero.{k}
      h₁ := coordinate_one.{k} }
  let rel : LeftHomotopyRel f g := raw.leftHomotopyRel
  refine ⟨rel, ?_⟩
  let H := @SSet.RealizationCWUpgrade.continuousHomotopyOfLeftHomotopy.{k}
    K.{k} TopCat.I.{k}
    (SSet.RealizationCWUpgrade.allTopCatObjectsFibrant.{k} TopCat.I.{k}) f g rel
  let x₀ : SSet.toTop.obj K.{k} := default
  exact ⟨H.map_zero_left x₀, H.map_one_left x₀⟩

/-!
Case 4: Whitehead is applied to the genuine zero-endpoint inclusion. Its
weakness is derived from the cylinder projection and the actual section law.
The forward map must land at 0, not the other endpoint or an arbitrary point.
-/
theorem whitehead_literal_forward_endpoint :
    let K₀ : SSet.{k} := Δ[0]
    let Q : Cylinder K₀ := SSet.modelCategoryQuillen.standardCylinder.{k} K₀
    let f : K₀ ⟶ Q.I := Q.i₀
    ∃ hf : SSet.realizationWeakEquivalences f,
      let E : ContinuousMap.HomotopyEquiv (SSet.toTop.obj K₀) (SSet.toTop.obj Q.I) :=
        SSet.RealizationCWUpgrade.realizationHomotopyEquiv.{k} f hf
      E.toFun = (SSet.toTop.map f).hom ∧
        (SSet.toTop.map (CartesianMonoidalCategory.snd K₀ (Δ[1] : SSet.{k})) ≫
          SSet.stdSimplex.toTopObjIsoI.{k}.hom) (E.toFun (default : SSet.toTop.obj K₀)) = 0 ∧
        E.toFun (default : SSet.toTop.obj K₀) ≠
          SSet.toTop.map Q.i₁ (default : SSet.toTop.obj K₀) := by
  let Q : Cylinder K.{k} := SSet.modelCategoryQuillen.standardCylinder.{k} K.{k}
  let f : K.{k} ⟶ Q.I := Q.i₀
  have hπ : WeakEquivalence Q.π := Q.weakEquivalence_π
  have hId : WeakEquivalence (𝟙 K.{k}) := inferInstance
  have hSection : f ≫ Q.π = 𝟙 K.{k} := Q.toPrecylinder.i₀_π
  have hWeak : WeakEquivalence f :=
    @HomotopicalAlgebra.weakEquivalence_of_postcomp_of_fac
      SSet.{k} _ _ _ K.{k} Q.I K.{k} f Q.π (𝟙 K.{k}) hSection hπ hId
  have hf : SSet.realizationWeakEquivalences f :=
    (weakEquivalence_iff (f := f)).mp hWeak
  let E : ContinuousMap.HomotopyEquiv (SSet.toTop.obj K.{k}) (SSet.toTop.obj Q.I) :=
    SSet.RealizationCWUpgrade.realizationHomotopyEquiv.{k} f hf
  have hForward : E.toFun = (SSet.toTop.map f).hom :=
    SSet.RealizationCWUpgrade.realizationHomotopyEquiv_toFun.{k} f hf
  let x₀ : SSet.toTop.obj K.{k} := default
  have hAtPoint : E.toFun x₀ = (SSet.toTop.map f).hom x₀ :=
    DFunLike.congr_fun hForward x₀
  refine ⟨hf, hForward, ?_, ?_⟩
  · exact (congrArg intervalCoordinate.{k} hAtPoint).trans
      (ConcreteCategory.congr_hom coordinate_zero.{k} x₀)
  · intro heq
    exact native_endpoints_distinct.{k} (hAtPoint.symm.trans heq)

/-- The original zero-simplex cylinder has a contractible realization and
literal conull weak map while its native endpoint points remain distinct. -/
theorem contractible_cylinder_has_literal_conull_map :
    let K₀ : SSet.{k} := Δ[0]
    let Q : Cylinder K₀ := SSet.modelCategoryQuillen.standardCylinder.{k} K₀
    SSet.realizationWeakEquivalences (terminal.from Q.I) ∧
      SSet.toTop.map Q.i₀ (default : SSet.toTop.obj K₀) ≠
        SSet.toTop.map Q.i₁ (default : SSet.toTop.obj K₀) := by
  dsimp only
  let K₀ : SSet.{k} := Δ[0]
  let Q : Cylinder K₀ := SSet.modelCategoryQuillen.standardCylinder.{k} K₀
  have hAffine : ContractibleSpace (Convexity.StdSimplex ℝ (Fin 1)) := inferInstance
  have hZero : ContractibleSpace (SSet.toTop.obj K₀) :=
    @Homeomorph.contractibleSpace _ _ _ _ hAffine (SimplexCategory.toTopHomeo ⦋0⦌)
  have hProjection : SSet.realizationWeakEquivalences Q.π :=
    (weakEquivalence_iff (f := Q.π)).mp Q.weakEquivalence_π
  let e : ContinuousMap.HomotopyEquiv (SSet.toTop.obj Q.I) (SSet.toTop.obj K₀) :=
    SSet.RealizationCWUpgrade.realizationHomotopyEquiv.{k} Q.π hProjection
  have hCylinder : ContractibleSpace (SSet.toTop.obj Q.I) :=
    @ContinuousMap.HomotopyEquiv.contractibleSpace _ _ _ _ hZero e
  have hWeak : SSet.realizationWeakEquivalences (terminal.from Q.I) :=
    @SSet.RealizationCWUpgrade.conull_mem_of_contractible.{k} Q.I hCylinder
  refine ⟨hWeak, ?_⟩
  exact native_endpoints_distinct.{k}

end CanonicalContinuousWhiteheadConsumers

end
