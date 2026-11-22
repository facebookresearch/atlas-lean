/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalCorePathObject
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalMappingComposition
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalMappingOperatorEquivalences
import MathlibExt.AlgebraicTopology.SimplicialSpace.EquivalenceFibreHomTransport
import MathlibExt.AlgebraicTopology.SimplicialSpace.RowRestriction
import MathlibExt.AlgebraicTopology.SimplicialSet.CoherentIso

/-!
# Original walking-groupoid prisms on Segal mapping fibres

External, uncompiled proof terms. The ordinary categorical homotopy is
written in the E × U order of the existing external tensor. The primary
U × E convention is obtained by the actual product symmetry. Neither an
equivalence-fibre point nor a Dwyer--Kan outcome is supplied by the caller.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory HomotopicalAlgebra
open CategoryTheory.SimplicialObject
open scoped Simplicial SSet.modelCategoryQuillen SimplicialSpace.Inner

namespace SimplicialSpace.CategoricalHomotopyPrism
open SegalHomotopy

private theorem constAtZero {A B : SSet.{u}} (a : A _⦋0⦌) (b : B _⦋0⦌) :
    (SSet.const (X := A) b).app (op ⦋0⦌) a = b := by
  have h : SimplexCategory.const ⦋0⦌ ⦋0⦌ (0 : Fin 1) = 𝟙 ⦋0⦌ := by decide
  change B.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ (0 : Fin 1)).op b = b
  rw [h, op_id, CategoryTheory.Functor.map_id, CategoryTheory.id_apply]

/-- The actual endpoint insertion into the original E-indexed external tensor. -/
def tensorEndpoint (U : SimplicialSpace.{u}) (e : SSet.coherentIso.{u} _⦋0⦌) :
    U.diagram ⟶ (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj U.diagram where
  app m := SSet.simplicialSpaceTensorι SSet.coherentIso U.diagram m
    (SSet.coherentIso.map (m.unop.const ⦋0⦌ (0 : Fin 1)).op e)
  naturality {m n} α := by
    rw [SSet.simplicialSpaceTensorι_outer]
    congr 1

/-- A categorical homotopy at the SAME original object gives an actual row-zero E-map. -/
def rowAtVertex {U V : SimplicialSpace.{u}}
    (H : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj U.diagram ⟶ V.diagram)
    (x : (U.diagram _⦋0⦌) _⦋0⦌) :
    SSet.coherentIso.{u} ⟶ (rowFunctor 0).obj V where
  app m := ↾fun e => (H.app m).app (op ⦋0⦌)
    (e, (U.diagram.map (m.unop.const ⦋0⦌ (0 : Fin 1)).op).app (op ⦋0⦌) x)
  naturality {m n} α := by
    ext e
    have hx : U.diagram.map (m.unop.const ⦋0⦌ (0 : Fin 1)).op ≫ U.diagram.map α =
        U.diagram.map (n.unop.const ⦋0⦌ (0 : Fin 1)).op := by
      rw [← CategoryTheory.Functor.map_comp]
      congr 1
    have h := congrArg (fun k => k.app (op ⦋0⦌)
      (e, (U.diagram.map (m.unop.const ⦋0⦌ (0 : Fin 1)).op).app (op ⦋0⦌) x))
      (H.naturality α)
    have hx0 := congrArg (fun k => k.app (op ⦋0⦌) x) hx
    change (H.app n).app (op ⦋0⦌)
        (SSet.coherentIso.map α e, (U.diagram.map α).app (op ⦋0⦌)
          ((U.diagram.map (m.unop.const ⦋0⦌ (0 : Fin 1)).op).app (op ⦋0⦌) x)) =
      (V.diagram.map α).app (op ⦋0⦌) ((H.app m).app (op ⦋0⦌)
        (e, (U.diagram.map (m.unop.const ⦋0⦌ (0 : Fin 1)).op).app (op ⦋0⦌) x)) at h
    change (U.diagram.map α).app (op ⦋0⦌)
      ((U.diagram.map (m.unop.const ⦋0⦌ (0 : Fin 1)).op).app (op ⦋0⦌) x) =
        (U.diagram.map (n.unop.const ⦋0⦌ (0 : Fin 1)).op).app (op ⦋0⦌) x at hx0
    rw [hx0] at h
    exact h

/-- Both endpoint identities are derived from the original two tensor equations. -/
theorem rowAtVertex_endpoints {U V : SimplicialSpace.{u}} (f₀ f₁ : U ⟶ V)
    (H : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj U.diagram ⟶ V.diagram)
    (h₀ : tensorEndpoint U SSet.coherentIso.x₀ ≫ H = f₀.hom)
    (h₁ : tensorEndpoint U SSet.coherentIso.x₁ ≫ H = f₁.hom)
    (x : (U.diagram _⦋0⦌) _⦋0⦌) :
    (rowAtVertex H x).app (op ⦋0⦌) SSet.coherentIso.x₀ = mappingVertexMap f₀ x ∧
    (rowAtVertex H x).app (op ⦋0⦌) SSet.coherentIso.x₁ = mappingVertexMap f₁ x := by
  have he : SimplexCategory.const ⦋0⦌ ⦋0⦌ (0 : Fin 1) = 𝟙 ⦋0⦌ := by decide
  have hx : (U.diagram.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ (0 : Fin 1)).op).app (op ⦋0⦌) x = x := by
    have h := constAtZero (B := (rowFunctor 0).obj U) SSet.coherentIso.x₀ x
    change (U.diagram.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ (0 : Fin 1)).op).app (op ⦋0⦌) x = x at h
    exact h
  constructor
  · have h := congrArg (fun k => (k.app (op ⦋0⦌)).app (op ⦋0⦌) x) h₀
    change (H.app (op ⦋0⦌)).app (op ⦋0⦌)
      (SSet.coherentIso.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ (0 : Fin 1)).op
        SSet.coherentIso.x₀, x) = mappingVertexMap f₀ x at h
    rw [he, op_id, CategoryTheory.Functor.map_id, CategoryTheory.id_apply] at h
    change (H.app (op ⦋0⦌)).app (op ⦋0⦌)
      (SSet.coherentIso.x₀,
          (U.diagram.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ (0 : Fin 1)).op).app
          (op ⦋0⦌) x) = _
    rw [hx]
    exact h
  · have h := congrArg (fun k => (k.app (op ⦋0⦌)).app (op ⦋0⦌) x) h₁
    change (H.app (op ⦋0⦌)).app (op ⦋0⦌)
      (SSet.coherentIso.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ (0 : Fin 1)).op
        SSet.coherentIso.x₁, x) = mappingVertexMap f₁ x at h
    rw [he, op_id, CategoryTheory.Functor.map_id, CategoryTheory.id_apply] at h
    change (H.app (op ⦋0⦌)).app (op ⦋0⦌)
      (SSet.coherentIso.x₁,
          (U.diagram.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ (0 : Fin 1)).op).app
          (op ⦋0⦌) x) = _
    rw [hx]
    exact h

private def inversePattern : SSet.coherentIso.{u} _⦋3⦌ :=
  ComposableArrows.mk₃ WalkingIso.iso.inv WalkingIso.iso.hom WalkingIso.iso.inv

private theorem inversePattern_first :
    SSet.coherentIso.map (SimplexCategory.mkOfLe (0 : Fin 4) 2 (by decide)).op
      inversePattern = SSet.coherentIso.σ (0 : Fin 1) SSet.coherentIso.x₁ := by
  apply SSet.coherentIso.eq_of_forall_vertexBool_eq
  intro i
  fin_cases i <;> rfl

private theorem inversePattern_middle :
    SSet.coherentIso.map (SimplexCategory.mkOfLe (1 : Fin 4) 2 (by decide)).op
      inversePattern = SSet.coherentIso.hom.edge := by
  apply SSet.coherentIso.eq_of_forall_vertexBool_eq
  intro i
  fin_cases i <;> rfl

private theorem inversePattern_last :
    SSet.coherentIso.map (SimplexCategory.mkOfLe (1 : Fin 4) 3 (by decide)).op
      inversePattern = SSet.coherentIso.σ (0 : Fin 1) SSet.coherentIso.x₀ := by
  apply SSet.coherentIso.eq_of_forall_vertexBool_eq
  intro i
  fin_cases i <;> rfl

private theorem inverseVertex_ext (V : SimplicialSpace.{u})
    {a b : (inverseEdgeLimit V) _⦋0⦌}
    (h₀ : (inverseFirst V).app (op ⦋0⦌) a = (inverseFirst V).app (op ⦋0⦌) b)
    (h₁ : (inverseMiddle V).app (op ⦋0⦌) a = (inverseMiddle V).app (op ⦋0⦌) b)
    (h₂ : (inverseLast V).app (op ⦋0⦌) a = (inverseLast V).app (op ⦋0⦌) b) : a = b := by
  apply SSet.yonedaEquiv.symm.injective
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · change SSet.yonedaEquiv.symm a ≫ inverseFirst V = SSet.yonedaEquiv.symm b ≫ inverseFirst V
      rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, h₀]
    · change SSet.yonedaEquiv.symm a ≫ inverseMiddle V = SSet.yonedaEquiv.symm b ≫ inverseMiddle V
      rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, h₁]
  · change SSet.yonedaEquiv.symm a ≫ inverseLast V = SSet.yonedaEquiv.symm b ≫ inverseLast V
    rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, h₂]

/-- The literal 1010 simplex supplies the actual 02/12/13 inverse test, without RF of D(E). -/
theorem rowE_hasInverseData (V : SimplicialSpace.{u})
    (q : SSet.coherentIso.{u} ⟶ (rowFunctor 0).obj V) :
    HasInverseData V (q.app (op ⦋1⦌) SSet.coherentIso.hom.edge) := by
  let t : (V.diagram _⦋3⦌) _⦋0⦌ := q.app (op ⦋3⦌) inversePattern
  let g : (V.diagram _⦋1⦌) _⦋0⦌ := q.app (op ⦋1⦌) SSet.coherentIso.hom.edge
  refine ⟨t, inverseVertex_ext V ?_ ?_ ?_⟩
  · have ht := congrArg (fun k => k.app (op ⦋0⦌) t) (inverseRestriction_first V)
    have hi := congrArg (fun k => k.app (op ⦋0⦌) g) (identityTriple_first V)
    have hq := q.naturality_apply (SimplexCategory.mkOfLe (0 : Fin 4) 2 (by decide)).op
        inversePattern
    rw [inversePattern_first] at hq
    have hs := q.naturality_apply (SimplexCategory.σ (0 : Fin 1)).op SSet.coherentIso.x₁
    have he := q.naturality_apply (SimplexCategory.δ (0 : Fin 2)).op SSet.coherentIso.hom.edge
    change q.app (op ⦋0⦌) (SSet.coherentIso.δ (0 : Fin 2) SSet.coherentIso.hom.edge) =
      (V.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g at he
    rw [SSet.coherentIso.hom.tgt_eq] at he
    exact ht.trans (hq.symm.trans (hs.trans
      ((congrArg ((V.diagram.σ (0 : Fin 1)).app (op ⦋0⦌)) he).trans hi.symm)))
  · have ht := congrArg (fun k => k.app (op ⦋0⦌) t) (inverseRestriction_middle V)
    have hi := congrArg (fun k => k.app (op ⦋0⦌) g) (identityTriple_middle V)
    have hq := q.naturality_apply (SimplexCategory.mkOfLe (1 : Fin 4) 2 (by decide)).op
        inversePattern
    rw [inversePattern_middle] at hq
    exact ht.trans (hq.symm.trans hi.symm)
  · have ht := congrArg (fun k => k.app (op ⦋0⦌) t) (inverseRestriction_last V)
    have hi := congrArg (fun k => k.app (op ⦋0⦌) g) (identityTriple_last V)
    have hq := q.naturality_apply (SimplexCategory.mkOfLe (1 : Fin 4) 3 (by decide)).op
        inversePattern
    rw [inversePattern_last] at hq
    have hs := q.naturality_apply (SimplexCategory.σ (0 : Fin 1)).op SSet.coherentIso.x₀
    have he := q.naturality_apply (SimplexCategory.δ (1 : Fin 2)).op SSet.coherentIso.hom.edge
    change q.app (op ⦋0⦌) (SSet.coherentIso.δ (1 : Fin 2) SSet.coherentIso.hom.edge) =
      (V.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g at he
    rw [SSet.coherentIso.hom.src_eq] at he
    exact ht.trans (hq.symm.trans (hs.trans
      ((congrArg ((V.diagram.σ (0 : Fin 1)).app (op ⦋0⦌)) he).trans hi.symm)))

/-- The original E-map yields a point of the actual equivalence fibre, with both endpoint labels. -/
def rowEEquivalenceFibrePoint (V : SimplicialSpace.{u}) (hV : segalSpaces V)
    (q : SSet.coherentIso.{u} ⟶ (rowFunctor 0).obj V)
    (x y : (V.diagram _⦋0⦌) _⦋0⦌)
    (hx : q.app (op ⦋0⦌) SSet.coherentIso.x₀ = x)
    (hy : q.app (op ⦋0⦌) SSet.coherentIso.x₁ = y) :
    (equivalenceFibre V hV x y) _⦋0⦌ := by
  let g : (V.diagram _⦋1⦌) _⦋0⦌ := q.app (op ⦋1⦌) SSet.coherentIso.hom.edge
  have hg : g ∈ (equivalenceSubcomplex V hV).obj (op ⦋0⦌) :=
    (mem_equivalenceSubcomplex_zero V hV g).mpr
      (isEquivalenceEdge_of_hasInverseData V hV g (rowE_hasInverseData V q))
  refine SSet.yonedaEquiv (pullback.lift
    (SSet.yonedaEquiv.symm (show (equivalenceSubcomplex V hV : SSet.{u}) _⦋0⦌ from ⟨g, hg⟩))
    (𝟙 (Δ[0] : SSet.{u})) ?_)
  apply prod.hom_ext
  · simp only [coreEndpoint, Category.assoc, prod.lift_fst, Category.id_comp,
      mappingPointPair_fst, equivalenceSource]
    rw [SSet.yonedaEquiv_symm_comp]
    congr 1
    change (V.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g = x
    have he := q.naturality_apply (SimplexCategory.δ (1 : Fin 2)).op SSet.coherentIso.hom.edge
    change q.app (op ⦋0⦌) (SSet.coherentIso.δ (1 : Fin 2) SSet.coherentIso.hom.edge) =
      (V.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g at he
    rw [SSet.coherentIso.hom.src_eq] at he
    exact he.symm.trans hx
  · simp only [coreEndpoint, Category.assoc, prod.lift_snd, Category.id_comp,
      mappingPointPair_snd, equivalenceTarget]
    rw [SSet.yonedaEquiv_symm_comp]
    congr 1
    change (V.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g = y
    have he := q.naturality_apply (SimplexCategory.δ (0 : Fin 2)).op SSet.coherentIso.hom.edge
    change q.app (op ⦋0⦌) (SSet.coherentIso.δ (0 : Fin 2) SSet.coherentIso.hom.edge) =
      (V.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g at he
    rw [SSet.coherentIso.hom.tgt_eq] at he
    exact he.symm.trans hy

/-- The actual EF point retains the whole original forward edge and the Delta-zero projection. -/
theorem rowEEquivalenceFibrePoint_laws (V : SimplicialSpace.{u}) (hV : segalSpaces V)
    (q : SSet.coherentIso.{u} ⟶ (rowFunctor 0).obj V)
    (x y : (V.diagram _⦋0⦌) _⦋0⦌)
    (hx : q.app (op ⦋0⦌) SSet.coherentIso.x₀ = x)
    (hy : q.app (op ⦋0⦌) SSet.coherentIso.x₁ = y) :
    let η := rowEEquivalenceFibrePoint V hV q x y hx hy
    SSet.yonedaEquiv.symm η ≫ pullback.fst (coreEndpoint V hV) (mappingPointPair V x y) ≫
      (equivalenceSubcomplex V hV).ι =
        (SSet.yonedaEquiv (X := V.diagram _⦋1⦌) (n := ⦋0⦌)).symm
          (q.app (op ⦋1⦌) SSet.coherentIso.hom.edge) ∧
    SSet.yonedaEquiv.symm η ≫ equivalenceFibreToMappingFibre V hV x y ≫ mappingFibre.fst V x y =
        (SSet.yonedaEquiv (X := V.diagram _⦋1⦌) (n := ⦋0⦌)).symm
          (q.app (op ⦋1⦌) SSet.coherentIso.hom.edge) ∧
    SSet.yonedaEquiv.symm η ≫ equivalenceFibreToMappingFibre V hV x y ≫ mappingFibre.snd V x y =
        𝟙 (Δ[0] : SSet.{u}) := by
  have hf : equivalenceFibreToMappingFibre V hV x y ≫ mappingFibre.fst V x y =
      pullback.fst (coreEndpoint V hV) (mappingPointPair V x y) ≫
        (equivalenceSubcomplex V hV).ι := pullback.lift_fst _ _ _
  have hs : equivalenceFibreToMappingFibre V hV x y ≫ mappingFibre.snd V x y =
      pullback.snd (coreEndpoint V hV) (mappingPointPair V x y) := pullback.lift_snd _ _ _
  dsimp only [rowEEquivalenceFibrePoint]
  simp only [Equiv.symm_apply_apply]
  refine ⟨?_, ?_, ?_⟩
  · rw [pullback.lift_fst_assoc, SSet.yonedaEquiv_symm_comp]
    rfl
  · rw [hf, pullback.lift_fst_assoc, SSet.yonedaEquiv_symm_comp]
    rfl
  · rw [hs, pullback.lift_snd]

/-- A categorical homotopy supplies the actual original f-zero-to-f-one equivalence point. -/
def homotopyEquivalencePoint {U V : SimplicialSpace.{u}} (f₀ f₁ : U ⟶ V)
    (hV : segalSpaces V)
    (H : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj U.diagram ⟶ V.diagram)
    (h₀ : tensorEndpoint U SSet.coherentIso.x₀ ≫ H = f₀.hom)
    (h₁ : tensorEndpoint U SSet.coherentIso.x₁ ≫ H = f₁.hom)
    (x : (U.diagram _⦋0⦌) _⦋0⦌) :
    (equivalenceFibre V hV (mappingVertexMap f₀ x) (mappingVertexMap f₁ x)) _⦋0⦌ :=
  rowEEquivalenceFibrePoint V hV (rowAtVertex H x) _ _
    (rowAtVertex_endpoints f₀ f₁ H h₀ h₁ x).1 (rowAtVertex_endpoints f₀ f₁ H h₀ h₁ x).2

/-- The original forward H-edge at x, as a full scalar map rather than a selected component. -/
def etaEdgeArrow {U V : SimplicialSpace.{u}}
    (H : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj U.diagram ⟶ V.diagram)
    (x : (U.diagram _⦋0⦌) _⦋0⦌) : (Δ[0] : SSet.{u}) ⟶ V.diagram _⦋1⦌ :=
  SSet.yonedaEquiv.symm x ≫ U.diagram.σ (0 : Fin 1) ≫
    SSet.simplicialSpaceTensorι SSet.coherentIso U.diagram (op ⦋1⦌) SSet.coherentIso.hom.edge ≫
    H.app (op ⦋1⦌)

private theorem etaEdgeArrow_zero {U V : SimplicialSpace.{u}}
    (H : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj U.diagram ⟶ V.diagram)
    (x : (U.diagram _⦋0⦌) _⦋0⦌) :
    SSet.yonedaEquiv (etaEdgeArrow H x) =
      (rowAtVertex H x).app (op ⦋1⦌) SSet.coherentIso.hom.edge := by
  dsimp only [etaEdgeArrow]
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  have h : SimplexCategory.const ⦋1⦌ ⦋0⦌ (0 : Fin 1) = SimplexCategory.σ (0 : Fin 1) := by decide
  change (H.app (op ⦋1⦌)).app (op ⦋0⦌)
    (SSet.coherentIso.hom.edge, (U.diagram.σ (0 : Fin 1)).app (op ⦋0⦌) x) = _
  change _ = (H.app (op ⦋1⦌)).app (op ⦋0⦌)
    (SSet.coherentIso.hom.edge,
      (U.diagram.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ (0 : Fin 1)).op).app (op ⦋0⦌) x)
  rw [h]
  rfl

/-- Both actual fibre projection legs of the constructed homotopy point retain H's full edge. -/
theorem homotopyEquivalencePoint_laws {U V : SimplicialSpace.{u}} (f₀ f₁ : U ⟶ V)
    (hV : segalSpaces V)
    (H : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj U.diagram ⟶ V.diagram)
    (h₀ : tensorEndpoint U SSet.coherentIso.x₀ ≫ H = f₀.hom)
    (h₁ : tensorEndpoint U SSet.coherentIso.x₁ ≫ H = f₁.hom)
    (x : (U.diagram _⦋0⦌) _⦋0⦌) :
    let a := (equivalenceFibreToMappingFibre V hV (mappingVertexMap f₀ x)
      (mappingVertexMap f₁ x)).app (op ⦋0⦌) (homotopyEquivalencePoint f₀ f₁ hV H h₀ h₁ x)
    SSet.yonedaEquiv.symm a ≫ mappingFibre.fst V (mappingVertexMap f₀ x) (mappingVertexMap f₁ x) =
      etaEdgeArrow H x ∧
    SSet.yonedaEquiv.symm a ≫ mappingFibre.snd V (mappingVertexMap f₀ x) (mappingVertexMap f₁ x) =
      𝟙 (Δ[0] : SSet.{u}) := by
  have h := rowEEquivalenceFibrePoint_laws V hV (rowAtVertex H x)
    (mappingVertexMap f₀ x) (mappingVertexMap f₁ x)
    (rowAtVertex_endpoints f₀ f₁ H h₀ h₁ x).1 (rowAtVertex_endpoints f₀ f₁ H h₀ h₁ x).2
  dsimp only [homotopyEquivalencePoint] at ⊢
  simp only [SSet.yonedaEquiv_symm_comp] at h ⊢
  refine ⟨h.2.1.trans ?_, h.2.2⟩
  exact congrArg (fun z => (SSet.yonedaEquiv (X := V.diagram _⦋1⦌) (n := ⦋0⦌)).symm z)
    (etaEdgeArrow_zero H x).symm |>.trans (Equiv.symm_apply_apply _ _)

/-- The 001 simplex used with the original source-side degeneracy σ-one. -/
def sourcePattern : SSet.coherentIso.{u} _⦋2⦌ :=
  ComposableArrows.mk₂ (𝟙 WalkingIso.zero) WalkingIso.iso.hom

/-- The complementary 011 simplex used with the original target-side degeneracy σ-zero. -/
def targetPattern : SSet.coherentIso.{u} _⦋2⦌ :=
  ComposableArrows.mk₂ WalkingIso.iso.hom (𝟙 WalkingIso.one)

private theorem pattern_faces :
    SSet.coherentIso.δ (2 : Fin 3) sourcePattern.{u} =
        SSet.coherentIso.σ (0 : Fin 1) SSet.coherentIso.x₀ ∧
    SSet.coherentIso.δ (0 : Fin 3) sourcePattern.{u} = SSet.coherentIso.hom.edge ∧
    SSet.coherentIso.δ (1 : Fin 3) sourcePattern.{u} = SSet.coherentIso.hom.edge ∧
    SSet.coherentIso.δ (2 : Fin 3) targetPattern.{u} = SSet.coherentIso.hom.edge ∧
    SSet.coherentIso.δ (0 : Fin 3) targetPattern.{u} =
        SSet.coherentIso.σ (0 : Fin 1) SSet.coherentIso.x₁ ∧
    SSet.coherentIso.δ (1 : Fin 3) targetPattern.{u} = SSet.coherentIso.hom.edge := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    apply SSet.coherentIso.eq_of_forall_vertexBool_eq <;>
    intro i <;> fin_cases i <;> rfl

private theorem tensorH_operator {U V : SimplicialSpace.{u}}
    (H : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj U.diagram ⟶ V.diagram)
    {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n) (e : SSet.coherentIso.obj m) :
    SSet.simplicialSpaceTensorι SSet.coherentIso U.diagram m e ≫ H.app m ≫ V.diagram.map α =
      U.diagram.map α ≫ SSet.simplicialSpaceTensorι SSet.coherentIso U.diagram n
        (SSet.coherentIso.map α e) ≫ H.app n := by
  rw [← H.naturality, ← Category.assoc, SSet.simplicialSpaceTensorι_outer, Category.assoc]

private theorem endpointH_zero {U V : SimplicialSpace.{u}} (f : U ⟶ V)
    (H : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj U.diagram ⟶ V.diagram)
    (e : SSet.coherentIso.{u} _⦋0⦌) (he : tensorEndpoint U e ≫ H = f.hom) :
    SSet.simplicialSpaceTensorι SSet.coherentIso U.diagram (op ⦋0⦌) e ≫ H.app (op ⦋0⦌) =
      f.hom.app (op ⦋0⦌) := by
  have h := NatTrans.congr_app he (op ⦋0⦌)
  have hc : SimplexCategory.const ⦋0⦌ ⦋0⦌ (0 : Fin 1) = 𝟙 ⦋0⦌ := by decide
  change SSet.simplicialSpaceTensorι SSet.coherentIso U.diagram (op ⦋0⦌)
    (SSet.coherentIso.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ (0 : Fin 1)).op e) ≫
      H.app (op ⦋0⦌) = _ at h
  simpa only [hc, op_id, CategoryTheory.Functor.map_id, CategoryTheory.id_apply] using h

private theorem endpointH_one {U V : SimplicialSpace.{u}} (f : U ⟶ V)
    (H : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj U.diagram ⟶ V.diagram)
    (e : SSet.coherentIso.{u} _⦋0⦌) (he : tensorEndpoint U e ≫ H = f.hom) :
    SSet.simplicialSpaceTensorι SSet.coherentIso U.diagram (op ⦋1⦌)
      (SSet.coherentIso.σ (0 : Fin 1) e) ≫ H.app (op ⦋1⦌) = f.hom.app (op ⦋1⦌) := by
  have h := NatTrans.congr_app he (op ⦋1⦌)
  have hc : SimplexCategory.const ⦋1⦌ ⦋0⦌ (0 : Fin 1) = SimplexCategory.σ (0 : Fin 1) := by decide
  change SSet.simplicialSpaceTensorι SSet.coherentIso U.diagram (op ⦋1⦌)
    (SSet.coherentIso.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ (0 : Fin 1)).op e) ≫
      H.app (op ⦋1⦌) = _ at h
  rw [hc] at h
  exact h

private theorem sourceDegeneracy_last (U : SimplicialSpace.{u}) :
    U.diagram.σ (1 : Fin 2) ≫ U.diagram.δ (0 : Fin 3) =
      U.diagram.δ (0 : Fin 2) ≫ U.diagram.σ (0 : Fin 1) := by
  exact U.diagram.δ_comp_σ_of_le (i := (0 : Fin 2)) (j := (0 : Fin 1)) (by decide)

private theorem targetDegeneracy_first (U : SimplicialSpace.{u}) :
    U.diagram.σ (0 : Fin 2) ≫ U.diagram.δ (2 : Fin 3) =
      U.diagram.δ (1 : Fin 2) ≫ U.diagram.σ (0 : Fin 1) := by
  exact U.diagram.δ_comp_σ_of_gt (i := (1 : Fin 2)) (j := (0 : Fin 1)) (by decide)

/-- The first whole triangle is H on (001, σ-one of the original edge). -/
def sourceTriangleEdge {U V : SimplicialSpace.{u}}
    (H : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj U.diagram ⟶ V.diagram)
    (x y : (U.diagram _⦋0⦌) _⦋0⦌) : mappingFibre U x y ⟶ V.diagram _⦋2⦌ :=
  mappingFibre.fst U x y ≫ U.diagram.σ (1 : Fin 2) ≫
    SSet.simplicialSpaceTensorι SSet.coherentIso U.diagram (op ⦋2⦌) sourcePattern ≫
      H.app (op ⦋2⦌)

/-- The complementary whole triangle is H on (011, σ-zero of the original edge). -/
def targetTriangleEdge {U V : SimplicialSpace.{u}}
    (H : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj U.diagram ⟶ V.diagram)
    (x y : (U.diagram _⦋0⦌) _⦋0⦌) : mappingFibre U x y ⟶ V.diagram _⦋2⦌ :=
  mappingFibre.fst U x y ≫ U.diagram.σ (0 : Fin 2) ≫
    SSet.simplicialSpaceTensorι SSet.coherentIso U.diagram (op ⦋2⦌) targetPattern ≫
      H.app (op ⦋2⦌)

/-- The SAME middle edge is H on the original edge paired with E's forward edge. -/
def middleEdge {U V : SimplicialSpace.{u}}
    (H : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj U.diagram ⟶ V.diagram)
    (x y : (U.diagram _⦋0⦌) _⦋0⦌) : mappingFibre U x y ⟶ V.diagram _⦋1⦌ :=
  mappingFibre.fst U x y ≫
    SSet.simplicialSpaceTensorι SSet.coherentIso U.diagram (op ⦋1⦌) SSet.coherentIso.hom.edge ≫
      H.app (op ⦋1⦌)

/-- All six original outer face equations, including the two identical middle faces. -/
theorem prismFaceEquations {U V : SimplicialSpace.{u}} (f₀ f₁ : U ⟶ V)
    (H : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj U.diagram ⟶ V.diagram)
    (h₀ : tensorEndpoint U SSet.coherentIso.x₀ ≫ H = f₀.hom)
    (h₁ : tensorEndpoint U SSet.coherentIso.x₁ ≫ H = f₁.hom)
    (x y : (U.diagram _⦋0⦌) _⦋0⦌) :
    sourceTriangleEdge H x y ≫ V.diagram.δ (2 : Fin 3) =
      mappingFibre.fst U x y ≫ f₀.hom.app (op ⦋1⦌) ∧
    sourceTriangleEdge H x y ≫ V.diagram.δ (0 : Fin 3) = mappingFibre.snd U x y ≫ etaEdgeArrow H y ∧
    sourceTriangleEdge H x y ≫ V.diagram.δ (1 : Fin 3) = middleEdge H x y ∧
    targetTriangleEdge H x y ≫ V.diagram.δ (2 : Fin 3) = mappingFibre.snd U x y ≫ etaEdgeArrow H x ∧
    targetTriangleEdge H x y ≫ V.diagram.δ (0 : Fin 3) =
      mappingFibre.fst U x y ≫ f₁.hom.app (op ⦋1⦌) ∧
    targetTriangleEdge H x y ≫ V.diagram.δ (1 : Fin 3) = middleEdge H x y := by
  have hd (i : Fin 3) (e : SSet.coherentIso.{u} _⦋2⦌) :
      SSet.simplicialSpaceTensorι SSet.coherentIso U.diagram (op ⦋2⦌) e ≫ H.app (op ⦋2⦌) ≫
          V.diagram.δ i = U.diagram.δ i ≫
        SSet.simplicialSpaceTensorι SSet.coherentIso U.diagram (op ⦋1⦌) (SSet.coherentIso.δ i e) ≫
          H.app (op ⦋1⦌) := tensorH_operator H (SimplexCategory.δ i).op e
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [sourceTriangleEdge, Category.assoc]
    rw [hd, pattern_faces.1, ← Category.assoc (U.diagram.σ (1 : Fin 2)) (U.diagram.δ (2 : Fin 3)) _,
      U.diagram.δ_comp_σ_succ' (i := (1 : Fin 2)) (j := (2 : Fin 3)) (by decide), Category.id_comp]
    rw [endpointH_one f₀ H SSet.coherentIso.x₀ h₀]
  · simp only [sourceTriangleEdge, Category.assoc]
    rw [hd, pattern_faces.2.1,
        ← Category.assoc (U.diagram.σ (1 : Fin 2)) (U.diagram.δ (0 : Fin 3)) _,
        sourceDegeneracy_last]
    simpa only [Category.assoc, etaEdgeArrow] using congrArg
      (fun k => k ≫ U.diagram.σ (0 : Fin 1) ≫
        SSet.simplicialSpaceTensorι SSet.coherentIso U.diagram (op ⦋1⦌)
          SSet.coherentIso.hom.edge ≫ H.app (op ⦋1⦌)) (mappingFibre.target_eq U x y)
  · simp only [sourceTriangleEdge, middleEdge, Category.assoc]
    rw [hd, pattern_faces.2.2.1,
        ← Category.assoc (U.diagram.σ (1 : Fin 2)) (U.diagram.δ (1 : Fin 3)) _,
      U.diagram.δ_comp_σ_self' (i := (1 : Fin 2)) (j := (1 : Fin 3)) (by decide), Category.id_comp]
  · simp only [targetTriangleEdge, Category.assoc]
    rw [hd, pattern_faces.2.2.2.1,
        ← Category.assoc (U.diagram.σ (0 : Fin 2)) (U.diagram.δ (2 : Fin 3)) _,
        targetDegeneracy_first]
    simpa only [Category.assoc, etaEdgeArrow] using congrArg
      (fun k => k ≫ U.diagram.σ (0 : Fin 1) ≫
        SSet.simplicialSpaceTensorι SSet.coherentIso U.diagram (op ⦋1⦌)
          SSet.coherentIso.hom.edge ≫ H.app (op ⦋1⦌)) (mappingFibre.source_eq U x y)
  · simp only [targetTriangleEdge, Category.assoc]
    rw [hd, pattern_faces.2.2.2.2.1,
        ← Category.assoc (U.diagram.σ (0 : Fin 2)) (U.diagram.δ (0 : Fin 3)) _,
      U.diagram.δ_comp_σ_self' (i := (0 : Fin 2)) (j := (0 : Fin 3)) (by decide), Category.id_comp]
    rw [endpointH_one f₁ H SSet.coherentIso.x₁ h₁]
  · simp only [targetTriangleEdge, middleEdge, Category.assoc]
    rw [hd, pattern_faces.2.2.2.2.2,
        ← Category.assoc (U.diagram.σ (0 : Fin 2)) (U.diagram.δ (1 : Fin 3)) _,
      U.diagram.δ_comp_σ_succ' (i := (0 : Fin 2)) (j := (1 : Fin 3)) (by decide), Category.id_comp]

private theorem middleEdge_endpoints {U V : SimplicialSpace.{u}} (f₀ f₁ : U ⟶ V)
    (H : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj U.diagram ⟶ V.diagram)
    (h₀ : tensorEndpoint U SSet.coherentIso.x₀ ≫ H = f₀.hom)
    (h₁ : tensorEndpoint U SSet.coherentIso.x₁ ≫ H = f₁.hom)
    (x y : (U.diagram _⦋0⦌) _⦋0⦌) :
    middleEdge H x y ≫ V.diagram.δ (1 : Fin 2) =
      mappingFibre.snd U x y ≫ SSet.yonedaEquiv.symm (mappingVertexMap f₀ x) ∧
    middleEdge H x y ≫ V.diagram.δ (0 : Fin 2) =
      mappingFibre.snd U x y ≫ SSet.yonedaEquiv.symm (mappingVertexMap f₁ y) := by
  have hd (i : Fin 2) :
      SSet.simplicialSpaceTensorι SSet.coherentIso U.diagram (op ⦋1⦌) SSet.coherentIso.hom.edge ≫
          H.app (op ⦋1⦌) ≫ V.diagram.δ i = U.diagram.δ i ≫
        SSet.simplicialSpaceTensorι SSet.coherentIso U.diagram (op ⦋0⦌)
          (SSet.coherentIso.δ i SSet.coherentIso.hom.edge) ≫ H.app (op ⦋0⦌) :=
    tensorH_operator H (SimplexCategory.δ i).op SSet.coherentIso.hom.edge
  constructor
  · simp only [middleEdge, Category.assoc]
    rw [hd, SSet.coherentIso.hom.src_eq, ← Category.assoc, mappingFibre.source_eq]
    rw [Category.assoc, endpointH_zero f₀ H SSet.coherentIso.x₀ h₀, SSet.yonedaEquiv_symm_comp]
  · simp only [middleEdge, Category.assoc]
    rw [hd, SSet.coherentIso.hom.tgt_eq, ← Category.assoc, mappingFibre.target_eq]
    rw [Category.assoc, endpointH_zero f₁ H SSet.coherentIso.x₁ h₁, SSet.yonedaEquiv_symm_comp]

/-- The original common middle lies in the prescribed f-zero-x-to-f-one-y mapping fibre. -/
def prismMiddle {U V : SimplicialSpace.{u}} (f₀ f₁ : U ⟶ V)
    (H : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj U.diagram ⟶ V.diagram)
    (h₀ : tensorEndpoint U SSet.coherentIso.x₀ ≫ H = f₀.hom)
    (h₁ : tensorEndpoint U SSet.coherentIso.x₁ ≫ H = f₁.hom)
    (x y : (U.diagram _⦋0⦌) _⦋0⦌) :
    mappingFibre U x y ⟶ mappingFibre V (mappingVertexMap f₀ x) (mappingVertexMap f₁ y) :=
  pullback.lift (middleEdge H x y) (mappingFibre.snd U x y) (by
    apply prod.hom_ext
    · simpa only [Category.assoc, mappingEndpoint_fst, mappingPointPair_fst] using
        (middleEdge_endpoints f₀ f₁ H h₀ h₁ x y).1
    · simpa only [Category.assoc, mappingEndpoint_snd, mappingPointPair_snd] using
        (middleEdge_endpoints f₀ f₁ H h₀ h₁ x y).2)

/-- The 001/σ-one triangle is a map of the actual prescribed triangle fibre. -/
def sourceTriangle {U V : SimplicialSpace.{u}} (f₀ f₁ : U ⟶ V) (hV : segalSpaces V)
    (H : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj U.diagram ⟶ V.diagram)
    (h₀ : tensorEndpoint U SSet.coherentIso.x₀ ≫ H = f₀.hom)
    (h₁ : tensorEndpoint U SSet.coherentIso.x₁ ≫ H = f₁.hom)
    (x y : (U.diagram _⦋0⦌) _⦋0⦌) :
    mappingFibre U x y ⟶ triangleSpace V (mappingVertexMap f₀ x)
      (mappingVertexMap f₀ y) (mappingVertexMap f₁ y) := by
  let a := (equivalenceFibreToMappingFibre V hV (mappingVertexMap f₀ y)
    (mappingVertexMap f₁ y)).app (op ⦋0⦌) (homotopyEquivalencePoint f₀ f₁ hV H h₀ h₁ y)
  let b := prod.lift (mappingFibre.map f₀ (x := x) (y := y) rfl rfl)
    (mappingFibre.snd U x y ≫ SSet.yonedaEquiv.symm a)
  refine pullback.lift (sourceTriangleEdge H x y) b ?_
  apply pullback.hom_ext
  · simp only [Category.assoc, twoEdgeComparison_fst, twoEdgePair_fst, b, prod.lift_fst_assoc]
    rw [(prismFaceEquations f₀ f₁ H h₀ h₁ x y).1, mappingFibre.map_fst]
  · simp only [Category.assoc, twoEdgeComparison_snd, twoEdgePair_snd, b, prod.lift_snd_assoc]
    rw [(prismFaceEquations f₀ f₁ H h₀ h₁ x y).2.1]
    exact congrArg (fun k => mappingFibre.snd U x y ≫ k)
      (homotopyEquivalencePoint_laws f₀ f₁ hV H h₀ h₁ y).1.symm

/-- The 011/σ-zero triangle is the complementary original prescribed triangle fibre map. -/
def targetTriangle {U V : SimplicialSpace.{u}} (f₀ f₁ : U ⟶ V) (hV : segalSpaces V)
    (H : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj U.diagram ⟶ V.diagram)
    (h₀ : tensorEndpoint U SSet.coherentIso.x₀ ≫ H = f₀.hom)
    (h₁ : tensorEndpoint U SSet.coherentIso.x₁ ≫ H = f₁.hom)
    (x y : (U.diagram _⦋0⦌) _⦋0⦌) :
    mappingFibre U x y ⟶ triangleSpace V (mappingVertexMap f₀ x)
      (mappingVertexMap f₁ x) (mappingVertexMap f₁ y) := by
  let a := (equivalenceFibreToMappingFibre V hV (mappingVertexMap f₀ x)
    (mappingVertexMap f₁ x)).app (op ⦋0⦌) (homotopyEquivalencePoint f₀ f₁ hV H h₀ h₁ x)
  let b := prod.lift (mappingFibre.snd U x y ≫ SSet.yonedaEquiv.symm a)
    (mappingFibre.map f₁ (x := x) (y := y) rfl rfl)
  refine pullback.lift (targetTriangleEdge H x y) b ?_
  apply pullback.hom_ext
  · simp only [Category.assoc, twoEdgeComparison_fst, twoEdgePair_fst, b, prod.lift_fst_assoc]
    rw [(prismFaceEquations f₀ f₁ H h₀ h₁ x y).2.2.2.1]
    exact congrArg (fun k => mappingFibre.snd U x y ≫ k)
      (homotopyEquivalencePoint_laws f₀ f₁ hV H h₀ h₁ x).1.symm
  · simp only [Category.assoc, twoEdgeComparison_snd, twoEdgePair_snd, b, prod.lift_snd_assoc]
    rw [(prismFaceEquations f₀ f₁ H h₀ h₁ x y).2.2.2.2.1, mappingFibre.map_fst]

/-- Both triangle projections/comparisons retain their original edges, including all inner
operators. -/
theorem triangleFibreProjectionLaws {U V : SimplicialSpace.{u}} (f₀ f₁ : U ⟶ V)
    (hV : segalSpaces V)
    (H : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj U.diagram ⟶ V.diagram)
    (h₀ : tensorEndpoint U SSet.coherentIso.x₀ ≫ H = f₀.hom)
    (h₁ : tensorEndpoint U SSet.coherentIso.x₁ ≫ H = f₁.hom)
    (x y : (U.diagram _⦋0⦌) _⦋0⦌) :
    let aₓ := (equivalenceFibreToMappingFibre V hV (mappingVertexMap f₀ x)
      (mappingVertexMap f₁ x)).app (op ⦋0⦌) (homotopyEquivalencePoint f₀ f₁ hV H h₀ h₁ x)
    let aᵧ := (equivalenceFibreToMappingFibre V hV (mappingVertexMap f₀ y)
      (mappingVertexMap f₁ y)).app (op ⦋0⦌) (homotopyEquivalencePoint f₀ f₁ hV H h₀ h₁ y)
    sourceTriangle f₀ f₁ hV H h₀ h₁ x y ≫
        triangleProjection V (mappingVertexMap f₀ x) (mappingVertexMap f₀ y)
            (mappingVertexMap f₁ y) =
      sourceTriangleEdge H x y ∧
    sourceTriangle f₀ f₁ hV H h₀ h₁ x y ≫
        triangleComparison V (mappingVertexMap f₀ x) (mappingVertexMap f₀ y)
            (mappingVertexMap f₁ y) =
      prod.lift (mappingFibre.map f₀ (x := x) (y := y) rfl rfl)
        (mappingFibre.snd U x y ≫ SSet.yonedaEquiv.symm aᵧ) ∧
    targetTriangle f₀ f₁ hV H h₀ h₁ x y ≫
        triangleProjection V (mappingVertexMap f₀ x) (mappingVertexMap f₁ x)
            (mappingVertexMap f₁ y) =
      targetTriangleEdge H x y ∧
    targetTriangle f₀ f₁ hV H h₀ h₁ x y ≫
        triangleComparison V (mappingVertexMap f₀ x) (mappingVertexMap f₁ x)
            (mappingVertexMap f₁ y) =
      prod.lift (mappingFibre.snd U x y ≫ SSet.yonedaEquiv.symm aₓ)
        (mappingFibre.map f₁ (x := x) (y := y) rfl rfl) := by
  dsimp only [sourceTriangle, targetTriangle, triangleProjection, triangleComparison]
  exact ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _,
    pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

/-- Both complementary triangle middles are the SAME whole original mapping-fibre map. -/
theorem triangleMiddleEquations {U V : SimplicialSpace.{u}} (f₀ f₁ : U ⟶ V)
    (hV : segalSpaces V)
    (H : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj U.diagram ⟶ V.diagram)
    (h₀ : tensorEndpoint U SSet.coherentIso.x₀ ≫ H = f₀.hom)
    (h₁ : tensorEndpoint U SSet.coherentIso.x₁ ≫ H = f₁.hom)
    (x y : (U.diagram _⦋0⦌) _⦋0⦌) :
    sourceTriangle f₀ f₁ hV H h₀ h₁ x y ≫
        triangleMiddle V (mappingVertexMap f₀ x) (mappingVertexMap f₀ y) (mappingVertexMap f₁ y) =
      prismMiddle f₀ f₁ H h₀ h₁ x y ∧
    targetTriangle f₀ f₁ hV H h₀ h₁ x y ≫
        triangleMiddle V (mappingVertexMap f₀ x) (mappingVertexMap f₁ x) (mappingVertexMap f₁ y) =
      prismMiddle f₀ f₁ H h₀ h₁ x y := by
  constructor
  · apply pullback.hom_ext
    · change _ ≫ mappingFibre.fst V (mappingVertexMap f₀ x) (mappingVertexMap f₁ y) =
        _ ≫ mappingFibre.fst V (mappingVertexMap f₀ x) (mappingVertexMap f₁ y)
      rw [Category.assoc, triangleMiddle_fst, ← Category.assoc,
        (triangleFibreProjectionLaws f₀ f₁ hV H h₀ h₁ x y).1,
        (prismFaceEquations f₀ f₁ H h₀ h₁ x y).2.2.1]
      exact (pullback.lift_fst _ _ _).symm
    · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  · apply pullback.hom_ext
    · change _ ≫ mappingFibre.fst V (mappingVertexMap f₀ x) (mappingVertexMap f₁ y) =
        _ ≫ mappingFibre.fst V (mappingVertexMap f₀ x) (mappingVertexMap f₁ y)
      rw [Category.assoc, triangleMiddle_fst, ← Category.assoc,
        (triangleFibreProjectionLaws f₀ f₁ hV H h₀ h₁ x y).2.2.1,
        (prismFaceEquations f₀ f₁ H h₀ h₁ x y).2.2.2.2.2]
      exact (pullback.lift_fst _ _ _).symm
    · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- Every original inner simplex operator acts on both actual triangle maps naturally. -/
theorem triangleOperatorEquations {U V : SimplicialSpace.{u}} (f₀ f₁ : U ⟶ V)
    (hV : segalSpaces V)
    (H : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj U.diagram ⟶ V.diagram)
    (h₀ : tensorEndpoint U SSet.coherentIso.x₀ ≫ H = f₀.hom)
    (h₁ : tensorEndpoint U SSet.coherentIso.x₁ ≫ H = f₁.hom)
    (x y : (U.diagram _⦋0⦌) _⦋0⦌) {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n) :
    (mappingFibre U x y).map α ≫ (sourceTriangle f₀ f₁ hV H h₀ h₁ x y).app n =
      (sourceTriangle f₀ f₁ hV H h₀ h₁ x y).app m ≫
        (triangleSpace V (mappingVertexMap f₀ x) (mappingVertexMap f₀ y)
            (mappingVertexMap f₁ y)).map α ∧
    (mappingFibre U x y).map α ≫ (targetTriangle f₀ f₁ hV H h₀ h₁ x y).app n =
      (targetTriangle f₀ f₁ hV H h₀ h₁ x y).app m ≫
        (triangleSpace V (mappingVertexMap f₀ x) (mappingVertexMap f₁ x)
            (mappingVertexMap f₁ y)).map α :=
  ⟨(sourceTriangle f₀ f₁ hV H h₀ h₁ x y).naturality α,
    (targetTriangle f₀ f₁ hV H h₀ h₁ x y).naturality α⟩

private def homotopyPre {A B C : SSet.{u}} {f g : B ⟶ C}
    (H : SSet.Homotopy f g) (k : A ⟶ B) : SSet.Homotopy (k ≫ f) (k ≫ g) :=
  (show SSet.HomotopyRel (k ≫ f) (k ≫ g) (⊥ : A.Subcomplex) from
    { h := (k ▷ (Δ[1] : SSet.{u})) ≫ H.h
      h₀ := by rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, H.h₀]
      h₁ := by rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, H.h₁]
      stationary := by intro n a ha t; cases ha }).toHomotopy

/-- Both whole original composites are homotopic to the SAME prescribed middle map. -/
def compositionHomotopies {U V : SimplicialSpace.{u}} (f₀ f₁ : U ⟶ V)
    (hV : segalSpaces V)
    (H : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj U.diagram ⟶ V.diagram)
    (h₀ : tensorEndpoint U SSet.coherentIso.x₀ ≫ H = f₀.hom)
    (h₁ : tensorEndpoint U SSet.coherentIso.x₁ ≫ H = f₁.hom)
    (x y : (U.diagram _⦋0⦌) _⦋0⦌) :
    SSet.Homotopy (prismMiddle f₀ f₁ H h₀ h₁ x y)
      (mappingFibre.map f₀ (x := x) (y := y) rfl rfl ≫
        SegalEquivalenceHomTransport.postcomposePoint V hV (mappingVertexMap f₀ y)
          (mappingVertexMap f₁ y) (homotopyEquivalencePoint f₀ f₁ hV H h₀ h₁ y)
          (mappingVertexMap f₀ x)) ×
    SSet.Homotopy (prismMiddle f₀ f₁ H h₀ h₁ x y)
      (mappingFibre.map f₁ (x := x) (y := y) rfl rfl ≫
        SegalEquivalenceHomTransport.precomposePoint V hV (mappingVertexMap f₀ x)
          (mappingVertexMap f₁ x) (homotopyEquivalencePoint f₀ f₁ hV H h₀ h₁ x)
          (mappingVertexMap f₁ y)) := by
  have H₀ := homotopyPre (mappingCompositionOfTriangle V hV
    (mappingVertexMap f₀ x) (mappingVertexMap f₀ y) (mappingVertexMap f₁ y))
      (sourceTriangle f₀ f₁ hV H h₀ h₁ x y)
  have H₁ := homotopyPre (mappingCompositionOfTriangle V hV
    (mappingVertexMap f₀ x) (mappingVertexMap f₁ x) (mappingVertexMap f₁ y))
      (targetTriangle f₀ f₁ hV H h₀ h₁ x y)
  rw [(triangleMiddleEquations f₀ f₁ hV H h₀ h₁ x y).1] at H₀
  rw [(triangleMiddleEquations f₀ f₁ hV H h₀ h₁ x y).2] at H₁
  rw [← Category.assoc, (triangleFibreProjectionLaws f₀ f₁ hV H h₀ h₁ x y).2.1] at H₀
  rw [← Category.assoc, (triangleFibreProjectionLaws f₀ f₁ hV H h₀ h₁ x y).2.2.2] at H₁
  constructor
  · simpa only [SegalEquivalenceHomTransport.postcomposePoint, mappingPostcomposition,
      prod.comp_lift_assoc, Category.comp_id, Category.assoc, mappingFibre.map_snd_assoc] using H₀
  · simpa only [SegalEquivalenceHomTransport.precomposePoint, mappingPrecomposition,
      prod.comp_lift_assoc, Category.comp_id, Category.assoc, mappingFibre.map_snd_assoc] using H₁

/-- The actual MF-to-Delta-zero fibration joins the two prism homotopies on the SAME target. -/
def mappingFibreHomotopy {U V : SimplicialSpace.{u}} (f₀ f₁ : U ⟶ V)
    (hV : segalSpaces V)
    (H : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj U.diagram ⟶ V.diagram)
    (h₀ : tensorEndpoint U SSet.coherentIso.x₀ ≫ H = f₀.hom)
    (h₁ : tensorEndpoint U SSet.coherentIso.x₁ ≫ H = f₁.hom)
    (x y : (U.diagram _⦋0⦌) _⦋0⦌) :
    SSet.Homotopy
      (mappingFibre.map f₀ (x := x) (y := y) rfl rfl ≫
        SegalEquivalenceHomTransport.postcomposePoint V hV (mappingVertexMap f₀ y)
          (mappingVertexMap f₁ y) (homotopyEquivalencePoint f₀ f₁ hV H h₀ h₁ y)
          (mappingVertexMap f₀ x))
      (mappingFibre.map f₁ (x := x) (y := y) rfl rfl ≫
        SegalEquivalenceHomTransport.precomposePoint V hV (mappingVertexMap f₀ x)
          (mappingVertexMap f₁ x) (homotopyEquivalencePoint f₀ f₁ hV H h₀ h₁ x)
          (mappingVertexMap f₁ y)) := by
  have join : ∀ {A B : SSet.{u}} (p : B ⟶ (Δ[0] : SSet.{u})) (_ : Fibration p)
      {f g m : A ⟶ B}, SSet.Homotopy m f → SSet.Homotopy m g →
        Nonempty (SSet.Homotopy f g) := by
    intro A B p hp f g m H₀ H₁
    let : Fibration p := hp
    let R₀ : SSet.HomotopyRelOver p m f (⊥ : A.Subcomplex) :=
      { toHomotopyRel :=
          { h := H₀.h, h₀ := H₀.h₀, h₁ := H₀.h₁
            stationary := by intro n a ha t; cases ha }
        over := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _ }
    let R₁ : SSet.HomotopyRelOver p m g (⊥ : A.Subcomplex) :=
      { toHomotopyRel :=
          { h := H₁.h, h₀ := H₁.h₀, h₁ := H₁.h₁
            stationary := by intro n a ha t; cases ha }
        over := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _ }
    exact ⟨(SSet.HomotopyRelOver.trans (SSet.HomotopyRelOver.symm R₀) R₁).toHomotopyRel.toHomotopy⟩
  exact Classical.choice (join
    (mappingFibre.snd V (mappingVertexMap f₀ x) (mappingVertexMap f₁ y))
    (ReedyModel.mappingFibre_snd_fibration V (mappingVertexMap f₀ x) (mappingVertexMap f₁ y) hV.1)
    (compositionHomotopies f₀ f₁ hV H h₀ h₁ x y).1
    (compositionHomotopies f₀ f₁ hV H h₀ h₁ x y).2)

/-- Full weakness of the SAME original mapping-fibre maps is invariant under this categorical H. -/
theorem mappingFibreWeak_iff {U V : SimplicialSpace.{u}} (f₀ f₁ : U ⟶ V)
    (hV : segalSpaces V)
    (H : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj U.diagram ⟶ V.diagram)
    (h₀ : tensorEndpoint U SSet.coherentIso.x₀ ≫ H = f₀.hom)
    (h₁ : tensorEndpoint U SSet.coherentIso.x₁ ≫ H = f₁.hom)
    (x y : (U.diagram _⦋0⦌) _⦋0⦌) :
    SSet.realizationWeakEquivalences (mappingFibre.map f₀ (x := x) (y := y) rfl rfl) ↔
      SSet.realizationWeakEquivalences (mappingFibre.map f₁ (x := x) (y := y) rfl rfl) := by
  let p := SegalEquivalenceHomTransport.postcomposePoint V hV (mappingVertexMap f₀ y)
    (mappingVertexMap f₁ y) (homotopyEquivalencePoint f₀ f₁ hV H h₀ h₁ y) (mappingVertexMap f₀ x)
  let q := SegalEquivalenceHomTransport.precomposePoint V hV (mappingVertexMap f₀ x)
    (mappingVertexMap f₁ x) (homotopyEquivalencePoint f₀ f₁ hV H h₀ h₁ x) (mappingVertexMap f₁ y)
  have hp : SSet.realizationWeakEquivalences p :=
    SegalEquivalenceHomTransport.postcomposePoint_realizationWeak V hV _ _ _ _
  have hq : SSet.realizationWeakEquivalences q :=
    SegalEquivalenceHomTransport.precomposePoint_realizationWeak V hV _ _ _ _
  have hc := SSet.realizationWeakEquivalences_iff_of_homotopy
      (mappingFibreHomotopy f₀ f₁ hV H h₀ h₁ x y)
  exact (SSet.realizationWeakEquivalences.postcomp_iff
    (mappingFibre.map f₀ (x := x) (y := y) rfl rfl) p hp).symm.trans
      (hc.trans (SSet.realizationWeakEquivalences.postcomp_iff
        (mappingFibre.map f₁ (x := x) (y := y) rfl rfl) q hq))

private theorem homotopy_components {A B : SSet.{u}} {f g : A ⟶ B}
    (H : SSet.Homotopy f g) (c : SSet.π₀ A) : SSet.mapπ₀ f c = SSet.mapπ₀ g c := by
  refine SSet.π₀.rec (fun a => ?_) c
  rw [SSet.mapπ₀_mk, SSet.mapπ₀_mk]
  let h := H.toSimplicialObjectHomotopy
  apply SSet.π₀.sound
  refine { edge := (h.h (0 : Fin 1)) a, src_eq := ?_, tgt_eq := ?_ }
  · exact congrArg (fun k => k a) (h.h_last_comp_δ_last 0)
  · exact congrArg (fun k => k a) (h.h_zero_comp_δ_zero 0)

/-- Every original Hom component obeys the actual EF-point naturality equation. -/
theorem homComponentEquation {U V : SimplicialSpace.{u}} (f₀ f₁ : U ⟶ V)
    (hV : segalSpaces V)
    (H : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj U.diagram ⟶ V.diagram)
    (h₀ : tensorEndpoint U SSet.coherentIso.x₀ ≫ H = f₀.hom)
    (h₁ : tensorEndpoint U SSet.coherentIso.x₁ ≫ H = f₁.hom)
    (x y : (U.diagram _⦋0⦌) _⦋0⦌) (c : SSet.π₀ (mappingFibre U x y)) :
    SSet.mapπ₀ (mappingFibre.map f₀ (x := x) (y := y) rfl rfl) c ≫
      SegalEquivalenceHomTransport.pointHom V hV (mappingVertexMap f₀ y) (mappingVertexMap f₁ y)
        (homotopyEquivalencePoint f₀ f₁ hV H h₀ h₁ y) =
    SegalEquivalenceHomTransport.pointHom V hV (mappingVertexMap f₀ x) (mappingVertexMap f₁ x)
        (homotopyEquivalencePoint f₀ f₁ hV H h₀ h₁ x) ≫
      SSet.mapπ₀ (mappingFibre.map f₁ (x := x) (y := y) rfl rfl) c := by
  have h := homotopy_components (mappingFibreHomotopy f₀ f₁ hV H h₀ h₁ x y) c
  simpa only [SSet.mapπ₀_comp_apply, SegalEquivalenceHomTransport.postcomposePoint_component,
    SegalEquivalenceHomTransport.precomposePoint_component] using h

/-- The original intrinsic Ho functors carry the actual point isomorphisms as a natural Iso. -/
def homotopyHoNatIso {U V : SimplicialSpace.{u}} (f₀ f₁ : U ⟶ V)
    (hU : segalSpaces U) (hV : segalSpaces V)
    (H : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj U.diagram ⟶ V.diagram)
    (h₀ : tensorEndpoint U SSet.coherentIso.x₀ ≫ H = f₀.hom)
    (h₁ : tensorEndpoint U SSet.coherentIso.x₁ ≫ H = f₁.hom) :
    SegalHomotopy.map f₀ hU hV ≅ SegalHomotopy.map f₁ hU hV :=
  NatIso.ofComponents
    (fun a => SegalEquivalenceHomTransport.pointIso V hV (mappingVertexMap f₀ a.vertex)
      (mappingVertexMap f₁ a.vertex) (homotopyEquivalencePoint f₀ f₁ hV H h₀ h₁ a.vertex))
    (by intro a b c
        exact homComponentEquation f₀ f₁ hV H h₀ h₁ a.vertex b.vertex c)

/-- Essential surjectivity of the SAME intrinsic Ho functors is transported by the actual H. -/
theorem homotopyHoEssSurj_iff {U V : SimplicialSpace.{u}} (f₀ f₁ : U ⟶ V)
    (hU : segalSpaces U) (hV : segalSpaces V)
    (H : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj U.diagram ⟶ V.diagram)
    (h₀ : tensorEndpoint U SSet.coherentIso.x₀ ≫ H = f₀.hom)
    (h₁ : tensorEndpoint U SSet.coherentIso.x₁ ≫ H = f₁.hom) :
    (SegalHomotopy.map f₀ hU hV).EssSurj ↔ (SegalHomotopy.map f₁ hU hV).EssSurj := by
  constructor
  · intro h
    let := h
    exact CategoryTheory.Functor.essSurj_of_iso (homotopyHoNatIso f₀ f₁ hU hV H h₀ h₁)
  · intro h
    let := h
    exact CategoryTheory.Functor.essSurj_of_iso (homotopyHoNatIso f₀ f₁ hU hV H h₀ h₁).symm

end SimplicialSpace.CategoricalHomotopyPrism
