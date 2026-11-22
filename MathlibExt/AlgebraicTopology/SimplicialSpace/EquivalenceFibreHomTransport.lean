/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Original RF Segal equivalence-fibre points give intrinsic Ho isomorphisms,
-- full weak mapping-fibre spans, and their original Hom transport.
import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalCorePathObject
import Mathlib.CategoryTheory.HomCongr
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalMappingOperatorEquivalences

/-!
# Homotopy-category transport through equivalence fibres

Vertices of ordered equivalence fibres give isomorphisms in the homotopy category of a Reedy-
fibrant Segal space. Precomposition and postcomposition by these vertices are weak equivalences
of the original mapping fibres, and their component transport is precisely conjugation by the
induced homotopy-category isomorphisms, with forward, inverse and span equations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen
namespace SimplicialSpace.SegalEquivalenceHomTransport
open SegalHomotopy

/-- An original equivalence-fibre point gives its same original prescribed-fibre Hom class. -/
def pointHom (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (e : (equivalenceFibre W hW x y) _⦋0⦌) :
    (⟨x⟩ : Object W hW) ⟶ (⟨y⟩ : Object W hW) :=
  SSet.π₀.mk ((equivalenceFibreToMappingFibre W hW x y).app (op ⦋0⦌) e)

/-- Invertibility is derived from the actual EF preimage selector and the SAME original MF
vertex. -/
theorem pointHom_isIso (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (e : (equivalenceFibre W hW x y) _⦋0⦌) :
    IsIso (pointHom W hW x y e) := by
  let U := SSet.componentUnion (mappingFibre W x y)
    ((SSet.mapπ₀ (mappingFibre.fst W x y)) ⁻¹' equivalenceComponents W hW)
  let a := (equivalenceFibreToMappingFibre W hW x y).app (op ⦋0⦌) e
  let b := (equivalenceFibrePreimageIso W hW x y).hom.app (op ⦋0⦌) e
  have he : b.val = a := by
    have h := congrArg (fun k => k.app (op ⦋0⦌) e)
      (equivalenceFibrePreimageIso_laws W hW x y).1
    change b.val = a at h
    exact h
  have ha : a ∈ U.obj (op ⦋0⦌) := he ▸ b.property
  exact ((equivalenceFibrePreimageIso_laws W hW x y).2.2.2.2 a).mp ha

/-- The actual intrinsic Iso is constructed, rather than accepted as an outcome premise. -/
def pointIso (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (e : (equivalenceFibre W hW x y) _⦋0⦌) :
    (⟨x⟩ : Object W hW) ≅ (⟨y⟩ : Object W hW) := by
  letI := pointHom_isIso W hW x y e
  exact asIso (pointHom W hW x y e)

/-- Its Hom is exactly the class of the original EF-to-MF point projection. -/
theorem pointIso_hom (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (e : (equivalenceFibre W hW x y) _⦋0⦌) :
    (pointIso W hW x y e).hom =
      SSet.π₀.mk ((equivalenceFibreToMappingFibre W hW x y).app (op ⦋0⦌) e) := rfl

/-- Two original equivalence-fibre points transport ORIGINAL MF components in both directions. -/
def originalHomTransport (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x x' y y' : (W.diagram _⦋0⦌) _⦋0⦌)
    (a : (equivalenceFibre W hW x x') _⦋0⦌)
    (b : (equivalenceFibre W hW y y') _⦋0⦌) :
    SSet.π₀ (mappingFibre W x y) ≃ SSet.π₀ (mappingFibre W x' y') :=
  Iso.homCongr (pointIso W hW x x' a) (pointIso W hW y y' b)

/-- Both characteristics retain the actual two EF-point isomorphisms and original Hom order. -/
theorem originalHomTransport_characteristics (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x x' y y' : (W.diagram _⦋0⦌) _⦋0⦌)
    (a : (equivalenceFibre W hW x x') _⦋0⦌)
    (b : (equivalenceFibre W hW y y') _⦋0⦌)
    (f : SSet.π₀ (mappingFibre W x y)) (g : SSet.π₀ (mappingFibre W x' y')) :
    originalHomTransport W hW x x' y y' a b f =
      (pointIso W hW x x' a).inv ≫ f ≫ (pointIso W hW y y' b).hom ∧
    (originalHomTransport W hW x x' y y' a b).symm g =
      (pointIso W hW x x' a).hom ≫ g ≫ (pointIso W hW y y' b).inv := by
  constructor
  · exact Iso.homCongr_apply (C := Object W hW)
      (pointIso W hW x x' a) (pointIso W hW y y' b)
      (f : (⟨x⟩ : Object W hW) ⟶ (⟨y⟩ : Object W hW))
  · change (Iso.homCongr (C := Object W hW)
      (pointIso W hW x x' a) (pointIso W hW y y' b)).symm
      (g : (⟨x'⟩ : Object W hW) ⟶ (⟨y'⟩ : Object W hW)) = _
    rw [Iso.homCongr_symm, Iso.homCongr_apply, Iso.symm_inv, Iso.symm_hom]

/-- Original fibre maps preserve the very same EF-point Hom class, without a weak-map hypothesis. -/
theorem pointHom_map {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (e : (equivalenceFibre W hW x y) _⦋0⦌) :
    SSet.mapπ₀ (mappingFibre.map f (x := x) (y := y) rfl rfl) (pointHom W hW x y e) =
      pointHom V hV (mappingVertexMap f x) (mappingVertexMap f y)
        ((equivalenceFibreMap f hW hV (x := x) (y := y) rfl rfl).app (op ⦋0⦌) e) := by
  change SSet.mapπ₀ (mappingFibre.map f rfl rfl)
    (SSet.π₀.mk ((equivalenceFibreToMappingFibre W hW x y).app (op ⦋0⦌) e)) = _
  rw [SSet.mapπ₀_mk]
  have h := congrArg (fun k => k.app (op ⦋0⦌) e)
    ((equivalenceFibreMap_laws f hW hV (x := x) (y := y) rfl rfl).2.2.1)
  change (equivalenceFibreToMappingFibre V hV _ _).app (op ⦋0⦌)
      ((equivalenceFibreMap f hW hV rfl rfl).app (op ⦋0⦌) e) =
    (mappingFibre.map f rfl rfl).app (op ⦋0⦌)
      ((equivalenceFibreToMappingFibre W hW x y).app (op ⦋0⦌) e) at h
  exact congrArg SSet.π₀.mk h.symm

/-- The original EF-point edge is intrinsically invertible, derived from its actual selected MF
class. -/
theorem pointEdge_isEquivalence (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (e : (equivalenceFibre W hW x y) _⦋0⦌) :
    IsEquivalenceEdge W hW ((mappingFibre.fst W x y).app (op ⦋0⦌)
      ((equivalenceFibreToMappingFibre W hW x y).app (op ⦋0⦌) e)) :=
  (isEquivalenceEdge_iff_of_fibre W hW _ _ rfl).mpr (pointHom_isIso W hW x y e)

/-- Full postcomposition uses the SAME original EF-to-MF point and accepted original mapping
operator. -/
def postcomposePoint (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (e : (equivalenceFibre W hW x y) _⦋0⦌)
    (w : (W.diagram _⦋0⦌) _⦋0⦌) : mappingFibre W w x ⟶ mappingFibre W w y :=
  mappingPostcomposition W hW w x y
    ((equivalenceFibreToMappingFibre W hW x y).app (op ⦋0⦌) e)

/-- Full precomposition retains that same original point and both prescribed endpoints. -/
def precomposePoint (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (e : (equivalenceFibre W hW x y) _⦋0⦌)
    (z : (W.diagram _⦋0⦌) _⦋0⦌) : mappingFibre W y z ⟶ mappingFibre W x z :=
  mappingPrecomposition W hW x y z
    ((equivalenceFibreToMappingFibre W hW x y).app (op ⦋0⦌) e)

/-- Realization weakness of the full postcomposition is derived without a supplied weak outcome. -/
theorem postcomposePoint_realizationWeak (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (e : (equivalenceFibre W hW x y) _⦋0⦌)
    (w : (W.diagram _⦋0⦌) _⦋0⦌) :
        SSet.realizationWeakEquivalences (postcomposePoint W hW x y e w) :=
  mappingPostcomposition_realizationWeakEquivalence W hW x y _
    (pointEdge_isEquivalence W hW x y e) w

/-- Realization weakness of full precomposition uses the existing independent two-inverse-point
theorem. -/
theorem precomposePoint_realizationWeak (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (e : (equivalenceFibre W hW x y) _⦋0⦌)
    (z : (W.diagram _⦋0⦌) _⦋0⦌) : SSet.realizationWeakEquivalences (precomposePoint W hW x y e z) :=
  mappingPrecomposition_realizationWeakEquivalence W hW x y _
    (pointEdge_isEquivalence W hW x y e) z

/-- Both arrows of the ORIGINAL moving-endpoint MF span are FULL realization weak. -/
theorem originalMappingTransport_weakSpan (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x x' y y' : (W.diagram _⦋0⦌) _⦋0⦌)
    (a : (equivalenceFibre W hW x x') _⦋0⦌)
    (b : (equivalenceFibre W hW y y') _⦋0⦌) :
    SSet.realizationWeakEquivalences (postcomposePoint W hW y y' b x) ∧
      SSet.realizationWeakEquivalences (precomposePoint W hW x x' a y') :=
  ⟨postcomposePoint_realizationWeak W hW y y' b x,
    precomposePoint_realizationWeak W hW x x' a y'⟩

/-- The SAME two full MF arrows lie in the full Kan weak class, including every original homotopy
group. -/
theorem originalMappingTransport_KanWeakSpan (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x x' y y' : (W.diagram _⦋0⦌) _⦋0⦌)
    (a : (equivalenceFibre W hW x x') _⦋0⦌)
    (b : (equivalenceFibre W hW y y') _⦋0⦌) :
    SSet.KanComplex.W (postcomposePoint W hW y y' b x) ∧
      SSet.KanComplex.W (precomposePoint W hW x x' a y') :=
  ⟨mappingPostcomposition_W W hW y y' _ (pointEdge_isEquivalence W hW y y' b) x,
    mappingPrecomposition_W W hW x x' _ (pointEdge_isEquivalence W hW x x' a) y'⟩

/-- The full postcomposition operator has the exact original intrinsic Hom-class characteristic. -/
theorem postcomposePoint_component (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (e : (equivalenceFibre W hW x y) _⦋0⦌)
    (w : (W.diagram _⦋0⦌) _⦋0⦌) (f : SSet.π₀ (mappingFibre W w x)) :
    SSet.mapπ₀ (postcomposePoint W hW x y e w) f = f ≫ pointHom W hW x y e := by
  refine SSet.π₀.rec (fun q => ?_) f
  let a := (equivalenceFibreToMappingFibre W hW x y).app (op ⦋0⦌) e
  let v : (Δ[0] : SSet.{u}) _⦋0⦌ := SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))
  have hv : (mappingFibre.snd W w x).app (op ⦋0⦌) q = v := by
    apply SSet.yonedaEquiv.symm.injective
    exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have heval : (SSet.yonedaEquiv.symm a).app (op ⦋0⦌) v = a := by
    have h := SSet.yonedaEquiv_comp (𝟙 (Δ[0] : SSet.{u})) (SSet.yonedaEquiv.symm a)
    simpa only [v, Category.id_comp, Equiv.apply_symm_apply] using h.symm
  let pair : mappingFibre W w x ⟶ mappingFibre W w x ⨯ mappingFibre W x y :=
    prod.lift (𝟙 (mappingFibre W w x)) (mappingFibre.snd W w x ≫ SSet.yonedaEquiv.symm a)
  let t := pair.app (op ⦋0⦌) q
  have ht₀ : (prod.fst : mappingFibre W w x ⨯ mappingFibre W x y ⟶ _).app (op ⦋0⦌) t = q := by
    change (pair ≫ prod.fst).app (op ⦋0⦌) q = q
    dsimp only [pair]
    rw [prod.lift_fst]
    rfl
  have ht₁ : (prod.snd : mappingFibre W w x ⨯ mappingFibre W x y ⟶ _).app (op ⦋0⦌) t = a := by
    change (pair ≫ prod.snd).app (op ⦋0⦌) q = a
    dsimp only [pair]
    rw [prod.lift_snd]
    change (SSet.yonedaEquiv.symm a).app (op ⦋0⦌)
      ((mappingFibre.snd W w x).app (op ⦋0⦌) q) = a
    rw [hv, heval]
  rw [SSet.mapπ₀_mk]
  change SSet.π₀.mk ((mappingComposition W hW w x y).app (op ⦋0⦌) t) =
    compose W hW (SSet.π₀.mk q) (SSet.π₀.mk a)
  have h := mappingComposition_π₀ W hW w x y t
  simpa only [ht₀, ht₁] using h

/-- Full precomposition computes the same original left Hom composition on every MF component. -/
theorem precomposePoint_component (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (e : (equivalenceFibre W hW x y) _⦋0⦌)
    (z : (W.diagram _⦋0⦌) _⦋0⦌) (f : SSet.π₀ (mappingFibre W y z)) :
    SSet.mapπ₀ (precomposePoint W hW x y e z) f = pointHom W hW x y e ≫ f := by
  refine SSet.π₀.rec (fun q => ?_) f
  let a := (equivalenceFibreToMappingFibre W hW x y).app (op ⦋0⦌) e
  let v : (Δ[0] : SSet.{u}) _⦋0⦌ := SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))
  have hv : (mappingFibre.snd W y z).app (op ⦋0⦌) q = v := by
    apply SSet.yonedaEquiv.symm.injective
    exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have heval : (SSet.yonedaEquiv.symm a).app (op ⦋0⦌) v = a := by
    have h := SSet.yonedaEquiv_comp (𝟙 (Δ[0] : SSet.{u})) (SSet.yonedaEquiv.symm a)
    simpa only [v, Category.id_comp, Equiv.apply_symm_apply] using h.symm
  let pair : mappingFibre W y z ⟶ mappingFibre W x y ⨯ mappingFibre W y z :=
    prod.lift (mappingFibre.snd W y z ≫ SSet.yonedaEquiv.symm a) (𝟙 (mappingFibre W y z))
  let t := pair.app (op ⦋0⦌) q
  have ht₀ : (prod.fst : mappingFibre W x y ⨯ mappingFibre W y z ⟶ _).app (op ⦋0⦌) t = a := by
    change (pair ≫ prod.fst).app (op ⦋0⦌) q = a
    dsimp only [pair]
    rw [prod.lift_fst]
    change (SSet.yonedaEquiv.symm a).app (op ⦋0⦌)
      ((mappingFibre.snd W y z).app (op ⦋0⦌) q) = a
    rw [hv, heval]
  have ht₁ : (prod.snd : mappingFibre W x y ⨯ mappingFibre W y z ⟶ _).app (op ⦋0⦌) t = q := by
    change (pair ≫ prod.snd).app (op ⦋0⦌) q = q
    dsimp only [pair]
    rw [prod.lift_snd]
    rfl
  rw [SSet.mapπ₀_mk]
  change SSet.π₀.mk ((mappingComposition W hW x y z).app (op ⦋0⦌) t) =
    compose W hW (SSet.π₀.mk a) (SSet.π₀.mk q)
  have h := mappingComposition_π₀ W hW x y z t
  simpa only [ht₀, ht₁] using h

/-- The two FULL weak MF arrows induce precisely the original Hom transport, in its actual Hom
order. -/
theorem originalHomTransport_spanEquation (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x x' y y' : (W.diagram _⦋0⦌) _⦋0⦌)
    (a : (equivalenceFibre W hW x x') _⦋0⦌)
    (b : (equivalenceFibre W hW y y') _⦋0⦌)
    (f : SSet.π₀ (mappingFibre W x y)) :
    SSet.mapπ₀ (precomposePoint W hW x x' a y')
      (originalHomTransport W hW x x' y y' a b f) =
    SSet.mapπ₀ (postcomposePoint W hW y y' b x) f := by
  rw [precomposePoint_component, postcomposePoint_component]
  change (pointIso W hW x x' a).hom ≫
      ((pointIso W hW x x' a).inv ≫ f ≫ (pointIso W hW y y' b).hom) =
    f ≫ (pointIso W hW y y' b).hom
  simp only [Iso.hom_inv_id_assoc]

end SimplicialSpace.SegalEquivalenceHomTransport
