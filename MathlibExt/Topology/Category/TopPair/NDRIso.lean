/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.Topology.Category.TopPair.NDR

/-!
# Transport of NDR data across pair isomorphisms

Controlled neighborhood deformation retract data transports along an
isomorphism of topological pairs.  The characteristic formulas expose the
transport on the ambient control, endpoint, and deformation maps.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory Topology
open scoped unitInterval

universe u

namespace TopPair.NDRData

/-- Cancellation of the ambient components of a pair isomorphism, in the
forward-then-inverse direction. -/
private theorem fst_hom_inv_id_apply {P Q : TopPair.{u}} (e : P ≅ Q)
    (x : P.fst) :
    TopPair.Hom.fst e.inv (TopPair.Hom.fst e.hom x) = x := by
  have h := congrArg (TopPair.proj₁.map) e.hom_inv_id
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at h
  change TopPair.Hom.fst e.hom ≫ TopPair.Hom.fst e.inv = 𝟙 P.fst at h
  simpa only [TopCat.comp_app, TopCat.id_app] using
    ConcreteCategory.congr_hom h x

/-- Cancellation of the ambient components of a pair isomorphism, in the
inverse-then-forward direction. -/
private theorem fst_inv_hom_id_apply {P Q : TopPair.{u}} (e : P ≅ Q)
    (y : Q.fst) :
    TopPair.Hom.fst e.hom (TopPair.Hom.fst e.inv y) = y := by
  have h := congrArg (TopPair.proj₁.map) e.inv_hom_id
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at h
  change TopPair.Hom.fst e.inv ≫ TopPair.Hom.fst e.hom = 𝟙 Q.fst at h
  simpa only [TopCat.comp_app, TopCat.id_app] using
    ConcreteCategory.congr_hom h y

/-- Transport controlled NDR data along an isomorphism of topological pairs. -/
noncomputable def ofIso {P Q : TopPair.{u}}
    (d : NDRData P) (e : P ≅ Q) : NDRData Q where
  control := d.control.comp (TopPair.Hom.fst e.inv).hom
  endpoint := (TopPair.Hom.fst e.hom).hom.comp
    (d.endpoint.comp (TopPair.Hom.fst e.inv).hom)
  deformation :=
    { toFun := fun p =>
        TopPair.Hom.fst e.hom
          (d.deformation (p.1, TopPair.Hom.fst e.inv p.2))
      continuous_toFun := (TopPair.Hom.fst e.hom).hom.continuous.comp
        (d.deformation.continuous.comp
          (continuous_fst.prodMk
            ((TopPair.Hom.fst e.inv).hom.continuous.comp continuous_snd)))
      map_zero_left := fun y => by
        change TopPair.Hom.fst e.hom
          (d.deformation (0, TopPair.Hom.fst e.inv y)) = y
        rw [d.deformation.apply_zero]
        exact fst_inv_hom_id_apply e y
      map_one_left := fun y => by
        change TopPair.Hom.fst e.hom
            (d.deformation (1, TopPair.Hom.fst e.inv y)) =
          TopPair.Hom.fst e.hom
            (d.endpoint (TopPair.Hom.fst e.inv y))
        rw [d.deformation.apply_one]
      prop' := fun t y hy => by
        rcases hy with ⟨x, rfl⟩
        have hInv : P.map (TopPair.Hom.snd e.inv x) =
            TopPair.Hom.fst e.inv (Q.map x) := by
          simpa only [TopCat.comp_app] using
            congrArg (fun k : Q.snd ⟶ P.fst => k x)
              (TopPair.Hom.w e.inv)
        change TopPair.Hom.fst e.hom
            (d.deformation (t, TopPair.Hom.fst e.inv (Q.map x))) = Q.map x
        rw [← hInv]
        calc
          TopPair.Hom.fst e.hom
              (d.deformation (t, P.map (TopPair.Hom.snd e.inv x))) =
              TopPair.Hom.fst e.hom (P.map (TopPair.Hom.snd e.inv x)) :=
            congrArg (TopPair.Hom.fst e.hom)
              (d.deformation.eq_fst t ⟨TopPair.Hom.snd e.inv x, rfl⟩)
          _ = TopPair.Hom.fst e.hom
              (TopPair.Hom.fst e.inv (Q.map x)) :=
            congrArg (TopPair.Hom.fst e.hom) hInv
          _ = Q.map x := fst_inv_hom_id_apply e _ }
  control_eq_zero_iff := fun y => by
    change d.control (TopPair.Hom.fst e.inv y) = 0 ↔ y ∈ Set.range Q.map
    rw [d.control_eq_zero_iff]
    have hHom (x : P.snd) :
        Q.map (TopPair.Hom.snd e.hom x) =
          TopPair.Hom.fst e.hom (P.map x) := by
      simpa only [TopCat.comp_app] using
        congrArg (fun k : P.snd ⟶ Q.fst => k x)
          (TopPair.Hom.w e.hom)
    have hInv (x : Q.snd) :
        P.map (TopPair.Hom.snd e.inv x) =
          TopPair.Hom.fst e.inv (Q.map x) := by
      simpa only [TopCat.comp_app] using
        congrArg (fun k : Q.snd ⟶ P.fst => k x)
          (TopPair.Hom.w e.inv)
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨TopPair.Hom.snd e.hom x, ?_⟩
      calc
        Q.map (TopPair.Hom.snd e.hom x) =
            TopPair.Hom.fst e.hom (P.map x) := hHom x
        _ = TopPair.Hom.fst e.hom (TopPair.Hom.fst e.inv y) :=
          congrArg (TopPair.Hom.fst e.hom) hx
        _ = y := fst_inv_hom_id_apply e y
    · rintro ⟨x, hx⟩
      refine ⟨TopPair.Hom.snd e.inv x, ?_⟩
      calc
        P.map (TopPair.Hom.snd e.inv x) =
            TopPair.Hom.fst e.inv (Q.map x) := hInv x
        _ = TopPair.Hom.fst e.inv y :=
          congrArg (TopPair.Hom.fst e.inv) hx
  control_deformation_le := fun t y => by
    change d.control
        (TopPair.Hom.fst e.inv (TopPair.Hom.fst e.hom
          (d.deformation (t, TopPair.Hom.fst e.inv y)))) ≤
      d.control (TopPair.Hom.fst e.inv y)
    rw [fst_hom_inv_id_apply]
    exact d.control_deformation_le t (TopPair.Hom.fst e.inv y)
  endpoint_mem_range := fun y hy => by
    change d.control (TopPair.Hom.fst e.inv y) < 1 at hy
    rcases d.endpoint_mem_range (TopPair.Hom.fst e.inv y) hy with ⟨x, hx⟩
    refine ⟨TopPair.Hom.snd e.hom x, ?_⟩
    calc
      Q.map (TopPair.Hom.snd e.hom x) =
          TopPair.Hom.fst e.hom (P.map x) := by
        simpa only [TopCat.comp_app] using
          congrArg (fun k : P.snd ⟶ Q.fst => k x)
            (TopPair.Hom.w e.hom)
      _ = TopPair.Hom.fst e.hom
          (d.endpoint (TopPair.Hom.fst e.inv y)) :=
        congrArg (TopPair.Hom.fst e.hom) hx

/-- The transported control is the original control after the inverse
ambient isomorphism. -/
theorem ofIso_control {P Q : TopPair.{u}} (d : NDRData P) (e : P ≅ Q)
    (y : Q.fst) :
    (d.ofIso e).control y = d.control (TopPair.Hom.fst e.inv y) :=
  rfl

/-- The transported control cancels against the forward ambient isomorphism. -/
@[simp]
theorem ofIso_control_hom {P Q : TopPair.{u}}
    (d : NDRData P) (e : P ≅ Q) (x : P.fst) :
    (d.ofIso e).control (TopPair.Hom.fst e.hom x) = d.control x := by
  rw [ofIso_control, fst_hom_inv_id_apply]

/-- The transported endpoint is conjugation by the ambient isomorphism. -/
theorem ofIso_endpoint {P Q : TopPair.{u}} (d : NDRData P) (e : P ≅ Q)
    (y : Q.fst) :
    (d.ofIso e).endpoint y =
      TopPair.Hom.fst e.hom (d.endpoint (TopPair.Hom.fst e.inv y)) :=
  rfl

/-- The transported endpoint on a forward image is the forward image of the
original endpoint. -/
@[simp]
theorem ofIso_endpoint_hom {P Q : TopPair.{u}}
    (d : NDRData P) (e : P ≅ Q) (x : P.fst) :
    (d.ofIso e).endpoint (TopPair.Hom.fst e.hom x) =
      TopPair.Hom.fst e.hom (d.endpoint x) := by
  rw [ofIso_endpoint, fst_hom_inv_id_apply]

/-- The transported deformation is conjugation by the ambient isomorphism. -/
theorem ofIso_deformation {P Q : TopPair.{u}}
    (d : NDRData P) (e : P ≅ Q) (t : unitInterval) (y : Q.fst) :
    (d.ofIso e).deformation (t, y) =
      TopPair.Hom.fst e.hom
        (d.deformation (t, TopPair.Hom.fst e.inv y)) :=
  rfl

/-- The transported deformation on a forward image is the forward image of
the original deformation. -/
@[simp]
theorem ofIso_deformation_hom {P Q : TopPair.{u}}
    (d : NDRData P) (e : P ≅ Q) (t : unitInterval) (x : P.fst) :
    (d.ofIso e).deformation (t, TopPair.Hom.fst e.hom x) =
      TopPair.Hom.fst e.hom (d.deformation (t, x)) := by
  rw [ofIso_deformation, fst_hom_inv_id_apply]

end TopPair.NDRData
