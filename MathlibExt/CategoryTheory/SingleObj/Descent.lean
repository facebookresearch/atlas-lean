/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Logic.Function.Basic

/-!
# Difference functors and strict object adjustment

A functor from a groupoid to `SingleObj G` that kills the based endomorphisms
is determined by its actual connectors: its arrow values are the standard
difference formula. Connectors are required at every object of the groupoid
under consideration. An application to a disconnected family therefore uses
this result separately on its component categories.

For an object-injective functor `H`, inverse weights on its object image extend
by one outside that image. The stock `Functor.copyObj` construction adjusts an
existing functor using these weights. A proved difference formula on `H` makes
the restriction strictly constant, while arrows and original based End maps
outside the image are unchanged.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uC vC uD vD uG

namespace CategoryTheory.SingleObj

section Connectors

variable {C : Type uC} [Groupoid.{vC} C]
variable {G : Type uG} [Group G]

/-- The original based loop, evaluated by `F`, gives the difference formula.
The hypothesis concerns the original `End b`, whose multiplication is reversed
categorical composition, just as in `SingleObj G`. -/
theorem map_eq_difference_of_kills_mapEnd
    (F : C ⥤ SingleObj G) (b : C) (β : ∀ c : C, b ⟶ c)
    (hkill : ∀ e : End b, ((F.mapEnd b) e).asHom = (1 : G))
    {c d : C} (f : c ⟶ d) :
    (F.map f : G) = (F.map (β d) : G) * (F.map (β c) : G)⁻¹ := by
  have h := hkill (End.of (β c ≫ f ≫ inv (β d)))
  change (F.map (β c ≫ f ≫ inv (β d)) : G) = 1 at h
  simp only [F.map_comp, F.map_inv, comp_as_mul, inv_as_inv, mul_assoc] at h
  apply eq_mul_inv_iff_mul_eq.mpr
  have hc := congrArg (fun g : G => (F.map (β d) : G) * g) h
  simpa only [← mul_assoc, mul_inv_cancel, one_mul, mul_one] using hc

/-- Killing the original based End group identifies `F` with the stock
difference functor of its connector values, as an equality of functors. -/
theorem eq_differenceFunctor_of_kills_mapEnd
    (F : C ⥤ SingleObj G) (b : C) (β : ∀ c : C, b ⟶ c)
    (hkill : ∀ e : End b, ((F.mapEnd b) e).asHom = (1 : G)) :
    F = differenceFunctor (fun c : C => (F.map (β c) : G)) := by
  apply Functor.hext (fun _ => Subsingleton.elim _ _)
  intro c d f
  apply heq_of_eq
  change (F.map f : G) = (F.map (β d) : G) * (F.map (β c) : G)⁻¹
  exact map_eq_difference_of_kills_mapEnd F b β hkill f

/-- Two original functors with the same based End map are related
by the computed connector weights. The categorical and End multiplication
orders are retained, without a commutativity assumption on G. -/
theorem map_eq_conjugate_of_eq_mapEnd
    (F K : C ⥤ SingleObj G) (b : C) (β : ∀ c : C, b ⟶ c)
    (heq : ∀ e : End b, (F.map e.asHom : G) = (K.map e.asHom : G))
    {c d : C} (f : c ⟶ d) :
    (F.map f : G) = ((F.map (β d) : G) * (K.map (β d) : G)⁻¹) *
      (K.map f : G) * (((F.map (β c) : G) * (K.map (β c) : G)⁻¹)⁻¹) := by
  apply eq_mul_inv_iff_mul_eq.mpr
  have h := heq (End.of (β c ≫ f ≫ inv (β d)))
  change (F.map (β c ≫ f ≫ inv (β d)) : G) =
    (K.map (β c ≫ f ≫ inv (β d)) : G) at h
  simp only [Functor.map_comp, Functor.map_inv, comp_as_mul, inv_as_inv,
    mul_assoc] at h
  have hc := congrArg (fun z : G => (F.map (β d) : G) * z) h
  have hbase : (F.map f : G) * (F.map (β c) : G) =
      (((F.map (β d) : G) * (K.map (β d) : G)⁻¹) * (K.map f : G)) *
        (K.map (β c) : G) := by
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hc
  have hr := mul_inv_eq_of_eq_mul hbase
  simpa only [← mul_assoc] using hr

end Connectors

section ObjectAdjustment

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {G : Type uG} [Group G]

/-- The actual inverse weights, extended by one off the object image of `H`. -/
def objectAdjustmentWeight (H : C ⥤ D) (w : C → G) : D → G :=
  Function.extend H.obj (fun c => (w c)⁻¹) (fun _ => 1)

/-- Injectivity on objects gives the exact prescribed inverse weight on `H`. -/
theorem objectAdjustmentWeight_obj (H : C ⥤ D) (w : C → G)
    (hH : Function.Injective H.obj) (c : C) :
    objectAdjustmentWeight H w (H.obj c) = (w c)⁻¹ :=
  hH.extend_apply (fun c => (w c)⁻¹) (fun _ => 1) c

/-- Every object outside the original image has identity adjustment weight. -/
theorem objectAdjustmentWeight_of_not_mem_range (H : C ⥤ D) (w : C → G)
    (d : D) (hd : d ∉ Set.range H.obj) :
    objectAdjustmentWeight H w d = 1 :=
  Function.extend_apply' (fun c => (w c)⁻¹) (fun _ => 1) d hd

/-- The extended weight is the actual morphism representing the object
isomorphism used by the stock copy construction. -/
def objectAdjustmentIso (H : C ⥤ D) (F : D ⥤ SingleObj G) (w : C → G) (d : D) :
    F.obj d ≅ star G :=
  asIso (show F.obj d ⟶ star G from objectAdjustmentWeight H w d)

/-- Object adjustment of the existing functor by its extended inverse weights.
Functoriality is supplied by `Functor.copyObj`. -/
def objectAdjustment (H : C ⥤ D) (F : D ⥤ SingleObj G) (w : C → G) :
    D ⥤ SingleObj G :=
  F.copyObj (fun _ => star G) (objectAdjustmentIso H F w)

/-- The original functor and its adjustment are compared by the stock
`Functor.isoCopyObj` natural isomorphism. -/
def isoObjectAdjustment (H : C ⥤ D) (F : D ⥤ SingleObj G) (w : C → G) :
    F ≅ objectAdjustment H F w :=
  F.isoCopyObj (fun _ => star G) (objectAdjustmentIso H F w)

/-- Every adjusted object is the actual stock one-object target. -/
@[simp]
theorem objectAdjustment_obj (H : C ⥤ D) (F : D ⥤ SingleObj G) (w : C → G) (d : D) :
    (objectAdjustment H F w).obj d = star G :=
  rfl

/-- In the original reversed SingleObj composition, copying objects gives
`eta(target) * F(f) * inverse(eta(source))`. -/
theorem objectAdjustment_map (H : C ⥤ D) (F : D ⥤ SingleObj G) (w : C → G)
    {d d' : D} (f : d ⟶ d') :
    ((objectAdjustment H F w).map f : G) =
      objectAdjustmentWeight H w d' * (F.map f : G) *
        (objectAdjustmentWeight H w d)⁻¹ := by
  change (objectAdjustmentIso H F w d').hom * (F.map f : G) *
    (objectAdjustmentIso H F w d).inv = _
  simp only [objectAdjustmentIso, asIso_hom, asIso_inv, inv_as_inv]

/-- The comparison component is exactly the original extended inverse weight. -/
theorem isoObjectAdjustment_hom_app (H : C ⥤ D) (F : D ⥤ SingleObj G) (w : C → G)
    (d : D) :
    ((isoObjectAdjustment H F w).hom.app d : G) = objectAdjustmentWeight H w d := by
  change (objectAdjustmentIso H F w d).hom = _
  exact asIso_hom _

/-- The actual difference formula cancels on every arrow of `H`. No fullness
or faithfulness of `H` is used. -/
theorem objectAdjustment_map_map (H : C ⥤ D) (F : D ⥤ SingleObj G) (w : C → G)
    (hH : Function.Injective H.obj)
    (hformula : ∀ {c d : C} (f : c ⟶ d),
      (F.map (H.map f) : G) = w d * (w c)⁻¹)
    {c d : C} (f : c ⟶ d) :
    ((objectAdjustment H F w).map (H.map f) : G) = 1 := by
  rw [objectAdjustment_map, objectAdjustmentWeight_obj H w hH d,
    objectAdjustmentWeight_obj H w hH c, hformula f]
  simp only [inv_inv, ← mul_assoc, inv_mul_cancel, one_mul]

/-- The SAME computed object adjustment can make a restriction
equal to an arbitrary existing one-object functor. Only the actual
conjugacy equation and injective original object inclusion are required. -/
theorem comp_objectAdjustment_eq
    (H : C ⥤ D) (F : D ⥤ SingleObj G) (K : C ⥤ SingleObj G) (w : C → G)
    (hH : Function.Injective H.obj)
    (hformula : ∀ {c d : C} (f : c ⟶ d),
      (F.map (H.map f) : G) = w d * (K.map f : G) * (w c)⁻¹) :
    H ⋙ objectAdjustment H F w = K := by
  apply Functor.hext (fun _ => Subsingleton.elim _ _)
  intro c d f
  apply heq_of_eq
  change ((objectAdjustment H F w).map (H.map f) : G) = (K.map f : G)
  rw [objectAdjustment_map, objectAdjustmentWeight_obj H w hH d,
    objectAdjustmentWeight_obj H w hH c, hformula f]
  calc
    (w d)⁻¹ * (w d * (K.map f : G) * (w c)⁻¹) * ((w c)⁻¹)⁻¹ =
        (((w d)⁻¹ * w d) * (K.map f : G)) * ((w c)⁻¹ * w c) := by
      simp only [inv_inv, mul_assoc]
    _ = (K.map f : G) := by simp only [inv_mul_cancel, one_mul, mul_one]

/-- The adjusted restriction is strictly the actual constant functor, with
equality on both its objects and its arrows. -/
theorem comp_objectAdjustment_eq_const (H : C ⥤ D) (F : D ⥤ SingleObj G) (w : C → G)
    (hH : Function.Injective H.obj)
    (hformula : ∀ {c d : C} (f : c ⟶ d),
      (F.map (H.map f) : G) = w d * (w c)⁻¹) :
    H ⋙ objectAdjustment H F w = (Functor.const C).obj (star G) := by
  refine Functor.hext (F := H ⋙ objectAdjustment H F w)
    (G := (Functor.const C).obj (star G)) (fun _ => rfl) ?_
  intro c d f
  apply heq_of_eq
  change ((objectAdjustment H F w).map (H.map f) : G) = 1
  exact objectAdjustment_map_map H F w hH hformula f

/-- Arrows with both endpoints outside the object image are unchanged. -/
theorem objectAdjustment_map_of_not_mem_range
    (H : C ⥤ D) (F : D ⥤ SingleObj G) (w : C → G)
    {d d' : D} (f : d ⟶ d') (hd : d ∉ Set.range H.obj) (hd' : d' ∉ Set.range H.obj) :
    ((objectAdjustment H F w).map f : G) = (F.map f : G) := by
  rw [objectAdjustment_map, objectAdjustmentWeight_of_not_mem_range H w d' hd',
    objectAdjustmentWeight_of_not_mem_range H w d hd]
  simp only [inv_one, one_mul, mul_one]

/-- At every original outside object, the original based End map has the same
value in `G`; its original reversed End multiplication is retained. -/
theorem objectAdjustment_mapEnd_of_not_mem_range
    (H : C ⥤ D) (F : D ⥤ SingleObj G) (w : C → G)
    (d : D) (hd : d ∉ Set.range H.obj) (e : End d) :
    (((objectAdjustment H F w).mapEnd d) e).asHom = ((F.mapEnd d) e).asHom := by
  change ((objectAdjustment H F w).map e.asHom : G) = (F.map e.asHom : G)
  exact objectAdjustment_map_of_not_mem_range H F w e.asHom hd hd

/-- An object-injective overlap with a proved difference formula admits an
actual strict adjustment, naturally isomorphic to the original functor. Both
outside arrows and the original based End values are preserved. -/
theorem exists_strictObjectAdjustment
    (H : C ⥤ D) (F : D ⥤ SingleObj G) (w : C → G)
    (hH : Function.Injective H.obj)
    (hformula : ∀ {c d : C} (f : c ⟶ d),
      (F.map (H.map f) : G) = w d * (w c)⁻¹) :
    ∃ F' : D ⥤ SingleObj G,
      Nonempty (F ≅ F') ∧ H ⋙ F' = (Functor.const C).obj (star G) ∧
        (∀ {d d' : D} (f : d ⟶ d'), d ∉ Set.range H.obj → d' ∉ Set.range H.obj →
          (F'.map f : G) = (F.map f : G)) ∧
        (∀ (d : D), d ∉ Set.range H.obj → ∀ e : End d,
          ((F'.mapEnd d) e).asHom = ((F.mapEnd d) e).asHom) := by
  refine ⟨objectAdjustment H F w, ⟨isoObjectAdjustment H F w⟩,
    comp_objectAdjustment_eq_const H F w hH hformula, ?_, ?_⟩
  · intro d d' f hd hd'
    exact objectAdjustment_map_of_not_mem_range H F w f hd hd'
  · intro d hd e
    exact objectAdjustment_mapEnd_of_not_mem_range H F w d hd e

end ObjectAdjustment

end CategoryTheory.SingleObj

end
