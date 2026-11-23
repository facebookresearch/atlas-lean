/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.ActionLocalization
public import MathlibExt.CategoryTheory.Limits.Shapes.CoreBiproductMonoidal
public import MathlibExt.CategoryTheory.FiberedCategory.CofiberedCommaAdjunction
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Denominator projection and fixed-denominator fibers

A monoidal action localization retains a positive object and its denominator.
The denominator projection maps it to the corresponding self-action
category. For biproduct core actions, represented lifts give this
projection a cofibered structure.

The fixed-denominator strict fiber is equivalent to the original acted-on
category. Its comma retraction and inclusion form an adjunction, with
explicit object, arrow, unit, and counit formulas.
-/

@[expose] public section

universe uS vS uX vX u v

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open MonoidalCategory
open scoped MonoidalCategory CategoryTheory.MonoidalCategory.MonoidalLeftAction


namespace CategoryTheory.MonoidalActionCategory

private theorem actualActionIso_cancel
    {S : Type uS} [Category.{vS} S] [MonoidalCategory S]
    {Y : Type uX} [Category.{vX} Y] [MonoidalLeftAction S Y]
    {T U : S} (e : T ≅ U) (x : Y) {z : Y} (f : T ⊙ₗ x ⟶ z) :
    e.hom ⊵ₗ x ≫ e.inv ⊵ₗ x ≫ f = f := by
  calc
    e.hom ⊵ₗ x ≫ e.inv ⊵ₗ x ≫ f = (e.hom ⊵ₗ x ≫ e.inv ⊵ₗ x) ≫ f :=
      (Category.assoc _ _ _).symm
    _ = (e.hom ≫ e.inv) ⊵ₗ x ≫ f :=
      congrArg (fun k => k ≫ f) (MonoidalLeftAction.comp_actionHomLeft e.hom e.inv x).symm
    _ = 𝟙 (T ⊙ₗ x) ≫ f := by rw [e.hom_inv_id, MonoidalLeftAction.id_actionHomLeft]
    _ = f := Category.id_comp f

private theorem actualHomLift_of_map_eq
    {B : Type uX} [Category.{vX} B] {A : Type uS} [Category.{vS} A]
    (p : B ⥤ A) {a b : B} (f : p.obj a ⟶ p.obj b) (phi : a ⟶ b)
    (h : p.map phi = f) : Functor.IsHomLift p f phi :=
  h ▸ Functor.IsHomLift.map (p := p) phi

private theorem actualHomLift_map_heq
    {B : Type uX} [Category.{vX} B] {A : Type uS} [Category.{vS} A]
    (p : B ⥤ A) {R S : A} {a b : B} (f : R ⟶ S) (phi : a ⟶ b)
    (h : Functor.IsHomLift p f phi) : HEq (p.map phi) f := by
  cases h
  rfl

section Projection

variable {S : Type uS} [Category.{vS} S] [MonoidalCategory S]
  {X : Type uX} [Category.{vX} X] [MonoidalLeftAction S X]

attribute [local instance] diagonalAction

/-- The original denominator, as an object of the one-coordinate action category. -/
def denominatorObject (a : SInverse S X) : MonoidalActionCategory S S :=
  ⟨a.of.2⟩

/-- Project the actual stabilized arrow without changing its stabilizer. -/
def denominatorRawMap {a b : SInverse S X} (r : RawHom a b) :
    RawHom (denominatorObject a) (denominatorObject b) where
  stabilizer := r.stabilizer
  hom := r.hom.2

private theorem denominatorRawMap_rel {a b : SInverse S X} {r s : RawHom a b}
    (h : r.Rel s) : (denominatorRawMap r).Rel (denominatorRawMap s) := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, ?_⟩
  exact congrArg (fun k : (r.stabilizer ⊙ₗ a.of) ⟶ b.of => k.2) he

/-- The actual denominator projection from the existing action localization. -/
def denominatorProjection (S : Type uS) [Category.{vS} S] [MonoidalCategory S]
    (X : Type uX) [Category.{vX} X] [MonoidalLeftAction S X] :
    SInverse S X ⥤ MonoidalActionCategory S S where
  obj := denominatorObject
  map f := _root_.Quotient.map denominatorRawMap (by
    intro _ _ h
    exact denominatorRawMap_rel h) f
  map_id a := rfl
  map_comp f g := by
    refine _root_.Quotient.inductionOn₂ f g ?_
    intro r s
    rfl

/-- The projection retains the literal denominator coordinate. -/
theorem denominatorProjection_obj (a : SInverse S X) :
    ((denominatorProjection S X).obj a).of = a.of.2 := rfl

/-- On a represented arrow, the projection is its original second component. -/
theorem denominatorProjection_map_mk {a b : SInverse S X} (r : RawHom a b) :
    (denominatorProjection S X).map (Hom.mk r) = Hom.mk (denominatorRawMap r) := rfl

end Projection

section Initial

variable {S : Type uS} [Groupoid.{vS} S] [MonoidalCategory S]

/-- The original right unitor supplies the arrow from the tensor-unit object. -/
def selfUnitArrow (a : MonoidalActionCategory S S) :
    (⟨𝟙_ S⟩ : MonoidalActionCategory S S) ⟶ a :=
  Hom.mk { stabilizer := a.of, hom := (ρ_ a.of).hom }

/-- The tensor unit is initial in the actual one-coordinate translation category. -/
noncomputable def selfUnitIsInitial :
    IsInitial (⟨𝟙_ S⟩ : MonoidalActionCategory S S) := by
  refine IsInitial.ofUniqueHom selfUnitArrow ?_
  intro a f
  refine _root_.Quotient.inductionOn f ?_
  intro r
  change Hom.mk r =
    Hom.mk ({ stabilizer := a.of, hom := (ρ_ a.of).hom } :
      RawHom (⟨𝟙_ S⟩ : MonoidalActionCategory S S) a)
  apply (Hom.mk_eq_mk_iff _ _).2
  let e : r.stabilizer ≅ a.of := (ρ_ r.stabilizer).symm ≪≫ asIso r.hom
  refine ⟨e, ?_⟩
  change e.hom ▷ (𝟙_ S) ≫ (ρ_ a.of).hom = r.hom
  rw [MonoidalCategory.rightUnitor_naturality]
  change (ρ_ r.stabilizer).hom ≫ ((ρ_ r.stabilizer).inv ≫ r.hom) = r.hom
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end Initial

end CategoryTheory.MonoidalActionCategory

end


noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open MonoidalCategory
open scoped MonoidalCategory CategoryTheory.MonoidalCategory.MonoidalLeftAction


namespace CategoryTheory.MonoidalActionCategory

variable {S : Type uS} [Category.{vS} S] [MonoidalCategory S]
  {X : Type uX} [Category.{vX} X] [MonoidalLeftAction S X]

attribute [local instance] diagonalAction

/-- Lift a represented base arrow by translating its original positive coordinate. -/
def denominatorLiftObject (a : SInverse S X) {s : S}
    (r : RawHom (denominatorObject a) (⟨s⟩ : MonoidalActionCategory S S)) :
    SInverse S X :=
  ⟨(r.stabilizer ⊙ₗ a.of.1, s)⟩

/-- The actual lift has identity positive component and the original base component. -/
def denominatorLiftRaw (a : SInverse S X) {s : S}
    (r : RawHom (denominatorObject a) (⟨s⟩ : MonoidalActionCategory S S)) :
    RawHom a (denominatorLiftObject a r) where
  stabilizer := r.stabilizer
  hom := (𝟙 (r.stabilizer ⊙ₗ a.of.1), r.hom)

/-- Its target projects to the same literal given base object. -/
theorem denominatorLiftObject_projection (a : SInverse S X) {s : S}
    (r : RawHom (denominatorObject a) (⟨s⟩ : MonoidalActionCategory S S)) :
    (denominatorProjection S X).obj (denominatorLiftObject a r) =
      (⟨s⟩ : MonoidalActionCategory S S) := rfl

/-- The represented lift projects to the original base representative. -/
theorem denominatorLiftRaw_projection (a : SInverse S X) {s : S}
    (r : RawHom (denominatorObject a) (⟨s⟩ : MonoidalActionCategory S S)) :
    denominatorRawMap (denominatorLiftRaw a r) = r := rfl

/-- A genuine base composition relation supplies a factor through the chosen raw lift.
No positive component is assumed invertible. The original later stabilizer is retained. -/
theorem denominatorLift_exists_raw_factor {a z : SInverse S X} {s : S}
    (r : RawHom (denominatorObject a) (⟨s⟩ : MonoidalActionCategory S S))
    (q : RawHom (⟨s⟩ : MonoidalActionCategory S S) (denominatorObject z))
    (ψ : RawHom a z) (h : (denominatorRawMap ψ).Rel (r.comp q)) :
    ∃ k : RawHom (denominatorLiftObject a r) z,
      denominatorRawMap k = q ∧ ψ.Rel ((denominatorLiftRaw a r).comp k) := by
  change ∃ e : ψ.stabilizer ≅ q.stabilizer ⊗ r.stabilizer,
    e.hom ▷ a.of.2 ≫
      ((α_ q.stabilizer r.stabilizer a.of.2).hom ≫ q.stabilizer ◁ r.hom ≫ q.hom) =
      ψ.hom.2 at h
  obtain ⟨e, he⟩ := h
  let k : RawHom (denominatorLiftObject a r) z :=
    { stabilizer := q.stabilizer
      hom :=
        ((αₗ q.stabilizer r.stabilizer a.of.1).inv ≫
          (e.inv ⊵ₗ a.of.1) ≫ ψ.hom.1, q.hom) }
  refine ⟨k, rfl, e, ?_⟩
  apply Prod.ext
  · change (e.hom ⊵ₗ a.of.1) ≫
      (αₗ q.stabilizer r.stabilizer a.of.1).hom ≫
      (q.stabilizer ⊴ₗ (𝟙 (r.stabilizer ⊙ₗ a.of.1))) ≫
      (αₗ q.stabilizer r.stabilizer a.of.1).inv ≫
      (e.inv ⊵ₗ a.of.1) ≫ ψ.hom.1 = ψ.hom.1
    simp only [MonoidalLeftAction.actionHomRight_id, Category.id_comp,
      Iso.hom_inv_id_assoc]
    exact actualActionIso_cancel e a.of.1 ψ.hom.1
  · exact he
/-- Every actual quotient arrow above a composite factors through the actual lift.
This proves the existence part of cocartesianness; uniqueness is a separate next leaf. -/
theorem denominatorLift_exists_factor {a z : SInverse S X} {s : S}
    (r : RawHom (denominatorObject a) (⟨s⟩ : MonoidalActionCategory S S))
    (g : (⟨s⟩ : MonoidalActionCategory S S) ⟶ (denominatorProjection S X).obj z)
    (ψ : a ⟶ z)
    (h : (denominatorProjection S X).map ψ = Hom.mk r ≫ g) :
    ∃ k : denominatorLiftObject a r ⟶ z,
      (denominatorProjection S X).map k = g ∧ Hom.mk (denominatorLiftRaw a r) ≫ k = ψ := by
  obtain ⟨q, rfl⟩ := Hom.exists_rep g
  obtain ⟨w, rfl⟩ := Hom.exists_rep ψ
  have hclass : Hom.mk (denominatorRawMap w) = Hom.mk (r.comp q) :=
    (denominatorProjection_map_mk w).symm.trans (h.trans (Hom.mk_comp r q))
  have hraw : (denominatorRawMap w).Rel (r.comp q) := (Hom.mk_eq_mk_iff _ _).mp hclass
  obtain ⟨k, hk, hrel⟩ := denominatorLift_exists_raw_factor r q w hraw
  refine ⟨Hom.mk k, ?_, ?_⟩
  · change Hom.mk (denominatorRawMap k) = Hom.mk q
    exact congrArg Hom.mk hk
  · exact (Hom.mk_comp (denominatorLiftRaw a r) k).trans (_root_.Quotient.sound hrel).symm

end CategoryTheory.MonoidalActionCategory

end


noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open MonoidalCategory
open scoped MonoidalCategory CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace CategoryTheory.MonoidalActionCategory

section GenericCancellation

variable {S : Type uS} [Groupoid.{vS} S] [MonoidalCategory S]
  {X : Type uX} [Category.{vX} X] [MonoidalLeftAction S X]

attribute [local instance] diagonalAction

private theorem denominatorLift_raw_cancel {a z : SInverse S X} {s : S}
    (r : RawHom (denominatorObject a) (⟨s⟩ : MonoidalActionCategory S S))
    (k l : RawHom (denominatorLiftObject a r) z)
    (hFaithful : (MonoidalCategory.tensorRight a.of.2).Faithful)
    (hDen : (denominatorRawMap k).Rel (denominatorRawMap l))
    (hComp : ((denominatorLiftRaw a r).comp k).Rel ((denominatorLiftRaw a r).comp l)) :
    k.Rel l := by
  change ∃ δ : k.stabilizer ≅ l.stabilizer,
    δ.hom ▷ s ≫ l.hom.2 = k.hom.2 at hDen
  dsimp only [RawHom.Rel, RawHom.comp, denominatorLiftRaw, denominatorLiftObject] at hComp
  obtain ⟨δ, hδ⟩ := hDen
  obtain ⟨ε, hε⟩ := hComp
  let K := k.stabilizer
  let L := l.stabilizer
  let R := r.stabilizer
  let D := a.of.2
  let θ : K ⊗ R ⟶ L ⊗ R := δ.hom ⊗ₘ 𝟙 R
  let kd : K ⊗ s ⟶ z.of.2 := k.hom.2
  let ld : L ⊗ s ⟶ z.of.2 := l.hom.2
  let ak : (K ⊗ R) ⊗ D ⟶ K ⊗ (R ⊗ D) := (α_ K R D).hom
  let al : (L ⊗ R) ⊗ D ⟶ L ⊗ (R ⊗ D) := (α_ L R D).hom
  let kr : K ⊗ (R ⊗ D) ⟶ K ⊗ s := K ◁ r.hom
  let lr : L ⊗ (R ⊗ D) ⟶ L ⊗ s := L ◁ r.hom
  let δs : K ⊗ s ⟶ L ⊗ s := δ.hom ▷ s
  let εD : (K ⊗ R) ⊗ D ⟶ (L ⊗ R) ⊗ D := ε.hom ▷ D
  let θD : (K ⊗ R) ⊗ D ⟶ (L ⊗ R) ⊗ D := θ ▷ D
  have hd := congrArg _root_.Prod.snd hε
  change εD ≫ al ≫ lr ≫ ld = ak ≫ kr ≫ kd at hd
  have hkd : δs ≫ ld = kd := hδ
  have hd' : εD ≫ al ≫ lr ≫ ld = ak ≫ kr ≫ δs ≫ ld :=
    hd.trans (congrArg (fun d : K ⊗ s ⟶ z.of.2 => ak ≫ kr ≫ d) hkd.symm)
  let tail : (L ⊗ R) ⊗ D ⟶ L ⊗ s := al ≫ lr
  let rhs : (K ⊗ R) ⊗ D ⟶ L ⊗ s := ak ≫ kr ≫ δs
  have hdc : (εD ≫ tail) ≫ ld = rhs ≫ ld := by
    simpa only [tail, rhs, Category.assoc] using hd'
  have hd0 : εD ≫ tail = rhs := (cancel_mono ld).mp hdc
  have hAssocRaw := MonoidalCategory.associator_naturality
    δ.hom (𝟙 R) (𝟙 D)
  have hLeft : θ ⊗ₘ 𝟙 D = θD := MonoidalCategory.tensorHom_id θ D
  have hRight : δ.hom ⊗ₘ (𝟙 R ⊗ₘ 𝟙 D) = δ.hom ▷ (R ⊗ D) :=
    (congrArg (fun d : R ⊗ D ⟶ R ⊗ D => δ.hom ⊗ₘ d)
      (MonoidalCategory.id_tensorHom_id R D)).trans
        (MonoidalCategory.tensorHom_id δ.hom (R ⊗ D))
  have hAssoc : θD ≫ al = ak ≫ δ.hom ▷ (R ⊗ D) :=
    (congrArg (fun d => d ≫ al) hLeft.symm).trans
      (hAssocRaw.trans (congrArg (fun d => ak ≫ d) hRight))
  have hExchange : δ.hom ▷ (R ⊗ D) ≫ lr = kr ≫ δs :=
    (MonoidalCategory.whisker_exchange δ.hom r.hom).symm
  have hNat : θD ≫ tail = rhs := by
    calc
      θD ≫ tail = (θD ≫ al) ≫ lr := (Category.assoc θD al lr).symm
      _ = (ak ≫ δ.hom ▷ (R ⊗ D)) ≫ lr := congrArg (fun d => d ≫ lr) hAssoc
      _ = ak ≫ (δ.hom ▷ (R ⊗ D) ≫ lr) := Category.assoc _ _ _
      _ = ak ≫ (kr ≫ δs) := congrArg (fun d => ak ≫ d) hExchange
      _ = rhs := rfl
  have hWhisker : εD = θD := (cancel_mono tail).mp (hd0.trans hNat.symm)
  have hεhom : ε.hom = θ := hFaithful.map_injective hWhisker
  let px := a.of.1
  let kp : K ⊙ₗ (R ⊙ₗ px) ⟶ z.of.1 := k.hom.1
  let lp : L ⊙ₗ (R ⊙ₗ px) ⟶ z.of.1 := l.hom.1
  let bxk : (K ⊗ R) ⊙ₗ px ⟶ K ⊙ₗ (R ⊙ₗ px) := (αₗ K R px).hom
  let bxl : (L ⊗ R) ⊙ₗ px ⟶ L ⊙ₗ (R ⊙ₗ px) := (αₗ L R px).hom
  let δx : K ⊙ₗ (R ⊙ₗ px) ⟶ L ⊙ₗ (R ⊙ₗ px) := δ.hom ⊵ₗ (R ⊙ₗ px)
  have hp := congrArg _root_.Prod.fst hε
  change ε.hom ⊵ₗ px ≫ bxl ≫ L ⊴ₗ 𝟙 (R ⊙ₗ px) ≫ lp =
    bxk ≫ K ⊴ₗ 𝟙 (R ⊙ₗ px) ≫ kp at hp
  have hp0 : ε.hom ⊵ₗ px ≫ bxl ≫ lp = bxk ≫ kp := by
    simpa only [MonoidalLeftAction.actionHomRight_id, Category.id_comp] using hp
  have hθ : ε.hom ⊵ₗ px = θ ⊵ₗ px := congrArg (fun d => d ⊵ₗ px) hεhom
  have hAction : θ ⊵ₗ px ≫ bxl = bxk ≫ δx := by
    simpa only [MonoidalLeftAction.actionHom_def, MonoidalLeftAction.actionHomRight_id,
      MonoidalLeftAction.id_actionHomLeft, Category.id_comp, Category.comp_id] using
      (MonoidalLeftAction.actionAssocIso_hom_naturality δ.hom (𝟙 R) (𝟙 px))
  have hp1 : (θ ⊵ₗ px ≫ bxl) ≫ lp = bxk ≫ kp :=
    ((Category.assoc (θ ⊵ₗ px) bxl lp).trans
      ((congrArg (fun d => d ≫ bxl ≫ lp) hθ.symm).trans hp0))
  have hp2 : (bxk ≫ δx) ≫ lp = bxk ≫ kp :=
    (congrArg (fun d => d ≫ lp) hAction.symm).trans hp1
  have hp3 : bxk ≫ (δx ≫ lp) = bxk ≫ kp :=
    (Category.assoc bxk δx lp).symm.trans hp2
  have hPositive : δx ≫ lp = kp := (cancel_epi bxk).mp hp3
  refine ⟨δ, ?_⟩
  apply Prod.ext
  · exact hPositive
  · exact hδ

end GenericCancellation

section ConcreteCore

open scoped CategoryTheory.Limits.CoreBiprodMonoidal

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

private theorem coreRightTensor_faithful (T : Core C) :
    (MonoidalCategory.tensorRight T).Faithful := by
  constructor
  intro A B f g h
  apply Core.hom_ext
  have hMap := congrArg (fun k : A ⊗ T ⟶ B ⊗ T => k.iso.hom) h
  change biprod.map f.iso.hom (𝟙 T.of) = biprod.map g.iso.hom (𝟙 T.of) at hMap
  have hComponent := congrArg
    (fun k : A.of ⊞ T.of ⟶ B.of ⊞ T.of =>
      (biprod.inl : A.of ⟶ A.of ⊞ T.of) ≫ k ≫ (biprod.fst : B.of ⊞ T.of ⟶ B.of)) hMap
  simpa only [Category.assoc, biprod.map_fst, biprod.inl_fst_assoc, Category.id_comp]
    using hComponent

variable {X : Type uX} [Category.{vX} X] [MonoidalLeftAction (Core C) X]

attribute [local instance] diagonalAction

/-- Actual core translation faithfulness makes the canonical lift left-cancellative
among maps with the same actual denominator projection. -/
theorem denominatorLift_cancel {a z : SInverse (Core C) X} {s : Core C}
    (r : RawHom (denominatorObject a) (⟨s⟩ : MonoidalActionCategory (Core C) (Core C)))
    (k l : denominatorLiftObject a r ⟶ z)
    (hDen : (denominatorProjection (Core C) X).map k =
      (denominatorProjection (Core C) X).map l)
    (hComp : Hom.mk (denominatorLiftRaw a r) ≫ k = Hom.mk (denominatorLiftRaw a r) ≫ l) :
    k = l := by
  revert hDen hComp
  refine _root_.Quotient.inductionOn₂ k l ?_
  intro k l hDen hComp
  apply _root_.Quotient.sound
  apply denominatorLift_raw_cancel r k l (coreRightTensor_faithful a.of.2)
  · apply (Hom.mk_eq_mk_iff _ _).mp
    exact ((denominatorProjection_map_mk k).symm.trans hDen).trans
      (denominatorProjection_map_mk l)
  · apply (Hom.mk_eq_mk_iff _ _).mp
    exact ((Hom.mk_comp (denominatorLiftRaw a r) k).symm.trans hComp).trans
      (Hom.mk_comp (denominatorLiftRaw a r) l)

/-- The actual canonical lift is strongly cocartesian for the denominator projection. -/
theorem denominatorLift_isStronglyCocartesian (a : SInverse (Core C) X) {s : Core C}
    (r : RawHom (denominatorObject a) (⟨s⟩ : MonoidalActionCategory (Core C) (Core C))) :
    (denominatorProjection (Core C) X).IsStronglyCocartesian
      (Hom.mk r) (Hom.mk (denominatorLiftRaw a r)) := by
  let p := denominatorProjection (Core C) X
  let b := denominatorLiftObject a r
  let phi : a ⟶ b := Hom.mk (denominatorLiftRaw a r)
  let f : p.obj a ⟶ p.obj b := Hom.mk r
  have hMap : p.map phi = f := (denominatorProjection_map_mk _).trans
    (congrArg Hom.mk (denominatorLiftRaw_projection a r))
  have hLift : Functor.IsHomLift p f phi := actualHomLift_of_map_eq p f phi hMap
  refine
    { toIsHomLift := hLift
      universal_property' := ?_ }
  intro z g ψ hψ
  have hp : p.map ψ = Hom.mk r ≫ g := eq_of_heq (actualHomLift_map_heq p _ ψ hψ)
  obtain ⟨k, hk, hcomp⟩ := denominatorLift_exists_factor r g ψ hp
  refine ⟨k, ⟨?_, hcomp⟩, ?_⟩
  · let g0 : p.obj b ⟶ p.obj z := g
    have hEq : p.map k = g0 := hk
    exact actualHomLift_of_map_eq p g0 k hEq
  · rintro k' ⟨hLift', hcomp'⟩
    apply denominatorLift_cancel r k' k
    · have hk' : p.map k' = g := eq_of_heq (actualHomLift_map_heq p g k' hLift')
      exact hk'.trans hk.symm
    · exact hcomp'.trans hcomp.symm
/-- The actual positive-first action localization is cofibered over its
one-coordinate translation category; no cofiberedness is a premise. -/
theorem denominatorProjection_isCofibered :
    (denominatorProjection (Core C) X).IsCofibered := by
  constructor
  intro a b f
  rcases b with ⟨s⟩
  obtain ⟨r, rfl⟩ := Hom.exists_rep f
  exact ⟨denominatorLiftObject a r, Hom.mk (denominatorLiftRaw a r),
    denominatorLift_isStronglyCocartesian a r⟩

end ConcreteCore

end CategoryTheory.MonoidalActionCategory

end


noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open MonoidalCategory
open scoped MonoidalCategory CategoryTheory.MonoidalCategory.MonoidalLeftAction
open scoped CategoryTheory.Limits.CoreBiprodMonoidal

namespace CategoryTheory.MonoidalActionCategory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
  {X : Type uX} [Category.{vX} X] [MonoidalLeftAction (Core C) X]

attribute [local instance] diagonalAction

/-- The actual positive-first pairs at the same given denominator. -/
def fixedDenominatorTotal (s : Core C) : X ⥤ SInverse (Core C) X :=
  ((𝟭 X).prod' ((CategoryTheory.Functor.const X).obj s)) ⋙
    MonoidalActionCategory.inclusion (Core C) (X × Core C)

/-- The represented original arrow at a fixed denominator. -/
def fixedDenominatorRawMap (s : Core C) {x y : X} (f : x ⟶ y) :
    RawHom ((fixedDenominatorTotal s).obj x) ((fixedDenominatorTotal s).obj y) :=
  RawHom.ofMap (S := Core C) (x := (x, s)) (y := (y, s)) (f, 𝟙 s)

/-- Projection of a product inclusion keeps the original denominator arrow. -/
theorem denominatorProjection_pairMap {x y : X} {s t : Core C}
    (f : x ⟶ y) (g : s ⟶ t) :
    (denominatorProjection (Core C) X).map
      ((MonoidalActionCategory.inclusion (Core C) (X × Core C)).map
        (X := (x, s)) (Y := (y, t)) (f, g)) =
      (MonoidalActionCategory.inclusion (Core C) (Core C)).map (X := s) (Y := t) g := rfl
/-- The tensor-unit denominator gives exactly the existing positive inclusion. -/
theorem fixedDenominatorTotal_unit :
    fixedDenominatorTotal (X := X) (𝟙_ (Core C)) = SInverse.inclusion (Core C) X := rfl

/-- The actual strict fiber of the denominator projection at the given denominator. -/
abbrev denominatorFiber (s : Core C) :=
  CategoryTheory.Functor.Fiber (denominatorProjection (Core C) X)
    (⟨s⟩ : MonoidalActionCategory (Core C) (Core C))

private theorem fixedDenominatorTotal_lift (s : Core C) {x y : X} (f : x ⟶ y) :
    CategoryTheory.Functor.IsHomLift (denominatorProjection (Core C) X)
      (𝟙 (⟨s⟩ : MonoidalActionCategory (Core C) (Core C)))
      ((fixedDenominatorTotal s).map f) := by
  let p := denominatorProjection (Core C) X
  let phi : (fixedDenominatorTotal s).obj x ⟶ (fixedDenominatorTotal s).obj y :=
    (fixedDenominatorTotal s).map f
  let id0 : p.obj ((fixedDenominatorTotal s).obj x) ⟶
      p.obj ((fixedDenominatorTotal s).obj y) :=
    𝟙 (⟨s⟩ : MonoidalActionCategory (Core C) (Core C))
  have hm : p.map phi = id0 :=
    (denominatorProjection_pairMap f (𝟙 s)).trans
      ((MonoidalActionCategory.inclusion (Core C) (Core C)).map_id s)
  exact actualHomLift_of_map_eq p id0 phi hm
/-- Original positive objects/maps include in the literal fixed-denominator fiber. -/
def denominatorFiberFunctor (s : Core C) : X ⥤ denominatorFiber (X := X) s where
  obj x := ⟨(fixedDenominatorTotal s).obj x, rfl⟩
  map f := ⟨(fixedDenominatorTotal s).map f, by exact fixedDenominatorTotal_lift s f⟩
  map_id x := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact (fixedDenominatorTotal s).map_id x
  map_comp f g := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact (fixedDenominatorTotal s).map_comp f g
private theorem denominatorFiberFunctor_map_injective (s : Core C) {x y : X}
    (f g : x ⟶ y) (h : (denominatorFiberFunctor s).map f =
      (denominatorFiberFunctor s).map g) : f = g := by
  have ht := congrArg
    (fun k : (denominatorFiberFunctor s).obj x ⟶ (denominatorFiberFunctor s).obj y =>
      (CategoryTheory.Functor.Fiber.fiberInclusion :
        denominatorFiber (X := X) s ⥤ SInverse (Core C) X).map k) h
  change Hom.mk (fixedDenominatorRawMap s f) = Hom.mk (fixedDenominatorRawMap s g) at ht
  have hRaw := (Hom.mk_eq_mk_iff _ _).mp ht
  let qf : (𝟙_ (Core C)) ⊙ₗ (x, s) ⟶ (y, s) :=
    ((λₗ[Core C] x).hom ≫ f, (λ_ s).hom ≫ 𝟙 s)
  let qg : (𝟙_ (Core C)) ⊙ₗ (x, s) ⟶ (y, s) :=
    ((λₗ[Core C] x).hom ≫ g, (λ_ s).hom ≫ 𝟙 s)
  change ∃ e : (𝟙_ (Core C)) ≅ (𝟙_ (Core C)),
    e.hom ⊵ₗ (x, s) ≫ qg = qf at hRaw
  obtain ⟨e, he⟩ := hRaw
  have hd := congrArg _root_.Prod.snd he
  change e.hom ▷ s ≫ ((λ_ s).hom ≫ 𝟙 s) = (λ_ s).hom ≫ 𝟙 s at hd
  have hd0 : e.hom ▷ s ≫ (λ_ s).hom = (λ_ s).hom := by
    simpa only [Category.comp_id] using hd
  have hWhisker : e.hom ▷ s = 𝟙 ((𝟙_ (Core C)) ⊗ s) :=
    (cancel_mono (λ_ s).hom).mp (hd0.trans (Category.id_comp _).symm)
  have hIdentity : (MonoidalCategory.tensorRight s).map (𝟙 (𝟙_ (Core C))) =
      𝟙 ((𝟙_ (Core C)) ⊗ s) := (MonoidalCategory.tensorRight s).map_id _
  have heid : e.hom = 𝟙 (𝟙_ (Core C)) :=
    (coreRightTensor_faithful s).map_injective (hWhisker.trans hIdentity.symm)
  have hp := congrArg _root_.Prod.fst he
  change (e.hom ⊵ₗ x) ≫ (λₗ[Core C] x).hom ≫ g = (λₗ[Core C] x).hom ≫ f at hp
  have hActionId : e.hom ⊵ₗ x = 𝟙 ((𝟙_ (Core C)) ⊙ₗ x) :=
    (congrArg (fun j : (𝟙_ (Core C)) ⟶ (𝟙_ (Core C)) => j ⊵ₗ x) heid).trans
      (MonoidalLeftAction.id_actionHomLeft (𝟙_ (Core C)) x)
  rw [hActionId, Category.id_comp] at hp
  exact ((cancel_epi (λₗ[Core C] x).hom).mp hp).symm
private theorem denominatorFiberFunctor_map_surjective (s : Core C) {x y : X}
    (h : (denominatorFiberFunctor s).obj x ⟶ (denominatorFiberFunctor s).obj y) :
    ∃ f : x ⟶ y, (denominatorFiberFunctor s).map f = h := by
  let p := denominatorProjection (Core C) X
  let ψ : (fixedDenominatorTotal s).obj x ⟶ (fixedDenominatorTotal s).obj y := h.val
  have hLift : Functor.IsHomLift p
      (𝟙 (⟨s⟩ : MonoidalActionCategory (Core C) (Core C))) ψ := h.property
  have hm : p.map ψ = 𝟙 (⟨s⟩ : MonoidalActionCategory (Core C) (Core C)) :=
    eq_of_heq (actualHomLift_map_heq p _ ψ hLift)
  obtain ⟨r, hr⟩ := Hom.exists_rep ψ
  let rd : r.stabilizer ⊗ s ⟶ s := r.hom.2
  let rp : r.stabilizer ⊙ₗ x ⟶ y := r.hom.1
  let dr : RawHom (⟨s⟩ : MonoidalActionCategory (Core C) (Core C)) ⟨s⟩ :=
    ⟨r.stabilizer, rd⟩
  have hProjected : Hom.mk dr = p.map (Hom.mk r) := (denominatorProjection_map_mk r).symm
  have hClass : Hom.mk dr = Hom.mk (RawHom.id
      (⟨s⟩ : MonoidalActionCategory (Core C) (Core C))) :=
    hProjected.trans ((congrArg
      (fun k : (fixedDenominatorTotal s).obj x ⟶ (fixedDenominatorTotal s).obj y =>
        p.map k) hr).trans
        (hm.trans (Hom.mk_id (⟨s⟩ : MonoidalActionCategory (Core C) (Core C))).symm))
  have hRaw : dr.Rel (RawHom.id (⟨s⟩ : MonoidalActionCategory (Core C) (Core C))) :=
    (Hom.mk_eq_mk_iff _ _).mp hClass
  change ∃ e : r.stabilizer ≅ (𝟙_ (Core C)), e.hom ▷ s ≫ (λ_ s).hom = rd at hRaw
  obtain ⟨e, he⟩ := hRaw
  let f : x ⟶ y := (λₗ[Core C] x).inv ≫ (e.inv ⊵ₗ x) ≫ rp
  have hrel : r.Rel (fixedDenominatorRawMap s f) := by
    change ∃ e : r.stabilizer ≅ (𝟙_ (Core C)),
      ((e.hom ⊵ₗ x) ≫ (λₗ[Core C] x).hom ≫ f,
        e.hom ▷ s ≫ (λ_ s).hom ≫ 𝟙 s) = (rp, rd)
    refine ⟨e, ?_⟩
    apply Prod.ext
    · change (e.hom ⊵ₗ x) ≫ (λₗ[Core C] x).hom ≫ (λₗ[Core C] x).inv ≫
        (e.inv ⊵ₗ x) ≫ rp = rp
      simp only [Iso.hom_inv_id_assoc]
      exact actualActionIso_cancel e x rp
    · simpa only [Category.comp_id] using he
  refine ⟨f, ?_⟩
  apply CategoryTheory.Functor.Fiber.hom_ext
  change Hom.mk (fixedDenominatorRawMap s f) = ψ
  exact (_root_.Quotient.sound hrel).symm.trans hr
/-- Every fixed-denominator fiber hom-set is reconstructed from the actual raw relation. -/
def denominatorFiberFullyFaithful (s : Core C) :
    (denominatorFiberFunctor (X := X) s).FullyFaithful where
  preimage {x y} f := Classical.choose
    (show ∃ g : x ⟶ y, (denominatorFiberFunctor s).map g = f from by
      exact denominatorFiberFunctor_map_surjective s f)
  map_preimage {x y} f := by
    exact Classical.choose_spec
      (show ∃ g : x ⟶ y, (denominatorFiberFunctor s).map g = f from by
        exact denominatorFiberFunctor_map_surjective s f)
  preimage_map f := by
    apply denominatorFiberFunctor_map_injective s
    exact Classical.choose_spec
      (denominatorFiberFunctor_map_surjective s ((denominatorFiberFunctor s).map f))

/-- The actual positive coordinate of an original fixed-denominator fiber object. -/
def denominatorFiberInverseObject {s : Core C} (a : denominatorFiber (X := X) s) : X :=
  a.val.of.1

/-- The reconstructed pair is the original fiber object, using only its denominator equality. -/
theorem denominatorFiberObject_eq {s : Core C} (a : denominatorFiber (X := X) s) :
    (denominatorFiberFunctor s).obj (denominatorFiberInverseObject a) = a := by
  apply Subtype.ext
  have h : a.val.of.2 = s := congrArg
    (fun k : MonoidalActionCategory (Core C) (Core C) => k.of) a.property
  change (⟨(a.val.of.1, s)⟩ : SInverse (Core C) X) = ⟨(a.val.of.1, a.val.of.2)⟩
  exact congrArg (fun t : Core C => (⟨(a.val.of.1, t)⟩ : SInverse (Core C) X)) h.symm

/-- The fiber counit is the actual equality of the original reconstructed pair. -/
def denominatorFiberCounitComponent {s : Core C} (a : denominatorFiber (X := X) s) :
    (denominatorFiberFunctor s).obj (denominatorFiberInverseObject a) ≅ a :=
  eqToIso (denominatorFiberObject_eq a)

/-- The inverse functor reconstructs the original positive map through the actual counit. -/
def denominatorFiberInverse (s : Core C) : denominatorFiber (X := X) s ⥤ X where
  obj := denominatorFiberInverseObject
  map {a b} f := (denominatorFiberFullyFaithful s).preimage
    ((denominatorFiberCounitComponent a).hom ≫ f ≫ (denominatorFiberCounitComponent b).inv)
  map_id a := by
    apply (denominatorFiberFullyFaithful s).map_injective
    simp only [CategoryTheory.Functor.FullyFaithful.map_preimage,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id]
  map_comp f g := by
    apply (denominatorFiberFullyFaithful s).map_injective
    simp only [CategoryTheory.Functor.FullyFaithful.map_preimage,
      CategoryTheory.Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]

/-- The original pair-equality counit is natural at every fixed denominator. -/
def denominatorFiberCounit (s : Core C) :
    denominatorFiberInverse s ⋙ denominatorFiberFunctor s ≅
      𝟭 (denominatorFiber (X := X) s) :=
  NatIso.ofComponents denominatorFiberCounitComponent (by
    intro a b f
    change (denominatorFiberFunctor s).map ((denominatorFiberFullyFaithful s).preimage
        ((denominatorFiberCounitComponent a).hom ≫ f ≫
          (denominatorFiberCounitComponent b).inv)) ≫ (denominatorFiberCounitComponent b).hom =
      (denominatorFiberCounitComponent a).hom ≫ f
    rw [CategoryTheory.Functor.FullyFaithful.map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- The unit is the unique inverse of the actual counit under the proved hom correspondence. -/
def denominatorFiberUnit (s : Core C) :
    𝟭 X ≅ denominatorFiberFunctor s ⋙ denominatorFiberInverse s :=
  NatIso.ofComponents
    (fun x => (denominatorFiberFullyFaithful s).preimageIso
      (denominatorFiberCounitComponent ((denominatorFiberFunctor s).obj x)).symm) (by
    intro x y f
    apply (denominatorFiberFullyFaithful s).map_injective
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    change (denominatorFiberFunctor s).map f ≫
        (denominatorFiberFunctor s).map ((denominatorFiberFullyFaithful s).preimage
          (denominatorFiberCounitComponent ((denominatorFiberFunctor s).obj y)).inv) =
      (denominatorFiberFunctor s).map ((denominatorFiberFullyFaithful s).preimage
          (denominatorFiberCounitComponent ((denominatorFiberFunctor s).obj x)).inv) ≫
        (denominatorFiberFunctor s).map ((denominatorFiberFullyFaithful s).preimage
          ((denominatorFiberCounitComponent ((denominatorFiberFunctor s).obj x)).hom ≫
            (denominatorFiberFunctor s).map f ≫
              (denominatorFiberCounitComponent ((denominatorFiberFunctor s).obj y)).inv))
    rw [CategoryTheory.Functor.FullyFaithful.map_preimage,
      CategoryTheory.Functor.FullyFaithful.map_preimage,
      CategoryTheory.Functor.FullyFaithful.map_preimage]
    simp only [Iso.inv_hom_id_assoc])

/-- The actual unit/counit satisfy the genuine equivalence triangle. -/
theorem denominatorFiber_triangle (s : Core C) (x : X) :
    (denominatorFiberFunctor s).map ((denominatorFiberUnit s).hom.app x) ≫
      (denominatorFiberCounit s).hom.app ((denominatorFiberFunctor s).obj x) =
        𝟙 ((denominatorFiberFunctor s).obj x) := by
  change (denominatorFiberFunctor s).map ((denominatorFiberFullyFaithful s).preimage
      (denominatorFiberCounitComponent ((denominatorFiberFunctor s).obj x)).inv) ≫
        (denominatorFiberCounitComponent ((denominatorFiberFunctor s).obj x)).hom = _
  rw [CategoryTheory.Functor.FullyFaithful.map_preimage]
  exact (denominatorFiberCounitComponent ((denominatorFiberFunctor s).obj x)).inv_hom_id

/-- The original positive category is equivalent to the literal denominator-projection fiber. -/
def denominatorFiberEquivalence (s : Core C) : X ≌ denominatorFiber (X := X) s where
  functor := denominatorFiberFunctor s
  inverse := denominatorFiberInverse s
  unitIso := denominatorFiberUnit s
  counitIso := denominatorFiberCounit s
  functor_unitIso_comp x := denominatorFiber_triangle s x

/-- Forgetting the actual fixed-denominator inclusion is exactly the original pair functor. -/
theorem denominatorFiberFunctor_forget (s : Core C) :
    denominatorFiberFunctor (X := X) s ⋙
      (CategoryTheory.Functor.Fiber.fiberInclusion :
        denominatorFiber (X := X) s ⥤ SInverse (Core C) X) = fixedDenominatorTotal s := rfl

/-- At the tensor unit this is exactly the actual positive inclusion into S-inverse-X. -/
theorem denominatorFiberFunctor_unit_forget :
    denominatorFiberFunctor (X := X) (𝟙_ (Core C)) ⋙
      (CategoryTheory.Functor.Fiber.fiberInclusion :
        denominatorFiber (X := X) (𝟙_ (Core C)) ⥤ SInverse (Core C) X) =
      SInverse.inclusion (Core C) X := rfl

end CategoryTheory.MonoidalActionCategory

end


noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.IsCofibered
open scoped CategoryTheory.Limits.CoreBiprodMonoidal
open scoped MonoidalCategory CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace CategoryTheory.MonoidalActionCategory

-- The acted-on category keeps independent object and Hom universes.
-- The actual cofibered projection supplies the comma and strict-fiber constructions.
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
  {X : Type uX} [Category.{vX} X] [MonoidalLeftAction (Core C) X]

attribute [local instance] diagonalAction

/-- The actual cocartesian retraction of the denominator right comma to its strict fiber. -/
def denominatorCommaRetraction (s : Core C) :
    CostructuredArrow (denominatorProjection (Core C) X)
      (⟨s⟩ : MonoidalActionCategory (Core C) (Core C)) ⥤
        denominatorFiber (X := X) s := by
  letI : (denominatorProjection (Core C) X).IsCofibered :=
    denominatorProjection_isCofibered (C := C) (X := X)
  exact costructuredToFiber (p := denominatorProjection (Core C) X) ⟨s⟩

/-- The actual strict fiber includes into the denominator right comma. -/
def denominatorCommaInclusion (s : Core C) :
    denominatorFiber (X := X) s ⥤
      CostructuredArrow (denominatorProjection (Core C) X)
        (⟨s⟩ : MonoidalActionCategory (Core C) (Core C)) := by
  letI : (denominatorProjection (Core C) X).IsCofibered :=
    denominatorProjection_isCofibered (C := C) (X := X)
  exact fiberToCostructuredArrow (p := denominatorProjection (Core C) X) ⟨s⟩

/-- Cocartesian lifting proves the adjunction; no adjunction is a premise. -/
def denominatorCommaAdjunction (s : Core C) :
    denominatorCommaRetraction (X := X) s ⊣ denominatorCommaInclusion (X := X) s := by
  letI : (denominatorProjection (Core C) X).IsCofibered :=
    denominatorProjection_isCofibered (C := C) (X := X)
  exact costructuredToFiberAdjunction (p := denominatorProjection (Core C) X) ⟨s⟩


end CategoryTheory.MonoidalActionCategory

end
