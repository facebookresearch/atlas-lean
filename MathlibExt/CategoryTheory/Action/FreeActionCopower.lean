/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Action.Coinvariants

/-!
# Coefficient colimits of free actions

For a free group action on an arbitrary index type, its coefficient diagram
is a copower indexed by the actual orbit quotient. The comparison chooses
orbit representatives and is natural for equivariant coefficient maps.
Only the displayed coproduct and, for comparison, the chosen colimit are needed.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v wH wE

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ActionCategory

variable (H : Type wH) (E : Type wE) [Group H] [MulAction H E]

/-- The representative of the actual orbit class of an index. -/
def freeActionRepresentative (q : MulAction.orbitRel.Quotient H E) : E :=
  Quotient.out q

/-- Freeness gives a unique element sending an index to its chosen representative. -/
theorem freeActionTwist_existsUnique
    (hfree : ∀ e : E, Function.Injective (fun a : H => a • e)) (e : E) :
    ∃! a : H, a • e = freeActionRepresentative H E (Quotient.mk'' e) := by
  have hclass : (Quotient.mk'' (freeActionRepresentative H E (Quotient.mk'' e)) :
      MulAction.orbitRel.Quotient H E) = Quotient.mk'' e :=
    Quotient.out_eq' (Quotient.mk'' e)
  have horbit : freeActionRepresentative H E (Quotient.mk'' e) ∈ MulAction.orbit H e :=
    (MulAction.orbitRel_apply).mp (Quotient.exact' hclass)
  obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp horbit
  exact ⟨a, ha, fun b hb => hfree e (hb.trans ha.symm)⟩

/-- The unique group element sending an index to its chosen orbit representative. -/
def freeActionTwist (hfree : ∀ e : E, Function.Injective (fun a : H => a • e))
    (e : E) : H :=
  Classical.choose (freeActionTwist_existsUnique H E hfree e)

/-- The chosen twist sends the actual index to its orbit representative. -/
theorem freeActionTwist_spec
    (hfree : ∀ e : E, Function.Injective (fun a : H => a • e)) (e : E) :
    freeActionTwist H E hfree e • e = freeActionRepresentative H E (Quotient.mk'' e) :=
  (Classical.choose_spec (freeActionTwist_existsUnique H E hfree e)).1

/-- An action arrow changes the twist in source-first coefficient-composition order. -/
theorem freeActionTwist_comp
    (hfree : ∀ e : E, Function.Injective (fun a : H => a • e))
    {e e' : ActionCategory H E} (f : e ⟶ e') :
    freeActionTwist H E hfree e.back = freeActionTwist H E hfree e'.back * f.hom := by
  let x : E := e.back
  let y : E := e'.back
  let a : H := f.hom
  have hxy : a • x = y := f.map_val
  have hclass : (Quotient.mk'' y : MulAction.orbitRel.Quotient H E) = Quotient.mk'' x :=
    (congrArg (fun t : E => (Quotient.mk'' t : MulAction.orbitRel.Quotient H E)) hxy).symm.trans
      (MulAction.orbitRel.Quotient.quotient_smul_eq (g := a) (a := x))
  apply hfree x
  change freeActionTwist H E hfree x • x = (freeActionTwist H E hfree y * a) • x
  rw [mul_smul, hxy, freeActionTwist_spec, freeActionTwist_spec]
  exact congrArg (freeActionRepresentative H E) hclass.symm

/-- The twist of a chosen representative is the group identity. -/
theorem freeActionTwist_representative
    (hfree : ∀ e : E, Function.Injective (fun a : H => a • e))
    (q : MulAction.orbitRel.Quotient H E) :
    freeActionTwist H E hfree (freeActionRepresentative H E q) = 1 := by
  let r : E := freeActionRepresentative H E q
  have hclass : (Quotient.mk'' r : MulAction.orbitRel.Quotient H E) = q :=
    Quotient.out_eq' q
  apply hfree r
  change freeActionTwist H E hfree r • r = (1 : H) • r
  rw [freeActionTwist_spec, one_smul]
  exact congrArg (freeActionRepresentative H E) hclass

variable {C : Type u} [Category.{v} C]
variable (Z : C) (rho : H →* End Z)
variable (hfree : ∀ e : E, Function.Injective (fun a : H => a • e))
variable [HasCoproduct (fun _ : MulAction.orbitRel.Quotient H E => Z)]

/-- The actual orbit copower carries the coefficient cocone, twisted to chosen representatives. -/
def freeActionCopowerCocone : Cocone (coefficientDiagram H E Z rho) :=
  CoefficientFamily.cocone H E Z rho
    { leg := fun e => (rho (freeActionTwist H E hfree e)).asHom ≫
        Sigma.ι (fun _ : MulAction.orbitRel.Quotient H E => Z) (Quotient.mk'' e)
      relation := by
        intro a e
        have hc : (Quotient.mk'' (a • e) : MulAction.orbitRel.Quotient H E) =
            Quotient.mk'' e := MulAction.orbitRel.Quotient.quotient_smul_eq
        have ht := freeActionTwist_comp H E hfree
          (show (e : ActionCategory H E) ⟶ ((a • e : E) : ActionCategory H E) from ⟨a, rfl⟩)
        change freeActionTwist H E hfree e = freeActionTwist H E hfree (a • e) * a at ht
        rw [← Category.assoc, ← End.mul_asHom, ← rho.map_mul, ← ht, hc] }

/-- The orbit copower is a colimit of the actual coefficient diagram. -/
def freeActionCopowerIsColimit : IsColimit (freeActionCopowerCocone H E Z rho hfree) where
  desc c := Sigma.desc
    (fun q => c.ι.app (freeActionRepresentative H E q : ActionCategory H E))
  fac c e := by
    let family : MulAction.orbitRel.Quotient H E → C := fun _ => Z
    let x : E := e.val
    let q : MulAction.orbitRel.Quotient H E := Quotient.mk'' x
    let rq : ActionCategory H E := (ActionCategory.objEquiv H E) (freeActionRepresentative H E q)
    let a : H := freeActionTwist H E hfree x
    let arrow : e ⟶ rq := ⟨a, freeActionTwist_spec H E hfree x⟩
    have hw : (rho a).asHom ≫ c.ι.app rq = c.ι.app e := c.w arrow
    let leg : Z ⟶ ∐ family := Sigma.ι family q
    let desc : (∐ family) ⟶ c.pt := Sigma.desc
      (fun t => c.ι.app ((ActionCategory.objEquiv H E) (freeActionRepresentative H E t)))
    have hd : leg ≫ desc = c.ι.app rq := Sigma.ι_comp_desc _ _
    change ((rho a).asHom ≫ leg) ≫ desc = c.ι.app e
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k : Z ⟶ c.pt => (rho a).asHom ≫ k) hd).trans hw)
  uniq c m hm := by
    let family : MulAction.orbitRel.Quotient H E → C := fun _ => Z
    change (∐ family) ⟶ c.pt at m
    let desc : (∐ family) ⟶ c.pt := Sigma.desc
      (fun t => c.ι.app ((ActionCategory.objEquiv H E) (freeActionRepresentative H E t)))
    change m = desc
    apply Sigma.hom_ext
    intro q
    let r : E := freeActionRepresentative H E q
    let rq : ActionCategory H E := (ActionCategory.objEquiv H E) r
    have hq : ((rho (freeActionTwist H E hfree r)).asHom ≫
        Sigma.ι family (Quotient.mk'' r)) ≫ m = c.ι.app rq := hm rq
    have hclass : (Quotient.mk'' r : MulAction.orbitRel.Quotient H E) = q :=
      Quotient.out_eq' q
    have ht : freeActionTwist H E hfree r = 1 := freeActionTwist_representative H E hfree q
    have hrho : (rho (freeActionTwist H E hfree r)).asHom = 𝟙 Z :=
      congrArg End.asHom ((congrArg rho ht).trans rho.map_one)
    have hleg : (rho (freeActionTwist H E hfree r)).asHom ≫
        Sigma.ι family (Quotient.mk'' r) =
        Sigma.ι family q := by
      rw [hrho, Category.id_comp, hclass]
    have hsource : Sigma.ι family q ≫ m = c.ι.app rq :=
      (congrArg (fun k : Z ⟶ ∐ family => k ≫ m) hleg).symm.trans hq
    have hdesc : Sigma.ι family q ≫ desc = c.ι.app rq := Sigma.ι_comp_desc _ _
    exact hsource.trans hdesc.symm

variable [HasColimit (coefficientDiagram H E Z rho)]

/-- A chosen coefficient colimit identifies with the actual orbit-indexed copower. -/
def freeActionColimitCopowerIso :
    colimit (coefficientDiagram H E Z rho) ≅
      ∐ (fun _ : MulAction.orbitRel.Quotient H E => Z) :=
  (colimit.isColimit (coefficientDiagram H E Z rho)).coconePointUniqueUpToIso
    (freeActionCopowerIsColimit H E Z rho hfree)

/-- The comparison's exact generator characteristic retains the chosen twist and orbit class. -/
theorem freeActionColimitCopowerIso_generator (e : E) :
    colimit.ι (coefficientDiagram H E Z rho) (e : ActionCategory H E) ≫
        (freeActionColimitCopowerIso H E Z rho hfree).hom =
      (rho (freeActionTwist H E hfree e)).asHom ≫
        Sigma.ι (fun _ : MulAction.orbitRel.Quotient H E => Z) (Quotient.mk'' e) :=
  (colimit.isColimit (coefficientDiagram H E Z rho)).comp_coconePointUniqueUpToIso_hom
    (freeActionCopowerIsColimit H E Z rho hfree) (e : ActionCategory H E)

/-- Chosen orbit coordinates are natural for actual equivariant coefficient maps. -/
theorem freeActionColimitCopowerIso_naturality
    (Z' : C) (rho' : H →* End Z') (f : Z ⟶ Z')
    (hf : ∀ a : H, (rho a).asHom ≫ f = f ≫ (rho' a).asHom)
    [HasCoproduct (fun _ : MulAction.orbitRel.Quotient H E => Z')]
    [HasColimit (coefficientDiagram H E Z' rho')] :
    colimMap (coefficientNatTrans H E Z Z' rho rho' f hf) ≫
        (freeActionColimitCopowerIso H E Z' rho' hfree).hom =
      (freeActionColimitCopowerIso H E Z rho hfree).hom ≫
        Limits.Sigma.map (fun _ : MulAction.orbitRel.Quotient H E => f) := by
  apply colimit.hom_ext
  intro e
  obtain ⟨x, hx⟩ := (ActionCategory.objEquiv H E).surjective e
  rw [← hx]
  let ax : ActionCategory H E := (ActionCategory.objEquiv H E) x
  let L := colimit (coefficientDiagram H E Z rho)
  let L' := colimit (coefficientDiagram H E Z' rho')
  let family : MulAction.orbitRel.Quotient H E → C := fun _ => Z
  let family' : MulAction.orbitRel.Quotient H E → C := fun _ => Z'
  let l : Z ⟶ L := colimit.ι (coefficientDiagram H E Z rho) ax
  let l' : Z' ⟶ L' := colimit.ι (coefficientDiagram H E Z' rho') ax
  let cmp : L ⟶ ∐ family := (freeActionColimitCopowerIso H E Z rho hfree).hom
  let cmp' : L' ⟶ ∐ family' := (freeActionColimitCopowerIso H E Z' rho' hfree).hom
  let lm : L ⟶ L' := colimMap (coefficientNatTrans H E Z Z' rho rho' f hf)
  let pm : (∐ family) ⟶ ∐ family' := Limits.Sigma.map (fun _ => f)
  let leg : Z ⟶ ∐ family := Sigma.ι family (Quotient.mk'' x)
  let leg' : Z' ⟶ ∐ family' := Sigma.ι family' (Quotient.mk'' x)
  let t : H := freeActionTwist H E hfree x
  have hm : l ≫ lm = f ≫ l' := ι_colimMap (coefficientNatTrans H E Z Z' rho rho' f hf) ax
  have hc : l ≫ cmp = (rho t).asHom ≫ leg :=
    freeActionColimitCopowerIso_generator H E Z rho hfree x
  have hc' : l' ≫ cmp' = (rho' t).asHom ≫ leg' :=
    freeActionColimitCopowerIso_generator H E Z' rho' hfree x
  have hp : leg ≫ pm = f ≫ leg' := Sigma.ι_map _ _
  have hLeft : (l ≫ lm) ≫ cmp' = (f ≫ (rho' t).asHom) ≫ leg' :=
    (congrArg (fun k : Z ⟶ L' => k ≫ cmp') hm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k : Z' ⟶ ∐ family' => f ≫ k) hc').trans (Category.assoc _ _ _).symm))
  have hRight : (l ≫ cmp) ≫ pm = (f ≫ (rho' t).asHom) ≫ leg' :=
    (congrArg (fun k : Z ⟶ ∐ family => k ≫ pm) hc).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k : Z ⟶ ∐ family' => (rho t).asHom ≫ k) hp).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun k : Z ⟶ Z' => k ≫ leg') (hf t)))))
  change l ≫ (lm ≫ cmp') = l ≫ (cmp ≫ pm)
  exact (Category.assoc _ _ _).symm.trans
    (hLeft.trans (hRight.symm.trans (Category.assoc _ _ _)))

end CategoryTheory.ActionCategory
