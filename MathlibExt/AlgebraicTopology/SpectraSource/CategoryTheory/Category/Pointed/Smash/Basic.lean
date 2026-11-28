/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/Category/Pointed/Smash/Basic.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import Mathlib.CategoryTheory.Category.Pointed
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# The smash product of pointed types

The smash product `X ∧ Y` of pointed types is the quotient of `X × Y` collapsing the wedge
`X × {y₀} ∪ {x₀} × Y` to the basepoint. Pointed maps out of it are exactly functions of two
variables sending the wedge to the basepoint. With unit `S⁰ = PUnit₊` (`Option PUnit` pointed
at `none`), the smash product makes `Pointed` a symmetric monoidal category, whose braiding
swaps the two factors.

This is the levelwise input for the smash product of pointed simplicial sets, viewed as
simplicial objects in `Pointed`.

## Main definitions

* `Pointed.smash X Y`: the smash product, pointed at the collapsed wedge.
* `Pointed.smash.mk x y`: the class of a pair.
* `Pointed.smash.lift`: the pointed map induced by a function of two variables sending the
  wedge to the basepoint; `Pointed.smash.hom_ext` gives uniqueness.
* `Pointed.smash.map`: the smash product of two pointed maps.
* The instances `MonoidalCategory Pointed` and `SymmetricCategory Pointed`.

## References

* A. Hatcher, *Algebraic Topology*, Chapter 0 (the smash product of pointed spaces).
-/

public section

universe u

open CategoryTheory MonoidalCategory

namespace Pointed

variable {X Y Z W X' Y' : Pointed.{u}}

/-- The equivalence relation on `X × Y` identifying all points of the wedge
`X × {y₀} ∪ {x₀} × Y` and nothing else. -/
private def smashSetoid (X Y : Pointed.{u}) : Setoid (X × Y) where
  r p q := p = q ∨ ((p.1 = X.point ∨ p.2 = Y.point) ∧ (q.1 = X.point ∨ q.2 = Y.point))
  iseqv :=
    { refl _ := .inl rfl
      symm := by
        rintro p q (rfl | ⟨hp, hq⟩)
        exacts [.inl rfl, .inr ⟨hq, hp⟩]
      trans := by
        rintro p q r (rfl | ⟨hp, hq⟩) hqr
        · exact hqr
        rcases hqr with rfl | ⟨-, hr⟩
        exacts [.inr ⟨hp, hq⟩, .inr ⟨hp, hr⟩] }

/-- The smash product `X ∧ Y` of pointed types: the quotient of `X × Y` collapsing the wedge
`X × {y₀} ∪ {x₀} × Y` to a single point, which is the basepoint. -/
def smash (X Y : Pointed.{u}) : Pointed.{u} :=
  of (Quotient.mk (smashSetoid X Y) (X.point, Y.point))

namespace smash

/-- The class of the pair `(x, y)` in the smash product. -/
def mk (x : X) (y : Y) : smash X Y :=
  Quotient.mk (smashSetoid X Y) (x, y)

lemma mk_surjective : Function.Surjective (fun p : X × Y ↦ mk p.1 p.2) :=
  Quotient.mk_surjective

/-- Induction on the smash product: it suffices to treat the classes of pairs. -/
@[elab_as_elim]
lemma ind {motive : smash X Y → Prop} (h : ∀ x y, motive (mk x y)) (a : smash X Y) :
    motive a :=
  Quotient.ind (fun p ↦ h p.1 p.2) a

lemma point_def : (smash X Y).point = mk X.point Y.point := (rfl)

/-- Two pairs have the same class exactly when they are equal or both lie in the wedge. -/
lemma mk_eq_mk_iff {x x' : X} {y y' : Y} :
    mk x y = mk x' y' ↔
      x = x' ∧ y = y' ∨ (x = X.point ∨ y = Y.point) ∧ (x' = X.point ∨ y' = Y.point) := by
  exact Quotient.eq.trans (or_congr_left Prod.ext_iff)

/-- A pair represents the basepoint exactly when it lies in the wedge. -/
@[simp]
lemma mk_eq_point_iff {x : X} {y : Y} :
    mk x y = (smash X Y).point ↔ x = X.point ∨ y = Y.point := by
  rw [point_def, mk_eq_mk_iff]
  grind

@[simp]
lemma mk_point_left (y : Y) : mk X.point y = (smash X Y).point :=
  mk_eq_point_iff.2 (.inl rfl)

@[simp]
lemma mk_point_right (x : X) : mk x Y.point = (smash X Y).point :=
  mk_eq_point_iff.2 (.inr rfl)

/-- The pointed map out of the smash product induced by a function of two variables sending
the wedge to the basepoint. -/
def lift (f : X → Y → Z) (hl : ∀ y, f X.point y = Z.point) (hr : ∀ x, f x Y.point = Z.point) :
    smash X Y ⟶ Z where
  toFun := Quotient.lift (fun p ↦ f p.1 p.2) <| by
    have h : ∀ p : X × Y, p.1 = X.point ∨ p.2 = Y.point → f p.1 p.2 = Z.point := by
      rintro ⟨x, y⟩ (rfl | rfl)
      exacts [hl y, hr x]
    rintro p q (rfl | ⟨hp, hq⟩)
    exacts [rfl, (h p hp).trans (h q hq).symm]
  map_point := hl Y.point

@[simp]
lemma lift_mk (f : X → Y → Z) (hl : ∀ y, f X.point y = Z.point)
    (hr : ∀ x, f x Y.point = Z.point) (x : X) (y : Y) :
    (lift f hl hr).toFun (mk x y) = f x y := (rfl)

/-- Pointed maps out of the smash product are determined by their values on pairs. -/
@[ext]
lemma hom_ext {f g : smash X Y ⟶ Z} (h : ∀ x y, f.toFun (mk x y) = g.toFun (mk x y)) :
    f = g :=
  Hom.ext (funext (ind h))

/-- The smash product of two pointed maps. -/
def map (f : X ⟶ X') (g : Y ⟶ Y') : smash X Y ⟶ smash X' Y' :=
  lift (fun x y ↦ mk (f.toFun x) (g.toFun y)) (by simp [f.map_point])
    (by simp [g.map_point])

@[simp]
lemma map_mk (f : X ⟶ X') (g : Y ⟶ Y') (x : X) (y : Y) :
    (map f g).toFun (mk x y) = mk (f.toFun x) (g.toFun y) := (rfl)

/-- The associativity isomorphism `(X ∧ Y) ∧ Z ≅ X ∧ (Y ∧ Z)`. -/
def associator (X Y Z : Pointed.{u}) : smash (smash X Y) Z ≅ smash X (smash Y Z) where
  hom := lift (fun a z ↦ (lift (fun x y ↦ mk x (mk y z)) (by simp) (by simp)).toFun a)
    (fun _ ↦ Hom.map_point _) (fun a ↦ by induction a using smash.ind; simp)
  inv := lift (fun x b ↦ (lift (fun y z ↦ mk (mk x y) z) (by simp) (by simp)).toFun b)
    (fun b ↦ by induction b using smash.ind; simp) (fun _ ↦ Hom.map_point _)
  hom_inv_id := by
    ext a z
    induction a using smash.ind
    simp
  inv_hom_id := by
    ext x b
    induction b using smash.ind
    simp

/-- The left unit isomorphism `S⁰ ∧ X ≅ X`, where `S⁰ = PUnit₊`. -/
def leftUnitor (X : Pointed.{u}) : smash (of (none : Option PUnit.{u + 1})) X ≅ X where
  hom := lift (fun o x ↦ o.elim X.point fun _ ↦ x) (fun _ ↦ Option.elim_none _ _)
    (by rintro (_ | _) <;> rfl)
  inv := ⟨fun x ↦ mk (some PUnit.unit) x, mk_point_right _⟩
  hom_inv_id := by
    ext (_ | _) x <;> simp [eq_comm (b := mk _ _)]

/-- The right unit isomorphism `X ∧ S⁰ ≅ X`, where `S⁰ = PUnit₊`. -/
def rightUnitor (X : Pointed.{u}) : smash X (of (none : Option PUnit.{u + 1})) ≅ X where
  hom := lift (fun x o ↦ o.elim X.point fun _ ↦ x) (by rintro (_ | _) <;> rfl)
    (fun _ ↦ Option.elim_none _ _)
  inv := ⟨fun x ↦ mk x (some PUnit.unit), mk_point_left _⟩
  hom_inv_id := by
    ext x (_ | _) <;> simp [eq_comm (b := mk _ _)]

/-- The isomorphism `X ∧ Y ≅ Y ∧ X` swapping the two factors. -/
def braiding (X Y : Pointed.{u}) : smash X Y ≅ smash Y X where
  hom := lift (fun x y ↦ mk y x) (fun _ ↦ mk_point_right _) (fun _ ↦ mk_point_left _)
  inv := lift (fun y x ↦ mk x y) (fun _ ↦ mk_point_right _) (fun _ ↦ mk_point_left _)

/- The braiding laws are proved before `β_` exists, so they use this private form; the public
API is `Pointed.braiding_hom_mk` and `Pointed.braiding_inv_mk`. -/
private lemma braiding_hom_mk (x : X) (y : Y) :
    (braiding X Y).hom.toFun (mk x y) = mk y x := (rfl)

end smash

open smash

/-- The smash product, with unit the free pointed type `S⁰ = PUnit₊` on one point. -/
instance monoidalCategoryStruct : MonoidalCategoryStruct Pointed.{u} where
  tensorObj := smash
  whiskerLeft X _ _ g := map (𝟙 X) g
  whiskerRight f Y := map f (𝟙 Y)
  tensorHom := map
  tensorUnit := of (none : Option PUnit.{u + 1})
  associator := smash.associator
  leftUnitor := smash.leftUnitor
  rightUnitor := smash.rightUnitor

lemma tensorObj_def (X Y : Pointed.{u}) : X ⊗ Y = smash X Y := (rfl)

lemma tensorUnit_def : 𝟙_ Pointed.{u} = of (none : Option PUnit.{u + 1}) := (rfl)

@[simp]
lemma tensorObj_point (X Y : Pointed.{u}) : (X ⊗ Y).point = (smash X Y).point := (rfl)

/-- Pointed maps out of a tensor product are determined by their values on pairs. -/
@[ext]
lemma tensor_ext {f g : X ⊗ Y ⟶ Z}
    (h : ∀ x y, f.toFun (smash.mk x y) = g.toFun (smash.mk x y)) : f = g :=
  smash.hom_ext h

/-- Pointed maps out of `(X ⊗ Y) ⊗ Z` are determined by their values on triples. -/
lemma tensor_ext₃' {f g : (X ⊗ Y) ⊗ Z ⟶ W}
    (h : ∀ x y z, f.toFun (smash.mk (smash.mk x y) z) = g.toFun (smash.mk (smash.mk x y) z)) :
    f = g :=
  tensor_ext fun a z ↦ smash.ind
    (motive := fun a ↦ f.toFun (smash.mk a z) = g.toFun (smash.mk a z))
    (fun x y ↦ h x y z) a

/-- Pointed maps out of `X ⊗ (Y ⊗ Z)` are determined by their values on triples. -/
lemma tensor_ext₃ {f g : X ⊗ (Y ⊗ Z) ⟶ W}
    (h : ∀ x y z, f.toFun (smash.mk x (smash.mk y z)) = g.toFun (smash.mk x (smash.mk y z))) :
    f = g :=
  tensor_ext fun x b ↦ smash.ind
    (motive := fun b ↦ f.toFun (smash.mk x b) = g.toFun (smash.mk x b))
    (fun y z ↦ h x y z) b

@[simp]
lemma tensorHom_mk (f : X ⟶ X') (g : Y ⟶ Y') (x : X) (y : Y) :
    (f ⊗ₘ g).toFun (smash.mk x y) = smash.mk (f.toFun x) (g.toFun y) := (rfl)

@[simp]
lemma whiskerLeft_mk (g : Y ⟶ Y') (x : X) (y : Y) :
    (X ◁ g).toFun (smash.mk x y) = smash.mk x (g.toFun y) := (rfl)

@[simp]
lemma whiskerRight_mk (f : X ⟶ X') (x : X) (y : Y) :
    (f ▷ Y).toFun (smash.mk x y) = smash.mk (f.toFun x) y := (rfl)

@[simp]
lemma associator_hom_mk (x : X) (y : Y) (z : Z) :
    (α_ X Y Z).hom.toFun (smash.mk (smash.mk x y) z) = smash.mk x (smash.mk y z) := (rfl)

@[simp]
lemma associator_inv_mk (x : X) (y : Y) (z : Z) :
    (α_ X Y Z).inv.toFun (smash.mk x (smash.mk y z)) = smash.mk (smash.mk x y) z := (rfl)

@[simp]
lemma leftUnitor_hom_mk (o : Option PUnit.{u + 1}) (x : X) :
    (λ_ X).hom.toFun (smash.mk o x) = Option.elim o X.point fun _ ↦ x := (rfl)

@[simp]
lemma leftUnitor_inv_apply (x : X) :
    (λ_ X).inv.toFun x = smash.mk (X := 𝟙_ Pointed) (some PUnit.unit) x := (rfl)

@[simp]
lemma rightUnitor_hom_mk (x : X) (o : Option PUnit.{u + 1}) :
    (ρ_ X).hom.toFun (smash.mk x o) = Option.elim o X.point fun _ ↦ x := (rfl)

@[simp]
lemma rightUnitor_inv_apply (x : X) :
    (ρ_ X).inv.toFun x = smash.mk (Y := 𝟙_ Pointed) x (some PUnit.unit) := (rfl)

/-- The smash product makes `Pointed` a monoidal category. -/
instance monoidalCategory : MonoidalCategory Pointed.{u} where
  tensorHom_def _ _ := by ext; simp
  id_tensorHom_id _ _ := by ext; simp
  tensorHom_comp_tensorHom _ _ _ _ := by ext; simp
  whiskerLeft_id _ _ := by ext; simp
  id_whiskerRight _ _ := by ext; simp
  associator_naturality _ _ _ := tensor_ext₃' fun _ _ _ ↦ by simp
  leftUnitor_naturality f := by
    ext o _
    simp only [Hom.comp_toFun', Function.comp_apply, whiskerLeft_mk, leftUnitor_hom_mk]
    cases o <;> simp [f.map_point]
  rightUnitor_naturality f := by
    ext _ o
    simp only [Hom.comp_toFun', Function.comp_apply, whiskerRight_mk, rightUnitor_hom_mk]
    cases o <;> simp [f.map_point]
  pentagon _ _ _ _ := tensor_ext₃' fun a _ _ ↦ by
    induction a using smash.ind
    simp
  triangle _ _ := tensor_ext₃' fun _ o _ ↦ by
    simp only [Hom.comp_toFun', Function.comp_apply, associator_hom_mk, whiskerLeft_mk,
      whiskerRight_mk, leftUnitor_hom_mk, rightUnitor_hom_mk]
    cases o <;> simp

/-- The swap of factors makes the smash product symmetric monoidal. -/
instance symmetricCategory : SymmetricCategory Pointed.{u} where
  braiding := smash.braiding
  braiding_naturality_right _ _ _ _ := by ext; simp [smash.braiding_hom_mk]
  braiding_naturality_left _ _ := by ext; simp [smash.braiding_hom_mk]
  hexagon_forward _ _ _ := tensor_ext₃' fun _ _ _ ↦ by simp [smash.braiding_hom_mk]
  hexagon_reverse _ _ _ := tensor_ext₃ fun _ _ _ ↦ by simp [smash.braiding_hom_mk]
  symmetry _ _ := by ext; simp [smash.braiding_hom_mk]

@[simp]
lemma braiding_hom_mk (x : X) (y : Y) :
    (β_ X Y).hom.toFun (smash.mk x y) = smash.mk y x := (rfl)

@[simp]
lemma braiding_inv_mk (x : X) (y : Y) :
    (β_ X Y).inv.toFun (smash.mk y x) = smash.mk x y := (rfl)

end Pointed
