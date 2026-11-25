/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Enriched.Basic

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uA uB
open CategoryTheory MonoidalCategory

namespace CategoryTheory.EnrichedHomIsoEquivalence

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {A : Type uA} [EnrichedCategory V A] {B : Type uB} [EnrichedCategory V B]
  (e : A ≃ B) (h : ∀ a b : A, (a ⟶[V] b) ≅ (e a ⟶[V] e b))
  (hid : ∀ a : A, eId V a ≫ (h a a).hom = eId V (e a))
  (hcomp : ∀ a b c : A, eComp V a b c ≫ (h a c).hom =
    ((h a b).hom ⊗ₘ (h b c).hom) ≫ eComp V (e a) (e b) (e c))

/-- The actual object bijection and whole Hom maps form the genuine enriched comparison. -/
@[no_expose]
def forward : EnrichedFunctor V A B where
  obj := e
  map a b := (h a b).hom
  map_id := hid
  map_comp := hcomp

/-- The complete inverse maps retain both actual object equalities and the full Hom inverse. -/
@[no_expose]
def inverseMap (b c : B) : (b ⟶[V] c) ⟶ (e.symm b ⟶[V] e.symm c) :=
  eqToHom (congrArg₂ (fun x y : B => x ⟶[V] y)
    (e.apply_symm_apply b).symm (e.apply_symm_apply c).symm) ≫
      (h (e.symm b) (e.symm c)).inv

/-- Equality transport retains the actual entire enriched identity. -/
private theorem identity_cast {b b' : B} (p : b = b') :
    eId V b ≫ eqToHom (congrArg₂ (fun x y : B => x ⟶[V] y) p p) = eId V b' := by
  cases p
  rw [eqToHom_refl, Category.comp_id]

/-- Equality transport retains both full inputs of actual enriched composition. -/
private theorem composition_cast {b b' c c' d d' : B}
    (pb : b = b') (pc : c = c') (pd : d = d') :
    eComp V b c d ≫ eqToHom (congrArg₂ (fun x y : B => x ⟶[V] y) pb pd) =
      (eqToHom (congrArg₂ (fun x y : B => x ⟶[V] y) pb pc) ⊗ₘ
        eqToHom (congrArg₂ (fun x y : B => x ⟶[V] y) pc pd)) ≫ eComp V b' c' d' := by
  cases pb
  cases pc
  cases pd
  simp only [eqToHom_refl, id_tensorHom_id, Category.id_comp, Category.comp_id]

/-- Both actual inverse equality transports cancel on the entire Hom object. -/
private theorem cast_inverse {a a' b b' : A} (pa : a = a') (pb : b = b') :
    eqToHom (congrArg₂ (fun x y : A => x ⟶[V] y) pa.symm pb.symm) ≫
      eqToHom (congrArg₂ (fun x y : A => x ⟶[V] y) pa pb) = 𝟙 (a' ⟶[V] b') := by
  cases pa
  cases pb
  rw [eqToHom_refl, Category.id_comp]

/-- The complete inverse family respects both actual source-object equalities. -/
private theorem inverse_cast {a a' b b' : A} (pa : a = a') (pb : b = b') :
    eqToHom (congrArg₂ (fun x y : A => e x ⟶[V] e y) pa pb) ≫ (h a' b').inv =
      (h a b).inv ≫ eqToHom (congrArg₂ (fun x y : A => x ⟶[V] y) pa pb) := by
  cases pa
  cases pb
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

include hid in
/-- The entire inverse identity is derived from the actual full forward identity. -/
theorem inverse_id (b : B) : eId V b ≫ inverseMap e h b b = eId V (e.symm b) := by
  unfold inverseMap
  rw [← Category.assoc, identity_cast (e.apply_symm_apply b).symm,
    ← hid (e.symm b), Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

include hcomp in
/-- Both inverse Hom factors satisfy the complete original composition equation. -/
private theorem inverse_hom_comp (a b c : A) :
    eComp V (e a) (e b) (e c) ≫ (h a c).inv =
      ((h a b).inv ⊗ₘ (h b c).inv) ≫ eComp V a b c := by
  apply (cancel_mono (h a c).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Category.assoc, hcomp, tensorHom_comp_tensorHom_assoc,
    Iso.inv_hom_id, Iso.inv_hom_id, id_tensorHom_id, Category.id_comp]

include hcomp in
/-- The inverse composition retains both entire original Hom factors. -/
theorem inverse_comp (b c d : B) :
    eComp V b c d ≫ inverseMap e h b d =
      (inverseMap e h b c ⊗ₘ inverseMap e h c d) ≫
        eComp V (e.symm b) (e.symm c) (e.symm d) := by
  unfold inverseMap
  rw [← Category.assoc, composition_cast (e.apply_symm_apply b).symm
    (e.apply_symm_apply c).symm (e.apply_symm_apply d).symm, Category.assoc,
    inverse_hom_comp e h hcomp, ← tensorHom_comp_tensorHom_assoc]

/-- On the actual object image the inverse keeps its complete Hom inverse after equality
transport. -/
theorem inverseMap_image (a b : A) :
    inverseMap e h (e a) (e b) ≫
      eqToHom (congrArg₂ (fun x y : A => x ⟶[V] y)
        (e.symm_apply_apply a) (e.symm_apply_apply b)) = (h a b).inv := by
  let pa := e.symm_apply_apply a
  let pb := e.symm_apply_apply b
  unfold inverseMap
  change (eqToHom (congrArg₂ (fun x y : A => e x ⟶[V] e y) pa.symm pb.symm) ≫
    (h (e.symm (e a)) (e.symm (e b))).inv) ≫
      eqToHom (congrArg₂ (fun x y : A => x ⟶[V] y) pa pb) = _
  rw [inverse_cast e h pa.symm pb.symm, Category.assoc,
    cast_inverse pa pb, Category.comp_id]

/-- The whole inverse source and Hom maps satisfy the actual enriched category laws. -/
@[no_expose]
def inverse : EnrichedFunctor V B A where
  obj := e.symm
  map := inverseMap e h
  map_id := inverse_id e h hid
  map_comp := inverse_comp e h hcomp

/-- Both complete forward/inverse Hom maps recover the actual original enriched identity. -/
theorem forward_inverse :
    (forward e h hid hcomp).comp V (inverse e h hid hcomp) = EnrichedFunctor.id V A := by
  refine EnrichedFunctor.ext V (fun a => e.symm_apply_apply a) ?_
  intro a b
  change ((h a b).hom ≫ inverseMap e h (e a) (e b)) ≫
    eqToHom (congrArg₂ (fun x y : A => x ⟶[V] y)
      (e.symm_apply_apply a) (e.symm_apply_apply b)) = 𝟙 (a ⟶[V] b)
  rw [Category.assoc, inverseMap_image, Iso.hom_inv_id]

/-- The complete inverse/forward maps recover the actual target enrichment. -/
theorem inverse_forward :
    (inverse e h hid hcomp).comp V (forward e h hid hcomp) = EnrichedFunctor.id V B := by
  refine EnrichedFunctor.ext V (fun b => e.apply_symm_apply b) ?_
  intro b c
  change (inverseMap e h b c ≫ (h (e.symm b) (e.symm c)).hom) ≫
    eqToHom (congrArg₂ (fun x y : B => x ⟶[V] y)
      (e.apply_symm_apply b) (e.apply_symm_apply c)) = 𝟙 (b ⟶[V] c)
  unfold inverseMap
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc]
  exact cast_inverse (e.apply_symm_apply b) (e.apply_symm_apply c)

private theorem forward_obj_proof (a : A) : (forward e h hid hcomp).obj a = e a := rfl

/-- Every complete forward object is the actual supplied degree bijection. -/
theorem forward_obj (a : A) : (forward e h hid hcomp).obj a = e a :=
  forward_obj_proof e h hid hcomp a

private theorem forward_map_proof (a b : A) :
    HEq ((forward e h hid hcomp).map a b) ((h a b).hom) := by rfl

/-- The full forward Hom map is exactly the original whole isomorphism map. -/
theorem forward_map (a b : A) :
    HEq ((forward e h hid hcomp).map a b) ((h a b).hom) :=
  forward_map_proof e h hid hcomp a b

private theorem inverse_obj_proof (b : B) : (inverse e h hid hcomp).obj b = e.symm b := rfl

/-- Every complete inverse object is the actual inverse degree bijection. -/
theorem inverse_obj (b : B) : (inverse e h hid hcomp).obj b = e.symm b :=
  inverse_obj_proof e h hid hcomp b

private theorem inverse_map_proof (b c : B) :
    HEq ((inverse e h hid hcomp).map b c) (inverseMap e h b c) := by rfl

/-- The inverse retains the entire original Hom inverse and both actual equality transports. -/
theorem inverse_map (b c : B) :
    HEq ((inverse e h hid hcomp).map b c) (inverseMap e h b c) :=
  inverse_map_proof e h hid hcomp b c

private theorem inverseMap_eq_proof (b c : B) : inverseMap e h b c =
    eqToHom (congrArg₂ (fun x y : B => x ⟶[V] y)
      (e.apply_symm_apply b).symm (e.apply_symm_apply c).symm) ≫
        (h (e.symm b) (e.symm c)).inv := rfl

/-- The complete actual inverse-map initializer remains public with every original leg. -/
theorem inverseMap_eq (b c : B) : inverseMap e h b c =
    eqToHom (congrArg₂ (fun x y : B => x ⟶[V] y)
      (e.apply_symm_apply b).symm (e.apply_symm_apply c).symm) ≫
        (h (e.symm b) (e.symm c)).inv := inverseMap_eq_proof e h b c

end CategoryTheory.EnrichedHomIsoEquivalence
