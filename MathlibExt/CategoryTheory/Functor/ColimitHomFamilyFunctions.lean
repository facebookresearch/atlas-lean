/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.CoendCharacteristicEquationTransport
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Complete Hom-family uniqueness through the original colimit and Iso

Whole inverse-leg and generator functions determine the entire Hom-map
function. Every source diagram, colimit, Iso and target object family is
fixed. This is the ordinary colimit universal property at full function
level; no replacement colimit or incoming Hom equality is introduced.
The cocone varies with the shift index although its source diagram is fixed.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section

universe uC vC uJ uR uD vD

open CategoryTheory CategoryTheory.Limits

open CategoryTheory.Enriched

namespace CategoryTheory.Functor
namespace ColimitHomFamily

variable {C : Type uC} [Category.{vC} C] {J : Type uJ} {R : Type uR}
  {D : J → J → Type uD} [∀ n k : J, Category.{vD} (D n k)]
  (F : ∀ n k : J, D n k ⥤ C) [∀ n k : J, HasColimit (F n k)]
  {M : J → J → C} {N : R → J → J → C}

/-- Every original source generator on the complete source diagram family. -/
abbrev SourceGenerator := ∀ n k : J, ∀ a : D n k, (F n k).obj a ⟶ M n k

/-- Every full target generator on the same original source diagrams. -/
abbrev TargetGenerator := ∀ r : R, ∀ n k : J, ∀ a : D n k, (F n k).obj a ⟶ N r n k

/-- The complete original Iso-inverse generator function. -/
def inverseLegs (e : ∀ n k : J, M n k ≅ colimit (F n k)) : SourceGenerator F (M := M) :=
  fun n k a => colimit.ι (F n k) a ≫ (e n k).inv

/-- The whole source-colimit characteristic of the target map function. -/
def targetLegs (t : ∀ r : R, ∀ n k : J, colimit (F n k) ⟶ N r n k) :
    TargetGenerator F (N := N) := fun r n k a => colimit.ι (F n k) a ≫ t r n k

/-- Every original generator followed by the complete Hom-map function. -/
def generatorAfter (g : SourceGenerator F (M := M))
    (f : CoendEquationTransport.HomMap M N) : TargetGenerator F (N := N) :=
  fun r n k a => g n k a ≫ f r n k

/-- The full original Iso-forward function followed by the actual colimit descent. -/
def isoForwardDescent (e : ∀ n k : J, M n k ≅ colimit (F n k))
    (t : ∀ r : R, ∀ n k : J, colimit (F n k) ⟶ N r n k) :
    CoendEquationTransport.HomMap M N := fun r n k => (e n k).hom ≫ t r n k

/-- The actual complete cocone-descent function on the original diagrams. -/
def coconeDesc (c : ∀ _r : R, ∀ n k : J, Cocone (F n k)) :
    ∀ r : R, ∀ n k : J, colimit (F n k) ⟶ (c r n k).pt :=
  fun r n k => colimit.desc (F n k) (c r n k)

/-- Every full component of the original cocone function. -/
def coconeComponents (c : ∀ _r : R, ∀ n k : J, Cocone (F n k)) :=
  fun (r : R) (n k : J) (a : D n k) => (c r n k).ι.app a

/-- The full colimit-descent characteristic is proved before any native source object is applied. -/
theorem coconeDesc_legs_function (c : ∀ _r : R, ∀ n k : J, Cocone (F n k)) :
    targetLegs F (coconeDesc F c) = coconeComponents F c := by
  funext r n k a
  exact colimit.ι_desc (c r n k) a

/-- The actual whole inverse and generator characteristics determine the
full Hom function through the fixed original Iso and colimit universal property. -/
theorem hom_eq_of_full_generators (e : ∀ n k : J, M n k ≅ colimit (F n k))
    (g : SourceGenerator F (M := M)) (f : CoendEquationTransport.HomMap M N)
    (t : ∀ r : R, ∀ n k : J, colimit (F n k) ⟶ N r n k)
    (hInverse : inverseLegs F e = g) (hAfter : generatorAfter F g f = targetLegs F t) :
    f = isoForwardDescent F e t := by
  funext r n k
  apply (cancel_epi (e n k).inv).1
  apply colimit.hom_ext
  intro a
  have hb := congrArg (fun Φ => Φ n k a) hInverse
  have hg := congrArg (fun Φ => Φ r n k a) hAfter
  change colimit.ι (F n k) a ≫ (e n k).inv = g n k a at hb
  change g n k a ≫ f r n k = colimit.ι (F n k) a ≫ t r n k at hg
  change colimit.ι (F n k) a ≫ ((e n k).inv ≫ f r n k) =
    colimit.ι (F n k) a ≫ ((e n k).inv ≫ ((e n k).hom ≫ t r n k))
  calc
    _ = (colimit.ι (F n k) a ≫ (e n k).inv) ≫ f r n k := (Category.assoc _ _ _).symm
    _ = g n k a ≫ f r n k := congrArg (fun q => q ≫ f r n k) hb
    _ = colimit.ι (F n k) a ≫ t r n k := hg
    _ = _ := by simp only [Iso.inv_hom_id_assoc]


variable {N' : R → J → J → C}

/-- Actual target-object function identity transports the complete target-map type. -/
theorem target_map_type_eq (hN : N = N') :
    (∀ r : R, ∀ n k : J, colimit (F n k) ⟶ N r n k) =
      (∀ r : R, ∀ n k : J, colimit (F n k) ⟶ N' r n k) := by
  cases hN
  rfl

/-- The full target-leg functions respect the actual target-object and map-function identities. -/
theorem target_legs_function_heq
    (t : ∀ r : R, ∀ n k : J, colimit (F n k) ⟶ N r n k)
    (t' : ∀ r : R, ∀ n k : J, colimit (F n k) ⟶ N' r n k)
    (hN : N = N') (ht : HEq t t') : HEq (targetLegs F t) (targetLegs F t') := by
  cases hN
  cases eq_of_heq ht
  rfl

/-- The entire original cocone descent characteristic is heterogeneous
at its exact complete function type before a native target family is substituted. -/
theorem coconeDesc_legs_function_heq (c : ∀ _r : R, ∀ n k : J, Cocone (F n k)) :
    HEq (targetLegs F (coconeDesc F c)) (coconeComponents F c) :=
  heq_of_eq (coconeDesc_legs_function F c)

end ColimitHomFamily
end CategoryTheory.Functor
