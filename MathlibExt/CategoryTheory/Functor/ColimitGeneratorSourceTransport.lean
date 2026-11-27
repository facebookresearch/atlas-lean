/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Functor.ColimitHomFamilyFunctions
public import MathlibExt.CategoryTheory.Enriched.CoendGeneratorEquationTransport

/-!
# Whole generator equation types under actual source-object identities

The source diagram object function and the original coefficient object
function are identified by a proved whole function equality. Their actual
complete generator functions are transported before any source object or
label is supplied. The source and target Hom-object families stay fixed.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section

universe uC vC uJ uR uD vD uE

open CategoryTheory CategoryTheory.Limits

open CategoryTheory.Enriched

namespace CategoryTheory.Functor
namespace BlockGeneratorSourceTransport

variable {C : Type uC} [Category.{vC} C] {J : Type uJ} {R : Type uR}
  {D : J → J → Type uD} {M : J → J → C} {N : R → J → J → C}

/-- Every actual original source object in the full diagram family. -/
abbrev Objects := ∀ n k : J, D n k → C

/-- The entire generator function on one fixed original source-object family. -/
abbrev Source (O : Objects (C := C) (D := D)) :=
  ∀ n k : J, ∀ a : D n k, O n k a ⟶ M n k

/-- Every complete target generator on the same original source-object family. -/
abbrev Target (O : Objects (C := C) (D := D)) :=
  ∀ r : R, ∀ n k : J, ∀ a : D n k, O n k a ⟶ N r n k

/-- The complete source-generator function followed by the actual Hom-map function. -/
def afterHom {O : Objects (C := C) (D := D)} (g : Source (M := M) O)
    (m : CoendEquationTransport.HomMap M N) : Target (N := N) O :=
  fun r n k a => g n k a ≫ m r n k

/-- The exact full diagram-generator equation, with both Hom families fixed. -/
def Condition {O : Objects (C := C) (D := D)} (g : Source (M := M) O)
    (g' : Target (N := N) O) (m : CoendEquationTransport.HomMap M N) : Prop :=
  afterHom g m = g'

/-- Whole actual source-object identity identifies the entire source-generator type. -/
theorem source_type_eq {O O' : Objects (C := C) (D := D)} (hO : O = O') :
    Source (M := M) O = Source (M := M) O' := by
  cases hO
  rfl

/-- The full target-generator type respects the same actual source-object identity. -/
theorem target_type_eq {O O' : Objects (C := C) (D := D)} (hO : O = O') :
    Target (N := N) O = Target (N := N) O' := by
  cases hO
  rfl

/-- Actual whole source-object and generator identities identify the complete equation type. -/
theorem condition_type_eq {O O' : Objects (C := C) (D := D)}
    (g : Source (M := M) O) (g₁ : Source (M := M) O')
    (g' : Target (N := N) O) (g₁' : Target (N := N) O')
    (m : CoendEquationTransport.HomMap M N) (hO : O = O')
    (hg : HEq g g₁) (hg' : HEq g' g₁') :
    Condition g g' m = Condition g₁ g₁' m := by
  cases hO
  cases eq_of_heq hg
  cases eq_of_heq hg'
  rfl

section Colimit
variable [∀ n k : J, Category.{vD} (D n k)] (F : ∀ n k : J, D n k ⥤ C)

/-- The complete original diagram object function. -/
abbrev diagramObjects : Objects (C := C) (D := D) := fun n k a => (F n k).obj a

/-- The whole colimit-generator equation is the same exact source-family equation. -/
theorem colimit_condition_type_eq
    (g : ColimitHomFamily.SourceGenerator F (M := M))
    (g' : ColimitHomFamily.TargetGenerator F (N := N))
    (m : CoendEquationTransport.HomMap M N) :
    Condition (O := diagramObjects F) g g' m =
      (ColimitHomFamily.generatorAfter F g m = g') := rfl
end Colimit

section Restricted
variable {E : J → J → J → Type uE} {T : J → C}

/-- The entire original coefficient-source object function on diagram labels. -/
abbrev restrictedObjects (a : ∀ n k : J, D n k → J) : Objects (C := C) (D := D) :=
  fun n k d => T (a n k d)

/-- The complete restricted generator equation is the same exact equation
at the original coefficient source-object family before native data is applied. -/
theorem restricted_condition_type_eq (a : ∀ n k : J, D n k → J)
    (label : ∀ n k : J, ∀ d : D n k, E n k (a n k d))
    (g : CoendGeneratorTransport.SourceGenerator (E := E) (T := T) (M := M))
    (g' : CoendGeneratorTransport.TargetGenerator (E := E) (T := T) (N := N))
    (m : CoendEquationTransport.HomMap M N) :
    Condition (O := restrictedObjects (T := T) a)
      (CoendGeneratorTransport.restrictSource a label g)
      (CoendGeneratorTransport.restrictTarget a label g') m =
      (CoendGeneratorTransport.restrictedHomComposite a label g m =
        CoendGeneratorTransport.restrictTarget a label g') := rfl
end Restricted

end BlockGeneratorSourceTransport
end CategoryTheory.Functor
