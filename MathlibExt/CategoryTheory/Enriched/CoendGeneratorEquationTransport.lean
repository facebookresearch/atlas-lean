/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.CoendCharacteristicEquationTransport

/-!
# Full generator equations from the actual characteristic functions

The complete coend characteristic and coefficient-label naturality imply
the complete labelled-generator equation. Source and target objects, labels,
weights and coefficient functions remain fixed throughout the construction.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section

universe uV vV uJ uR uE uD

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Enriched
namespace CoendGeneratorTransport

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {J : Type uJ} {R : Type uR} {E : J → J → J → Type uE}
  {W : J → J → J → V} {W' : R → J → J → J → V} {T : J → V}
  {M : J → J → V} {N : R → J → J → V}

/-- Every original labelled source coefficient insertion. -/
abbrev SourceCoefficient :=
  ∀ n k a : J, E n k a → (T a ⟶ W n k a ⊗ T a)

/-- Every whole shifted coefficient insertion at its original full label. -/
abbrev TargetCoefficient :=
  ∀ r : R, ∀ n k a : J, E n k a → (T a ⟶ W' r n k a ⊗ T a)

/-- The complete original labelled source generator family. -/
abbrev SourceGenerator := ∀ n k a : J, E n k a → (T a ⟶ M n k)

/-- The complete original labelled target generator family. -/
abbrev TargetGenerator := ∀ r : R, ∀ n k a : J, E n k a → (T a ⟶ N r n k)

/-- Coefficient insertion followed by the complete actual source coend insertion. -/
def sourceGenerator (i : SourceCoefficient (E := E) (W := W) (T := T))
    (j : CoendEquationTransport.SourceInsertion W T M) :
    SourceGenerator (E := E) (T := T) (M := M) :=
  fun n k a f => i n k a f ≫ j n k a

/-- The original full shifted coefficient followed by its complete target insertion. -/
def targetGenerator (i' : TargetCoefficient (E := E) (W' := W') (T := T))
    (j' : CoendEquationTransport.TargetInsertion W' T N) :
    TargetGenerator (E := E) (T := T) (N := N) :=
  fun r n k a f => i' r n k a f ≫ j' r n k a

/-- The full actual source generator followed by the complete Hom-map function. -/
def homComposite (g : SourceGenerator (E := E) (T := T) (M := M))
    (m : CoendEquationTransport.HomMap M N) : TargetGenerator (E := E) (T := T) (N := N) :=
  fun r n k a f => g n k a f ≫ m r n k

/-- The entire original coefficient-label naturality function equation. -/
def CoefficientCondition (i : SourceCoefficient (E := E) (W := W) (T := T))
    (i' : TargetCoefficient (E := E) (W' := W') (T := T))
    (w : CoendEquationTransport.WeightMap W W') : Prop :=
  (fun (r : R) (n k a : J) (f : E n k a) => i n k a f ≫ (w r n k a ▷ T a)) = i'

/-- The exact complete original labelled-generator/Hom-map equation. -/
def Condition (g : SourceGenerator (E := E) (T := T) (M := M))
    (g' : TargetGenerator (E := E) (T := T) (N := N))
    (m : CoendEquationTransport.HomMap M N) : Prop :=
  homComposite g m = g'

/-- The full coend characteristic and whole coefficient equation derive
every original generator equation before a native Hom input is applied. -/
theorem condition_of_characteristic
    (i : SourceCoefficient (E := E) (W := W) (T := T))
    (i' : TargetCoefficient (E := E) (W' := W') (T := T))
    (j : CoendEquationTransport.SourceInsertion W T M)
    (j' : CoendEquationTransport.TargetInsertion W' T N)
    (m : CoendEquationTransport.HomMap M N) (w : CoendEquationTransport.WeightMap W W')
    (hC : CoendEquationTransport.Condition j j' m w) (hI : CoefficientCondition i i' w) :
    Condition (sourceGenerator i j) (targetGenerator i' j') m := by
  funext r n k a f
  have hc := congrArg (fun Φ => Φ r n k a) hC
  have hi := congrArg (fun Φ => Φ r n k a f) hI
  change j n k a ≫ m r n k = (w r n k a ▷ T a) ≫ j' r n k a at hc
  change i n k a f ≫ (w r n k a ▷ T a) = i' r n k a f at hi
  change (i n k a f ≫ j n k a) ≫ m r n k = i' r n k a f ≫ j' r n k a
  rw [Category.assoc, hc, ← Category.assoc, hi]

omit [MonoidalCategory V] in
/-- Actual identities of both whole generator functions identify their complete equation type. -/
theorem condition_eq
    (g g₁ : SourceGenerator (E := E) (T := T) (M := M))
    (g' g₁' : TargetGenerator (E := E) (T := T) (N := N))
    (m : CoendEquationTransport.HomMap M N) (hg : g = g₁) (hg' : g' = g₁') :
    Condition g g' m = Condition g₁ g₁' m := by
  cases hg
  cases hg'
  rfl


variable {D : J → J → Type uD}

/-- Restrict the whole original source-generator function to original diagram labels. -/
def restrictSource (a : ∀ n k : J, D n k → J)
    (label : ∀ n k : J, ∀ d : D n k, E n k (a n k d))
    (g : SourceGenerator (E := E) (T := T) (M := M)) :=
  fun (n k : J) (d : D n k) => g n k (a n k d) (label n k d)

/-- Restrict the complete target-generator function to the same original labels. -/
def restrictTarget (a : ∀ n k : J, D n k → J)
    (label : ∀ n k : J, ∀ d : D n k, E n k (a n k d))
    (g' : TargetGenerator (E := E) (T := T) (N := N)) :=
  fun (r : R) (n k : J) (d : D n k) => g' r n k (a n k d) (label n k d)

/-- The entire source-generator/Hom function restricted by its original diagram labels. -/
def restrictedHomComposite (a : ∀ n k : J, D n k → J)
    (label : ∀ n k : J, ∀ d : D n k, E n k (a n k d))
    (g : SourceGenerator (E := E) (T := T) (M := M))
    (m : CoendEquationTransport.HomMap M N) :=
  restrictTarget a label (homComposite g m)

omit [MonoidalCategory V] in
/-- A proved complete generator equation gives the whole original diagram-generator equation. -/
theorem restricted_condition_function (a : ∀ n k : J, D n k → J)
    (label : ∀ n k : J, ∀ d : D n k, E n k (a n k d))
    (g : SourceGenerator (E := E) (T := T) (M := M))
    (g' : TargetGenerator (E := E) (T := T) (N := N))
    (m : CoendEquationTransport.HomMap M N) (h : Condition g g' m) :
    restrictedHomComposite a label g m = restrictTarget a label g' :=
  congrArg (restrictTarget a label) h

end CoendGeneratorTransport
end CategoryTheory.Enriched
