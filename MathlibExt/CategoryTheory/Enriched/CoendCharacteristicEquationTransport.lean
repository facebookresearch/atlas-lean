/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Whole characteristic equation types under actual Hom-family identities

The full source and target integrands and coefficient objects remain fixed.
An equality of the actual Hom-object families and heterogeneous equalities
of the complete insertion and Hom-map functions identify the entire equation
type. No characteristic, balancing, identity or composition law is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section

universe uV vV uJ uR

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Enriched
namespace CoendEquationTransport

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {J : Type uJ} {R : Type uR}

/-- The entire original source insertion family, before any coefficient is applied. -/
abbrev SourceInsertion (W : J → J → J → V) (T : J → V) (M : J → J → V) :=
  ∀ n k a : J, (W n k a ⊗ T a) ⟶ M n k

/-- The entire target insertion family with all original shift indices retained. -/
abbrev TargetInsertion (W : R → J → J → J → V) (T : J → V) (N : R → J → J → V) :=
  ∀ r : R, ∀ n k a : J, (W r n k a ⊗ T a) ⟶ N r n k

/-- The whole Hom-map family on the exact source and target object functions. -/
abbrev HomMap (M : J → J → V) (N : R → J → J → V) :=
  ∀ r : R, ∀ n k : J, M n k ⟶ N r n k

/-- The full weight-map family, retaining both complete weight objects. -/
abbrev WeightMap (W : J → J → J → V) (W' : R → J → J → J → V) :=
  ∀ r : R, ∀ n k a : J, W n k a ⟶ W' r n k a

variable {W : J → J → J → V} {W' : R → J → J → J → V} {T : J → V}
  {M M' : J → J → V} {N N' : R → J → J → V}

/-- The complete insertion followed by the complete original Hom map. -/
def sourceComposite (j : SourceInsertion W T M) (m : HomMap M N) :=
  fun (r : R) (n k a : J) => j n k a ≫ m r n k

/-- The whole unchanged coefficient whisker followed by the complete target insertion. -/
def targetComposite (j' : TargetInsertion W' T N) (w : WeightMap W W') :=
  fun (r : R) (n k a : J) => (w r n k a ▷ T a) ≫ j' r n k a

/-- The exact entire characteristic equation on the original full integrands. -/
def Condition (j : SourceInsertion W T M) (j' : TargetInsertion W' T N)
    (m : HomMap M N) (w : WeightMap W W') : Prop :=
  sourceComposite j m = targetComposite j' w

/-- Equality of the actual objects identifies the full source-insertion type. -/
theorem source_type_eq (hM : M = M') :
    SourceInsertion W T M = SourceInsertion W T M' := by
  cases hM
  rfl

/-- Equality of the actual target objects identifies every full target-insertion type. -/
theorem target_type_eq (hN : N = N') :
    TargetInsertion W' T N = TargetInsertion W' T N' := by
  cases hN
  rfl

omit [MonoidalCategory V] in
/-- Both whole object identities identify the entire original Hom-map type. -/
theorem hom_type_eq (hM : M = M') (hN : N = N') : HomMap M N = HomMap M' N' := by
  cases hM
  cases hN
  rfl

/-- Whole source and Hom-function identities preserve the complete source composite. -/
theorem source_composite_heq (j : SourceInsertion W T M) (j₁ : SourceInsertion W T M')
    (m : HomMap M N) (m₁ : HomMap M' N') (hM : M = M') (hN : N = N')
    (hj : HEq j j₁) (hm : HEq m m₁) :
    HEq (sourceComposite j m) (sourceComposite j₁ m₁) := by
  cases hM
  cases hN
  cases eq_of_heq hj
  cases eq_of_heq hm
  rfl

/-- The complete target composite respects the actual target and weight-function identities. -/
theorem target_composite_heq (j' : TargetInsertion W' T N)
    (j₁' : TargetInsertion W' T N') (w w₁ : WeightMap W W') (hN : N = N')
    (hj : HEq j' j₁') (hw : w = w₁) :
    HEq (targetComposite j' w) (targetComposite j₁' w₁) := by
  cases hN
  cases eq_of_heq hj
  cases hw
  rfl

/-- Actual whole object and function identities identify the complete
characteristic equation type. -/
theorem condition_eq (j : SourceInsertion W T M) (j₁ : SourceInsertion W T M')
    (j' : TargetInsertion W' T N) (j₁' : TargetInsertion W' T N')
    (m : HomMap M N) (m₁ : HomMap M' N') (w w₁ : WeightMap W W')
    (hM : M = M') (hN : N = N') (hj : HEq j j₁) (hj' : HEq j' j₁')
    (hm : HEq m m₁) (hw : w = w₁) :
    Condition j j' m w = Condition j₁ j₁' m₁ w₁ := by
  cases hM
  cases hN
  cases eq_of_heq hj
  cases eq_of_heq hj'
  cases eq_of_heq hm
  cases hw
  rfl

end CoendEquationTransport
end CategoryTheory.Enriched
