/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import Mathlib.Basic.Finite.Sigma
public import Mathlib.CategoryTheory.EqToHom
public import MathlibExt.CategoryTheory.Reedy.Basic
public import MathlibExt.CategoryTheory.Reedy.Boundary

section

-- Author: @toskua, Codex


/-!
# Opposite ordinary Reedy structures

The opposite structure keeps the original degree and reverses the two
original factor arrows. Its direct and inverse properties are the opposite
of the original inverse and direct properties, respectively.
-/

@[expose] public section

set_option autoImplicit false

universe uJ vJ uD

namespace CategoryTheory

open MorphismProperty

variable {J : Type uJ} [Category.{vJ} J]

namespace ReedyFactorization

variable {direct inverse : MorphismProperty J} {i j : J} {f : i ⟶ j}

/-- Equality of complete original factor records from their object and both maps. -/
@[ext]
theorem ext {a b : ReedyFactorization direct inverse f}
    (hm : a.middle = b.middle)
    (hi : HEq a.inverseMap b.inverseMap)
    (hd : HEq a.directMap b.directMap) : a = b := by
  cases a
  cases b
  cases hm
  cases hi
  cases hd
  rfl

/-- The original factor record, with both arrows reversed. -/
abbrev op (a : ReedyFactorization direct inverse f) :
    ReedyFactorization inverse.op direct.op f.op :=
      MorphismProperty.MapFactorizationData.op inverse direct a

variable {direct' inverse' : MorphismProperty Jᵒᵖ} {i' j' : Jᵒᵖ} {f' : i' ⟶ j'}

/-- The original opposite factor record, with both arrows unopposed. -/
abbrev unop (a : ReedyFactorization direct' inverse' f') :
    ReedyFactorization inverse'.unop direct'.unop f'.unop :=
  MorphismProperty.MapFactorizationData.unop a

/-- Opposing after unopposing retains the whole original factor record. -/
@[simp]
theorem op_unop (a : ReedyFactorization direct' inverse' f') : a.unop.op = a := by
  cases a
  rfl

/-- Unopposing after opposing retains the whole original factor record. -/
@[simp]
theorem unop_op (a : ReedyFactorization direct inverse f) : a.op.unop = a := by
  cases a
  rfl

/-- Unopposing is injective on complete original factor records. -/
theorem unop_injective :
    Function.Injective (unop (direct' := direct') (inverse' := inverse') (f' := f')) := by
  intro a b h
  have := congrArg op h
  simpa only [MorphismProperty.op_unop, Quiver.Hom.op_unop, op_unop] using this

end ReedyFactorization

namespace ReedyStructure

variable {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)

/-- The opposite ordinary Reedy structure, retaining the degree and both original subcategories. -/
noncomputable def op : ReedyStructure Jᵒᵖ D where
  degree j := r.degree j.unop
  direct := r.inverse.op
  inverse := r.direct.op
  direct_multiplicative := inferInstance
  inverse_multiplicative := inferInstance
  native := r.native.op
  native_degree j := r.native_degree j.unop
  factor f := (r.factor f.unop).op

/-- The opposite degree is the original object's unchanged degree. -/
@[simp]
theorem op_degree (j : Jᵒᵖ) : r.op.degree j = r.degree j.unop := rfl

/-- The opposite direct maps are exactly the original inverse maps. -/
@[simp]
theorem op_direct {i j : Jᵒᵖ} (f : i ⟶ j) : r.op.direct f ↔ r.inverse f.unop := Iff.rfl

/-- The opposite inverse maps are exactly the original direct maps. -/
@[simp]
theorem op_inverse {i j : Jᵒᵖ} (f : i ⟶ j) : r.op.inverse f ↔ r.direct f.unop := Iff.rfl

/-- The opposite middle object is the opposite of the original middle object. -/
@[simp]
theorem op_factor_middle {i j : Jᵒᵖ} (f : i ⟶ j) :
    (r.op.factor f).middle = Opposite.op (r.factor f.unop).middle := rfl

/-- The opposite inverse arrow is the opposite of the original direct arrow. -/
@[simp]
theorem op_factor_inverseMap {i j : Jᵒᵖ} (f : i ⟶ j) :
    (r.op.factor f).inverseMap = (r.factor f.unop).directMap.op := rfl

/-- The opposite direct arrow is the opposite of the original inverse arrow. -/
@[simp]
theorem op_factor_directMap {i j : Jᵒᵖ} (f : i ⟶ j) :
    (r.op.factor f).directMap = (r.factor f.unop).inverseMap.op := rfl

end ReedyStructure

end CategoryTheory

end
end

section

-- Author: @toskua, Codex


/-!
# Finite ordinary Reedy boundaries from the actual bounded arrows

The actual latching and matching objects are encoded by their original
lower-degree endpoint and original direct or inverse map. Thus finite
degree downsets and finite original Hom types give finite boundaries.
No completeness property of the coefficient category is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe uJ vJ uD

namespace CategoryTheory.ReedyStructure

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)

/-- The original object downset strictly below a supplied Reedy degree. -/
abbrev BelowDegree (d : D) := {j : J // r.degree j < d}

/-- A latching object retains its exact lower endpoint and original direct arrow. -/
abbrev LatchingCode (j : J) :=
  Σ k : r.BelowDegree (r.degree j), {f : k.val ⟶ j // r.direct f}

/-- A matching object retains its exact lower endpoint and original inverse arrow. -/
abbrev MatchingCode (j : J) :=
  Σ k : r.BelowDegree (r.degree j), {f : j ⟶ k.val // r.inverse f}

/-- Encode each actual original latching object by its endpoint and direct arrow. -/
def latchingCode (j : J) (a : r.Latching j) : r.LatchingCode j :=
  ⟨⟨r.latchingSource a, a.property⟩, ⟨r.latchingArrow a, a.obj.hom.property⟩⟩

/-- Reconstruct the complete actual latching object from its original endpoint and arrow. -/
def latchingOfCode (j : J) (a : r.LatchingCode j) : r.Latching j :=
  r.latchingMk a.2.val a.2.property a.1.property

/-- Both original latching object fields are retained by encoding and reconstruction. -/
@[simp]
theorem latchingOfCode_code (j : J) (a : r.Latching j) :
    r.latchingOfCode j (r.latchingCode j a) = a := rfl

/-- Both original latching code fields are retained by reconstruction and encoding. -/
@[simp]
theorem latchingCode_ofCode (j : J) (a : r.LatchingCode j) :
    r.latchingCode j (r.latchingOfCode j a) = a := rfl

/-- The complete original latching objects are exactly the original bounded direct arrows. -/
def latchingCodeEquiv (j : J) : r.Latching j ≃ r.LatchingCode j where
  toFun := r.latchingCode j
  invFun := r.latchingOfCode j
  left_inv := r.latchingOfCode_code j
  right_inv := r.latchingCode_ofCode j

/-- Encode each actual original matching object by its endpoint and inverse arrow. -/
def matchingCode (j : J) (a : r.Matching j) : r.MatchingCode j :=
  ⟨⟨r.matchingTarget a, a.property⟩, ⟨r.matchingArrow a, a.obj.hom.property⟩⟩

/-- Reconstruct the complete actual matching object from its original endpoint and arrow. -/
def matchingOfCode (j : J) (a : r.MatchingCode j) : r.Matching j :=
  r.matchingMk a.2.val a.2.property a.1.property

/-- Both original matching object fields are retained by encoding and reconstruction. -/
@[simp]
theorem matchingOfCode_code (j : J) (a : r.Matching j) :
    r.matchingOfCode j (r.matchingCode j a) = a := rfl

/-- Both original matching code fields are retained by reconstruction and encoding. -/
@[simp]
theorem matchingCode_ofCode (j : J) (a : r.MatchingCode j) :
    r.matchingCode j (r.matchingOfCode j a) = a := rfl

/-- The complete original matching objects are exactly the original bounded inverse arrows. -/
def matchingCodeEquiv (j : J) : r.Matching j ≃ r.MatchingCode j where
  toFun := r.matchingCode j
  invFun := r.matchingOfCode j
  left_inv := r.matchingOfCode_code j
  right_inv := r.matchingCode_ofCode j

/-- A latching comparison retains its complete original underlying triangle. -/
theorem latchingComparison_injective (j : J) (a b : r.Latching j) :
    Function.Injective (r.latchingComparison (a := a) (c := b)) := by
  intro f g h
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext f.hom g.hom
  exact WideSubcategory.hom_ext r.direct h

/-- A matching comparison retains its complete original underlying triangle. -/
theorem matchingComparison_injective (j : J) (a b : r.Matching j) :
    Function.Injective (r.matchingComparison (a := a) (c := b)) := by
  intro f g h
  apply ObjectProperty.hom_ext
  apply StructuredArrow.hom_ext f.hom g.hom
  exact WideSubcategory.hom_ext r.inverse h

variable [∀ i j : J, Finite (i ⟶ j)]

/-- Finite actual lower-degree objects give finite actual latching objects. -/
instance finiteLatching (j : J) [Finite (r.BelowDegree (r.degree j))] : Finite (r.Latching j) :=
  Finite.of_equiv (r.LatchingCode j) (r.latchingCodeEquiv j).symm

/-- Finite actual lower-degree objects give finite actual matching objects. -/
instance finiteMatching (j : J) [Finite (r.BelowDegree (r.degree j))] : Finite (r.Matching j) :=
  Finite.of_equiv (r.MatchingCode j) (r.matchingCodeEquiv j).symm

/-- Actual latching comparison types are finite because their original arrow types are finite. -/
instance finiteLatchingHom (j : J) (a b : r.Latching j) : Finite (a ⟶ b) :=
  Finite.of_injective _ (r.latchingComparison_injective j a b)

/-- Actual matching comparison types are finite because their original arrow types are finite. -/
instance finiteMatchingHom (j : J) (a b : r.Matching j) : Finite (a ⟶ b) :=
  Finite.of_injective _ (r.matchingComparison_injective j a b)

omit [∀ i j : J, Finite (i ⟶ j)] in
/-- A least-degree original object has an empty actual latching boundary. -/
theorem latching_isEmpty_of_degree_eq_bot [OrderBot D] (j : J) (hj : r.degree j = ⊥) :
    IsEmpty (r.Latching j) :=
  ⟨fun a => by simpa only [latchingObjects, hj, not_lt_bot] using a.property⟩

omit [∀ i j : J, Finite (i ⟶ j)] in
/-- A least-degree original object has an empty actual matching boundary. -/
theorem matching_isEmpty_of_degree_eq_bot [OrderBot D] (j : J) (hj : r.degree j = ⊥) :
    IsEmpty (r.Matching j) :=
  ⟨fun a => by simpa only [matchingObjects, hj, not_lt_bot] using a.property⟩

end CategoryTheory.ReedyStructure

end
end

section

-- Author: @toskua, Codex


/-!
# Original Reedy boundaries and opposite categories

Every original opposite matching arrow is the unop of the same original latching arrow.
The actual Over/Under triangles and original direct/inverse/degree conditions give the
complete indexing equivalence. All original coefficient diagrams and maps are retained.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uJ vJ uD uC vC

open CategoryTheory Opposite Limits

namespace CategoryTheory.ReedyStructure.BoundaryOpposite

variable {J : Type uJ} [Category.{vJ} J]
variable {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)

/-- The original opposite matching object is the same original unop proper direct arrow. -/
def matchingToLatchingObj (j : J) (a : r.op.Matching (Opposite.op j)) : r.Latching j :=
  r.latchingMk (r.op.matchingArrow a).unop a.obj.hom.property a.property

/-- Every original opposite matching comparison retains its entire original unop triangle. -/
def matchingToLatchingHom {j : J} {a b : r.op.Matching (Opposite.op j)} (f : a ⟶ b) :
    matchingToLatchingObj r j b ⟶ matchingToLatchingObj r j a :=
  ObjectProperty.homMk (Over.homMk ⟨(r.op.matchingComparison f).unop, f.hom.right.property⟩ (by
    apply WideSubcategory.hom_ext
    change (r.op.matchingComparison f).unop ≫ (r.op.matchingArrow a).unop =
      (r.op.matchingArrow b).unop
    rw [← unop_comp, r.op.matchingArrow_comparison]))

/-- The original matching index of the opposite is the original opposite latching index. -/
def matchingToLatching (j : J) : r.op.Matching (Opposite.op j) ⥤ (r.Latching j)ᵒᵖ where
  obj a := Opposite.op (matchingToLatchingObj r j a)
  map f := (matchingToLatchingHom r f).op
  map_id a := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext (r.latchingObjects j)
    apply CostructuredArrow.hom_ext
    apply WideSubcategory.hom_ext
    rfl
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext (r.latchingObjects j)
    apply CostructuredArrow.hom_ext
    apply WideSubcategory.hom_ext
    rfl

/-- Every original latching object supplies the same original opposite matching arrow. -/
def latchingToMatchingObj (j : J) (a : r.Latching j) : r.op.Matching (Opposite.op j) :=
  r.op.matchingMk (r.latchingArrow a).op a.obj.hom.property a.property

/-- Every original latching comparison supplies the same actual opposite Under triangle. -/
def latchingToMatchingHom {j : J} {a b : r.Latching j} (f : a ⟶ b) :
    latchingToMatchingObj r j b ⟶ latchingToMatchingObj r j a :=
  ObjectProperty.homMk (Under.homMk ⟨(r.latchingComparison f).op, f.hom.left.property⟩ (by
    apply WideSubcategory.hom_ext
    change (r.latchingArrow b).op ≫ (r.latchingComparison f).op = (r.latchingArrow a).op
    rw [← op_comp, r.latchingComparison_arrow]))

/-- The original opposite latching index returns to the actual opposite matching index. -/
def latchingToMatching (j : J) : (r.Latching j)ᵒᵖ ⥤ r.op.Matching (Opposite.op j) where
  obj a := latchingToMatchingObj r j a.unop
  map f := latchingToMatchingHom r f.unop
  map_id a := by
    apply ObjectProperty.hom_ext (r.op.matchingObjects (Opposite.op j))
    apply StructuredArrow.hom_ext
    apply WideSubcategory.hom_ext
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext (r.op.matchingObjects (Opposite.op j))
    apply StructuredArrow.hom_ext
    apply WideSubcategory.hom_ext
    rfl

/-- The complete original boundary indexing equivalence uses the same actual arrows and
triangles. -/
def equivalence (j : J) : r.op.Matching (Opposite.op j) ≌ (r.Latching j)ᵒᵖ where
  functor := matchingToLatching r j
  inverse := latchingToMatching r j
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp a := by
    change (matchingToLatching r j).map (𝟙 a) ≫ 𝟙 _ = 𝟙 _
    rw [Functor.map_id, Category.id_comp]

/-- The forward index map retains the same original unop target/source. -/
theorem matchingToLatching_source (j : J) (a : r.op.Matching (Opposite.op j)) :
    r.latchingSource ((matchingToLatching r j).obj a).unop = (r.op.matchingTarget a).unop := rfl

/-- The forward index map retains the same entire original unop boundary arrow. -/
theorem matchingToLatching_arrow (j : J) (a : r.op.Matching (Opposite.op j)) :
    r.latchingArrow ((matchingToLatching r j).obj a).unop = (r.op.matchingArrow a).unop := rfl

/-- The forward index map retains the same entire original unop comparison arrow. -/
theorem matchingToLatching_comparison {j : J} {a b : r.op.Matching (Opposite.op j)} (f : a ⟶ b) :
    r.latchingComparison ((matchingToLatching r j).map f).unop =
      (r.op.matchingComparison f).unop := rfl

variable {C : Type uC} [Category.{vC} C]

/-- The whole actual opposite matching diagram is the same original opposite latching diagram. -/
def diagramIso (X : J ⥤ C) (j : J) :
    r.op.matchingDiagram X.op (Opposite.op j) ≅
      matchingToLatching r j ⋙ (r.latchingDiagram X j).op :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro a b f
    change (X.map (r.op.matchingComparison f).unop).op ≫ 𝟙 _ =
      𝟙 _ ≫ (X.map (r.op.matchingComparison f).unop).op
    rw [Category.comp_id, Category.id_comp])

end CategoryTheory.ReedyStructure.BoundaryOpposite

end
end
end
