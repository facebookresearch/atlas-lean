/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Order.DirectedInverseSystem
public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.NClassStageTransition

/-!
# The raw direct limit of literal finite-stage homotopy classes

For a proof `h : i <= j`, the transition map is the already constructed
offset map by `j - i`, transported along `Nat.add_sub_of_le h`.  Its identity
and composition laws make the literal classes a genuine `DirectedSystem` of
types.  Mathlib's arbitrary-type `DirectLimit` then supplies the raw colimit,
its canonical stage maps, and its universal lift.

No additive, group, algebraic, or E-theory structure is placed on the
colimit.  In particular this file does not define products, flattening,
surjectivity, or the disputed shifted map in Blackadar 25.7.4.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra

attribute [local instance] AsymptoticAlgebra.cStarAlgebra

namespace IteratedAsymptoticAlgebra

universe uA uB uC

/-! ## Explicit transport and proof-indexed stage maps -/

/-- Transport literal classes across an equality of finite stage indices. -/
def nClassesCast {n m : ℕ}
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (h : n = m) : NClasses n A B → NClasses m A B := by
  cases h
  exact id

@[simp]
theorem nClassesCast_rfl (n : ℕ)
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (q : NClasses n A B) :
    nClassesCast A B rfl q = q :=
  rfl


/- A generic stage equality can be eliminated before specializing to an
arithmetic index; this transports the actual class of the composed hom. -/
private theorem nClassesCast_classOf_comp_castTarget
    {i m m' : ℕ}
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (h : m = m')
    (F : IteratedAsymptoticAlgebra i B →⋆ₙₐ[ℂ]
      IteratedAsymptoticAlgebra m B)
    (phi : HomN i A B) :
    nClassesCast A B h (classOf m (F.comp phi)) =
      classOf m'
        ((cast
          (congrArg
            (fun j => IteratedAsymptoticAlgebra i B →⋆ₙₐ[ℂ]
              IteratedAsymptoticAlgebra j B) h) F).comp phi) := by
  cases h
  rfl

/- Equal offsets give the same transported transition after carrying both
target-equality proofs explicitly. Only independent equalities are eliminated. -/
private theorem nClassesCast_stageTransitionFrom_offset
    {i d d' j : ℕ}
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (hd : d = d') (h : i + d = j) (h' : i + d' = j)
    (q : NClasses i A B) :
    nClassesCast A B h (stageTransitionFrom i d A B q) =
      nClassesCast A B h' (stageTransitionFrom i d' A B q) := by
  cases hd
  have hh : h = h' := Subsingleton.elim _ _
  cases hh
  rfl

/-- The stage map attached to a proof `i <= j`.  Its computational offset is
literally `j-i`; the result is transported into stage `j` by
`Nat.add_sub_of_le`. -/
@[no_expose]
def stageTransitionLE
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    {i j : ℕ} (h : i ≤ j) : NClasses i A B → NClasses j A B :=
  Function.comp
    (nClassesCast A B (Nat.add_sub_of_le h))
    (stageTransitionFrom i (j - i) A B)

@[simp]
theorem stageTransitionLE_classOf
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    {i j : ℕ} (h : i ≤ j) (phi : HomN i A B) :
    stageTransitionLE A B h (classOf i phi) =
      nClassesCast A B (Nat.add_sub_of_le h)
        (classOf (i + (j - i))
          (stageTransitionRepresentativeFrom i (j - i) phi)) := by
  unfold stageTransitionLE Function.comp
  rw [stageTransitionFrom_classOf]

/-- For the canonical proof `i <= i+k`, the proof-indexed map is exactly the
offset map by `k`. -/
theorem stageTransitionLE_of_add (i k : ℕ)
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    stageTransitionLE A B (Nat.le_add_right i k) =
      stageTransitionFrom i k A B := by
  funext q
  unfold stageTransitionLE Function.comp
  calc
    nClassesCast A B (Nat.add_sub_of_le (Nat.le_add_right i k))
        (stageTransitionFrom i (i + k - i) A B q) =
      nClassesCast A B rfl (stageTransitionFrom i k A B q) :=
        nClassesCast_stageTransitionFrom_offset A B
          (Nat.add_sub_cancel_left i k)
          (Nat.add_sub_of_le (Nat.le_add_right i k)) rfl q
    _ = stageTransitionFrom i k A B q :=
      nClassesCast_rfl (i + k) A B _

private theorem nClassesCast_stageTransitionFrom_add (i k l : ℕ)
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (q : NClasses i A B) :
    nClassesCast A B (Nat.add_assoc i k l).symm
        (stageTransitionFrom i (k + l) A B q) =
      stageTransitionFromReassoc i k l A B q := by
  refine Quotient.inductionOn q ?_
  intro phi
  change nClassesCast A B (Nat.add_assoc i k l).symm
    (stageTransitionFrom i (k + l) A B (classOf i phi)) =
    stageTransitionFromReassoc i k l A B (classOf i phi)
  rw [stageTransitionFrom_classOf,
    stageTransitionFromReassoc_classOf,
    stageMapFromReassoc_eq_cast]
  have hrepresentative :
      stageTransitionRepresentativeFrom i (k + l) phi =
        (stageMapFrom i (k + l) B).comp phi := by
    apply NonUnitalStarAlgHom.ext
    intro a
    rw [stageTransitionRepresentativeFrom_apply,
      NonUnitalStarAlgHom.comp_apply]
  rw [hrepresentative]
  exact nClassesCast_classOf_comp_castTarget A B
    (Nat.add_assoc i k l).symm
    (stageMapFrom i (k + l) B) phi

private theorem stageTransitionLE_of_add_add (i k l : ℕ)
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    stageTransitionLE A B
        ((Nat.le_add_right i k).trans (Nat.le_add_right (i + k) l)) =
      stageTransitionFromReassoc i k l A B := by
  funext q
  unfold stageTransitionLE Function.comp
  have hoff : ((i + k) + l) - i = k + l := by
    rw [Nat.add_assoc, Nat.add_sub_cancel_left]
  calc
    nClassesCast A B
        (Nat.add_sub_of_le
          ((Nat.le_add_right i k).trans (Nat.le_add_right (i + k) l)))
        (stageTransitionFrom i (((i + k) + l) - i) A B q) =
      nClassesCast A B (Nat.add_assoc i k l).symm
        (stageTransitionFrom i (k + l) A B q) :=
          nClassesCast_stageTransitionFrom_offset A B hoff
            (Nat.add_sub_of_le
              ((Nat.le_add_right i k).trans
                (Nat.le_add_right (i + k) l)))
            (Nat.add_assoc i k l).symm q
    _ = stageTransitionFromReassoc i k l A B q :=
      nClassesCast_stageTransitionFrom_add i k l A B q

/-! ## Directed-system laws -/

/-- The proof-indexed stage maps form a directed system.  This dictionary is
ordinary public data, not a globally registered instance. -/
theorem nClassesDirectedSystem
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    DirectedSystem (fun n : ℕ => NClasses n A B)
      (fun _ _ h => stageTransitionLE A B h) where
  map_self {i} q := by
    have hproof : (le_rfl : i ≤ i) = Nat.le_add_right i 0 :=
      Subsingleton.elim _ _
    calc
      stageTransitionLE A B le_rfl q =
          stageTransitionLE A B (Nat.le_add_right i 0) q :=
        congrArg (fun h : i ≤ i => stageTransitionLE A B h q) hproof
      _ = stageTransitionFrom i 0 A B q :=
        congrFun (stageTransitionLE_of_add i 0 A B) q
      _ = q :=
        congrFun (stageTransitionFrom_zero i A B) q
  map_map {k} {j} {i} hij hjk q := by
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hij
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hjk
    rw [stageTransitionLE_of_add i a A B,
      stageTransitionLE_of_add (i + a) b A B,
      stageTransitionLE_of_add_add i a b A B]
    exact (congrFun (stageTransitionFrom_add i a b A B) q).symm

/-! ## Raw direct limit and its universal maps -/

/-- The raw set-level direct limit of literal finite-stage homotopy classes.
It is Mathlib's arbitrary-type `DirectLimit`, not a new quotient model. -/
abbrev NClassesDirectLimit
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :=
  @DirectLimit ℕ inferInstance (fun n => NClasses n A B)
    (fun {i j} _ => NClasses i A B → NClasses j A B)
    (fun _ _ h => stageTransitionLE A B h)
    (fun {_ _} _ => { coe := id, coe_injective := Function.injective_id })
    (nClassesDirectedSystem A B) inferInstance

/-- The canonical map from one finite stage into the raw direct limit. -/
@[no_expose]
def nClassesDirectLimitOf
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (n : ℕ) : NClasses n A B → NClassesDirectLimit A B :=
  fun q => ⟦⟨n, q⟩⟧

/-- Canonical direct-limit maps identify a class with every later-stage
image. -/
theorem nClassesDirectLimitOf_transition
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    {i j : ℕ} (h : i ≤ j) (q : NClasses i A B) :
    nClassesDirectLimitOf A B j (stageTransitionLE A B h q) =
      nClassesDirectLimitOf A B i q := by
  unfold nClassesDirectLimitOf
  exact @DirectLimit.mk_apply ℕ inferInstance (fun n => NClasses n A B)
    (fun {i j} _ => NClasses i A B → NClasses j A B)
    (fun _ _ h => stageTransitionLE A B h)
    (fun {_ _} _ => { coe := id, coe_injective := Function.injective_id })
    (nClassesDirectedSystem A B) inferInstance i j q h

/-- Lift compatible finite-stage functions out of the raw direct limit. The
codomain is an arbitrary `Sort`; no algebraic structure is required. -/
@[no_expose]
def nClassesDirectLimitLift
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    {C : Sort uC}
    (g : ∀ n, NClasses n A B → C)
    (hcompat : ∀ i j (h : i ≤ j) q,
      g i q = g j (stageTransitionLE A B h q)) :
    NClassesDirectLimit A B → C :=
  @DirectLimit.lift ℕ inferInstance (fun n => NClasses n A B)
    (fun {i j} _ => NClasses i A B → NClasses j A B)
    (fun _ _ h => stageTransitionLE A B h)
    (fun {_ _} _ => { coe := id, coe_injective := Function.injective_id })
    (nClassesDirectedSystem A B) inferInstance C g hcompat

@[simp]
theorem nClassesDirectLimitLift_of
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    {C : Sort uC}
    (g : ∀ n, NClasses n A B → C)
    (hcompat : ∀ i j (h : i ≤ j) q,
      g i q = g j (stageTransitionLE A B h q))
    (n : ℕ) (q : NClasses n A B) :
    nClassesDirectLimitLift A B g hcompat
        (nClassesDirectLimitOf A B n q) = g n q := by
  unfold nClassesDirectLimitLift nClassesDirectLimitOf
  rfl

#print axioms nClassesCast
#print axioms nClassesCast_rfl
#print axioms stageTransitionLE
#print axioms stageTransitionLE_classOf
#print axioms stageTransitionLE_of_add
#print axioms nClassesDirectedSystem
#print axioms NClassesDirectLimit
#print axioms nClassesDirectLimitOf
#print axioms nClassesDirectLimitOf_transition
#print axioms nClassesDirectLimitLift
#print axioms nClassesDirectLimitLift_of

end IteratedAsymptoticAlgebra
