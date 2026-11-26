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
# Direct limit of finite-stage homotopy classes

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
For i≤j, write S_(i,j) for the transition across j-i constant-class stages. The direct limit
L=NClassesDirectLimit A B identifies a class at any stage with its image at every later stage.
The transitions satisfy S_(i,i)=id and S_(j,k)∘S_(i,j)=S_(i,k) for i≤j≤k. Compatible functions
on the stages extend to a function on L. This is the finite-stage class system occurring in
Blackadar25.7.4.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra

attribute [local instance] AsymptoticAlgebra.cStarAlgebra

namespace IteratedAsymptoticAlgebra

universe uA uB uC

/-!
## Equal stage indices and later-stage inclusions

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
For equal stage indices n=m, class spaces identify canonically. For i≤j, the later-stage map
uses j-i constant-class inclusions.
-/

/-- **Identification of class spaces with equal stage indices.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
For an equality h:n=m, nClassesCast A B h:Q_n(A,B)→Q_m(A,B) is the canonical identification of
the same indexed homotopy class space.
-/
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

/-- **Transition map between ordered finite stages.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
For i≤j, stageTransitionLE A B h:Q_i(A,B)→Q_j(A,B) is the offset map stageTransitionFrom
i(j-i) A B with target identified using i+(j-i)=j.
-/
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

/-- **Ordered-stage transition for a specified offset.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
For i,k∈ℕ, stageTransitionLE A B (i≤i+k)=stageTransitionFrom i k A B, the transition from
Q_i(A,B) to Q_(i+k)(A,B).
-/
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

/-!
## Directed-system identities

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
For i≤j≤k, the transition maps satisfy S_(j,k)∘S_(i,j)=S_(i,k), with S_(i,i)=id.
-/

/-- **Directed system of finite-stage homotopy classes.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
The class spaces Q_i(A,B), i∈ℕ, and maps S_(i,j)=stageTransitionLE A B (i≤j) form a directed
system: S_(i,i)=id and S_(j,k)∘S_(i,j)=S_(i,k) whenever i≤j≤k.
-/
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

/-!
## Direct limit and its universal maps

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
For i≤j, write S_(i,j) for the transition across j-i constant-class stages. The direct limit
L=NClassesDirectLimit A B identifies a class at any stage with its image at every later stage.
The canonical stage maps j_n:Q_n(A,B)→L satisfy j_j∘S_(i,j)=j_i for i≤j.
-/

/-- **Direct-limit set of finite-stage homotopy classes.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
For i≤j, write S_(i,j) for the transition across j-i constant-class stages. The direct limit
L=NClassesDirectLimit A B identifies a class at any stage with its image at every later stage.
NClassesDirectLimit A B is the direct limit of this directed system of class spaces.
-/
abbrev NClassesDirectLimit
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :=
  @DirectLimit ℕ inferInstance (fun n => NClasses n A B)
    (fun {i j} _ => NClasses i A B → NClasses j A B)
    (fun _ _ h => stageTransitionLE A B h)
    (fun {_ _} _ => { coe := id, coe_injective := Function.injective_id })
    (nClassesDirectedSystem A B) inferInstance

/-- **Canonical map from a class stage to the direct limit.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
For i≤j, write S_(i,j) for the transition across j-i constant-class stages. The direct limit
L=NClassesDirectLimit A B identifies a class at any stage with its image at every later stage.
For n∈ℕ, nClassesDirectLimitOf A B n:Q_n(A,B)→L is the canonical stage map j_n.
-/
@[no_expose]
def nClassesDirectLimitOf
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (n : ℕ) : NClasses n A B → NClassesDirectLimit A B :=
  fun q => ⟦⟨n, q⟩⟧

/-- **A direct-limit class equals each later-stage image.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
For i≤j, write S_(i,j) for the transition across j-i constant-class stages. The direct limit
L=NClassesDirectLimit A B identifies a class at any stage with its image at every later stage.
For i≤j and q∈Q_i(A,B), nClassesDirectLimitOf A B j (S_(i,j)q)=nClassesDirectLimitOf A B i q.
-/
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

/-- **Universal function out of the direct limit.**

Let A,B be nonunital complex C-star algebras in independent universes and n∈ℕ. For a nonunital
complex C-star algebra X, set αX=C_b([1,∞),X)/C₀([1,∞),X), α⁰X=X and αⁿ⁺¹X=α(αⁿX), with the
quotient C-star norms. Write Q_n(A,B)=NClasses n A B for star homomorphisms A→αⁿB modulo
homotopies F:A→αⁿ(C([0,1],B)) whose iterated endpoint evaluations are the two representatives.
For i≤j, write S_(i,j) for the transition across j-i constant-class stages. The direct limit
L=NClassesDirectLimit A B identifies a class at any stage with its image at every later stage.
Let C be any Sort and let g_n:Q_n(A,B)→C satisfy g_i(q)=g_j(S_(i,j)q) for every i≤j and q. The
function nClassesDirectLimitLift A B g hcompat:L→C extends these compatible stage functions,
with value g_n(q) on j_n(q).
-/
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


end IteratedAsymptoticAlgebra
