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

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.AsymptoticAlgebraFunctor

public import Mathlib.CategoryTheory.EqToHom

/-!
# Finite iterates of the actual asymptotic quotient

The object recursion uses the reducible `asymptoticAlgebraObject`, never the
functor's record body. Direct maps retain independent universes.  Stage
offset composition exposes its natural-number reassociation transport.

`alphaRepresentative` applies the asymptotic quotient functor to a homomorphism
into a finite iterate. Its codomain is the literal successor quotient. This
file defines no homotopy quotient or class-level transition map.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory
open scoped BoundedContinuousFunction

noncomputable section

universe u uA uB uC

attribute [local instance] AsymptoticAlgebra.cStarAlgebra

namespace NonUnitalCStarAlgCat

/-- Canonical finite iteration of the lightweight literal quotient object. -/
abbrev iteratedAsymptoticAlgebraObject
    (n : ℕ) (A : NonUnitalCStarAlgCat.{u}) :
    NonUnitalCStarAlgCat.{u} :=
  Nat.rec A (fun _ B => asymptoticAlgebraObject B) n

theorem iteratedAsymptoticAlgebraObject_zero
    (A : NonUnitalCStarAlgCat.{u}) :
    iteratedAsymptoticAlgebraObject 0 A = A := by
  rfl

theorem iteratedAsymptoticAlgebraObject_succ
    (n : ℕ) (A : NonUnitalCStarAlgCat.{u}) :
    iteratedAsymptoticAlgebraObject (n + 1) A =
      asymptoticAlgebraObject (iteratedAsymptoticAlgebraObject n A) := by
  rfl

/-- Iterating the stored asymptotic-algebra object `n` times after `m`
times is the stored object at summed stage `n + m`. -/
theorem iteratedAsymptoticAlgebraObject_add (n m : ℕ)
    (C : NonUnitalCStarAlgCat.{u}) :
    iteratedAsymptoticAlgebraObject n
        (iteratedAsymptoticAlgebraObject m C) =
      iteratedAsymptoticAlgebraObject (n + m) C := by
  induction n with
  | zero =>
      exact
        (iteratedAsymptoticAlgebraObject_zero
          (iteratedAsymptoticAlgebraObject m C)).trans
        (congrArg (fun k => iteratedAsymptoticAlgebraObject k C)
          (Nat.zero_add m).symm)
  | succ n ih =>
      change
        asymptoticAlgebraObject
            (iteratedAsymptoticAlgebraObject n
              (iteratedAsymptoticAlgebraObject m C)) =
          iteratedAsymptoticAlgebraObject (Nat.succ n + m) C
      rw [ih, Nat.succ_add]

end NonUnitalCStarAlgCat

/-- Literal carrier of the nth finite iterate, with its exact stored quotient
C-star dictionary. -/
abbrev IteratedAsymptoticAlgebra
    (n : ℕ) (A : Type u) [NonUnitalCStarAlgebra A] : Type u :=
  (NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject n
    (NonUnitalCStarAlgCat.of A)).carrier

theorem iteratedAsymptoticAlgebra_zero
    (A : Type u) [NonUnitalCStarAlgebra A] :
    IteratedAsymptoticAlgebra 0 A = A := by
  rfl

theorem iteratedAsymptoticAlgebra_succ
    (n : ℕ) (A : Type u) [NonUnitalCStarAlgebra A] :
    IteratedAsymptoticAlgebra (n + 1) A =
      AsymptoticAlgebra (IteratedAsymptoticAlgebra n A) := by
  rfl

namespace NonUnitalCStarAlgCat

/-- Rebundling an iterated carrier with its inferred canonical dictionary
recovers the stored iterated category object. -/
theorem of_iteratedAsymptoticAlgebra (n : ℕ)
    (C : Type u) [NonUnitalCStarAlgebra C] :
    of (IteratedAsymptoticAlgebra n C) =
      iteratedAsymptoticAlgebraObject n (of C) := by
  rfl

end NonUnitalCStarAlgCat

namespace IteratedAsymptoticAlgebra

/-! ## Canonical summed-stage transport -/

/-- The dictionary-safe equality morphism from nested finite iteration to the
literal summed stage. -/
@[no_expose]
def iteratedAddHom (n m : ℕ)
    (C : Type uC) [NonUnitalCStarAlgebra C] :
    IteratedAsymptoticAlgebra n (IteratedAsymptoticAlgebra m C) →⋆ₙₐ[ℂ]
      IteratedAsymptoticAlgebra (n + m) C := by
  change
    (NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject n
        (NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject m
          (NonUnitalCStarAlgCat.of C))) ⟶
      NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject (n + m)
        (NonUnitalCStarAlgCat.of C)
  exact eqToHom
    (NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject_add n m
      (NonUnitalCStarAlgCat.of C))

private theorem iteratedAddHom_eq_eqToHom (n m : ℕ)
    (C : Type uC) [NonUnitalCStarAlgebra C] :
    (iteratedAddHom n m C :
      (NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject n
        (NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject m
          (NonUnitalCStarAlgCat.of C))) ⟶
      NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject (n + m)
        (NonUnitalCStarAlgCat.of C)) =
      eqToHom
        (NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject_add n m
          (NonUnitalCStarAlgCat.of C)) := by
  rfl

theorem iteratedAddHom_zero_left (m : ℕ)
    (C : Type uC) [NonUnitalCStarAlgebra C] :
    eqToHom
        (NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject_zero
          (NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject m
            (NonUnitalCStarAlgCat.of C))).symm ≫
      (iteratedAddHom 0 m C :
        (NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject 0
          (NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject m
            (NonUnitalCStarAlgCat.of C))) ⟶
        NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject (0 + m)
          (NonUnitalCStarAlgCat.of C)) =
      eqToHom
        (congrArg
          (fun k => NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject k
            (NonUnitalCStarAlgCat.of C))
          (Nat.zero_add m)).symm := by
  simp only [iteratedAddHom_eq_eqToHom, eqToHom_trans]

theorem iteratedAddHom_zero_right (n : ℕ)
    (C : Type uC) [NonUnitalCStarAlgebra C] :
    iteratedAddHom n 0 C =
      NonUnitalStarAlgHom.id ℂ (IteratedAsymptoticAlgebra n C) := by
  change
    (eqToHom
      (NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject_add n 0
        (NonUnitalCStarAlgCat.of C)) :
      NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject n
          (NonUnitalCStarAlgCat.of C) ⟶
        NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject n
          (NonUnitalCStarAlgCat.of C)) = 𝟙 _
  exact eqToHom_refl _ _

/-- Independent-universe map on finite iterates. -/
@[no_expose]
def map (n : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (φ : A →⋆ₙₐ[ℂ] B) :
    IteratedAsymptoticAlgebra n A →⋆ₙₐ[ℂ]
      IteratedAsymptoticAlgebra n B :=
  Nat.rec (motive := fun k =>
      IteratedAsymptoticAlgebra k A →⋆ₙₐ[ℂ]
        IteratedAsymptoticAlgebra k B)
    φ (fun _ ψ => AsymptoticAlgebra.map ψ) n

@[simp]
theorem map_zero_stage
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (φ : A →⋆ₙₐ[ℂ] B) : map 0 φ = φ := by
  rfl

@[simp]
theorem map_succ
    (n : ℕ) {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (φ : A →⋆ₙₐ[ℂ] B) :
    map (n + 1) φ = AsymptoticAlgebra.map (map n φ) := by
  rfl

@[simp]
theorem map_id (n : ℕ)
    (A : Type uA) [NonUnitalCStarAlgebra A] :
    map n (NonUnitalStarAlgHom.id ℂ A) =
      NonUnitalStarAlgHom.id ℂ (IteratedAsymptoticAlgebra n A) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [map_succ, ih, AsymptoticAlgebra.map_id]

@[simp]
theorem map_zero (n : ℕ)
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    map n (0 : A →⋆ₙₐ[ℂ] B) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [map_succ, ih, AsymptoticAlgebra.map_zero]

/-- Finite alpha iteration respects composition across independent universes. -/
theorem map_comp (n : ℕ)
    {A : Type uA} {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C]
    (φ : A →⋆ₙₐ[ℂ] B) (ψ : B →⋆ₙₐ[ℂ] C) :
    map n (ψ.comp φ) = (map n ψ).comp (map n φ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [map_succ, map_succ, map_succ, ih, AsymptoticAlgebra.map_comp]

/-- Natural constant inclusion from one finite stage to its successor. -/
@[no_expose]
def stageHom (n : ℕ)
    (A : Type uA) [NonUnitalCStarAlgebra A] :
    IteratedAsymptoticAlgebra n A →⋆ₙₐ[ℂ]
      IteratedAsymptoticAlgebra (n + 1) A :=
  AsymptoticAlgebra.constantHom (IteratedAsymptoticAlgebra n A)

/-- The successor map is exactly the actual constant-class hom. -/
theorem stageHom_eq_constantHom (n : ℕ)
    (A : Type uA) [NonUnitalCStarAlgebra A] :
    stageHom n A =
      AsymptoticAlgebra.constantHom (IteratedAsymptoticAlgebra n A) := by
  rfl

theorem stageHom_apply (n : ℕ)
    (A : Type uA) [NonUnitalCStarAlgebra A]
    (x : IteratedAsymptoticAlgebra n A) :
    stageHom n A x =
      AsymptoticAlgebra.quotientMap (IteratedAsymptoticAlgebra n A)
        (BoundedContinuousFunction.const AsymptoticTime x) := by
  rw [stageHom_eq_constantHom, AsymptoticAlgebra.constantHom_apply]

theorem stageHom_injective (n : ℕ)
    (A : Type uA) [NonUnitalCStarAlgebra A] :
    Function.Injective (stageHom n A) := by
  rw [stageHom_eq_constantHom]
  exact AsymptoticAlgebra.constantHom_injective
    (IteratedAsymptoticAlgebra n A)

/-- The successor square commutes for maps between unrelated universes. -/
theorem stageHom_naturality (n : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (φ : A →⋆ₙₐ[ℂ] B) :
    (map (n + 1) φ).comp (stageHom n A) =
      (stageHom n B).comp (map n φ) := by
  rw [map_succ, stageHom_eq_constantHom, stageHom_eq_constantHom]
  exact AsymptoticAlgebra.map_comp_constantHom (map n φ)

/-- Computational stage change by an offset. -/
@[no_expose]
def stageMapFrom (n k : ℕ)
    (A : Type uA) [NonUnitalCStarAlgebra A] :
    IteratedAsymptoticAlgebra n A →⋆ₙₐ[ℂ]
      IteratedAsymptoticAlgebra (n + k) A :=
  Nat.rec (motive := fun j =>
      IteratedAsymptoticAlgebra n A →⋆ₙₐ[ℂ]
        IteratedAsymptoticAlgebra (n + j) A)
    (NonUnitalStarAlgHom.id ℂ (IteratedAsymptoticAlgebra n A))
    (fun j h => (stageHom (n + j) A).comp h) k

@[simp]
theorem stageMapFrom_zero (n : ℕ)
    (A : Type uA) [NonUnitalCStarAlgebra A] :
    stageMapFrom n 0 A =
      NonUnitalStarAlgHom.id ℂ (IteratedAsymptoticAlgebra n A) := by
  rfl

@[simp]
theorem stageMapFrom_succ (n k : ℕ)
    (A : Type uA) [NonUnitalCStarAlgebra A] :
    stageMapFrom n (k + 1) A =
      (stageHom (n + k) A).comp (stageMapFrom n k A) := by
  rfl

theorem stageMapFrom_one (n : ℕ)
    (A : Type uA) [NonUnitalCStarAlgebra A] :
    stageMapFrom n 1 A = stageHom n A := by
  apply NonUnitalStarAlgHom.ext
  intro x
  rfl

theorem stageMapFrom_injective (n k : ℕ)
    (A : Type uA) [NonUnitalCStarAlgebra A] :
    Function.Injective (stageMapFrom n k A) := by
  induction k with
  | zero => exact Function.injective_id
  | succ k ih =>
      rw [stageMapFrom_succ]
      exact (stageHom_injective (n + k) A).comp ih

/-- Every finite stage change is natural in the coefficient algebra. -/
theorem stageMapFrom_naturality (n k : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (φ : A →⋆ₙₐ[ℂ] B) :
    (map (n + k) φ).comp (stageMapFrom n k A) =
      (stageMapFrom n k B).comp (map n φ) := by
  induction k with
  | zero =>
      apply NonUnitalStarAlgHom.ext
      intro x
      rfl
  | succ k ih =>
      apply NonUnitalStarAlgHom.ext
      intro x
      rw [stageMapFrom_succ, stageMapFrom_succ,
        NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.comp_apply,
        NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.comp_apply]
      calc
        map (n + (k + 1)) φ
            (stageHom (n + k) A (stageMapFrom n k A x)) =
          stageHom (n + k) B
            (map (n + k) φ (stageMapFrom n k A x)) :=
          DFunLike.congr_fun (stageHom_naturality (n + k) φ)
            (stageMapFrom n k A x)
        _ = stageHom (n + k) B
            (stageMapFrom n k B (map n φ x)) :=
          congrArg (stageHom (n + k) B) (DFunLike.congr_fun ih x)

private def castTarget (n : ℕ) {m m' : ℕ}
    (A : Type uA) [NonUnitalCStarAlgebra A]
    (h : m = m')
    (F : IteratedAsymptoticAlgebra n A →⋆ₙₐ[ℂ]
      IteratedAsymptoticAlgebra m' A) :
    IteratedAsymptoticAlgebra n A →⋆ₙₐ[ℂ]
      IteratedAsymptoticAlgebra m A := by
  cases h
  exact F

private theorem castTarget_eq_cast (n : ℕ) {m m' : ℕ}
    (A : Type uA) [NonUnitalCStarAlgebra A] (h : m = m')
    (F : IteratedAsymptoticAlgebra n A →⋆ₙₐ[ℂ]
      IteratedAsymptoticAlgebra m' A) :
    castTarget n A h F =
      cast
        (congrArg
          (fun k => IteratedAsymptoticAlgebra n A →⋆ₙₐ[ℂ]
            IteratedAsymptoticAlgebra k A) h.symm) F := by
  cases h
  rfl

private theorem castTarget_stageHom (n : ℕ) {m m' : ℕ}
    (A : Type uA) [NonUnitalCStarAlgebra A]
    (h : m = m')
    (F : IteratedAsymptoticAlgebra n A →⋆ₙₐ[ℂ]
      IteratedAsymptoticAlgebra m' A) :
    castTarget n A (congrArg Nat.succ h)
        ((stageHom m' A).comp F) =
      (stageHom m A).comp (castTarget n A h F) := by
  cases h
  rfl

/-- Explicit transport of the direct `(k+l)`-offset map to the
left-associated target `(n+k)+l`. -/
@[no_expose]
def stageMapFromReassoc (n k l : ℕ)
    (A : Type uA) [NonUnitalCStarAlgebra A] :
    IteratedAsymptoticAlgebra n A →⋆ₙₐ[ℂ]
      IteratedAsymptoticAlgebra ((n + k) + l) A :=
  castTarget n A (Nat.add_assoc n k l) (stageMapFrom n (k + l) A)

/-- The reassociated stage map is exactly the direct offset map transported
along natural-number addition associativity. -/
theorem stageMapFromReassoc_eq_cast (n k l : ℕ)
    (A : Type uA) [NonUnitalCStarAlgebra A] :
    stageMapFromReassoc n k l A =
      cast
        (congrArg
          (fun m =>
            IteratedAsymptoticAlgebra n A →⋆ₙₐ[ℂ]
              IteratedAsymptoticAlgebra m A)
          (Nat.add_assoc n k l).symm)
        (stageMapFrom n (k + l) A) := by
  exact castTarget_eq_cast n A (Nat.add_assoc n k l)
    (stageMapFrom n (k + l) A)

private theorem stageMapFromReassoc_succ (n k l : ℕ)
    (A : Type uA) [NonUnitalCStarAlgebra A] :
    stageMapFromReassoc n k (l + 1) A =
      (stageHom ((n + k) + l) A).comp
        (stageMapFromReassoc n k l A) := by
  unfold stageMapFromReassoc
  have hstep :
      stageMapFrom n (k + (l + 1)) A =
        (stageHom (n + (k + l)) A).comp (stageMapFrom n (k + l) A) :=
    stageMapFrom_succ n (k + l) A
  calc
    castTarget n A (Nat.add_assoc n k (l + 1))
        (stageMapFrom n (k + (l + 1)) A) =
      castTarget n A (Nat.add_assoc n k (l + 1))
        ((stageHom (n + (k + l)) A).comp (stageMapFrom n (k + l) A)) :=
      congrArg (castTarget n A (Nat.add_assoc n k (l + 1))) hstep
    _ = (stageHom ((n + k) + l) A).comp
        (castTarget n A (Nat.add_assoc n k l) (stageMapFrom n (k + l) A)) :=
      castTarget_stageHom n A (Nat.add_assoc n k l)
        (stageMapFrom n (k + l) A)

/-- Offset addition computes composition, with the target reassociation made
explicit by `stageMapFromReassoc`. -/
theorem stageMapFrom_add (n k l : ℕ)
    (A : Type uA) [NonUnitalCStarAlgebra A] :
    stageMapFromReassoc n k l A =
      (stageMapFrom (n + k) l A).comp (stageMapFrom n k A) := by
  induction l with
  | zero =>
      apply NonUnitalStarAlgHom.ext
      intro x
      rfl
  | succ l ih =>
      rw [stageMapFromReassoc_succ, stageMapFrom_succ, ih,
        NonUnitalStarAlgHom.comp_assoc]

end IteratedAsymptoticAlgebra

namespace NonUnitalCStarAlgCat

/-- Lightweight same-universe categorical packaging of the opaque direct iterated map. -/
def iteratedAsymptoticAlgebraFunctor (n : ℕ) :
    NonUnitalCStarAlgCat.{u} ⥤ NonUnitalCStarAlgCat.{u} where
  obj := iteratedAsymptoticAlgebraObject n
  map φ := IteratedAsymptoticAlgebra.map n φ
  map_id A := IteratedAsymptoticAlgebra.map_id n A
  map_comp φ ψ := IteratedAsymptoticAlgebra.map_comp n φ ψ

/-- The categorical map is exactly the independent-universe direct map at
the same object universe. -/
theorem iteratedAsymptoticAlgebraFunctor_map (n : ℕ)
    {A B : NonUnitalCStarAlgCat.{u}} (φ : A ⟶ B) :
    (iteratedAsymptoticAlgebraFunctor n).map φ =
      IteratedAsymptoticAlgebra.map n φ := by
  rfl

/-- Successor inclusions as a same-universe natural transformation. -/
@[no_expose]
def stageNatTrans (n : ℕ) :
    NatTrans (iteratedAsymptoticAlgebraFunctor n)
      (iteratedAsymptoticAlgebraFunctor (n + 1)) where
  app A := IteratedAsymptoticAlgebra.stageHom n A
  naturality {_A _B} φ :=
    (IteratedAsymptoticAlgebra.stageHom_naturality n φ).symm

theorem stageNatTrans_app (n : ℕ)
    (A : NonUnitalCStarAlgCat.{u}) :
    (stageNatTrans n).app A = IteratedAsymptoticAlgebra.stageHom n A := by
  rfl

end NonUnitalCStarAlgCat

namespace IteratedAsymptoticAlgebra

/-- Representatives before any homotopy quotient. -/
abbrev HomN (n : ℕ)
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :=
  A →⋆ₙₐ[ℂ] IteratedAsymptoticAlgebra n B

/-- Literal application of alpha to a representative.  Its codomain is
shown without a class-index reinterpretation. -/
@[no_expose]
def alphaRepresentative (n : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (φ : HomN n A B) :
    AsymptoticAlgebra A →⋆ₙₐ[ℂ]
      AsymptoticAlgebra (IteratedAsymptoticAlgebra n B) :=
  AsymptoticAlgebra.map φ

theorem alphaRepresentative_eq (n : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (φ : HomN n A B) :
    alphaRepresentative n φ = AsymptoticAlgebra.map φ := by
  rfl

@[simp]
theorem alphaRepresentative_quotientMap (n : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (φ : HomN n A B) (f : AsymptoticTime →ᵇ A) :
    alphaRepresentative n φ (AsymptoticAlgebra.quotientMap A f) =
      AsymptoticAlgebra.quotientMap (IteratedAsymptoticAlgebra n B)
        (BoundedContinuousFunction.compNonUnitalStarAlgHom φ f) := by
  exact AsymptoticAlgebra.map_quotientMap φ f


end IteratedAsymptoticAlgebra
