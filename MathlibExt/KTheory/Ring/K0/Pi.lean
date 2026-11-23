/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.K0.Product
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Data.Fintype.Option
public import Mathlib.Algebra.Ring.Equiv

/-!
# Algebraic K₀ of a finite family of commutative rings

The canonical map consists of scalar extension along the original ring
evaluations. Finite product decomposition is earned from the existing
binary product equivalence; the empty family uses the actual zero ring.
No Noetherian hypothesis is required.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicKTheory.RingK0

variable {ι : Type v} (R : ι → Type (max u v)) [∀ i, CommRing (R i)]

/-- The actual scalar-extension maps along all original ring coordinates. -/
def piForward : RingK0 (∀ i, R i) →+* ∀ i, RingK0 (R i) :=
  RingHom.pi (fun i => mapRingHom (Pi.evalRingHom R i))

/-- Every component is the original algebraic K₀ evaluation map. -/
@[simp]
theorem piForward_apply (a : RingK0 (∀ i, R i)) (i : ι) :
    piForward R a i = mapRingHom (Pi.evalRingHom R i) a := rfl

private theorem subsingletonRingK0 (S : Type w) [Ring S] [Subsingleton S] :
    Subsingleton (RingK0 S) := by
  apply K0.subsingleton_of_forall_isZero
  intro M
  let _ : Subsingleton M.obj := Module.subsingleton S M.obj
  exact IsZero.of_full_of_faithful_of_isZero FGProjectiveCat.toModuleCat M
    (ModuleCat.isZero_of_subsingleton M.obj)

/-- The canonical map for an empty family is bijective between the
original algebraic K₀ of the zero ring and the unique empty product. -/
theorem piForward_bijective_of_isEmpty [IsEmpty ι] :
    Function.Bijective (piForward.{u, v} R) := by
  let _ : Subsingleton (∀ i, R i) := inferInstance
  let _ : Subsingleton (RingK0 (∀ i, R i)) := subsingletonRingK0 (∀ i, R i)
  constructor
  · intro a b _
    exact Subsingleton.elim a b
  · intro a
    exact ⟨0, Subsingleton.elim _ _⟩

private def piOptionAddEquiv {α : Type v} (S : Option α → Type (max u v))
    [∀ i, CommRing (S i)] (h : Function.Bijective (piForward (fun i => S (some i)))) :
    RingK0 (∀ i, S i) ≃+ ∀ i, RingK0 (S i) := by
  let e := (functor.{max u v}.mapIso
    (RingEquiv.piOptionEquivProd (R := S)).toCommRingCatIso).commRingCatIsoToRingEquiv
  let t := (RingEquiv.ofBijective (piForward (fun i => S (some i))) h).toAddEquiv
  let o := (RingEquiv.piOptionEquivProd (R := fun i => RingK0 (S i))).symm.toAddEquiv
  exact (e.toAddEquiv.trans (prodEquiv (R := S none) (S := ∀ i, S (some i)))).trans
    ((AddEquiv.refl (RingK0 (S none))).prodCongr t) |>.trans o

private theorem piOptionAddEquiv_none {α : Type v} (S : Option α → Type (max u v))
    [∀ i, CommRing (S i)] (h : Function.Bijective (piForward (fun i => S (some i))))
    (a : RingK0 (∀ i, S i)) :
    piOptionAddEquiv S h a none = piForward S a none := by
  let e := (RingEquiv.piOptionEquivProd (R := S)).toRingHom
  let p := RingHom.fst (S none) (∀ i, S (some i))
  change prodFstComponentHom (R := S none) (S := ∀ i, S (some i))
    (mapRingHom e a) = mapRingHom (Pi.evalRingHom S none) a
  rw [prodFstComponentHom_eq_functor_map]
  change mapRingHom p (mapRingHom e a) = mapRingHom (Pi.evalRingHom S none) a
  have he : p.comp e = Pi.evalRingHom S none := rfl
  have hk := congrArg (fun f => mapRingHom f) he
  rw [mapRingHom_comp] at hk
  exact DFunLike.congr_fun hk a

private theorem piOptionAddEquiv_some {α : Type v} (S : Option α → Type (max u v))
    [∀ i, CommRing (S i)] (h : Function.Bijective (piForward (fun i => S (some i))))
    (a : RingK0 (∀ i, S i)) (i : α) :
    piOptionAddEquiv S h a (some i) = piForward S a (some i) := by
  let e := (RingEquiv.piOptionEquivProd (R := S)).toRingHom
  let p := RingHom.snd (S none) (∀ i, S (some i))
  let q := Pi.evalRingHom (fun i => S (some i)) i
  change mapRingHom q (prodSndComponentHom (R := S none) (S := ∀ i, S (some i))
    (mapRingHom e a)) = mapRingHom (Pi.evalRingHom S (some i)) a
  rw [prodSndComponentHom_eq_functor_map]
  change mapRingHom q (mapRingHom p (mapRingHom e a)) =
    mapRingHom (Pi.evalRingHom S (some i)) a
  have he : q.comp (p.comp e) = Pi.evalRingHom S (some i) := rfl
  have hk := congrArg (fun f => mapRingHom f) he
  rw [mapRingHom_comp, mapRingHom_comp] at hk
  exact DFunLike.congr_fun hk a

private theorem piForward_bijective_option {α : Type v} (S : Option α → Type (max u v))
    [∀ i, CommRing (S i)] (h : Function.Bijective (piForward (fun i => S (some i)))) :
    Function.Bijective (piForward S) := by
  have he : (piOptionAddEquiv S h : RingK0 (∀ i, S i) → ∀ i, RingK0 (S i)) = piForward S := by
    funext a i
    cases i with
    | none => exact piOptionAddEquiv_none S h a
    | some i => exact piOptionAddEquiv_some S h a i
  rw [← he]
  exact (piOptionAddEquiv S h).bijective

private def piRelabelAddEquiv {α β : Type v} (e : α ≃ β)
    (S : β → Type (max u v)) [∀ i, CommRing (S i)]
    (h : Function.Bijective (piForward (fun i => S (e i)))) :
    RingK0 (∀ i, S i) ≃+ ∀ i, RingK0 (S i) := by
  let r := (RingEquiv.piCongrLeft S e).symm
  let k := (functor.{max u v}.mapIso r.toCommRingCatIso).commRingCatIsoToRingEquiv
  let t := RingEquiv.ofBijective (piForward (fun i => S (e i))) h
  let o := RingEquiv.piCongrLeft (fun i => RingK0 (S i)) e
  exact (k.toAddEquiv.trans t.toAddEquiv).trans o.toAddEquiv

private theorem piRelabelAddEquiv_apply {α β : Type v} (e : α ≃ β)
    (S : β → Type (max u v)) [∀ i, CommRing (S i)]
    (h : Function.Bijective (piForward (fun i => S (e i))))
    (a : RingK0 (∀ i, S i)) (i : α) :
    piRelabelAddEquiv e S h a (e i) = piForward S a (e i) := by
  let r := (RingEquiv.piCongrLeft S e).symm.toRingHom
  let q := Pi.evalRingHom (fun i => S (e i)) i
  change Equiv.piCongrLeft (fun i => RingK0 (S i)) e
      (piForward (fun i => S (e i)) (mapRingHom r a)) (e i) = piForward S a (e i)
  rw [Equiv.piCongrLeft_apply_apply]
  change mapRingHom q (mapRingHom r a) = mapRingHom (Pi.evalRingHom S (e i)) a
  have hr : q.comp r = Pi.evalRingHom S (e i) := by
    ext f
    rfl
  have hk := congrArg (fun f => mapRingHom f) hr
  rw [mapRingHom_comp] at hk
  exact DFunLike.congr_fun hk a

private theorem piForward_bijective_relabel {α β : Type v} (e : α ≃ β)
    (S : β → Type (max u v)) [∀ i, CommRing (S i)]
    (h : Function.Bijective (piForward (fun i => S (e i)))) :
    Function.Bijective (piForward S) := by
  have he : (piRelabelAddEquiv e S h : RingK0 (∀ i, S i) → ∀ i, RingK0 (S i)) =
      piForward S := by
    funext a i
    obtain ⟨j, rfl⟩ := e.surjective i
    exact piRelabelAddEquiv_apply e S h a j
  rw [← he]
  exact (piRelabelAddEquiv e S h).bijective

/-- Finite products have a genuine canonical algebraic K₀ bijection,
with every original coordinate given by its actual scalar-extension evaluation. -/
theorem piForward_bijective [Finite ι] : Function.Bijective (piForward.{u, v} R) := by
  have h : ∀ (S : ι → Type (max u v)) [∀ i, CommRing (S i)],
      Function.Bijective (piForward S) :=
    Finite.induction_empty_option
      (P := fun α => ∀ (S : α → Type (max u v)) [∀ i, CommRing (S i)],
        Function.Bijective (piForward S))
      (by
        intro α β e ih S _
        exact piForward_bijective_relabel e S (ih (fun i => S (e i))))
      (by
        intro S _
        exact piForward_bijective_of_isEmpty S)
      (by
        intro α _ ih S _
        exact piForward_bijective_option S (ih (fun i => S (some i)))) ι
  exact h R

/-- The finite-family ring equivalence uses the original coordinate maps
and the bijection earned from the original binary product formula. -/
def piEquiv [Finite ι] : RingK0 (∀ i, R i) ≃+* ∀ i, RingK0 (R i) :=
  RingEquiv.ofBijective (piForward.{u, v} R) (piForward_bijective R)

/-- Every finite-family coordinate is the same original algebraic K₀ ring evaluation. -/
@[simp]
theorem piEquiv_apply [Finite ι] (a : RingK0 (∀ i, R i)) (i : ι) :
    piEquiv.{u, v} R a i = mapRingHom (Pi.evalRingHom R i) a := rfl

/-- The original coordinate maps recover every component of the inverse. -/
@[simp]
theorem piEquiv_symm_apply [Finite ι] (a : ∀ i, RingK0 (R i)) (i : ι) :
    mapRingHom (Pi.evalRingHom R i) ((piEquiv.{u, v} R).symm a) = a i :=
  congrFun ((piEquiv R).apply_symm_apply a) i

/-- The entire finite-product ring equivalence commutes with the
coordinatewise ring homomorphisms and their actual scalar-extension maps. -/
theorem piEquiv_naturality [Finite ι] (S : ι → Type (max u v))
    [∀ i, CommRing (S i)] (φ : ∀ i, R i →+* S i) :
    (piEquiv.{u, v} S).toRingHom.comp
        (mapRingHom (RingHom.pi (fun i => (φ i).comp (Pi.evalRingHom R i)))) =
      (RingHom.pi (fun i => (mapRingHom (φ i)).comp
        (Pi.evalRingHom (fun i => RingK0 (R i)) i))).comp
          (piEquiv.{u, v} R).toRingHom := by
  ext a i
  change mapRingHom (Pi.evalRingHom S i)
      (mapRingHom (RingHom.pi (fun j => (φ j).comp (Pi.evalRingHom R j))) a) =
    mapRingHom (φ i) (mapRingHom (Pi.evalRingHom R i) a)
  have h : (Pi.evalRingHom S i).comp
      (RingHom.pi (fun j => (φ j).comp (Pi.evalRingHom R j))) =
        (φ i).comp (Pi.evalRingHom R i) := rfl
  have hk := congrArg (fun f => mapRingHom f) h
  rw [mapRingHom_comp, mapRingHom_comp] at hk
  exact DFunLike.congr_fun hk a

/-- The inverse for an empty family lands in the actual zero algebraic K₀ group. -/
@[simp]
theorem piEquiv_symm_of_isEmpty [IsEmpty ι] (a : ∀ i, RingK0 (R i)) :
    (piEquiv.{u, v} R).symm a = 0 := by
  let _ : Subsingleton (∀ i, R i) := inferInstance
  let _ : Subsingleton (RingK0 (∀ i, R i)) := subsingletonRingK0 (∀ i, R i)
  exact Subsingleton.elim _ _

end AlgebraicKTheory.RingK0

end
