/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.FGProjectiveCat.FiniteFreeComplement
public import MathlibExt.Algebra.Category.FGProjectiveCat.IdempotentModel
public import Mathlib.CategoryTheory.Adjunction.Limits
public import MathlibExt.Algebra.Monoid.CofinalElementLocalization
public import MathlibExt.CategoryTheory.Preadditive.Skeleton
public import MathlibExt.KTheory.Exact.K0.Split
public import MathlibExt.KTheory.Ring.K0.Projective
public import MathlibExt.CategoryTheory.Monoidal.SInverseSCoreGrade
public import MathlibExt.CategoryTheory.Monoidal.GroupCompletion

/-!
# Finite-free cofinality in ring K₀

The class of the rank-one free module is cofinal among classes represented
by finitely generated projective modules: for every projective `P`, there are
`n` and a projective `Q` such that

```text
[P] + [Q] = n • [R].
```

This is the algebraic cofinality input for the group-completion comparison.
No space-level group-completion or plus-construction theorem is claimed.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe u w

namespace AlgebraicKTheory
namespace RingK0

variable (R : Type u) [Ring R]

/-- The standard rank-`n` finite free object in `FGProjectiveCat R`. -/
abbrev standardFreeProjective (n : ℕ) : FGProjectiveCat.{u} R :=
  FGProjectiveCat.standardFree R n

/-- The rank-one regular projective module. -/
abbrev regularProjective : FGProjectiveCat.{u} R :=
  FGProjectiveCat.regular R

/-- The class of the regular module in `RingK0 R`. -/
noncomputable def regularClass : RingK0 R :=
  K0.mk (regularProjective R)

private lemma standardFreeProjective_zero_isZero :
    IsZero (standardFreeProjective R 0) := by
  let _ : Subsingleton (standardFreeProjective R 0 : Type u) :=
    ⟨fun x y => funext fun i => i.elim0⟩
  apply (IsZero.iff_id_eq_zero _).2
  apply FGProjectiveCat.hom_ext
  apply LinearMap.ext
  intro x
  exact Subsingleton.elim _ _

/-- The zero-rank standard free object represents zero in `RingK0`. -/
theorem mk_standardFreeProjective_zero :
    (K0.mk (standardFreeProjective R 0) : RingK0 R) = 0 :=
  K0.mk_eq_zero_of_isZero (standardFreeProjective_zero_isZero R)

/-- The zero-rank standard free object is zero in the additive monoid of
isomorphism classes. -/
theorem toSkeleton_standardFreeProjective_zero :
    toSkeleton (standardFreeProjective R 0) =
      (0 : Skeleton (FGProjectiveCat.{u} R)) := by
  let e : standardFreeProjective R 0 ≅ (0 : FGProjectiveCat.{u} R) :=
    (standardFreeProjective_zero_isZero R).iso (isZero_zero _)
  calc
    toSkeleton (standardFreeProjective R 0) =
        toSkeleton (0 : FGProjectiveCat.{u} R) := congr_toSkeleton_of_iso e
    _ = 0 := Skeleton.toSkeleton_zero

/-- The head--tail decomposition of a finite free module, transported to
the categorical biproduct in `FGProjectiveCat`. -/
noncomputable def standardFreeProjectiveSuccIso (n : ℕ) :
    standardFreeProjective R (n + 1) ≅
      regularProjective R ⊞ standardFreeProjective R n := by
  let headTail : (Fin (n + 1) → R) ≃ₗ[R] R × (Fin n → R) :=
    (LinearEquiv.piCongrLeft R (fun _ => R) (finSuccEquiv n)).trans
      (LinearEquiv.piOptionEquivProd R)
  let biprodProduct :
      (((regularProjective R ⊞ standardFreeProjective R n :
          FGProjectiveCat.{u} R)) : Type u) ≃ₗ[R]
        R × (Fin n → R) :=
    FGProjectiveCat.biprodCarrierLinearEquiv
      (regularProjective R) (standardFreeProjective R n)
  exact FGProjectiveCat.isoOfLinearEquiv
    (headTail.trans biprodProduct.symm)

/-- Split a standard free module indexed by `Fin (n+m)` into the
corresponding binary biproduct. -/
noncomputable def standardFreeProjectiveAddIso (n m : ℕ) :
    standardFreeProjective R (n + m) ≅
      standardFreeProjective R n ⊞ standardFreeProjective R m :=
  FGProjectiveCat.standardFreeAddIso R n m

/-- Adding one free generator adds the regular class. -/
theorem mk_standardFreeProjective_succ (n : ℕ) :
    K0.mk (standardFreeProjective R (n + 1)) =
      regularClass R + K0.mk (standardFreeProjective R n) := by
  calc
    K0.mk (standardFreeProjective R (n + 1)) =
        K0.mk (regularProjective R ⊞ standardFreeProjective R n) :=
      K0.mk_congr_of_iso (standardFreeProjectiveSuccIso R n)
    _ = K0.mk (regularProjective R) +
        K0.mk (standardFreeProjective R n) := K0.mk_biprod _ _
    _ = regularClass R + K0.mk (standardFreeProjective R n) := rfl

/-- Adding one generator adds the regular-module isomorphism class in the
projective-class monoid. -/
theorem toSkeleton_standardFreeProjective_succ (n : ℕ) :
    toSkeleton (standardFreeProjective R (n + 1)) =
      toSkeleton (regularProjective R) +
        toSkeleton (standardFreeProjective R n) := by
  calc
    toSkeleton (standardFreeProjective R (n + 1)) =
        toSkeleton (regularProjective R ⊞ standardFreeProjective R n) :=
      congr_toSkeleton_of_iso (standardFreeProjectiveSuccIso R n)
    _ = toSkeleton (regularProjective R) +
        toSkeleton (standardFreeProjective R n) :=
      Skeleton.toSkeleton_biprod _ _

/-- The isomorphism class of the standard rank-`n` free module is `n`
times the regular-module class. -/
@[simp]
theorem toSkeleton_standardFreeProjective (n : ℕ) :
    toSkeleton (standardFreeProjective R n) =
      n • toSkeleton (regularProjective R) := by
  induction n with
  | zero => simp only [toSkeleton_standardFreeProjective_zero, zero_nsmul]
  | succ n ih =>
      rw [toSkeleton_standardFreeProjective_succ, ih]
      rw [succ_nsmul, add_comm]

/-- The standard rank-`n` free module represents `n` times the regular
class in `RingK0`. -/
@[simp]
theorem mk_standardFreeProjective (n : ℕ) :
    K0.mk (standardFreeProjective R n) = n • regularClass R := by
  induction n with
  | zero => simp only [mk_standardFreeProjective_zero, zero_nsmul]
  | succ n ih =>
      rw [mk_standardFreeProjective_succ, ih]
      rw [succ_nsmul, add_comm]

/-- Cofinality of the regular class among classes of finitely generated
projectives. -/
theorem exists_add_eq_nsmul_regularClass (P : FGProjectiveCat.{u} R) :
    ∃ (n : ℕ) (Q : FGProjectiveCat.{u} R),
      K0.mk P + K0.mk Q = n • regularClass R := by
  obtain ⟨n, Q, ⟨e⟩⟩ := FGProjectiveCat.exists_biprod_iso_fin_free P
  refine ⟨n, Q, ?_⟩
  calc
    K0.mk P + K0.mk Q = K0.mk (P ⊞ Q) := (K0.mk_biprod P Q).symm
    _ = K0.mk (standardFreeProjective R n) := K0.mk_congr_of_iso e
    _ = n • regularClass R := mk_standardFreeProjective R n

/-- The regular-module class is cofinal already in the additive monoid of
isomorphism classes of finitely generated projectives. -/
theorem exists_toSkeleton_add_eq_nsmul_regular
    (P : FGProjectiveCat.{u} R) :
    ∃ (n : ℕ) (Q : FGProjectiveCat.{u} R),
      toSkeleton P + toSkeleton Q =
        n • toSkeleton (regularProjective R) := by
  obtain ⟨n, Q, ⟨e⟩⟩ := FGProjectiveCat.exists_biprod_iso_fin_free P
  refine ⟨n, Q, ?_⟩
  calc
    toSkeleton P + toSkeleton Q = toSkeleton (P ⊞ Q) :=
      (Skeleton.toSkeleton_biprod P Q).symm
    _ = toSkeleton (standardFreeProjective R n) :=
      congr_toSkeleton_of_iso e
    _ = n • toSkeleton (regularProjective R) :=
      toSkeleton_standardFreeProjective R n

private theorem grothendieck_exists_eq_of_sub_of
    (x : Algebra.GrothendieckAddGroup
      (Skeleton (FGProjectiveCat.{u} R))) :
    ∃ a b : Skeleton (FGProjectiveCat.{u} R),
      x = Algebra.GrothendieckAddGroup.of a -
        Algebra.GrothendieckAddGroup.of b := by
  induction x using AddLocalization.induction_on with
  | _ p =>
      refine ⟨p.1, p.2.1, ?_⟩
      symm
      change
        (AddLocalization.addMonoidOf
            (⊤ : AddSubmonoid (Skeleton (FGProjectiveCat.{u} R)))) p.1 -
          (AddLocalization.addMonoidOf
            (⊤ : AddSubmonoid (Skeleton (FGProjectiveCat.{u} R)))) p.2.1 =
          AddLocalization.mk p.1 p.2
      rw [← AddLocalization.mk_zero_eq_addMonoidOf_mk p.1,
        ← AddLocalization.mk_zero_eq_addMonoidOf_mk p.2.1,
        Algebra.GrothendieckAddGroup.mk_sub_mk]
      simp

/-- Every `RingK0` class is a difference of two projective classes. -/
theorem exists_eq_mk_sub_mk (x : RingK0 R) :
    ∃ P Q : FGProjectiveCat.{u} R, x = K0.mk P - K0.mk Q := by
  let y : Algebra.GrothendieckAddGroup
      (Skeleton (FGProjectiveCat.{u} R)) :=
    (K0.splitIso (FGProjectiveCat.{u} R)).inv x
  obtain ⟨a, b, hab⟩ := grothendieck_exists_eq_of_sub_of R y
  let P : FGProjectiveCat.{u} R :=
    (fromSkeleton (FGProjectiveCat.{u} R)).obj a
  let Q : FGProjectiveCat.{u} R :=
    (fromSkeleton (FGProjectiveCat.{u} R)).obj b
  refine ⟨P, Q, ?_⟩
  have hx : (K0.splitIso (FGProjectiveCat.{u} R)).hom y = x := by
    exact (K0.splitIso (FGProjectiveCat.{u} R)).addCommGroupIsoToAddEquiv.apply_symm_apply x
  rw [hab, map_sub] at hx
  have hP : (K0.splitIso (FGProjectiveCat.{u} R)).hom
      (Algebra.GrothendieckAddGroup.of a) = K0.mk P := by
    change K0.grothendieckToK0 (FGProjectiveCat.{u} R)
      (Algebra.GrothendieckAddGroup.of a) = K0.mk P
    rw [← toSkeleton_fromSkeleton_obj a]
    exact K0.grothendieckToK0_of_toSkeleton (FGProjectiveCat.{u} R) P
  have hQ : (K0.splitIso (FGProjectiveCat.{u} R)).hom
      (Algebra.GrothendieckAddGroup.of b) = K0.mk Q := by
    change K0.grothendieckToK0 (FGProjectiveCat.{u} R)
      (Algebra.GrothendieckAddGroup.of b) = K0.mk Q
    rw [← toSkeleton_fromSkeleton_obj b]
    exact K0.grothendieckToK0_of_toSkeleton (FGProjectiveCat.{u} R) Q
  rw [hP, hQ] at hx
  exact hx.symm

/-- Cofinality normal form: every `RingK0` class is a projective class minus
a finite multiple of the regular class. -/
theorem exists_eq_mk_sub_nsmul_regularClass (x : RingK0 R) :
    ∃ (P : FGProjectiveCat.{u} R) (n : ℕ),
      x = K0.mk P - n • regularClass R := by
  obtain ⟨P, Q, hx⟩ := exists_eq_mk_sub_mk R x
  obtain ⟨n, Q', hQ⟩ := exists_add_eq_nsmul_regularClass R Q
  refine ⟨P ⊞ Q', n, ?_⟩
  rw [K0.mk_biprod]
  rw [← hQ]
  rw [hx]
  abel

private theorem grothendieck_of_eq_iff_exists_add_eq
    (a b : Skeleton (FGProjectiveCat.{u} R)) :
    Algebra.GrothendieckAddGroup.of a =
        Algebra.GrothendieckAddGroup.of b ↔
      ∃ c : Skeleton (FGProjectiveCat.{u} R), a + c = b + c := by
  change
    (AddLocalization.addMonoidOf
        (⊤ : AddSubmonoid (Skeleton (FGProjectiveCat.{u} R)))) a =
      (AddLocalization.addMonoidOf
        (⊤ : AddSubmonoid (Skeleton (FGProjectiveCat.{u} R)))) b ↔ _
  rw [← AddLocalization.mk_zero_eq_addMonoidOf_mk a,
    ← AddLocalization.mk_zero_eq_addMonoidOf_mk b,
    AddLocalization.mk_eq_mk_iff, AddLocalization.r_iff_exists]
  constructor
  · rintro ⟨c, h⟩
    exact ⟨c, by simpa [add_comm] using h⟩
  · rintro ⟨c, h⟩
    exact ⟨⟨c, AddSubmonoid.mem_top c⟩, by simpa [add_comm] using h⟩

/-- Equality in `RingK0` is stable isomorphism after adding the same finite
free summand. -/
theorem mk_eq_mk_iff_exists_biprod_free_iso
    (P Q : FGProjectiveCat.{u} R) :
    (K0.mk P : RingK0 R) = K0.mk Q ↔
      ∃ n : ℕ, Nonempty
        (P ⊞ standardFreeProjective R n ≅
          Q ⊞ standardFreeProjective R n) := by
  constructor
  · intro h
    have hGroth := congrArg
      (K0.splitIso (FGProjectiveCat.{u} R)).inv h
    change
      (K0.splitK0ToGrothendieck (FGProjectiveCat.{u} R)) (K0.mk P) =
        (K0.splitK0ToGrothendieck (FGProjectiveCat.{u} R)) (K0.mk Q)
      at hGroth
    simp only [K0.splitK0ToGrothendieck, K0.lift_mk] at hGroth
    obtain ⟨c, hc⟩ :=
      (grothendieck_of_eq_iff_exists_add_eq R
        (toSkeleton P) (toSkeleton Q)).1 hGroth
    let T : FGProjectiveCat.{u} R :=
      (fromSkeleton (FGProjectiveCat.{u} R)).obj c
    have hStableSkeleton : toSkeleton (P ⊞ T) = toSkeleton (Q ⊞ T) := by
      rw [Skeleton.toSkeleton_biprod, Skeleton.toSkeleton_biprod,
        toSkeleton_fromSkeleton_obj, hc]
    let e : P ⊞ T ≅ Q ⊞ T := Skeleton.isoOfEq hStableSkeleton
    obtain ⟨n, T', ⟨cT⟩⟩ := FGProjectiveCat.exists_biprod_iso_fin_free T
    refine ⟨n, ⟨?_⟩⟩
    exact
      (biprod.mapIso (Iso.refl P) cT.symm).trans
        ((biprod.associator P T T').symm.trans
          ((biprod.mapIso e (Iso.refl T')).trans
            ((biprod.associator Q T T').trans
              (biprod.mapIso (Iso.refl Q) cT))))
  · rintro ⟨n, ⟨e⟩⟩
    have hStable :
        K0.mk P + K0.mk (standardFreeProjective R n) =
          K0.mk Q + K0.mk (standardFreeProjective R n) := by
      rw [← K0.mk_biprod, ← K0.mk_biprod]
      exact K0.mk_congr_of_iso e
    exact add_right_cancel hStable

/-- A projective represents `n[R]` exactly when it becomes isomorphic to the
rank-`n` free module after adding the same finite free summand to both sides. -/
theorem mk_eq_nsmul_regularClass_iff_exists_biprod_free_iso
    (P : FGProjectiveCat.{u} R) (n : ℕ) :
    (K0.mk P : RingK0 R) = n • regularClass R ↔
      ∃ m : ℕ, Nonempty
        (P ⊞ standardFreeProjective R m ≅
          standardFreeProjective R n ⊞ standardFreeProjective R m) := by
  rw [← mk_standardFreeProjective R n]
  exact mk_eq_mk_iff_exists_biprod_free_iso R P
    (standardFreeProjective R n)

/-- The regular-module isomorphism class is a cofinal element in the
projective-class additive monoid. -/
theorem regularSkeletonClass_isCofinalElement :
    AddMonoid.IsCofinalElement
      (toSkeleton (regularProjective R)) := by
  intro p
  let P : FGProjectiveCat.{u} R :=
    (fromSkeleton (FGProjectiveCat.{u} R)).obj p
  obtain ⟨n, Q, h⟩ := exists_toSkeleton_add_eq_nsmul_regular R P
  refine ⟨n, toSkeleton Q, ?_⟩
  simpa [P, toSkeleton_fromSkeleton_obj] using h

/-- In the integral projective-class monoid algebra, all monomials and the
powers of the regular-module monomial have the same saturation. -/
theorem projectiveClassMonomialSubmonoid_saturation_eq_regularPowers :
    (AddMonoidAlgebra.monomialSubmonoid ℤ
        (Skeleton (FGProjectiveCat.{u} R))).saturation =
      (Submonoid.powers
        (AddMonoidAlgebra.of' ℤ
          (Skeleton (FGProjectiveCat.{u} R))
          (toSkeleton (regularProjective R)))).saturation :=
  AddMonoidAlgebra.monomialSubmonoid_saturation_eq_powers
    ℤ (Skeleton (FGProjectiveCat.{u} R))
    (regularSkeletonClass_isCofinalElement R)

/-- A ring is a localization of the projective-class monoid algebra at all
monomials exactly when it is a localization at powers of the regular-module
monomial. -/
theorem isLocalization_projectiveClassMonomials_iff_regularPowers
    {A : Type w} [CommRing A]
    [Algebra
      (AddMonoidAlgebra ℤ (Skeleton (FGProjectiveCat.{u} R))) A] :
    IsLocalization
        (AddMonoidAlgebra.monomialSubmonoid ℤ
          (Skeleton (FGProjectiveCat.{u} R))) A ↔
      IsLocalization
        (Submonoid.powers
          (AddMonoidAlgebra.of' ℤ
            (Skeleton (FGProjectiveCat.{u} R))
            (toSkeleton (regularProjective R)))) A :=
  AddMonoidAlgebra.isLocalization_monomialSubmonoid_iff_powers
    ℤ (Skeleton (FGProjectiveCat.{u} R))
    (regularSkeletonClass_isCofinalElement R)

/-- In the existing small idempotent model, the literal rank-n free object
has n times the literal regular skeleton class. -/
theorem idempotentFreeSkeletonClass_eq_nsmul_regular (n : ℕ) :
    toSkeleton ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n) =
      n • toSkeleton
        ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (1 : ℕ)) := by
  induction n with
  | zero =>
      rw [zero_nsmul]
      exact (congr_toSkeleton_of_iso
        (FGProjectiveCat.IdempotentModel.freeZeroIso R)).trans Skeleton.toSkeleton_zero
  | succ n hn =>
      calc
        toSkeleton ((Idempotents.toKaroubi
            (FGProjectiveCat.FiniteRowRanks R)).obj (n + 1)) =
            toSkeleton
              (((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n) ⊞
                ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (1 : ℕ))) :=
          congr_toSkeleton_of_iso (FGProjectiveCat.IdempotentModel.freeBiprodIso R n 1)
        _ = toSkeleton
              ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n) +
            toSkeleton
              ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (1 : ℕ)) :=
          Skeleton.toSkeleton_biprod _ _
        _ = (n + 1) • toSkeleton
              ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (1 : ℕ)) := by
          rw [hn, add_nsmul, one_nsmul]

/-- Every actual object of the small row-idempotent model has a complement
to a literal finite free object, transported through its existing exact equivalence. -/
theorem idempotent_exists_biprod_iso_free
    (P : FGProjectiveCat.IdempotentModel R) :
    ∃ (n : ℕ) (Q : FGProjectiveCat.IdempotentModel R),
      Nonempty (P ⊞ Q ≅
        (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n) := by
  let E := FGProjectiveCat.IdempotentModel.equivalence R
  obtain ⟨n, Q, ⟨e⟩⟩ :=
    FGProjectiveCat.exists_biprod_iso_fin_free (E.functor.obj P)
  let Q' : FGProjectiveCat.IdempotentModel R := E.inverse.obj Q
  letI : PreservesBinaryBiproduct P Q' E.functor :=
    preservesBinaryBiproduct_of_preservesBiproduct E.functor P Q'
  let ec : E.functor.obj (P ⊞ Q') ≅
      E.functor.obj
        ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n) :=
    E.functor.mapBiprod P Q' ≪≫
      biprod.mapIso (Iso.refl (E.functor.obj P)) (E.counitIso.app Q) ≪≫
      e ≪≫ (FGProjectiveCat.IdempotentModel.freeIso R n).symm
  exact ⟨n, Q', ⟨E.fullyFaithfulFunctor.preimageIso ec⟩⟩

/-- The literal rank-one skeleton class is cofinal in the existing Ring-only
small projective model. No caller model/cofinality witness is required. -/
theorem idempotentRegularSkeletonClass_isCofinalElement :
    AddMonoid.IsCofinalElement
      (toSkeleton
        ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (1 : ℕ))) := by
  intro p
  let P : FGProjectiveCat.IdempotentModel R :=
    (fromSkeleton (FGProjectiveCat.IdempotentModel R)).obj p
  obtain ⟨n, Q, ⟨e⟩⟩ := idempotent_exists_biprod_iso_free R P
  refine ⟨n, toSkeleton Q, ?_⟩
  have h : toSkeleton P + toSkeleton Q =
      n • toSkeleton
        ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (1 : ℕ)) :=
    (Skeleton.toSkeleton_biprod P Q).symm.trans
      ((congr_toSkeleton_of_iso e).trans
        (idempotentFreeSkeletonClass_eq_nsmul_regular R n))
  simpa only [P, toSkeleton_fromSkeleton_obj] using h

/-- A zero-difference pair in the existing Ring-only idempotent model becomes
isomorphic after adding the SAME literal finite free summand to both coordinates.
The proof uses the existing stable-cross theorem and the derived finite-free
complement; it does not assume invariant basis number or a homology comparison. -/
theorem idempotentPair_zeroDifference_iff_exists_same_free_stabilization
    (P Q : FGProjectiveCat.IdempotentModel R) :
    (CategoryTheory.SInverseS.Pair.mk P Q).difference = 0 ↔
      ∃ n : ℕ, Nonempty
        (P ⊞ (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n ≅
          Q ⊞ (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n) := by
  constructor
  · intro h
    let X : CategoryTheory.SInverseS.Pair (FGProjectiveCat.IdempotentModel R) := ⟨P, Q⟩
    let Z : CategoryTheory.SInverseS.Pair (FGProjectiveCat.IdempotentModel R) := ⟨0, 0⟩
    have hZ : Z.difference = 0 := by
      simp only [Z, CategoryTheory.SInverseS.Pair.difference, sub_self]
    have hXZ : X.difference = Z.difference := h.trans hZ.symm
    obtain ⟨t, ht⟩ :=
      CategoryTheory.SInverseS.Pair.exists_stable_cross_of_difference_eq hXZ
    have ht' : toSkeleton P + t = toSkeleton Q + t := by
      simpa only [X, Z, Skeleton.toSkeleton_zero, add_zero, zero_add] using ht
    let T : FGProjectiveCat.IdempotentModel R :=
      (fromSkeleton (FGProjectiveCat.IdempotentModel R)).obj t
    have hStable : toSkeleton (P ⊞ T) = toSkeleton (Q ⊞ T) := by
      rw [Skeleton.toSkeleton_biprod, Skeleton.toSkeleton_biprod,
        toSkeleton_fromSkeleton_obj]
      exact ht'
    let e : P ⊞ T ≅ Q ⊞ T := Skeleton.isoOfEq hStable
    obtain ⟨m, T', ⟨cT⟩⟩ := idempotent_exists_biprod_iso_free R T
    refine ⟨m, ⟨?_⟩⟩
    exact
      (biprod.mapIso (Iso.refl P) cT.symm) ≪≫
        (biprod.associator P T T').symm ≪≫
          biprod.mapIso e (Iso.refl T') ≪≫
            biprod.associator Q T T' ≪≫
              biprod.mapIso (Iso.refl Q) cT
  · rintro ⟨n, ⟨e⟩⟩
    let F : FGProjectiveCat.IdempotentModel R :=
      (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n
    have hStable : toSkeleton P + toSkeleton F = toSkeleton Q + toSkeleton F :=
      (Skeleton.toSkeleton_biprod P F).symm.trans
        ((congr_toSkeleton_of_iso e).trans (Skeleton.toSkeleton_biprod Q F))
    have hGroth := congrArg
      (fun s : Skeleton (FGProjectiveCat.IdempotentModel R) =>
        Algebra.GrothendieckAddGroup.of s) hStable
    simp only [map_add] at hGroth
    change Algebra.GrothendieckAddGroup.of (toSkeleton P) -
      Algebra.GrothendieckAddGroup.of (toSkeleton Q) = 0
    exact sub_eq_zero.mpr (add_right_cancel hGroth)

/-! ## Actual projective-complement stabilization of a diagonal pair -/

/-- Every original diagonal `(P,P)` has an actual arrow to a literal
finite free diagonal. Its stabilizer is the derived projective complement
`Q`; both raw isomorphism fields are the same `Q ⊞ P ≅ Rⁿ`. This gives
no stable-free assertion about `P` and uses no IBN or nonzero-Ring premise. -/
theorem idempotentDiagonal_exists_free_stabilization
    (P : FGProjectiveCat.IdempotentModel R) :
    ∃ (n : ℕ) (Q : FGProjectiveCat.IdempotentModel R)
      (e : Q ⊞ P ≅ (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n)
      (h : CategoryTheory.SInverseS.diagonalZeroComponentObject P ⟶
        CategoryTheory.SInverseS.diagonalZeroComponentObject
          ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n)),
      h = ObjectProperty.homMk
        (eqToHom (CategoryTheory.SInverseS.diagonalZeroComponentObject_obj P) ≫
          CategoryTheory.SInverseS.Hom.mk
            ({ stabilizer := Q, hom₁ := e, hom₂ := e } :
              CategoryTheory.SInverseS.RawHom (CategoryTheory.SInverseS.Pair.mk P P)
                (CategoryTheory.SInverseS.Pair.mk
                  ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n)
                  ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n))) ≫
          eqToHom ((CategoryTheory.SInverseS.diagonalZeroComponentObject_obj
            ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n)).symm)) := by
  obtain ⟨n, Q, ⟨e₀⟩⟩ := idempotent_exists_biprod_iso_free R P
  let F := (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n
  let e : Q ⊞ P ≅ F := biprod.braiding Q P ≪≫ e₀
  let r : CategoryTheory.SInverseS.RawHom
      (CategoryTheory.SInverseS.Pair.mk P P) (CategoryTheory.SInverseS.Pair.mk F F) :=
    { stabilizer := Q, hom₁ := e, hom₂ := e }
  let h : CategoryTheory.SInverseS.diagonalZeroComponentObject P ⟶
      CategoryTheory.SInverseS.diagonalZeroComponentObject F :=
    ObjectProperty.homMk
      (eqToHom (CategoryTheory.SInverseS.diagonalZeroComponentObject_obj P) ≫
        CategoryTheory.SInverseS.Hom.mk r ≫
        eqToHom ((CategoryTheory.SInverseS.diagonalZeroComponentObject_obj F).symm))
  exact ⟨n, Q, e, h, rfl⟩

end RingK0
end AlgebraicKTheory
