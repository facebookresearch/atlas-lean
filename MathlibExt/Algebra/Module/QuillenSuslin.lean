/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Basic

import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Quillen–Suslin theorem

Formalizes that every finitely generated projective module over a polynomial ring over a field is
free.
The proof uses idempotent matrices, Roberts' local proof of Horrocks' theorem, Quillen patching,
and induction on the number of variables.
-/

namespace MathlibExt.Algebra.Module.QuillenSuslinWanted

noncomputable section

universe u v

private def qsMatrixEquiv
    {R : Type*} [CommRing R]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : Matrix ι ι R) (F : Matrix κ κ R) : Prop :=
  ∃ A : Matrix ι κ R, ∃ B : Matrix κ ι R, A * B = E ∧ B * A = F

private def qsShear {R : Type*} [CommRing R] (j : R) :
    Polynomial R →+* Polynomial (Polynomial R) :=
  Polynomial.eval₂RingHom
    ((Polynomial.C : Polynomial R →+* Polynomial (Polynomial R)).comp Polynomial.C)
    (Polynomial.C Polynomial.X + Polynomial.C (Polynomial.C j) * Polynomial.X)

private def qsShiftX {R : Type*} [CommRing R] (j : R) :
    Polynomial (Polynomial R) →+* Polynomial (Polynomial R) :=
  Polynomial.eval₂RingHom (qsShear j) Polynomial.X

private def qsScaleY {R : Type*} [CommRing R] (r : R) :
    Polynomial (Polynomial R) →+* Polynomial (Polynomial R) :=
  Polynomial.eval₂RingHom Polynomial.C
    (Polynomial.C (Polynomial.C r) * Polynomial.X)

private def qsConstantAtZero {R : Type*} [CommRing R] :
    Polynomial R →+* Polynomial R :=
  Polynomial.C.comp Polynomial.constantCoeff

private def qsEvalXY {R : Type*} [CommRing R] :
    Polynomial (Polynomial R) →+* Polynomial R :=
  Polynomial.eval₂RingHom qsConstantAtZero Polynomial.X

private def qsMonicSubmonoid (R : Type*) [CommRing R] : Submonoid (Polynomial R) where
  carrier := {p | p.Monic}
  one_mem' := Polynomial.monic_one
  mul_mem' hp hq := hp.mul hq

private theorem qs_divByMonic_mul_monic
    {R : Type*} [CommRing R] [Nontrivial R]
    (a : Polynomial R) {b d : Polynomial R}
    (hb : b.Monic) (hd : d.Monic) :
    (d * a) /ₘ (d * b) = a /ₘ b := by
  apply (Polynomial.div_modByMonic_unique (a /ₘ b) (d * (a %ₘ b)) (hd.mul hb) ?_).1
  constructor
  · rw [mul_assoc, ← mul_add, Polynomial.modByMonic_add_div]
  · by_cases hrem : a %ₘ b = 0
    · rw [hrem, mul_zero, Polynomial.degree_zero, bot_lt_iff_ne_bot,
        Ne, Polynomial.degree_eq_bot]
      exact (hd.mul hb).ne_zero
    · have hdrem : d * (a %ₘ b) ≠ 0 := fun h ↦
        hrem (hd.mul_right_eq_zero_iff.mp h)
      rw [Polynomial.degree_eq_natDegree hdrem,
        Polynomial.degree_eq_natDegree (hd.mul hb).ne_zero]
      have hnat : (a %ₘ b).natDegree < b.natDegree := by
        simpa [Polynomial.degree_eq_natDegree hrem,
          Polynomial.degree_eq_natDegree hb.ne_zero] using
            Polynomial.degree_modByMonic_lt a hb
      norm_cast
      rw [hd.natDegree_mul' hrem, hd.natDegree_mul hb]
      exact Nat.add_lt_add_left hnat d.natDegree

private theorem qs_divByMonic_eq_of_localization_rel
    {R : Type*} [CommRing R] [Nontrivial R]
    {a c : Polynomial R} {b d : qsMonicSubmonoid R}
    (h : Localization.r (qsMonicSubmonoid R) (a, b) (c, d)) :
    a /ₘ (b : Polynomial R) = c /ₘ (d : Polynomial R) := by
  obtain ⟨u, hu⟩ := Localization.r_iff_exists.mp h
  have hcross : (d : Polynomial R) * a = (b : Polynomial R) * c := by
    exact u.property.isRegular.left hu
  calc
    a /ₘ (b : Polynomial R) =
        ((d : Polynomial R) * a) /ₘ ((d : Polynomial R) * b) :=
      (qs_divByMonic_mul_monic a b.property d.property).symm
    _ = ((b : Polynomial R) * c) /ₘ ((d : Polynomial R) * b) := by rw [hcross]
    _ = ((b : Polynomial R) * c) /ₘ ((b : Polynomial R) * d) := by
      rw [mul_comm (d : Polynomial R) b]
    _ = c /ₘ (d : Polynomial R) :=
      qs_divByMonic_mul_monic c d.property b.property

private def qsPolynomialPartFun
    {R : Type*} [CommRing R] [Nontrivial R]
    (z : Localization (qsMonicSubmonoid R)) : Polynomial R :=
  Localization.liftOn z
    (fun a b ↦ a /ₘ (b : Polynomial R))
    qs_divByMonic_eq_of_localization_rel

private theorem qsPolynomialPartFun_mk
    {R : Type*} [CommRing R] [Nontrivial R]
    (a : Polynomial R) (b : qsMonicSubmonoid R) :
    qsPolynomialPartFun (Localization.mk a b) = a /ₘ (b : Polynomial R) :=
  rfl

private theorem qsPolynomialPartFun_add
    {R : Type*} [CommRing R] [Nontrivial R]
    (x y : Localization (qsMonicSubmonoid R)) :
    qsPolynomialPartFun (x + y) = qsPolynomialPartFun x + qsPolynomialPartFun y := by
  induction x using Localization.induction_on with
  | _ x =>
    induction y using Localization.induction_on with
    | _ y =>
      rcases x with ⟨a, b⟩
      rcases y with ⟨c, d⟩
      rw [Localization.add_mk]
      simp only [qsPolynomialPartFun_mk, Polynomial.add_divByMonic]
      change
        ((b : Polynomial R) * c) /ₘ ((b : Polynomial R) * d) +
          ((d : Polynomial R) * a) /ₘ ((b : Polynomial R) * d) =
        a /ₘ (b : Polynomial R) + c /ₘ (d : Polynomial R)
      calc
        _ = c /ₘ (d : Polynomial R) +
            ((d : Polynomial R) * a) /ₘ ((d : Polynomial R) * b) := by
          rw [qs_divByMonic_mul_monic c d.property b.property,
            mul_comm (b : Polynomial R) d]
        _ = c /ₘ (d : Polynomial R) + a /ₘ (b : Polynomial R) := by
          rw [qs_divByMonic_mul_monic a b.property d.property]
        _ = _ := add_comm _ _

private theorem qsPolynomialPartFun_smul
    {R : Type*} [CommRing R] [Nontrivial R]
    (r : R) (x : Localization (qsMonicSubmonoid R)) :
    qsPolynomialPartFun (r • x) = r • qsPolynomialPartFun x := by
  induction x using Localization.induction_on with
  | _ x =>
    rcases x with ⟨a, b⟩
    rw [Algebra.smul_def]
    change qsPolynomialPartFun
      (Localization.mk (Polynomial.C r) 1 * Localization.mk a b) = _
    rw [Localization.mk_mul]
    simp only [qsPolynomialPartFun_mk, one_mul]
    rw [← Polynomial.smul_eq_C_mul, Polynomial.smul_divByMonic]

private def qsPolynomialPart
    (R : Type*) [CommRing R] [Nontrivial R] :
    Localization (qsMonicSubmonoid R) →ₗ[R] Polynomial R where
  toFun := qsPolynomialPartFun
  map_add' := qsPolynomialPartFun_add
  map_smul' := qsPolynomialPartFun_smul

private theorem qsPolynomialPart_algebraMap
    {R : Type*} [CommRing R] [Nontrivial R]
    (p : Polynomial R) :
    qsPolynomialPart R
        (algebraMap (Polynomial R) (Localization (qsMonicSubmonoid R)) p) = p := by
  change p /ₘ (1 : Polynomial R) = p
  exact Polynomial.divByMonic_one p

private theorem qs_exists_monic_lift
    {R S : Type*} [CommRing R] [CommRing S] [Nontrivial R] [Nontrivial S]
    (f : R →+* S) (hf : Function.Surjective f)
    {p : Polynomial S} (hp : p.Monic) :
    ∃ q : Polynomial R, q.Monic ∧ q.map f = p := by
  let n := p.natDegree
  have hpdeg : p.degree = ((Polynomial.X : Polynomial S) ^ n).degree := by
    rw [Polynomial.degree_eq_natDegree hp.ne_zero, Polynomial.degree_X_pow]
  have hplc : p.leadingCoeff =
      ((Polynomial.X : Polynomial S) ^ n).leadingCoeff := by
    simp [hp.leadingCoeff]
  have hlower : (p - (Polynomial.X : Polynomial S) ^ n).degree < (n : WithBot ℕ) := by
    simpa [Polynomial.degree_eq_natDegree hp.ne_zero] using
      Polynomial.degree_sub_lt_left hpdeg hp.ne_zero hplc
  obtain ⟨q₀, hq₀⟩ := Polynomial.map_surjective f hf
    (p - (Polynomial.X : Polynomial S) ^ n)
  let q := (Polynomial.X : Polynomial R) ^ n +
    q₀ %ₘ (Polynomial.X : Polynomial R) ^ n
  refine ⟨q, Polynomial.monic_X_pow_add ?_, ?_⟩
  · simpa only [Polynomial.degree_X_pow] using
      Polynomial.degree_modByMonic_lt q₀ (Polynomial.monic_X_pow n)
  · dsimp only [q]
    rw [Polynomial.map_add,
      Polynomial.map_modByMonic f (Polynomial.monic_X_pow n), hq₀]
    simp only [Polynomial.map_pow, Polynomial.map_X]
    rw [(Polynomial.modByMonic_eq_self_iff (Polynomial.monic_X_pow n)).mpr <| by
      simpa only [Polynomial.degree_X_pow] using hlower]
    ring

private theorem qs_map_monicSubmonoid_eq
    {R S : Type*} [CommRing R] [CommRing S] [Nontrivial R] [Nontrivial S]
    (f : R →+* S) (hf : Function.Surjective f) :
    (qsMonicSubmonoid R).map (Polynomial.mapRingHom f) = qsMonicSubmonoid S := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq.map f
  · intro hp
    obtain ⟨q, hq, rfl⟩ := qs_exists_monic_lift f hf hp
    exact Submonoid.mem_map_of_mem _ hq

private theorem qs_monicLocalization_isFractionRing
    (k : Type*) [Field k] :
    IsFractionRing (Polynomial k) (Localization (qsMonicSubmonoid k)) := by
  apply (IsLocalization.iff_of_le_of_exists_dvd
    (M := qsMonicSubmonoid k) (S := Localization (qsMonicSubmonoid k))
    (nonZeroDivisors (Polynomial k)) ?_ ?_).mp
  · exact Localization.isLocalization
  · intro p hp
    exact hp.mem_nonZeroDivisors
  · intro p hp
    have hp0 : p ≠ 0 :=
      mem_nonZeroDivisors_iff_ne_zero.mp hp
    let q := p * Polynomial.C p.leadingCoeff⁻¹
    refine ⟨q, Polynomial.monic_mul_leadingCoeff_inv hp0, ?_⟩
    exact ⟨Polynomial.C p.leadingCoeff⁻¹, rfl⟩

private theorem qs_nonzero_polynomial_maps_to_unit
    {k A : Type*} [Field k] [CommRing A] [Nontrivial A]
    (f : k →+* A) {p : Polynomial k} (hp : p ≠ 0) :
    IsUnit (((algebraMap (Polynomial A)
      (Localization (qsMonicSubmonoid A))).comp
        (Polynomial.mapRingHom f)) p) := by
  let p' := p * Polynomial.C p.leadingCoeff⁻¹
  have hp' : p'.Monic := Polynomial.monic_mul_leadingCoeff_inv hp
  let s : qsMonicSubmonoid A := ⟨p'.map f, hp'.map f⟩
  have hmonic : IsUnit (algebraMap (Polynomial A)
      (Localization (qsMonicSubmonoid A)) (s : Polynomial A)) :=
    IsLocalization.map_units _ s
  have hlc : IsUnit (f p.leadingCoeff) :=
    (isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp)).map f
  have hconstant : IsUnit (algebraMap (Polynomial A)
      (Localization (qsMonicSubmonoid A))
        (Polynomial.C (f p.leadingCoeff))) :=
    (Polynomial.isUnit_C.mpr hlc).map
      (algebraMap (Polynomial A) (Localization (qsMonicSubmonoid A)))
  have hpdecomp : p' * Polynomial.C p.leadingCoeff = p := by
    simp only [p', mul_assoc, ← Polynomial.C_mul]
    rw [inv_mul_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hp), map_one, mul_one]
  rw [← hpdecomp, map_mul]
  change IsUnit
    (algebraMap (Polynomial A) (Localization (qsMonicSubmonoid A))
        (p'.map f) *
      algebraMap (Polynomial A) (Localization (qsMonicSubmonoid A))
        ((Polynomial.C p.leadingCoeff).map f))
  simpa [s] using hmonic.mul hconstant

private noncomputable def qsFractionToMonicLocalization
    (k A : Type*) [Field k] [CommRing A] [Nontrivial A]
    (f : k →+* A) :
    FractionRing (Polynomial k) →+*
      Localization (qsMonicSubmonoid A) :=
  IsLocalization.lift (M := nonZeroDivisors (Polynomial k))
    (S := FractionRing (Polynomial k)) fun s ↦
      qs_nonzero_polynomial_maps_to_unit f
        (mem_nonZeroDivisors_iff_ne_zero.mp s.property)

private theorem qsFractionToMonicLocalization_algebraMap
    (k A : Type*) [Field k] [CommRing A] [Nontrivial A]
    (f : k →+* A) (p : Polynomial k) :
    qsFractionToMonicLocalization k A f
        (algebraMap (Polynomial k) (FractionRing (Polynomial k)) p) =
      algebraMap (Polynomial A) (Localization (qsMonicSubmonoid A))
        (p.map f) := by
  exact IsLocalization.lift_eq _ p

private def qsGenericMap
    (k : Type*) [Field k] (n : ℕ) :
    Polynomial (MvPolynomial (Fin n) k) →+*
      MvPolynomial (Fin n) (FractionRing (Polynomial k)) :=
  Polynomial.eval₂RingHom
    (MvPolynomial.map (algebraMap k (FractionRing (Polynomial k))))
    (MvPolynomial.C
      (algebraMap (Polynomial k) (FractionRing (Polynomial k)) Polynomial.X))

private noncomputable def qsGenericSpecialization
    (k : Type*) [Field k] (n : ℕ)
    (A : Type*) [CommRing A] [Nontrivial A]
    (f : MvPolynomial (Fin n) k →+* A) :
    MvPolynomial (Fin n) (FractionRing (Polynomial k)) →+*
      Localization (qsMonicSubmonoid A) :=
  MvPolynomial.eval₂Hom
    (qsFractionToMonicLocalization k A (f.comp MvPolynomial.C))
    (fun i ↦ algebraMap (Polynomial A) (Localization (qsMonicSubmonoid A))
      (Polynomial.C (f (MvPolynomial.X i))))

private theorem qs_genericSpecialization_comp_genericMap
    (k : Type*) [Field k] (n : ℕ)
    (A : Type*) [CommRing A] [Nontrivial A]
    (f : MvPolynomial (Fin n) k →+* A) :
    (qsGenericSpecialization k n A f).comp (qsGenericMap k n) =
      (algebraMap (Polynomial A)
        (Localization (qsMonicSubmonoid A))).comp
        (Polynomial.mapRingHom f) := by
  let K := FractionRing (Polynomial k)
  let Q := Localization (qsMonicSubmonoid A)
  let coeff : K →+* Q :=
    qsFractionToMonicLocalization k A (f.comp MvPolynomial.C)
  let ev : MvPolynomial (Fin n) K →+* Q :=
    qsGenericSpecialization k n A f
  have hcoeff : ev.comp
      (MvPolynomial.map (algebraMap k K)) =
        (algebraMap (Polynomial A) Q).comp
          ((Polynomial.C : A →+* Polynomial A).comp f) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      dsimp only [ev, qsGenericSpecialization]
      simp only [RingHom.comp_apply, MvPolynomial.map_C,
        MvPolynomial.eval₂Hom_C]
      change coeff (algebraMap k K r) =
        algebraMap (Polynomial A) Q (Polynomial.C (f (MvPolynomial.C r)))
      rw [show algebraMap k K r =
          algebraMap (Polynomial k) K (Polynomial.C r) by
        exact IsScalarTower.algebraMap_apply k (Polynomial k) K r]
      rw [qsFractionToMonicLocalization_algebraMap]
      simp only [Polynomial.map_C, RingHom.coe_comp, Function.comp_apply]
      rfl
    · intro i
      dsimp only [ev, qsGenericSpecialization]
      simp only [RingHom.comp_apply, MvPolynomial.map_X,
        MvPolynomial.eval₂Hom_X']
      rfl
  apply Polynomial.ringHom_ext
  · intro b
    simpa [qsGenericMap, ev] using DFunLike.congr_fun hcoeff b
  · simp only [RingHom.comp_apply, qsGenericMap,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      qsGenericSpecialization, MvPolynomial.eval₂Hom_C]
    rw [qsFractionToMonicLocalization_algebraMap]
    simp

private noncomputable def qsResidueMonicMap
    (R : Type*) [CommRing R] [IsLocalRing R] :
    Localization (qsMonicSubmonoid R) →+*
      Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R)) := by
  let f := Polynomial.mapRingHom (IsLocalRing.residue R)
  have hsub : (qsMonicSubmonoid R).map f =
      qsMonicSubmonoid (IsLocalRing.ResidueField R) :=
    qs_map_monicSubmonoid_eq _ IsLocalRing.residue_surjective
  let _ : IsLocalization ((qsMonicSubmonoid R).map f)
      (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R))) := by
    rw [hsub]
    infer_instance
  exact IsLocalization.map _ f (qsMonicSubmonoid R).le_comap_map

private theorem qsResidueMonicMap_algebraMap
    (R : Type*) [CommRing R] [IsLocalRing R] (p : Polynomial R) :
    qsResidueMonicMap R
        (algebraMap (Polynomial R) (Localization (qsMonicSubmonoid R)) p) =
      algebraMap (Polynomial (IsLocalRing.ResidueField R))
        (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R)))
        (p.map (IsLocalRing.residue R)) := by
  let f := Polynomial.mapRingHom (IsLocalRing.residue R)
  have hsub : (qsMonicSubmonoid R).map f =
      qsMonicSubmonoid (IsLocalRing.ResidueField R) :=
    qs_map_monicSubmonoid_eq _ IsLocalRing.residue_surjective
  let _ : IsLocalization ((qsMonicSubmonoid R).map f)
      (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R))) := by
    rw [hsub]
    infer_instance
  change (IsLocalization.map
    (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R))) f
      (qsMonicSubmonoid R).le_comap_map)
        (algebraMap (Polynomial R) (Localization (qsMonicSubmonoid R)) p) = _
  exact IsLocalization.map_eq _ _

private theorem qsResidueMonicMap_mk
    (R : Type*) [CommRing R] [IsLocalRing R]
    (p : Polynomial R) (s : qsMonicSubmonoid R) :
    qsResidueMonicMap R (Localization.mk p s) =
      Localization.mk (p.map (IsLocalRing.residue R))
        (⟨(s : Polynomial R).map (IsLocalRing.residue R),
          s.property.map (IsLocalRing.residue R)⟩ :
          qsMonicSubmonoid (IsLocalRing.ResidueField R)) := by
  let f := Polynomial.mapRingHom (IsLocalRing.residue R)
  have hsub : (qsMonicSubmonoid R).map f =
      qsMonicSubmonoid (IsLocalRing.ResidueField R) :=
    qs_map_monicSubmonoid_eq _ IsLocalRing.residue_surjective
  let _ : IsLocalization ((qsMonicSubmonoid R).map f)
      (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R))) := by
    rw [hsub]
    infer_instance
  change (IsLocalization.map
    (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R))) f
      (qsMonicSubmonoid R).le_comap_map) (Localization.mk p s) = _
  rw [Localization.mk_eq_mk', IsLocalization.map_mk', Localization.mk_eq_mk']
  rfl

private theorem qsPolynomialPart_map_residue
    (R : Type*) [CommRing R] [IsLocalRing R]
    (z : Localization (qsMonicSubmonoid R)) :
    (qsPolynomialPart R z).map (IsLocalRing.residue R) =
      qsPolynomialPart (IsLocalRing.ResidueField R) (qsResidueMonicMap R z) := by
  induction z using Localization.induction_on with
  | _ x =>
    rcases x with ⟨p, s⟩
    rw [qsResidueMonicMap_mk]
    change (p /ₘ (s : Polynomial R)).map (IsLocalRing.residue R) =
      p.map (IsLocalRing.residue R) /ₘ
        (s : Polynomial R).map (IsLocalRing.residue R)
    exact Polynomial.map_divByMonic (IsLocalRing.residue R) s.property

private def qsMatrixPolynomialPart
    (R : Type*) [CommRing R] [Nontrivial R]
    {ι κ : Type*} :
    Matrix ι κ (Localization (qsMonicSubmonoid R)) →ₗ[R]
      Matrix ι κ (Polynomial R) where
  toFun A i j := qsPolynomialPart R (A i j)
  map_add' A B := by
    apply Matrix.ext
    intro i j
    change qsPolynomialPart R (A i j + B i j) =
      qsPolynomialPart R (A i j) + qsPolynomialPart R (B i j)
    exact (qsPolynomialPart R).map_add (A i j) (B i j)
  map_smul' r A := by
    apply Matrix.ext
    intro i j
    change qsPolynomialPart R (r • A i j) = r • qsPolynomialPart R (A i j)
    exact (qsPolynomialPart R).map_smul r (A i j)

private theorem qsMatrixPolynomialPart_transpose
    (R : Type*) [CommRing R] [Nontrivial R]
    {ι κ : Type*}
    (A : Matrix ι κ (Localization (qsMonicSubmonoid R))) :
    qsMatrixPolynomialPart R A.transpose =
      (qsMatrixPolynomialPart R A).transpose :=
  rfl

private theorem qsMatrixPolynomialPart_algebraMap
    {R : Type*} [CommRing R] [Nontrivial R]
    {ι κ : Type*} (A : Matrix ι κ (Polynomial R)) :
    qsMatrixPolynomialPart R
        (A.map (algebraMap (Polynomial R)
          (Localization (qsMonicSubmonoid R)))) = A := by
  apply Matrix.ext
  intro i j
  exact qsPolynomialPart_algebraMap (A i j)

private theorem qsMatrixPolynomialPart_map_residue
    (R : Type*) [CommRing R] [IsLocalRing R]
    {ι κ : Type*}
    (A : Matrix ι κ (Localization (qsMonicSubmonoid R)))
    (C : Matrix ι κ (Polynomial (IsLocalRing.ResidueField R)))
    (hAC : A.map (qsResidueMonicMap R) =
      C.map (algebraMap (Polynomial (IsLocalRing.ResidueField R))
        (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R))))) :
    (qsMatrixPolynomialPart R A).map
      (Polynomial.mapRingHom (IsLocalRing.residue R)) = C := by
  apply Matrix.ext
  intro i j
  have hij := congrFun (congrFun hAC i) j
  have hpart := qsPolynomialPart_map_residue R (A i j)
  change qsResidueMonicMap R (A i j) =
    algebraMap (Polynomial (IsLocalRing.ResidueField R))
      (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R))) (C i j) at hij
  rw [hij, qsPolynomialPart_algebraMap] at hpart
  exact hpart

private theorem qsPolynomialPart_mul_eq_zero
    {R : Type*} [CommRing R] [Nontrivial R]
    {x y : Localization (qsMonicSubmonoid R)}
    (hx : qsPolynomialPart R x = 0)
    (hy : qsPolynomialPart R y = 0) :
    qsPolynomialPart R (x * y) = 0 := by
  induction x using Localization.induction_on with
  | _ x =>
    rcases x with ⟨a, b⟩
    induction y using Localization.induction_on with
    | _ y =>
      rcases y with ⟨c, d⟩
      change a /ₘ (b : Polynomial R) = 0 at hx
      change c /ₘ (d : Polynomial R) = 0 at hy
      rw [Localization.mk_mul]
      change (a * c) /ₘ ((b : Polynomial R) * d) = 0
      rw [Polynomial.divByMonic_eq_zero_iff (b.property.mul d.property)]
      by_cases ha : a = 0
      · rw [ha, zero_mul, Polynomial.degree_zero, bot_lt_iff_ne_bot,
          Ne, Polynomial.degree_eq_bot]
        exact (b.property.mul d.property).ne_zero
      by_cases hc : c = 0
      · rw [hc, mul_zero, Polynomial.degree_zero, bot_lt_iff_ne_bot,
          Ne, Polynomial.degree_eq_bot]
        exact (b.property.mul d.property).ne_zero
      exact (Polynomial.degree_mul_le a c).trans_lt <|
        (WithBot.add_lt_add_of_lt_of_le (Polynomial.degree_ne_bot.mpr hc)
          ((Polynomial.divByMonic_eq_zero_iff b.property).mp hx)
          ((Polynomial.divByMonic_eq_zero_iff d.property).mp hy).le).trans_le
            d.property.degree_mul.ge

private theorem qs_isUnit_one_add_of_polynomialPart_eq_zero
    {R : Type*} [CommRing R] [Nontrivial R]
    (z : Localization (qsMonicSubmonoid R))
    (hz : qsPolynomialPart R z = 0) : IsUnit (1 + z) := by
  induction z using Localization.induction_on with
  | _ z =>
    rcases z with ⟨a, b⟩
    change a /ₘ (b : Polynomial R) = 0 at hz
    have hdeg : a.degree < (b : Polynomial R).degree :=
      (Polynomial.divByMonic_eq_zero_iff b.property).mp hz
    let s : qsMonicSubmonoid R :=
      ⟨(b : Polynomial R) + a, b.property.add_of_left hdeg⟩
    refine isUnit_iff_exists_inv.mpr
      ⟨Localization.mk (b : Polynomial R) s, ?_⟩
    calc
      (1 + Localization.mk a b) * Localization.mk (b : Polynomial R) s =
          (Localization.mk (b : Polynomial R) b + Localization.mk a b) *
            Localization.mk (b : Polynomial R) s := by
        rw [Localization.mk_self]
      _ = Localization.mk ((b : Polynomial R) + a) b *
            Localization.mk (b : Polynomial R) s := by
        rw [Localization.add_mk_self]
      _ = Localization.mk (((b : Polynomial R) + a) * b) (b * s) := by
        rw [Localization.mk_mul]
      _ = Localization.mk (↑(b * s) : Polynomial R) (b * s) := by
        congr 1
        simp only [Submonoid.coe_mul]
        change ((b : Polynomial R) + a) * b =
          (b : Polynomial R) * ((b : Polynomial R) + a)
        exact mul_comm _ _
      _ = 1 := Localization.mk_self (b * s)

private theorem qsPolynomialPart_C_mul
    {R : Type*} [CommRing R] [Nontrivial R]
    (r : R) (z : Localization (qsMonicSubmonoid R)) :
    qsPolynomialPart R
        (algebraMap (Polynomial R) (Localization (qsMonicSubmonoid R))
          (Polynomial.C r) * z) =
      r • qsPolynomialPart R z := by
  change qsPolynomialPart R (algebraMap R
    (Localization (qsMonicSubmonoid R)) r * z) = _
  rw [← Algebra.smul_def, map_smul]

private theorem qsPolynomialPart_mul_of_constant_parts
    {R : Type*} [CommRing R] [Nontrivial R]
    {x y : Localization (qsMonicSubmonoid R)} {r s : R}
    (hx : qsPolynomialPart R x = Polynomial.C r)
    (hy : qsPolynomialPart R y = Polynomial.C s) :
    qsPolynomialPart R (x * y) = Polynomial.C (r * s) := by
  let alg : Polynomial R →+* Localization (qsMonicSubmonoid R) :=
    algebraMap (Polynomial R) (Localization (qsMonicSubmonoid R))
  let x₀ := x - alg (Polynomial.C r)
  let y₀ := y - alg (Polynomial.C s)
  have halg (p : Polynomial R) : qsPolynomialPart R (alg p) = p := by
    exact qsPolynomialPart_algebraMap p
  have hx₀ : qsPolynomialPart R x₀ = 0 := by
    rw [show qsPolynomialPart R x₀ = qsPolynomialPart R x -
        qsPolynomialPart R (alg (Polynomial.C r)) by simp [x₀], hx, halg,
      sub_self]
  have hy₀ : qsPolynomialPart R y₀ = 0 := by
    rw [show qsPolynomialPart R y₀ = qsPolynomialPart R y -
        qsPolynomialPart R (alg (Polynomial.C s)) by simp [y₀], hy, halg,
      sub_self]
  have hxy₀ : qsPolynomialPart R (x₀ * y₀) = 0 :=
    qsPolynomialPart_mul_eq_zero hx₀ hy₀
  have hxsplit : alg (Polynomial.C r) + x₀ = x := by
    dsimp only [x₀]
    abel
  have hysplit : alg (Polynomial.C s) + y₀ = y := by
    dsimp only [y₀]
    abel
  calc
    qsPolynomialPart R (x * y) = qsPolynomialPart R
        ((alg (Polynomial.C r) + x₀) * (alg (Polynomial.C s) + y₀)) := by
      rw [hxsplit, hysplit]
    _ = qsPolynomialPart R
        (alg (Polynomial.C r) * alg (Polynomial.C s) +
          alg (Polynomial.C r) * y₀ + x₀ * alg (Polynomial.C s) + x₀ * y₀) := by
      congr 1
      ring
    _ = Polynomial.C (r * s) + r • qsPolynomialPart R y₀ +
        s • qsPolynomialPart R x₀ + qsPolynomialPart R (x₀ * y₀) := by
      simp only [map_add]
      rw [← map_mul, ← Polynomial.C_mul, qsPolynomialPart_algebraMap,
        qsPolynomialPart_C_mul, mul_comm x₀, qsPolynomialPart_C_mul]
    _ = Polynomial.C (r * s) := by rw [hx₀, hy₀, hxy₀]; simp

private theorem qsPolynomialPart_prod_of_constant_parts
    {R : Type*} [CommRing R] [Nontrivial R]
    {α : Type*} (t : Finset α)
    (f : α → Localization (qsMonicSubmonoid R)) (g : α → R)
    (h : ∀ i ∈ t, qsPolynomialPart R (f i) = Polynomial.C (g i)) :
    qsPolynomialPart R (∏ i ∈ t, f i) = Polynomial.C (∏ i ∈ t, g i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simpa using qsPolynomialPart_algebraMap (R := R) (1 : Polynomial R)
  | @insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      apply qsPolynomialPart_mul_of_constant_parts
      · exact h a (Finset.mem_insert_self a t)
      · exact ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)

private theorem qsPolynomialPart_det_of_constant_parts
    {R : Type*} [CommRing R] [Nontrivial R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι (Localization (qsMonicSubmonoid R)))
    (M : Matrix ι ι R)
    (h : ∀ i j, qsPolynomialPart R (H i j) = Polynomial.C (M i j)) :
    qsPolynomialPart R H.det = Polynomial.C M.det := by
  rw [Matrix.det_apply, map_sum, Matrix.det_apply,
    map_sum (Polynomial.C : R →+* Polynomial R)]
  apply Finset.sum_congr rfl
  intro σ _
  have hprod : qsPolynomialPart R (∏ i, H (σ i) i) =
      Polynomial.C (∏ i, M (σ i) i) :=
    qsPolynomialPart_prod_of_constant_parts Finset.univ
      (fun i ↦ H (σ i) i) (fun i ↦ M (σ i) i) fun i _ ↦ h _ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul, one_smul, hprod]
  · rw [hs, Units.neg_smul, one_smul, Units.neg_smul, one_smul,
      map_neg, hprod, map_neg]

private theorem qs_isUnit_det_of_matrixPolynomialPart_eq_one
    {R : Type*} [CommRing R] [Nontrivial R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι (Localization (qsMonicSubmonoid R)))
    (hH : ∀ i j, qsPolynomialPart R (H i j) =
      (1 : Matrix ι ι (Polynomial R)) i j) : IsUnit H.det := by
  have hentry : ∀ i j, qsPolynomialPart R (H i j) =
      Polynomial.C ((1 : Matrix ι ι R) i j) := by
    intro i j
    by_cases hij : i = j
    · subst j
      simpa using hH i i
    · simpa [Matrix.one_apply, hij] using hH i j
  have hdet : qsPolynomialPart R H.det = 1 := by
    calc
      qsPolynomialPart R H.det = Polynomial.C (1 : Matrix ι ι R).det :=
        qsPolynomialPart_det_of_constant_parts H 1 hentry
      _ = 1 := by rw [Matrix.det_one, map_one]
  have hproper : qsPolynomialPart R (H.det - 1) = 0 := by
    have hone : qsPolynomialPart R
        (1 : Localization (qsMonicSubmonoid R)) = 1 := by
      simpa using qsPolynomialPart_algebraMap (R := R) (1 : Polynomial R)
    rw [map_sub, hdet, hone, sub_self]
  have hu := qs_isUnit_one_add_of_polynomialPart_eq_zero (H.det - 1) hproper
  have heq : 1 + (H.det - 1) = H.det := by ring
  rw [heq] at hu
  exact hu

private def qsHorrocksMap
    (R : Type*) [CommRing R] [Nontrivial R]
    {ι κ : Type*} [Fintype ι]
    (A : Matrix ι κ (Localization (qsMonicSubmonoid R))) :
    Matrix κ ι (Polynomial R) →ₗ[R] Matrix κ κ (Polynomial R) :=
  (qsMatrixPolynomialPart R).comp <|
    (mulRightLinearMap κ R A).comp <|
      LinearMap.mapMatrix
        (IsScalarTower.toAlgHom R (Polynomial R)
          (Localization (qsMonicSubmonoid R))).toLinearMap

private theorem qsHorrocksMap_apply
    (R : Type*) [CommRing R] [Nontrivial R]
    {ι κ : Type*} [Fintype ι]
    (A : Matrix ι κ (Localization (qsMonicSubmonoid R)))
    (F : Matrix κ ι (Polynomial R)) :
    qsHorrocksMap R A F = qsMatrixPolynomialPart R
      (F.map (algebraMap (Polynomial R)
        (Localization (qsMonicSubmonoid R))) * A) :=
  rfl

private theorem qs_exists_monic_matrix_multiple
    (R : Type*) [CommRing R] [Nontrivial R]
    {ι κ : Type*} [Finite ι] [Finite κ]
    (B : Matrix ι κ (Localization (qsMonicSubmonoid R))) :
    ∃ h : Polynomial R, h.Monic ∧
      ∃ B₀ : Matrix ι κ (Polynomial R),
        B₀.map (algebraMap (Polynomial R)
          (Localization (qsMonicSubmonoid R))) =
          (algebraMap (Polynomial R)
            (Localization (qsMonicSubmonoid R)) h) • B := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : Fintype κ := Fintype.ofFinite κ
  let f : ι × κ → Localization (qsMonicSubmonoid R) :=
    fun z ↦ B z.1 z.2
  obtain ⟨h, hh⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (qsMonicSubmonoid R) f
  choose b₀ hb₀ using hh
  refine ⟨h, h.property, fun i j ↦ b₀ (i, j), ?_⟩
  apply Matrix.ext
  intro i j
  have hij := hb₀ (i, j)
  rw [Algebra.smul_def] at hij
  exact hij

private theorem qs_horrocks_multiple_mem_range
    (R : Type*) [CommRing R] [Nontrivial R]
    {ι κ : Type*} [Fintype ι] [Finite κ] [DecidableEq κ]
    (A : Matrix ι κ (Localization (qsMonicSubmonoid R)))
    (B : Matrix κ ι (Localization (qsMonicSubmonoid R)))
    (hBA : B * A = 1)
    (h : Polynomial R) (B₀ : Matrix κ ι (Polynomial R))
    (hB₀ : B₀.map (algebraMap (Polynomial R)
      (Localization (qsMonicSubmonoid R))) =
      (algebraMap (Polynomial R)
        (Localization (qsMonicSubmonoid R)) h) • B)
    (G : Matrix κ κ (Polynomial R)) :
    h • G ∈ LinearMap.range (qsHorrocksMap R A) := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let Q := Localization (qsMonicSubmonoid R)
  let alg : Polynomial R →+* Q := algebraMap (Polynomial R) Q
  refine ⟨G * B₀, ?_⟩
  rw [qsHorrocksMap_apply]
  have hsmul : (h • G).map alg = (alg h) • G.map alg := by
    apply Matrix.ext
    intro i j
    change alg (h * G i j) = alg h * alg (G i j)
    exact map_mul alg h (G i j)
  calc
    qsMatrixPolynomialPart R ((G * B₀).map alg * A) =
        qsMatrixPolynomialPart R ((G.map alg * B₀.map alg) * A) := by
      rw [Matrix.map_mul]
    _ = qsMatrixPolynomialPart R
        ((G.map alg * ((alg h) • B)) * A) := by rw [hB₀]
    _ = qsMatrixPolynomialPart R
        ((alg h) • (G.map alg * (B * A))) := by
      congr 1
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = qsMatrixPolynomialPart R ((alg h) • G.map alg) := by
      rw [hBA, Matrix.mul_one]
    _ = qsMatrixPolynomialPart R ((h • G).map alg) := by rw [hsmul]
    _ = h • G := qsMatrixPolynomialPart_algebraMap (h • G)

private theorem qs_matrix_mem_maximal_smul_of_map_eq_zero
    (R : Type*) [CommRing R] [IsLocalRing R]
    {ι κ : Type*} [Finite ι] [Finite κ]
    (P : Matrix ι κ (Polynomial R))
    (hP : P.map (Polynomial.mapRingHom (IsLocalRing.residue R)) = 0) :
    P ∈ IsLocalRing.maximalIdeal R •
      (⊤ : Submodule R (Matrix ι κ (Polynomial R))) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : Fintype κ := Fintype.ofFinite κ
  rw [Matrix.matrix_eq_sum_single P]
  refine Submodule.sum_mem _ fun i _ ↦ Submodule.sum_mem _ fun j _ ↦ ?_
  have hij := congrFun (congrFun hP i) j
  change (P i j).map (IsLocalRing.residue R) = 0 at hij
  have hp : P i j ∈ IsLocalRing.maximalIdeal R •
      (⊤ : Submodule R (Polynomial R)) := by
    rw [Ideal.smul_top_eq_map]
    change P i j ∈ (IsLocalRing.maximalIdeal R).map Polynomial.C
    rw [← IsLocalRing.ker_residue,
      ← Polynomial.ker_mapRingHom, RingHom.mem_ker]
    exact hij
  let f : Polynomial R →ₗ[R] Matrix ι κ (Polynomial R) :=
    Matrix.singleLinearMap R i j
  have hmap : Matrix.single i j (P i j) ∈
      Submodule.map f (IsLocalRing.maximalIdeal R •
        (⊤ : Submodule R (Polynomial R))) := ⟨P i j, hp, rfl⟩
  rw [Submodule.map_smul''] at hmap
  exact (Submodule.smul_mono le_rfl le_top) hmap

private def qsMatrixRemainder
    (R : Type*) [CommRing R] [Nontrivial R]
    {ι κ : Type*} (h : Polynomial R) (hh : h.Monic) :
    Matrix ι κ (Polynomial R) →ₗ[R]
      Matrix ι κ (Polynomial.degreeLT R h.natDegree) :=
  LinearMap.mapMatrix <|
    (Polynomial.modByMonicHom h).codRestrict
      (Polynomial.degreeLT R h.natDegree) fun p ↦ by
        rw [Polynomial.mem_degreeLT]
        simpa [Polynomial.degree_eq_natDegree hh.ne_zero] using
          Polynomial.degree_modByMonic_lt p hh

private theorem qs_quotient_finite_of_monic_smul_mem
    (R : Type*) [CommRing R] [Nontrivial R]
    {κ : Type*} [Finite κ]
    (N : Submodule R (Matrix κ κ (Polynomial R)))
    (h : Polynomial R) (hh : h.Monic)
    (hN : ∀ G : Matrix κ κ (Polynomial R), h • G ∈ N) :
    Module.Finite R (Matrix κ κ (Polynomial R) ⧸ N) := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let rem := qsMatrixRemainder R (ι := κ) (κ := κ) h hh
  let inc : Matrix κ κ (Polynomial.degreeLT R h.natDegree) →ₗ[R]
      Matrix κ κ (Polynomial R) :=
    LinearMap.mapMatrix (Polynomial.degreeLT R h.natDegree).subtype
  let f := N.mkQ.comp inc
  apply Module.Finite.of_surjective f
  intro z
  obtain ⟨G, rfl⟩ := N.mkQ_surjective z
  let D : Matrix κ κ (Polynomial R) := fun i j ↦ G i j /ₘ h
  refine ⟨rem G, ?_⟩
  change N.mkQ (inc (rem G)) = N.mkQ G
  rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  change inc (rem G) - G ∈ N
  have hdecomp : inc (rem G) + h • D = G := by
    apply Matrix.ext
    intro i j
    exact Polynomial.modByMonic_add_div (G i j) h
  have hdiff : inc (rem G) - G = -(h • D) := by
    calc
      inc (rem G) - G =
          inc (rem G) - (inc (rem G) + h • D) :=
        congrArg (fun X ↦ inc (rem G) - X) hdecomp.symm
      _ = -(h • D) := by abel
  rw [hdiff]
  exact N.neg_mem (hN D)

private theorem qs_horrocks_range_sup_maximal_eq_top
    (R : Type*) [CommRing R] [IsLocalRing R]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ (Localization (qsMonicSubmonoid R)))
    (B : Matrix κ ι (Localization (qsMonicSubmonoid R)))
    (hBA : B * A = 1)
    (hA : ∃ C : Matrix ι κ (Polynomial (IsLocalRing.ResidueField R)),
      A.map (qsResidueMonicMap R) =
        C.map (algebraMap (Polynomial (IsLocalRing.ResidueField R))
          (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R)))))
    (hB : ∃ D : Matrix κ ι (Polynomial (IsLocalRing.ResidueField R)),
      B.map (qsResidueMonicMap R) =
        D.map (algebraMap (Polynomial (IsLocalRing.ResidueField R))
          (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R))))) :
    LinearMap.range (qsHorrocksMap R A) ⊔
        IsLocalRing.maximalIdeal R •
          (⊤ : Submodule R (Matrix κ κ (Polynomial R))) = ⊤ := by
  classical
  let k := IsLocalRing.ResidueField R
  let Q := Localization (qsMonicSubmonoid R)
  let K := Localization (qsMonicSubmonoid k)
  let alg : Polynomial R →+* Q := algebraMap (Polynomial R) Q
  let ak : Polynomial k →+* K := algebraMap (Polynomial k) K
  let q : Q →+* K := qsResidueMonicMap R
  let bar : Polynomial R →+* Polynomial k :=
    Polynomial.mapRingHom (IsLocalRing.residue R)
  obtain ⟨C, hAC⟩ := hA
  obtain ⟨D, hBD⟩ := hB
  have hDC : D.map ak * C.map ak = 1 := by
    calc
      D.map ak * C.map ak = B.map q * A.map q := by rw [hAC, hBD]
      _ = (B * A).map q := (Matrix.map_mul ..).symm
      _ = (1 : Matrix κ κ Q).map q := by rw [hBA]
      _ = 1 := Matrix.map_one q q.map_zero q.map_one
  apply top_unique
  intro G _
  have hGcompat : (G.map alg).map q = (G.map bar).map ak := by
    apply Matrix.ext
    intro i j
    exact qsResidueMonicMap_algebraMap R (G i j)
  have hGB : (G.map alg * B).map q = (G.map bar * D).map ak := by
    calc
      (G.map alg * B).map q = (G.map alg).map q * B.map q := Matrix.map_mul ..
      _ = (G.map bar).map ak * D.map ak := by rw [hGcompat, hBD]
      _ = (G.map bar * D).map ak := (Matrix.map_mul ..).symm
  let F := qsMatrixPolynomialPart R (G.map alg * B)
  have hFbar : F.map bar = G.map bar * D :=
    qsMatrixPolynomialPart_map_residue R (G.map alg * B) (G.map bar * D) hGB
  have hFcompat : (F.map alg).map q = (F.map bar).map ak := by
    apply Matrix.ext
    intro i j
    exact qsResidueMonicMap_algebraMap R (F i j)
  have hFA : (F.map alg * A).map q = (G.map bar).map ak := by
    calc
      (F.map alg * A).map q = (F.map alg).map q * A.map q := Matrix.map_mul ..
      _ = (F.map bar).map ak * C.map ak := by rw [hFcompat, hAC]
      _ = (G.map bar * D).map ak * C.map ak := by rw [hFbar]
      _ = (G.map bar).map ak * (D.map ak * C.map ak) := by
        rw [Matrix.map_mul, Matrix.mul_assoc]
      _ = (G.map bar).map ak := by rw [hDC, Matrix.mul_one]
  have hTbar : (qsHorrocksMap R A F).map bar = G.map bar := by
    rw [qsHorrocksMap_apply]
    exact qsMatrixPolynomialPart_map_residue R
      (F.map alg * A) (G.map bar) hFA
  have hdiff : G - qsHorrocksMap R A F ∈
      IsLocalRing.maximalIdeal R •
        (⊤ : Submodule R (Matrix κ κ (Polynomial R))) := by
    apply qs_matrix_mem_maximal_smul_of_map_eq_zero R
    rw [Matrix.map_sub bar (map_sub bar), hTbar, sub_self]
  have hrange : qsHorrocksMap R A F ∈
      LinearMap.range (qsHorrocksMap R A) := ⟨F, rfl⟩
  have hsum : qsHorrocksMap R A F +
      (G - qsHorrocksMap R A F) = G := by abel
  rw [← hsum]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hrange)
    (Submodule.mem_sup_right hdiff)

private theorem qs_horrocks_map_surjective
    (R : Type*) [CommRing R] [IsLocalRing R]
    {ι κ : Type*} [Fintype ι] [Finite κ] [DecidableEq κ]
    (A : Matrix ι κ (Localization (qsMonicSubmonoid R)))
    (B : Matrix κ ι (Localization (qsMonicSubmonoid R)))
    (hBA : B * A = 1)
    (hA : ∃ C : Matrix ι κ (Polynomial (IsLocalRing.ResidueField R)),
      A.map (qsResidueMonicMap R) =
        C.map (algebraMap (Polynomial (IsLocalRing.ResidueField R))
          (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R)))))
    (hB : ∃ D : Matrix κ ι (Polynomial (IsLocalRing.ResidueField R)),
      B.map (qsResidueMonicMap R) =
        D.map (algebraMap (Polynomial (IsLocalRing.ResidueField R))
          (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R))))) :
    Function.Surjective (qsHorrocksMap R A) := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let W := Matrix κ κ (Polynomial R)
  let T := qsHorrocksMap R A
  let N : Submodule R W := LinearMap.range T
  obtain ⟨h, hh, B₀, hB₀⟩ := qs_exists_monic_matrix_multiple R B
  have hmultiple : ∀ G : W, h • G ∈ N := fun G ↦
    qs_horrocks_multiple_mem_range R A B hBA h B₀ hB₀ G
  let _ : Module.Finite R (W ⧸ N) :=
    qs_quotient_finite_of_monic_smul_mem R N h hh hmultiple
  have hsup : N ⊔ IsLocalRing.maximalIdeal R •
      (⊤ : Submodule R W) = ⊤ :=
    qs_horrocks_range_sup_maximal_eq_top R A B hBA hA hB
  have hmaptop : Submodule.map N.mkQ
      (IsLocalRing.maximalIdeal R • (⊤ : Submodule R W)) = ⊤ :=
    (Submodule.map_mkQ_eq_top N _).mpr hsup
  rw [Submodule.map_smul'', Submodule.map_top, N.range_mkQ] at hmaptop
  have hquot : (⊤ : Submodule R (W ⧸ N)) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
      (IsLocalRing.maximalIdeal R) ⊤ Module.Finite.fg_top
      (by rw [hmaptop]) (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  apply LinearMap.range_eq_top.mp
  apply top_unique
  intro G _
  have hz : N.mkQ G = 0 := by
    have : N.mkQ G ∈ (⊥ : Submodule R (W ⧸ N)) := by
      rw [← hquot]
      exact Submodule.mem_top
    exact this
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz
  exact hz

private theorem qs_lift_invertible_matrix
    {A K : Type*} [CommRing A] [Field K]
    (f : A →+* K)
    (hlift : ∀ x : K, x ≠ 0 → ∃ u : Aˣ, f u = x)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (hM : M.det ≠ 0) :
    ∃ U : Matrix ι ι A, IsUnit U.det ∧ U.map f = M := by
  classical
  apply Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun N ↦ ∃ U : Matrix ι ι A, IsUnit U.det ∧ U.map f = N) M hM
  · intro D hD
    have hDi : ∀ i, D i ≠ 0 := by
      intro i hi
      apply hD
      rw [Matrix.det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    choose u hu using fun i ↦ hlift (D i) (hDi i)
    refine ⟨Matrix.diagonal (fun i ↦ (u i : A)), ?_, ?_⟩
    · rw [Matrix.det_diagonal]
      exact IsUnit.prod_univ_iff.mpr fun i ↦ (u i).isUnit
    · ext i j
      by_cases hij : i = j
      · subst j
        simpa using hu i
      · simp [Matrix.diagonal, hij]
  · intro t
    obtain ⟨c, hc⟩ : ∃ c : A, f c = t.c := by
      by_cases hc0 : t.c = 0
      · exact ⟨0, by simp [hc0]⟩
      · obtain ⟨u, hu⟩ := hlift t.c hc0
        exact ⟨u, hu⟩
    refine ⟨Matrix.transvection t.i t.j c, ?_, ?_⟩
    · rw [Matrix.det_transvection_of_ne _ _ t.hij]
      exact isUnit_one
    · change (1 + Matrix.single t.i t.j c).map f =
        1 + Matrix.single t.i t.j t.c
      rw [Matrix.map_add f f.map_add, Matrix.map_one f f.map_zero f.map_one,
        Matrix.map_single t.i t.j c f, hc]
  · rintro X Y _hX _hY ⟨X', hXunit, hXmap⟩ ⟨Y', hYunit, hYmap⟩
    refine ⟨X' * Y', ?_, ?_⟩
    · rw [Matrix.det_mul]
      exact hXunit.mul hYunit
    · rw [Matrix.map_mul, hXmap, hYmap]

private theorem qsResidueMonicMap_lifts_unit
    (R : Type*) [CommRing R] [IsLocalRing R]
    (z : Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R)))
    (hz : z ≠ 0) :
    ∃ u : (Localization (qsMonicSubmonoid R))ˣ,
      qsResidueMonicMap R u = z := by
  classical
  let k := IsLocalRing.ResidueField R
  let K := Localization (qsMonicSubmonoid k)
  let Q := Localization (qsMonicSubmonoid R)
  let _ : IsFractionRing (Polynomial k) K :=
    qs_monicLocalization_isFractionRing k
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (qsMonicSubmonoid k) z
  have hb0 : algebraMap (Polynomial k) K (b : Polynomial k) ≠ 0 := by
    intro hb
    exact b.property.ne_zero ((IsFractionRing.injective (Polynomial k) K) (by simpa using hb))
  have ha0 : a ≠ 0 := by
    intro ha
    rw [ha, map_zero] at hab
    exact hz ((mul_eq_zero.mp hab).resolve_right hb0)
  let a' := a * Polynomial.C a.leadingCoeff⁻¹
  have ha'monic : a'.Monic := Polynomial.monic_mul_leadingCoeff_inv ha0
  obtain ⟨pa, hpamonic, hpamap⟩ :=
    qs_exists_monic_lift (IsLocalRing.residue R)
      IsLocalRing.residue_surjective ha'monic
  obtain ⟨pb, hpbmonic, hpbmap⟩ :=
    qs_exists_monic_lift (IsLocalRing.residue R)
      IsLocalRing.residue_surjective b.property
  obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective a.leadingCoeff
  have hlc0 : a.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr ha0
  have hrunit : IsUnit r :=
    (IsLocalRing.residue_ne_zero_iff_isUnit r).mp (by simpa [hr] using hlc0)
  have hscalar : IsUnit (algebraMap (Polynomial R) Q (Polynomial.C r)) :=
    (Polynomial.isUnit_C.mpr hrunit).map (algebraMap (Polynomial R) Q)
  have hpaunit : IsUnit (algebraMap (Polynomial R) Q pa) :=
    IsLocalization.map_units Q (⟨pa, hpamonic⟩ : qsMonicSubmonoid R)
  have hpbunit : IsUnit (algebraMap (Polynomial R) Q pb) :=
    IsLocalization.map_units Q (⟨pb, hpbmonic⟩ : qsMonicSubmonoid R)
  let u : Qˣ := hscalar.unit * hpaunit.unit * hpbunit.unit⁻¹
  refine ⟨u, ?_⟩
  have hscalarMap : qsResidueMonicMap R
      (algebraMap (Polynomial R) Q (Polynomial.C r)) =
      algebraMap (Polynomial k) K (Polynomial.C a.leadingCoeff) := by
    rw [qsResidueMonicMap_algebraMap, Polynomial.map_C, hr]
  have hpaMap : qsResidueMonicMap R
      (algebraMap (Polynomial R) Q pa) = algebraMap (Polynomial k) K a' := by
    rw [qsResidueMonicMap_algebraMap, hpamap]
  have hpbMap : qsResidueMonicMap R
      (algebraMap (Polynomial R) Q pb) =
      algebraMap (Polynomial k) K (b : Polynomial k) := by
    rw [qsResidueMonicMap_algebraMap, hpbmap]
  have hnormalize : Polynomial.C a.leadingCoeff * a' = a := by
    dsimp only [a']
    calc
      Polynomial.C a.leadingCoeff *
          (a * Polynomial.C a.leadingCoeff⁻¹) =
          a * (Polynomial.C a.leadingCoeff *
            Polynomial.C a.leadingCoeff⁻¹) := by ring
      _ = a := by rw [← Polynomial.C_mul, mul_inv_cancel₀ hlc0]; simp
  apply mul_right_cancel₀ hb0
  change qsResidueMonicMap R (↑u : Q) *
      algebraMap (Polynomial k) K (b : Polynomial k) =
    z * algebraMap (Polynomial k) K (b : Polynomial k)
  rw [hab]
  simp only [u, Units.val_mul, map_mul]
  rw [hscalar.unit_spec, hpaunit.unit_spec]
  rw [hscalarMap, hpaMap]
  have hnormalizeMap :
      algebraMap (Polynomial k) K (Polynomial.C a.leadingCoeff) *
        algebraMap (Polynomial k) K a' = algebraMap (Polynomial k) K a := by
    rw [← map_mul, hnormalize]
  rw [← hnormalizeMap]
  have hpbcoe : (↑hpbunit.unit : Q) = algebraMap (Polynomial R) Q pb :=
    hpbunit.unit_spec
  have hpbMap' : qsResidueMonicMap R (↑hpbunit.unit : Q) =
      algebraMap (Polynomial k) K (b : Polynomial k) := by
    rw [hpbcoe, hpbMap]
  rw [← hpbMap']
  have hcancel :
      qsResidueMonicMap R (↑(hpbunit.unit⁻¹) : Q) *
        qsResidueMonicMap R (↑hpbunit.unit : Q) = 1 := by
    rw [← map_mul]
    simp
  calc
    _ = algebraMap (Polynomial k) K (Polynomial.C a.leadingCoeff) *
        algebraMap (Polynomial k) K a' *
          (qsResidueMonicMap R (↑(hpbunit.unit⁻¹) : Q) *
            qsResidueMonicMap R (↑hpbunit.unit : Q)) := by ring
    _ = _ := by rw [hcancel, mul_one]

private theorem qs_lift_residue_invertible_matrix
    (R : Type*) [CommRing R] [IsLocalRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι
      (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R))))
    (hM : M.det ≠ 0) :
    ∃ U : Matrix ι ι (Localization (qsMonicSubmonoid R)),
      IsUnit U.det ∧ U.map (qsResidueMonicMap R) = M := by
  let _ : IsFractionRing (Polynomial (IsLocalRing.ResidueField R))
      (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R))) :=
    qs_monicLocalization_isFractionRing (IsLocalRing.ResidueField R)
  let _ : Field (Localization
      (qsMonicSubmonoid (IsLocalRing.ResidueField R))) :=
    IsFractionRing.toField (Polynomial (IsLocalRing.ResidueField R))
  exact qs_lift_invertible_matrix (qsResidueMonicMap R)
    (qsResidueMonicMap_lifts_unit R) M hM

private theorem qsMatrixEquiv.refl
    {R : Type*} [CommRing R]
    {i : Type*} [Fintype i]
    {E : Matrix i i R} (hE : E * E = E) : qsMatrixEquiv E E :=
  ⟨E, E, hE, hE⟩

private theorem qsShear_zero {R : Type*} [CommRing R] :
    qsShear (0 : R) =
      (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R)) := by
  apply Polynomial.ringHom_ext
  · intro r
    simp [qsShear]
  · simp [qsShear]

private theorem qsShiftX_comp_shear
    {R : Type*} [CommRing R] (j j' : R) :
    (qsShiftX j').comp (qsShear j) = qsShear (j + j') := by
  apply Polynomial.ringHom_ext
  · intro r
    simp [qsShiftX, qsShear]
  · simp [qsShiftX, qsShear]
    ring

private theorem qsShiftX_comp_C
    {R : Type*} [CommRing R] (j : R) :
    (qsShiftX j).comp
        (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R)) =
      qsShear j := by
  apply Polynomial.ringHom_ext
  · intro r
    simp [qsShiftX, qsShear]
  · simp [qsShiftX, qsShear]

private theorem qsScaleY_comp_shear
    {R : Type*} [CommRing R] (r j : R) :
    (qsScaleY r).comp (qsShear j) = qsShear (r * j) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [qsScaleY, qsShear]
  · simp [qsScaleY, qsShear]
    ring

private theorem qsScaleY_comp_C
    {R : Type*} [CommRing R] (r : R) :
    (qsScaleY r).comp
        (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R)) =
      (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R)) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [qsScaleY]
  · simp [qsScaleY]

private theorem qs_scale_shear_map
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (r : R) :
    (qsScaleY (f r)).comp
        ((qsShear (1 : S)).comp (Polynomial.mapRingHom f)) =
      (Polynomial.mapRingHom (Polynomial.mapRingHom f)).comp (qsShear r) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [qsScaleY, qsShear]
  · simp [qsScaleY, qsShear]

private theorem qsEvalXY_comp_shear_one
    {R : Type*} [CommRing R] :
    (qsEvalXY : Polynomial (Polynomial R) →+* Polynomial R).comp
        (qsShear (1 : R)) = RingHom.id (Polynomial R) := by
  apply Polynomial.ringHom_ext
  · intro r
    simp [qsEvalXY, qsConstantAtZero, qsShear]
  · simp [qsEvalXY, qsConstantAtZero, qsShear]

private theorem qsEvalXY_comp_C
    {R : Type*} [CommRing R] :
    (qsEvalXY : Polynomial (Polynomial R) →+* Polynomial R).comp
        Polynomial.C = qsConstantAtZero := by
  apply Polynomial.ringHom_ext
  · intro r
    simp [qsEvalXY, qsConstantAtZero]
  · simp [qsEvalXY, qsConstantAtZero]

private theorem qsMatrixEquiv.symm
    {R : Type*} [CommRing R]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {E : Matrix ι ι R} {F : Matrix κ κ R}
    (h : qsMatrixEquiv E F) : qsMatrixEquiv F E := by
  obtain ⟨A, B, hAB, hBA⟩ := h
  exact ⟨B, A, hBA, hAB⟩

private theorem qsMatrixEquiv.reindex_one
    {R : Type*} [CommRing R]
    {ι κ η : Type*} [Fintype ι] [Fintype κ] [Fintype η]
    [DecidableEq κ] [DecidableEq η]
    {E : Matrix ι ι R}
    (h : qsMatrixEquiv E (1 : Matrix κ κ R)) (e : η ≃ κ) :
    qsMatrixEquiv E (1 : Matrix η η R) := by
  classical
  obtain ⟨A, B, hAB, hBA⟩ := h
  refine ⟨A.submatrix (Equiv.refl ι) e,
    B.submatrix e (Equiv.refl ι), ?_, ?_⟩
  · rw [Matrix.submatrix_mul_equiv]
    simp [hAB]
  · rw [Matrix.submatrix_mul_equiv]
    rw [hBA]
    exact Matrix.submatrix_one_equiv e

private theorem qsMatrixEquiv.map
    {R S : Type*} [CommRing R] [CommRing S]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {E : Matrix ι ι R} {F : Matrix κ κ R}
    (h : qsMatrixEquiv E F) (f : R →+* S) :
    qsMatrixEquiv (E.map f) (F.map f) := by
  obtain ⟨A, B, hAB, hBA⟩ := h
  refine ⟨A.map f, B.map f, ?_, ?_⟩
  · simpa only [Matrix.map_mul] using congrArg (fun M ↦ M.map f) hAB
  · simpa only [Matrix.map_mul] using congrArg (fun M ↦ M.map f) hBA

private theorem qs_transition_one_of_equal_after
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    {i k : Type*} [Fintype i] [Fintype k] [DecidableEq k]
    {E : Matrix i i R}
    (h : qsMatrixEquiv E (1 : Matrix k k R))
    (g₁ g₂ : R →+* S) (e : S →+* T)
    (he : e.comp g₁ = e.comp g₂) :
    ∃ C D : Matrix i i S,
      C * D = E.map g₁ ∧ D * C = E.map g₂ ∧
      C.map e = E.map (e.comp g₁) ∧
      D.map e = E.map (e.comp g₁) := by
  obtain ⟨A, B, hAB, hBA⟩ := h
  let C := A.map g₁ * B.map g₂
  let D := A.map g₂ * B.map g₁
  refine ⟨C, D, ?_, ?_, ?_, ?_⟩
  · calc
      C * D = A.map g₁ * (B.map g₂ * A.map g₂) * B.map g₁ := by
        simp only [C, D, Matrix.mul_assoc]
      _ = A.map g₁ * (B * A).map g₂ * B.map g₁ := by rw [Matrix.map_mul]
      _ = A.map g₁ * B.map g₁ := by rw [hBA]; simp
      _ = E.map g₁ := by rw [← Matrix.map_mul, hAB]
  · calc
      D * C = A.map g₂ * (B.map g₁ * A.map g₁) * B.map g₂ := by
        simp only [C, D, Matrix.mul_assoc]
      _ = A.map g₂ * (B * A).map g₁ * B.map g₂ := by rw [Matrix.map_mul]
      _ = A.map g₂ * B.map g₂ := by rw [hBA]; simp
      _ = E.map g₂ := by rw [← Matrix.map_mul, hAB]
  · simp only [C, Matrix.map_mul, Matrix.map_map]
    change
      (A.map ((e.comp g₁)) * B.map ((e.comp g₂))) = E.map (e.comp g₁)
    rw [← he, ← Matrix.map_mul, hAB]
  · simp only [D, Matrix.map_mul, Matrix.map_map]
    change
      (A.map ((e.comp g₂)) * B.map ((e.comp g₁))) = E.map (e.comp g₁)
    rw [← he, ← Matrix.map_mul, hAB]

private theorem qsMatrixEquiv.trans
    {R : Type*} [CommRing R]
    {ι κ η : Type*} [Fintype ι] [Fintype κ] [Fintype η]
    {E : Matrix ι ι R} {F : Matrix κ κ R} {G : Matrix η η R}
    (hEF : qsMatrixEquiv E F) (hFG : qsMatrixEquiv F G)
    (hE : E * E = E) (hG : G * G = G) : qsMatrixEquiv E G := by
  obtain ⟨A, B, hAB, hBA⟩ := hEF
  obtain ⟨C, D, hCD, hDC⟩ := hFG
  refine ⟨A * C, D * B, ?_, ?_⟩
  · calc
      (A * C) * (D * B) = A * (C * D) * B := by simp only [Matrix.mul_assoc]
      _ = A * F * B := by rw [hCD]
      _ = A * (B * A) * B := by rw [hBA]
      _ = (A * B) * (A * B) := by simp only [Matrix.mul_assoc]
      _ = E * E := by rw [hAB]
      _ = E := hE
  · calc
      (D * B) * (A * C) = D * (B * A) * C := by simp only [Matrix.mul_assoc]
      _ = D * F * C := by rw [hBA]
      _ = D * (C * D) * C := by rw [hCD]
      _ = (D * C) * (D * C) := by simp only [Matrix.mul_assoc]
      _ = G * G := by rw [hDC]
      _ = G := hG

private theorem qs_idempotent_map
    {R S : Type*} [CommRing R] [CommRing S]
    {i : Type*} [Fintype i]
    {E : Matrix i i R} (hE : E * E = E) (f : R →+* S) :
    E.map f * E.map f = E.map f := by
  rw [← Matrix.map_mul, hE]

private theorem qs_patching_zero
    {R : Type*} [CommRing R]
    {i : Type*} [Fintype i]
    {E : Matrix i i (Polynomial R)} (hE : E * E = E) :
    qsMatrixEquiv (E.map (qsShear (0 : R)))
      (E.map (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R))) := by
  rw [qsShear_zero]
  exact qsMatrixEquiv.refl (qs_idempotent_map hE _)

private theorem qs_patching_add
    {R : Type*} [CommRing R]
    {i : Type*} [Fintype i]
    {E : Matrix i i (Polynomial R)} (hE : E * E = E)
    {j j' : R}
    (hj : qsMatrixEquiv (E.map (qsShear j))
      (E.map (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R))))
    (hj' : qsMatrixEquiv (E.map (qsShear j'))
      (E.map (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R)))) :
    qsMatrixEquiv (E.map (qsShear (j + j')))
      (E.map (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R))) := by
  have hmap := hj.map (qsShiftX j')
  have hstep : qsMatrixEquiv (E.map (qsShear (j + j'))) (E.map (qsShear j')) := by
    change qsMatrixEquiv
      (E.map ((qsShiftX j').comp (qsShear j)))
      (E.map ((qsShiftX j').comp Polynomial.C)) at hmap
    rwa [qsShiftX_comp_shear, qsShiftX_comp_C] at hmap
  exact hstep.trans hj'
    (qs_idempotent_map hE _) (qs_idempotent_map hE _)

private theorem qs_patching_mul
    {R : Type*} [CommRing R]
    {i : Type*} [Fintype i]
    {E : Matrix i i (Polynomial R)}
    {j : R}
    (hj : qsMatrixEquiv (E.map (qsShear j))
      (E.map (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R))))
    (r : R) :
    qsMatrixEquiv (E.map (qsShear (r * j)))
      (E.map (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R))) := by
  have hmap := hj.map (qsScaleY r)
  change qsMatrixEquiv
    (E.map ((qsScaleY r).comp (qsShear j)))
    (E.map ((qsScaleY r).comp Polynomial.C)) at hmap
  rwa [qsScaleY_comp_shear, qsScaleY_comp_C] at hmap

private def qsPatchingIdeal
    {R : Type*} [CommRing R]
    {i : Type*} [Fintype i]
    (E : Matrix i i (Polynomial R)) (hE : E * E = E) : Ideal R where
  carrier := {j | qsMatrixEquiv (E.map (qsShear j))
    (E.map (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R)))}
  zero_mem' := qs_patching_zero hE
  add_mem' hj hj' := qs_patching_add hE hj hj'
  smul_mem' r _j hj := qs_patching_mul hj r

private theorem qs_exists_lifts_after_scale
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M : Submonoid R} [IsLocalization M S]
    {a : Type*} [Finite a]
    (p : a → Polynomial S) (hzero : ∀ i, (p i).coeff 0 = 0) :
    ∃ b : M, ∀ i, ∃ q : Polynomial R,
      q.map (algebraMap R S) =
        (p i).comp (Polynomial.C (algebraMap R S b) * Polynomial.X) := by
  classical
  let _ : Fintype a := Fintype.ofFinite a
  let I := Σ i : a, {n // n ∈ (p i).support}
  let f : I → S := fun z ↦ (p z.1).coeff z.2
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite M f
  refine ⟨b, fun i ↦ ?_⟩
  have hlift :
      (p i).comp (Polynomial.C (algebraMap R S b) * Polynomial.X) ∈
        Polynomial.lifts (algebraMap R S) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.comp_C_mul_X_coeff]
    by_cases hn0 : n = 0
    · subst n
      rw [hzero i, zero_mul]
      exact ⟨0, map_zero _⟩
    by_cases hn : n ∈ (p i).support
    · have hi := hb ⟨i, ⟨n, hn⟩⟩
      rw [Algebra.smul_def] at hi
      obtain ⟨c, hc⟩ := hi
      change algebraMap R S c =
        algebraMap R S (b : R) * (p i).coeff n at hc
      obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      refine ⟨c * (b : R) ^ d, ?_⟩
      rw [map_mul, map_pow, hc]
      rw [pow_succ]
      ring
    · rw [Polynomial.notMem_support_iff.mp hn]
      exact ⟨0, by simp⟩
  exact (Polynomial.lifts_iff_set_range _).mp hlift

private theorem qs_constantCoeff_comp_shear_one
    {R : Type*} [CommRing R] :
    (Polynomial.constantCoeff : Polynomial (Polynomial R) →+* Polynomial R).comp
        (qsShear (1 : R)) =
      (Polynomial.constantCoeff : Polynomial (Polynomial R) →+* Polynomial R).comp
        Polynomial.C := by
  apply Polynomial.ringHom_ext
  · intro r
    simp [qsShear]
  · simp [qsShear]

private theorem qs_constantCoeff_comp_shear_one_eq_id
    {R : Type*} [CommRing R] :
    (Polynomial.constantCoeff : Polynomial (Polynomial R) →+* Polynomial R).comp
        (qsShear (1 : R)) = RingHom.id (Polynomial R) := by
  apply Polynomial.ringHom_ext
  · intro r
    simp [qsShear]
  · simp [qsShear]

private theorem qs_exists_transition_with_zero_constant
    {R : Type*} [CommRing R]
    {i k : Type*} [Fintype i] [Fintype k] [DecidableEq k]
    {E : Matrix i i (Polynomial R)}
    (h : qsMatrixEquiv E (1 : Matrix k k (Polynomial R))) :
    ∃ C D : Matrix i i (Polynomial (Polynomial R)),
      C * D = E.map (qsShear (1 : R)) ∧
      D * C = E.map (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R)) ∧
      (∀ x y, (C x y - Polynomial.C (E x y)).coeff 0 = 0) ∧
      ∀ x y, (D x y - Polynomial.C (E x y)).coeff 0 = 0 := by
  obtain ⟨C, D, hCD, hDC, hC0, hD0⟩ :=
    qs_transition_one_of_equal_after h (qsShear (1 : R)) Polynomial.C
      Polynomial.constantCoeff qs_constantCoeff_comp_shear_one
  rw [qs_constantCoeff_comp_shear_one_eq_id] at hC0 hD0
  refine ⟨C, D, hCD, hDC, ?_, ?_⟩
  · intro x y
    have hxy := congrFun (congrFun hC0 x) y
    simpa [Polynomial.coeff_zero_eq_eval_zero] using sub_eq_zero.mpr hxy
  · intro x y
    have hxy := congrFun (congrFun hD0 x) y
    simpa [Polynomial.coeff_zero_eq_eval_zero] using sub_eq_zero.mpr hxy

private theorem qs_patching_member_of_localization
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M : Submonoid R} [IsLocalization M S]
    (hM : M ≤ nonZeroDivisors R)
    {i k : Type*} [Fintype i] [Fintype k] [DecidableEq k]
    (E : Matrix i i (Polynomial R)) (hE : E * E = E)
    (hlocal : qsMatrixEquiv
      (E.map (Polynomial.mapRingHom (algebraMap R S)))
      (1 : Matrix k k (Polynomial S))) :
    ∃ r : M, (r : R) ∈ qsPatchingIdeal E hE := by
  classical
  let f : Polynomial R →+* Polynomial S :=
    Polynomial.mapRingHom (algebraMap R S)
  obtain ⟨C, D, hCD, hDC, hCzero, hDzero⟩ :=
    qs_exists_transition_with_zero_constant hlocal
  let _ : Algebra (Polynomial R) (Polynomial S) := Polynomial.algebra R S
  let _ : IsLocalization (M.map Polynomial.C) (Polynomial S) :=
    Polynomial.isLocalization M S
  let p : Bool × (i × i) → Polynomial (Polynomial S) := fun z ↦
    match z.1 with
    | true => C z.2.1 z.2.2 - Polynomial.C (f (E z.2.1 z.2.2))
    | false => D z.2.1 z.2.2 - Polynomial.C (f (E z.2.1 z.2.2))
  have hpzero : ∀ z, (p z).coeff 0 = 0 := by
    rintro ⟨b, x, y⟩
    cases b
    · simpa [p, f] using hDzero x y
    · simpa [p, f] using hCzero x y
  obtain ⟨b, hb⟩ := qs_exists_lifts_after_scale
    (R := Polynomial R) (S := Polynomial S) (M := M.map Polynomial.C) p hpzero
  obtain ⟨r, hr, hCr⟩ := Submonoid.mem_map.mp b.property
  let qC : Matrix i i (Polynomial (Polynomial R)) := fun x y ↦
    Classical.choose (hb (true, (x, y)))
  let qD : Matrix i i (Polynomial (Polynomial R)) := fun x y ↦
    Classical.choose (hb (false, (x, y)))
  let E₀ : Matrix i i (Polynomial (Polynomial R)) := E.map Polynomial.C
  let C₀ := E₀ + qC
  let D₀ := E₀ + qD
  let F : Polynomial (Polynomial R) →+* Polynomial (Polynomial S) :=
    Polynomial.mapRingHom f
  let scale : Polynomial (Polynomial S) →+* Polynomial (Polynomial S) :=
    qsScaleY (algebraMap R S r)
  have hCmap : C₀.map F = C.map scale := by
    apply Matrix.ext
    intro x y
    have hq := Classical.choose_spec (hb (true, (x, y)))
    change F (C₀ x y) = scale (C x y)
    change F (E₀ x y + qC x y) = scale (C x y)
    rw [map_add]
    change F (Polynomial.C (E x y)) + F (qC x y) = scale (C x y)
    change F (Polynomial.C (E x y)) +
      (qC x y).map (algebraMap (Polynomial R) (Polynomial S)) = scale (C x y)
    rw [hq]
    simp only [p]
    rw [← hCr]
    simp [F, f, scale, qsScaleY, Polynomial.comp]
  have hDmap : D₀.map F = D.map scale := by
    apply Matrix.ext
    intro x y
    have hq := Classical.choose_spec (hb (false, (x, y)))
    change F (D₀ x y) = scale (D x y)
    change F (E₀ x y + qD x y) = scale (D x y)
    rw [map_add]
    change F (Polynomial.C (E x y)) + F (qD x y) = scale (D x y)
    change F (Polynomial.C (E x y)) +
      (qD x y).map (algebraMap (Polynomial R) (Polynomial S)) = scale (D x y)
    rw [hq]
    simp only [p]
    rw [← hCr]
    simp [F, f, scale, qsScaleY, Polynomial.comp]
  refine ⟨⟨r, hr⟩, ?_⟩
  change qsMatrixEquiv (E.map (qsShear r)) E₀
  refine ⟨C₀, D₀, ?_, ?_⟩
  · apply Matrix.map_injective (Polynomial.map_injective f <|
      Polynomial.map_injective (algebraMap R S) (IsLocalization.injective S hM))
    change (C₀ * D₀).map F = (E.map (qsShear r)).map F
    rw [Matrix.map_mul, hCmap, hDmap, ← Matrix.map_mul, hCD]
    apply Matrix.ext
    intro x y
    simpa [F, f, scale] using
      DFunLike.congr_fun (qs_scale_shear_map (algebraMap R S) r) (E x y)
  · apply Matrix.map_injective (Polynomial.map_injective f <|
      Polynomial.map_injective (algebraMap R S) (IsLocalization.injective S hM))
    change (D₀ * C₀).map F = E₀.map F
    rw [Matrix.map_mul, hDmap, hCmap, ← Matrix.map_mul, hDC]
    apply Matrix.ext
    intro x y
    simp [F, f, scale, qsScaleY, E₀]

private theorem qs_quillen_patching
    {R : Type*} [CommRing R] [IsDomain R]
    {i : Type*} [Fintype i]
    (E : Matrix i i (Polynomial R)) (hE : E * E = E)
    (hlocal : ∀ (m : Ideal R) (hm : m.IsMaximal),
      let _ : m.IsPrime := hm.isPrime
      ∃ n : ℕ, qsMatrixEquiv
        (E.map (Polynomial.mapRingHom (algebraMap R (Localization.AtPrime m))))
        (1 : Matrix (Fin n) (Fin n) (Polynomial (Localization.AtPrime m)))) :
    qsMatrixEquiv E (E.map (qsConstantAtZero : Polynomial R →+* Polynomial R)) := by
  let J := qsPatchingIdeal E hE
  have hJtop : J = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hne
    let _ : m.IsPrime := hm.isPrime
    obtain ⟨n, hn⟩ := hlocal m hm
    obtain ⟨r, hr⟩ := qs_patching_member_of_localization
      (S := Localization.AtPrime m) (M := m.primeCompl)
      m.primeCompl_le_nonZeroDivisors E hE hn
    exact r.property (hJm hr)
  have h1 : (1 : R) ∈ J := by
    rw [hJtop]
    simp
  have hmapped := h1.map (qsEvalXY : Polynomial (Polynomial R) →+* Polynomial R)
  change qsMatrixEquiv
    (E.map ((qsEvalXY : Polynomial (Polynomial R) →+* Polynomial R).comp
      (qsShear (1 : R))))
    (E.map ((qsEvalXY : Polynomial (Polynomial R) →+* Polynomial R).comp
      Polynomial.C)) at hmapped
  rw [qsEvalXY_comp_shear_one, qsEvalXY_comp_C] at hmapped
  have hid : E.map (RingHom.id (Polynomial R)) = E := by
    rfl
  rw [hid] at hmapped
  exact hmapped

private theorem qs_range_projective
    {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι]
    (E : Matrix ι ι R) (hE : E * E = E) :
    Module.Projective R (LinearMap.range E.mulVecLin) := by
  let p := E.mulVecLin
  apply Module.Projective.of_split (LinearMap.range p).subtype p.rangeRestrict
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  obtain ⟨y, hy⟩ := x.property
  change p x = x
  rw [← hy]
  change E.mulVecLin (E.mulVecLin y) = E.mulVecLin y
  change (E.mulVecLin.comp E.mulVecLin) y = E.mulVecLin y
  rw [← Matrix.mulVecLin_mul, hE]

private theorem qs_range_finite
    {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι]
    (E : Matrix ι ι R) :
    Module.Finite R (LinearMap.range E.mulVecLin) :=
  Module.Finite.range E.mulVecLin

private theorem qs_mulVec_eq_self_of_mem_range
    {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι]
    {E : Matrix ι ι R} (hE : E * E = E)
    {x : ι → R} (hx : x ∈ LinearMap.range E.mulVecLin) :
    E.mulVecLin x = x := by
  obtain ⟨y, rfl⟩ := hx
  change (E.mulVecLin.comp E.mulVecLin) y = E.mulVecLin y
  rw [← Matrix.mulVecLin_mul, hE]

private theorem qs_equiv_one_of_free_range
    {R : Type u} [CommRing R]
    {ι : Type v} [Fintype ι]
    (E : Matrix ι ι R) (hE : E * E = E)
    [Module.Free R (LinearMap.range E.mulVecLin)]
    [Module.Finite R (LinearMap.range E.mulVecLin)] :
    ∃ (κ : Type (max u v)) (_ : Fintype κ) (_ : DecidableEq κ),
      qsMatrixEquiv E (1 : Matrix κ κ R) := by
  classical
  let P := LinearMap.range E.mulVecLin
  let κ := Module.Free.ChooseBasisIndex R P
  let _ : Fintype κ := Module.Free.ChooseBasisIndex.fintype R P
  let b := Module.Free.chooseBasis R P
  let e := Finsupp.linearEquivFunOnFinite R R κ
  let a : (κ → R) →ₗ[R] (ι → R) :=
    (LinearMap.range E.mulVecLin).subtype.comp
      (b.repr.symm.toLinearMap.comp e.symm.toLinearMap)
  let c : (ι → R) →ₗ[R] (κ → R) :=
    e.toLinearMap.comp (b.repr.toLinearMap.comp E.mulVecLin.rangeRestrict)
  refine ⟨κ, inferInstance, inferInstance, LinearMap.toMatrix' a, LinearMap.toMatrix' c, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_toLin' E]
    congr 1
    ext x
    simp only [a, c, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply, Submodule.coe_subtype]
    rfl
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    apply LinearMap.ext
    intro x
    let z : P := b.repr.symm (e.symm x)
    have hz : E.mulVecLin.rangeRestrict (z : ι → R) = z := by
      apply Subtype.ext
      exact qs_mulVec_eq_self_of_mem_range hE z.property
    change e (b.repr (E.mulVecLin.rangeRestrict (z : ι → R))) = x
    rw [hz]
    simp [z]

private theorem qs_equiv_one_fin_of_free_range
    {R : Type u} [CommRing R]
    {ι : Type v} [Fintype ι]
    (E : Matrix ι ι R) (hE : E * E = E)
    [Module.Free R (LinearMap.range E.mulVecLin)]
    [Module.Finite R (LinearMap.range E.mulVecLin)] :
    ∃ n : ℕ, qsMatrixEquiv E (1 : Matrix (Fin n) (Fin n) R) := by
  classical
  obtain ⟨κ, _, _, hκ⟩ := qs_equiv_one_of_free_range E hE
  exact ⟨Fintype.card κ,
    hκ.reindex_one (Fintype.equivFin κ).symm⟩

private theorem qs_residue_equiv_one
    (R : Type*) [CommRing R] [IsLocalRing R]
    {ι : Type*} [Fintype ι]
    (E : Matrix ι ι (Polynomial R)) (hE : E * E = E) :
    ∃ n : ℕ, qsMatrixEquiv
      (E.map (Polynomial.mapRingHom (IsLocalRing.residue R)))
      (1 : Matrix (Fin n) (Fin n)
        (Polynomial (IsLocalRing.ResidueField R))) := by
  let Ebar := E.map (Polynomial.mapRingHom (IsLocalRing.residue R))
  have hEbar : Ebar * Ebar = Ebar := qs_idempotent_map hE _
  let _ : Module.Projective (Polynomial (IsLocalRing.ResidueField R))
      (LinearMap.range Ebar.mulVecLin) := qs_range_projective Ebar hEbar
  let _ : Module.Finite (Polynomial (IsLocalRing.ResidueField R))
      (LinearMap.range Ebar.mulVecLin) := qs_range_finite Ebar
  let _ : Module.Free (Polynomial (IsLocalRing.ResidueField R))
      (LinearMap.range Ebar.mulVecLin) :=
    Module.free_of_finite_type_torsion_free'
  exact qs_equiv_one_fin_of_free_range Ebar hEbar

private theorem qs_fin_eq_of_one_equiv_one
    {K : Type*} [Field K] {n m : ℕ}
    (h : qsMatrixEquiv (1 : Matrix (Fin n) (Fin n) K)
      (1 : Matrix (Fin m) (Fin m) K)) : n = m := by
  classical
  obtain ⟨A, B, hAB, hBA⟩ := h
  let e : (Fin m → K) ≃ₗ[K] (Fin n → K) :=
    LinearEquiv.ofLinearMap A.mulVecLin B.mulVecLin (by
      apply LinearMap.ext
      intro x
      change (A.mulVecLin.comp B.mulVecLin) x = x
      rw [← Matrix.mulVecLin_mul, hAB, Matrix.mulVecLin_one,
        LinearMap.id_apply]) (by
      apply LinearMap.ext
      intro x
      change (B.mulVecLin.comp A.mulVecLin) x = x
      rw [← Matrix.mulVecLin_mul, hBA, Matrix.mulVecLin_one,
        LinearMap.id_apply])
  have hrank := e.finrank_eq
  rw [Module.finrank_eq_card_basis (Pi.basisFun K (Fin m)),
    Module.finrank_eq_card_basis (Pi.basisFun K (Fin n)),
    Fintype.card_fin, Fintype.card_fin] at hrank
  exact hrank.symm

private theorem qs_residue_equiv_one_same_rank
    (R : Type*) [CommRing R] [IsLocalRing R]
    {ι : Type*} [Fintype ι]
    (E : Matrix ι ι (Polynomial R)) (hE : E * E = E)
    {m : ℕ}
    (hQ : qsMatrixEquiv
      (E.map (algebraMap (Polynomial R)
        (Localization (qsMonicSubmonoid R))))
      (1 : Matrix (Fin m) (Fin m)
        (Localization (qsMonicSubmonoid R)))) :
    qsMatrixEquiv
      (E.map (Polynomial.mapRingHom (IsLocalRing.residue R)))
      (1 : Matrix (Fin m) (Fin m)
        (Polynomial (IsLocalRing.ResidueField R))) := by
  classical
  obtain ⟨n, hn⟩ := qs_residue_equiv_one R E hE
  let k := IsLocalRing.ResidueField R
  let K := Localization (qsMonicSubmonoid k)
  let Q := Localization (qsMonicSubmonoid R)
  let _ : IsFractionRing (Polynomial k) K :=
    qs_monicLocalization_isFractionRing k
  let _ : Field K := IsFractionRing.toField (Polynomial k)
  have hnK := hn.map (algebraMap (Polynomial k) K)
  have hmK := hQ.map (qsResidueMonicMap R)
  rw [Matrix.map_one (algebraMap (Polynomial k) K) (map_zero _) (map_one _)] at hnK
  rw [Matrix.map_one (qsResidueMonicMap R) (map_zero _) (map_one _)] at hmK
  have hcompat :
      (E.map (algebraMap (Polynomial R) Q)).map (qsResidueMonicMap R) =
        (E.map (Polynomial.mapRingHom (IsLocalRing.residue R))).map
          (algebraMap (Polynomial k) K) := by
    apply Matrix.ext
    intro i j
    exact qsResidueMonicMap_algebraMap R (E i j)
  rw [hcompat] at hmK
  have hone : qsMatrixEquiv (1 : Matrix (Fin n) (Fin n) K)
      (1 : Matrix (Fin m) (Fin m) K) :=
    hnK.symm.trans hmK (by simp) (by simp)
  have hnm : n = m := qs_fin_eq_of_one_equiv_one hone
  subst n
  exact hn

private def qsResiduePolynomialMatrix
    (R : Type*) [CommRing R] [IsLocalRing R]
    {ι κ : Type*}
    (A : Matrix ι κ (Localization (qsMonicSubmonoid R))) : Prop :=
  ∃ C : Matrix ι κ (Polynomial (IsLocalRing.ResidueField R)),
    A.map (qsResidueMonicMap R) =
      C.map (algebraMap (Polynomial (IsLocalRing.ResidueField R))
        (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R))))

private theorem qs_horrocks_adjusted_factors
    (R : Type*) [CommRing R] [IsLocalRing R]
    {ι : Type*} [Fintype ι]
    (E : Matrix ι ι (Polynomial R)) (hE : E * E = E)
    {m : ℕ}
    (hQ : qsMatrixEquiv
      (E.map (algebraMap (Polynomial R)
        (Localization (qsMonicSubmonoid R))))
      (1 : Matrix (Fin m) (Fin m)
        (Localization (qsMonicSubmonoid R)))) :
    ∃ A : Matrix ι (Fin m) (Localization (qsMonicSubmonoid R)),
      ∃ B : Matrix (Fin m) ι (Localization (qsMonicSubmonoid R)),
        A * B = E.map (algebraMap (Polynomial R)
          (Localization (qsMonicSubmonoid R))) ∧
        B * A = 1 ∧
        qsResiduePolynomialMatrix R A ∧
        qsResiduePolynomialMatrix R B := by
  classical
  let k := IsLocalRing.ResidueField R
  let K := Localization (qsMonicSubmonoid k)
  let Q := Localization (qsMonicSubmonoid R)
  let q : Q →+* K := qsResidueMonicMap R
  let ak : Polynomial k →+* K := algebraMap (Polynomial k) K
  let _ : IsFractionRing (Polynomial k) K :=
    qs_monicLocalization_isFractionRing k
  let _ : Field K := IsFractionRing.toField (Polynomial k)
  obtain ⟨C, D, hCD, hDC⟩ :=
    qs_residue_equiv_one_same_rank R E hE hQ
  obtain ⟨A, B, hAB, hBA⟩ := hQ
  let AK := A.map q
  let BK := B.map q
  let CK := C.map ak
  let DK := D.map ak
  have hcompat :
      (E.map (algebraMap (Polynomial R) Q)).map q =
        (E.map (Polynomial.mapRingHom (IsLocalRing.residue R))).map ak := by
    apply Matrix.ext
    intro i j
    exact qsResidueMonicMap_algebraMap R (E i j)
  have hABK : AK * BK = CK * DK := by
    calc
      AK * BK = (A * B).map q := by simp only [AK, BK, Matrix.map_mul]
      _ = (E.map (algebraMap (Polynomial R) Q)).map q := by rw [hAB]
      _ = (E.map (Polynomial.mapRingHom (IsLocalRing.residue R))).map ak := hcompat
      _ = (C * D).map ak := by rw [hCD]
      _ = CK * DK := by simp only [CK, DK, Matrix.map_mul]
  have hBAK : BK * AK = 1 := by
    calc
      BK * AK = (B * A).map q := by simp only [AK, BK, Matrix.map_mul]
      _ = (1 : Matrix (Fin m) (Fin m) Q).map q := by rw [hBA]
      _ = 1 := Matrix.map_one q q.map_zero q.map_one
  have hDCK : DK * CK = 1 := by
    calc
      DK * CK = (D * C).map ak := by simp only [CK, DK, Matrix.map_mul]
      _ = (1 : Matrix (Fin m) (Fin m) (Polynomial k)).map ak := by rw [hDC]
      _ = 1 := Matrix.map_one ak ak.map_zero ak.map_one
  let T := DK * AK
  let S := BK * CK
  have hTS : T * S = 1 := by
    calc
      T * S = DK * (AK * BK) * CK := by simp only [T, S, Matrix.mul_assoc]
      _ = DK * (CK * DK) * CK := by rw [hABK]
      _ = (DK * CK) * (DK * CK) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hDCK, Matrix.one_mul]
  have hST : S * T = 1 := by
    calc
      S * T = BK * (CK * DK) * AK := by simp only [S, T, Matrix.mul_assoc]
      _ = BK * (AK * BK) * AK := by rw [← hABK]
      _ = (BK * AK) * (BK * AK) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBAK, Matrix.one_mul]
  have hTdet : T.det ≠ 0 := by
    intro hzero
    have hdet := congrArg Matrix.det hTS
    rw [Matrix.det_mul, hzero, zero_mul, Matrix.det_one] at hdet
    exact zero_ne_one hdet
  obtain ⟨U, hUunit, hUmap⟩ :=
    qs_lift_residue_invertible_matrix R T hTdet
  let Uinv := U⁻¹
  have hleft : T * Uinv.map q = 1 := by
    have hu := congrArg (fun N ↦ N.map q) (Matrix.mul_nonsing_inv U hUunit)
    rw [Matrix.map_mul, hUmap,
      Matrix.map_one q q.map_zero q.map_one] at hu
    exact hu
  have hUinvmap : Uinv.map q = S := by
    calc
      Uinv.map q = 1 * Uinv.map q := by rw [Matrix.one_mul]
      _ = (S * T) * Uinv.map q := by rw [hST]
      _ = S * (T * Uinv.map q) := by rw [Matrix.mul_assoc]
      _ = S := by rw [hleft, Matrix.mul_one]
  let A' := A * Uinv
  let B' := U * B
  have hA'B' : A' * B' = E.map (algebraMap (Polynomial R) Q) := by
    calc
      A' * B' = A * (Uinv * U) * B := by simp only [A', B', Matrix.mul_assoc]
      _ = A * (1 : Matrix (Fin m) (Fin m) Q) * B := by
        rw [Matrix.nonsing_inv_mul U hUunit]
      _ = _ := by rw [Matrix.mul_one, hAB]
  have hB'A' : B' * A' = 1 := by
    calc
      B' * A' = U * (B * A) * Uinv := by simp only [A', B', Matrix.mul_assoc]
      _ = U * 1 * Uinv := by rw [hBA]
      _ = 1 := by rw [Matrix.mul_one, Matrix.mul_nonsing_inv U hUunit]
  have hA'map : A'.map q = CK := by
    calc
      A'.map q = AK * Uinv.map q := by
        simp only [A', AK, Matrix.map_mul]
      _ = AK * (BK * CK) := by rw [hUinvmap]
      _ = (AK * BK) * CK := by rw [Matrix.mul_assoc]
      _ = (CK * DK) * CK := by rw [hABK]
      _ = CK * (DK * CK) := by rw [Matrix.mul_assoc]
      _ = CK := by rw [hDCK, Matrix.mul_one]
  have hB'map : B'.map q = DK := by
    calc
      B'.map q = U.map q * BK := by
        simp only [B', BK, Matrix.map_mul]
      _ = (DK * AK) * BK := by rw [hUmap]
      _ = DK * (AK * BK) := by rw [Matrix.mul_assoc]
      _ = DK * (CK * DK) := by rw [hABK]
      _ = (DK * CK) * DK := by rw [Matrix.mul_assoc]
      _ = DK := by rw [hDCK, Matrix.one_mul]
  exact ⟨A', B', hA'B', hB'A', ⟨C, hA'map⟩, ⟨D, hB'map⟩⟩

private theorem qs_horrocks_local
    (R : Type*) [CommRing R] [IsLocalRing R]
    {ι : Type*} [Fintype ι]
    (E : Matrix ι ι (Polynomial R)) (hE : E * E = E)
    {m : ℕ}
    (hQ : qsMatrixEquiv
      (E.map (algebraMap (Polynomial R)
        (Localization (qsMonicSubmonoid R))))
      (1 : Matrix (Fin m) (Fin m)
        (Localization (qsMonicSubmonoid R)))) :
    qsMatrixEquiv E (1 : Matrix (Fin m) (Fin m) (Polynomial R)) := by
  classical
  let k := IsLocalRing.ResidueField R
  let Q := Localization (qsMonicSubmonoid R)
  let K := Localization (qsMonicSubmonoid k)
  let alg : Polynomial R →+* Q := algebraMap (Polynomial R) Q
  let ak : Polynomial k →+* K := algebraMap (Polynomial k) K
  let q : Q →+* K := qsResidueMonicMap R
  let bar : Polynomial R →+* Polynomial k :=
    Polynomial.mapRingHom (IsLocalRing.residue R)
  obtain ⟨A, B, hAB, hBA, hA, hB⟩ :=
    qs_horrocks_adjusted_factors R E hE hQ
  obtain ⟨F, hF⟩ := qs_horrocks_map_surjective R A B hBA hA hB
    (1 : Matrix (Fin m) (Fin m) (Polynomial R))
  let FQ := F.map alg
  let H := FQ * A
  have hHpart : qsMatrixPolynomialPart R H = 1 := by
    simpa only [qsHorrocksMap_apply] using hF
  have hHunit : IsUnit H.det :=
    qs_isUnit_det_of_matrixPolynomialPart_eq_one H fun i j ↦
      congrFun (congrFun hHpart i) j
  let Hinv := H⁻¹
  let A₂ := A * Hinv
  let B₂ := H * B
  have hA₂B₂ : A₂ * B₂ = E.map alg := by
    calc
      A₂ * B₂ = A * (Hinv * H) * B := by
        simp only [A₂, B₂, Matrix.mul_assoc]
      _ = A * (1 : Matrix (Fin m) (Fin m) Q) * B := by
        rw [Matrix.nonsing_inv_mul H hHunit]
      _ = E.map alg := by rw [Matrix.mul_one A, hAB]
  have hB₂A₂ : B₂ * A₂ = 1 := by
    calc
      B₂ * A₂ = H * (B * A) * Hinv := by
        simp only [A₂, B₂, Matrix.mul_assoc]
      _ = H * (1 : Matrix (Fin m) (Fin m) Q) * Hinv := by rw [hBA]
      _ = 1 := by rw [Matrix.mul_one, Matrix.mul_nonsing_inv H hHunit]
  let B₀ := F * E
  have hB₂ : B₂ = B₀.map alg := by
    calc
      B₂ = (FQ * A) * B := rfl
      _ = FQ * (A * B) := by rw [Matrix.mul_assoc]
      _ = FQ * E.map alg := by rw [hAB]
      _ = B₀.map alg := by simp only [B₀, FQ, Matrix.map_mul]
  obtain ⟨C, hAC⟩ := hA
  have hFcompat : FQ.map q = (F.map bar).map ak := by
    apply Matrix.ext
    intro i j
    exact qsResidueMonicMap_algebraMap R (F i j)
  have hHC : H.map q = (F.map bar * C).map ak := by
    calc
      H.map q = FQ.map q * A.map q := by
        simp only [H, Matrix.map_mul]
      _ = (F.map bar).map ak * C.map ak := by rw [hFcompat, hAC]
      _ = (F.map bar * C).map ak := (Matrix.map_mul ..).symm
  have hFC : F.map bar * C = 1 := by
    have hp := qsMatrixPolynomialPart_map_residue R H (F.map bar * C) hHC
    rw [hHpart] at hp
    calc
      F.map bar * C =
          (1 : Matrix (Fin m) (Fin m) (Polynomial R)).map bar := hp.symm
      _ = 1 := Matrix.map_one bar bar.map_zero bar.map_one
  have hHq : H.map q = 1 := by
    rw [hHC, hFC]
    exact Matrix.map_one ak ak.map_zero ak.map_one
  have hHinvq : Hinv.map q = 1 := by
    have hu := congrArg (fun X ↦ X.map q) (Matrix.mul_nonsing_inv H hHunit)
    rw [Matrix.map_mul, hHq, Matrix.one_mul,
      Matrix.map_one q q.map_zero q.map_one] at hu
    exact hu
  have hA₂res : qsResiduePolynomialMatrix R A₂ := by
    refine ⟨C, ?_⟩
    calc
      A₂.map q = A.map q * Hinv.map q := by
        simp only [A₂, Matrix.map_mul]
      _ = C.map ak * (1 : Matrix (Fin m) (Fin m) K) := by
        rw [hAC, hHinvq]
      _ = C.map ak := Matrix.mul_one _
  have hB₀compat : (B₀.map alg).map q = (B₀.map bar).map ak := by
    apply Matrix.ext
    intro i j
    exact qsResidueMonicMap_algebraMap R (B₀ i j)
  have hB₂res : qsResiduePolynomialMatrix R B₂ := by
    refine ⟨B₀.map bar, ?_⟩
    rw [hB₂]
    exact hB₀compat
  obtain ⟨C₂, hB₂C₂⟩ := hB₂res
  obtain ⟨D₂, hA₂D₂⟩ := hA₂res
  have htransinv : A₂.transpose * B₂.transpose = 1 := by
    rw [← Matrix.transpose_mul, hB₂A₂, Matrix.transpose_one]
  have hB₂transres : qsResiduePolynomialMatrix R B₂.transpose := by
    refine ⟨C₂.transpose, ?_⟩
    rw [Matrix.transpose_map, hB₂C₂, Matrix.transpose_map]
  have hA₂transres : qsResiduePolynomialMatrix R A₂.transpose := by
    refine ⟨D₂.transpose, ?_⟩
    rw [Matrix.transpose_map, hA₂D₂, Matrix.transpose_map]
  obtain ⟨F₂, hF₂⟩ := qs_horrocks_map_surjective R
    B₂.transpose A₂.transpose htransinv hB₂transres hA₂transres
    (1 : Matrix (Fin m) (Fin m) (Polynomial R))
  have hF₂part : qsMatrixPolynomialPart R
      (F₂.map alg * B₂.transpose) = 1 := by
    simpa only [qsHorrocksMap_apply] using hF₂
  let G := F₂.transpose
  have htrans : (F₂.map alg * B₂.transpose).transpose =
      B₂ * G.map alg := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_map]
  have hBGpart : qsMatrixPolynomialPart R (B₂ * G.map alg) = 1 := by
    have hp := congrArg Matrix.transpose hF₂part
    rw [← qsMatrixPolynomialPart_transpose, htrans, Matrix.transpose_one] at hp
    exact hp
  have hB₀G : B₀ * G = 1 := by
    calc
      B₀ * G = qsMatrixPolynomialPart R ((B₀ * G).map alg) :=
        (qsMatrixPolynomialPart_algebraMap (B₀ * G)).symm
      _ = qsMatrixPolynomialPart R (B₂ * G.map alg) := by
        rw [Matrix.map_mul, ← hB₂]
      _ = 1 := hBGpart
  let A₀ := E * G
  have hA₂ : A₂ = A₀.map alg := by
    calc
      A₂ = A₂ * (1 : Matrix (Fin m) (Fin m) Q) := (Matrix.mul_one A₂).symm
      _ = A₂ * ((B₀ * G).map alg) := by
        rw [hB₀G, Matrix.map_one alg alg.map_zero alg.map_one]
      _ = A₂ * (B₂ * G.map alg) := by rw [Matrix.map_mul, ← hB₂]
      _ = (A₂ * B₂) * G.map alg := (Matrix.mul_assoc ..).symm
      _ = E.map alg * G.map alg := by rw [hA₂B₂]
      _ = A₀.map alg := by simp only [A₀, Matrix.map_mul]
  have halg : Function.Injective alg :=
    IsLocalization.injective Q fun _
      (hs : _ ∈ qsMonicSubmonoid R) ↦
        Polynomial.Monic.mem_nonZeroDivisors hs
  refine ⟨A₀, B₀, ?_, ?_⟩
  · apply Matrix.map_injective halg
    calc
      (A₀ * B₀).map alg = A₂ * B₂ := by rw [Matrix.map_mul, ← hA₂, ← hB₂]
      _ = E.map alg := hA₂B₂
  · apply Matrix.map_injective halg
    calc
      (B₀ * A₀).map alg = B₂ * A₂ := by rw [Matrix.map_mul, ← hA₂, ← hB₂]
      _ = 1 := hB₂A₂
      _ = (1 : Matrix (Fin m) (Fin m) (Polynomial R)).map alg :=
        (Matrix.map_one alg alg.map_zero alg.map_one).symm

private theorem qs_free_range_of_equiv_one
    {R : Type*} [CommRing R]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {E : Matrix ι ι R}
    (h : qsMatrixEquiv E (1 : Matrix κ κ R)) :
    Module.Free R (LinearMap.range E.mulVecLin) := by
  classical
  obtain ⟨A, B, hAB, hBA⟩ := h
  have hE : E * E = E := by
    calc
      E * E = (A * B) * (A * B) := by rw [hAB]
      _ = A * (B * A) * B := by simp only [Matrix.mul_assoc]
      _ = A * (1 : Matrix κ κ R) * B := by rw [hBA]
      _ = E := by rw [Matrix.mul_one, hAB]
  have hEA : E * A = A := by
    calc
      E * A = (A * B) * A := by rw [hAB]
      _ = A * (B * A) := by rw [Matrix.mul_assoc]
      _ = A := by rw [hBA, Matrix.mul_one]
  let P := LinearMap.range E.mulVecLin
  let f : P →ₗ[R] (κ → R) := B.mulVecLin.comp (LinearMap.range E.mulVecLin).subtype
  let g : (κ → R) →ₗ[R] P := A.mulVecLin.codRestrict P fun x ↦ by
    refine ⟨A.mulVecLin x, ?_⟩
    change (E.mulVecLin.comp A.mulVecLin) x = A.mulVecLin x
    rw [← Matrix.mulVecLin_mul, hEA]
  have hfg : f.comp g = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change B.mulVecLin (A.mulVecLin x) = x
    change (B.mulVecLin.comp A.mulVecLin) x = x
    rw [← Matrix.mulVecLin_mul, hBA, Matrix.mulVecLin_one, LinearMap.id_apply]
  have hgf : g.comp f = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change A.mulVecLin (B.mulVecLin x) = x
    change (A.mulVecLin.comp B.mulVecLin) x = x
    rw [← Matrix.mulVecLin_mul, hAB]
    exact qs_mulVec_eq_self_of_mem_range hE x.property
  exact Module.Free.of_equiv (LinearEquiv.ofLinearMap f g hfg hgf).symm

private theorem qs_exists_idempotent_range_equiv
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    ∃ (n : ℕ) (E : Matrix (Fin n) (Fin n) R),
      E * E = E ∧ Nonempty (M ≃ₗ[R] LinearMap.range E.mulVecLin) := by
  classical
  obtain ⟨n, f, g, hf, _, hfg⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective R M
  let p : (Fin n → R) →ₗ[R] (Fin n → R) := g.comp f
  have hp : p.comp p = p := by
    apply LinearMap.ext
    intro x
    change g (f (g (f x))) = g (f x)
    have hx := LinearMap.congr_fun hfg (f x)
    change f (g (f x)) = f x at hx
    rw [hx]
  let E : Matrix (Fin n) (Fin n) R := LinearMap.toMatrix' p
  have hE : E * E = E := by
    calc
      E * E = LinearMap.toMatrix' (p.comp p) :=
        (LinearMap.toMatrix'_comp p p).symm
      _ = E := congrArg LinearMap.toMatrix' hp
  have hEp : E.mulVecLin = p := Matrix.toLin'_toMatrix' p
  let i : M →ₗ[R] LinearMap.range p := g.codRestrict (LinearMap.range p) fun m ↦ by
    obtain ⟨x, rfl⟩ := hf m
    exact ⟨x, rfl⟩
  let s : LinearMap.range p →ₗ[R] M := f.comp (LinearMap.range p).subtype
  have hsi : s.comp i = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun hfg x
  have his : i.comp s = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    obtain ⟨y, hy⟩ := x.property
    change p x = x
    rw [← hy]
    exact LinearMap.congr_fun hp y
  refine ⟨n, E, hE, ?_⟩
  rw [hEp]
  exact ⟨LinearEquiv.ofLinearMap i s his hsi⟩

private theorem qs_free_of_matrix_equiv_one
    {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {E : Matrix ι ι R}
    (e : M ≃ₗ[R] LinearMap.range E.mulVecLin)
    (h : qsMatrixEquiv E (1 : Matrix κ κ R)) : Module.Free R M := by
  let : Module.Free R (LinearMap.range E.mulVecLin) :=
    qs_free_range_of_equiv_one h
  exact Module.Free.of_equiv e.symm

private theorem qs_zero_variables
    {k : Type*} [Field k]
    {M : Type*} [AddCommGroup M] [Module (MvPolynomial (Fin 0) k) M] :
    Module.Free (MvPolynomial (Fin 0) k) M := by
  let e : MvPolynomial (Fin 0) k ≃+* k :=
    (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).toRingEquiv
  let : Module k M := Module.compHom M e.symm.toRingHom
  exact Module.Free.of_basis <|
    (Module.Basis.ofVectorSpace k M).mapCoeffs e.symm fun _ _ ↦ rfl

private theorem qs_idempotent_free
    (n : ℕ) (k : Type*) [Field k]
    {ι : Type*} [Fintype ι]
    (E : Matrix ι ι (MvPolynomial (Fin n) k)) (hE : E * E = E) :
    ∃ m : ℕ, qsMatrixEquiv E
      (1 : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) k)) := by
  induction n generalizing k ι with
  | zero =>
      let P := LinearMap.range E.mulVecLin
      let _ : Module.Projective (MvPolynomial (Fin 0) k) P :=
        qs_range_projective E hE
      let _ : Module.Finite (MvPolynomial (Fin 0) k) P :=
        qs_range_finite E
      let _ : Module.Free (MvPolynomial (Fin 0) k) P :=
        qs_zero_variables
      exact qs_equiv_one_fin_of_free_range E hE
  | succ n ih =>
      let B := MvPolynomial (Fin n) k
      let e := MvPolynomial.finSuccEquiv k n
      let er : MvPolynomial (Fin (n + 1)) k →+* Polynomial B :=
        e.toRingEquiv.toRingHom
      let Ep := E.map er
      have hEp : Ep * Ep = Ep := qs_idempotent_map hE er
      let K := FractionRing (Polynomial k)
      let gen := qsGenericMap k n
      let Eg := Ep.map gen
      have hEg : Eg * Eg = Eg := qs_idempotent_map hEp gen
      obtain ⟨m, hm⟩ := ih K Eg hEg
      have hlocal : ∀ (p : Ideal B) (hp : p.IsMaximal),
          let _ : p.IsPrime := hp.isPrime
          ∃ r : ℕ, qsMatrixEquiv
            (Ep.map (Polynomial.mapRingHom
              (algebraMap B (Localization.AtPrime p))))
            (1 : Matrix (Fin r) (Fin r)
              (Polynomial (Localization.AtPrime p))) := by
        intro p hp
        let _ : p.IsPrime := hp.isPrime
        let A := Localization.AtPrime p
        let f : B →+* A := algebraMap B A
        let Q := Localization (qsMonicSubmonoid A)
        let alg : Polynomial A →+* Q := algebraMap (Polynomial A) Q
        let spec := qsGenericSpecialization k n A f
        have hcomp := qs_genericSpecialization_comp_genericMap k n A f
        have hmQ := hm.map spec
        rw [Matrix.map_one spec spec.map_zero spec.map_one] at hmQ
        have hmatrix : (Ep.map gen).map spec =
            Ep.map (alg.comp (Polynomial.mapRingHom f)) := by
          apply Matrix.ext
          intro i j
          exact DFunLike.congr_fun hcomp (Ep i j)
        rw [hmatrix] at hmQ
        have hmQ' : qsMatrixEquiv
            (Ep.map (alg.comp (Polynomial.mapRingHom f)))
            (1 : Matrix (Fin m) (Fin m) Q) := hmQ
        let Eloc := Ep.map (Polynomial.mapRingHom f)
        have hEloc : Eloc * Eloc = Eloc := by
          have h := congrArg
            (fun M ↦ M.map (Polynomial.mapRingHom f)) hEp
          simpa only [Eloc, Matrix.map_mul] using h
        have hmQloc : qsMatrixEquiv (Eloc.map alg)
            (1 : Matrix (Fin m) (Fin m) Q) := by
          have heq : Eloc.map alg =
              Ep.map (alg.comp (Polynomial.mapRingHom f)) := by
            apply Matrix.ext
            intro i j
            rfl
          rw [heq]
          exact hmQ'
        exact ⟨m, qs_horrocks_local A Eloc hEloc hmQloc⟩
      have hpatch := qs_quillen_patching Ep hEp hlocal
      let E₀ := Ep.map Polynomial.constantCoeff
      have hE₀ : E₀ * E₀ = E₀ :=
        qs_idempotent_map hEp Polynomial.constantCoeff
      obtain ⟨r, hr⟩ := ih k E₀ hE₀
      have hrpoly := hr.map (Polynomial.C : B →+* Polynomial B)
      rw [Matrix.map_one (Polynomial.C : B →+* Polynomial B)
        (map_zero _) (map_one _)] at hrpoly
      have hconstant : qsMatrixEquiv
          (Ep.map (qsConstantAtZero : Polynomial B →+* Polynomial B))
          (1 : Matrix (Fin r) (Fin r) (Polynomial B)) := by
        have heq : E₀.map (Polynomial.C : B →+* Polynomial B) =
            Ep.map (qsConstantAtZero : Polynomial B →+* Polynomial B) := by
          apply Matrix.ext
          intro i j
          rfl
        rw [← heq]
        exact hrpoly
      have hEpone : qsMatrixEquiv Ep
          (1 : Matrix (Fin r) (Fin r) (Polynomial B)) :=
        hpatch.trans hconstant hEp (by simp)
      have hback := hEpone.map e.symm.toRingEquiv.toRingHom
      rw [Matrix.map_one e.symm.toRingEquiv.toRingHom
        (map_zero _) (map_one _)] at hback
      have heq : Ep.map e.symm.toRingEquiv.toRingHom = E := by
        apply Matrix.ext
        intro i j
        exact e.symm_apply_apply (E i j)
      rw [heq] at hback
      exact ⟨r, hback⟩

/--
**Quillen–Suslin theorem.** Let $k$ be a field and let $n$ be a natural number. Every finitely
generated projective module over the polynomial ring $k[x_1, \dots, x_n]$ in $n$ variables is
free.

Proof: The argument follows Quillen's induction and patching route, using Roberts'
idempotent-matrix proof of local Horrocks; see Quillen (1976), Lam, Lang, and Dicks.

Proves `Wanted` entry `quillen_suslin`.

Source: Serre's conjecture proved by D. Quillen, Invent. Math. 36 (1976) and A.
A. Suslin, Dokl. Akad. Nauk SSSR 229 (1976); Lam, Serre's Problem; Lean states field case over
`MvPolynomial (Fin n) k` with PID generalization existing.
-/
theorem quillen_suslin
    {k : Type*} [Field k]
    {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module (MvPolynomial (Fin n) k) M]
    [Module.Finite (MvPolynomial (Fin n) k) M]
    [Module.Projective (MvPolynomial (Fin n) k) M] :
    Module.Free (MvPolynomial (Fin n) k) M := by
  obtain ⟨r, E, hE, ⟨e⟩⟩ :=
    qs_exists_idempotent_range_equiv
      (R := MvPolynomial (Fin n) k) (M := M)
  obtain ⟨m, hm⟩ := qs_idempotent_free n k E hE
  exact qs_free_of_matrix_equiv_one e hm

end

end MathlibExt.Algebra.Module.QuillenSuslinWanted
