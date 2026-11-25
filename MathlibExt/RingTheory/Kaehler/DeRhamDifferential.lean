/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.RingTheory.Kaehler.DeRhamDifferential.ExteriorPower
public import MathlibExt.LinearAlgebra.ExteriorPower.ContractionWedge
public import Mathlib.Data.ZMod.Basic

/-!
# The algebraic de Rham differential on exterior powers

The base-linear differential on exterior powers of Kähler differentials
satisfies the scalar-wedge formula, squares to zero and obeys the graded
Leibniz rule. It is natural under change of algebra, without smoothness or
perfection assumptions. The differential on forms over the integer base
is also `ZMod p`-linear for a `ZMod p`-algebra.
-/

public section
noncomputable section
universe u v
variable (K : Type u) (A : Type v) [CommRing K] [CommRing A] [Algebra K A]

namespace KaehlerDifferential.DeRham

/-- The actual de Rham differential in every degree, linear over the base ring. -/
def differential (n : ℕ) : Forms K A n →ₗ[K] Forms K A (n + 1) where
  toFun w := ⟨differentialToExterior K A n w, differentialToExterior_mem K A n w⟩
  map_add' x y := by apply Subtype.ext; exact map_add _ x y
  map_smul' r x := by apply Subtype.ext; exact map_smul _ r x

lemma differential_presentation_coe (n : ℕ) (q : (Fin n → W K A) →₀ A) :
    (differential K A n (presentationForms K A n q) : E K A) =
      freeDifferentialDegree K A n q := by
  exact differentialToExterior_presentation K A n q

lemma differentialToExterior_smul (n : ℕ) (a : A) (w : Forms K A n) :
    differentialToExterior K A n (a • w) =
      ExteriorAlgebra.ι A (D K A a) * (w : E K A) +
        a • differentialToExterior K A n w := by
  obtain ⟨q, rfl⟩ := presentationForms_surjective K A n w
  rw [← (presentationForms K A n).map_smul, differentialToExterior_presentation,
    freeDifferentialDegree_smul, differentialToExterior_presentation,
    presentationDegree_eq_subtype_comp, LinearMap.comp_apply]
  rfl

/-- The original scalar-times-differential-wedge formula, in every degree. -/
theorem differential_smul_differentials (n : ℕ) (r : A) (a : Fin n → A) :
    differential K A n (r • exteriorPower.ιMulti A n (fun i => D K A (a i))) =
      exteriorPower.ιMulti A (n + 1) (Fin.cons (D K A r) (fun i => D K A (a i))) := by
  apply Subtype.ext
  have h := differential_presentation_coe K A n
    (Finsupp.single (fun i => D K A (a i)) r)
  have hp : presentationForms K A n (Finsupp.single (fun i => D K A (a i)) r) =
      r • exteriorPower.ιMulti A n (fun i => D K A (a i)) :=
    presentationForms_single K A n _ _
  rw [hp, freeDifferentialDegree_single, tupleDifferential_differentials, smul_zero, add_zero] at h
  rw [h]
  simp [ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]

/-- A pure wedge of universal differentials in the original exterior power. -/
abbrev differentialForm (n : ℕ) (a : Fin n → A) : Forms K A n :=
  exteriorPower.ιMulti A n (fun i => D K A (a i))

lemma differentialForms_span (n : ℕ) :
    Submodule.span A (Set.range (differentialForm K A n)) = ⊤ := by
  classical
  have hset :
      Set.range (fun a : Fin n → A => ExteriorAlgebra.ιMulti A n (fun i => D K A (a i))) =
        ExteriorAlgebra.ιMulti A n ''
          {v : Fin n → W K A | Set.range v ⊆ Set.range (D K A)} := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨fun i => D K A (a i), ?_, rfl⟩
      rintro _ ⟨i, rfl⟩
      exact ⟨a i, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      have h : ∀ i, ∃ a : A, D K A a = v i := fun i => hv ⟨i, rfl⟩
      choose a ha using h
      refine ⟨a, ?_⟩
      exact congrArg (ExteriorAlgebra.ιMulti A n) (funext ha)
  have hspan := exteriorPower.ιMulti_span_fixedDegree_of_span_eq_top A n (W K A)
    (KaehlerDifferential.span_range_derivation K A)
  rw [← hset] at hspan
  apply LinearMap.map_injective (Submodule.ker_subtype (Forms K A n))
  simp only [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
  simpa only [Function.comp_def, differentialForm, Submodule.coe_subtype,
    exteriorPower.ιMulti_apply_coe] using hspan

/-- Additive maps on forms are determined by all scalar-weighted universal differential wedges. -/
theorem additive_ext_differentialForms (n : ℕ) {T : Type*} [AddCommMonoid T]
    (f g : Forms K A n →+ T)
    (h : ∀ (r : A) (a : Fin n → A),
      f (r • differentialForm K A n a) = g (r • differentialForm K A n a)) : f = g := by
  apply AddMonoidHom.ext
  intro w
  have hw : w ∈ Submodule.span A (Set.range (differentialForm K A n)) := by
    rw [differentialForms_span]
    trivial
  have all : ∀ r : A, f (r • w) = g (r • w) := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
    · rintro w ⟨a, rfl⟩ r
      exact h r a
    · intro r
      simp
    · intro x y hx hy ihx ihy r
      rw [smul_add, map_add, map_add, ihx, ihy]
    · intro a x hx ih r
      simpa only [smul_smul] using ih (r * a)
  simpa only [one_smul] using all 1

/-- The actual differential is square-zero in every degree. -/
theorem differential_squared (n : ℕ) (w : Forms K A n) :
    differential K A (n + 1) (differential K A n w) = 0 := by
  have h := additive_ext_differentialForms K A n
    (((differential K A (n + 1)).comp (differential K A n)).toAddMonoidHom)
    (0 : Forms K A n →+ Forms K A ((n + 1) + 1)) (by
      intro r a
      change differential K A (n + 1)
        (differential K A n (r • exteriorPower.ιMulti A n (fun i => D K A (a i)))) = 0
      rw [differential_smul_differentials]
      have hv : Fin.cons (D K A r) (fun i => D K A (a i)) =
          (fun i : Fin (n + 1) => D K A ((Fin.cons r a : Fin (n + 1) → A) i)) := by
        funext i
        induction i using Fin.cases with
        | zero => rfl
        | succ i => rfl
      rw [hv]
      have hnext := differential_smul_differentials K A (n + 1) 1 (Fin.cons r a)
      rw [one_smul] at hnext
      rw [hnext]
      apply Subtype.ext
      simp [ExteriorAlgebra.ιMulti_succ_apply])
  exact DFunLike.congr_fun h w

/-- The canonical graded product on the original exterior-power carriers. -/
abbrev wedge (m n : ℕ) : Forms K A m →ₗ[A] Forms K A n →ₗ[A] Forms K A (m + n) :=
  DirectSum.gMulLHom A (fun i => Forms K A i)

lemma wedge_coe (m n : ℕ) (x : Forms K A m) (y : Forms K A n) :
    (wedge K A m n x y : E K A) = (x : E K A) * (y : E K A) := by
  simp only [wedge, DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul]

lemma wedge_smul_ιMulti (m n : ℕ) (a b : A)
    (u : Fin m → W K A) (v : Fin n → W K A) :
    wedge K A m n (a • exteriorPower.ιMulti A m u) (b • exteriorPower.ιMulti A n v) =
      (a * b) • exteriorPower.ιMulti A (m + n) (Fin.append u v) := by
  apply Subtype.ext
  rw [wedge_coe]
  change (a • ExteriorAlgebra.ιMulti A m u) * (b • ExteriorAlgebra.ιMulti A n v) =
    (a * b) • ExteriorAlgebra.ιMulti A (m + n) (Fin.append u v)
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, ExteriorAlgebra.ιMulti_mul_ιMulti]

lemma differential_smul_ιMulti_coe (n : ℕ) (a : A) (v : Fin n → W K A) :
    (differential K A n (a • exteriorPower.ιMulti A n v) : E K A) =
      ExteriorAlgebra.ι A (D K A a) * ExteriorAlgebra.ιMulti A n v +
        a • tupleDifferential K A n v := by
  have h := differential_presentation_coe K A n (Finsupp.single v a)
  have hp : presentationForms K A n (Finsupp.single v a) = a • exteriorPower.ιMulti A n v :=
    presentationForms_single K A n _ _
  rw [hp, freeDifferentialDegree_single] at h
  exact h

lemma differentialToExterior_smul_ιMulti (n : ℕ) (a : A) (v : Fin n → W K A) :
    differentialToExterior K A n (a • exteriorPower.ιMulti A n v) =
      ExteriorAlgebra.ι A (D K A a) * ExteriorAlgebra.ιMulti A n v +
        a • tupleDifferential K A n v :=
  differential_smul_ιMulti_coe K A n a v

lemma differential_leibniz_smul_ιMulti (m n : ℕ) (a b : A)
    (u : Fin m → W K A) (v : Fin n → W K A) :
    differentialToExterior K A (m + n)
      (wedge K A m n (a • exteriorPower.ιMulti A m u) (b • exteriorPower.ιMulti A n v)) =
      differentialToExterior K A m (a • exteriorPower.ιMulti A m u) *
          (b • ExteriorAlgebra.ιMulti A n v) +
        (-1 : ℤˣ) ^ m •
          ((a • ExteriorAlgebra.ιMulti A m u) *
            differentialToExterior K A n (b • exteriorPower.ιMulti A n v)) := by
  rw [wedge_smul_ιMulti, differentialToExterior_smul_ιMulti,
    differentialToExterior_smul_ιMulti, differentialToExterior_smul_ιMulti,
    tupleDifferential_append]
  rw [← ExteriorAlgebra.ιMulti_mul_ιMulti]
  simp only [Derivation.leibniz, map_add, map_smul, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, smul_add, ← mul_assoc]
  have hs := oneForm_mul_orderedProduct_sign K A (D K A b) (List.ofFn u)
  simp only [orderedProduct_ofFn, List.length_ofFn] at hs
  rw [hs]
  simp only [smul_mul_assoc, smul_smul]
  rw [smul_comm a ((-1 : ℤˣ) ^ m), smul_comm (a * b) ((-1 : ℤˣ) ^ m), mul_comm b a]
  abel

/-- The actual differential satisfies the graded Leibniz rule on all original forms. -/
theorem differential_leibniz (m n : ℕ) (x : Forms K A m) (y : Forms K A n) :
    (differential K A (m + n) (wedge K A m n x y) : E K A) =
      (differential K A m x : E K A) * (y : E K A) +
        (-1 : ℤˣ) ^ m • ((x : E K A) * (differential K A n y : E K A)) := by
  let lhs : Forms K A m →+ (Forms K A n →+ E K A) :=
    { toFun := fun x =>
        { toFun := fun y => differentialToExterior K A (m + n) (wedge K A m n x y)
          map_zero' := by rw [(wedge K A m n x).map_zero, map_zero]
          map_add' := by intro y z; simp only [map_add] }
      map_zero' := by ext y; simp
      map_add' := by
        intro x z
        ext y
        change differentialToExterior K A (m + n) (wedge K A m n (x + z) y) =
          differentialToExterior K A (m + n) (wedge K A m n x y) +
            differentialToExterior K A (m + n) (wedge K A m n z y)
        rw [map_add, LinearMap.add_apply, map_add] }
  let rhs : Forms K A m →+ (Forms K A n →+ E K A) :=
    { toFun := fun x =>
        { toFun := fun y => differentialToExterior K A m x * (y : E K A) +
            (-1 : ℤˣ) ^ m • ((x : E K A) * differentialToExterior K A n y)
          map_zero' := by simp
          map_add' := by
            intro y z
            simp only [map_add, Submodule.coe_add, mul_add, smul_add]
            abel }
      map_zero' := by ext y; simp
      map_add' := by
        intro x z
        ext y
        change differentialToExterior K A m (x + z) * (y : E K A) +
            (-1 : ℤˣ) ^ m • (((x + z : Forms K A m) : E K A) *
              differentialToExterior K A n y) =
          (differentialToExterior K A m x * (y : E K A) +
            (-1 : ℤˣ) ^ m • ((x : E K A) * differentialToExterior K A n y)) +
          (differentialToExterior K A m z * (y : E K A) +
            (-1 : ℤˣ) ^ m • ((z : E K A) * differentialToExterior K A n y))
        simp only [map_add, Submodule.coe_add, add_mul, smul_add]
        abel }
  have h : lhs = rhs := by
    apply additive_ext_differentialForms K A m
    intro a u
    apply additive_ext_differentialForms K A n
    intro b v
    change differentialToExterior K A (m + n)
        (wedge K A m n (a • differentialForm K A m u) (b • differentialForm K A n v)) = _
    exact differential_leibniz_smul_ιMulti K A m n a b
      (fun i => D K A (u i)) (fun i => D K A (v i))
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

section Naturality

universe w
variable (B : Type w) [CommRing B] [Algebra K B] [Algebra A B] [IsScalarTower K A B]

private def exteriorAlternatingRestriction (n : ℕ) :
    (W K B) [⋀^Fin n]→ₗ[A] Forms K B n where
  toMultilinearMap := (exteriorPower.ιMulti B n).toMultilinearMap.restrictScalars A
  map_eq_zero_of_eq' v _i _j hv hij := (exteriorPower.ιMulti B n).map_eq_zero_of_eq v hv hij

/-- The actual exterior-power map along the original algebra map `A → B`. -/
def formsMap (n : ℕ) : Forms K A n →ₗ[A] Forms K B n :=
  exteriorPower.alternatingMapLinearEquiv
    ((exteriorAlternatingRestriction K A B n).compLinearMap (KaehlerDifferential.map K K A B))

lemma formsMap_ιMulti (n : ℕ) (v : Fin n → W K A) :
    formsMap K A B n (exteriorPower.ιMulti A n v) =
      exteriorPower.ιMulti B n (fun i => KaehlerDifferential.map K K A B (v i)) := by
  unfold formsMap
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- Actual change of algebra commutes with left exterior multiplication by every original one-form. -/
theorem formsMap_wedgeLeft (w : Ω[A⁄K]) (n : ℕ) (x : Forms K A n) :
    formsMap K A B (n + 1) (exteriorPower.wedgeLeft A Ω[A⁄K] w n x) =
      exteriorPower.wedgeLeft B Ω[B⁄K] (KaehlerDifferential.map K K A B w) n
        (formsMap K A B n x) := by
  have hx : x ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A n (M := Ω[A⁄K]))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨v, rfl⟩
    rw [exteriorPower.wedgeLeft_apply_ιMulti, formsMap_ιMulti, formsMap_ιMulti,
      exteriorPower.wedgeLeft_apply_ιMulti]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  · rw [map_zero, map_zero, map_zero, map_zero]
  · intro x y _ _ hx hy
    rw [map_add, map_add, map_add, map_add, hx, hy]
  · intro r x _ hx
    rw [map_smul, map_smul, map_smul, hx]
    exact ((exteriorPower.wedgeLeft B Ω[B⁄K] (KaehlerDifferential.map K K A B w) n).restrictScalars A).map_smul
      r (formsMap K A B n x) |>.symm

/-- Change of algebra preserves the original coefficients and universal differential wedges. -/
theorem formsMap_smul_differentialForm (n : ℕ) (r : A) (a : Fin n → A) :
    formsMap K A B n (r • differentialForm K A n a) =
      algebraMap A B r • differentialForm K B n (fun i => algebraMap A B (a i)) := by
  rw [map_smul]
  unfold differentialForm
  rw [formsMap_ιMulti]
  have hv : (fun i => KaehlerDifferential.map K K A B (D K A (a i))) =
      (fun i => D K B (algebraMap A B (a i))) := by
    funext i
    exact KaehlerDifferential.map_D K K A B (a i)
  rw [hv]
  exact (IsScalarTower.algebraMap_smul B r _).symm

/-- The differential commutes with the actual change-of-algebra map in every degree. -/
theorem differential_naturality (n : ℕ) (x : Forms K A n) :
    formsMap K A B (n + 1) (differential K A n x) =
      differential K B n (formsMap K A B n x) := by
  have h := additive_ext_differentialForms K A n
    ((((formsMap K A B (n + 1)).restrictScalars K).comp (differential K A n)).toAddMonoidHom)
    (((differential K B n).comp ((formsMap K A B n).restrictScalars K)).toAddMonoidHom) (by
      intro r a
      change formsMap K A B (n + 1)
        (differential K A n (r • differentialForm K A n a)) =
        differential K B n (formsMap K A B n (r • differentialForm K A n a))
      rw [formsMap_smul_differentialForm]
      unfold differentialForm
      rw [differential_smul_differentials, formsMap_ιMulti, differential_smul_differentials]
      congr 1
      funext i
      induction i using Fin.cases with
      | zero => exact KaehlerDifferential.map_D K K A B r
      | succ i => exact KaehlerDifferential.map_D K K A B (a i))
  exact DFunLike.congr_fun h x

end Naturality

section Absolute

variable (p : ℕ) [Algebra (ZMod p) A]

/-- The canonical coefficient retraction from actual degree-one forms to the Kähler module. -/
def oneFormProjection : Forms ℤ A 1 →ₗ[A] W ℤ A :=
  (ExteriorAlgebra.ιInv (R := A) (M := W ℤ A)).comp (Forms ℤ A 1).subtype

/-- The degree-zero differential followed by the canonical one-form retraction is the universal `D`. -/
theorem oneFormProjection_differential_zero (a : A) :
    oneFormProjection A
      (differential ℤ A 0 (a • differentialForm ℤ A 0 Fin.elim0)) = D ℤ A a := by
  rw [differential_smul_differentials]
  change ExteriorAlgebra.ιInv
    (ExteriorAlgebra.ιMulti A 1 (Fin.cons (D ℤ A a) (fun i => D ℤ A (Fin.elim0 i)))) = _
  simp only [ExteriorAlgebra.ιMulti_succ_apply, Fin.cons_zero,
    ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  exact ExteriorAlgebra.ι_leftInverse _

/-- The original integer-base differential, bundled as a `ZMod p`-linear map. -/
def absoluteDifferential (n : ℕ) : Forms ℤ A n →ₗ[ZMod p] Forms ℤ A (n + 1) where
  toFun := differential ℤ A n
  map_add' x y := map_add _ x y
  map_smul' r x := by
    apply Subtype.ext
    change differentialToExterior ℤ A n (r • x) = r • differentialToExterior ℤ A n x
    rw [← IsScalarTower.algebraMap_smul A r x, differentialToExterior_smul]
    have hr : D ℤ A (algebraMap (ZMod p) A r) = 0 := by
      obtain ⟨z, rfl⟩ := ZMod.intCast_surjective r
      rw [_root_.map_intCast, Derivation.map_intCast]
    rw [hr, map_zero, zero_mul, zero_add]
    exact IsScalarTower.algebraMap_smul A r _

/-- The original absolute degree-zero differential retracts to the universal `D`. -/
theorem oneFormProjection_absolute_zero (a : A) :
    oneFormProjection A
      (absoluteDifferential A p 0 (a • differentialForm ℤ A 0 Fin.elim0)) = D ℤ A a :=
  oneFormProjection_differential_zero A a

/-- The original absolute scalar-wedge differential formula in every degree. -/
theorem absoluteDifferential_smul_differentials (n : ℕ) (r : A) (a : Fin n → A) :
    absoluteDifferential A p n (r • differentialForm ℤ A n a) =
      exteriorPower.ιMulti A (n + 1) (Fin.cons (D ℤ A r) (fun i => D ℤ A (a i))) :=
  differential_smul_differentials ℤ A n r a

theorem absoluteDifferential_squared (n : ℕ) (x : Forms ℤ A n) :
    absoluteDifferential A p (n + 1) (absoluteDifferential A p n x) = 0 :=
  differential_squared ℤ A n x

theorem absoluteDifferential_leibniz (m n : ℕ) (x : Forms ℤ A m) (y : Forms ℤ A n) :
    (absoluteDifferential A p (m + n) (wedge ℤ A m n x y) : E ℤ A) =
      (absoluteDifferential A p m x : E ℤ A) * (y : E ℤ A) +
        (-1 : ℤˣ) ^ m • ((x : E ℤ A) * (absoluteDifferential A p n y : E ℤ A)) :=
  differential_leibniz ℤ A m n x y

theorem absoluteDifferential_naturality {B : Type*} [CommRing B]
    [Algebra (ZMod p) B] [Algebra A B]
    (n : ℕ) (x : Forms ℤ A n) :
    formsMap ℤ A B (n + 1) (absoluteDifferential A p n x) =
      absoluteDifferential B p n (formsMap ℤ A B n x) :=
  differential_naturality ℤ A B n x

end Absolute


/-- The original prime-linear differential retains the actual integer-base differential value. -/
theorem absoluteDifferential_eq_differential (p : ℕ) (A : Type*) [CommRing A] [Algebra (ZMod p) A]
    (n : ℕ) (x : Forms ℤ A n) : absoluteDifferential A p n x = differential ℤ A n x := by
  rfl

end KaehlerDifferential.DeRham
