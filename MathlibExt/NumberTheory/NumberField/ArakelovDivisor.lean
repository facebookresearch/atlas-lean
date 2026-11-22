/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Positive.Field
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.FractionalIdeal.Norm

/-!
# Arakelov divisors of a number field

This file introduces the group of Arakelov divisors of a number field `K`, together with
its size homomorphism, the principal-divisor homomorphism, and the degree-zero subgroup.

An Arakelov divisor is an invertible fractional ideal together with a positive real number
at each infinite place. Its size is the archimedean factor (the finite product over all
infinite places, each value raised to that place's multiplicity) divided by the absolute
norm of the finite (ideal) component. Every principal divisor has size one; the archimedean factor
equals `|Algebra.norm ℚ x|` by `NumberField.InfinitePlace.prod_eq_abs_norm` while the ideal
norm of the principal ideal is the same value by
`FractionalIdeal.absNorm_span_singleton`, so the principal
subgroup lies in the degree-zero subgroup.

Complex-place values in the carrier are ordinary (unsquared) radii: the section set
`ArakelovDivisor.sectionSet` compares `w x` directly against `D.2 w`. The `w.mult = 2`
complex squaring appears only in the size homomorphism, never in the section-set bounds.

## Mathlib conventions

* `w : NumberField.InfinitePlace K` is the absolute value induced by a complex embedding,
  with no extra normalization.
* `w.mult` is `1` at a real place and `2` at a complex place, so that
  `∏ w, w x ^ w.mult = |Algebra.norm ℚ x|`
  (`NumberField.InfinitePlace.prod_eq_abs_norm`).
* `FractionalIdeal.absNorm` of a principal fractional ideal is
  `|Algebra.norm ℚ x|` (`FractionalIdeal.absNorm_span_singleton`).

The two bullets above are the two sides of the product formula; the size-one theorem
below is their combination, not a new normalization.
-/

@[expose] public section

open scoped NumberField nonZeroDivisors

namespace FractionalIdeal

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R]
  [Module.Finite ℤ R]
variable {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]

/-- The absolute norm of an invertible fractional ideal is nonzero. -/
theorem absNorm_units_ne_zero (I : (FractionalIdeal R⁰ F)ˣ) :
    absNorm (I : FractionalIdeal R⁰ F) ≠ 0 := by
  rw [ne_eq, absNorm_eq_zero_iff]
  exact Units.ne_zero I

/-- The absolute norm of an invertible fractional ideal is positive. -/
theorem absNorm_units_pos (I : (FractionalIdeal R⁰ F)ˣ) :
    0 < absNorm (I : FractionalIdeal R⁰ F) :=
  lt_of_le_of_ne (absNorm_nonneg _) (Ne.symm (absNorm_units_ne_zero I))

end FractionalIdeal

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- An Arakelov divisor on a number field: an invertible fractional ideal together with
a positive real at each infinite place. -/
abbrev ArakelovDivisor :=
  (FractionalIdeal (𝓞 K)⁰ K)ˣ × (InfinitePlace K → { r : ℝ // 0 < r })

/-- The natural commutative group structure on Arakelov divisors (pointwise). -/
noncomputable instance : CommGroup (ArakelovDivisor K) := inferInstance

/-- The archimedean factor of an Arakelov divisor: the finite product over all infinite
places of each value raised to that place's multiplicity. -/
noncomputable def ArakelovDivisor.archimedeanFactor (D : ArakelovDivisor K) :
    { r : ℝ // 0 < r } :=
  ∏ w : InfinitePlace K, D.2 w ^ w.mult

open Classical in
/-- Coercion of the archimedean factor to the reals. -/
@[simp]
theorem ArakelovDivisor.archimedeanFactor_coe (D : ArakelovDivisor K) :
    (D.archimedeanFactor : ℝ) = ∏ w : InfinitePlace K, (D.2 w : ℝ) ^ w.mult := by
  have h : ∀ s : Finset (InfinitePlace K),
      ((s.prod (fun w => D.2 w ^ w.mult) : { r : ℝ // 0 < r }) : ℝ) =
        s.prod (fun w => (D.2 w : ℝ) ^ w.mult) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s _ ih
      rw [Finset.prod_insert ‹a ∉ s›, Finset.prod_insert ‹a ∉ s›, Positive.val_mul,
        Positive.val_pow, ih]
  have := h Finset.univ
  simpa [ArakelovDivisor.archimedeanFactor] using this

/-- The absolute norm of the finite (ideal) component, as a positive real. -/
noncomputable def ArakelovDivisor.idealNorm (D : ArakelovDivisor K) :
    { r : ℝ // 0 < r } :=
  ⟨((FractionalIdeal.absNorm (D.1 : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ),
    by
      have h := FractionalIdeal.absNorm_units_pos (R := 𝓞 K) (F := K) D.1
      exact_mod_cast h⟩

/-- Coercion of the ideal norm to the reals. -/
@[simp]
theorem ArakelovDivisor.idealNorm_coe (D : ArakelovDivisor K) :
    (D.idealNorm : ℝ) =
      ((FractionalIdeal.absNorm (D.1 : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ) :=
  rfl

/-- The archimedean factor as a bundled monoid homomorphism. -/
noncomputable def ArakelovDivisor.archHom :
    ArakelovDivisor K →* { r : ℝ // 0 < r } where
  toFun := ArakelovDivisor.archimedeanFactor K
  map_one' := Subtype.ext (by
    change ((ArakelovDivisor.archimedeanFactor K 1 : { r : ℝ // 0 < r }) : ℝ) =
      ((1 : { r : ℝ // 0 < r }) : ℝ)
    rw [ArakelovDivisor.archimedeanFactor_coe, Positive.val_one]
    simp)
  map_mul' D E := Subtype.ext (by
    change ((ArakelovDivisor.archimedeanFactor K (D * E) : { r : ℝ // 0 < r }) : ℝ) =
      ((ArakelovDivisor.archimedeanFactor K D * ArakelovDivisor.archimedeanFactor K E :
        { r : ℝ // 0 < r }) : ℝ)
    rw [ArakelovDivisor.archimedeanFactor_coe, Positive.val_mul,
      ArakelovDivisor.archimedeanFactor_coe, ArakelovDivisor.archimedeanFactor_coe,
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro w _
    rw [Prod.snd_mul, Pi.mul_apply, Positive.val_mul, mul_pow])

/-- The ideal norm as a bundled monoid homomorphism. -/
noncomputable def ArakelovDivisor.idealHom :
    ArakelovDivisor K →* { r : ℝ // 0 < r } where
  toFun := ArakelovDivisor.idealNorm K
  map_one' := Subtype.ext (by
    change ((ArakelovDivisor.idealNorm K 1 : { r : ℝ // 0 < r }) : ℝ) =
      ((1 : { r : ℝ // 0 < r }) : ℝ)
    rw [ArakelovDivisor.idealNorm_coe, Positive.val_one, Prod.fst_one, Units.val_one,
      FractionalIdeal.absNorm_one, Rat.cast_one])
  map_mul' D E := Subtype.ext (by
    change ((ArakelovDivisor.idealNorm K (D * E) : { r : ℝ // 0 < r }) : ℝ) =
      ((ArakelovDivisor.idealNorm K D * ArakelovDivisor.idealNorm K E :
        { r : ℝ // 0 < r }) : ℝ)
    rw [ArakelovDivisor.idealNorm_coe, Positive.val_mul,
      ArakelovDivisor.idealNorm_coe, ArakelovDivisor.idealNorm_coe, Prod.fst_mul,
      Units.val_mul, map_mul, Rat.cast_mul])

/-- The size (norm) homomorphism on Arakelov divisors: the archimedean factor divided
by the absolute norm of the finite component. -/
noncomputable def ArakelovDivisor.sizeHom :
    ArakelovDivisor K →* { r : ℝ // 0 < r } :=
  ArakelovDivisor.archHom K / ArakelovDivisor.idealHom K

/-- The size homomorphism unfolds to the quotient of its two factors. -/
@[simp]
theorem ArakelovDivisor.sizeHom_apply (D : ArakelovDivisor K) :
    ArakelovDivisor.sizeHom K D =
      ArakelovDivisor.archHom K D / ArakelovDivisor.idealHom K D :=
  rfl

/-- Coercion of the size homomorphism to the reals. -/
theorem ArakelovDivisor.sizeHom_coe (D : ArakelovDivisor K) :
    (ArakelovDivisor.sizeHom K D : ℝ) =
      (∏ w : InfinitePlace K, (D.2 w : ℝ) ^ w.mult) /
        ((FractionalIdeal.absNorm (D.1 : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ) := by
  rw [ArakelovDivisor.sizeHom_apply,
    show (ArakelovDivisor.archHom K) D = ArakelovDivisor.archimedeanFactor K D from rfl,
    show (ArakelovDivisor.idealHom K) D = ArakelovDivisor.idealNorm K D from rfl,
    div_eq_mul_inv, Positive.val_mul, Positive.coe_inv,
    ArakelovDivisor.archimedeanFactor_coe, ArakelovDivisor.idealNorm_coe,
    (div_eq_mul_inv _ _).symm]

/-- The section set of an Arakelov divisor: the elements of the finite (ideal)
component bounded by the ordinary archimedean radii at every infinite place.
Complex-place bounds are ordinary (unsquared) radii; the `w.mult = 2` squaring
enters only in the size homomorphism. -/
noncomputable def ArakelovDivisor.sectionSet (D : ArakelovDivisor K) : Set K :=
  { x | x ∈ (D.1 : FractionalIdeal (𝓞 K)⁰ K) ∧
    ∀ w : InfinitePlace K, w x ≤ (D.2 w : ℝ) }

omit [NumberField K] in
/-- Membership in a section set unfolds to the ideal membership plus the
archimedean bounds. -/
@[simp]
theorem ArakelovDivisor.mem_sectionSet (D : ArakelovDivisor K) (x : K) :
    x ∈ D.sectionSet ↔
      x ∈ (D.1 : FractionalIdeal (𝓞 K)⁰ K) ∧
        ∀ w : InfinitePlace K, w x ≤ (D.2 w : ℝ) :=
  Iff.rfl

/-- Every section set of an Arakelov divisor is finite. Clearing denominators by a
nonzero element of `𝓞 K` lands in the ring of integers, and the ordinary-radius
archimedean bounds transfer to uniform bounds on all complex embeddings, so
`NumberField.Embeddings.finite_of_norm_le` applies. -/
theorem ArakelovDivisor.sectionSet_finite (D : ArakelovDivisor K) :
    D.sectionSet.Finite := by
  obtain ⟨d, hd_mem, hden⟩ := (D.1 : FractionalIdeal (𝓞 K)⁰ K).isFractional
  have hd_ne : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd_mem
  have hc_ne : algebraMap (𝓞 K) K d ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd_ne
  obtain ⟨w₀, hw₀⟩ := Set.exists_upper_bound_image Set.univ
    (fun w : InfinitePlace K => ((D.2 w : ℝ))) Set.finite_univ
  obtain ⟨φ₀, hφ₀⟩ := Set.exists_upper_bound_image Set.univ
    (fun φ : K →+* ℂ => ‖φ (algebraMap (𝓞 K) K d)‖) Set.finite_univ
  refine Set.Finite.of_finite_image (f := fun x => algebraMap (𝓞 K) K d * x)
    ((NumberField.Embeddings.finite_of_norm_le K ℂ
      (‖φ₀ (algebraMap (𝓞 K) K d)‖ * ((D.2 w₀ : ℝ)))).subset ?_)
    (mul_right_injective₀ hc_ne).injOn
  intro y hy
  simp only [Set.mem_image] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [ArakelovDivisor.mem_sectionSet] at hx
  obtain ⟨hxI, hxb⟩ := hx
  refine ⟨?_, fun φ => ?_⟩
  · obtain ⟨z, hz⟩ := hden x (FractionalIdeal.mem_coe.mpr hxI)
    rw [Algebra.smul_def] at hz
    exact hz ▸ RingOfIntegers.isIntegral_coe z
  · have hφx : ‖φ x‖ ≤ ((D.2 w₀ : ℝ)) := by
      have h1 : (InfinitePlace.mk φ) x = ‖φ x‖ := rfl
      rw [← h1]
      exact le_trans (hxb (InfinitePlace.mk φ)) (hw₀ _ (Set.mem_univ _))
    rw [map_mul, norm_mul]
    exact mul_le_mul (hφ₀ _ (Set.mem_univ _)) hφx (norm_nonneg _) (norm_nonneg _)

/-- The archimedean component of the principal divisor of a unit. -/
noncomputable def principalArch (x : Kˣ) : InfinitePlace K → { r : ℝ // 0 < r } :=
  fun w => ⟨w (x : K), InfinitePlace.pos_iff.mpr (Units.ne_zero x)⟩

/-- The principal Arakelov divisor of a unit: the principal fractional ideal together
with the archimedean absolute values. -/
noncomputable def principalDivisor (x : Kˣ) : ArakelovDivisor K :=
  (toPrincipalIdeal (𝓞 K) K x, principalArch K x)

/-- Coercion of the infinite component of a principal divisor. -/
@[simp]
theorem coe_principalDivisor_snd (x : Kˣ) (w : InfinitePlace K) :
    (((principalDivisor K x).2 w : { r : ℝ // 0 < r }) : ℝ) = w (x : K) :=
  rfl

/-- The finite component of a principal divisor is the principal fractional ideal. -/
theorem coe_principalDivisor_fst (x : Kˣ) :
    ((principalDivisor K x).1 : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) :=
  coe_toPrincipalIdeal x

/-- The principal-divisor homomorphism from units of `K`. -/
noncomputable def principalHom : Kˣ →* ArakelovDivisor K where
  toFun := principalDivisor K
  map_one' := by
    apply Prod.ext
    · change toPrincipalIdeal (𝓞 K) K 1 = 1
      exact map_one _
    · funext w
      apply Subtype.ext
      change w (((1 : Kˣ) : K)) = ((1 : InfinitePlace K → { r : ℝ // 0 < r }) w : ℝ)
      rw [Units.val_one, Pi.one_apply, Positive.val_one]
      exact map_one w
  map_mul' x y := by
    apply Prod.ext
    · change toPrincipalIdeal (𝓞 K) K (x * y) = _
      rw [map_mul]
      rfl
    · funext w
      apply Subtype.ext
      change w (((x * y : Kˣ) : K)) = ((principalArch K x * principalArch K y) w : ℝ)
      rw [Units.val_mul, Pi.mul_apply, Positive.val_mul]
      exact map_mul w _ _

/-- The subgroup of principal Arakelov divisors. -/
noncomputable def principalSubgroup : Subgroup (ArakelovDivisor K) := (principalHom K).range

/-- The degree-zero subgroup: the kernel of the size homomorphism. -/
noncomputable def degreeZero : Subgroup (ArakelovDivisor K) := (ArakelovDivisor.sizeHom K).ker

/-- Every principal divisor has size one. This is Mathlib's number-field product
formula: the archimedean factor is `|Algebra.norm ℚ x|` by
`NumberField.InfinitePlace.prod_eq_abs_norm`, and the ideal norm of the principal
ideal is the same value by `FractionalIdeal.absNorm_span_singleton`. -/
theorem size_principal (x : Kˣ) : ArakelovDivisor.sizeHom K (principalHom K x) = 1 := by
  have hmap : principalHom K x = principalDivisor K x := rfl
  rw [hmap]
  apply Subtype.ext
  show ((ArakelovDivisor.sizeHom K (principalDivisor K x) : { r : ℝ // 0 < r }) : ℝ) =
    ((1 : { r : ℝ // 0 < r }) : ℝ)
  rw [ArakelovDivisor.sizeHom_coe, Positive.val_one, coe_principalDivisor_fst,
    FractionalIdeal.absNorm_span_singleton]
  have hprod := InfinitePlace.prod_eq_abs_norm (K := K) (x : K)
  simp only [coe_principalDivisor_snd] at hprod ⊢
  rw [← hprod]
  apply div_self
  apply ne_of_gt
  apply Finset.prod_pos
  intro w _
  apply pow_pos
  exact InfinitePlace.pos_iff.mpr (Units.ne_zero x)

/-- The principal subgroup is contained in the degree-zero subgroup. -/
theorem principalSubgroup_le_degreeZero : principalSubgroup K ≤ degreeZero K := by
  rw [principalSubgroup, degreeZero, MonoidHom.range_le_ker_iff]
  exact MonoidHom.ext fun x => size_principal K x

end NumberField
