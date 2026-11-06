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

/-- **Invertible fractional ideals have nonzero absolute norm.** Let $R$ be a Dedekind domain
that is a free $\mathbb{Z}$-module of finite rank, and let $F$ be its field of fractions. For
every invertible fractional ideal $I$ of $R$ in $F$, the absolute norm of $I$, a rational
number, is nonzero. -/
theorem absNorm_units_ne_zero (I : (FractionalIdeal R⁰ F)ˣ) :
    absNorm (I : FractionalIdeal R⁰ F) ≠ 0 := by
  rw [ne_eq, absNorm_eq_zero_iff]
  exact Units.ne_zero I

/-- **Invertible fractional ideals have positive absolute norm.** Let $R$ be a Dedekind domain
that is a free $\mathbb{Z}$-module of finite rank, and let $F$ be its field of fractions. For
every invertible fractional ideal $I$ of $R$ in $F$, the absolute norm of $I$, a rational
number, is positive. -/
theorem absNorm_units_pos (I : (FractionalIdeal R⁰ F)ˣ) :
    0 < absNorm (I : FractionalIdeal R⁰ F) :=
  lt_of_le_of_ne (absNorm_nonneg _) (Ne.symm (absNorm_units_ne_zero I))

end FractionalIdeal

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- **Arakelov divisor.** Let $K$ be a number field with ring of integers $\mathcal{O}_K$. An
Arakelov divisor on $K$ is a pair $(I, r)$, where $I$ is an invertible fractional ideal of
$\mathcal{O}_K$ in $K$ and $r$ assigns a positive real number $r_w$ to each infinite place $w$
of $K$. -/
abbrev ArakelovDivisor :=
  (FractionalIdeal (𝓞 K)⁰ K)ˣ × (InfinitePlace K → { r : ℝ // 0 < r })

/-- The natural commutative group structure on Arakelov divisors (pointwise). -/
noncomputable instance : CommGroup (ArakelovDivisor K) := inferInstance

/-- **Archimedean factor.** Let $D = (I, r)$ be an Arakelov divisor on a number field $K$. Its
archimedean factor is the positive real number $\prod_w r_w^{m_w}$, where the product runs over
all infinite places $w$ of $K$ and $m_w$ is $1$ if $w$ is real and $2$ if $w$ is complex. -/
noncomputable def ArakelovDivisor.archimedeanFactor (D : ArakelovDivisor K) :
    { r : ℝ // 0 < r } :=
  ∏ w : InfinitePlace K, D.2 w ^ w.mult

open Classical in
/-- **Archimedean factor as a real number.** Let $D = (I, r)$ be an Arakelov divisor on a number
field $K$, and for each infinite place $w$ of $K$ let $m_w$ be $1$ if $w$ is real and $2$ if $w$
is complex. Viewed as a real number, the archimedean factor of $D$ equals the real product
$\prod_w r_w^{m_w}$ over all infinite places $w$ of $K$. -/
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

/-- **Ideal norm of an Arakelov divisor.** For an Arakelov divisor $D$ of a number field $K$ with
invertible fractional ideal $I$, the ideal norm of $D$ is the absolute norm $N(I)$ of $I$,
regarded as a positive real number; it is positive because $I$ is invertible. -/
noncomputable def ArakelovDivisor.idealNorm (D : ArakelovDivisor K) :
    { r : ℝ // 0 < r } :=
  ⟨((FractionalIdeal.absNorm (D.1 : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ),
    by
      have h := FractionalIdeal.absNorm_units_pos (R := 𝓞 K) (F := K) D.1
      exact_mod_cast h⟩

/-- **Real value of the ideal norm.** For every Arakelov divisor $D$ of a number field $K$ with
fractional ideal $I$, the ideal norm of $D$, viewed as a real number, equals the absolute norm
$N(I) \in \mathbb{Q}$ of $I$, viewed as a real number. -/
@[simp]
theorem ArakelovDivisor.idealNorm_coe (D : ArakelovDivisor K) :
    (D.idealNorm : ℝ) =
      ((FractionalIdeal.absNorm (D.1 : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ) :=
  rfl

/-- **Archimedean factor homomorphism.** For a number field $K$, the map sending an Arakelov
divisor on $K$ to its archimedean factor is a monoid homomorphism from the Arakelov divisors on
$K$, multiplied componentwise, to the positive real numbers under multiplication. -/
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

/-- **Ideal norm homomorphism.** For a number field $K$, the map sending an Arakelov divisor
$(I, r)$ on $K$ to the absolute norm of $I$, viewed as a positive real number, is a monoid
homomorphism from the Arakelov divisors on $K$, multiplied componentwise, to the positive real
numbers under multiplication. -/
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

/-- **Size of an Arakelov divisor.** For a number field $K$, the size homomorphism sends an
Arakelov divisor $D = (I, (r_w)_w)$, with $I$ an invertible fractional ideal of the ring of
integers of $K$ and $r_w > 0$ for each infinite place $w$, to the positive real number
$\prod_w r_w^{m_w} / N(I)$, where $w$ runs over the infinite places of $K$, $m_w$ is $1$ for a
real place and $2$ for a complex place, and $N(I)$ is the absolute norm of $I$. It is a group
homomorphism from Arakelov divisors to the multiplicative group of positive reals. -/
noncomputable def ArakelovDivisor.sizeHom :
    ArakelovDivisor K →* { r : ℝ // 0 < r } :=
  ArakelovDivisor.archHom K / ArakelovDivisor.idealHom K

/-- **Size as a quotient of homomorphisms.** For every Arakelov divisor $D$ of a number field
$K$, the size of $D$ equals the archimedean-factor homomorphism evaluated at $D$ divided by the
ideal-norm homomorphism evaluated at $D$, the quotient taken in the group of positive reals. -/
@[simp]
theorem ArakelovDivisor.sizeHom_apply (D : ArakelovDivisor K) :
    ArakelovDivisor.sizeHom K D =
      ArakelovDivisor.archHom K D / ArakelovDivisor.idealHom K D :=
  rfl

/-- **Explicit formula for the size of an Arakelov divisor.** Let $D = (I, (r_w)_w)$ be an
Arakelov divisor of a number field $K$, where $I$ is an invertible fractional ideal of the ring
of integers of $K$ and $r_w > 0$ for each infinite place $w$ of $K$. For each $w$ let $m_w$ be
$1$ if $w$ is real and $2$ if $w$ is complex, and let $N(I)$ be the absolute norm of $I$. Then
the size of $D$, as a real number, is
$$\frac{\prod_w r_w^{m_w}}{N(I)},$$
where the product runs over all infinite places $w$ of $K$. -/
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

/-- **Section set of an Arakelov divisor.** Let $D$ be an Arakelov divisor of a number field $K$,
with invertible fractional ideal $I$ and positive real number $r_w$ at each infinite place $w$
of $K$. The section set of $D$ is the set of $x \in I$ such that $w(x) \le r_w$ for every
infinite place $w$ of $K$.

At a complex place the bound is on $w(x)$ itself, not on $w(x)^2$; the squaring at complex
places enters only in the size of $D$. -/
noncomputable def ArakelovDivisor.sectionSet (D : ArakelovDivisor K) : Set K :=
  { x | x ∈ (D.1 : FractionalIdeal (𝓞 K)⁰ K) ∧
    ∀ w : InfinitePlace K, w x ≤ (D.2 w : ℝ) }

/-- **Membership in the section set.** Let $D$ be an Arakelov divisor of a number field $K$, with
invertible fractional ideal $I$ and positive real number $r_w$ at each infinite place $w$ of $K$.
An element $x \in K$ lies in the section set of $D$ if and only if $x \in I$ and
$w(x) \le r_w$ for every infinite place $w$ of $K$. -/
@[simp]
theorem ArakelovDivisor.mem_sectionSet (D : ArakelovDivisor K) (x : K) :
    x ∈ D.sectionSet ↔
      x ∈ (D.1 : FractionalIdeal (𝓞 K)⁰ K) ∧
        ∀ w : InfinitePlace K, w x ≤ (D.2 w : ℝ) :=
  Iff.rfl

/-- **Finiteness of section sets.** For every Arakelov divisor $D$ of a number field $K$, the
section set of $D$ is finite.

Multiplying by a nonzero $d \in \mathcal{O}_K$ that clears the denominators of the fractional
ideal of $D$ sends the section set into $\mathcal{O}_K$, and the bounds at the infinite places
give a uniform bound $B$ on $|\sigma(dx)|$ for all $x$ in the section set and all complex
embeddings $\sigma$ of $K$; only finitely many algebraic integers of $K$ have all conjugates of
absolute value at most $B$. -/
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

/-- **Archimedean part of a principal divisor.** For a nonzero element $x$ of a number field $K$,
this is the family that assigns to each infinite place $w$ of $K$ the positive real
number $w(x)$. -/
noncomputable def principalArch (x : Kˣ) : InfinitePlace K → { r : ℝ // 0 < r } :=
  fun w => ⟨w (x : K), InfinitePlace.pos_iff.mpr (Units.ne_zero x)⟩

/-- **Principal Arakelov divisor.** For a nonzero element $x$ of a number field $K$, the principal
Arakelov divisor of $x$ consists of the principal fractional ideal $x\mathcal{O}_K$ together with
the positive real number $w(x)$ at each infinite place $w$ of $K$. -/
noncomputable def principalDivisor (x : Kˣ) : ArakelovDivisor K :=
  (toPrincipalIdeal (𝓞 K) K x, principalArch K x)

/-- **Infinite component of a principal divisor.** Let $K$ be a number field, $x \in K$ nonzero
and $w$ an infinite place of $K$. The positive real number that the principal Arakelov divisor
of $x$ assigns to $w$ is $w(x)$, the absolute value of $x$ at $w$. -/
@[simp]
theorem coe_principalDivisor_snd (x : Kˣ) (w : InfinitePlace K) :
    (((principalDivisor K x).2 w : { r : ℝ // 0 < r }) : ℝ) = w (x : K) :=
  rfl

/-- **Finite component of a principal divisor.** Let $K$ be a number field with ring of integers
$\mathcal{O}_K$. For every nonzero $x \in K$, the fractional ideal component of the principal
Arakelov divisor of $x$ is the principal fractional ideal $x\mathcal{O}_K$. -/
theorem coe_principalDivisor_fst (x : Kˣ) :
    ((principalDivisor K x).1 : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) :=
  coe_toPrincipalIdeal x

/-- **Principal divisor homomorphism.** For a number field $K$, the map sending a nonzero element
$x \in K$ to its principal Arakelov divisor is a group homomorphism from the multiplicative
group $K^\times$ to the group of Arakelov divisors of $K$. -/
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

/-- **Subgroup of principal Arakelov divisors.** For a number field $K$, the principal subgroup is
the image of the principal divisor homomorphism, that is, the subgroup of the group of Arakelov
divisors of $K$ consisting of the principal Arakelov divisors of the nonzero elements of $K$. -/
noncomputable def principalSubgroup : Subgroup (ArakelovDivisor K) := (principalHom K).range

/-- **Degree-zero Arakelov divisors.** For a number field $K$, the degree-zero subgroup of the
group of Arakelov divisors on $K$ is the kernel of the size homomorphism, that is, the subgroup
of Arakelov divisors of size $1$. -/
noncomputable def degreeZero : Subgroup (ArakelovDivisor K) := (ArakelovDivisor.sizeHom K).ker

/-- **Principal Arakelov divisors have size one.** Let $K$ be a number field with ring of
integers $\mathcal{O}_K$. For every nonzero $x \in K$, the principal Arakelov divisor of $x$,
formed by the principal fractional ideal $x\mathcal{O}_K$ and the values $w(x)$ at the infinite
places $w$ of $K$, has size $1$.

This is the product formula: with $m_w$ equal to $1$ at real and $2$ at complex places, the
archimedean factor $\prod_w w(x)^{m_w}$ equals $|N_{K/\mathbb{Q}}(x)|$, where $N_{K/\mathbb{Q}}$
is the field norm from $K$ to $\mathbb{Q}$, and so does the absolute norm of $x\mathcal{O}_K$. -/
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

/-- **Principal Arakelov divisors have degree zero.** For a number field $K$, the subgroup of
principal Arakelov divisors of $K$ is contained in the degree-zero subgroup. -/
theorem principalSubgroup_le_degreeZero : principalSubgroup K ≤ degreeZero K := by
  rw [principalSubgroup, degreeZero, MonoidHom.range_le_ker_iff]
  exact MonoidHom.ext fun x => size_principal K x

end NumberField
