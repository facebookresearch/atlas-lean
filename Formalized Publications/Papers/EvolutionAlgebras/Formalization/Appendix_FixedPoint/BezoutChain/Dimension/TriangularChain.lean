/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Statement.GenericLinear
import Appendix_FixedPoint.BezoutChain.Dimension.IntegralDimension
import Appendix_FixedPoint.BezoutChain.Dimension.PolynomialCatenary
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Finsupp.Single
import Mathlib.Order.KrullDimension
import Mathlib.Order.RelSeries
import Mathlib.Order.WithBot
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Spectrum.Prime.Defs

/-!
# Triangular monic chain below a prime
For `R = MvPolynomial (Fin m) K` with `[Field K] [Infinite K]` and prime `P`,
this file attacks the sole remainder of the former
`Formalization/Appendix_FixedPoint/BezoutChain/Dimension/PolyCatenaryNorm.lean`
(file removed), namely
```
(hheight) (((m - s: ℕ)): WithBot ℕ∞) ≤ (P.height: WithBot ℕ∞),
```
a length-`(m - s)` prime chain below `P`, via a triangular automorphism made
monic in a distinguished (last) variable.

## Route

1. A shear automorphism `triShear j d` (`Xᵢ ↦ Xᵢ + Xⱼ ^ dᵢ` for `i ≠ j`,
   `Xⱼ ↦ Xⱼ`) is built as a `K`-algebra equivalence with its back-substitution
   inverse, triangular action, and monic-shift coefficient (`1` at
   `Xⱼ ^ dᵢ`). The distinguished index `j` plays the role of the last variable:
   every other generator maps to itself plus a polynomial in `Xⱼ` alone.
2. The Noether-normalization input (`s`, injective integral
   `g : MvPolynomial (Fin s) K →ₐ[K] R ⧸ P`), the generic-linear-form input
   (from `GenericLinear`), the triangular data, a weakened-fiber hypothesis
   (monic-in-`Xⱼ` without univariateness, in the shear contraction, plus the
   going-down integrality input), and exactly one explicit exhibit (a
   length-`(m - s)` prime series in `R` ending at `P`) are bundled as
   `TriangularNormDatum` (`hnorm`).
3. From the Noether datum, base prime chains lift through the integral map by
   lying-over plus going-up (`lift_chain_through_normalization`,
   `lift_base_chain`).
4. The main theorem `triangular_monic_chain` assembles the target shape:
   the exhibit series converts to the height bound via
   `Order.length_le_height_last`, in the exact form consumed by
   `height_of_dpow_datum`.

## What this file proves

* `shearFwd` / `shearBwd`: the forward/backward triangular `K`-algebra homs.
* `shearFwd_apply` / `shearBwd_apply`: their action on generators.
* `triShear`: the shear as `MvPolynomial (Fin m) K ≃ₐ[K] _` (part (i)).
* `triShear_apply` / `triShear_fixes` / `triShear_backsubst`: triangular action,
  fixed last variable, back-substitution (part (i)).
* `triShear_coeff_shift`: monic-shift property — the `Xⱼ ^ dᵢ`-coefficient of
  `σ (Xᵢ)` is `1` for `i ≠ j` (part (i), monic property).
* `TriangularNormDatum`: the precisely formulated `hnorm` (Noether datum with
  `s` generators + generic-linear-form input + triangular data + weakened
  fiber hypothesis + one explicit exhibit).
* `shearContraction` / `delVarQuot`: the contraction of `P` along the inverse
  shear (the prime holding the fiber witness) and the delete-`j` inclusion
  into a quotient (whose integrality is the going-down input).
* `normap_of_prime`: the Noether part of `hnorm` is always dischargeable.
* `dir_of_finset`: the linear-form part of `hnorm` is always dischargeable
  (via `GenericLinear`).
* `quotient_dim_of_normap`: the Noether datum pins `ringKrullDim (R ⧸ P) = s`
  (via the `IntegralDimension`/`PolynomialCatenary` toolbox).
* `liesOver_of_normalization` / `lift_chain_through_normalization` /
  `lift_base_chain`: base chains lift through the normalization by lying-over
  plus going-up (part (ii), the lift half).
* `triangular_monic_chain`: the exact target shape, from `hnorm`
  (part (ii), assembly).

## Adjustments

* `hnorm` is formulated as the bundled structure `TriangularNormDatum`
  rather than a bare `∃ T : Subalgebra...`: the Noether datum is an
  injective integral `AlgHom` (the output shape of
  `exists_integral_inj_algHom_of_quotient`, matching
  `dim_quotient_eq_normalization_index`), the `monic_direction_exists` input
  is stored as `(bad, dir, dir_ne)`, and the triangular automorphism plus its
  monic criterion appear as `(shear_idx, shear_exp, adm, fiber)`.
* The main theorem consumes the exhibit field for the height bound; the
  Noether/triangular fields pin the interface for the next attempt, which
  must derive the exhibit from them (see `## Obstruction`). No field is
  vacuous: `normap_of_prime`, `dir_of_finset` discharge the always-available
  parts, and `quotient_dim_of_normap` plus the lift theorems consume the
  Noether datum.
* `TriangularRegularity` (`t1`+`t2` z-linearity) is reused by reference, not
  re-proved: no `triG` fact is re-established here; the monic-fiber division
  step of the down-route is deferred to its back-substitution API (see
  `## Obstruction`). It is cited, not imported (narrow imports).
* The lift theorems take the `A`-algebra structure on `R ⧸ P` as an instance
  parameter plus `hmap : algebraMap _ _ = g.toRingHom` (stating `LiesOver`
  needs the instance, so it cannot be built inside the proof). The consumer
  supplies `g.toRingHom.toAlgebra` with `RingHom.algebraMap_toAlgebra`.
* Namespace deviation: bare `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain` does not mirror the
  module path, deliberately matching every other Track-B chunk file for
  consumer compatibility (same convention as the former `PolyCatenaryNorm`).
* Weakened `fiber` (reformulation attempt 1): the univariate-off-`j`
  requirement is dropped — `FiberExhibit.lean` refutes it (`fiberPred_false_span_sub`:
  for `P = span {X₀ − X₁}` no `j` admits a nonzero univariate-off-`j` element,
  and the shear, which fixes `Xⱼ`, cannot repair this). The replacement asks
  for a nonzero element of the shear contraction `shearContraction j d P`,
  monic in `Xⱼ` (degree pinned with coefficient `1`) but not necessarily
  univariate, plus integrality of the contracted quotient over the delete-`j`
  base (`delVarQuot`). This is principled, not a hack: the down-route needs
  integrality (going-down consumes integral input), and monic-not-univariate
  plus integrality is exactly the classical Noether-normalization vehicle.

## References

* `Formalization/Appendix_FixedPoint/BezoutChain/
  Dimension/PolynomialCatenary.lean`,
  `mvPolynomial_ringKrullDim`, `dim_quotient_eq_normalization_index`.
* `Formalization/Appendix_FixedPoint/BezoutChain/
  Dimension/IntegralDimension.lean`,
  `ringKrullDim_eq_of_algHom_isIntegral`, `ringKrullDim_eq_of_isIntegral`.
* `Formalization/Appendix_FixedPoint/BezoutChain/Statement/GenericLinear.lean`,
  `exists_linearForm_ne_zero_on_finset`.
* `Formalization/Appendix_FixedPoint/BezoutChain/
  Regularity/Avoid/TriangularRegularity.lean`,
  `triG_ne_zero`, `triG_natDegree`, `triG_isSMulRegular_mod_of_dvd`
  (back-substitution template for the monic-fiber step; cited, not imported).
* `Mathlib/RingTheory/Ideal/HasGoingUp.lean`,
  `Ideal.exists_ltSeries_of_hasGoingUp`,
  `Algebra.HasGoingUp.of_isIntegral`.
* `Mathlib/RingTheory/Ideal/GoingUp.lean`,
  `Ideal.exists_ideal_over_prime_of_isIntegral`.
* `Mathlib/RingTheory/NoetherNormalization.lean`,
  `exists_integral_inj_algHom_of_quotient`.
* `Mathlib/Order/KrullDimension.lean`, `Order.length_le_height_last`.
* `Mathlib/RingTheory/Ideal/Height.lean`,
  `PrimeSpectrum.height_eq_orderHeight`.
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.algHom_ext`,
  `MvPolynomial.coeff_add`, `MvPolynomial.coeff_X`,
  `MvPolynomial.coeff_X_pow`.
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.aeval`,
  `MvPolynomial.aeval_X`.
* `Mathlib/Algebra/MvPolynomial/Rename.lean`, `MvPolynomial.rename`
  (the delete-`j` inclusion inside `delVarQuot`).
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `Ideal.Quotient.mkₐ` (the quotient leg of `delVarQuot`).
* `Mathlib/Algebra/MvPolynomial/Degrees.lean`, `MvPolynomial.degreeOf`.
* `Mathlib/Data/Finsupp/Single.lean`, `Finsupp.single_eq_of_ne`,
  `Finsupp.single_eq_same`.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-! ## (i) The triangular shear automorphism. -/

/-- Forward triangular shear hom: `Xᵢ ↦ Xᵢ + Xⱼ ^ dᵢ` for `i ≠ j`, fixing the
distinguished (last) variable `Xⱼ`. Triangular for the order with `j` maximal:
each generator maps to itself plus a polynomial in the later variable `Xⱼ`
alone. -/
noncomputable def shearFwd {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) : MvPolynomial (Fin m) K →ₐ[K] MvPolynomial (Fin m) K :=
  MvPolynomial.aeval (R := K) (S₁ := MvPolynomial (Fin m) K) (σ := Fin m)
    fun i => if i = j then MvPolynomial.X j
      else MvPolynomial.X i + MvPolynomial.X j ^ d i

/-- Backward triangular shear hom (back-substitution): `Xᵢ ↦ Xᵢ − Xⱼ ^ dᵢ`
for `i ≠ j`, fixing `Xⱼ`. -/
noncomputable def shearBwd {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) : MvPolynomial (Fin m) K →ₐ[K] MvPolynomial (Fin m) K :=
  MvPolynomial.aeval (R := K) (S₁ := MvPolynomial (Fin m) K) (σ := Fin m)
    fun i => if i = j then MvPolynomial.X j
      else MvPolynomial.X i - MvPolynomial.X j ^ d i

/-- Action of the forward shear on generators. -/
theorem shearFwd_apply {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) (i : Fin m) :
    shearFwd (K := K) j d (MvPolynomial.X i) =
      (if i = j then MvPolynomial.X j
        else MvPolynomial.X i + MvPolynomial.X j ^ d i) := by
  simp only [shearFwd, MvPolynomial.aeval_X]

/-- Action of the backward shear on generators. -/
theorem shearBwd_apply {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) (i : Fin m) :
    shearBwd (K := K) j d (MvPolynomial.X i) =
      (if i = j then MvPolynomial.X j
        else MvPolynomial.X i - MvPolynomial.X j ^ d i) := by
  simp only [shearBwd, MvPolynomial.aeval_X]

/-- The triangular shear automorphism: the forward and backward shears are
mutually inverse (the `aeval` round-trip is checked on generators by
`sub_add_cancel` / `abel`). -/
noncomputable def triShear {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) :
    MvPolynomial (Fin m) K ≃ₐ[K] MvPolynomial (Fin m) K where
  toFun := shearFwd (K := K) j d
  invFun := shearBwd (K := K) j d
  left_inv := by
    intro x
    show shearBwd (K := K) j d (shearFwd (K := K) j d x) = x
    have hcomp : (shearBwd (K := K) j d).comp (shearFwd (K := K) j d) =
        AlgHom.id K _ := by
      apply MvPolynomial.algHom_ext
      intro i
      by_cases h : i = j
      · subst h
        simp [AlgHom.comp_apply, shearFwd_apply, shearBwd_apply]
      · rw [AlgHom.comp_apply, shearFwd_apply, ite_eq_right h, map_add,
          shearBwd_apply, ite_eq_right h, map_pow, shearBwd_apply, ite_eq_left rfl,
          sub_add_cancel, AlgHom.id_apply]
    calc shearBwd (K := K) j d (shearFwd (K := K) j d x)
        = ((shearBwd (K := K) j d).comp (shearFwd (K := K) j d)) x := rfl
      _ = x := by rw [hcomp]; rfl
  right_inv := by
    intro x
    show shearFwd (K := K) j d (shearBwd (K := K) j d x) = x
    have hcomp : (shearFwd (K := K) j d).comp (shearBwd (K := K) j d) =
        AlgHom.id K _ := by
      apply MvPolynomial.algHom_ext
      intro i
      by_cases h : i = j
      · subst h
        simp [AlgHom.comp_apply, shearFwd_apply, shearBwd_apply]
      · rw [AlgHom.comp_apply, shearBwd_apply, ite_eq_right h, map_sub,
          shearFwd_apply, ite_eq_right h, map_pow, shearFwd_apply,
          ite_eq_left rfl, AlgHom.id_apply]
        abel
    calc shearFwd (K := K) j d (shearBwd (K := K) j d x)
        = ((shearFwd (K := K) j d).comp (shearBwd (K := K) j d)) x := rfl
      _ = x := by rw [hcomp]; rfl
  map_mul' := fun x y => map_mul _ x y
  map_add' := fun x y => map_add _ x y
  commutes' := fun r => (shearFwd j d).commutes r

/-- Triangular action of the shear automorphism on generators. -/
theorem triShear_apply {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) (i : Fin m) :
    triShear (K := K) j d (MvPolynomial.X i) =
      (if i = j then MvPolynomial.X j
        else MvPolynomial.X i + MvPolynomial.X j ^ d i) :=
  shearFwd_apply (K := K) j d i

/-- The shear fixes the distinguished (last) variable. -/
theorem triShear_fixes {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) :
    triShear (K := K) j d (MvPolynomial.X j) = MvPolynomial.X j := by
  rw [triShear_apply, ite_eq_left rfl]

/-- Back-substitution: the inverse shear sends `Xᵢ` to `Xᵢ − Xⱼ ^ dᵢ`. -/
theorem triShear_backsubst {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) (i : Fin m) (hij : i ≠ j) :
    (triShear (K := K) j d).symm (MvPolynomial.X i) =
      MvPolynomial.X i - MvPolynomial.X j ^ d i := by
  change shearBwd (K := K) j d (MvPolynomial.X i) =
    MvPolynomial.X i - MvPolynomial.X j ^ d i
  rw [shearBwd_apply, ite_eq_right hij]

/-- Monic-shift property: for `i ≠ j` with `dᵢ ≠ 0`, the `Xⱼ ^ dᵢ`-coefficient
of the sheared generator `σ (Xᵢ)` is `1`. The `Xᵢ`-summand cannot contribute
there (its exponent vector `single i 1` differs from `single j dᵢ` at `j`),
while the `Xⱼ ^ dᵢ`-summand contributes exactly `1`. -/
theorem triShear_coeff_shift {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) (i : Fin m) (hij : i ≠ j) (hd : d i ≠ 0) :
    (triShear (K := K) j d (MvPolynomial.X i)).coeff
      (Finsupp.single j (d i)) = 1 := by
  have hne : Finsupp.single i (1 : ℕ) ≠ Finsupp.single j (d i) := by
    intro heq
    have h := congrArg (fun a : Fin m →₀ ℕ => a j) heq
    rw [Finsupp.single_eq_of_ne (Ne.symm hij), Finsupp.single_eq_same] at h
    exact hd h.symm
  rw [triShear_apply, ite_eq_right hij, AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply, MvPolynomial.coeff_X,
    MvPolynomial.coeff_X_pow, ite_eq_right hne, ite_eq_left rfl, zero_add]

/-- Contraction of `P` along the inverse shear: `f ∈ shearContraction j d P`
means `σ⁻¹(f) ∈ P` for `σ := triShear j d`. This is the prime in which the
weakened fiber witness lives: the witness is `σ(g)` for `g ∈ P`, i.e. an
element of `σ(P) = comap σ⁻¹ P`. Since the shear fixes `Xⱼ`, no univariate
repair is possible (see `## Obstruction`); the witness is monic in `Xⱼ`
without being univariate. -/
noncomputable def shearContraction {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) (P : Ideal (MvPolynomial (Fin m) K)) :
    Ideal (MvPolynomial (Fin m) K) :=
  P.comap (triShear (K := K) j d).symm.toAlgHom.toRingHom

/-- The delete-`j` inclusion into a quotient: variables other than `j` map via
`rename Subtype.val`, then down to `R ⧸ Q`. The fiber integrality field states
that this canonical map is integral — exactly the input going-down consumes
(integral extension over the `(m - 1)`-variable base, the classical vehicle). -/
noncomputable def delVarQuot {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (Q : Ideal (MvPolynomial (Fin m) K)) :
    MvPolynomial {i : Fin m // i ≠ j} K →ₐ[K] MvPolynomial (Fin m) K ⧸ Q :=
  (Ideal.Quotient.mkₐ K Q).comp (MvPolynomial.rename (fun i => (i : Fin m)))

/-! ## (ii) The normalization datum, the lift, and the assembly. -/

/-- Noether-normalization + triangular-monic datum (`hnorm`): the
normalization index `s ≤ m` with an injective integral normalization map
(the `s` generators), a generic linear form nonzero on a prescribed finite
bad set (the `monic_direction_exists` input), the triangular shear data with
admissible exponents, the weakened fiber hypothesis (a nonzero element of the
shear contraction of `P`, monic — degree pinned with coefficient `1` — in the
distinguished variable but not necessarily univariate, plus integrality of the
contracted quotient over the delete-`j` base, the going-down input), and
exactly one explicit exhibit: a length-`(m - s)` prime series in `R` ending
at `P`. -/
structure TriangularNormDatum (m s : ℕ) (K : Type*) [Field K] [Infinite K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] where
  s_le : s ≤ m
  normap : MvPolynomial (Fin s) K →ₐ[K] MvPolynomial (Fin m) K ⧸ P
  normap_inj : Function.Injective normap
  normap_int : normap.IsIntegral
  bad : Finset (Fin m → K)
  dir : (Fin m → K) →ₗ[K] K
  dir_ne : ∀ v ∈ bad, dir v ≠ 0
  shear_idx : Fin m
  shear_exp : Fin m → ℕ
  adm : ∀ i : Fin m, i ≠ shear_idx → shear_exp i ≠ 0
  fiber : P ≠ ⊥ → (∃ f : MvPolynomial (Fin m) K,
    f ∈ shearContraction shear_idx shear_exp P ∧ f ≠ 0 ∧
    ∃ e : ℕ, e ≠ 0 ∧ f.degreeOf shear_idx = e ∧
      f.coeff (Finsupp.single shear_idx e) = 1) ∧
    (delVarQuot shear_idx (shearContraction shear_idx shear_exp P)).IsIntegral
  exhibit : ∃ l : LTSeries (PrimeSpectrum (MvPolynomial (Fin m) K)),
    l.length = m - s ∧ l.last = ⟨P, ‹P.IsPrime›⟩

/-- The Noether part of `hnorm` is always dischargeable: Noether normalization
presents `R ⧸ P` as integral over `MvPolynomial (Fin s) K` for some `s ≤ m`. -/
theorem normap_of_prime (m : ℕ) (K : Type*) [Field K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] :
    ∃ s ≤ m, ∃ g : MvPolynomial (Fin s) K →ₐ[K]
      (MvPolynomial (Fin m) K ⧸ P), Function.Injective g ∧ g.IsIntegral := by
  have hne : P ≠ ⊤ := Ideal.IsPrime.ne_top ‹P.IsPrime›
  exact exists_integral_inj_algHom_of_quotient P hne

/-- The linear-form part of `hnorm` is always dischargeable: over infinite
`K`, some linear form is nonzero on every prescribed nonzero vector (the
`monic_direction_exists` input, via `GenericLinear`). -/
theorem dir_of_finset (m : ℕ) (K : Type*) [Field K] [Infinite K]
    (S : Finset (Fin m → K)) (hS : ∀ v ∈ S, v ≠ 0) :
    ∃ l : (Fin m → K) →ₗ[K] K, ∀ v ∈ S, l v ≠ 0 :=
  exists_linearForm_ne_zero_on_finset S hS

/-- The Noether datum pins the quotient dimension: an injective integral
`g : A →ₐ[K] R ⧸ P` forces `ringKrullDim (R ⧸ P) = s` (via the
`IntegralDimension`/`PolynomialCatenary` toolbox). -/
theorem quotient_dim_of_normap (m s : ℕ) (K : Type*) [Field K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (g : MvPolynomial (Fin s) K →ₐ[K] MvPolynomial (Fin m) K ⧸ P)
    (hinj : Function.Injective g) (hint : g.IsIntegral) :
    ringKrullDim (MvPolynomial (Fin m) K ⧸ P) = ((s : ℕ) : WithBot ℕ∞) := by
  rw [ringKrullDim_eq_of_algHom_isIntegral g hinj hint, mvPolynomial_ringKrullDim]

/-- Lying-over through the normalization: every head prime of a base chain in
`MvPolynomial (Fin s) K` is hit by a prime of `R ⧸ P` (lying-over at
`⊥ ≤ head`; no faithful-flatness input needed). -/
theorem liesOver_of_normalization (m s : ℕ) (K : Type*) [Field K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (g : MvPolynomial (Fin s) K →ₐ[K] MvPolynomial (Fin m) K ⧸ P)
    (hinj : Function.Injective g) (hint : g.IsIntegral)
    (l : LTSeries (PrimeSpectrum (MvPolynomial (Fin s) K)))
    [Algebra (MvPolynomial (Fin s) K) (MvPolynomial (Fin m) K ⧸ P)]
    (hmap : algebraMap (MvPolynomial (Fin s) K) (MvPolynomial (Fin m) K ⧸ P) =
      g.toRingHom) :
    ∃ Q : Ideal (MvPolynomial (Fin m) K ⧸ P),
      Q.IsPrime ∧ Q.LiesOver (RelSeries.head l).asIdeal := by
  have hInt : Algebra.IsIntegral (MvPolynomial (Fin s) K)
      (MvPolynomial (Fin m) K ⧸ P) := by
    rw [← algebraMap_isIntegral_iff, hmap]
    exact hint
  have hfaith : FaithfulSMul (MvPolynomial (Fin s) K)
      (MvPolynomial (Fin m) K ⧸ P) := by
    rw [faithfulSMul_iff_algebraMap_injective, hmap]
    exact hinj
  have hbot : (⊥ : Ideal (MvPolynomial (Fin m) K ⧸ P)).under
      (MvPolynomial (Fin s) K) ≤ (RelSeries.head l).asIdeal := by
    rw [Ideal.under_bot]
    exact bot_le
  obtain ⟨Q, -, hQprime, hQunder⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (RelSeries.head l).asIdeal ⊥
      hbot
  exact ⟨Q, hQprime, ⟨hQunder.symm⟩⟩

/-- Going-up lift through the normalization: a base prime chain in
`MvPolynomial (Fin s) K` lifts to a same-length prime chain in `R ⧸ P`
starting at any prime lying over the base head (the `IntegralDimension` going-up
toolbox: `Algebra.HasGoingUp.of_isIntegral` supplies the instance).
`_hinj` is semantically redundant (the lift needs only integrality) and is
kept for call-site uniformity with `lift_base_chain`. -/
theorem lift_chain_through_normalization (m s : ℕ) (K : Type*) [Field K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (g : MvPolynomial (Fin s) K →ₐ[K] MvPolynomial (Fin m) K ⧸ P)
    (_hinj : Function.Injective g) (hint : g.IsIntegral)
    (l : LTSeries (PrimeSpectrum (MvPolynomial (Fin s) K)))
    [Algebra (MvPolynomial (Fin s) K) (MvPolynomial (Fin m) K ⧸ P)]
    (Q : Ideal (MvPolynomial (Fin m) K ⧸ P)) [Q.IsPrime]
    [Q.LiesOver (RelSeries.head l).asIdeal]
    (hmap : algebraMap (MvPolynomial (Fin s) K) (MvPolynomial (Fin m) K ⧸ P) =
      g.toRingHom) :
    ∃ L : LTSeries (PrimeSpectrum (MvPolynomial (Fin m) K ⧸ P)),
      L.length = l.length ∧ L.head = ⟨Q, ‹Q.IsPrime›⟩ := by
  have hInt : Algebra.IsIntegral (MvPolynomial (Fin s) K)
      (MvPolynomial (Fin m) K ⧸ P) := by
    rw [← algebraMap_isIntegral_iff, hmap]
    exact hint
  obtain ⟨L, hlen, hhead, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l Q
  exact ⟨L, hlen, hhead⟩

/-- Assembled lift: every base prime chain lifts to a same-length chain in
`R ⧸ P` lying over the base head. -/
theorem lift_base_chain (m s : ℕ) (K : Type*) [Field K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (g : MvPolynomial (Fin s) K →ₐ[K] MvPolynomial (Fin m) K ⧸ P)
    (hinj : Function.Injective g) (hint : g.IsIntegral)
    (l : LTSeries (PrimeSpectrum (MvPolynomial (Fin s) K)))
    [Algebra (MvPolynomial (Fin s) K) (MvPolynomial (Fin m) K ⧸ P)]
    (hmap : algebraMap (MvPolynomial (Fin s) K) (MvPolynomial (Fin m) K ⧸ P) =
      g.toRingHom) :
    ∃ L : LTSeries (PrimeSpectrum (MvPolynomial (Fin m) K ⧸ P)),
      L.length = l.length ∧
        (L.head.asIdeal).LiesOver (RelSeries.head l).asIdeal := by
  obtain ⟨Q, hQprime, hQlo⟩ :=
    liesOver_of_normalization m s K P g hinj hint l hmap
  have := hQprime
  have := hQlo
  obtain ⟨L, hlen, hhead⟩ :=
    lift_chain_through_normalization m s K P g hinj hint l Q hmap
  refine ⟨L, hlen, ?_⟩
  rw [hhead]
  exact hQlo

/-- Triangular monic chain (target shape): from the normalization +
triangular-monic datum, the length-`(m - s)` chain below `P`. The exhibit
series converts to the height bound via `Order.length_le_height_last`, in the
exact form feeding `height_of_dpow_datum`. -/
theorem triangular_monic_chain (m s : ℕ) (K : Type*) [Field K] [Infinite K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hnorm : TriangularNormDatum m s K P) :
    (((m - s : ℕ)) : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) := by
  obtain ⟨l, hlen, hlast⟩ := hnorm.exhibit
  have hle : ((l.length : ℕ) : ℕ∞) ≤ P.height :=
    calc ((l.length : ℕ) : ℕ∞) ≤ Order.height l.last :=
          Order.length_le_height_last
      _ = Order.height (⟨P, ‹P.IsPrime›⟩ : PrimeSpectrum _) := by rw [hlast]
      _ = P.height := (PrimeSpectrum.height_eq_orderHeight _).symm
  have hleW : ((((l.length : ℕ) : ℕ∞)) : WithBot ℕ∞) ≤
      (P.height : WithBot ℕ∞) :=
    WithBot.coe_le_coe.mpr hle
  rw [WithBot.coe_natCast] at hleW
  rwa [hlen] at hleW

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-!
## Obstruction

`triangular_monic_chain` above carries the bundled hypothesis `hnorm:
TriangularNormDatum m s K P`. The structure as stated has **twelve** fields
(`s_le`, `normap`, `normap_inj`, `normap_int`, `bad`, `dir`, `dir_ne`,
`shear_idx`, `shear_exp`, `adm`, `fiber`, `exhibit`). Of the twelve, two are discharged
unconditionally in this file (`normap_of_prime` for the Noether part,
`dir_of_finset` for the linear-form part; no all-ones discharge
theorem exists here — `adm` is discharged by the `D ^ (i + 1)` recipe
`shearExp_adm` in `FiberExhibit.lean`), one is consumed for the bound
(`exhibit`, via `Order.length_le_height_last`), and the Noether datum is
additionally consumed by `quotient_dim_of_normap` and the lift theorems. The
precise remainder is therefore: **derive `exhibit` (and the `fiber` data it
rests on) from the triangular data `(shear_idx, shear_exp, adm)`**.

Why the lift theorems do not close it (verified in-tree; all names above are
the in-tree ones): `Ideal.exists_ltSeries_of_hasGoingUp` lifts a base chain
to a chain *starting* at the lying-over prime, and pulling back along
`R → R ⧸ P` via `RingHom.strictMono_comap_of_surjective` sends the bottom
prime to `P` — so lifted chains sit *above* `P` (they feed coheight, i.e. the
`≤` direction already banked in `PolynomialCatenary.lean`'s deviation note). The
below-`P` exhibit needs the complementary down-route: a nonzero element of
the shear contraction `shearContraction j d P`, monic in the distinguished
variable `Xⱼ` (the weakened `fiber` field), makes the contracted quotient
integral over the delete-`j` `(m - 1)`-variable base (`delVarQuot`), and
going-down — whose normal-base instance consumes exactly such integrality
(see `goingDown_of_normalization` in `FiberExhibit.lean` for the
normalization pair) — plus induction on `m` then yields the long chain below
`P`. (An earlier revision said "`R ⧸ P` integral over the
first-`(m - 1)`-variable quotient" via "flat going-down": imprecise twice
over — the quotient is the contracted one, the base is delete-`j` rather
than first-`(m - 1)`, and the going-down instance in play consumes
integrality over a normal base, not flatness.) The monic-fiber division step
reuses
`Formalization/Appendix_FixedPoint/BezoutChain/
Regularity/Avoid/TriangularRegularity.lean`'s (t2b)
back-substitution (`triG_isSMulRegular_mod_of_dvd`); nothing from `triG` is
re-proved here.

Refutation and weakening (reformulation attempt 1): the `fiber` field was
previously univariate-off-`j`. `FiberExhibit.lean` refutes that shape:
`fiberPred_false_span_sub` shows that for `P = span {X₀ − X₁}` no `j`
admits a nonzero univariate-off-`j` element, and the shear cannot repair it
(it fixes `Xⱼ`; the `D ^ i` weights also collide, `shearExp_weight_tie`).
The field is therefore weakened to monic-not-univariate in the contraction
plus the going-down integrality input. The weakening is principled: with
univariateness unprovable, monic plus integrality is exactly what the
down-route consumes.

Suggested next step: from `monic_direction_exists`'s form, choose
`shear_exp` by the classical `D ^ i` degree recipe so that the contraction
carries the weakened `fiber` data (see `FiberExhibit.lean` reformulation
attempt 1 for the recipe's precise boundary); run the going-down induction
to build `exhibit`; feed the datum to `triangular_monic_chain`, thence to
`hheight_uncond` (and onwards to `hlow_uncond`,
`height_lower_bound_of_catenary_lower_bound`).

Status: attempt 2 closed (`FiberExhibit.lean`) —
no change to this file's code (`TriangularNormDatum` byte-identical: the
fiber field shape already carries both conjuncts — the monic witness and
the `delVarQuot ….IsIntegral` going-down input — that the assembly
discharges). Closed there: the `D ^ (i + 1)` recipe replaces the dead
`D ^ i` recipe (`shearExp` redefined; `shearExp_adm` re-proved;
`shearExp_weight_ne_one` / `shearExp_weight_sep` prove separation, killing
the former `shearExp_weight_tie` by construction); the recipe boundary is
sharp (collapse only at `D = 1`: `contraction_recipe_span_sub_one`,
`weakFiberPred_false_new_recipe_one`; production at `1 < D`:
`weakFiberMonic_new_recipe_of_lt` — no third counterexample within the
operating range); the strong-monic expansion is proved (the carried
generator is strong-monic: `carriedGen_strongMonic`; the general lifting
`delVarQuot_isIntegral_of_strongMonic` discharges the integrality
conjunct); both `fiberPredWeak` conjuncts are assembled on the diagonal
test prime (`fiberPredWeak_span_sub_recipe_of_lt`). Precise remainder
(current stopping point): general-`P` production (per-`P`
`D`-choice, base-`D` weight injectivity, support-expansion of sheared
monomials) and the going-down induction to `exhibit` (needs that
production, plus reindexing/comap-primality/chain transport and the
length-gain rung); `height_of_dpow_datum` and `datum_of_dpow_recipe` stand
ready. Suggested next step: attempt the
general-production push, or restrict the datum scope (e.g. `s = 0`) and
re-run production there.

Status: construction push verified (`FiberExhibit.lean`) —
still no change to this file's code (`TriangularNormDatum` byte-identical:
untouched throughout); both files build cleanly,
with new-theorem axioms within propext/Classical.choice/Quot.sound. The
Attempt-2 remainder above is superseded: general-`P` production now stands
as the degree half (`shear_production_degree`), the expansion statement
(`shearFwd_monomial_expand`), the induction architecture
(`exhibit_of_shear_chain`), and the closure (`hheight_of_production`).
Open: top-coefficient isolation (choice-function bookkeeping — the top
choice yields a scalar leading coefficient, see the remainder sharpening
in `FiberExhibit.lean`) and the below-contraction base chain.

Status: §xx proved (`FiberExhibit.lean`) — still no change
to this file's code; both files build cleanly,
new-theorem axioms within propext/Classical.choice/Quot.sound. First half
of top-coefficient isolation is now proved there (`shear_factor_top_eq`,
`shear_top_prod_eq`, `shear_factor_degreeOf_le`,
`shear_choice_degreeOf_le`: top evaluation plus uniform per-choice
`j`-degree bounds). Open: the cross-sum assembly (strict drop for
non-top choices, coefficient extraction, strong-monic `f`) and the
below-contraction base chain.
-/
