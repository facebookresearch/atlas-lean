/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Polynomial.Splits
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.LocalizationLocalization
import MathlibExt.RingTheory.KrullAkizuki
import MathlibExt.RingTheory.DedekindDomain.DVRCharacterization

/-!
# A finite free algebra over a discrete valuation ring splits over a finite extension

Let `O` be a discrete valuation ring with maximal ideal `𝔪` and field of fractions `K`, and let `H`
be a commutative `O`-algebra, free of finite rank as an `O`-module. Then there are a finite
extension `K'` of `K` and a discrete valuation ring `O' ⊆ K'` with field of fractions `K'`,
containing `O`, whose maximal ideal `𝔪'` satisfies `𝔪' ∩ O = 𝔪`, such that every maximal ideal of
the `K'`-algebra `K' ⊗[O] H` has residue field `K'`
(`IsDiscreteValuationRing.exists_finite_extension_forall_isMaximal_surjective`).

## Proof

For `K'` take the splitting field over `K` of the product of the minimal polynomials of a
`K`-basis `(b_i)` of `K ⊗[O] H`. In a residue field `F` of `K' ⊗[K] (K ⊗[O] H)`, the image of
`1 ⊗ b_i` is a root of the minimal polynomial of `b_i`, which splits in `K'`, so it lies in `K'`;
as the `1 ⊗ b_i` span over `K'`, `F = K'`
(`Algebra.TensorProduct.surjective_algebraMap_quotient_of_splits`). This passes to
`K' ⊗[O] H ≅ K' ⊗[K] (K ⊗[O] H)`. Deligne and Serre take a finite normal extension into which every
residue field of `K ⊗ H` embeds; the splitting field used here is one. For `O'`: the integral
closure `B` of `O` in `K'` is noetherian of dimension at most one by the Krull–Akizuki theorem and
integrally closed, so its localizations at nonzero primes are discrete valuation rings; take
`O' = B_P` for a maximal ideal `P` of `B` above `𝔪`, which exists as `B` is integral over `O`.

## References

* P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7
  (1974), 507–530: proof of Lemme 6.11, p. 522 ("Quitte à faire une extension finie des scalaires,
  on peut supposer que K ⊗ ℋ est un produit d'anneaux artiniens de corps résiduel K"), with the
  statement of the lemma, p. 522, for the extension `O'` of `O` with `O ∩ 𝔪' = 𝔪` and `K'` finite
  over `K`.
-/

@[expose] public section

set_option autoImplicit false

open Polynomial
open scoped TensorProduct

universe w

/-- **Residue fields after splitting the minimal polynomials of a basis.** Let $K$ be a field,
$B$ a finite-dimensional commutative $K$-algebra with a $K$-basis $(b_i)$, and $L$ a field
extension of $K$ in which the minimal polynomial over $K$ of every $b_i$ splits. Then every maximal
ideal $Q$ of $L \otimes_K B$ has residue field $L$: the map $L \to (L \otimes_K B)/Q$ is
surjective.

Source: P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4)
7 (1974), 507–530, proof of Lemme 6.11, p. 522 (the extension of scalars after which
$K \otimes \mathcal{H}$ is a product of local artinian rings with residue field $K$). -/
theorem Algebra.TensorProduct.surjective_algebraMap_quotient_of_splits {K L B : Type*} [Field K]
    [Field L] [Algebra K L] [CommRing B] [Algebra K B] [FiniteDimensional K B] {ι : Type*}
    (b : Module.Basis ι K B) (hsplit : ∀ i, ((minpoly K (b i)).map (algebraMap K L)).Splits)
    (Q : Ideal (L ⊗[K] B)) [Q.IsMaximal] :
    Function.Surjective (algebraMap L ((L ⊗[K] B) ⧸ Q)) := by
  let F := (L ⊗[K] B) ⧸ Q
  let _ : Field F := Ideal.Quotient.field Q
  let π : L ⊗[K] B →ₐ[L] F := Ideal.Quotient.mkₐ L Q
  let R : Subalgebra L F := ⊥
  -- the image of each `1 ⊗ b i` lies in `L`
  have hb : ∀ i, π (1 ⊗ₜ b i) ∈ R := fun i => by
    have hint : IsIntegral K (b i) := Algebra.IsIntegral.isIntegral _
    have hp0 : (minpoly K (b i)).map (algebraMap K L) ≠ 0 :=
      Polynomial.map_ne_zero (minpoly.ne_zero hint)
    rw [Algebra.mem_bot]
    refine (hsplit i).mem_range_of_isRoot hp0 ?_
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq, IsRoot, eval_map_algebraMap]
    have h1 : aeval (1 ⊗ₜ[K] b i : L ⊗[K] B) (minpoly K (b i)) = 0 := by
      rw [show (1 ⊗ₜ[K] b i : L ⊗[K] B) = Algebra.TensorProduct.includeRight (b i) from rfl,
        aeval_algHom_apply, minpoly.aeval, map_zero]
    have h2 := congrArg (π.restrictScalars K) h1
    rwa [map_zero, ← aeval_algHom_apply] at h2
  -- hence the image of every `1 ⊗ y`, as `b` spans `B` over `K`
  have hy : ∀ y : B, π (1 ⊗ₜ y) ∈ R := by
    let φ : B →ₗ[K] F := (π.restrictScalars K).toLinearMap ∘ₗ
      (Algebra.TensorProduct.includeRight : B →ₐ[K] L ⊗[K] B).toLinearMap
    have hle : Submodule.span K (Set.range b) ≤
        (R.toSubmodule.restrictScalars K).comap φ := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hb i
    intro y
    have := hle (b.span_eq ▸ Submodule.mem_top : y ∈ Submodule.span K (Set.range b))
    exact this
  -- and of every element of `L ⊗ B`
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hx : π x ∈ R := by
    induction x using TensorProduct.inductionOn with
    | tmul l y =>
      rw [show (l ⊗ₜ[K] y : L ⊗[K] B) = l • (1 ⊗ₜ y) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul]
      exact R.smul_mem (hy y) l
    | add x x' hx hx' => rw [map_add]; exact R.add_mem hx hx'
  exact Algebra.mem_bot.1 hx

/-- **A finite free algebra over a discrete valuation ring splits over a finite extension.** Let
$\mathcal{O}$ be a discrete valuation ring with maximal ideal $\mathfrak{m}$ and field of fractions
$K$, and let $\mathcal{H}$ be a commutative $\mathcal{O}$-algebra that is free of finite rank as an
$\mathcal{O}$-module. Then there are a finite extension $K'$ of $K$ and a discrete valuation ring
$\mathcal{O}' \subset K'$ with field of fractions $K'$, containing $\mathcal{O}$, whose maximal
ideal $\mathfrak{m}'$ satisfies $\mathfrak{m}' \cap \mathcal{O} = \mathfrak{m}$, such that every
maximal ideal $Q$ of the $K'$-algebra $K' \otimes_{\mathcal{O}} \mathcal{H}$ has residue field
$K'$, that is, $K' \to (K' \otimes_{\mathcal{O}} \mathcal{H})/Q$ is surjective. Here
$\mathcal{O}'$ is a subring of $K'$, the inclusion $\mathcal{O} \subseteq \mathcal{O}'$ is the
ring homomorphism `ι`, which agrees with $\mathcal{O} \to K \to K'$, and
$\mathfrak{m}' \cap \mathcal{O} = \mathfrak{m}$ is the equality of the preimage of $\mathfrak{m}'$
under `ι` with $\mathfrak{m}$; $K'$ lies in the universe of $K$.

Source: P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4)
7 (1974), 507–530, proof of Lemme 6.11, p. 522. -/
theorem IsDiscreteValuationRing.exists_finite_extension_forall_isMaximal_surjective
    {O H : Type*} (K : Type w) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [CommRing H] [Algebra O H] [Module.Free O H]
    [Module.Finite O H] :
    ∃ (K' : Type w) (_ : Field K') (_ : Algebra K K') (_ : Algebra O K')
      (_ : IsScalarTower O K K') (O' : Subring K') (_ : IsDiscreteValuationRing O')
      (ι : O →+* O'), FiniteDimensional K K' ∧ IsFractionRing O' K' ∧
      (∀ x, (ι x : K') = algebraMap O K' x) ∧
      (IsLocalRing.maximalIdeal O').comap ι = IsLocalRing.maximalIdeal O ∧
      ∀ Q : Ideal (K' ⊗[O] H), Q.IsMaximal →
        Function.Surjective (Algebra.ofId K' ((K' ⊗[O] H) ⧸ Q)) := by
  -- the splitting field of the minimal polynomials of a basis of `K ⊗ H`
  let b := Module.finBasis K (K ⊗[O] H)
  let P : K[X] := ∏ i, minpoly K (b i)
  have hint : ∀ i, IsIntegral K (b i) := fun i => Algebra.IsIntegral.isIntegral _
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => minpoly.ne_zero (hint i)
  let K' := P.SplittingField
  have hsplit : ∀ i, ((minpoly K (b i)).map (algebraMap K K')).Splits := fun i =>
    (SplittingField.splits P).of_dvd (Polynomial.map_ne_zero hP0)
      (Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))
  have : IsScalarTower O K K' := inferInstance
  -- residue fields of `K' ⊗[O] H`
  have hres : ∀ Q : Ideal (K' ⊗[O] H), Q.IsMaximal →
      Function.Surjective (Algebra.ofId K' ((K' ⊗[O] H) ⧸ Q)) := by
    intro Q hQ
    let e := Algebra.TensorProduct.cancelBaseChange O K K' K' H
    let Q' := Q.comap e
    have : Q'.IsMaximal := Ideal.comap_isMaximal_of_equiv e
    have hQ' : Q = Q'.map e := by
      rw [Ideal.map_comap_of_surjective _ e.surjective]
    let f := Ideal.quotientEquivAlg Q' Q e hQ'
    have h := Algebra.TensorProduct.surjective_algebraMap_quotient_of_splits b hsplit Q'
    intro y
    obtain ⟨c, hc⟩ := h (f.symm y)
    refine ⟨c, ?_⟩
    rw [Algebra.ofId_apply, ← f.apply_symm_apply y, ← hc, AlgEquiv.commutes]
  -- the integral closure of `O` in `K'`
  let A0 := integralClosure O K'
  have hKA := Subalgebra.isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite
    (A := O) (K := K) (L := K') A0
  have : IsNoetherianRing A0 := hKA.1
  have : Ring.KrullDimLE 1 A0 := hKA.2.1
  have : IsFractionRing A0 K' := integralClosure.isFractionRing_of_finite_extension K K'
  have : IsIntegrallyClosed A0 := integralClosure.isIntegrallyClosedOfFiniteExtension K
  have : Ring.DimensionLEOne A0 :=
    ⟨fun hp hpr => by have := hpr; exact Ideal.isMaximal_of_isPrime_of_ne_bot _ hp⟩
  have hdvr := (isDiscreteValuationRing_localization_atPrime_iff_integrallyClosed_dimensionLEOne
    A0).2 ⟨inferInstance, inferInstance⟩
  -- a maximal ideal of `A0` over the maximal ideal of `O`
  have hinj : Function.Injective (algebraMap O A0) := by
    intro x y hxy
    have : algebraMap O K' x = algebraMap O K' y := by
      rw [IsScalarTower.algebraMap_apply O A0 K', hxy, ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply O K K', IsScalarTower.algebraMap_apply O K K' y] at this
    exact IsFractionRing.injective O K ((algebraMap K K').injective this)
  obtain ⟨Pm, hPm, hPu⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := A0) (IsLocalRing.maximalIdeal O) (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)
  have hPne : Pm ≠ ⊥ := by
    intro h
    apply IsDiscreteValuationRing.not_a_field O
    rw [← hPu, h, Ideal.under, Ideal.comap_bot_of_injective _ hinj]
  have : Pm.IsPrime := hPm.isPrime
  have hS := Ideal.primeCompl_le_nonZeroDivisors Pm
  let S' := Localization.subalgebra.ofField K' Pm.primeCompl hS
  have : IsLocalization Pm.primeCompl S' :=
    Localization.subalgebra.isLocalization_ofField K' Pm.primeCompl hS
  have : IsLocalization.AtPrime S' Pm := inferInstance
  have : IsFractionRing S' K' :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization Pm.primeCompl S' K'
  have : IsDiscreteValuationRing (Localization.AtPrime Pm) := hdvr Pm hPne hPm.isPrime
  have hS'dvr : IsDiscreteValuationRing S' :=
    RingEquivClass.isDiscreteValuationRing
      (IsLocalization.algEquiv Pm.primeCompl (Localization.AtPrime Pm) S')
  -- `O'` is `S'`, as a subring of `K'`
  let O' : Subring K' := S'.toSubring
  let eO : S' ≃+* O' := RingEquiv.refl _
  have hO'dvr : IsDiscreteValuationRing O' := RingEquivClass.isDiscreteValuationRing eO
  let ι : O →+* O' := eO.toRingHom.comp ((algebraMap A0 S').comp (algebraMap O A0))
  have hι : ∀ x, (ι x : K') = algebraMap O K' x := fun x => by
    rfl
  refine ⟨K', inferInstance, inferInstance, inferInstance, inferInstance, O', hO'dvr, ι,
    inferInstance, (inferInstance : IsFractionRing S' K'), hι, ?_, hres⟩
  change ((IsLocalRing.maximalIdeal S').under A0).comap (algebraMap O A0) = _
  rw [IsLocalization.AtPrime.under_maximalIdeal S' Pm]
  exact hPu

end
