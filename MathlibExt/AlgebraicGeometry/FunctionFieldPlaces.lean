/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/AlgebraicGeometry/Faltings.lean` (leanprover/lean-eval), at commit
38361be884302c7edce1908c4aef8296eb2cb27e, problem `faltings`: the function field
and place definitions and instances, the adele ring and its principal map, and the
statement of finiteness of poles.
Copyright 2026 Lean FRO, LLC.
Authors: Junyan Xu
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
For the adapted portions, see the Apache 2.0 terms and disclaimer of warranties.
Modification notice (Apache License 2.0, Section 4). The declarations retain their ATLAS
namespace. Finiteness of poles is proved here and used in the principal adele map.
-/

module

public import Mathlib.NumberTheory.FunctionField
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
import Mathlib.RingTheory.Valuation.LocalSubring
import MathlibExt.RingTheory.DedekindDomain.FiniteSupport
import MathlibExt.RingTheory.KrullAkizuki

/-!
# Places and adeles of one-variable function fields

This file defines places as proper valuation subalgebras and proves that each element
of a one-variable function field has only finitely many poles. It defines the adele ring
and the diagonal ring homomorphism from the function field into it.
-/

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.FaltingsWanted

namespace AlgebraicGeometry.Faltings

section ValuationSubalgebra

variable (R F : Type*) [CommSemiring R] [Field F] [Algebra R F]

set_option linter.dupNamespace false in
@[ext] structure ValuationSubalgebra extends Subalgebra R F, ValuationSubring F

end ValuationSubalgebra

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

set_option linter.dupNamespace false in
class BundledFunctionField extends
  Algebra (RatFunc K) F, IsScalarTower K (RatFunc K) F, FunctionField K F

set_option linter.dupNamespace false in
/-- **Place.** Let $F$ be a field and $K$ a field with $F$ a $K$-algebra. A place of $F/K$ is a
valuation ring of $F$ containing $K$ and different from $F$: a $K$-subalgebra $\mathcal{O}$ of
$F$ with $\mathcal{O} \neq F$ such that $z \in \mathcal{O}$ or $z^{-1} \in \mathcal{O}$ for
every $z \in F$. See [Stichtenoth, Definition 1.1.4 and 1.1.8].

Stichtenoth calls the maximal ideal of $\mathcal{O}$ the place, which determines $\mathcal{O}$,
and also requires $\mathcal{O} \neq K$; that condition is omitted since it is automatic. -/
@[ext] structure Place extends ValuationSubalgebra K F where
  ne_top : toSubalgebra ≠ ⊤

set_option linter.dupNamespace false in
instance : SetLike (Place K F) F where
  coe v := v.carrier
  coe_injective _ _ := Place.ext

set_option linter.dupNamespace false in
instance : SMulMemClass (Place K F) K F where
  smul_mem {v} r _ h := v.smul_mem h r

set_option linter.dupNamespace false in
instance : SubringClass (Place K F) F where
  mul_mem {v} := v.mul_mem
  one_mem {v} := v.one_mem
  add_mem {v} := v.add_mem
  zero_mem {v} := v.zero_mem
  neg_mem {v} := v.toValuationSubring.neg_mem _

variable (v : Place K F)

set_option linter.dupNamespace false in
instance : HasMemOrInvMem v where
  mem_or_inv_mem := v.mem_or_inv_mem'

set_option linter.dupNamespace false in
instance : Algebra v F := inferInstanceAs (Algebra v.toSubalgebra F)
set_option linter.dupNamespace false in
instance : IsScalarTower K v F := inferInstanceAs (IsScalarTower K v.toSubalgebra F)
set_option linter.dupNamespace false in
instance : IsFractionRing v F := inferInstanceAs (IsFractionRing v.toValuationSubring F)
set_option linter.dupNamespace false in
instance : ValuationRing v := inferInstanceAs (ValuationRing v.toValuationSubring)

variable {F}

open Polynomial IntermediateField IsDedekindDomain

private theorem Place.valuationSubring_injective :
    Function.Injective (fun v : Place K F ↦ v.toValuationSubring) :=
  fun _ _ h ↦ SetLike.coe_injective (congrArg (fun V : ValuationSubring F ↦ (V : Set F)) h)

private theorem finite_valuationSubrings_of_mem_nonunits
    {A L : Type*} [CommRing A] [IsDedekindDomain A] [Field L] [Algebra A L]
    [IsFractionRing A L] (a : A) (ha : a ≠ 0) :
    {V : ValuationSubring L | (∀ b : A, algebraMap A L b ∈ V) ∧
      algebraMap A L a ∈ V.nonunits}.Finite := by
  classical
  let S := {p : Ideal A | p.IsPrime ∧ a ∈ p}
  have : Finite S := (Ideal.finite_setOf_isPrime_and_mem ha).to_subtype
  let prime (p : S) : HeightOneSpectrum A :=
    ⟨p.1, p.2.1, fun hp ↦ ha (Ideal.mem_bot.mp (hp ▸ p.2.2))⟩
  refine (Set.finite_range fun p : S ↦ (prime p).valuationSubringAtPrime L).subset ?_
  rintro V ⟨hA, haV⟩
  let f : A →+* V := (algebraMap A L).codRestrict V.toSubring hA
  let p := (IsLocalRing.maximalIdeal V).comap f
  have hp : a ∈ p := ValuationSubring.coe_mem_nonunits_iff.mp haV
  let q : S := ⟨p, inferInstanceAs (p.IsPrime), hp⟩
  refine ⟨q, ValuationSubring.eq_of_le_of_ne_top _ ?_ ?_⟩
  · change (prime q).valuationSubringAtPrime L ≤ V
    rintro z ⟨b, s, hs, rfl⟩
    have hinv : (algebraMap A L s)⁻¹ ∈ V := by
      by_contra h
      exact hs (ValuationSubring.coe_mem_nonunits_iff.mp
        ((V.mem_nonunits_iff_or).mpr (Or.inr h)))
    exact V.mul_mem _ _ (hA b) hinv
  · intro h
    have ha₀ := (map_ne_zero_iff _ (IsFractionRing.injective A L)).mpr ha
    exact ((V.mem_nonunits_iff_or).mp haV).resolve_left ha₀
      (h ▸ ValuationSubring.mem_top _)

private theorem finite_nonunits_of_transcendental [BundledFunctionField K F]
    {y : F} (hy : Transcendental K y) :
    {v : Place K F | y ∈ v.toValuationSubring.nonunits}.Finite := by
  let E := IntermediateField.adjoin K ({y} : Set F)
  let gen : E := AdjoinSimple.gen K y
  let : FiniteDimensional E F := FunctionField.finiteDimensional_of_adjoin_transcendental hy
  let : Algebra K[X] E := (aeval gen : K[X] →ₐ[K] E).toRingHom.toAlgebra
  let : Algebra K[X] F := (aeval y : K[X] →ₐ[K] F).toRingHom.toAlgebra
  have : IsScalarTower K[X] E F := IsScalarTower.of_algebraMap_eq fun p ↦
    aeval_algebraMap_apply F gen p
  let e : RatFunc K ≃ₐ[K[X]] E :=
    { RatFunc.algEquivOfTranscendental y hy with
      commutes' := RatFunc.algEquivOfTranscendental_algebraMap y hy }
  have : IsFractionRing K[X] E := IsFractionRing.of_algEquiv e
  -- Krull–Akizuki gives Noetherianity even for inseparable extensions.
  let A := integralClosure K[X] F
  have : IsFractionRing A F := integralClosure.isFractionRing_of_finite_extension E F
  have : IsNoetherianRing A :=
    (Subalgebra.isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite
      (K := E) (integralClosure K[X] F)).1
  have : IsIntegrallyClosed A := integralClosure.isIntegrallyClosedOfFiniteExtension E
  have : IsDedekindDomain A := { }
  let a : A := algebraMap K[X] A X
  have ha : algebraMap A F a = y := by
    rw [← IsScalarTower.algebraMap_apply]
    exact aeval_X y
  have ha₀ : a ≠ 0 := by
    intro h
    apply hy.ne_zero
    rw [← ha, h, map_zero]
  refine Set.Finite.of_injOn ?_ (Place.valuationSubring_injective K).injOn
    (finite_valuationSubrings_of_mem_nonunits a ha₀)
  intro v hv
  change (∀ b : A, algebraMap A F b ∈ v.toValuationSubring) ∧
    algebraMap A F a ∈ v.toValuationSubring.nonunits
  refine ⟨?_, ha.symm ▸ hv⟩
  let V := v.toValuationSubring
  let yV : v := ⟨y, V.nonunits_subset hv⟩
  let f : K[X] →+* V := (aeval yV : K[X] →ₐ[K] v).toRingHom
  have hf (p : K[X]) : (f p : F) = algebraMap K[X] F p :=
    (aeval_algebraMap_apply F yV p).symm
  intro b
  have hb : IsIntegral K[X] (b : F) := b.2
  obtain ⟨c, hc⟩ := (isIntegrallyClosed_iff F).mp (inferInstance : IsIntegrallyClosed V)
    (hb.map_of_comp_eq f (RingHom.id F) (RingHom.ext hf))
  exact hc ▸ c.2

set_option linter.dupNamespace false in
/-- **Finitely many poles.** Let $F$ be a function field over a field $K$, that is, a finite
extension of the rational function field $K(t)$. For every $x \in F$, there are only finitely
many places $P$ of $F/K$ whose valuation ring $\mathcal{O}_P$ does not contain $x$, that is,
$x$ has only finitely many poles. See [Stichtenoth, Corollary 1.3.4].

Source: see manifest Via leanprover/lean-eval@38361be, problem `faltings`. -/
theorem finite_setOf_place_notMem [BundledFunctionField K F] (x : F) :
    {v : Place K F | x ∉ v}.Finite := by
  by_cases hx : IsAlgebraic K x
  · refine Set.finite_empty.subset fun v hv ↦ ?_
    have hv' : IsIntegral v x := hx.isIntegral.tower_top
    have hvClosed : IsIntegrallyClosed v :=
      inferInstanceAs (IsIntegrallyClosed v.toValuationSubring)
    obtain ⟨z, hz⟩ := (isIntegrallyClosed_iff F).mp hvClosed hv'
    exact (hv (hz ▸ z.2)).elim
  -- At a pole, the inverse lies in the maximal ideal of the place ring.
  · refine (finite_nonunits_of_transcendental K (y := x⁻¹)
      (fun h ↦ hx (IsAlgebraic.inv_iff.mp h))).subset fun v hv ↦ ?_
    exact v.toValuationSubring.inv_mem_nonunits_iff.mpr (Or.inr hv)

open scoped RestrictedProduct

variable (F)

set_option linter.dupNamespace false in
/-- **Adele ring.** Let $F$ be a field and $K$ a field with $F$ a $K$-algebra. The adele ring
$\mathcal{A}_F$ of $F/K$ is the restricted product of copies of $F$ indexed by the places $P$
of $F/K$, with respect to their valuation rings $\mathcal{O}_P$ and the cofinite filter: its
elements are the families $\alpha = (\alpha_P)_P$ with $\alpha_P \in F$ for every place $P$
and $\alpha_P \in \mathcal{O}_P$ for all but finitely many $P$. See [Stichtenoth, Definition
1.5.2]. -/
abbrev Adele : Type _ :=
  RestrictedProduct (fun _ ↦ F) (fun v : Place K F ↦ (v : Set F)) Filter.cofinite

set_option linter.dupNamespace false in
instance : CommRing (Adele K F) := RestrictedProduct.instCommRingCoeOfSubringClass ..

variable {F}

set_option linter.dupNamespace false in
/-- **Principal adele map.** Let $F$ be a function field over a field $K$, that is, a finite
extension of the rational function field $K(t)$. The principal adele map is a ring homomorphism
from $F$ to the adele ring $\mathcal{A}_F$ of $F/K$. It is the diagonal embedding sending $x \in F$
to the adele whose coordinate at every place $P$ of $F/K$ is $x$. This is well defined since $x$
has only finitely many poles. See `Adele.principal_apply` for the coordinate formula.

Source: see manifest Via leanprover/lean-eval@38361be, problem `faltings`. -/
def Adele.principal [BundledFunctionField K F] : F →+* Adele K F where
  toFun x := ⟨fun _ ↦ x, Filter.eventually_cofinite.mpr (finite_setOf_place_notMem K x)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

set_option linter.dupNamespace false in
/-- **Coordinates of a principal adele.** Let $F$ be a function field over a field $K$, that is,
a finite extension of the rational function field $K(t)$. For every $x \in F$ and every place
$P$ of $F/K$, the coordinate at $P$ of the principal adele of $x$ is $x$.

Source: see manifest Via leanprover/lean-eval@38361be, problem `faltings`. -/
theorem Adele.principal_apply [BundledFunctionField K F] (x : F)
    (v : Place K F) : (Adele.principal K x) v = x := rfl

end AlgebraicGeometry.Faltings

end MathlibExt.AlgebraicGeometry.FaltingsWanted
