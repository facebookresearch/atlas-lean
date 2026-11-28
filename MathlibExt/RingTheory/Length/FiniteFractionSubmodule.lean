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

public import MathlibExt.RingTheory.Length.FiniteFractionSubalgebra
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Principal quotient lengths in finite fraction submodules

Over a Noetherian ring of Krull dimension at most one, a finite submodule
of the actual fraction field containing the original unit has finite
colength over the original ring. Under these same ring hypotheses,
multiplication by a nonzero original scalar gives the same quotient length
on that submodule and on the original ring. A finite quotient of such a
fraction submodule, annihilated by the same scalar, has length at most the
original principal quotient length.

The submodules and surjective quotient maps are constructed from their
actual finite generators. Ring and module universes remain independent.
-/

@[expose] public section
noncomputable section

universe u v w

namespace Submodule

variable {R : Type u} [CommRing R]

private theorem length_quotient_span_eq_lsmul_of_finite_colength
    {A : Type v} [AddCommGroup A] [Module R A]
    (i : R →ₗ[R] A) (hi : Function.Injective i)
    (hfinite : IsFiniteLength R (A ⧸ i.range))
    (a : R) (hf : Function.Injective (LinearMap.lsmul R A a)) :
    Module.length R (R ⧸ Ideal.span {a}) =
      Module.length R (A ⧸ (LinearMap.lsmul R A a).range) := by
  let N : Submodule R A := i.range
  let f : A →ₗ[R] A := LinearMap.lsmul R A a
  let T : Submodule R N := (N.map f).comap N.subtype
  let e : R ≃ₗ[R] N := LinearEquiv.ofInjective i hi
  have hN : N.map f ≤ N := by
    rintro z ⟨x, ⟨r, rfl⟩, rfl⟩
    refine ⟨a * r, ?_⟩
    simpa only [smul_eq_mul, f, LinearMap.lsmul_apply] using i.map_smul a r
  have hmap : Submodule.map e.toLinearMap (Ideal.span {a}) = T := by
    ext z
    constructor
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hr
      refine ⟨i q, ⟨q, rfl⟩, ?_⟩
      change f (i q) = i (a * q)
      simpa only [smul_eq_mul, f, LinearMap.lsmul_apply] using (i.map_smul a q).symm
    · rintro ⟨x, ⟨r, rfl⟩, hr⟩
      refine ⟨a * r, Ideal.mem_span_singleton.mpr ⟨r, rfl⟩, ?_⟩
      apply Subtype.ext
      change i (a * r) = (z : A)
      calc
        i (a * r) = f (i r) := by
          simpa only [smul_eq_mul, f, LinearMap.lsmul_apply] using i.map_smul a r
        _ = (z : A) := hr
  have hleft : Module.length R (R ⧸ Ideal.span {a}) = Module.length R (N ⧸ T) :=
    (Submodule.Quotient.equiv (Ideal.span {a}) T e hmap).length_eq
  exact hleft.trans (Submodule.length_quotient_map_eq_of_finite_colength N hfinite f hf hN)

variable {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]

/-- Let `R` be a commutative ring, `K` an `R`-algebra field that is a fraction
ring of `R`, and `N ⊆ K` an `R`-submodule containing `1`. The algebra map factors
as an `R`-linear scalar inclusion `R → N`, whose value in `K` is the original
algebra-map value. -/
def fractionScalarMap (N : Submodule R K) (h1 : (1 : K) ∈ N) : R →ₗ[R] N :=
  (Algebra.linearMap R K).codRestrict N (fun r => by
    simpa only [Algebra.linearMap_apply, Algebra.smul_def, mul_one] using N.smul_mem r h1)

omit [IsFractionRing R K] in
/-- For a commutative ring `R`, an `R`-algebra field `K`, and an `R`-submodule
`N ⊆ K` containing `1`, the scalar inclusion sends `r` to an element whose value
in `K` is exactly `algebraMap R K r`. This coordinate formula does not require
the fraction-ring hypothesis. -/
@[simp] theorem fractionScalarMap_apply (N : Submodule R K) (h1 : (1 : K) ∈ N) (r : R) :
    ((fractionScalarMap N h1 r : N) : K) = algebraMap R K r := rfl

/-- For a commutative ring `R`, a chosen fraction-ring field `K`, and an
`R`-submodule `N ⊆ K` containing `1`, the scalar inclusion `R → N` is
injective. -/
theorem fractionScalarMap_injective (N : Submodule R K) (h1 : (1 : K) ∈ N) :
    Function.Injective (fractionScalarMap N h1) := by
  intro a b h
  exact IsFractionRing.injective R K (congrArg Subtype.val h)

/-- Let `R` be a commutative ring, `K` an `R`-algebra field that is a fraction
ring of `R`, and `N ⊆ K` an `R`-submodule containing `1`. The quotient of `N`
by its scalar image of `R` is torsion as an `R`-module. -/
theorem isTorsion_quotient_fractionScalarMap (N : Submodule R K) (h1 : (1 : K) ∈ N) :
    Module.IsTorsion R (N ⧸ (fractionScalarMap N h1).range) := by
  let i := fractionScalarMap N h1
  intro z
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective i.range z
  obtain ⟨c, r, hr⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors R) (x : K)
  refine ⟨c, ?_⟩
  change (c : R) • i.range.mkQ x = 0
  rw [← i.range.mkQ.map_smul]
  apply (Submodule.Quotient.mk_eq_zero i.range).mpr
  refine ⟨r, ?_⟩
  apply Subtype.ext
  change algebraMap R K r = (c : R) • (x : K)
  exact hr

/-- Let `R` be a Noetherian commutative ring of Krull dimension at most one,
`K` an `R`-algebra field that is a fraction ring of `R`, and `N ⊆ K` a finitely
generated `R`-submodule containing `1`. The quotient of `N` by the scalar image
of `R` has finite composition length over `R`. -/
theorem isFiniteLength_quotient_fractionScalarMap
    (N : Submodule R K) (h1 : (1 : K) ∈ N)
    [Module.Finite R N] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] :
    IsFiniteLength R (N ⧸ (fractionScalarMap N h1).range) := by
  obtain ⟨c, hc, hc0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors
    (isTorsion_quotient_fractionScalarMap N h1)
  have hann : ∀ z : N ⧸ (fractionScalarMap N h1).range, c • z = 0 :=
    fun z => Submodule.mem_annihilator.mp hc z Submodule.mem_top
  have hI : Ideal.span {c} ≤ Module.annihilator R (N ⧸ (fractionScalarMap N h1).range) :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Module.mem_annihilator.mpr hann))
  have hquot : Module.length R (R ⧸ Ideal.span {c}) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (isFiniteLength_quotient_span_singleton R hc0)
  exact Module.length_ne_top_iff.mp
    (Module.length_ne_top_of_finite_of_ideal_le_annihilator R
      (N ⧸ (fractionScalarMap N h1).range) (Ideal.span {c}) hI hquot)

/-- Let `R` be a Noetherian commutative ring of Krull dimension at most one,
`K` an `R`-algebra field that is a fraction ring of `R`, and `M ⊆ K` a finitely
generated `R`-submodule containing `1`. For nonzero `a ∈ R`,
`length_R(R/(a)) = length_R(M/aM)`, where `aM` is the range of multiplication
by `a` on `M`. -/
theorem length_quotient_span_eq_quotient_lsmul_finite_fraction
    (M : Submodule R K) (h1 : (1 : K) ∈ M)
    [Module.Finite R M] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    {a : R} (ha : a ≠ 0) :
    Module.length R (R ⧸ Ideal.span {a}) =
      Module.length R (M ⧸ (LinearMap.lsmul R M a).range) := by
  classical
  let i : R →ₗ[R] M := fractionScalarMap M h1
  let f : M →ₗ[R] M := LinearMap.lsmul R M a
  have haK : algebraMap R K a ≠ 0 := by
    intro h
    apply ha
    exact IsFractionRing.injective R K (h.trans (map_zero (algebraMap R K)).symm)
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have hv := congrArg (fun z : M => (z : K)) h
    apply mul_left_cancel₀ haK
    simpa only [f, LinearMap.lsmul_apply, Submodule.coe_smul, Algebra.smul_def] using hv
  exact length_quotient_span_eq_lsmul_of_finite_colength i (fractionScalarMap_injective M h1)
    (isFiniteLength_quotient_fractionScalarMap M h1) a hf

omit [IsFractionRing R K] in
private theorem exists_finite_fraction_lift
    {Q : Type w} [AddCommGroup Q] [Module R Q] [Module.Finite R Q]
    (N : Submodule R K) (h1 : (1 : K) ∈ N)
    (f : N →ₗ[R] Q) (hf : Function.Surjective f) :
    ∃ (P : Submodule R K) (hPN : P ≤ N), P.FG ∧ (1 : K) ∈ P ∧
      Function.Surjective (f.comp (P.inclusion hPN)) := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := Q)
  choose g hg using (fun j : Fin n => hf (s j))
  let P : Submodule R K := Submodule.span R (insert 1 (Set.range (fun j => (g j : K))))
  have hPN : P ≤ N := by
    apply Submodule.span_le.mpr
    rintro x (rfl | ⟨j, rfl⟩)
    · exact h1
    · exact (g j).property
  have hfg : P.FG := Submodule.fg_span ((Set.finite_range (fun j => (g j : K))).insert 1)
  have hone : (1 : K) ∈ P := Submodule.subset_span (Set.mem_insert 1 _)
  let fp := f.comp (P.inclusion hPN)
  have htop : (⊤ : Submodule R Q) ≤ fp.range := by
    rw [← hs]
    apply Submodule.span_le.mpr
    rintro q ⟨j, rfl⟩
    refine ⟨⟨(g j : K), Submodule.subset_span (Set.mem_insert_of_mem 1 ⟨j, rfl⟩)⟩, ?_⟩
    change f (g j) = s j
    exact hg j
  exact ⟨P, hPN, hfg, hone, LinearMap.range_eq_top.mp (top_le_iff.mp htop)⟩

/-- Let `R` be a Noetherian commutative ring of Krull dimension at most one,
`K` an `R`-algebra field that is a fraction ring of `R`, and `N ⊆ K` an
`R`-submodule containing `1`. If a linear map `N → Q` is surjective, `Q` is a
finitely generated `R`-module in any given universe, and a nonzero scalar `a`
annihilates `Q`, then `length_R(Q) ≤ length_R(R/(a))`. The submodule `N` need
not itself be finitely generated. -/
theorem length_le_quotient_span_of_surjective_finite_fraction
    {Q : Type w} [AddCommGroup Q] [Module R Q] [Module.Finite R Q]
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    (N : Submodule R K) (h1 : (1 : K) ∈ N)
    (f : N →ₗ[R] Q) (hf : Function.Surjective f)
    {a : R} (ha : a ≠ 0) (hkill : ∀ q : Q, a • q = 0) :
    Module.length R Q ≤ Module.length R (R ⧸ Ideal.span {a}) := by
  obtain ⟨P, hPN, hfg, hone, hsurj⟩ := exists_finite_fraction_lift N h1 f hf
  let _ : Module.Finite R P := Module.Finite.of_fg hfg
  let fa : P →ₗ[R] P := LinearMap.lsmul R P a
  let fp : P →ₗ[R] Q := f.comp (P.inclusion hPN)
  have hker : fa.range ≤ fp.ker := by
    rintro z ⟨p, rfl⟩
    change fp (a • p) = 0
    rw [fp.map_smul]
    exact hkill _
  let fq : P ⧸ fa.range →ₗ[R] Q := fa.range.liftQ fp hker
  have hq : Function.Surjective fq := by
    intro q
    obtain ⟨p, hp⟩ := hsurj q
    exact ⟨fa.range.mkQ p, hp⟩
  exact (Module.length_le_of_surjective fq hq).trans
    (length_quotient_span_eq_quotient_lsmul_finite_fraction P hone ha).symm.le

end Submodule
