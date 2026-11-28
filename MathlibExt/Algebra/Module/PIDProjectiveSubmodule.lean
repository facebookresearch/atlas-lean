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

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.SetTheory.Cardinal.Order

/-!
# Submodules of projective modules over a principal ideal domain

Let R be a commutative domain in which every ideal is principal. Every
submodule of a free R-module is free, with no restriction on the rank.
Every submodule of a projective R-module is consequently projective.
The ring and module carriers may lie in independent universes.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe u v

namespace Module.Free

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {ι : Type v}

private def leadingIdeal [LinearOrder ι] (N : Submodule R (ι →₀ R)) (i : ι) : Ideal R :=
  (N ⊓ Finsupp.supported R R (Set.Iic i)).map
    (Finsupp.lapply i : (ι →₀ R) →ₗ[R] R)

private noncomputable def leadingGenerator [LinearOrder ι]
    (N : Submodule R (ι →₀ R)) (i : ι) : R :=
  Submodule.IsPrincipal.generator (leadingIdeal N i)

omit [IsDomain R] in
private theorem leadingGenerator_mem [LinearOrder ι]
    (N : Submodule R (ι →₀ R)) (i : ι) :
    leadingGenerator N i ∈ leadingIdeal N i := by
  exact Submodule.IsPrincipal.generator_mem (R := R) (M := R) (leadingIdeal N i)

private noncomputable def leadingPivot [LinearOrder ι]
    (N : Submodule R (ι →₀ R)) (i : ι) : ι →₀ R :=
  (Submodule.mem_map.mp (leadingGenerator_mem N i)).choose

omit [IsDomain R] in
private theorem leadingPivot_spec [LinearOrder ι]
    (N : Submodule R (ι →₀ R)) (i : ι) :
    leadingPivot N i ∈ N ⊓ Finsupp.supported R R (Set.Iic i) ∧
      (Finsupp.lapply i : (ι →₀ R) →ₗ[R] R) (leadingPivot N i) =
        leadingGenerator N i :=
  (Submodule.mem_map.mp (leadingGenerator_mem N i)).choose_spec

omit [IsDomain R] in
private theorem leadingPivot_mem [LinearOrder ι]
    (N : Submodule R (ι →₀ R)) (i : ι) : leadingPivot N i ∈ N :=
  (leadingPivot_spec N i).1.1

omit [IsDomain R] in
private theorem leadingPivot_supported [LinearOrder ι]
    (N : Submodule R (ι →₀ R)) (i : ι) :
    leadingPivot N i ∈ Finsupp.supported R R (Set.Iic i) :=
  (leadingPivot_spec N i).1.2

omit [IsDomain R] in
@[simp]
private theorem leadingPivot_apply [LinearOrder ι]
    (N : Submodule R (ι →₀ R)) (i : ι) :
    leadingPivot N i i = leadingGenerator N i := by
  simpa only [Finsupp.lapply_apply] using (leadingPivot_spec N i).2

private noncomputable def PivotIndex [LinearOrder ι]
    (N : Submodule R (ι →₀ R)) : Type v :=
  {i : ι // leadingGenerator N i ≠ 0}

private noncomputable def pivotFamily [LinearOrder ι]
    (N : Submodule R (ι →₀ R)) : PivotIndex N → N :=
  fun i => ⟨leadingPivot N i.1, leadingPivot_mem N i.1⟩

private theorem finsuppSubmodule_free [LinearOrder ι] [WellFoundedLT ι]
    (N : Submodule R (ι →₀ R)) : Module.Free R N := by
  classical
  let S : Submodule R N := Submodule.span R (Set.range (pivotFamily N))
  have hp : LinearIndependent R (pivotFamily N) := by
    refine (linearIndependent_iff' (R := R) (v := pivotFamily N)).mpr ?_
    intro s g h i hi
    by_contra hgi
    let t : Finset (PivotIndex N) := s.filter fun j => g j ≠ 0
    have hit : i ∈ t := by simp [t, hi, hgi]
    obtain ⟨k, hkt, hkmax⟩ :=
      Finset.exists_max_image t (fun j : PivotIndex N => (j.1 : ι)) ⟨i, hit⟩
    have hks : k ∈ s := (Finset.mem_filter.mp hkt).1
    have hgk : g k ≠ 0 := (Finset.mem_filter.mp hkt).2
    let ev : N →ₗ[R] R :=
      (Finsupp.lapply k.1 : (ι →₀ R) →ₗ[R] R).comp N.subtype
    have hcoord₀ : ∑ j ∈ s, g j • ev (pivotFamily N j) = 0 := by
      simpa only [map_sum, map_smul, map_zero] using congrArg ev h
    have hcoord : ∑ j ∈ s, g j * (pivotFamily N j : ι →₀ R) k.1 = 0 := by
      simpa only [ev, LinearMap.comp_apply, Finsupp.lapply_apply, smul_eq_mul,
        Submodule.coe_subtype] using hcoord₀
    have hterm (j : PivotIndex N) (hjs : j ∈ s) (hjk : j ≠ k) :
        g j * (pivotFamily N j : ι →₀ R) k.1 = 0 := by
      by_cases hgj : g j = 0
      · simp [hgj]
      have hjt : j ∈ t := Finset.mem_filter.mpr ⟨hjs, hgj⟩
      have hjle : j.1 ≤ k.1 := hkmax j hjt
      have hjne : j.1 ≠ k.1 := fun hj => hjk (Subtype.ext hj)
      have hjlt : j.1 < k.1 := lt_of_le_of_ne hjle hjne
      have hpzero : (pivotFamily N j : ι →₀ R) k.1 = 0 := by
        change leadingPivot N j.1 k.1 = 0
        exact (Finsupp.mem_supported' R _).mp (leadingPivot_supported N j.1) k.1
          (by simpa only [Set.mem_Iic] using not_le_of_gt hjlt)
      simp [hpzero]
    have hsingle : g k * (pivotFamily N k : ι →₀ R) k.1 = 0 := by
      calc
        g k * (pivotFamily N k : ι →₀ R) k.1 =
            ∑ j ∈ s, g j * (pivotFamily N j : ι →₀ R) k.1 := by
          symm
          apply Finset.sum_eq_single k
          · exact hterm
          · intro hk
            exact (hk hks).elim
        _ = 0 := hcoord
    have hmul : g k * leadingGenerator N k.1 = 0 := by
      simpa only [pivotFamily, leadingPivot_apply] using hsingle
    have hgk_zero : g k = 0 := (mul_eq_zero.mp hmul).resolve_right k.2
    exact hgk hgk_zero
  have hbounded : ∀ i : ι, ∀ y : N,
      (y.1.support : Set ι) ⊆ Set.Iic i → y ∈ S := by
    intro i
    apply wellFounded_lt.induction i
    intro i ih y hy
    have hy_supported : y.1 ∈ Finsupp.supported R R (Set.Iic i) :=
      (Finsupp.mem_supported R y.1).mpr hy
    have hy_leading : y.1 i ∈ leadingIdeal N i := by
      change (Finsupp.lapply i : (ι →₀ R) →ₗ[R] R) y.1 ∈ leadingIdeal N i
      exact Submodule.mem_map_of_mem ⟨y.2, hy_supported⟩
    obtain ⟨c, hc⟩ :=
      (Submodule.IsPrincipal.mem_iff_eq_smul_generator (leadingIdeal N i)).mp hy_leading
    have hc' : y.1 i = c * leadingGenerator N i := by
      simpa only [smul_eq_mul, leadingGenerator] using hc
    have lower_mem (z : N) (hz : (z.1.support : Set ι) ⊆ Set.Iio i) : z ∈ S := by
      by_cases hz0 : z = 0
      · subst z
        exact S.zero_mem
      have hzval : z.1 ≠ 0 := fun h => hz0 (Subtype.ext h)
      have hsupp : z.1.support.Nonempty := Finsupp.support_nonempty_iff.mpr hzval
      let j : ι := z.1.support.max' hsupp
      have hjmem : j ∈ z.1.support := Finset.max'_mem _ _
      have hji : j < i := hz hjmem
      apply ih j hji z
      intro q hq
      exact z.1.support.le_max' q hq
    by_cases ha : leadingGenerator N i ≠ 0
    · let k : PivotIndex N := ⟨i, ha⟩
      let z : N := y - c • pivotFamily N k
      have hzi : z.1 i = 0 := by
        change y.1 i - c * leadingPivot N i i = 0
        rw [leadingPivot_apply, hc', sub_self]
      have hz_supported : z.1 ∈ Finsupp.supported R R (Set.Iic i) := by
        change y.1 - c • leadingPivot N i ∈ Finsupp.supported R R (Set.Iic i)
        exact Submodule.sub_mem _ hy_supported
          (Submodule.smul_mem _ c (leadingPivot_supported N i))
      have hzlt : (z.1.support : Set ι) ⊆ Set.Iio i := by
        intro j hj
        have hji : j ≤ i := (Finsupp.mem_supported R z.1).mp hz_supported hj
        have hjne : j ≠ i := by
          intro h
          subst j
          exact (Finsupp.mem_support_iff.mp hj) hzi
        exact lt_of_le_of_ne hji hjne
      have hzS : z ∈ S := lower_mem z hzlt
      have hpS : pivotFamily N k ∈ S :=
        Submodule.subset_span (Set.mem_range_self k)
      have := S.add_mem hzS (S.smul_mem c hpS)
      change y - c • pivotFamily N k + c • pivotFamily N k ∈ S at this
      have hcancel : y - c • pivotFamily N k + c • pivotFamily N k = y :=
        sub_add_cancel y (c • pivotFamily N k)
      exact hcancel ▸ this
    · have hgen : leadingGenerator N i = 0 := not_ne_iff.mp ha
      have hyi : y.1 i = 0 := by simpa [hgen] using hc'
      have hylt : (y.1.support : Set ι) ⊆ Set.Iio i := by
        intro j hj
        have hji : j ≤ i := hy hj
        have hjne : j ≠ i := by
          intro h
          subst j
          exact (Finsupp.mem_support_iff.mp hj) hyi
        exact lt_of_le_of_ne hji hjne
      exact lower_mem y hylt
  have htop : (⊤ : Submodule R N) ≤ S := by
    intro y _
    by_cases hy0 : y = 0
    · subst y
      exact S.zero_mem
    have hyval : y.1 ≠ 0 := fun h => hy0 (Subtype.ext h)
    have hsupp : y.1.support.Nonempty := Finsupp.support_nonempty_iff.mpr hyval
    let i : ι := y.1.support.max' hsupp
    apply hbounded i y
    intro j hj
    exact y.1.support.le_max' j hj
  exact Module.Free.of_basis (Basis.mk hp htop)

private theorem submodule_free_aux
    {M : Type v} [AddCommMonoid M] [Module R M] [Module.Free R M]
    (N : Submodule R M) : Module.Free R N := by
  classical
  let ι := Module.Free.ChooseBasisIndex R M
  let b : Basis ι R M := Module.Free.chooseBasis R M
  obtain ⟨_, _⟩ := exists_wellFoundedLT ι
  let N' : Submodule R (ι →₀ R) := N.map b.repr.toLinearMap
  have hN' : Module.Free R N' := finsuppSubmodule_free N'
  exact Module.Free.of_equiv' hN' (b.repr.submoduleMap N).symm

/-- Let R be a commutative principal ideal domain, M a free R-module,
and N an R-submodule of M. Then N is free over R. The module M may
have arbitrary rank, and its carrier universe is independent of that of R. -/
theorem submodule_of_isPrincipalIdealRing
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Free R M]
    (N : Submodule R M) : Module.Free R N :=
  submodule_free_aux N

end Module.Free

namespace Module.Projective

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/-- Let R be a commutative principal ideal domain, M a projective
R-module, and N an R-submodule of M. Then N is projective over R.
No finite-generation or finite-rank condition is imposed. -/
theorem submodule_of_isPrincipalIdealRing
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Projective R M]
    (N : Submodule R M) : Module.Projective R N := by
  classical
  obtain ⟨F, addF, moduleF, freeF, ⟨i, s, hsi⟩⟩ :=
    Module.Projective.iff_split.mp (inferInstance : Module.Projective R M)
  let _ : AddCommMonoid F := addF
  let _ : Module R F := moduleF
  let _ : Module.Free R F := freeF
  have hi : Function.Injective i := by
    intro x y hxy
    have h := congrArg s hxy
    simpa only [← LinearMap.comp_apply, hsi, LinearMap.id_apply] using h
  let iN : N →ₗ[R] F := i.domRestrict N
  have hiN : Function.Injective iN := fun x y h => Subtype.ext (hi h)
  have hfree : Module.Free R (LinearMap.range iN) :=
    Module.Free.submodule_free_aux (R := R) (M := F) (LinearMap.range iN)
  let _ : Module.Free R (LinearMap.range iN) := hfree
  exact Module.Projective.of_equiv' (LinearEquiv.ofInjective iN hiN).symm

end Module.Projective
