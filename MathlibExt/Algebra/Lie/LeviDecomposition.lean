/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Lie.Semisimple.Defs

import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Levi decomposition

This file proves Weyl's complete reducibility theorem and the Levi decomposition for
finite-dimensional Lie algebras over fields of characteristic zero.
-/

@[expose] public section

namespace MathlibExt.Algebra.Lie.LandmarkWanted

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem levi_sum_repr
    {K V ι : Type*} [Semiring K] [AddCommMonoid V] [Module K V]
    [Fintype ι] (b : Module.Basis ι K V) (x : V) :
    ∑ i, b.repr x i • b i = x := by
  apply b.repr.injective
  ext j
  simp

private theorem levi_repr_eq_dual
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Finite ι] [DecidableEq ι] {B : LinearMap.BilinForm K V}
    (hB : B.Nondegenerate) (b : Module.Basis ι K V) (x : V) (i : ι) :
    b.repr x i = B (B.dualBasis hB b i) x := by
  let _ := Fintype.ofFinite ι
  conv_rhs => rw [← levi_sum_repr b x]
  rw [map_sum]
  simp_rw [map_smul]
  simp_rw [LinearMap.BilinForm.apply_dualBasis_left hB b]
  simp

private noncomputable def leviTraceKernel
    {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Module.Finite K M] : LieIdeal K L where
  __ := LinearMap.ker (LieModule.traceForm K L M)
  lie_mem := by
    intro x y hy
    change LieModule.traceForm K L M ⁅x, y⁆ = 0
    ext z
    rw [LieModule.traceForm_apply_lie_apply']
    have h := LinearMap.congr_fun (LinearMap.mem_ker.mp hy) (⁅x, z⁆ : L)
    simpa using h

private theorem leviTraceKernel_isSolvable
    {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [AddCommGroup M] [Module K M] [LieRingModule L M]
    [LieModule K L M] [Module.Finite K M] [LieModule.IsFaithful K L M] :
    LieAlgebra.IsSolvable (leviTraceKernel (K := K) (L := L) (M := M)) := by
  let I := leviTraceKernel (K := K) (L := L) (M := M)
  change LieAlgebra.IsSolvable I
  have htf : LieModule.traceForm K I M = 0 := by
    ext x y
    change LieModule.traceForm K L M x.1 y.1 = 0
    exact LinearMap.congr_fun (LinearMap.mem_ker.mp x.2) y
  let D' := LieAlgebra.derivedSeries K I 1
  have hnil : LieModule.IsNilpotent D' M :=
    LieModule.isNilpotent_derivedSeries_of_traceForm_eq_zero htf
  let D : LieIdeal K L := ⁅I, I⁆
  have hnil' (x : D) : IsNilpotent (LieModule.toEnd K D M x) := by
    have hxI : x.1 ∈ I := LieSubmodule.lie_le_left I I x.2
    have hxD' : (⟨x.1, hxI⟩ : I) ∈ LieAlgebra.derivedSeries K I 1 := by
      rw [LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_comap]
      exact x.2
    let x' : D' := ⟨⟨x.1, hxI⟩, hxD'⟩
    have hx := (LieModule.isNilpotent_iff_forall' (R := K)).mp hnil x'
    change IsNilpotent (LieModule.toEnd K L M x.1)
    change IsNilpotent (LieModule.toEnd K L M x'.1.1) at hx
    simpa [x'] using hx
  let φ := LieModule.toEnd K D M
  have hrange : LieRing.IsNilpotent φ.range := by
    rw [LieAlgebra.isNilpotent_iff_forall (R := K) (L := φ.range)]
    rintro ⟨_, ⟨x, rfl⟩⟩
    apply LieAlgebra.isNilpotent_ad_of_isNilpotent
    exact hnil' x
  let _ : LieRing.IsNilpotent φ.range := hrange
  have hφ : Function.Injective φ.rangeRestrict := by
    intro x y hxy
    apply Subtype.ext
    apply LieModule.IsFaithful.injective_toEnd (R := K) (L := L) (M := M)
    exact congr_arg Subtype.val hxy
  have hD : LieRing.IsNilpotent D := hφ.lieAlgebra_isNilpotent
  let _ : LieRing.IsNilpotent D := hD
  let _ : LieAlgebra.IsSolvable D := inferInstance
  obtain ⟨k, hk⟩ := LieAlgebra.IsSolvable.solvable K D
  rw [LieIdeal.derivedSeries_eq_bot_iff (R := K) (L := L) D] at hk
  change LieAlgebra.derivedSeriesOfIdeal K L k ⁅I, I⁆ = ⊥ at hk
  refine LieAlgebra.IsSolvable.mk (R := K) (L := I) (k := k + 1) ?_
  rw [LieIdeal.derivedSeries_eq_bot_iff (R := K) (L := L) I]
  rwa [LieAlgebra.derivedSeriesOfIdeal_add, LieAlgebra.derivedSeriesOfIdeal_succ,
    LieAlgebra.derivedSeriesOfIdeal_zero]

private theorem levi_traceForm_nondegenerate
    {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [LieAlgebra.IsSemisimple K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Module.Finite K M] [LieModule.IsFaithful K L M] :
    (LieModule.traceForm K L M).Nondegenerate := by
  let I := leviTraceKernel (K := K) (L := L) (M := M)
  have hsolv : LieAlgebra.IsSolvable I := leviTraceKernel_isSolvable
  let _ : LieAlgebra.IsSolvable I := hsolv
  have hI : I = ⊥ := LieAlgebra.HasTrivialRadical.eq_bot_of_isSolvable I
  rw [LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot]
  change (I : Submodule K L) = ⊥
  exact congr_arg LieSubmodule.toSubmodule hI

private noncomputable def leviCasimir
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [AddCommGroup M] [Module K M] [LieRingModule L M]
    [LieModule K L M] [Module.Free K M] [Module.Finite K M]
    (hβ : (LieModule.traceForm K L M).Nondegenerate) : Module.End K M := by
  classical
  let b := Module.Free.chooseBasis K L
  exact ∑ i, LieModule.toEnd K L M (b i) *
    LieModule.toEnd K L M ((LieModule.traceForm K L M).dualBasis hβ b i)

private theorem levi_trace_casimir
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [AddCommGroup M] [Module K M] [LieRingModule L M]
    [LieModule K L M] [Module.Free K M] [Module.Finite K M]
    (hβ : (LieModule.traceForm K L M).Nondegenerate) :
    LinearMap.trace K M (leviCasimir hβ) = (Module.finrank K L : K) := by
  classical
  let b := Module.Free.chooseBasis K L
  change LinearMap.trace K M (∑ i, LieModule.toEnd K L M (b i) *
    LieModule.toEnd K L M ((LieModule.traceForm K L M).dualBasis hβ b i)) = _
  rw [map_sum]
  simp_rw [Module.End.mul_eq_comp]
  simp_rw [← LieModule.traceForm_apply_apply]
  simp_rw [LinearMap.BilinForm.apply_dualBasis_right hβ
    (LinearMap.BilinForm.isSymm_iff.mpr (LieModule.traceForm_isSymm K L M)) b]
  simp [Module.finrank_eq_card_basis b]

private theorem levi_lie_dualBasis
    {K L M ι : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Fintype ι] [DecidableEq ι]
    (hβ : (LieModule.traceForm K L M).Nondegenerate)
    (b : Module.Basis ι K L) (x : L) (i : ι) :
    ⁅x, (LieModule.traceForm K L M).dualBasis hβ b i⁆ =
      -∑ j, b.repr ⁅x, b j⁆ i •
        (LieModule.traceForm K L M).dualBasis hβ b j := by
  let d := (LieModule.traceForm K L M).dualBasis hβ b
  apply d.repr.injective
  ext j
  rw [LinearMap.BilinForm.dualBasis_repr_apply]
  rw [LieModule.traceForm_apply_lie_apply']
  rw [← levi_repr_eq_dual hβ b ⁅x, b j⁆ i]
  simp [d, Finsupp.single_apply]

private theorem levi_casimir_commute
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [AddCommGroup M] [Module K M] [LieRingModule L M]
    [LieModule K L M] [Module.Free K M] [Module.Finite K M]
    (hβ : (LieModule.traceForm K L M).Nondegenerate) (x : L) :
    Commute (leviCasimir hβ) (LieModule.toEnd K L M x) := by
  classical
  let b := Module.Free.chooseBasis K L
  let d := (LieModule.traceForm K L M).dualBasis hβ b
  let ρ := LieModule.toEnd K L M
  change Commute (∑ i, ρ (b i) * ρ (d i)) (ρ x)
  rw [commute_iff_eq]
  rw [← sub_eq_zero]
  calc
    (∑ i, ρ (b i) * ρ (d i)) * ρ x - ρ x * (∑ i, ρ (b i) * ρ (d i)) =
        -(∑ i, (ρ ⁅x, b i⁆ * ρ (d i) + ρ (b i) * ρ ⁅x, d i⁆)) := by
          rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
            ← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [LieHom.map_lie ρ, LieHom.map_lie ρ, Ring.lie_def, Ring.lie_def]
          noncomm_ring
    _ = 0 := by
      have hxb (i) : ρ ⁅x, b i⁆ =
          ∑ j, b.repr ⁅x, b i⁆ j • ρ (b j) := by
        conv_lhs => rw [← levi_sum_repr b ⁅x, b i⁆]
        rw [map_sum]
        simp_rw [map_smul]
      have hxd (i) : ρ ⁅x, d i⁆ =
          -∑ j, b.repr ⁅x, b j⁆ i • ρ (d j) := by
        rw [levi_lie_dualBasis hβ b x i]
        rw [map_neg, map_sum]
        simp_rw [map_smul]
        rfl
      rw [Finset.sum_add_distrib]
      simp_rw [hxb, hxd]
      simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
        mul_neg, Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
      simp

private theorem levi_casimir_range_le
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [AddCommGroup M] [Module K M] [LieRingModule L M]
    [LieModule K L M] [Module.Free K M] [Module.Finite K M]
    (hβ : (LieModule.traceForm K L M).Nondegenerate) (W : Submodule K M)
    (hW : ∀ (x : L) (m : M), LieModule.toEnd K L M x m ∈ W) :
    LinearMap.range (leviCasimir hβ) ≤ W := by
  classical
  rintro _ ⟨m, rfl⟩
  let b := Module.Free.chooseBasis K L
  let d := (LieModule.traceForm K L M).dualBasis hβ b
  change (∑ i, LieModule.toEnd K L M (b i) * LieModule.toEnd K L M (d i)) m ∈ W
  rw [LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro i _
  rw [Module.End.mul_apply]
  exact hW (b i) _

private theorem levi_isKilling_killingCompl
    {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [LieAlgebra.IsSemisimple K L] (I : LieIdeal K L) :
    LieAlgebra.IsKilling K I.killingCompl := by
  let _ : LieAlgebra.IsKilling K L := inferInstance
  let H := I.killingCompl
  have hcompl : IsCompl I H := I.isCompl_killingCompl
  have hB := LieAlgebra.IsKilling.killingForm_nondegenerate K L
  have hrefl := (LieModule.traceForm_isSymm K L L).isRefl
  have horth : (killingForm K L).orthogonal H.toSubmodule = I.toSubmodule := by
    change (killingForm K L).orthogonal
      ((killingForm K L).orthogonal I.toSubmodule) = I.toSubmodule
    exact LinearMap.BilinForm.orthogonal_orthogonal hB hrefl I.toSubmodule
  have hdisj : Disjoint H.toSubmodule
      ((killingForm K L).orthogonal H.toSubmodule) := by
    rw [horth]
    exact LieSubmodule.disjoint_toSubmodule.mpr hcompl.disjoint.symm
  have hres : ((killingForm K L).restrict H.toSubmodule).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal
      (killingForm K L) hrefl hdisj
  have hk : (killingForm K H).Nondegenerate := by
    rw [LieIdeal.killingForm_eq]
    exact hres
  refine LieAlgebra.IsKilling.mk ?_
  rw [eq_bot_iff]
  intro x hx
  rw [LieSubmodule.mem_bot]
  apply hk.2 x
  intro y
  exact (LieIdeal.mem_killingCompl K H ⊤).mp hx y (LieSubmodule.mem_top y)

private theorem levi_isFaithful_killingCompl_ker
    {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [LieAlgebra.IsSemisimple K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] :
    LieModule.IsFaithful K (LieModule.ker K L M).killingCompl M := by
  let I := LieModule.ker K L M
  let H := I.killingCompl
  let _ : LieAlgebra.IsKilling K L := inferInstance
  have hcompl : IsCompl I H := I.isCompl_killingCompl
  refine ⟨?_⟩
  intro x y hxy
  apply Subtype.ext
  change LieModule.toEnd K L M x.1 = LieModule.toEnd K L M y.1 at hxy
  have hker : x.1 - y.1 ∈ I := by
    change LieModule.toEnd K L M (x.1 - y.1) = 0
    rw [map_sub, sub_eq_zero]
    exact hxy
  have hH : x.1 - y.1 ∈ H := H.sub_mem x.2 y.2
  have hz : x.1 - y.1 ∈ I ⊓ H := ⟨hker, hH⟩
  rw [hcompl.inf_eq_bot] at hz
  change x.1 - y.1 = 0 at hz
  exact sub_eq_zero.mp hz

private theorem levi_lie_top_eq_top
    {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieAlgebra.IsSemisimple K L] :
    ⁅(⊤ : LieIdeal K L), (⊤ : LieIdeal K L)⁆ = ⊤ := by
  apply top_unique
  calc
    (⊤ : LieIdeal K L) = sSup {I : LieIdeal K L | IsAtom I} :=
      LieAlgebra.IsSemisimple.sSup_atoms_eq_top.symm
    _ ≤ ⁅(⊤ : LieIdeal K L), (⊤ : LieIdeal K L)⁆ := by
      apply sSup_le
      intro I hI
      rw [← lie_eq_self_of_isAtom_of_nonabelian I hI
        (LieAlgebra.IsSemisimple.non_abelian_of_isAtom I hI)]
      exact LieSubmodule.mono_lie le_top le_top

private theorem levi_codim_one_action_mem
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [LieAlgebra.IsSemisimple K L] [AddCommGroup M] [Module K M]
    [LieRingModule L M] [LieModule K L M] [Module.Finite K M]
    (W : LieSubmodule K L M) (hW : Module.finrank K (M ⧸ W) = 1) :
    ∀ (x : L) (m : M), ⁅x, m⁆ ∈ W := by
  let Q := M ⧸ W
  have hendcomm (f g : Module.End K Q) : Commute f g := by
    obtain ⟨a, ha, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hW f
    obtain ⟨b, hb, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hW g
    rw [ha, hb]
    ext q
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
    rw [mul_comm]
  have hbracket (x y : L) : LieModule.toEnd K L Q ⁅x, y⁆ = 0 := by
    rw [LieHom.map_lie, Ring.lie_def, (hendcomm _ _).eq, sub_self]
  have hle : ⁅(⊤ : LieIdeal K L), (⊤ : LieIdeal K L)⁆ ≤ LieModule.ker K L Q := by
    rw [LieSubmodule.lie_le_iff]
    intro x _ y _
    change LieModule.toEnd K L Q ⁅x, y⁆ = 0
    exact hbracket x y
  have hker : LieModule.ker K L Q = ⊤ := by
    apply top_unique
    rw [← levi_lie_top_eq_top]
    exact hle
  intro x m
  apply (LieSubmodule.Quotient.mk_eq_zero W).mp
  rw [LieModuleHom.map_lie]
  have hx : x ∈ LieModule.ker K L Q := by
    rw [hker]
    exact LieSubmodule.mem_top x
  change LieModule.toEnd K L Q x ((LieSubmodule.Quotient.mk' W) m) = 0
  change LieModule.toEnd K L Q x = 0 at hx
  rw [hx]
  rfl

private theorem levi_exists_isCompl_of_trivial_action
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (htriv : ∀ (x : L) (m : M), ⁅x, m⁆ = 0) (W : LieSubmodule K L M) :
    ∃ U : LieSubmodule K L M, IsCompl W U := by
  obtain ⟨U, hU⟩ := W.toSubmodule.exists_isCompl
  let U' : LieSubmodule K L M :=
    { __ := U
      lie_mem := by
        intro x m _
        rw [htriv]
        exact zero_mem U }
  exact ⟨U', LieSubmodule.isCompl_toSubmodule.mp hU⟩

private def leviZeroFitting
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (c : Module.End K M)
    (hc : ∀ x : L, Commute c (LieModule.toEnd K L M x)) : LieSubmodule K L M where
  __ := c.maxGenEigenspace 0
  lie_mem := by
    intro x m hm
    exact Module.End.mapsTo_maxGenEigenspace_of_comm (hc x) 0 hm

private theorem levi_finrank_quotient_comap
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Module.Finite K M] (V W : LieSubmodule K L M) (hVW : V ⊔ W = ⊤) :
    Module.finrank K (V ⧸ W.comap V.incl) = Module.finrank K (M ⧸ W) := by
  change Module.finrank K (V ⧸ (W.comap V.incl).toSubmodule) =
    Module.finrank K (M ⧸ W.toSubmodule)
  let f : V →ₗ[K] M ⧸ W := W.toSubmodule.mkQ.comp V.toSubmodule.subtype
  have hker : LinearMap.ker f = (W.comap V.incl).toSubmodule := by
    ext v
    simp [f]
  have hsurj : Function.Surjective f := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ m =>
      have hm : m ∈ V ⊔ W := by
        rw [hVW]
        exact LieSubmodule.mem_top m
      rw [LieSubmodule.mem_sup] at hm
      obtain ⟨v, hv, w, hw, rfl⟩ := hm
      refine ⟨⟨v, hv⟩, ?_⟩
      change LieSubmodule.Quotient.mk (N := W) v =
        LieSubmodule.Quotient.mk (N := W) (v + w)
      apply (Submodule.Quotient.eq W.toSubmodule).2
      have hw' : w ∈ W.toSubmodule := hw
      simpa only [sub_add_cancel_left, neg_mem_iff] using hw'
  calc
    Module.finrank K (V ⧸ (W.comap V.incl).toSubmodule) =
        Module.finrank K (V ⧸ LinearMap.ker f) := by rw [hker]
    _ = Module.finrank K (LinearMap.range f) := f.quotKerEquivRange.finrank_eq
    _ = Module.finrank K (M ⧸ W) := by
      exact (LinearEquiv.ofTop (LinearMap.range f)
        (LinearMap.range_eq_top.mpr hsurj)).finrank_eq

private theorem levi_isCompl_map_of_isCompl_comap
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (V W : LieSubmodule K L M) (hVW : V ⊔ W = ⊤)
    (U : LieSubmodule K L V) (hU : IsCompl (W.comap V.incl) U) :
    IsCompl W (U.map V.incl) := by
  constructor
  · rw [disjoint_iff]
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxW, hxU⟩ := hx
    change x ∈ U.toSubmodule.map V.toSubmodule.subtype at hxU
    rw [Submodule.mem_map] at hxU
    obtain ⟨u, hu, rfl⟩ := hxU
    have huW : u ∈ W.comap V.incl := hxW
    have hu0 : u ∈ (W.comap V.incl) ⊓ U := ⟨huW, hu⟩
    rw [hU.inf_eq_bot] at hu0
    change u = 0 at hu0
    change (u.1 : M) = 0
    exact congr_arg Subtype.val hu0
  · rw [codisjoint_iff]
    apply top_unique
    intro x _
    have hx : x ∈ V ⊔ W := by
      rw [hVW]
      exact LieSubmodule.mem_top x
    rw [LieSubmodule.mem_sup] at hx
    obtain ⟨v, hv, w, hw, rfl⟩ := hx
    let v' : V := ⟨v, hv⟩
    have hv' : v' ∈ (W.comap V.incl) ⊔ U := by
      rw [hU.sup_eq_top]
      exact LieSubmodule.mem_top v'
    rw [LieSubmodule.mem_sup] at hv'
    obtain ⟨a, ha, b, hb, hab⟩ := hv'
    rw [LieSubmodule.mem_sup]
    refine ⟨a.1 + w, W.add_mem ha hw, b.1, ?_, ?_⟩
    · exact LieSubmodule.mem_map_of_mem hb
    · apply_fun Subtype.val at hab
      dsimp [v'] at hab
      rw [← hab]
      abel

private theorem levi_codim_one_complement_aux
    (n : ℕ) {K L M : Type*} [Field K] [CharZero K] [LieRing L]
    [LieAlgebra K L] [Module.Finite K L] [LieAlgebra.IsSemisimple K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Module.Finite K M] (W : LieSubmodule K L M)
    (hquot : Module.finrank K (M ⧸ W) = 1) (_hlt : Module.finrank K W < n) :
    ∃ U : LieSubmodule K L M, IsCompl W U := by
  classical
  let I := LieModule.ker K L M
  let H := I.killingCompl
  let _ : LieAlgebra.IsKilling K L := inferInstance
  have hcompl : IsCompl I H := I.isCompl_killingCompl
  have hHkilling : LieAlgebra.IsKilling K H := levi_isKilling_killingCompl I
  let _ : LieAlgebra.IsKilling K H := hHkilling
  let _ : LieAlgebra.IsSemisimple K H := inferInstance
  by_cases hH0 : Module.finrank K H = 0
  · have hHbot : H = ⊥ := by
      rw [← LieSubmodule.toSubmodule_inj]
      exact Submodule.finrank_eq_zero.mp hH0
    have hItop : I = ⊤ := by
      have hs := hcompl.sup_eq_top
      rwa [hHbot, sup_bot_eq] at hs
    apply levi_exists_isCompl_of_trivial_action (W := W)
    intro x m
    have hx : x ∈ I := by
      rw [hItop]
      exact LieSubmodule.mem_top x
    change LieModule.toEnd K L M x = 0 at hx
    change LieModule.toEnd K L M x m = 0
    rw [hx]
    rfl
  · have hfaithful : LieModule.IsFaithful K H M :=
      levi_isFaithful_killingCompl_ker
    let _ : LieModule.IsFaithful K H M := hfaithful
    have hβ : (LieModule.traceForm K H M).Nondegenerate :=
      levi_traceForm_nondegenerate
    let c := leviCasimir hβ
    have hcL (x : L) : Commute c (LieModule.toEnd K L M x) := by
      have hx : x ∈ I ⊔ H := by
        rw [hcompl.sup_eq_top]
        exact LieSubmodule.mem_top x
      rw [LieSubmodule.mem_sup] at hx
      obtain ⟨i, hi, h, hh, rfl⟩ := hx
      have hi0 : LieModule.toEnd K L M i = 0 := by
        exact hi
      have hch := levi_casimir_commute hβ (⟨h, hh⟩ : H)
      change Commute c (LieModule.toEnd K L M h) at hch
      rw [map_add, hi0, zero_add]
      exact hch
    let V := leviZeroFitting c hcL
    let P := ⨅ k : ℕ, LinearMap.range (c ^ k)
    have hV : V.toSubmodule = ⨆ k : ℕ, LinearMap.ker (c ^ k) := by
      change c.maxGenEigenspace 0 = _
      rw [← Module.End.iSup_genEigenspace_eq]
      simp_rw [Module.End.genEigenspace_zero_nat]
    have hVP : IsCompl V.toSubmodule P := by
      rw [hV]
      exact LinearMap.isCompl_iSup_ker_pow_iInf_range_pow c
    have haction := levi_codim_one_action_mem W hquot
    have hcW : LinearMap.range c ≤ W.toSubmodule := by
      apply levi_casimir_range_le hβ W.toSubmodule
      intro x m
      exact haction x.1 m
    have hPW : P ≤ W.toSubmodule := by
      calc
        P ≤ LinearMap.range (c ^ 1) := iInf_le _ 1
        _ = LinearMap.range c := by rw [pow_one]
        _ ≤ W.toSubmodule := hcW
    have hPne : P ≠ ⊥ := by
      intro hP
      have hVtop : V.toSubmodule = ⊤ := by
        have hs := hVP.sup_eq_top
        rwa [hP, sup_bot_eq] at hs
      have hpoint : ∀ m : M, ∃ k : ℕ, (c ^ k) m = 0 := by
        intro m
        have hm : m ∈ c.maxGenEigenspace 0 := by
          change m ∈ V.toSubmodule
          rw [hVtop]
          exact Submodule.mem_top
        simpa using (Module.End.mem_maxGenEigenspace c 0 m).mp hm
      have hnil : IsNilpotent c :=
        ((LinearMap.charpoly_nilpotent_tfae c).out 3 1).mp hpoint
      have htrace0 : LinearMap.trace K M c = 0 :=
        (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero
      rw [levi_trace_casimir hβ] at htrace0
      exact (Nat.cast_ne_zero.mpr hH0) htrace0
    have hVWsub : V.toSubmodule ⊔ W.toSubmodule = ⊤ := by
      apply top_unique
      rw [← hVP.sup_eq_top]
      exact sup_le_sup le_rfl hPW
    have hVW : V ⊔ W = ⊤ := by
      rw [← LieSubmodule.toSubmodule_inj]
      exact hVWsub
    have hInfLt : V.toSubmodule ⊓ W.toSubmodule < W.toSubmodule := by
      refine lt_of_le_of_ne inf_le_right ?_
      intro heq
      have hWV : W.toSubmodule ≤ V.toSubmodule := by
        rw [← heq]
        exact inf_le_left
      have hPV : P ≤ V.toSubmodule := hPW.trans hWV
      apply hPne
      rw [← le_bot_iff, ← hVP.inf_eq_bot]
      exact le_inf hPV le_rfl
    let W' := W.comap V.incl
    have hmapW' : W'.map V.incl = V ⊓ W := by
      ext x
      constructor
      · intro hx
        rw [LieSubmodule.mem_map] at hx
        obtain ⟨w, hw, rfl⟩ := hx
        exact ⟨w.2, hw⟩
      · rintro ⟨hxV, hxW⟩
        exact LieSubmodule.mem_map_of_mem (m := (⟨x, hxV⟩ : V)) hxW
    have hfinW' : Module.finrank K W' = Module.finrank K ↑(V ⊓ W) := by
      rw [← hmapW']
      exact (LieSubmodule.equivMapOfInjective W' V.injective_incl).toLinearEquiv.finrank_eq
    have hlt' : Module.finrank K W' < Module.finrank K W := by
      rw [hfinW']
      exact Submodule.finrank_lt_finrank_of_lt hInfLt
    have hquot' : Module.finrank K (V ⧸ W') = 1 := by
      rw [levi_finrank_quotient_comap V W hVW]
      exact hquot
    obtain ⟨U, hU⟩ := levi_codim_one_complement_aux (Module.finrank K W) W' hquot' hlt'
    exact ⟨U.map V.incl, levi_isCompl_map_of_isCompl_comap V W hVW U hU⟩
termination_by n
decreasing_by exact _hlt

private theorem levi_codim_one_complement
    {K L M : Type*} [Field K] [CharZero K] [LieRing L]
    [LieAlgebra K L] [Module.Finite K L] [LieAlgebra.IsSemisimple K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Module.Finite K M] (W : LieSubmodule K L M)
    (hquot : Module.finrank K (M ⧸ W) = 1) :
    ∃ U : LieSubmodule K L M, IsCompl W U :=
  levi_codim_one_complement_aux (Module.finrank K W + 1) W hquot (Nat.lt_succ_self _)

private def leviHomVanishing
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (W : LieSubmodule K L M) : LieSubmodule K L (M →ₗ[K] W) where
  carrier := {f | ∀ w : W, f w = 0}
  zero_mem' w := rfl
  add_mem' {f g} hf hg w := by rw [LinearMap.add_apply, hf, hg, add_zero]
  smul_mem' a f hf w := by rw [LinearMap.smul_apply, hf, smul_zero]
  lie_mem := by
    intro x f hf w
    rw [LieHom.lie_apply]
    rw [hf, lie_zero]
    have hfw := hf (⟨⁅x, w.1⁆, W.lie_mem w.2⟩ : W)
    simpa using hfw

private def leviHomScalarMaps
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (W : LieSubmodule K L M) : LieSubmodule K L (M →ₗ[K] W) where
  carrier := {f | ∃ a : K, ∀ w : W, f w = a • w}
  zero_mem' := ⟨0, fun w ↦ by simp⟩
  add_mem' {f g} := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, fun w ↦ ?_⟩
    rw [LinearMap.add_apply, ha, hb, add_smul]
  smul_mem' c f := by
    rintro ⟨a, ha⟩
    refine ⟨c * a, fun w ↦ ?_⟩
    rw [LinearMap.smul_apply, ha, mul_smul]
  lie_mem := by
    intro x f hf
    obtain ⟨a, ha⟩ := hf
    refine ⟨0, fun w ↦ ?_⟩
    rw [LieHom.lie_apply, ha, lie_smul]
    have haw := ha (⟨⁅x, w.1⁆, W.lie_mem w.2⟩ : W)
    rw [haw]
    have hxw : ⁅x, w⁆ = (⟨⁅x, w.1⁆, W.lie_mem w.2⟩ : W) := rfl
    rw [hxw, sub_self, zero_smul]

private theorem levi_scalar_unique
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (W : LieSubmodule K L M) (hW : W ≠ ⊥) {a b : K}
    (h : ∀ w : W, a • w = b • w) : a = b := by
  have hWsub : W.toSubmodule ≠ ⊥ := by
    intro h
    apply hW
    rw [← LieSubmodule.toSubmodule_inj]
    exact h
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWsub
  have hab : a • w = b • w := congrArg Subtype.val (h ⟨w, hw⟩)
  have hz : (a - b) • w = 0 := by rw [sub_smul, hab, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hw0)

private noncomputable def leviHomScalar
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (W : LieSubmodule K L M) (hW : W ≠ ⊥) :
    leviHomScalarMaps W →ₗ[K] K where
  toFun f := Classical.choose f.2
  map_add' f g := by
    apply levi_scalar_unique W hW
    intro w
    calc
      Classical.choose (f + g).property • w = (f + g : M →ₗ[K] W) w :=
        (Classical.choose_spec (f + g).property w).symm
      _ = f.1 w + g.1 w := rfl
      _ = Classical.choose f.property • w + Classical.choose g.property • w := by
        rw [Classical.choose_spec f.property w, Classical.choose_spec g.property w]
      _ = (Classical.choose f.property + Classical.choose g.property) • w :=
        (add_smul _ _ _).symm
  map_smul' c f := by
    apply levi_scalar_unique W hW
    intro w
    calc
      Classical.choose (c • f).property • w = (c • f : M →ₗ[K] W) w :=
        (Classical.choose_spec (c • f).property w).symm
      _ = c • f.1 w := rfl
      _ = c • (Classical.choose f.property • w) := by
        rw [Classical.choose_spec f.property w]
      _ = (c * Classical.choose f.property) • w := (mul_smul _ _ _).symm

private theorem leviHomScalar_apply
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (W : LieSubmodule K L M) (hW : W ≠ ⊥)
    (f : leviHomScalarMaps W) (w : W) :
    f.1 w = leviHomScalar W hW f • w :=
  Classical.choose_spec f.2 w

private theorem leviHomScalar_ker
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (W : LieSubmodule K L M) (hW : W ≠ ⊥) :
    LinearMap.ker (leviHomScalar W hW) =
      (leviHomVanishing W).toSubmodule.comap
        (leviHomScalarMaps W).toSubmodule.subtype := by
  ext f
  constructor
  · intro hf
    change leviHomScalar W hW f = 0 at hf
    change ∀ w : W, f.1 w = 0
    intro w
    rw [leviHomScalar_apply W hW f w, hf, zero_smul]
  · intro hf
    change leviHomScalar W hW f = 0
    apply levi_scalar_unique W hW
    intro w
    rw [zero_smul]
    exact (leviHomScalar_apply W hW f w).symm.trans (hf w)

private theorem leviHomScalar_surjective
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (W : LieSubmodule K L M) (hW : W ≠ ⊥) :
    Function.Surjective (leviHomScalar W hW) := by
  obtain ⟨Q, hQ⟩ := W.toSubmodule.exists_isCompl
  let p : M →ₗ[K] W := W.toSubmodule.projectionOnto Q hQ
  have hp (w : W) : p w = w := by
    exact Submodule.projectionOnto_apply_left hQ w
  let pv : leviHomScalarMaps W :=
    ⟨p, 1, fun w ↦ by rw [hp, one_smul]⟩
  have hpv : leviHomScalar W hW pv = 1 := by
    apply levi_scalar_unique W hW
    intro w
    rw [one_smul]
    exact (leviHomScalar_apply W hW pv w).symm.trans (hp w)
  intro a
  refine ⟨a • pv, ?_⟩
  rw [LinearMap.map_smul, hpv, smul_eq_mul, mul_one]

private theorem leviHomScalarMaps_quotient_finrank
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Module.Finite K M] (W : LieSubmodule K L M) (hW : W ≠ ⊥) :
    Module.finrank K
        (leviHomScalarMaps W ⧸
          (leviHomVanishing W).comap (leviHomScalarMaps W).incl) = 1 := by
  let s := leviHomScalar W hW
  have hsKer : LinearMap.ker s =
      ((leviHomVanishing W).comap (leviHomScalarMaps W).incl).toSubmodule := by
    exact leviHomScalar_ker W hW
  have hsRange : LinearMap.range s = ⊤ :=
    LinearMap.range_eq_top.mpr (leviHomScalar_surjective W hW)
  change Module.finrank K
      (leviHomScalarMaps W ⧸
        ((leviHomVanishing W).comap (leviHomScalarMaps W).incl).toSubmodule) = 1
  rw [← hsKer, s.quotKerEquivRange.finrank_eq, hsRange]
  rw [finrank_top]
  exact Module.finrank_self K

private theorem levi_lie_mem_HomVanishing_of_mem_scalarMaps
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (W : LieSubmodule K L M) (f : leviHomScalarMaps W) (x : L) :
    ⁅x, (f.1 : M →ₗ[K] W)⁆ ∈ leviHomVanishing W := by
  obtain ⟨a, ha⟩ := f.2
  intro w
  rw [LieHom.lie_apply, ha, lie_smul]
  have haw := ha (⟨⁅x, w.1⁆, W.lie_mem w.2⟩ : W)
  rw [haw]
  have hxw : ⁅x, w⁆ = (⟨⁅x, w.1⁆, W.lie_mem w.2⟩ : W) := rfl
  rw [hxw, sub_self]

/-- Weyl's complete reducibility theorem for finite-dimensional modules over a
semisimple Lie algebra in characteristic zero. -/
public theorem _root_.LieModule.exists_isCompl_of_isSemisimple
    {K L M : Type*} [Field K] [CharZero K] [LieRing L]
    [LieAlgebra K L] [Module.Finite K L] [LieAlgebra.IsSemisimple K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Module.Finite K M] (W : LieSubmodule K L M) :
    ∃ U : LieSubmodule K L M, IsCompl W U := by
  by_cases hW : W = ⊥
  · subst W
    exact ⟨⊤, isCompl_bot_top⟩
  let V := leviHomScalarMaps W
  let Z := (leviHomVanishing W).comap V.incl
  have hfin : Module.finrank K (V ⧸ Z) = 1 :=
    leviHomScalarMaps_quotient_finrank W hW
  obtain ⟨T, hT⟩ := levi_codim_one_complement Z hfin
  obtain ⟨Q, hQ⟩ := W.toSubmodule.exists_isCompl
  let p : M →ₗ[K] W := W.toSubmodule.projectionOnto Q hQ
  have hp (w : W) : p w = w := Submodule.projectionOnto_apply_left hQ w
  let pv : V := ⟨p, 1, fun w ↦ by rw [hp, one_smul]⟩
  have hpvScalar : leviHomScalar W hW pv = 1 := by
    apply levi_scalar_unique W hW
    intro w
    rw [one_smul]
    exact (leviHomScalar_apply W hW pv w).symm.trans (hp w)
  have hpvMem : pv ∈ Z ⊔ T := by
    rw [hT.sup_eq_top]
    trivial
  rw [LieSubmodule.mem_sup] at hpvMem
  obtain ⟨z, hz, t, ht, hzt⟩ := hpvMem
  have hzScalar : leviHomScalar W hW z = 0 := by
    have hzKer : z ∈ LinearMap.ker (leviHomScalar W hW) := by
      rw [leviHomScalar_ker W hW]
      exact hz
    exact hzKer
  have htScalar : leviHomScalar W hW t = 1 := by
    have h := congrArg (fun f : V ↦ leviHomScalar W hW f) hzt
    rw [LinearMap.map_add, hzScalar, zero_add, hpvScalar] at h
    exact h
  have htApply (w : W) : t.1 w = w := by
    rw [leviHomScalar_apply W hW t w, htScalar, one_smul]
  have htInvariant (x : L) : ⁅x, (t.1 : M →ₗ[K] W)⁆ = 0 := by
    have hxZ : ⁅x, t⁆ ∈ Z := by
      exact levi_lie_mem_HomVanishing_of_mem_scalarMaps W t x
    have hxT : ⁅x, t⁆ ∈ T := T.lie_mem ht
    have hxBot : ⁅x, t⁆ ∈ (⊥ : LieSubmodule K L V) := by
      rw [← hT.inf_eq_bot]
      exact ⟨hxZ, hxT⟩
    have hxZero : ⁅x, t⁆ = 0 := by simpa using hxBot
    exact congrArg Subtype.val hxZero
  let U : LieSubmodule K L M :=
    { carrier := {m | t.1 m = 0}
      zero_mem' := LinearMap.map_zero t.1
      add_mem' := by
        intro a b ha hb
        change t.1 (a + b) = 0
        rw [LinearMap.map_add, ha, hb, add_zero]
      smul_mem' := by
        intro a m hm
        change t.1 (a • m) = 0
        rw [LinearMap.map_smul, hm, smul_zero]
      lie_mem := by
        intro x m hm
        have h := congrArg (fun f : M →ₗ[K] W ↦ f m) (htInvariant x)
        rw [LieHom.lie_apply, hm, lie_zero, zero_sub] at h
        exact neg_eq_zero.mp h }
  refine ⟨U, ?_⟩
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    intro m hm
    have htm : t.1 m = 0 := hm.2
    have hrest := htApply (⟨m, hm.1⟩ : W)
    have hm0 : m = 0 := by
      have h := congrArg Subtype.val hrest
      rw [htm] at h
      exact h.symm
    change m = 0
    exact hm0
  · rw [codisjoint_iff, eq_top_iff]
    intro m _
    rw [LieSubmodule.mem_sup]
    refine ⟨(t.1 m).1, (t.1 m).2, m - (t.1 m).1, ?_, ?_⟩
    · change t.1 (m - (t.1 m).1) = 0
      rw [LinearMap.map_sub, htApply (t.1 m), sub_self]
    · abel

private noncomputable def leviFactorAction
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (I : LieIdeal K L) (hI : ∀ x ∈ I, ∀ m : M, ⁅x, m⁆ = 0) :
    (L ⧸ I) →ₗ⁅K⁆ Module.End K M := by
  let f := LieModule.toEnd K L M
  have hker : I.toSubmodule ≤ LinearMap.ker (f : L →ₗ[K] Module.End K M) := by
    intro x hx
    rw [LinearMap.mem_ker]
    ext m
    exact hI x hx m
  exact
    { I.toSubmodule.liftQ (f : L →ₗ[K] Module.End K M) hker with
      map_lie' := by
        intro x y
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          induction y using Submodule.Quotient.induction_on with
          | _ y =>
            rw [← LieSubmodule.Quotient.mk_bracket]
            change f ⁅x, y⁆ = ⁅f x, f y⁆
            exact f.map_lie x y }

@[instance_reducible] private noncomputable def leviFactorLieRingModule
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (I : LieIdeal K L) (hI : ∀ x ∈ I, ∀ m : M, ⁅x, m⁆ = 0) :
    LieRingModule (L ⧸ I) M :=
  LieRingModule.compLieHom M (leviFactorAction I hI)

private theorem leviFactorLieModule
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (I : LieIdeal K L) (hI : ∀ x ∈ I, ∀ m : M, ⁅x, m⁆ = 0) :
    @LieModule K (L ⧸ I) M _ _ _ _ _ (leviFactorLieRingModule I hI) :=
  LieModule.compLieHom M (leviFactorAction I hI)

private theorem leviFactorAction_mk
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (I : LieIdeal K L) (hI : ∀ x ∈ I, ∀ m : M, ⁅x, m⁆ = 0)
    (x : L) (m : M) :
    leviFactorAction I hI (LieSubmodule.Quotient.mk x) m = ⁅x, m⁆ := by
  rfl

private noncomputable def leviFactorSubmodule
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (I : LieIdeal K L) (hI : ∀ x ∈ I, ∀ m : M, ⁅x, m⁆ = 0)
    (W : LieSubmodule K L M) :
    letI := leviFactorLieRingModule I hI
    LieSubmodule K (L ⧸ I) M := by
  letI := leviFactorLieRingModule I hI
  exact
    { W.toSubmodule with
      lie_mem := by
        intro x m hm
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          change leviFactorAction I hI (LieSubmodule.Quotient.mk x) m ∈ W
          rw [leviFactorAction_mk I hI]
          exact W.lie_mem hm }

private noncomputable def leviUnfactorSubmodule
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (I : LieIdeal K L) (hI : ∀ x ∈ I, ∀ m : M, ⁅x, m⁆ = 0) :
    letI := leviFactorLieRingModule I hI
    LieSubmodule K (L ⧸ I) M → LieSubmodule K L M := by
  letI := leviFactorLieRingModule I hI
  intro W
  exact
    { W.toSubmodule with
      lie_mem := by
        intro x m hm
        rw [← leviFactorAction_mk I hI]
        exact W.lie_mem hm }

private theorem levi_factor_exists_isCompl
    {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] (I : LieIdeal K L)
    [LieAlgebra.IsSemisimple K (L ⧸ I)]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Module.Finite K M]
    (hI : ∀ x ∈ I, ∀ m : M, ⁅x, m⁆ = 0) (W : LieSubmodule K L M) :
    ∃ U : LieSubmodule K L M, IsCompl W U := by
  let _ := leviFactorLieRingModule I hI
  let _ := leviFactorLieModule I hI
  obtain ⟨U, hU⟩ :=
    LieModule.exists_isCompl_of_isSemisimple (leviFactorSubmodule I hI W)
  refine ⟨leviUnfactorSubmodule I hI U, ?_⟩
  rw [← LieSubmodule.isCompl_toSubmodule] at hU ⊢
  exact hU

private def leviQuotientMk
    {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    (I : LieIdeal K L) : L →ₗ⁅K⁆ L ⧸ I :=
  { (LieSubmodule.Quotient.mk' I : L →ₗ[K] L ⧸ I) with
    map_lie' := by
      intro x y
      change LieSubmodule.Quotient.mk ⁅x, y⁆ =
        ⁅LieSubmodule.Quotient.mk x, LieSubmodule.Quotient.mk y⁆
      exact LieSubmodule.Quotient.mk_bracket I x y }

@[simp] private theorem leviQuotientMk_apply
    {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    (I : LieIdeal K L) (x : L) :
    leviQuotientMk I x = LieSubmodule.Quotient.mk x := by
  rfl

private theorem leviQuotientMk_surjective
    {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    (I : LieIdeal K L) : Function.Surjective (leviQuotientMk I) := by
  intro y
  obtain ⟨x, hx⟩ := LieSubmodule.Quotient.surjective_mk' I y
  exact ⟨x, (leviQuotientMk_apply I x).trans hx⟩

@[simp] private theorem leviQuotientMk_ker
    {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    (I : LieIdeal K L) : (leviQuotientMk I).ker = I := by
  ext x
  rw [LieHom.mem_ker, leviQuotientMk_apply]
  exact LieSubmodule.Quotient.mk_eq_zero (N := I)

private theorem levi_isSolvable_of_ker_quotient
    {K L L' : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing L'] [LieAlgebra K L'] (f : L →ₗ⁅K⁆ L')
    (hf : Function.Surjective f) [LieAlgebra.IsSolvable f.ker]
    [LieAlgebra.IsSolvable L'] : LieAlgebra.IsSolvable L := by
  obtain ⟨k, hk⟩ := LieAlgebra.IsSolvable.solvable K L'
  obtain ⟨l, hl⟩ := LieAlgebra.IsSolvable.solvable K f.ker
  apply LieAlgebra.IsSolvable.mk (R := K) (L := L) (k := l + k)
  change LieAlgebra.derivedSeriesOfIdeal K L (l + k) ⊤ = ⊥
  rw [LieAlgebra.derivedSeriesOfIdeal_add]
  rw [LieIdeal.derivedSeries_eq_bot_iff] at hl
  apply le_bot_iff.mp
  rw [← hl]
  apply LieAlgebra.derivedSeriesOfIdeal_mono
  rw [← LieIdeal.map_eq_bot_iff]
  rw [LieIdeal.derivedSeries_map_eq k hf, hk]

private def leviComapMap
    {K L L' : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing L'] [LieAlgebra K L'] (f : L →ₗ⁅K⁆ L') (J : LieIdeal K L') :
    J.comap f →ₗ⁅K⁆ J where
  toFun x := ⟨f x.1, x.2⟩
  map_add' x y := Subtype.ext (f.map_add x.1 y.1)
  map_smul' c x := Subtype.ext (f.map_smul c x.1)
  map_lie' := by
    intro x y
    apply Subtype.ext
    exact f.map_lie x.1 y.1

private theorem leviComapMap_surjective
    {K L L' : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing L'] [LieAlgebra K L'] (f : L →ₗ⁅K⁆ L')
    (hf : Function.Surjective f) (J : LieIdeal K L') :
    Function.Surjective (leviComapMap f J) := by
  intro y
  obtain ⟨x, hx⟩ := hf y
  have hxJ : x ∈ J.comap f := by
    change f x ∈ J
    rw [hx]
    exact y.2
  refine ⟨⟨x, hxJ⟩, ?_⟩
  apply Subtype.ext
  exact hx

private def leviComapMapKerToKer
    {K L L' : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing L'] [LieAlgebra K L'] (f : L →ₗ⁅K⁆ L') (J : LieIdeal K L') :
    (leviComapMap f J).ker →ₗ⁅K⁆ f.ker where
  toFun x := ⟨x.1.1, by
    rw [LieHom.mem_ker]
    have hx : leviComapMap f J x.1 = 0 := LieHom.mem_ker.mp x.2
    have h := congrArg Subtype.val hx
    exact h⟩
  map_add' x y := Subtype.ext rfl
  map_smul' c x := Subtype.ext rfl
  map_lie' := by
    intro x y
    apply Subtype.ext
    rfl

private theorem leviComapMapKerToKer_injective
    {K L L' : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing L'] [LieAlgebra K L'] (f : L →ₗ⁅K⁆ L') (J : LieIdeal K L') :
    Function.Injective (leviComapMapKerToKer f J) := by
  intro x y h
  have hxy := congrArg (fun z : f.ker ↦ z.1) h
  change x.1.1 = y.1.1 at hxy
  exact Subtype.ext (Subtype.ext hxy)

private theorem levi_isSolvable_comap
    {K L L' : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing L'] [LieAlgebra K L'] (f : L →ₗ⁅K⁆ L')
    (hf : Function.Surjective f) [LieAlgebra.IsSolvable f.ker]
    (J : LieIdeal K L') [LieAlgebra.IsSolvable J] :
    LieAlgebra.IsSolvable (J.comap f) := by
  let q := leviComapMap f J
  have _ : LieAlgebra.IsSolvable q.ker :=
    (leviComapMapKerToKer_injective f J).lieAlgebra_isSolvable
  exact levi_isSolvable_of_ker_quotient q (leviComapMap_surjective f hf J)

private def leviMapRestrict
    {K L L' : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing L'] [LieAlgebra K L'] (f : L →ₗ⁅K⁆ L') (I : LieIdeal K L) :
    I →ₗ⁅K⁆ I.map f where
  toFun x := ⟨f x.1, LieIdeal.mem_map x.2⟩
  map_add' x y := Subtype.ext (f.map_add x.1 y.1)
  map_smul' c x := Subtype.ext (f.map_smul c x.1)
  map_lie' := by
    intro x y
    apply Subtype.ext
    exact f.map_lie x.1 y.1

private theorem leviMapRestrict_surjective
    {K L L' : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing L'] [LieAlgebra K L'] (f : L →ₗ⁅K⁆ L')
    (hf : Function.Surjective f) (I : LieIdeal K L) :
    Function.Surjective (leviMapRestrict f I) := by
  intro y
  obtain ⟨x, hx⟩ := LieIdeal.mem_map_of_surjective hf y.2
  refine ⟨x, ?_⟩
  exact Subtype.ext hx

private theorem levi_isSolvable_map
    {K L L' : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing L'] [LieAlgebra K L'] (f : L →ₗ⁅K⁆ L')
    (hf : Function.Surjective f) (I : LieIdeal K L)
    [LieAlgebra.IsSolvable I] : LieAlgebra.IsSolvable (I.map f) :=
  (leviMapRestrict_surjective f hf I).lieAlgebra_isSolvable

private theorem levi_radical_quotient
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] (I : LieIdeal K L)
    (hI : I ≤ LieAlgebra.radical K L) :
    (LieAlgebra.radical K L).map (leviQuotientMk I) =
      LieAlgebra.radical K (L ⧸ I) := by
  let q := leviQuotientMk I
  have hq : Function.Surjective q := leviQuotientMk_surjective I
  apply le_antisymm
  · rw [← LieIdeal.solvable_iff_le_radical]
    exact levi_isSolvable_map q hq (LieAlgebra.radical K L)
  · change LieAlgebra.radical K (L ⧸ I) ≤
      (LieAlgebra.radical K L).map q
    have hmapComap :
        ((LieAlgebra.radical K (L ⧸ I)).comap q).map q =
          LieAlgebra.radical K (L ⧸ I) := by
      rw [LieIdeal.map_comap_eq (q.isIdealMorphism_of_surjective hq)]
      rw [q.idealRange_eq_top_of_surjective hq, top_inf_eq]
    rw [← hmapComap]
    apply LieIdeal.map_mono
    rw [← LieIdeal.solvable_iff_le_radical]
    have hker : q.ker = I := leviQuotientMk_ker I
    have _ : LieAlgebra.IsSolvable q.ker := by
      rw [hker]
      exact LieAlgebra.le_solvable_ideal_solvable hI inferInstance
    exact levi_isSolvable_comap q hq (LieAlgebra.radical K (L ⧸ I))

private theorem levi_radical_quotient_radical_eq_bot
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] :
    LieAlgebra.radical K (L ⧸ LieAlgebra.radical K L) = ⊥ := by
  rw [← levi_radical_quotient (LieAlgebra.radical K L) le_rfl]
  rw [LieIdeal.map_eq_bot_iff, leviQuotientMk_ker]

private theorem levi_quotient_radical_isSemisimple
    {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] :
    LieAlgebra.IsSemisimple K (L ⧸ LieAlgebra.radical K L) := by
  let _ : LieAlgebra.HasTrivialRadical K (L ⧸ LieAlgebra.radical K L) :=
    ⟨levi_radical_quotient_radical_eq_bot⟩
  exact inferInstance

private theorem levi_split_central_kernel
    {K L G : Type*} [Field K] [CharZero K]
    [LieRing L] [LieAlgebra K L] [Module.Finite K L]
    [LieRing G] [LieAlgebra K G] [Module.Finite K G]
    [LieAlgebra.IsSemisimple K G] (q : L →ₗ⁅K⁆ G)
    (hq : Function.Surjective q)
    (hcentral : ∀ x ∈ q.ker, ∀ y : L, ⁅x, y⁆ = 0) :
    ∃ S : LieSubalgebra K L, LieAlgebra.IsSemisimple K S ∧
      ((q.ker : Submodule K L) + (S : Submodule K L) = ⊤) ∧
      ((q.ker : Submodule K L) ⊓ (S : Submodule K L) = ⊥) := by
  let rangeIncl : q.range →ₗ⁅K⁆ G := q.range.incl
  have hRangeIncl : Function.Bijective rangeIncl := by
    constructor
    · intro x y h
      exact Subtype.ext h
    · intro y
      obtain ⟨x, rfl⟩ := hq y
      exact ⟨⟨q x, LieHom.mem_range_self q x⟩, rfl⟩
  let eRange : q.range ≃ₗ⁅K⁆ G := LieEquiv.ofBijective rangeIncl hRangeIncl
  let eQuot : (L ⧸ q.ker) ≃ₗ⁅K⁆ G := q.quotKerEquivRange.trans eRange
  let _ : LieAlgebra.IsKilling K (L ⧸ q.ker) :=
    LieAlgebra.isKilling_of_equiv eQuot.symm
  let _ : LieAlgebra.IsSemisimple K (L ⧸ q.ker) := inferInstance
  have hkerAction : ∀ x ∈ q.ker, ∀ y : L, ⁅x, y⁆ = 0 := hcentral
  obtain ⟨U, hU⟩ :=
    levi_factor_exists_isCompl q.ker hkerAction (q.ker : LieSubmodule K L L)
  let qU : U →ₗ⁅K⁆ G := q.comp (LieSubalgebra.incl (LieIdeal.toLieSubalgebra K L U))
  have hqUInjective : Function.Injective qU := by
    intro x y hxy
    apply Subtype.ext
    have hdiffKer : x.1 - y.1 ∈ q.ker := by
      rw [LieHom.mem_ker]
      rw [map_sub]
      change qU x - qU y = 0
      rw [hxy, sub_self]
    have hdiffU : x.1 - y.1 ∈ U := U.sub_mem x.2 y.2
    have hdiffBot : x.1 - y.1 ∈ (⊥ : LieSubmodule K L L) := by
      rw [← hU.inf_eq_bot]
      exact ⟨hdiffKer, hdiffU⟩
    have hdiff : x.1 - y.1 = 0 := by simpa using hdiffBot
    exact sub_eq_zero.mp hdiff
  have hqUSurjective : Function.Surjective qU := by
    intro y
    obtain ⟨x, hx⟩ := hq y
    have hxSup : x ∈ q.ker ⊔ U := by
      rw [hU.sup_eq_top]
      trivial
    rw [LieSubmodule.mem_sup] at hxSup
    obtain ⟨z, hz, u, hu, hzu⟩ := hxSup
    refine ⟨⟨u, hu⟩, ?_⟩
    change q u = y
    have hz0 : q z = 0 := LieHom.mem_ker.mp hz
    calc
      q u = q (z + u) := by rw [map_add, hz0, zero_add]
      _ = q x := congrArg q hzu
      _ = y := hx
  let eU : U ≃ₗ⁅K⁆ G := LieEquiv.ofBijective qU ⟨hqUInjective, hqUSurjective⟩
  let _ : LieAlgebra.IsKilling K U := LieAlgebra.isKilling_of_equiv eU.symm
  let _ : LieAlgebra.IsSemisimple K U := inferInstance
  let S := LieIdeal.toLieSubalgebra K L U
  let UtoS : U →ₗ⁅K⁆ S :=
    { toFun := fun x ↦ ⟨x.1, x.2⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      map_lie' := by
        intro x y
        apply Subtype.ext
        rfl }
  have hUtoS : Function.Bijective UtoS := by
    constructor
    · intro x y h
      have h' := congrArg (fun z : S ↦ z.1) h
      change x.1 = y.1 at h'
      exact Subtype.ext h'
    · intro y
      refine ⟨⟨y.1, y.2⟩, ?_⟩
      apply Subtype.ext
      rfl
  let eUS : U ≃ₗ⁅K⁆ S := LieEquiv.ofBijective UtoS hUtoS
  let _ : LieAlgebra.IsKilling K S := LieAlgebra.isKilling_of_equiv eUS
  let _ : LieAlgebra.IsSemisimple K S := inferInstance
  refine ⟨S, inferInstance, ?_, ?_⟩
  · rw [← LieSubmodule.isCompl_toSubmodule] at hU
    exact hU.sup_eq_top
  · rw [← LieSubmodule.isCompl_toSubmodule] at hU
    exact hU.inf_eq_bot

private theorem levi_abelian_radical_map
    {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] :
    let R := LieAlgebra.radical K L
    let V := leviHomScalarMaps (L := L) R
    let P : LieSubmodule K L V := ⁅R, ⊤⁆
    ∃ f : V, (∀ r : R, f.1 r = r) ∧ (∀ x : L, ⁅x, f⁆ ∈ P) := by
  let R := LieAlgebra.radical K L
  let V := leviHomScalarMaps (L := L) R
  let Z := (leviHomVanishing R).comap V.incl
  let P : LieSubmodule K L V := ⁅R, ⊤⁆
  have hPZ : P ≤ Z := by
    rw [LieSubmodule.lie_le_iff]
    intro x hx f _
    exact levi_lie_mem_HomVanishing_of_mem_scalarMaps R f x
  let Wbar := Z.map (LieSubmodule.Quotient.mk' P)
  have hRaction : ∀ x ∈ R, ∀ m : V ⧸ P, ⁅x, m⁆ = 0 := by
    intro x hx m
    induction m using Submodule.Quotient.induction_on with
    | _ f =>
      change LieSubmodule.Quotient.mk' P ⁅x, f⁆ = 0
      rw [LieSubmodule.Quotient.mk_eq_zero]
      exact LieSubmodule.lie_mem_lie hx (LieSubmodule.mem_top f)
  let _ : LieAlgebra.IsSemisimple K (L ⧸ R) :=
    levi_quotient_radical_isSemisimple
  obtain ⟨C, hC⟩ := levi_factor_exists_isCompl R hRaction Wbar
  obtain ⟨Q, hQ⟩ := R.toSubmodule.exists_isCompl
  let p : L →ₗ[K] R := R.toSubmodule.projectionOnto Q hQ
  have hp (r : R) : p r = r := Submodule.projectionOnto_apply_left hQ r
  let pv : V := ⟨p, 1, fun r ↦ by rw [hp, one_smul]⟩
  let pvbar : V ⧸ P := LieSubmodule.Quotient.mk' P pv
  have hpvbar : pvbar ∈ Wbar ⊔ C := by
    rw [hC.sup_eq_top]
    trivial
  rw [LieSubmodule.mem_sup] at hpvbar
  obtain ⟨z, hz, c, hc, hzc⟩ := hpvbar
  rw [LieSubmodule.mem_map] at hz
  obtain ⟨z₀, hz₀, hz₀eq⟩ := hz
  let f : V := pv - z₀
  have hfbar : LieSubmodule.Quotient.mk' P f = c := by
    change LieSubmodule.Quotient.mk' P (pv - z₀) = c
    rw [map_sub, hz₀eq]
    change pvbar - z = c
    rw [← hzc]
    abel
  have hfApply (r : R) : f.1 r = r := by
    change (pv.1 - z₀.1) r = r
    rw [LinearMap.sub_apply, hp]
    have hz₀r : z₀.1 r = 0 := hz₀ r
    rw [hz₀r, sub_zero]
  refine ⟨f, hfApply, ?_⟩
  intro x
  have hxcC : ⁅x, c⁆ ∈ C := C.lie_mem hc
  have hxcW : ⁅x, c⁆ ∈ Wbar := by
    rw [← hfbar, ← LieModuleHom.map_lie]
    exact LieSubmodule.mem_map_of_mem
      (levi_lie_mem_HomVanishing_of_mem_scalarMaps R f x)
  have hxcBot : ⁅x, c⁆ ∈ (⊥ : LieSubmodule K L (V ⧸ P)) := by
    rw [← hC.inf_eq_bot]
    exact ⟨hxcW, hxcC⟩
  have hxcZero : ⁅x, c⁆ = 0 := by simpa using hxcBot
  rw [← LieSubmodule.Quotient.mk_eq_zero]
  rw [LieModuleHom.map_lie, hfbar, hxcZero]

private def leviTheta
    {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    (I : LieIdeal K L) (f : leviHomScalarMaps (L := L) I) :
    I →ₗ[K] leviHomScalarMaps I where
  toFun x := ⁅(x.1 : L), f⁆
  map_add' x y := by rw [Submodule.coe_add, add_lie]
  map_smul' a x := by
    change ⁅((a • x).1 : L), f⁆ = (RingHom.id K) a • ⁅(x.1 : L), f⁆
    rw [RingHom.id_apply, SetLike.val_smul, smul_lie]

private theorem levi_lie_le_range_theta
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (I : LieIdeal K L) (hI : IsLieAbelian I)
    (f : leviHomScalarMaps (L := L) I) (hf : ∀ r : I, f.1 r = r) :
    (⁅I, (⊤ : LieSubmodule K L (leviHomScalarMaps I))⁆ :
        LieSubmodule K L (leviHomScalarMaps I)).toSubmodule ≤
      LinearMap.range (leviTheta I f) := by
  rw [LieSubmodule.lieIdeal_oper_eq_linear_span]
  rw [Submodule.span_le]
  rintro g ⟨r, v, rfl⟩
  obtain ⟨a, ha⟩ := v.1.2
  refine ⟨a • r, ?_⟩
  apply Subtype.ext
  ext y
  change
    ((⁅((a • r).1 : L), (f.1 : L →ₗ[K] I)⁆ : L →ₗ[K] I) y : L) =
      ((⁅(r.1 : L), (v.1.1 : L →ₗ[K] I)⁆ : L →ₗ[K] I) y : L)
  rw [LieHom.lie_apply, LieHom.lie_apply]
  change
    ⁅(a • r : I).1, (f.1 y).1⁆ - (f.1 ⁅(a • r : I).1, y⁆).1 =
      ⁅r.1, (v.1.1 y).1⁆ - (v.1.1 ⁅r.1, y⁆).1
  have hry : ⁅r.1, y⁆ ∈ I := lie_mem_left K L I r.1 y r.2
  have hary : ⁅(a • r : I).1, y⁆ ∈ I :=
    lie_mem_left K L I (a • r).1 y (a • r).2
  have hrv : ⁅r.1, (v.1.1 y).1⁆ = 0 :=
    congrArg Subtype.val (hI.trivial r (v.1.1 y))
  have harf : ⁅(a • r : I).1, (f.1 y).1⁆ = 0 :=
    congrArg Subtype.val (hI.trivial (a • r) (f.1 y))
  rw [hrv, harf, zero_sub, zero_sub]
  have hv := congrArg Subtype.val (ha (⟨⁅r.1, y⁆, hry⟩ : I))
  have hfv := congrArg Subtype.val (hf (⟨⁅(a • r : I).1, y⁆, hary⟩ : I))
  rw [hv, hfv]
  simp only [SetLike.val_smul, smul_lie]

private def leviStabilizer
    {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    (I : LieIdeal K L) (f : leviHomScalarMaps (L := L) I) :
    LieSubalgebra K L where
  carrier := {x | ⁅x, f⁆ = 0}
  zero_mem' := by
    change ⁅0, f⁆ = 0
    rw [zero_lie]
  add_mem' {x y} hx hy := by
    change ⁅x + y, f⁆ = 0
    rw [add_lie, hx, hy, add_zero]
  smul_mem' a x hx := by
    change ⁅a • x, f⁆ = 0
    rw [smul_lie, hx, smul_zero]
  lie_mem' := by
    intro x y hx hy
    change ⁅⁅x, y⁆, f⁆ = 0
    rw [lie_lie, hx, hy]
    simp

private theorem levi_exists_of_abelian_radical
    {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] (hR : IsLieAbelian (LieAlgebra.radical K L)) :
    ∃ S : LieSubalgebra K L, LieAlgebra.IsSemisimple K S ∧
      ((LieAlgebra.radical K L : Submodule K L) + (S : Submodule K L) = ⊤) ∧
      ((LieAlgebra.radical K L : Submodule K L) ⊓ (S : Submodule K L) = ⊥) := by
  let R := LieAlgebra.radical K L
  let V := leviHomScalarMaps (L := L) R
  let P : LieSubmodule K L V := ⁅R, ⊤⁆
  obtain ⟨f, hf, hfP⟩ := levi_abelian_radical_map (K := K) (L := L)
  have hPrange : P.toSubmodule ≤ LinearMap.range (leviTheta R f) :=
    levi_lie_le_range_theta R hR f hf
  let H := leviStabilizer R f
  have hRH : (R : Submodule K L) + (H : Submodule K L) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hxP : ⁅x, f⁆ ∈ P := hfP x
    obtain ⟨r, hr⟩ := hPrange hxP
    rw [Submodule.add_eq_sup, Submodule.mem_sup]
    refine ⟨r.1, r.2, x - r.1, ?_, ?_⟩
    · change ⁅x - r.1, f⁆ = 0
      rw [sub_lie]
      change ⁅r.1, f⁆ = ⁅x, f⁆ at hr
      rw [hr, sub_self]
    · abel
  let q := leviQuotientMk R
  let qH : H →ₗ⁅K⁆ L ⧸ R := q.comp H.incl
  have hqH : Function.Surjective qH := by
    intro y
    obtain ⟨x, hx⟩ := leviQuotientMk_surjective R y
    have hxTop : x ∈ (R : Submodule K L) + (H : Submodule K L) := by
      rw [hRH]
      trivial
    rw [Submodule.add_eq_sup, Submodule.mem_sup] at hxTop
    obtain ⟨r, hr, h, hh, hrh⟩ := hxTop
    refine ⟨⟨h, hh⟩, ?_⟩
    change q h = y
    have hqr : q r = 0 := by
      rw [← LieHom.mem_ker, leviQuotientMk_ker]
      exact hr
    calc
      q h = q (r + h) := by rw [map_add, hqr, zero_add]
      _ = q x := congrArg q hrh
      _ = y := hx
  have hcentral : ∀ x ∈ qH.ker, ∀ y : H, ⁅x, y⁆ = 0 := by
    intro x hx y
    have hxq : q x.1 = 0 := by
      exact LieHom.mem_ker.mp hx
    have hxR : x.1 ∈ R := by
      rw [← leviQuotientMk_ker R, LieHom.mem_ker]
      exact hxq
    have hxStab : ⁅x.1, f⁆ = 0 := x.2
    have hmap := congrArg Subtype.val hxStab
    have heval := congrArg (fun g : L →ₗ[K] R ↦ g y.1) hmap
    change ⁅x.1, f.1 y.1⁆ - f.1 ⁅x.1, y.1⁆ = 0 at heval
    have hab : ⁅(⟨x.1, hxR⟩ : R), f.1 y.1⁆ = 0 :=
      hR.trivial ⟨x.1, hxR⟩ (f.1 y.1)
    have hab' : ⁅x.1, f.1 y.1⁆ = 0 := hab
    rw [hab', zero_sub] at heval
    have hfxy : f.1 ⁅x.1, y.1⁆ = 0 := neg_eq_zero.mp heval
    have hxyR : ⁅x.1, y.1⁆ ∈ R := lie_mem_left K L R x.1 y.1 hxR
    have hfix := hf (⟨⁅x.1, y.1⁆, hxyR⟩ : R)
    apply Subtype.ext
    have hzero := congrArg Subtype.val hfxy
    have hfix' := congrArg Subtype.val hfix
    rw [hfix'] at hzero
    exact hzero
  let _ : LieAlgebra.IsSemisimple K (L ⧸ R) :=
    levi_quotient_radical_isSemisimple
  obtain ⟨T, hTsemi, hTsum, hTinf⟩ :=
    levi_split_central_kernel qH hqH hcentral
  let S := T.map H.incl
  have hHincl : Function.Injective H.incl := by
    intro x y h
    exact Subtype.ext h
  let eTS : T ≃ₗ⁅K⁆ S := LieSubalgebra.equivMapOfInjective H.incl T hHincl
  let _ : LieAlgebra.IsKilling K T := inferInstance
  let _ : LieAlgebra.IsKilling K S := LieAlgebra.isKilling_of_equiv eTS
  let _ : LieAlgebra.IsSemisimple K S := inferInstance
  refine ⟨S, inferInstance, ?_, ?_⟩
  · rw [eq_top_iff]
    intro x _
    have hxTop : x ∈ (R : Submodule K L) + (H : Submodule K L) := by
      rw [hRH]
      trivial
    rw [Submodule.add_eq_sup, Submodule.mem_sup] at hxTop
    obtain ⟨r, hr, h, hh, hrh⟩ := hxTop
    have hhTop : (⟨h, hh⟩ : H) ∈
        (qH.ker : Submodule K H) + (T : Submodule K H) := by
      rw [hTsum]
      trivial
    rw [Submodule.add_eq_sup, Submodule.mem_sup] at hhTop
    obtain ⟨z, hz, t, ht, hzt⟩ := hhTop
    change x ∈ (R : Submodule K L) + (S : Submodule K L)
    rw [Submodule.add_eq_sup, Submodule.mem_sup]
    refine ⟨r + z.1, R.add_mem hr ?_, t.1, ?_, ?_⟩
    · have hzq : q z.1 = 0 := LieHom.mem_ker.mp hz
      have hzker : z.1 ∈ (leviQuotientMk R).ker := LieHom.mem_ker.mpr hzq
      change z.1 ∈ R
      rwa [leviQuotientMk_ker] at hzker
    · exact (LieSubalgebra.mem_map H.incl T t.1).mpr ⟨t, ht, rfl⟩
    · have hhval : z.1 + t.1 = h := congrArg Subtype.val hzt
      rw [← hrh, ← hhval]
      abel
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨t, ht, htval⟩ := (LieSubalgebra.mem_map H.incl T x).mp hx.2
    have htR : t.1 ∈ R := by
      change H.incl t ∈ R
      rw [htval]
      exact hx.1
    have htKer : t ∈ qH.ker := by
      rw [LieHom.mem_ker]
      change q t.1 = 0
      rw [← LieHom.mem_ker, leviQuotientMk_ker]
      exact htR
    have htBot : t ∈ (⊥ : Submodule K H) := by
      rw [← hTinf]
      exact ⟨htKer, ht⟩
    have htZero : t = 0 := by simpa using htBot
    change x = 0
    rw [← htval, htZero, map_zero]

private def leviSubalgebraComapMap
    {K L G : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing G] [LieAlgebra K G] (q : L →ₗ⁅K⁆ G) (T : LieSubalgebra K G) :
    T.comap q →ₗ⁅K⁆ T where
  toFun x := ⟨q x.1, x.2⟩
  map_add' x y := Subtype.ext (q.map_add x.1 y.1)
  map_smul' a x := Subtype.ext (q.map_smul a x.1)
  map_lie' := by
    intro x y
    apply Subtype.ext
    exact q.map_lie x.1 y.1

private theorem leviSubalgebraComapMap_surjective
    {K L G : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing G] [LieAlgebra K G] (q : L →ₗ⁅K⁆ G)
    (hq : Function.Surjective q) (T : LieSubalgebra K G) :
    Function.Surjective (leviSubalgebraComapMap q T) := by
  intro y
  obtain ⟨x, hx⟩ := hq y
  have hxT : x ∈ T.comap q := by
    change q x ∈ T
    rw [hx]
    exact y.2
  refine ⟨⟨x, hxT⟩, ?_⟩
  apply Subtype.ext
  exact hx

private def leviSubalgebraComapKerToKer
    {K L G : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing G] [LieAlgebra K G] (q : L →ₗ⁅K⁆ G) (T : LieSubalgebra K G) :
    (leviSubalgebraComapMap q T).ker →ₗ⁅K⁆ q.ker where
  toFun x := ⟨x.1.1, by
    rw [LieHom.mem_ker]
    have hx : leviSubalgebraComapMap q T x.1 = 0 := LieHom.mem_ker.mp x.2
    exact congrArg Subtype.val hx⟩
  map_add' x y := Subtype.ext rfl
  map_smul' a x := Subtype.ext rfl
  map_lie' := by
    intro x y
    apply Subtype.ext
    rfl

private theorem leviSubalgebraComapKerToKer_injective
    {K L G : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing G] [LieAlgebra K G] (q : L →ₗ⁅K⁆ G) (T : LieSubalgebra K G) :
    Function.Injective (leviSubalgebraComapKerToKer q T) := by
  intro x y h
  have hxy := congrArg (fun z : q.ker ↦ z.1) h
  change x.1.1 = y.1.1 at hxy
  exact Subtype.ext (Subtype.ext hxy)

private theorem levi_radical_comap_semisimple
    {K L G : Type*} [Field K] [CharZero K]
    [LieRing L] [LieAlgebra K L] [Module.Finite K L]
    [LieRing G] [LieAlgebra K G] [Module.Finite K G] (q : L →ₗ⁅K⁆ G)
    (hq : Function.Surjective q) (T : LieSubalgebra K G)
    [LieAlgebra.IsSemisimple K T] [LieAlgebra.IsSolvable q.ker] :
    LieAlgebra.radical K (T.comap q) = (leviSubalgebraComapMap q T).ker := by
  let qT := leviSubalgebraComapMap q T
  have hqT : Function.Surjective qT := leviSubalgebraComapMap_surjective q hq T
  have _ : LieAlgebra.IsSolvable qT.ker :=
    (leviSubalgebraComapKerToKer_injective q T).lieAlgebra_isSolvable
  apply le_antisymm
  · rw [← LieIdeal.map_eq_bot_iff]
    have hsolv : LieAlgebra.IsSolvable ((LieAlgebra.radical K (T.comap q)).map qT) :=
      levi_isSolvable_map qT hqT (LieAlgebra.radical K (T.comap q))
    have hle : (LieAlgebra.radical K (T.comap q)).map qT ≤
        LieAlgebra.radical K T :=
      (LieIdeal.solvable_iff_le_radical (R := K) (L := T) _).mp hsolv
    simpa using hle
  · exact (LieIdeal.solvable_iff_le_radical (R := K) (L := T.comap q) _).mp inferInstance

private theorem levi_derived_radical_lt
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L]
    (hR : ¬ IsLieAbelian (LieAlgebra.radical K L)) :
    ⁅LieAlgebra.radical K L, LieAlgebra.radical K L⁆ <
      LieAlgebra.radical K L := by
  let R := LieAlgebra.radical K L
  let D : LieIdeal K L := ⁅R, R⁆
  have hRne : R ≠ ⊥ := by
    intro h
    apply hR
    rw [show LieAlgebra.radical K L = ⊥ from h]
    infer_instance
  let _ : Nontrivial R :=
    (LieSubmodule.nontrivial_iff_ne_bot K L L).mpr hRne
  have hder : LieAlgebra.derivedSeries K R 1 < ⊤ :=
    LieAlgebra.derivedSeries_lt_top_of_solvable K R
  have hDle : D ≤ R := LieSubmodule.lie_le_left R R
  refine lt_of_le_of_ne hDle ?_
  intro hEq
  change D = R at hEq
  have htop : LieAlgebra.derivedSeries K R 1 = ⊤ := by
    rw [LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_comap]
    change D.comap R.incl = ⊤
    rw [hEq]
    exact LieIdeal.comap_incl_self R
  exact hder.ne htop

private theorem levi_quotient_derived_radical_abelian
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] :
    let R := LieAlgebra.radical K L
    let D : LieIdeal K L := ⁅R, R⁆
    IsLieAbelian (LieAlgebra.radical K (L ⧸ D)) := by
  dsimp only
  let R := LieAlgebra.radical K L
  let D : LieIdeal K L := ⁅R, R⁆
  let q := leviQuotientMk D
  have hq : Function.Surjective q := leviQuotientMk_surjective D
  have hDle : D ≤ R := LieSubmodule.lie_le_left R R
  have hrad : R.map q = LieAlgebra.radical K (L ⧸ D) :=
    levi_radical_quotient D hDle
  rw [← hrad]
  refine ⟨?_⟩
  intro x y
  obtain ⟨rx, hrx⟩ := LieIdeal.mem_map_of_surjective hq x.2
  obtain ⟨ry, hry⟩ := LieIdeal.mem_map_of_surjective hq y.2
  apply Subtype.ext
  change ⁅x.1, y.1⁆ = 0
  rw [← hrx, ← hry, ← q.map_lie]
  have hbr : ⁅rx.1, ry.1⁆ ∈ D := LieSubmodule.lie_mem_lie rx.2 ry.2
  rw [← LieHom.mem_ker, leviQuotientMk_ker]
  exact hbr

private theorem levi_decomposition_aux
    (n : ℕ) {K L : Type*} [Field K] [CharZero K]
    [LieRing L] [LieAlgebra K L] [Module.Finite K L]
    (hDim : Module.finrank K (LieAlgebra.radical K L) < n) :
    ∃ S : LieSubalgebra K L, LieAlgebra.IsSemisimple K S ∧
      ((LieAlgebra.radical K L : Submodule K L) + (S : Submodule K L) = ⊤) ∧
      ((LieAlgebra.radical K L : Submodule K L) ⊓ (S : Submodule K L) = ⊥) := by
  induction n generalizing L with
  | zero => omega
  | succ n ih =>
    let R := LieAlgebra.radical K L
    by_cases hRabelian : IsLieAbelian R
    · exact levi_exists_of_abelian_radical hRabelian
    · let D : LieIdeal K L := ⁅R, R⁆
      let q := leviQuotientMk D
      have hq : Function.Surjective q := leviQuotientMk_surjective D
      have hDle : D ≤ R := LieSubmodule.lie_le_left R R
      have hDlt : D < R := levi_derived_radical_lt hRabelian
      have hDfin : Module.finrank K D < Module.finrank K R :=
        Submodule.finrank_lt_finrank_of_lt hDlt
      have hQabelian : IsLieAbelian (LieAlgebra.radical K (L ⧸ D)) :=
        levi_quotient_derived_radical_abelian
      obtain ⟨T, hTsemi, hTsum, hTinf⟩ :=
        levi_exists_of_abelian_radical hQabelian
      let L₁ := T.comap q
      let qT := leviSubalgebraComapMap q T
      have hqT : Function.Surjective qT :=
        leviSubalgebraComapMap_surjective q hq T
      have _ : LieAlgebra.IsSemisimple K T := hTsemi
      have _ : LieAlgebra.IsSolvable q.ker := by
        rw [leviQuotientMk_ker]
        exact LieAlgebra.le_solvable_ideal_solvable hDle inferInstance
      have hRad₁ : LieAlgebra.radical K L₁ = qT.ker :=
        levi_radical_comap_semisimple q hq T
      have hFinKer : Module.finrank K qT.ker ≤ Module.finrank K q.ker :=
        LinearMap.finrank_le_finrank_of_injective
          (leviSubalgebraComapKerToKer_injective q T)
      have hFinRad₁ : Module.finrank K (LieAlgebra.radical K L₁) < n := by
        have hRle : Module.finrank K R ≤ n := Nat.lt_succ_iff.mp hDim
        have hkerD : Module.finrank K q.ker = Module.finrank K D := by
          rw [leviQuotientMk_ker]
        rw [hRad₁]
        calc
          Module.finrank K qT.ker ≤ Module.finrank K q.ker := hFinKer
          _ = Module.finrank K D := hkerD
          _ < Module.finrank K R := hDfin
          _ ≤ n := hRle
      obtain ⟨S₁, hS₁semi, hS₁sum, hS₁inf⟩ := ih hFinRad₁
      let S := S₁.map L₁.incl
      have hL₁incl : Function.Injective L₁.incl := by
        intro x y h
        exact Subtype.ext h
      let eS : S₁ ≃ₗ⁅K⁆ S :=
        LieSubalgebra.equivMapOfInjective L₁.incl S₁ hL₁incl
      let _ : LieAlgebra.IsSemisimple K S₁ := hS₁semi
      let _ : LieAlgebra.IsKilling K S₁ := inferInstance
      let _ : LieAlgebra.IsKilling K S := LieAlgebra.isKilling_of_equiv eS
      let _ : LieAlgebra.IsSemisimple K S := inferInstance
      have hRadQ : R.map q = LieAlgebra.radical K (L ⧸ D) :=
        levi_radical_quotient D hDle
      refine ⟨S, inferInstance, ?_, ?_⟩
      · rw [eq_top_iff]
        intro x _
        have hxQ : q x ∈
            (LieAlgebra.radical K (L ⧸ D) : Submodule K (L ⧸ D)) +
              (T : Submodule K (L ⧸ D)) := by
          rw [hTsum]
          trivial
        rw [Submodule.add_eq_sup, Submodule.mem_sup] at hxQ
        obtain ⟨a, ha, t, ht, hat⟩ := hxQ
        have haMap : a ∈ R.map q := by
          rw [hRadQ]
          exact ha
        obtain ⟨r, hr⟩ := LieIdeal.mem_map_of_surjective hq haMap
        have hxt : q (x - r.1) = t := by
          rw [map_sub, hr]
          rw [← hat]
          abel
        let l₁ : L₁ := ⟨x - r.1, by
          change q (x - r.1) ∈ T
          rw [hxt]
          exact ht⟩
        have hl₁Top : l₁ ∈
            (LieAlgebra.radical K L₁ : Submodule K L₁) +
              (S₁ : Submodule K L₁) := by
          rw [hS₁sum]
          trivial
        rw [Submodule.add_eq_sup, Submodule.mem_sup] at hl₁Top
        obtain ⟨z, hz, s, hs, hzs⟩ := hl₁Top
        have hzKer : z ∈ qT.ker := by
          rw [← hRad₁]
          exact hz
        have hzR : z.1 ∈ R := by
          have hzqT := LieHom.mem_ker.mp hzKer
          have hzq := congrArg Subtype.val hzqT
          change q z.1 = 0 at hzq
          have hzD : z.1 ∈ D := by
            rw [← leviQuotientMk_ker D, LieHom.mem_ker]
            exact hzq
          exact hDle hzD
        change x ∈ (R : Submodule K L) + (S : Submodule K L)
        rw [Submodule.add_eq_sup, Submodule.mem_sup]
        refine ⟨r.1 + z.1, R.add_mem r.2 hzR, s.1, ?_, ?_⟩
        · exact (LieSubalgebra.mem_map L₁.incl S₁ s.1).mpr ⟨s, hs, rfl⟩
        · have hl₁val : z.1 + s.1 = x - r.1 := congrArg Subtype.val hzs
          calc
            r.1 + z.1 + s.1 = r.1 + (z.1 + s.1) := by abel
            _ = r.1 + (x - r.1) := by rw [hl₁val]
            _ = x := by abel
      · rw [eq_bot_iff]
        intro x hx
        obtain ⟨s, hs, hsx⟩ := (LieSubalgebra.mem_map L₁.incl S₁ x).mp hx.2
        have hsR : s.1 ∈ R := by
          have hsval : s.1 = x := hsx
          rw [hsval]
          exact hx.1
        have hqsR : q s.1 ∈ LieAlgebra.radical K (L ⧸ D) := by
          rw [← hRadQ]
          exact LieIdeal.mem_map hsR
        have hqsT : q s.1 ∈ T := s.2
        have hqsBot : q s.1 ∈ (⊥ : Submodule K (L ⧸ D)) := by
          rw [← hTinf]
          exact ⟨hqsR, hqsT⟩
        have hqsZero : q s.1 = 0 := by simpa using hqsBot
        have hsKer : s ∈ qT.ker := by
          rw [LieHom.mem_ker]
          apply Subtype.ext
          exact hqsZero
        have hsRad : s ∈ LieAlgebra.radical K L₁ := by
          rw [hRad₁]
          exact hsKer
        have hsBot : s ∈ (⊥ : Submodule K L₁) := by
          rw [← hS₁inf]
          exact ⟨hsRad, hs⟩
        have hsZero : s = 0 := by simpa using hsBot
        change x = 0
        rw [← hsx, hsZero, map_zero]

/--
**Levi decomposition.** Let $L$ be a finite-dimensional Lie algebra over a field $K$ of
characteristic zero, and let $\operatorname{rad}(L)$ be its radical, the largest solvable ideal
of $L$. Then there is a semisimple Lie subalgebra $S$ of $L$ (a Levi factor) such that
$L = \operatorname{rad}(L) \oplus S$ as $K$-vector spaces, that is,
$\operatorname{rad}(L) + S = L$ and $\operatorname{rad}(L) \cap S = 0$.

Proves `Wanted` entry `levi_decomposition`.

Proof: Weyl's complete reducibility theorem is proved with the trace-form Casimir operator. The
Levi factor is then constructed for an abelian radical and the general case follows by induction
through the derived ideal of the radical.

Source: E. E. Levi, Atti Accad. Sci.
Torino 1905 and A. I. Malcev, Izv. Akad. Nauk SSSR 1945; Bourbaki, Lie I; Lean states K-module
direct sum form over char-zero fields.
-/
public theorem levi_decomposition
    {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] :
    ∃ (S : LieSubalgebra K L), LieAlgebra.IsSemisimple K S ∧
      (↑(LieAlgebra.radical K L) + (S : Submodule K L) = (⊤ : Submodule K L)) ∧
      (↑(LieAlgebra.radical K L) ⊓ (S : Submodule K L) = (⊥ : Submodule K L)) := by
  exact levi_decomposition_aux
    (Module.finrank K (LieAlgebra.radical K L) + 1) (Nat.lt_succ_self _)

end MathlibExt.Algebra.Lie.LandmarkWanted
