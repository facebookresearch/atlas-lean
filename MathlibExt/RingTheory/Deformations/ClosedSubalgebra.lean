/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_Deformations_ClosedSubalgebra.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.RingTheory.Deformations.ProartinianCompact
public import MathlibExt.RingTheory.Deformations.TraceAlgebra

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.LinearCombination

/-!
# Closed subalgebras of local proartinian algebras

Let `A` be a compact local proartinian `𝓞`-algebra and `S` a closed `𝓞`-subalgebra of `A`. Then
`S` is again a local proartinian `𝓞`-algebra: an element of `S` invertible in `A` is invertible
in `S` (its inverse is a limit of geometric series in `S`), so `S` is local with maximal ideal
`S ∩ 𝔪_A`, and `S` is compact with a linear topology. This gives an object of
`ProartinianCat 𝓞` with an injective morphism to `A`. Applied to the trace subalgebra of a
representation `ρ` (when `ResidueField 𝓞` is finite), it gives the trace algebra of `ρ`.

## Main definitions

* `Deformation.ProartinianCat.closedSubalgebraObj S hS`: `S` as an object of `ProartinianCat 𝓞`.
* `Deformation.ProartinianCat.closedSubalgebraι S hS`: the inclusion `S ⟶ A`.
* `Deformation.TraceAlgebra.obj ρ`, `Deformation.TraceAlgebra.ι ρ`: the trace algebra of `ρ` and
  its inclusion, for a local ring `𝓞` with finite residue field.

## Main results

* `Deformation.ProartinianCat.isUnit_of_isUnit_val`: units of `A` lying in `S` are units of `S`.
* `Deformation.ProartinianCat.ClosedSubalgebra.isLocalProartinianAlgebra`: `S` is a local
  proartinian `𝓞`-algebra.
-/

@[expose] public section

universe u v w

open CategoryTheory Function Limits IsLocalRing Filter Topology

namespace Deformation

variable {𝓞 : Type u} [CommRing 𝓞]

namespace ProartinianCat

variable {A : ProartinianCat 𝓞}

theorem tendsto_pow_nhds_zero_of_mem_maximalIdeal {m : A.carrier} (hm : m ∈ maximalIdeal A) :
    Tendsto (fun N => m ^ N) atTop (𝓝 0) := by
  rw [(IsLinearTopology.hasBasis_open_ideal (R := A.carrier)).tendsto_right_iff]
  intro I hI
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_of_isProartinian I hI
  filter_upwards [eventually_ge_atTop n] with N hN
  exact hn (Ideal.pow_le_pow_right hN (Ideal.pow_mem_pow hm N))

section ClosedSubalgebra

variable (S : Subalgebra 𝓞 A.carrier) (hS : IsClosed (S : Set A.carrier))

theorem exists_mul_one_sub_eq_one_of_isClosed [CompactSpace A.carrier]
    {T : Set A.carrier} (hT : IsClosed T) {m : A.carrier} (hm : m ∈ maximalIdeal A)
    (hmem : ∀ N, (∑ i ∈ Finset.range N, m ^ i) ∈ T) :
    ∃ s ∈ T, s * (1 - m) = 1 := by
  obtain ⟨s, hsT, hs⟩ := (hT.isCompact).exists_mapClusterPt
    (u := fun N => ∑ i ∈ Finset.range N, m ^ i) (f := atTop)
    (le_principal_iff.mpr (mem_map.mpr (Filter.Eventually.of_forall hmem)))
  refine ⟨s, hsT, ?_⟩
  have hclust : MapClusterPt (s * (1 - m)) atTop
      (fun N => (∑ i ∈ Finset.range N, m ^ i) * (1 - m)) :=
    hs.continuousAt_comp (f := fun a => a * (1 - m)) (continuous_mul_const _).continuousAt
  have heq : (fun N => (∑ i ∈ Finset.range N, m ^ i) * (1 - m)) = fun N => 1 - m ^ N := by
    funext N
    have h1 := geom_sum_mul m N
    calc (∑ i ∈ Finset.range N, m ^ i) * (1 - m)
        = -((∑ i ∈ Finset.range N, m ^ i) * (m - 1)) := by ring
      _ = -(m ^ N - 1) := by rw [h1]
      _ = 1 - m ^ N := by ring
  have htend : Tendsto (fun N => (∑ i ∈ Finset.range N, m ^ i) * (1 - m)) atTop (𝓝 1) := by
    rw [heq]
    have h0 : Tendsto (fun N => m ^ N) atTop (𝓝 0) :=
      tendsto_pow_nhds_zero_of_mem_maximalIdeal hm
    simpa using (tendsto_const_nhds (x := (1 : A.carrier))).sub h0
  have h3 : ClusterPt (s * (1 - m)) (𝓝 (1 : A.carrier)) := hclust.clusterPt.mono htend
  exact eq_of_nhds_neBot h3

include hS in
theorem isUnit_of_isUnit_val [CompactSpace A.carrier] (x : S) (hx : IsUnit (x : A.carrier)) :
    IsUnit x := by
  set o : 𝓞 := IsResidueAlgebra.preimage 𝓞 (x : A.carrier) with ho
  have hm₀ : (x : A.carrier) - algebraMap 𝓞 A.carrier o ∈ maximalIdeal A :=
    IsResidueAlgebra.preimage_spec 𝓞 (x : A.carrier)
  have hu : IsUnit (algebraMap 𝓞 A.carrier o) := by
    by_contra h
    have hmem : algebraMap 𝓞 A.carrier o ∈ maximalIdeal A := h
    exact (notMem_maximalIdeal.mpr hx)
      (by simpa using (maximalIdeal A).add_mem hmem hm₀)
  have ho_unit : IsUnit o := (isUnit_map_iff (algebraMap 𝓞 A.carrier) o).mp hu
  obtain ⟨ou, hou⟩ := ho_unit
  have hinv_mem : algebraMap 𝓞 A.carrier (↑ou⁻¹ : 𝓞) ∈ S := S.algebraMap_mem _
  have huu : algebraMap 𝓞 A.carrier o * algebraMap 𝓞 A.carrier (↑ou⁻¹ : 𝓞) = 1 := by
    rw [← map_mul, ← hou, Units.mul_inv, map_one]
  set m : A.carrier := 1 - (x : A.carrier) * algebraMap 𝓞 A.carrier (↑ou⁻¹ : 𝓞) with hm_def
  have hm_mem_max : m ∈ maximalIdeal A := by
    have heq : m = -(((x : A.carrier) - algebraMap 𝓞 A.carrier o) *
        algebraMap 𝓞 A.carrier (↑ou⁻¹ : 𝓞)) := by
      rw [hm_def]
      linear_combination -huu
    rw [heq]
    exact (maximalIdeal A).neg_mem ((maximalIdeal A).mul_mem_right _ hm₀)
  have hm_mem_S : m ∈ S := by
    rw [hm_def]
    exact S.sub_mem S.one_mem (S.mul_mem x.2 hinv_mem)
  have hsums : ∀ N, (∑ i ∈ Finset.range N, m ^ i) ∈ S :=
    fun N => S.toSubring.sum_mem fun i _ => S.toSubring.pow_mem hm_mem_S i
  obtain ⟨s, hsS, hs⟩ := exists_mul_one_sub_eq_one_of_isClosed hS hm_mem_max hsums
  have hxinv : (x : A.carrier) * (algebraMap 𝓞 A.carrier (↑ou⁻¹ : 𝓞) * s) = 1 := by
    have h1 : (x : A.carrier) * algebraMap 𝓞 A.carrier (↑ou⁻¹ : 𝓞) = 1 - m := by
      rw [hm_def]; ring
    calc (x : A.carrier) * (algebraMap 𝓞 A.carrier (↑ou⁻¹ : 𝓞) * s)
        = ((x : A.carrier) * algebraMap 𝓞 A.carrier (↑ou⁻¹ : 𝓞)) * s := by ring
      _ = (1 - m) * s := by rw [h1]
      _ = s * (1 - m) := by ring
      _ = 1 := hs
  refine ⟨⟨x, ⟨_, S.mul_mem hinv_mem hsS⟩, Subtype.ext hxinv, Subtype.ext ?_⟩, rfl⟩
  change (algebraMap 𝓞 A.carrier (↑ou⁻¹ : 𝓞) * s) * (x : A.carrier) = 1
  rw [mul_comm]
  exact hxinv

end ClosedSubalgebra

section ClosedSubalgebraObj

variable [CompactSpace A.carrier] (S : Subalgebra 𝓞 A.carrier) (hS : IsClosed (S : Set A.carrier))

namespace ClosedSubalgebra

include hS in
theorem isLocalRing : IsLocalRing S := by
  refine .of_nonunits_add fun x y hx hy hxy => ?_
  rw [mem_nonunits_iff] at hx hy
  have hx' : ¬ IsUnit (x : A.carrier) := fun h => hx (isUnit_of_isUnit_val S hS x h)
  have hy' : ¬ IsUnit (y : A.carrier) := fun h => hy (isUnit_of_isUnit_val S hS y h)
  have hxy' : ((x + y : S) : A.carrier) ∈ maximalIdeal A :=
    (maximalIdeal A).add_mem ((mem_maximalIdeal _).mpr hx') ((mem_maximalIdeal _).mpr hy')
  exact (mem_nonunits_iff.mp ((mem_maximalIdeal _).mp hxy')) (hxy.map S.val)

include hS in
theorem mem_maximalIdeal_iff_val (x : S) :
    letI := isLocalRing S hS
    x ∈ maximalIdeal S ↔ (x : A.carrier) ∈ maximalIdeal A := by
  let := isLocalRing S hS
  rw [mem_maximalIdeal, mem_nonunits_iff, mem_maximalIdeal, mem_nonunits_iff]
  exact ⟨fun h h' => h (isUnit_of_isUnit_val S hS x h'), fun h h' => h (h'.map S.val)⟩

omit [CompactSpace A.carrier] in
theorem isLocalHom_algebraMap : IsLocalHom (algebraMap 𝓞 S) := by
  constructor
  intro o ho
  have h1 : IsUnit ((algebraMap 𝓞 S o : S) : A.carrier) := ho.map S.val
  have h2 : ((algebraMap 𝓞 S o : S) : A.carrier) = algebraMap 𝓞 A.carrier o := rfl
  rw [h2] at h1
  exact (isUnit_map_iff (algebraMap 𝓞 A.carrier) o).mp h1

include hS in
theorem isResidueAlgebra :
    letI := isLocalRing S hS
    IsResidueAlgebra 𝓞 S := by
  let := isLocalRing S hS
  constructor
  intro ξ
  obtain ⟨x, rfl⟩ := residue_surjective ξ
  obtain ⟨o, ho⟩ := IsResidueAlgebra.algebraMap_surjective 𝓞 A.carrier
    (residue A.carrier (x : A.carrier))
  rw [IsScalarTower.algebraMap_apply 𝓞 A.carrier (ResidueField A.carrier),
    ResidueField.algebraMap_eq] at ho
  refine ⟨o, ?_⟩
  rw [IsScalarTower.algebraMap_apply 𝓞 S (ResidueField S), ResidueField.algebraMap_eq]
  refine (Ideal.Quotient.eq (I := maximalIdeal S)).mpr ?_
  rw [mem_maximalIdeal_iff_val S hS]
  exact Ideal.Quotient.eq.mp ho

instance : IsTopologicalRing S := S.toSubring.instIsTopologicalRing

omit [CompactSpace A.carrier] in
theorem hasBasis_nhds_zero :
    (𝓝 (0 : S)).HasBasis (fun I : Ideal A.carrier => IsOpen (I : Set A.carrier))
      (fun I => ((I.comap (S.toSubring.subtype : S →+* A.carrier) : Ideal S) : Set S)) := by
  have hval : Topology.IsInducing (Subtype.val : S → A.carrier) := ⟨rfl⟩
  have hbasis : (𝓝 ((0 : S) : A.carrier)).HasBasis
      (fun I : Ideal A.carrier => IsOpen (I : Set A.carrier)) (fun I => (I : Set A.carrier)) := by
    rw [show ((0 : S) : A.carrier) = 0 from rfl]
    exact IsLinearTopology.hasBasis_open_ideal
  refine (hval.basis_nhds hbasis).congr (fun _ => Iff.rfl) (fun I _ => ?_)
  ext x
  simp only [Function.comp_apply, Set.mem_preimage, SetLike.mem_coe, Ideal.mem_comap]
  rfl

instance : IsLinearTopology S S := .mk_of_hasBasis _ (hasBasis_nhds_zero S)

include hS in
theorem compactSpace : CompactSpace S :=
  isCompact_iff_compactSpace.mp hS.isCompact

include hS in
theorem isProartinian : IsProartinian S := by
  have := compactSpace S hS
  exact { isArtinianRing_quotient := fun I hI =>
      have : Finite (S ⧸ I) := AddSubgroup.quotient_finite_of_isOpen _ hI
      inferInstance }

include hS in
theorem isLocalProartinianAlgebra : IsLocalProartinianAlgebra 𝓞 S := by
  have := isLocalRing S hS
  have := compactSpace S hS
  have := isProartinian S hS
  have := isLocalHom_algebraMap S
  have := isResidueAlgebra S hS
  exact { }

end ClosedSubalgebra

/-- **Closed subalgebras as local proartinian algebras.** A closed subalgebra of a compact local
proartinian `𝓞`-algebra, as an object of `ProartinianCat 𝓞`. -/
noncomputable def closedSubalgebraObj : ProartinianCat 𝓞 :=
  letI := ClosedSubalgebra.isLocalProartinianAlgebra S hS
  of 𝓞 S

/-- **Inclusion of a closed subalgebra.** The inclusion of a closed subalgebra of a compact local
proartinian `𝓞`-algebra `A` into `A`, as a morphism of `ProartinianCat 𝓞`. -/
noncomputable def closedSubalgebraι : closedSubalgebraObj S hS ⟶ A :=
  letI := ClosedSubalgebra.isLocalProartinianAlgebra S hS
  ofHom ⟨S.val, continuous_subtype_val⟩

@[simp]
theorem closedSubalgebraι_apply (x : S) : (closedSubalgebraι S hS).hom x = (x : A.carrier) := rfl

theorem closedSubalgebraι_injective : Function.Injective (closedSubalgebraι S hS).hom :=
  Subtype.val_injective

end ClosedSubalgebraObj

end ProartinianCat

section Universal

open ProartinianCat

variable {n : Type v} [Fintype n] [DecidableEq n]
variable {G : Type w} [Group G] [TopologicalSpace G]

namespace TraceAlgebra

variable [IsLocalRing 𝓞] [Finite (ResidueField 𝓞)] {A : ProartinianCat 𝓞}

/-- **Trace algebra.** For a local ring `𝓞` with finite residue field, the trace algebra of `ρ`:
its trace subalgebra, as an object of `ProartinianCat 𝓞`. -/
noncomputable def obj (ρ : G →ₜ* GL n A) : ProartinianCat 𝓞 :=
  closedSubalgebraObj (traceSubalgebra 𝓞 ρ) (isClosed_traceSubalgebra ρ)

/-- **Inclusion of the trace algebra.** For a local ring `𝓞` with finite residue field, the
inclusion of the trace algebra of `ρ` into `A`. -/
noncomputable def ι (ρ : G →ₜ* GL n A) : obj ρ ⟶ A :=
  closedSubalgebraι (traceSubalgebra 𝓞 ρ) (isClosed_traceSubalgebra ρ)

end TraceAlgebra

end Universal

end Deformation
