/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EqualCharacteristicCoefficientModels
public import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Algebra.Order.Archimedean.Submonoid
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology

/-!
# Laurent-series fields over finite fields are nonarchimedean local fields

For a prime `p` and a finite field `k` of characteristic `p`, the Laurent-series
field `k((t))`, with the valuative relation of its `t`-adic valuation, is a
nonarchimedean local field.

Source: Fargues--Scholze, arXiv:2102.13459v4, Definition I.2.2 and Section II.1.
The native Laurent-series valuation and completeness results are reused from
pinned Mathlib.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.EqualCharacteristicFFModels

open MathlibExt.AlgebraicGeometry.EqualCharacteristicCoefficientModels
open Valued.integer
open scoped WithZero Topology

-- The t-adic valuation is nontrivial: the uniformizer has valuation exp (-1).
private theorem nontrivial_valued (k : Type) [Field k] :
    (Valued.v : Valuation (CoefficientField k) ℤᵐ⁰).IsNontrivial where
  exists_val_nontrivial := by
    refine ⟨HahnSeries.single (1 : ℤ) (1 : k), ?_, ?_⟩
    · rw [LaurentSeries.valuation_single_zpow]
      exact WithZero.exp_ne_zero
    · rw [LaurentSeries.valuation_single_zpow]
      simp only [ne_eq, WithZero.exp_eq_one]
      decide

-- The t-adic valuation has rank one.
private instance rankOne_valued (k : Type) [Field k] :
    (Valued.v : Valuation (CoefficientField k) ℤᵐ⁰).RankOne := by
  haveI := nontrivial_valued k
  exact (Valuation.nonempty_rankOne_iff_mulArchimedean.mpr inferInstance).some

-- The integer ring is a domain, transported from power series.
private instance isDomain_integers (k : Type) [Field k] : IsDomain (Integers k) :=
  MulEquiv.isDomain _ (integerEquiv k).symm.toMulEquiv

-- The integer ring is a DVR, transported from power series.
private instance dvr_integers (k : Type) [Field k] : IsDiscreteValuationRing (Integers k) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (integerEquiv k)

-- The residue field is finite: it is isomorphic to the finite coefficient field.
private theorem finite_residue (k : Type) [Field k] [Finite k] :
    Finite (Valued.ResidueField (CoefficientField k)) :=
  let e := (IsLocalRing.ResidueField.mapEquiv (integerEquiv k)).symm.trans
    PowerSeries.residueFieldOfPowerSeries
  (e.toEquiv.finite_iff).mpr inferInstance

-- The integer ring is complete, as a closed subset of a complete field.
private instance completeSpace_integers (k : Type) [Field k] : CompleteSpace (Integers k) := by
  have _ := Valued.isClosed_integer (R := CoefficientField k)
  exact IsClosed.completeSpace_coe

-- The integer ring is compact: complete DVR with finite residue field.
private instance compactSpace_integers (k : Type) [Field k] [Finite k] :
    CompactSpace (Integers k) :=
  compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
    ⟨inferInstance, inferInstance, finite_residue k⟩

-- The integer ring is a neighborhood of zero.
private theorem integers_mem_nhds_zero (k : Type) [Field k] :
    (↑(Valued.integer (CoefficientField k)) : Set (CoefficientField k)) ∈
      𝓝 (0 : CoefficientField k) := by
  refine Valued.mem_nhds_zero.mpr ⟨1, fun x hx ↦ ?_⟩
  simp only [Set.mem_ofPred_eq] at hx
  change x ∈ (Valued.v : Valuation (CoefficientField k) ℤᵐ⁰).integer
  rw [Valuation.mem_integer_iff]
  have hlt :=
    (Valuation.restrict_lt_iff_lt_embedding
      (v := (Valued.v : Valuation (CoefficientField k) ℤᵐ⁰))).mp hx
  simpa using hlt.le

-- The Laurent-series field is locally compact.
private theorem locallyCompact (k : Type) [Field k] [Finite k] :
    LocallyCompactSpace (CoefficientField k) := by
  have hmem := integers_mem_nhds_zero k
  have hcomp : IsCompact (↑(Valued.integer (CoefficientField k)) : Set (CoefficientField k)) :=
    isCompact_iff_compactSpace.mpr (compactSpace_integers k)
  exact IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup hcomp hmem

-- The Valued topology is the valuative topology for the t-adic relation.
private theorem valuativeTopology (k : Type) [Field k] :
    @IsValuativeTopology (CoefficientField k) _ (valuativeRelation k) _ := by
  let _ := valuativeRelation k
  exact IsValuativeTopology.of_mem_nhds_zero_iff_vle
    (Valued.v : Valuation (CoefficientField k) ℤᵐ⁰) (fun {s} ↦ Valued.mem_nhds_zero)

-- The t-adic valuative relation is nontrivial.
private theorem nontrivial_rel (k : Type) [Field k] :
    @ValuativeRel.IsNontrivial (CoefficientField k) _ (valuativeRelation k) := by
  let _ := valuativeRelation k
  exact (ValuativeRel.isNontrivial_iff_isNontrivial
    (Valued.v : Valuation (CoefficientField k) ℤᵐ⁰)).mpr (nontrivial_valued k)

-- The statement keeps the `[Fintype k]` binder of the wanted statement; only `Finite k` is used.
set_option linter.unusedFintypeInType false in
/-- For a prime $p$ and a finite field $k$ of characteristic $p$, the Laurent-series field $k((t))$,
with the valuative relation of its $t$-adic valuation, is a nonarchimedean local field. -/
public theorem laurentSeriesLocalField
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [Fintype k] :
    letI := valuativeRelation k
    IsNonarchimedeanLocalField (CoefficientField k) := by
  let _ := valuativeRelation k
  have _ := valuativeTopology k
  have _ := locallyCompact k
  have _ := nontrivial_rel k
  exact ⟨⟩

end WantedExt.AlgebraicGeometry.EqualCharacteristicFFModels
