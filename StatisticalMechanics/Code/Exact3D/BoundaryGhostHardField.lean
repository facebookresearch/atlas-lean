/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.FKPositiveSubcriticalQ2Bridge
import Code.Exact3D.FiniteHardField
import Code.Sharpness.FieldGhostDict












open Filter
open scoped BigOperators Topology

namespace StatMech
namespace Exact3D


abbrev BoundaryGhostConfig (d n : ℕ) :=
  ConfigSpace (Option (FK.boxVerts d n))




noncomputable def boundaryGhostOriginalBase (d n : ℕ) (β : ℝ)
    (σ : BoundaryGhostConfig d n) : ℝ :=
  Sharpness.boltzmannJ (FK.boxGraph d n) β (fun _ => 1)
    (fun x => σ (some x))



noncomputable def boundaryGhostOnePointObservable (d n : ℕ)
    (σ : BoundaryGhostConfig d n) : ℝ :=
  Ising.spinProd (finiteBoundaryGhostOnePointSource d n) σ



theorem boundaryGhostOnePointObservable_eq (d n : ℕ)
    (σ : BoundaryGhostConfig d n) :
    boundaryGhostOnePointObservable d n σ =
      Ising.spin σ (some (IsingFK.boxOrigin d n)) * Ising.spin σ none := by
  simp [boundaryGhostOnePointObservable, finiteBoundaryGhostOnePointSource,
    Ising.spinProd]




noncomputable def boundaryGhostMismatchCount (d n : ℕ)
    (σ : BoundaryGhostConfig d n) : ℕ :=
  ((Finset.univ : Finset (FK.boxVerts d n)).filter
    (fun x => FK.boxBoundary d n x ∧ σ (some x) ≠ σ none)).card



theorem boundaryGhostMismatchCount_eq_zero_iff (d n : ℕ)
    (σ : BoundaryGhostConfig d n) :
    boundaryGhostMismatchCount d n σ = 0 ↔
      ∀ x : FK.boxVerts d n, FK.boxBoundary d n x →
        σ (some x) = σ none := by
  classical
  unfold boundaryGhostMismatchCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h x hx
    by_contra hne
    exact h (Finset.mem_univ x) ⟨hx, hne⟩
  · intro h x _hx hxbad
    exact hxbad.2 (h x hxbad.1)



theorem boundaryGhost_bond_some_none_eq_if
    {V : Type*} (σ : ConfigSpace (Option V)) (x : V) :
    Ising.bond σ s(some x, none) =
      if σ (some x) = σ none then 1 else -1 := by
  rw [Ising.bond_mk]
  unfold Ising.spin
  by_cases h : σ (some x) = σ none
  · rw [if_pos h]
    cases hnone : σ none <;> cases hsome : σ (some x) <;> simp_all
  · rw [if_neg h]
    cases hnone : σ none <;> cases hsome : σ (some x) <;> simp_all



theorem finset_sum_ite_neg_one_eq_card_sub_two_filter
    {α : Type*} (s : Finset α)
    (p : α → Prop) [DecidablePred p] :
    (∑ x ∈ s, if p x then (-1 : ℝ) else 1) =
      (s.card : ℝ) - 2 * ((s.filter p).card : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s has ih =>
      by_cases hp : p a
      · simp [Finset.filter_insert, has, hp, ih]
        ring
      · simp [Finset.filter_insert, has, hp, ih]
        ring



theorem boundaryGhost_boundaryBondSum_eq_card_sub_two_mismatch
    (d n : ℕ) (σ : BoundaryGhostConfig d n) :
    (∑ x ∈ (Finset.univ.filter (FK.boxBoundary d n)),
        Ising.bond σ s(some x, none)) =
      (((Finset.univ.filter (FK.boxBoundary d n)).card : ℝ) -
        2 * (boundaryGhostMismatchCount d n σ : ℝ)) := by
  classical
  let bdrySet : Finset (FK.boxVerts d n) :=
    Finset.univ.filter (FK.boxBoundary d n)
  let bad : FK.boxVerts d n → Prop := fun x => σ (some x) ≠ σ none
  have hterm :
      ∀ x, Ising.bond σ s(some x, none) =
        if bad x then (-1 : ℝ) else 1 := by
    intro x
    rw [boundaryGhost_bond_some_none_eq_if]
    by_cases hx : σ (some x) = σ none
    · simp [bad, hx]
    · simp [bad, hx]
  calc
    (∑ x ∈ (Finset.univ.filter (FK.boxBoundary d n)),
        Ising.bond σ s(some x, none))
        = ∑ x ∈ bdrySet, if bad x then (-1 : ℝ) else 1 := by
          refine Finset.sum_congr ?_ ?_
          · rfl
          · intro x _hx
            rw [hterm x]
    _ = (bdrySet.card : ℝ) - 2 * ((bdrySet.filter bad).card : ℝ) := by
          exact finset_sum_ite_neg_one_eq_card_sub_two_filter bdrySet bad
    _ = (((Finset.univ.filter (FK.boxBoundary d n)).card : ℝ) -
        2 * (boundaryGhostMismatchCount d n σ : ℝ)) := by
          simp [bdrySet, bad, boundaryGhostMismatchCount,
            Finset.filter_filter]




theorem boundaryGhost_weightedBondSum_split
    (d n : ℕ) (H : ℝ) (σ : BoundaryGhostConfig d n) :
    (∑ e ∈ (Sharpness.withGhost (FK.boxGraph d n)).edgeFinset,
        boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1) e *
          Ising.bond σ e)
      =
      (∑ e ∈ (FK.boxGraph d n).edgeFinset,
          (1 : ℝ) * Ising.bond (fun x => σ (some x)) e)
        + H * ∑ x ∈ (Finset.univ.filter (FK.boxBoundary d n)),
          Ising.bond σ s(some x, none) := by
  classical
  rw [Sharpness.FieldGhostDict.withGhost_edgeFinset_eq,
    Finset.sum_union
      (Sharpness.FieldGhostDict.disjoint_orig_ghost (FK.boxGraph d n))]
  congr 1
  · rw [Sharpness.FieldGhostDict.origEdges, Finset.sum_image]
    · refine Finset.sum_congr rfl (fun e _ => ?_)
      induction e with
      | h x y =>
          rw [Sym2.map_mk, Ising.bond_mk, Ising.bond_mk]
          simp only [boundaryGhostCoupling_some_some, one_mul]
          unfold Ising.spin
          rfl
    · intro a _ b _ hab
      exact Sym2.map.injective (Option.some_injective (FK.boxVerts d n)) hab
  · rw [Sharpness.FieldGhostDict.ghostEdges, Finset.sum_image]
    · rw [Finset.mul_sum]
      calc
        (∑ x : FK.boxVerts d n,
            boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1)
                s(some x, none) *
              Ising.bond σ s(some x, none))
            = ∑ x : FK.boxVerts d n,
                if FK.boxBoundary d n x then
                  H * Ising.bond σ s(some x, none)
                else 0 := by
              refine Finset.sum_congr rfl (fun x _ => ?_)
              by_cases hx : FK.boxBoundary d n x <;> simp [hx]
        _ = ∑ x ∈ (Finset.univ.filter (FK.boxBoundary d n)),
              H * Ising.bond σ s(some x, none) := by
              rw [← Finset.sum_filter]
    · intro a _ b _ hab
      rw [Sym2.eq_iff] at hab
      rcases hab with ⟨h1, _⟩ | ⟨_h1, h2⟩
      · exact Option.some_injective (FK.boxVerts d n) h1
      · exact absurd h2 (by simp)



theorem boundaryGhost_weightedBondSum_eq_original_add_mismatch
    (d n : ℕ) (H : ℝ) (σ : BoundaryGhostConfig d n) :
    (∑ e ∈ (Sharpness.withGhost (FK.boxGraph d n)).edgeFinset,
        boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1) e *
          Ising.bond σ e)
      =
      (∑ e ∈ (FK.boxGraph d n).edgeFinset,
          (1 : ℝ) * Ising.bond (fun x => σ (some x)) e)
        + H * (((Finset.univ.filter (FK.boxBoundary d n)).card : ℝ) -
          2 * (boundaryGhostMismatchCount d n σ : ℝ)) := by
  rw [boundaryGhost_weightedBondSum_split,
    boundaryGhost_boundaryBondSum_eq_card_sub_two_mismatch]




noncomputable def boundaryGhostCountFactor (d n : ℕ) (β H : ℝ)
    (σ : BoundaryGhostConfig d n) : ℝ :=
  countHardFieldFactor (boundaryGhostMismatchCount d n) (2 * β) H σ




theorem boundaryGhost_boltzmannJ_eq_common_mul_base_mul_countFactor
    (d n : ℕ) (β H : ℝ) (σ : BoundaryGhostConfig d n) :
    Sharpness.boltzmannJ (Sharpness.withGhost (FK.boxGraph d n)) β
        (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1)) σ
      =
      Real.exp (β * H *
          ((Finset.univ.filter (FK.boxBoundary d n)).card : ℝ)) *
        boundaryGhostOriginalBase d n β σ *
          boundaryGhostCountFactor d n β H σ := by
  unfold boundaryGhostOriginalBase boundaryGhostCountFactor
    countHardFieldFactor
  unfold Sharpness.boltzmannJ
  rw [boundaryGhost_weightedBondSum_eq_original_add_mismatch]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring



noncomputable def boundaryGhostAlignedLimitFactor (d n : ℕ)
    (σ : BoundaryGhostConfig d n) : ℝ :=
  countHardFieldLimitFactor (boundaryGhostMismatchCount d n) σ



theorem boundaryGhostCountFactor_tendsto (d n : ℕ)
    {β : ℝ} (hβ : 0 < β) (σ : BoundaryGhostConfig d n) :
    Tendsto (fun H : ℝ => boundaryGhostCountFactor d n β H σ)
      atTop
      (𝓝 (boundaryGhostAlignedLimitFactor d n σ)) := by
  have hscale : 0 < 2 * β := by linarith
  exact countHardFieldFactor_tendsto
    (boundaryGhostMismatchCount d n) hscale σ



theorem boundaryGhostCountFactorRatio_tendsto (d n : ℕ)
    {β : ℝ} (hβ : 0 < β)
    (base obs : BoundaryGhostConfig d n → ℝ)
    (hden :
      finiteFactorLimitDenominator
        (Finset.univ : Finset (BoundaryGhostConfig d n))
        base (boundaryGhostAlignedLimitFactor d n) ≠ 0) :
    Tendsto
      (fun H : ℝ =>
        finiteFactorRatio
          (Finset.univ : Finset (BoundaryGhostConfig d n))
          base obs (boundaryGhostCountFactor d n β) H)
      atTop
      (𝓝
        (finiteFactorLimitRatio
          (Finset.univ : Finset (BoundaryGhostConfig d n))
          base obs (boundaryGhostAlignedLimitFactor d n))) := by
  exact finiteFactorRatio_tendsto
    (Finset.univ : Finset (BoundaryGhostConfig d n))
    base obs (boundaryGhostAlignedLimitFactor d n)
    (boundaryGhostCountFactor d n β)
    (fun σ _hσ => boundaryGhostCountFactor_tendsto d n hβ σ)
    hden





theorem boundaryGhostExpectationJ_eq_countFactorRatio
    (d n : ℕ) (β H : ℝ) :
    Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph d n)) β
        (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1))
        (finiteBoundaryGhostOnePointSource d n)
      =
      finiteFactorRatio
        (Finset.univ : Finset (BoundaryGhostConfig d n))
        (boundaryGhostOriginalBase d n β)
        (boundaryGhostOnePointObservable d n)
        (boundaryGhostCountFactor d n β) H := by
  classical
  let C : ℝ :=
    Real.exp (β * H *
      ((Finset.univ.filter (FK.boxBoundary d n)).card : ℝ))
  have hC : C ≠ 0 := Real.exp_ne_zero _
  have hnum :
      (∑ σ : BoundaryGhostConfig d n,
          Ising.spinProd (finiteBoundaryGhostOnePointSource d n) σ *
            Sharpness.boltzmannJ (Sharpness.withGhost (FK.boxGraph d n)) β
              (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1))
              σ)
        =
      C * finiteFactorNumerator
        (Finset.univ : Finset (BoundaryGhostConfig d n))
        (boundaryGhostOriginalBase d n β)
        (boundaryGhostOnePointObservable d n)
        (boundaryGhostCountFactor d n β) H := by
    unfold finiteFactorNumerator
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [boundaryGhost_boltzmannJ_eq_common_mul_base_mul_countFactor]
    simp [C, boundaryGhostOnePointObservable]
    ring
  have hden :
      Sharpness.partitionJ (Sharpness.withGhost (FK.boxGraph d n)) β
          (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1))
        =
      C * finiteFactorDenominator
        (Finset.univ : Finset (BoundaryGhostConfig d n))
        (boundaryGhostOriginalBase d n β)
        (boundaryGhostCountFactor d n β) H := by
    unfold Sharpness.partitionJ finiteFactorDenominator
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [boundaryGhost_boltzmannJ_eq_common_mul_base_mul_countFactor]
    simp [C]
    ring
  unfold Sharpness.expectationJ finiteFactorRatio
  rw [hnum, hden]
  exact mul_div_mul_left _ _ hC



theorem finiteBoundaryGhostCurrentOnePoint_eq_countFactorRatio
    (d n : ℕ) (β H : ℝ) :
    finiteBoundaryGhostCurrentOnePoint d n β H =
      finiteFactorRatio
        (Finset.univ : Finset (BoundaryGhostConfig d n))
        (boundaryGhostOriginalBase d n β)
        (boundaryGhostOnePointObservable d n)
        (boundaryGhostCountFactor d n β) H := by
  rw [finiteBoundaryGhostCurrentOnePoint_eq_expectationJ,
    boundaryGhostExpectationJ_eq_countFactorRatio]




noncomputable def boolFin2Equiv : Bool ≃ Fin 2 where
  toFun := IsingFK.bToF
  invFun := fun a => a = 0
  left_inv := by
    intro b
    cases b <;> simp [IsingFK.bToF]
  right_inv := by
    intro a
    fin_cases a <;> simp [IsingFK.bToF]


noncomputable def boolConfigFin2Equiv (V : Type*) :
    ConfigSpace V ≃ (V → Fin 2) :=
  Equiv.piCongrRight fun _ => boolFin2Equiv


theorem isingSpin_bToF_eq_spin {V : Type*} (τ : ConfigSpace V) (x : V) :
    FK.isingSpin (IsingFK.bToF (τ x)) = Ising.spin τ x := by
  simp [IsingFK.isingSpin_bToF, Ising.spin]


theorem isingBond_bToF_eq_bond {V : Type*} (τ : ConfigSpace V)
    (e : Sym2 V) :
    IsingFK.isingBond (fun x => IsingFK.bToF (τ x)) e =
      Ising.bond τ e := by
  induction e with
  | h x y =>
      rw [IsingFK.isingBond_mk, Ising.bond_mk]
      simp [isingSpin_bToF_eq_spin]



theorem boltzmannJ_one_flipV {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (τ : ConfigSpace V) :
    Sharpness.boltzmannJ G β (fun _ => 1)
        (Sharpness.FieldGhostDict.flipV τ) =
      Sharpness.boltzmannJ G β (fun _ => 1) τ := by
  classical
  unfold Sharpness.boltzmannJ
  congr 1
  refine congrArg (fun t : ℝ => β * t) ?_
  refine Finset.sum_congr rfl (fun e _he => ?_)
  rw [Sharpness.FieldGhostDict.bond_flipV]




theorem isingWiredWeight_bToF_eq_if
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (bdry : V → Prop) [DecidablePred bdry]
    (β : ℝ) (τ : ConfigSpace V) :
    IsingFK.isingWiredWeight G bdry β
        (fun x => IsingFK.bToF (τ x)) =
      if (∀ x : V, bdry x → τ x = true) then
        Sharpness.boltzmannJ G β (fun _ => 1) τ
      else 0 := by
  classical
  by_cases h : ∀ x : V, bdry x → τ x = true
  · have hbf : IsingFK.BoundaryFixed bdry (0 : Fin 2)
        (fun x => IsingFK.bToF (τ x)) := by
      intro x hx
      change IsingFK.bToF (τ x) = 0
      rw [h x hx]
      rfl
    rw [if_pos h]
    unfold IsingFK.isingWiredWeight Sharpness.boltzmannJ
    rw [if_pos hbf]
    congr 1
    refine congrArg (fun t : ℝ => β * t) ?_
    refine Finset.sum_congr rfl (fun e _he => ?_)
    rw [isingBond_bToF_eq_bond]
    ring
  · have hbf : ¬ IsingFK.BoundaryFixed bdry (0 : Fin 2)
        (fun x => IsingFK.bToF (τ x)) := by
      intro hfixed
      apply h
      intro x hx
      have hx0 := hfixed x hx
      cases hτ : τ x <;> simp [IsingFK.bToF, hτ] at hx0 ⊢
    rw [if_neg h]
    unfold IsingFK.isingWiredWeight
    rw [if_neg hbf]



theorem isingWiredZ_eq_boolBoundaryBase
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (bdry : V → Prop) [DecidablePred bdry]
    (β : ℝ) :
    IsingFK.isingWiredZ G bdry β =
      ∑ τ : ConfigSpace V,
        if (∀ x : V, bdry x → τ x = true) then
          Sharpness.boltzmannJ G β (fun _ => 1) τ
        else 0 := by
  classical
  unfold IsingFK.isingWiredZ
  rw [← Equiv.sum_comp (boolConfigFin2Equiv V)
    (fun σ : V → Fin 2 => IsingFK.isingWiredWeight G bdry β σ)]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  change IsingFK.isingWiredWeight G bdry β
      (fun x => IsingFK.bToF (τ x)) = _
  exact isingWiredWeight_bToF_eq_if G bdry β τ



theorem isingWiredOnePointNumerator_eq_boolBoundaryBase
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (bdry : V → Prop) [DecidablePred bdry]
    (β : ℝ) (x : V) :
    (∑ σ : V → Fin 2,
        IsingFK.isingWiredWeight G bdry β σ * FK.isingSpin (σ x)) =
      ∑ τ : ConfigSpace V,
        if (∀ y : V, bdry y → τ y = true) then
          Sharpness.boltzmannJ G β (fun _ => 1) τ * Ising.spin τ x
        else 0 := by
  classical
  rw [← Equiv.sum_comp (boolConfigFin2Equiv V)
    (fun σ : V → Fin 2 =>
      IsingFK.isingWiredWeight G bdry β σ * FK.isingSpin (σ x))]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  change IsingFK.isingWiredWeight G bdry β
      (fun x => IsingFK.bToF (τ x)) *
        FK.isingSpin (IsingFK.bToF (τ x)) = _
  rw [isingWiredWeight_bToF_eq_if G bdry β τ,
    isingSpin_bToF_eq_spin]
  by_cases h : ∀ y : V, bdry y → τ y = true <;> simp [h]




theorem boundaryGhostMismatchCount_split_eq_zero_iff (d n : ℕ)
    (b : Bool) (τ : ConfigSpace (FK.boxVerts d n)) :
    boundaryGhostMismatchCount d n
        (fun a => Option.rec b τ a : BoundaryGhostConfig d n) = 0 ↔
      ∀ x : FK.boxVerts d n, FK.boxBoundary d n x → τ x = b := by
  simpa using boundaryGhostMismatchCount_eq_zero_iff d n
    (fun a => Option.rec b τ a : BoundaryGhostConfig d n)



theorem boundaryGhostAlignedLimitFactor_split_eq_if (d n : ℕ)
    (b : Bool) (τ : ConfigSpace (FK.boxVerts d n)) :
    boundaryGhostAlignedLimitFactor d n
        (fun a => Option.rec b τ a : BoundaryGhostConfig d n) =
      if (∀ x : FK.boxVerts d n, FK.boxBoundary d n x → τ x = b) then
        1 else 0 := by
  unfold boundaryGhostAlignedLimitFactor countHardFieldLimitFactor
  by_cases h : ∀ x : FK.boxVerts d n, FK.boxBoundary d n x → τ x = b
  · rw [if_pos h]
    have hz := (boundaryGhostMismatchCount_split_eq_zero_iff d n b τ).mpr h
    rw [if_pos hz]
  · rw [if_neg h]
    have hz : boundaryGhostMismatchCount d n
        (fun a => Option.rec b τ a : BoundaryGhostConfig d n) ≠ 0 := by
      intro hz
      exact h ((boundaryGhostMismatchCount_split_eq_zero_iff d n b τ).mp hz)
    rw [if_neg hz]



theorem boundaryGhostOnePointObservable_split_true (d n : ℕ)
    (τ : ConfigSpace (FK.boxVerts d n)) :
    boundaryGhostOnePointObservable d n
        (fun a => Option.rec true τ a : BoundaryGhostConfig d n) =
      Ising.spin τ (IsingFK.boxOrigin d n) := by
  rw [boundaryGhostOnePointObservable_eq]
  change Ising.spin τ (IsingFK.boxOrigin d n) * (1 : ℝ) =
    Ising.spin τ (IsingFK.boxOrigin d n)
  ring



theorem boundaryGhostOnePointObservable_split_false (d n : ℕ)
    (τ : ConfigSpace (FK.boxVerts d n)) :
    boundaryGhostOnePointObservable d n
        (fun a => Option.rec false τ a : BoundaryGhostConfig d n) =
      -(Ising.spin τ (IsingFK.boxOrigin d n)) := by
  rw [boundaryGhostOnePointObservable_eq]
  change Ising.spin τ (IsingFK.boxOrigin d n) * (-1 : ℝ) =
    -(Ising.spin τ (IsingFK.boxOrigin d n))
  ring



theorem boundaryGhostLimitDenominator_trueSector_eq_wiredZ
    (d n : ℕ) (β : ℝ) :
    (∑ τ : ConfigSpace (FK.boxVerts d n),
        boundaryGhostOriginalBase d n β
            (fun a => Option.rec true τ a : BoundaryGhostConfig d n) *
          boundaryGhostAlignedLimitFactor d n
            (fun a => Option.rec true τ a : BoundaryGhostConfig d n)) =
      IsingFK.isingWiredZ (FK.boxGraph d n) (FK.boxBoundary d n) β := by
  classical
  rw [isingWiredZ_eq_boolBoundaryBase]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [boundaryGhostAlignedLimitFactor_split_eq_if]
  by_cases h : ∀ x : FK.boxVerts d n, FK.boxBoundary d n x → τ x = true
  · rw [if_pos h, if_pos h]
    change Sharpness.boltzmannJ (FK.boxGraph d n) β (fun _ => 1) τ * 1 =
      Sharpness.boltzmannJ (FK.boxGraph d n) β (fun _ => 1) τ
    ring
  · rw [if_neg h, if_neg h]
    ring



theorem boundaryGhostLimitDenominator_falseSector_eq_wiredZ
    (d n : ℕ) (β : ℝ) :
    (∑ τ : ConfigSpace (FK.boxVerts d n),
        boundaryGhostOriginalBase d n β
            (fun a => Option.rec false τ a : BoundaryGhostConfig d n) *
          boundaryGhostAlignedLimitFactor d n
            (fun a => Option.rec false τ a : BoundaryGhostConfig d n)) =
      IsingFK.isingWiredZ (FK.boxGraph d n) (FK.boxBoundary d n) β := by
  classical
  rw [isingWiredZ_eq_boolBoundaryBase]
  rw [← Equiv.sum_comp
    (Sharpness.FieldGhostDict.flipV_involutive
      (V := FK.boxVerts d n)).toPerm
    (fun τ : ConfigSpace (FK.boxVerts d n) =>
      if (∀ x : FK.boxVerts d n, FK.boxBoundary d n x → τ x = true) then
        Sharpness.boltzmannJ (FK.boxGraph d n) β (fun _ => 1) τ else 0)]
  simp only [Function.Involutive.coe_toPerm]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [boundaryGhostAlignedLimitFactor_split_eq_if]
  have hiff :
      (∀ x : FK.boxVerts d n, FK.boxBoundary d n x →
        Sharpness.FieldGhostDict.flipV τ x = true) ↔
      (∀ x : FK.boxVerts d n, FK.boxBoundary d n x → τ x = false) := by
    constructor
    · intro h x hx
      have := h x hx
      unfold Sharpness.FieldGhostDict.flipV at this
      cases hτ : τ x <;> simp [hτ] at this ⊢
    · intro h x hx
      have := h x hx
      unfold Sharpness.FieldGhostDict.flipV
      rw [this]
      rfl
  by_cases hfalse :
      ∀ x : FK.boxVerts d n, FK.boxBoundary d n x → τ x = false
  · have htrue : ∀ x : FK.boxVerts d n, FK.boxBoundary d n x →
        Sharpness.FieldGhostDict.flipV τ x = true := hiff.mpr hfalse
    rw [if_pos hfalse, if_pos htrue]
    change Sharpness.boltzmannJ (FK.boxGraph d n) β (fun _ => 1) τ * 1 =
      Sharpness.boltzmannJ (FK.boxGraph d n) β (fun _ => 1)
        (Sharpness.FieldGhostDict.flipV τ)
    rw [boltzmannJ_one_flipV]
    ring
  · have htrue : ¬ ∀ x : FK.boxVerts d n, FK.boxBoundary d n x →
        Sharpness.FieldGhostDict.flipV τ x = true := by
      intro ht
      exact hfalse (hiff.mp ht)
    rw [if_neg hfalse, if_neg htrue]
    ring



theorem boundaryGhostLimitDenominator_eq_two_mul_wiredZ
    (d n : ℕ) (β : ℝ) :
    finiteFactorLimitDenominator
        (Finset.univ : Finset (BoundaryGhostConfig d n))
        (boundaryGhostOriginalBase d n β)
        (boundaryGhostAlignedLimitFactor d n) =
      2 * IsingFK.isingWiredZ
        (FK.boxGraph d n) (FK.boxBoundary d n) β := by
  classical
  unfold finiteFactorLimitDenominator
  rw [Sharpness.FieldGhostDict.sum_option_config, Fintype.sum_bool,
    boundaryGhostLimitDenominator_trueSector_eq_wiredZ,
    boundaryGhostLimitDenominator_falseSector_eq_wiredZ]
  ring



theorem boundaryGhostLimitNumerator_trueSector_eq_wiredNumerator
    (d n : ℕ) (β : ℝ) :
    (∑ τ : ConfigSpace (FK.boxVerts d n),
        boundaryGhostOriginalBase d n β
            (fun a => Option.rec true τ a : BoundaryGhostConfig d n) *
          boundaryGhostAlignedLimitFactor d n
            (fun a => Option.rec true τ a : BoundaryGhostConfig d n) *
          boundaryGhostOnePointObservable d n
            (fun a => Option.rec true τ a : BoundaryGhostConfig d n)) =
      ∑ σ : FK.boxVerts d n → Fin 2,
        IsingFK.isingWiredWeight (FK.boxGraph d n) (FK.boxBoundary d n) β σ *
          FK.isingSpin (σ (IsingFK.boxOrigin d n)) := by
  classical
  rw [isingWiredOnePointNumerator_eq_boolBoundaryBase]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [boundaryGhostAlignedLimitFactor_split_eq_if,
    boundaryGhostOnePointObservable_split_true]
  by_cases h : ∀ x : FK.boxVerts d n, FK.boxBoundary d n x → τ x = true
  · rw [if_pos h, if_pos h]
    change Sharpness.boltzmannJ (FK.boxGraph d n) β (fun _ => 1) τ * 1 *
        Ising.spin τ (IsingFK.boxOrigin d n) =
      Sharpness.boltzmannJ (FK.boxGraph d n) β (fun _ => 1) τ *
        Ising.spin τ (IsingFK.boxOrigin d n)
    ring
  · rw [if_neg h, if_neg h]
    ring



theorem boundaryGhostLimitNumerator_falseSector_eq_wiredNumerator
    (d n : ℕ) (β : ℝ) :
    (∑ τ : ConfigSpace (FK.boxVerts d n),
        boundaryGhostOriginalBase d n β
            (fun a => Option.rec false τ a : BoundaryGhostConfig d n) *
          boundaryGhostAlignedLimitFactor d n
            (fun a => Option.rec false τ a : BoundaryGhostConfig d n) *
          boundaryGhostOnePointObservable d n
            (fun a => Option.rec false τ a : BoundaryGhostConfig d n)) =
      ∑ σ : FK.boxVerts d n → Fin 2,
        IsingFK.isingWiredWeight (FK.boxGraph d n) (FK.boxBoundary d n) β σ *
          FK.isingSpin (σ (IsingFK.boxOrigin d n)) := by
  classical
  rw [isingWiredOnePointNumerator_eq_boolBoundaryBase]
  rw [← Equiv.sum_comp
    (Sharpness.FieldGhostDict.flipV_involutive
      (V := FK.boxVerts d n)).toPerm
    (fun τ : ConfigSpace (FK.boxVerts d n) =>
      if (∀ x : FK.boxVerts d n, FK.boxBoundary d n x → τ x = true) then
        Sharpness.boltzmannJ (FK.boxGraph d n) β (fun _ => 1) τ *
          Ising.spin τ (IsingFK.boxOrigin d n)
      else 0)]
  simp only [Function.Involutive.coe_toPerm]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [boundaryGhostAlignedLimitFactor_split_eq_if,
    boundaryGhostOnePointObservable_split_false]
  have hiff :
      (∀ x : FK.boxVerts d n, FK.boxBoundary d n x →
        Sharpness.FieldGhostDict.flipV τ x = true) ↔
      (∀ x : FK.boxVerts d n, FK.boxBoundary d n x → τ x = false) := by
    constructor
    · intro h x hx
      have := h x hx
      unfold Sharpness.FieldGhostDict.flipV at this
      cases hτ : τ x <;> simp [hτ] at this ⊢
    · intro h x hx
      have := h x hx
      unfold Sharpness.FieldGhostDict.flipV
      rw [this]
      rfl
  by_cases hfalse :
      ∀ x : FK.boxVerts d n, FK.boxBoundary d n x → τ x = false
  · have htrue : ∀ x : FK.boxVerts d n, FK.boxBoundary d n x →
        Sharpness.FieldGhostDict.flipV τ x = true := hiff.mpr hfalse
    rw [if_pos hfalse, if_pos htrue]
    change Sharpness.boltzmannJ (FK.boxGraph d n) β (fun _ => 1) τ * 1 *
        (-(Ising.spin τ (IsingFK.boxOrigin d n))) =
      Sharpness.boltzmannJ (FK.boxGraph d n) β (fun _ => 1)
          (Sharpness.FieldGhostDict.flipV τ) *
        Ising.spin (Sharpness.FieldGhostDict.flipV τ) (IsingFK.boxOrigin d n)
    rw [boltzmannJ_one_flipV, Sharpness.FieldGhostDict.spin_flipV]
    ring
  · have htrue : ¬ ∀ x : FK.boxVerts d n, FK.boxBoundary d n x →
        Sharpness.FieldGhostDict.flipV τ x = true := by
      intro ht
      exact hfalse (hiff.mp ht)
    rw [if_neg hfalse, if_neg htrue]
    ring



theorem boundaryGhostLimitNumerator_eq_two_mul_wiredNumerator
    (d n : ℕ) (β : ℝ) :
    finiteFactorLimitNumerator
        (Finset.univ : Finset (BoundaryGhostConfig d n))
        (boundaryGhostOriginalBase d n β)
        (boundaryGhostOnePointObservable d n)
        (boundaryGhostAlignedLimitFactor d n) =
      2 * (∑ σ : FK.boxVerts d n → Fin 2,
        IsingFK.isingWiredWeight (FK.boxGraph d n) (FK.boxBoundary d n) β σ *
          FK.isingSpin (σ (IsingFK.boxOrigin d n))) := by
  classical
  unfold finiteFactorLimitNumerator
  rw [Sharpness.FieldGhostDict.sum_option_config, Fintype.sum_bool,
    boundaryGhostLimitNumerator_trueSector_eq_wiredNumerator,
    boundaryGhostLimitNumerator_falseSector_eq_wiredNumerator]
  ring




theorem boundaryGhostAlignedLimitRatio_eq_wiredOnePoint
    (d n : ℕ) (β : ℝ) :
    finiteFactorLimitRatio
      (Finset.univ : Finset (BoundaryGhostConfig d n))
      (boundaryGhostOriginalBase d n β)
      (boundaryGhostOnePointObservable d n)
      (boundaryGhostAlignedLimitFactor d n) =
        IsingFK.isingWiredOnePoint
          (FK.boxGraph d n) (FK.boxBoundary d n) β
          (IsingFK.boxOrigin d n) := by
  unfold finiteFactorLimitRatio IsingFK.isingWiredOnePoint
  rw [boundaryGhostLimitNumerator_eq_two_mul_wiredNumerator,
    boundaryGhostLimitDenominator_eq_two_mul_wiredZ]
  exact mul_div_mul_left _ _ two_ne_zero



theorem boundaryGhostOriginalBase_pos (d n : ℕ) (β : ℝ)
    (σ : BoundaryGhostConfig d n) :
    0 < boundaryGhostOriginalBase d n β σ := by
  unfold boundaryGhostOriginalBase
  exact Sharpness.boltzmannJ_pos (FK.boxGraph d n) β (fun _ => 1)
    (fun x => σ (some x))




theorem boundaryGhostAlignedLimitDenominator_ne_zero
    (d n : ℕ) (β : ℝ) :
    finiteFactorLimitDenominator
      (Finset.univ : Finset (BoundaryGhostConfig d n))
      (boundaryGhostOriginalBase d n β)
      (boundaryGhostAlignedLimitFactor d n) ≠ 0 := by
  classical
  unfold boundaryGhostAlignedLimitFactor
  refine countHardFieldLimitDenominator_ne_zero_of_exists_pos
    (s := (Finset.univ : Finset (BoundaryGhostConfig d n)))
    (penalty := boundaryGhostMismatchCount d n)
    (base := boundaryGhostOriginalBase d n β) ?_ ?_
  · intro σ _hσ _hzero
    exact (boundaryGhostOriginalBase_pos d n β σ).le
  · let σ0 : BoundaryGhostConfig d n := fun _ => true
    refine ⟨σ0, Finset.mem_univ σ0, ?_, ?_⟩
    · rw [boundaryGhostMismatchCount_eq_zero_iff]
      intro x _hx
      rfl
    · exact boundaryGhostOriginalBase_pos d n β σ0




structure FiniteBoundaryGhostFactorDictionary (d n : ℕ) (β : ℝ)
    (base obs limitFactor : BoundaryGhostConfig d n → ℝ)
    (factor : ℝ → BoundaryGhostConfig d n → ℝ) : Prop where
  current_eq :
    ∀ H : ℝ,
      finiteBoundaryGhostCurrentOnePoint d n β H =
        finiteFactorRatio
          (Finset.univ : Finset (BoundaryGhostConfig d n))
          base obs factor H
  factor_tendsto :
    ∀ σ, σ ∈ (Finset.univ : Finset (BoundaryGhostConfig d n)) →
      Tendsto (fun H : ℝ => factor H σ) atTop (𝓝 (limitFactor σ))
  denominator_ne_zero :
    finiteFactorLimitDenominator
      (Finset.univ : Finset (BoundaryGhostConfig d n))
      base limitFactor ≠ 0
  limit_eq_wired :
    finiteFactorLimitRatio
      (Finset.univ : Finset (BoundaryGhostConfig d n))
      base obs limitFactor =
        IsingFK.isingWiredOnePoint
          (FK.boxGraph d n) (FK.boxBoundary d n) β
          (IsingFK.boxOrigin d n)






structure FiniteBoundaryGhostCountFactorDictionary (d n : ℕ) (β : ℝ)
    (base obs : BoundaryGhostConfig d n → ℝ) : Prop where
  beta_pos : 0 < β
  current_eq :
    ∀ H : ℝ,
      finiteBoundaryGhostCurrentOnePoint d n β H =
        finiteFactorRatio
          (Finset.univ : Finset (BoundaryGhostConfig d n))
          base obs (boundaryGhostCountFactor d n β) H
  denominator_ne_zero :
    finiteFactorLimitDenominator
      (Finset.univ : Finset (BoundaryGhostConfig d n))
      base (boundaryGhostAlignedLimitFactor d n) ≠ 0
  limit_eq_wired :
    finiteFactorLimitRatio
      (Finset.univ : Finset (BoundaryGhostConfig d n))
      base obs (boundaryGhostAlignedLimitFactor d n) =
        IsingFK.isingWiredOnePoint
          (FK.boxGraph d n) (FK.boxBoundary d n) β
          (IsingFK.boxOrigin d n)




structure FiniteBoundaryGhostAlignedLimitIdentification
    (d n : ℕ) (β : ℝ) : Prop where
  beta_pos : 0 < β
  limit_eq_wired :
    finiteFactorLimitRatio
      (Finset.univ : Finset (BoundaryGhostConfig d n))
      (boundaryGhostOriginalBase d n β)
      (boundaryGhostOnePointObservable d n)
      (boundaryGhostAlignedLimitFactor d n) =
        IsingFK.isingWiredOnePoint
          (FK.boxGraph d n) (FK.boxBoundary d n) β
          (IsingFK.boxOrigin d n)




theorem finiteBoundaryGhostAlignedLimitIdentification_of_pos
    (d n : ℕ) {β : ℝ} (hβ : 0 < β) :
    FiniteBoundaryGhostAlignedLimitIdentification d n β where
  beta_pos := hβ
  limit_eq_wired := boundaryGhostAlignedLimitRatio_eq_wiredOnePoint d n β




theorem finiteBoundaryGhostCountFactorDictionary_of_alignedLimitIdentification
    {d n : ℕ} {β : ℝ}
    (D : FiniteBoundaryGhostAlignedLimitIdentification d n β) :
    FiniteBoundaryGhostCountFactorDictionary d n β
      (boundaryGhostOriginalBase d n β)
      (boundaryGhostOnePointObservable d n) where
  beta_pos := D.beta_pos
  current_eq := finiteBoundaryGhostCurrentOnePoint_eq_countFactorRatio d n β
  denominator_ne_zero := boundaryGhostAlignedLimitDenominator_ne_zero d n β
  limit_eq_wired := D.limit_eq_wired



theorem finiteBoundaryGhostFactorDictionary_of_countFactorDictionary
    {d n : ℕ} {β : ℝ}
    {base obs : BoundaryGhostConfig d n → ℝ}
    (D : FiniteBoundaryGhostCountFactorDictionary d n β base obs) :
    FiniteBoundaryGhostFactorDictionary d n β
      base obs (boundaryGhostAlignedLimitFactor d n)
      (boundaryGhostCountFactor d n β) where
  current_eq := D.current_eq
  factor_tendsto := fun σ _hσ =>
    boundaryGhostCountFactor_tendsto d n D.beta_pos σ
  denominator_ne_zero := D.denominator_ne_zero
  limit_eq_wired := D.limit_eq_wired



theorem finiteBoundaryGhostCurrentOnePoint_tendsto_wired_of_factorDictionary
    {d n : ℕ} {β : ℝ}
    {base obs limitFactor : BoundaryGhostConfig d n → ℝ}
    {factor : ℝ → BoundaryGhostConfig d n → ℝ}
    (D :
      FiniteBoundaryGhostFactorDictionary d n β
        base obs limitFactor factor) :
    Tendsto (fun H : ℝ => finiteBoundaryGhostCurrentOnePoint d n β H)
      atTop
      (𝓝
        (IsingFK.isingWiredOnePoint
          (FK.boxGraph d n) (FK.boxBoundary d n) β
          (IsingFK.boxOrigin d n))) := by
  have ht :
      Tendsto
        (fun H : ℝ =>
          finiteFactorRatio
            (Finset.univ : Finset (BoundaryGhostConfig d n))
            base obs factor H)
        atTop
        (𝓝
          (finiteFactorLimitRatio
            (Finset.univ : Finset (BoundaryGhostConfig d n))
            base obs limitFactor)) :=
    finiteFactorRatio_tendsto
      (Finset.univ : Finset (BoundaryGhostConfig d n))
      base obs limitFactor factor
      D.factor_tendsto D.denominator_ne_zero
  have hfun :
      (fun H : ℝ => finiteBoundaryGhostCurrentOnePoint d n β H)
        =
      (fun H : ℝ =>
        finiteFactorRatio
          (Finset.univ : Finset (BoundaryGhostConfig d n))
          base obs factor H) := by
    funext H
    exact D.current_eq H
  rw [hfun]
  simpa [D.limit_eq_wired] using ht



theorem finiteBoundaryGhostCurrentOnePoint_tendsto_wired_of_countFactorDictionary
    {d n : ℕ} {β : ℝ}
    {base obs : BoundaryGhostConfig d n → ℝ}
    (D : FiniteBoundaryGhostCountFactorDictionary d n β base obs) :
    Tendsto (fun H : ℝ => finiteBoundaryGhostCurrentOnePoint d n β H)
      atTop
      (𝓝
        (IsingFK.isingWiredOnePoint
          (FK.boxGraph d n) (FK.boxBoundary d n) β
          (IsingFK.boxOrigin d n))) :=
  finiteBoundaryGhostCurrentOnePoint_tendsto_wired_of_factorDictionary
    (D := finiteBoundaryGhostFactorDictionary_of_countFactorDictionary D)




def FiniteBoundaryGhostFactorDictionaryPositiveSubcritical : Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∃ (base obs limitFactor : BoundaryGhostConfig 3 n → ℝ)
        (factor : ℝ → BoundaryGhostConfig 3 n → ℝ),
        FiniteBoundaryGhostFactorDictionary 3 n β
          base obs limitFactor factor



def FiniteBoundaryGhostCountFactorDictionaryPositiveSubcritical : Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∃ (base obs : BoundaryGhostConfig 3 n → ℝ),
        FiniteBoundaryGhostCountFactorDictionary 3 n β base obs



def FiniteBoundaryGhostAlignedLimitIdentificationPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      FiniteBoundaryGhostAlignedLimitIdentification 3 n β



theorem
    finiteBoundaryGhostAlignedLimitIdentificationPositiveSubcritical_proved :
    FiniteBoundaryGhostAlignedLimitIdentificationPositiveSubcritical := by
  intro β hβpos _hβc
  exact Eventually.of_forall fun n =>
    finiteBoundaryGhostAlignedLimitIdentification_of_pos 3 n hβpos



theorem
    finiteBoundaryGhostCountFactorDictionaryPositiveSubcritical_of_alignedLimit
    (hdict :
      FiniteBoundaryGhostAlignedLimitIdentificationPositiveSubcritical) :
    FiniteBoundaryGhostCountFactorDictionaryPositiveSubcritical := by
  intro β hβpos hβc
  exact (hdict β hβpos hβc).mono (fun n hn => by
    exact
      ⟨boundaryGhostOriginalBase 3 n β, boundaryGhostOnePointObservable 3 n,
        finiteBoundaryGhostCountFactorDictionary_of_alignedLimitIdentification
          hn⟩)


theorem finiteBoundaryGhostFactorDictionaryPositiveSubcritical_of_countFactor
    (hdict : FiniteBoundaryGhostCountFactorDictionaryPositiveSubcritical) :
    FiniteBoundaryGhostFactorDictionaryPositiveSubcritical := by
  intro β hβpos hβc
  exact (hdict β hβpos hβc).mono (fun n hn => by
    rcases hn with ⟨base, obs, D⟩
    exact
      ⟨base, obs, boundaryGhostAlignedLimitFactor 3 n,
        boundaryGhostCountFactor 3 n β,
        finiteBoundaryGhostFactorDictionary_of_countFactorDictionary D⟩)



theorem finiteQ2SimonBoundaryGhostHardFieldLimit_of_factorDictionary
    (hdict : FiniteBoundaryGhostFactorDictionaryPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostHardFieldLimitPositiveSubcritical := by
  intro β hβpos hβc
  exact (hdict β hβpos hβc).mono (fun n hn => by
    rcases hn with ⟨base, obs, limitFactor, factor, D⟩
    exact
      finiteBoundaryGhostCurrentOnePoint_tendsto_wired_of_factorDictionary
        (D := D))



theorem finiteQ2SimonBoundaryGhostHardFieldLimit_of_countFactorDictionary
    (hdict : FiniteBoundaryGhostCountFactorDictionaryPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostHardFieldLimitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostHardFieldLimit_of_factorDictionary
    (finiteBoundaryGhostFactorDictionaryPositiveSubcritical_of_countFactor hdict)



theorem finiteQ2SimonBoundaryGhostHardFieldLimit_of_alignedLimit
    (hdict :
      FiniteBoundaryGhostAlignedLimitIdentificationPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostHardFieldLimitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostHardFieldLimit_of_countFactorDictionary
    (finiteBoundaryGhostCountFactorDictionaryPositiveSubcritical_of_alignedLimit
      hdict)




theorem finiteQ2SimonBoundaryGhostHardFieldLimit_from_exactAlignedSector :
    FiniteQ2SimonBoundaryGhostHardFieldLimitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostHardFieldLimit_of_alignedLimit
    finiteBoundaryGhostAlignedLimitIdentificationPositiveSubcritical_proved



theorem finiteQ2SimonBoundaryGhostApprox_from_exactAlignedSector :
    FiniteQ2SimonBoundaryGhostApproxPositiveSubcritical :=
  finiteBoundaryGhostApprox_of_hardFieldLimit
    finiteQ2SimonBoundaryGhostHardFieldLimit_from_exactAlignedSector



theorem finiteCurrentSimon_of_exactBoundaryGhostComparison
    (hcompare :
      FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical) :
    FiniteQ2SimonFreeBoundaryCurrentPositiveSubcritical :=
  finiteCurrentSimon_of_boundaryGhostApprox_comparison
    finiteQ2SimonBoundaryGhostApprox_from_exactAlignedSector hcompare




theorem finiteIsingSimon_of_exactBoundaryGhostComparison
    (hcompare :
      FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical) :
    FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical :=
  finiteIsingSimon_of_boundaryGhostApprox_comparison
    finiteQ2SimonBoundaryGhostApprox_from_exactAlignedSector hcompare



theorem freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_exactBoundaryGhostComparison
    (hcompare :
      FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical) :
    FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_boundaryGhostApprox_comparison
    finiteQ2SimonBoundaryGhostApprox_from_exactAlignedSector hcompare




theorem freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (hcompare :
      FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical) :
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_finiteFK
    (freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_exactBoundaryGhostComparison
      hcompare)





theorem finiteCurrentSimon_of_exactBoundaryGhostFirstExitPositive
    (hfirst :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical) :
    FiniteQ2SimonFreeBoundaryCurrentPositiveSubcritical :=
  finiteCurrentSimon_of_exactBoundaryGhostComparison
    (finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive hfirst)



theorem finiteIsingSimon_of_exactBoundaryGhostFirstExitPositive
    (hfirst :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical) :
    FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical :=
  finiteIsingSimon_of_exactBoundaryGhostComparison
    (finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive hfirst)



theorem freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_exactBoundaryGhostFirstExitPositive
    (hfirst :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical) :
    FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_exactBoundaryGhostComparison
    (finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive hfirst)




theorem freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostFirstExitPositive
    (hfirst :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical) :
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive hfirst)

end Exact3D
end StatMech
