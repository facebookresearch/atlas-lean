/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.FK.InfiniteVolume
import Code.FK.EdgeConfigZ
import Code.Ising.FiniteVolumeRelabel
import Code.FrontierA.IsingSpinConformalScaling

open Filter Topology
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech StatMech.FK StatMech.Ising




noncomputable def finiteMarkedSpinCorrelation
    {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β h : Real) (marked : ι ↪ V) : Real :=
  isingExpectation G β h (spinProd (Finset.univ.map marked))


theorem finiteMarkedSpinCorrelation_nonneg
    {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β h : Real) (hβ : 0 ≤ β) (hh : 0 ≤ h) (marked : ι ↪ V) :
    0 ≤ finiteMarkedSpinCorrelation G β h marked := by
  exact gks_first G β h hβ hh (Finset.univ.map marked)




theorem finiteMarkedSpinCorrelation_relabel
    {V W ι : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] [Fintype ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y))
    (β h : Real) (marked : ι ↪ V) :
    finiteMarkedSpinCorrelation G β h marked =
      finiteMarkedSpinCorrelation H β h
        (marked.trans σ.toEmbedding) := by
  unfold finiteMarkedSpinCorrelation
  rw [isingExpectation_spinProd_relabel G H σ hσ]
  congr 2
  ext y
  simp only [Finset.mem_map, Finset.mem_univ, true_and,
    Function.Embedding.coe_trans, Equiv.coe_toEmbedding, Function.comp_apply]
  constructor
  · rintro ⟨v, ⟨i, rfl⟩, hv⟩
    exact ⟨i, hv⟩
  · rintro ⟨i, hi⟩
    exact ⟨marked i, ⟨i, rfl⟩, hi⟩




noncomputable def squareBoxMovingSpinCorrelation
    (ι : Type*) [Fintype ι]
    (β h : Real) (radius : Nat → Nat)
    (marked : ∀ n, ι ↪ boxVerts 2 (radius n)) : Nat → Real :=
  fun n => finiteMarkedSpinCorrelation (boxGraph 2 (radius n)) β h (marked n)

theorem squareBoxMovingSpinCorrelation_nonneg
    (ι : Type*) [Fintype ι]
    (β h : Real) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (radius : Nat → Nat)
    (marked : ∀ n, ι ↪ boxVerts 2 (radius n)) (n : Nat) :
    0 ≤ squareBoxMovingSpinCorrelation ι β h radius marked n := by
  exact finiteMarkedSpinCorrelation_nonneg
    (boxGraph 2 (radius n)) β h hβ hh (marked n)




theorem squareBoxMovingSpinCorrelation_eq_of_relabel
    (ι : Type*) [Fintype ι]
    (β h : Real) (sourceRadius targetRadius : Nat → Nat)
    (sourceMarked : ∀ n, ι ↪ boxVerts 2 (sourceRadius n))
    (targetMarked : ∀ n, ι ↪ boxVerts 2 (targetRadius n))
    (σ : ∀ n, boxVerts 2 (sourceRadius n) ≃ boxVerts 2 (targetRadius n))
    (hσ : ∀ n x y,
      (boxGraph 2 (sourceRadius n)).Adj x y ↔
        (boxGraph 2 (targetRadius n)).Adj (σ n x) (σ n y))
    (hmarked : ∀ n i, σ n (sourceMarked n i) = targetMarked n i) :
    squareBoxMovingSpinCorrelation ι β h sourceRadius sourceMarked =
      squareBoxMovingSpinCorrelation ι β h targetRadius targetMarked := by
  funext n
  rw [squareBoxMovingSpinCorrelation, squareBoxMovingSpinCorrelation]
  have htransport := finiteMarkedSpinCorrelation_relabel
    (boxGraph 2 (sourceRadius n)) (boxGraph 2 (targetRadius n))
    (σ n) (hσ n) β h (sourceMarked n)
  have hmarkedEmbedding :
      (sourceMarked n).trans (σ n).toEmbedding = targetMarked n := by
    apply DFunLike.ext _ _
    intro i
    exact hmarked n i
  simpa only [hmarkedEmbedding] using htransport




theorem spinMeshRenormalization_uniformScale
    (ι : Type*) [Fintype ι] {sourceδ targetδ : Real}
    (hsourceδ : 0 < sourceδ) (htargetδ : 0 < targetδ) :
    spinMeshRenormalization ι targetδ =
      (∏ _ : ι, (targetδ / sourceδ) ^ (-isingSpinScalingDimension)) *
        spinMeshRenormalization ι sourceδ := by
  unfold spinMeshRenormalization
  rw [Finset.prod_const, Finset.card_univ]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg htargetδ.le hsourceδ.le)]
  rw [show -isingSpinScalingDimension * (Fintype.card ι : Real) =
    -(Fintype.card ι : Real) * isingSpinScalingDimension by ring]
  rw [← Real.mul_rpow (div_nonneg htargetδ.le hsourceδ.le) hsourceδ.le]
  congr 1
  field_simp



noncomputable def squareBoxRenormalizedSpinCorrelation
    (ι : Type*) [Fintype ι]
    (δ : Nat → Real) (β h : Real) (radius : Nat → Nat)
    (marked : ∀ n, ι ↪ boxVerts 2 (radius n)) : Nat → Real :=
  spinRenormalizedCorrelation ι δ
    (squareBoxMovingSpinCorrelation ι β h radius marked)




theorem squareBoxRenormalizedSpinCorrelation_uniformScale_of_relabel
    (ι : Type*) [Fintype ι]
    (sourceδ targetδ : Nat → Real)
    (hsourceδ : ∀ n, 0 < sourceδ n) (htargetδ : ∀ n, 0 < targetδ n)
    (β h : Real) (sourceRadius targetRadius : Nat → Nat)
    (sourceMarked : ∀ n, ι ↪ boxVerts 2 (sourceRadius n))
    (targetMarked : ∀ n, ι ↪ boxVerts 2 (targetRadius n))
    (σ : ∀ n, boxVerts 2 (sourceRadius n) ≃ boxVerts 2 (targetRadius n))
    (hσ : ∀ n x y,
      (boxGraph 2 (sourceRadius n)).Adj x y ↔
        (boxGraph 2 (targetRadius n)).Adj (σ n x) (σ n y))
    (hmarked : ∀ n i, σ n (sourceMarked n i) = targetMarked n i) (n : Nat) :
    squareBoxRenormalizedSpinCorrelation
        ι targetδ β h targetRadius targetMarked n =
      (∏ _ : ι,
          (targetδ n / sourceδ n) ^ (-isingSpinScalingDimension)) *
        squareBoxRenormalizedSpinCorrelation
          ι sourceδ β h sourceRadius sourceMarked n := by
  unfold squareBoxRenormalizedSpinCorrelation spinRenormalizedCorrelation
  have hraw := congrFun (squareBoxMovingSpinCorrelation_eq_of_relabel
    ι β h sourceRadius targetRadius sourceMarked targetMarked σ hσ hmarked) n
  rw [← hraw, spinMeshRenormalization_uniformScale
    ι (hsourceδ n) (htargetδ n)]
  ring





theorem tendsto_squareBoxRenormalizedSpinCorrelation_uniformScale_of_relabel
    (ι : Type*) [Fintype ι]
    (sourceδ targetδ : Nat → Real)
    (hsourceδ : ∀ n, 0 < sourceδ n) (htargetδ : ∀ n, 0 < targetδ n)
    (β h : Real) (sourceRadius targetRadius : Nat → Nat)
    (sourceMarked : ∀ n, ι ↪ boxVerts 2 (sourceRadius n))
    (targetMarked : ∀ n, ι ↪ boxVerts 2 (targetRadius n))
    (σ : ∀ n, boxVerts 2 (sourceRadius n) ≃ boxVerts 2 (targetRadius n))
    (hσ : ∀ n x y,
      (boxGraph 2 (sourceRadius n)).Adj x y ↔
        (boxGraph 2 (targetRadius n)).Adj (σ n x) (σ n y))
    (hmarked : ∀ n i, σ n (sourceMarked n i) = targetMarked n i)
    {ρ L : Real} (hρ : 0 < ρ)
    (hratio : Tendsto (fun n ↦ targetδ n / sourceδ n) atTop (nhds ρ))
    (hsource : Tendsto
      (squareBoxRenormalizedSpinCorrelation
        ι sourceδ β h sourceRadius sourceMarked)
      atTop (nhds L)) :
    Tendsto
      (squareBoxRenormalizedSpinCorrelation
        ι targetδ β h targetRadius targetMarked)
      atTop (nhds ((∏ _ : ι, ρ ^ (-isingSpinScalingDimension)) * L)) := by
  have hratioPow : Tendsto
      (fun n ↦ (targetδ n / sourceδ n) ^ (-isingSpinScalingDimension))
      atTop (nhds (ρ ^ (-isingSpinScalingDimension))) :=
    hratio.rpow_const (Or.inl hρ.ne')
  have hfactor : Tendsto
      (fun n ↦ ∏ _ : ι,
        (targetδ n / sourceδ n) ^ (-isingSpinScalingDimension))
      atTop (nhds (∏ _ : ι, ρ ^ (-isingSpinScalingDimension))) := by
    exact tendsto_finsetProd Finset.univ (fun _ _ ↦ hratioPow)
  refine (hfactor.mul hsource).congr' (Filter.Eventually.of_forall fun n ↦ ?_)
  exact (squareBoxRenormalizedSpinCorrelation_uniformScale_of_relabel
    ι sourceδ targetδ hsourceδ htargetδ β h sourceRadius targetRadius
    sourceMarked targetMarked σ hσ hmarked n).symm




noncomputable def inverseUniformScaleConformalMap
    (rho : Real) : Complex → Complex :=
  fun z ↦ (rho⁻¹ : Complex) * z

@[simp] theorem deriv_inverseUniformScaleConformalMap
    (rho : Real) (z : Complex) :
    deriv (inverseUniformScaleConformalMap rho) z = (rho⁻¹ : Complex) := by
  have h := ((hasDerivAt_id z).const_mul (rho⁻¹ : Complex)).deriv
  change deriv (fun y : Complex ↦ (rho⁻¹ : Complex) * y) z =
    (rho⁻¹ : Complex)
  simpa only [mul_one, id_eq] using h



theorem spinConformalFactor_inverseUniformScaleConformalMap
    (ι : Type*) [Fintype ι] (a : ι → Complex)
    {rho : Real} (hrho : 0 < rho) :
    spinConformalFactor (inverseUniformScaleConformalMap rho) a =
      ∏ _ : ι, rho ^ (-isingSpinScalingDimension) := by
  classical
  unfold spinConformalFactor spinDerivativeFactor
  apply Finset.prod_congr rfl
  intro i _hi
  change ‖deriv (inverseUniformScaleConformalMap rho) (a i)‖ ^
      isingSpinScalingDimension = rho ^ (-isingSpinScalingDimension)
  rw [deriv_inverseUniformScaleConformalMap,
    show (rho⁻¹ : Complex) = (rho : Complex)⁻¹ by norm_num,
    norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrho,
    Real.rpow_neg_eq_inv_rpow]





theorem tendsto_squareBoxRenormalizedSpinCorrelation_inverseUniformScale_of_relabel
    (ι : Type*) [Fintype ι]
    (sourceδ targetδ : Nat → Real)
    (hsourceδ : ∀ n, 0 < sourceδ n) (htargetδ : ∀ n, 0 < targetδ n)
    (β h : Real) (sourceRadius targetRadius : Nat → Nat)
    (sourceMarked : ∀ n, ι ↪ boxVerts 2 (sourceRadius n))
    (targetMarked : ∀ n, ι ↪ boxVerts 2 (targetRadius n))
    (σ : ∀ n, boxVerts 2 (sourceRadius n) ≃ boxVerts 2 (targetRadius n))
    (hσ : ∀ n x y,
      (boxGraph 2 (sourceRadius n)).Adj x y ↔
        (boxGraph 2 (targetRadius n)).Adj (σ n x) (σ n y))
    (hmarked : ∀ n i, σ n (sourceMarked n i) = targetMarked n i)
    (a : ι → Complex) {rho L : Real} (hrho : 0 < rho)
    (hratio : Tendsto (fun n ↦ targetδ n / sourceδ n)
      atTop (nhds rho))
    (hsource : Tendsto
      (squareBoxRenormalizedSpinCorrelation
        ι sourceδ β h sourceRadius sourceMarked)
      atTop (nhds L)) :
    Tendsto
      (squareBoxRenormalizedSpinCorrelation
        ι targetδ β h targetRadius targetMarked)
      atTop (nhds
        (spinConformalFactor (inverseUniformScaleConformalMap rho) a * L)) := by
  rw [spinConformalFactor_inverseUniformScaleConformalMap ι a hrho]
  exact tendsto_squareBoxRenormalizedSpinCorrelation_uniformScale_of_relabel
    ι sourceδ targetδ hsourceδ htargetδ β h sourceRadius targetRadius
      sourceMarked targetMarked σ hσ hmarked hrho hratio hsource




theorem squareBox_radius_eq_of_equiv {sourceRadius targetRadius : Nat}
    (σ : boxVerts 2 sourceRadius ≃ boxVerts 2 targetRadius) :
    sourceRadius = targetRadius := by
  have hcard := Fintype.card_congr σ
  rw [ecz_boxVerts_card, ecz_boxVerts_card] at hcard
  have hside : 2 * sourceRadius + 1 = 2 * targetRadius + 1 :=
    Nat.pow_left_injective (by norm_num : (2 : Nat) ≠ 0) hcard
  omega



theorem squareBox_radiusSequence_eq_of_equiv
    {sourceRadius targetRadius : Nat → Nat}
    (σ : ∀ n, boxVerts 2 (sourceRadius n) ≃ boxVerts 2 (targetRadius n)) :
    sourceRadius = targetRadius := by
  funext n
  exact squareBox_radius_eq_of_equiv (σ n)



theorem squareBoxRenormalizedSpinCorrelation_eq_of_relabel
    (ι : Type*) [Fintype ι]
    (δ : Nat → Real) (β h : Real)
    (sourceRadius targetRadius : Nat → Nat)
    (sourceMarked : ∀ n, ι ↪ boxVerts 2 (sourceRadius n))
    (targetMarked : ∀ n, ι ↪ boxVerts 2 (targetRadius n))
    (σ : ∀ n, boxVerts 2 (sourceRadius n) ≃ boxVerts 2 (targetRadius n))
    (hσ : ∀ n x y,
      (boxGraph 2 (sourceRadius n)).Adj x y ↔
        (boxGraph 2 (targetRadius n)).Adj (σ n x) (σ n y))
    (hmarked : ∀ n i, σ n (sourceMarked n i) = targetMarked n i) :
    squareBoxRenormalizedSpinCorrelation ι δ β h sourceRadius sourceMarked =
      squareBoxRenormalizedSpinCorrelation ι δ β h targetRadius targetMarked := by
  unfold squareBoxRenormalizedSpinCorrelation
  rw [squareBoxMovingSpinCorrelation_eq_of_relabel
    ι β h sourceRadius targetRadius sourceMarked targetMarked σ hσ hmarked]



theorem squareBoxRenormalizedSpinCorrelation_transportError_eq_zero
    (ι : Type*) [Fintype ι]
    (δ : Nat → Real) (β h : Real)
    (sourceRadius targetRadius : Nat → Nat)
    (sourceMarked : ∀ n, ι ↪ boxVerts 2 (sourceRadius n))
    (targetMarked : ∀ n, ι ↪ boxVerts 2 (targetRadius n))
    (σ : ∀ n, boxVerts 2 (sourceRadius n) ≃ boxVerts 2 (targetRadius n))
    (hσ : ∀ n x y,
      (boxGraph 2 (sourceRadius n)).Adj x y ↔
        (boxGraph 2 (targetRadius n)).Adj (σ n x) (σ n y))
    (hmarked : ∀ n i, σ n (sourceMarked n i) = targetMarked n i) (n : Nat) :
    squareBoxRenormalizedSpinCorrelation ι δ β h targetRadius targetMarked n -
      squareBoxRenormalizedSpinCorrelation ι δ β h sourceRadius sourceMarked n = 0 := by
  rw [squareBoxRenormalizedSpinCorrelation_eq_of_relabel
    ι δ β h sourceRadius targetRadius sourceMarked targetMarked σ hσ hmarked]
  exact sub_self _

end StatMech.FrontierA
