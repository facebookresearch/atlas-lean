/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianFourCurrentTree











open Finset SimpleGraph
open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false

namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

private abbrev TreeFourProfiles (G : SimpleGraph V) [DecidableRel G.Adj] :=
  ((G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)) ×
    ((G.edgeFinset -> Nat) × (G.edgeFinset -> Nat))


noncomputable def finiteTreeSeparatedFourSummand
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l y : V)
    (z : TreeFourProfiles G) : Real :=
  ((if sources G (ofEdgeFun G z.1.1) = grahamPairSupport i j
      then weight G beta J (ofEdgeFun G z.1.1) else 0) *
    (if sources G (ofEdgeFun G z.1.2) = ∅
      then weight G beta J (ofEdgeFun G z.1.2) else 0) *
    (if CurrentConnected G
        (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)) i y
      then 1 else 0)) *
  ((if sources G (ofEdgeFun G z.2.1) = grahamPairSupport k l
      then weight G beta J (ofEdgeFun G z.2.1) else 0) *
    (if sources G (ofEdgeFun G z.2.2) = ∅
      then weight G beta J (ofEdgeFun G z.2.2) else 0) *
    (if CurrentConnected G
        (ofEdgeFun G (fun e => z.2.1 e + z.2.2 e)) k y
      then 1 else 0))



noncomputable def finiteTreeIndependentIntersectionSummand
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V)
    (z : TreeFourProfiles G) : Real :=
  ((if sources G (ofEdgeFun G z.1.1) = grahamPairSupport i j
      then weight G beta J (ofEdgeFun G z.1.1) else 0) *
    (if sources G (ofEdgeFun G z.1.2) = ∅
      then weight G beta J (ofEdgeFun G z.1.2) else 0)) *
  ((if sources G (ofEdgeFun G z.2.1) = grahamPairSupport k l
      then weight G beta J (ofEdgeFun G z.2.1) else 0) *
    (if sources G (ofEdgeFun G z.2.2) = ∅
      then weight G beta J (ofEdgeFun G z.2.2) else 0)) *
  (if ∃ y : V,
      CurrentConnected G
        (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)) i y ∧
      CurrentConnected G
        (ofEdgeFun G (fun e => z.2.1 e + z.2.2 e)) k y
    then 1 else 0)



noncomputable def finiteTreeIndependentIntersectionFourMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V) : Real :=
  ∑' z : TreeFourProfiles G,
    finiteTreeIndependentIntersectionSummand G beta J i j k l z

theorem finiteTreeSeparatedFourMass_eq_summand
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l y : V) :
    finiteTreeSeparatedFourMass G beta J i j k l y =
      ∑' z : TreeFourProfiles G,
        finiteTreeSeparatedFourSummand G beta J i j k l y z := by
  unfold finiteTreeSeparatedFourMass
  apply tsum_congr
  rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
  rfl

private noncomputable def finiteTreeFourWeightMajorant
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (z : TreeFourProfiles G) : Real :=
  ‖weight G beta J (ofEdgeFun G z.1.1)‖ *
    ‖weight G beta J (ofEdgeFun G z.1.2)‖ *
    ‖weight G beta J (ofEdgeFun G z.2.1)‖ *
    ‖weight G beta J (ofEdgeFun G z.2.2)‖

private theorem summable_finiteTreeFourWeightMajorant
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) :
    Summable (finiteTreeFourWeightMajorant G beta J) := by
  let w : (G.edgeFinset -> Nat) -> Real := fun p =>
    ‖weight G beta J (ofEdgeFun G p)‖
  have hw : Summable w := summable_norm_weight_ofEdgeFun G beta J
  have hp : Summable (fun z :
      (G.edgeFinset -> Nat) × (G.edgeFinset -> Nat) =>
      w z.1 * w z.2) := hw.mul_of_nonneg hw (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _)
  have hpp : Summable (fun z : TreeFourProfiles G =>
      (w z.1.1 * w z.1.2) * (w z.2.1 * w z.2.2)) := hp.mul_of_nonneg hp
    (fun z => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun z => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  apply hpp.congr
  rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
  simp only [finiteTreeFourWeightMajorant, w]
  ring

theorem finiteTreeIndependentIntersectionSummand_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (i j k l : V) (z : TreeFourProfiles G) :
    0 <= finiteTreeIndependentIntersectionSummand G beta J i j k l z := by
  unfold finiteTreeIndependentIntersectionSummand
  apply mul_nonneg
  · exact mul_nonneg
      (mul_nonneg
        (by split <;> simp [StatMech.Ising.acw_weight_nonneg G beta J hbeta hJ])
        (by split <;> simp [StatMech.Ising.acw_weight_nonneg G beta J hbeta hJ]))
      (mul_nonneg
        (by split <;> simp [StatMech.Ising.acw_weight_nonneg G beta J hbeta hJ])
        (by split <;> simp [StatMech.Ising.acw_weight_nonneg G beta J hbeta hJ]))
  · split <;> norm_num

private theorem finiteTreeIndependentIntersectionSummand_norm_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V)
    (z : TreeFourProfiles G) :
    ‖finiteTreeIndependentIntersectionSummand G beta J i j k l z‖ <=
      finiteTreeFourWeightMajorant G beta J z := by
  unfold finiteTreeIndependentIntersectionSummand
  unfold finiteTreeFourWeightMajorant
  by_cases h1 : sources G (ofEdgeFun G z.1.1) = grahamPairSupport i j <;>
    by_cases h2 : sources G (ofEdgeFun G z.1.2) = ∅ <;>
    by_cases h3 : sources G (ofEdgeFun G z.2.1) = grahamPairSupport k l <;>
    by_cases h4 : sources G (ofEdgeFun G z.2.2) = ∅ <;>
    by_cases h5 : ∃ y : V,
      CurrentConnected G
        (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)) i y ∧
      CurrentConnected G
        (ofEdgeFun G (fun e => z.2.1 e + z.2.2 e)) k y <;>
    simp [h1, h2, h3, h4, h5, norm_mul, mul_assoc] <;>
    positivity

theorem summable_finiteTreeIndependentIntersectionSummand
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V) :
    Summable (finiteTreeIndependentIntersectionSummand G beta J i j k l) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (finiteTreeIndependentIntersectionSummand_norm_le
      G beta J i j k l)
    (summable_finiteTreeFourWeightMajorant G beta J)

private theorem summable_finiteTreeSeparatedFourSummand
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l y : V) :
    Summable (finiteTreeSeparatedFourSummand G beta J i j k l y) := by
  let C : Current V -> Prop := fun n => CurrentConnected G n i y
  let D : Current V -> Prop := fun n => CurrentConnected G n k y
  have hleft := summable_gatedSourcePairSummand G beta J
    (grahamPairSupport i j) ∅ C
  have hright := summable_gatedSourcePairSummand G beta J
    (grahamPairSupport k l) ∅ D
  have hprod := summable_mul_of_summable_norm hleft.norm hright.norm
  apply hprod.congr
  rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
  rfl

theorem finiteTreeSeparatedFourSummand_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (i j k l y : V) (z : TreeFourProfiles G) :
    0 <= finiteTreeSeparatedFourSummand G beta J i j k l y z := by
  unfold finiteTreeSeparatedFourSummand
  apply mul_nonneg
  · exact mul_nonneg
      (mul_nonneg
        (by split <;> simp [StatMech.Ising.acw_weight_nonneg G beta J hbeta hJ])
        (by split <;> simp [StatMech.Ising.acw_weight_nonneg G beta J hbeta hJ]))
      (by split <;> norm_num)
  · exact mul_nonneg
      (mul_nonneg
        (by split <;> simp [StatMech.Ising.acw_weight_nonneg G beta J hbeta hJ])
        (by split <;> simp [StatMech.Ising.acw_weight_nonneg G beta J hbeta hJ]))
      (by split <;> norm_num)

theorem finiteTreeIndependentIntersectionSummand_le_sum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (i j k l : V) (z : TreeFourProfiles G) :
    finiteTreeIndependentIntersectionSummand G beta J i j k l z <=
      ∑ y : V, finiteTreeSeparatedFourSummand G beta J i j k l y z := by
  by_cases hinter : ∃ y : V,
      CurrentConnected G
        (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)) i y ∧
      CurrentConnected G
        (ofEdgeFun G (fun e => z.2.1 e + z.2.2 e)) k y
  · obtain ⟨y, hiy, hky⟩ := hinter
    have hinter' : ∃ x : V,
        CurrentConnected G
          (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)) i x ∧
        CurrentConnected G
          (ofEdgeFun G (fun e => z.2.1 e + z.2.2 e)) k x :=
      ⟨y, hiy, hky⟩
    calc
      finiteTreeIndependentIntersectionSummand G beta J i j k l z =
          finiteTreeSeparatedFourSummand G beta J i j k l y z := by
        unfold finiteTreeIndependentIntersectionSummand
        unfold finiteTreeSeparatedFourSummand
        rw [if_pos hinter', if_pos hiy, if_pos hky]
        ring
      _ <= ∑ y : V,
          finiteTreeSeparatedFourSummand G beta J i j k l y z := by
        calc
          finiteTreeSeparatedFourSummand G beta J i j k l y z <=
              (∑ x ∈ (Finset.univ : Finset V).erase y,
                finiteTreeSeparatedFourSummand G beta J i j k l x z) +
                finiteTreeSeparatedFourSummand G beta J i j k l y z := by
            exact le_add_of_nonneg_left (Finset.sum_nonneg fun x _ =>
              finiteTreeSeparatedFourSummand_nonneg
                G beta J hbeta hJ i j k l x z)
          _ = ∑ x : V,
              finiteTreeSeparatedFourSummand G beta J i j k l x z := by
            exact Finset.sum_erase_add (Finset.univ : Finset V)
              (fun x => finiteTreeSeparatedFourSummand
                G beta J i j k l x z) (Finset.mem_univ y)
  · rw [finiteTreeIndependentIntersectionSummand]
    rw [if_neg hinter, mul_zero]
    apply Finset.sum_nonneg
    intro y _
    exact finiteTreeSeparatedFourSummand_nonneg
      G beta J hbeta hJ i j k l y z



theorem finiteTreeIndependentIntersectionFourMass_le_sum_separated
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (i j k l : V) :
    finiteTreeIndependentIntersectionFourMass G beta J i j k l <=
      ∑ y : V, finiteTreeSeparatedFourMass G beta J i j k l y := by
  let f : TreeFourProfiles G -> Real :=
    finiteTreeIndependentIntersectionSummand G beta J i j k l
  let g : TreeFourProfiles G -> Real := fun z =>
    ∑ y : V, finiteTreeSeparatedFourSummand G beta J i j k l y z
  have hf : Summable f := by
    simpa only [f] using
      summable_finiteTreeIndependentIntersectionSummand
        G beta J i j k l
  have hsep (y : V) := summable_finiteTreeSeparatedFourSummand
    G beta J i j k l y
  have hfinite : ∀ T : Finset V,
      Summable (fun z : TreeFourProfiles G =>
        ∑ y ∈ T, finiteTreeSeparatedFourSummand
          G beta J i j k l y z) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simpa using
        (summable_zero : Summable (fun _ : TreeFourProfiles G => (0 : Real)))
    | @insert y T hyT ih =>
        simpa [Finset.sum_insert hyT] using (hsep y).add ih
  have hg : Summable g := by
    simpa only [g] using hfinite (Finset.univ : Finset V)
  have hswap : ∀ T : Finset V,
      (∑' z : TreeFourProfiles G,
        ∑ y ∈ T, finiteTreeSeparatedFourSummand
          G beta J i j k l y z) =
      ∑ y ∈ T, ∑' z : TreeFourProfiles G,
        finiteTreeSeparatedFourSummand G beta J i j k l y z := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | @insert y T hyT ih =>
        have hfun : (fun z : TreeFourProfiles G =>
            ∑ x ∈ insert y T,
              finiteTreeSeparatedFourSummand G beta J i j k l x z) =
            (fun z => finiteTreeSeparatedFourSummand
              G beta J i j k l y z +
                ∑ x ∈ T, finiteTreeSeparatedFourSummand
                  G beta J i j k l x z) := by
          funext z
          rw [Finset.sum_insert hyT]
        rw [hfun, Summable.tsum_add (hsep y) (hfinite T),
          Finset.sum_insert hyT, ih]
  have hpoint : ∀ z, f z <= g z := fun z =>
    finiteTreeIndependentIntersectionSummand_le_sum
      G beta J hbeta hJ i j k l z
  calc
    finiteTreeIndependentIntersectionFourMass G beta J i j k l =
        ∑' z, f z := rfl
    _ <= ∑' z, g z := hf.tsum_le_tsum hpoint hg
    _ = ∑ y : V, finiteTreeSeparatedFourMass G beta J i j k l y := by
      rw [show (∑' z, g z) =
          ∑' z : TreeFourProfiles G,
            ∑ y ∈ (Finset.univ : Finset V),
              finiteTreeSeparatedFourSummand G beta J i j k l y z by rfl]
      rw [hswap (Finset.univ : Finset V)]
      apply Finset.sum_congr rfl
      intro y _
      exact (finiteTreeSeparatedFourMass_eq_summand
        G beta J i j k l y).symm

end StatMech.FrontierA
