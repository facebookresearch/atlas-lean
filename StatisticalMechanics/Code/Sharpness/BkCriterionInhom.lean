/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Sharpness.BkCriterionFull
import Code.Inequalities.ReimerEndpointProve

open scoped BigOperators
open Finset

namespace StatMech

namespace Sharpness

open ConfigSpace SimpleGraph

variable {E V : Type*}


theorem shk_pweight_splitAt [Fintype E] [DecidableEq E]
    (phi : E → Bool → ℝ) (e : E) (b : Bool) (rest : {j // j ≠ e} → Bool) :
    pweight phi ((Equiv.piSplitAt e (fun _ : E => Bool)).symm (b, rest)) =
      phi e b * pweight (fun j : {j // j ≠ e} => phi j.1) rest := by
  unfold pweight
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => phi j ((Equiv.piSplitAt e (fun _ : E => Bool)).symm (b, rest) j))
    (Finset.mem_univ e)]
  congr 1
  · simp [Equiv.piSplitAt_symm_apply]
  · rw [Finset.prod_subtype (p := fun j => j ≠ e) (Finset.univ.erase e)
      (fun j => by simp)]
    apply Finset.prod_congr rfl
    intro j _
    simp [Equiv.piSplitAt_symm_apply, j.2]



theorem shk_wprob_edgeOpen [Fintype E] [DecidableEq E]
    (phi : E → Bool → ℝ) (hphi : ∀ e, phi e false + phi e true = 1) (e : E) :
    wprob phi {omega : ConfigSpace E | omega e = true} = phi e true := by
  unfold wprob
  rw [← Equiv.sum_comp (Equiv.piSplitAt e (fun _ : E => Bool)).symm]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Set.indicator, Set.mem_setOf_eq, Equiv.piSplitAt_symm_apply]
  simp_rw [shk_pweight_splitAt]
  simp [← Finset.mul_sum,
    sum_pweight_eq_one (fun j : {j // j ≠ e} => hphi j.1)]


theorem shk_bk_triple_inhom [Fintype E] [DecidableEq E]
    (phi : E → Bool → ℝ)
    (hphi0 : ∀ e b, 0 ≤ phi e b) (hphi1 : ∀ e, phi e false + phi e true = 1)
    {P Q R : Set (ConfigSpace E)}
    (hP : IsIncreasing P) (hQ : IsIncreasing Q) (hR : IsIncreasing R) :
    wprob phi (disjointOccurrence P (disjointOccurrence Q R)) ≤
      wprob phi P * wprob phi Q * wprob phi R := by
  calc
    wprob phi (disjointOccurrence P (disjointOccurrence Q R)) ≤
        wprob phi P * wprob phi (disjointOccurrence Q R) :=
      bk_wprob_general phi hphi0 hphi1 hP (disjointOccurrence_isIncreasing hQ hR)
    _ ≤ wprob phi P * (wprob phi Q * wprob phi R) :=
      mul_le_mul_of_nonneg_left
        (bk_wprob_general phi hphi0 hphi1 hQ hR) (wprob_nonneg hphi0 P)
    _ = _ := by ring


theorem shk_wprob_biUnion_le [Fintype E] [DecidableEq E]
    (phi : E → Bool → ℝ) (hphi0 : ∀ e b, 0 ≤ phi e b)
    {I : Type*} (s : Finset I) (F : I → Set (ConfigSpace E)) :
    wprob phi (⋃ i ∈ s, F i) ≤ ∑ i ∈ s, wprob phi (F i) := by
  unfold wprob
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro omega _
  by_cases homega : omega ∈ ⋃ i ∈ s, F i
  · rw [Set.indicator_of_mem homega]
    obtain ⟨i, hi, hFi⟩ := Set.mem_iUnion₂.mp homega
    have hterm : pweight phi omega ≤
        ∑ j ∈ s, (F j).indicator (fun _ => (1 : ℝ)) omega * pweight phi omega := by
      have hnonneg : ∀ j ∈ s,
          0 ≤ (F j).indicator (fun _ => (1 : ℝ)) omega * pweight phi omega := by
        intro j _
        exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (pweight_nonneg hphi0 _)
      calc
        pweight phi omega =
            (F i).indicator (fun _ => (1 : ℝ)) omega * pweight phi omega := by
              rw [Set.indicator_of_mem hFi, one_mul]
        _ ≤ _ := Finset.single_le_sum (fun j hj => hnonneg j hj) hi
    simpa only [one_mul] using hterm
  · rw [Set.indicator_of_notMem homega, zero_mul]
    exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (pweight_nonneg hphi0 _))



noncomputable def shk_edgeLaw (beta : ℝ) (J : E → ℝ) (e : E) (b : Bool) : ℝ :=
  if b then 1 - Real.exp (-beta * J e) else Real.exp (-beta * J e)

theorem shk_edgeLaw_nonneg (beta : ℝ) (J : E → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (e : E) (b : Bool) :
    0 ≤ shk_edgeLaw beta J e b := by
  cases b with
  | false => exact (Real.exp_pos _).le
  | true =>
      exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hbeta) (hJ e)))

theorem shk_edgeLaw_sum_one (beta : ℝ) (J : E → ℝ) (e : E) :
    shk_edgeLaw beta J e false + shk_edgeLaw beta J e true = 1 := by
  simp [shk_edgeLaw]




theorem bk_criterion_inhomogeneous [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : ℝ) (J : Sym2 V → ℝ) (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (A : Set V) (S : Finset V) (B : Set V) (u : V)
    (huS : u ∈ S) (hBS : ∀ z ∈ B, z ∉ S) :
    wprob (shk_edgeLaw beta J) (connEvent G A u B) ≤
      ∑ q ∈ shk_boundaryPairs G S,
        (1 - Real.exp (-beta * J s(q.1, q.2))) *
          wprob (shk_edgeLaw beta J) (connEvent G (S : Set V) u {q.1}) *
          wprob (shk_edgeLaw beta J) (connEvent G A q.2 B) := by
  let F : V × V → Set (ConfigSpace (Sym2 V)) := fun q =>
    disjointOccurrence (connEvent G (S : Set V) u {q.1})
      (disjointOccurrence (edgeOpenEvent q.1 q.2) (connEvent G A q.2 B))
  have hincl := shk_firstExit_inclusion G A S B u huS hBS
  calc
    wprob (shk_edgeLaw beta J) (connEvent G A u B) ≤
        wprob (shk_edgeLaw beta J) (⋃ q ∈ shk_boundaryPairs G S, F q) :=
      wprob_mono (fun e b => shk_edgeLaw_nonneg beta J hbeta hJ e b) hincl
    _ ≤ ∑ q ∈ shk_boundaryPairs G S, wprob (shk_edgeLaw beta J) (F q) :=
      shk_wprob_biUnion_le (shk_edgeLaw beta J)
        (fun e b => shk_edgeLaw_nonneg beta J hbeta hJ e b) _ F
    _ ≤ ∑ q ∈ shk_boundaryPairs G S,
        wprob (shk_edgeLaw beta J) (connEvent G (S : Set V) u {q.1}) *
          wprob (shk_edgeLaw beta J) (edgeOpenEvent q.1 q.2) *
          wprob (shk_edgeLaw beta J) (connEvent G A q.2 B) := by
      apply Finset.sum_le_sum
      intro q _
      exact shk_bk_triple_inhom (shk_edgeLaw beta J)
        (fun e b => shk_edgeLaw_nonneg beta J hbeta hJ e b)
        (shk_edgeLaw_sum_one beta J)
        (isIncreasing_connEvent G (S : Set V) u {q.1})
        (isIncreasing_edgeOpenEvent q.1 q.2)
        (isIncreasing_connEvent G A q.2 B)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      change _ * wprob (shk_edgeLaw beta J)
        {omega : ConfigSpace (Sym2 V) | omega s(q.1, q.2) = true} * _ = _
      rw [shk_wprob_edgeOpen (shk_edgeLaw beta J) (shk_edgeLaw_sum_one beta J)]
      change _ * (1 - Real.exp (-beta * J s(q.1, q.2))) * _ = _
      ring

end Sharpness

end StatMech
