/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























import Mathlib
import Code.Sharpness.DeltaRewrite
import Code.Sharpness.SwitchingDichotomy
import Code.Sharpness.SwitchingCovariance

open Finset BigOperators
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech
namespace Sharpness

open StatMech.Sharpness.RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]



















theorem drd_deltaRewrite_perEdge_dichotomy
    (ends : ι → Sym2 V)
    (covTerm : ℝ)
    (pairSum : (Finset ι → Prop) → ℝ)
    (hpairSum_add : ∀ (P₁ P₂ : Finset ι → Prop) [DecidablePred P₁] [DecidablePred P₂]
        [DecidablePred (fun m => P₁ m ∨ P₂ m)],
        (∀ m, ¬ (P₁ m ∧ P₂ m)) →
        pairSum (fun m => P₁ m ∨ P₂ m) = pairSum P₁ + pairSum P₂)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hloop : ∀ m : Finset ι, ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → RandomCurrent.sources ends m = {o, x, y, g})
    (hcov : covTerm = pairSum (fun m => ¬ connK ends m o g)) :
    covTerm
      = pairSum (fun m => (¬ connK ends m o g) ∧ (connK ends m o x ∧ connK ends m y g))
        + pairSum (fun m => (¬ connK ends m o g) ∧ (connK ends m o y ∧ connK ends m x g)) := by
  classical
  refine sdr_deltaRewrite_perEdge covTerm pairSum hpairSum_add
    (disconn := fun m => ¬ connK ends m o g)
    (caseA := fun m => connK ends m o x ∧ connK ends m y g)
    (caseB := fun m => connK ends m o y ∧ connK ends m x g)
    hcov ?_
  
  intro m hdisc
  exact disconnect_dichotomy_prop ends m (hloop m) hox hoy hog hxy hxg hyg
    (hsrcSet m hdisc) hdisc










noncomputable def drd_pairSum (ends : ι → Sym2 V) (A : Finset V) (F : Finset ι → ℝ)
    (P : Finset ι → Prop) : ℝ :=
  ∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources ends m = A)),
    (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources ends K = A),
        F m * (if P m then 1 else 0))



theorem drd_pairSum_add (ends : ι → Sym2 V) (A : Finset V) (F : Finset ι → ℝ)
    (P₁ P₂ : Finset ι → Prop) [DecidablePred P₁] [DecidablePred P₂]
    [DecidablePred (fun m => P₁ m ∨ P₂ m)]
    (hdisj : ∀ m, ¬ (P₁ m ∧ P₂ m)) :
    drd_pairSum ends A F (fun m => P₁ m ∨ P₂ m)
      = drd_pairSum ends A F P₁ + drd_pairSum ends A F P₂ := by
  classical
  unfold drd_pairSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun K _ => ?_)
  by_cases h1 : P₁ m <;> by_cases h2 : P₂ m
  · exact absurd ⟨h1, h2⟩ (hdisj m)
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]
















theorem drd_deltaRewrite_full
    (ends : ι → Sym2 V) (F : Finset ι → ℝ)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hnd : ∀ i, ¬ (ends i).IsDiag)
    (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → RandomCurrent.sources ends m = {o, x, y, g}) :
    drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => ¬ connK ends m o g)
      = drd_pairSum ends ({o, x, y, g} : Finset V) F
          (fun m => (¬ connK ends m o g) ∧ (connK ends m o x ∧ connK ends m y g))
        + drd_pairSum ends ({o, x, y, g} : Finset V) F
          (fun m => (¬ connK ends m o g) ∧ (connK ends m o y ∧ connK ends m x g)) := by
  classical
  
  refine sdr_deltaRewrite_perEdge
    (drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => ¬ connK ends m o g))
    (drd_pairSum ends ({o, x, y, g} : Finset V) F)
    (fun P₁ P₂ _ _ _ hdisj => drd_pairSum_add ends _ F P₁ P₂ hdisj)
    (disconn := fun m => ¬ connK ends m o g)
    (caseA := fun m => connK ends m o x ∧ connK ends m y g)
    (caseB := fun m => connK ends m o y ∧ connK ends m x g)
    rfl ?_
  intro m hdisc
  exact disconnect_dichotomy_prop ends m (fun i _ => hnd i) hox hoy hog hxy hxg hyg
    (hsrcSet m hdisc) hdisc






theorem drd_pairSum_disconnect_eq_gap
    (ends : ι → Sym2 V) (F : Finset ι → ℝ) (A : Finset V)
    (hnd : ∀ i, ¬ (ends i).IsDiag) {u v : V} (huv : u ≠ v) :
    drd_pairSum ends A F (fun m => ¬ connK ends m u v)
      = (∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources ends m = A)),
          (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources ends K = A), F m))
        - (∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources ends m = A)),
            (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources ends K = A ∆ {u, v}), F m)) := by
  rw [srcPairDisconnect_eq ends hnd A huv F]
  unfold drd_pairSum
  refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun K _ => ?_))
  by_cases h : connK ends m u v <;> simp [h]








theorem drd_gap_eq_deltaForm
    (ends : ι → Sym2 V) (F : Finset ι → ℝ)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hnd : ∀ i, ¬ (ends i).IsDiag)
    (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → RandomCurrent.sources ends m = {o, x, y, g}) :
    ((∑ m ∈ (Finset.univ.powerset.filter
          (fun m => RandomCurrent.sources ends m = ({o, x, y, g} : Finset V))),
          (∑ _K ∈ m.powerset.filter
            (fun K => RandomCurrent.sources ends K = ({o, x, y, g} : Finset V)), F m))
        - (∑ m ∈ (Finset.univ.powerset.filter
            (fun m => RandomCurrent.sources ends m = ({o, x, y, g} : Finset V))),
            (∑ _K ∈ m.powerset.filter
              (fun K => RandomCurrent.sources ends K = ({o, x, y, g} : Finset V) ∆ {o, g}), F m)))
      = drd_pairSum ends ({o, x, y, g} : Finset V) F
          (fun m => (¬ connK ends m o g) ∧ (connK ends m o x ∧ connK ends m y g))
        + drd_pairSum ends ({o, x, y, g} : Finset V) F
          (fun m => (¬ connK ends m o g) ∧ (connK ends m o y ∧ connK ends m x g)) := by
  rw [← drd_pairSum_disconnect_eq_gap ends F ({o, x, y, g} : Finset V) hnd (u := o) (v := g) hog]
  exact drd_deltaRewrite_full ends F hox hoy hog hxy hxg hyg hnd hsrcSet

end Sharpness
end StatMech
