/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































import Mathlib
import Code.Sharpness.Switching
import Code.Sharpness.Claim1IsingFull

open Finset BigOperators
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech
namespace Sharpness
namespace RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]














theorem switching_disconnect_card (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {u v : V} (huv : u ≠ v) :
    (#(m.powerset.filter (fun K => sources ends K = A)) : ℤ)
        - #(m.powerset.filter (fun K => sources ends K = A ∆ {u, v}))
      = (if ¬ connK ends m u v then
          (#(m.powerset.filter (fun K => sources ends K = A)) : ℤ) else 0) := by
  rw [switching_card ends m hnd A hm huv]
  by_cases hconn : connK ends m u v
  · simp [hconn]
  · simp [hconn]






theorem switching_disconnect_lemma (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {u v : V} (huv : u ≠ v) (F : Finset ι → ℝ) :
    (∑ _K ∈ m.powerset.filter (fun K => sources ends K = A), F m)
        - (∑ _K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {u, v}), F m)
      = ∑ _K ∈ m.powerset.filter (fun K => sources ends K = A),
          F m * (if ¬ connK ends m u v then 1 else 0) := by
  rw [Finset.sum_const, Finset.sum_const, Finset.sum_const]
  rw [switching_card ends m hnd A hm huv]
  by_cases hconn : connK ends m u v
  · simp [hconn]
  · simp [hconn]













theorem srcPairDisconnect_eq (ends : ι → Sym2 V)
    (hnd : ∀ i, ¬ (ends i).IsDiag)
    (A : Finset V) {u v : V} (huv : u ≠ v) (F : Finset ι → ℝ) :
    (∑ m ∈ (Finset.univ.powerset.filter (fun m => sources ends m = A)),
        (∑ _K ∈ m.powerset.filter (fun K => sources ends K = A), F m))
      - (∑ m ∈ (Finset.univ.powerset.filter (fun m => sources ends m = A)),
          (∑ _K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {u, v}), F m))
      = ∑ m ∈ (Finset.univ.powerset.filter (fun m => sources ends m = A)),
          (∑ _K ∈ m.powerset.filter (fun K => sources ends K = A),
              F m * (if ¬ connK ends m u v then 1 else 0)) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [Finset.mem_filter, Finset.mem_powerset] at hm
  exact switching_disconnect_lemma ends m (fun i _ => hnd i) A hm.2 huv F

end RandomCurrent
end Sharpness
end StatMech
